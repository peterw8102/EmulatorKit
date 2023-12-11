/*
 *  https://oshwlab.com/peterw8102/simple-z80
 *  https://github.com/peterw8102/Z80-Retro/wiki
 *
 *	Platform features
 *
 *	Z80 at 14.7MHz
 *  Zilog CTC at 0x40-0x43 at 1/2 clock
 *	Zilog SIO/2 at 0x80-0x83
 *	Memory banking Zeta style 16K page at 0x60-63
 *	Config port at 64
 *	RTC on bitbang I2C
 *	SD on bitbang SPI
 *
 *	I2C use: 0x64, 0x65 (address bit 0 is clock)
 *	SPI use: 0x64 for chip selects
 *		0x68, 0x69 SPI data and (addr bit 0) SPI clock
 *
 *	Limitations:
 *	+ Only the first SDCard is supported
 *	+ Only emulates the main CPU card, not VDU or PIO cards
 *	+ Doesn't simulate programming the Flash
 *
 *  Send a SIGHUP to emulate a press of the hardware reset button.
 */

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <signal.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>
#include <errno.h>
#include <sys/select.h>

#include "sdcard.h"
#include "i2c_bitbang.h"
#include "i2c_ds1307.h"
#include "system.h"
#include "libz80/z80.h"
#include "z80dis.h"

/* Whole available memory space - although only 64 pages exist
 * in the base system (0-1F: ROM, 20-3F: RAM)
 */
enum {
	READABLE=1,
	WRITEABLE
};
static uint8_t ramrom[256 * 16384];
static uint8_t pages[256] = {0};   /* 0:not installed, bit 0:readable, bit 1:writeable */
static uint8_t bankreg[4];
static uint8_t genio_data;    /* Generic I/O bits */

static uint8_t fast = 0;
static uint8_t int_recalc = 0;

static struct sdcard *sdcard;

static struct i2c_bus *i2cbus;		/* I2C bus */
static struct ds1307 *rtcdev;		/* DS1307 RTC */
static char  *nvpath = "z80retrom.nvram";

static uint16_t tstate_steps = 730;	/* 14.4MHz speed */

/* IRQ source that is live in IM2 */
static uint8_t live_irq;

#define IRQ_SIOA	1
#define IRQ_SIOB	2
#define IRQ_CTC		3	/* 3 4 5 6 */
/* TOOD: PIO */

/* Value of the 3 configuration DIP switches */
static uint8_t dip_switch;

/* Storage for data sent FROM SIO port B */
static uint8_t blk_out[256] = {0x55, 0xcc};
static int     blk_out_cnt = 0;
static int     blk_out_sz  = 0;

/* And data that's queued to be sent. */
static uint8_t blk_in[256];
static int     blk_in_cnt = 0;
static uint8_t blk_size = 0;

/* If there's an open file for transfer to the Z80 system then this is the file descriptor */
static int blk_fd = -1;
static int blk_fsize;

/* Files are openned in the blk_path directory */
static const char *blk_path = NULL;

static Z80Context cpu_z80;

volatile int emulator_done;

#define TRACE_MEM	0x000001
#define TRACE_IO	0x000002
#define TRACE_ROM	0x000004
#define TRACE_UNK	0x000008
#define TRACE_CPU	0x000010
#define TRACE_BANK	0x000020
#define TRACE_SIO	0x000040
#define TRACE_CTC	0x000080
#define TRACE_IRQ	0x000100
#define TRACE_SPI	0x000200
#define TRACE_SD	0x000400
#define TRACE_I2C	0x000800
#define TRACE_RTC	0x001000
#define TRACE_CMD	0x002000
#define TRACE_INFO	0x000004

static int trace = 0;

static void reti_event(void);

static void cpu_state()
{
	fprintf(stderr, "[ PC:%04X AF:%02X:%02X BC:%04X DE:%04X HL:%04X IX:%04X IY:%04X SP:%04X ]\n",
					cpu_z80.M1PC,
					cpu_z80.R1.br.A, cpu_z80.R1.br.F,
					cpu_z80.R1.wr.BC, cpu_z80.R1.wr.DE, cpu_z80.R1.wr.HL,
					cpu_z80.R1.wr.IX, cpu_z80.R1.wr.IY, cpu_z80.R1.wr.SP);
}

/* Map 16 bit CPU address to a 22 bit physical address */
static uint8_t *map_addr(uint16_t addr, unsigned is_write) {
	unsigned int bank = (addr & 0xC000) >> 14;
	if (!(genio_data & 1)) {
		/* MMU disabled so ROM everywhere */
		if (is_write) {
			if (trace & TRACE_INFO)
				fprintf(stderr, "[Discarded: ROM] MMU disabled %04x\n",addr);
			return NULL;
		}
		return ramrom + addr;
	}
	/* MMU enabled so use bankreg and pstat to determine access */
	uint8_t pstat = pages[bankreg[bank]];
	if (!(pstat & WRITEABLE) && is_write) {
		if (trace & TRACE_INFO) { /* ROM writes go nowhere */
			fprintf(stderr, "[Discarded: ROM] @%02x:%04x\n", (int)bankreg[bank], (addr & 0x3FFF));
			cpu_state();
		}
		return NULL;
	}
	else if (!(pstat & READABLE) && (trace & TRACE_INFO)) {
		fprintf(stderr, "Read from uninstalled memory @%02x:%04x [%02x %02x %02x %02x]\n",
						(int)bankreg[bank], (addr & 0x3FFF), bankreg[0], bankreg[1], bankreg[2], bankreg[3]);
		cpu_state();
	}
	return ramrom + (bankreg[bank] << 14) + (addr & 0x3FFF);
}


static uint8_t do_mem_read(uint16_t addr, int quiet)
{
	uint8_t *p = map_addr(addr, 0);
	uint8_t r = *p;
	if ((trace & TRACE_MEM) && !quiet)
		fprintf(stderr, "R %04x = %02X\n", addr, r) ;
	return r;
}

void mem_write(int unused, uint16_t addr, uint8_t val)
{
	uint8_t *p = map_addr(addr, 1);
	if (trace & TRACE_MEM)
		fprintf(stderr, "W %04x = %02X\n",
			addr, val);
	if (p)
		*p = val;
	else if (trace & TRACE_MEM)	/* ROM writes go nowhere */
		fprintf(stderr, "[Discarded: ROM]\n");
}

uint8_t mem_read(int unused, uint16_t addr)
{
	static uint8_t rstate = 0;
	uint8_t r = do_mem_read(addr, 0);

	if (cpu_z80.M1) {
		/* DD FD CB see the Z80 interrupt manual */
		if (r == 0xDD || r == 0xFD || r == 0xCB) {
			rstate = 2;
			return r;
		}
		/* Look for ED with M1, followed directly by 4D and if so trigger
			 the interrupt chain */
		if (r == 0xED && rstate == 0) {
			rstate = 1;
			return r;
		}
	}
	if (r == 0x4D && rstate == 1)
		reti_event();
	rstate = 0;
	return r;
}

static unsigned int nbytes;

uint8_t z80dis_byte(uint16_t addr)
{
	uint8_t r = do_mem_read(addr, 1);
	fprintf(stderr, "%02X ", r);
	nbytes++;
	return r;
}

uint8_t z80dis_byte_quiet(uint16_t addr)
{
	return do_mem_read(addr, 1);
}

static void z80_trace(unsigned unused)
{
	static uint32_t lastpc = -1;
	char buf[256];

	if ((trace & TRACE_CPU) == 0)
		return;
	nbytes = 0;
	/* Spot XXXR repeating instructions and squash the trace */
	if (cpu_z80.M1PC == lastpc && z80dis_byte_quiet(lastpc) == 0xED &&
		(z80dis_byte_quiet(lastpc + 1) & 0xF4) == 0xB0) {
		return;
	}
	lastpc = cpu_z80.M1PC;
	fprintf(stderr, "%04X: ", lastpc);
	z80_disasm(buf, lastpc);
	while(nbytes++ < 6)
		fprintf(stderr, "   ");
	fprintf(stderr, "%-16s ", buf);
  cpu_state();
}

void recalc_interrupts(void) {
  int_recalc = 1;
}

/***************** SIO_CLIENT. ***************************/
/* Three variants - null, console and blk. An instance of
 * this structure can be connected to either of the SIO ports.
 */
typedef struct SIO_CLIENT {
  uint8_t (*test_chr)(void);
  uint8_t (*get_chr)(void);
  void    (*write_chr)(uint8_t chr);
} SIO_CLIENT;

/***************** Null service *****************/
/* Use this when an SIO channel is disconnected. Basically a bitbucket */
static uint8_t null_check(void) {
  /* Never any characters waiting */
  return 0;
}
static void null_putchr(uint8_t chr) {
  /* Characters from the Z80 are dumped */
}

struct SIO_CLIENT null_chan = {
  null_check,
  NULL,
  null_putchr
};

/***************** Console service *****************/
/* Used to send/receive data to/from the console */

static uint8_t term_check(void) {
	fd_set i, o;
	struct timeval tv;
	unsigned int r = 0;

	FD_ZERO(&i);
	FD_SET(0, &i);
	FD_ZERO(&o);
	FD_SET(1, &o);
	tv.tv_sec = 0;
	tv.tv_usec = 0;

	if (select(2, &i, &o, NULL, &tv) == -1) {
		if (errno == EINTR)
			return 0;
		perror("select");
		exit(1);
	}
	if (FD_ISSET(0, &i))
		r |= 1;
	if (FD_ISSET(1, &o))
		r |= 2;
	return r;
}

static uint8_t term_getchr(void)
{
	char c;
	if (read(0, &c, 1) != 1) {
		printf("(tty read without ready byte)\n");
		return 0xFF;
	}
  if (trace & TRACE_SIO) {
    if (c >= 32)
      fprintf(stderr, "RX: 0x%02x ('%c')\n", (int)c, c);
    else
      fprintf(stderr, "RX: 0x%02x\n", (int)c);
  }
	if (c == 0x0A)
		c = '\r';
	return c;
}

/* Write character to stdout */
static void term_putchr(uint8_t chr) {
  write(1, &chr, 1);
}

struct SIO_CLIENT cons_chan = {
  term_check,
  term_getchr,
  term_putchr
};

/********************** Block/command protocol emulation  ******************/
/* To speed development on the real hardware I connect a Raspberry Pi to
 * SIO port B operating at about 400Kbps. A simple command/response protocol
 * allows the Z80 code to load files directly from the Pi's file system. The
 * most common use of this is for the ZLoader to be set to automotically load
 * 'boot.ihx' at start up and effectively automatically boot into an operational
 * system. This set of 'blk_' functions implements the basica protocol and
 * allows this emulator to serve files to the Z80 from the path provided
 * in the '-b' command line option.
 *
 * https://github.com/peterw8102/Z80-Retro/wiki/SIO-Command-Protocol
 */
/* blk_check
 * Check whether there's an available character to send to the Z80.  */
static uint8_t blk_check(void) {
  return (blk_out_cnt < blk_out_sz);
}

/* blk_getchr
 * Return the next character ready to be sent to the Z80 and change counters/pointers
 */
static uint8_t blk_getchr() {
  uint8_t c = (blk_out_cnt < blk_out_sz) ?
                blk_out[blk_out_cnt++]  :
                0;
  return c;
}
/* blk_show
 * Dump a command or response buffer
 */
static void blk_show(uint8_t *buf, int len) {
  for (int i = 0; i < len; i++)
    fprintf(stderr, "%02x ", buf[i]);
  fprintf(stderr, "\n");
}

/* blk_error - Send a 6 byte error response to the Z80. */
static void blk_error(uint8_t code) {
  blk_out[2]  = blk_in[2]; // Command code
  blk_out[3]  = code;      // Error code
  blk_out[4]  = 0;         // No payload.
  blk_out[5]  = 0;
  blk_out_sz  = 6;         // Bytes to write
  blk_out_cnt = 0;         // Current offset
  if (trace & TRACE_CMD) {
    fprintf(stderr, "CMD: Tx Response :");
    blk_show(blk_out, blk_out_sz);
  }
}

/* blk_dispatch
 * There's a complete command in the `blk_in` buffer. Process and make a
 * response. At the moment ONLY implement command codes 0x10 and 0x11 used
 * to read files from the slave file system. Leave emulating block storage
 * devices until another time.
 */
static void blk_dispatch() {
  if (trace & TRACE_CMD) {
    fprintf(stderr, "CMD: Rx Command: ");
    blk_show(blk_in, blk_in_cnt);
  }

  if (blk_in_cnt > 5) {
    /* There's a body so there's a checksum */
    uint8_t cs = 0;
    for (int i = 5; i < blk_in_cnt-1 ; i++)
      cs += blk_in[i];
    if (trace & TRACE_CMD)
      fprintf(stderr, "CMD: Rx checksum: %02x - %s\n", cs, (cs == blk_in[blk_in_cnt - 1]) ? "Ok" : "Bad");
    if (cs != blk_in[blk_in_cnt-1]) {
      /* Reject commands with a payload and bad checksum */
      blk_error(0xff);
      return;
    }
  }
  blk_out[2] = blk_out[1]; // Copy the command ID into the response
  char fname[100];

  switch (blk_in[2]) {
  case 0x10:
    /* Open a named file for reading */
    if (blk_in_cnt < 7) {
      blk_error(0xff);
      return;
    }
    int i, j;
    for (i = 5, j = 0; i < blk_in_cnt - 1; i++, j++)
      fname[j] = blk_in[i];
    fname[j] = 0;
    if (trace & TRACE_CMD)
      fprintf(stderr, "CMD: Open File: %s\n", fname);

    // Close any currently open file.
    if (blk_fd!=-1) {
      close(blk_fd);
      blk_fd = -1;
    }
    char target[256];
    strcpy(target, blk_path);
    strcat(target, "/");
    strcat(target, fname);

    // Open the new file
    blk_fd = open(target, O_RDWR);

    if (trace & TRACE_CMD)
      fprintf(stderr, "CMD: File open \"%s\" : %d - %s\n",
              target, blk_fd, blk_fd>=0 ? "Ok" : "Failed");

    blk_error(blk_fd<0);
    blk_fsize = 0;
    break;
  case 0x11:
    /* Read the next 128 bytes from the currently open file */
    if (blk_fd<0)
      blk_error(1); // No open file

    // Read next up to 128 bytes into blk_out
    const int sz = read(blk_fd, (void *)&blk_out[6], 128);

    blk_out[2] = 0x11; // Command ID

    const uint8_t end_of_file = (sz<128);

    blk_out_sz = 6;

    if (sz > 0) {
      // Checksum...
      uint8_t *p  = &blk_out[6];
      uint8_t  cs = 0;
      for (int i=0;i<sz;i++, p++)
        cs += *p;
      *p = cs;

      /* Adjust the number of bytes to transmit */
      blk_out_sz += sz + 1;

      blk_fsize += sz;

      if (trace & TRACE_CMD)
          fprintf(stderr, "Checksum: %02x\n", (int)cs);
    }

    // Add payload length to header.
    blk_out[3] = end_of_file;       // 1: end of file
    blk_out[4] = (sz & 0xff);
    blk_out[5] = 0;                 // Never more than 128 bytes.

    // Send response.
    if (end_of_file) {
      /* End of file - close and just return the header. */
      close(blk_fd);
      blk_fd = -1;
      if (trace & TRACE_CMD)
        fprintf(stderr, "CMD: Sent %d bytes - host file closed\n", blk_fsize);
    }
    blk_out_cnt = 0;

    if (trace & TRACE_CMD) {
      fprintf(stderr, "CMD: Read %d bytes from input file\nCMD: Tx Response :", (int)sz);
      blk_show(blk_out, blk_out_sz);
    }
    break;
  default:
    /* unimplemented command - send error. */
    blk_error(0xff);
    break;
  }
}
/* blk_putchr
 * Character sent to US from the Z80. An ad-hoc state machine using
 * blk_in_cnt looking for the a sequence starting with 0x55, 0xAA.
 */
static void blk_putchr(uint8_t chr)
{
  blk_in[blk_in_cnt++] = chr;

  if (blk_in_cnt == 1) {
    /* Ignore everything until a 0x55 sync character */
    if (chr != 0x55)
      blk_in_cnt = 0;
  }
  else if (blk_in_cnt == 2) {
    /* 0x55 must be followed by 0xAA */
    if (chr != 0xAA)
      blk_in_cnt = 0;
  }
  else if (blk_in_cnt == 255) {
    // Too long. Reset and start again
    blk_in_cnt = 0;
  }
  else if (blk_in_cnt == 5) {
    /* Have the header - so we know how many more bytes we should expect (body plus checksum) */
    blk_size = ((blk_in[4] << 8) | blk_in[3]) + 1;
    if (blk_size == 1) {
      /* No payload so process what we have */
      blk_dispatch();
      blk_in_cnt = 0;
    }
    else if (blk_size>128) {
      /* Although the protocol allows a payload over 128 bytes none
       * of the currently defined commands use a larger payload so
       * ignore what we have. */
      blk_in_cnt = 0;
    }
  }
  else if (blk_in_cnt > 5 && (--blk_size) == 0) {
    // Header and payload complete
    blk_dispatch();
    blk_in_cnt = 0;
  }
}

struct SIO_CLIENT blk_chan = {
  blk_check,
  blk_getchr,
  blk_putchr
};

/********************** SIO Emulation ******************/
struct z80_sio_chan
{
	uint8_t wr[8];
	uint8_t rr[3];
	uint8_t data[3];
	uint8_t dptr;
	uint8_t irq;
	uint8_t rxint;
	uint8_t txint;
	uint8_t intbits;
#define INT_TX	1
#define INT_RX	2
#define INT_ERR	4
	uint8_t pending;	/* Interrupt bits pending as an IRQ cause */
	uint8_t vector;		/* Vector pending to deliver */
	#define SIO_BUSY 1
	#define SIO_RTS  2 /* Don't change this value - must align with wr[5] */
	  uint8_t status;  /* Just to help with debug output and tracking state changes */
	  uint16_t rxchrs; /* Count of received characters */

	  /* What this channel is connected to. Nothing, console, blk protocol etc */
	  SIO_CLIENT *client;
	};

static int sio2_input;
static struct z80_sio_chan sio[2];

/*
 *	Interrupts. We don't handle IM2 yet.
 */

static void sio2_clear_int(struct z80_sio_chan *chan, uint8_t m)
{
	if (trace & TRACE_IRQ) {
		fprintf(stderr, "Clear intbits %d %x\n",
			(int)(chan - sio), m);
	}
	chan->intbits &= ~m;
	chan->pending &= ~m;
	/* Check me - does it auto clear down or do you have to reti it ? */
	if (!(sio->intbits | sio[1].intbits)) {
		sio->rr[1] &= ~0x02;
		chan->irq = 0;
	}
	recalc_interrupts();
}

static void sio2_raise_int(struct z80_sio_chan *chan, uint8_t m)
{
	uint8_t new = (chan->intbits ^ m) & m;
	chan->intbits |= m;
	if ((trace & TRACE_SIO) && new)
		fprintf(stderr, "SIO raise int %x new = %x\n", m, new);
	if (new) {
		if (!sio->irq) {
			chan->irq = 1;
			sio->rr[1] |= 0x02;
			recalc_interrupts();
		}
	}
}

static void sio2_reti(struct z80_sio_chan *chan)
{
	/* Recalculate the pending state and vectors */
	/* FIXME: what really goes here */
	sio->irq = 0;
	recalc_interrupts();
}

static int sio2_check_im2(struct z80_sio_chan *chan)
{
	uint8_t vector = sio[1].wr[2];
	/* See if we have an IRQ pending and if so deliver it and return 1 */
	if (chan->irq) {
		/* Do the vector calculation in the right place */
		/* FIXME: move this to other platforms */
		if (sio[1].wr[1] & 0x04) {
			/* This is a subset of the real options. FIXME: add
				 external status change */
			if (sio[1].wr[1] & 0x04) {
				vector &= 0xF1;
				if (chan == sio)
					vector |= 1 << 3;
				if (chan->intbits & INT_RX)
					vector |= 4;
				else if (chan->intbits & INT_ERR)
					vector |= 2;
			}
			if (trace & TRACE_SIO)
				fprintf(stderr, "SIO2 interrupt %02X\n", vector);
			chan->vector = vector;
		} else {
			chan->vector = vector;
		}
		if (trace & (TRACE_IRQ|TRACE_SIO))
			fprintf(stderr, "New live interrupt pending is SIO (%d:%02X).\n",
				(int)(chan - sio), chan->vector);
		if (chan == sio)
			live_irq = IRQ_SIOA;
		else
			live_irq = IRQ_SIOB;
		Z80INT(&cpu_z80, chan->vector);
		return 1;
	}
	return 0;
}

/*
 *	The SIO replaces the last character in the FIFO on an
 *	overrun.
 */
static void sio2_queue(struct z80_sio_chan *chan, uint8_t c)
{
	if (trace & TRACE_SIO)
		fprintf(stderr, "SIO %d queue %d: ", (int) (chan - sio), c);
	/* Receive disabled */
	if (!(chan->wr[3] & 1)) {
    if (trace & TRACE_SIO)
			fprintf(stderr, "RX disabled.\n");
		return;
	}
	/* Overrun */
	if (chan->dptr == 2) {
    if (trace & TRACE_INFO)
      fprintf(stderr, "SIO Input Overrun.\n");
		chan->data[2] = c;
		chan->rr[1] |= 0x20;	/* Overrun flagged */
		/* What are the rules for overrun delivery FIXME */
		sio2_raise_int(chan, INT_ERR);
	} else {
		/* FIFO add */
    chan->rxchrs++;

		if (trace & TRACE_SIO)
			fprintf(stderr, "Queued %d (mode %d)\n", chan->dptr, chan->wr[1] & 0x18);
		chan->data[chan->dptr++] = c;

    // Set character available flag (Read Reg 0)
		chan->rr[0] |= 1;
		switch (chan->wr[1] & 0x18) {
		case 0x00:
			break;
		case 0x08:
			if (chan->dptr == 1)
				sio2_raise_int(chan, INT_RX);
			break;
		case 0x10:
		case 0x18:
			sio2_raise_int(chan, INT_RX);
			break;
		}
	}
	/* Need to deal with interrupt results */
}

static void sio2_channel_timer(struct z80_sio_chan *chan, uint8_t ab)
{
  int c = chan->client->test_chr();

  /* Check status */
  if ((chan->wr[5] ^ chan->status) & SIO_RTS) {
    /* Change in RTS line status */
    if (trace & TRACE_SIO)
      fprintf(stderr, "RTS Change to: %s @%d chars\n", ((chan->wr[5] & 2) ? "Hi" : "Lo"), chan->rxchrs);
    chan->status ^= SIO_RTS;
  }
		if (sio2_input) {
    /* Read a character IF one is available AND there's room
     * in the channel input buffer
     */
    if (c & 1) {
      /* There's a character available. Ignore unless:
        *  - there's room in the channel input buffer (avoid overrun)
        *  - RTS is active (flow control)
        */
      if (chan->dptr < 2) {
        /* There's room for the input character */
        if (chan->wr[5] & SIO_RTS) {
          /* And flow control says not to block it */
          sio2_queue(chan, chan->client->get_chr());
		}
        if (chan->status & SIO_BUSY) {
          if (trace & TRACE_SIO)
            fprintf(stderr, "SIO unblocked @%d chars\n", chan->rxchrs);

          /* Clear busy flag */
          chan->status &= !SIO_BUSY;
        }
      }
      else {
        /* No space in SIO for this character so block - try again later */
        if ((trace & TRACE_SIO) && !(chan->status & SIO_BUSY))
          fprintf(stderr, "SIO full, input blocked @%d chars\n", chan->rxchrs);
        chan->status |= SIO_BUSY;
      }
    }
  }
		if (c & 2) {
    /* Ready to transmit a character */
			if (!(chan->rr[0] & 0x04)) {
				chan->rr[0] |= 0x04;
				if (chan->wr[1] & 0x02)
					sio2_raise_int(chan, INT_TX);
			}
		}
  if (chan!=sio) {
		if (!(chan->rr[0] & 0x04)) {
			chan->rr[0] |= 0x04;
			if (chan->wr[1] & 0x02)
				sio2_raise_int(chan, INT_TX);
		}
	}
}

static void sio2_timer(void) {
	sio2_channel_timer(sio, 0);
	sio2_channel_timer(sio + 1, 1);
}

static void sio2_channel_reset(struct z80_sio_chan *chan) {
	chan->rr[0] = 0x2C;
	chan->rr[1] = 0x01;
	chan->rr[2] = 0;
	sio2_clear_int(chan, INT_RX | INT_TX | INT_ERR);
}

static void sio_reset(void) {
	sio2_channel_reset(sio);
	sio2_channel_reset(sio + 1);

  /* Channel A (0) connects to the console */
  sio[0].client = &cons_chan;

  if (blk_path) {
    /* Only if the -b option specified */
    sio[1].client  = &blk_chan;
}
  else {
    sio[1].client  = &null_chan;
  }
}

static uint8_t sio2_read(uint16_t addr) {
	/* Weird mapping */
	struct z80_sio_chan *chan = (addr & 1) ? sio : sio + 1;
	if (addr & 2) {
		/* Control */
		uint8_t r = chan->wr[0] & 007;
		chan->wr[0] &= ~007;

		chan->rr[0] &= ~2;
		if (chan == sio && (sio[0].intbits | sio[1].intbits))
			chan->rr[0] |= 2;
		if (trace & TRACE_SIO)
			fprintf(stderr, "sio%c read reg %d = ", (addr & 2) ? 'b' : 'a', r);
		switch (r) {
		case 0:
		case 1:
			if (trace & TRACE_SIO)
				fprintf(stderr, "%02X\n", chan->rr[r]);
			return chan->rr[r];
		case 2:
			if (chan != sio) {
				if (trace & TRACE_SIO)
					fprintf(stderr, "%02X\n", chan->rr[2]);
				return chan->rr[2];
			}
		case 3:
			/* What does the hw report ?? */
      if (trace & TRACE_INFO)
				fprintf(stderr, "INVALID(0xFF)\n");
			return 0xFF;
		}
	} else {
		uint8_t c = chan->data[0];
		chan->data[0] = chan->data[1];
		chan->data[1] = chan->data[2];
		if (chan->dptr)
			chan->dptr--;
		if (chan->dptr == 0)
			chan->rr[0] &= 0xFE;	/* Clear RX pending */
		sio2_clear_int(chan, INT_RX);
		chan->rr[0] &= 0x3F;
		chan->rr[1] &= 0x3F;
    if (trace & TRACE_SIO) {
      if (c>32 && c<128)
        fprintf(stderr, "sio%c read data %d (%c)\n", (addr & 2) ? 'b' : 'a', c, c);
      else
			fprintf(stderr, "sio%c read data %d\n", (addr & 2) ? 'b' : 'a', c);
    }
		if (chan->dptr && (chan->wr[1] & 0x10))
			sio2_raise_int(chan, INT_RX);
		return c;
	}
	return 0xFF;
}

static void sio2_write(uint16_t addr, uint8_t val)
{
	struct z80_sio_chan *chan = (addr & 1) ? sio : sio + 1;
	uint8_t r;
	/* Weird mapping */
	if (addr & 2) {
		if (trace & TRACE_SIO)
			fprintf(stderr, "sio%c write reg %d with %02X\n", (addr & 2) ? 'b' : 'a', chan->wr[0] & 7, val);
		switch (chan->wr[0] & 007) {
		case 0:
			chan->wr[0] = val;
			/* FIXME: CRC reset bits ? */
			switch (val & 070) {
			case 000:	/* NULL */
				break;
			case 010:	/* Send Abort SDLC */
				/* SDLC specific no-op for async */
				break;
			case 020:	/* Reset external/status interrupts */
				sio2_clear_int(chan, INT_ERR);
				chan->rr[1] &= 0xCF;	/* Clear status bits on rr0 */
				break;
			case 030:	/* Channel reset */
				if (trace & TRACE_SIO)
					fprintf(stderr, "[channel reset]\n");
				sio2_channel_reset(chan);
				break;
			case 040:	/* Enable interrupt on next rx */
				chan->rxint = 1;
				break;
			case 050:	/* Reset transmitter interrupt pending */
				chan->txint = 0;
				sio2_clear_int(chan, INT_TX);
				break;
			case 060:	/* Reset the error latches */
				chan->rr[1] &= 0x8F;
				break;
			case 070:	/* Return from interrupt (channel A) */
				if (chan == sio) {
					sio->irq = 0;
					sio->rr[1] &= ~0x02;
					sio2_clear_int(sio, INT_RX | INT_TX | INT_ERR);
					sio2_clear_int(sio + 1, INT_RX | INT_TX | INT_ERR);
				}
				break;
			}
			break;
		case 1:
		case 2:
		case 3:
		case 4:
		case 5:
		case 6:
		case 7:
			r = chan->wr[0] & 7;
			if (trace & TRACE_SIO)
				fprintf(stderr, "sio%c: wrote r%d to %02X\n",
					(addr & 2) ? 'b' : 'a', r, val);
			chan->wr[r] = val;
			if (chan != sio && r == 2)
				chan->rr[2] = val;
			chan->wr[0] &= ~007;
			break;
		}
		/* Control */
	} else {
		/* Strictly we should emulate this as two bytes, one going out and
			 the visible queue - FIXME */
		/* FIXME: irq handling */
		chan->rr[0] &= ~(1 << 2);	/* Transmit buffer no longer empty */
		chan->txint = 1;
		/* Should check chan->wr[5] & 8 */
		sio2_clear_int(chan, INT_TX);
		if (trace & TRACE_SIO)
			fprintf(stderr, "sio%c write data %d\n", (addr & 2) ? 'b' : 'a', val);
    if (chan->client->write_chr!=NULL)
      chan->client->write_chr(val);
		}
	}

/*
 *	Z80 CTC
 */

struct z80_ctc {
	uint16_t count;
	uint16_t reload;
	uint8_t vector;
	uint8_t ctrl;
#define CTC_IRQ		0x80
#define CTC_COUNTER	0x40
#define CTC_PRESCALER	0x20
#define CTC_RISING	0x10
#define CTC_PULSE	0x08
#define CTC_TCONST	0x04
#define CTC_RESET	0x02
#define CTC_CONTROL	0x01
	uint8_t irq;		/* Only valid for channel 0, so we know
					 if we must wait for a RETI before doing
					 a further interrupt */
};

#define CTC_STOPPED(c)	(((c)->ctrl & (CTC_TCONST|CTC_RESET)) == (CTC_TCONST|CTC_RESET))

struct z80_ctc ctc[4];
uint8_t ctc_irqmask;

static void ctc_reset(struct z80_ctc *c)
{
	c->vector = 0;
	c->ctrl = CTC_RESET;
}

static void ctc_init(void)
{
	ctc_reset(ctc);
	ctc_reset(ctc + 1);
	ctc_reset(ctc + 2);
	ctc_reset(ctc + 3);
}

static void ctc_interrupt(struct z80_ctc *c)
{
	int i = c - ctc;
	if (c->ctrl & CTC_IRQ) {
		if (!(ctc_irqmask & (1 << i))) {
			ctc_irqmask |= 1 << i;
			recalc_interrupts();
			if (trace & TRACE_CTC)
				fprintf(stderr, "CTC %d wants to interrupt.\n", i);
		}
	}
}

static void ctc_reti(int ctcnum)
{
	if (ctc_irqmask & (1 << ctcnum)) {
		ctc_irqmask &= ~(1 << ctcnum);
		if (trace & TRACE_IRQ)
			fprintf(stderr, "Acked interrupt from CTC %d.\n", ctcnum);
	}
}

/* After a RETI or when idle compute the status of the interrupt line and
	 if we are head of the chain this time then raise our interrupt */

static int ctc_check_im2(void)
{
	if (ctc_irqmask) {
		int i;
		for (i = 0; i < 4; i++) {	/* FIXME: correct order ? */
			if (ctc_irqmask & (1 << i)) {
				uint8_t vector = ctc[0].vector & 0xF8;
				vector += 2 * i;
				if (trace & TRACE_IRQ)
					fprintf(stderr, "New live interrupt is from CTC %d vector %x.\n", i, vector);
				live_irq = IRQ_CTC + i;
				Z80INT(&cpu_z80, vector);
				return 1;
			}
		}
	}
	return 0;
}

/* Model the chains between the CTC devices */
/* TODO: DS1307 can provide a clock to the CTC */
static void ctc_pulse(int i)
{
}
#if 0
/* We don't worry about edge directions just a logical pulse model */
static void ctc_receive_pulse(int i)
{
	struct z80_ctc *c = ctc + i;
	if (c->ctrl & CTC_COUNTER) {
		if (CTC_STOPPED(c))
			return;
		if (c->count >= 0x0100)
			c->count -= 0x100;	/* No scaling on pulses */
		if ((c->count & 0xFF00) == 0) {
			ctc_interrupt(c);
			ctc_pulse(i);
			c->count = c->reload << 8;
		}
	} else {
		if (c->ctrl & CTC_PULSE)
			c->ctrl &= ~CTC_PULSE;
	}
}
#endif

/* Model counters */
static void ctc_tick(unsigned int clocks)
{
	struct z80_ctc *c = ctc;
	int i;
	int n;
	int decby;

	for (i = 0; i < 4; i++, c++) {
		/* Waiting a value */
		if (CTC_STOPPED(c))
			continue;
		/* Pulse trigger mode */
		if (c->ctrl & CTC_COUNTER)
			continue;
		/* 256x downscaled */
		decby = clocks;
		/* 16x not 256x downscale - so increase by 16x */
		if (!(c->ctrl & CTC_PRESCALER))
			decby <<= 4;
		/* Now iterate over the events. We need to deal with wraps
			 because we might have something counters chained */
		n = c->count - decby;
		while (n < 0) {
			ctc_interrupt(c);
			ctc_pulse(i);
			if (c->reload == 0)
				n += 256 << 8;
			else
				n += c->reload << 8;
		}
		c->count = n;
	}
}

static void ctc_write(uint8_t channel, uint8_t val)
{
	struct z80_ctc *c = ctc + channel;
	if (c->ctrl & CTC_TCONST) {
		if (trace & TRACE_CTC)
			fprintf(stderr, "CTC %d constant loaded with %02X\n", channel, val);
		c->reload = val;
		if ((c->ctrl & (CTC_TCONST|CTC_RESET)) == (CTC_TCONST|CTC_RESET)) {
			c->count = (c->reload - 1) << 8;
			if (trace & TRACE_CTC)
				fprintf(stderr, "CTC %d constant reloaded with %02X\n", channel, val);
		}
		c->ctrl &= ~CTC_TCONST|CTC_RESET;
	} else if (val & CTC_CONTROL) {
		/* We don't yet model the weirdness around edge wanted
			 toggling and clock starts */
		if (trace & TRACE_CTC)
			fprintf(stderr, "CTC %d control loaded with %02X\n", channel, val);
		c->ctrl = val;
		if ((c->ctrl & (CTC_TCONST|CTC_RESET)) == CTC_RESET) {
			c->count = (c->reload - 1) << 8;
			if (trace & TRACE_CTC)
				fprintf(stderr, "CTC %d constant reloaded with %02X\n", channel, val);
		}
		/* Undocumented */
		if (!(c->ctrl & CTC_IRQ) && (ctc_irqmask & (1 << channel))) {
			ctc_irqmask &= ~(1 << channel);
			if (ctc_irqmask == 0) {
				if (trace & TRACE_IRQ)
					fprintf(stderr, "CTC %d irq reset.\n", channel);
				if (live_irq == IRQ_CTC + channel)
					live_irq = 0;
			}
		}
	} else {
		if (trace & TRACE_CTC)
			fprintf(stderr, "CTC %d vector loaded with %02X\n", channel, val);
		/* Only works on channel 0 */
		if (channel == 0)
			c->vector = val;
	}
}

static uint8_t ctc_read(uint8_t channel)
{
	uint8_t val = ctc[channel].count >> 8;
	if (trace & TRACE_CTC)
		fprintf(stderr, "CTC %d reads %02x\n", channel, val);
	return val;
}

/******************* Generic I/O - SPI, I2C, memory mapper ***************/
static uint8_t bitcnt;
static uint8_t txbits, rxbits;
static uint8_t genio_txbit;
static uint8_t spi_addr;
static uint8_t spi_data;
static uint8_t i2c_clk;

static void spi_clock_high(void)
{
	txbits <<= 1;
	txbits |= spi_data;
	bitcnt++;
	if (bitcnt == 8) {
		rxbits = sd_spi_in(sdcard, txbits);
		if (trace & TRACE_SPI)
			fprintf(stderr, "spi %02X | %02X\n", rxbits, txbits);
		bitcnt = 0;
	}
}

static void spi_clock_low(void)
{
	genio_txbit = (rxbits & 0x80) ? 1 : 0;
	rxbits <<= 1;
	rxbits |= 1;
}

static void genio_write(uint16_t addr, uint8_t val)
{
	uint8_t delta = genio_data ^ val;
	genio_data = val;
	if (delta & 4) {
    /* SPI1 (SDCard 1) chip select line */
		if (genio_data & 4)
			sd_spi_lower_cs(sdcard);
		else
			sd_spi_raise_cs(sdcard);
	}
	/* I2C clock or data change. Provide new driven bits to bus */
	if ((delta & 2) || (addr & 1) != i2c_clk) {
		unsigned n = 0;
		i2c_clk = addr  & 1;
		/* The i2c bus interface and genio bits are not the same */
		if (val & 2)
			n |= I2C_DATA;
		if (i2c_clk)
			n |= I2C_CLK;
		i2c_write(i2cbus, n);
	}
}

/* genio_read - port 64h input. Show
 * SDCard 0 as having a card present,
 * SDCard 1 as absent
 */
static uint8_t genio_read(uint16_t addr) {
  return dip_switch | 0x08 | (i2c_read(i2cbus) << 1) | (genio_data & 0x04) | genio_txbit;
}

static void spi_write(uint16_t addr, uint8_t val)
{
	uint8_t delta = spi_addr ^ addr;
	spi_addr = addr & 1;
	spi_data = val & 1;
	if (delta & 1) {
		if (spi_addr)
			spi_clock_high();
		else
			spi_clock_low();
	}
}

uint8_t io_read(int unused, uint16_t addr)
{
	if (trace & TRACE_IO)
		fprintf(stderr, "read %02x\n", addr);
	addr &= 0xFF;

	if (addr >= 0x80 && addr <= 0x87)
		return sio2_read(addr & 3);
	if (addr >= 0x40 && addr <= 0x43)
		return ctc_read(addr & 3);
	if (addr >= 0x64 && addr <= 0x65)
		return genio_read(addr);
	if (trace & TRACE_UNK)
		fprintf(stderr, "Unknown read from port %04X\n", addr);
	return 0xFF;	/* FF is what my actual board floats at */
}

void io_write(int unused, uint16_t addr, uint8_t val)
{
	if (trace & TRACE_IO)
		fprintf(stderr, "write %02x <- %02x\n", addr, val);
	addr &= 0xFF;
	if (addr >= 0x80 && addr <= 0x87)
		sio2_write(addr & 3, val);
	else if (addr >= 0x60 && addr <= 0x63) {
		if (trace & TRACE_BANK)
      fprintf(stderr, "Bank %d set to %02X before: [%02X %02X %02X %02X]\n", addr & 3, val,
				bankreg[0], bankreg[1], bankreg[2], bankreg[3]);
    bankreg[addr & 3] = val;
	}
	else if (addr >= 0x40 && addr <= 0x43)
		ctc_write(addr & 3, val);
	else if (addr >= 0x64 && addr <= 0x67)
		genio_write(addr, val);
	else if (addr >= 0x68 && addr <= 0x6B)
		spi_write(addr, val);
	else if (addr == 0xFD) {
		trace &= 0xFF00;
		trace |= val;
		fprintf(stderr, "trace set to %04X\n", trace);
	} else if (addr == 0xFE) {
		trace &= 0xFF;
		trace |= val << 8;
		printf("trace set to %d\n", trace);
	} else if (trace & TRACE_UNK)
		fprintf(stderr, "Unknown write to port %04X of %02X\n", addr, val);
}

/* Change any generic I/O registers that are affected by a reset */
void io_reset() {
  bankreg[0]  =  bankreg[1] = bankreg[2] = bankreg[3] = 0;
  genio_data &= ~1;   /* MMU off */
}

static void poll_irq_event(void)
{
	if (!live_irq)
		if (!sio2_check_im2(sio))
						if (!sio2_check_im2(sio + 1))
				ctc_check_im2();
	/* TODO: PIO */
}

static void reti_event(void)
{
	if (live_irq && (trace & TRACE_IRQ))
		fprintf(stderr, "RETI\n");
	switch(live_irq) {
	case IRQ_SIOA:
		sio2_reti(sio);
		break;
	case IRQ_SIOB:
		sio2_reti(sio + 1);
		break;
	case IRQ_CTC:
	case IRQ_CTC + 1:
	case IRQ_CTC + 2:
	case IRQ_CTC + 3:
		ctc_reti(live_irq - IRQ_CTC);
		break;
	}
	live_irq = 0;
	poll_irq_event();
}

static struct termios saved_term, term;

static void cleanup(int sig)
{
  if (nvpath!=NULL)
    rtc_save(rtcdev, nvpath);

  if (sdcard!=NULL)
		sd_detach(sdcard);

	tcsetattr(0, TCSADRAIN, &saved_term);
	emulator_done = 1;
}

static void exit_cleanup(void)
{
	tcsetattr(0, TCSADRAIN, &saved_term);
}

static void usage(void)
{
	fprintf(stderr,
		"z80retro: [-b cpath] [-c config] [-r rompath] [-S sdpath] [-N nvpath] [-f] [-d debug]\n"
			"   config:  State of DIP switches (0-7)\n"
			"   rompath: 512K binary file\n"
      "   cpath:   Path to directory holding files to serve over SIO port B\n"
			"   sdpath:  Path to file containing SDCard data\n"
			"   debug:   Comma separated list of: MEM,IO,INFO,UNK,CPU,BANK,SIO,CTC,IRQ,SPI,SD,I2C,RTC\n"
			"   nvpath:  file to store DS1307+ RTC non-volatile memory\n"
		"If -b is specified then the emulator runs a file server function allowing the\n"
          "Z80 to download files directly from the host computer.");
  exit(EXIT_FAILURE);
}


/**/
static const char *tokens[] =
  {"MEM", "IO", "ROM", "UNK", "CPU", "BANK", "SIO", "CTC", "IRQ", "SPI", "SD", "I2C", "RTC", "CMD", "INFO", NULL};

static void trace_on(const char *token)
{
  uint16_t code=1; //, cnt=0;
  const char **tptr = tokens;
  while (*tptr!=NULL) {
    if (strcasecmp(token, *tptr)==0) {
      trace |= code;
      return;
    }
    tptr++;
    code <<= 1;
  }
}

/* parse_trace
 * Parse the value of provided with the -d run time option. This
 * is either a number or a string. If a number then it's decimal
 * and is used to set the literal value of the trace register. If
 * it's a string then treat it as a comma separated list and break
 * into tokens. Each token is the name of a trace flag to switch
 * on.
 * */
static void parse_trace(const char *str)
{

  /* If str looks like a number then literal trace value */
  if (str[0]>='0' && str[1]<='9') {
    trace = atoi(str);
    return;
  }

  char *args = strdup(str);
  char *toklst, *token;

  fprintf(stderr, "Trace flags: %s\n", args);
  if (args==NULL) {
    fprintf(stderr, "Out of memory\n");
    exit(EXIT_FAILURE);
  }
  toklst = args;
  while ((token = strsep(&toklst,","))!=NULL)
    trace_on(token);

  free(args);
}

/* make_sd
 * Only used for SDCard 0 but could be called a second time to
 * emulate the second SDCard. This would only require a little
 * logic in the genio area to direct calls to the right card.
 */
static struct sdcard *make_sd(const char *name, const char *path)
{
struct sdcard *card = sd_create(name);
int fd;

	if (path) {
		fd = open(path, O_RDWR);
		if (fd == -1) {
			perror(path);
			exit(1);
		}
		sd_attach(card, fd);
	}

	sd_trace(card, (trace & TRACE_SD) != 0);

	return card;
}

/* sys_reset
 * Simulates the hardware reset button being pressed. Called
 * when the emulator receives a HUP signal. Note that i2c/SPI
 * devices aren't connected to the reset line so aren't reset.
 */
static void sys_reset()
{
  fprintf(stderr, "Hardware RESET\n");
  Z80RESET(&cpu_z80);
  io_reset();
  sio_reset();
  ctc_init();
}

int main(int argc, char *argv[])
{
	static struct timespec tc;
	int opt;
	int fd;
	char *rompath = "z80retro.rom";
	char *nvpath = "z80retrom.nvram";
	char *sdpath = NULL;

  while ((opt = getopt(argc, argv, "b:c:d:fr:S:N:")) != -1) {
		switch (opt) {
    case 'b':
      blk_path = optarg;
      break;
		case 'r':
			rompath = optarg;
			break;
		case 'S':
			sdpath = optarg;
			break;
		case 'N':
			nvpath = optarg;
			break;
    case 'd':
      parse_trace(optarg);
      break;
		case 'c':
			/* State of the 3 DIP switches used for configuration,
			 * shifted to the right place in  */
			dip_switch = (atoi(optarg) & 0x7) << 5;
			break;
		case 'f':
			fast = 1;
			break;
		default:
			usage();
		}
	}
	if (optind < argc)
		usage();

  /* Identify read/write pages */
  for (int p=0x20;p<0x40;p++)
    pages[p] = READABLE | WRITEABLE;

  /* And read only (flash) pages */
  for (int p=0;p<0x20;p++)
    pages[p] = READABLE;

	fd = open(rompath, O_RDONLY);
	if (fd == -1) {
		perror(rompath);
		exit(EXIT_FAILURE);
	}

	if (read(fd, &ramrom[0], 524288) != 524288) {
		fprintf(stderr, "z80retro: banked rom image should be 512K.\n");
		exit(EXIT_FAILURE);
	}
	close(fd);

	sdcard = make_sd("sd0", sdpath);

	i2cbus = i2c_create();
	i2c_trace(i2cbus, (trace & TRACE_I2C) != 0);

	rtcdev = rtc_create(i2cbus);
	rtc_trace(rtcdev, (trace & TRACE_RTC) != 0);
	rtc_load(rtcdev, nvpath);

	sio_reset();
	ctc_init();
	sio2_input = 1;

	/* 2.5ms - it's a balance between nice behaviour and simulation
		 smoothness */
	tc.tv_sec = 0;
	tc.tv_nsec = 20000000L;

	if (tcgetattr(0, &term) == 0) {
		saved_term = term;
		atexit(exit_cleanup);
		signal(SIGINT, cleanup);
    signal(SIGTERM, cleanup);
		signal(SIGQUIT, cleanup);
		signal(SIGPIPE, cleanup);
    signal(SIGHUP, sys_reset);
		term.c_lflag &= ~(ICANON | ECHO);
		term.c_cc[VMIN] = 0;
		term.c_cc[VTIME] = 1;
		term.c_cc[VINTR] = 0;
		term.c_cc[VSUSP] = 0;
		term.c_cc[VSTOP] = 0;
		tcsetattr(0, TCSADRAIN, &term);
	}

	Z80RESET(&cpu_z80);
	cpu_z80.ioRead = io_read;
	cpu_z80.ioWrite = io_write;
	cpu_z80.memRead = mem_read;
	cpu_z80.memWrite = mem_write;
	cpu_z80.trace = z80_trace;

	/* This is the wrong way to do it but it's easier for the moment. We
		 should track how much real time has occurred and try to keep cycle
		 matched with that. The scheme here works fine except when the host
		 is loaded though */

	/* We run 7372000 t-states per second */
	/* We run 365 cycles per I/O check, do that 50 times then poll the
		 slow stuff and nap for 20ms to get 50Hz on the TMS99xx */
	while (!emulator_done) {
		if (cpu_z80.halted && ! cpu_z80.IFF1) {
			/* HALT with interrupts disabled, so nothing left
				 to do, so exit simulation. If NMI was supported,
				 this might have to change. */
			emulator_done = 1;
			break;
		}
		int i;
		/* 36400 T states for base RC2014 - varies for others */
		for (i = 0; i < 40; i++) {
			int j;
			for (j = 0; j < 100; j++) {
				Z80ExecuteTStates(&cpu_z80, (tstate_steps + 5)/ 10);
				sio2_timer();
			}
			ctc_tick(tstate_steps);
			/* We want to run UI events regularly it seems */
		}

		/* Do 20ms of I/O and delays */
		if (!fast)
			nanosleep(&tc, NULL);
		if (int_recalc) {
			/* If there is no pending Z80 vector IRQ but we think
				 there now might be one we use the same logic as for
				 reti */
			if (!live_irq)
				poll_irq_event();
			/* Clear this after because reti_event may set the
				 flags to indicate there is more happening. We will
				 pick up the next state changes on the reti if so */
			if (!(cpu_z80.IFF1|cpu_z80.IFF2))
				int_recalc = 0;
		}
	}
	if (nvpath!=NULL)
		rtc_save(rtcdev, nvpath);
	exit(0);
}
