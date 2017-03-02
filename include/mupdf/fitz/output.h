#ifndef MUPDF_FITZ_OUTPUT_H
#define MUPDF_FITZ_OUTPUT_H

#include "mupdf/fitz/system.h"
#include "mupdf/fitz/context.h"
#include "mupdf/fitz/buffer.h"
#include "mupdf/fitz/string.h"

/*
	Generic output streams - generalise between outputting to a file,
	a buffer, etc.
*/
typedef struct fz_output_s fz_output;

struct fz_output_s
{
	void *opaque;
	void (*write)(fz_context *, void *opaque, const void *, size_t n);
	void (*seek)(fz_context *, void *opaque, fz_off_t off, int whence);
	fz_off_t (*tell)(fz_context *, void *opaque);
	void (*close)(fz_context *, void *opaque);
};

/*
	fz_new_output_with_file: Open an output stream that writes to a FILE *.
	fz_new_output_with_path: Open an output stream that writes to a file.
	fz_new_output_with_buffer: Open an output stream that writes into a buffer.
*/
fz_output *fz_new_output_with_file_ptr(fz_context *, FILE *, int close);
fz_output *fz_new_output_with_path(fz_context *, const char *filename, int append);
fz_output *fz_new_output_with_buffer(fz_context *, fz_buffer *);

/*
	fz_stdout: The standard out output stream.
	fz_stderr: The standard error output stream.
	fz_set_stdout: Replace default standard output stream with a new stream.
	fz_set_stderr: Replace default standard error stream with a new stream.
*/
fz_output *fz_stdout(fz_context *);
fz_output *fz_stderr(fz_context *);
void fz_set_stdout(fz_context *ctx, fz_output *out);
void fz_set_stderr(fz_context *ctx, fz_output *err);

/*
	fz_write: fwrite equivalent for output streams.
	fz_printf: fprintf equivalent for output streams. See fz_snprintf.
	fz_vprintf: vfprintf equivalent for output streams. See fz_vsnprintf.
	fz_puts: fputs equivalent for output streams.
	fz_putc: fputc equivalent for output streams.
	fz_putrune: fputrune equivalent for output streams.
*/
void fz_printf(fz_context *ctx, fz_output *out, const char *fmt, ...);
void fz_vprintf(fz_context *ctx, fz_output *out, const char *fmt, va_list ap);
#define fz_puts(C,O,S) fz_write(C, O, (S), strlen(S))
#define fz_putc(C,O,B) fz_write_byte(C, O, B)
#define fz_putrune(C,O,R) fz_write_rune(C, O, R)

/*
	fz_seek_output: Seek to the specified file position. Throw an error on unseekable outputs.
	fz_tell_output: Return the current file position. Throw an error on unseekable outputs.
*/
void fz_seek_output(fz_context *ctx, fz_output *out, fz_off_t off, int whence);
fz_off_t fz_tell_output(fz_context *ctx, fz_output *out);

/*
	fz_drop_output: Close and free an output stream.
*/
void fz_drop_output(fz_context *, fz_output *);

/*
	fz_write: Write data to output.
*/

static inline void fz_write(fz_context *ctx, fz_output *out, const void *data, size_t size)
{
	if (out)
		out->write(ctx, out->opaque, data, size);
}

/*
	fz_write_int32be: Write a big-endian 32-bit binary integer.
	fz_write_int32le: Write a little-endian 32-bit binary integer.
	fz_write_byte: Write a single byte.
	fz_write_rune: Write a UTF-8 encoded unicode character.
*/

static inline void fz_write_int32_be(fz_context *ctx, fz_output *out, int x)
{
	char data[4];

	data[0] = x>>24;
	data[1] = x>>16;
	data[2] = x>>8;
	data[3] = x;

	fz_write(ctx, out, data, 4);
}

static inline void fz_write_int32_le(fz_context *ctx, fz_output *out, int x)
{
	char data[4];

	data[0] = x;
	data[1] = x>>8;
	data[2] = x>>16;
	data[3] = x>>24;

	fz_write(ctx, out, data, 4);
}

static inline void fz_write_int16_le(fz_context *ctx, fz_output *out, int x)
{
	char data[2];

	data[0] = x;
	data[1] = x>>8;

	fz_write(ctx, out, data, 2);
}

static inline void fz_write_byte(fz_context *ctx, fz_output *out, unsigned char x)
{
	fz_write(ctx, out, &x, 1);
}

static inline void fz_write_rune(fz_context *ctx, fz_output *out, int rune)
{
	char data[10];
	fz_write(ctx, out, data, fz_runetochar(data, rune));
}

/*
	fz_vsnprintf: Our customised vsnprintf routine. Takes %c, %d, %o, %s, %u, %x, as usual.
	Modifiers are not supported except for zero-padding ints (e.g. %02d, %03o, %04x, etc).
	%f and %g both output in "as short as possible hopefully lossless non-exponent" form,
	see fz_ftoa for specifics.
	%C outputs a utf8 encoded int.
	%M outputs a fz_matrix*. %R outputs a fz_rect*. %P outputs a fz_point*.
	%q and %( output escaped strings in C/PDF syntax.
	%ll{d,u,x} indicates that the values are 64bit.
	%z{d,u,x} indicates that the value is a size_t.
	%Z{d,u,x} indicates that the value is a fz_off_t.
*/
size_t fz_vsnprintf(char *buffer, size_t space, const char *fmt, va_list args);
size_t fz_snprintf(char *buffer, size_t space, const char *fmt, ...);

/*
	fz_tempfilename: Get a temporary filename based upon 'base'.

	'hint' is the path of a file (normally the existing document file)
	supplied to give the function an idea of what directory to use. This
	may or may not be used depending on the implementations whim.

	The returned path must be freed.
*/
char *fz_tempfilename(fz_context *ctx, const char *base, const char *hint);

/*
	fz_save_buffer: Save contents of a buffer to file.
*/
void fz_save_buffer(fz_context *ctx, fz_buffer *buf, const char *filename);

/*
	fz_band_writer
*/
typedef struct fz_band_writer_s fz_band_writer;

typedef void (fz_write_header_fn)(fz_context *ctx, fz_band_writer *writer);
typedef void (fz_write_band_fn)(fz_context *ctx, fz_band_writer *writer, int stride, int band_start, int band_height, const unsigned char *samples);
typedef void (fz_write_trailer_fn)(fz_context *ctx, fz_band_writer *writer);
typedef void (fz_drop_band_writer_fn)(fz_context *ctx, fz_band_writer *writer);

struct fz_band_writer_s
{
	fz_drop_band_writer_fn *drop;
	fz_write_header_fn *header;
	fz_write_band_fn *band;
	fz_write_trailer_fn *trailer;
	fz_output *out;
	int w;
	int h;
	int n;
	int alpha;
	int xres;
	int yres;
	int pagenum;
};

fz_band_writer *fz_new_band_writer_of_size(fz_context *ctx, size_t size, fz_output *out);
#define fz_new_band_writer(C,M,O) ((M *)Memento_label(fz_new_band_writer_of_size(ctx, sizeof(M), O), #M))
void fz_write_header(fz_context *ctx, fz_band_writer *writer, int w, int h, int n, int alpha, int xres, int yres, int pagenum);
void fz_write_band(fz_context *ctx, fz_band_writer *writer, int stride, int band_start, int band_height, const unsigned char *samples);
void fz_write_trailer(fz_context *ctx, fz_band_writer *writer);
void fz_drop_band_writer(fz_context *ctx, fz_band_writer *writer);

#endif
