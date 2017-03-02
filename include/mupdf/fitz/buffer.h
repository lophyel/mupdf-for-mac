#ifndef MUPDF_FITZ_BUFFER_H
#define MUPDF_FITZ_BUFFER_H

#include "mupdf/fitz/system.h"
#include "mupdf/fitz/context.h"

/*
	fz_buffer is a wrapper around a dynamically allocated array of bytes.

	Buffers have a capacity (the number of bytes storage immediately
	available) and a current size.
*/
typedef struct fz_buffer_s fz_buffer;

/*
	fz_keep_buffer: Increment the reference count for a buffer.

	buf: The buffer to increment the reference count for.

	Returns a pointer to the buffer. Does not throw exceptions.
*/
fz_buffer *fz_keep_buffer(fz_context *ctx, fz_buffer *buf);

/*
	fz_drop_buffer: Decrement the reference count for a buffer.

	buf: The buffer to decrement the reference count for.
*/
void fz_drop_buffer(fz_context *ctx, fz_buffer *buf);

/*
	fz_buffer_storage: Retrieve information on the storage currently used
	by a buffer.

	data: Pointer to place to retrieve data pointer.

	Returns length of stream.
*/
size_t fz_buffer_storage(fz_context *ctx, fz_buffer *buf, unsigned char **data);

/*
	fz_string_from_buffer: Ensure that a buffers data ends in a
	0 byte, and return a pointer to it.

	Returns pointer to data.
*/
const char *fz_string_from_buffer(fz_context *ctx, fz_buffer *buf);

/*
	fz_new_buffer: Create a new buffer.

	capacity: Initial capacity.

	Returns pointer to new buffer. Throws exception on allocation
	failure.
*/
fz_buffer *fz_new_buffer(fz_context *ctx, size_t capacity);

/*
	fz_new_buffer_from_data: Create a new buffer with existing data.

	data: Pointer to existing data.
	size: Size of existing data.

	Takes ownership of data. Does not make a copy. Calls fz_free on the
	data when the buffer is deallocated. Do not use 'data' after passing
	to this function.

	Returns pointer to new buffer. Throws exception on allocation
	failure.
*/
fz_buffer *fz_new_buffer_from_data(fz_context *ctx, unsigned char *data, size_t size);

/*
	fz_new_buffer_from_shared_data: Like fz_new_buffer, but does not take ownership.
*/
fz_buffer *fz_new_buffer_from_shared_data(fz_context *ctx, const char *data, size_t size);

/*
	fz_new_buffer_from_base64: Create a new buffer with data decoded from a base64 input string.
*/
fz_buffer *fz_new_buffer_from_base64(fz_context *ctx, const char *data, size_t size);

/*
	fz_resize_buffer: Ensure that a buffer has a given capacity,
	truncating data if required.

	buf: The buffer to alter.

	capacity: The desired capacity for the buffer. If the current size
	of the buffer contents is smaller than capacity, it is truncated.

*/
void fz_resize_buffer(fz_context *ctx, fz_buffer *buf, size_t capacity);

/*
	fz_grow_buffer: Make some space within a buffer (i.e. ensure that
	capacity > size).

	buf: The buffer to grow.

	May throw exception on failure to allocate.
*/
void fz_grow_buffer(fz_context *ctx, fz_buffer *buf);

/*
	fz_trim_buffer: Trim wasted capacity from a buffer.

	buf: The buffer to trim.
*/
void fz_trim_buffer(fz_context *ctx, fz_buffer *buf);

/*
	fz_append_buffer: Concatenate buffers

	buf: first to concatenate and the holder of the result
	extra: second to concatenate

	May throw exception on failure to allocate.
*/
void fz_append_buffer(fz_context *ctx, fz_buffer *buf, fz_buffer *extra);

/*
	fz_write_buffer*: write to a buffer.
	fz_buffer_printf: print formatted to a buffer.
	fz_buffer_print_pdfstring: Print a string using PDF syntax and escapes.
	The buffer will grow as required.
*/
void fz_write_buffer(fz_context *ctx, fz_buffer *buf, const void *data, size_t len);
void fz_write_buffer_byte(fz_context *ctx, fz_buffer *buf, int val);
void fz_write_buffer_rune(fz_context *ctx, fz_buffer *buf, int val);
void fz_write_buffer_int32_le(fz_context *ctx, fz_buffer *buf, int x);
void fz_write_buffer_int16_le(fz_context *ctx, fz_buffer *buf, int x);
void fz_write_buffer_bits(fz_context *ctx, fz_buffer *buf, int val, int bits);
void fz_write_buffer_pad(fz_context *ctx, fz_buffer *buf);
size_t fz_buffer_printf(fz_context *ctx, fz_buffer *buffer, const char *fmt, ...);
size_t fz_buffer_vprintf(fz_context *ctx, fz_buffer *buffer, const char *fmt, va_list args);
void fz_buffer_print_pdf_string(fz_context *ctx, fz_buffer *buffer, const char *text);

/*
	fz_md5_buffer: create MD5 digest of buffer contents.
*/
void fz_md5_buffer(fz_context *ctx, fz_buffer *buffer, unsigned char digest[16]);

/*
	fz_buffer_extract: Take ownership of buffer contents.
	Performs the same task as fz_buffer_storage, but ownership of
	the data buffer returns with this call. The buffer is left
	empty.

	Note: Bad things may happen if this is called on a buffer with
	multiple references that is being used from multiple threads.

	data: Pointer to place to retrieve data pointer.

	Returns length of stream.
*/
size_t fz_buffer_extract(fz_context *ctx, fz_buffer *buf, unsigned char **data);


#endif
