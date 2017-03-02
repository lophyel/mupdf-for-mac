#include "mupdf/html.h"

enum { T, R, B, L };

typedef struct html_document_s html_document;
typedef struct html_page_s html_page;

struct html_document_s
{
	fz_document super;
	fz_archive *zip;
	fz_html_font_set *set;
	float page_w, page_h, em;
	float page_margin[4];
	fz_html *html;
};

struct html_page_s
{
	fz_page super;
	html_document *doc;
	int number;
};

static void
htdoc_drop_document(fz_context *ctx, fz_document *doc_)
{
	html_document *doc = (html_document*)doc_;
	fz_drop_archive(ctx, doc->zip);
	fz_drop_html(ctx, doc->html);
	fz_drop_html_font_set(ctx, doc->set);
}

static int
htdoc_resolve_link(fz_context *ctx, fz_document *doc_, const char *dest, float *xp, float *yp)
{
	html_document *doc = (html_document*)doc_;
	const char *s = strchr(dest, '#');
	if (s && s[1] != 0)
	{
		float y = fz_find_html_target(ctx, doc->html, s+1);
		if (y >= 0)
		{
			int page = y / doc->page_h;
			if (yp) *yp = y - page * doc->page_h;
			return page;
		}
	}

	return -1;
}

static int
htdoc_count_pages(fz_context *ctx, fz_document *doc_)
{
	html_document *doc = (html_document*)doc_;
	int count = ceilf(doc->html->root->h / doc->page_h);
	return count;
}

static void
htdoc_layout(fz_context *ctx, fz_document *doc_, float w, float h, float em)
{
	html_document *doc = (html_document*)doc_;

	if (doc->html && doc->html->root)
	{
		doc->page_margin[T] = fz_from_css_number(doc->html->root->style.margin[T], em, em);
		doc->page_margin[B] = fz_from_css_number(doc->html->root->style.margin[B], em, em);
		doc->page_margin[L] = fz_from_css_number(doc->html->root->style.margin[L], em, em);
		doc->page_margin[R] = fz_from_css_number(doc->html->root->style.margin[R], em, em);
	}

	doc->page_w = w - doc->page_margin[L] - doc->page_margin[R];
	doc->page_h = h - doc->page_margin[T] - doc->page_margin[B];
	doc->em = em;

	fz_layout_html(ctx, doc->html, doc->page_w, doc->page_h, doc->em);
}

static void
htdoc_drop_page(fz_context *ctx, fz_page *page_)
{
}

static fz_rect *
htdoc_bound_page(fz_context *ctx, fz_page *page_, fz_rect *bbox)
{
	html_page *page = (html_page*)page_;
	html_document *doc = page->doc;
	bbox->x0 = 0;
	bbox->y0 = 0;
	bbox->x1 = doc->page_w + doc->page_margin[L] + doc->page_margin[R];
	bbox->y1 = doc->page_h + doc->page_margin[T] + doc->page_margin[B];
	return bbox;
}

static void
htdoc_run_page(fz_context *ctx, fz_page *page_, fz_device *dev, const fz_matrix *ctm, fz_cookie *cookie)
{
	html_page *page = (html_page*)page_;
	html_document *doc = page->doc;
	fz_matrix local_ctm = *ctm;
	int n = page->number;

	fz_pre_translate(&local_ctm, doc->page_margin[L], doc->page_margin[T]);

	fz_draw_html(ctx, dev, &local_ctm, doc->html, n * doc->page_h, (n+1) * doc->page_h);
}

static fz_link *
htdoc_load_links(fz_context *ctx, fz_page *page_)
{
	html_page *page = (html_page*)page_;
	html_document *doc = page->doc;
	fz_link *head, *link;

	head = fz_load_html_links(ctx, doc->html, page->number, doc->page_h, "");
	for (link = head; link; link = link->next)
	{
		link->doc = doc;

		/* Adjust for page margins */
		link->rect.x0 += doc->page_margin[L];
		link->rect.x1 += doc->page_margin[L];
		link->rect.y0 += doc->page_margin[T];
		link->rect.y1 += doc->page_margin[T];
	}
	return head;
}

static fz_page *
htdoc_load_page(fz_context *ctx, fz_document *doc_, int number)
{
	html_document *doc = (html_document*)doc_;
	html_page *page = fz_new_page(ctx, sizeof *page);
	page->super.bound_page = htdoc_bound_page;
	page->super.run_page_contents = htdoc_run_page;
	page->super.load_links = htdoc_load_links;
	page->super.drop_page = htdoc_drop_page;
	page->doc = doc;
	page->number = number;
	return (fz_page*)page;
}

int
htdoc_lookup_metadata(fz_context *ctx, fz_document *doc_, const char *key, char *buf, int size)
{
	if (!strcmp(key, "format"))
		return (int)fz_strlcpy(buf, "XHTML", size);
	return -1;
}

static fz_document *
htdoc_open_document_with_stream(fz_context *ctx, fz_stream *file)
{
	html_document *doc;
	fz_buffer *buf;

	doc = fz_new_document(ctx, html_document);

	doc->super.drop_document = htdoc_drop_document;
	doc->super.layout = htdoc_layout;
	doc->super.resolve_link = htdoc_resolve_link;
	doc->super.count_pages = htdoc_count_pages;
	doc->super.load_page = htdoc_load_page;
	doc->super.lookup_metadata = htdoc_lookup_metadata;
	doc->super.is_reflowable = 1;

	doc->zip = fz_open_directory(ctx, ".");
	doc->set = fz_new_html_font_set(ctx);

	buf = fz_read_all(ctx, file, 0);

	fz_try(ctx)
	{
		fz_write_buffer_byte(ctx, buf, 0);
		doc->html = fz_parse_html(ctx, doc->set, doc->zip, ".", buf, fz_user_css(ctx));
	}
	fz_always(ctx)
		fz_drop_buffer(ctx, buf);
	fz_catch(ctx)
		fz_rethrow(ctx);

	return (fz_document*)doc;
}

static fz_document *
htdoc_open_document(fz_context *ctx, const char *filename)
{
	char dirname[2048];
	fz_buffer *buf;
	html_document *doc;

	fz_dirname(dirname, filename, sizeof dirname);

	doc = fz_new_document(ctx, html_document);
	doc->super.drop_document = htdoc_drop_document;
	doc->super.layout = htdoc_layout;
	doc->super.resolve_link = htdoc_resolve_link;
	doc->super.count_pages = htdoc_count_pages;
	doc->super.load_page = htdoc_load_page;
	doc->super.lookup_metadata = htdoc_lookup_metadata;
	doc->super.is_reflowable = 1;

	doc->zip = fz_open_directory(ctx, dirname);
	doc->set = fz_new_html_font_set(ctx);

	buf = fz_read_file(ctx, filename);

	fz_try(ctx)
	{
		fz_write_buffer_byte(ctx, buf, 0);
		doc->html = fz_parse_html(ctx, doc->set, doc->zip, ".", buf, fz_user_css(ctx));
	}
	fz_always(ctx)
		fz_drop_buffer(ctx, buf);
	fz_catch(ctx)
		fz_rethrow(ctx);

	return (fz_document*)doc;
}

static int
htdoc_recognize(fz_context *doc, const char *magic)
{
	char *ext = strrchr(magic, '.');

	if (ext)
	{
		if (!fz_strcasecmp(ext, ".xml") || !fz_strcasecmp(ext, ".xhtml") ||
				!fz_strcasecmp(ext, ".html") || !fz_strcasecmp(ext, ".htm") ||
				!fz_strcasecmp(ext, ".fb2"))
			return 100;
	}
	if (!strcmp(magic, "application/html+xml") || !strcmp(magic, "application/xml") || !strcmp(magic, "text/xml"))
		return 100;
	return 0;
}

fz_document_handler html_document_handler =
{
	&htdoc_recognize,
	&htdoc_open_document,
	&htdoc_open_document_with_stream
};
