use clap::{App, Arg, ArgMatches, SubCommand};
use mdbook::book::{Book, BookItem};
use mdbook::errors::Error;
use mdbook::preprocess::{CmdPreprocessor, Preprocessor, PreprocessorContext};
use pulldown_cmark::{CowStr, Event, Options, Parser, Tag};
use pulldown_cmark_to_cmark::fmt::cmark;
use regex::Regex;
use std::io;
use std::process;
use svgbob::to_svg;

pub struct SvgBobber;

impl SvgBobber {
    pub fn new() -> Self {
        SvgBobber
    }
}

fn process_content(s: &String) -> Result<String, Error> {
    let mut buf = String::with_capacity(s.len());
    let mut in_code = false;
    let options = Options::empty();
    let events = Parser::new_ext(&*s, options).filter_map(|e| match e {
        Event::Start(Tag::CodeBlock(s)) => {
            let s = s.into_string();
            if let "bob" = &*s {
                in_code = true;
                None
            } else {
                Some(Event::Start(Tag::CodeBlock(CowStr::Boxed(
                    s.into_boxed_str(),
                ))))
            }
        }
        Event::End(Tag::CodeBlock(_)) => {
            if in_code {
                in_code = false;
                None
            } else {
                Some(e)
            }
        }
        Event::Text(s) => {
            if in_code {
                let s: String = format!("{}", to_svg(&*s.into_string()));
                let re = Regex::new("\n\\s*\n").unwrap();
                let result = format!("{}\n\n", re.replace_all(&s, "\n"));
                Some(Event::Html(CowStr::Boxed(result.into_boxed_str())))
            } else {
                Some(Event::Text(s))
            }
        }
        _ => Some(e),
    });

    cmark(events, &mut buf, None)
        .map(|_| buf)
        .map_err(|err| Error::from(format!("Markdown serialization failed: {}", err)))
}

fn process_bobs(item: &mut BookItem) -> () {
    match item {
        BookItem::Separator => (),
        BookItem::Chapter(c) => c.content = process_content(&c.content).unwrap(),
    }
}

impl Preprocessor for SvgBobber {
    fn name(&self) -> &str {
        "mdbook-svgbob-processor"
    }

    fn run(&self, _ctx: &PreprocessorContext, mut book: Book) -> Result<Book, Error> {
        book.for_each_mut(process_bobs);

        Ok(book)
    }

    fn supports_renderer(&self, renderer: &str) -> bool {
        renderer != "not-supported"
    }
}

pub fn make_app() -> App<'static, 'static> {
    App::new("mdbook-svgbob-processor")
        .about("A mdbook preprocessor which runs svgbob on bob diagrams")
        .subcommand(
            SubCommand::with_name("supports")
                .arg(Arg::with_name("renderer").required(true))
                .about("Check whether a renderer is supported by this preprocessor"),
        )
}

fn handle_preprocessing(pre: &dyn Preprocessor) -> Result<(), Error> {
    let (ctx, book) = CmdPreprocessor::parse_input(io::stdin())?;

    if ctx.mdbook_version != mdbook::MDBOOK_VERSION {
        // probably better to use the `semver` crate to check compatibility
        eprintln!(
            "Warning: The {} plugin was built against version {} of mdbook, \
             but we're being called from version {}",
            pre.name(),
            mdbook::MDBOOK_VERSION,
            ctx.mdbook_version
        );
    }

    let processed_book = pre.run(&ctx, book)?;
    serde_json::to_writer(io::stdout(), &processed_book)?;

    Ok(())
}

fn handle_supports(pre: &dyn Preprocessor, sub_args: &ArgMatches) -> ! {
    let renderer = sub_args.value_of("renderer").expect("Required argument");
    let supported = pre.supports_renderer(&renderer);

    // Signal whether the renderer is supported by exiting with 1 or 0.
    if supported {
        process::exit(0);
    } else {
        process::exit(1);
    }
}

fn main() {
    let matches = make_app().get_matches();

    // Users will want to construct their own preprocessor here
    let preprocessor = SvgBobber::new();

    if let Some(sub_args) = matches.subcommand_matches("supports") {
        handle_supports(&preprocessor, sub_args);
    } else if let Err(e) = handle_preprocessing(&preprocessor) {
        eprintln!("{}", e);
        process::exit(1);
    }
}
