use clap::{App, Arg, ArgMatches, SubCommand};
use mdbook::book::{Book, BookItem};
use mdbook::errors::Error;
use mdbook::preprocess::{CmdPreprocessor, Preprocessor, PreprocessorContext};
use std::io;
use std::process;

pub struct MathFixer;

impl MathFixer {
    pub fn new() -> Self {
        MathFixer
    }
}

pub enum ViewMode {
    Wait,
    DisplayMath,
    InlineMath,
    SeenDollarRaw,
    SeenDollarMath,
}

fn process_content(s: &String) -> String {
    use ViewMode::*;
    let mut result = String::with_capacity(s.len());
    let mut mode = Wait;
    let mut output_bussproofs = false;
    for ch in s.chars() {
        match (ch, &mode) {
            ('$', Wait) => mode = SeenDollarRaw,
            ('$', SeenDollarRaw) => {
                mode = DisplayMath;
                result.push_str("\\\\[");
                if !output_bussproofs {
                    result.push_str("\\require{bussproofs}");
                    output_bussproofs = true;
                }
            }
            (_, SeenDollarRaw) => {
                mode = InlineMath;
                result.push_str("\\\\(");
                result.push(ch);
            }
            ('$', DisplayMath) => mode = SeenDollarMath,
            ('$', SeenDollarMath) => {
                mode = Wait;
                result.push_str("\\\\]");
            }
            (_, SeenDollarMath) => {
                mode = DisplayMath;
                result.push('$');
                result.push(ch);
            }
            ('$', InlineMath) => {
                mode = Wait;
                result.push_str("\\\\)");
            }
            _ => result.push(ch),
        }
    }

    return result;
}

fn fix_math_dollars(item: &mut BookItem) -> () {
    match item {
        BookItem::Separator => (),
        BookItem::Chapter(c) => {
            c.content = process_content(&c.content);
        }
    }
}

impl Preprocessor for MathFixer {
    fn name(&self) -> &str {
        "mdbook-math-fixer"
    }

    fn run(&self, _ctx: &PreprocessorContext, mut book: Book) -> Result<Book, Error> {
        book.for_each_mut(fix_math_dollars);

        Ok(book)
    }

    fn supports_renderer(&self, renderer: &str) -> bool {
        renderer != "not-supported"
    }
}

pub fn make_app() -> App<'static, 'static> {
    App::new("mdbook-math-fixer")
        .about("A mdbook preprocessor which (poorly) fixes math dollars")
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
    let preprocessor = MathFixer::new();

    if let Some(sub_args) = matches.subcommand_matches("supports") {
        handle_supports(&preprocessor, sub_args);
    } else if let Err(e) = handle_preprocessing(&preprocessor) {
        eprintln!("{}", e);
        process::exit(1);
    }
}
