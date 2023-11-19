use db::Database;
use diagnostic::miette;
use files::{Db, Source, SourceData};
use parse::parser::ParserConfiguration;
use thiserror::Error;

#[derive(Error, miette::Diagnostic, Debug, Clone, PartialEq, Eq, Hash)]
#[error("hello {message}!")]
pub struct ParseError {
    message: String,
}

fn main() {
    let log_level = tracing::Level::TRACE;
    let subscriber = tracing_subscriber::FmtSubscriber::builder()
        .with_writer(std::io::stderr)
        .with_max_level(log_level)
        .with_span_events(tracing_subscriber::fmt::format::FmtSpan::CLOSE)
        .with_timer(tracing_subscriber::fmt::time::uptime())
        .pretty()
        .finish();
    tracing::subscriber::set_global_default(subscriber)
        .expect("could not set default tracing subscriber");
    tracing::info!("initialised logging with verbosity level {}", log_level);

    let db = Database::new(".");
    let src = Source {
        directory: vec!["test".to_owned().into()],
        name: "main".to_owned().into(),
        extension: files::FileExtension::Quill,
    };

    let value = db
        .read_source(src.clone())
        .to_dynamic()
        .bind(|value| parse::lex::tokenise(&SourceData::new(src.clone(), &db), value.chars()))
        .bind(|tokens| {
            parse::parser::Parser::new(
                &ParserConfiguration::new(&SourceData::new(src.clone(), &db)),
                tokens.into_iter(),
            )
            .parse_defs()
            .to_dynamic()
        })
        .print_reports();

    if let Some(value) = value {
        for def in value {
            if let Some(ty) = def.ty {
                let mut elaborator = elab::Elaborator::new(SourceData::new(src.clone(), &db));
                let value = elaborator
                    .elaborate_type(&Default::default(), &ty)
                    .map(|mut ty| {
                        elaborator.instantiate_metavariables(&mut ty);
                        ty
                    })
                    .to_dynamic()
                    .print_reports();

                if let Some(value) = value {
                    tracing::info!("{value}");
                }
            }
        }
    }
}
