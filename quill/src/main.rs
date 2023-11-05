use diagnostic::{miette, Dr};
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

    Dr::<(), _>::new_err(ParseError {
        message: "world".to_owned(),
    })
    .to_dynamic()
    .print_reports();
}
