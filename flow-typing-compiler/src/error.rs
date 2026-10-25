use logos::Span;

/// Records an error with span information.
#[derive(Debug)]
pub struct Diagnostic {
    span: Span,
    message: String,
}

impl Diagnostic {
    pub fn error(span: Span, message: String) -> Self {
        Self { span, message }
    }
}

impl Diagnostic {
    pub fn display(self, file: &str) {
        ariadne::Report::build(ariadne::ReportKind::Error, self.span.clone())
            .with_message(&self.message)
            .with_label(ariadne::Label::new(self.span).with_message(self.message))
            .finish()
            .print(ariadne::Source::from(file))
            .unwrap();
    }
}

/// A result possibly with a sequence of errors inside it.
/// This is a monad.
pub struct EResult<T> {
    value: Option<T>,
    errors: Vec<Diagnostic>,
}

impl<T> EResult<T> {
    fn ok(value: T) -> EResult<T> {
        Self {
            value: Some(value),
            errors: Vec::new(),
        }
    }

    fn fails(errors: Vec<Diagnostic>) -> EResult<T> {
        Self {
            value: None,
            errors,
        }
    }
}

impl<T> From<Result<T, Vec<Diagnostic>>> for EResult<T> {
    fn from(value: Result<T, Vec<Diagnostic>>) -> Self {
        match value {
            Ok(value) => EResult::ok(value),
            Err(errors) => EResult::fails(errors),
        }
    }
}

impl<T> From<Result<T, Diagnostic>> for EResult<T> {
    fn from(value: Result<T, Diagnostic>) -> Self {
        value.map_err(|e| vec![e]).into()
    }
}

/// Tracks a list of errors.
#[derive(Default)]
pub struct Errors {
    errors: Vec<Diagnostic>,
}

impl Errors {
    pub fn get<T>(&mut self, result: EResult<T>) -> Option<T> {
        self.errors.extend(result.errors);
        result.value
    }

    pub fn push(&mut self, e: Diagnostic) {
        self.errors.push(e);
    }

    pub fn emit(&mut self, file: &str) -> Option<()> {
        if self.errors.is_empty() {
            Some(())
        } else {
            for e in std::mem::take(&mut self.errors) {
                e.display(file);
            }
            None
        }
    }
}
