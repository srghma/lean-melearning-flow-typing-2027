macro_rules! out_of_scope {
    () => {
        unimplemented!(
            "this behaviour is out of scope for this compiler (error emitted at {}:{}:{})",
            file!(),
            line!(),
            column!(),
        )
    };
}
pub(crate) use out_of_scope;
