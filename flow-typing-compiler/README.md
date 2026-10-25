# Flow typing compiler

This is a compiler for a programming language based on *flow typing*, introduced in the article *Flow Typing: A New Lens on Linearity*.

## Build instructions

1. Install modern versions of [Rust](https://rust-lang.org/) and [GHC](https://www.haskell.org/).
    The flow typing compiler is written in Rust, and it outputs Linear Haskell.
    We rely on some modern features of Haskell, so it's important to use a recent version (we tested using GHC 9.6.7).

2. Open a terminal in the `flow` directory.
    Run `cabal update` to get the latest list of Haskell dependencies.

3. Optional but recommended: install a recent version of `fourmolu`, a Haskell formatter, by running `cabal install fourmolu` (this may take around 10 minutes).
    If you have `fourmolu` installed, our flow typing compiler will be able to generate much nicer-looking Haskell code.

4. Run the compiler by executing `cargo run` in the `flow` directory.
    Cargo, Rust's build system, will automatically download the necessary dependencies.
    This will compile the flow typing file `examples.fl` to the Linear Haskell file `flow/Examples.hs`.
    You should see some debug output, showing how the compiler translated each definition in the file.
    A copy of `flow/Examples.hs`, generated from the original `examples.fl` in this tarball, has been provided for convenience.

5. Run the compiled flow typing program by executing `cabal run` in the `flow` directory.
    Cabal is one of Haskell's build systems, and it should automatically download the required dependencies, such as a standard library for Linear Haskell.

    Alternatively, open the REPL using `cabal repl` in the `flow` directory.
    In the REPL, you can view the types of compiled flow typing functions.
    For example, `:t Examples.avg` shows the type of the `avg` function defined in `examples.fl`.

6. You can recompile and run the project again by running `cargo run` then `cabal run` in the `flow` directory.

## Notes

The generated Haskell code uses a lot of `case` expressions instead of the more obvious `let`.
This is because case expressions cooperate better with Linear Haskell, whereas the laziness of `let` bindings makes them more difficult to use.
