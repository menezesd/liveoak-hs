# LiveOak Compiler (Haskell)

A Haskell compiler for the LiveOak 3 object-oriented language. The compiler can
generate either SAM (Stack Abstract Machine) assembly or x86_64 (GAS syntax)
and ships with a growing suite of SSA-based optimizations.

## Features
- Parser and semantic analyzer for classes, fields, methods, control flow, and
  primitive/object types.
- SSA construction with data-flow analyses and classic optimizations (GVN,
  LICM, SROA, PRE, copy propagation, load forwarding, dead code elimination,
  tail-call optimization, strength reduction, loop optimizations, and more).
- Peephole optimization for generated SAM assembly.
- Dual backends:
  - **SAM**: Stack-based assembly suitable for the LiveOak simulator.
  - **x86_64**: GAS syntax assembly using a custom register allocator,
    scheduling, and liveness analysis.
- Warning collection and detailed diagnostics with source snippets.
- Test suite covering compiler correctness, simulator behavior, and property
  tests.

## Building
```bash
cabal build
```

To develop interactively you can also load the project in GHCi:
```bash
cabal repl
```

## Usage
Compile a LiveOak source file to SAM (default target):
```bash
cabal run liveoak -- path/to/input.lo path/to/output.sam
```

Compile to x86_64 assembly:
```bash
cabal run liveoak -- --target=x86_64 path/to/input.lo path/to/output.s
```

Omit the output path to print assembly to stdout. Use `--target=sam` to be
explicit about the default target.

## Project Structure
```text
app/Main.hs             -- CLI entrypoint and flag parsing
src/LiveOak/Compiler.hs -- High-level compilation pipeline
src/LiveOak/Parser.hs   -- Megaparsec parser and symbol table construction
src/LiveOak/Semantic.hs -- Type checking and validation
src/LiveOak/Optimize.hs -- AST optimizations and warning collection
src/LiveOak/SSA*.hs     -- SSA IR, analyses, and optimization passes
src/LiveOak/Codegen.hs  -- SAM code generation
src/LiveOak/X86*.hs     -- x86_64 backend, register allocation, runtime stubs
src/LiveOak/Peephole.hs -- SAM peephole optimizer
```

## LiveOak Language
LiveOak is a small object-oriented language with:
- Classes with fields and methods
- Primitive types: `int`, `bool`, `String`
- Object types (class references)
- Control flow: `if/else`, `while`, `break`, `return`
- Operators: arithmetic, logical, comparison

Example program:
```java
class car() {
  int carPrice() { { return 10; } }
}

class Main() {
  int main() {
    car c;
    { c = new car(); return c.carPrice(); }
  }
}
```

## Testing
Run the full test suite (unit tests, simulator tests, and property checks):
```bash
cabal test
```

## Dependencies
- GHC 9.4+
- Cabal 3+
- Library dependencies: megaparsec, text, containers, mtl, transformers,
  vector
