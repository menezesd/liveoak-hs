# LiveOak Compiler (Haskell)

A compiler for the LiveOak 3 programming language, written in Haskell. Generates SAM (Stack Abstract Machine) assembly.

## Building

```bash
cabal build
```

## Usage

```bash
# Compile to file
cabal run liveoak -- input.lo output.sam

# Compile to stdout
cabal run liveoak -- input.lo
```

## Project Structure

```
src/LiveOak/
├── Types.hs          -- Type system (int, bool, String, object types)
├── Ast.hs            -- Abstract syntax tree (expressions, statements)
├── Symbol.hs         -- Symbol table (variables, methods, classes)
├── Diag.hs           -- Diagnostics and Result monad
├── Lexer.hs          -- Megaparsec lexer
├── Parser.hs         -- Megaparsec parser
├── Semantic.hs       -- Type checking and validation
├── Codegen.hs        -- SAM code generation
├── StringRuntime.hs  -- String operation SAM routines
└── Compiler.hs       -- Compilation pipeline
```

## LiveOak Language

LiveOak is a simple object-oriented language with:
- Classes with fields and methods
- Primitive types: `int`, `bool`, `String`
- Object types (class references)
- Control flow: `if/else`, `while`, `break`, `return`
- Operators: arithmetic, logical, comparison

Example:
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

## Dependencies

- GHC 9.4+
- megaparsec >= 9.0
- text >= 2.0
- containers >= 0.6
- mtl >= 2.3
