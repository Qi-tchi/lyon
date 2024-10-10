# Graph Rewriting Systems Termination Checker

This project provides an implementation of linear DPO graph rewriting systems, as well as a method to check whether these systems are terminating.

## Features

- Examples of graph rewriting systems from several publications
- Methods to check termination of these systems
- Interpretation of the results of termination checks

## Prerequisites

To use this software, ensure that you have installed:

- [OCaml](https://ocaml.org/)
- [Dune](https://dune.build/)
- [utop](https://github.com/diml/utop) (for the OCaml REPL)
- [Batteries](https://github.com/ocaml-batteries-team/batteries-included) (for utility functions)

You can install the necessary dependencies via `opam`:

```bash
opam install dune utop batteries
```

## Getting Started

To use this software, follow these steps:

1. **Open the REPL**:
   In the root directory of the project, run:

   ```bash
   dune utop lib
   ```
2. **Load the examples and functions**:
   Once in the REPL, load the following examples and functions:

   let ex40 = Lyon.ConcretGraphRewritingSystems.bruggink_2014_example_4
   let ex41 = Lyon.ConcretGraphRewritingSystems.grs_ex69
   let ex42 = Lyon.ConcretGraphRewritingSystems.endrullis_2023_ex6_3
   let ex43 = Lyon.ConcretGraphRewritingSystems.grs_ex69_variant

   let print_grs = Lyon.Termination.print_grs

   let isTerminating = Lyon.Termination.isTerminating
   let interp = Lyon.Termination.interpret
3. **Print a graph rewriting system**:

   ```ocaml
   let _ = print_grs ex40
   ```
4. **Test an example**:
   To check whether a graph rewriting system is terminating, you can call the `isTerminating` method on any of the loaded examples. For instance, to test `ex40`:

   ```ocaml
   let res = isTerminating ex40
   ```

   To interpret the result returned by the method, run:

   ```ocaml
   interp res
   ```

## Example Usage

Here’s a full example in the REPL:

```ocaml
dune utop lib
```

```ocaml
let ex40 = Lyon.ConcretGraphRewritingSystems.grs_ex69;;
let _ = print_grs ex40

let isTerminating = Lyon.Termination.isTerminating;;
let interp = Lyon.Termination.interpret;;
let res = isTerminating ex40;;
interp res;;
```

## Preprocessing Requirements

This project uses several preprocessors for code generation and testing:

- `ppx_jane`
- `ppx_inline_test`
- `ppx_assert`
- `ppx_expect`

## License

This project is licensed under the MIT License. See the [LICENSE](LICENSE) file for details.
