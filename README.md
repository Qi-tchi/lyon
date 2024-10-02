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

You can install the necessary dependencies via `opam`:

```bash
opam install dune utop
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

   ```ocaml
   let ex3 = Lyon.ConcretGraphRewritingSystems.bruggink_2014_example_4
   let ex4 = Lyon.ConcretGraphRewritingSystems.grs_ex69
   let ex12 = Lyon.ConcretGraphRewritingSystems.endrullis_2023_ex6_3
   let ex13 = Lyon.ConcretGraphRewritingSystems.grs_ex69_variant

   let print_grs = Lyon.Termination.print_grs

   let isTerminating = Lyon.Termination.isTerminating
   let interp = Lyon.Termination.interpret
   ```
3. **Test an example**:
   To check whether a graph rewriting system is terminating, you can call the `isTerminating` method on any of the loaded examples. For instance, to test `ex4`:

   ```ocaml
   let res = isTerminating ex4
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
let ex4 = Lyon.ConcretGraphRewritingSystems.grs_ex69;;
let _ = print_grs ex4

let isTerminating = Lyon.Termination.isTerminating;;
let interp = Lyon.Termination.interpret;;
let res = isTerminating ex4;;
interp res;;
```

The `interp` function will provide an interpretation of whether the system is terminating.

## License

This project is licensed under the MIT License. See the [LICENSE](LICENSE) file for details.
