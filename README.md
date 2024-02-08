# Verified QBF Solver(s)

Isabelle/HOL implementation of and correctness proofs for quantified Boolean formula (QBF) solvers.

## Structure

- `codegen/` contains files used to build executable programs from the Isabelle theories.
- `data/` contains files to generate `.qdimacs` instances of two different problems.
- `document/` contains a `.tex` file for Isabelle's document preparation.
- `NaiveSolver.thy` implements and shows the correctness of a naive expansion-based solver.
- `PCNF.thy` defines a type for prenex conjugate normal form (PCNF) QBFs and defines a formally verified conversion to the QBF datatype used by the naive solver.
- `Parser.thy` defines a unverified parser for `.qdimacs` instances outputting instances of the PCNF type.
- `ROOT` contains metadata for Isabelle.
- `SearchSolver.thy` implements and shows the correctness of a simple search-based solver.
- `SolverExport.thy` defines the executable code exports of the solvers.

## Code Export

Running `make` in `codegen/` will build executable programs from the code exports.
One executable is built for each combination of export language and solver.
(Zip files used for running on the StarExec cluster are also created.)

## Instance Generation

Running `make` in `data/` will create `.qdimacs` instances of the domino game and the xor problem.

## Document Generation

Running `isabelle document -d . a_verified_qbf_solver` in `.` will create a pdf version of the Isabelle theories.

## Dependencies/Versions

The project has been tested on a Linux system with the following software versions:
- Isabelle/HOL, 2023
- GNU Make, 4.4.1
- MLton, 20210117
- OCaml, 5.1.0
- Zarith, 1.13
- GHC, 9.0.2
- Scala, 2.13.12
- CPython, 3.11.6
- Bash, 5.2.21
