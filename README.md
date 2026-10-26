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
- `StarExec_results.csv` contains the data from an evaluation the solvers using StarExec.

## Code Export

Running `make` in `codegen/` will build executable programs from the code exports.
One executable is built for each combination of export language and solver.
All solvers take a single `.qdimacs` file argument as input and yields the exit code `10` if the input was determined to be satisfiable and the exit code `20` if it was determined to be unsatisfiable.
(Zip files used for running on the StarExec cluster are also created.)

## Instance Generation

Running `make` in `data/` will create `.qdimacs` instances of the domino game and the xor problem.

## StarExec results

The file `StarExec_results.csv` contains the data from an evaluation of the naive solver and the search solver across the four code export target languages Standard ML, OCaml, Haskell, and Scala.
Each solver was ran on the now-decommissioned University of Iowa StarExec instance against a range of different instances of the xor problem and the domino game with a 900s timeout and a 32GB memory limit.
The result for each run is either an execution time in seconds, a timeout, a stack overflow, or an out-of-memory error.
The state-of-the-art solver CAQE was also included as a reference point.

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
