all: naive_solver_sml naive_solver_ocaml naive_solver_haskell naive_solver_scala.jar naive_solver.zip search_solver_sml search_solver_ocaml search_solver_haskell search_solver_scala.jar search_solver.zip

naive_solver.zip: naive_solver_sml naive_solver_ocaml naive_solver_haskell naive_solver_scala.jar bin/starexec_run_naive_solver_sml bin/starexec_run_naive_solver_ocaml bin/starexec_run_naive_solver_haskell bin/starexec_run_naive_solver_scala
	zip naive_solver.zip naive_solver_sml naive_solver_ocaml naive_solver_haskell naive_solver_scala.jar scala-library.jar bin/starexec_run_naive_solver_sml bin/starexec_run_naive_solver_ocaml bin/starexec_run_naive_solver_haskell bin/starexec_run_naive_solver_scala

search_solver.zip: search_solver_sml search_solver_ocaml search_solver_haskell search_solver_scala.jar bin/starexec_run_search_solver_sml bin/starexec_run_search_solver_ocaml bin/starexec_run_search_solver_haskell bin/starexec_run_search_solver_scala
	zip search_solver.zip search_solver_sml search_solver_ocaml search_solver_haskell search_solver_scala.jar scala-library.jar bin/starexec_run_search_solver_sml bin/starexec_run_search_solver_ocaml bin/starexec_run_search_solver_haskell bin/starexec_run_search_solver_scala

../export/a_verified_qbf_solver.SolverExport/: ../SolverExport.thy ../Parser.thy ../Solver.thy
	isabelle build -D .. -e

naive_solver_sml: naive_solver_wrapper.sml naive_solver_sml.mlb ../export/a_verified_qbf_solver.SolverExport/
	cp ../export/a_verified_qbf_solver.SolverExport/code/run_naive_solver.ML run_naive_solver.sml
	mlton naive_solver_sml.mlb

naive_solver_ocaml: naive_solver_wrapper.ml ../export/a_verified_qbf_solver.SolverExport/
	cp ../export/a_verified_qbf_solver.SolverExport/code/run_naive_solver.ocaml run_naive_solver.ml
	ocamlfind ocamlopt -O3 -linkpkg -package zarith -o naive_solver_ocaml run_naive_solver.ml naive_solver_wrapper.ml

naive_solver_haskell: naive_solver_wrapper.hs ../export/a_verified_qbf_solver.SolverExport/code/run_naive_solver/
	cp -r ../export/a_verified_qbf_solver.SolverExport/code/run_naive_solver/ .
	ghc -O3 -irun_naive_solver -o naive_solver_haskell naive_solver_wrapper.hs 

naive_solver_scala.jar: naive_solver_wrapper.scala MANIFEST.MF ../export/a_verified_qbf_solver.SolverExport/
	cp ../export/a_verified_qbf_solver.SolverExport/code/run_naive_solver.scala .
	scalac -opt:local run_naive_solver.scala naive_solver_wrapper.scala -d naive_solver_scala.jar
	jar umf MANIFEST.MF naive_solver_scala.jar

search_solver_sml: search_solver_wrapper.sml search_solver_sml.mlb ../export/a_verified_qbf_solver.SolverExport/
	cp ../export/a_verified_qbf_solver.SolverExport/code/run_search_solver.ML run_search_solver.sml
	mlton search_solver_sml.mlb

search_solver_ocaml: search_solver_wrapper.ml ../export/a_verified_qbf_solver.SolverExport/
	cp ../export/a_verified_qbf_solver.SolverExport/code/run_search_solver.ocaml run_search_solver.ml
	ocamlfind ocamlopt -O3 -linkpkg -package zarith -o search_solver_ocaml run_search_solver.ml search_solver_wrapper.ml

search_solver_haskell: search_solver_wrapper.hs ../export/a_verified_qbf_solver.SolverExport/code/run_search_solver/
	cp -r ../export/a_verified_qbf_solver.SolverExport/code/run_search_solver/ .
	ghc -O3 -irun_search_solver -o search_solver_haskell search_solver_wrapper.hs

search_solver_scala.jar: search_solver_wrapper.scala MANIFEST.MF ../export/a_verified_qbf_solver.SolverExport/
	cp ../export/a_verified_qbf_solver.SolverExport/code/run_search_solver.scala .
	scalac -opt:local run_search_solver.scala search_solver_wrapper.scala -d search_solver_scala.jar
	jar umf MANIFEST.MF search_solver_scala.jar

clean_most:
	${RM} -r run_naive_solver.sml naive_solver_wrapper.cmi run_naive_solver.cmx run_naive_solver.o naive_solver_wrapper.cmx naive_solver_wrapper.o run_naive_solver.cmi run_naive_solver.ml naive_solver_wrapper.hi  naive_solver_wrapper.o  run_naive_solver/ run_naive_solver.scala run_search_solver.sml search_solver_wrapper.cmi run_search_solver.cmx run_search_solver.o search_solver_wrapper.cmx search_solver_wrapper.o run_search_solver.cmi run_search_solver.ml search_solver_wrapper.hi  search_solver_wrapper.o  run_search_solver/ run_search_solver.scala

clean: clean_most
	${RM} naive_solver_sml naive_solver_ocaml naive_solver_haskell naive_solver_scala.jar naive_solver.zip search_solver_sml search_solver_ocaml search_solver_haskell search_solver_scala.jar search_solver.zip

.PHONY: all clean clean_most
