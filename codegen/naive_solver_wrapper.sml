val (input_filename::args) = CommandLine.arguments();
val sat = NaiveSolverExport.run_naive_solver (TextIO.inputAll (TextIO.openIn input_filename));
Posix.Process.exit(if sat then Word8.fromInt 10 else Word8.fromInt 20);
