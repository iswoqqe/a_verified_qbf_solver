module Main where
import NaiveSolverExport
import System.Exit
import System.Environment

main :: IO ()
main = do
  (input_filename:rest) <- getArgs
  qdimacs <- readFile input_filename
  let sat = run_naive_solver qdimacs
  if sat then exitWith (ExitFailure 10) else exitWith (ExitFailure 20)
