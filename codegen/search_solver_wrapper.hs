module Main where
import SolverExport
import System.Exit
import System.Environment

main :: IO ()
main = do
  (input_filename:rest) <- getArgs
  qdimacs <- readFile input_filename
  let sat = run_search_solver qdimacs
  if sat then exitWith (ExitFailure 10) else exitWith (ExitFailure 20)
