import scala.io.Source

object Main {
    def main(args: Array[String]) = {
        val qdimacs = Source.fromFile(args(0)).mkString
        val sat = SolverExport.run_search_solver(qdimacs)
        if (sat) System.exit(10) else System.exit(20)
    }
}
