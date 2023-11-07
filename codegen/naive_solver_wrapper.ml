open Run_naive_solver

let read_file filename =
    let ch = open_in filename in
    let s = really_input_string ch (in_channel_length ch) in
    close_in ch;
    s

let executable_name::input_filename::args = Array.to_list Sys.argv;;
let sat = NaiveSolverExport.run_naive_solver (read_file input_filename);;
if sat then exit 10 else exit 20;;
