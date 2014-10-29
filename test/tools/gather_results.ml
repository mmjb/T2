(* Copyright (c) Microsoft Corporation.  All rights reserved. *)

let fnames = ref []
let dirname = ref "."
let test_results = ref []
let starting_dir = Sys.getcwd ()
let expected_fname = ref ""

(** Read the results from a file *)
let read_results fname =
  if Sys.file_exists fname then begin
    let in_ch = open_in fname in
    let rec go l =
      let (s, has_more) =
        try (input_line in_ch, true) with End_of_file -> ("", false) in
      if has_more then
        if (Str.string_match (Str.regexp "\\([^:]+\\): *\\(.+\\)") s 0) then
	  let test_name = Str.matched_group 1 s in
	  let expected_result = Str.matched_group 2 s in
          go ((test_name, expected_result)::l)
        else
          go l
      else
        List.fast_sort (fun (x,_) (y,_) -> String.compare x y) l
    in
    let res = go [] in
    close_in in_ch;
    res
  end else begin
    []
  end


(** One-line summary of results *)
let summarize_res res =
  let incr_on_match s t i = if (s=t) then i+1 else i in
  let initial_summary = (0,0,0,0) in
  List.fold_left
    (fun (ee,ff,ss,uu) (_,_,what,_) ->
       let ee' = incr_on_match "error" what ee in
       let ff' = incr_on_match "fail" what ff in
       let ss' = incr_on_match "succ" what ss in
       let uu' = if (ee=ee' && ff=ff' && ss=ss') then (uu+1) else uu in
       (ee',ff',ss',uu'))
    initial_summary res

(** Write the results to a csv (format testname,result,time) file *)
let produce_csv fname res =
  let ch = open_out fname in
  try
    List.iter (fun (name,(utime, stime, ttime),_,res) ->
      Printf.fprintf ch "%s,%s,%.3f\n" name res ttime
    ) res;
    close_out ch
  with exn ->
    close_out ch;
    raise exn

(** Write the results to a txt file *)
let produce_txt fname res =
  let ch = open_out fname in
  try
    let (errors,fails,succs,unknowns) = summarize_res res in
    Printf.fprintf ch "Summary: errors %d, fails %d, succs %d, unknowns %d\n"
      errors fails succs unknowns;
    List.iter (fun (name,_what,_time,msg) ->
      Printf.fprintf ch "%s:%s\n" name msg
    ) res;
    close_out ch
  with exn ->
    close_out ch;
    raise exn


(** Write the results to a html file *)
let produce_html fname res =
  (* SI: precompute Summary *)
  let errors, fails, succs, unknowns = summarize_res res in
  let out_ch = open_out fname in
  let pr x = Printf.fprintf out_ch x in
  try
    pr "<html><head><title>Test results</title><style>\n" ;
    pr ".error { background-color: #ffcccc; padding: 5px; }\n" ;
    pr ".fail { background-color: #ffffcc; padding: 5px; }\n" ;
    pr ".succ { background-color: #ccffcc; padding: 5px; }\n" ;
    pr "</style></head>\n" ;
    pr "<body>" ;
    pr "<h1>Test results</h1>\n" ;

    let module U = Unix in
    let tm = U.localtime (U.time ()) in
    let yy = tm.U.tm_year + 1900
    and mm = tm.U.tm_mon + 1
    and dd = tm.U.tm_mday
    and hh = tm.U.tm_hour
    and nn = tm.U.tm_min
    in
    pr "<p>%d:%02d:%02d:%02d:%02d</p>\n"
      yy mm dd hh nn ;
    pr "<table><tr><td>Summary:</td><td>errors %d, </td>\
                   <td>fails %d, </td><td>succs %d, </td>\
                   <td>unknowns %d</td></tr>\n"
      errors fails succs unknowns ;
    pr "<table><tr><th>Test</th>\
                   <th>total<br>(sec)</th>\
                   <th>Result</th></tr>\n" ;
    List.iter (fun (name, (utime, stime, ttime), what, msg) ->
      pr "<tr>\
	  <td class=\"%s\"><a href=\"%s\">%s</a></td>"
	 what name name ;
      pr "<td align=\"right\" class=\"%s\">%12.6f</td>\n\
	  <td class=\"%s\">%s</td></tr>\n"
	 what ttime
	 what msg
    ) res ;
    pr "<table>\n" ;
    pr "</body></html>\n" ;
    close_out out_ch
  with exn ->
    close_out out_ch ;
    raise exn


(** Compare results *)
let compare_results res1 res2 =
  let no_found (x,time,what,m) =
    if what = "error" then (x,time,what,m)
    else (x,time,"fail",m ^ " No expected result found.") in
  let rec go res res1 res2 =
    match res1, res2 with
    | [], _ -> List.rev res
    | x::res1, [] -> go (no_found x :: res) res1 []
    | (x,time,what,m)::res1', (x2,m2)::res2' ->
        let n = String.compare x x2 in
        if n < 0 then
	  go (no_found (x,time,what,m) :: res) res1' res2
        else if n = 0 then
          let res' =
            if m = m2 then
	      (x, time, "succ", m) :: res
            else if what = "error" then
	      (x, time, what, m^" Expected:"^m2) :: res
            else
              (x, time, "fail", m^" Expected:"^m2) :: res
          in
          go res' res1' res2'
        else go res res1 res2'
  in
  go [] res1 res2


let grep num_groups rex fname =
  let inch = open_in fname in
  let rec go l =
    let s, has_more =
      try (input_line inch, true) with End_of_file -> ("", false) in
    let l =
      try
	let _ = Str.search_forward rex s 0 in
	let rec loop i z =
	  if i > num_groups then z else loop (i+1) (Str.matched_group i s :: z)
	in
	(List.rev (loop 1 [])) :: l
      with Not_found -> l in
    (if has_more then go l else l)
  in
  let res = go [] in
  close_in inch;
  res

(* Parse a t2 output file *)
let parse_t2_output output_file = 
  let original_file = Filename.chop_extension (Str.string_after output_file (1 + String.length !dirname)) in
  if Sys.file_exists output_file then
  let t_rex = Str.regexp "TotalWallClockTime: \\([0-9.]+\\)"
  in
  let t =
    match grep 1 t_rex output_file with
    | [[t]] ->
        let t = float_of_string t in (t /. 1000., 0., t /. 1000.)
    | _ ->
        (0.,0.,0.)
  in
  let out_rex = Str.regexp "Status: *\\([0-9]+\\)" in
  let r1, r2 =
    (match grep 1 out_rex output_file with
    | [["1"]] -> ("error", "TIMEOUT")
    | [["4"]] -> ("error", "MEMOUT")
    | _ -> ("", ""))
  in
  if r1 = "error" then
   test_results := (original_file, t, r1, r2) :: !test_results
  else
   let output_re = Str.regexp "\\(Termination\\|Nontermination\\) proof succeeded" in
   let r1, r2  =
     match grep 1 output_re output_file with
     | (["Termination"]::_) -> ("succ", "YES")
     | (["Nontermination"]::_) -> ("succ", "NO")
     | _ -> ("error", "MAYBE")
   in
   test_results := (original_file, t, r1, r2) :: !test_results

let parse_args () =
  let usage = "\nUsage: gather_results -expected <FILE> DIR" in
  Arg.parse [("-expected", Arg.String (fun str -> expected_fname := str), ": path of expected.txt")] (fun dir -> dirname := dir ) usage;
  ()

let rec collect_files_in_dir dir =
  List.iter 
    (fun dir_entry ->
       if (Sys.is_directory (dir ^ "/" ^ dir_entry)) then 
         collect_files_in_dir (dir ^ "/" ^ dir_entry)
       else if (Str.string_match (Str.regexp ".*\\.out") dir_entry 0) then begin
         fnames := ((dir ^ "/" ^ dir_entry) :: !fnames) end
       else ())
    (Array.to_list (Sys.readdir dir));
  ()
  
let () =
  let _ = parse_args () in
  collect_files_in_dir !dirname;
  List.iter (parse_t2_output) !fnames;
  let res =
    List.fast_sort (fun (x,_,_,_) (y,_,_,_) -> String.compare x y)
      !test_results in
  let res2 = compare_results res (read_results !expected_fname) in
  produce_csv (!dirname ^ "/RESULT.csv") res ;
  produce_txt (!dirname ^ "/RESULT.txt") res2 ;
  produce_html (!dirname ^ "/RESULT.html") res2
