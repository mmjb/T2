// Copyright (c) Microsoft Corporation
//
// All rights reserved. 
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the ""Software""), to 
// deal in the Software without restriction, including without limitation the
// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
// sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included 
// in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED *AS IS*, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
// THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
// DEALINGS IN THE SOFTWARE.

module Microsoft.Research.T2.Output

open Utils
open Programs

let print_program p =
   printf "=================== PROGRAM =====================\n"
   printf "Initial location: %d\n" !p.initial
   printf "Labels:\n"
   let print_label l n =
      printf "  %s:%d\n" l n
   Map.iter print_label !p.labels

   printf "Transitions:\n"
   let print_trans (k,T,k') =
      printf "%d ---> %d\n%s\n" k k' (commands2pp T)

   Seq.iter print_trans (enumerate_transitions p)

// Dot pretty printers for programs/terms/formula -------------------------

let print_dot_program p (fname : string) =
   let h = new System.IO.StreamWriter(fname)
   fprintf h "digraph program {\nnode [shape=circle];\n" ;
   let nodes = ref Set.empty
   let commands2pp b =
       let f x y = x + command2pp y + "\\l" // "\l" is a "left-aligned line-break"...
       let true_assume = assume Formula.truec
       b |> List.filter (fun c -> c <> true_assume)
         |> List.fold f ""

   let print_trans idx (k,T,k') =
       nodes := Set.add k !nodes
       nodes := Set.add k' !nodes
       let cmd_box_num = Gensym.fresh_num()
       let cmd_box = sprintf "cmd%O" cmd_box_num
       fprintf h "node%d -> %s;\n" k cmd_box
       fprintf h "%s [shape=box label=\"%i: %s\"];\n" cmd_box idx (commands2pp T)
       fprintf h "%s -> node%d;\n" cmd_box k'

   for transIdx in !p.active do
       let (k,t,k') = p.transitions.[transIdx]
       print_trans transIdx (k,t,k')

   for n in !nodes do
       let lab = match Map.tryFindKey (fun _ v -> v=n) !p.labels with
                 | Some(s) -> s
                 | None -> "?"
       let color = "red"
       if n<> !p.initial then
           fprintf h "node%d [ color=%s label = \"%d (%s)\" ];\n" n color n lab
       else
           fprintf h "node%d [ color=%s label = \"%d (start)\" ];\n" n color n
   done
   fprintf h "}\n"
   h.Dispose ()
   printf "Created %s\n" fname

let pp_label pp (cps: seq<int>) =
    if Seq.exists ((=) pp) cps then
        sprintf "loc_CP_%i" pp
    else
        sprintf "loc_%i" pp

let print_c_program_goto p (fname : string) =
    let out_channel = new System.IO.StreamWriter(fname)
    fprintfn out_channel "int nondet() { int a; return a; }"
    fprintfn out_channel "_Bool nondet_bool() { _Bool a; return a; }"
    fprintfn out_channel "int main() {"

    let (loops, _) = find_loops p
    let cps = loops.Keys

    //sanitize var names, declare:
    let vars = variables p
    let var_map = ref Map.empty;
    let i = ref 1
    for v in vars do
        let new_v = "v" + (!i).ToString()
        var_map := Map.add v new_v !var_map
        i := !i + 1
        fprintfn out_channel "int %s = nondet();" new_v

    //map all location to outgoing transitions:
    let out_trans = new System.Collections.Generic.Dictionary<int, System.Collections.Generic.HashSet<command list * int>>()
    let add_to_set_dict (dict : System.Collections.Generic.Dictionary<int, System.Collections.Generic.HashSet<command list * int>>) k v =
        if dict.ContainsKey k then
            dict.[k].Add v
        else
            dict.Add(k, new System.Collections.Generic.HashSet<command list * int>())
            dict.[k].Add v
    for n in !p.active do
        let (k, cmds, k') = p.transitions.[n]
        add_to_set_dict out_trans k (cmds, k') |> ignore

    //first step:
    fprintfn out_channel "goto %s;" (pp_label !p.initial cps)

    //encode transitions. Order locations first, putting initial and cutpoints first:
    let final_locs = ref []
    let locations = ref <| !p.initial :: (List.ofSeq cps)
    locations := !locations @ (List.ofSeq <| Seq.filter (fun pp -> not <| List.contains pp !locations) out_trans.Keys)
    for location in !locations do
        fprintfn out_channel "%s:" (pp_label location cps)

        let trans = out_trans.[location]
        for (cmds, k') in trans do
            fprintfn out_channel " if (nondet_bool()) {"
            cmds
            |> List.iter (
                function
                    | Assume(_, f) ->
                        let sanitized_f = Formula.alpha (fun v -> (!var_map).[v]) f
                        fprintfn out_channel "  if (!( %s )) goto end;" (sanitized_f.pp);
                    | Assign(_, v, t) ->
                        let sanitized_v = (!var_map).[v]
                        let sanitized_t = Term.alpha (fun v -> (!var_map).[v]) t
                        fprintfn out_channel "  %s = %s;" (sanitized_v) (sanitized_t.pp);
                )
            ()
            fprintfn out_channel "  goto %s;" (pp_label k' cps)
            if not(out_trans.ContainsKey k') then
                final_locs := k' :: !final_locs
            fprintfn out_channel " }"

        fprintfn out_channel " goto end;"

    for final_loc in !final_locs do
        fprintfn out_channel "%s:" (pp_label final_loc cps)
    fprintfn out_channel "end:\n;\n}"
    out_channel.Dispose ()
    printf "Created %s\n" fname
    ()

let print_c_program_pc_loop p (fname : string) =
    let out_channel = new System.IO.StreamWriter(fname)
    fprintfn out_channel "int nondet() { int a; return a; }"
    fprintfn out_channel "_Bool nondet_bool() { _Bool a; return a; }"
    fprintfn out_channel "int main() {"

    //sanitize var names, declare:
    let vars = variables p
    let var_map = ref Map.empty;
    let i = ref 1
    for v in vars do
        let new_v = "v" + (!i).ToString()
        var_map := Map.add v new_v !var_map
        i := !i + 1
        fprintfn out_channel "int %s = nondet();" new_v

    //map all location to outgoing transitions:
    let out_trans = new System.Collections.Generic.Dictionary<int, System.Collections.Generic.HashSet<command list * int>>()
    let add_to_set_dict (dict : System.Collections.Generic.Dictionary<int, System.Collections.Generic.HashSet<command list * int>>) k v =
        if dict.ContainsKey k then
            dict.[k].Add v
        else
            dict.Add(k, new System.Collections.Generic.HashSet<command list * int>())
            dict.[k].Add v
    for n in !p.active do
        let (k, cmds, k') = p.transitions.[n]
        add_to_set_dict out_trans k (cmds, k') |> ignore

    //first step:
    fprintfn out_channel "unsigned int pc = %i;" !p.initial
    fprintfn out_channel " while (pc != -1) {"
    fprintfn out_channel "  switch (pc) {"

    //encode transitions. Order locations first, putting initial and cutpoints first:
    let final_locs = ref []
    let locations = ref <| !p.initial :: (List.ofSeq (fst <| find_loops p).Keys)
    locations := !locations @ (List.ofSeq <| Seq.filter (fun pp -> not <| List.contains pp !locations) out_trans.Keys)
    for location in !locations do
        fprintfn out_channel "case %i:" location

        let trans = out_trans.[location]
        for (cmds, k') in trans do
            fprintfn out_channel " if (nondet_bool()) {"
            cmds
            |> List.iter (
                function
                    | Assume(_, f) ->
                        let sanitized_f = Formula.alpha (fun v -> (!var_map).[v]) f
                        fprintfn out_channel "  if (!( %s )) { pc = -1; break; }" (sanitized_f.pp);
                    | Assign(_, v, t) ->
                        let sanitized_v = (!var_map).[v]
                        let sanitized_t = Term.alpha (fun v -> (!var_map).[v]) t
                        fprintfn out_channel "  %s = %s;" (sanitized_v) (sanitized_t.pp);
                )
            ()
            fprintfn out_channel "  pc = %i; break;" k'
            if not(out_trans.ContainsKey k') then
                final_locs := k' :: !final_locs
            fprintfn out_channel " }"

        fprintfn out_channel " pc = -1; break;"

    fprintfn out_channel "default:\n pc = -1; break; }}}"
    out_channel.Dispose ()
    printf "Created %s\n" fname
    ()

let print_c_program p imperative_style fname =
    match imperative_style with
        | Parameters.Goto -> print_c_program_goto p fname
        | Parameters.Loop -> print_c_program_pc_loop p fname

let print_t2_program p (fname : string) =
    let out_channel = new System.IO.StreamWriter(fname)
    fprintfn out_channel "START: %i;\n" !p.initial

    let print_transition k cmds k' =
        fprintfn out_channel "FROM: %i;" k
        cmds |> Seq.iter (fun c -> c |> command2pp |> fprintfn out_channel "%s")
        fprintfn out_channel "TO: %i;\n" k'

    for n in !p.active do
        let (k, cmds, k') = p.transitions.[n]
        print_transition k cmds k'

let print_clauses p (fname : string) =
    let out_channel = new System.IO.StreamWriter(fname)

    //Prepare variable lists, print the actual transitions:
    let varPP (v : string) = v.Replace("^", "_")
    let varPPPrefix v = "_" + (varPP v)
    let preVarsString = !p.vars |> Seq.map (fun v -> varPPPrefix (v + "^0")) |> String.concat ", "
    let postVarsString = !p.vars |> Seq.map (fun v -> varPPPrefix (v + "^post")) |> String.concat ", "
    let trans_to_rule src cmds dst=
        let io_rel = Symex.path_to_relation [(src, cmds, dst)] !p.vars |> Relation.standardise_postvars
        let io_formula = Relation.formula io_rel
        sprintf "PC=%i,PCP=%i,%s" src dst (io_formula.clause_pp varPPPrefix)
    let transs = ref []
    for n in !p.active do
        let (k, cmds, k') = p.transitions.[n]
        transs := (trans_to_rule k cmds k')::!transs

    let (loops, _) = Programs.find_loops p
    let cps = loops.Keys
    let cpString = cps |> Seq.map (fun cp -> sprintf "PC = %i" cp) |> String.concat "; "

    fprintfn out_channel "init([PC, %s]) :- PC=%i." preVarsString !p.initial
    fprintfn out_channel "next([PC, %s], [PCP, %s]) :-" preVarsString postVarsString
    !transs |> String.concat ";\n  " |> fprintfn out_channel "  %s."
    fprintfn out_channel "cutpoint([PC, %s]) :- %s."  preVarsString cpString

    let ppvarString = !p.vars |> Seq.map varPP |> String.concat "', '"
    let ppPreVarsString = !p.vars |> Seq.map varPP |> String.concat "', '"
    let ppPostVarsString = !p.vars |> Seq.map varPP |> String.concat "\\'', '"
    fprintfn out_channel "query_naming(cutpoint, ['PC', '%s'])." ppvarString
    fprintfn out_channel "query_naming(init, ['PC', '%s'])." ppvarString
    fprintfn out_channel "query_naming(next, ['PC', '%s', 'PC\\'', '%s\\''])." ppPreVarsString ppPostVarsString

    out_channel.Dispose ()

let add_java_nondet_declaration java_nondet_style out_channel =
    fprintfn out_channel "  public static int nondet() {"
    match java_nondet_style with
    | Parameters.Aprove ->
        fprintfn out_channel "    return (new Object()).hashCode();"
    | Parameters.Julia ->
        fprintfn out_channel "    int res = (int) System.currentTimeMillis();"
        fprintfn out_channel "    int sign = (int) System.currentTimeMillis();"
        fprintfn out_channel "    if (sign %% 2 == 0) {"
        fprintfn out_channel "      res = -res;"
        fprintfn out_channel "    }"
        fprintfn out_channel "    return res;"
    fprintfn out_channel "  }"
    fprintfn out_channel "  public static boolean nondet_bool() { return (nondet() %% 2) == 0; }"

let print_java_program_goto p java_nondet_style class_name path =
    let out_channel = new System.IO.StreamWriter(path + "/" + class_name + ".java")
    fprintfn out_channel "public class %s {" class_name

    add_java_nondet_declaration java_nondet_style out_channel

    //sanitize var names, declare:
    let vars = variables p
    let var_map = ref Map.empty;
    let i = ref 1
    for v in vars do
        let new_v = "v" + (!i).ToString()
        var_map := Map.add v new_v !var_map
        i := !i + 1
        fprintfn out_channel "  public static int %s;" new_v

    fprintfn out_channel ""
    fprintfn out_channel "  public static void main(String[] args) {"

    let mutable i = 0 in
        for v in !var_map do
            fprintfn out_channel "    %s = args[%d].length() - args[%d].length();" v.Value (2*i) (2*i + 1)
            i <- i+1
    fprintfn out_channel ""

    let (loops, _) = find_loops p
    let cps = loops.Keys

    //map all location to outgoing transitions:
    let out_trans = new System.Collections.Generic.Dictionary<int, System.Collections.Generic.HashSet<command list * int>>()
    let add_to_set_dict (dict : System.Collections.Generic.Dictionary<int, System.Collections.Generic.HashSet<command list * int>>) k v =
        if dict.ContainsKey k then
            dict.[k].Add v
        else
            dict.Add(k, new System.Collections.Generic.HashSet<command list * int>())
            dict.[k].Add v
    for n in !p.active do
        let (k, cmds, k') = p.transitions.[n]
        add_to_set_dict out_trans k (cmds, k') |> ignore

    //first step:
    fprintfn out_channel "    %s();" (pp_label !p.initial cps)
    fprintfn out_channel "  }" // main

    //encode transitions. Order locations first, putting initial and cutpoints first:
    let final_locs = new System.Collections.Generic.HashSet<int>();
    let locations = ref <| !p.initial :: (List.ofSeq cps)
    locations := !locations @ (List.ofSeq <| Seq.filter (fun pp -> not <| List.contains pp !locations) out_trans.Keys)
    for location in !locations do
        fprintfn out_channel ""
        fprintfn out_channel "  public static void %s() {" (pp_label location cps)

        let trans = out_trans.[location]
        for (cmds, k') in trans do
            fprintfn out_channel "    if (nondet_bool()) {"
            cmds
            |> List.iter (
                function
                    | Assume(_, f) ->
                        let sanitized_f = Formula.alpha (fun v -> (!var_map).[v]) f
                        fprintfn out_channel "      if (!( %s )) return;" (sanitized_f.pp);
                    | Assign(_, v, t) ->
                        let sanitized_v = (!var_map).[v]
                        let sanitized_t = Term.alpha (fun v -> (!var_map).[v]) t
                        fprintfn out_channel "      %s = %s;" (sanitized_v) (sanitized_t.pp);
                )
            ()
            fprintfn out_channel "      %s();" (pp_label k' cps)
            fprintfn out_channel "      return;"
            if not(out_trans.ContainsKey k') then
                final_locs.Add k' |> ignore
            fprintfn out_channel "    }"

        fprintfn out_channel "  }"

    for final_loc in final_locs do
        fprintfn out_channel ""
        fprintfn out_channel "  public static void %s() {}" (pp_label final_loc cps)

    fprintfn out_channel "}" // class

    out_channel.Dispose ()
    printf "Created %s\n" class_name
    ()

let print_java_program_pc_loop p java_nondet_style class_name path =
    let out_channel = new System.IO.StreamWriter(path + "/" + class_name + ".java")
    fprintfn out_channel "public class %s {" class_name

    add_java_nondet_declaration java_nondet_style out_channel

    fprintfn out_channel "  public static void main(String[] args) {"

    //sanitize var names, declare:
    let vars = variables p
    let var_map = ref Map.empty;
    let mutable i = 0
    for v in vars do
        let new_v = "v" + (i+1).ToString()
        var_map := Map.add v new_v !var_map
        i <- i + 1
        fprintfn out_channel "    int %s = args[%d].length() - args[%d].length();" new_v (2*i) (2*i + 1)

    //map all location to outgoing transitions:
    let out_trans = new System.Collections.Generic.Dictionary<int, System.Collections.Generic.HashSet<command list * int>>()
    let add_to_set_dict (dict : System.Collections.Generic.Dictionary<int, System.Collections.Generic.HashSet<command list * int>>) k v =
        if dict.ContainsKey k then
            dict.[k].Add v
        else
            dict.Add(k, new System.Collections.Generic.HashSet<command list * int>())
            dict.[k].Add v
    for n in !p.active do
        let (k, cmds, k') = p.transitions.[n]
        add_to_set_dict out_trans k (cmds, k') |> ignore

    //first step:
    fprintfn out_channel "    int pc = %i;" !p.initial
    fprintfn out_channel "    while (pc != -1) {"
    fprintfn out_channel "      switch (pc) {"

    //encode transitions. Order locations first, putting initial and cutpoints first:
    let locations = ref <| !p.initial :: (List.ofSeq (fst <| find_loops p).Keys)
    locations := !locations @ (List.ofSeq <| Seq.filter (fun pp -> not <| List.contains pp !locations) out_trans.Keys)
    for location in !locations do
        fprintfn out_channel "        case %i:" location

        let trans = out_trans.[location]
        for (cmds, k') in trans do
            fprintfn out_channel "          if (nondet_bool()) {"
            cmds
            |> List.iter (
                function
                    | Assume(_, f) ->
                        let sanitized_f = Formula.alpha (fun v -> (!var_map).[v]) f
                        fprintfn out_channel "            if (!( %s )) { pc = -1; break; }" (sanitized_f.pp);
                    | Assign(_, v, t) ->
                        let sanitized_v = (!var_map).[v]
                        let sanitized_t = Term.alpha (fun v -> (!var_map).[v]) t
                        fprintfn out_channel "            %s = %s;" (sanitized_v) (sanitized_t.pp);
                )
            ()
            fprintfn out_channel "            pc = %i;" k'
            fprintfn out_channel "            break;"
            fprintfn out_channel "          }"

        fprintfn out_channel "          pc = -1;"
        fprintfn out_channel "          break;"

    fprintfn out_channel "        default:"
    fprintfn out_channel "          pc = -1;"
    fprintfn out_channel "          break;"
    fprintfn out_channel "      }"
    fprintfn out_channel "    }"
    fprintfn out_channel "  }"
    fprintfn out_channel "}"

    out_channel.Dispose ()
    printf "Created %s\n" class_name
    ()

let print_java_program p imperative_style class_name path =
    match imperative_style with
        | Parameters.Goto -> print_java_program_goto p class_name path
        | Parameters.Loop -> print_java_program_pc_loop p class_name path

let print_smtpushdown p (fname : string) =
    let out_channel = new System.IO.StreamWriter(fname)

    //Get all locations:
    let locations = new System.Collections.Generic.HashSet<int>() in
    for n in !p.active do
        let (k, _, k') = p.transitions.[n]
        ignore <| locations.Add k
        ignore <| locations.Add k'
    let locPP k = sprintf "l%i" k

    //Get the variable lists
    let pre_vars = !p.vars |> Set.map (sprintf "%s^0")
    let pre_vars_string = pre_vars |> Set.map (sprintf "(%s Int)") |> String.concat " "
    let post_vars = !p.vars |> Set.map (sprintf "%s^post")
    let post_vars_string = post_vars |> Set.map (sprintf "(%s Int)") |> String.concat " "
    let all_vars = Set.union pre_vars post_vars

    let rec get_unused v used = if Set.contains v used then get_unused ("_" + v) used else v
    let pc_pre_var = get_unused "pc^0" all_vars
    let pc_post_var = get_unused "pc^post" all_vars

    fprintf out_channel "(declare-sort Loc 0)\n";
    for l in locations do
        fprintf out_channel "(declare-const %s Loc)\n" (locPP l)
    fprintf out_channel "(assert (distinct %s))\n\n" (String.concat " " (List.ofSeq locations |> List.map locPP));

    fprintf out_channel "(define-fun cfg_init ( (pc Loc) (src Loc) (rel Bool) ) Bool\n";
    fprintf out_channel "  (and (= pc src) rel))\n\n";

    fprintf out_channel "(define-fun cfg_trans2 ( (pc Loc) (src Loc)\n";
    fprintf out_channel "                         (pc1 Loc) (dst Loc)\n";
    fprintf out_channel "                         (rel Bool) ) Bool\n";
    fprintf out_channel "  (and (= pc src) (= pc1 dst) rel))\n\n";

    fprintf out_channel "(define-fun cfg_trans3 ( (pc Loc) (exit Loc)\n";
    fprintf out_channel "                         (pc1 Loc) (call Loc)\n";
    fprintf out_channel "                         (pc2 Loc) (return Loc)\n";
    fprintf out_channel "                         (rel Bool) ) Bool\n";
    fprintf out_channel "  (and (= pc exit) (= pc1 call) (= pc2 return) rel))\n\n";

    fprintf out_channel "(define-fun init_main ( (%s Loc) %s ) Bool\n" pc_pre_var pre_vars_string;
    fprintf out_channel "  (cfg_init %s %s true))\n\n" pc_pre_var (locPP !p.initial);

    fprintf out_channel "(define-fun next_main (\n";
    fprintf out_channel "                 (%s Loc) %s\n" pc_pre_var pre_vars_string;
    fprintf out_channel "                 (%s Loc) %s\n" pc_post_var post_vars_string;
    fprintf out_channel "             ) Bool\n";
    fprintf out_channel "  (or\n";

    for n in !p.active do
        let (src, cmds, dst) = p.transitions.[n]
        let io_rel = Symex.path_to_relation [(src, cmds, dst)] !p.vars |> Relation.standardise_postvars
        let io_formula = Relation.formula io_rel
        let ex_vars = Set.fold (fun vars bound_var -> Set.remove bound_var vars) (Formula.freevars io_formula) all_vars
        if ex_vars.IsEmpty then
            fprintf out_channel "    (cfg_trans2 %s %s %s %s %s)\n" pc_pre_var (locPP src) pc_post_var (locPP dst) (io_formula.prefix_pp)
        else
            fprintf out_channel "    (cfg_trans2 %s %s %s %s (exists ( %s ) %s))\n"
                pc_pre_var
                (locPP src)
                pc_post_var
                (locPP dst)
                (ex_vars |> Set.map (sprintf "(%s Int)") |> String.concat " ")
                (io_formula.prefix_pp)
    fprintf out_channel "  )\n)\n";
    out_channel.Dispose ()

    ()
