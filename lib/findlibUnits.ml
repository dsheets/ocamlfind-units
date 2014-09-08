(*
 * Copyright (c) 2014 David Sheets <sheets@alum.mit.edu>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 *)

open Printf

module Map = Map.Make(String)
module Set = Set.Make(String)

type state = {
  sublibraries_of_package : Set.t Map.t;
  packages_of_dir         : Set.t Map.t;
}

type source =
| Archive of string
| Meta
| Path

type u = {
  name   : string; (** The name of the module the compilation unit represents *)
  path   : string; (** The path where the compilation unit is found *)
  cmi    : string; (** The filename of the cmi containing the unit *)
  source : source; (** The means by which the unit's membership was inferred *)
}

type t = u Map.t Map.t

let combine_source a b = match a, b with
  | Path,      _ | _, Path      -> Path
  | Archive a, _ | _, Archive a -> Archive a
  | Meta,   Meta                -> Meta

let unit_name_of_path path =
  let file = Filename.basename path in
  let file = String.(sub file 0 (index file '.')) in
  let first = String.sub file 0 1 in
  let rest = String.(sub file 1 (length file - 1)) in
  String.iteri (fun i -> function
  | '-' -> Bytes.set rest i '_'
  | _ -> ()) rest;
  let name = String.uppercase first ^ rest in
  name

let rec cmis_of_dir set dir =
  try
    let path = Unix.readdir dir in
    if Filename.check_suffix path ".cmi"
    then cmis_of_dir (Set.add path set) dir
    else cmis_of_dir set dir
  with End_of_file -> Unix.closedir dir; set

let is_subpackage name =
  try ignore (String.index name '.'); true with Not_found -> false

let root_package lib =
  try
    let dot = String.index lib '.' in
    String.sub lib 0 dot
  with Not_found -> lib

let sources_of_path_interfaces state dir name =
  if is_subpackage name then None (* we'll conflict *)
  else
    try
      match Set.elements (Map.find dir state.packages_of_dir) with
      | [] -> failwith
        "FindlibUnits: package directory index inversion was corrupted"
      | lib::libs ->
        let root = root_package lib in
        if name = root
        then
          if List.for_all (fun lib -> root_package lib = root) libs
          then 
            let dir = Unix.opendir dir in
            Some (Set.fold (fun file ->
              Map.add (unit_name_of_path file) Path
            ) (cmis_of_dir Set.empty dir) Map.empty)
          else None (* ambiguous *)
        else None (* ambiguous *)
    with Not_found ->
      failwith "FindlibUnits: package directory index inversion failed"

(* This really is as stupid as it looks. If you know of a better way
   to query findlib, please tell us. *)
let stupid_prefix = " Unit name: "
let prefix_len = String.length stupid_prefix
let rec extract_units_from_stupid_string map stupid_string =
  let len = String.length stupid_string in
  if len < prefix_len
  then
    if stupid_string = " " then map
    else failwith
      ("findlib put this at the end of browse_interfaces: "^stupid_string)
  else
    let prefix = String.sub stupid_string 0 prefix_len in
    if prefix = stupid_prefix
    then
      let next = String.sub stupid_string prefix_len (len - prefix_len) in
      let space = String.index next ' ' in
      let unit_name = String.sub next 0 space in
      let next = String.sub next space (String.length next - space) in
      extract_units_from_stupid_string (Map.add unit_name Meta map) next
    else failwith ("findlib put this in browse_interfaces: "^stupid_string)

(* The compilation units in a given library from browse_interfaces *)
let sources_of_browse_interfaces name =
  let open Fl_package_base in
  let open Fl_metascanner in
  let fl_pkg = query name in
  let browse_interfaces = List.fold_left (fun l -> function
    | { def_var = "browse_interfaces"; def_value } -> def_value::l
    | _ -> l
  ) [] fl_pkg.package_defs in
  match browse_interfaces with
  | [] -> None
  | _::_::_ -> failwith
    ("findlib's schema is broken (multiple browse_interfaces for "^name)
  | [stupid_string] ->
    Some (extract_units_from_stupid_string Map.empty stupid_string)

let extract_units_from_cma dir cma =
  let path = Filename.concat dir cma in
  let ic = open_in_bin path in
  let buffer = really_input_string ic (String.length Config.cma_magic_number) in
  if buffer = Config.cma_magic_number
  then Cmo_format.(
    let pos_toc = input_binary_int ic in
    seek_in ic pos_toc;
    let toc = (input_value ic : library) in
    close_in ic;
    List.map (fun cu -> cu.cu_name) toc.lib_units
  ) else
    failwith ("cma " ^ cma ^ " doesn't have the right magic number")

let extract_units_from_cmxa dir cmxa =
  let open Unix in
  let path = Filename.concat dir cmxa in
  try
    access path [];
    let infos = Compilenv.read_library_info path in
    List.map (fun (ui, _) -> ui.Cmx_format.ui_name) infos.Cmx_format.lib_units
  with Unix_error (ENOENT, _, _) -> (* Maybe native wasn't installed... *) []

let is_native preds = List.mem (`Pred "native") preds
let is_byte preds = List.mem (`Pred "byte") preds

let rec split_by_space acc space_delimited =
  let acc_ref = ref [] in
  match
    try
      let space = String.index space_delimited ' ' in
      let first = String.sub space_delimited 0 space in
      let next = String.sub space_delimited
        (space+1) (String.length space_delimited - space - 1)
      in
      acc_ref := first::acc;
      Some next
    with Not_found -> acc_ref := space_delimited::acc; None
  with None -> !acc_ref | Some next -> split_by_space !acc_ref next

(* The interfaces in a library from its archive *)
let sources_of_archive_interfaces dir name =
  let open Fl_package_base in
  let open Fl_metascanner in
  let fl_pkg = query name in
  let natives = List.fold_left (fun l -> function
    | { def_var = "archive"; def_preds; def_value } when is_native def_preds ->
      List.rev_append (split_by_space [] def_value) l
    | _ -> l
  ) [] fl_pkg.package_defs in
  let bytes = List.fold_left (fun l -> function
    | { def_var = "archive"; def_preds; def_value } when is_byte def_preds ->
      (* To work around findlib's design, sometimes archives are
         necessarily empty. *)
      if def_value = "" then l
      else List.rev_append (split_by_space [] def_value) l
    | _ -> l
  ) [] fl_pkg.package_defs in
  match natives, bytes with
  | [],  [] -> None
  | ns,  bs ->
    let byte_map = List.fold_left (fun map cma ->
      (* People sometimes have to mark objects as archives thanks to findlib. *)
      if Filename.check_suffix cma ".cmo"
      then Map.add (unit_name_of_path cma) (Archive cma) map
      else if Filename.check_suffix cma ".o"
      (* Some libraries, e.g. ocamlnet, put native objects into the
         archive line. *)
      then map
      else List.fold_left (fun map unit ->
        Map.add unit (Archive cma) map
      ) map (extract_units_from_cma dir cma)
    ) Map.empty bs in
    let native_map = List.fold_left (fun map cmxa ->
      (* People sometimes have to mark objects as archives thanks to findlib. *)
      if Filename.(check_suffix cmxa ".cmx" || check_suffix cmxa ".cmxs")
      then Map.add (unit_name_of_path cmxa) (Archive cmxa) map
      else if Filename.check_suffix cmxa ".o"
      (* Some libraries, e.g. ocamlnet, put native objects into the
         archive line. *)
      then map
      else List.fold_left (fun map unit ->
        Map.add unit (Archive cmxa) map
      ) map (extract_units_from_cmxa dir cmxa)
    ) Map.empty ns in
    Some (Map.merge (fun unit a_opt b_opt -> match a_opt, b_opt with
    | None, None -> None
    | Some a, None | None, Some a -> Some a
    | Some a, Some b -> Some (combine_source a b)
    ) byte_map native_map)

(* For a unit name, give the existing cmi corresponding. *)
let cmi_of_unit_name dir unit_name =
  let exact = Filename.concat dir (unit_name ^ ".cmi") in
  let open Unix in
  try
    access exact [];
    Some exact
  with Unix_error (ENOENT, _, _) ->
    let len = String.length unit_name in
    let first_lower = String.(lowercase (sub unit_name 0 1)) in
    let filename = first_lower ^ (String.sub unit_name 1 (len - 1)) ^ ".cmi" in
    let cmi = Filename.concat dir filename in
    try
      access cmi [];
      Some cmi
    with Unix_error (ENOENT, _, _) ->
      (* hidden cmi or our error; indistinguishable *)
      None

let map_add_with_source name unit map =
  try
    let existing = Map.find name map in
    if existing.name = unit.name then
      if existing.path = unit.path then
        if existing.cmi  = unit.cmi then
          let unit = {
            existing with source = combine_source existing.source unit.source
          } in Map.add name unit map
        else failwith
          (sprintf "FindlibUnits: unit %s in %s found 2 cmis: %s and %s"
             unit.name unit.path existing.cmi unit.cmi)
      else failwith
        (sprintf "FindlibUnits: unit %s found in 2 paths: %s and %s"
           unit.name existing.path unit.path)
    else failwith
      (sprintf "FindlibUnits: %s is called both %s and %s"
         name existing.name unit.name)
  with Not_found ->
    Map.add name unit map

let add_unit_of_source_name path name source map =
  match cmi_of_unit_name path name with
  | Some cmi -> map_add_with_source name { name; path; cmi; source; } map
  | None -> map

let of_package_only state name =
  let dir = Findlib.package_directory name in
  Map.fold (add_unit_of_source_name dir)
    (match sources_of_path_interfaces state dir name with
    | Some source_map -> source_map
    | None -> match sources_of_archive_interfaces dir name with
      | Some source_map -> source_map
      | None -> match sources_of_browse_interfaces name with
        | Some source_map -> source_map
        | None ->
          (* Maybe findlib knows something but it's too convoluted to
             coerce it to tell us. If you know how to query findlib
             better, please tell us! *)
          Map.empty
    ) Map.empty

let map_set_add map k v =
  try
    let set = Map.find k map in
    Map.add k (Set.add v set) map
  with Not_found ->
    Map.add k (Set.singleton v) map

(* TODO: re-init? refresh? *)
let state () =
  Findlib.init ();
  let all_libs = Fl_package_base.list_packages () in
  let sublibraries_of_package, packages_of_dir = List.fold_left
    (fun (s_p,p_d) lib ->
      let s_p = map_set_add s_p (root_package lib) lib in
      let p_d =
        let dir = Findlib.package_directory lib in
        map_set_add p_d dir lib
      in
      (s_p, p_d)
    ) (Map.empty,Map.empty) all_libs
  in
  { sublibraries_of_package; packages_of_dir }

let of_package_set state set =
  let sublibs,rootlibs = Set.partition is_subpackage set in
  let subunits = Set.fold (fun name map ->
    Map.add name (of_package_only state name) map
  ) sublibs Map.empty in
  Set.fold (fun name submap ->
    let child_units = Map.(fold (fun _k ->
      fold (fun unit_name _u -> Set.add unit_name)
    ) (filter (fun k _v -> name = root_package k) submap)) Set.empty in
    let unit_map = of_package_only state name in
    Map.(add name (filter (fun unit_name _u ->
      not (Set.mem unit_name child_units)
    ) unit_map)) submap
  ) rootlibs subunits

let of_package state name =
  let sublibs =
    try Map.find name state.sublibraries_of_package
    with Not_found -> Set.empty
  in
  of_package_set state sublibs

let all state =
  let all = Map.fold (fun _k sublibs set ->
    Set.union sublibs set
  ) state.sublibraries_of_package Set.empty in
  of_package_set state all
