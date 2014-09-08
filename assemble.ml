open Assemblage

let lib_pkgs = [
  pkg "compiler-libs.common";
  pkg "compiler-libs.optcomp";
  pkg "findlib";
]

let findlibUnits  = unit "findlibUnits" (`Path ["lib"])

let l = lib ~deps:lib_pkgs "ocamlfind-units" (`Units [findlibUnits])

let () = assemble (project "ocamlfind-units" [l])
