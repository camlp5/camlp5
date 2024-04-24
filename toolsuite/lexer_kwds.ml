(* camlp5r *)
(* o_lexer_test.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Pcaml ;

value generate_keywords () =
  let lexer = Grammar.glexer Pcaml.gram in
  let kwds = lexer.Plexing.kwds in
  let l = Hashtbl.fold (fun k _ acc -> [k::acc]) kwds [] in
  let l = List.sort Stdlib.compare l in
  Fmt.(pf stdout {foo|(* camlp5r *)

value keywords = [%a];
value keywords_hash = Hashtbl.create 23 ;
List.iter (fun k -> Hashtbl.add keywords_hash k k) keywords ;
|foo}
       (list ~{sep=(const string ";\n\t")} Dump.string) l)
;

value _ = 
if not Sys.interactive.val then
  generate_keywords ()
else ()
;
