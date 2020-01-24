(* camlp5r *)
(* testutil.ml,v *)

value pa s = let (ast, _) = Pcaml.parse_implem.val (Stream.of_string s) in ast ;
Pcaml.inter_phrases.val := Some " ;\n" ;
value sep = match Pcaml.inter_phrases.val with [ None -> "" | Some s -> s ] ;
value pr l = 
  let b = Buffer.create 23 in do {
    List.iter (fun (ast, _) -> 
      let s = Eprinter.apply Pcaml.pr_str_item Pprintf.empty_pc ast in do {
        Buffer.add_string b s ;
        Buffer.add_string b sep ;
      }) l ;
    Buffer.contents b
  }
;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
