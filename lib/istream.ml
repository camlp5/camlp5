(* camlp5r *)
(***********************************************************************)
(*                                                                     *)
(*                             Ocaml                                   *)
(*                                                                     *)
(*        Daniel de Rauglaudre, projet Cristal, INRIA Rocquencourt     *)
(*                                                                     *)
(*  Copyright 1997 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* $Id$ *)

(* The fields of type t are not mutable to preserve polymorphism of
   the empty stream. This is type safe because the empty stream is never
   patched. *)

type t α = { count : int; data : data α }
and data α =
  [ Sempty
  | Scons of α and data α
  | Sapp of data α and data α
  | Slazy of Lazy.t (data α)
  | Sgen of gen α
  | Sbuffio of buffio ]
and gen α = { curr : mutable option (option α); func : int → option α }
and buffio =
  { ic : in_channel; buff : Bytes.t; len : mutable int; ind : mutable int }
;
exception Failure;
exception Error of string;

external count : t α → int = "%field0";
external set_count : t α → int → unit = "%setfield0";
value set_data (s : t α) (d : data α) =
  Obj.set_field (Obj.repr s) 1 (Obj.repr d)
;

value fill_buff b = do {
  b.len := input b.ic b.buff 0 (Bytes.length b.buff);
  b.ind := 0
};

value rec get_data count d =
  match d with
  [ Sempty | Scons _ _ → d
  | Sapp d1 d2 →
      match get_data count d1 with
      [ Scons a d11 → Scons a (Sapp d11 d2)
      | Sempty → get_data count d2
      | _ → assert False ]
  | Sgen {curr = Some None; func = _} → Sempty
  | Sgen ({curr = Some (Some a); func = f} as g) → do {
      g.curr := None;
      Scons a d
    }
  | Sgen g →
      match g.func count with
      [ None → do { g.curr := Some None; Sempty }
      | Some a → Scons a d ]
  | Sbuffio b → do {
      if b.ind >= b.len then fill_buff b else ();
      if b.len == 0 then Sempty
      else do {
        let r = Obj.magic (Bytes.unsafe_get b.buff b.ind) in
        (* Warning: anyone using g thinks that an item has been read *)
        b.ind := succ b.ind;
        Scons r d
      }
    }
  | Slazy f → get_data count (Lazy.force f) ]
;

value rec peek s =
  (* consult the first item of s *)
  match
    s.data
  with
  [ Sempty → None
  | Scons a _ → Some a
  | Sapp _ _ →
      match get_data s.count s.data with
      [ Scons a _ as d → do { set_data s d; Some a }
      | Sempty → None
      | _ → assert False ]
  | Slazy f → do { set_data s (Lazy.force f); peek s }
  | Sgen {curr = Some a} → a
  | Sgen g → do {
      let x = g.func s.count in
      g.curr := Some x;
      x
    }
  | Sbuffio b → do {
      if b.ind >= b.len then fill_buff b else ();
      if b.len == 0 then do { set_data s Sempty; None }
      else Some (Obj.magic (Bytes.unsafe_get b.buff b.ind))
    } ]
;

value rec junk s =
  match s.data with
  [ Scons _ d → do { set_count s (succ s.count); set_data s d }
  | Sgen ({curr = Some _} as g) → do {
      set_count s (succ s.count);
      g.curr := None
    }
  | Sbuffio b → do { set_count s (succ s.count); b.ind := succ b.ind }
  | _ →
      match peek s with
      [ None → ()
      | Some _ → junk s ] ]
;

value rec nget n s =
  if n <= 0 then ([], s.data, 0)
  else
    match peek s with
    [ Some a → do {
        junk s;
        let (al, d, k) = nget (pred n) s in
        ([a :: al], Scons a d, succ k)
      }
    | None → ([], s.data, 0) ]
;

value npeek n s = do {
  let (al, d, len) = nget n s in
  set_count s (s.count - len);
  set_data s d;
  al
};

value next s =
  match peek s with
  [ Some a → do { junk s; a }
  | None → raise Failure ]
;

value empty s =
  match peek s with
  [ Some _ → raise Failure
  | None → () ]
;

value iter f strm =
  do_rec () where rec do_rec () =
    match peek strm with
    [ Some a → do { junk strm; ignore (f a); do_rec () }
    | None → () ]
;

(* Istream building functions *)

value from f = {count = 0; data = Sgen {curr = None; func = f}};

value of_list l =
  {count = 0; data = List.fold_right (fun x l → Scons x l) l Sempty}
;

value of_string s =
  from (fun c → if c < String.length s then Some s.[c] else None)
;

value of_channel ic =
  {count = 0;
   data = Sbuffio {ic = ic; buff = Bytes.create 4096; len = 0; ind = 0}}
;

(* Istream expressions builders *)

value iapp i s = {count = 0; data = Sapp i.data s.data};
value icons i s = {count = 0; data = Scons i s.data};
value ising i = {count = 0; data = Scons i Sempty};

value lapp f s = {count = 0; data = Slazy (lazy (Sapp (f ()).data s.data))};
value lcons f s = {count = 0; data = Slazy (lazy (Scons (f ()) s.data))};
value lsing f = {count = 0; data = Slazy (lazy (Scons (f ()) Sempty))};

value sempty = {count = 0; data = Sempty};
value slazy f = {count = 0; data = Slazy (lazy (f ()).data)};

(* For debugging use *)

value rec dump f s = do {
  print_string "{count = ";
  print_int s.count;
  print_string "; data = ";
  dump_data f s.data;
  print_string "}";
  print_newline ()
}
and dump_data f =
  fun
  [ Sempty → print_string "Sempty"
  | Scons a d → do {
      print_string "Scons (";
      f a;
      print_string ", ";
      dump_data f d;
      print_string ")"
    }
  | Sapp d1 d2 → do {
      print_string "Sapp (";
      dump_data f d1;
      print_string ", ";
      dump_data f d2;
      print_string ")"
    }
  | Slazy _ → print_string "Slazy"
  | Sgen _ → print_string "Sgen"
  | Sbuffio b → print_string "Sbuffio" ]
;
