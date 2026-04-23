(* camlp5r *)
(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*         Daniel de Rauglaudre, projet Cristal, INRIA Rocquencourt       *)
(*                                                                        *)
(*   Copyright 1997 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

type t 'a = option (cell 'a)
and cell 'a = { count : mutable int; data : mutable data 'a }
and data 'a =
  [ Sempty
  | Scons of 'a and data 'a
  | Sapp of data 'a and data 'a
  | Slazy of Lazy.t (data 'a)
  | Sgen of gen 'a
  | Sbuffio : buffio → data char ]
and gen 'a = { curr : mutable option (option 'a); func : int → option 'a }
and buffio =
  { ic : in_channel; buff : bytes; len : mutable int; ind : mutable int }
;

exception Failure;
exception Error of string;

value count =
  fun
  [ None → 0
  | Some {count = count} → count ]
;
value data =
  fun
  [ None → Sempty
  | Some {data = data} → data ]
;

value fill_buff b = do {
  b.len := input b.ic b.buff 0 (Bytes.length b.buff);
  b.ind := 0
};


value rec get_data : type v . int → data v → data v =
  fun count d →
    match d with
    [ Sempty | Scons _ _ → d
    | Sapp d1 d2 →
        match get_data count d1 with
        [ Scons a d11 → Scons a (Sapp d11 d2)
        | Sempty → get_data count d2
        | _ → assert False ]
    | Sgen {curr = Some None} → Sempty
    | Sgen ({curr = Some (Some a)} as g) → do { g.curr := None; Scons a d }
    | Sgen g →
        match g.func count with
        [ None → do { g.curr := Some None; Sempty }
        | Some a → Scons a d ]
    | Sbuffio b → do {
        if b.ind >= b.len then fill_buff b else ();
        if b.len == 0 then Sempty
        else do {
          let r = Bytes.unsafe_get b.buff b.ind in
          (* Warning: anyone using g thinks that an item has been read *)
          b.
          ind :=
            succ b.ind;
          Scons r d
        }
      }
    | Slazy f → get_data count (Lazy.force f) ]
;


value rec peek_data : type v . cell v → option v =
  fun s →
    (* consult the first item of s *)
    match
      s.data
    with
    [ Sempty → None
    | Scons a _ → Some a
    | Sapp _ _ →
        match get_data s.count s.data with
        [ Scons a _ as d → do { s.data := d; Some a }
        | Sempty → None
        | _ → assert False ]
    | Slazy f → do { s.data := Lazy.force f; peek_data s }
    | Sgen {curr = Some a} → a
    | Sgen g → do {
        let x = g.func s.count in
        g.curr := Some x;
        x
      }
    | Sbuffio b → do {
        if b.ind >= b.len then fill_buff b else ();
        if b.len == 0 then do { s.data := Sempty; None }
        else Some (Bytes.unsafe_get b.buff b.ind)
      } ]
;


value peek =
  fun
  [ None → None
  | Some s → peek_data s ]
;


value rec junk_data : type v . cell v → unit =
  fun s →
    match s.data with
    [ Scons _ d → do { s.count := succ s.count; s.data := d }
    | Sgen ({curr = Some _} as g) → do {
        s.count := succ s.count;
        g.curr := None
      }
    | Sbuffio b → do { s.count := succ s.count; b.ind := succ b.ind }
    | _ →
        match peek_data s with
        [ None → ()
        | Some _ → junk_data s ] ]
;


value junk =
  fun
  [ None → ()
  | Some data → junk_data data ]
;

value rec nget_data n s =
  if n <= 0 then ([], s.data, 0)
  else
    match peek_data s with
    [ Some a → do {
        junk_data s;
        let (al, d, k) = nget_data (pred n) s in
        ([a :: al], Scons a d, succ k)
      }
    | None → ([], s.data, 0) ]
;


value npeek_data n s = do {
  let (al, d, len) = nget_data n s in
  s.count := s.count - len;
  s.data := d;
  al
};


value npeek n =
  fun
  [ None → []
  | Some d → npeek_data n d ]
;

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

value from f = Some {count = 0; data = Sgen {curr = None; func = f}};

value of_list l =
  Some {count = 0; data = List.fold_right (fun x l → Scons x l) l Sempty}
;


value of_string s =
  let count = ref 0 in
  from
    (fun _ →
       (* We cannot use the index passed by the [from] function directly
          because it returns the current stream count, with absolutely no
          guarantee that it will start from 0. For example, in the case
          of [Istream.icons 'c' (Istream.from_string "ab")], the first
          access to the string will be made with count [1] already.
       *)
       let c =
         count.val
       in
       if c < String.length s then do { incr count; Some s.[c] } else None)
;


value of_bytes s =
  let count = ref 0 in
  from
    (fun _ →
       let c = count.val in
       if c < Bytes.length s then do { incr count; Some (Bytes.get s c) }
       else None)
;


value of_channel ic =
  Some
    {count = 0;
     data = Sbuffio {ic = ic; buff = Bytes.create 4096; len = 0; ind = 0}}
;


(* Istream expressions builders *)

value iapp i s = Some {count = 0; data = Sapp (data i) (data s)};
value icons i s = Some {count = 0; data = Scons i (data s)};
value ising i = Some {count = 0; data = Scons i Sempty};

value lapp f s =
  Some {count = 0; data = Slazy (lazy (Sapp (data (f ())) (data s)))}
;

value lcons f s =
  Some {count = 0; data = Slazy (lazy (Scons (f ()) (data s)))}
;
value lsing f = Some {count = 0; data = Slazy (lazy (Scons (f ()) Sempty))};

value sempty = None;
value slazy f = Some {count = 0; data = Slazy (lazy (data (f ())))};

(* For debugging use *)

value rec dump : type v . (v → unit) → t v → unit =
  fun f s -> do {
    print_string "{count = ";
    print_int (count s);
    print_string "; data = ";
    dump_data f (data s);
    print_string "}";
    print_newline ()
  }
and dump_data : type v . (v → unit) → data v → unit =
  fun f →
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
    | Sbuffio _ → print_string "Sbuffio" ]
;
