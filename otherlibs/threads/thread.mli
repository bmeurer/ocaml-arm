(***********************************************************************)
(*                                                                     *)
(*                         Caml Special Light                          *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1995 Institut National de Recherche en Informatique et   *)
(*  Automatique.  Distributed only by permission.                      *)
(*                                                                     *)
(***********************************************************************)

(* $Id$ *)

(* Module [Thread]: user-level lightweight threads *)

type t
val new : ('a -> 'b) -> 'a -> t
val exit : unit -> unit
val self : unit -> t
val kill : t -> unit
val sleep : unit -> unit
val wakeup : t -> unit
val wait_descr : Unix.file_descr -> unit
val wait_inchan : in_channel -> unit
val delay: float -> unit

(*--*)

val critical_section: bool ref
