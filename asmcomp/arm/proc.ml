(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*                  Benedikt Meurer, University of Siegen              *)
(*                                                                     *)
(*    Copyright 2011 Lehrstuhl für Compilerbau und Softwareanalyse,    *)
(*    Universität Siegen. All rights reserved. This file is distri-    *)
(*    buted under the terms of the Q Public License version 1.0.       *)
(*                                                                     *)
(***********************************************************************)

(* $Id$ *)

(* Description of the ARM processor *)

open Misc
open Cmm
open Reg
open Arch
open Mach

(* Instruction selection *)

let word_addressed = false

(* Registers available for register allocation *)

(* Integer register map:
    r0 - r3               general purpose (not preserved)
    r4 - r7               general purpose (preserved)
    r8                    trap pointer (preserved)
    r9                    platform register, usually reserved
    r10                   allocation pointer (preserved)
    r11                   allocation limit (preserved)
    r12                   intra-procedural scratch register (not preserved)
    r13                   stack pointer
    r14                   return address
    r15                   program counter
   Floatinng-point register map (VFPv3-D16):
    d0 - d7               general purpose (not preserved)
    d8 - d15              general purpose (preserved)
*)

let int_reg_name =
  [| "r0"; "r1"; "r2"; "r3"; "r4"; "r5"; "r6"; "r7"; "r12" |]

let float_reg_name =
  if vfp3 then
    [| "d0"; "d1"; "d2"; "d3"; "d4"; "d5"; "d6"; "d7";
       "d8"; "d9"; "d10"; "d11"; "d12"; "d13"; "d14"; "d15" |]
  else
    [||]

let num_register_classes = 2

let register_class r =
  match r.typ with
    Int
  | Addr -> 0
  | Float -> 1

let num_available_registers =
  [| Array.length int_reg_name; Array.length float_reg_name |]

let first_available_register = [| 0; 100 |]

let register_name r =
  if r < 100 then int_reg_name.(r) else float_reg_name.(r - 100)

let rotate_registers = true

(* Representation of hard registers by pseudo-registers *)

let hard_reg cl ty =
  let o = first_available_register.(cl) in
  let v = Array.create num_available_registers.(cl) Reg.dummy in
  for i = 0 to Array.length v - 1 do
    v.(i) <- Reg.at_location ty (Reg (i + o))
  done;
  v

let hard_int_reg =
  hard_reg 0 Int

let hard_float_reg =
  hard_reg 1 Float

let all_phys_regs =
  Array.append hard_int_reg hard_float_reg

let phys_reg n =
  if n < 100 then hard_int_reg.(n) else hard_float_reg.(n - 100)

let stack_slot slot ty =
  Reg.at_location ty (Stack slot)

(* Calling conventions *)

let calling_conventions
    first_int last_int first_float last_float make_stack arg =
  let loc = Array.create (Array.length arg) Reg.dummy in
  let int = ref first_int in
  let float = ref first_float in
  let ofs = ref 0 in
  for i = 0 to Array.length arg - 1 do
    match arg.(i).typ with
      Int | Addr as ty ->
        if !int <= last_int then begin
          loc.(i) <- phys_reg !int;
          incr int
        end else begin
          loc.(i) <- stack_slot (make_stack !ofs) ty;
          ofs := !ofs + size_int
        end
    | Float ->
        assert vfp3;
        if !float <= last_float then begin
          loc.(i) <- phys_reg !float;
          incr float
        end else begin
          ofs := Misc.align !ofs 8;
          loc.(i) <- stack_slot (make_stack !ofs) Float;
          ofs := !ofs + size_float
        end
  done;
  (loc, Misc.align !ofs 8)  (* keep stack 8-aligned *)

let incoming ofs = Incoming ofs
let outgoing ofs = Outgoing ofs
let not_supported ofs = fatal_error "Proc.loc_results: cannot call"

let loc_arguments arg =
  calling_conventions 0 7 100 115 outgoing arg
let loc_parameters arg =
  let (loc, _) = calling_conventions 0 7 100 115 incoming arg in loc
let loc_results res =
  let (loc, _) = calling_conventions 0 7 100 115 not_supported res in loc

(* C calling convention:
     first integer args in r0 ... r3
     first float args in d0 ... d7 (ARMv7+VFPv3)
     remaining args on stack.
   Return value in r0 or r0,r1 / d0. *)

let loc_external_arguments arg =
  calling_conventions 0 3 100 107 outgoing arg
let loc_external_results res =
  if vfp3 then
    let (loc, _) = calling_conventions 0 0 100 100 not_supported res in loc
  else
    let (loc, _) = calling_conventions 0 1 100 100 not_supported res in loc

let loc_exn_bucket = phys_reg 0

(* Registers destroyed by operations *)

let destroyed_at_c_call_noalloc =
  if vfp3 then                         (* r4-r7, d8-d15 preserved *)
    Array.of_list(List.map phys_reg
      [0;1;2;3;8;
       100;101;102;103;104;105;106;107])
  else                                  (* r4-r7 preserved *)
    Array.of_list(List.map phys_reg
      [0;1;2;3;8])

let destroyed_at_c_call =
  Array.append
    destroyed_at_c_call_noalloc
    (Array.of_list(List.map phys_reg [4;5;6;7]))

let destroyed_at_oper = function
    Iop(Icall_ind | Icall_imm _ ) ->
      all_phys_regs
  | Iop(Iextcall(_, true)) ->
      destroyed_at_c_call
  | Iop(Iextcall(_, false)) ->
      destroyed_at_c_call_noalloc
  | Iop(Ialloc n) ->
      [|phys_reg 8|]              (* r12 destroyed *)
  | Iop(Iconst_symbol _) when !pic_code ->
      [|phys_reg 3; phys_reg 8|]  (* r3 and r12 destroyed *)
  | Iop(Iintoffloat | Istore(Single, _)) when vfp3 ->
      [|phys_reg 107|]            (* d7 (s14-s15) destroyed *)
  | _ -> [||]

let destroyed_at_raise = all_phys_regs

(* Maximal register pressure *)

let safe_register_pressure = function
    Iextcall(_, _) -> 4
  | _ -> 9
let max_register_pressure = function
    Iextcall(_, _) -> [| 4; 10 |]
  | _ -> [| 9; 16 |]

(* Layout of the stack *)

let num_stack_slots = [| 0; 0 |]
let contains_calls = ref false

(* Calling the assembler *)

let assemble_file infile outfile =
  Ccomp.command (Config.asm ^ " -o " ^
                 Filename.quote outfile ^ " " ^ Filename.quote infile)
