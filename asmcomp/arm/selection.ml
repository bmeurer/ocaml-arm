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

(* Instruction selection for the ARM processor *)

open Misc
open Cmm
open Reg
open Arch
open Proc
open Mach

(* We have 12-bit + sign byte offsets for word accesses,
   8-bit + sign word offsets for float accesses,
   and 8-bit + sign byte offsets for bytes and shorts.
   Use lowest common denominator. *)

let is_offset n = n < 256 && n > -256

let is_intconst = function
    Cconst_int _ | Cconst_natint _ -> true
  | _ -> false

(* Special constraints on operand and result registers *)

exception Use_default

let pseudoregs_for_operation op arg res =
  match op with
  (* For mul rd,rm,rs and mla rd,rm,rs,ra (pre-ARMv6) the registers rm
     and rd must be different. We deal with this by pretending that rm
     is also a result of the mul / mla operation. *)
    Iintop Imul | Ispecific Imla when armv < 6 ->
      (arg, [| res.(0); arg.(0) |])
  (* Soft-float Iabsf and Inegf: arg.(0) and res.(0) must be the same *)
  | Iabsf | Inegf when not vfp3 ->
      ([|res.(0); arg.(1)|], res)
  (* VFPv3 Imacf...Inmscf: arg.(0) and res.(0) must be the same *)
  | Ispecific(Imacf | Inmacf | Imscf | Inmscf) ->
      let arg' = Array.copy arg in
      arg'.(0) <- res.(0);
      (arg', res)
  (* Other instructions are regular *)
  | _ -> raise Use_default

(* Instruction selection *)
class selector = object(self)

inherit Selectgen.selector_generic as super

method! regs_for tyv =
  Reg.createv (if vfp3 then
                 tyv
               else begin
                 (* Expand floats into pairs of integer registers (softfp) *)
                 let rec expand = function
                   [] -> []
                 | Float :: tyl -> Int :: Int :: expand tyl
                 | ty :: tyl -> ty :: expand tyl in
                 Array.of_list (expand (Array.to_list tyv))
               end)

method is_immediate n =
  is_immediate (Int32.of_int n)

method! is_simple_expr = function
  (* inlined floating-point ops are simple if their arguments are *)
  | Cop(Cextcall("sqrt", _, _, _), args) when vfp3 ->
      List.for_all self#is_simple_expr args
  | e -> super#is_simple_expr e

method select_addressing = function
    Cop(Cadda, [arg; Cconst_int n]) when is_offset n ->
      (Iindexed n, arg)
  | Cop(Cadda, [arg1; Cop(Caddi, [arg2; Cconst_int n])]) when is_offset n ->
      (Iindexed n, Cop(Cadda, [arg1; arg2]))
  | arg ->
      (Iindexed 0, arg)

method select_shift_arith op shiftop shiftrevop args =
  match args with
    [arg1; Cop(Clsl, [arg2; Cconst_int n])]
    when n > 0 && n < 32 && not(is_intconst arg2) ->
      (Ispecific(Ishiftarith(shiftop, n)), [arg1; arg2])
  | [arg1; Cop(Casr, [arg2; Cconst_int n])]
    when n > 0 && n < 32 && not(is_intconst arg2) ->
      (Ispecific(Ishiftarith(shiftop, -n)), [arg1; arg2])
  | [Cop(Clsl, [arg1; Cconst_int n]); arg2]
    when n > 0 && n < 32 && not(is_intconst arg1) ->
      (Ispecific(Ishiftarith(shiftrevop, n)), [arg2; arg1])
  | [Cop(Casr, [arg1; Cconst_int n]); arg2]
    when n > 0 && n < 32 && not(is_intconst arg1) ->
      (Ispecific(Ishiftarith(shiftrevop, -n)), [arg2; arg1])
  | args ->
      begin match super#select_operation op args with
      (* Recognize multiply-accumulate *)
        (Iintop Iadd, [Cop(Cmuli, args); arg3])
      | (Iintop Iadd, [arg3; Cop(Cmuli, args)]) as op_args ->
          begin match self#select_operation Cmuli args with
            (Iintop Imul, [arg1; arg2]) ->
              (Ispecific Imla, [arg1; arg2; arg3])
          | _ -> op_args
          end
      (* Recognize multiply-subtract *)
      | (Iintop Isub, [arg3; Cop(Cmuli, args)]) as op_args when armv > 6 ->
          begin match self#select_operation Cmuli args with
            (Iintop Imul, [arg1; arg2]) ->
              (Ispecific Imls, [arg1; arg2; arg3])
          | _ -> op_args
          end
      | op_args -> op_args
      end

method! select_operation op args =
  match (op, args) with
  (* Recognize special shift arithmetic *)
    ((Cadda | Caddi), [arg; Cconst_int n])
    when n < 0 && self#is_immediate (-n) ->
      (Iintop_imm(Isub, -n), [arg])
  | ((Cadda | Caddi as op), args) ->
      self#select_shift_arith op Ishiftadd Ishiftadd args
  | ((Csuba | Csubi), [arg; Cconst_int n])
    when n < 0 && self#is_immediate (-n) ->
      (Iintop_imm(Iadd, -n), [arg])
  | ((Csuba | Csubi), [Cconst_int n; arg])
    when self#is_immediate n ->
      (Ispecific(Irevsubimm n), [arg])
  | ((Csuba | Csubi as op), args) ->
      self#select_shift_arith op Ishiftsub Ishiftsubrev args
  | (Ccheckbound _, [Cop(Clsr, [arg1; Cconst_int n]); arg2])
    when n > 0 && n < 32 && not(is_intconst arg2) ->
      (Ispecific(Ishiftcheckbound n), [arg1; arg2])
  (* ARM does not support immediate operands for multiplication *)
  | (Cmuli, args) ->
      (Iintop Imul, args)
  (* Turn integer division/modulus into runtime ABI calls *)
  | (Cdivi, [arg; Cconst_int n])
    when n = 1 lsl Misc.log2 n ->
      (Iintop_imm(Idiv, n), [arg])
  | (Cdivi, args) ->
      (Iextcall("__aeabi_idiv", false), args)
  | (Cmodi, [arg; Cconst_int n])
    when n = 1 lsl Misc.log2 n ->
      (Iintop_imm(Imod, n), [arg])
  | (Cmodi, args) ->
      (* see below for fix up of return register *)
      (Iextcall("__aeabi_idivmod", false), args)
  (* Turn floating-point operations into runtime ABI calls for softfp *)
  | _ when not vfp3 ->
      self#select_operation_softfp op args
  (* Select operations for VFPv3 *)
  | _ ->
      self#select_operation_vfp3 op args

method private select_operation_softfp op args =
  match (op, args) with
  (* Turn floating-point operations into runtime ABI calls *)
  | (Caddf, args) -> (Iextcall("__aeabi_dadd", false), args)
  | (Csubf, args) -> (Iextcall("__aeabi_dsub", false), args)
  | (Cmulf, args) -> (Iextcall("__aeabi_dmul", false), args)
  | (Cdivf, args) -> (Iextcall("__aeabi_ddiv", false), args)
  | (Cfloatofint, args) -> (Iextcall("__aeabi_i2d", false), args)
  | (Cintoffloat, args) -> (Iextcall("__aeabi_d2iz", false), args)
  | (Ccmpf comp, args) ->
      let func = (match comp with
                    Cne    (* there's no __aeabi_dcmpne *)
                  | Ceq -> "__aeabi_dcmpeq"
                  | Clt -> "__aeabi_dcmplt"
                  | Cle -> "__aeabi_dcmple"
                  | Cgt -> "__aeabi_dcmpgt"
                  | Cge -> "__aeabi_dcmpge") in
      let comp = (match comp with
                    Cne -> Ceq (* eq 0 => false *)
                  | _   -> Cne (* ne 0 => true *)) in
      (Iintop_imm(Icomp(Iunsigned comp), 0),
       [Cop(Cextcall(func, typ_int, false, Debuginfo.none), args)])
  (* Add coercions around loads and stores of 32-bit floats *)
  | (Cload Single, args) ->
      (Iextcall("__aeabi_f2d", false), [Cop(Cload Word, args)])
  | (Cstore Single, [arg1; arg2]) ->
      let arg2' =
        Cop(Cextcall("__aeabi_d2f", typ_int, false, Debuginfo.none),
            [arg2]) in
      self#select_operation (Cstore Word) [arg1; arg2']
  (* Other operations are regular *)
  | (op, args) -> super#select_operation op args

method private select_operation_vfp3 op args =
  match (op, args) with
  (* Recognize floating-point negate-multiply *)
    (Cnegf, [Cop(Cmulf, args)]) ->
      (Ispecific Inmulf, args)
  (* Recognize floating-point multiply-accumulate *)
  | (Caddf, [arg; Cop(Cmulf, args)])
  | (Caddf, [Cop(Cmulf, args); arg]) ->
      (Ispecific Imacf, arg :: args)
  (* Recognize negate-multiply-subtract *)
  | (Csubf, [Cop(Cnegf, [arg]); Cop(Cmulf, args)])
  | (Csubf, [Cop(Cnegf, [Cop(Cmulf, args)]); arg]) ->
      (Ispecific Inmscf, arg :: args)
  (* Recognize floating-point negate-multiply-accumulate *)
  | (Csubf, [arg; Cop(Cmulf, args)]) ->
      (Ispecific Inmacf, arg :: args)
  (* Recognize multiply-subtract *)
  | (Csubf, [Cop(Cmulf, args); arg]) ->
      (Ispecific Imscf, arg :: args)
  (* Recognize floating-point square root *)
  | (Cextcall("sqrt", _, false, _), args) ->
      (Ispecific Isqrtf, args)
  (* Other operations are regular *)
  | (op, args) -> super#select_operation op args

method! select_condition = function
  (* Turn floating-point comparisons into runtime ABI calls *)
    Cop(Ccmpf _ as op, args) when not vfp3 ->
      begin match self#select_operation_softfp op args with
        (Iintop_imm(Icomp(Iunsigned Ceq), 0), [arg]) -> (Ifalsetest, arg)
      | (Iintop_imm(Icomp(Iunsigned Cne), 0), [arg]) -> (Itruetest, arg)
      | _ -> assert false
      end
  | expr ->
      super#select_condition expr

(* Deal with some register constraints *)

method! insert_op_debug op dbg rs rd =
  try
    let (rsrc, rdst) = pseudoregs_for_operation op rs rd in
    self#insert_moves rs rsrc;
    self#insert_debug (Iop op) dbg rsrc rdst;
    self#insert_moves rdst rd;
    rd
  with Use_default ->
    super#insert_op_debug op dbg rs rd

method! insert_op op rs rd =
  self#insert_op_debug op Debuginfo.none rs rd

method! insert_debug desc dbg rs rd =
  begin match desc with
  (* We use __aeabi_idivmod for Cmodi only, and hence we care only
     for the remainder in r1, so fix up the destination register. *)
    Iop(Iextcall("__aeabi_idivmod", false)) ->
      rd.(0) <- phys_reg 1
  | _ -> ()
  end;
  super#insert_debug desc dbg rs rd

end

let fundecl f = (new selector)#emit_fundecl f
