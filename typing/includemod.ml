(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* $Id$ *)

(* Inclusion checks for the module language *)

open Misc
open Path
open Types
open Typedtree

type symptom =
    Missing_field of Ident.t
  | Value_descriptions of Ident.t * value_description * value_description
  | Type_declarations of Ident.t * type_declaration
        * type_declaration * Includecore.type_mismatch list
  | Exception_declarations of
      Ident.t * exception_declaration * exception_declaration
  | Module_types of module_type * module_type
  | Modtype_infos of Ident.t * modtype_declaration * modtype_declaration
  | Modtype_permutation
  | Interface_mismatch of string * string
  | Class_type_declarations of
      Ident.t * cltype_declaration * cltype_declaration *
      Ctype.class_match_failure list
  | Class_declarations of
      Ident.t * class_declaration * class_declaration *
      Ctype.class_match_failure list
  | Unbound_modtype_path of Path.t

type pos =
    Module of Ident.t | Modtype of Ident.t | Arg of Ident.t | Body of Ident.t
type error = pos list * symptom

exception Error of error list

(* All functions "blah env x1 x2" check that x1 is included in x2,
   i.e. that x1 is the type of an implementation that fulfills the
   specification x2. If not, Error is raised with a backtrace of the error. *)

(* Inclusion between value descriptions *)

let value_descriptions env cxt subst id vd1 vd2 =
  Env.mark_value_used (Ident.name id) vd1;
  let vd2 = Subst.value_description subst vd2 in
  try
    Includecore.value_descriptions env vd1 vd2
  with Includecore.Dont_match ->
    raise(Error[cxt, Value_descriptions(id, vd1, vd2)])

(* Inclusion between type declarations *)

let type_declarations env cxt subst id decl1 decl2 =
  Env.mark_type_used (Ident.name id) decl1;
  let decl2 = Subst.type_declaration subst decl2 in
  let err = Includecore.type_declarations env (Ident.name id) decl1 id decl2 in
  if err <> [] then raise(Error[cxt, Type_declarations(id, decl1, decl2, err)])

(* Inclusion between exception declarations *)

let exception_declarations env cxt subst id decl1 decl2 =
  Env.mark_exception_used `Positive decl1 (Ident.name id);
  let decl2 = Subst.exception_declaration subst decl2 in
  if Includecore.exception_declarations env decl1 decl2
  then ()
  else raise(Error[cxt, Exception_declarations(id, decl1, decl2)])

(* Inclusion between class declarations *)

let class_type_declarations env cxt subst id decl1 decl2 =
  let decl2 = Subst.cltype_declaration subst decl2 in
  match Includeclass.class_type_declarations env decl1 decl2 with
    []     -> ()
  | reason ->
      raise(Error[cxt, Class_type_declarations(id, decl1, decl2, reason)])

let class_declarations env cxt subst id decl1 decl2 =
  let decl2 = Subst.class_declaration subst decl2 in
  match Includeclass.class_declarations env decl1 decl2 with
    []     -> ()
  | reason -> raise(Error[cxt, Class_declarations(id, decl1, decl2, reason)])

(* Expand a module type identifier when possible *)

exception Dont_match

let expand_module_path env cxt path =
  try
    Env.find_modtype_expansion path env
  with Not_found ->
    raise(Error[cxt, Unbound_modtype_path path])

(* Extract name, kind and ident from a signature item *)

type field_desc =
    Field_value of string
  | Field_type of string
  | Field_exception of string
  | Field_module of string
  | Field_modtype of string
  | Field_class of string
  | Field_classtype of string

let item_ident_name = function
    Tsig_value(id, _) -> (id, Field_value(Ident.name id))
  | Tsig_type(id, _, _) -> (id, Field_type(Ident.name id))
  | Tsig_exception(id, _) -> (id, Field_exception(Ident.name id))
  | Tsig_module(id, _, _) -> (id, Field_module(Ident.name id))
  | Tsig_modtype(id, _) -> (id, Field_modtype(Ident.name id))
  | Tsig_class(id, _, _) -> (id, Field_class(Ident.name id))
  | Tsig_cltype(id, _, _) -> (id, Field_classtype(Ident.name id))

(* Simplify a structure coercion *)

let simplify_structure_coercion cc =
  let rec is_identity_coercion pos = function
  | [] ->
      true
  | (n, c) :: rem ->
      n = pos && c = Tcoerce_none && is_identity_coercion (pos + 1) rem in
  if is_identity_coercion 0 cc
  then Tcoerce_none
  else Tcoerce_structure cc

(* Inclusion between module types.
   Return the restriction that transforms a value of the smaller type
   into a value of the bigger type. *)

let rec modtypes env cxt subst mty1 mty2 =
  try
    try_modtypes env cxt subst mty1 mty2
  with
    Dont_match ->
      raise(Error[cxt, Module_types(mty1, Subst.modtype subst mty2)])
  | Error reasons ->
      raise(Error((cxt, Module_types(mty1, Subst.modtype subst mty2))
                  :: reasons))

and try_modtypes env cxt subst mty1 mty2 =
  match (mty1, mty2) with
    (_, Tmty_ident p2) ->
      try_modtypes2 env cxt mty1 (Subst.modtype subst mty2)
  | (Tmty_ident p1, _) ->
      try_modtypes env cxt subst (expand_module_path env cxt p1) mty2
  | (Tmty_signature sig1, Tmty_signature sig2) ->
      signatures env cxt subst sig1 sig2
  | (Tmty_functor(param1, arg1, res1), Tmty_functor(param2, arg2, res2)) ->
      let arg2' = Subst.modtype subst arg2 in
      let cc_arg = modtypes env (Arg param1::cxt) Subst.identity arg2' arg1 in
      let cc_res =
        modtypes (Env.add_module param1 arg2' env) (Body param1::cxt)
          (Subst.add_module param2 (Pident param1) subst) res1 res2 in
      begin match (cc_arg, cc_res) with
          (Tcoerce_none, Tcoerce_none) -> Tcoerce_none
        | _ -> Tcoerce_functor(cc_arg, cc_res)
      end
  | (_, _) ->
      raise Dont_match

and try_modtypes2 env cxt mty1 mty2 =
  (* mty2 is an identifier *)
  match (mty1, mty2) with
    (Tmty_ident p1, Tmty_ident p2) when Path.same p1 p2 ->
      Tcoerce_none
  | (_, Tmty_ident p2) ->
      try_modtypes env cxt Subst.identity mty1 (expand_module_path env cxt p2)
  | (_, _) ->
      assert false

(* Inclusion between signatures *)

and signatures env cxt subst sig1 sig2 =
  (* Environment used to check inclusion of components *)
  let new_env =
    Env.add_signature sig1 (Env.in_signature env) in
  (* Build a table of the components of sig1, along with their positions.
     The table is indexed by kind and name of component *)
  let rec build_component_table pos tbl = function
      [] -> tbl
    | item :: rem ->
        let (id, name) = item_ident_name item in
        let nextpos =
          match item with
            Tsig_value(_,{val_kind = Val_prim _})
          | Tsig_type(_,_,_)
          | Tsig_modtype(_,_)
          | Tsig_cltype(_,_,_) -> pos
          | Tsig_value(_,_)
          | Tsig_exception(_,_)
          | Tsig_module(_,_,_)
          | Tsig_class(_, _,_) -> pos+1 in
        build_component_table nextpos
                              (Tbl.add name (id, item, pos) tbl) rem in
  let comps1 =
    build_component_table 0 Tbl.empty sig1 in
  (* Pair each component of sig2 with a component of sig1,
     identifying the names along the way.
     Return a coercion list indicating, for all run-time components
     of sig2, the position of the matching run-time components of sig1
     and the coercion to be applied to it. *)
  let rec pair_components subst paired unpaired = function
      [] ->
        begin match unpaired with
            [] -> signature_components new_env cxt subst (List.rev paired)
          | _  -> raise(Error unpaired)
        end
    | item2 :: rem ->
        let (id2, name2) = item_ident_name item2 in
        let name2, report =
          match item2, name2 with
            Tsig_type (_, {type_manifest=None}, _), Field_type s
            when let l = String.length s in
            l >= 4 && String.sub s (l-4) 4 = "#row" ->
              (* Do not report in case of failure,
                 as the main type will generate an error *)
              Field_type (String.sub s 0 (String.length s - 4)), false
          | _ -> name2, true
        in
        begin try
          let (id1, item1, pos1) = Tbl.find name2 comps1 in
          let new_subst =
            match item2 with
              Tsig_type _ ->
                Subst.add_type id2 (Pident id1) subst
            | Tsig_module _ ->
                Subst.add_module id2 (Pident id1) subst
            | Tsig_modtype _ ->
                Subst.add_modtype id2 (Tmty_ident (Pident id1)) subst
            | Tsig_value _ | Tsig_exception _ | Tsig_class _ | Tsig_cltype _ ->
                subst
          in
          pair_components new_subst
            ((item1, item2, pos1) :: paired) unpaired rem
        with Not_found ->
          let unpaired =
            if report then (cxt, Missing_field id2) :: unpaired else unpaired in
          pair_components subst paired unpaired rem
        end in
  (* Do the pairing and checking, and return the final coercion *)
  simplify_structure_coercion (pair_components subst [] [] sig2)

(* Inclusion between signature components *)

and signature_components env cxt subst = function
    [] -> []
  | (Tsig_value(id1, valdecl1), Tsig_value(id2, valdecl2), pos) :: rem ->
      let cc = value_descriptions env cxt subst id1 valdecl1 valdecl2 in
      begin match valdecl2.val_kind with
        Val_prim p -> signature_components env cxt subst rem
      | _ -> (pos, cc) :: signature_components env cxt subst rem
      end
  | (Tsig_type(id1, tydecl1, _), Tsig_type(id2, tydecl2, _), pos) :: rem ->
      type_declarations env cxt subst id1 tydecl1 tydecl2;
      signature_components env cxt subst rem
  | (Tsig_exception(id1, excdecl1), Tsig_exception(id2, excdecl2), pos)
    :: rem ->
      exception_declarations env cxt subst id1 excdecl1 excdecl2;
      (pos, Tcoerce_none) :: signature_components env cxt subst rem
  | (Tsig_module(id1, mty1, _), Tsig_module(id2, mty2, _), pos) :: rem ->
      let cc =
        modtypes env (Module id1::cxt) subst
          (Mtype.strengthen env mty1 (Pident id1)) mty2 in
      (pos, cc) :: signature_components env cxt subst rem
  | (Tsig_modtype(id1, info1), Tsig_modtype(id2, info2), pos) :: rem ->
      modtype_infos env cxt subst id1 info1 info2;
      signature_components env cxt subst rem
  | (Tsig_class(id1, decl1, _), Tsig_class(id2, decl2, _), pos) :: rem ->
      class_declarations env cxt subst id1 decl1 decl2;
      (pos, Tcoerce_none) :: signature_components env cxt subst rem
  | (Tsig_cltype(id1, info1, _), Tsig_cltype(id2, info2, _), pos) :: rem ->
      class_type_declarations env cxt subst id1 info1 info2;
      signature_components env cxt subst rem
  | _ ->
      assert false

(* Inclusion between module type specifications *)

and modtype_infos env cxt subst id info1 info2 =
  let info2 = Subst.modtype_declaration subst info2 in
  let cxt' = Modtype id :: cxt in
  try
    match (info1, info2) with
      (Tmodtype_abstract, Tmodtype_abstract) -> ()
    | (Tmodtype_manifest mty1, Tmodtype_abstract) -> ()
    | (Tmodtype_manifest mty1, Tmodtype_manifest mty2) ->
        check_modtype_equiv env cxt' mty1 mty2
    | (Tmodtype_abstract, Tmodtype_manifest mty2) ->
        check_modtype_equiv env cxt' (Tmty_ident(Pident id)) mty2
  with Error reasons ->
    raise(Error((cxt, Modtype_infos(id, info1, info2)) :: reasons))

and check_modtype_equiv env cxt mty1 mty2 =
  match
    (modtypes env cxt Subst.identity mty1 mty2,
     modtypes env cxt Subst.identity mty2 mty1)
  with
    (Tcoerce_none, Tcoerce_none) -> ()
  | (_, _) -> raise(Error [cxt, Modtype_permutation])

(* Simplified inclusion check between module types (for Env) *)

let check_modtype_inclusion env mty1 path1 mty2 =
  try
    ignore(modtypes env [] Subst.identity
                    (Mtype.strengthen env mty1 path1) mty2)
  with Error reasons ->
    raise Not_found

let _ = Env.check_modtype_inclusion := check_modtype_inclusion

(* Check that an implementation of a compilation unit meets its
   interface. *)

let compunit impl_name impl_sig intf_name intf_sig =
  try
    signatures Env.initial [] Subst.identity impl_sig intf_sig
  with Error reasons ->
    raise(Error(([], Interface_mismatch(impl_name, intf_name)) :: reasons))

(* Hide the context and substitution parameters to the outside world *)

let modtypes env mty1 mty2 = modtypes env [] Subst.identity mty1 mty2
let signatures env sig1 sig2 = signatures env [] Subst.identity sig1 sig2
let type_declarations env id decl1 decl2 =
  type_declarations env [] Subst.identity id decl1 decl2

(* Error report *)

open Format
open Printtyp

let show_loc msg ppf loc =
  let pos = loc.Location.loc_start in
  if List.mem pos.Lexing.pos_fname [""; "_none_"; "//toplevel//"] then ()
  else fprintf ppf "@\n@[<2>%a:@ %s@]" Location.print_loc loc msg

let show_locs ppf (loc1, loc2) =
  show_loc "Expected declaration" ppf loc2;
  show_loc "Actual declaration" ppf loc1

let include_err ppf = function
  | Missing_field id ->
      fprintf ppf "The field `%a' is required but not provided" ident id
  | Value_descriptions(id, d1, d2) ->
      fprintf ppf
        "@[<hv 2>Values do not match:@ %a@;<1 -2>is not included in@ %a@]"
        (value_description id) d1 (value_description id) d2;
      show_locs ppf (d1.val_loc, d2.val_loc);
  | Type_declarations(id, d1, d2, errs) ->
      fprintf ppf "@[<v>@[<hv>%s:@;<1 2>%a@ %s@;<1 2>%a@]%a%a@]"
        "Type declarations do not match"
        (type_declaration id) d1
        "is not included in"
        (type_declaration id) d2
        show_locs (d1.type_loc, d2.type_loc)
        (Includecore.report_type_mismatch
           "the first" "the second" "declaration") errs
  | Exception_declarations(id, d1, d2) ->
      fprintf ppf
       "@[<hv 2>Exception declarations do not match:@ \
        %a@;<1 -2>is not included in@ %a@]"
        (exception_declaration id) d1
        (exception_declaration id) d2;
      show_locs ppf (d1.exn_loc, d2.exn_loc)
  | Module_types(mty1, mty2)->
      fprintf ppf
       "@[<hv 2>Modules do not match:@ \
        %a@;<1 -2>is not included in@ %a@]"
      modtype mty1
      modtype mty2
  | Modtype_infos(id, d1, d2) ->
      fprintf ppf
       "@[<hv 2>Module type declarations do not match:@ \
        %a@;<1 -2>does not match@ %a@]"
      (modtype_declaration id) d1
      (modtype_declaration id) d2
  | Modtype_permutation ->
      fprintf ppf "Illegal permutation of structure fields"
  | Interface_mismatch(impl_name, intf_name) ->
      fprintf ppf "@[The implementation %s@ does not match the interface %s:"
       impl_name intf_name
  | Class_type_declarations(id, d1, d2, reason) ->
      fprintf ppf
       "@[<hv 2>Class type declarations do not match:@ \
        %a@;<1 -2>does not match@ %a@]@ %a"
      (Printtyp.cltype_declaration id) d1
      (Printtyp.cltype_declaration id) d2
      Includeclass.report_error reason
  | Class_declarations(id, d1, d2, reason) ->
      fprintf ppf
       "@[<hv 2>Class declarations do not match:@ \
        %a@;<1 -2>does not match@ %a@]@ %a"
      (Printtyp.class_declaration id) d1
      (Printtyp.class_declaration id) d2
      Includeclass.report_error reason
  | Unbound_modtype_path path ->
      fprintf ppf "Unbound module type %a" Printtyp.path path

let rec context ppf = function
    Module id :: rem ->
      fprintf ppf "@[<2>module %a%a@]" ident id args rem
  | Modtype id :: rem ->
      fprintf ppf "@[<2>module type %a =@ %a@]" ident id context_mty rem
  | Body x :: rem ->
      fprintf ppf "functor (%a) ->@ %a" ident x context_mty rem
  | Arg x :: rem ->
      fprintf ppf "functor (%a : %a) -> ..." ident x context_mty rem
  | [] ->
      fprintf ppf "<here>"
and context_mty ppf = function
    (Module _ | Modtype _) :: _ as rem ->
      fprintf ppf "@[<2>sig@ %a@;<1 -2>end@]" context rem
  | cxt -> context ppf cxt
and args ppf = function
    Body x :: rem ->
      fprintf ppf "(%a)%a" ident x args rem
  | Arg x :: rem ->
      fprintf ppf "(%a :@ %a) : ..." ident x context_mty rem
  | cxt ->
      fprintf ppf " :@ %a" context_mty cxt

let path_of_context = function
    Module id :: rem ->
      let rec subm path = function
          [] -> path
        | Module id :: rem -> subm (Pdot (path, Ident.name id, -1)) rem
        | _ -> assert false
      in subm (Pident id) rem
  | _ -> assert false

let context ppf cxt =
  if cxt = [] then () else
  if List.for_all (function Module _ -> true | _ -> false) cxt then
    fprintf ppf "In module %a:@ " path (path_of_context cxt)
  else
    fprintf ppf "@[<hv 2>At position@ %a@]@ " context cxt

let include_err ppf (cxt, err) =
  fprintf ppf "@[<v>%a%a@]" context (List.rev cxt) include_err err

let buffer = ref ""
let is_big obj =
  let size = !Clflags.error_size in
  size > 0 &&
  begin
    if String.length !buffer < size then buffer := String.create size;
    try ignore (Marshal.to_buffer !buffer 0 size obj []); false
    with _ -> true
  end

let report_error ppf errs =
  if errs = [] then () else
  let (errs , err) = split_last errs in
  let pe = ref true in
  let include_err' ppf err =
    if not (is_big err) then fprintf ppf "%a@ " include_err err
    else if !pe then (fprintf ppf "...@ "; pe := false)
  in
  let print_errs ppf = List.iter (include_err' ppf) in
  fprintf ppf "@[<v>%a%a@]" print_errs errs include_err err
