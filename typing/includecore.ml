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

(* Inclusion checks for the core language *)

open Misc
open Asttypes
open Path
open Types
open Typedtree

(* Inclusion between value descriptions *)

exception Dont_match

let value_descriptions env vd1 vd2 =
  if Ctype.moregeneral env true vd1.val_type vd2.val_type then begin
    match (vd1.val_kind, vd2.val_kind) with
        (Val_prim p1, Val_prim p2) ->
          if p1 = p2 then Tcoerce_none else raise Dont_match
      | (Val_prim p, _) -> Tcoerce_primitive p
      | (_, Val_prim p) -> raise Dont_match
      | (_, _) -> Tcoerce_none
  end else
    raise Dont_match

(* Inclusion between "private" annotations *)

let private_flags decl1 decl2 =
  match decl1.type_private, decl2.type_private with
  | Private, Public ->
      decl2.type_kind = Type_abstract &&
      (decl2.type_manifest = None || decl1.type_kind <> Type_abstract)
  | _, _ -> true

(* Inclusion between manifest types (particularly for private row types) *)

let is_absrow env ty =
  match ty.desc with
    Tconstr(Pident id, _, _) ->
      begin match Ctype.expand_head env ty with
        {desc=Tobject _|Tvariant _} -> true
      | _ -> false
      end
  | _ -> false

let type_manifest env ty1 params1 ty2 params2 priv2 =
  let ty1' = Ctype.expand_head env ty1 and ty2' = Ctype.expand_head env ty2 in
  match ty1'.desc, ty2'.desc with
    Tvariant row1, Tvariant row2 when is_absrow env (Btype.row_more row2) ->
      let row1 = Btype.row_repr row1 and row2 = Btype.row_repr row2 in
      Ctype.equal env true (ty1::params1) (row2.row_more::params2) &&
      begin match row1.row_more with
        {desc=Tvar _|Tconstr _|Tnil} -> true
      | _ -> false
      end &&
      let r1, r2, pairs =
        Ctype.merge_row_fields row1.row_fields row2.row_fields in
      (not row2.row_closed ||
       row1.row_closed && Ctype.filter_row_fields false r1 = []) &&
      List.for_all
        (fun (_,f) -> match Btype.row_field_repr f with
          Rabsent | Reither _ -> true | Rpresent _ -> false)
        r2 &&
      let to_equal = ref (List.combine params1 params2) in
      List.for_all
        (fun (_, f1, f2) ->
          match Btype.row_field_repr f1, Btype.row_field_repr f2 with
            Rpresent(Some t1),
            (Rpresent(Some t2) | Reither(false, [t2], _, _)) ->
              to_equal := (t1,t2) :: !to_equal; true
          | Rpresent None, (Rpresent None | Reither(true, [], _, _)) -> true
          | Reither(c1,tl1,_,_), Reither(c2,tl2,_,_)
            when List.length tl1 = List.length tl2 && c1 = c2 ->
              to_equal := List.combine tl1 tl2 @ !to_equal; true
          | Rabsent, (Reither _ | Rabsent) -> true
          | _ -> false)
        pairs &&
      let tl1, tl2 = List.split !to_equal in
      Ctype.equal env true tl1 tl2
  | Tobject (fi1, _), Tobject (fi2, _)
    when is_absrow env (snd(Ctype.flatten_fields fi2)) ->
      let (fields2,rest2) = Ctype.flatten_fields fi2 in
      Ctype.equal env true (ty1::params1) (rest2::params2) &&
      let (fields1,rest1) = Ctype.flatten_fields fi1 in
      (match rest1 with {desc=Tnil|Tvar _|Tconstr _} -> true | _ -> false) &&
      let pairs, miss1, miss2 = Ctype.associate_fields fields1 fields2 in
      miss2 = [] &&
      let tl1, tl2 =
        List.split (List.map (fun (_,_,t1,_,t2) -> t1, t2) pairs) in
      Ctype.equal env true (params1 @ tl1) (params2 @ tl2)
  | _ ->
      let rec check_super ty1 =
        Ctype.equal env true (ty1 :: params1) (ty2 :: params2) ||
        priv2 = Private &&
        try check_super
              (Ctype.try_expand_once_opt env (Ctype.expand_head env ty1))
        with Ctype.Cannot_expand -> false
      in check_super ty1

(* Inclusion between type declarations *)

type type_mismatch =
    Arity
  | Privacy
  | Kind
  | Constraint
  | Manifest
  | Variance
  | Field_type of Ident.t
  | Field_mutable of Ident.t
  | Field_arity of Ident.t
  | Field_names of int * Ident.t * Ident.t
  | Field_missing of bool * Ident.t
  | Record_representation of bool

let nth n =
  if n = 1 then "first" else
  if n = 2 then "2nd" else
  if n = 3 then "3rd" else
  string_of_int n ^ "th"

let report_type_mismatch0 first second decl ppf err =
  let pr fmt = Format.fprintf ppf fmt in
  match err with
    Arity -> pr "They have different arities"
  | Privacy -> pr "A private type would be revealed"
  | Kind -> pr "Their kinds differ"
  | Constraint -> pr "Their constraints differ"
  | Manifest -> ()
  | Variance -> pr "Their variances do not agree"
  | Field_type s ->
      pr "The types for field %s are not equal" (Ident.name s)
  | Field_mutable s ->
      pr "The mutability of field %s is different" (Ident.name s)
  | Field_arity s ->
      pr "The arities for field %s differ" (Ident.name s)
  | Field_names (n, name1, name2) ->
      pr "Their %s fields have different names, %s and %s"
        (nth n) (Ident.name name1) (Ident.name name2)
  | Field_missing (b, s) ->
      pr "The field %s is only present in %s %s"
        (Ident.name s) (if b then second else first) decl
  | Record_representation b ->
      pr "Their internal representations differ:@ %s %s %s"
        (if b then second else first) decl
        "uses unboxed float representation"

let report_type_mismatch first second decl ppf =
  List.iter
    (fun err ->
      if err = Manifest then () else
      Format.fprintf ppf "@ %a." (report_type_mismatch0 first second decl) err)

let rec compare_variants env decl1 decl2 n cstrs1 cstrs2 =
  match cstrs1, cstrs2 with
    [], []           -> []
  | [], (cstr2,_,_)::_ -> [Field_missing (true, cstr2)]
  | (cstr1,_,_)::_, [] -> [Field_missing (false, cstr1)]
  | (cstr1, arg1, ret1)::rem1, (cstr2, arg2,ret2)::rem2 ->
      if Ident.name cstr1 <> Ident.name cstr2 then
        [Field_names (n, cstr1, cstr2)]
      else if List.length arg1 <> List.length arg2 then
        [Field_arity cstr1]
      else match ret1, ret2 with
      | Some r1, Some r2 when not (Ctype.equal env true [r1] [r2]) ->
	  [Field_type cstr1]
      | Some _, None | None, Some _ ->
	  [Field_type cstr1]
      | _ ->
	  if Misc.for_all2
	      (fun ty1 ty2 ->
		Ctype.equal env true (ty1::decl1.type_params)
		  (ty2::decl2.type_params))
	      (arg1) (arg2)
	  then
	    compare_variants env decl1 decl2 (n+1) rem1 rem2
	  else [Field_type cstr1]


let rec compare_records env decl1 decl2 n labels1 labels2 =
  match labels1, labels2 with
    [], []           -> []
  | [], (lab2,_,_)::_ -> [Field_missing (true, lab2)]
  | (lab1,_,_)::_, [] -> [Field_missing (false, lab1)]
  | (lab1, mut1, arg1)::rem1, (lab2, mut2, arg2)::rem2 ->
      if Ident.name lab1 <> Ident.name lab2
      then [Field_names (n, lab1, lab2)]
      else if mut1 <> mut2 then [Field_mutable lab1] else
      if Ctype.equal env true (arg1::decl1.type_params)
                              (arg2::decl2.type_params)
      then compare_records env decl1 decl2 (n+1) rem1 rem2
      else [Field_type lab1]

let type_declarations ?(equality = false) env name decl1 id decl2 =
  if decl1.type_arity <> decl2.type_arity then [Arity] else
  if not (private_flags decl1 decl2) then [Privacy] else
  let err = match (decl1.type_kind, decl2.type_kind) with
      (_, Type_abstract) -> []
    | (Type_variant cstrs1, Type_variant cstrs2) ->
        let mark cstrs usage name decl =
          List.iter
            (fun (c, _, _) ->
              Env.mark_constructor_used usage name decl (Ident.name c))
            cstrs
        in
        let usage =
          if decl1.type_private = Private || decl2.type_private = Public
          then Env.Positive else Env.Privatize
        in
        mark cstrs1 usage name decl1;
        if equality then mark cstrs2 Env.Positive (Ident.name id) decl2;
        compare_variants env decl1 decl2 1 cstrs1 cstrs2
    | (Type_record(labels1,rep1), Type_record(labels2,rep2)) ->
        let err = compare_records env decl1 decl2 1 labels1 labels2 in
        if err <> [] || rep1 = rep2 then err else
        [Record_representation (rep2 = Record_float)]
    | (_, _) -> [Kind]
  in
  if err <> [] then err else
  let err = match (decl1.type_manifest, decl2.type_manifest) with
      (_, None) ->
        if Ctype.equal env true decl1.type_params decl2.type_params
        then [] else [Constraint]
    | (Some ty1, Some ty2) ->
        if type_manifest env ty1 decl1.type_params ty2 decl2.type_params
            decl2.type_private
        then [] else [Manifest]
    | (None, Some ty2) ->
        let ty1 =
          Btype.newgenty (Tconstr(Pident id, decl2.type_params, ref Mnil))
        in
        if Ctype.equal env true decl1.type_params decl2.type_params then
          if Ctype.equal env false [ty1] [ty2] then []
          else [Manifest]
        else [Constraint]
  in
  if err <> [] then err else
  if match decl2.type_kind with
  | Type_record (_,_) | Type_variant _ -> decl2.type_private = Private
  | Type_abstract ->
      match decl2.type_manifest with
      | None -> true
      | Some ty -> Btype.has_constr_row (Ctype.expand_head env ty)
  then
    if List.for_all2
        (fun (co1,cn1,ct1) (co2,cn2,ct2) -> (not co1 || co2)&&(not cn1 || cn2))
        decl1.type_variance decl2.type_variance
    then [] else [Variance]
  else []

(* Inclusion between exception declarations *)

let exception_declarations env ed1 ed2 =
  Misc.for_all2 (fun ty1 ty2 -> Ctype.equal env false [ty1] [ty2])
    ed1.exn_args ed2.exn_args

(* Inclusion between class types *)
let encode_val (mut, ty) rem =
  begin match mut with
    Asttypes.Mutable   -> Predef.type_unit
  | Asttypes.Immutable -> Btype.newgenvar ()
  end
  ::ty::rem

let meths meths1 meths2 =
  Meths.fold
    (fun nam t2 (ml1, ml2) ->
       (begin try
          Meths.find nam meths1 :: ml1
        with Not_found ->
          ml1
        end,
        t2 :: ml2))
    meths2 ([], [])

let vars vars1 vars2 =
  Vars.fold
    (fun lab v2 (vl1, vl2) ->
       (begin try
          encode_val (Vars.find lab vars1) vl1
        with Not_found ->
          vl1
        end,
        encode_val v2 vl2))
    vars2 ([], [])
