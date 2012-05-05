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

(* Typechecking for the core language *)

open Misc
open Asttypes
open Parsetree
open Types
open Typedtree
open Btype
open Ctype

type error =
    Polymorphic_label of Longident.t
  | Constructor_arity_mismatch of Longident.t * int * int
  | Label_mismatch of Longident.t * (type_expr * type_expr) list
  | Pattern_type_clash of (type_expr * type_expr) list
  | Multiply_bound_variable of string
  | Orpat_vars of Ident.t
  | Expr_type_clash of (type_expr * type_expr) list
  | Apply_non_function of type_expr
  | Apply_wrong_label of label * type_expr
  | Label_multiply_defined of Longident.t
  | Label_missing of string list
  | Label_not_mutable of Longident.t
  | Incomplete_format of string
  | Bad_conversion of string * int * char
  | Undefined_method of type_expr * string
  | Undefined_inherited_method of string
  | Virtual_class of Longident.t
  | Private_type of type_expr
  | Private_label of Longident.t * type_expr
  | Unbound_instance_variable of string
  | Instance_variable_not_mutable of bool * string
  | Not_subtype of (type_expr * type_expr) list * (type_expr * type_expr) list
  | Outside_class
  | Value_multiply_overridden of string
  | Coercion_failure of
      type_expr * type_expr * (type_expr * type_expr) list * bool
  | Too_many_arguments of bool * type_expr
  | Abstract_wrong_label of label * type_expr
  | Scoping_let_module of string * type_expr
  | Masked_instance_variable of Longident.t
  | Not_a_variant_type of Longident.t
  | Incoherent_label_order
  | Less_general of string * (type_expr * type_expr) list
  | Modules_not_allowed
  | Cannot_infer_signature
  | Not_a_packed_module of type_expr
  | Recursive_local_constraint of (type_expr * type_expr) list
  | Unexpected_existential

exception Error of Location.t * error

(* Forward declaration, to be filled in by Typemod.type_module *)

let type_module =
  ref ((fun env md -> assert false) :
       Env.t -> Parsetree.module_expr -> Typedtree.module_expr)

(* Forward declaration, to be filled in by Typemod.type_open *)

let type_open =
  ref (fun _ -> assert false)

(* Forward declaration, to be filled in by Typemod.type_package *)

let type_package =
  ref (fun _ -> assert false)

(* Forward declaration, to be filled in by Typeclass.class_structure *)
let type_object =
  ref (fun env s -> assert false :
       Env.t -> Location.t -> Parsetree.class_structure ->
         class_structure * class_signature * string list)

(*
  Saving and outputting type information.
  We keep these function names short, because they have to be
  called each time we create a record of type [Typedtree.expression]
  or [Typedtree.pattern] that will end up in the typed AST.
*)
let re node =
  Stypes.record (Stypes.Ti_expr node);
  node
;;
let rp node =
  Stypes.record (Stypes.Ti_pat node);
  node
;;

(* Upper approximation of free identifiers on the parse tree *)

let iter_expression f e =

  let rec expr e =
    f e;
    match e.pexp_desc with
    | Pexp_ident _
    | Pexp_assertfalse
    | Pexp_new _
    | Pexp_constant _ -> ()
    | Pexp_function (_, eo, pel) ->
        may expr eo; List.iter (fun (_, e) -> expr e) pel
    | Pexp_apply (e, lel) -> expr e; List.iter (fun (_, e) -> expr e) lel
    | Pexp_let (_, pel, e)
    | Pexp_match (e, pel)
    | Pexp_try (e, pel) -> expr e; List.iter (fun (_, e) -> expr e) pel
    | Pexp_array el
    | Pexp_tuple el -> List.iter expr el
    | Pexp_construct (_, eo, _)
    | Pexp_variant (_, eo) -> may expr eo
    | Pexp_record (iel, eo) ->
        may expr eo; List.iter (fun (_, e) -> expr e) iel
    | Pexp_open (_, e)
    | Pexp_newtype (_, e)
    | Pexp_poly (e, _)
    | Pexp_lazy e
    | Pexp_assert e
    | Pexp_setinstvar (_, e)
    | Pexp_send (e, _)
    | Pexp_constraint (e, _, _)
    | Pexp_field (e, _) -> expr e
    | Pexp_when (e1, e2)
    | Pexp_while (e1, e2)
    | Pexp_sequence (e1, e2)
    | Pexp_setfield (e1, _, e2) -> expr e1; expr e2
    | Pexp_ifthenelse (e1, e2, eo) -> expr e1; expr e2; may expr eo
    | Pexp_for (_, e1, e2, _, e3) -> expr e1; expr e2; expr e3
    | Pexp_override sel -> List.iter (fun (_, e) -> expr e) sel
    | Pexp_letmodule (_, me, e) -> expr e; module_expr me
    | Pexp_object (_, cs) -> List.iter class_field cs
    | Pexp_pack me -> module_expr me

  and module_expr me =
    match me.pmod_desc with
    | Pmod_ident _ -> ()
    | Pmod_structure str -> List.iter structure_item str
    | Pmod_constraint (me, _)
    | Pmod_functor (_, _, me) -> module_expr me
    | Pmod_apply (me1, me2) -> module_expr me1; module_expr me2
    | Pmod_unpack e -> expr e

  and structure_item str =
    match str.pstr_desc with
    | Pstr_eval e -> expr e
    | Pstr_value (_, pel) -> List.iter (fun (_, e) -> expr e) pel
    | Pstr_primitive _
    | Pstr_type _
    | Pstr_exception _
    | Pstr_modtype _
    | Pstr_open _
    | Pstr_class_type _
    | Pstr_exn_rebind _ -> ()
    | Pstr_include me
    | Pstr_module (_, me) -> module_expr me
    | Pstr_recmodule l -> List.iter (fun (_, _, me) -> module_expr me) l
    | Pstr_class cdl -> List.iter (fun c -> class_expr c.pci_expr) cdl

  and class_expr ce =
    match ce.pcl_desc with
    | Pcl_constr _ -> ()
    | Pcl_structure (_, cfl) -> List.iter class_field cfl
    | Pcl_fun (_, eo, _,  ce) -> may expr eo; class_expr ce
    | Pcl_apply (ce, lel) ->
        class_expr ce; List.iter (fun (_, e) -> expr e) lel
    | Pcl_let (_, pel, ce) ->
        List.iter (fun (_, e) -> expr e) pel; class_expr ce
    | Pcl_constraint (ce, _) -> class_expr ce

  and class_field = function
    | Pcf_inher (_, ce, _) -> class_expr ce
    | Pcf_valvirt _ | Pcf_virt _ | Pcf_cstr _ -> ()
    | Pcf_val (_,_,_, e, _) | Pcf_meth (_,_,_, e, _) -> expr e
    | Pcf_init e -> expr e

  in
  expr e


let all_idents el =
  let idents = Hashtbl.create 8 in
  let f = function
    | {pexp_desc=Pexp_ident (Longident.Lident id); _} ->
        Hashtbl.replace idents id ()
    | _ -> ()
  in
  List.iter (iter_expression f) el;
  Hashtbl.fold (fun x () rest -> x :: rest) idents []


(* Typing of constants *)

let type_constant = function
    Const_int _ -> instance_def Predef.type_int
  | Const_char _ -> instance_def Predef.type_char
  | Const_string _ -> instance_def Predef.type_string
  | Const_float _ -> instance_def Predef.type_float
  | Const_int32 _ -> instance_def Predef.type_int32
  | Const_int64 _ -> instance_def Predef.type_int64
  | Const_nativeint _ -> instance_def Predef.type_nativeint

(* Specific version of type_option, using newty rather than newgenty *)

let type_option ty =
  newty (Tconstr(Predef.path_option,[ty], ref Mnil))

let option_none ty loc =
  let cnone = Env.lookup_constructor (Longident.Lident "None") Env.initial in
  { exp_desc = Texp_construct(cnone, []);
    exp_type = ty; exp_loc = loc; exp_env = Env.initial }

let option_some texp =
  let csome = Env.lookup_constructor (Longident.Lident "Some") Env.initial in
  { exp_desc = Texp_construct(csome, [texp]); exp_loc = texp.exp_loc;
    exp_type = type_option texp.exp_type; exp_env = texp.exp_env }

let extract_option_type env ty =
  match expand_head env ty with {desc = Tconstr(path, [ty], _)}
    when Path.same path Predef.path_option -> ty
  | _ -> assert false

let rec extract_label_names sexp env ty =
  let ty = expand_head env ty in
  match ty.desc with
  | Tconstr (path, _, _) ->
      let td = Env.find_type path env in
      begin match td.type_kind with
      | Type_record (fields, _) ->
          List.map (fun (name, _, _) -> name) fields
      | Type_abstract when td.type_manifest <> None ->
          extract_label_names sexp env (expand_head env ty)
      | _ -> assert false
      end
  | _ ->
      assert false

(* Typing of patterns *)

(* unification inside type_pat*)
let unify_pat_types loc env ty ty' =
  try
    unify env ty ty'
  with
    Unify trace ->
      raise(Error(loc, Pattern_type_clash(trace)))
  | Tags(l1,l2) ->
      raise(Typetexp.Error(loc, Typetexp.Variant_tags (l1, l2)))

(* unification inside type_exp and type_expect *)
let unify_exp_types loc env ty expected_ty =
  (* Format.eprintf "@[%a@ %a@]@." Printtyp.raw_type_expr exp.exp_type
    Printtyp.raw_type_expr expected_ty; *)
  try
    unify env ty expected_ty
  with
    Unify trace ->
      raise(Error(loc, Expr_type_clash(trace)))
  | Tags(l1,l2) ->
      raise(Typetexp.Error(loc, Typetexp.Variant_tags (l1, l2)))

(* level at which to create the local type declarations *)
let newtype_level = ref None
let get_newtype_level () =
  match !newtype_level with
    Some y -> y
  | None -> assert false

let unify_pat_types_gadt loc env ty ty' =
  let newtype_level =
    match !newtype_level with
    | None -> assert false
    | Some x -> x
  in
  try
    unify_gadt ~newtype_level env ty ty'
  with
    Unify trace ->
      raise(Error(loc, Pattern_type_clash(trace)))
  | Tags(l1,l2) ->
      raise(Typetexp.Error(loc, Typetexp.Variant_tags (l1, l2)))
  | Unification_recursive_abbrev trace ->
      raise(Error(loc, Recursive_local_constraint trace))


(* Creating new conjunctive types is not allowed when typing patterns *)
let unify_pat env pat expected_ty =
  unify_pat_types pat.pat_loc env pat.pat_type expected_ty

(* make all Reither present in open variants *)
let finalize_variant pat =
  match pat.pat_desc with
    Tpat_variant(tag, opat, r) ->
      let row =
        match expand_head pat.pat_env pat.pat_type with
          {desc = Tvariant row} -> r := row; row_repr row
        | _ -> assert false
      in
      begin match row_field tag row with
      | Rabsent -> assert false
      | Reither (true, [], _, e) when not row.row_closed ->
          set_row_field e (Rpresent None)
      | Reither (false, ty::tl, _, e) when not row.row_closed ->
          set_row_field e (Rpresent (Some ty));
          begin match opat with None -> assert false
          | Some pat -> List.iter (unify_pat pat.pat_env pat) (ty::tl)
          end
      | Reither (c, l, true, e) when not row.row_fixed ->
          set_row_field e (Reither (c, [], false, ref None))
      | _ -> ()
      end;
      (* Force check of well-formedness   WHY? *)
      (* unify_pat pat.pat_env pat
        (newty(Tvariant{row_fields=[]; row_more=newvar(); row_closed=false;
                        row_bound=(); row_fixed=false; row_name=None})); *)
  | _ -> ()

let rec iter_pattern f p =
  f p;
  iter_pattern_desc (iter_pattern f) p.pat_desc

let has_variants p =
  try
    iter_pattern (function {pat_desc=Tpat_variant _} -> raise Exit | _ -> ())
      p;
    false
  with Exit ->
    true


(* pattern environment *)
let pattern_variables = ref ([]: (Ident.t * type_expr * Location.t * bool (* as-variable *)) list)
let pattern_force = ref ([] : (unit -> unit) list)
let pattern_scope = ref (None : Annot.ident option);;
let allow_modules = ref false
let module_variables = ref ([] : (string * Location.t) list)
let reset_pattern scope allow =
  pattern_variables := [];
  pattern_force := [];
  pattern_scope := scope;
  allow_modules := allow;
  module_variables := [];
;;

let enter_variable ?(is_module=false) ?(is_as_variable=false) loc name ty =
  if List.exists (fun (id, _, _, _) -> Ident.name id = name) !pattern_variables
  then raise(Error(loc, Multiply_bound_variable name));
  let id = Ident.create name in
  pattern_variables := (id, ty, loc, is_as_variable) :: !pattern_variables;
  if is_module then begin
    (* Note: unpack patterns enter a variable of the same name *)
    if not !allow_modules then raise (Error (loc, Modules_not_allowed));
    module_variables := (name, loc) :: !module_variables
  end else begin
    match !pattern_scope with
    | None -> ()
    | Some s -> Stypes.record (Stypes.An_ident (loc, name, s));
  end;
  id

let sort_pattern_variables vs =
  List.sort
    (fun (x,_,_,_) (y,_,_,_) -> Pervasives.compare (Ident.name x) (Ident.name y))
    vs

let enter_orpat_variables loc env  p1_vs p2_vs =
  (* unify_vars operate on sorted lists *)

  let p1_vs = sort_pattern_variables p1_vs
  and p2_vs = sort_pattern_variables p2_vs in

  let rec unify_vars p1_vs p2_vs = match p1_vs, p2_vs with
      | (x1,t1,l1,a1)::rem1, (x2,t2,l2,a2)::rem2 when Ident.equal x1 x2 ->
          if x1==x2 then
            unify_vars rem1 rem2
          else begin
            begin try
              unify env t1 t2
            with
            | Unify trace ->
                raise(Error(loc, Pattern_type_clash(trace)))
            end;
          (x2,x1)::unify_vars rem1 rem2
          end
      | [],[] -> []
      | (x,_,_,_)::_, [] -> raise (Error (loc, Orpat_vars x))
      | [],(x,_,_,_)::_  -> raise (Error (loc, Orpat_vars x))
      | (x,_,_,_)::_, (y,_,_,_)::_ ->
          let min_var =
            if Ident.name x < Ident.name y then x
            else y in
          raise (Error (loc, Orpat_vars min_var)) in
  unify_vars p1_vs p2_vs

let rec build_as_type env p =
  match p.pat_desc with
    Tpat_alias(p1, _) -> build_as_type env p1
  | Tpat_tuple pl ->
      let tyl = List.map (build_as_type env) pl in
      newty (Ttuple tyl)
  | Tpat_construct(cstr, pl) ->
      let keep = cstr.cstr_private = Private || cstr.cstr_existentials <> [] in
      if keep then p.pat_type else
      let tyl = List.map (build_as_type env) pl in
      let ty_args, ty_res = instance_constructor cstr in
      List.iter2 (fun (p,ty) -> unify_pat env {p with pat_type = ty})
        (List.combine pl tyl) ty_args;
      ty_res
  | Tpat_variant(l, p', _) ->
      let ty = may_map (build_as_type env) p' in
      newty (Tvariant{row_fields=[l, Rpresent ty]; row_more=newvar();
                      row_bound=(); row_name=None;
                      row_fixed=false; row_closed=false})
  | Tpat_record lpl ->
      let lbl = fst(List.hd lpl) in
      if lbl.lbl_private = Private then p.pat_type else
      let ty = newvar () in
      let ppl = List.map (fun (l,p) -> l.lbl_pos, p) lpl in
      let do_label lbl =
        let _, ty_arg, ty_res = instance_label false lbl in
        unify_pat env {p with pat_type = ty} ty_res;
        let refinable =
          lbl.lbl_mut = Immutable && List.mem_assoc lbl.lbl_pos ppl &&
          match (repr lbl.lbl_arg).desc with Tpoly _ -> false | _ -> true in
        if refinable then begin
          let arg = List.assoc lbl.lbl_pos ppl in
          unify_pat env {arg with pat_type = build_as_type env arg} ty_arg
        end else begin
          let _, ty_arg', ty_res' = instance_label false lbl in
          unify env ty_arg ty_arg';
          unify_pat env p ty_res'
        end in
      Array.iter do_label lbl.lbl_all;
      ty
  | Tpat_or(p1, p2, row) ->
      begin match row with
        None ->
          let ty1 = build_as_type env p1 and ty2 = build_as_type env p2 in
          unify_pat env {p2 with pat_type = ty2} ty1;
          ty1
      | Some row ->
          let row = row_repr row in
          newty (Tvariant{row with row_closed=false; row_more=newvar()})
      end
  | Tpat_any | Tpat_var _ | Tpat_constant _
  | Tpat_array _ | Tpat_lazy _ -> p.pat_type

let build_or_pat env loc lid =
  let path, decl = Typetexp.find_type env loc lid
  in
  let tyl = List.map (fun _ -> newvar()) decl.type_params in
  let row0 =
    let ty = expand_head env (newty(Tconstr(path, tyl, ref Mnil))) in
    match ty.desc with
      Tvariant row when static_row row -> row
    | _ -> raise(Error(loc, Not_a_variant_type lid))
  in
  let pats, fields =
    List.fold_left
      (fun (pats,fields) (l,f) ->
        match row_field_repr f with
          Rpresent None ->
            (l,None) :: pats,
            (l, Reither(true,[], true, ref None)) :: fields
        | Rpresent (Some ty) ->
            (l, Some {pat_desc=Tpat_any; pat_loc=Location.none; pat_env=env;
                      pat_type=ty})
            :: pats,
            (l, Reither(false, [ty], true, ref None)) :: fields
        | _ -> pats, fields)
      ([],[]) (row_repr row0).row_fields in
  let row =
    { row_fields = List.rev fields; row_more = newvar(); row_bound = ();
      row_closed = false; row_fixed = false; row_name = Some (path, tyl) }
  in
  let ty = newty (Tvariant row) in
  let gloc = {loc with Location.loc_ghost=true} in
  let row' = ref {row with row_more=newvar()} in
  let pats =
    List.map (fun (l,p) -> {pat_desc=Tpat_variant(l,p,row'); pat_loc=gloc;
                            pat_env=env; pat_type=ty})
      pats
  in
  match pats with
    [] -> raise(Error(loc, Not_a_variant_type lid))
  | pat :: pats ->
      let r =
        List.fold_left
          (fun pat pat0 -> {pat_desc=Tpat_or(pat0,pat,Some row0);
                            pat_loc=gloc; pat_env=env; pat_type=ty})
          pat pats in
      (rp { r with pat_loc = loc },ty)

(* Records *)

let rec find_record_qual = function
  | [] -> None
  | (Longident.Ldot (modname, _), _) :: _ -> Some modname
  | _ :: rest -> find_record_qual rest

let type_label_a_list ?labels env loc type_lbl_a lid_a_list =
  let record_qual = find_record_qual lid_a_list in
  let lbl_a_list =
    List.map
      (fun (lid, a) ->
        match lid, labels, record_qual with
          Longident.Lident s, Some labels, _ when Hashtbl.mem labels s ->
            Hashtbl.find labels s, a
        | Longident.Lident s, _, Some modname ->
            Typetexp.find_label env loc (Longident.Ldot (modname, s)), a
        | _ ->
            Typetexp.find_label env loc lid, a)
      lid_a_list in
  (* Invariant: records are sorted in the typed tree *)
  let lbl_a_list =
    List.sort
      (fun (lbl1,_) (lbl2,_) -> compare lbl1.lbl_pos lbl2.lbl_pos)
      lbl_a_list
  in
  List.map type_lbl_a lbl_a_list

let lid_of_label label =
  match repr label.lbl_res with
  | {desc = Tconstr(Path.Pdot(mpath,_,_),_,_)} ->
      Longident.Ldot(lid_of_path mpath, label.lbl_name)
  | _ -> Longident.Lident label.lbl_name

(* Checks over the labels mentioned in a record pattern:
   no duplicate definitions (error); properly closed (warning) *)

let check_recordpat_labels loc lbl_pat_list closed =
  match lbl_pat_list with
  | [] -> ()                            (* should not happen *)
  | (label1, _) :: _ ->
      let all = label1.lbl_all in
      let defined = Array.make (Array.length all) false in
      let check_defined (label, _) =
        if defined.(label.lbl_pos)
        then raise(Error(loc, Label_multiply_defined
                                       (Longident.Lident label.lbl_name)))
        else defined.(label.lbl_pos) <- true in
      List.iter check_defined lbl_pat_list;
      if closed = Closed
      && Warnings.is_active (Warnings.Non_closed_record_pattern "")
      then begin
        let undefined = ref [] in
        for i = 0 to Array.length all - 1 do
          if not defined.(i) then undefined := all.(i).lbl_name :: !undefined
        done;
        if !undefined <> [] then begin
          let u = String.concat ", " (List.rev !undefined) in
          Location.prerr_warning loc (Warnings.Non_closed_record_pattern u)
        end
      end

(* unification of a type with a tconstr with
   freshly created arguments *)
let unify_head_only loc env ty constr =
  let (_, ty_res) = instance_constructor constr in
  match (repr ty_res).desc with
  | Tconstr(p,args,m) ->
      ty_res.desc <- Tconstr(p,List.map (fun _ -> newvar ()) args,m);
      enforce_constraints env ty_res;
      unify_pat_types loc env ty ty_res
  | _ -> assert false

(* Typing of patterns *)

(* type_pat does not generate local constraints inside or patterns *)
type type_pat_mode =
  | Normal
  | Inside_or

(* type_pat propagates the expected type as well as maps for
   constructors and labels.
   Unification may update the typing environment. *)
let rec type_pat ~constrs ~labels ~no_existentials ~mode ~env sp expected_ty =
  let type_pat ?(mode=mode) ?(env=env) =
    type_pat ~constrs ~labels ~no_existentials ~mode ~env in
  let loc = sp.ppat_loc in
  match sp.ppat_desc with
    Ppat_any ->
      rp {
        pat_desc = Tpat_any;
        pat_loc = loc;
        pat_type = expected_ty;
        pat_env = !env }
  | Ppat_var name ->
      let id = enter_variable loc name expected_ty in
      rp {
        pat_desc = Tpat_var id;
        pat_loc = loc;
        pat_type = expected_ty;
        pat_env = !env }
  | Ppat_unpack name ->
      let id = enter_variable loc name expected_ty ~is_module:true in
      rp {
        pat_desc = Tpat_var id;
        pat_loc = loc;
        pat_type = expected_ty;
        pat_env = !env }
  | Ppat_constraint({ppat_desc=Ppat_var name; ppat_loc=loc},
                    ({ptyp_desc=Ptyp_poly _} as sty)) ->
      (* explicitly polymorphic type *)
      let ty, force = Typetexp.transl_simple_type_delayed !env sty in
      unify_pat_types loc !env ty expected_ty;
      pattern_force := force :: !pattern_force;
      begin match ty.desc with
      | Tpoly (body, tyl) ->
          begin_def ();
          let _, ty' = instance_poly ~keep_names:true false tyl body in
          end_def ();
          generalize ty';
          let id = enter_variable loc name ty' in
          rp { pat_desc = Tpat_var id;
               pat_loc = loc;
               pat_type = ty;
               pat_env = !env }
      | _ -> assert false
      end
  | Ppat_alias(sq, name) ->
      let q = type_pat sq expected_ty in
      begin_def ();
      let ty_var = build_as_type !env q in
      end_def ();
      generalize ty_var;
      let id = enter_variable ~is_as_variable:true loc name ty_var in
      rp {
        pat_desc = Tpat_alias(q, id);
        pat_loc = loc;
        pat_type = q.pat_type;
        pat_env = !env }
  | Ppat_constant cst ->
      unify_pat_types loc !env (type_constant cst) expected_ty;
      rp {
        pat_desc = Tpat_constant cst;
        pat_loc = loc;
        pat_type = expected_ty;
        pat_env = !env }
  | Ppat_tuple spl ->
      let spl_ann = List.map (fun p -> (p,newvar ())) spl in
      let ty = newty (Ttuple(List.map snd spl_ann)) in
      unify_pat_types loc !env ty expected_ty;
      let pl = List.map (fun (p,t) -> type_pat p t) spl_ann in
      rp {
        pat_desc = Tpat_tuple pl;
        pat_loc = loc;
        pat_type = expected_ty;
        pat_env = !env }
  | Ppat_construct(lid, sarg, explicit_arity) ->
      let constr =
        match lid, constrs with
          Longident.Lident s, Some constrs when Hashtbl.mem constrs s ->
            Hashtbl.find constrs s
        | _ ->  Typetexp.find_constructor !env loc lid
      in
      Env.mark_constructor `Pattern !env (Longident.last lid) constr;
      if no_existentials && constr.cstr_existentials <> [] then
        raise (Error (loc, Unexpected_existential));
      (* if constructor is gadt, we must verify that the expected type has the
         correct head *)
      if constr.cstr_generalized then
        unify_head_only loc !env expected_ty constr;
      let sargs =
        match sarg with
          None -> []
        | Some {ppat_desc = Ppat_tuple spl} when explicit_arity -> spl
        | Some {ppat_desc = Ppat_tuple spl} when constr.cstr_arity > 1 -> spl
        | Some({ppat_desc = Ppat_any} as sp) when constr.cstr_arity <> 1 ->
            if constr.cstr_arity = 0 then
              Location.prerr_warning sp.ppat_loc
                                     Warnings.Wildcard_arg_to_constant_constr;
            replicate_list sp constr.cstr_arity
        | Some sp -> [sp] in
      if List.length sargs <> constr.cstr_arity then
        raise(Error(loc, Constructor_arity_mismatch(lid,
                                     constr.cstr_arity, List.length sargs)));
      let (ty_args, ty_res) =
        instance_constructor ~in_pattern:(env, get_newtype_level ()) constr
      in
      if constr.cstr_generalized && mode = Normal then
        unify_pat_types_gadt loc env ty_res expected_ty
      else
        unify_pat_types loc !env ty_res expected_ty;
      let args = List.map2 (fun p t -> type_pat p t) sargs ty_args in
      rp {
        pat_desc = Tpat_construct(constr, args);
        pat_loc = loc;
        pat_type = expected_ty;
        pat_env = !env }
  | Ppat_variant(l, sarg) ->
      let arg = may_map (fun p -> type_pat p (newvar())) sarg in
      let arg_type = match arg with None -> [] | Some arg -> [arg.pat_type]  in
      let row = { row_fields =
                    [l, Reither(arg = None, arg_type, true, ref None)];
                  row_bound = ();
                  row_closed = false;
                  row_more = newvar ();
                  row_fixed = false;
                  row_name = None } in
      unify_pat_types loc !env (newty (Tvariant row)) expected_ty;
      rp {
        pat_desc = Tpat_variant(l, arg, ref {row with row_more = newvar()});
        pat_loc = loc;
        pat_type =  expected_ty;
        pat_env = !env }
  | Ppat_record(lid_sp_list, closed) ->
      let type_label_pat (label, sarg) =
        begin_def ();
        let (vars, ty_arg, ty_res) = instance_label false label in
        if vars = [] then end_def ();
        begin try
          unify_pat_types loc !env ty_res expected_ty
        with Unify trace ->
          raise(Error(loc, Label_mismatch(lid_of_label label, trace)))
        end;
        let arg = type_pat sarg ty_arg in
        if vars <> [] then begin
          end_def ();
          generalize ty_arg;
          List.iter generalize vars;
          let instantiated tv =
            let tv = expand_head !env tv in
            not (is_Tvar tv) || tv.level <> generic_level in
          if List.exists instantiated vars then
            raise (Error(loc, Polymorphic_label (lid_of_label label)))
        end;
        (label, arg)
      in
      let lbl_pat_list =
        type_label_a_list ?labels !env loc type_label_pat lid_sp_list in
      check_recordpat_labels loc lbl_pat_list closed;
      rp {
        pat_desc = Tpat_record lbl_pat_list;
        pat_loc = loc;
        pat_type = expected_ty;
        pat_env = !env }
  | Ppat_array spl ->
      let ty_elt = newvar() in
      unify_pat_types
        loc !env (instance_def (Predef.type_array ty_elt)) expected_ty;
      let spl_ann = List.map (fun p -> (p,newvar())) spl in
      let pl = List.map (fun (p,t) -> type_pat p ty_elt) spl_ann in
      rp {
        pat_desc = Tpat_array pl;
        pat_loc = loc;
        pat_type = expected_ty;
        pat_env = !env }
  | Ppat_or(sp1, sp2) ->
      let initial_pattern_variables = !pattern_variables in
      let p1 = type_pat ~mode:Inside_or sp1 expected_ty in
      let p1_variables = !pattern_variables in
      pattern_variables := initial_pattern_variables;
      let p2 = type_pat ~mode:Inside_or sp2 expected_ty in
      let p2_variables = !pattern_variables in
      let alpha_env =
        enter_orpat_variables loc !env p1_variables p2_variables in
      pattern_variables := p1_variables;
      rp {
        pat_desc = Tpat_or(p1, alpha_pat alpha_env p2, None);
        pat_loc = loc;
        pat_type = expected_ty;
        pat_env = !env }
  | Ppat_lazy sp1 ->
      let nv = newvar () in
      unify_pat_types loc !env (instance_def (Predef.type_lazy_t nv)) expected_ty;
      let p1 = type_pat sp1 nv in
      rp {
        pat_desc = Tpat_lazy p1;
        pat_loc = loc;
        pat_type = expected_ty;
        pat_env = !env }
  | Ppat_constraint(sp, sty) ->
      (* Separate when not already separated by !principal *)
      let separate = true in
      if separate then begin_def();
      let ty, force = Typetexp.transl_simple_type_delayed !env sty in
      let ty, expected_ty' =
        if separate then begin
          end_def();
          generalize_structure ty;
          instance !env ty, instance !env ty
        end else ty, ty
      in
      unify_pat_types loc !env ty expected_ty;
      let p = type_pat sp expected_ty' in
      (*Format.printf "%a@.%a@."
        Printtyp.raw_type_expr ty
        Printtyp.raw_type_expr p.pat_type;*)
      pattern_force := force :: !pattern_force;
      if separate then
        match p.pat_desc with
          Tpat_var id ->
            {p with pat_type = ty;
             pat_desc = Tpat_alias ({p with pat_desc = Tpat_any}, id)}
        | _ -> {p with pat_type = ty}
      else p
  | Ppat_type lid ->
      let (r,ty) = build_or_pat !env loc lid in
      unify_pat_types loc !env ty expected_ty;
      r

let type_pat ?(allow_existentials=false) ?constrs ?labels
    ?(lev=get_current_level()) env sp expected_ty =
  newtype_level := Some lev;
  try
    let r =
      type_pat ~no_existentials:(not allow_existentials) ~constrs ~labels
        ~mode:Normal ~env sp expected_ty in
    iter_pattern (fun p -> p.pat_env <- !env) r;
    newtype_level := None;
    r
  with e ->
    newtype_level := None;
    raise e


(* this function is passed to Partial.parmatch
   to type check gadt nonexhaustiveness *)
let partial_pred ~lev env expected_ty constrs labels p =
  let snap = snapshot () in
  try
    reset_pattern None true;
    let typed_p =
      type_pat ~allow_existentials:true ~lev
        ~constrs ~labels (ref env) p expected_ty
    in
    backtrack snap;
    (* types are invalidated but we don't need them here *)
    Some typed_p
  with _ ->
    backtrack snap;
    None

let rec iter3 f lst1 lst2 lst3 =
  match lst1,lst2,lst3 with
  | x1::xs1,x2::xs2,x3::xs3 ->
      f x1 x2 x3;
      iter3 f xs1 xs2 xs3
  | [],[],[] ->
      ()
  | _ ->
      assert false

let add_pattern_variables ?check ?check_as env =
  let pv = get_ref pattern_variables in
  (List.fold_right
    (fun (id, ty, loc, as_var) env ->
       let check = if as_var then check_as else check in
       let e1 = Env.add_value ?check id
           {val_type = ty; val_kind = Val_reg; val_loc = loc} env in
       Env.add_annot id (Annot.Iref_internal loc) e1)
    pv env,
   get_ref module_variables)

let type_pattern ~lev env spat scope expected_ty =
  reset_pattern scope true;
  let new_env = ref env in
  let pat = type_pat ~allow_existentials:true ~lev new_env spat expected_ty in
  let new_env, unpacks =
    add_pattern_variables !new_env
      ~check:(fun s -> Warnings.Unused_var_strict s)
      ~check_as:(fun s -> Warnings.Unused_var s) in
  (pat, new_env, get_ref pattern_force, unpacks)

let type_pattern_list env spatl scope expected_tys allow =
  reset_pattern scope allow;
  let new_env = ref env in
  let patl = List.map2 (type_pat new_env) spatl expected_tys in
  let new_env, unpacks = add_pattern_variables !new_env in
  (patl, new_env, get_ref pattern_force, unpacks)

let type_class_arg_pattern cl_num val_env met_env l spat =
  reset_pattern None false;
  let nv = newvar () in
  let pat = type_pat (ref val_env) spat nv in
  if has_variants pat then begin
    Parmatch.pressure_variants val_env [pat];
    iter_pattern finalize_variant pat
  end;
  List.iter (fun f -> f()) (get_ref pattern_force);
  if is_optional l then unify_pat val_env pat (type_option (newvar ()));
  let (pv, met_env) =
    List.fold_right
      (fun (id, ty, loc, as_var) (pv, env) ->
         let check s =
           if as_var then Warnings.Unused_var s
           else Warnings.Unused_var_strict s in
         let id' = Ident.create (Ident.name id) in
         ((id', id, ty)::pv,
          Env.add_value id' {val_type = ty;
                             val_kind = Val_ivar (Immutable, cl_num);
                             val_loc = loc;
                            } ~check
            env))
      !pattern_variables ([], met_env)
  in
  let val_env, _ = add_pattern_variables val_env in
  (pat, pv, val_env, met_env)

let mkpat d = { ppat_desc = d; ppat_loc = Location.none }

let type_self_pattern cl_num privty val_env met_env par_env spat =
  let spat =
    mkpat (Ppat_alias (mkpat(Ppat_alias (spat, "selfpat-*")),
                       "selfpat-" ^ cl_num))
  in
  reset_pattern None false;
  let nv = newvar() in
  let pat = type_pat (ref val_env) spat nv in
  List.iter (fun f -> f()) (get_ref pattern_force);
  let meths = ref Meths.empty in
  let vars = ref Vars.empty in
  let pv = !pattern_variables in
  pattern_variables := [];
  let (val_env, met_env, par_env) =
    List.fold_right
      (fun (id, ty, loc, as_var) (val_env, met_env, par_env) ->
         (Env.add_value id {val_type = ty;
                            val_kind = Val_unbound;
                            val_loc = loc;
                           } val_env,
          Env.add_value id {val_type = ty;
                            val_kind = Val_self (meths, vars, cl_num, privty);
                            val_loc = loc;
                           }
            ~check:(fun s -> if as_var then Warnings.Unused_var s
                             else Warnings.Unused_var_strict s)
            met_env,
          Env.add_value id {val_type = ty; val_kind = Val_unbound;
                            val_loc = loc;
                           } par_env))
      pv (val_env, met_env, par_env)
  in
  (pat, meths, vars, val_env, met_env, par_env)

let delayed_checks = ref []
let reset_delayed_checks () = delayed_checks := []
let add_delayed_check f = delayed_checks := f :: !delayed_checks
let force_delayed_checks () =
  (* checks may change type levels *)
  let snap = Btype.snapshot () in
  List.iter (fun f -> f ()) (List.rev !delayed_checks);
  reset_delayed_checks ();
  Btype.backtrack snap


(* Generalization criterion for expressions *)

let rec is_nonexpansive exp =
  match exp.exp_desc with
    Texp_ident(_,_) -> true
  | Texp_constant _ -> true
  | Texp_let(rec_flag, pat_exp_list, body) ->
      List.for_all (fun (pat, exp) -> is_nonexpansive exp) pat_exp_list &&
      is_nonexpansive body
  | Texp_function _ -> true
  | Texp_apply(e, (None,_)::el) ->
      is_nonexpansive e && List.for_all is_nonexpansive_opt (List.map fst el)
  | Texp_tuple el ->
      List.for_all is_nonexpansive el
  | Texp_construct(_, el) ->
      List.for_all is_nonexpansive el
  | Texp_variant(_, arg) -> is_nonexpansive_opt arg
  | Texp_record(lbl_exp_list, opt_init_exp) ->
      List.for_all
        (fun (lbl, exp) -> lbl.lbl_mut = Immutable && is_nonexpansive exp)
        lbl_exp_list
      && is_nonexpansive_opt opt_init_exp
  | Texp_field(exp, lbl) -> is_nonexpansive exp
  | Texp_array [] -> true
  | Texp_ifthenelse(cond, ifso, ifnot) ->
      is_nonexpansive ifso && is_nonexpansive_opt ifnot
  | Texp_sequence (e1, e2) -> is_nonexpansive e2  (* PR#4354 *)
  | Texp_new (_, cl_decl) when Ctype.class_type_arity cl_decl.cty_type > 0 ->
      true
  (* Note: nonexpansive only means no _observable_ side effects *)
  | Texp_lazy e -> is_nonexpansive e
  | Texp_object ({cl_field=fields}, {cty_vars=vars}, _) ->
      let count = ref 0 in
      List.for_all
        (function
            Cf_meth _ -> true
          | Cf_val (_,_,e,_) -> incr count; is_nonexpansive_opt e
          | Cf_init e -> is_nonexpansive e
          | Cf_inher _ -> false)
        fields &&
      Vars.fold (fun _ (mut,_,_) b -> decr count; b && mut = Immutable)
        vars true &&
      !count = 0
  | Texp_pack mexp ->
      is_nonexpansive_mod mexp
  | _ -> false

and is_nonexpansive_mod mexp =
  match mexp.mod_desc with
  | Tmod_ident _ -> true
  | Tmod_functor _ -> true
  | Tmod_unpack (e, _) -> is_nonexpansive e
  | Tmod_constraint (m, _, _) -> is_nonexpansive_mod m
  | Tmod_structure items ->
      List.for_all
        (function
          | Tstr_eval _ | Tstr_primitive _ | Tstr_type _ | Tstr_modtype _
          | Tstr_open _ | Tstr_cltype _ | Tstr_exn_rebind _ -> true
          | Tstr_value (_, pat_exp_list) ->
              List.for_all (fun (_, exp) -> is_nonexpansive exp) pat_exp_list
          | Tstr_module (_, m) | Tstr_include (m, _) -> is_nonexpansive_mod m
          | Tstr_recmodule id_mod_list ->
              List.for_all (fun (_, m) -> is_nonexpansive_mod m) id_mod_list
          | Tstr_exception _ -> false (* true would be unsound *)
          | Tstr_class _ -> false (* could be more precise *)
        )
        items
  | Tmod_apply _ -> false

and is_nonexpansive_opt = function
    None -> true
  | Some e -> is_nonexpansive e

(* Typing format strings for printing or reading.

   These format strings are used by functions in modules Printf, Format, and
   Scanf.

   (Handling of * modifiers contributed by Thorsten Ohl.) *)

external string_to_format :
 string -> ('a, 'b, 'c, 'd, 'e, 'f) format6 = "%identity"
external format_to_string :
 ('a, 'b, 'c, 'd, 'e, 'f) format6 -> string = "%identity"

let type_format loc fmt =

  let ty_arrow gty ty = newty (Tarrow ("", instance_def gty, ty, Cok)) in

  let bad_conversion fmt i c =
    raise (Error (loc, Bad_conversion (fmt, i, c))) in
  let incomplete_format fmt =
    raise (Error (loc, Incomplete_format fmt)) in

  let rec type_in_format fmt =

    let len = String.length fmt in

    let ty_input = newvar ()
    and ty_result = newvar ()
    and ty_aresult = newvar ()
    and ty_uresult = newvar () in

    let meta = ref 0 in

    let rec scan_format i =
      if i >= len then
        if !meta = 0
        then ty_uresult, ty_result
        else incomplete_format fmt else
      match fmt.[i] with
      | '%' -> scan_opts i (i + 1)
      | _ -> scan_format (i + 1)
    and scan_opts i j =
      if j >= len then incomplete_format fmt else
      match fmt.[j] with
      | '_' -> scan_rest true i (j + 1)
      | _ -> scan_rest false i j
    and scan_rest skip i j =
      let rec scan_flags i j =
        if j >= len then incomplete_format fmt else
        match fmt.[j] with
        | '#' | '0' | '-' | ' ' | '+' -> scan_flags i (j + 1)
        | _ -> scan_width i j
      and scan_width i j = scan_width_or_prec_value scan_precision i j
      and scan_decimal_string scan i j =
        if j >= len then incomplete_format fmt else
        match fmt.[j] with
        | '0' .. '9' -> scan_decimal_string scan i (j + 1)
        | _ -> scan i j
      and scan_width_or_prec_value scan i j =
        if j >= len then incomplete_format fmt else
        match fmt.[j] with
        | '*' ->
          let ty_uresult, ty_result = scan i (j + 1) in
          ty_uresult, ty_arrow Predef.type_int ty_result
        | '-' | '+' -> scan_decimal_string scan i (j + 1)
        | _ -> scan_decimal_string scan i j
      and scan_precision i j =
        if j >= len then incomplete_format fmt else
        match fmt.[j] with
        | '.' -> scan_width_or_prec_value scan_conversion i (j + 1)
        | _ -> scan_conversion i j
      and scan_indication j =
        if j >= len then j - 1 else
        match fmt.[j] with
        | '@' ->
          let k = j + 1 in
          if k >= len then j - 1 else
          begin match fmt.[k] with
          | '%' ->
            let k = k + 1 in
            if k >= len then j - 1 else
            begin match fmt.[k] with
            | '%' | '@' -> k
            | _c -> j - 1
            end
          | _c -> k
          end
        | _c -> j - 1
      and scan_range j =
        let rec scan_closing j =
          if j >= len then incomplete_format fmt else
          match fmt.[j] with
          | ']' -> j
          | '%' ->
            let j = j + 1 in
            if j >= len then incomplete_format fmt else
            begin match fmt.[j] with
            | '%' | '@' -> scan_closing (j + 1)
            | c -> bad_conversion fmt j c
            end
          | c -> scan_closing (j + 1) in
        let scan_first_pos j =
          if j >= len then incomplete_format fmt else
          match fmt.[j] with
          | ']' -> scan_closing (j + 1)
          | c -> scan_closing j in
        let rec scan_first_neg j =
          if j >= len then incomplete_format fmt else
          match fmt.[j] with
          | '^' -> scan_first_pos (j + 1)
          | c -> scan_first_pos j in

        scan_first_neg j

      and conversion j ty_arg =
        let ty_uresult, ty_result = scan_format (j + 1) in
        ty_uresult,
        if skip then ty_result else ty_arrow ty_arg ty_result

      and conversion_a j ty_e ty_arg =
        let ty_uresult, ty_result = conversion j ty_arg in
        let ty_a = ty_arrow ty_input (ty_arrow ty_e ty_aresult) in
        ty_uresult, ty_arrow ty_a ty_result

      and conversion_r j ty_e ty_arg =
        let ty_uresult, ty_result = conversion j ty_arg in
        let ty_r = ty_arrow ty_input ty_e in
        ty_arrow ty_r ty_uresult, ty_result

      and scan_conversion i j =
        if j >= len then incomplete_format fmt else
        match fmt.[j] with
        | '%' | '@' | '!' | ',' -> scan_format (j + 1)
        | 's' | 'S' ->
          let j = scan_indication (j + 1) in
          conversion j Predef.type_string
        | '[' ->
          let j = scan_range (j + 1) in
          let j = scan_indication (j + 1) in
          conversion j Predef.type_string
        | 'c' | 'C' -> conversion j Predef.type_char
        | 'd' | 'i' | 'o' | 'u' | 'x' | 'X' | 'N' ->
          conversion j Predef.type_int
        | 'f' | 'e' | 'E' | 'g' | 'G' | 'F' -> conversion j Predef.type_float
        | 'B' | 'b' -> conversion j Predef.type_bool
        | 'a' | 'r' as conv ->
          let conversion =
            if conv = 'a' then conversion_a else conversion_r in
          let ty_e = newvar () in
          let j = j + 1 in
          if j >= len then conversion (j - 1) ty_e ty_e else begin
            match fmt.[j] with
(*            | 'a' | 'A' -> conversion j ty_e (Predef.type_array ty_e)
            | 'l' | 'L' -> conversion j ty_e (Predef.type_list ty_e)
            | 'o' | 'O' -> conversion j ty_e (Predef.type_option ty_e)*)
            | _ -> conversion (j - 1) ty_e ty_e end
(*        | 'r' ->
          let ty_e = newvar () in
          let j = j + 1 in
          if j >= len then conversion_r (j - 1) ty_e ty_e else begin
            match fmt.[j] with
            | 'a' | 'A' -> conversion_r j ty_e (Pref.type_array ty_e)
            | 'l' | 'L' -> conversion_r j ty_e (Pref.type_list ty_e)
            | 'o' | 'O' -> conversion_r j ty_e (Pref.type_option ty_e)
            | _ -> conversion_r (j - 1) ty_e ty_e end *)
        | 't' -> conversion j (ty_arrow ty_input ty_aresult)
        | 'l' | 'n' | 'L' as c ->
          let j = j + 1 in
          if j >= len then conversion (j - 1) Predef.type_int else begin
            match fmt.[j] with
            | 'd' | 'i' | 'o' | 'u' | 'x' | 'X' ->
              let ty_arg =
                match c with
                | 'l' -> Predef.type_int32
                | 'n' -> Predef.type_nativeint
                | _ -> Predef.type_int64 in
              conversion j ty_arg
            | c -> conversion (j - 1) Predef.type_int
          end
        | '{' | '(' as c ->
          let j = j + 1 in
          if j >= len then incomplete_format fmt else
          let sj =
            Printf.CamlinternalPr.Tformat.sub_format
              (fun fmt -> incomplete_format (format_to_string fmt))
              (fun fmt -> bad_conversion (format_to_string fmt))
              c (string_to_format fmt) j in
          let sfmt = String.sub fmt j (sj - 2 - j) in
          let ty_sfmt = type_in_format sfmt in
          begin match c with
          | '{' -> conversion (sj - 1) ty_sfmt
          | _ -> incr meta; conversion (j - 1) ty_sfmt end
        | ')' when !meta > 0 -> decr meta; scan_format (j + 1)
        | c -> bad_conversion fmt i c in
      scan_flags i j in

    let ty_ureader, ty_args = scan_format 0 in
    newty
      (Tconstr
        (Predef.path_format6,
         [ ty_args; ty_input; ty_aresult;
           ty_ureader; ty_uresult; ty_result; ],
         ref Mnil)) in

  type_in_format fmt

(* Approximate the type of an expression, for better recursion *)

let rec approx_type env sty =
  match sty.ptyp_desc with
    Ptyp_arrow (p, _, sty) ->
      let ty1 = if is_optional p then type_option (newvar ()) else newvar () in
      newty (Tarrow (p, ty1, approx_type env sty, Cok))
  | Ptyp_tuple args ->
      newty (Ttuple (List.map (approx_type env) args))
  | Ptyp_constr (lid, ctl) ->
      begin try
        let (path, decl) = Env.lookup_type lid env in
        if List.length ctl <> decl.type_arity then raise Not_found;
        let tyl = List.map (approx_type env) ctl in
        newconstr path tyl
      with Not_found -> newvar ()
      end
  | Ptyp_poly (_, sty) ->
      approx_type env sty
  | _ -> newvar ()

let rec type_approx env sexp =
  match sexp.pexp_desc with
    Pexp_let (_, _, e) -> type_approx env e
  | Pexp_function (p,_,(_,e)::_) when is_optional p ->
       newty (Tarrow(p, type_option (newvar ()), type_approx env e, Cok))
  | Pexp_function (p,_,(_,e)::_) ->
       newty (Tarrow(p, newvar (), type_approx env e, Cok))
  | Pexp_match (_, (_,e)::_) -> type_approx env e
  | Pexp_try (e, _) -> type_approx env e
  | Pexp_tuple l -> newty (Ttuple(List.map (type_approx env) l))
  | Pexp_ifthenelse (_,e,_) -> type_approx env e
  | Pexp_sequence (_,e) -> type_approx env e
  | Pexp_constraint (e, sty1, sty2) ->
      let approx_ty_opt = function
        | None -> newvar ()
        | Some sty -> approx_type env sty
      in
      let ty = type_approx env e
      and ty1 = approx_ty_opt sty1
      and ty2 = approx_ty_opt sty2 in
      begin try unify env ty ty1 with Unify trace ->
        raise(Error(sexp.pexp_loc, Expr_type_clash trace))
      end;
      if sty2 = None then ty1 else ty2
  | _ -> newvar ()

(* List labels in a function type, and whether return type is a variable *)
let rec list_labels_aux env visited ls ty_fun =
  let ty = expand_head env ty_fun in
  if List.memq ty visited then
    List.rev ls, false
  else match ty.desc with
    Tarrow (l, _, ty_res, _) ->
      list_labels_aux env (ty::visited) (l::ls) ty_res
  | _ ->
      List.rev ls, is_Tvar ty

let list_labels env ty = list_labels_aux env [] [] ty

(* Check that all univars are safe in a type *)
let check_univars env expans kind exp ty_expected vars =
  if expans && not (is_nonexpansive exp) then
    generalize_expansive env exp.exp_type;
  (* need to expand twice? cf. Ctype.unify2 *)
  let vars = List.map (expand_head env) vars in
  let vars = List.map (expand_head env) vars in
  let vars' =
    List.filter
      (fun t ->
        let t = repr t in
        generalize t;
        match t.desc with
          Tvar name when t.level = generic_level ->
            log_type t; t.desc <- Tunivar name; true
        | _ -> false)
      vars in
  if List.length vars = List.length vars' then () else
  let ty = newgenty (Tpoly(repr exp.exp_type, vars'))
  and ty_expected = repr ty_expected in
  raise (Error (exp.exp_loc,
                Less_general(kind, [ty, ty; ty_expected, ty_expected])))

(* Check that a type is not a function *)
let check_application_result env statement exp =
  let loc = exp.exp_loc in
  match (expand_head env exp.exp_type).desc with
  | Tarrow _ ->
      Location.prerr_warning exp.exp_loc Warnings.Partial_application
  | Tvar _ -> ()
  | Tconstr (p, _, _) when Path.same p Predef.path_unit -> ()
  | _ ->
      if statement then
        Location.prerr_warning loc Warnings.Statement_type

(* Check that a type is generalizable at some level *)
let generalizable level ty =
  let rec check ty =
    let ty = repr ty in
    if ty.level < lowest_level then () else
    if ty.level <= level then raise Exit else
    (mark_type_node ty; iter_type_expr check ty)
  in
  try check ty; unmark_type ty; true
  with Exit -> unmark_type ty; false

(* Hack to allow coercion of self. Will clean-up later. *)
let self_coercion = ref ([] : (Path.t * Location.t list ref) list)

(* Helpers for packaged modules. *)
let create_package_type loc env (p, l) =
  let s = !Typetexp.transl_modtype_longident loc env p in
  newty (Tpackage (s,
                   List.map fst l,
                   List.map (Typetexp.transl_simple_type env false)
                     (List.map snd l)))

let wrap_unpacks sexp unpacks =
  List.fold_left
    (fun sexp (name, loc) ->
      {pexp_loc = sexp.pexp_loc; pexp_desc = Pexp_letmodule (
       name,
       {pmod_loc = loc; pmod_desc = Pmod_unpack
          {pexp_desc=Pexp_ident(Longident.Lident name); pexp_loc=loc}},
       sexp)})
    sexp unpacks

(* Helpers for type_cases *)
let iter_ppat f p = 
  match p.ppat_desc with
  | Ppat_any | Ppat_var _ | Ppat_constant _ 
  | Ppat_type _ | Ppat_unpack _ -> ()    
  | Ppat_array pats -> List.iter f pats
  | Ppat_or (p1,p2) -> f p1; f p2
  | Ppat_variant (_, arg) | Ppat_construct (_, arg, _) -> may f arg
  | Ppat_tuple lst ->  List.iter f lst
  | Ppat_alias (p,_) | Ppat_constraint (p,_) | Ppat_lazy p -> f p
  | Ppat_record (args, flag) -> List.iter (fun (_,p) -> f p) args

let contains_polymorphic_variant p =
  let rec loop p =
    match p.ppat_desc with
      Ppat_variant _ | Ppat_type _ -> raise Exit
    | _ -> iter_ppat loop p
  in
  try loop p; false with Exit -> true

let contains_gadt env p =
  let rec loop p =
    match p.ppat_desc with
      Ppat_construct (lid, _, _) ->
        begin try
          if (Env.lookup_constructor lid env).cstr_generalized then raise Exit
        with Not_found -> ()
        end; iter_ppat loop p
    | _ -> iter_ppat loop p
  in
  try loop p; false with Exit -> true

let dummy_expr = {pexp_desc = Pexp_tuple []; pexp_loc = Location.none}

(* Duplicate types of values in the environment *)
(* XXX Should we do something about global type variables too? *)

let duplicate_ident_types loc caselist env =
  let caselist =
    List.filter (fun (pat, _) -> contains_gadt env pat) caselist in
  let idents = all_idents (List.map snd caselist) in
  List.fold_left
    (fun env s ->
      try
        (* XXX This will mark the value as being used;
           I don't think this is what we want *)
        let (path, desc) = Env.lookup_value (Longident.Lident s) env in
        match path with
          Path.Pident id ->
            let desc = {desc with val_type = correct_levels desc.val_type} in
            Env.add_value id desc env
        | _ -> env
      with Not_found -> env)
    env idents

(* Typing of expressions *)

let unify_exp env exp expected_ty =
  (* Format.eprintf "@[%a@ %a@]@." Printtyp.raw_type_expr exp.exp_type
    Printtyp.raw_type_expr expected_ty; *)
    unify_exp_types exp.exp_loc env exp.exp_type expected_ty

let rec type_exp env sexp =
  (* We now delegate everything to type_expect *)
  type_expect env sexp (newvar ())

(* Typing of an expression with an expected type.
   This provide better error messages, and allows controlled
   propagation of return type information.
   In the principal case, [type_expected'] may be at generic_level.
 *)

and type_expect ?in_function env sexp ty_expected =
  let loc = sexp.pexp_loc in
  (* Record the expression type before unifying it with the expected type *)
  let rue exp =
    Stypes.record (Stypes.Ti_expr exp);
    unify_exp env exp (instance env ty_expected);
    exp
  in
  match sexp.pexp_desc with
  | Pexp_ident lid ->
      begin
        if !Clflags.annotations then begin
          try let (path, annot) = Env.lookup_annot lid env in
              Stypes.record
                (Stypes.An_ident (
                 loc, Path.name ~paren:Oprint.parenthesized_ident path, annot))
          with _ -> ()
        end;
        let (path, desc) = Typetexp.find_value env loc lid in
        rue {
          exp_desc =
            begin match desc.val_kind with
              Val_ivar (_, cl_num) ->
                let (self_path, _) =
                  Env.lookup_value (Longident.Lident ("self-" ^ cl_num)) env
                in
                Texp_instvar(self_path, path)
            | Val_self (_, _, cl_num, _) ->
                let (path, _) =
                  Env.lookup_value (Longident.Lident ("self-" ^ cl_num)) env
                in
                Texp_ident(path, desc)
            | Val_unbound ->
                raise(Error(loc, Masked_instance_variable lid))
            | _ ->
                Texp_ident(path, desc)
            end;
          exp_loc = loc;
          exp_type = instance env desc.val_type;
          exp_env = env }
      end
  | Pexp_constant(Const_string s as cst) ->
      rue {
        exp_desc = Texp_constant cst;
        exp_loc = loc;
        exp_type =
        (* Terrible hack for format strings *)
           begin match (repr (expand_head env ty_expected)).desc with
             Tconstr(path, _, _) when Path.same path Predef.path_format6 ->
               type_format loc s
           | _ -> instance_def Predef.type_string
           end;
        exp_env = env }
  | Pexp_constant cst ->
      rue {
        exp_desc = Texp_constant cst;
        exp_loc = loc;
        exp_type = type_constant cst;
        exp_env = env }
  | Pexp_let(Nonrecursive, [spat, sval], sbody) when contains_gadt env spat ->
      type_expect ?in_function env
        {sexp with pexp_desc = Pexp_match (sval, [spat, sbody])}
        ty_expected
  | Pexp_let(rec_flag, spat_sexp_list, sbody) ->
      let scp =
        match rec_flag with
        | Recursive -> Some (Annot.Idef loc)
        | Nonrecursive -> Some (Annot.Idef sbody.pexp_loc)
        | Default -> None
      in
      let (pat_exp_list, new_env, unpacks) =
        type_let env rec_flag spat_sexp_list scp true in
      let body =
        type_expect new_env (wrap_unpacks sbody unpacks) ty_expected in
      re {
        exp_desc = Texp_let(rec_flag, pat_exp_list, body);
        exp_loc = loc;
        exp_type = body.exp_type;
        exp_env = env }
  | Pexp_function (l, Some default, [spat, sbody]) ->
      let default_loc = default.pexp_loc in
      let scases = [
         {ppat_loc = default_loc;
          ppat_desc =
            Ppat_construct
              (Longident.(Ldot (Lident "*predef*", "Some")),
               Some {ppat_loc = default_loc; ppat_desc = Ppat_var "*sth*"},
               false)},
         {pexp_loc = default_loc;
          pexp_desc = Pexp_ident(Longident.Lident "*sth*")};
         {ppat_loc = default_loc;
          ppat_desc = Ppat_construct
            (Longident.(Ldot (Lident "*predef*", "None")), None, false)},
         default;
      ] in
      let smatch = {
        pexp_loc = loc;
        pexp_desc =
          Pexp_match ({
            pexp_loc = loc;
            pexp_desc = Pexp_ident(Longident.Lident "*opt*")
            },
            scases
          )
      } in
      let sfun = {
        pexp_loc = loc;
        pexp_desc =
         Pexp_function (
           l, None,
           [ {ppat_loc = loc;
              ppat_desc = Ppat_var "*opt*"},
             {pexp_loc = loc;
              pexp_desc = Pexp_let(Default, [spat, smatch], sbody);
             }
           ]
         )
      } in
      type_expect ?in_function env sfun ty_expected
  | Pexp_function (l, _, caselist) ->
      let (loc_fun, ty_fun) =
        match in_function with Some p -> p
        | None -> (loc, instance env ty_expected)
      in
      let separate = !Clflags.principal || Env.has_local_constraints env in
      if separate then begin_def ();
      let (ty_arg, ty_res) =
        try filter_arrow env (instance env ty_expected) l
        with Unify _ ->
          match expand_head env ty_expected with
            {desc = Tarrow _} as ty ->
              raise(Error(loc, Abstract_wrong_label(l, ty)))
          | _ ->
              raise(Error(loc_fun,
                          Too_many_arguments (in_function <> None, ty_fun)))
      in
      let ty_arg =
        if is_optional l then
          let tv = newvar() in
          begin
            try unify env ty_arg (type_option tv)
            with Unify _ -> assert false
          end;
          type_option tv
        else ty_arg
      in
      if separate then begin
        end_def ();
        generalize_structure ty_arg;
        generalize_structure ty_res
      end;
      let cases, partial =
        type_cases ~in_function:(loc_fun,ty_fun) env ty_arg ty_res
          true loc caselist in
      let not_function ty =
        let ls, tvar = list_labels env ty in
        ls = [] && not tvar
      in
      if is_optional l && not_function ty_res then
        Location.prerr_warning (fst (List.hd cases)).pat_loc
          Warnings.Unerasable_optional_argument;
      re {
        exp_desc = Texp_function(cases, partial);
        exp_loc = loc;
        exp_type = instance env (newgenty (Tarrow(l, ty_arg, ty_res, Cok)));
        exp_env = env }
  | Pexp_apply(sfunct, sargs) ->
      begin_def (); (* one more level for non-returning functions *)
      if !Clflags.principal then begin_def ();
      let funct = type_exp env sfunct in
      if !Clflags.principal then begin
        end_def ();
        generalize_structure funct.exp_type
      end;
      let rec lower_args seen ty_fun =
        let ty = expand_head env ty_fun in
        if List.memq ty seen then () else
        match ty.desc with
          Tarrow (l, ty_arg, ty_fun, com) ->
            (try unify_var env (newvar()) ty_arg with Unify _ -> assert false);
            lower_args (ty::seen) ty_fun
        | _ -> ()
      in
      let ty = instance env funct.exp_type in
      end_def ();
      lower_args [] ty;
      begin_def ();
      let (args, ty_res) = type_application env funct sargs in
      end_def ();
      unify_var env (newvar()) funct.exp_type;
      rue {
        exp_desc = Texp_apply(funct, args);
        exp_loc = loc;
        exp_type = ty_res;
        exp_env = env }
  | Pexp_match(sarg, caselist) ->
      begin_def ();
      let arg = type_exp env sarg in
      end_def ();
      if is_nonexpansive arg then generalize arg.exp_type
      else generalize_expansive env arg.exp_type;
      let cases, partial =
        type_cases env arg.exp_type ty_expected true loc caselist
      in
      re {
        exp_desc = Texp_match(arg, cases, partial);
        exp_loc = loc;
        exp_type = instance env ty_expected;
        exp_env = env }
  | Pexp_try(sbody, caselist) ->
      let body = type_expect env sbody ty_expected in
      let cases, _ =
        type_cases env Predef.type_exn ty_expected false loc caselist in
      re {
        exp_desc = Texp_try(body, cases);
        exp_loc = loc;
        exp_type = body.exp_type;
        exp_env = env }
  | Pexp_tuple sexpl ->
      let subtypes = List.map (fun _ -> newgenvar ()) sexpl in
      let to_unify = newgenty (Ttuple subtypes) in
      unify_exp_types loc env to_unify ty_expected;
      let expl =
        List.map2 (fun body ty -> type_expect env body ty) sexpl subtypes
      in
      re {
        exp_desc = Texp_tuple expl;
        exp_loc = loc;
        (* Keep sharing *)
        exp_type = newty (Ttuple (List.map (fun e -> e.exp_type) expl));
        exp_env = env }
  | Pexp_construct(lid, sarg, explicit_arity) ->
      type_construct env loc lid sarg explicit_arity ty_expected
  | Pexp_variant(l, sarg) ->
      (* Keep sharing *)
      let ty_expected0 = instance env ty_expected in
      begin try match
        sarg, expand_head env ty_expected, expand_head env ty_expected0 with
      | Some sarg, {desc = Tvariant row}, {desc = Tvariant row0} ->
          let row = row_repr row in
          begin match row_field_repr (List.assoc l row.row_fields),
          row_field_repr (List.assoc l row0.row_fields) with
            Rpresent (Some ty), Rpresent (Some ty0) ->
              let arg = type_argument env sarg ty ty0 in
              re { exp_desc = Texp_variant(l, Some arg);
                   exp_loc = loc;
                   exp_type = ty_expected0;
                   exp_env = env }
          | _ -> raise Not_found
          end
      | _ -> raise Not_found
      with Not_found ->
        let arg = may_map (type_exp env) sarg in
        let arg_type = may_map (fun arg -> arg.exp_type) arg in
        rue {
          exp_desc = Texp_variant(l, arg);
          exp_loc = loc;
          exp_type= newty (Tvariant{row_fields = [l, Rpresent arg_type];
                                    row_more = newvar ();
                                    row_bound = ();
                                    row_closed = false;
                                    row_fixed = false;
                                    row_name = None});
          exp_env = env }
      end
  | Pexp_record(lid_sexp_list, opt_sexp) ->
      let lbl_exp_list =
        type_label_a_list env loc (type_label_exp true env loc ty_expected)
          lid_sexp_list in
      let rec check_duplicates seen_pos lid_sexp lbl_exp =
        match (lid_sexp, lbl_exp) with
          ((lid, _) :: rem1, (lbl, _) :: rem2) ->
            if List.mem lbl.lbl_pos seen_pos
            then raise(Error(loc, Label_multiply_defined lid))
            else check_duplicates (lbl.lbl_pos :: seen_pos) rem1 rem2
        | (_, _) -> () in
      check_duplicates [] lid_sexp_list lbl_exp_list;
      let opt_exp =
        match opt_sexp, lbl_exp_list with
          None, _ -> None
        | Some sexp, (lbl, _) :: _ ->
            if !Clflags.principal then begin_def ();
            let ty_exp = newvar () in
            let unify_kept lbl =
              if List.for_all (fun (lbl',_) -> lbl'.lbl_pos <> lbl.lbl_pos)
                  lbl_exp_list
              then begin
                let _, ty_arg1, ty_res1 = instance_label false lbl
                and _, ty_arg2, ty_res2 = instance_label false lbl in
                unify env ty_exp ty_res1;
                unify env (instance env ty_expected) ty_res2;
                unify env ty_arg1 ty_arg2
              end in
            Array.iter unify_kept lbl.lbl_all;
            if !Clflags.principal then begin
              end_def ();
              generalize_structure ty_exp
            end;
            Some(type_expect env sexp ty_exp)
        | _ -> assert false
      in
      let num_fields =
        match lbl_exp_list with [] -> assert false
        | (lbl,_)::_ -> Array.length lbl.lbl_all in
      if opt_sexp = None && List.length lid_sexp_list <> num_fields then begin
        let present_indices =
          List.map (fun (lbl, _) -> lbl.lbl_pos) lbl_exp_list in
        let label_names = extract_label_names sexp env ty_expected in
        let rec missing_labels n = function
            [] -> []
          | lbl :: rem ->
              if List.mem n present_indices then missing_labels (n + 1) rem
              else lbl :: missing_labels (n + 1) rem
        in
        let missing = missing_labels 0 label_names in
        raise(Error(loc, Label_missing missing))
      end
      else if opt_sexp <> None && List.length lid_sexp_list = num_fields then
        Location.prerr_warning loc Warnings.Useless_record_with;
      re {
        exp_desc = Texp_record(lbl_exp_list, opt_exp);
        exp_loc = loc;
        exp_type = instance env ty_expected;
        exp_env = env }
  | Pexp_field(sarg, lid) ->
      let arg = type_exp env sarg in
      let label = Typetexp.find_label env loc lid in
      let (_, ty_arg, ty_res) = instance_label false label in
      unify_exp env arg ty_res;
      rue {
        exp_desc = Texp_field(arg, label);
        exp_loc = loc;
        exp_type = ty_arg;
        exp_env = env }
  | Pexp_setfield(srecord, lid, snewval) ->
      let record = type_exp env srecord in
      let label = Typetexp.find_label env loc lid in
      let (label, newval) =
        type_label_exp false env loc record.exp_type (label, snewval) in
      if label.lbl_mut = Immutable then
        raise(Error(loc, Label_not_mutable lid));
      rue {
        exp_desc = Texp_setfield(record, label, newval);
        exp_loc = loc;
        exp_type = instance_def Predef.type_unit;
        exp_env = env }
  | Pexp_array(sargl) ->
      let ty = newgenvar() in
      let to_unify = Predef.type_array ty in
      unify_exp_types loc env to_unify ty_expected;
      let argl = List.map (fun sarg -> type_expect env sarg ty) sargl in
      re {
        exp_desc = Texp_array argl;
        exp_loc = loc;
        exp_type = instance env ty_expected;
        exp_env = env }
  | Pexp_ifthenelse(scond, sifso, sifnot) ->
      let cond = type_expect env scond Predef.type_bool in
      begin match sifnot with
        None ->
          let ifso = type_expect env sifso Predef.type_unit in
          rue {
            exp_desc = Texp_ifthenelse(cond, ifso, None);
            exp_loc = loc;
            exp_type = ifso.exp_type;
            exp_env = env }
      | Some sifnot ->
          let ifso = type_expect env sifso ty_expected in
          let ifnot = type_expect env sifnot ty_expected in
          (* Keep sharing *)
          unify_exp env ifnot ifso.exp_type;
          re {
            exp_desc = Texp_ifthenelse(cond, ifso, Some ifnot);
            exp_loc = loc;
            exp_type = ifso.exp_type;
            exp_env = env }
      end
  | Pexp_sequence(sexp1, sexp2) ->
      let exp1 = type_statement env sexp1 in
      let exp2 = type_expect env sexp2 ty_expected in
      re {
        exp_desc = Texp_sequence(exp1, exp2);
        exp_loc = loc;
        exp_type = exp2.exp_type;
        exp_env = env }
  | Pexp_while(scond, sbody) ->
      let cond = type_expect env scond Predef.type_bool in
      let body = type_statement env sbody in
      rue {
        exp_desc = Texp_while(cond, body);
        exp_loc = loc;
        exp_type = instance_def Predef.type_unit;
        exp_env = env }
  | Pexp_for(param, slow, shigh, dir, sbody) ->
      let low = type_expect env slow Predef.type_int in
      let high = type_expect env shigh Predef.type_int in
      let (id, new_env) =
        Env.enter_value param {val_type = instance_def Predef.type_int;
                               val_kind = Val_reg;
                               val_loc = loc;
                              } env
          ~check:(fun s -> Warnings.Unused_for_index s)
      in
      let body = type_statement new_env sbody in
      rue {
        exp_desc = Texp_for(id, low, high, dir, body);
        exp_loc = loc;
        exp_type = instance_def Predef.type_unit;
        exp_env = env }
  | Pexp_constraint(sarg, sty, sty') ->
      let separate = true (* always separate, 1% slowdown for lablgtk *)
        (* !Clflags.principal || Env.has_local_constraints env *) in
      let (arg, ty') =
        match (sty, sty') with
          (None, None) ->               (* Case actually unused *)
            let arg = type_exp env sarg in
            (arg, arg.exp_type)
        | (Some sty, None) ->
            if separate then begin_def ();
            let ty = Typetexp.transl_simple_type env false sty in
            if separate then begin
              end_def ();
              generalize_structure ty;
              (type_argument env sarg ty (instance env ty), instance env ty)
            end else
              (type_argument env sarg ty ty, ty)
        | (None, Some sty') ->
            let (ty', force) =
              Typetexp.transl_simple_type_delayed env sty'
            in
            if separate then begin_def ();
            let arg = type_exp env sarg in
            let gen =
              if separate then begin
                end_def ();
                let tv = newvar () in
                let gen = generalizable tv.level arg.exp_type in
                unify_var env tv arg.exp_type;
                gen
              end else true
            in
            begin match arg.exp_desc, !self_coercion, (repr ty').desc with
              Texp_ident(_, {val_kind=Val_self _}), (path,r) :: _,
              Tconstr(path',_,_) when Path.same path path' ->
                (* prerr_endline "self coercion"; *)
                r := loc :: !r;
                force ()
            | _ when free_variables ~env arg.exp_type = []
                  && free_variables ~env ty' = [] ->
                if not gen && (* first try a single coercion *)
                  let snap = snapshot () in
                  let ty, b = enlarge_type env ty' in
                  try
                    force (); Ctype.unify env arg.exp_type ty; true
                  with Unify _ ->
                    backtrack snap; false
                then ()
                else begin try
                  let force' = subtype env arg.exp_type ty' in
                  force (); force' ();
                  if not gen then
                    Location.prerr_warning loc
                      (Warnings.Not_principal "this ground coercion");
                with Subtype (tr1, tr2) ->
                  (* prerr_endline "coercion failed"; *)
                  raise(Error(loc, Not_subtype(tr1, tr2)))
                end;
            | _ ->
                let ty, b = enlarge_type env ty' in
                force ();
                begin try Ctype.unify env arg.exp_type ty with Unify trace ->
                  raise(Error(sarg.pexp_loc,
                        Coercion_failure(ty', full_expand env ty', trace, b)))
                end
            end;
            (arg, ty')
        | (Some sty, Some sty') ->
            if separate then begin_def ();
            let (ty, force) =
              Typetexp.transl_simple_type_delayed env sty
            and (ty', force') =
              Typetexp.transl_simple_type_delayed env sty'
            in
            begin try
              let force'' = subtype env ty ty' in
              force (); force' (); force'' ()
            with Subtype (tr1, tr2) ->
              raise(Error(loc, Not_subtype(tr1, tr2)))
            end;
            if separate then begin
              end_def ();
              generalize_structure ty;
              generalize_structure ty';
              (type_argument env sarg ty (instance env ty), instance env ty')
            end else
              (type_argument env sarg ty ty, ty')
      in
      rue {
        exp_desc = arg.exp_desc;
        exp_loc = arg.exp_loc;
        exp_type = ty';
        exp_env = env }
  | Pexp_when(scond, sbody) ->
      let cond = type_expect env scond Predef.type_bool in
      let body = type_expect env sbody ty_expected in
      re {
        exp_desc = Texp_when(cond, body);
        exp_loc = loc;
        exp_type = body.exp_type;
        exp_env = env }
  | Pexp_send (e, met) ->
      if !Clflags.principal then begin_def ();
      let obj = type_exp env e in
      begin try
        let (exp, typ) =
          match obj.exp_desc with
            Texp_ident(path, {val_kind = Val_self (meths, _, _, privty)}) ->
              let (id, typ) =
                filter_self_method env met Private meths privty
              in
              if is_Tvar (repr typ) then
                Location.prerr_warning loc
                  (Warnings.Undeclared_virtual_method met);
              (Texp_send(obj, Tmeth_val id), typ)
          | Texp_ident(path, {val_kind = Val_anc (methods, cl_num)}) ->
              let method_id =
                begin try List.assoc met methods with Not_found ->
                  raise(Error(e.pexp_loc, Undefined_inherited_method met))
                end
              in
              begin match
                Env.lookup_value (Longident.Lident ("selfpat-" ^ cl_num)) env,
                Env.lookup_value (Longident.Lident ("self-" ^cl_num)) env
              with
                (_, ({val_kind = Val_self (meths, _, _, privty)} as desc)),
                (path, _) ->
                  let (_, typ) =
                    filter_self_method env met Private meths privty
                  in
                  let method_type = newvar () in
                  let (obj_ty, res_ty) = filter_arrow env method_type "" in
                  unify env obj_ty desc.val_type;
                  unify env res_ty (instance env typ);
                  (Texp_apply({ exp_desc = Texp_ident(Path.Pident method_id,
                                                     {val_type = method_type;
                                                      val_kind = Val_reg;
                                                      val_loc = Location.none;
                                                     });
                                exp_loc = loc;
                                exp_type = method_type;
                                exp_env = env },
                              [Some {exp_desc = Texp_ident(path, desc);
                                     exp_loc = obj.exp_loc;
                                     exp_type = desc.val_type;
                                     exp_env = env },
                               Required]),
                   typ)
              |  _ ->
                  assert false
              end
          | _ ->
              (Texp_send(obj, Tmeth_name met),
               filter_method env met Public obj.exp_type)
        in
        if !Clflags.principal then begin
          end_def ();
          generalize_structure typ;
        end;
        let typ =
          match repr typ with
            {desc = Tpoly (ty, [])} ->
              instance env ty
          | {desc = Tpoly (ty, tl); level = l} ->
              if !Clflags.principal && l <> generic_level then
                Location.prerr_warning loc
                  (Warnings.Not_principal "this use of a polymorphic method");
              snd (instance_poly false tl ty)
          | {desc = Tvar _} as ty ->
              let ty' = newvar () in
              unify env (instance_def ty) (newty(Tpoly(ty',[])));
              (* if not !Clflags.nolabels then
                 Location.prerr_warning loc (Warnings.Unknown_method met); *)
              ty'
          | _ ->
              assert false
        in
        rue {
          exp_desc = exp;
          exp_loc = loc;
          exp_type = typ;
          exp_env = env }
      with Unify _ ->
        raise(Error(e.pexp_loc, Undefined_method (obj.exp_type, met)))
      end
  | Pexp_new cl ->
      let (cl_path, cl_decl) = Typetexp.find_class env loc cl in
        begin match cl_decl.cty_new with
          None ->
            raise(Error(loc, Virtual_class cl))
        | Some ty ->
            rue {
              exp_desc = Texp_new (cl_path, cl_decl);
              exp_loc = loc;
              exp_type = instance_def ty;
              exp_env = env }
        end
  | Pexp_setinstvar (lab, snewval) ->
      begin try
        let (path, desc) = Env.lookup_value (Longident.Lident lab) env in
        match desc.val_kind with
          Val_ivar (Mutable, cl_num) ->
            let newval = type_expect env snewval (instance env desc.val_type) in
            let (path_self, _) =
              Env.lookup_value (Longident.Lident ("self-" ^ cl_num)) env
            in
            rue {
              exp_desc = Texp_setinstvar(path_self, path, newval);
              exp_loc = loc;
              exp_type = instance_def Predef.type_unit;
              exp_env = env }
        | Val_ivar _ ->
            raise(Error(loc,Instance_variable_not_mutable(true,lab)))
        | _ ->
            raise(Error(loc,Instance_variable_not_mutable(false,lab)))
      with
        Not_found ->
          raise(Error(loc, Unbound_instance_variable lab))
      end
  | Pexp_override lst ->
      let _ =
       List.fold_right
        (fun (lab, _) l ->
           if List.exists ((=) lab) l then
             raise(Error(loc,
                         Value_multiply_overridden lab));
           lab::l)
        lst
        [] in
      begin match
        try
          Env.lookup_value (Longident.Lident "selfpat-*") env,
          Env.lookup_value (Longident.Lident "self-*") env
        with Not_found ->
          raise(Error(loc, Outside_class))
      with
        (_, {val_type = self_ty; val_kind = Val_self (_, vars, _, _)}),
        (path_self, _) ->
          let type_override (lab, snewval) =
            begin try
              let (id, _, _, ty) = Vars.find lab !vars in
              (Path.Pident id, type_expect env snewval (instance env ty))
            with
              Not_found ->
                raise(Error(loc, Unbound_instance_variable lab))
            end
          in
          let modifs = List.map type_override lst in
          rue {
            exp_desc = Texp_override(path_self, modifs);
            exp_loc = loc;
            exp_type = self_ty;
            exp_env = env }
      | _ ->
          assert false
      end
  | Pexp_letmodule(name, smodl, sbody) ->
      let ty = newvar() in
      (* remember original level *)
      begin_def ();
      Ident.set_current_time ty.level;
      let context = Typetexp.narrow () in
      let modl = !type_module env smodl in
      let (id, new_env) = Env.enter_module name modl.mod_type env in
      Ctype.init_def(Ident.current_time());
      Typetexp.widen context;
      let body = type_expect new_env sbody ty_expected in
      (* go back to original level *)
      end_def ();
      (* Unification of body.exp_type with the fresh variable ty
         fails if and only if the prefix condition is violated,
         i.e. if generative types rooted at id show up in the
         type body.exp_type.  Thus, this unification enforces the
         scoping condition on "let module". *)
      begin try
        Ctype.unify_var new_env ty body.exp_type
      with Unify _ ->
        raise(Error(loc, Scoping_let_module(name, body.exp_type)))
      end;
      re {
        exp_desc = Texp_letmodule(id, modl, body);
        exp_loc = loc;
        exp_type = ty;
        exp_env = env }
  | Pexp_assert (e) ->
      let cond = type_expect env e Predef.type_bool in
      rue {
        exp_desc = Texp_assert (cond);
        exp_loc = loc;
        exp_type = instance_def Predef.type_unit;
        exp_env = env;
      }
  | Pexp_assertfalse ->
      re {
        exp_desc = Texp_assertfalse;
        exp_loc = loc;
        exp_type = instance env ty_expected;
        exp_env = env;
      }
  | Pexp_lazy e ->
      let ty = newgenvar () in
      let to_unify = Predef.type_lazy_t ty in
      unify_exp_types loc env to_unify ty_expected;
      let arg = type_expect env e ty in
      re {
        exp_desc = Texp_lazy arg;
        exp_loc = loc;
        exp_type = instance env ty_expected;
        exp_env = env;
      }
  | Pexp_object s ->
      let desc, sign, meths = !type_object env loc s in
      rue {
        exp_desc = Texp_object (desc, sign, meths);
        exp_loc = loc;
        exp_type = sign.cty_self;
        exp_env = env;
      }
  | Pexp_poly(sbody, sty) ->
      if !Clflags.principal then begin_def ();
      let ty =
        match sty with None -> repr ty_expected
        | Some sty ->
            let ty = Typetexp.transl_simple_type env false sty in
            repr ty
      in
      if !Clflags.principal then begin
        end_def ();
        generalize_structure ty
      end;
      if sty <> None then
        unify_exp_types loc env (instance env ty) (instance env ty_expected);
      begin
        match (expand_head env ty).desc with
          Tpoly (ty', []) ->
            let exp = type_expect env sbody ty' in
            re { exp with exp_type = instance env ty }
        | Tpoly (ty', tl) ->
            (* One more level to generalize locally *)
            begin_def ();
            if !Clflags.principal then begin_def ();
            let vars, ty'' = instance_poly true tl ty' in
            if !Clflags.principal then begin
              end_def ();
              generalize_structure ty''
            end;
            let exp = type_expect env sbody ty'' in
            end_def ();
            check_univars env false "method" exp ty_expected vars;
            re { exp with exp_type = instance env ty }
        | Tvar _ ->
            let exp = type_exp env sbody in
            let exp = {exp with exp_type = newty (Tpoly (exp.exp_type, []))} in
            unify_exp env exp ty;
            re exp
        | _ -> assert false
      end
  | Pexp_newtype(name, sbody) ->
      (* Create a fake abstract type declaration for name. *)
      let level = get_current_level () in
      let decl = {
        type_params = [];
        type_arity = 0;
        type_kind = Type_abstract;
        type_private = Public;
        type_manifest = None;
        type_variance = [];
        type_newtype_level = Some (level, level);
        type_loc = loc;
      }
      in
      let ty = newvar () in
      (* remember original level *)
      begin_def ();
      Ident.set_current_time ty.level;
      let (id, new_env) = Env.enter_type name decl env in
      Ctype.init_def(Ident.current_time());

      let body = type_exp new_env sbody in
      (* Replace every instance of this type constructor in the resulting
         type. *)
      let seen = Hashtbl.create 8 in
      let rec replace t =
        if Hashtbl.mem seen t.id then ()
        else begin
          Hashtbl.add seen t.id ();
          match t.desc with
          | Tconstr (Path.Pident id', _, _) when id == id' -> link_type t ty
          | _ -> Btype.iter_type_expr replace t
        end
      in
      let ety = Subst.type_expr Subst.identity body.exp_type in
      replace ety;
      (* back to original level *)
      end_def ();
      (* lower the levels of the result type *)
      (* unify_var env ty ety; *)

      (* non-expansive if the body is non-expansive, so we don't introduce
         any new extra node in the typed AST. *)
      rue { body with exp_loc = sexp.pexp_loc; exp_type = ety }
  | Pexp_pack m ->
      let (p, nl, tl) =
        match Ctype.expand_head env (instance env ty_expected) with
          {desc = Tpackage (p, nl, tl)} ->
            if !Clflags.principal &&
              (Ctype.expand_head env ty_expected).level < Btype.generic_level
            then
              Location.prerr_warning loc
                (Warnings.Not_principal "this module packing");
            (p, nl, tl)
        | {desc = Tvar _} ->
            raise (Error (loc, Cannot_infer_signature))
        | _ ->
            raise (Error (loc, Not_a_packed_module ty_expected))
      in
      let (modl, tl') = !type_package env m p nl tl in
      rue {
        exp_desc = Texp_pack modl;
        exp_loc = loc;
        exp_type = newty (Tpackage (p, nl, tl'));
        exp_env = env }
  | Pexp_open (lid, e) ->
      type_expect (!type_open env sexp.pexp_loc lid) e ty_expected

and type_label_exp create env loc ty_expected (label, sarg) =
  (* Here also ty_expected may be at generic_level *)
  begin_def ();
  let separate = !Clflags.principal || Env.has_local_constraints env in
  if separate then (begin_def (); begin_def ());
  let (vars, ty_arg, ty_res) = instance_label true label in
  if separate then begin
    end_def ();
    (* Generalize label information *)
    generalize_structure ty_arg;
    generalize_structure ty_res
  end;
  begin try
    unify env (instance_def ty_res) (instance env ty_expected)
  with Unify trace ->
    raise(Error(loc , Label_mismatch(lid_of_label label, trace)))
  end;
  (* Instantiate so that we can generalize internal nodes *)
  let ty_arg = instance_def ty_arg in
  if separate then begin
    end_def ();
    (* Generalize information merged from ty_expected *)
    generalize_structure ty_arg
  end;
  if label.lbl_private = Private then
    raise(Error(loc, if create then Private_type ty_expected
                     else Private_label (lid_of_label label, ty_expected)));
  let arg =
    let snap = if vars = [] then None else Some (Btype.snapshot ()) in
    let arg = type_argument env sarg ty_arg (instance env ty_arg) in
    end_def ();
    try
      check_univars env (vars <> []) "field value" arg label.lbl_arg vars;
      arg
    with exn when not (is_nonexpansive arg) -> try
      (* Try to retype without propagating ty_arg, cf PR#4862 *)
      may Btype.backtrack snap;
      begin_def ();
      let arg = type_exp env sarg in
      end_def ();
      generalize_expansive env arg.exp_type;
      unify_exp env arg ty_arg;
      check_univars env false "field value" arg label.lbl_arg vars;
      arg
    with Error (_, Less_general _) as e -> raise e
    | _ -> raise exn    (* In case of failure return the first error *)
  in
  (label, {arg with exp_type = instance env arg.exp_type})

and type_argument env sarg ty_expected' ty_expected =
  (* ty_expected' may be generic *)
  let no_labels ty =
    let ls, tvar = list_labels env ty in
    not tvar && List.for_all ((=) "") ls
  in
  let rec is_inferred sexp =
    match sexp.pexp_desc with
      Pexp_ident _ | Pexp_apply _ | Pexp_send _ | Pexp_field _ -> true
    | Pexp_open (_, e) -> is_inferred e
    | _ -> false
  in
  match expand_head env ty_expected' with
    {desc = Tarrow("",ty_arg,ty_res,_); level = lv} when is_inferred sarg ->
      (* apply optional arguments when expected type is "" *)
      (* we must be very careful about not breaking the semantics *)
      if !Clflags.principal then begin_def ();
      let texp = type_exp env sarg in
      if !Clflags.principal then begin
        end_def ();
        generalize_structure texp.exp_type
      end;
      let rec make_args args ty_fun =
        match (expand_head env ty_fun).desc with
        | Tarrow (l,ty_arg,ty_fun,_) when is_optional l ->
            make_args
              ((Some(option_none (instance env ty_arg) sarg.pexp_loc), Optional)
               :: args)
              ty_fun
        | Tarrow (l,_,ty_res',_) when l = "" || !Clflags.classic ->
            args, ty_fun, no_labels ty_res'
        | Tvar _ ->  args, ty_fun, false
        |  _ -> [], texp.exp_type, false
      in
      let args, ty_fun', simple_res = make_args [] texp.exp_type in
      let warn = !Clflags.principal &&
        (lv <> generic_level || (repr ty_fun').level <> generic_level)
      and texp = {texp with exp_type = instance env texp.exp_type}
      and ty_fun = instance env ty_fun' in
      if not (simple_res || no_labels ty_res) then begin
        unify_exp env texp ty_expected;
        texp
      end else begin
      unify_exp env {texp with exp_type = ty_fun} ty_expected;
      if args = [] then texp else
      (* eta-expand to avoid side effects *)
      let var_pair name ty =
        let id = Ident.create name in
        {pat_desc = Tpat_var id; pat_type = ty;
         pat_loc = Location.none; pat_env = env},
        {exp_type = ty; exp_loc = Location.none; exp_env = env; exp_desc =
         Texp_ident(Path.Pident id, {val_type = ty; val_kind = Val_reg;
                                     val_loc = Location.none})}
      in
      let eta_pat, eta_var = var_pair "eta" ty_arg in
      let func texp =
        { texp with exp_type = ty_fun; exp_desc =
          Texp_function([eta_pat, {texp with exp_type = ty_res; exp_desc =
                                   Texp_apply (texp, args@
                                               [Some eta_var, Required])}],
                        Total) } in
      if warn then Location.prerr_warning texp.exp_loc
          (Warnings.Without_principality "eliminated optional argument");
      if is_nonexpansive texp then func texp else
      (* let-expand to have side effects *)
      let let_pat, let_var = var_pair "let" texp.exp_type in
      re { texp with exp_type = ty_fun; exp_desc =
           Texp_let (Nonrecursive, [let_pat, texp], func let_var) }
      end
  | _ ->
      let texp = type_expect env sarg ty_expected' in
      unify_exp env texp ty_expected;
      texp

and type_application env funct sargs =
  (* funct.exp_type may be generic *)
  let result_type omitted ty_fun =
    List.fold_left
      (fun ty_fun (l,ty,lv) -> newty2 lv (Tarrow(l,ty,ty_fun,Cok)))
      ty_fun omitted
  in
  let has_label l ty_fun =
    let ls, tvar = list_labels env ty_fun in
    tvar || List.mem l ls
  in
  let ignored = ref [] in
  let rec type_unknown_args args omitted ty_fun = function
      [] ->
        (List.map
           (function None, x -> None, x | Some f, x -> Some (f ()), x)
           (List.rev args),
         instance env (result_type omitted ty_fun))
    | (l1, sarg1) :: sargl ->
        let (ty1, ty2) =
          let ty_fun = expand_head env ty_fun in
          match ty_fun.desc with
            Tvar _ ->
              let t1 = newvar () and t2 = newvar () in
              let not_identity = function
                  Texp_ident(_,{val_kind=Val_prim
                                  {Primitive.prim_name="%identity"}}) ->
                    false
                | _ -> true
              in
              if ty_fun.level >= t1.level && not_identity funct.exp_desc then
                Location.prerr_warning sarg1.pexp_loc Warnings.Unused_argument;
              unify env ty_fun (newty (Tarrow(l1,t1,t2,Clink(ref Cunknown))));
              (t1, t2)
          | Tarrow (l,t1,t2,_) when l = l1
            || !Clflags.classic && l1 = "" && not (is_optional l) ->
              (t1, t2)
          | td ->
              let ty_fun =
                match td with Tarrow _ -> newty td | _ -> ty_fun in
              let ty_res = result_type (omitted @ !ignored) ty_fun in
              match ty_res.desc with
                Tarrow _ ->
                  if (!Clflags.classic || not (has_label l1 ty_fun)) then
                    raise(Error(sarg1.pexp_loc, Apply_wrong_label(l1, ty_res)))
                  else
                    raise(Error(funct.exp_loc, Incoherent_label_order))
              | _ ->
                  raise(Error(funct.exp_loc, Apply_non_function
                                (expand_head env funct.exp_type)))
        in
        let optional = if is_optional l1 then Optional else Required in
        let arg1 () =
          let arg1 = type_expect env sarg1 ty1 in
          if optional = Optional then
            unify_exp env arg1 (type_option(newvar()));
          arg1
        in
        type_unknown_args ((Some arg1, optional) :: args) omitted ty2 sargl
  in
  let ignore_labels =
    !Clflags.classic ||
    begin
      let ls, tvar = list_labels env funct.exp_type in
      not tvar &&
      let labels = List.filter (fun l -> not (is_optional l)) ls in
      List.length labels = List.length sargs &&
      List.for_all (fun (l,_) -> l = "") sargs &&
      List.exists (fun l -> l <> "") labels &&
      (Location.prerr_warning funct.exp_loc Warnings.Labels_omitted;
       true)
    end
  in
  let warned = ref false in
  let rec type_args args omitted ty_fun ty_fun0 ty_old sargs more_sargs =
    match expand_head env ty_fun, expand_head env ty_fun0 with
      {desc=Tarrow (l, ty, ty_fun, com); level=lv} as ty_fun',
      {desc=Tarrow (_, ty0, ty_fun0, _)}
      when (sargs <> [] || more_sargs <> []) && commu_repr com = Cok ->
        let may_warn loc w =
          if not !warned && !Clflags.principal && lv <> generic_level
          then begin
            warned := true;
            Location.prerr_warning loc w
          end
        in
        let name = label_name l
        and optional = if is_optional l then Optional else Required in
        let sargs, more_sargs, arg =
          if ignore_labels && not (is_optional l) then begin
            (* In classic mode, omitted = [] *)
            match sargs, more_sargs with
              (l', sarg0) :: _, _ ->
                raise(Error(sarg0.pexp_loc, Apply_wrong_label(l', ty_old)))
            | _, (l', sarg0) :: more_sargs ->
                if l <> l' && l' <> "" then
                  raise(Error(sarg0.pexp_loc, Apply_wrong_label(l', ty_fun')))
                else
                  ([], more_sargs,
                   Some (fun () -> type_argument env sarg0 ty ty0))
            | _ ->
                assert false
          end else try
            let (l', sarg0, sargs, more_sargs) =
              try
                let (l', sarg0, sargs1, sargs2) = extract_label name sargs in
                if sargs1 <> [] then
                  may_warn sarg0.pexp_loc
                    (Warnings.Not_principal "commuting this argument");
                (l', sarg0, sargs1 @ sargs2, more_sargs)
              with Not_found ->
                let (l', sarg0, sargs1, sargs2) =
                  extract_label name more_sargs in
                if sargs1 <> [] || sargs <> [] then
                  may_warn sarg0.pexp_loc
                    (Warnings.Not_principal "commuting this argument");
                (l', sarg0, sargs @ sargs1, sargs2)
            in
            sargs, more_sargs,
            if optional = Required || is_optional l' then
              Some (fun () -> type_argument env sarg0 ty ty0)
            else begin
              may_warn sarg0.pexp_loc
                (Warnings.Not_principal "using an optional argument here");
              Some (fun () -> option_some (type_argument env sarg0
                                             (extract_option_type env ty)
                                             (extract_option_type env ty0)))
            end
          with Not_found ->
            sargs, more_sargs,
            if optional = Optional &&
              (List.mem_assoc "" sargs || List.mem_assoc "" more_sargs)
            then begin
              may_warn funct.exp_loc
                (Warnings.Without_principality "eliminated optional argument");
              ignored := (l,ty,lv) :: !ignored;
              Some (fun () -> option_none (instance env ty) Location.none)
            end else begin
              may_warn funct.exp_loc
                (Warnings.Without_principality "commuted an argument");
              None
            end
        in
        let omitted =
          if arg = None then (l,ty,lv) :: omitted else omitted in
        let ty_old = if sargs = [] then ty_fun else ty_old in
        type_args ((arg,optional)::args) omitted ty_fun ty_fun0
          ty_old sargs more_sargs
    | _ ->
        match sargs with
          (l, sarg0) :: _ when ignore_labels ->
            raise(Error(sarg0.pexp_loc, Apply_wrong_label(l, ty_old)))
        | _ ->
            type_unknown_args args omitted ty_fun0
              (sargs @ more_sargs)
  in
  match funct.exp_desc, sargs with
    (* Special case for ignore: avoid discarding warning *)
    Texp_ident (_, {val_kind=Val_prim{Primitive.prim_name="%ignore"}}),
    ["", sarg] ->
      let ty_arg, ty_res = filter_arrow env (instance env funct.exp_type) "" in
      let exp = type_expect env sarg ty_arg in
      begin match (expand_head env exp.exp_type).desc with
      | Tarrow _ ->
          Location.prerr_warning exp.exp_loc Warnings.Partial_application
      | Tvar _ ->
          add_delayed_check (fun () -> check_application_result env false exp)
      | _ -> ()
      end;
      ([Some exp, Required], ty_res)
  | _ ->
      let ty = funct.exp_type in
      if ignore_labels then
        type_args [] [] ty (instance env ty) ty [] sargs
      else
        type_args [] [] ty (instance env ty) ty sargs []

and type_construct env loc lid sarg explicit_arity ty_expected =
  let constr = Typetexp.find_constructor env loc lid in
  Env.mark_constructor `Positive env (Longident.last lid) constr;
  let sargs =
    match sarg with
      None -> []
    | Some {pexp_desc = Pexp_tuple sel} when explicit_arity -> sel
    | Some {pexp_desc = Pexp_tuple sel} when constr.cstr_arity > 1 -> sel
    | Some se -> [se] in
  if List.length sargs <> constr.cstr_arity then
    raise(Error(loc, Constructor_arity_mismatch
                  (lid, constr.cstr_arity, List.length sargs)));
  let separate = !Clflags.principal || Env.has_local_constraints env in
  if separate then (begin_def (); begin_def ());
  let (ty_args, ty_res) = instance_constructor constr in
  let texp =
    re {
      exp_desc = Texp_construct(constr, []);
      exp_loc = loc;
      exp_type = ty_res;
      exp_env = env } in
  if separate then begin
    end_def ();
    generalize_structure ty_res;
    unify_exp env {texp with exp_type = instance_def ty_res}
                  (instance env ty_expected);
    end_def ();
    List.iter generalize_structure ty_args;
    generalize_structure ty_res;
  end;
  let ty_args0, ty_res =
    match instance_list env (ty_res :: ty_args) with
      t :: tl -> tl, t
    | _ -> assert false
  in
  let texp = {texp with exp_type = ty_res} in
  if not separate then unify_exp env texp (instance env ty_expected);
  let args = List.map2 (fun e (t,t0) -> type_argument env e t t0) sargs
      (List.combine ty_args ty_args0) in
  if constr.cstr_private = Private then
    raise(Error(loc, Private_type ty_res));
  { texp with exp_desc = Texp_construct(constr, args)}

(* Typing of statements (expressions whose values are discarded) *)

and type_statement env sexp =
  let loc = sexp.pexp_loc in
  begin_def();
  let exp = type_exp env sexp in
  end_def();
  if !Clflags.strict_sequence then
    let expected_ty = instance_def Predef.type_unit in
    unify_exp env exp expected_ty;
    exp else
  let ty = expand_head env exp.exp_type and tv = newvar() in
  begin match ty.desc with
  | Tarrow _ ->
      Location.prerr_warning loc Warnings.Partial_application
  | Tconstr (p, _, _) when Path.same p Predef.path_unit -> ()
  | Tvar _ when ty.level > tv.level ->
      Location.prerr_warning loc Warnings.Nonreturning_statement
  | Tvar _ ->
      add_delayed_check (fun () -> check_application_result env true exp)
  | _ ->
      Location.prerr_warning loc Warnings.Statement_type
  end;
  unify_var env tv ty;
  exp

(* Typing of match cases *)

and type_cases ?in_function env ty_arg ty_res partial_flag loc caselist =
  (* ty_arg is _fully_ generalized *)
  let dont_propagate, has_gadts =
    let patterns = List.map fst caselist in
    List.exists contains_polymorphic_variant patterns,
    List.exists (contains_gadt env) patterns in
  (* prerr_endline ( if has_gadts then "contains gadt" else "no gadt"); *)
  let ty_arg, ty_res, env =
    if has_gadts && not !Clflags.principal then
      correct_levels ty_arg, correct_levels ty_res,
      duplicate_ident_types loc caselist env
    else ty_arg, ty_res, env in
  let lev, env =
    if has_gadts then begin
      (* raise level for existentials *)
      begin_def ();
      Ident.set_current_time (get_current_level ()); 
      let lev = Ident.current_time () in
      Ctype.init_def (lev+1000);                 (* up to 1000 existentials *)
      (lev, Env.add_gadt_instance_level lev env)
    end else (get_current_level (), env)
  in
  (* if has_gadts then
    Format.printf "lev = %d@.%a@." lev Printtyp.raw_type_expr ty_res;*)
  begin_def (); (* propagation of the argument *)
  let ty_arg' = newvar () in
  let pattern_force = ref [] in
  (* Format.printf "@[%i %i@ %a@]@." lev (get_current_level())
    Printtyp.raw_type_expr ty_arg; *)
  let pat_env_list =
    List.map
      (fun (spat, sexp) ->
        let loc = sexp.pexp_loc in
        if !Clflags.principal then begin_def (); (* propagation of pattern *)
        let scope = Some (Annot.Idef loc) in
        let (pat, ext_env, force, unpacks) =
          let partial =
            if !Clflags.principal then Some false else None in
          let ty_arg =
            if dont_propagate then newvar () else instance ?partial env ty_arg
          in type_pattern ~lev env spat scope ty_arg
        in
        pattern_force := force @ !pattern_force;
        let pat =
          if !Clflags.principal then begin
            end_def ();
            iter_pattern (fun {pat_type=t} -> generalize_structure t) pat;
            { pat with pat_type = instance env pat.pat_type }
          end else pat
        in
        unify_pat env pat ty_arg';
        (pat, (ext_env, unpacks)))
      caselist in
  (* Check for polymorphic variants to close *)
  let patl = List.map fst pat_env_list in
  if List.exists has_variants patl then begin
    Parmatch.pressure_variants env patl;
    List.iter (iter_pattern finalize_variant) patl
  end;
  (* `Contaminating' unifications start here *)
  List.iter (fun f -> f()) !pattern_force;
  (* Post-processing and generalization *)
  let patl = List.map fst pat_env_list in
  List.iter (iter_pattern (fun {pat_type=t} -> unify_var env t (newvar())))
    patl;
  List.iter (fun pat -> unify_pat env pat (instance env ty_arg)) patl;
  end_def ();
  List.iter (iter_pattern (fun {pat_type=t} -> generalize t)) patl;
  (* type bodies *)
  let in_function = if List.length caselist = 1 then in_function else None in
  let cases =
    List.map2
      (fun (pat, (ext_env, unpacks)) (spat, sexp) ->
        let sexp = wrap_unpacks sexp unpacks in
        let ty_res' =
          if !Clflags.principal then begin
            begin_def ();
            let ty = instance ~partial:true env ty_res in
            end_def ();
            generalize_structure ty; ty
          end
          else if contains_gadt env spat then correct_levels ty_res
          else ty_res in
        (* Format.printf "@[%i %i, ty_res' =@ %a@]@." lev (get_current_level())
          Printtyp.raw_type_expr ty_res'; *)
        let exp = type_expect ?in_function ext_env sexp ty_res' in
        (pat, {exp with exp_type = instance env ty_res'}))
      pat_env_list caselist
  in
  if !Clflags.principal || has_gadts then begin
    let ty_res' = instance env ty_res in
    List.iter (fun (_,exp) -> unify_exp env exp ty_res') cases
  end;
  let partial =
    if partial_flag then
      Parmatch.check_partial_gadt (partial_pred ~lev env ty_arg) loc cases
    else
      Partial
  in
  add_delayed_check (fun () -> Parmatch.check_unused env cases);
  if has_gadts then begin
    end_def ();
    (* Ensure that existential types do not escape *)
    unify_exp_types loc env (instance env ty_res) (newvar ()) ;
  end;
  cases, partial

(* Typing of let bindings *)

and type_let ?(check = fun s -> Warnings.Unused_var s)
             ?(check_strict = fun s -> Warnings.Unused_var_strict s)
    env rec_flag spat_sexp_list scope allow =
  begin_def();
  if !Clflags.principal then begin_def ();

  let is_fake_let =
    match spat_sexp_list with
    | [_, {pexp_desc=Pexp_match(
           {pexp_desc=Pexp_ident(Longident.Lident "*opt*")},_)}] ->
        true (* the fake let-declaration introduced by fun ?(x = e) -> ... *)
    | _ ->
        false
  in
  let check = if is_fake_let then check_strict else check in

  let spatl =
    List.map
      (fun (spat, sexp) ->
        match spat.ppat_desc, sexp.pexp_desc with
          (Ppat_any | Ppat_constraint _), _ -> spat
        | _, Pexp_constraint (_, _, Some sty)
        | _, Pexp_constraint (_, Some sty, None) when !Clflags.principal ->
            (* propagate type annotation to pattern,
               to allow it to be generalized in -principal mode *)
            {ppat_desc = Ppat_constraint (spat, sty);
             ppat_loc = {spat.ppat_loc with Location.loc_ghost=true}}
        | _ -> spat)
      spat_sexp_list in
  let nvs = List.map (fun _ -> newvar ()) spatl in
  let (pat_list, new_env, force, unpacks) =
    type_pattern_list env spatl scope nvs allow in
  let is_recursive = (rec_flag = Recursive) in
  (* If recursive, first unify with an approximation of the expression *)
  if is_recursive then
    List.iter2
      (fun pat (_, sexp) ->
        let pat =
          match pat.pat_type.desc with
          | Tpoly (ty, tl) ->
              {pat with pat_type =
               snd (instance_poly ~keep_names:true false tl ty)}
          | _ -> pat
        in unify_pat env pat (type_approx env sexp))
      pat_list spat_sexp_list;
  (* Polymorphic variant processing *)
  List.iter
    (fun pat ->
      if has_variants pat then begin
        Parmatch.pressure_variants env [pat];
        iter_pattern finalize_variant pat
      end)
    pat_list;
  (* Generalize the structure *)
  let pat_list =
    if !Clflags.principal then begin
      end_def ();
      List.map
        (fun pat ->
          iter_pattern (fun pat -> generalize_structure pat.pat_type) pat;
          {pat with pat_type = instance env pat.pat_type})
        pat_list
    end else pat_list in
  (* Only bind pattern variables after generalizing *)
  List.iter (fun f -> f()) force;
  let exp_env =
    if is_recursive then new_env else env in

  let current_slot = ref None in
  let warn_unused =
    Warnings.is_active (check "") || Warnings.is_active (check_strict "") in
  let pat_slot_list =
    (* Algorithm to detect unused declarations in recursive bindings:
       - During type checking of the definitions, we capture the 'value_used'
         events on the bound identifiers and record them in a slot corresponding
         to the current definition (!current_slot).
         In effect, this creates a dependency graph between definitions.

       - After type checking the definition (!current_slot = Mone),
         when one of the bound identifier is effectively used, we trigger
         again all the events recorded in the corresponding slot.
         The effect is to traverse the transitive closure of the graph created
         in the first step.

       We also keep track of whether *all* variables in a given pattern
       are unused. If this is the case, for local declarations, the issued
       warning is 26, not 27.
     *)
    List.map
      (fun pat ->
        if not warn_unused then pat, None
        else
          let some_used = ref false in
            (* has one of the identifier of this pattern been used? *)
          let slot = ref [] in
          List.iter
            (fun id ->
              let vd = Env.find_value (Path.Pident id) new_env in
              (* note: Env.find_value does not trigger the value_used event *)
              let name = Ident.name id in
              let used = ref false in
              if not (name = "" || name.[0] = '_' || name.[0] = '#') then
                add_delayed_check
                  (fun () ->
                    if not !used then
                      Location.prerr_warning vd.val_loc
                        ((if !some_used then check_strict else check) name)
                  );
              Env.set_value_used_callback
                name vd
                (fun () ->
                  match !current_slot with
                  | Some slot -> slot := (name, vd) :: !slot
                  | None ->
                      List.iter
                        (fun (name, vd) -> Env.mark_value_used name vd)
                        (get_ref slot);
                      used := true;
                      some_used := true
                )
            )
            (Typedtree.pat_bound_idents pat);
          pat, Some slot
        )
      pat_list
  in
  let exp_list =
    List.map2
      (fun (spat, sexp) (pat, slot) ->
        let sexp =
          if rec_flag = Recursive then wrap_unpacks sexp unpacks else sexp in
        if is_recursive then current_slot := slot;
        match pat.pat_type.desc with
        | Tpoly (ty, tl) ->
            begin_def ();
            if !Clflags.principal then begin_def ();
            let vars, ty' = instance_poly ~keep_names:true true tl ty in
            if !Clflags.principal then begin
              end_def ();
              generalize_structure ty'
            end;
            let exp = type_expect exp_env sexp ty' in
            end_def ();
            check_univars env true "definition" exp pat.pat_type vars;
            {exp with exp_type = instance env exp.exp_type}
        | _ -> type_expect exp_env sexp pat.pat_type)
      spat_sexp_list pat_slot_list in
  current_slot := None;
  List.iter2
    (fun pat exp -> ignore(Parmatch.check_partial pat.pat_loc [pat, exp]))
    pat_list exp_list;
  end_def();
  List.iter2
    (fun pat exp ->
       if not (is_nonexpansive exp) then
         iter_pattern (fun pat -> generalize_expansive env pat.pat_type) pat)
    pat_list exp_list;
  List.iter
    (fun pat -> iter_pattern (fun pat -> generalize pat.pat_type) pat)
    pat_list;
  (List.combine pat_list exp_list, new_env, unpacks)

(* Typing of toplevel bindings *)

let type_binding env rec_flag spat_sexp_list scope =
  Typetexp.reset_type_variables();
  let (pat_exp_list, new_env, unpacks) =
    type_let
      ~check:(fun s -> Warnings.Unused_value_declaration s)
      ~check_strict:(fun s -> Warnings.Unused_value_declaration s)
      env rec_flag spat_sexp_list scope false
  in
  (pat_exp_list, new_env)

let type_let env rec_flag spat_sexp_list scope =
  let (pat_exp_list, new_env, unpacks) =
    type_let env rec_flag spat_sexp_list scope false in
  (pat_exp_list, new_env)

(* Typing of toplevel expressions *)

let type_expression env sexp =
  Typetexp.reset_type_variables();
  begin_def();
  let exp = type_exp env sexp in
  end_def();
  if is_nonexpansive exp then generalize exp.exp_type
  else generalize_expansive env exp.exp_type;
  match sexp.pexp_desc with
    Pexp_ident lid ->
      (* Special case for keeping type variables when looking-up a variable *)
      let (path, desc) = Env.lookup_value lid env in
      {exp with exp_type = desc.val_type}
  | _ -> exp

(* Error report *)

open Format
open Printtyp

let report_error ppf = function
  | Polymorphic_label lid ->
      fprintf ppf "@[The record field label %a is polymorphic.@ %s@]"
        longident lid "You cannot instantiate it in a pattern."
  | Constructor_arity_mismatch(lid, expected, provided) ->
      fprintf ppf
       "@[The constructor %a@ expects %i argument(s),@ \
        but is applied here to %i argument(s)@]"
       longident lid expected provided
  | Label_mismatch(lid, trace) ->
      report_unification_error ppf trace
        (function ppf ->
           fprintf ppf "The record field label %a@ belongs to the type"
                   longident lid)
        (function ppf ->
           fprintf ppf "but is mixed here with labels of type")
  | Pattern_type_clash trace ->
      report_unification_error ppf trace
        (function ppf ->
           fprintf ppf "This pattern matches values of type")
        (function ppf ->
           fprintf ppf "but a pattern was expected which matches values of type")
  | Multiply_bound_variable name ->
      fprintf ppf "Variable %s is bound several times in this matching" name
  | Orpat_vars id ->
      fprintf ppf "Variable %s must occur on both sides of this | pattern"
        (Ident.name id)
  | Expr_type_clash trace ->
      report_unification_error ppf trace
        (function ppf ->
           fprintf ppf "This expression has type")
        (function ppf ->
           fprintf ppf "but an expression was expected of type")
  | Apply_non_function typ ->
      begin match (repr typ).desc with
        Tarrow _ ->
          fprintf ppf "This function is applied to too many arguments;@ ";
          fprintf ppf "maybe you forgot a `;'"
      | _ ->
          fprintf ppf
            "This expression is not a function; it cannot be applied"
      end
  | Apply_wrong_label (l, ty) ->
      let print_label ppf = function
        | "" -> fprintf ppf "without label"
        | l ->
            fprintf ppf "with label %s%s" (if is_optional l then "" else "~") l
      in
      reset_and_mark_loops ty;
      fprintf ppf
        "@[<v>@[<2>The function applied to this argument has type@ %a@]@.\
          This argument cannot be applied %a@]"
        type_expr ty print_label l
  | Label_multiply_defined lid ->
      fprintf ppf "The record field label %a is defined several times"
              longident lid
  | Label_missing labels ->
      let print_labels ppf = List.iter (fun lbl -> fprintf ppf "@ %s" lbl) in
      fprintf ppf "@[<hov>Some record field labels are undefined:%a@]"
        print_labels labels
  | Label_not_mutable lid ->
      fprintf ppf "The record field label %a is not mutable" longident lid
  | Incomplete_format s ->
      fprintf ppf "Premature end of format string ``%S''" s
  | Bad_conversion (fmt, i, c) ->
      fprintf ppf
        "Bad conversion %%%c, at char number %d \
         in format string ``%s''" c i fmt
  | Undefined_method (ty, me) ->
      reset_and_mark_loops ty;
      fprintf ppf
        "@[<v>@[This expression has type@;<1 2>%a@]@,\
         It has no method %s@]" type_expr ty me
  | Undefined_inherited_method me ->
      fprintf ppf "This expression has no method %s" me
  | Virtual_class cl ->
      fprintf ppf "Cannot instantiate the virtual class %a"
        longident cl
  | Unbound_instance_variable v ->
      fprintf ppf "Unbound instance variable %s" v
  | Instance_variable_not_mutable (b, v) ->
      if b then
        fprintf ppf "The instance variable %s is not mutable" v
      else
        fprintf ppf "The value %s is not an instance variable" v
  | Not_subtype(tr1, tr2) ->
      report_subtyping_error ppf tr1 "is not a subtype of" tr2
  | Outside_class ->
      fprintf ppf "This object duplication occurs outside a method definition"
  | Value_multiply_overridden v ->
      fprintf ppf "The instance variable %s is overridden several times" v
  | Coercion_failure (ty, ty', trace, b) ->
      report_unification_error ppf trace
        (function ppf ->
           let ty, ty' = prepare_expansion (ty, ty') in
           fprintf ppf
             "This expression cannot be coerced to type@;<1 2>%a;@ it has type"
           (type_expansion ty) ty')
        (function ppf ->
           fprintf ppf "but is here used with type");
      if b then
        fprintf ppf ".@.@[<hov>%s@ %s@]"
          "This simple coercion was not fully general."
          "Consider using a double coercion."
  | Too_many_arguments (in_function, ty) ->
      reset_and_mark_loops ty;
      if in_function then begin
        fprintf ppf "This function expects too many arguments,@ ";
        fprintf ppf "it should have type@ %a"
          type_expr ty
      end else begin
        fprintf ppf "This expression should not be a function,@ ";
        fprintf ppf "the expected type is@ %a"
          type_expr ty
      end
  | Abstract_wrong_label (l, ty) ->
      let label_mark = function
        | "" -> "but its first argument is not labelled"
        |  l -> sprintf "but its first argument is labelled ~%s" l in
      reset_and_mark_loops ty;
      fprintf ppf "@[<v>@[<2>This function should have type@ %a@]@,%s@]"
      type_expr ty (label_mark l)
  | Scoping_let_module(id, ty) ->
      reset_and_mark_loops ty;
      fprintf ppf
       "This `let module' expression has type@ %a@ " type_expr ty;
      fprintf ppf
       "In this type, the locally bound module name %s escapes its scope" id
  | Masked_instance_variable lid ->
      fprintf ppf
        "The instance variable %a@ \
         cannot be accessed from the definition of another instance variable"
        longident lid
  | Private_type ty ->
      fprintf ppf "Cannot create values of the private type %a" type_expr ty
  | Private_label (lid, ty) ->
      fprintf ppf "Cannot assign field %a of the private type %a"
        longident lid type_expr ty
  | Not_a_variant_type lid ->
      fprintf ppf "The type %a@ is not a variant type" longident lid
  | Incoherent_label_order ->
      fprintf ppf "This function is applied to arguments@ ";
      fprintf ppf "in an order different from other calls.@ ";
      fprintf ppf "This is only allowed when the real type is known."
  | Less_general (kind, trace) ->
      report_unification_error ppf trace
        (fun ppf -> fprintf ppf "This %s has type" kind)
        (fun ppf -> fprintf ppf "which is less general than")
  | Modules_not_allowed ->
      fprintf ppf "Modules are not allowed in this pattern."
  | Cannot_infer_signature ->
      fprintf ppf
        "The signature for this packaged module couldn't be inferred."
  | Not_a_packed_module ty ->
      fprintf ppf
        "This expression is packed module, but the expected type is@ %a"
        type_expr ty
  | Recursive_local_constraint trace ->
      report_unification_error ppf trace
        (function ppf ->
           fprintf ppf "Recursive local constraint when unifying")
        (function ppf ->
           fprintf ppf "with")
  | Unexpected_existential ->
      fprintf ppf
        "Unexpected existential"

let () =
  Env.add_delayed_check_forward := add_delayed_check
