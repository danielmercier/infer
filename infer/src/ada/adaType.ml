(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open Libadalang
open AdaUtils
open LalUtils
open Option.Monad_infix
module L = Logging

module TypenameHash = Caml.Hashtbl.Make (struct
  type t = Typ.Name.t

  let equal tn1 tn2 = Typ.Name.equal tn1 tn2

  let hash = Caml.Hashtbl.hash
end)

type index_kind = Fixed | Dynamic

type discriminant = Typ.Fieldname.t

type expr = Int of int | Lal of Expr.t

type range = expr * expr

type condition = Equal of expr | InRange of range | LessThan of expr

type discrete = Signed of range | Enum of expr (* Length of the enum *) | Mod of expr

type field = {name: Typ.Fieldname.t; condition: (discriminant * condition) list; typ: t}

and record = {discriminants: (discriminant * discrete * expr option) list; fields: field list}

and tenv = record TypenameHash.t

and t =
  | Discrete of discrete
  | Float
  | Array of Typ.Name.t * (index_kind * discrete) list * t
  | Record of Typ.Name.t
  | Access of t
  | Void

let lookup = TypenameHash.find_opt

type any_field = Discriminant of discriminant * discrete * expr option | Field of field

let lookup_field tenv name field_name =
  let open Option.Monad_infix in
  let field record =
    (* Get the field with name field_name inside the given record *)
    let from_fields =
      (* If the field_name is inside record.fields, return it's type *)
      List.find_map
        ~f:(fun value_field ->
          if Typ.Fieldname.equal field_name value_field.name then Some (Field value_field)
          else None )
        record.fields
    in
    match from_fields with
    | Some field ->
        Some field
    | None ->
        (* The field_name is not part of record.fields, try to find it in
        * the discriminants*)
        List.find_map
          ~f:(fun (discriminant, discrete, expr_opt) ->
            if Typ.Fieldname.equal field_name discriminant then
              Some (Discriminant (discriminant, discrete, expr_opt))
            else None )
          record.discriminants
  in
  lookup tenv name >>= field


let field_typ = function
  | Field {typ} ->
      typ
  | Discriminant (_, _, Some expr) ->
      (* If some expr is binded to this discriminant, set the type
         * to the range containing only this expr since it's the only
         * possible value for this field *)
      Discrete (Signed (expr, expr))
  | Discriminant (_, discrete, None) ->
      Discrete discrete


(** Create a name that uniquely refers to the given base type declaration *)
let get_name base_type_decl =
  match BaseTypeDecl.f_name base_type_decl with
  | Some name ->
      (* If the type have a name, simply use this *)
      Typ.AdaRecord (unique_defining_name name)
  | None ->
      (* If not, use the short_image of the node. The short image contains the
       * position of the node *)
      Typ.AdaRecord (Mangled.from_string (AdaNode.short_image base_type_decl))


(** Translate an expression to a simplified expression for use in typing.
 * TODO: For now, whenever the expression cannot be computed to an integer,
 * We return the expression as it is. The translation should do the work of
 * creating a program variable and assign the expression to it at the level of
 * the type declaration. *)
let trans_expr expr = try Int (Expr.p_eval_as_int expr) with PropertyError _ -> Lal expr

let trans_expr expr = trans_expr (expr :> Expr.t)

(** Translate a BinOp to a range *)
let trans_binop binop =
  match (binop :> BinOp.t) with
  | `BinOp {f_op= (lazy (`OpDoubleDot _)); f_left= (lazy left); f_right= (lazy right)}
  | `RelationOp {f_op= (lazy (`OpDoubleDot _)); f_left= (lazy left); f_right= (lazy right)} ->
      (trans_expr left, trans_expr right)
  | `BinOp {f_op= (lazy op)} | `RelationOp {f_op= (lazy op)} ->
      L.die InternalError "Cannot generate a discrete type with op %s" (AdaNode.short_image op)


(** Translate a RangeSpec to a discrete type *)
let rec trans_range_spec range_spec =
  match RangeSpec.f_range range_spec with
  | #BinOp.t as binop ->
      Discrete (Signed (trans_binop binop))
  | _ ->
      L.die InternalError "Expecting operator .. for a signed int type definintion"


(** Translate a list of constraint to a list of indices types. For use with
 * array definition and constraint *)
and trans_array_constraints tenv constraints =
  let trans_array_constraint constr =
    match (constr :> AdaNode.t) with
    | #BinOp.t as binop ->
        (Fixed, Signed (trans_binop binop))
    | #Name.t as name -> (
      match Name.p_referenced_decl name with
      | Some (#BaseTypeDecl.t as type_decl) -> (
        match trans_type_decl tenv type_decl with
        | Discrete discrete ->
            (Fixed, discrete)
        | _ ->
            L.die InternalError "Index type should be a discrete type" )
      | _ ->
          L.die InternalError "Expecting subtype indication" )
    | #SubtypeIndication.t as subtype_indication -> (
      match SubtypeIndication.f_constraint subtype_indication with
      | Some (`RangeConstraint {f_range= (lazy (`RangeSpec {f_range= (lazy (`BoxExpr _))}))}) -> (
        (* Here is the only way to make a dynamic array *)
        match
          Option.value_exn (TypeExpr.p_designated_type_decl subtype_indication)
          |> trans_type_decl tenv
        with
        | Discrete discrete ->
            (Dynamic, discrete)
        | _ ->
            L.die InternalError "Index type should be a discrete type" )
      | _ -> (
        (* In other cases, this array dimension is fixed *)
        match trans_type_expr tenv (subtype_indication :> TypeExpr.t) with
        | Discrete discrete ->
            (Fixed, discrete)
        | _ ->
            L.die InternalError "Index type should be a discrete type" ) )
    | _ ->
        unimplemented "constraint for %s" (AdaNode.short_image constr)
  in
  List.map ~f:trans_array_constraint (ConstraintList.f_list constraints)


(** Translate an ada constraint on a type, to a new type derived from the given
 * one*)
and trans_constraint tenv name orig_type constr =
  match (constr :> Constraint.t) with
  | `DeltaConstraint _ | `DigitsConstraint _ ->
      (* TODO: Same as for RealTypeDef, this should be updated when we implement
       * ranges on real types *)
      orig_type
  | `DiscriminantConstraint {f_constraints= (lazy constraints)} -> (
    match orig_type with
    | Record base_name ->
        let param_actuals = AssocList.p_zip_with_params constraints |> sort_params in
        ( match lookup tenv base_name with
        | Some {discriminants; fields} ->
            let discriminants =
              match
                List.map2
                  ~f:(fun (discr, typ, _) {ParamActual.actual} ->
                    (discr, typ, Some (trans_expr actual)) )
                  discriminants param_actuals
              with
              | Ok result ->
                  result
              | Unequal_lengths ->
                  L.die InternalError "Discriminant constraint incorrect size"
            in
            TypenameHash.add tenv name {discriminants; fields}
        | None ->
            () ) ;
        Record name
    | _ ->
        L.die InternalError "Discriminant constraint on a non record type" )
  | `IndexConstraint {f_constraints= (lazy constraints)} -> (
    match orig_type with
    | Array (_, _, elt_typ) ->
        Array (name, trans_array_constraints tenv constraints, elt_typ)
    | _ ->
        L.die InternalError "Index constraint on a non array type" )
  | `RangeConstraint {f_range= (lazy range_spec)} -> (
    match orig_type with
    | Discrete _ ->
        trans_range_spec range_spec
    | _ ->
        L.die InternalError "Range constraint on a non discrete type" )


(** translate the lal definition of an array.
 * We translate an array to it's name, the index for each dimension as a list,
 * and the element type *)
and trans_array_type_def tenv name array_type_def =
  match (array_type_def :> ArrayTypeDef.t) with
  | `ArrayTypeDef
      { f_indices= (lazy indices)
      ; f_component_type= (lazy (`ComponentDef {f_type_expr= (lazy type_expr)})) } ->
      let elt_typ = trans_type_expr tenv (type_expr :> TypeExpr.t) in
      let indices =
        match indices with
        | `ConstrainedArrayIndices {f_list= (lazy constraints)} ->
            (* For constrained array indices, we fallback on calling
             * the translation of a list constraint *)
            trans_array_constraints tenv constraints
        | `UnconstrainedArrayIndices _ ->
            (* TODO: Check what this kind of index is *)
            unimplemented "trans_type_def for UnconstrainedArrayIndices"
      in
      Array (name, indices, elt_typ)


(** Translate a lal record definition into a type.
 * The type for a record is simply it's name. But we register the fields of
 * a record in the type environement *)
and trans_record_type_def tenv type_decl record_type_def =
  let name = get_name type_decl in
  match TypenameHash.find_opt tenv name with
  | Some _ ->
      Record name
  | None ->
      let trans_component condition component =
        match (component :> AdaNode.t) with
        | `ComponentDecl
            { f_ids= (lazy (`DefiningNameList {list= (lazy ids)}))
            ; f_component_def= (lazy (`ComponentDef {f_type_expr= (lazy type_expr)})) } ->
            let typ = trans_type_expr tenv (type_expr :> TypeExpr.t) in
            List.map ~f:(fun name -> {name= field_name name; condition; typ}) ids
        | _ ->
            (* we ignore the rest of the possible types *)
            []
      in
      let rec trans_variant_part condition = function
        | `VariantPart
            { VariantPartType.f_discr_name= (lazy ident)
            ; f_variant= (lazy (`VariantList {list= (lazy variants)})) } ->
            (* A variant part is of the form:
             * when discr_name is
             *   case alternative_list =>
             *     component_list
             *
             * for each case, construct the new condition based on the given one
             * and the alternative_list, and call trans_component with this
             * newly created condition on the component_list
             * *)
            let discriminant = Option.value_exn (AdaNode.p_xref ident) |> field_name in
            let f variant =
              let f choice =
                (* create a condition for this choice *)
                match choice with
                | #Expr.t as expr -> (
                  match expr with
                  | #BinOp.t as binop ->
                      (discriminant, InRange (trans_binop binop))
                  | _ ->
                      (discriminant, Equal (trans_expr expr)) )
                | #SubtypeIndication.t as subtype -> (
                  match trans_type_expr tenv subtype with
                  | Discrete (Signed range) ->
                      (discriminant, InRange range)
                  | Discrete (Enum bound) | Discrete (Mod bound) ->
                      (discriminant, LessThan bound)
                  | _ ->
                      L.die InternalError "Expecting discrete type for a choice" )
                | _ ->
                    L.die InternalError "Unexpecting node %s" (AdaNode.short_image choice)
              in
              let new_conditions =
                (* Create the new conditions based on the previous one plus all
                 * the alternatives using the function f defined above *)
                condition @ List.map ~f (Variant.f_choices variant |> AlternativesList.f_list)
              in
              trans_componentlist new_conditions (Variant.f_components variant)
            in
            List.concat_map ~f variants
      and trans_componentlist conditions componentlist =
        let components =
          ComponentList.f_components componentlist
          >>| AdaNodeList.f_list |> Option.value ~default:[]
        in
        let variant_part = ComponentList.f_variant_part componentlist in
        List.concat_map ~f:(trans_component conditions) components
        @ Option.value ~default:[] (variant_part >>| trans_variant_part conditions)
      in
      let trans_discriminant discriminant =
        (* A discriminant spec possibly contains multiple ids so map them to
         * the name and the type of the discriminant *)
        let typ =
          match trans_type_expr tenv (DiscriminantSpec.f_type_expr discriminant :> TypeExpr.t) with
          | Discrete discrete ->
              discrete
          | _ ->
              L.die InternalError "Type of discriminant should be a discrete type"
        in
        DiscriminantSpec.f_ids discriminant
        |> DefiningNameList.f_list
        |> List.map ~f:(fun name -> (field_name name, typ, None))
      in
      let componentlist =
        RecordTypeDef.f_record_def record_type_def |> BaseRecordDef.f_components
      in
      let discriminants =
        match TypeDecl.f_discriminants type_decl with
        | Some
            (`KnownDiscriminantPart
              {f_discr_specs= (lazy (`DiscriminantSpecList {list= (lazy discriminants)}))}) ->
            discriminants
        | _ ->
            []
      in
      TypenameHash.add tenv name
        { discriminants= List.concat_map ~f:trans_discriminant discriminants
        ; fields= trans_componentlist [] componentlist } ;
      Record name


(** Given the name of the translated type and the type definition, translate
 * a type definition into a type *)
and trans_type_def tenv type_decl type_def =
  match (type_def :> TypeDef.t) with
  | #EnumTypeDef.t as enum_type_def ->
      (* type Number is (One, Two, Three)
       * We assume that enum types first is 0 and last is (length - 1) *)
      let enum_length =
        EnumTypeDef.f_enum_literals enum_type_def |> EnumLiteralDeclList.f_list |> List.length
      in
      Discrete (Enum (Int enum_length))
  | #SignedIntTypeDef.t as signed_int_type_def ->
      (* type IntRange is range 1 .. 10
       * Fallback on translating the range constraint *)
      SignedIntTypeDef.f_range signed_int_type_def |> trans_range_spec
  | #ModIntTypeDef.t as mod_int_type_def ->
      (* type IntMod is mod 256
     * *)
      Discrete (Mod (ModIntTypeDef.f_expr mod_int_type_def |> trans_expr))
  | #RecordTypeDef.t as record_type_def ->
      (* record definition *)
      trans_record_type_def tenv type_decl record_type_def
  | #RealTypeDef.t ->
      (* TODO: simple float for now without taking ranges in account *)
      Float
  | `AnonymousTypeAccessDef {f_type_decl= (lazy type_decl)} ->
      (* anonymous access *)
      Access (trans_type_decl tenv type_decl)
  | `TypeAccessDef {f_subtype_indication= (lazy subtype_indication)} ->
      (* access definition *)
      Access (trans_type_expr tenv (subtype_indication :> TypeExpr.t))
  | `DerivedTypeDef {f_subtype_indication= (lazy subtype_indication)} ->
      (* type Derived is new SomeType
       * return the type of the original type *)
      let name = get_name type_decl in
      trans_subtype_indication tenv name subtype_indication
  | #ArrayTypeDef.t as array_type_def ->
      (* type Arr is array (1 .. 10) of Integer *)
      trans_array_type_def tenv (get_name type_decl) array_type_def
  | (`AccessToSubpDef _ | #FormalDiscreteTypeDef.t | #PrivateTypeDef.t | #InterfaceTypeDef.t) as
    type_def ->
      unimplemented "trans_type_decl for %s" (AdaNode.short_image type_def)


and trans_type_decl tenv base_type_decl =
  match (base_type_decl :> BaseTypeDecl.t) with
  | #TypeDecl.t as type_decl ->
      (* This is a type declaration, the type depends on the type definition *)
      let typ = trans_type_def tenv type_decl (TypeDecl.f_type_def type_decl) in
      typ
  | `SubtypeDecl {f_subtype= (lazy subtype)} ->
      (* For a subtype, we can simply fallback on calling the translation for
       * a type expr *)
      let name = get_name base_type_decl in
      trans_subtype_indication tenv name subtype
  | #DiscreteBaseSubtypeDecl.t ->
      (* TODO: Check what kind of subtype declaration this refers to *)
      unimplemented "trans_type_decl for %s" (AdaNode.short_image base_type_decl)
  | #ClasswideTypeDeclType.t
  | #TaskTypeDeclType.t
  | #ProtectedTypeDeclType.t
  | #IncompleteTypeDeclType.t ->
      unimplemented "trans_type_decl for %s" (AdaNode.short_image base_type_decl)


and trans_subtype_indication tenv name subtype_indication =
  match lookup tenv name with
  | Some _ ->
      Record name
  | None -> (
      let orig_type =
        match SubtypeIndication.f_name subtype_indication |> Name.p_referenced_decl with
        | Some (#BaseTypeDecl.t as base_type_decl) ->
            trans_type_decl tenv base_type_decl
        | _ ->
            L.die InternalError "Name for subtype indication should refer to a type"
      in
      match SubtypeIndication.f_constraint subtype_indication with
      | Some constr ->
          (* This is the only case where we change the type *)
          trans_constraint tenv name orig_type constr
      | None ->
          orig_type )


and trans_type_expr tenv type_expr =
  (* The orig type is the type of the type declaration designated by this type
   * expression *)
  let orig_type =
    Option.value_exn (TypeExpr.p_designated_type_decl type_expr) |> trans_type_decl tenv
  in
  match (type_expr :> TypeExpr.t) with
  | #SubtypeIndication.t as subtype_indication ->
      let name = Typ.AdaRecord (Mangled.from_string (AdaNode.short_image type_expr)) in
      trans_subtype_indication tenv name subtype_indication
  | _ ->
      orig_type


let trans_type_decl tenv type_decl = trans_type_decl tenv (type_decl :> BaseTypeDecl.t)

let trans_type_expr tenv type_expr = trans_type_expr tenv (type_expr :> TypeExpr.t)

let rec trans_type_of_expr tenv expr =
  match (expr :> Expr.t) with
  | #lvalue as call when Name.p_is_call call -> (
    (* This is a call without arguments *)
    match Name.p_referenced_decl call with
    | Some (#EnumLiteralDecl.t as enum_literal) -> (
      match EnumLiteralDecl.p_enum_type enum_literal with
      | Some type_decl ->
          trans_type_decl tenv type_decl
      | None ->
          L.die InternalError "Cannot generate a type for %s" (AdaNode.short_image expr) )
    | Some (#BaseSubpBody.t as subp) -> (
      match BaseSubpBody.f_subp_spec subp |> SubpSpec.f_subp_returns with
      | Some type_expr ->
          trans_type_expr tenv type_expr
      | None ->
          (* the subp is a procedure, return void *)
          Void )
    | _ ->
        L.die InternalError "Cannot generate a type for %s" (AdaNode.short_image expr) )
  | `DottedName {f_prefix= (lazy prefix)} as name when is_record_field_access name ->
      (* in a case of a dotted name representing the access to a field,
       * get the registered type for this field *)
      let rec aux = function
        | Record record_name -> (
            let field = field_name (Option.value_exn (AdaNode.p_xref name)) in
            match lookup_field tenv record_name field >>| field_typ with
            | Some typ ->
                typ
            | None ->
                L.die InternalError "Cannot translate a type for %s" (AdaNode.short_image expr) )
        | Access root_typ ->
            (* Implicity dereference *)
            aux root_typ
        | _ ->
            L.die InternalError "Cannot translate a type for %s" (AdaNode.short_image expr)
      in
      aux (trans_type_of_expr tenv (prefix :> Expr.t))
  | `ExplicitDeref {f_prefix= (lazy prefix)} -> (
      (* For an explicit deref, rely on the accessed type of the pointer type *)
      let access_typ = trans_type_of_expr tenv (prefix :> Expr.t) in
      match access_typ with
      | Access typ ->
          typ
      | _ ->
          L.die InternalError "Cannot translate a type for %s" (AdaNode.short_image expr) )
  | `CallExpr {f_name= (lazy name)} ->
      (* For an call expr (that here represents a array access), rely on the
       * element type of the array type *)
      let rec aux = function
        | Array (_, _, elt_typ) ->
            elt_typ
        | Access root_typ ->
            (* Implicity dereference *)
            aux root_typ
        | _ ->
            L.die InternalError "Cannot translate a type for %s" (AdaNode.short_image expr)
      in
      aux (trans_type_of_expr tenv (name :> Expr.t))
  | `AttributeRef {f_prefix= (lazy prefix); f_attribute= (lazy attribute)} when is_access attribute
    ->
      (* 'Access type has type Access on the type of the prefix *)
      let accessed_typ = trans_type_of_expr tenv (prefix :> Expr.t) in
      Access accessed_typ
  | #lvalue as lvalue -> (
    (* For an lvalue, we need to go to it's declaration to get the more precise
     * type.
     * For example:
     * X : Integer range 1 .. 10
     *
     * calling p_expression_type would return Integer without the range info *)
    match Name.p_referenced_decl lvalue >>= BasicDecl.p_type_expression with
    | Some type_expr ->
        trans_type_expr tenv type_expr
    | None ->
        L.die InternalError "Cannot translate a type for %s" (AdaNode.short_image expr) )
  | _ -> (
    match Expr.p_expression_type expr with
    | Some base_type_decl ->
        trans_type_decl tenv base_type_decl
    | None ->
        L.die InternalError "Cannot translate a type for %s" (AdaNode.short_image expr) )


let trans_type_of_expr tenv expr = trans_type_of_expr tenv (expr :> Expr.t)

let pp_expr fmt expr =
  match expr with
  | Int i ->
      Format.pp_print_int fmt i
  | Lal lal ->
      Format.pp_print_string fmt (AdaNode.text lal)


let pp_discrete fmt = function
  | Signed (lower, upper) ->
      Format.fprintf fmt "range %a .. %a" pp_expr lower pp_expr upper
  | Enum length ->
      Format.fprintf fmt "enum with length %a" pp_expr length
  | Mod upper ->
      Format.fprintf fmt "mod %a" pp_expr upper


let pp_kind fmt = function
  | Fixed ->
      Format.pp_print_string fmt "Fixed"
  | Dynamic ->
      Format.pp_print_string fmt "Dynamic"


let create () = TypenameHash.create 1024

let rec to_infer_typ tenv infer_tenv typ =
  let int_typ = Typ.mk (Tint IInt) in
  let of_discrete = function
    | Signed (Int lower, Int upper) ->
        Typ.mk (Tint (IRange (Some lower, Some upper)))
    | Signed (Int lower, _) ->
        Typ.mk (Tint (IRange (Some lower, None)))
    | Signed (_, Int upper) ->
        Typ.mk (Tint (IRange (None, Some upper)))
    | Enum (Int upper) ->
        Typ.mk (Tint (IRange (Some 0, Some (upper - 1))))
    | Mod (Int upper) ->
        Typ.mk (Tint (IMod upper))
    | _ ->
        int_typ
  in
  match typ with
  | Discrete discrete ->
      of_discrete discrete
  | Float ->
      Typ.mk (Tfloat FFloat)
  | Array (name, [(index_kind, index_typ)], elt_typ) -> (
      (* TODO: dimensions are not taken into account. Only one dimensional array
       * is implemented*)
      let struct_typ = Typ.mk (Tstruct name) in
      match Tenv.lookup infer_tenv name with
      | Some _ ->
          struct_typ
      | None ->
          (* We convert an array to a record with fields first, last, length and
           * data. *)
          let array_typ =
            Typ.mk (Typ.Tptr (to_infer_typ tenv infer_tenv elt_typ, Typ.Pk_pointer))
          in
          let lower, upper =
            match index_typ with
            | Signed (Int lower, Int upper) ->
                (Some lower, Some upper)
            | Signed (_, Int upper) ->
                (None, Some upper)
            | Signed (Int lower, _) ->
                (Some lower, None)
            | Signed _ ->
                (None, None)
            | Enum (Int upper) ->
                (Some 0, Some (upper - 1))
            | Enum _ ->
                (Some 0, None)
            | Mod (Int upper) ->
                (Some 0, Some upper)
            | Mod _ ->
                (Some 0, None)
          in
          let first_typ, last_typ, length_typ =
            let length =
              match (lower, upper) with
              | Some int_lower, Some int_upper ->
                  Some (max 0 (int_upper - int_lower + 1))
              | _ ->
                  None
            in
            match index_kind with
            | Fixed ->
                ( Typ.mk (Tint (IRange (lower, lower)))
                , Typ.mk (Tint (IRange (upper, upper)))
                , Typ.mk (Tint (IRange (Some (Option.value ~default:0 length), length))) )
            | Dynamic ->
                ( Typ.mk (Tint (IRange (lower, None)))
                , Typ.mk (Tint (IRange (None, upper)))
                , Typ.mk (Tint (IRange (Some 0, length))) )
          in
          ignore
            (Tenv.mk_struct infer_tenv
               ~fields:
                 [ (Typ.Fieldname.Ada.from_string "first", first_typ, Annot.Item.empty)
                 ; (Typ.Fieldname.Ada.from_string "last", last_typ, Annot.Item.empty)
                 ; (Typ.Fieldname.Ada.from_string "length", length_typ, Annot.Item.empty)
                 ; (Typ.Fieldname.Ada.from_string "data", array_typ, Annot.Item.empty) ]
               name) ;
          struct_typ )
  | Record name -> (
      let struct_typ = Typ.mk (Tstruct name) in
      match (Tenv.lookup infer_tenv name, lookup tenv name) with
      | Some _, _ | None, None ->
          struct_typ
      | None, Some {discriminants; fields} ->
          (* In that case we need to add the type information in the infer tenv *)
          let fields =
            List.map
              ~f:(fun (discriminant, discrete, expr_opt) ->
                match expr_opt with
                | Some (Int i) ->
                    (discriminant, Typ.mk (Tint (IRange (Some i, Some i))), Annot.Item.empty)
                | _ ->
                    (discriminant, of_discrete discrete, Annot.Item.empty) )
              discriminants
            @ List.map
                ~f:(fun {name; typ} -> (name, to_infer_typ tenv infer_tenv typ, Annot.Item.empty))
                fields
          in
          ignore (Tenv.mk_struct infer_tenv ~fields name) ;
          struct_typ )
  | Access typ ->
      let accessed_typ = to_infer_typ tenv infer_tenv typ in
      Typ.mk (Tptr (accessed_typ, Pk_pointer))
  | Void ->
      Typ.void
  | Array _ ->
      (* TODO: dimensions are not taken into account. Only one dimensional array
       * is implemented *)
      unimplemented "multidimensional array"


let rec pp tenv fmt typ =
  match typ with
  | Discrete discrete ->
      pp_discrete fmt discrete
  | Float ->
      Format.fprintf fmt "float"
  | Array (name, dimensions, elt_typ) ->
      let pp_dimension fmt (kind, discrete) =
        Format.fprintf fmt "%a %a" pp_kind kind pp_discrete discrete
      in
      let pp_sep fmt () = Format.pp_print_string fmt ",@ " in
      Format.fprintf fmt "type %a is array(@[%a@]) of %a" Typ.Name.pp name
        (Format.pp_print_list ~pp_sep pp_dimension)
        dimensions (pp tenv) elt_typ
  | Record name -> (
    match lookup tenv name with
    | Some {discriminants; fields} ->
        let pp_discriminant fmt (discriminant, discrete, expr_opt) =
          match expr_opt with
          | Some expr ->
              Format.fprintf fmt "%a" pp_expr expr
          | None ->
              Format.fprintf fmt "%a : %a" Typ.Fieldname.pp discriminant pp_discrete discrete
        in
        let pp_field fmt field =
          let pp_condition fmt (discriminant, condition) =
            match condition with
            | Equal expr ->
                Format.fprintf fmt "%a = %a" Typ.Fieldname.pp discriminant pp_expr expr
            | InRange (lower, upper) ->
                Format.fprintf fmt "%a in %a .. %a" Typ.Fieldname.pp discriminant pp_expr lower
                  pp_expr upper
            | LessThan expr ->
                Format.fprintf fmt "%a < %a" Typ.Fieldname.pp discriminant pp_expr expr
          in
          let pp_sep fmt () = Format.pp_print_string fmt "@ | " in
          Format.fprintf fmt "%a %a : %a"
            (Format.pp_print_list ~pp_sep pp_condition)
            field.condition Typ.Fieldname.pp field.name (pp tenv) field.typ
        in
        Format.fprintf fmt "@[<v>@[<v 2>type %a is record (@[%a@])@ %a@]@ end record" Typ.Name.pp
          name
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ",@ ")
             pp_discriminant)
          discriminants (Format.pp_print_list pp_field) fields
    | None ->
        Format.fprintf fmt "type %a is record" Typ.Name.pp name )
  | Access typ -> (
    match typ with
    | Record name | Array (name, _, _) ->
        Format.fprintf fmt "is access %a" Typ.Name.pp name
    | _ ->
        Format.fprintf fmt "is access %a" (pp tenv) typ )
  | Void ->
      Format.fprintf fmt "is void"
