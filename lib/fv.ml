open Ppxlib
module List = ListLabels
open Ast_builder.Default

let ppat_tuple_or_nothing ~loc es =
  if 0 == List.length es then None else Some (ppat_tuple ~loc es)

let pexp_nolabel_apply ~loc f args =
  pexp_apply ~loc f (List.map ~f:(fun x -> (Nolabel, x)) args)

let layout_ f t =
  let _ = Format.flush_str_formatter () in
  f Format.str_formatter t;
  Format.flush_str_formatter ()

let layout_core_type = layout_ Pprintast.core_type
let map_loc f { loc; txt } = { loc; txt = f txt }
let ppat_tmp_var ~loc i = ppat_var ~loc { loc; txt = "x_" ^ string_of_int i }

let pexp_tmp_var ~loc i =
  pexp_ident ~loc { loc; txt = lident ("x_" ^ string_of_int i) }

let ptyp_string ~loc = ptyp_constr ~loc { loc; txt = lident "string" } []
let pexp_empty_list ~loc = pexp_construct ~loc { loc; txt = lident "[]" } None

let pexp_list_literal ~loc es =
  List.fold_right
    ~f:(fun hd tl ->
      pexp_construct ~loc
        { loc; txt = lident "::" }
        (Some (pexp_tuple ~loc [ hd; tl ])))
    es ~init:(pexp_empty_list ~loc)

let pexp_list_concat ~loc es =
  match es with
  | [] -> pexp_empty_list ~loc
  | [ x ] -> x
  | _ ->
      pexp_nolabel_apply ~loc
        (pexp_ident ~loc { loc; txt = Longident.parse "List.concat" })
        [ pexp_list_literal ~loc es ]

let fv_name type_name = { txt = "fv_of_" ^ type_name.txt; loc = type_name.loc }

let is_free_var_type ct =
  List.exists
    ~f:(fun attr -> String.equal "free" attr.attr_name.txt)
    ct.ptyp_attributes

let fv_impl ~ptype_name (cds : constructor_declaration list) =
  let loc = ptype_name.loc in
  let pexp_input = pexp_ident ~loc { loc; txt = lident "input" } in
  let fv_expr name = pexp_ident ~loc (map_loc lident @@ fv_name name) in
  let self = fv_expr ptype_name in
  let id = pexp_ident ~loc { loc; txt = lident "_singleton_list" } in
  let rec type_to_fv_function ct =
    let loc = ct.ptyp_loc in
    match ct.ptyp_desc with
    | Ptyp_constr (ld_constr, [])
      when is_free_var_type ct
           && 0 == Longident.compare ld_constr.txt (lident "string") ->
        Some id
    | Ptyp_constr (ld_constr, [])
      when 0 == Longident.compare ld_constr.txt (lident ptype_name.txt) ->
        Some self
    | Ptyp_constr (_, []) -> None
    | Ptyp_constr (ld_constr, [ arg ]) -> (
        match type_to_fv_function arg with
        | None -> None
        | Some f ->
            let label = map_loc Longident.last_exn ld_constr in
            Some (pexp_nolabel_apply ~loc (fv_expr label) [ f ]))
    | Ptyp_constr (_, _) -> failwith "unimp constructor with multiple args"
    | _ -> None
  in
  let mk_match_case (cd : constructor_declaration) =
    let loc = cd.pcd_loc in
    match cd.pcd_args with
    | Pcstr_record _ -> failwith "unimp recorde type"
    | Pcstr_tuple ct_list ->
        let args, pexp_gathared_fvs =
          List.split
          @@ List.mapi
               ~f:(fun i ct ->
                 let loc = ct.ptyp_loc in
                 match type_to_fv_function ct with
                 | None -> (ppat_any ~loc, None)
                 | Some f ->
                     ( ppat_tmp_var ~loc i,
                       Some (pexp_nolabel_apply ~loc f [ pexp_tmp_var ~loc i ])
                     ))
               ct_list
        in
        let pc_lhs =
          ppat_variant ~loc cd.pcd_name.txt (ppat_tuple_or_nothing ~loc args)
        in
        let pc_rhs =
          pexp_list_concat ~loc
            (List.filter_map ~f:(fun x -> x) pexp_gathared_fvs)
        in
        { pc_lhs; pc_guard = None; pc_rhs }
  in
  let body = pexp_match ~loc pexp_input (List.map ~f:mk_match_case cds) in
  pstr_value ~loc Recursive
    [
      {
        pvb_pat = ppat_var ~loc (fv_name ptype_name);
        pvb_expr =
          pexp_fun ~loc Nolabel None (ppat_var ~loc { loc; txt = "input" }) body;
        pvb_attributes = [];
        pvb_loc = loc;
      };
    ]

let fv_intf ~ptype_name =
  let loc = ptype_name.loc in
  psig_value ~loc
    {
      pval_name = fv_name ptype_name;
      pval_type =
        ptyp_arrow ~loc Nolabel
          (ptyp_constr ~loc { loc; txt = lident ptype_name.txt } [])
          (ptyp_string ~loc);
      pval_attributes = [];
      pval_loc = loc;
      pval_prim = [];
    }

let generate_impl ~ctxt (_rec_flag, type_declarations) =
  let loc = Expansion_context.Deriver.derived_item_loc ctxt in
  List.map type_declarations ~f:(fun (td : type_declaration) ->
      match td with
      | {
       ptype_kind = Ptype_abstract | Ptype_record _ | Ptype_open;
       ptype_loc;
       _;
      } ->
          let ext =
            Location.error_extensionf ~loc:ptype_loc
              "Cannot derive fvs for non varaint types"
          in
          [ Ast_builder.Default.pstr_extension ~loc ext [] ]
      | { ptype_kind = Ptype_variant fields; ptype_name; _ } ->
          [ fv_impl ~ptype_name fields ])
  |> List.concat

let generate_intf ~ctxt (_rec_flag, type_declarations) =
  let loc = Expansion_context.Deriver.derived_item_loc ctxt in
  List.map type_declarations ~f:(fun (td : type_declaration) ->
      match td with
      | {
       ptype_kind = Ptype_abstract | Ptype_record _ | Ptype_open;
       ptype_loc;
       _;
      } ->
          let ext =
            Location.error_extensionf ~loc:ptype_loc
              "Cannot derive fvs for non varaint types"
          in
          [ Ast_builder.Default.psig_extension ~loc ext [] ]
      | { ptype_kind = Ptype_variant _; ptype_name; _ } ->
          [ fv_intf ~ptype_name ])
  |> List.concat

let impl_generator = Deriving.Generator.V2.make_noarg generate_impl
let intf_generator = Deriving.Generator.V2.make_noarg generate_intf

let my_deriver =
  Deriving.add "fv" ~str_type_decl:impl_generator ~sig_type_decl:intf_generator
