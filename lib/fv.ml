open Ppxlib
module List = ListLabels
open Ast_builder.Default

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
  pexp_apply ~loc
    (pexp_ident ~loc { loc; txt = Longident.parse "List.concat" })
    (List.map ~f:(fun x -> (Nolabel, x)) es)

let fv_name type_name = { txt = "fv_of_" ^ type_name.txt; loc = type_name.loc }

let is_free_var_type ct =
  List.exists
    ~f:(fun attr -> String.equal "free" attr.attr_name.txt)
    ct.ptyp_attributes

let is_cur_type_container cur_ct_name ct =
  match ct.ptyp_desc with
  | Ptyp_constr (ld_constr, [ arg ]) ->
      (* let () = *)
      (*   Printf.printf "compare: %s == %s? %b\n" cur_ct_name *)
      (*     (layout_core_type arg) *)
      (*     (String.equal cur_ct_name (layout_core_type arg)) *)
      (* in *)
      if String.equal cur_ct_name (layout_core_type arg) then Some ld_constr
      else None
  | Ptyp_constr (_, []) -> None
  | Ptyp_constr (_, _) -> failwith "unimp constructor with multiple args"
  | _ -> None

let fv_impl ~ptype_name (cds : constructor_declaration list) =
  let loc = ptype_name.loc in
  let pexp_input = pexp_ident ~loc { loc; txt = lident "input" } in
  let self = pexp_ident ~loc (map_loc lident @@ fv_name ptype_name) in
  let mk_match_case (cd : constructor_declaration) =
    let loc = cd.pcd_loc in
    match cd.pcd_args with
    | Pcstr_record _ -> failwith "unimp recorde type"
    | Pcstr_tuple ct_list ->
        let id_ct_list = List.mapi ~f:(fun i ct -> (i, ct)) ct_list in
        let free_index =
          List.filter ~f:(fun (_, ct) -> is_free_var_type ct) id_ct_list
        in
        let pexp_direct_fvs =
          List.map
            ~f:(fun (i, _) ->
              (i, pexp_list_literal ~loc [ pexp_tmp_var ~loc i ]))
            free_index
        in
        let containers =
          List.filter_map
            ~f:(fun (i, ct) ->
              match is_cur_type_container ptype_name.txt ct with
              | Some ld_constr -> Some (i, ld_constr)
              | None -> None)
            id_ct_list
        in
        let pexp_containers =
          List.map
            ~f:(fun (i, ld_constr) ->
              ( i,
                pexp_apply ~loc
                  (pexp_ident ~loc
                     (map_loc lident @@ fv_name
                     @@ map_loc Longident.last_exn ld_constr))
                  [ (Nolabel, self); (Nolabel, pexp_tmp_var ~loc i) ] ))
            containers
        in
        let pexp_gathared_fvs = pexp_direct_fvs @ pexp_containers in
        let args =
          List.filter_map
            ~f:(fun (i, _) ->
              if List.exists ~f:(fun (j, _) -> i == j) pexp_gathared_fvs then
                Some (ppat_tmp_var ~loc i)
              else None)
            id_ct_list
        in
        let ppat_args =
          if List.length args == 0 then None else Some (ppat_tuple ~loc args)
        in
        let pc_lhs = ppat_variant ~loc cd.pcd_name.txt ppat_args in
        let pc_rhs =
          pexp_list_concat ~loc (List.map ~f:snd pexp_gathared_fvs)
        in
        { pc_lhs; pc_guard = None; pc_rhs }
  in
  let body = pexp_match ~loc pexp_input (List.map ~f:mk_match_case cds) in
  pstr_value ~loc Nonrecursive
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
