#if OCAML_VERSION < (4, 03, 0)
#define Pcstr_tuple(core_types) core_types
#endif

open Longident
open Location
open Asttypes
open Parsetree
open Ast_helper
open Ast_convenience

let deriver = "map2"
let raise_errorf = Ppx_deriving.raise_errorf

let parse_options options =
  options |> List.iter (fun (name, expr) ->
    match name with
    | _ -> raise_errorf ~loc:expr.pexp_loc "%s does not support option %s" deriver name)

let attr_nobuiltin attrs =
  Ppx_deriving.(attrs |> attr ~deriver "nobuiltin" |> Arg.get_flag ~deriver)

let argn = Printf.sprintf "a%d"
let argm = Printf.sprintf "b%d"
let argl = Printf.sprintf "a%s"
let argk = Printf.sprintf "b%s"

let pattn typs   = List.mapi (fun i _ -> pvar (argn i)) typs
let pattm typs   = List.mapi (fun i _ -> pvar (argm i)) typs
let pattl labels = List.map (fun { pld_name = { txt = n } } -> n, pvar (argl n)) labels
let pattk labels = List.map (fun { pld_name = { txt = n } } -> n, pvar (argk n)) labels

let pconstrrec name fields = pconstr name [precord ~closed:Closed fields]
let  constrrec name fields =  constr name [ record                fields]

let rec expr_of_typ typ =
  match typ with
  | _ when Ppx_deriving.free_vars_in_core_type typ = [] -> 
    [%expr fun (x, _) -> x]
  | { ptyp_desc = Ptyp_constr _ } ->
    let builtin = not (attr_nobuiltin typ.ptyp_attributes) in
    begin match builtin, typ with
    | true, [%type: [%t? typ] list] ->
      [%expr Ppx_deriving_runtime.List.map2p [%e expr_of_typ typ]]
    | true, [%type: [%t? typ] array] ->
      [%expr Ppx_deriving_runtime.Array.map2p [%e expr_of_typ typ]]
    | true, [%type: [%t? typ] option] ->
      [%expr function None,None -> None  
                    | Some x, Some y -> Some ([%e expr_of_typ typ] (x,y))
                    | _, _ -> raise (Invalid_argument "option")]
    | _, { ptyp_desc = Ptyp_constr ({ txt = lid }, args) } ->
      app (Exp.ident (mknoloc (Ppx_deriving.mangle_lid (`Prefix deriver) lid)))
          (List.map expr_of_typ args)
    | _ -> assert false
    end
  | { ptyp_desc = Ptyp_tuple typs } ->
    [%expr fun ([%p ptuple (List.mapi (fun i _ -> pvar (argn i)) typs)], 
                [%p ptuple (List.mapi (fun i _ -> pvar (argm i)) typs)]) ->
      [%e tuple (List.mapi (fun i typ -> app (expr_of_typ typ) 
                                             [tuple [evar (argn i); evar (argm i)]]) typs)]];
  | { ptyp_desc = Ptyp_variant (fields, _, _); ptyp_loc } ->
    let cases =
      fields |> List.map (fun field ->
        match field with
        | Rtag (label, _, true (*empty*), []) ->
          Exp.case 
            [%pat? ([%p Pat.variant label None], [%p Pat.variant label None])] 
            (Exp.variant label None)
        | Rtag (label, _, false, [typ]) ->
          Exp.case 
            [%pat?  ([%p Pat.variant label (Some [%pat? x])],
                     [%p Pat.variant label (Some [%pat? y])])]
            (Exp.variant label (Some [%expr [%e expr_of_typ typ] (x,y)]))
        | Rinherit ({ ptyp_desc = Ptyp_constr (tname, _) } as typ) ->
          Exp.case 
            [%pat? (([%p Pat.type_ tname] as x),
                    ([%p Pat.type_ tname] as y))]
            [%expr [%e expr_of_typ typ] (x,y)]
        | _ ->
          raise_errorf ~loc:ptyp_loc "%s cannot be derived for %s"
                       deriver (Ppx_deriving.string_of_core_type typ))
    in
    let cany = 
      if List.length fields <= 1 then []
      else [Exp.case [%pat? (_, _)] [%expr raise (Invalid_argument "poly variant")]]
    in
    Exp.function_ (cases @ cany)
  | { ptyp_desc = Ptyp_var name } -> evar ("poly_"^name)
  | { ptyp_desc = Ptyp_alias (typ, name); ptyp_loc } -> (* XXX *)
    (*[%expr fun x -> [%e evar ("poly_"^name)] ([%e expr_of_typ typ] x)]*)
    raise_errorf ~loc:ptyp_loc "%s cannot be derived for %s"
                 deriver (Ppx_deriving.string_of_core_type typ)
  | { ptyp_loc } ->
    raise_errorf ~loc:ptyp_loc "%s cannot be derived for %s"
                 deriver (Ppx_deriving.string_of_core_type typ)

let str_of_type ~options ~path ({ ptype_loc = loc } as type_decl) =
  parse_options options;
  let mapper =
    match type_decl.ptype_kind, type_decl.ptype_manifest with
    | Ptype_abstract, Some manifest -> 
      expr_of_typ manifest
    | Ptype_variant constrs, _ ->
      let cases = constrs |>
        List.map (fun { pcd_name = { txt = name' }; pcd_args } ->
          match pcd_args with
          | Pcstr_tuple(typs) ->
            let args = List.mapi 
              (fun i typ -> app (expr_of_typ typ) [tuple [evar (argn i); evar (argm i)]]) typs 
            in
            Exp.case 
              [%pat? ([%p (pconstr name' (pattn typs))],
                      [%p (pconstr name' (pattm typs))])]
              (constr name' args)
#if OCAML_VERSION >= (4, 03, 0)
          | Pcstr_record(labels) ->
            let args = labels |> List.map (fun { pld_name = { txt = n }; pld_type = typ } ->
              n, [%expr [%e expr_of_typ typ] [%e tuple [evar (argl n); evar (argk n)]]]) in
            Exp.case 
              [%pat? ([%p (pconstrrec name' (pattl labels))],
                       [%p (pconstrrec name' (pattk labels))])]
              (constrrec name' args)
#endif
        ) 
      in
      let cany = 
        if List.length constrs <= 1 then [] 
        else [Exp.case [%pat? (_, _)] [%expr raise (Invalid_argument "variant")]] 
      in
      Exp.function_ (cases @ cany)
    | Ptype_record labels, _ ->
      let fields =
        labels |> List.mapi (fun i { pld_name = { txt = name }; pld_type } ->
          name, [%expr [%e expr_of_typ pld_type]
                       ([%e Exp.field (evar "x") (mknoloc (Lident name))],
                        [%e Exp.field (evar "y") (mknoloc (Lident name))])])
      in
      [%expr fun (x,y) -> [%e record fields]]
    | Ptype_abstract, None ->
      raise_errorf ~loc "%s cannot be derived for fully abstract types" deriver
    | Ptype_open, _        ->
      raise_errorf ~loc "%s cannot be derived for open types" deriver
  in
  let polymorphize = Ppx_deriving.poly_fun_of_type_decl type_decl in
  [Vb.mk (pvar (Ppx_deriving.mangle_type_decl (`Prefix deriver) type_decl))
               (polymorphize mapper)]

let sig_of_type ~options ~path type_decl =
  parse_options options;
  (* 0: t * t -> t 
   * 1: ('a * 'b -> 'c) -> 'a t -> 'b t -> 'c t 
   * 2: ('a * 'c -> 'e) -> ('b * 'd -> 'f) -> ('a, 'b) t * ('c, 'd) -> ('e, 'f) t *)
  let typ = Ppx_deriving.core_type_of_type_decl type_decl in
  let free = Ppx_deriving.free_vars_in_core_type typ in
  let gen_vars used = 
    let fresh_var (vars,used) _ = 
      let var = Ppx_deriving.fresh_var used in
      (Typ.var var)::vars, var::used
    in
    let vars, used = List.fold_left fresh_var ([],used) free in
    Array.of_list @@ List.rev vars, used
  in
  let arg1, used = gen_vars [] in
  let arg2, used = gen_vars used in
  let result, _ = gen_vars used in

  let poly_fns = Array.init (List.length free) 
    (fun i -> [%type: [%t arg1.(i)] * [%t arg2.(i)] -> [%t result.(i)]]) in

  let new_typ vars = 
    Ppx_deriving.core_type_of_type_decl 
      { type_decl with 
        ptype_params = 
          List.map2 (fun (_,variance) var -> (var,variance))
            type_decl.ptype_params
            (Array.to_list vars) } 
  in

  let typ = 
    Array.fold_right (fun t acc -> [%type: [%t t] -> [%t acc]]) 
      poly_fns [%type: [%t new_typ arg1] * [%t new_typ arg2] -> [%t new_typ result]] 
  in

  [Sig.value (Val.mk (mknoloc (Ppx_deriving.mangle_type_decl (`Prefix deriver) type_decl)) typ)]
    
let () =
  Ppx_deriving.(register (create deriver
    ~core_type: expr_of_typ
    ~type_decl_str: (fun ~options ~path type_decls ->
      [Str.value Recursive (List.concat (List.map (str_of_type ~options ~path) type_decls))])
    ~type_decl_sig: (fun ~options ~path type_decls ->
      List.concat (List.map (sig_of_type ~options ~path) type_decls))
    ()
  ))
