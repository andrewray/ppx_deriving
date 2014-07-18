open Longident
open Location
open Asttypes
open Parsetree
open Ast_helper
open Ast_convenience

let raise_errorf = Ppx_deriving_host.raise_errorf
let mangle_lid = Ppx_deriving_host.mangle_lid

let () =
  Ppx_deriving_host.register "Show" (fun options type_decls ->
    let argn i = Printf.sprintf "a%d" i in
    let rec derive_typ expr typ =
      let format x = [%expr Format.fprintf fmt [%e str x] [%e expr]] in
      match typ with
      | [%type: int]    -> format "%d"
      | [%type: int32]     | [%type: Int32.t] -> format "%ldl"
      | [%type: int64]     | [%type: Int64.t] -> format "%LdL"
      | [%type: nativeint] | [%type: Nativeint.t] -> format "%ndn"
      | [%type: float]  -> format "%F"
      | [%type: bool]   -> format "%B"
      | [%type: char]   -> format "%C"
      | [%type: string] -> format "%S"
      | [%type: bytes]  -> [%expr Format.fprintf fmt "%S" (Bytes.to_string [%e expr])]
      | { ptyp_desc = Ptyp_tuple typs } ->
        begin match List.mapi (fun i typ -> derive_typ (evar (argn i)) typ) typs with
        | [] -> assert false
        | hd :: tl ->
          [%expr
            let [%p ptuple (List.mapi (fun i _ -> pvar (argn i)) typs)] = [%e expr] in
            Format.pp_print_string fmt "(";
            [%e List.fold_left (fun exp exp' ->
                  [%expr [%e exp]; Format.pp_print_string fmt ", "; [%e exp']])
                hd tl];
            Format.pp_print_string fmt ")"]
        end
      | { ptyp_desc = Ptyp_constr ({ txt = lid }, args) } ->
        app (Exp.ident { txt = mangle_lid ~prefix:"pp_" lid; loc = !default_loc })
            ([%expr fmt] ::
             (List.map (fun typ -> [%expr fun x -> [%e derive_typ [%expr x] typ]]) args) @
             [expr])
      | { ptyp_desc = Ptyp_variant (fields, _, _); ptyp_loc } ->
        let cases =
          fields |> List.map (fun field ->
            match field with
            | Rtag (label, _, true (*empty*), []) ->
              Exp.case (Pat.variant label None)
                       [%expr Format.pp_print_string fmt [%e str ("`" ^ label)]]
            | Rtag (label, _, false, [typ]) ->
              Exp.case (Pat.variant label (Some (pvar "x")))
                       [%expr Format.pp_print_string fmt [%e str ("`" ^ label ^ " ")];
                              [%e derive_typ (evar "x") typ]]
            | Rinherit ({ ptyp_desc = Ptyp_constr (tname, []) } as typ) ->
              Exp.case (Pat.alias (Pat.type_ tname) (mknoloc "x"))
                       (derive_typ (evar "x") typ)
            | _ ->
              raise_errorf ~loc:ptyp_loc "Cannot derive Show for %s"
                           (Ppx_deriving_host.string_of_core_type typ))
        in
        Exp.match_ expr cases
      | { ptyp_desc = Ptyp_alias (typ', _) } -> derive_typ expr typ'
      | { ptyp_loc } ->
        raise_errorf ~loc:ptyp_loc "Cannot derive Show for %s"
                     (Ppx_deriving_host.string_of_core_type typ)
    in
    let derive_type { ptype_name = { txt = name }; ptype_kind; ptype_manifest; ptype_loc } =
      let prettyprinter =
        match ptype_kind, ptype_manifest with
        | Ptype_abstract, Some manifest ->
          [%expr fun fmt x -> [%e derive_typ (evar "x") manifest]]
        | Ptype_variant constrs, _ ->
          let cases =
            constrs |> List.map (fun { pcd_name = { txt = name }; pcd_args } ->
              let result =
                match List.mapi (fun i typ -> derive_typ (evar (argn i)) typ) pcd_args with
                | [] -> [%expr Format.pp_print_string fmt [%e str name]]
                | hd :: [] -> [%expr Format.pp_print_string fmt [%e str (name ^ " ")]; [%e hd]]
                | hd :: tl ->
                  [%expr
                    Format.pp_print_string fmt [%e str (name ^ " (")];
                    [%e List.fold_left (fun exp exp' ->
                          [%expr [%e exp]; Format.pp_print_string fmt ", "; [%e exp']])
                        hd tl];
                    Format.pp_print_string fmt ")"]
              in
              Exp.case (pconstr name (List.mapi (fun i _ -> pvar (argn i)) pcd_args)) result)
          in
          [%expr fun fmt x -> [%e Exp.match_ (evar "x") cases]]
        | Ptype_record labels, _ ->
          assert false
        | Ptype_abstract, None ->
          raise_errorf ~loc:ptype_loc "Cannot derive Show for fully abstract type"
        | Ptype_open, _ ->
          raise_errorf ~loc:ptype_loc "Cannot derive Show for open type"
      in
      let stringprinter = [%expr fun x -> Format.asprintf "%a" [%e evar ("pp_"^name)] x] in
      [Vb.mk (pvar ("pp_"^name))   prettyprinter;
       Vb.mk (pvar ("show_"^name)) stringprinter;]
    in
    [Str.value Recursive (List.concat (List.map derive_type type_decls))])