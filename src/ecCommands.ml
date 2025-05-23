(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcParsetree

module Sid = EcIdent.Sid
module Mx  = EcPath.Mx

(* -------------------------------------------------------------------- *)
exception Restart

(* -------------------------------------------------------------------- *)
type pragma = {
  pm_verbose : bool; (* true  => display goal after each command *)
  pm_g_prall : bool; (* true  => display all open goals *)
  pm_g_prpo  : EcPrinting.prpo_display;
  pm_check   : [`Check | `WeakCheck | `Report];
}

let dpragma = {
  pm_verbose = true  ;
  pm_g_prall = false ;
  pm_g_prpo  = EcPrinting.{ prpo_pr = false; prpo_po = false; };
  pm_check   = `Check;
}

module Pragma : sig
  val get : unit -> pragma
  val set : pragma -> unit
  val upd : (pragma -> pragma) -> unit
end = struct
  let pragma = ref dpragma

  let notify () =
    EcUserMessages.set_ppo
      EcUserMessages.{ ppo_prpo = (!pragma).pm_g_prpo }

  let () = notify ()

  let get () = !pragma
  let set x  = pragma := x; notify ()
  let upd f  = set (f (get ()))
end

let pragma_verbose (b : bool) =
  Pragma.upd (fun pragma -> { pragma with pm_verbose = b; })

let pragma_g_prall (b : bool) =
  Pragma.upd (fun pragma -> { pragma with pm_g_prall = b; })

let pragma_g_pr_display (b : bool) =
  Pragma.upd (fun pragma ->
    { pragma with pm_g_prpo =
        EcPrinting.{ pragma.pm_g_prpo with prpo_pr = b; } })

let pragma_g_po_display (b : bool) =
  Pragma.upd (fun pragma ->
    { pragma with pm_g_prpo =
        EcPrinting.{ pragma.pm_g_prpo with prpo_po = b; } })

let pragma_check mode =
  Pragma.upd (fun pragma -> { pragma with pm_check = mode; })

module Pragmas = struct
  let silent     = "silent"
  let verbose    = "verbose"

  module Proofs = struct
    let check  = "Proofs:check"
    let weak   = "Proofs:weak"
    let report = "Proofs:report"
  end

  module Goals = struct
    let printall = "Goals:printall"
    let printone = "Goals:printone"
  end

  module PrPo = struct
    let prpo_pr_raw = "PrPo:pr:raw"
    let prpo_pr_spl = "PrPo:pr:ands"
    let prpo_po_raw = "PrPo:po:raw"
    let prpo_po_spl = "PrPo:po:ands"
  end

end

exception InvalidPragma of string

let apply_pragma (x : string) =
  match x with
  | x when x = Pragmas.silent           -> pragma_verbose false
  | x when x = Pragmas.verbose          -> pragma_verbose true
  | x when x = Pragmas.Proofs.check     -> pragma_check   `Check
  | x when x = Pragmas.Proofs.weak      -> pragma_check   `WeakCheck
  | x when x = Pragmas.Proofs.report    -> pragma_check   `Report
  | x when x = Pragmas.Goals.printone   -> pragma_g_prall false
  | x when x = Pragmas.Goals.printall   -> pragma_g_prall true
  | x when x = Pragmas.PrPo.prpo_pr_raw -> pragma_g_pr_display false
  | x when x = Pragmas.PrPo.prpo_pr_spl -> pragma_g_pr_display true
  | x when x = Pragmas.PrPo.prpo_po_raw -> pragma_g_po_display false
  | x when x = Pragmas.PrPo.prpo_po_spl -> pragma_g_po_display true
  | x when x = Pragmas.Goals.printall   -> pragma_g_prall true

  | _ -> Printf.eprintf "%s\n%!" x; raise (InvalidPragma x)

(* -------------------------------------------------------------------- *)
module Loader : sig
  type loader

  type kind      = EcLoader.kind
  type idx_t     = EcLoader.idx_t
  type namespace = EcLoader.namespace

  val create  : unit   -> loader
  val forsys  : loader -> loader
  val dup     : ?namespace:EcLoader.namespace -> loader -> loader

  val namespace : loader -> EcLoader.namespace option

  val addidir : ?namespace:namespace -> ?recursive:bool -> string -> loader -> unit
  val aslist  : loader -> ((namespace option * string) * idx_t) list
  val locate  : ?namespaces:namespace option list -> string ->
                  loader -> (namespace option * string * kind) option

  val push      : string -> loader -> unit
  val pop       : loader -> string option
  val context   : loader -> string list
  val incontext : string -> loader -> bool
end = struct
  type loader = {
    (*---*) ld_core      : EcLoader.ecloader;
    mutable ld_stack     : string list;
    (*---*) ld_namespace : EcLoader.namespace option;
  }

  type kind      = EcLoader.kind
  type idx_t     = EcLoader.idx_t
  type namespace = EcLoader.namespace

  module Path = BatPathGen.OfString

  let norm p =
    try  Path.s (Path.normalize_in_tree (Path.p p))
    with Path.Malformed_path -> p

  let create () =
    { ld_core      = EcLoader.create ();
      ld_stack     = [];
      ld_namespace = None; }

  let forsys (ld : loader) =
    { ld_core      = EcLoader.forsys ld.ld_core;
      ld_stack     = ld.ld_stack;
      ld_namespace = None; }

  let dup ?namespace (ld : loader) =
    { ld_core      = EcLoader.dup ld.ld_core;
      ld_stack     = ld.ld_stack;
      ld_namespace =
        match namespace with
        | Some _ -> namespace
        | None   -> ld.ld_namespace; }

  let namespace { ld_namespace = nm } = nm

  let addidir ?namespace ?recursive (path : string) (ld : loader) =
    EcLoader.addidir ?namespace ?recursive path ld.ld_core

  let aslist (ld : loader) =
    EcLoader.aslist ld.ld_core

  let locate ?namespaces (path : string) (ld : loader) =
    EcLoader.locate ?namespaces path ld.ld_core

  let push (p : string) (ld : loader) =
    ld.ld_stack <- norm p :: ld.ld_stack

  let pop (ld : loader) =
    match ld.ld_stack with
    | [] -> None
    | p :: tl -> ld.ld_stack <- tl; Some p

  let context (ld : loader) =
    ld.ld_stack

  let incontext (p : string) (ld : loader) =
    List.mem (norm p) ld.ld_stack
end

(* -------------------------------------------------------------------- *)
type loader = Loader.loader

(* -------------------------------------------------------------------- *)
let process_search scope qs =
  EcScope.Search.search scope qs

(* -------------------------------------------------------------------- *)
let process_locate scope x =
  EcScope.Search.locate scope x

(* -------------------------------------------------------------------- *)
module HiPrinting = struct
  (* ------------------------------------------------------------------ *)
  let pr_glob fmt env pm =
    let ppe = EcPrinting.PPEnv.ofenv env in
    let (p, _) = EcTyping.trans_msymbol env pm in
    let us = EcEnv.NormMp.mod_use env p in
    let (globs, pv) = EcEnv.NormMp.flatten_use us in

    Format.fprintf fmt "Globals [# = %d]:@."
      (Sid.cardinal us.EcEnv.us_gl);
    List.iter (fun id ->
      Format.fprintf fmt "  %s@." (EcIdent.name id))
      globs;

    Format.fprintf fmt "@.";

    Format.fprintf fmt "Prog. variables [# = %d]:@."
      (Mx.cardinal us.EcEnv.us_pv);
    List.iter (fun (xp, _) ->
      let pv = EcTypes.pv_glob xp in
      let ty = EcEnv.Var.by_xpath xp env in
      Format.fprintf fmt "  @[%a : %a@]@."
        (EcPrinting.pp_pv ppe) pv
        (EcPrinting.pp_type ppe) ty)
      pv


  (* ------------------------------------------------------------------ *)
  let pr_goal fmt scope n =
    match EcScope.xgoal scope with
    | None | Some { EcScope.puc_active = None} ->
        EcScope.hierror "no active proof"

    | Some { EcScope.puc_active = Some (puc, _) } -> begin
        match puc.EcScope.puc_jdg with
        | EcScope.PSNoCheck -> ()

        | EcScope.PSCheck pf -> begin
            let hds = EcCoreGoal.all_hd_opened pf in
            let sz  = List.length hds in
            let ppe = EcPrinting.PPEnv.ofenv (EcScope.env scope) in

            if n > sz then
              EcScope.hierror "only %n goal(s) remaining" sz;
            if n <= 0 then
              EcScope.hierror "goal ID must be positive";
            let penv = EcCoreGoal.proofenv_of_proof pf in
            let goal = List.nth hds (n-1) in
            let goal = EcCoreGoal.FApi.get_pregoal_by_id goal penv in
            let goal = (EcEnv.LDecl.tohyps goal.EcCoreGoal.g_hyps,
                        goal.EcCoreGoal.g_concl) in

            Format.fprintf fmt "Printing Goal %d\n\n%!" n;
            EcPrinting.pp_goal ppe (Pragma.get ()).pm_g_prpo
              fmt (goal, `One sz)
        end
    end

  (* ------------------------------------------------------------------ *)
  let pr_axioms (fmt : Format.formatter) (env : EcEnv.env) =
    let ax  = EcEnv.Ax.all ~check:(fun _ ax -> EcDecl.is_axiom ax.ax_kind) env in
    let ppe0 = EcPrinting.PPEnv.ofenv env in
    EcPrinting.pp_by_theory ppe0 (EcPrinting.pp_axiom) fmt ax  

  let pr_hint_solve (fmt : Format.formatter) (env : EcEnv.env) =
    let hint_solve = EcEnv.Auto.all env in
    let hint_solve = List.map (fun (p, mode) ->
      let ax = EcEnv.Ax.by_path p env in
      (p, (ax, mode))
    ) hint_solve in 
    
    let ppe = EcPrinting.PPEnv.ofenv env in
  
    let pp_hint_solve ppe fmt = (fun (p, (ax, mode)) ->
      let mode =
        match mode with
        | `Default -> ""
        | `Rigid -> "(rigid)" in
        Format.fprintf fmt "%a %s" (EcPrinting.pp_axiom ppe) (p, ax) mode
      )
    in
    
    EcPrinting.pp_by_theory ppe pp_hint_solve fmt hint_solve    

  (* ------------------------------------------------------------------ *)
  let pr_hint_rewrite (fmt : Format.formatter) (env : EcEnv.env) =
    let hint_rewrite = EcEnv.BaseRw.all env in

    let ppe = EcPrinting.PPEnv.ofenv env in

    let pp_path =
      EcPrinting.pp_shorten_path ppe
        (fun (p : EcPath.path) (q : EcSymbols.qsymbol) ->
          Option.equal EcPath.p_equal
            (Some p)
            (Option.map fst (EcEnv.Ax.lookup_opt q env))) in

    let pp_hint_rewrite _ppe fmt = (fun (p,  sp) ->
      let elems = EcPath.Sp.ntr_elements sp in
      if List.is_empty elems then
        Format.fprintf fmt "%s (empty)@." (EcPath.basename p)
      else
        Format.fprintf fmt "@[<b 2>%s = @\n%a@]@\n" (EcPath.basename p) 
          (EcPrinting.pp_list "@\n" (fun fmt p -> 
            Format.fprintf fmt "%a" pp_path p))
          (EcPath.Sp.ntr_elements sp)
      )
    in
    
    EcPrinting.pp_by_theory ppe pp_hint_rewrite fmt hint_rewrite

  (* ------------------------------------------------------------------ *)
  let pr_hint_simplify (fmt : Format.formatter) (env : EcEnv.env) =
    let open EcTheory in

    let (hint_simplify: (EcEnv.Reduction.topsym * rule list) list) = EcEnv.Reduction.all env in

    let hint_simplify = List.filter_map (fun (ts, rl) -> 
      match ts with
      | `Path p -> Some (p, rl) 
      | _ -> None
    ) hint_simplify 
    in
    
    let ppe = EcPrinting.PPEnv.ofenv env in
    
    let pp_hint_simplify ppe fmt = (fun (p,  (rls : rule list)) ->
      Format.fprintf fmt "@[<b 2>%s:@\n%a@]" (EcPath.basename p) 
        (EcPrinting.pp_list "@\n" (fun fmt rl ->
          begin match rl.rl_cond with
          | [] -> Format.fprintf fmt "Conditions: None@\n"
          | xs -> Format.fprintf fmt "Conditions: %a@\n" (EcPrinting.pp_list ",@ " (EcPrinting.pp_form ppe)) xs
          end;
          Format.fprintf fmt "Target: %a@\nPattern: %a@\n"
          (EcPrinting.pp_form ppe) rl.rl_tg
          (EcPrinting.pp_rule_pattern ppe) rl.rl_ptn
        ))
        rls
      )
    in
    
    EcPrinting.pp_by_theory ppe pp_hint_simplify fmt hint_simplify
end

(* -------------------------------------------------------------------- *)
let process_pr fmt scope p =
  let env = EcScope.env scope in

  match p with
  | Pr_ty   qs -> EcPrinting.ObjectInfo.pr_ty   fmt env   (unloc qs)
  | Pr_op   qs -> EcPrinting.ObjectInfo.pr_op   fmt env   (unloc qs)
  | Pr_pr   qs -> EcPrinting.ObjectInfo.pr_op   fmt env   (unloc qs)
  | Pr_th   qs -> EcPrinting.ObjectInfo.pr_th   fmt env   (unloc qs)
  | Pr_ax   qs -> EcPrinting.ObjectInfo.pr_ax   fmt env   (unloc qs)
  | Pr_mod  qs -> EcPrinting.ObjectInfo.pr_mod  fmt env   (unloc qs)
  | Pr_mty  qs -> EcPrinting.ObjectInfo.pr_mty  fmt env   (unloc qs)
  | Pr_any  qs -> EcPrinting.ObjectInfo.pr_any  fmt env   (unloc qs)

  | Pr_db (`Rewrite qs) ->
      EcPrinting.ObjectInfo.pr_rw fmt env (unloc qs)

  | Pr_db (`Solve q) ->
      EcPrinting.ObjectInfo.pr_at fmt env (unloc q)

  | Pr_glob pm -> HiPrinting.pr_glob fmt env pm
  | Pr_goal n  -> HiPrinting.pr_goal fmt scope n

  | Pr_axioms -> HiPrinting.pr_axioms fmt env

  | Pr_hint (Some `Simplify) -> HiPrinting.pr_hint_simplify fmt env
  | Pr_hint (Some `Solve) -> HiPrinting.pr_hint_solve fmt env
  | Pr_hint (Some `Rewrite) -> HiPrinting.pr_hint_rewrite fmt env

  | Pr_hint None ->
    let printers = [
      ("Solve"   , (fun fmt -> HiPrinting.pr_hint_solve fmt env));
      ("Simplify", (fun fmt -> HiPrinting.pr_hint_simplify fmt env));
      ("Rewrite" , (fun fmt -> HiPrinting.pr_hint_rewrite fmt env));
    ] in

    List.iter (fun (header, printer) ->
      Format.fprintf fmt "%s hints:@.%t@." header printer
    ) printers

(* -------------------------------------------------------------------- *)
let check_opname_validity (scope : EcScope.scope) (x : string) =
  if EcIo.is_binop x = `Invalid then
    EcScope.notify scope `Warning
      "operator `%s' cannot be used in prefix mode" x;
  if EcIo.is_uniop x = `Invalid then
    EcScope.notify scope `Warning
      "operator `%s' cannot be used in infix mode" x

(* -------------------------------------------------------------------- *)
let process_print scope p =
  process_pr Format.std_formatter scope p

(* -------------------------------------------------------------------- *)
exception Pragma of [`Reset | `Restart]

(* -------------------------------------------------------------------- *)
let rec process_type (scope : EcScope.scope) (tyd : ptydecl located) =
  EcScope.check_state `InTop "type" scope;
  let scope  =  EcScope.Ty.add scope tyd in
  EcScope.notify scope `Info "added type: `%s'" (unloc tyd.pl_desc.pty_name);
  scope

(* -------------------------------------------------------------------- *)
and process_types (scope : EcScope.scope) tyds =
  List.fold_left process_type scope tyds

(* -------------------------------------------------------------------- *)
and process_subtype (scope : EcScope.scope) (subtype : psubtype located) =
  EcScope.check_state `InTop "subtype" scope;
  let scope = EcScope.Ty.add_subtype scope subtype in
  EcScope.notify scope `Info "added subtype: `%s'" (unloc subtype.pl_desc.pst_name);
  scope

(* -------------------------------------------------------------------- *)
and process_typeclass (scope : EcScope.scope) (tcd : ptypeclass located) =
  EcScope.check_state `InTop "type class" scope;
  let scope = EcScope.Ty.add_class scope tcd in
    EcScope.notify scope `Info "added type class: `%s'" (unloc tcd.pl_desc.ptc_name);
    scope

(* -------------------------------------------------------------------- *)
and process_tycinst (scope : EcScope.scope) (tci : ptycinstance located) =
  EcScope.check_state `InTop "type class instance" scope;
  EcScope.Ty.add_instance scope (Pragma.get ()).pm_check tci

(* -------------------------------------------------------------------- *)
and process_module (scope : EcScope.scope) m =
  EcScope.check_state `InTop "module" scope;
  EcScope.Mod.add scope m

(* -------------------------------------------------------------------- *)
and process_interface (scope : EcScope.scope) intf =
  EcScope.check_state `InTop "interface" scope;
  EcScope.ModType.add scope intf

(* -------------------------------------------------------------------- *)
and process_operator (scope : EcScope.scope) (pop : poperator located) =
  EcScope.check_state `InTop "operator" scope;
  let op, axs, scope = EcScope.Op.add scope pop in
  let ppe = EcPrinting.PPEnv.ofenv (EcScope.env scope) in
  List.iter
    (fun { pl_desc = name } ->
      EcScope.notify scope `Info "added operator %s %a"
        name (EcPrinting.pp_added_op ppe) op;
        check_opname_validity scope name)
      (pop.pl_desc.po_name :: pop.pl_desc.po_aliases);
  List.iter (fun s -> EcScope.notify scope `Info "added axiom: `%s'" s) axs;
  scope

(* -------------------------------------------------------------------- *)
and process_procop (scope : EcScope.scope) (pop : pprocop located) =
  EcScope.check_state `InTop "operator" scope;
  EcScope.Op.add_opsem scope pop

(* -------------------------------------------------------------------- *)
and process_predicate (scope : EcScope.scope) (p : ppredicate located) =
  EcScope.check_state `InTop "predicate" scope;
  let op, scope = EcScope.Pred.add scope p in
  let ppe = EcPrinting.PPEnv.ofenv (EcScope.env scope) in
  EcScope.notify scope `Info "added predicate %s %a"
    (unloc p.pl_desc.pp_name) (EcPrinting.pp_added_op ppe) op;
  check_opname_validity scope (unloc p.pl_desc.pp_name);
    scope

(* -------------------------------------------------------------------- *)
and process_notation (scope : EcScope.scope) (n : pnotation located) =
  EcScope.check_state `InTop "notation" scope;
  let scope = EcScope.Notations.add scope n in
    EcScope.notify scope `Info "added notation: `%s'"
      (unloc n.pl_desc.nt_name);
    scope

(* -------------------------------------------------------------------- *)
and process_abbrev (scope : EcScope.scope) (a : pabbrev located) =
  EcScope.check_state `InTop "abbreviation" scope;
  let scope = EcScope.Notations.add_abbrev scope a in
    EcScope.notify scope `Info "added abbrev.: `%s'"
      (unloc a.pl_desc.ab_name);
    scope

(* -------------------------------------------------------------------- *)
and process_axiom (scope : EcScope.scope) (ax : paxiom located) =
  EcScope.check_state `InTop "axiom" scope;
  let (name, scope) = EcScope.Ax.add scope (Pragma.get ()).pm_check ax in
    name |> EcUtils.oiter
      (fun x ->
         match (unloc ax).pa_kind with
         | PAxiom _ -> EcScope.notify scope `Info "added axiom: `%s'" x
         | PLemma _ -> EcScope.notify scope `Info "added lemma: `%s'" x);
    scope

(* -------------------------------------------------------------------- *)
and process_th_open (scope : EcScope.scope) (loca, abs, name) =
  EcScope.check_state `InTop "theory" scope;
  EcScope.Theory.enter scope (if abs then `Abstract else `Concrete) (unloc name) loca

(* -------------------------------------------------------------------- *)
and process_th_close (scope : EcScope.scope) (clears, name) =
  let name = unloc name in
  EcScope.check_state `InTop "theory closing" scope;
  if (fst (EcScope.name scope)) <> name then
    EcScope.hierror
      "active theory has name `%s', not `%s'"
      (fst (EcScope.name scope)) name;
  snd (EcScope.Theory.exit ~clears scope)

(* -------------------------------------------------------------------- *)
and process_th_clear (scope : EcScope.scope) clears =
  EcScope.check_state `InTop "theory clear" scope;
  EcScope.Theory.add_clears clears scope

(* -------------------------------------------------------------------- *)
and process_th_require1 ld scope (nm, (sysname, thname), io) =
  EcScope.check_state `InTop "theory require" scope;

  let sysname, thname = (unloc sysname, omap unloc thname) in
  let thname = odfl sysname thname in

  let nm = omap (fun x -> `Named (unloc x)) nm in
  let nm =
    if   is_none nm && is_some (Loader.namespace ld)
    then [Loader.namespace ld; None]
    else [nm] in

  match Loader.locate ~namespaces:nm sysname ld with
  | None ->
      EcScope.hierror "cannot locate theory `%s'" sysname

  | Some (fnm, filename, kind) ->
      if Loader.incontext filename ld then
        EcScope.hierror "circular requires involving `%s'" sysname;

      let dirname = Filename.dirname filename in
      let subld   = Loader.dup ?namespace:fnm ld in

      Loader.push    filename subld;
      Loader.addidir ?namespace:fnm dirname subld;

      let name = EcScope.{
        rqd_name      = thname;
        rqd_kind      = kind;
        rqd_namespace = fnm;
        rqd_digest    = Digest.file filename;
        rqd_direct    = List.is_empty (Loader.context ld);
      } in

      let loader iscope =
        let i_pragma = Pragma.get () in

        try_finally (fun () ->
          let commands = EcIo.parseall (EcIo.from_file filename) in
          let commands =
            List.fold_left 
              (fun scope g -> process_internal subld scope g.gl_action)
              iscope commands in
          commands)
        (fun () -> Pragma.set i_pragma)
      in

      let kind = match kind with `Ec -> `Concrete | `EcA -> `Abstract in

      let scope = EcScope.Theory.require scope (name, kind) loader in
          match io with
          | None         -> scope
          | Some `Export -> EcScope.Theory.export scope ([], name.EcScope.rqd_name)
          | Some `Import -> EcScope.Theory.import scope ([], name.EcScope.rqd_name)

(* -------------------------------------------------------------------- *)
and process_th_require ld scope (nm, xs, io) =
  List.fold_left
    (fun scope x -> process_th_require1 ld scope (nm, x, io))
    scope xs

(* -------------------------------------------------------------------- *)
and process_th_import (scope : EcScope.scope) (names : pqsymbol list) =
  EcScope.check_state `InTop "theory import" scope;
  List.fold_left EcScope.Theory.import scope (List.map unloc names)

(* -------------------------------------------------------------------- *)
and process_th_export (scope : EcScope.scope) (names : pqsymbol list) =
  EcScope.check_state `InTop "theory export" scope;
  List.fold_left EcScope.Theory.export scope (List.map unloc names)

(* -------------------------------------------------------------------- *)
and process_th_clone (scope : EcScope.scope) thcl =
  EcScope.check_state `InTop "theory cloning" scope;
  EcScope.Cloning.clone scope (Pragma.get ()).pm_check thcl

(* -------------------------------------------------------------------- *)
and process_th_alias (scope : EcScope.scope) (thcl : psymbol * pqsymbol) =
  EcScope.check_state `InTop "theory alias" scope;
  EcScope.Theory.alias scope thcl

  (* -------------------------------------------------------------------- *)
and process_mod_import (scope : EcScope.scope) mods =
  EcScope.check_state `InTop "module var import" scope;
  List.fold_left EcScope.Mod.import scope mods

(* -------------------------------------------------------------------- *)
and process_sct_open (scope : EcScope.scope) name =
  EcScope.check_state `InTop "section opening" scope;
  EcScope.Section.enter scope name

(* -------------------------------------------------------------------- *)
and process_sct_close (scope : EcScope.scope) name =
  EcScope.check_state `InTop "section closing" scope;
  EcScope.Section.exit scope name

(* -------------------------------------------------------------------- *)
and process_tactics (scope : EcScope.scope) t =
  let mode = (Pragma.get ()).pm_check in
  match t with
  | `Actual t -> snd (EcScope.Tactics.process scope mode t)
  | `Proof    -> EcScope.Tactics.proof scope

(* -------------------------------------------------------------------- *)
and process_save (scope : EcScope.scope) ed =
  let (oname, scope) =
    match unloc ed with
    | `Qed   -> EcScope.Ax.save  scope
    | `Admit -> EcScope.Ax.admit scope
    | `Abort -> (None, EcScope.Ax.abort scope)
  in
    oname |> EcUtils.oiter
      (fun x -> EcScope.notify scope `Info "added lemma: `%s'" x);
    scope

(* -------------------------------------------------------------------- *)
and process_realize (scope : EcScope.scope) pr =
  let mode = (Pragma.get ()).pm_check in
  let (name, scope) = EcScope.Ax.realize scope mode pr in
    name |> EcUtils.oiter
      (fun x -> EcScope.notify scope `Info "added lemma: `%s'" x);
    scope

(* -------------------------------------------------------------------- *)
and process_proverinfo scope pi =
  let scope = EcScope.Prover.process scope pi in
    scope

(* -------------------------------------------------------------------- *)
and process_pragma (scope : EcScope.scope) opt =
  match unloc opt with
  | x when x = Pragmas.Proofs.weak    -> pragma_check `WeakCheck
  | x when x = Pragmas.Proofs.check   -> pragma_check `Check
  | x when x = Pragmas.Proofs.report  -> pragma_check `Report

  | "noop"    -> ()
  | "compact" -> Gc.compact ()
  | "reset"   -> raise (Pragma `Reset)
  | "restart" -> raise (Pragma `Restart)

  | x ->
      try  apply_pragma x
      with InvalidPragma _ ->
        EcScope.notify scope `Warning "unknown pragma: `%s'" x

(* -------------------------------------------------------------------- *)
and process_option (scope : EcScope.scope) (name, value) =
  match value with
  | `Bool value when EcLocation.unloc name = EcGState.old_mem_restr ->
    let gs = EcEnv.gstate (EcScope.env scope) in
    EcGState.setflag (unloc name) value gs; scope

  | (`Int _) as value ->
      let gs = EcEnv.gstate (EcScope.env scope) in
      EcGState.setvalue (unloc name) value gs; scope

  | `Bool value -> begin
      try  EcScope.Options.set scope (unloc name) value
      with EcScope.UnknownFlag _ ->
        EcScope.hierror "unknown option: %s" (unloc name)
    end

(* -------------------------------------------------------------------- *)
and process_addrw scope (local, base, names) =
  EcScope.Auto.add_rw scope ~local ~base names

(* -------------------------------------------------------------------- *)
and process_reduction scope name =
  EcScope.Reduction.add_reduction scope name

(* -------------------------------------------------------------------- *)
and process_hint scope hint =
  EcScope.Auto.add_hint scope hint

(* -------------------------------------------------------------------- *)
and process_dump_why3 scope filename =
  EcScope.dump_why3 scope filename; scope

(* -------------------------------------------------------------------- *)
and process_dump scope (source, tc) =
  let open EcCoreGoal in

  let input, (p1, p2) = source.tcd_source in

  let goals, scope  =
    let mode = (Pragma.get ()).pm_check in
     EcScope.Tactics.process scope mode tc
  in

  let wrerror fname =
    EcScope.notify scope `Warning "cannot write `%s'" fname in

  let tactic =
    try  File.read_from_file ~offset:p1 ~length:(p2-p1) input
    with Invalid_argument _ -> "(* failed to read back script *)" in
  let tactic = Printf.sprintf "%s.\n" (String.strip tactic) in

  let ecfname = Printf.sprintf "%s.ec" source.tcd_output in

  (try  File.write_to_file ~output:ecfname tactic
   with Invalid_argument _ -> wrerror ecfname);

  goals |> oiter (fun (penv, (hd, hds)) ->
    let goals =
      List.map
        (fun hd -> EcCoreGoal.FApi.get_pregoal_by_id hd penv)
        (hd :: hds) in

    List.iteri (fun i { g_hyps = hyps; g_concl = concl; } ->
        let ecfname = Printf.sprintf "%s.%d.ec" source.tcd_output i in

        try
          let output  = open_out_bin ecfname in

          try_finally
            (fun () ->
              let fbuf = Format.formatter_of_out_channel output in
              let ppe  = EcPrinting.PPEnv.ofenv (EcEnv.LDecl.toenv hyps) in

              source.tcd_width |> oiter (Format.pp_set_margin fbuf);

              Format.fprintf fbuf "%a@?"
                (EcPrinting.pp_goal ppe (Pragma.get ()).pm_g_prpo)
                ((EcEnv.LDecl.tohyps hyps, concl), `One (-1)))
            (fun () -> close_out output)
        with Sys_error _ -> wrerror ecfname)
      goals);

  scope

(* -------------------------------------------------------------------- *)
and process (ld : Loader.loader) (scope : EcScope.scope) g =
  let loc = g.pl_loc in

  let scope =
    match
      match g.pl_desc with
      | Gtype        t    -> `Fct   (fun scope -> process_types      scope  (List.map (mk_loc loc) t))
      | Gsubtype     t    -> `Fct   (fun scope -> process_subtype    scope  (mk_loc loc t))
      | Gtypeclass   t    -> `Fct   (fun scope -> process_typeclass  scope  (mk_loc loc t))
      | Gtycinstance t    -> `Fct   (fun scope -> process_tycinst    scope  (mk_loc loc t))
      | Gmodule      m    -> `Fct   (fun scope -> process_module     scope  m)
      | Ginterface   i    -> `Fct   (fun scope -> process_interface  scope  i)
      | Goperator    o    -> `Fct   (fun scope -> process_operator   scope  (mk_loc loc o))
      | Gprocop      o    -> `Fct   (fun scope -> process_procop     scope  (mk_loc loc o))
      | Gpredicate   p    -> `Fct   (fun scope -> process_predicate  scope  (mk_loc loc p))
      | Gnotation    n    -> `Fct   (fun scope -> process_notation   scope  (mk_loc loc n))
      | Gabbrev      n    -> `Fct   (fun scope -> process_abbrev     scope  (mk_loc loc n))
      | Gaxiom       a    -> `Fct   (fun scope -> process_axiom      scope  (mk_loc loc a))
      | GthOpen      name -> `Fct   (fun scope -> process_th_open    scope  name)
      | GthClose     info -> `Fct   (fun scope -> process_th_close   scope  info)
      | GthClear     info -> `Fct   (fun scope -> process_th_clear   scope  info)
      | GthRequire   name -> `Fct   (fun scope -> process_th_require ld scope name)
      | GthImport    name -> `Fct   (fun scope -> process_th_import  scope  name)
      | GthExport    name -> `Fct   (fun scope -> process_th_export  scope  name)
      | GthClone     thcl -> `Fct   (fun scope -> process_th_clone   scope  thcl)
      | GthAlias     als  -> `Fct   (fun scope -> process_th_alias   scope  als)
      | GModImport   mods -> `Fct   (fun scope -> process_mod_import scope  mods)
      | GsctOpen     name -> `Fct   (fun scope -> process_sct_open   scope  name)
      | GsctClose    name -> `Fct   (fun scope -> process_sct_close  scope  name)
      | Gprint       p    -> `Fct   (fun scope -> process_print      scope  p; scope)
      | Gsearch      qs   -> `Fct   (fun scope -> process_search     scope  qs; scope)
      | Glocate      x    -> `Fct   (fun scope -> process_locate     scope  x; scope)
      | Gtactics     t    -> `Fct   (fun scope -> process_tactics    scope  t)
      | Gtcdump      info -> `Fct   (fun scope -> process_dump       scope  info)
      | Grealize     p    -> `Fct   (fun scope -> process_realize    scope  p)
      | Gprover_info pi   -> `Fct   (fun scope -> process_proverinfo scope  pi)
      | Gsave        ed   -> `Fct   (fun scope -> process_save       scope  ed)
      | Gpragma      opt  -> `State (fun scope -> process_pragma     scope  opt)
      | Goption      opt  -> `Fct   (fun scope -> process_option     scope  opt)
      | Gaddrw       hint -> `Fct   (fun scope -> process_addrw      scope hint)
      | Greduction   red  -> `Fct   (fun scope -> process_reduction  scope red)
      | Ghint        hint -> `Fct   (fun scope -> process_hint       scope hint)
      | GdumpWhy3    file -> `Fct   (fun scope -> process_dump_why3  scope file)
    with
    | `Fct   f -> Some (f scope)
    | `State f -> f scope; None
  in
    scope

(* -------------------------------------------------------------------- *)
and process_internal
  (ld     : Loader.loader)
  (scope  : EcScope.scope)
  (action : global_action located)
  : EcScope.scope
=
  try  odfl scope (process ld scope action)
  with e -> raise (EcScope.toperror_of_exn ~gloc:(loc action) e)

(* -------------------------------------------------------------------- *)
let loader = Loader.create ()

let addidir ?namespace ?recursive (idir : string) =
  Loader.addidir ?namespace ?recursive idir loader

let loadpath () =
  List.map fst (Loader.aslist loader)

(* -------------------------------------------------------------------- *)
type checkmode = {
  cm_checkall  : bool;
  cm_timeout   : int;
  cm_cpufactor : int;
  cm_nprovers  : int;
  cm_provers   : string list option;
  cm_profile   : bool;
  cm_iterate   : bool;
}

let initial ~checkmode ~boot =
  let checkall  = checkmode.cm_checkall  in
  let profile   = checkmode.cm_profile   in
  let poptions  = { EcScope.Prover.empty_options with
    EcScope.Prover.po_timeout   = Some checkmode.cm_timeout;
    EcScope.Prover.po_cpufactor = Some checkmode.cm_cpufactor;
    EcScope.Prover.po_nprovers  = Some checkmode.cm_nprovers;
    EcScope.Prover.po_provers   = (checkmode.cm_provers, []);
    EcScope.Prover.pl_iterate   = Some (checkmode.cm_iterate);
  } in

  let perv    = (None, (mk_loc _dummy EcCoreLib.i_Pervasive, None), Some `Export) in
  let tactics = (None, (mk_loc _dummy "Tactics", None), Some `Export) in
  let prelude = (None, (mk_loc _dummy "Logic", None), Some `Export) in
  let loader  = Loader.forsys loader in
  let gstate  = EcGState.from_flags [("profile", profile)] in
  let scope   = EcScope.empty gstate in
  let scope   = process_th_require1 loader scope perv in
  let scope   = if boot then scope else
                  List.fold_left (process_th_require1 loader)
                                 scope [tactics; prelude] in

  let scope = EcScope.Prover.set_default scope poptions in
  let scope = if checkall then EcScope.Prover.full_check scope else scope in

  EcScope.freeze scope

(* -------------------------------------------------------------------- *)
type context = {
  ct_level   : int;
  ct_current : EcScope.scope;
  ct_root    : EcScope.scope;
  ct_stack   : (EcScope.scope list) option;
}

let context = ref (None : context option)

let rootctxt ?(undo = true) (scope : EcScope.scope) =
  { ct_level   = 0;
    ct_current = scope;
    ct_root    = scope;
    ct_stack   = if undo then Some [] else None; }

(* -------------------------------------------------------------------- *)
let pop_context context =
  match context.ct_stack with
  | None -> EcScope.hierror "undo stack disabled"
  | Some stack ->
      assert (not (List.is_empty stack));
      { ct_level   = context.ct_level - 1;
        ct_root    = context.ct_root;
        ct_current = List.hd stack;
        ct_stack   = Some (List.tl stack); }

(* -------------------------------------------------------------------- *)
let push_context scope context =
  { ct_level   = context.ct_level + 1;
    ct_root    = context.ct_root;
    ct_current = scope;
    ct_stack   = context.ct_stack
      |> omap (fun st -> context.ct_current :: st); }

(* -------------------------------------------------------------------- *)
let initialize ~restart ~undo ~boot ~checkmode =
  assert (restart || EcUtils.is_none !context);
  if restart then Pragma.set dpragma;
  context := Some (rootctxt ~undo (initial ~checkmode ~boot))

(* -------------------------------------------------------------------- *)
type notifier = EcGState.loglevel -> string Lazy.t -> unit

let addnotifier (notifier : notifier) =
  assert (EcUtils.is_some !context);
  let gstate = EcScope.gstate (oget !context).ct_root in
  ignore (EcGState.add_notifier notifier gstate)

(* -------------------------------------------------------------------- *)
let current () =
  (oget !context).ct_current

(* -------------------------------------------------------------------- *)
let uuid () : int =
  (oget !context).ct_level

(* -------------------------------------------------------------------- *)
let mode () : string =
  match (Pragma.get ()).pm_check with
  | `Check     -> "check"
  | `WeakCheck -> "weakcheck"
  | `Report    -> "report"

(* -------------------------------------------------------------------- *)
let undo (olduuid : int) =
  if olduuid < (uuid ()) then
    for _ = (uuid ()) - 1 downto olduuid do
      context := Some (pop_context (oget !context))
    done

(* -------------------------------------------------------------------- *)
let reset () =
  context := Some (rootctxt (oget !context).ct_root)

(* -------------------------------------------------------------------- *)
let process ?(timed = false) ?(break = false) (g : global_action located) : float option =
  ignore break;

  let current = oget !context in
  let scope   = current.ct_current in

  try
    let (tdelta, oscope) = EcUtils.timed (process loader scope) g in
    oscope |> oiter (fun scope -> context := Some (push_context scope current));
    if timed then
      EcScope.notify scope `Info "time: %f" tdelta;
    Some tdelta
  with
  | Pragma `Reset   -> reset (); None
  | Pragma `Restart -> raise Restart

(* -------------------------------------------------------------------- *)
let check_eco =
  EcEco.check_eco (fun name -> Loader.locate name loader)

(* -------------------------------------------------------------------- *)
module S = EcScope
module L = EcBaseLogic

let pp_current_goal ?(all = false) stream =
  let scope = current () in

  match S.xgoal scope with
  | None -> ()

  | Some { S.puc_active = None; S.puc_cont = ct } ->
      Format.fprintf stream "Remaining lemmas to prove:@\n%!";
      List.iter
        (fun ((_, ax), p, env) ->
           let ppe = EcPrinting.PPEnv.ofenv (EcSection.env env)in
           Format.fprintf stream " %s: %a@\n%!"
             (EcPath.tostring p)
             (EcPrinting.pp_form ppe) ax.EcDecl.ax_spec)
        (fst ct)

  | Some { S.puc_active = Some (puc, _) } -> begin
      match puc.S.puc_jdg with
      | S.PSNoCheck -> ()

      | S.PSCheck pf -> begin
          let ppe = EcPrinting.PPEnv.ofenv (S.env scope) in

          match EcCoreGoal.opened pf with
          | None -> Format.fprintf stream "No more goals@\n%!"

          | Some (n, g) ->
              let get_hc { EcCoreGoal.g_hyps; EcCoreGoal.g_concl } =
                (EcEnv.LDecl.tohyps g_hyps, g_concl)
              in

              if all then
                let subgoals = EcCoreGoal.all_opened pf in
                let subgoals = odfl [] (List.otail subgoals) in
                let subgoals = List.map get_hc subgoals in
                EcPrinting.pp_goal ppe (Pragma.get ()).pm_g_prpo
                  stream (get_hc g, `All subgoals)
              else
                EcPrinting.pp_goal ppe (Pragma.get ()).pm_g_prpo
                  stream (get_hc g, `One n)
      end
  end

let pp_maybe_current_goal stream =
  match (Pragma.get ()).pm_verbose with
  | true  -> pp_current_goal ~all:(Pragma.get ()).pm_g_prall stream
  | false -> ()
