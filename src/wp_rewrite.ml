(******************************************************************************)
(*                  This file is part of Waterproof-lib.                      *)
(*                                                                            *)
(*   Waterproof-lib is free software: you can redistribute it and/or modify   *)
(*    it under the terms of the GNU General Public License as published by    *)
(*     the Free Software Foundation, either version 3 of the License, or      *)
(*                    (at your option) any later version.                     *)
(*                                                                            *)
(*     Waterproof-lib is distributed in the hope that it will be useful,      *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*       MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the         *)
(*               GNU General Public License for more details.                 *)
(*                                                                            *)
(*     You should have received a copy of the GNU General Public License      *)
(*   along with Waterproof-lib. If not, see <https://www.gnu.org/licenses/>.  *)
(*                                                                            *)
(******************************************************************************)

open Genarg
open Ltac_plugin.Tacarg
open Proofview

open CErrors
open Constr
open Equality
open Locus
open Names
open Pp
open Util

(* Rewriting rules *)
type rew_rule = { rew_id : KerName.t;
                  rew_lemma : constr;
                  rew_type: types;
                  rew_pat: constr;
                  rew_ctx: Univ.ContextSet.t;
                  rew_l2r: bool;
                  rew_tac: Genarg.glob_generic_argument option }

module HintIdent =
struct
  type t = rew_rule

  let compare r1 r2 = KerName.compare r1.rew_id r2.rew_id
end

(* Representation/approximation of terms to use in the dnet:
 *
 * - no meta or evar (use ['a pattern] for that)
 *
 * - [Rel]s and [Sort]s are not taken into account (that's why we need
 *   a second pass of linear filterin on the results - it's not a perfect
 *   term indexing structure)
 *)

module DTerm =
struct

  type 't t =
    | DRel
    | DSort
    | DRef    of GlobRef.t
    | DProd
    | DLet
    | DLambda
    | DApp
    | DCase   of case_info
    | DFix    of int array * int
    | DCoFix  of int
    | DInt    of Uint63.t
    | DFloat  of Float64.t
    | DArray

  let compare_ci ci1 ci2 =
    let c = Ind.CanOrd.compare ci1.ci_ind ci2.ci_ind in
    if c = 0 then
      let c = Int.compare ci1.ci_npar ci2.ci_npar in
      if c = 0 then
        let c = Array.compare Int.compare ci1.ci_cstr_ndecls ci2.ci_cstr_ndecls in
        if c = 0 then
          Array.compare Int.compare ci1.ci_cstr_nargs ci2.ci_cstr_nargs
        else c
      else c
    else c

  let compare t1 t2 = match t1, t2 with
  | DRel, DRel -> 0
  | DRel, _ -> -1 | _, DRel -> 1
  | DSort, DSort -> 0
  | DSort, _ -> -1 | _, DSort -> 1
  | DRef gr1, DRef gr2 -> GlobRef.CanOrd.compare gr1 gr2
  | DRef _, _ -> -1 | _, DRef _ -> 1

  | DProd, DProd -> 0
  | DProd, _ -> -1 | _, DProd -> 1

  | DLet, DLet -> 0
  | DLet, _ -> -1 | _, DLet -> 1

  | DLambda, DLambda
  | DApp, DApp -> 0
  | DLambda, _ -> -1 | _, DLambda -> 1
  | DApp, _ -> -1 | _, DApp -> 1

  | DCase ci1, DCase ci2 ->
    compare_ci ci1 ci2
  | DCase _, _ -> -1 | _, DCase _ -> 1

  | DFix (i1, j1), DFix (i2, j2) ->
    let c = Int.compare j1 j2 in
    if c = 0 then
      Array.compare Int.compare i1 i2
    else c
  | DFix _, _ -> -1 | _, DFix _ -> 1

  | DCoFix i1, DCoFix i2 ->
    Int.compare i1 i2
  | DCoFix _, _ -> -1 | _, DCoFix _ -> 1

  | DInt i1, DInt i2 -> Uint63.compare i1 i2

  | DInt _, _ -> -1 | _, DInt _ -> 1

  | DFloat f1, DFloat f2 -> Float64.total_compare f1 f2

  | DFloat _, _ -> -1 | _, DFloat _ -> 1

  | DArray, DArray -> 1

end

(*
 * Terms discrimination nets
 * Uses the general dnet datatype on DTerm.t
 * (here you can restart reading)
 *)

module HintDN :
sig
  type t
  type ident = HintIdent.t

  val empty : t

  (** [add c i dn] adds the binding [(c,i)] to [dn]. [c] can be a
     closed term or a pattern (with untyped Evars). No Metas accepted *)
  val add : constr -> ident -> t -> t

  (** [find_all dn] returns all idents contained in dn *)
  val find_all : t -> ident list

end
=
struct
  module Ident = HintIdent
  module PTerm =
  struct
    type t = unit DTerm.t
    let compare = DTerm.compare
  end
  module TDnet = Dn.Make(PTerm)(Ident)

  type t = TDnet.t

  type ident = HintIdent.t

  open DTerm
  open TDnet

  let pat_of_constr c : (unit DTerm.t * Constr.t list) option =
    let open GlobRef in
    let rec pat_of_constr c = match Constr.kind c with
    | Rel _          -> Some (DRel, [])
    | Sort _         -> Some (DSort, [])
    | Var i          -> Some (DRef (VarRef i), [])
    | Const (c,u)    -> Some (DRef (ConstRef c), [])
    | Ind (i,u)      -> Some (DRef (IndRef i), [])
    | Construct (c,u)-> Some (DRef (ConstructRef c), [])
    | Meta _         -> assert false
    | Evar (i,_)     -> None
    | Case (ci,u1,pms1,c1,_iv,c2,ca)     ->
      let f_ctx (_, p) = p in
      Some (DCase(ci), [f_ctx c1; c2] @ Array.map_to_list f_ctx ca)
    | Fix ((ia,i),(_,ta,ca)) ->
      Some (DFix(ia,i), Array.to_list ta @ Array.to_list ca)
    | CoFix (i,(_,ta,ca))    ->
      Some (DCoFix(i), Array.to_list ta @ Array.to_list ca)
    | Cast (c,_,_)   -> pat_of_constr c
    | Lambda (_,t,c) -> Some (DLambda, [t; c])
    | Prod (_, t, u) -> Some (DProd, [t; u])
    | LetIn (_, c, t, u) -> Some (DLet, [c; t; u])
    | App (f,ca)     ->
      let len = Array.length ca in
      let a = ca.(len - 1) in
      let ca = Array.sub ca 0 (len - 1) in
      Some (DApp, [mkApp (f, ca); a])
    | Proj (p,c) -> pat_of_constr (mkApp (mkConst (Projection.constant p), [|c|]))
    | Int i -> Some (DInt i, [])
    | Float f -> Some (DFloat f, [])
    | Array (_u,t,def,ty) ->
      Some (DArray, Array.to_list t @ [def ; ty])
    in
    pat_of_constr c

  (*
   * Basic primitives
   *)

  let empty = TDnet.empty

  let add (c:constr) (id:Ident.t) (dn:t) =
    (* We used to consider the types of the product as well, but since the dnet
       is only computing an approximation rectified by [filtering] we do not
       anymore. *)
    let (ctx, c) = Term.decompose_prod_assum c in
    let c = TDnet.pattern pat_of_constr c in
    TDnet.add dn c id

  let find_all dn = TDnet.lookup dn (fun () -> Everything) ()

end

type rewrite_db = {
  rdb_hintdn : HintDN.t;
  rdb_order : int KNmap.t;
  rdb_maxuid : int;
}

let empty_rewrite_db = {
  rdb_hintdn = HintDN.empty;
  rdb_order = KNmap.empty;
  rdb_maxuid = 0;
}

let rewtab: rewrite_db String.Map.t ref = ref String.Map.empty

let raw_find_base bas = String.Map.find bas !rewtab

let find_base bas =
  try raw_find_base bas
  with Not_found ->
    user_err
      (str "Rewriting base " ++ str bas ++ str " does not exist.")

let find_rewrites bas =
  let db = find_base bas in
  let sort r1 r2 = Int.compare (KNmap.find r2.rew_id db.rdb_order) (KNmap.find r1.rew_id db.rdb_order) in
  List.sort sort (HintDN.find_all db.rdb_hintdn)

let print_rewrite_hintdb (env: Environ.env) (sigma: Evd.evar_map) (db_name: string) =
  (str "Database " ++ str db_name ++ fnl () ++
           prlist_with_sep fnl
           (fun h ->
             str (if h.rew_l2r then "rewrite -> " else "rewrite <- ") ++
               Printer.pr_lconstr_env env sigma h.rew_lemma ++ str " of type " ++ Printer.pr_lconstr_env env sigma h.rew_type ++
               Option.cata (fun tac -> str " then use tactic " ++
               Pputils.pr_glb_generic env sigma tac) (mt ()) h.rew_tac)
           (find_rewrites db_name))

type raw_rew_rule = (constr Univ.in_universe_context_set * bool * Genarg.raw_generic_argument option) CAst.t

let tclMAP_rev f args =
  List.fold_left (fun accu arg -> Tacticals.tclTHEN accu (f arg)) (Proofview.tclUNIT ()) args

(* Applies all the rules of one base *)
let one_base where tac_main bas =
  let lrul = find_rewrites bas in
  let rewrite dir c tac =
    let c = (EConstr.of_constr c, Tactypes.NoBindings) in
    general_rewrite ~where ~l2r:dir AllOccurrences ~freeze:true ~dep:false ~with_evars:false ~tac:(tac, Naive) c
  in
  let try_rewrite h tc =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let subst, ctx' = UnivGen.fresh_universe_context_set_instance h.rew_ctx in
    let c' = Vars.subst_univs_level_constr subst h.rew_lemma in
    let sigma = Evd.merge_context_set Evd.univ_flexible sigma ctx' in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma) (rewrite h.rew_l2r c' tc)
  end in
  let open Proofview.Notations in
  Proofview.tclProofInfo [@ocaml.warning "-3"] >>= fun (_name, poly) ->
  let eval h =
    let tac = match h.rew_tac with
    | None -> Proofview.tclUNIT ()
    | Some (Genarg.GenArg (Genarg.Glbwit wit, tac)) ->
      let ist = { Geninterp.lfun = Id.Map.empty
                ; poly
                ; extra = Geninterp.TacStore.empty } in
      Ftactic.run (Geninterp.interp wit ist tac) (fun _ -> Proofview.tclUNIT ())
    in
    Tacticals.tclREPEAT_MAIN (Tacticals.tclTHENFIRST (try_rewrite h tac) tac_main)
  in
  let lrul = tclMAP_rev eval lrul in
  Tacticals.tclREPEAT_MAIN (Proofview.tclPROGRESS lrul)

(* The AutoRewrite tactic *)
let autorewrite tac_main lbas =
  Tacticals.tclREPEAT_MAIN (Proofview.tclPROGRESS
    (tclMAP_rev (fun bas -> (one_base None tac_main bas)) lbas))

let autorewrite_multi_in idl tac_main lbas =
  Proofview.Goal.enter begin fun gl ->
  (* let's check at once if id exists (to raise the appropriate error) *)
    let _ = List.map (fun id -> Tacmach.pf_get_hyp id gl) idl in
  Tacticals.tclMAP (fun id ->
    Tacticals.tclREPEAT_MAIN (Proofview.tclPROGRESS
      (tclMAP_rev (fun bas -> (one_base (Some id) tac_main bas)) lbas)))
    idl
  end

let gen_auto_multi_rewrite tac_main lbas cl =
  let try_do_hyps treat_id l =
    autorewrite_multi_in (List.map treat_id l) tac_main lbas
  in
  let concl_tac = (if cl.concl_occs != NoOccurrences then autorewrite tac_main lbas else Proofview.tclUNIT ()) in
  if not (Locusops.is_all_occurrences cl.concl_occs) &&
     cl.concl_occs != NoOccurrences
  then
    let info = Exninfo.reify () in
    Tacticals.tclZEROMSG ~info (str"The \"at\" syntax isn't available yet for the autorewrite tactic.")
  else
    match cl.onhyps with
    | Some [] -> concl_tac
    | Some l -> Tacticals.tclTHENFIRST concl_tac (try_do_hyps (fun ((_,id),_) -> id) l)
    | None ->
      let hyp_tac =
        (* try to rewrite in all hypothesis (except maybe the rewritten one) *)
        Proofview.Goal.enter begin fun gl ->
          let ids = Tacmach.pf_ids_of_hyps gl in
          try_do_hyps (fun id -> id)  ids
        end
      in
      Tacticals.tclTHENFIRST concl_tac hyp_tac

let wp_autorewrite (lbas: string list) (cl: clause) (tac: unit tactic): unit tactic =
  let onconcl = match cl.Locus.concl_occs with NoOccurrences -> false | _ -> true in
  match onconcl,cl.Locus.onhyps with
    | false,Some [_] | true,Some [] | false,Some [] ->
        Proofview.wrap_exceptions (fun () -> gen_auto_multi_rewrite tac lbas cl)
    | _ ->
      let info = Exninfo.reify () in
      Tacticals.tclZEROMSG ~info
        (strbrk "autorewrite .. in .. using can only be used either with a unique hypothesis or on the conclusion.")

(* Same hack as auto hints: we generate an essentially unique identifier for
   rewrite hints. *)
let fresh_key =
  let id = ref 0 in
  fun () ->
    let cur = incr id; !id in
    let lbl = Id.of_string ("_" ^ string_of_int cur) in
    let kn = Lib.make_kn lbl in
    let (mp, _) = KerName.repr kn in
    (* We embed the full path of the kernel name in the label so that
       the identifier should be unique. This ensures that including
       two modules together won't confuse the corresponding labels. *)
    let lbl = Id.of_string_soft (Printf.sprintf "%s#%i"
      (ModPath.to_string mp) cur)
    in
    KerName.make mp (Label.of_id lbl)

(* Functions necessary to the library object declaration *)
let cache_hintrewrite (rbase,lrl) =
  let base = try raw_find_base rbase with Not_found -> empty_rewrite_db in
  let fold accu r = {
    rdb_hintdn = HintDN.add r.rew_pat r accu.rdb_hintdn;
    rdb_order = KNmap.add r.rew_id accu.rdb_maxuid accu.rdb_order;
    rdb_maxuid = accu.rdb_maxuid + 1;
  } in
  let base = List.fold_left fold base lrl in
  rewtab := String.Map.add rbase base !rewtab

type hypinfo = {
  hyp_ty : EConstr.types;
  hyp_pat : EConstr.constr;
}

let decompose_applied_relation env sigma c ctype left2right =
  let find_rel ty =
    (* FIXME: this is nonsense, we generate evars and then we drop the
       corresponding evarmap. This sometimes works because [Term_dnet] performs
       evar surgery via [Termops.filtering]. *)
    let sigma, ty = Clenv.make_evar_clause env sigma ty in
    let (_, args) = Termops.decompose_app_vect sigma ty.Clenv.cl_concl in
    let len = Array.length args in
    if 2 <= len then
      let c1 = args.(len - 2) in
      let c2 = args.(len - 1) in
      Some (if left2right then c1 else c2)
    else None
  in
    match find_rel ctype with
    | Some c -> Some { hyp_pat = c; hyp_ty = ctype }
    | None ->
        let ctx,t' = Reductionops.splay_prod_assum env sigma ctype in (* Search for underlying eq *)
        let ctype = EConstr.it_mkProd_or_LetIn t' ctx in
        match find_rel ctype with
        | Some c -> Some { hyp_pat = c; hyp_ty = ctype }
        | None -> None

let find_applied_relation ?loc env sigma c left2right =
  let ctype = Retyping.get_type_of env sigma (EConstr.of_constr c) in
    match decompose_applied_relation env sigma c ctype left2right with
    | Some c -> c
    | None ->
        user_err ?loc
                    (str"The type" ++ spc () ++ Printer.pr_econstr_env env sigma ctype ++
                       spc () ++ str"of this term does not end with an applied relation.")

(* To add rewriting rules to a base *)
let add_rew_rules (env: Environ.env) (sigma: Evd.evar_map) base (lrul: raw_rew_rule list) =
  let ist = Genintern.empty_glob_sign env in
  let intern tac = snd (Genintern.generic_intern ist tac) in
  let map {CAst.loc;v=((c,ctx),b,t)} =
    let sigma = Evd.merge_context_set Evd.univ_rigid sigma ctx in
    let info = find_applied_relation ?loc env sigma c b in
    let pat = EConstr.Unsafe.to_constr info.hyp_pat in
    let uid = fresh_key () in
    { rew_id = uid; rew_lemma = c; rew_type = EConstr.Unsafe.to_constr info.hyp_ty;
      rew_pat = pat; rew_ctx = ctx; rew_l2r = b;
      rew_tac = Option.map intern t }
  in
  let lrul = List.map map lrul in
  cache_hintrewrite (base,lrul)

(**
  Converts a given hypothesis into a raw rule than can be added to the hint rewrite database    
*)
let to_raw_rew_rule (env: Environ.env) (sigma: Evd.evar_map) (hyp: Constrexpr.constr_expr): (Constr.t Univ.in_universe_context_set * bool * raw_generic_argument option) CAst.t =
  let econstr, context = Constrintern.interp_constr env sigma hyp in
  let constr = EConstr.to_constr sigma econstr in
  let univ_ctx = UState.context_set context in
  let ctx = (DeclareUctx.declare_universe_context ~poly:false univ_ctx; Univ.ContextSet.empty) in
  CAst.make ?loc:(Constrexpr_ops.constr_loc hyp) ((constr, ctx), true, Option.map (in_gen (rawwit wit_ltac)) None)

(**  
  This function will add in the rewrite hint database "core" every hint possible created from the hypothesis
*)
let fill_local_rewrite_database (): unit tactic =
  Goal.enter @@ fun goal ->
    let env = Goal.env goal in
    let sigma = Goal.sigma goal in

    let hyps = List.map (fun decl ->
      Constrexpr_ops.mkIdentC @@ Context.Named.Declaration.get_id decl
    ) (Goal.hyps goal) in

    let new_rules = List.map (to_raw_rew_rule env sigma) hyps in
    List.iter (fun rule ->
      try
        add_rew_rules env sigma "wp_core" [rule];
      with _ -> ()
    ) new_rules;

    Feedback.msg_notice @@ print_rewrite_hintdb env sigma "wp_core";

    tclUNIT ()

let clear_rewrite_database (): unit =
  try
    rewtab := String.Map.remove "wp_core" !rewtab
  with Not_found -> ()