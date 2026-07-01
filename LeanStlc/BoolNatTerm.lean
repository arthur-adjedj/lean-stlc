import LeanStlc.NatTerm
import LeanStlc.BoolTerm

namespace BoolNatTerm

modular (name := `BoolNatTerm) (imports := #[`BoolTerm.BoolTerm, `NatExt.NatTerm])

  inductive Ty extends NatExt.Ty, BoolTerm.Ty

  -- TODO this should not be needed here
  set_option match.ignoreUnusedAlts true
  mod def Ty.repr extends NatExt.Ty.repr, BoolTerm.Ty.repr

  @[implicit_reducible,instance] -- TODO infer reducibility/instance attribute from what it extends
  mod def instReprTy extends NatExt.instReprTy, BoolTerm.instReprTy

  inductive Term extends NatExt.Term, BoolTerm.Term

  inductive Neutral extends NatExt.Neutral, BoolTerm.Neutral

  mod def Term.repr extends NatExt.Term.repr, BoolTerm.Term.repr

  @[implicit_reducible,instance] -- TODO infer reducibility/instance attribute from what it extends
  mod def instReprTerm extends NatExt.instReprTerm, BoolTerm.instReprTerm

  -- No need to say anything about booleans here, nice !
  mod def Term.is_nat_lit extends NatExt.Term.is_nat_lit

  -- No need to say anything about nats here either !
  mod def Term.is_bool_lit extends BoolTerm.Term.is_bool_lit

  mod def Term.from_action extends NatExt.Term.from_action, BoolTerm.Term.from_action

  @[implicit_reducible,instance] -- TODO infer reducibility/instance attribute from what it extends
  mod def instCoe_SubstActionTerm_Term extends NatExt.instCoe_SubstActionTerm_Term, BoolTerm.instCoe_SubstActionTerm_Term

  @[simp] mod def Term.from_action_id   extends NatExt.Term.from_action_id, BoolTerm.Term.from_action_id
  @[simp] mod def Term.from_action_succ extends NatExt.Term.from_action_succ, BoolTerm.Term.from_action_succ
  @[simp] mod def Term.from_acton_re    extends NatExt.Term.from_acton_re, BoolTerm.Term.from_acton_re
  mod def Term.from_action_su           extends NatExt.Term.from_action_su, BoolTerm.Term.from_action_su

  @[simp]
  mod def smap extends NatExt.smap, BoolTerm.smap

  @[implicit_reducible,instance]
  mod def SubstMap_Term extends NatExt.SubstMap_Term, BoolTerm.SubstMap_Term -- TODO infer reducibility attribute from what it extends

  @[grind =, simp]
  mod def subst_var extends NatExt.subst_var, BoolTerm.subst_var
  @[grind =, simp]
  mod def subst_app extends NatExt.subst_app, BoolTerm.subst_app
  @[grind =, simp]
  mod def subst_lam extends NatExt.subst_lam, BoolTerm.subst_lam
  @[grind =, simp]
  mod def subst_zero extends NatExt.subst_zero
  @[grind =, simp]
  mod def subst_succ extends NatExt.subst_succ
  @[grind =, simp]
  mod def subst_natRec extends NatExt.subst_natRec
  @[grind =, simp]
  mod def subst_true extends BoolTerm.subst_true
  @[grind =, simp]
  mod def subst_false extends BoolTerm.subst_false
  @[grind =, simp]
  mod def subst_ite extends BoolTerm.subst_ite

  @[simp]
  mod def ren_app extends NatExt.ren_app, BoolTerm.ren_app

  @[simp]
  mod def ren_lam extends NatExt.ren_lam, BoolTerm.ren_lam

  @[simp]
  mod def Term.from_action_compose extends NatExt.Term.from_action_compose, BoolTerm.Term.from_action_compose

  mod def apply_id extends NatExt.apply_id, BoolTerm.apply_id

  set_option trace.Modular true in
  mod def apply_stable extends NatExt.apply_stable, BoolTerm.apply_stable
  #check apply_stable._proof_2
