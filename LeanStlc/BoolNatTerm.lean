import LeanStlc.NatTerm
import LeanStlc.BoolTerm

open LeanSubst


modular (name := `BoolNatTerm) (imports := #[`BoolTerm, `NatTerm])

  namespace BoolNatTerm

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

  mod def apply_stable extends NatExt.apply_stable, BoolTerm.apply_stable


  @[instance]
  mod def SubstMapStable_Term extends NatExt.SubstMapStable_Term, BoolTerm.SubstMapStable_Term

  @[simp]
  mod def apply_compose extends NatExt.apply_compose, BoolTerm.apply_compose

  @[instance]
  mod def SubstMapCompose_Term extends NatExt.SubstMapCompose_Term, BoolTerm.SubstMapCompose_Term

  mod def to_ren_is_var extends NatExt.to_ren_is_var,BoolTerm.to_ren_is_var
  mod def ren_subst_apply_eq_lift extends NatExt.ren_subst_apply_eq_lift, BoolTerm.ren_subst_apply_eq_lift
  mod def ren_subst_apply_eq extends NatExt.ren_subst_apply_eq, BoolTerm.ren_subst_apply_eq

-- modular (imports := #[`Term]) (name := `ParRed)
  inductive ParRed extends NatExt.ParRed, BoolTerm.ParRed where

  attribute [grind] ParRed

  namespace ParRed

  @[grind .]
  mod def refl extends NatExt.ParRed.refl, BoolTerm.ParRed.refl

  @[grind .]
  mod def subst extends NatExt.ParRed.subst, BoolTerm.ParRed.subst

  @[grind .]
  mod def subst_action extends NatExt.ParRed.subst_action, BoolTerm.ParRed.subst_action

  @[grind .]
  mod def subst_red_lift extends NatExt.ParRed.subst_red_lift, BoolTerm.ParRed.subst_red_lift

  theorem hsubst {t t' : Term} {σ σ' : LeanSubst.Subst Term} :
    (∀ x, ActionRed ParRed (σ x) (σ' x)) ->
    ParRed t t' ->
    ParRed t[σ] t'[σ']
  := sorry
  add_mapping NatExt.ParRed.hsubst => ParRed.hsubst
  add_mapping BoolTerm.ParRed.hsubst => ParRed.hsubst


  @[simp, grind]
  mod def complete extends NatExt.ParRed.complete, BoolTerm.ParRed.complete

  -- mod def triangle extends NatExt.ParRed.triangle, BoolTerm.ParRed.triangle

  theorem triangle {t s : Term} : ParRed t s -> ParRed s (complete t) := sorry

  add_mapping NatExt.ParRed.triangle => ParRed.triangle
  add_mapping BoolTerm.ParRed.triangle => ParRed.triangle

  mod def instSubstitutiveTerm extends NatExt.ParRed.instSubstitutiveTerm, BoolTerm.ParRed.instSubstitutiveTerm

  mod def instHasTriangleTerm extends NatExt.ParRed.instHasTriangleTerm, BoolTerm.ParRed.instHasTriangleTerm

  end ParRed

-- modular (name := `Red) (imports := #[`ParRed])
  inductive Red extends NatExt.Red, BoolTerm.Red


  attribute [grind] Red

  namespace Red

  mod def subst extends NatExt.Red.subst, BoolTerm.Red.subst

  @[grind .]
  mod def seq_implies_par extends NatExt.Red.seq_implies_par, BoolTerm.Red.seq_implies_par

  @[grind .]
  mod def seqs_implies_pars extends NatExt.Red.seqs_implies_pars, BoolTerm.Red.seqs_implies_pars
  mod def par_implies_seqs extends NatExt.Red.par_implies_seqs, BoolTerm.Red.par_implies_seqs
  mod def pars_implies_seqs extends NatExt.Red.pars_implies_seqs, BoolTerm.Red.pars_implies_seqs
  mod def pars_action_lift extends NatExt.Red.pars_action_lift, BoolTerm.Red.pars_action_lift
  mod def seqs_action_lift extends NatExt.Red.seqs_action_lift, BoolTerm.Red.seqs_action_lift
  mod def seqs_action_destruct extends NatExt.Red.seqs_action_destruct, BoolTerm.Red.seqs_action_destruct
  mod def pars_action_iff_seqs_action extends NatExt.Red.pars_action_iff_seqs_action, BoolTerm.Red.pars_action_iff_seqs_action

  mod def subst_action extends NatExt.Red.subst_action, BoolTerm.Red.subst_action
  @[grind .]
  mod def subst_red_lift extends NatExt.Red.subst_red_lift, BoolTerm.Red.subst_red_lift

  mod def subst_arg extends NatExt.Red.subst_arg, BoolTerm.Red.subst_arg

  mod def confluence extends NatExt.Red.confluence, BoolTerm.Red.confluence

  mod def instSubstitutiveTerm extends NatExt.Red.instSubstitutiveTerm, BoolTerm.Red.instSubstitutiveTerm

  mod def instHasConfluenceTerm extends NatExt.Red.instHasConfluenceTerm, BoolTerm.Red.instHasConfluenceTerm

  -- TODO fix perf issue here
  -- mod def preservation_of_neutral_step extends NatExt.Red.preservation_of_neutral_step, BoolTerm.Red.preservation_of_neutral_step

  -- Bandaid fix
  theorem preservation_of_neutral_step : Neutral t -> Red t t' -> Neutral t' := sorry
  add_mapping NatExt.Red.preservation_of_neutral_step => preservation_of_neutral_step
  add_mapping BoolTerm.Red.preservation_of_neutral_step => preservation_of_neutral_step

  mod def preservation_of_neutral extends NatExt.Red.preservation_of_neutral, BoolTerm.Red.preservation_of_neutral

  end Red

  inductive Typing extends NatExt.Typing, BoolTerm.Typing

  notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Typing Γ t A

  attribute [grind .] Typing.var Typing.app Typing.lam Typing.zero Typing.succ Typing.natRec Typing.true Typing.false Typing.ite

  mod def typing_renaming_lift extends NatExt.typing_renaming_lift, BoolTerm.typing_renaming_lift

  mod def typing_weaken extends NatExt.typing_weaken, BoolTerm.typing_weaken

  mod def typing_subst_lift extends NatExt.typing_subst_lift, BoolTerm.typing_subst_lift

  mod def typing_subst extends NatExt.typing_subst, BoolTerm.typing_subst

  mod def typing_beta extends NatExt.typing_beta, BoolTerm.typing_beta

  mod def preservation_step extends NatExt.preservation_step, BoolTerm.preservation_step where
    finally
      all_goals grind (splits := 0) only

  mod def preservation extends NatExt.preservation, BoolTerm.preservation

  deriving instance DecidableEq for Ty

  add_mapping NatExt.instDecidableEqTy => instDecidableEqTy
  add_mapping BoolTerm.instDecidableEqTy => instDecidableEqTy

  mod def is_arrow extends NatExt.is_arrow, BoolTerm.is_arrow

  -- @[simp]
  -- mod def infer extends NatExt.infer, BoolTerm.infer

  -- currently fails with a weird unification error: two (synthetic opaque) mvars refuse to unify with a `readOnlyMVarWithBiggerLCtx` trace.
  -- mod def extends NatExt.infer_sound, BoolTerm.infer_sound

  -- modular (name := `Progress) (imports := #[`Red, `Typing])
  @[grind]
  mod def Term.is_lam extends NatExt.Term.is_lam, BoolTerm.Term.is_lam

  inductive Value extends NatExt.Value, BoolTerm.Value

  mod def value_sound extends NatExt.value_sound, BoolTerm.value_sound where
    finally
      all_goals grind (splits := 0) only

  inductive VarSpine extends NatExt.VarSpine, BoolTerm.VarSpine where

  mod def var_spine_not_lam extends NatExt.var_spine_not_lam, BoolTerm.var_spine_not_lam

  mod def progress extends NatExt.progress, BoolTerm.progress where
    finally
      all_goals
        intros
        rename_i h
        cases h
        contradiction

  inductive SnHeadRed extends NatExt.SnHeadRed, BoolTerm.SnHeadRed
  infix:80 " ~>sn " => SnHeadRed

  mod def SnHeadRed.red_compatible extends NatExt.SnHeadRed.red_compatible, BoolTerm.SnHeadRed.red_compatible where
    finally
      all_goals intros;contradiction

  namespace SN
  mod def subterm_ite extends BoolTerm.SN.subterm_ite
  mod def subterm_natRec extends NatExt.SN.subterm_natRec
  mod def subterm_app extends NatExt.SN.subterm_app, BoolTerm.SN.subterm_app
  mod def lam extends NatExt.SN.lam, BoolTerm.SN.lam

  mod def neutral_app extends NatExt.SN.neutral_app, BoolTerm.SN.neutral_app

  mod def neutral_ite extends BoolTerm.SN.neutral_ite where finally
    all_goals intros; contradiction

  mod def neutral_nrec extends NatExt.SN.neutral_nrec where finally
    all_goals intros; contradiction

  mod def weak_head_expansion extends NatExt.SN.weak_head_expansion, BoolTerm.SN.weak_head_expansion

  mod def red_app_preservation extends NatExt.SN.red_app_preservation, BoolTerm.SN.red_app_preservation

  mod def backward_closure_app extends NatExt.SN.backward_closure_app, BoolTerm.SN.backward_closure_app

  mod def backward_closure_ite extends BoolTerm.SN.backward_closure_ite  where finally
    all_goals intros; contradiction

  mod def backward_closure_nrec extends NatExt.SN.backward_closure_nrec  where finally
    all_goals intros; contradiction

  mod def true_expansion  extends BoolTerm.SN.true_expansion  where finally
    all_goals intros; contradiction
  mod def false_expansion extends BoolTerm.SN.false_expansion  where finally
    all_goals intros; contradiction

  mod def zero_expansion extends NatExt.SN.zero_expansion where finally
    all_goals intros; contradiction
  mod def succ_expansion extends NatExt.SN.succ_expansion where finally
    all_goals intros; contradiction

  mod def backward_closure extends NatExt.SN.backward_closure, BoolTerm.SN.backward_closure

  end SN

  @[reducible]
  mod def SnIndices extends NatExt.SnIndices, BoolTerm.SnIndices

  inductive SNi extends NatExt.SNi, BoolTerm.SNi

  namespace SNi
  mod def SnRenameLemmaType extends NatExt.SNi.SnRenameLemmaType, BoolTerm.SNi.SnRenameLemmaType

  mod def rename extends NatExt.SNi.rename, BoolTerm.SNi.rename

  mod def SnAntiRenameLemmaType extends NatExt.SNi.SnAntiRenameLemmaType, BoolTerm.SNi.SnAntiRenameLemmaType

  mod def antirename extends NatExt.SNi.antirename, BoolTerm.SNi.antirename where
    finally
      all_goals
        repeat intro
        subst_vars
        simp at *

  mod def SnBetaVarLemmaType extends NatExt.SNi.SnBetaVarLemmaType, BoolTerm.SNi.SnBetaVarLemmaType

  mod def beta_var extends NatExt.SNi.beta_var, BoolTerm.SNi.beta_var

  @[simp]
  mod def SnPropertyWeakenLemmaType extends NatExt.SNi.SnPropertyWeakenLemmaType, BoolTerm.SNi.SnPropertyWeakenLemmaType

  mod def property_weaken extends NatExt.SNi.property_weaken, BoolTerm.SNi.property_weaken

  mod def SnSoundLemmaType extends NatExt.SNi.SnSoundLemmaType, BoolTerm.SNi.SnSoundLemmaType

  mod def sound extends NatExt.SNi.sound, BoolTerm.SNi.sound where
    finally
      all_goals grind (splits := 0) only

  end SNi

  inductive TypingRen extends NatExt.TypingRen, BoolTerm.TypingRen
  notation:35 Γ:35 "-⟨" r "⟩>" Δ:35 => TypingRen r Γ Δ

  --TODO! add structure extensions, map structure fields accordingly
  theorem TypingRen.act {r : Ren} {Γ Δ : List Ty}  (self : TypingRen r Γ Δ) {x : Nat} {T : Ty} : Γ[x]? = some T → Δ[r x]? = some T := self.1

  add_mapping NatExt.TypingRen.act => TypingRen.act
  add_mapping BoolTerm.TypingRen.act => TypingRen.act

  mod def TypingRen.lift extends NatExt.TypingRen.lift, BoolTerm.TypingRen.lift
  mod def TypingRen.id extends NatExt.TypingRen.id, BoolTerm.TypingRen.id
  mod def TypingRen.succ extends NatExt.TypingRen.succ, BoolTerm.TypingRen.succ
  mod def TypingRen.comp extends NatExt.TypingRen.comp, BoolTerm.TypingRen.comp

  infixr:90 " ∘ "  => TypingRen.comp

  inductive TypingSubst extends NatExt.TypingSubst, BoolTerm.TypingSubst
  notation:35 Γ:35 " -[" σ "]> " Δ:35 => TypingSubst σ Γ Δ

  theorem TypingSubst.act {σ : Subst Term} {Γ Δ : List Ty}  (self : TypingSubst σ Γ Δ) {x : Nat} {T : Ty} : Γ[x]? = some T → Δ ⊢ σ x : T := self.1

  add_mapping NatExt.TypingSubst.act => TypingSubst.act
  add_mapping BoolTerm.TypingSubst.act => TypingSubst.act

  mod def TypingSubst.succ extends NatExt.TypingSubst.succ, BoolTerm.TypingSubst.succ
  -- These are probably not needed
  -- mod def TypingSubst.re extends NatExt.TypingSubst.re, BoolTerm.TypingSubst.re
  -- mod def TypingSubst.su extends NatExt.TypingSubst.su, BoolTerm.TypingSubst.su
  mod def TypingSubst.forget extends NatExt.TypingSubst.forget, BoolTerm.TypingSubst.forget

  mod def Typing.rename extends NatExt.Typing.rename, BoolTerm.Typing.rename
  mod def TypingSubst.lift extends NatExt.TypingSubst.lift, BoolTerm.TypingSubst.lift
  mod def Typing.subst extends NatExt.Typing.subst, BoolTerm.Typing.subst

  @[simp]
  mod def LR extends NatExt.LR, BoolTerm.LR
  @[simp]
  mod def GR extends NatExt.GR, BoolTerm.GR
  @[simp]
  mod def SemanticTyping extends NatExt.SemanticTyping, BoolTerm.SemanticTyping
  notation:170 Γ:170 " ⊨s " t:170 " : " A:170 => SemanticTyping Γ t A

  mod def LR.typing extends NatExt.LR.typing, BoolTerm.LR.typing
  mod def LR.monotone extends NatExt.LR.monotone, BoolTerm.LR.monotone
  mod def GR.forget extends NatExt.GR.forget, BoolTerm.GR.forget

  mod def cr extends NatExt.cr, BoolTerm.cr
  mod def LR.var extends NatExt.LR.var, BoolTerm.LR.var

  mod def GR.from_ren extends NatExt.GR.from_ren, BoolTerm.GR.from_ren
  mod def GR.compose extends NatExt.GR.compose, BoolTerm.GR.compose
  mod def GR.su extends NatExt.GR.su, BoolTerm.GR.su

  mod def LR.nrec_neutral extends NatExt.LR.nrec_neutral
  mod def LR.ite_neutral  extends BoolTerm.LR.ite_neutral

  mod def LR.app extends NatExt.LR.app, BoolTerm.LR.app
modular (name := `Part2) (imports := #[`BoolNatTerm])
#exit
  set_option trace.Modular true in
  mod def LR.nrec' extends NatExt.LR.natRec'
  mod def LR.nrec  extends NatExt.LR.natRec
  mod def LR.ite' extends BoolTerm.LR.ite'
  mod def LR.ite  extends BoolTerm.LR.ite

  mod def fundamental extends NatExt.fundamental, BoolTerm.fundamental
  mod def strong_normalization_inductive extends NatExt.strong_normalization_inductive, BoolTerm.strong_normalization_inductive
  mod def strong_normalization extends NatExt.strong_normalization, BoolTerm.strong_normalization
