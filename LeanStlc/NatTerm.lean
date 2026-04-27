import LeanALaCarte.ModMap
import LeanALaCarte.CheckTranslation
import LeanALaCarte.ExtendInd
import LeanALaCarte.ModularCommand
import LeanALaCarte.ModDef
import LeanStlc.Reduction
import LeanStlc.Term
import LeanStlc.Typing
import LeanStlc.Preservation
import LeanStlc.Infer
import LeanStlc.Progress
import LeanStlc.SNi
import LeanStlc.StrongNorm

open LeanSubst
namespace LeanSubst.Star
  @[grind .]
  theorem step1 {R : α → α → Prop} : R x y → LeanSubst.Star R x y := (.step .refl ·)
end LeanSubst.Star
namespace NatExt

modular (name := `Term)

  inductive Ty extends Ty where
    | nat

  notation "⊤" => Ty.base
  infixr:40 " -t> " => Ty.arrow

  mod_def extends Ty.repr where
    matcher match_1 with
      | .nat => "ℕ"

  @[implicit_reducible,instance] -- TODO infer reducibility/instance attribute from what it extends
  mod_def extends instReprTy

  inductive Term extends Term where
    | zero : Term
    | succ : Term → Term
    -- Nat.rec P0     PS     n
    | natRec : Term → Term → Term → Term

  mod_def extends Term.repr where
    matcher match_1 x y z with
      | .zero => "O"
      | Term.succ n => s!"S ({Term.repr n y})"
      | .natRec P0 PS n => s!"rec ({Term.repr P0 y}) ({Term.repr PS y}) ({Term.repr n y})"

  @[implicit_reducible,instance] -- TODO infer reducibility attribute from what it extends
  mod_def extends instReprTerm

  prefix:max "#" => Term.var
  infixl:66 " :@ " => Term.app
  notation ":λ[" A "] " t => Term.lam A t


  @[simp, grind]
  def Term.is_nat_lit : Term -> Prop
    | .zero | .succ _ => True
    | _ => False

  mod_def extends Term.from_action where
    matcher match_1 with

  @[simp] mod_def extends Term.from_action_id
  @[simp] mod_def extends Term.from_action_succ
  @[simp] mod_def extends Term.from_acton_re
  mod_def extends Term.from_action_su

  mod_def extends smap where
    matcher match_1 with
    matcher match_1 k lf f with
      | .zero => .zero
      | .succ n => .succ (smap k lf f n)
      | .natRec P0 PS n => .natRec (smap k lf f P0) (smap k lf f PS) (smap k lf f n)

  @[implicit_reducible,instance]
  mod_def extends SubstMap_Term -- TODO infer reducibility attribute from what it extends

  @[grind =, simp]
  mod_def extends subst_var
  @[grind =, simp]
  mod_def extends subst_app
  @[grind =, simp]
  mod_def extends subst_lam
  @[grind =, simp]
  theorem subst_zero {σ} : (Term.zero)[σ] = Term.zero := by
    rfl
  @[grind =, simp]
  theorem subst_succ {σ} : (Term.succ n)[σ] = Term.succ n[σ] := by
    rfl
  @[grind =, simp]
  theorem subst_natRec {σ} : (Term.natRec P0 PS n)[σ] = Term.natRec P0[σ] PS[σ] n[σ] := by
    rfl
  @[simp]
  mod_def extends Term.from_action_compose

  mod_def extends apply_id where
    finally
      all_goals
        intros
        simp [*]

  mod_def extends apply_stable where
    finally
      all_goals intros
      · rfl
      · subst_vars
        simp [LeanSubst.SubstMap.smap, smap, *] at *
        grind
      · subst_vars
        next ih_1 ih_2 ih_3 _ =>
          simp [LeanSubst.SubstMap.smap, smap, *] at *
          grind

  mod_def extends SubstMapStable_Term
  @[simp]
  mod_def extends apply_compose where
    finally
      all_goals
        intros
        simp [*] at *

  mod_def extends SubstMapCompose_Term

  -- inductive Neutral extends Neutral where
    -- | const : Neutral (.const n)

  mod_def extends to_ren_is_var
  mod_def extends ren_subst_apply_eq_lift
  mod_def extends ren_subst_apply_eq where
    finally
      all_goals
        intros
        simp [*] at * <;> grind

  @[simp]
  def Term.size : Term → Nat
    | .var _ => 10
    | .natRec P0 PS n => (size P0 + size PS + size n) + 10
    | .zero => 10
    | .succ n => (size n) + 1
    | .lam _ f => (size f) + 10
    | .app f x => (size f + size x) + 10
  termination_by structural t => t

modular (imports := #[`Term]) (name := `ParRed)
  inductive ParRed extends ParRed where
    | zero : ParRed .zero .zero
    | succ : ParRed n₁ n₂ → ParRed n₁.succ n₂.succ
    | natRec {P0 P0' PS PS' n n'} :
      ParRed P0 P0' ->
      ParRed PS PS' ->
      ParRed n n' ->
      ParRed (.natRec P0 PS n) (.natRec P0' PS' n')
    | natRecZero {P0 P0' PS} :
      ParRed P0 P0' ->
      -- ParRed PS PS' ->
      ParRed (.natRec P0 PS .zero) P0'
    | natRecSucc {P0 PS PS' n n' natRec'} :
      ParRed PS PS' ->
      ParRed n n' ->
      ParRed (.natRec P0 PS n) natRec' ->
      ParRed
        (.natRec P0 PS (.succ n))
        (.app (.app PS' n') natRec')

  infix:80 " ~p> " => ParRed
  infix:81 " ~p>* " => Star ParRed
  infix:80 " ~ps> " => ActionRed ParRed
  infix:81 " ~ps>* " => Star (ActionRed ParRed)

  attribute [grind] ParRed

  namespace ParRed

  @[grind .]
  mod_def refl extends ParRed.refl where
    finally all_goals grind

  @[grind .]
  mod_def subst extends ParRed.subst where
    finally all_goals grind

  @[grind .]
  mod_def subst_action extends ParRed.subst_action

  @[grind .]
  mod_def subst_red_lift extends ParRed.subst_red_lift
  theorem hsubst {t t' : Term} {σ σ' : LeanSubst.Subst Term} :
    (∀ x, ActionRed ParRed (σ x) (σ' x)) ->
    ParRed t t' ->
    ParRed t[σ] t'[σ']
  := by
    intros h1 t2
    induction t2 generalizing σ σ' <;> try grind (splits := 3)
    case var =>
      simp only [subst_var, Term.from_action]
      repeat split <;> try grind [ActionRed]
    case beta A b b' a a' r1 r2 ih1 ih2 =>
      have lem1 := @ParRed.beta A (b[σ.lift]) (b'[σ'.lift]) (a[σ]) (a'[σ'])
      simp only [apply_compose, subst_app, subst_lam, Subst.rewrite3_replace,
        Subst.rewrite2] at *
      sorry
    case app  =>
      simp only [subst_app]
      apply ParRed.app <;> grind only [= subst_zero]
    case lam ih =>
      simp only [subst_lam]
      apply ParRed.lam
      sorry
    case natRec =>
      simp only [subst_natRec]
      apply ParRed.natRec <;> grind only
    case natRecSucc =>
      simp only [subst_natRec,subst_app, subst_succ] at *
      apply ParRed.natRecSucc <;> grind only
  add_mapping _root_.ParRed.hsubst => ParRed.hsubst

    @[simp, grind]
  mod_def complete extends ParRed.complete where
    matcher match_1 with
      | .zero => .zero
      | .succ n => .succ (complete n)
      | .natRec P0 _ .zero => complete P0
      | .natRec P0 PS (.succ n) =>
        (complete PS) |>.app (complete n) |>.app (complete (.natRec P0 PS n))
      | .natRec P0 PS n =>
        let P0 := complete P0
        let PS := complete PS
        let n  := complete n
        .natRec P0 PS n

  open LeanSubst in
  theorem triangle {t s : Term} : ParRed t s -> ParRed s (complete t) := by
    intro r; fun_induction complete generalizing s <;> try grind
    case case1  =>
      cases r
      apply hsubst
      intro x; cases x
      apply ActionRed.su; grind
      apply ActionRed.re; grind
      grind

  add_mapping _root_.ParRed.triangle => ParRed.triangle

  mod_def extends ParRed.instSubstitutiveTerm

  mod_def extends ParRed.instHasTriangleTerm
end ParRed

modular (name := `Red) (imports := #[`ParRed])
  inductive Red extends Red where
    | succ : Red n₁ n₂ → Red n₁.succ n₂.succ
    | natRec1 {P0 P0' PS n} :
      Red P0 P0' ->
      Red (.natRec P0 PS n) (.natRec P0' PS n)
    | natRec2 {P0 PS PS' n} :
      Red PS PS' ->
      Red (.natRec P0 PS n) (.natRec P0 PS' n)
    | natRec3 {P0 PS n n'} :
      Red n n' ->
      Red (.natRec P0 PS n) (.natRec P0 PS n')
    | natRecZero {P0 PS} :
      Red (.natRec P0 PS .zero) P0
    | natRecSucc {P0 PS n} :
      Red
        (.natRec P0 PS (.succ n))
        (.app (.app PS n) (.natRec P0 PS n))

  attribute [grind] Red

  namespace Red

  mod_def subst extends Red.subst where
    finally all_goals grind

  @[grind .]
  mod_def extends Red.seq_implies_par where
    finally
      all_goals intros <;> try grind

  @[grind .]
  mod_def extends Red.seqs_implies_pars

  mod_def extends Red.par_implies_seqs where
    finally
      all_goals intros
      · constructor
      · apply LeanSubst.Star.congr1 <;> grind
      · apply LeanSubst.Star.congr3 <;> grind
      · apply LeanSubst.Star.trans
        · apply LeanSubst.Star.step1
          exact Red.natRecZero
        · assumption
      · apply LeanSubst.Star.trans
        · apply LeanSubst.Star.step1
          exact Red.natRecSucc
        · apply LeanSubst.Star.congr2 <;> try grind
          · apply LeanSubst.Star.congr2 <;> grind

  mod_def extends Red.pars_implies_seqs
  mod_def extends Red.pars_action_lift
  mod_def extends Red.seqs_action_lift
  mod_def extends Red.seqs_action_destruct
  mod_def extends Red.pars_action_iff_seqs_action

  mod_def extends Red.subst_action
  @[grind .]
  mod_def extends Red.subst_red_lift

  mod_def subst_arg extends _root_.Red.subst_arg where
    finally
      all_goals intros
      · simp; constructor
      · simp only [subst_succ]
        apply Star.congr1 _ Red.succ
        grind
      · simp only [subst_natRec]
        apply Star.congr3 _ Red.natRec1 Red.natRec2 Red.natRec3 <;> grind

  mod_def confluence extends _root_.Red.confluence

  mod_def extends Red.instSubstitutiveTerm

  mod_def extends Red.instHasConfluenceTerm

  inductive Neutral extends Neutral where
    | natRec : Neutral n → Neutral (.natRec P0 PS n)

  mod_def extends Red.preservation_of_neutral_step where
    finally
      all_goals try grind only
      · intro _ _ _ h1 ih _ r
        cases r <;> first
          | constructor;assumption
          | cases h1; done
          | constructor
            apply ih
            assumption

  mod_def extends Red.preservation_of_neutral

  end Red

modular (name := `Typing) (imports := #[`Term])
  inductive Typing extends Typing where
    | zero  : Typing Γ .zero .nat
    | succ  : Typing Γ n .nat → Typing Γ (.succ n) .nat
    | natRec : Typing Γ P0 A → Typing Γ PS (.nat -t> A -t> A) → Typing Γ n .nat → Typing Γ (.natRec P0 PS n) A
  notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Typing Γ t A

  mod_def extends typing_renaming_lift where
    finally
      all_goals grind only

  mod_def extends typing_weaken where
    finally
      all_goals first | grind only [Ren.apply] | intros
      · constructor
      · rename_i ih _ _ _
        constructor
        apply ih
        assumption
      · rename_i ih1 ih2 ih3 _ _ _
        constructor
        · apply ih1; assumption
        · apply ih2; assumption
        · apply ih3; assumption

  mod_def extends typing_subst_lift where
    finally
      all_goals grind only

  mod_def extends typing_subst where
    finally
      all_goals intros
      · rw [subst_zero]
        constructor
      · rw [subst_succ]
        constructor
        grind only
      · rw [subst_natRec]
        constructor <;>
        grind only

  mod_def extends typing_beta where
    finally
      all_goals grind only

modular (name := `Preservation) (imports := #[`Red, `Typing])
  mod_def extends preservation_step where
    finally
      all_goals (try grind (splits := 1) only) <;> intros
      · grind only [Red,Typing]
      · rename_i r
        cases r <;> first
          | grind (splits := 0) only [Typing]
          | rename_i h _
            cases h
            constructor <;>
            (constructor <;>
            assumption)

  mod_def extends preservation

modular (name := `Infer) (imports := #[`Typing])
  deriving instance DecidableEq for Ty

  add_mapping _root_.instDecidableEqTy => instDecidableEqTy

  mod_def extends is_arrow where
    matcher match_1 with
      | .nat => .none

  @[simp]
  mod_def extends infer where
    matcher match_1 with

    matcher match_3 Γ with
      | .zero => some .nat
      | .succ n => do
        let .nat ← infer Γ n | none
        return .nat
      | .natRec P0 PS n => do
        let .nat ← infer Γ n | none
        let A ← infer Γ P0
        let .nat -t> C -t> D ← infer Γ PS | none
        if A = C ∧ A = D then
          return A
        else none

  -- currently fails with a weird unification error: two (synthetic opaque) mvars refuse to unify with a `readOnlyMVarWithBiggerLCtx` trace.
  -- mod_def extends infer_sound

modular (name := `Progress) (imports := #[`Red, `Typing])
  @[grind]
  mod_def Term.is_lam extends _root_.Term.is_lam where
    matcher match_1 with

  inductive Value extends Value where
    | zero : Value .zero
    | succ : Value n → Value (.succ n)
    | natRec : Value P0 → Value PS → Value n →
      ¬ n.is_nat_lit → Value (.natRec P0 PS n)

  mod_def extends value_sound where
    finally
      all_goals try grind only [Term.is_nat_lit]

  inductive VarSpine extends VarSpine where
    | natRec : Value P0 → Value PS → VarSpine n → VarSpine (.natRec P0 PS n)

  mod_def extends var_spine_not_lam where
    finally
      grind only [Term.is_lam]

  mod_def extends progress where
    finally
      all_goals (try grind only [Value,Term.is_lam])
      · rintro a (h | ⟨t',h⟩)
        · left
          constructor
          assumption
        · right
          exists t'.succ
          constructor
          assumption
      · rintro P0 PS n (hP0 | ⟨P0',hP0⟩) (hPS | ⟨PS',hPS⟩) (hn | ⟨n',hn⟩)
        · by_cases h : n.is_nat_lit
          · unfold Term.is_nat_lit at h
            split at h
            · right
              constructor
              apply Red.natRecZero
            · right
              constructor
              apply Red.natRecSucc
            · contradiction
          · left
            grind only [Value]
        all_goals
          right
          constructor
          first
          | apply Red.natRec1; assumption
          | apply Red.natRec2; assumption
          | apply Red.natRec3; assumption

modular (name := `SNi) (imports := #[`Progress])

  inductive SnHeadRed extends SnHeadRed where --TODO add missing natRec constructor
  infix:80 " ~>sn " => SnHeadRed

  mod_def extends SnHeadRed.red_compatible where
    finally all_goals grind only

  mod_def extends SN.subterm_app
  mod_def extends SN.lam where
    finally all_goals grind only

  mod_def extends SN.neutral_app where
    finally all_goals grind only

  mod_def extends SN.weak_head_expansion where
    finally all_goals grind only

  mod_def extends SN.red_app_preservation where
    finally all_goals grind only

  mod_def extends SN.backward_closure

  mod_def extends SnIndices

  inductive SNi extends SNi where --TODO add missing constructors

  namespace SNi
  mod_def extends SNi.SnRenameLemmaType where
    matcher match_1 with

  mod_def extends SNi.rename

  mod_def extends SNi.SnAntiRenameLemmaType where
    matcher match_1 with

  mod_def extends SNi.antirename where
    finally all_goals sorry

  mod_def extends SNi.SnBetaVarLemmaType where
    matcher match_1 with

  mod_def extends SNi.beta_var where
    finally all_goals sorry

  mod_def extends SNi.SnPropertyWeakenLemmaType where
    matcher match_1 with

  mod_def extends SNi.property_weaken
  mod_def extends SNi.SnSoundLemmaType where
    matcher match_1 with

  mod_def extends SNi.sound where
    finally all_goals sorry

  end SNi

modular (name := `StrongNorm) (imports := #[`SNi])
  namespace StrongNormalizaton
  mod_def extends StrongNormalizaton.LR where
    matcher match_1 with
      | .nat => SNi .nor

  mod_def extends StrongNormalizaton.GR where
    matcher match_1 with

  mod_def SemanticTyping extends StrongNormalizaton.SemanticTyping

  notation:170 Γ:170 " ⊨s " t:170 " : " A:170 => SemanticTyping Γ t A

  mod_def extends StrongNormalizaton.monotone where
    finally sorry

  mod_def extends StrongNormalizaton.cr where
    finally all_goals sorry

  mod_def extends StrongNormalizaton.var

  mod_def extends StrongNormalizaton.fundamental where
    finally all_goals sorry

  end StrongNormalizaton

  mod_def extends strong_normalization_inductive
  mod_def extends strong_normalization
/-DONE
  - Term
  - Reduction
  - Typing
  - Preservation
  - Infer
  - Progress
  TODO
  - SNi
  - WeakNorm
  - StrongNorm
-/
