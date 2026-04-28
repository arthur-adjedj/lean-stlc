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
  theorem step2 {R : α → α → Prop} : R x y → R y z → LeanSubst.Star R x z :=
  fun h₁ h₂ =>
  (.step (.step .refl h₁) h₂)
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

  mod_def extends Term.from_action

  @[simp] mod_def extends Term.from_action_id
  @[simp] mod_def extends Term.from_action_succ
  @[simp] mod_def extends Term.from_acton_re
  mod_def extends Term.from_action_su

  @[simp]
  mod_def extends smap where
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
  @[instance]
  mod_def extends SubstMapStable_Term

  @[simp]
  mod_def extends apply_compose where
    finally all_goals grind

  @[instance]
  mod_def extends SubstMapCompose_Term

  mod_def extends to_ren_is_var
  mod_def extends ren_subst_apply_eq_lift
  mod_def extends ren_subst_apply_eq where
    finally all_goals grind

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
      grind [ActionRed]
    case beta A b b' a a' r1 r2 ih1 ih2 =>
      have lem1 := @ParRed.beta A (b[σ.lift]) (b'[σ'.lift]) (a[σ]) (a'[σ']) (ih1 (subst_red_lift h1)) (ih2 h1)
      simp [Subst.rewrite_lift] at *
      exact lem1
    case app  =>
      simp only [subst_app]
      apply ParRed.app <;> grind only [= subst_zero]
    case lam ih =>
      simp only [subst_lam]
      apply ParRed.lam
      exact ih (subst_red_lift h1)
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
  mod_def Term.is_lam extends _root_.Term.is_lam

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

  inductive SnHeadRed extends SnHeadRed where
    | natRecZero : SN Red PS → SnHeadRed (.natRec P0 PS .zero) P0
    | natRecSucc : SnHeadRed (.natRec P0 PS (.succ n)) (.app (.app PS n) (.natRec P0 PS n))
    | natRecStep : SnHeadRed n n' -> SnHeadRed (.natRec P0 PS n) (.natRec P0 PS n')
  infix:80 " ~>sn " => SnHeadRed

  mod_def extends SnHeadRed.red_compatible where
    finally
      all_goals (try grind only)
      · intro _ _ _ _ r
        cases r
        · right
          constructor
          constructor
          · constructor
            assumption
          · exact Star.step1 ‹_›
        · right
          constructor
          constructor
          · constructor
            rename_i s1 _ r
            cases s1 with | sn s1 =>
            exact s1 _ r
          · exact Star.refl
        · rename_i r; cases r
        · left; rfl
      · intros _ _ _ _ r
        cases r
        · right
          constructor
          constructor
          · constructor
          · exact Star.step1 (Red.app2 (Red.natRec1 ‹_›))
        · right
          constructor
          constructor
          · constructor
          · apply Star.step2
            · exact (Red.app1 (Red.app1 ‹_›))
            · exact (Red.app2 (Red.natRec2 ‹_›))
        · rename_i r; cases r
          right; constructor; constructor
          · constructor
          · apply Star.step2
            · exact Red.app2 (Red.natRec3 ‹_›)
            · exact Red.app1 (Red.app2 ‹_›)
        · left; rfl
      · intro _ _ _ _ snn ihn _ r
        cases r
        · exact .inr ⟨_,.natRecStep snn, Star.step1 (Red.natRec1 ‹_›)⟩
        · exact .inr ⟨_,.natRecStep snn, Star.step1 (Red.natRec2 ‹_›)⟩
        · cases ihn ‹_› with
          | inl => left; grind
          | inr h =>
           obtain ⟨z, ih1, ih2⟩ := h
           exact .inr ⟨_, .natRecStep ih1, .congr3_3 _ _ .natRec .natRec3 ih2⟩
        · cases snn
        · cases snn

  namespace SN
  theorem subterm_natRec : SN Red (.natRec P0 PS n) -> SN Red P0 ∧ SN Red PS ∧ SN Red n := by
    intro h
    generalize e : P0.natRec PS n = t at h
    induction h generalizing P0 PS n <;> cases e
    rename_i a a_ih
    refine ⟨?_,?_,?_⟩ <;> constructor
    · intro _ r
      exact a_ih _ (Red.natRec1 r) rfl |>.1
    · intro _ r
      exact a_ih _ (Red.natRec2 r) rfl |>.2.1
    · intro _ r
      exact a_ih _ (Red.natRec3 r) rfl |>.2.2

  mod_def subterm_app extends SN.subterm_app
  mod_def lam extends SN.lam where
    finally all_goals grind only

  mod_def neutral_app extends SN.neutral_app where
    finally all_goals grind only

  mod_def weak_head_expansion extends SN.weak_head_expansion where
    finally all_goals grind only

  mod_def red_app_preservation extends SN.red_app_preservation where
    finally all_goals grind only

  theorem backward_closure_app :
    SnHeadRed f f' ->
    SN Red f ->
    SN Red a ->
    SN Red (f'.app a) ->
    SN Red (f.app a)
  := by
    intro r1 h1 h2 h3
    induction h1 generalizing f' a
    case _ f h1 ih1 =>
    induction h2
    case _ a h2 ih2 =>
    apply SN.sn; intro y r2
    cases r2
    case _ => cases r1
    case _ f'' r =>
      have lem1 := SnHeadRed.red_compatible r1 r
      cases lem1
      case _ lem1 => subst lem1; apply h3
      case _ lem1 =>
        cases lem1; case _ z lem1 =>
        apply ih1 f'' r lem1.1 (SN.sn h2)
        apply SN.preservation h3
        apply Star.congr2_1 a Term.app Red.app1 lem1.2
    case _ a'' r =>
      apply ih2 a'' r
      apply SN.preservation h3
      apply Star.congr2_2 f' Term.app Red.app2 (Star.step Star.refl r)

  theorem backward_closure_nrec :
    SnHeadRed n n' ->
    SN Red z ->
    SN Red s ->
    SN Red n ->
    SN Red (.natRec z s n') ->
    SN Red (.natRec z s n)
  := by
    intro r1 h1 h2 h3 h4
    induction h3 generalizing z s n'; case _ n hn ihn =>
    induction h2 generalizing z; case _ s hs ihs =>
    induction h1; case _ z hz ihz =>
    apply SN.sn; intro y r2; case _ =>
    cases r2
    case natRecZero => cases r1
    case natRecSucc => cases r1
    case natRec1 z' r =>
      apply ihz z' r
      apply SN.preservation_step h4
      apply Red.natRec1 r
    case natRec2 s' r =>
      apply ihs s' r (SN.sn hz)
      apply SN.preservation_step h4
      apply Red.natRec2 r
    case natRec3 n'' r =>
      have lem1 := SnHeadRed.red_compatible r1 r
      cases lem1
      case _ lem1 => subst lem1; exact h4
      case _ lem1 =>
        obtain ⟨w, lem1, lem2⟩ := lem1
        apply ihn n'' r lem1 (SN.sn hz) (SN.sn hs)
        apply SN.preservation h4
        exact Star.congr3_3 _ _ _ Red.natRec3 lem2

  theorem zero_expansion : SN Red s -> SN Red z -> SN Red (.natRec z s .zero) := by
    intro h1 h2
    induction h2 generalizing s; case _ z hz ihz =>
    induction h1; case _ s hs ihs =>
    apply SN.sn; case _ =>
    intro y r; cases r
    case natRecZero => apply SN.sn hz
    case natRec1 z' r =>
      apply ihz _ r
      apply SN.sn hs
    case natRec2 s' r => apply ihs _ r
    case natRec3 n' r => cases r

  theorem succ_expansion :
    SN Red ((s.app n).app (.natRec z s n)) ->
    SN Red z ->
    SN Red s ->
    SN Red n ->
    SN Red (.natRec z s n.succ)
  := by
    intro h j1 j2 j3
    induction j3 generalizing z s; case _ n j3 ih3 =>
    induction j2 generalizing z; case _ s j2 ih2 =>
    induction j1; case _ z j1 ih1 =>
    apply SN.sn; case _ =>
    intro y r; cases r
    case natRecSucc n => exact h
    case natRec1 z' r =>
      apply ih1 _ r
      apply SN.preservation_step h
      apply Red.app2
      apply Red.natRec1 r
    case natRec2 s' r =>
      apply ih2 _ r
      apply SN.preservation h
      apply Star.congr2 Term.app Red.app1 Red.app2
      apply Star.step .refl (.app1 r)
      apply Star.step .refl
      apply Red.natRec2 r
      apply SN.sn j1
    case natRec3 n' r =>
      cases r; case _ n' r =>
      apply ih3 _ r _ (SN.sn j1) (SN.sn j2)
      apply SN.preservation h
      exact Star.step2 (Red.app1 (Red.app2 r)) (Red.app2 (Red.natRec3 r))

  theorem backward_closure {t' t} : SN Red t' -> SnHeadRed t t' -> SN Red t := by
    intro h r; induction r
    case beta h2 => apply weak_head_expansion h2 h
    case app r ih =>
      have lem := subterm_app h
      apply backward_closure_app r (ih lem.1) lem.2 h
    case natRecZero h2 => apply zero_expansion h2 h
    case natRecSucc =>
      obtain ⟨h1, h2⟩ := subterm_app h
      obtain ⟨h3, h4, h5⟩ := subterm_natRec h2
      apply succ_expansion h h3 h4 h5
    case natRecStep r ih =>
      obtain ⟨h1, h2, h3⟩ := subterm_natRec h
      apply backward_closure_nrec r h1 h2 (ih h3) h
  end SN

  add_mapping _root_.SN.backward_closure => SN.backward_closure

  mod_def extends SnIndices

  inductive SNi extends SNi where
    | zero : SNi .nor .zero
    | succ {n} : SNi .nor n → SNi .nor n.succ
    | natRecNeu : SNi .nor P0 → SNi .nor PS → SNi .neu n → SNi .neu (.natRec P0 PS .zero)
    | natRecZero : SNi .nor PS → SNi .red (.natRec P0 PS .zero, P0)
    | natRecSucc : SNi .red (.natRec P0 PS (.succ n), (PS.app n).app (.natRec P0 PS n))
    | natRecStep : SNi .red (n, n') → SNi .red (.natRec P0 PS n, .natRec P0 PS n')

  namespace SNi
  mod_def extends SNi.SnRenameLemmaType

  mod_def rename extends SNi.rename where
    finally
      all_goals intros
      · exact SNi.zero
      · rename_i ih _
        apply SNi.succ
        apply ih
      · sorry
      · rw [SNi.SnRenameLemmaType,subst_natRec]
        constructor
        rename_i ih _
        apply ih
      · rw [SNi.SnRenameLemmaType,subst_natRec]
        constructor
      · rw [SNi.SnRenameLemmaType,subst_natRec,subst_natRec]
        constructor
        rename_i ih _
        apply ih

  mod_def extends SNi.SnAntiRenameLemmaType

  mod_def extends SNi.antirename where
    finally
    all_goals
      repeat intro
      subst_vars
      try grind
    all_goals sorry

  mod_def extends SNi.SnBetaVarLemmaType

  mod_def extends SNi.beta_var where
    finally
      all_goals try grind (splits := 0) only [SNi.SnBetaVarLemmaType]

  @[simp]
  mod_def extends SNi.SnPropertyWeakenLemmaType

  mod_def extends SNi.property_weaken where
    finally
    all_goals simp
    · sorry
    · intros; constructor
    · intros; constructor
    · intros; apply Red.natRec3; assumption

  mod_def extends SNi.SnSoundLemmaType

  mod_def extends SNi.sound where
    finally
    all_goals try grind (splits := 0) only
    all_goals dsimp only [SNi.SnSoundLemmaType]
    · constructor
      intro _ r
      cases r
    · intro _ b r1
      clear b
      induction r1 with | sn a a_ih =>
      constructor
      intro y ry
      cases ry
      apply a_ih
      assumption
    · sorry
    · intros
      constructor
      assumption
    · intros
      constructor
    · intros
      constructor
      assumption

  end SNi

modular (name := `StrongNorm) (imports := #[`SNi])
  namespace StrongNormalizaton
  mod_def extends StrongNormalizaton.LR where
    matcher match_1 with
      | .nat => SNi .nor

  mod_def extends StrongNormalizaton.GR

  mod_def SemanticTyping extends StrongNormalizaton.SemanticTyping

  notation:170 Γ:170 " ⊨s " t:170 " : " A:170 => SemanticTyping Γ t A

  mod_def extends StrongNormalizaton.monotone where
    finally
      intro _ r h
      simp [StrongNormalizaton.LR] at *
      apply SNi.rename r h

  mod_def extends StrongNormalizaton.cr where
    finally all_goals sorry

  mod_def extends StrongNormalizaton.var

  mod_def extends StrongNormalizaton.fundamental where
    finally
      all_goals intros; intro x h
      · rw [subst_zero,StrongNormalizaton.LR]; exact .zero
      · rw [subst_succ,StrongNormalizaton.LR];
        apply SNi.succ
        rename_i ih
        apply ih _ h
      · rw [subst_natRec,StrongNormalizaton.LR.eq_def]
        split
        · sorry
        · sorry
        · sorry

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
