import Gemel.ModMap
import Gemel.CheckTranslation
import Gemel.ExtendInd
import Gemel.ModularCommand
import Gemel.ModDef
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

modular NatTerm
  namespace NatExt

  mod inductive Ty extends Ty where
    | nat

  notation "⊤" => Ty.base
  infixr:40 " -t> " => Ty.arrow

  mod def Ty.repr extends Ty.repr where
    extend match_1 with
      | .nat => "ℕ"

  @[implicit_reducible,instance] -- TODO infer reducibility/instance attribute from what it extends
  mod def instReprTy extends instReprTy

  mod inductive Term extends Term where
    | zero : Term
    | succ : Term → Term
    -- Nat.rec P0     PS     n
    | natRec : Term → Term → Term → Term

  mod inductive Neutral extends Neutral where
    | natRec : Neutral n → Neutral (.natRec P0 PS n)

  mod def Term.repr extends _root_.Term.repr where
    extend match_1 x y z with
      | .zero => "O"
      | Term.succ n => s!"S ({Term.repr n p})"
      | .natRec P0 PS n => s!"rec ({Term.repr P0 p}) ({Term.repr PS p}) ({Term.repr n p})"

  @[implicit_reducible,instance] -- TODO infer reducibility attribute from what it extends
  mod def instReprTerm extends instReprTerm

  prefix:max "#" => Term.var
  infixl:max " :@ " => Term.app
  notation:max ":λ[" A "] " t => Term.lam A t


  @[simp, grind]
  def Term.is_nat_lit : Term -> Prop
    | .zero | .succ _ => True
    | _ => False

  @[coe, grind]
  mod def Term.from_action extends Term.from_action

  @[implicit_reducible,instance]
  mod def instCoe_SubstActionTerm_Term extends instCoe_SubstActionTerm_Term

  @[simp] mod def Term.from_action_id extends Term.from_action_id
  @[simp] mod def Term.from_action_succ extends Term.from_action_succ
  @[simp] mod def Term.from_acton_re extends Term.from_acton_re
  mod def Term.from_action_su extends Term.from_action_su

  @[simp]
  mod def smap extends smap where
    extend match_1 k lf f with
      | .zero => .zero
      | .succ n => .succ (smap k lf f n)
      | .natRec P0 PS n => .natRec (smap k lf f P0) (smap k lf f PS) (smap k lf f n)

  @[implicit_reducible,instance]
  mod def SubstMap_Term extends SubstMap_Term -- TODO infer reducibility attribute from what it extends

  @[grind =, simp]
  mod def subst_var extends subst_var
  @[grind =, simp]
  mod def subst_app extends subst_app
  @[grind =, simp]
  mod def subst_lam extends subst_lam
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
  mod def ren_app extends ren_app

  @[simp]
  mod def ren_lam extends ren_lam

  @[simp]
  mod def Term.from_action_compose extends Term.from_action_compose

  mod def apply_id extends apply_id where
    finally
      all_goals
        intros
        simp [*]

  mod def apply_stable extends apply_stable where
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
  mod def SubstMapStable_Term extends SubstMapStable_Term

  @[simp]
  mod def apply_compose extends apply_compose where
    finally all_goals grind

  @[instance]
  mod def SubstMapCompose_Term extends SubstMapCompose_Term

  mod def to_ren_is_var extends to_ren_is_var
  mod def ren_subst_apply_eq_lift extends ren_subst_apply_eq_lift
  mod def ren_subst_apply_eq extends ren_subst_apply_eq where
    finally all_goals grind

  mod inductive ParRed extends ParRed where
    | zero : ParRed .zero .zero
    | succ : ParRed n₁ n₂ → ParRed n₁.succ n₂.succ
    | natRec {P0 P0' PS PS' n n'} : ParRed P0 P0' -> ParRed PS PS' -> ParRed n n' -> ParRed (.natRec P0 PS n) (.natRec P0' PS' n')
    | natRecZero {P0 P0' PS} : ParRed P0 P0' -> ParRed (.natRec P0 PS .zero) P0'
    | natRecSucc {P0 PS PS' n n' natRec'} : ParRed PS PS' -> ParRed n n' -> ParRed (.natRec P0 PS n) natRec' -> ParRed (.natRec P0 PS (.succ n)) (.app (.app PS' n') natRec')
  attribute [grind] ParRed
  infix:80 " ~p> "   => ParRed
  infix:81 " ~p>* "  => Star ParRed
  infix:80 " ~ps> "  => ActionRed ParRed
  infix:81 " ~ps>* " => Star (ActionRed ParRed)

  namespace ParRed

  @[grind .]
  mod def refl extends ParRed.refl where
    finally all_goals grind

  @[grind .]
  mod def subst extends ParRed.subst where
    finally all_goals grind

  @[grind .]
  mod def subst_action extends ParRed.subst_action

  @[grind .]
  mod def subst_red_lift extends ParRed.subst_red_lift

  theorem hsubst {t t' : Term} {σ σ' : LeanSubst.Subst Term} :
    (∀ x, ActionRed ParRed (σ x) (σ' x)) ->
    ParRed t t' ->
    ParRed t[σ] t'[σ']
  := by
    intros h1 t2
    induction t2 generalizing σ σ' <;> try grind (splits := 3)
    case var =>
      simp only [subst_var]
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

  @[simp, grind] mod def complete extends ParRed.complete where
    extend match_1 with
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

  theorem triangle {t s : Term} : ParRed t s -> ParRed s (complete t) := by
    intro r; fun_induction complete generalizing s <;> try grind
    case case1  =>
      cases r; apply hsubst
      intro x; cases x
      apply ActionRed.su; solve_by_elim
      apply ActionRed.re; solve_by_elim
      grind only [beta]

  add_mapping _root_.ParRed.triangle => ParRed.triangle

  mod def instSubstitutiveTerm extends ParRed.instSubstitutiveTerm

  mod def instHasTriangleTerm extends ParRed.instHasTriangleTerm
  end ParRed

  mod inductive Red extends Red where
    | succ : Red n₁ n₂ → Red n₁.succ n₂.succ
    | natRec1 {P0 P0' PS n} : Red P0 P0' -> Red (.natRec P0 PS n) (.natRec P0' PS n)
    | natRec2 {P0 PS PS' n} : Red PS PS' -> Red (.natRec P0 PS n) (.natRec P0 PS' n)
    | natRec3 {P0 PS n n'} : Red n n' -> Red (.natRec P0 PS n) (.natRec P0 PS n')
    | natRecZero {P0 PS} : Red (.natRec P0 PS .zero) P0
    | natRecSucc {P0 PS n} : Red (.natRec P0 PS (.succ n)) (.app (.app PS n) (.natRec P0 PS n))
  attribute [grind] Red
  namespace Red

  mod def subst extends Red.subst where
    finally all_goals grind

  @[grind .] mod def seq_implies_par extends Red.seq_implies_par where finally
      all_goals intros <;> try grind

  @[grind .] mod def seqs_implies_pars extends Red.seqs_implies_pars

  mod def par_implies_seqs extends Red.par_implies_seqs where finally
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

  mod def pars_implies_seqs extends Red.pars_implies_seqs
  mod def pars_action_lift extends Red.pars_action_lift
  mod def seqs_action_lift extends Red.seqs_action_lift
  mod def seqs_action_destruct extends Red.seqs_action_destruct
  mod def pars_action_iff_seqs_action extends Red.pars_action_iff_seqs_action

  mod def subst_action extends Red.subst_action
  @[grind .]
  mod def subst_red_lift extends Red.subst_red_lift

  mod def subst_arg extends _root_.Red.subst_arg where finally
    all_goals intros
    · simp; constructor
    · simp only [subst_succ]
      apply Star.congr1 _ Red.succ
      grind
    · simp only [subst_natRec]
      apply Star.congr3 _ Red.natRec1 Red.natRec2 Red.natRec3 <;> grind

  mod def confluence extends _root_.Red.confluence

  mod def instSubstitutiveTerm extends Red.instSubstitutiveTerm

  mod def instHasConfluenceTerm extends Red.instHasConfluenceTerm

  mod def preservation_of_neutral_step extends Red.preservation_of_neutral_step where finally
      all_goals try intro; simp at *
      intro _ _ _ h1 ih _ r
      cases r <;> first
        | constructor;assumption
        | cases h1; done
        | constructor
          apply ih
          assumption

  mod def preservation_of_neutral extends Red.preservation_of_neutral

  end Red

-- modular (name := `Typing) (imports := #[`Term])
  mod inductive Typing extends Typing where
    | zero  : Typing Γ .zero .nat
    | succ  : Typing Γ n .nat → Typing Γ (.succ n) .nat
    | natRec : Typing Γ P0 A → Typing Γ PS (Ty.nat.arrow (A.arrow A)) → Typing Γ n .nat → Typing Γ (.natRec P0 PS n) A
  scoped notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Typing Γ t A

  attribute [grind .] Typing.var Typing.app Typing.lam Typing.zero Typing.succ Typing.natRec

  mod def typing_renaming_lift extends typing_renaming_lift where finally all_goals grind only

  mod def typing_weaken extends typing_weaken where finally
    all_goals first | simp [Ren.apply,SubstMap.smap,smap] <;> grind

  mod def typing_subst_lift extends typing_subst_lift where finally
      all_goals grind only

  mod def typing_subst extends typing_subst where finally
      all_goals grind

  mod def typing_beta extends typing_beta where finally
      all_goals grind only

  mod def preservation_step extends preservation_step where finally
      all_goals (try simp) <;> (intros; rename_i r)
      · cases r
      · cases r
        constructor
        rename_i ih _ _
        apply ih
        assumption
      · cases r
        case natRecSucc =>
          rename_i h _
          cases h
          constructor <;>
          (constructor <;>
            assumption)
        all_goals solve_by_elim

  mod def preservation extends preservation
  deriving instance DecidableEq for Ty

  add_mapping _root_.instDecidableEqTy => instDecidableEqTy

  mod def is_arrow extends is_arrow where
    extend match_1 with
      | .nat => .none

  @[simp]
  mod def infer extends infer where
    extend match_3 Γ with
      | .zero => some .nat
      | .succ n => do
        let .nat ← infer Γ n | none
        return .nat
      | .natRec P0 PS n => do
        let .nat ← infer Γ n | none
        let A ← infer Γ P0
        let Ty.arrow .nat (Ty.arrow C D) ← infer Γ PS | none
        if A = C ∧ A = D then
          return A
        else none

  @[grind] mod def Term.is_lam extends _root_.Term.is_lam

  mod inductive Value extends Value where
    | zero : Value .zero
    | succ : Value n → Value (.succ n)
    | natRec : Value P0 → Value PS → Value n → ¬ n.is_nat_lit → Value (.natRec P0 PS n)

  mod def value_sound extends value_sound where finally
      all_goals try grind only [Term.is_nat_lit]

  mod inductive VarSpine extends VarSpine where
    | natRec : Value P0 → Value PS → VarSpine n → VarSpine (.natRec P0 PS n)

  mod def var_spine_not_lam extends var_spine_not_lam where finally
      grind only [Term.is_lam]

  mod def progress extends progress where finally
      all_goals (try grind (splits := 0) only [Value,Term.is_lam])
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
          · cases n
            case zero =>
              right
              constructor
              apply Red.natRecZero
            case succ =>
              right
              constructor
              apply Red.natRecSucc
            all_goals contradiction
          · left; constructor <;> assumption
        all_goals
          right; constructor
          first
          | apply Red.natRec1; assumption
          | apply Red.natRec2; assumption
          | apply Red.natRec3; assumption

  mod inductive SnHeadRed extends SnHeadRed where
    | natRecZero : SN Red PS → SnHeadRed (.natRec P0 PS .zero) P0
    | natRecSucc : SnHeadRed (.natRec P0 PS (.succ n)) (.app (.app PS n) (.natRec P0 PS n))
    | natRecStep : SnHeadRed n n' -> SnHeadRed (.natRec P0 PS n) (.natRec P0 PS n')
  infix:80 " ~>sn " => SnHeadRed

  mod def SnHeadRed.red_compatible extends SnHeadRed.red_compatible where finally
      all_goals (try (intros;contradiction))
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

  mod def subterm_app extends SN.subterm_app
  mod def lam extends SN.lam where
    finally all_goals grind only

  mod def neutral_app extends SN.neutral_app where
    finally all_goals grind only

  theorem neutral_nrec : Neutral n -> SN Red z -> SN Red s -> SN Red n -> SN Red (Term.natRec z s n) := by
    intro nh j1 j2 j3
    induction j3 generalizing z s; case _ n h1 ih1 =>
    induction j2 generalizing z; case _ s h2 ih2 =>
    induction j1; case _ z h3 ih3 =>
    apply SN.sn; case _ =>
    intro y r; cases r
    case natRecZero => cases nh
    case natRecSucc => cases nh
    case natRec1 z' r => apply ih3 _ r
    case natRec2 s' r => apply ih2 _ r (.sn h3)
    case natRec3 n' r =>
      apply ih1 _ r _ (.sn h3) (.sn h2)
      apply Red.preservation_of_neutral_step nh r

  mod def weak_head_expansion extends SN.weak_head_expansion where
    finally all_goals grind only

  mod def red_app_preservation extends SN.red_app_preservation where
    finally all_goals grind only

  theorem backward_closure_app : SnHeadRed f f' -> SN Red f -> SN Red a -> SN Red (f'.app a) -> SN Red (f.app a) := by
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

  theorem backward_closure_nrec : SnHeadRed n n' -> SN Red z -> SN Red s -> SN Red n -> SN Red (.natRec z s n') -> SN Red (.natRec z s n) := by
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

  theorem succ_expansion : SN Red ((s.app n).app (.natRec z s n)) -> SN Red z -> SN Red s -> SN Red n -> SN Red (.natRec z s n.succ) := by
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

  @[reducible]
  mod def SnIndices extends SnIndices

  mod inductive SNi extends SNi where
    | zero : SNi .nor .zero
    | succ {n} : SNi .nor n → SNi .nor n.succ
    | natRecNeu : SNi .nor P0 → SNi .nor PS → SNi .neu n → SNi .neu (.natRec P0 PS n)
    | natRecZero : SNi .nor PS → SNi .red (.natRec P0 PS .zero, P0)
    | natRecSucc : SNi .red (.natRec P0 PS (.succ n), (PS.app n).app (.natRec P0 PS n))
    | natRecStep : SNi .red (n, n') → SNi .red (.natRec P0 PS n, .natRec P0 PS n')

  namespace SNi
  mod def SnRenameLemmaType extends SNi.SnRenameLemmaType

  mod def rename extends SNi.rename where finally
      all_goals intros
      · exact SNi.zero
      · rename_i ih _
        apply SNi.succ
        apply ih
      · simp only [SNi.SnRenameLemmaType,subst_natRec] at *
        constructor <;> grind only
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

  mod def SnAntiRenameLemmaType extends SNi.SnAntiRenameLemmaType

  mod def antirename extends SNi.antirename where finally
    all_goals
      repeat intro
      subst_vars
      try simp at *
    · rename_i z e
      cases z <;> simp only [subst_var,subst_app,subst_lam,subst_zero, subst_succ,subst_natRec] at e <;> try cases e
      exact SNi.zero
    · rename_i a a_ih _ z e
      cases z <;> simp only [subst_var,subst_app,subst_lam,subst_zero, subst_succ,subst_natRec] at e <;> try cases e
      apply SNi.succ
      apply a_ih _ _ rfl
    · rename_i P0_ih PS_ih n_ih  _ z e
      cases z <;> simp only [subst_var,subst_app,subst_lam,subst_zero, subst_succ,subst_natRec] at e <;> try cases e
      apply SNi.natRecNeu
      · apply P0_ih _ _ rfl
      · apply PS_ih _ _ rfl
      · apply n_ih _ _ rfl
    · rename_i P0_ih PS_ih _ z e
      cases z <;> simp only [subst_var,subst_app,subst_lam,subst_zero, subst_succ,subst_natRec] at e <;> try cases e
      rename_i n
      cases n <;> simp only [subst_var,subst_app,subst_lam,subst_zero, subst_succ,subst_natRec] at e <;> cases e
      refine ⟨_, rfl, ?_⟩
      apply natRecZero
      apply PS_ih _ _ rfl
    · rename_i P0_ih PS_ih r z e
      cases z <;> simp only [subst_var,subst_app,subst_lam,subst_zero, subst_succ,subst_natRec] at e <;> try cases e
      rename_i P0 PS n
      cases n <;> simp only [subst_var,subst_app,subst_lam,subst_zero, subst_succ,subst_natRec] at e <;> cases e
      rename_i n
      refine ⟨(PS.app n).app (P0.natRec PS n), by simp, ?_⟩
      apply natRecSucc
    · rename_i snn n_ih r z e
      cases z <;> simp only [subst_var,subst_app,subst_lam,subst_zero, subst_succ,subst_natRec] at e <;> cases e
      rename_i n P0 PS k
      have ⟨w,e,_⟩ := n_ih r _ rfl
      cases e
      refine ⟨.natRec P0 PS w, by simp, ?_⟩
      apply natRecStep
      assumption

  mod def SnBetaVarLemmaType extends SNi.SnBetaVarLemmaType

  mod def beta_var extends SNi.beta_var where finally
      all_goals try grind (splits := 0) only [SNi.SnBetaVarLemmaType]

  @[simp]
  mod def SnPropertyWeakenLemmaType extends SNi.SnPropertyWeakenLemmaType

  mod def property_weaken extends SNi.property_weaken where finally
    all_goals simp
    · intros; constructor; assumption
    · intros; constructor
    · intros; constructor
    · intros; apply Red.natRec3; assumption

  mod def SnSoundLemmaType extends SNi.SnSoundLemmaType

  mod def sound extends SNi.sound where finally
    all_goals try grind (splits := 0) only
    all_goals dsimp only [SNi.SnSoundLemmaType]
    · constructor
      intro _ r
      cases r
    · intro _ b r1
      clear b
      induction r1 with | sn _ a_ih =>
      constructor
      intro y ry
      cases ry
      apply a_ih
      assumption
    · intros
      apply SN.neutral_nrec <;> try assumption
      apply SNi.property_weaken (v := .neu)
      assumption
    · intros
      constructor
      assumption
    · intros
      constructor
    · intros
      solve_by_elim

  end SNi
modular end _root_.NatTerm
structure TypingRen (r : Ren) (Γ Δ : List Ty) where
  act : ∀ {x T}, Γ[x]? = some T -> Δ[r x]? = some T

notation:35 Γ:35 " -⟨" r "⟩> " Δ:35 => TypingRen r Γ Δ

theorem TypingRen.lift {Γ Δ : List Ty} A {r : Ren} : Γ -⟨r⟩> Δ -> A::Γ -⟨r.lift⟩> A::Δ := by
  intro h; apply mk; intro x T j
  cases x <;> simp [Ren.lift] at *
  exact j; case _ x =>
  apply h.act j

theorem TypingRen.id : X -⟨id⟩> X := by
  apply mk; intro x T h; exact h

theorem TypingRen.succ : X -⟨(· + 1)⟩> A::X := by
  apply mk; intro x T h; exact h

theorem TypingRen.comp : X -⟨r1⟩> Y -> Y -⟨r2⟩> Z -> X -⟨r2 ∘ r1⟩> Z := by
  intro j1 j2; apply mk; intro x T h; simp
  apply j2.act (j1.act h)

infixr:90 " ∘ "  => TypingRen.comp

structure TypingSubst (σ : Subst Term) (Γ Δ : List Ty) where
  act : ∀ {x T}, Γ[x]? = some T -> Δ ⊢ σ x : T

notation:35 Γ:35 " -[" σ "]> " Δ:35 => TypingSubst σ Γ Δ

theorem TypingSubst.succ : X -[+1]> A::X := by
  apply mk
  intro x T h; simp
  apply Typing.var; exact h

theorem TypingSubst.re (j : Δ[y]? = some A) (m : Γ -[σ]> Δ) : A::Γ -[re y::σ]> Δ :=
  mk (λ {x} {T} h =>
    match x with
    | 0 => .var $ cast (by simp at h; rw [h]) j
    | x + 1 => m.act h)

theorem TypingSubst.su {a : Term} (j : Δ ⊢ a : A) (m : Γ -[σ]> Δ) : A::Γ -[su a::σ]> Δ :=
  mk (λ {x} {T} h =>
    match x with
    | 0 => cast (by simp; grind) j
    | x + 1 => m.act h)

theorem TypingSubst.forget (m : X -[r.to]> Y) : X -⟨r⟩> Y :=
  .mk (λ h => match m.act h with | .var h => h)

-- def TypingRen.to (m : X -⟨r⟩> Y) : X -[r.to]> Y := sorry

theorem Typing.rename (m : Γ -⟨r⟩> Δ) : Γ ⊢ t : A -> Δ ⊢ t[r] : A
| @var Γ T x h => var (m.act h)
| app f a => app (f.rename m) (a.rename m)
| lam (A := C) t =>
  let t' := t.rename (m.lift C)
  lam (by rw [Ren.to_lift] at t'; exact t')
| zero => zero
| succ t => succ (t.rename m)
| natRec z s n => natRec (z.rename m) (s.rename m) (n.rename m)


theorem TypingSubst.lift {Γ Δ : List Ty} A {σ : Subst Term} :
  Γ -[σ]> Δ ->
  A::Γ -[σ.lift]> A::Δ
:= by
  intro j; apply TypingSubst.mk
  intro x T h
  cases x <;> simp at *
  case _ => apply Typing.var; simp [h]
  case _ x =>
    have lem := Typing.rename (Δ := A::Δ) TypingRen.succ (j.act h)
    simp at lem; exact lem

theorem Typing.subst (m : Γ -[σ]> Δ) : Γ ⊢ t : A -> Δ ⊢ t[σ] : A
| var h => m.act h
| app f a => app (f.subst m) (a.subst m)
| lam (A := C) t => lam (t.subst (m.lift C))
| zero => zero
| succ t => succ (t.subst m)
| natRec z s n => natRec (z.subst m) (s.subst m) (n.subst m)

@[simp]
def LR (Γ : List Ty) : Ty -> Term -> Prop
  | .base => λ t => Γ ⊢ t : .base ∧ SNi .nor t
  | .arrow A B => λ t => Γ ⊢ t : (A -t> B)
    ∧ ∀ {r Δ v}, Γ -⟨r⟩> Δ -> LR Δ A v -> LR Δ B ((Subst.apply r t).app v)
  | .nat => λ t => Γ ⊢ t : Ty.nat ∧ SNi .nor t

@[simp]
def GR : List Ty -> List Ty -> (Subst Term -> Prop)
  | Γ, Δ, σ => ∀ {x T}, Γ[x]? = .some T -> LR Δ T ↑(σ x)

@[simp]
def SemanticTyping Γ t A := ∀ σ Δ, GR Γ Δ σ -> LR Δ A (t[σ])

notation:170 Γ:170 " ⊨s " t:170 " : " A:170 => SemanticTyping Γ t A

theorem LR.typing : LR Γ A t -> Γ ⊢ t : A := by
  intro j; induction A generalizing Γ t
  all_goals exact j.1

theorem LR.monotone (m : Γ -⟨r⟩> Δ) : LR Γ A t -> LR Δ A t[r] := by
  intro h; induction A generalizing Γ Δ t r
  case arrow A B ih1 ih2 =>
    apply And.intro
    apply Typing.rename m (typing h)
    intro r' Δ' v m' lv
    replace h := h.2 (m ∘ m') lv
    simp; exact h
  all_goals
    simp at *; constructor
    apply Typing.rename m h.1
    apply SNi.rename r h.2

theorem GR.forget : GR Γ Δ σ -> Γ -[σ]> Δ := by
  intro h1
  constructor
  intro x T h2
  replace h1 := h1 h2
  apply LR.typing h1

  theorem cr {A} : (∀ Γ t, LR Γ A t -> SNi .nor t) ∧ (∀ {Γ} t, Γ ⊢ t : A  → SNi .neu t -> LR Γ A t) ∧ (∀ {Γ} t t', Γ ⊢ t : A → SNi .red (t, t') -> LR Γ A t' -> LR Γ A t) := by
    induction A <;> simp at *
    case _ =>
      apply And.intro _ _
      · grind only [SNi.neu]
      · grind only [SNi.red]
    case _ A B ih1 ih2 =>
      apply And.intro
      case _ =>
        intro _ t _ h
        apply @SNi.antirename .nor (t[Ren.to (· + 1)]) (· + 1) _ t rfl
        apply @SNi.beta_var .nor _ _ _ 0 rfl
        replace h := h (TypingRen.succ (A := A)) (ih1.2.1 (.var 0) (.var rfl) SNi.var); simp at h
        apply ih2.1 _ _ h
      case _ =>
        apply And.intro
        case _ =>
          intro t h r v
          constructor
          · assumption
          · intros r _ _ _ lr
            apply ih2.2.1
            · constructor
              · apply Typing.rename <;> assumption
              · apply LR.typing
                assumption
            · apply SNi.app
              apply SNi.rename r v
              apply ih1.1 _ _ lr
        case _ =>
          intro _ t t' h1 h2 v lr
          constructor
          · assumption
          · intro r _ _ _ _
            have lem1 := lr ‹_› ‹_›
            apply ih2.2.2 _ _ _ _ lem1
            · constructor
              apply Typing.rename ‹_› ‹_›
              apply LR.typing
              assumption
            · apply SNi.step
              apply SNi.rename r h2
    case _ =>
      exact ⟨fun _ h1 h2 => ⟨h1,.neu h2⟩,fun t t' h1 h2 h3 h4 => ⟨h1,.red h2 h4⟩⟩

theorem LR.var  {Γ x} {A : Ty} : Γ ⊢ #x : A -> LR Γ A #x := by
  intro j; apply cr.2.1 _ j; apply SNi.var

theorem GR.from_ren (m : Γ -⟨r⟩> Δ) : GR Γ Δ r.to
  | _, _, h => LR.var $ .var (m.1 h)

theorem GR.compose {r : Ren} (a : GR X Y σ) (b : GR Y Z r.to) : GR X Z (σ ∘ r.to)
  | x, T, h =>
    let m : Y -⟨r⟩> Z := TypingSubst.forget b.forget
    cast (by simp) $ LR.monotone m (a h)

theorem GR.su (j : LR Δ A a) (m : GR Γ Δ σ) : GR (A::Γ) Δ (su a::σ)
  | 0, T, h => cast (by simp; grind) j
  | x + 1, T, h => m h

theorem LR.nrec_neutral
    (h1 : LR Γ A z)
    (h2 : LR Γ (.nat -t> A -t> A) s)
    (h3 : Γ ⊢ n : Ty.nat)
    (h4 : SNi .neu n)
    : LR Γ A (.natRec z s n)
  :=
    let lem := Typing.natRec (LR.typing h1) (LR.typing h2) h3
    cr.2.1 _ lem (SNi.natRecNeu (cr.1 _ _ h1) (cr.1  _ _ h2) h4)

  theorem LR.app (flr : LR Γ (A -t> B) f) (alr : LR Γ A a) : LR Γ B (f.app a) :=
    cast (by simp) $ flr.2 TypingRen.id alr

  theorem LR.natRec' (h1 : LR Γ A z) (h2 : LR Γ (.nat -t> A -t> A) s) : (t : SNi v n) → (e : v = .nor) →
      let n' :  SnIndices .nor := e ▸ n;
      (j : Γ ⊢ n' : Ty.nat) → LR Γ A (.natRec z s n')
    | .zero, rfl,j =>
      let j' := (Typing.natRec (LR.typing h1) (LR.typing h2) j)
      cr.2.2 _ _ j' (SNi.natRecZero (cr.1 _ _ h2)) h1
    | .succ t', rfl, j =>
      let j' := (Typing.natRec (LR.typing h1) (LR.typing h2) j)
      let .succ j := j
      cr.2.2 _ _  j' SNi.natRecSucc (app (app h2 ⟨j,t'⟩) (.natRec' h1 h2 t' rfl j))
    | .neu t, rfl,j => nrec_neutral h1 h2 j t
    | .red r t', rfl,j =>
      let j' := (Typing.natRec (LR.typing h1) (LR.typing h2) j)
      let r' := SNi.property_weaken r
      cr.2.2 _ _ j' (SNi.natRecStep r) (natRec' h1 h2 t' rfl (preservation_step j r'))
    termination_by structural t => t

  theorem LR.natRec (h1 : LR Γ A z) (h2 : LR Γ (.nat -t> A -t> A) s) (j : Γ ⊢ n : Ty.nat) (t : SNi .nor n)
    : LR Γ A (.natRec z s n) := natRec' h1 h2 t rfl j

  theorem fundamental {A : Ty}: Γ ⊢ t : A -> Γ ⊨s t : A
  | .var j, σ, Δ, h => h j
  | .app (f := f) (a := a) fj aj, σ, Δ, h =>
    let aj' := fundamental aj σ Δ h
    let fj' : LR Δ A (f[σ].app a[σ]) := cast (by simp) $ (fundamental fj σ Δ h).2 TypingRen.id aj'
    fj'
  | @Typing.lam _ A B t tj, σ, Δ, h =>
    let m1 : Γ -[σ]> Δ := h.forget
    let lem1 : Δ ⊢ (:λ[A] t)[σ] : (A -t> B) := .subst m1 (.lam tj)
    let lem2 {r Δ' v} (m2 : Δ -⟨r⟩> Δ') (lv : LR Δ' A v) : LR Δ' B ((:λ[A] t)[σ][r].app v) :=
      let m3  : GR (A :: Γ) Δ' (su v::σ ∘ r.to) := GR.su lv $ h.compose (GR.from_ren m2)
      let tj' : LR Δ' B t[su v::σ ∘ r.to]       := fundamental tj (.su v::σ ∘ r.to) Δ' m3
      let lem2 := @SNi.beta v A (t[.re 0::σ ∘ r ∘ +1]) (cr.1 _ _ lv)
      @cr.2.2 _ _ (t[.su v::σ ∘ r.to])
        (.app (Typing.rename m2 lem1) (LR.typing lv))
        (cast (by simp) $ lem2)
        tj'
    ⟨lem1, lem2⟩
  | .zero, σ, Δ, h => ⟨.zero, .zero⟩
  | .succ nj, σ, Δ, h =>
    let ⟨ih1, ih2⟩ := fundamental nj σ Δ h
    ⟨ih1.succ, ih2.succ⟩
  | .natRec zj sj nj, σ, Δ, h =>
    let ⟨ih1, ih2⟩ := fundamental nj σ Δ h
    LR.natRec (fundamental zj σ Δ h) (fundamental sj σ Δ h) ih1 ih2

theorem strong_normalization_inductive {A : Ty} (j : Γ ⊢ t : A) : SNi .nor t :=
  let lem1 : GR Γ Γ +0 := by
    simp; intros x t h
    apply LR.var
    apply Typing.var h
  let lem2 : LR Γ A t :=
    cast (by simp) $ fundamental j +0 Γ lem1
  cr.1 _ _ lem2

theorem strong_normalization  {A : Ty} (j : Γ ⊢ t : A) : SN Red t :=
  SNi.sound $ strong_normalization_inductive j
