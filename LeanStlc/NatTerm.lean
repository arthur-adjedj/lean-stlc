import LeanALaCarte.ModMap
import LeanALaCarte.CheckTranslation
import LeanALaCarte.ExtendInd
import LeanALaCarte.ModularCommand
import LeanALaCarte.ModDef
import LeanStlc.Reduction
import LeanStlc.Term
open LeanSubst
namespace LeanSubst.Star
  @[grind .]
  theorem step1 {R : α → α → Prop} : R x y → LeanSubst.Star R x y := (.step .refl ·)
end LeanSubst.Star
namespace NatExt
modular (name := `part1)

  inductive Ty extends Ty where
    | nat

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
-- #exit
  @[implicit_reducible,instance] -- TODO infer reducibility attribute from what it extends
  mod_def extends instReprTerm

  prefix:max "#" => Term.var
  infixl:66 " :@ " => Term.app
  notation ":λ[" A "] " t => Term.lam A t

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

modular (imports := #[`part1]) (name := `part2)
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

  attribute [grind] Red ParRed

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

modular (name := `part3) (imports := #[`part2])

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

-- modular (name := `part4) (imports := #[`part3])

  -- mod_def triangle extends _root_.ParRed.triangle where
    -- finally
      -- all_goals
        -- try grind
        -- try intros
      -- · rw [complete.eq_def]
        -- split <;> try grind
        -- next h =>
          -- cases h
          -- apply natRecSucc
--
      -- · rw [complete]
        -- (repeat apply ParRed.app) <;> try assumption

  -- mod_def extends ParRed.instSubstitutiveTerm
  -- mod_def extends ParRed.instHasTriangleTerm

  end ParRed

  namespace Red
-- modular (name := `part5) (imports := #[`part3])

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
  end Red
