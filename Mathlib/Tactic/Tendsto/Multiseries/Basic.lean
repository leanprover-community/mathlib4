/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Tactic.Tendsto.Multiseries.SeqLemmas
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Main definitions

-/


namespace TendstoTactic

open Filter Asymptotics Stream' Seq

abbrev Basis := List (ℝ → ℝ)

abbrev PreMS (basis : Basis) : Type :=
  match basis with
  | [] => ℝ
  | .cons _ tl => Seq (ℝ × PreMS tl)

namespace PreMS

universe v in
@[cases_eliminator]
def recOn {basis_hd} {basis_tl} {motive : PreMS (basis_hd :: basis_tl) → Sort v}
    (ms : PreMS (basis_hd :: basis_tl)) (nil : motive nil)
    (cons : ∀ exp coef (tl : PreMS (basis_hd :: basis_tl)), motive (cons (exp, coef) tl)) :
    motive ms := by
  cases' ms using Stream'.Seq.recOn with hd tl
  · exact nil
  · exact cons hd.1 hd.2 tl

instance (basis : Basis) : Inhabited (PreMS basis) where
  default := match basis with
  | [] => default
  | .cons _ _ => default

section leadingExp

variable {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}

def leadingExp (ms : PreMS (basis_hd :: basis_tl)) : WithBot ℝ :=
  match destruct ms with
  | none => ⊥
  | some ((exp, _), _) => exp

@[simp]
theorem leadingExp_nil : @leadingExp basis_hd basis_tl .nil = ⊥ := by
  simp [leadingExp]

@[simp]
theorem leadingExp_cons {hd : ℝ × PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)} :
    @leadingExp basis_hd basis_tl (Seq.cons hd tl) = hd.1 := by
  simp [leadingExp]

theorem leadingExp_of_head :
    ms.leadingExp = ms.head.elim ⊥ (fun (exp, _) ↦ exp) := by
  cases ms <;> simp

theorem leadingExp_eq_bot :
    ms = .nil ↔ ms.leadingExp = ⊥ := by
  cases ms <;> simp

theorem leadingExp_eq_coe {exp : ℝ} (h : ms.leadingExp = ↑exp) :
    ∃ (a : PreMS basis_tl × PreMS (basis_hd :: basis_tl)), ms = .cons (exp, a.1) a.2 := by
  cases' ms with exp' coef tl
  · simp at h
  · simp at h
    subst h
    use (coef, tl)

end leadingExp

section WellOrdered

scoped instance {basis : _} : Preorder (ℝ × PreMS basis) where
  le := fun x y ↦ x.1 ≤ y.1
  le_refl := by simp
  le_trans := by
    intro x y z hxy hyz
    simp at *
    trans y.1 <;> assumption

-- TODO: can be simpler??
private theorem lt_iff_lt {basis : _} {exp1 exp2 : ℝ} {coef1 coef2 : PreMS basis} :
    (exp1, coef1) < (exp2, coef2) ↔ exp1 < exp2 := by
  constructor
  · intro h
    rw [lt_iff_le_not_le] at h ⊢
    exact h
  · intro h
    rw [lt_iff_le_not_le] at h ⊢
    exact h

inductive WellOrdered : {basis : Basis} → (PreMS basis) → Prop
| const (ms : PreMS []) : WellOrdered ms
| colist {hd : _} {tl : _} (ms : PreMS (hd :: tl))
    (h_coef : ∀ i x, ms.get? i = .some x → x.2.WellOrdered)
    (h_sorted : Seq.Sorted (· > ·) ms) : ms.WellOrdered

variable {basis_hd : ℝ → ℝ} {basis_tl : Basis}

theorem WellOrdered.nil : @WellOrdered (basis_hd :: basis_tl) .nil := by
  constructor
  · intro i x
    intro h
    simp at h
  · unfold Seq.Sorted
    intro i j x y _ h
    simp at h

theorem WellOrdered.cons_nil {exp : ℝ} {coef : PreMS basis_tl} (h_coef : coef.WellOrdered) :
    @WellOrdered (basis_hd :: basis_tl) (.cons (exp, coef) .nil) := by
  constructor
  · intro i x h
    cases i with
    | zero =>
      simp at h
      rw [← h]
      simpa
    | succ j =>
      simp at h
  · unfold Seq.Sorted
    intro i j x y h_lt _ hj
    cases j with
    | zero => simp at h_lt
    | succ k => simp at hj

theorem WellOrdered.cons {exp : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h_coef : coef.WellOrdered)
    (h_comp : tl.leadingExp < exp)
    (h_tl : tl.WellOrdered) :
    @WellOrdered (basis_hd :: basis_tl) (.cons (exp, coef) tl) := by
  cases h_tl with | colist _ h_tl_coef h_tl_tl =>
  constructor
  · intro i x h
    cases i with
    | zero =>
      simp at h
      rw [← h]
      simpa
    | succ j =>
      simp at h
      simp at h_tl_coef
      solve_by_elim
  · apply Seq.Sorted.cons
    · cases tl
      · simp
      · simp at h_comp ⊢
        rwa [lt_iff_lt]
    · exact h_tl_tl

theorem WellOrdered_cons {exp : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h : @WellOrdered (basis_hd :: basis_tl) (.cons (exp, coef) tl)) :
    coef.WellOrdered ∧ tl.leadingExp < exp ∧ tl.WellOrdered := by
  cases h with | colist _ h_coef h_sorted =>
  apply Seq.Sorted_cons at h_sorted
  constructor
  · specialize h_coef 0 (exp, coef)
    simpa using h_coef
  constructor
  · cases' tl with tl_exp tl_coef tl_tl
    · simp
    · simp [lt_iff_lt] at h_sorted
      simp
      exact h_sorted.left
  · constructor
    · intro i x hx
      specialize h_coef (i + 1) x
      simp at h_coef hx
      exact h_coef hx
    · exact h_sorted.right

theorem WellOrdered.coind {ms : PreMS (basis_hd :: basis_tl)}
    (motive : (ms : PreMS (basis_hd :: basis_tl)) → Prop)
    (h_base : motive ms)
    (h_step : ∀ ms, motive ms →
      (ms = .nil) ∨
      (
        ∃ exp coef, ∃ (tl : PreMS (basis_hd :: basis_tl)), ms = .cons (exp, coef) tl ∧
        coef.WellOrdered ∧
        tl.leadingExp < exp ∧
        motive tl
      )
    )
    : ms.WellOrdered := by
  have h_all : ∀ n, motive (ms.drop n) := by
    intro n
    induction n with
    | zero => simpa
    | succ m ih =>
      simp only [Seq.drop]
      specialize h_step _ ih
      cases h_step with
      | inl h_ms_eq =>
        rw [h_ms_eq] at ih ⊢
        simpa
      | inr h =>
        obtain ⟨exp, coef, tl, h_ms_eq, _, _, h_tl⟩ := h
        rw [h_ms_eq]
        simp
        exact h_tl
  constructor
  · intro i x hx
    simp [← head_dropn] at hx
    specialize h_step _ (h_all i)
    cases h_step with
    | inl h_ms_eq =>
      rw [h_ms_eq] at hx
      simp at hx
    | inr h =>
      obtain ⟨exp, coef, tl, h_ms_eq, h_coef, h_comp, h_tl⟩ := h
      rw [h_ms_eq] at hx
      simp at hx
      simpa [← hx]
  · apply Seq.Sorted.coind motive h_base
    intro hd tl ih
    specialize h_step _ ih
    simp [Seq.cons_eq_cons] at h_step
    obtain ⟨exp, coef, tl, ⟨h_hd_eq, h_tl_eq⟩, _, h_comp, h_tl⟩ := h_step
    subst h_hd_eq h_tl_eq
    constructor
    · cases tl
      · simp
      simp at h_comp ⊢
      rwa [lt_iff_lt]
    · exact h_tl

end WellOrdered

section Approximates

def majorated (f basis_hd : ℝ → ℝ) (exp : ℝ) : Prop :=
  ∀ exp', exp < exp' → f =o[atTop] (fun x ↦ (basis_hd x)^exp')

theorem majorated_of_EventuallyEq {f g basis_hd : ℝ → ℝ} {exp : ℝ} (h_eq : g =ᶠ[atTop] f)
    (h : majorated f basis_hd exp) : majorated g basis_hd exp := by
  simp only [majorated] at *
  intro exp' h_exp
  specialize h exp' h_exp
  exact EventuallyEq.trans_isLittleO h_eq h

-- to upstream?
theorem majorated_self {f : ℝ → ℝ} {exp : ℝ}
    (h : Tendsto f atTop atTop) :
    majorated (fun x ↦ (f x)^exp) f exp := by
  simp only [majorated]
  intro exp' h_exp
  apply (isLittleO_iff_tendsto' _).mpr
  · have : (fun x ↦ f x ^ exp / f x ^ exp') =ᶠ[atTop] fun x ↦ (f x)^(exp - exp') := by
      apply Eventually.mono <| Tendsto.eventually_gt_atTop h 0
      intro x h
      simp only
      rw [← Real.rpow_sub h]
    apply Tendsto.congr' this.symm
    conv =>
      arg 1
      rw [show (fun x ↦ f x ^ (exp - exp')) = ((fun x ↦ x^(-(exp' - exp))) ∘ f) by ext; simp]
    apply Tendsto.comp _ h
    apply tendsto_rpow_neg_atTop
    linarith
  · apply Eventually.mono <| Tendsto.eventually_gt_atTop h 0
    intro x h1 h2
    absurd h2
    exact (Real.rpow_pos_of_pos h1 _).ne.symm

theorem majorated_of_lt {f basis_hd : ℝ → ℝ} {exp1 exp2 : ℝ}
    (h_lt : exp1 < exp2) (h : majorated f basis_hd exp1) :
    majorated f basis_hd exp2 := by
  simp [majorated] at *
  intro exp' h_exp
  apply h _ (by linarith)

theorem majorated_tendsto_zero_of_neg {f basis_hd : ℝ → ℝ} {exp : ℝ}
    (h_lt : exp < 0) (h : majorated f basis_hd exp) :
    Tendsto f atTop (nhds 0) := by
  simp [majorated] at h
  specialize h 0 (by linarith)
  simpa using h

theorem const_majorated {basis_hd : ℝ → ℝ} (h_tendsto : Tendsto basis_hd atTop atTop)
    {c : ℝ}
    : majorated (fun _ ↦ c) basis_hd 0 := by
  intro exp h_exp
  apply Asymptotics.isLittleO_const_left.mpr
  right
  apply Tendsto.comp tendsto_norm_atTop_atTop
  apply Tendsto.comp (tendsto_rpow_atTop h_exp)
  exact h_tendsto

theorem mul_const_majorated {f basis_hd : ℝ → ℝ} {exp : ℝ} (h : majorated f basis_hd exp)
    {c : ℝ}
    : majorated (fun x ↦ (f x) * c) basis_hd exp := by
  intro exp h_exp
  simp_rw [mul_comm]
  apply IsLittleO.const_mul_left (h exp h_exp)

theorem add_majorated {f g basis_hd : ℝ → ℝ} {f_exp g_exp : ℝ} (hf : majorated f basis_hd f_exp)
    (hg : majorated g basis_hd g_exp)
    : majorated (f + g) basis_hd (f_exp ⊔ g_exp) := by
  simp only [majorated] at *
  intro exp h_exp
  simp at h_exp
  apply IsLittleO.add
  · exact hf _ h_exp.left
  · exact hg _ h_exp.right

theorem mul_majorated {f g basis_hd : ℝ → ℝ} {f_exp g_exp : ℝ} (hf : majorated f basis_hd f_exp)
    (hg : majorated g basis_hd g_exp) (h_pos : ∀ᶠ x in atTop, 0 < basis_hd x)
    : majorated (f * g) basis_hd (f_exp + g_exp) := by
  simp only [majorated] at *
  intro exp h_exp
  let ε := (exp - f_exp - g_exp) / 2
  specialize hf (f_exp + ε) (by dsimp [ε]; linarith)
  specialize hg (g_exp + ε) (by dsimp [ε]; linarith)
  apply IsLittleO.trans_eventuallyEq
    (g₁ := fun x ↦ basis_hd x ^ (f_exp + ε) * basis_hd x ^ (g_exp + ε))
  · exact IsLittleO.mul hf hg
  · simp only [EventuallyEq]
    apply Eventually.mono h_pos
    intro x hx
    conv =>
      rhs
      rw [show exp = (f_exp + ε) + (g_exp + ε) by dsimp [ε]; ring_nf]
      rw [Real.rpow_add hx]

noncomputable def partialSumsFrom (Cs : Seq (ℝ → ℝ)) (exps : Seq ℝ) (basis_fun : ℝ → ℝ)
    (init : ℝ → ℝ) : Seq (ℝ → ℝ) :=
  Cs.zip exps |>.fold init fun acc (C, exp) =>
    fun x ↦ acc x + (basis_fun x)^exp * (C x)

noncomputable def partialSums (Cs : Seq (ℝ → ℝ)) (exps : Seq ℝ) (basis_fun : ℝ → ℝ) :
    Seq (ℝ → ℝ) :=
  partialSumsFrom Cs exps basis_fun 0

theorem partialSumsFrom_nil {exps : Seq ℝ} {basis_fun : ℝ → ℝ} {init : ℝ → ℝ} :
    partialSumsFrom .nil exps basis_fun init = .cons init .nil := by
  simp [partialSumsFrom]

theorem partialSumsFrom_cons {Cs_hd : ℝ → ℝ} {Cs_tl : Seq (ℝ → ℝ)} {exps_hd : ℝ}
    {exps_tl : Seq ℝ} {basis_fun : ℝ → ℝ} {init : ℝ → ℝ} :
    partialSumsFrom (.cons Cs_hd Cs_tl) (.cons exps_hd exps_tl) basis_fun init =
    (.cons init <| partialSumsFrom Cs_tl exps_tl basis_fun
      (fun x ↦ init x + (basis_fun x)^exps_hd * (Cs_hd x))) := by
  simp [partialSumsFrom]

theorem partialSumsFrom_eq_map {Cs : Seq (ℝ → ℝ)} {exps : Seq ℝ} {basis_fun : ℝ → ℝ}
    {init : ℝ → ℝ} (h : Cs.atLeastAsLongAs exps) :
    partialSumsFrom Cs exps basis_fun init =
      (partialSums Cs exps basis_fun).map fun G => init + G := by

  let motive : Seq (ℝ → ℝ) → Seq (ℝ → ℝ) → Prop := fun x y =>
    ∃ Cs exps init D,
      Cs.atLeastAsLongAs exps ∧
      (
        (x = partialSumsFrom Cs exps basis_fun (D + init)) ∧
        (y = (partialSumsFrom Cs exps basis_fun init).map fun G => D + G)
      ) ∨
      (x = .nil ∧ y = .nil)
  apply Seq.Eq.coind motive
  · simp [motive]
    use Cs, exps, 0, init
    left
    constructor
    · assumption
    constructor
    · simp
    · simp [partialSums]
  · intro x y ih
    simp [motive] at ih
    obtain ⟨Cs', exps', init', D, ih⟩ := ih
    cases' ih with ih ih
    · left
      obtain ⟨h_alal, h_x_eq, h_y_eq⟩ := ih
      cases' exps' with exps_hd exps_tl
      · simp [partialSums, partialSumsFrom] at h_x_eq h_y_eq
        use D + init', .nil
        constructor
        constructor
        · assumption
        constructor
        · assumption
        simp [motive]
      · obtain ⟨Cs_hd, Cs_tl, h_Cs⟩ := Seq.atLeastAsLongAs_cons h_alal
        subst h_Cs
        simp [partialSums, partialSumsFrom_cons] at h_x_eq h_y_eq
        use D + init',
          partialSumsFrom Cs_tl exps_tl basis_fun fun x ↦ D x + init' x +
            basis_fun x ^ exps_hd * Cs_hd x,
          Seq.map (fun G ↦ D + G) (partialSumsFrom Cs_tl exps_tl basis_fun fun x ↦ init' x +
            basis_fun x ^ exps_hd * Cs_hd x)
        constructor
        · assumption
        constructor
        · assumption
        simp [motive]
        simp at h_alal
        use Cs_tl, exps_tl, fun x ↦ init' x + basis_fun x ^ exps_hd * Cs_hd x, D
        left
        constructor
        · assumption
        constructor
        · congr
          eta_expand
          simp
          ext
          ring_nf
        rfl
    · right
      exact ih

def Approximates {basis : Basis} (ms : PreMS basis) (F : ℝ → ℝ)   : Prop :=
  match basis with
  | [] => F =ᶠ[atTop] fun _ ↦ ms
  | List.cons basis_hd _ =>
    ∃ Cs : Seq (ℝ → ℝ),
    Cs.atLeastAsLongAs ms ∧
    ((Cs.zip ms).All fun (C, (_, coef)) => coef.Approximates C) ∧
    (
      let exps := ms.map fun x => x.1;
      let exps' : Seq (Option ℝ) := (exps.map .some).append (.cons .none .nil);
      (partialSums Cs exps basis_hd).zip exps' |>.All fun (ps, exp?) =>
        match exp? with
        | .some exp =>
          majorated (fun x ↦ F x - ps x) basis_hd exp
        | .none => (fun x ↦ F x - ps x) =ᶠ[atTop] 0
    )

variable {F basis_hd : ℝ → ℝ} {basis_tl : Basis}

theorem Approximates_nil (h : @Approximates (basis_hd :: basis_tl) Seq.nil F) :
    F =ᶠ[atTop] 0 := by
  unfold Approximates at h
  obtain ⟨Cs, _, _, h_maj⟩ := h
  simp at h_maj
  apply Seq.all_get at h_maj
  unfold Seq.All at h_maj
  specialize h_maj (n := 0)
  simpa [partialSums, partialSumsFrom] using h_maj

theorem Approximates_cons {exp : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h : @Approximates (basis_hd :: basis_tl) (.cons (exp, coef) tl) F) :
    ∃ C,
      coef.Approximates C ∧
      majorated F basis_hd exp ∧
      tl.Approximates (fun x ↦ F x - (basis_hd x)^exp * (C x)) := by
  unfold Approximates at h
  obtain ⟨Cs, h_alal, h_coef, h_maj⟩ := h
  obtain ⟨C, Cs_tl, h_alal⟩ := Seq.atLeastAsLongAs_cons h_alal
  subst h_alal
  use C
  simp at h_coef
  constructor
  · exact h_coef.left
  · constructor
    · simp [partialSums, partialSumsFrom] at h_maj
      exact h_maj.left
    · simp at h_alal
      unfold Approximates
      use Cs_tl
      constructor
      · assumption
      · constructor
        · exact h_coef.right
        · simp [partialSums, partialSumsFrom_cons] at h_maj
          apply And.right at h_maj
          rw [partialSumsFrom_eq_map (Seq.atLeastAsLongAs_map h_alal)] at h_maj
          rw [Seq.map_zip_left] at h_maj
          apply Seq.all_mp _ (Seq.map_all_iff.mp h_maj)
          intro (C', exp?)
          simp
          intro h
          ring_nf at h
          ring_nf
          exact h

private structure Approximates_coind_auxT (motive : (F : ℝ → ℝ) → (basis_hd : ℝ → ℝ) →
    (basis_tl : Basis) → (ms : PreMS (basis_hd :: basis_tl)) → Prop)
    (basis_hd : ℝ → ℝ) (basis_tl : Basis) where
  val : PreMS (basis_hd :: basis_tl)
  F : ℝ → ℝ
  h : motive F basis_hd basis_tl val

theorem Approximates.coind' {ms : PreMS (basis_hd :: basis_tl)}
    (motive : (F : ℝ → ℝ) → (basis_hd : ℝ → ℝ) →
      (basis_tl : Basis) → (ms : PreMS (basis_hd :: basis_tl)) → Prop)
    (h_base : motive F basis_hd basis_tl ms)
    (h_step : ∀ basis_hd basis_tl F ms, motive F basis_hd basis_tl ms →
      (ms = .nil ∧ F =ᶠ[atTop] 0) ∨
      (
        ∃ exp coef tl C, ms = .cons (exp, coef) tl ∧
        (coef.Approximates C) ∧
        majorated F basis_hd exp ∧
        (motive (fun x ↦ F x - (basis_hd x)^exp * (C x)) basis_hd basis_tl tl)
      )
    ) : ms.Approximates F := by
  simp [Approximates]
  let T := Approximates_coind_auxT motive basis_hd basis_tl
  let g : T → Option ((ℝ → ℝ) × T) := fun ⟨val, F, h⟩ =>
    (val.recOn (motive := fun ms => motive F basis_hd basis_tl ms → Option ((ℝ → ℝ) × T))
    (nil := fun _ => .none)
    (cons := fun exp coef tl =>
      fun h =>
        have spec : ∃ C,
            coef.Approximates C ∧
            majorated F basis_hd exp ∧
            motive (fun x ↦ F x - basis_hd x ^ exp * C x) basis_hd basis_tl tl := by
          specialize h_step _ _ _ _ h
          simp [Seq.cons_eq_cons] at h_step
          obtain ⟨exp_1, coef_1, tl_1, ⟨⟨h_exp, h_coef⟩, h_tl⟩, h_step⟩ := h_step
          subst h_exp
          subst h_coef
          subst h_tl
          exact h_step
        let C := spec.choose
        .some (C, ⟨tl, fun x ↦ F x - (basis_hd x)^exp * (C x), spec.choose_spec.right.right⟩)
    )
    ) h
  let Cs : Seq (ℝ → ℝ) := Seq.corec g ⟨ms, F, h_base⟩
  use Cs
  constructor
  · let motive' : Seq (ℝ → ℝ) → Seq (ℝ × PreMS basis_tl) → Prop := fun Cs ms =>
      ∃ F h, Cs = (Seq.corec g ⟨ms, F, h⟩)
    apply Seq.atLeastAsLong.coind motive'
    · simp only [motive']
      use F, h_base
    · intro Cs ms ih (exp, coef) tl h_ms_eq
      simp only [motive'] at ih
      obtain ⟨F, h, h_Cs_eq⟩ := ih
      subst h_ms_eq
      rw [Seq.corec_cons] at h_Cs_eq
      pick_goal 2
      · simp [g]
        constructor
      use ?_, ?_
      constructor
      · exact h_Cs_eq
      simp only [motive']
      generalize_proofs p1 p2
      use fun x ↦ F x - basis_hd x ^ exp * p1.choose x, p2
      simp
  · constructor
    · let motive' : Seq ((ℝ → ℝ) × ℝ × PreMS basis_tl) → Prop := fun li =>
        ∃ (ms : PreMS (basis_hd :: basis_tl)), ∃ F h,
          li = (Seq.corec g ⟨ms, F, h⟩).zip ms
      apply Seq.All.coind motive'
      · simp only [motive']
        use ms, F, h_base
      · intro (C, (exp, coef)) tl ih
        simp only
        simp only [motive'] at ih
        obtain ⟨ms, F, h, h_eq⟩ := ih
        specialize h_step _ _ _ _ h
        cases' ms with ms_exp ms_coef ms_tl
        · simp at h_eq
        · rw [Seq.corec_cons] at h_eq
          pick_goal 2
          · simp [g]
            constructor
          simp [Seq.cons_eq_cons] at h_eq
          obtain ⟨⟨h1, ⟨h2, h3⟩⟩, h_eq⟩ := h_eq
          constructor
          · subst h1
            subst h2
            subst h3
            generalize_proofs p
            exact p.choose_spec.left
          · simp only [motive']
            use ?_, ?_, ?_
    · simp [partialSums]
      let motive' : Seq ((ℝ → ℝ) × Option ℝ) → Prop := fun li =>
        li = .nil ∨ ∃ (ms : Seq (ℝ × PreMS basis_tl)), ∃ G h init,
          li = ((partialSumsFrom (Seq.corec g ⟨ms, G, h⟩)
            (Seq.map (fun x ↦ x.1) ms) basis_hd init).zip
              ((Seq.map some (Seq.map (fun x ↦ x.1) ms)).append (Seq.cons none Seq.nil))) ∧
      G + init =ᶠ[atTop] F
      apply Seq.All.coind motive'
      · simp only [motive']
        right
        use ms, F, h_base, 0
        constructor
        · rfl
        simp
      · intro (F', exp?) li_tl ih
        simp only [motive'] at ih
        cases ih with
        | inl ih => simp at ih
        | inr ih =>
        obtain ⟨(ms : PreMS (basis_hd :: basis_tl)), G, h_mot, init, h_eq, hF_eq⟩ := ih
        · simp
          cases' ms with exp coef tl
          · rw [Seq.corec_nil] at h_eq
            pick_goal 2
            · simp [recOn, g]
            simp [Seq.cons_eq_cons, partialSumsFrom_nil] at h_eq
            obtain ⟨⟨h1, h2⟩, h3⟩ := h_eq
            subst h1 h2 h3
            simp
            specialize h_step _ _ _ _ h_mot
            cases h_step with
            | inr h_step => simp at h_step
            | inl h_step =>
              simp at h_step
              constructor
              · apply eventuallyEq_iff_sub.mp
                trans
                · exact hF_eq.symm
                conv => rhs; ext x; rw [← zero_add (F' x)]
                apply EventuallyEq.add h_step
                rfl
              · simp [motive']
          · rw [Seq.corec_cons] at h_eq
            swap
            · simp [g]
              rfl
            simp [Seq.cons_eq_cons, partialSumsFrom_cons] at h_eq
            obtain ⟨⟨h1, h2⟩, h3⟩ := h_eq
            subst h1 h2 h3
            simp
            constructor
            · intro exp' h_exp
              apply EventuallyEq.trans_isLittleO (f₂ := G)
              · apply eventuallyEq_iff_sub.mpr
                replace hF_eq := eventuallyEq_iff_sub.mp hF_eq.symm
                trans F - (G + F')
                · apply eventuallyEq_iff_sub.mpr
                  eta_expand
                  simp
                  ring_nf!
                  rfl
                · exact hF_eq
              · generalize_proofs h at h_eq
                obtain ⟨_, _, h_maj, _⟩ := h
                apply h_maj _ h_exp
            · simp [motive']
              right
              generalize_proofs h1 h2
              use tl, fun x ↦ G x - basis_hd x ^ exp * h1.choose x,
                h2, fun x ↦ F' x + basis_hd x ^ exp * h1.choose x
              constructor
              · rfl
              apply eventuallyEq_iff_sub.mpr
              eta_expand
              simp
              ring_nf!
              conv =>
                lhs; ext x; rw [show G x + (F' x - F x) = (G x + F' x) - F x by ring]
              apply eventuallyEq_iff_sub.mp
              exact hF_eq

-- without basis in motive. TODO: remove `coind'`
theorem Approximates.coind {ms : PreMS (basis_hd :: basis_tl)}
    (motive : (F : ℝ → ℝ) → (ms : PreMS (basis_hd :: basis_tl)) → Prop)
    (h_base : motive F ms)
    (h_step : ∀ F ms, motive F ms →
      (ms = .nil ∧ F =ᶠ[atTop] 0) ∨
      (
        ∃ exp coef tl C, ms = .cons (exp, coef) tl ∧
        (coef.Approximates C) ∧
        majorated F basis_hd exp ∧
        (motive (fun x ↦ F x - (basis_hd x)^exp * (C x)) tl)
      )
    )
    : ms.Approximates F := by
  let motive' : (F : ℝ → ℝ) → (basis_hd : ℝ → ℝ) →
    (basis_tl : Basis) → (ms : PreMS (basis_hd :: basis_tl)) → Prop :=
    fun F' basis_hd' basis_tl' ms' =>
      ∃ (h_hd : basis_hd' = basis_hd) (h_tl : basis_tl' = basis_tl), motive F' (h_tl ▸ (h_hd ▸ ms'))
  apply Approximates.coind' motive'
  · simp [motive']
    assumption
  · intro basis_hd' basis_tl' F' ms' ih
    simp [motive'] at ih ⊢
    obtain ⟨h_hd, h_tl, ih⟩ := ih
    subst h_hd h_tl
    specialize h_step F' ms' ih
    cases h_step with
    | inl h_step =>
      left
      exact h_step
    | inr h_step =>
      right
      obtain ⟨exp, coef, tl, C, h_ms_eq, h_coef, h_maj, h_tl⟩ := h_step
      use exp, coef, tl
      constructor
      · exact h_ms_eq
      use C
      constructor
      · exact h_coef
      constructor
      · exact h_maj
      simpa

theorem Approximates.nil (h : F =ᶠ[atTop] 0) :
    @Approximates (basis_hd :: basis_tl) .nil F := by
  simp [Approximates]
  use .nil
  simpa [partialSums, partialSumsFrom]

theorem Approximates.cons {exp : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (C : ℝ → ℝ) (h_coef : coef.Approximates C)
    (h_maj : majorated F basis_hd exp)
    (h_tl : tl.Approximates (fun x ↦ F x - (basis_hd x)^exp * (C x))) :
    @Approximates (basis_hd :: basis_tl) (.cons (exp, coef) tl) F := by
  simp [Approximates] at h_tl ⊢
  obtain ⟨Cs, h_tl_alal, h_tl_coef, h_tl_maj⟩ := h_tl
  use .cons C Cs
  constructor
  · simpa
  constructor
  · simp
    constructor
    · exact h_coef
    · exact h_tl_coef
  · unfold partialSums at h_tl_maj ⊢
    simp [partialSumsFrom_cons]
    constructor
    · exact h_maj
    -- copypaste from `Approximates_cons`
    · rw [partialSumsFrom_eq_map (Seq.atLeastAsLongAs_map h_tl_alal)]
      rw [Seq.map_zip_left]
      apply Seq.map_all_iff.mpr
      apply Seq.all_mp _ h_tl_maj
      intro (C', exp?)
      simp
      intro h
      ring_nf at h
      ring_nf
      exact h

theorem Approximates_of_EventuallyEq {basis : Basis} {ms : PreMS basis} {F F' : ℝ → ℝ}
     (h_equiv : F =ᶠ[atTop] F') (h_approx : ms.Approximates F) :
    ms.Approximates F' :=
  match basis with
  | [] => by
    simp [Approximates] at h_approx
    exact EventuallyEq.trans h_equiv.symm h_approx
  | List.cons basis_hd basis_tl => by
    let motive : (F : ℝ → ℝ) → (ms : PreMS (basis_hd :: basis_tl)) → Prop :=
      fun F' ms =>
        ∃ F, F =ᶠ[atTop] F' ∧ ms.Approximates F
    apply Approximates.coind motive
    · simp only [motive]
      use F
    · intro F' ms ih
      cases' ms with exp coef tl
      · left
        simp [motive] at ih
        obtain ⟨F, h_equiv, hF⟩ := ih
        apply Approximates_nil at hF
        constructor
        · rfl
        · exact EventuallyEq.trans h_equiv.symm hF
      · right
        use exp, coef, tl
        simp
        simp [motive] at ih
        obtain ⟨F, h_equiv, hF⟩ := ih
        obtain ⟨C, h_coef, h_maj, h_tl⟩ := Approximates_cons hF
        use C
        constructor
        · exact h_coef
        constructor
        · intro exp' h
          apply EventuallyEq.trans_isLittleO h_equiv.symm
          apply h_maj _ h
        · simp [motive]
          use fun x ↦ F x - basis_hd x ^ exp * (C x)
          constructor
          · apply EventuallyEq.sub h_equiv
            apply EventuallyEq.rfl
          · exact h_tl

end Approximates

--------------------------------

def const (basis : Basis) (c : ℝ) : PreMS basis :=
  match basis with
  | [] => c
  | List.cons _ basis_tl =>
    .cons (0, const basis_tl c) .nil

def zero (basis) : PreMS basis :=
  match basis with
  | [] => 0
  | List.cons _ _ => .nil

def one (basis : Basis) : PreMS basis :=
  const basis 1

def monomial (basis : Basis) (n : ℕ) : PreMS basis :=
  match n, basis with
  | 0, [] => 1
  | 0, List.cons _ _ => .cons (1, one _) .nil
  | _ + 1, [] => default
  | m + 1, List.cons _ basis_tl => .cons (0, monomial basis_tl m) .nil

instance instZero {basis : Basis} : Zero (PreMS basis) where
  zero := zero basis

end PreMS

end TendstoTactic
