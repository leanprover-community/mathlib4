/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Monad Operations for Probability Mass Functions

This file constructs two operations on `PMF` that give it a monad structure.
`pure a` is the distribution where a single value `a` has probability `1`.
`bind pa pb : PMF β` is the distribution given by sampling `a : α` from `pa : PMF α`,
and then sampling from `pb a : PMF β` to get a final result `b : β`.

`bindOnSupport` generalizes `bind` to allow binding to a partial function,
so that the second argument only needs to be defined on the support of the first argument.

-/

@[expose] public section


noncomputable section

variable {α β γ : Type*}

open NNReal ENNReal

open MeasureTheory

namespace PMF

section Pure

open scoped Classical in
/-- The pure `PMF` is the `PMF` where all the mass lies in one point.
  The value of `pure a` is `1` at `a` and `0` elsewhere. -/
def pure (a : α) : PMF α :=
  ⟨fun a' => if a' = a then 1 else 0, hasSum_ite_eq _ _⟩

variable (a a' : α)

open scoped Classical in
@[simp]
theorem pure_apply : pure a a' = if a' = a then 1 else 0 := by
  simp only [pure, DFunLike.coe]
  split_ifs <;> simp

@[simp]
theorem support_pure : (pure a).support = {a} :=
  Set.ext fun a' => by simp [mem_support_iff]

theorem mem_support_pure_iff : a' ∈ (pure a).support ↔ a' = a := by simp

theorem pure_apply_self : pure a a = 1 := by simp

theorem pure_apply_of_ne (h : a' ≠ a) : pure a a' = 0 := by simp [h]

instance [Inhabited α] : Inhabited (PMF α) :=
  ⟨pure default⟩

section Measure

variable (s : Set α)

open scoped Classical in
@[simp]
theorem toOuterMeasure_pure_apply : (pure a).toOuterMeasure s = if a ∈ s then 1 else 0 := by
  simp only [toOuterMeasure_apply, Set.indicator_apply, pure_apply]
  split_ifs with ha
  · trans (∑' b : α, if b = a then 1 else 0)
    · apply tsum_congr
      intro b
      split_ifs with hbs hba <;> simp_all
    · exact tsum_ite_eq a 1
  · trans (∑' _ : α, (0 : ℝ≥0∞))
    · apply tsum_congr
      intro b
      split_ifs with hbs hba <;> simp_all
    · exact tsum_zero

variable [MeasurableSpace α]

open scoped Classical in
/-- The measure of a set under `pure a` is `1` for sets containing `a` and `0` otherwise. -/
@[simp]
theorem toMeasure_pure_apply (hs : MeasurableSet s) :
    (pure a).toMeasure s = if a ∈ s then 1 else 0 :=
  (toMeasure_apply_eq_toOuterMeasure_apply (pure a) hs).trans (toOuterMeasure_pure_apply a s)

theorem toMeasure_pure : (pure a).toMeasure = Measure.dirac a :=
  Measure.ext fun s hs => by rw [toMeasure_pure_apply a s hs, Measure.dirac_apply' a hs]; rfl

@[simp]
theorem toPMF_dirac [Countable α] [h : MeasurableSingletonClass α] :
    (Measure.dirac a).toPMF = pure a := by
  rw [toPMF_eq_iff_toMeasure_eq, toMeasure_pure]

end Measure

end Pure

section Bind

/-- The monadic bind operation for `PMF`. -/
def bind (p : PMF α) (f : α → PMF β) : PMF β :=
  ⟨fun b => ∑' a, (p a : ℝ≥0∞) * f a b,
    ENNReal.summable.hasSum_iff.2
      (ENNReal.tsum_comm.trans <| by simp only [ENNReal.tsum_mul_left, tsum_coe_ennreal, mul_one])⟩

variable (p : PMF α) (f : α → PMF β) (g : β → PMF γ)

@[simp]
theorem bind_apply (b : β) : (p.bind f).1 b = ∑' a, (p a : ℝ≥0∞) * (f a b : ℝ≥0∞) := rfl

@[simp]
theorem support_bind : (p.bind f).support = ⋃ a ∈ p.support, (f a).support :=
  Set.ext fun b => by
    simp only [mem_support_iff, Set.mem_iUnion, exists_prop, ne_eq]
    have hne_top : (p.bind f).1 b ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top
      ((p.bind f).2.tsum_eq.symm ▸ ENNReal.one_ne_top) b
    have key : (p.bind f) b = 0 ↔ (p.bind f).1 b = 0 := by
      rw [show (p.bind f) b = ((p.bind f).1 b).toNNReal from rfl]
      rw [ENNReal.toNNReal_eq_zero_iff]
      simp only [hne_top, or_false]
    rw [key, bind_apply, ENNReal.tsum_eq_zero]
    push_neg
    constructor
    · rintro ⟨a, ha⟩
      simp only [ne_eq, mul_eq_zero, ENNReal.coe_eq_zero, not_or] at ha
      exact ⟨a, ha.1, ha.2⟩
    · rintro ⟨a, hpa, hfa⟩
      refine ⟨a, ?_⟩
      simp only [ne_eq, mul_eq_zero, ENNReal.coe_eq_zero, not_or]
      exact ⟨hpa, hfa⟩

theorem mem_support_bind_iff (b : β) :
    b ∈ (p.bind f).support ↔ ∃ a ∈ p.support, b ∈ (f a).support := by
  simp only [support_bind, Set.mem_iUnion, exists_prop]

@[simp]
theorem pure_bind (a : α) (f : α → PMF β) : (pure a).bind f = f a := by
  refine PMF.ext fun x => ?_
  have hne_bind : ((pure a).bind f).1 x ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top
    (((pure a).bind f).2.tsum_eq.symm ▸ ENNReal.one_ne_top) x
  have hne_f : (f a).1 x ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top
    ((f a).2.tsum_eq.symm ▸ ENNReal.one_ne_top) x
  rw [show ((pure a).bind f) x = (((pure a).bind f).1 x).toNNReal from rfl,
      show (f a) x = ((f a).1 x).toNNReal from rfl, ENNReal.toNNReal_eq_toNNReal_iff' hne_bind hne_f,
      bind_apply]
  rw [tsum_eq_single a]
  · simp only [pure_apply_self, ENNReal.coe_one, one_mul]
    exact ENNReal.coe_toNNReal hne_f
  · intro b hb
    simp only [pure_apply_of_ne _ _ hb, ENNReal.coe_zero, zero_mul]

@[simp]
theorem bind_pure : p.bind pure = p := by
  refine PMF.ext fun x => ?_
  have hne_bind : (p.bind pure).1 x ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top
    ((p.bind pure).2.tsum_eq.symm ▸ ENNReal.one_ne_top) x
  have hne_p : p.1 x ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top
    (p.2.tsum_eq.symm ▸ ENNReal.one_ne_top) x
  rw [show (p.bind pure) x = ((p.bind pure).1 x).toNNReal from rfl,
      show p x = (p.1 x).toNNReal from rfl, ENNReal.toNNReal_eq_toNNReal_iff' hne_bind hne_p,
      bind_apply]
  rw [tsum_eq_single x]
  · simp only [pure_apply_self, ENNReal.coe_one, mul_one]
    exact ENNReal.coe_toNNReal hne_p
  · intro y hy
    simp only [pure_apply_of_ne _ _ hy.symm, ENNReal.coe_zero, mul_zero]

@[simp]
theorem bind_const (p : PMF α) (q : PMF β) : (p.bind fun _ => q) = q := by
  refine PMF.ext fun x => ?_
  have hne_bind : (p.bind fun _ => q).1 x ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top
    ((p.bind fun _ => q).2.tsum_eq.symm ▸ ENNReal.one_ne_top) x
  have hne_q : q.1 x ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top
    (q.2.tsum_eq.symm ▸ ENNReal.one_ne_top) x
  rw [show (p.bind fun _ => q) x = ((p.bind fun _ => q).1 x).toNNReal from rfl,
      show q x = (q.1 x).toNNReal from rfl, ENNReal.toNNReal_eq_toNNReal_iff' hne_bind hne_q,
      bind_apply]
  simp only [ENNReal.tsum_mul_right, tsum_coe_ennreal, one_mul]
  exact ENNReal.coe_toNNReal hne_q

@[simp]
theorem bind_bind : (p.bind f).bind g = p.bind fun a => (f a).bind g := by
  apply Subtype.ext
  ext b
  simp only [bind_apply]
  calc ∑' c, ↑((p.bind f) c) * ↑(g c b)
      = ∑' c, (∑' a, ↑(p a) * ↑(f a c)) * ↑(g c b) := by
        congr 1; ext c
        have hne : (p.bind f).1 c ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top
          ((p.bind f).2.tsum_eq.symm ▸ ENNReal.one_ne_top) c
        rw [show ((p.bind f) c : ℝ≥0∞) = (p.bind f).1 c from ENNReal.coe_toNNReal hne, bind_apply]
    _ = ∑' (c) (a), ↑(p a) * ↑(f a c) * ↑(g c b) := by simp only [ENNReal.tsum_mul_right]
    _ = ∑' (a) (c), ↑(p a) * ↑(f a c) * ↑(g c b) := ENNReal.tsum_comm
    _ = ∑' a, ↑(p a) * ∑' c, ↑(f a c) * ↑(g c b) := by
        congr 1; ext a
        rw [← ENNReal.tsum_mul_left]
        congr 1; ext c
        ring
    _ = ∑' a, ↑(p a) * ((f a).bind g).1 b := by simp only [bind_apply]
    _ = ∑' a, ↑(p a) * ↑(((f a).bind g) b) := by
        congr 1; ext a
        have hne : ((f a).bind g).1 b ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top
          (((f a).bind g).2.tsum_eq.symm ▸ ENNReal.one_ne_top) b
        rw [show (((f a).bind g) b : ℝ≥0∞) = ((f a).bind g).1 b from ENNReal.coe_toNNReal hne]

theorem bind_comm (p : PMF α) (q : PMF β) (f : α → β → PMF γ) :
    (p.bind fun a => q.bind (f a)) = q.bind fun b => p.bind fun a => f a b := by
  apply Subtype.ext
  ext c
  simp only [bind_apply]
  calc ∑' a, ↑(p a) * ↑((q.bind (f a)) c)
      = ∑' a, ↑(p a) * (∑' b, ↑(q b) * ↑(f a b c)) := by
        congr 1; ext a
        have hne : (q.bind (f a)).1 c ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top
          ((q.bind (f a)).2.tsum_eq.symm ▸ ENNReal.one_ne_top) c
        rw [show ((q.bind (f a)) c : ℝ≥0∞) = (q.bind (f a)).1 c from ENNReal.coe_toNNReal hne,
            bind_apply]
    _ = ∑' (a) (b), ↑(p a) * (↑(q b) * ↑(f a b c)) := by
        congr 1; ext a; rw [ENNReal.tsum_mul_left]
    _ = ∑' (a) (b), ↑(q b) * (↑(p a) * ↑(f a b c)) := by
        congr 1; ext a; congr 1; ext b; ring
    _ = ∑' (b) (a), ↑(q b) * (↑(p a) * ↑(f a b c)) := ENNReal.tsum_comm
    _ = ∑' b, ↑(q b) * ∑' a, ↑(p a) * ↑(f a b c) := by
        congr 1; ext b; rw [ENNReal.tsum_mul_left]
    _ = ∑' b, ↑(q b) * (p.bind fun a => f a b).1 c := by simp only [bind_apply]
    _ = ∑' b, ↑(q b) * ↑((p.bind fun a => f a b) c) := by
        congr 1; ext b
        have hne : (p.bind fun a => f a b).1 c ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top
          ((p.bind fun a => f a b).2.tsum_eq.symm ▸ ENNReal.one_ne_top) c
        rw [show ((p.bind fun a => f a b) c : ℝ≥0∞) = (p.bind fun a => f a b).1 c
            from ENNReal.coe_toNNReal hne]

section Measure

variable (s : Set β)

@[simp]
theorem toOuterMeasure_bind_apply :
    (p.bind f).toOuterMeasure s = ∑' a, (p a : ℝ≥0∞) * (f a).toOuterMeasure s := by
  classical
  simp only [toOuterMeasure_apply]
  have hne_tsum : ∑' a, (p.bind f).1 a ≠ ⊤ :=
    (p.bind f).2.tsum_eq.symm ▸ ENNReal.one_ne_top
  have hne : ∀ b, (p.bind f).1 b ≠ ⊤ := fun b =>
    ENNReal.ne_top_of_tsum_ne_top hne_tsum b
  have hne_fa : ∀ a b, (f a).1 b ≠ ⊤ := fun a b =>
    ENNReal.ne_top_of_tsum_ne_top ((f a).2.tsum_eq.symm ▸ ENNReal.one_ne_top) b
  calc ∑' b, s.indicator (fun x => ((p.bind f) x : ℝ≥0∞)) b
      = ∑' b, if b ∈ s then ∑' a, (p a : ℝ≥0∞) * (f a b : ℝ≥0∞) else 0 := by
        congr 1; ext b
        simp only [Set.indicator_apply]
        split_ifs with h
        · -- Show ((p.bind f) b : ℝ≥0∞) = ∑' a, (p a : ℝ≥0∞) * (f a b : ℝ≥0∞)
          rw [show ((p.bind f) b : ℝ≥0∞) = (p.bind f).1 b from
            ENNReal.coe_toNNReal (hne b), bind_apply]
        · rfl
    _ = ∑' (b) (a), if b ∈ s then (p a : ℝ≥0∞) * (f a b : ℝ≥0∞) else 0 := by
        congr 1; ext b; split_ifs with h <;> simp
    _ = ∑' (b) (a), (p a : ℝ≥0∞) * if b ∈ s then (f a b : ℝ≥0∞) else 0 := by
        congr 1; ext b; congr 1; ext a; split_ifs with h <;> simp
    _ = ∑' (a) (b), (p a : ℝ≥0∞) * if b ∈ s then (f a b : ℝ≥0∞) else 0 := ENNReal.tsum_comm
    _ = ∑' a, (p a : ℝ≥0∞) * ∑' b, if b ∈ s then (f a b : ℝ≥0∞) else 0 := by
        congr 1; ext a; rw [ENNReal.tsum_mul_left]
    _ = ∑' a, (p a : ℝ≥0∞) * ∑' b, s.indicator (fun x => ((f a) x : ℝ≥0∞)) b := rfl

/-- The measure of a set under `p.bind f` is the sum over `a : α`
  of the probability of `a` under `p` times the measure of the set under `f a`. -/
@[simp]
theorem toMeasure_bind_apply [MeasurableSpace β] (hs : MeasurableSet s) :
    (p.bind f).toMeasure s = ∑' a, (p a : ℝ≥0∞) * (f a).toMeasure s :=
  (toMeasure_apply_eq_toOuterMeasure_apply (p.bind f) hs).trans
    ((toOuterMeasure_bind_apply p f s).trans
      (tsum_congr fun a =>
        congr_arg (fun x => (p a : ℝ≥0∞) * x)
          (toMeasure_apply_eq_toOuterMeasure_apply (f a) hs).symm))

end Measure

end Bind

instance : Monad PMF where
  pure a := pure a
  bind pa pb := pa.bind pb

section BindOnSupport

/-- Generalized version of `bind` allowing `f` to only be defined on the support of `p`.
  `p.bind f` is equivalent to `p.bindOnSupport (fun a _ ↦ f a)`, see `bindOnSupport_eq_bind`. -/
def bindOnSupport (p : PMF α) (f : ∀ a ∈ p.support, PMF β) : PMF β :=
  ⟨fun b => ∑' a, (p a : ℝ≥0∞) * if h : p a = 0 then 0 else (f a h b : ℝ≥0∞),
    ENNReal.summable.hasSum_iff.2 (by
      refine ENNReal.tsum_comm.trans (_root_.trans (tsum_congr fun a => ?_) p.tsum_coe_ennreal)
      simp_rw [ENNReal.tsum_mul_left]
      split_ifs with h
      · simp only [ENNReal.coe_eq_zero.mpr h, zero_mul]
      · rw [(f a h).tsum_coe_ennreal, mul_one])⟩

variable {p : PMF α} (f : ∀ a ∈ p.support, PMF β)

@[simp]
theorem bindOnSupport_apply (b : β) :
    (p.bindOnSupport f).1 b =
      ∑' a, (p a : ℝ≥0∞) * if h : p a = 0 then 0 else (f a h b : ℝ≥0∞) := rfl

@[simp]
theorem support_bindOnSupport :
    (p.bindOnSupport f).support = ⋃ (a : α) (h : a ∈ p.support), (f a h).support := by
  ext b
  simp only [mem_support_iff, Set.mem_iUnion, ne_eq]
  have hne_top : (p.bindOnSupport f).1 b ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top
    ((p.bindOnSupport f).2.tsum_eq.symm ▸ ENNReal.one_ne_top) b
  have key : (p.bindOnSupport f) b = 0 ↔ (p.bindOnSupport f).1 b = 0 := by
    rw [show (p.bindOnSupport f) b = ((p.bindOnSupport f).1 b).toNNReal from rfl]
    rw [ENNReal.toNNReal_eq_zero_iff]
    simp only [hne_top, or_false]
  rw [key, bindOnSupport_apply, ENNReal.tsum_eq_zero]
  push_neg
  constructor
  · rintro ⟨a, ha⟩
    simp only [ne_eq, mul_eq_zero, ENNReal.coe_eq_zero] at ha
    by_cases hpa : p a = 0
    · simp only [hpa, true_or, dite_true, not_true_eq_false] at ha
    · simp only [hpa, not_false_eq_true, dite_false, not_or] at ha
      refine ⟨a, hpa, ?_⟩
      simpa using ha.2
  · rintro ⟨a, hpa, hfa⟩
    refine ⟨a, ?_⟩
    simp only [ne_eq, mul_eq_zero, ENNReal.coe_eq_zero, hpa, false_or, not_false_eq_true,
      dite_false, hfa]

theorem mem_support_bindOnSupport_iff (b : β) :
    b ∈ (p.bindOnSupport f).support ↔ ∃ (a : α) (h : a ∈ p.support), b ∈ (f a h).support := by
  simp only [support_bindOnSupport, Set.mem_iUnion]

/-- `bindOnSupport` reduces to `bind` if `f` doesn't depend on the additional hypothesis. -/
@[simp]
theorem bindOnSupport_eq_bind (p : PMF α) (f : α → PMF β) :
    (p.bindOnSupport fun a _ => f a) = p.bind f := by
  apply Subtype.ext
  ext b
  simp only [bindOnSupport_apply, bind_apply]
  congr 1
  ext a
  by_cases hpa : p a = 0
  · simp only [hpa, ENNReal.coe_zero, zero_mul, dite_eq_ite, ite_true]
  · simp only [hpa, dite_false]

theorem bindOnSupport_eq_zero_iff (b : β) :
    p.bindOnSupport f b = 0 ↔ ∀ (a) (ha : p a ≠ 0), f a ha b = 0 := by
  have hne_top : (p.bindOnSupport f).1 b ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top
    ((p.bindOnSupport f).2.tsum_eq.symm ▸ ENNReal.one_ne_top) b
  have key : (p.bindOnSupport f) b = 0 ↔ (p.bindOnSupport f).1 b = 0 := by
    rw [show (p.bindOnSupport f) b = ((p.bindOnSupport f).1 b).toNNReal from rfl]
    rw [ENNReal.toNNReal_eq_zero_iff]
    simp only [hne_top, or_false]
  rw [key, bindOnSupport_apply, ENNReal.tsum_eq_zero]
  simp only [mul_eq_zero, or_iff_not_imp_left, ENNReal.coe_eq_zero]
  -- Goal: (∀ a, p a ≠ 0 → dite ... = 0) ↔ (∀ a, p a ≠ 0 → (f a _) b = 0)
  constructor
  · intro h a ha
    have := h a ha
    rw [dif_neg ha] at this
    have hne_fa : (f a ha).1 b ≠ ⊤ :=
      ENNReal.ne_top_of_tsum_ne_top ((f a ha).2.tsum_eq.symm ▸ ENNReal.one_ne_top) b
    rw [show (f a ha) b = ((f a ha).1 b).toNNReal from rfl, ENNReal.toNNReal_eq_zero_iff]
    left
    -- this : ↑((f a ha) b) = 0, goal : (f a ha).1 b = 0
    -- Since (f a ha) b is a NNReal, ↑((f a ha) b) = 0 implies (f a ha).1 b = 0
    rwa [show ((f a ha) b : ℝ≥0∞) = (f a ha).1 b from ENNReal.coe_toNNReal hne_fa] at this
  · intro h a ha
    rw [dif_neg ha]
    have := h a ha
    have hne_fa : (f a ha).1 b ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top
      ((f a ha).2.tsum_eq.symm ▸ ENNReal.one_ne_top) b
    rw [show (f a ha) b = ((f a ha).1 b).toNNReal from rfl, ENNReal.toNNReal_eq_zero_iff] at this
    cases this with
    | inl h => simp only [show (f a ha) b = ((f a ha).1 b).toNNReal from rfl, h]; rfl
    | inr h => exact (hne_fa h).elim

@[simp]
theorem pure_bindOnSupport (a : α) (f : ∀ (a' : α) (_ : a' ∈ (pure a).support), PMF β) :
    (pure a).bindOnSupport f = f a ((mem_support_pure_iff a a).mpr rfl) := by
  refine PMF.ext fun b => ?_
  simp only [bindOnSupport_apply, pure_apply]
  refine _root_.trans (tsum_congr fun a' => ?_) (tsum_ite_eq a _)
  by_cases h : a' = a <;> simp [h]

theorem bindOnSupport_pure (p : PMF α) : (p.bindOnSupport fun a _ => pure a) = p := by
  simp only [PMF.bind_pure, PMF.bindOnSupport_eq_bind]

@[simp]
theorem bindOnSupport_bindOnSupport (p : PMF α) (f : ∀ a ∈ p.support, PMF β)
    (g : ∀ b ∈ (p.bindOnSupport f).support, PMF γ) :
    (p.bindOnSupport f).bindOnSupport g =
      p.bindOnSupport fun a ha =>
        (f a ha).bindOnSupport fun b hb =>
          g b ((mem_support_bindOnSupport_iff f b).mpr ⟨a, ha, hb⟩) := by
  refine PMF.ext fun a => ?_
  dsimp only [bindOnSupport_apply]
  simp only [← tsum_dite_right, ENNReal.tsum_mul_left.symm, ENNReal.tsum_mul_right.symm]
  classical
  simp only [ENNReal.tsum_eq_zero]
  refine ENNReal.tsum_comm.trans (tsum_congr fun a' => tsum_congr fun b => ?_)
  split_ifs with h _ h_1 H h_2
  any_goals ring1
  · absurd H
    simpa [h] using h_1 a'
  · simp [h_2]

theorem bindOnSupport_comm (p : PMF α) (q : PMF β) (f : ∀ a ∈ p.support, ∀ b ∈ q.support, PMF γ) :
    (p.bindOnSupport fun a ha => q.bindOnSupport (f a ha)) =
      q.bindOnSupport fun b hb => p.bindOnSupport fun a ha => f a ha b hb := by
  apply PMF.ext; rintro c
  simp only [bindOnSupport_apply, ← tsum_dite_right,
    ENNReal.tsum_mul_left.symm]
  refine _root_.trans ENNReal.tsum_comm (tsum_congr fun b => tsum_congr fun a => ?_)
  split_ifs with h1 h2 h2 <;> ring

section Measure

variable (s : Set β)

@[simp]
theorem toOuterMeasure_bindOnSupport_apply :
    (p.bindOnSupport f).toOuterMeasure s =
      ∑' a, p a * if h : p a = 0 then 0 else (f a h).toOuterMeasure s := by
  simp only [toOuterMeasure_apply]
  classical
  calc
    (∑' b, ite (b ∈ s) (∑' a, p a * dite (p a = 0) (fun h => 0) fun h => f a h b) 0) =
        ∑' (b) (a), ite (b ∈ s) (p a * dite (p a = 0) (fun h => 0) fun h => f a h b) 0 :=
      tsum_congr fun b => by split_ifs with hbs <;> simp only [tsum_zero]
    _ = ∑' (a) (b), ite (b ∈ s) (p a * dite (p a = 0) (fun h => 0) fun h => f a h b) 0 :=
      ENNReal.tsum_comm
    _ = ∑' a, p a * ∑' b, ite (b ∈ s) (dite (p a = 0) (fun h => 0) fun h => f a h b) 0 :=
      (tsum_congr fun a => by simp only [← ENNReal.tsum_mul_left, mul_ite, mul_zero])
    _ = ∑' a, p a * dite (p a = 0) (fun h => 0) fun h => ∑' b, ite (b ∈ s) (f a h b) 0 :=
      tsum_congr fun a => by split_ifs with ha <;> simp only [ite_self, tsum_zero]

/-- The measure of a set under `p.bindOnSupport f` is the sum over `a : α`
  of the probability of `a` under `p` times the measure of the set under `f a _`.
  The additional if statement is needed since `f` is only a partial function. -/
@[simp]
theorem toMeasure_bindOnSupport_apply [MeasurableSpace β] (hs : MeasurableSet s) :
    (p.bindOnSupport f).toMeasure s =
      ∑' a, p a * if h : p a = 0 then 0 else (f a h).toMeasure s := by
  simp only [toMeasure_apply_eq_toOuterMeasure_apply _ hs, toOuterMeasure_bindOnSupport_apply]

end Measure

end BindOnSupport

end PMF
