/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Monad Operations for Probability Mass Functions

This file constructs two operations on `PMF` that give it a monad structure.
`pure a` is the distribution where a single value `a` has probability `1`.
`bind pa pb : PMF β` is the distribution given by sampling `a : α` from `pa : PMF α`,
and then sampling from `pb a : PMF β` to get a final result `b : β`.

`bindOnSupport` generalizes `bind` to allow binding to a partial function,
so that the second argument only needs to be defined on the support of the first argument.

-/


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
theorem pure_apply : pure a a' = if a' = a then 1 else 0 := rfl

@[simp]
theorem support_pure : (pure a).support = {a} :=
  Set.ext fun a' => by simp [mem_support_iff]

theorem mem_support_pure_iff : a' ∈ (pure a).support ↔ a' = a := by simp

theorem pure_apply_self : pure a a = 1 :=
  if_pos rfl

theorem pure_apply_of_ne (h : a' ≠ a) : pure a a' = 0 :=
  if_neg h

instance [Inhabited α] : Inhabited (PMF α) :=
  ⟨pure default⟩

section Measure

variable (s : Set α)

open scoped Classical in
@[simp]
theorem toOuterMeasure_pure_apply : (pure a).toOuterMeasure s = if a ∈ s then 1 else 0 := by
  refine (toOuterMeasure_apply (pure a) s).trans ?_
  split_ifs with ha
  · refine (tsum_congr fun b => ?_).trans (tsum_ite_eq a 1)
    exact ite_eq_left_iff.2 fun hb =>
      symm (ite_eq_right_iff.2 fun h => (hb <| h.symm ▸ ha).elim)
  · refine (tsum_congr fun b => ?_).trans tsum_zero
    exact ite_eq_right_iff.2 fun hb =>
      ite_eq_right_iff.2 fun h => (ha <| h ▸ hb).elim

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
  ⟨fun b => ∑' a, p a * f a b,
    ENNReal.summable.hasSum_iff.2
      (ENNReal.tsum_comm.trans <| by simp only [ENNReal.tsum_mul_left, tsum_coe, mul_one])⟩

variable (p : PMF α) (f : α → PMF β) (g : β → PMF γ)

@[simp]
theorem bind_apply (b : β) : p.bind f b = ∑' a, p a * f a b := rfl

@[simp]
theorem support_bind : (p.bind f).support = ⋃ a ∈ p.support, (f a).support :=
  Set.ext fun b => by simp [mem_support_iff, ENNReal.tsum_eq_zero, not_or]

theorem mem_support_bind_iff (b : β) :
    b ∈ (p.bind f).support ↔ ∃ a ∈ p.support, b ∈ (f a).support := by
  simp only [support_bind, Set.mem_iUnion, exists_prop]

@[simp]
theorem pure_bind (a : α) (f : α → PMF β) : (pure a).bind f = f a := by
  classical
  have : ∀ b a', ite (a' = a) (f a' b) 0 = ite (a' = a) (f a b) 0 := fun b a' => by
    split_ifs with h <;> simp [h]
  ext b
  simp [this]

@[simp]
theorem bind_pure : p.bind pure = p :=
  PMF.ext fun x => (bind_apply _ _ _).trans (_root_.trans
    (tsum_eq_single x fun y hy => by rw [pure_apply_of_ne _ _ hy.symm, mul_zero]) <|
    by rw [pure_apply_self, mul_one])

@[simp]
theorem bind_const (p : PMF α) (q : PMF β) : (p.bind fun _ => q) = q :=
  PMF.ext fun x => by rw [bind_apply, ENNReal.tsum_mul_right, tsum_coe, one_mul]

@[simp]
theorem bind_bind : (p.bind f).bind g = p.bind fun a => (f a).bind g :=
  PMF.ext fun b => by
    simpa only [ENNReal.coe_inj.symm, bind_apply, ENNReal.tsum_mul_left.symm,
      ENNReal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm

theorem bind_comm (p : PMF α) (q : PMF β) (f : α → β → PMF γ) :
    (p.bind fun a => q.bind (f a)) = q.bind fun b => p.bind fun a => f a b :=
  PMF.ext fun b => by
    simpa only [ENNReal.coe_inj.symm, bind_apply, ENNReal.tsum_mul_left.symm,
      ENNReal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm

section Measure

variable (s : Set β)

@[simp]
theorem toOuterMeasure_bind_apply :
    (p.bind f).toOuterMeasure s = ∑' a, p a * (f a).toOuterMeasure s := by
  classical
  calc
    (p.bind f).toOuterMeasure s = ∑' b, if b ∈ s then ∑' a, p a * f a b else 0 := by
      simp [toOuterMeasure_apply, Set.indicator_apply]
    _ = ∑' (b) (a), p a * if b ∈ s then f a b else 0 := tsum_congr fun b => by split_ifs <;> simp
    _ = ∑' (a) (b), p a * if b ∈ s then f a b else 0 := ENNReal.tsum_comm
    _ = ∑' a, p a * ∑' b, if b ∈ s then f a b else 0 := tsum_congr fun _ => ENNReal.tsum_mul_left
    _ = ∑' a, p a * ∑' b, if b ∈ s then f a b else 0 :=
      (tsum_congr fun a => (congr_arg fun x => p a * x) <| tsum_congr fun b => by split_ifs <;> rfl)
    _ = ∑' a, p a * (f a).toOuterMeasure s :=
      tsum_congr fun a => by simp only [toOuterMeasure_apply, Set.indicator_apply]

/-- The measure of a set under `p.bind f` is the sum over `a : α`
  of the probability of `a` under `p` times the measure of the set under `f a`. -/
@[simp]
theorem toMeasure_bind_apply [MeasurableSpace β] (hs : MeasurableSet s) :
    (p.bind f).toMeasure s = ∑' a, p a * (f a).toMeasure s :=
  (toMeasure_apply_eq_toOuterMeasure_apply (p.bind f) hs).trans
    ((toOuterMeasure_bind_apply p f s).trans
      (tsum_congr fun a =>
        congr_arg (fun x => p a * x) (toMeasure_apply_eq_toOuterMeasure_apply (f a) hs).symm))

end Measure

end Bind

instance : Monad PMF where
  pure a := pure a
  bind pa pb := pa.bind pb

section BindOnSupport

/-- Generalized version of `bind` allowing `f` to only be defined on the support of `p`.
  `p.bind f` is equivalent to `p.bindOnSupport (fun a _ ↦ f a)`, see `bindOnSupport_eq_bind`. -/
def bindOnSupport (p : PMF α) (f : ∀ a ∈ p.support, PMF β) : PMF β :=
  ⟨fun b => ∑' a, p a * if h : p a = 0 then 0 else f a h b, ENNReal.summable.hasSum_iff.2 (by
    refine ENNReal.tsum_comm.trans (_root_.trans (tsum_congr fun a => ?_) p.tsum_coe)
    simp_rw [ENNReal.tsum_mul_left]
    split_ifs with h
    · simp only [h, zero_mul]
    · rw [(f a h).tsum_coe, mul_one])⟩

variable {p : PMF α} (f : ∀ a ∈ p.support, PMF β)

@[simp]
theorem bindOnSupport_apply (b : β) :
    p.bindOnSupport f b = ∑' a, p a * if h : p a = 0 then 0 else f a h b := rfl

@[simp]
theorem support_bindOnSupport :
    (p.bindOnSupport f).support = ⋃ (a : α) (h : a ∈ p.support), (f a h).support := by
  refine Set.ext fun b => ?_
  simp only [ENNReal.tsum_eq_zero, not_or, mem_support_iff, bindOnSupport_apply, Ne, not_forall,
    mul_eq_zero, Set.mem_iUnion]
  exact
    ⟨fun hb =>
      let ⟨a, ⟨ha, ha'⟩⟩ := hb
      ⟨a, ha, by simpa [ha] using ha'⟩,
      fun hb =>
      let ⟨a, ha, ha'⟩ := hb
      ⟨a, ⟨ha, by simpa [(mem_support_iff _ a).1 ha] using ha'⟩⟩⟩

theorem mem_support_bindOnSupport_iff (b : β) :
    b ∈ (p.bindOnSupport f).support ↔ ∃ (a : α) (h : a ∈ p.support), b ∈ (f a h).support := by
  simp only [support_bindOnSupport, Set.mem_iUnion]

/-- `bindOnSupport` reduces to `bind` if `f` doesn't depend on the additional hypothesis. -/
@[simp]
theorem bindOnSupport_eq_bind (p : PMF α) (f : α → PMF β) :
    (p.bindOnSupport fun a _ => f a) = p.bind f := by
  ext b
  have : ∀ a, ite (p a = 0) 0 (p a * f a b) = p a * f a b :=
    fun a => ite_eq_right_iff.2 fun h => h.symm ▸ symm (zero_mul <| f a b)
  simp only [bindOnSupport_apply fun a _ => f a, p.bind_apply f, dite_eq_ite, mul_ite,
    mul_zero, this]

theorem bindOnSupport_eq_zero_iff (b : β) :
    p.bindOnSupport f b = 0 ↔ ∀ (a) (ha : p a ≠ 0), f a ha b = 0 := by
  simp only [bindOnSupport_apply, ENNReal.tsum_eq_zero, mul_eq_zero, or_iff_not_imp_left]
  exact ⟨fun h a ha => Trans.trans (dif_neg ha).symm (h a ha),
    fun h a ha => Trans.trans (dif_neg ha) (h a ha)⟩

@[simp]
theorem pure_bindOnSupport (a : α) (f : ∀ (a' : α) (_ : a' ∈ (pure a).support), PMF β) :
    (pure a).bindOnSupport f = f a ((mem_support_pure_iff a a).mpr rfl) := by
  refine PMF.ext fun b => ?_
  simp only [bindOnSupport_apply, pure_apply]
  classical
  refine _root_.trans (tsum_congr fun a' => ?_) (tsum_ite_eq a (fun _ ↦ _))
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
