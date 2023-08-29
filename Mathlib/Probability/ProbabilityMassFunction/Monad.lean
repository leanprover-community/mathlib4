/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic

#align_import probability.probability_mass_function.monad from "leanprover-community/mathlib"@"4ac69b290818724c159de091daa3acd31da0ee6d"

/-!
# Monad Operations for Probability Mass Functions

This file constructs two operations on `Pmf` that give it a monad structure.
`pure a` is the distribution where a single value `a` has probability `1`.
`bind pa pb : Pmf β` is the distribution given by sampling `a : α` from `pa : Pmf α`,
and then sampling from `pb a : Pmf β` to get a final result `b : β`.

`bindOnSupport` generalizes `bind` to allow binding to a partial function,
so that the second argument only needs to be defined on the support of the first argument.

-/


noncomputable section

variable {α β γ : Type*}

open Classical BigOperators NNReal ENNReal

open MeasureTheory

namespace Pmf

section Pure

/-- The pure `Pmf` is the `Pmf` where all the mass lies in one point.
  The value of `pure a` is `1` at `a` and `0` elsewhere. -/
def pure (a : α) : Pmf α :=
  ⟨fun a' => if a' = a then 1 else 0, hasSum_ite_eq _ _⟩
#align pmf.pure Pmf.pure

variable (a a' : α)

@[simp]
theorem pure_apply : pure a a' = if a' = a then 1 else 0 := rfl
#align pmf.pure_apply Pmf.pure_apply

@[simp]
theorem support_pure : (pure a).support = {a} :=
  Set.ext fun a' => by simp [mem_support_iff]
                       -- 🎉 no goals
#align pmf.support_pure Pmf.support_pure

theorem mem_support_pure_iff : a' ∈ (pure a).support ↔ a' = a := by simp
                                                                    -- 🎉 no goals
#align pmf.mem_support_pure_iff Pmf.mem_support_pure_iff

-- @[simp] -- Porting note: simp can prove this
theorem pure_apply_self : pure a a = 1 :=
  if_pos rfl
#align pmf.pure_apply_self Pmf.pure_apply_self

theorem pure_apply_of_ne (h : a' ≠ a) : pure a a' = 0 :=
  if_neg h
#align pmf.pure_apply_of_ne Pmf.pure_apply_of_ne

instance [Inhabited α] : Inhabited (Pmf α) :=
  ⟨pure default⟩

section Measure

variable (s : Set α)

@[simp]
theorem toOuterMeasure_pure_apply : (pure a).toOuterMeasure s = if a ∈ s then 1 else 0 := by
  refine' (toOuterMeasure_apply (pure a) s).trans _
  -- ⊢ ∑' (x : α), Set.indicator s (↑(pure a)) x = if a ∈ s then 1 else 0
  split_ifs with ha
  -- ⊢ ∑' (x : α), Set.indicator s (↑(pure a)) x = 1
  · refine' (tsum_congr fun b => _).trans (tsum_ite_eq a 1)
    -- ⊢ Set.indicator s (↑(pure a)) b = if b = a then 1 else 0
    exact ite_eq_left_iff.2 fun hb => symm (ite_eq_right_iff.2 fun h => (hb <| h.symm ▸ ha).elim)
    -- 🎉 no goals
  · refine' (tsum_congr fun b => _).trans tsum_zero
    -- ⊢ Set.indicator s (↑(pure a)) b = 0
    exact ite_eq_right_iff.2 fun hb => ite_eq_right_iff.2 fun h => (ha <| h ▸ hb).elim
    -- 🎉 no goals
#align pmf.to_outer_measure_pure_apply Pmf.toOuterMeasure_pure_apply

variable [MeasurableSpace α]

/-- The measure of a set under `pure a` is `1` for sets containing `a` and `0` otherwise. -/
@[simp]
theorem toMeasure_pure_apply (hs : MeasurableSet s) :
    (pure a).toMeasure s = if a ∈ s then 1 else 0 :=
  (toMeasure_apply_eq_toOuterMeasure_apply (pure a) s hs).trans (toOuterMeasure_pure_apply a s)
#align pmf.to_measure_pure_apply Pmf.toMeasure_pure_apply

theorem toMeasure_pure : (pure a).toMeasure = Measure.dirac a :=
  Measure.ext fun s hs => by rw [toMeasure_pure_apply a s hs, Measure.dirac_apply' a hs]; rfl
                             -- ⊢ (if a ∈ s then 1 else 0) = Set.indicator s 1 a
                                                                                          -- 🎉 no goals
#align pmf.to_measure_pure Pmf.toMeasure_pure

@[simp]
theorem toPmf_dirac [Countable α] [h : MeasurableSingletonClass α] :
    (Measure.dirac a).toPmf = pure a := by
  rw [toPmf_eq_iff_toMeasure_eq, toMeasure_pure]
  -- 🎉 no goals
#align pmf.to_pmf_dirac Pmf.toPmf_dirac

end Measure

end Pure

section Bind

/-- The monadic bind operation for `Pmf`. -/
def bind (p : Pmf α) (f : α → Pmf β) : Pmf β :=
  ⟨fun b => ∑' a, p a * f a b,
    ENNReal.summable.hasSum_iff.2
      (ENNReal.tsum_comm.trans <| by simp only [ENNReal.tsum_mul_left, tsum_coe, mul_one])⟩
                                     -- 🎉 no goals
#align pmf.bind Pmf.bind

variable (p : Pmf α) (f : α → Pmf β) (g : β → Pmf γ)

@[simp]
theorem bind_apply (b : β) : p.bind f b = ∑' a, p a * f a b := rfl
#align pmf.bind_apply Pmf.bind_apply

@[simp]
theorem support_bind : (p.bind f).support = ⋃ a ∈ p.support, (f a).support :=
  Set.ext fun b => by simp [mem_support_iff, ENNReal.tsum_eq_zero, not_or]
                      -- 🎉 no goals
#align pmf.support_bind Pmf.support_bind

theorem mem_support_bind_iff (b : β) :
    b ∈ (p.bind f).support ↔ ∃ a ∈ p.support, b ∈ (f a).support := by
  simp only [support_bind, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  -- 🎉 no goals
#align pmf.mem_support_bind_iff Pmf.mem_support_bind_iff

@[simp]
theorem pure_bind (a : α) (f : α → Pmf β) : (pure a).bind f = f a := by
  have : ∀ b a', ite (a' = a) (f a' b) 0 = ite (a' = a) (f a b) 0 := fun b a' => by
    split_ifs with h <;> simp; subst h; simp
  ext b
  -- ⊢ ↑(bind (pure a) f) b = ↑(f a) b
  simp [this]
  -- 🎉 no goals
#align pmf.pure_bind Pmf.pure_bind

@[simp]
theorem bind_pure : p.bind pure = p :=
  Pmf.ext fun x => (bind_apply _ _ _).trans (_root_.trans
    (tsum_eq_single x fun y hy => by rw [pure_apply_of_ne _ _ hy.symm, mul_zero]) <|
                                     -- 🎉 no goals
    by rw [pure_apply_self, mul_one])
       -- 🎉 no goals
#align pmf.bind_pure Pmf.bind_pure

@[simp]
theorem bind_const (p : Pmf α) (q : Pmf β) : (p.bind fun _ => q) = q :=
  Pmf.ext fun x => by rw [bind_apply, ENNReal.tsum_mul_right, tsum_coe, one_mul]
                      -- 🎉 no goals
#align pmf.bind_const Pmf.bind_const

@[simp]
theorem bind_bind : (p.bind f).bind g = p.bind fun a => (f a).bind g :=
  Pmf.ext fun b => by
    simpa only [ENNReal.coe_eq_coe.symm, bind_apply, ENNReal.tsum_mul_left.symm,
      ENNReal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm
#align pmf.bind_bind Pmf.bind_bind

theorem bind_comm (p : Pmf α) (q : Pmf β) (f : α → β → Pmf γ) :
    (p.bind fun a => q.bind (f a)) = q.bind fun b => p.bind fun a => f a b :=
  Pmf.ext fun b => by
    simpa only [ENNReal.coe_eq_coe.symm, bind_apply, ENNReal.tsum_mul_left.symm,
      ENNReal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm
#align pmf.bind_comm Pmf.bind_comm

section Measure

variable (s : Set β)

@[simp]
theorem toOuterMeasure_bind_apply :
    (p.bind f).toOuterMeasure s = ∑' a, p a * (f a).toOuterMeasure s :=
  calc
    (p.bind f).toOuterMeasure s = ∑' b, if b ∈ s then ∑' a, p a * f a b else 0 := by
      simp [toOuterMeasure_apply, Set.indicator_apply]
      -- 🎉 no goals
    _ = ∑' (b) (a), p a * if b ∈ s then f a b else 0 := (tsum_congr fun b => by split_ifs <;> simp)
                                                                                -- ⊢ ∑' (a : α), ↑p a * ↑(f a) b = ∑' (a : α), ↑p a * ↑(f a) b
                                                                                              -- 🎉 no goals
                                                                                              -- 🎉 no goals
    _ = ∑' (a) (b), p a * if b ∈ s then f a b else 0 :=
      (tsum_comm' ENNReal.summable (fun _ => ENNReal.summable) fun _ => ENNReal.summable)
    _ = ∑' a, p a * ∑' b, if b ∈ s then f a b else 0 := (tsum_congr fun a => ENNReal.tsum_mul_left)
    _ = ∑' a, p a * ∑' b, if b ∈ s then f a b else 0 :=
      (tsum_congr fun a => (congr_arg fun x => p a * x) <| tsum_congr fun b => by split_ifs <;> rfl)
                                                                                  -- ⊢ ↑(f a) b = ↑(f a) b
                                                                                                -- 🎉 no goals
                                                                                                -- 🎉 no goals
    _ = ∑' a, p a * (f a).toOuterMeasure s :=
      tsum_congr fun a => by simp only [toOuterMeasure_apply, Set.indicator_apply]
                             -- 🎉 no goals
#align pmf.to_outer_measure_bind_apply Pmf.toOuterMeasure_bind_apply

/-- The measure of a set under `p.bind f` is the sum over `a : α`
  of the probability of `a` under `p` times the measure of the set under `f a`. -/
@[simp]
theorem toMeasure_bind_apply [MeasurableSpace β] (hs : MeasurableSet s) :
    (p.bind f).toMeasure s = ∑' a, p a * (f a).toMeasure s :=
  (toMeasure_apply_eq_toOuterMeasure_apply (p.bind f) s hs).trans
    ((toOuterMeasure_bind_apply p f s).trans
      (tsum_congr fun a =>
        congr_arg (fun x => p a * x) (toMeasure_apply_eq_toOuterMeasure_apply (f a) s hs).symm))
#align pmf.to_measure_bind_apply Pmf.toMeasure_bind_apply

end Measure

end Bind

instance : Monad Pmf where
  pure a := pure a
  bind pa pb := pa.bind pb

section BindOnSupport

/-- Generalized version of `bind` allowing `f` to only be defined on the support of `p`.
  `p.bind f` is equivalent to `p.bindOnSupport (fun a _ ↦ f a)`, see `bindOnSupport_eq_bind`. -/
def bindOnSupport (p : Pmf α) (f : ∀ a ∈ p.support, Pmf β) : Pmf β :=
  ⟨fun b => ∑' a, p a * if h : p a = 0 then 0 else f a h b, ENNReal.summable.hasSum_iff.2 (by
    refine' ENNReal.tsum_comm.trans (_root_.trans (tsum_congr fun a => _) p.tsum_coe)
    -- ⊢ (∑' (a_1 : β), ↑p a * if h : ↑p a = 0 then 0 else ↑(f a h) a_1) = ↑p a
    simp_rw [ENNReal.tsum_mul_left]
    -- ⊢ (↑p a * ∑' (i : β), if h : ↑p a = 0 then 0 else ↑(f a (_ : ¬↑p a = 0)) i) =  …
    split_ifs with h
    -- ⊢ ↑p a * ∑' (i : β), 0 = ↑p a
    · simp only [h, zero_mul]
      -- 🎉 no goals
    · rw [(f a h).tsum_coe, mul_one])⟩
      -- 🎉 no goals
#align pmf.bind_on_support Pmf.bindOnSupport

variable {p : Pmf α} (f : ∀ a ∈ p.support, Pmf β)

@[simp]
theorem bindOnSupport_apply (b : β) :
    p.bindOnSupport f b = ∑' a, p a * if h : p a = 0 then 0 else f a h b := rfl
#align pmf.bind_on_support_apply Pmf.bindOnSupport_apply

@[simp]
theorem support_bindOnSupport :
    (p.bindOnSupport f).support = ⋃ (a : α) (h : a ∈ p.support), (f a h).support := by
  refine' Set.ext fun b => _
  -- ⊢ b ∈ support (bindOnSupport p f) ↔ b ∈ ⋃ (a : α) (h : a ∈ support p), support …
  simp only [ENNReal.tsum_eq_zero, not_or, mem_support_iff, bindOnSupport_apply, Ne.def, not_forall,
    mul_eq_zero, Set.mem_iUnion]
  exact
    ⟨fun hb =>
      let ⟨a, ⟨ha, ha'⟩⟩ := hb
      ⟨a, ha, by simpa [ha] using ha'⟩,
      fun hb =>
      let ⟨a, ha, ha'⟩ := hb
      ⟨a, ⟨ha, by simpa [(mem_support_iff _ a).1 ha] using ha'⟩⟩⟩
#align pmf.support_bind_on_support Pmf.support_bindOnSupport

theorem mem_support_bindOnSupport_iff (b : β) :
    b ∈ (p.bindOnSupport f).support ↔ ∃ (a : α) (h : a ∈ p.support), b ∈ (f a h).support := by
  simp only [support_bindOnSupport, Set.mem_setOf_eq, Set.mem_iUnion]
  -- 🎉 no goals
#align pmf.mem_support_bind_on_support_iff Pmf.mem_support_bindOnSupport_iff

/-- `bindOnSupport` reduces to `bind` if `f` doesn't depend on the additional hypothesis. -/
@[simp]
theorem bindOnSupport_eq_bind (p : Pmf α) (f : α → Pmf β) :
    (p.bindOnSupport fun a _ => f a) = p.bind f := by
  ext b
  -- ⊢ ↑(bindOnSupport p fun a x => f a) b = ↑(bind p f) b
  have : ∀ a, ite (p a = 0) 0 (p a * f a b) = p a * f a b :=
    fun a => ite_eq_right_iff.2 fun h => h.symm ▸ symm (zero_mul <| f a b)
  simp only [bindOnSupport_apply fun a _ => f a, p.bind_apply f, dite_eq_ite, mul_ite,
    mul_zero, this]
#align pmf.bind_on_support_eq_bind Pmf.bindOnSupport_eq_bind

theorem bindOnSupport_eq_zero_iff (b : β) :
    p.bindOnSupport f b = 0 ↔ ∀ (a) (ha : p a ≠ 0), f a ha b = 0 := by
  simp only [bindOnSupport_apply, ENNReal.tsum_eq_zero, mul_eq_zero, or_iff_not_imp_left]
  -- ⊢ (∀ (i : α), ¬↑p i = 0 → (if h : ↑p i = 0 then 0 else ↑(f i (_ : ¬↑p i = 0))  …
  exact ⟨fun h a ha => Trans.trans (dif_neg ha).symm (h a ha),
    fun h a ha => Trans.trans (dif_neg ha) (h a ha)⟩
#align pmf.bind_on_support_eq_zero_iff Pmf.bindOnSupport_eq_zero_iff

@[simp]
theorem pure_bindOnSupport (a : α) (f : ∀ (a' : α) (_ : a' ∈ (pure a).support), Pmf β) :
    (pure a).bindOnSupport f = f a ((mem_support_pure_iff a a).mpr rfl) := by
  refine' Pmf.ext fun b => _
  -- ⊢ ↑(bindOnSupport (pure a) f) b = ↑(f a (_ : a ∈ support (pure a))) b
  simp only [bindOnSupport_apply, pure_apply]
  -- ⊢ (∑' (a_1 : α), (if a_1 = a then 1 else 0) * if h : (if a_1 = a then 1 else 0 …
  refine' _root_.trans (tsum_congr fun a' => _) (tsum_ite_eq a _)
  -- ⊢ ((if a' = a then 1 else 0) * if h : (if a' = a then 1 else 0) = 0 then 0 els …
  by_cases h : a' = a <;> simp [h]
  -- ⊢ ((if a' = a then 1 else 0) * if h : (if a' = a then 1 else 0) = 0 then 0 els …
                          -- 🎉 no goals
                          -- 🎉 no goals
#align pmf.pure_bind_on_support Pmf.pure_bindOnSupport

theorem bindOnSupport_pure (p : Pmf α) : (p.bindOnSupport fun a _ => pure a) = p := by
  simp only [Pmf.bind_pure, Pmf.bindOnSupport_eq_bind]
  -- 🎉 no goals
#align pmf.bind_on_support_pure Pmf.bindOnSupport_pure

@[simp]
theorem bindOnSupport_bindOnSupport (p : Pmf α) (f : ∀ a ∈ p.support, Pmf β)
    (g : ∀ b ∈ (p.bindOnSupport f).support, Pmf γ) :
    (p.bindOnSupport f).bindOnSupport g =
      p.bindOnSupport fun a ha =>
        (f a ha).bindOnSupport fun b hb =>
          g b ((mem_support_bindOnSupport_iff f b).mpr ⟨a, ha, hb⟩) := by
  refine' Pmf.ext fun a => _
  -- ⊢ ↑(bindOnSupport (bindOnSupport p f) g) a = ↑(bindOnSupport p fun a ha => bin …
  dsimp only [bindOnSupport_apply]
  -- ⊢ (∑' (a_1 : β), (∑' (a : α), ↑p a * if h : ↑p a = 0 then 0 else ↑(f a h) a_1) …
  simp only [← tsum_dite_right, ENNReal.tsum_mul_left.symm, ENNReal.tsum_mul_right.symm]
  -- ⊢ (∑' (a_1 : β) (i : α), (↑p i * if h : ↑p i = 0 then 0 else ↑(f i h) a_1) * i …
  simp only [ENNReal.tsum_eq_zero, dite_eq_left_iff]
  -- ⊢ (∑' (a_1 : β) (i : α), (↑p i * if h : ↑p i = 0 then 0 else ↑(f i h) a_1) * i …
  refine' ENNReal.tsum_comm.trans (tsum_congr fun a' => tsum_congr fun b => _)
  -- ⊢ ((↑p a' * if h : ↑p a' = 0 then 0 else ↑(f a' h) b) * if h : ∀ (i : α), (↑p  …
  split_ifs with h _ h_1 _ h_2
  any_goals ring1
  -- ⊢ ↑p a' * ↑(f a' h) b * 0 = ↑p a' * (↑(f a' h) b * ↑(g b (_ : b ∈ support (bin …
  · have := h_1 a'
    -- ⊢ ↑p a' * ↑(f a' h) b * 0 = ↑p a' * (↑(f a' h) b * ↑(g b (_ : b ∈ support (bin …
    simp [h] at this
    -- ⊢ ↑p a' * ↑(f a' h) b * 0 = ↑p a' * (↑(f a' h) b * ↑(g b (_ : b ∈ support (bin …
    contradiction
    -- 🎉 no goals
  · simp [h_2]
    -- 🎉 no goals
#align pmf.bind_on_support_bind_on_support Pmf.bindOnSupport_bindOnSupport

theorem bindOnSupport_comm (p : Pmf α) (q : Pmf β) (f : ∀ a ∈ p.support, ∀ b ∈ q.support, Pmf γ) :
    (p.bindOnSupport fun a ha => q.bindOnSupport (f a ha)) =
      q.bindOnSupport fun b hb => p.bindOnSupport fun a ha => f a ha b hb := by
  apply Pmf.ext; rintro c
  -- ⊢ ∀ (x : γ), ↑(bindOnSupport p fun a ha => bindOnSupport q (f a ha)) x = ↑(bin …
                 -- ⊢ ↑(bindOnSupport p fun a ha => bindOnSupport q (f a ha)) c = ↑(bindOnSupport  …
  simp only [ENNReal.coe_eq_coe.symm, bindOnSupport_apply, ← tsum_dite_right,
    ENNReal.tsum_mul_left.symm, ENNReal.tsum_mul_right.symm]
  refine' _root_.trans ENNReal.tsum_comm (tsum_congr fun b => tsum_congr fun a => _)
  -- ⊢ (↑p a * if h : ↑p a = 0 then 0 else ↑q b * if h : ↑q b = 0 then 0 else ↑(f a …
  split_ifs with h1 h2 h2 <;> ring
                              -- 🎉 no goals
                              -- 🎉 no goals
                              -- 🎉 no goals
                              -- 🎉 no goals
#align pmf.bind_on_support_comm Pmf.bindOnSupport_comm

section Measure

variable (s : Set β)

@[simp]
theorem toOuterMeasure_bindOnSupport_apply :
    (p.bindOnSupport f).toOuterMeasure s =
      ∑' a, p a * if h : p a = 0 then 0 else (f a h).toOuterMeasure s := by
  simp only [toOuterMeasure_apply, Set.indicator_apply, bindOnSupport_apply]
  -- ⊢ (∑' (x : β), if x ∈ s then ∑' (a : α), ↑p a * if h : ↑p a = 0 then 0 else ↑( …
  calc
    (∑' b, ite (b ∈ s) (∑' a, p a * dite (p a = 0) (fun h => 0) fun h => f a h b) 0) =
        ∑' (b) (a), ite (b ∈ s) (p a * dite (p a = 0) (fun h => 0) fun h => f a h b) 0 :=
      tsum_congr fun b => by split_ifs with hbs <;> simp only [eq_self_iff_true, tsum_zero]
    _ = ∑' (a) (b), ite (b ∈ s) (p a * dite (p a = 0) (fun h => 0) fun h => f a h b) 0 :=
      ENNReal.tsum_comm
    _ = ∑' a, p a * ∑' b, ite (b ∈ s) (dite (p a = 0) (fun h => 0) fun h => f a h b) 0 :=
      (tsum_congr fun a => by simp only [← ENNReal.tsum_mul_left, mul_ite, mul_zero])
    _ = ∑' a, p a * dite (p a = 0) (fun h => 0) fun h => ∑' b, ite (b ∈ s) (f a h b) 0 :=
      tsum_congr fun a => by split_ifs with ha <;> simp only [ite_self, tsum_zero, eq_self_iff_true]
#align pmf.to_outer_measure_bind_on_support_apply Pmf.toOuterMeasure_bindOnSupport_apply

/-- The measure of a set under `p.bindOnSupport f` is the sum over `a : α`
  of the probability of `a` under `p` times the measure of the set under `f a _`.
  The additional if statement is needed since `f` is only a partial function. -/
@[simp]
theorem toMeasure_bindOnSupport_apply [MeasurableSpace β] (hs : MeasurableSet s) :
    (p.bindOnSupport f).toMeasure s =
      ∑' a, p a * if h : p a = 0 then 0 else (f a h).toMeasure s := by
  simp only [toMeasure_apply_eq_toOuterMeasure_apply _ _ hs, toOuterMeasure_bindOnSupport_apply]
  -- 🎉 no goals
#align pmf.to_measure_bind_on_support_apply Pmf.toMeasure_bindOnSupport_apply

end Measure

end BindOnSupport

end Pmf
