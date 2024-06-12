import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Data.Finset.Update

/-!
# Functions depending only on some variables

When dealing with a function `f : (i : ι) → α i` depending on many variables, some operations
may get rid of the dependency on some variables
(see `Function.updateFinset` or `lmarginal` for example). However considering this new function
as having a different domain with fewer points is not comfortable in Lean, as it requires the use
of subtypes and can lead to tedious writing.
On the other hand one wants to be able for example to call some function constant with respect to
some variables and be able to infer this when applying transformations mentioned above.
This is why introduce the predicate `DependsOn f s`, which states that if `x` and `y` coincide over
the set `s`, then `f x = f y`. This is then used to prove some properties about lmarginals.

## Main definitions

* `DependsOn f s`: If `x` and `y` coincide over the set `s`, then `f x` equals `f y`.

## Main statements

* `dependsOn_lmarginal`: If a function `f` depends on a set `s` and `t` is a finite set, then
  `∫⋯∫⁻_t, f ∂μ` depends on `s \ t`.
* `lmarginal_eq_of_disjoint`: If a function `f` depends on a set `s` and `t` is a finite set
  disjoint from `s` and the measures `μ i` are probability measures,
  then `∫⋯∫⁻_t, f ∂μ` is equal to `f`.

## Tags

depends on, updateFinset, update, lmarginal
-/

open MeasureTheory ENNReal Set Finset symmDiff

variable {ι : Type*} {α : ι → Type*} {β : Type*}
variable {f : ((i : ι) → α i) → β}

/-- A function `f` depends on `s` if, whenever `x` and `y` coincide over `s`, `f x = f y`. -/
def DependsOn (f : ((i : ι) → α i) → β) (s : Set ι) : Prop :=
  ∀ ⦃x y⦄, (∀ i ∈ s, x i = y i) → f x = f y

theorem dependsOn_univ (f : ((i : ι) → α i) → β) : DependsOn f univ := by
  intro x y hxy
  have : x = y := by
    ext i
    exact hxy i trivial
  rw [this]

/-- A constant function does not depend on any variable. -/
theorem dependsOn_const (b : β) : DependsOn (fun _ : (i : ι) → α i ↦ b) ∅ := by simp [DependsOn]

/-- A function which depends on the empty set is constant. -/
theorem dependsOn_empty (hf : DependsOn f ∅) (x y : (i : ι) → α i) : f x = f y := hf (by simp)

variable [DecidableEq ι]

/-- If one replaces the variables indexed by a finite set `t`, then `f` no longer depends on
these variables. -/
theorem dependsOn_updateFinset {s : Set ι} (hf : DependsOn f s) (t : Finset ι) (y : (i : t) → α i) :
    DependsOn (fun x ↦ f (Function.updateFinset x t y)) (s \ t) := by
  intro x₁ x₂ h
  refine hf (fun i hi ↦ ?_)
  simp only [Function.updateFinset]
  split_ifs with h'
  · rfl
  · exact h i <| (mem_diff _).2 ⟨hi, h'⟩

/-- If one replaces the variable indexed by `i`, then `f` no longer depends on
this variable. -/
theorem dependsOn_update {s : Finset ι} (hf : DependsOn f s) (i : ι) (y : α i) :
    DependsOn (fun x ↦ f (Function.update x i y)) (s.erase i) := by
  simp_rw [Function.update_eq_updateFinset, erase_eq, coe_sdiff]
  exact dependsOn_updateFinset hf _ _

variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable {μ : (i : ι) → Measure (X i)} {f : ((i : ι) → X i) → ℝ≥0∞} {s : Set ι}

/-- If a function depends on `s`, then its `lmarginal` with respect to a finite set `t` only
depends on `s \ t`. -/
theorem dependsOn_lmarginal (hf : DependsOn f s) (t : Finset ι) :
    DependsOn (∫⋯∫⁻_t, f ∂μ) (s \ t) := by
  intro x y hxy
  have aux z : f (Function.updateFinset x t z) = f (Function.updateFinset y t z) := by
    refine hf (fun i hi ↦ ?_)
    simp only [Function.updateFinset]
    split_ifs with h
    · rfl
    · exact hxy i ((mem_diff _).2 ⟨hi, h⟩)
  exact lintegral_congr aux

variable [∀ i, IsProbabilityMeasure (μ i)]

/-- If `μ` is a family of probability measures, and `f` depends on `s`, then integrating over
some variables which are not in `s` does not change the value. -/
theorem lmarginal_eq_of_disjoint (hf : DependsOn f s) {t : Finset ι} (hst : Disjoint s t) :
    ∫⋯∫⁻_t, f ∂μ = f := by
  ext x
  have aux y : f (Function.updateFinset x t y) = f x := by
    refine hf (fun i hi ↦ ?_)
    simp only [Function.updateFinset]
    split_ifs with h
    · exact (Set.not_disjoint_iff.2 ⟨i, hi, h⟩ hst).elim
    · rfl
  simp [lmarginal, lintegral_congr aux]

/-- Integrating a constant over some variables with respect to probability measures does nothing. -/
theorem lmarginal_const {s : Finset ι} (c : ℝ≥0∞) (x : (i : ι) → X i) :
    (∫⋯∫⁻_s, (fun _ ↦ c) ∂μ) x = c := by
  rw [lmarginal_eq_of_disjoint (dependsOn_const c) (empty_disjoint _)]

/-- If `μ` is a family of probability measures, and `f` depends on `s`, then integrating over
two different sets of variables such that their difference is not in `s`
yields the same function. -/
theorem lmarginal_eq_of_disjoint_diff (mf : Measurable f) (hf : DependsOn f s) {t u : Finset ι}
(htu : t ⊆ u) (hsut : Disjoint s (u \ t)) :
    ∫⋯∫⁻_u, f ∂μ = ∫⋯∫⁻_t, f ∂μ := by
  rw [← coe_sdiff] at hsut
  rw [← union_sdiff_of_subset htu, lmarginal_union _ _ mf disjoint_sdiff_self_right]
  congrm ∫⋯∫⁻_t, ?_ ∂μ
  exact lmarginal_eq_of_disjoint hf hsut

/-- If `μ` is a family of probability measures, and `f` depends on `s`, then integrating over
two different sets of variables such that their difference is not in `s`
yields the same function. -/
theorem lmarginal_eq_of_disjoint_symmDiff (mf : Measurable f) (hf : DependsOn f s)
    {t u : Finset ι} (hstu : Disjoint s (t ∆ u)) :
    ∫⋯∫⁻_t, f ∂μ = ∫⋯∫⁻_u, f ∂μ := by
  rw [symmDiff_def, disjoint_sup_right] at hstu
  rcases hstu with ⟨h1, h2⟩
  rw [← coe_sdiff] at h1 h2
  have : ∫⋯∫⁻_u ∪ t, f ∂μ = ∫⋯∫⁻_u, f ∂μ := by
    rw [← union_sdiff_self_eq_union, lmarginal_union _ _ mf disjoint_sdiff_self_right]
    congrm ∫⋯∫⁻_u, ?_ ∂μ
    exact lmarginal_eq_of_disjoint hf h1
  rw [← this, Finset.union_comm, ← union_sdiff_self_eq_union,
    lmarginal_union _ _ mf disjoint_sdiff_self_right]
  congrm ∫⋯∫⁻_t, ?_ ∂μ
  exact (lmarginal_eq_of_disjoint hf h2).symm
