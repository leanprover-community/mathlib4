/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# `Finsupp.multiinearCombination`

## Main definitions



## Tags

function with finite support, module, linear algebra
-/

@[expose] public section

noncomputable section

open Set LinearMap Submodule

namespace Finsupp

variable {ι : Type*} {α : ι → Type*} {M : Type*} {R : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M]

variable (v : (i : ι) → α i → M) (R)

def multilinearCombination : ((i : ι) → α i →₀ R) →ₗ[R] ι → M where
  toFun l i := linearCombination R (v i) (l i)
  map_add' l₁ l₂ := by ext _; simp
  map_smul' c l := by ext _; simp

variable {v}

theorem multilinearCombination_apply (l : (i : ι) → α i →₀ R) :
    multilinearCombination R v l = fun i => linearCombination R (v i) (l i) :=
  rfl

theorem multilinearCombination_apply_apply (l : (i : ι) → α i →₀ R) (i : ι) :
    multilinearCombination R v l i = linearCombination R (v i) (l i) :=
  rfl

@[simp]
theorem multilinearCombination_pi_single (c : ι → R) (a : (i : ι) → α i) :
    multilinearCombination R v (fun i => single (a i) (c i)) = fun i => c i • v i (a i) := by
  simp [multilinearCombination_apply]

theorem multilinearCombination_zero_apply (x : (i : ι) → α i →₀ R) :
    (multilinearCombination R (0 : (i : ι) → α i → M)) x = 0 := by
  ext
  simp [multilinearCombination_apply]

variable (α M)

@[simp]
theorem multilinearCombination_zero : multilinearCombination R (0 : (i : ι) → α i → M) = 0 :=
  LinearMap.ext (multilinearCombination_zero_apply R)

@[simp]
theorem multilinearCombination_single_index (c : ι → M) (a : (i : ι) → α i) (f : (i : ι) → α i →₀ R)
    [∀ i, DecidableEq (α i)] :
    multilinearCombination R (α := α) (fun i => Pi.single (a i) (c i)) f =
    fun i => (f i) (a i) • (c i) := by
  ext i
  rw [multilinearCombination_apply_apply, linearCombination_single_index]

variable {M' : Type*} [AddCommGroup M'] [Module R M']
variable {R M}

theorem multilinearCombination_linear_comp (f : M →ₗ[R] M') :
    multilinearCombination R (fun i => f ∘ v i) =
    LinearMap.funRight R ι f ∘ₗ multilinearCombination R v := by
  ext
  simp [multilinearCombination_apply, linearCombination_linear_comp]

theorem apply_multilinearCombination (f : M →ₗ[R] M') (v) (l : (i : ι) → α i →₀ R) :
    (fun i => f (multilinearCombination R v l i)) =
    multilinearCombination R (fun i => f ∘ v i) l :=
  congr($(multilinearCombination_linear_comp α f) l).symm

theorem multilinearCombination_unique [∀ i, Unique (α i)] (l : (i : ι) → α i →₀ R) :
    multilinearCombination R v l = fun i => l i default • v i default := by
  simp [← multilinearCombination_pi_single, ← unique_single]

theorem multilinearCombination_surjective (h : ∀ i, Function.Surjective (v i)) :
    Function.Surjective (multilinearCombination R v) := by
  intro x
  use fun i => single (h i (x i)).choose 1
  ext i
  simp [(h i (x i)).choose_spec]

theorem multilinearCombination_range (h : ∀ i, Function.Surjective (v i)) :
    LinearMap.range (multilinearCombination R v) = ⊤ :=
  range_eq_top.2 <| multilinearCombination_surjective α h

theorem range_multilinearCombination :
    LinearMap.range (multilinearCombination R v) =
    Submodule.pi univ (fun i => span R (Set.range (v i))) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨l, hl⟩
    rw [← hl]
    rw [multilinearCombination_apply, Submodule.mem_pi]
    intro i _
    rw [← range_linearCombination]
    exact LinearMap.mem_range_self (linearCombination R (v i)) (l i)
  · intro hx
    simp only [Submodule.mem_pi, ← range_linearCombination] at hx
    use fun i => (hx i (Set.mem_univ i)).choose
    rw [multilinearCombination_apply]
    ext i
    exact (hx i (Set.mem_univ i)).choose_spec

/-- A version of `Finsupp.range_multilinearCombination` which is useful for going in the other
direction -/
theorem span_eq_range_multilinearCombination (s : ι → Set M) :
    Submodule.pi univ (fun i => span R (s i)) =
    LinearMap.range (multilinearCombination (α := fun i => s i) R (fun _ => Subtype.val)) := by
  simp [range_multilinearCombination]

theorem mem_submodule_iff_multilinearCombination (s : ι → Set M) (x : ι → M) :
    x ∈ Submodule.pi univ (fun i => span R (s i)) ↔
    ∃ l : (i : ι) → s i →₀ R, multilinearCombination R (fun _ => Subtype.val) l = x :=
  (SetLike.ext_iff.1 <| span_eq_range_multilinearCombination _) x

theorem mem_span_iff_multilinearCombination (s : ι → Set M) (x : ι → M) :
    (∀ i, x i ∈ span R (s i)) ↔
    ∃ l : (i : ι) → s i →₀ R, multilinearCombination R (fun _ => Subtype.val) l = x := by
  rw [← mem_submodule_iff_multilinearCombination, Submodule.mem_pi]
  simp [mem_span_iff_linearCombination]

theorem mem_span_range_iff_exists_finsupp_family {v : (i : ι) → α i → M} {x : ι → M} :
    (∀ i, x i ∈ span R (range (v i))) ↔
    ∃ c : (i : ι) → α i →₀ R, ∀ i, ((c i).sum fun j a => a • v i j) = x i := by
  simp only [← Finsupp.range_linearCombination, LinearMap.mem_range, linearCombination_apply]
  constructor
  · intro h
    use fun i => (h i).choose
    exact fun i => (h i).choose_spec
  · rintro ⟨c, hc⟩
    exact fun i ↦ ⟨(c i), (hc i)⟩

theorem span_image_eq_map_multilinearCombination (s : (i : ι) → Set (α i)) :
    Submodule.pi univ (fun i => span R (v i '' s i)) = Submodule.map (multilinearCombination R v)
    (Submodule.pi univ (fun i => supported R R (s i))) := by
  apply le_antisymm
  · intro x hx
    simp only [Submodule.mem_pi, mem_univ, forall_const, span_image_eq_map_linearCombination] at hx
    rw [Submodule.mem_map]
    use fun i => (hx i).choose
    constructor
    · intro i
      simp [(hx i).choose_spec]
    · ext i
      simp [multilinearCombination_apply, (hx i).choose_spec]
  · rintro x ⟨y, ⟨y_mem, rfl⟩⟩
    rw [Submodule.mem_pi]
    rintro i -
    rw [span_image_eq_map_linearCombination, multilinearCombination_apply_apply]
    use y i
    simp [y_mem i]

theorem mem_span_image_iff_multilinearCombination {s : (i : ι) → Set (α i)} {x : ι → M} :
    (∀ i, x i ∈ span R (v i '' s i)) ↔
    ∃ l : (i : ι) → supported R R (s i), multilinearCombination R v (fun i => (l i).val) = x := by
  have : x ∈ Submodule.pi univ (fun i => span R (v i '' s i)) ↔
    x ∈ Submodule.map (multilinearCombination R v)
    (Submodule.pi univ (fun i => supported R R (s i))) := by
    rw [span_image_eq_map_multilinearCombination]
  simp only [Submodule.mem_pi, mem_univ, forall_const, mem_map] at this
  simp_rw [this, multilinearCombination_apply]
  constructor
  · rintro ⟨y, ⟨y_mem, rfl⟩⟩
    use (fun i => ⟨y i, y_mem i⟩)
  · rintro ⟨l, rfl⟩
    use fun i => (l i).val
    simp

theorem multilinearCombination_option (v : (i : ι) → Option (α i) → M)
    (f : (i : ι) → Option (α i) →₀ R) :
    ∀ i, multilinearCombination R v f i = (f i) none • (v i) none +
    multilinearCombination R (fun i => v i ∘ Option.some) (fun i => (f i).some) i := by
  simp [multilinearCombination_apply, linearCombination_option]

variable (R) (v) in
/-- `Finsupp.linearCombinationOn M v s` interprets `p : α →₀ R` as a linear combination of a
subset of the vectors in `v`, mapping it to the span of those vectors.

The subset is indicated by a set `s : Set α` of indices.
-/
def multilinearCombinationOn (s : (i : ι) → Set (α i)) :
    Submodule.pi univ (fun i => supported R R (s i)) →ₗ[R]
      Submodule.pi univ (fun i => span R (v i '' s i)) :=
    LinearMap.codRestrict _ ((multilinearCombination _ v).comp
      (Submodule.subtype (Submodule.pi univ (fun i => supported R R (s i)))))
      (by rintro ⟨l, hl⟩ i -; simp only [coe_comp, coe_subtype, Function.comp_apply,
        SetLike.mem_coe, multilinearCombination_apply_apply,
        mem_span_image_iff_linearCombination]; use l i; exact ⟨hl i (Set.mem_univ i), rfl⟩)

theorem multilinearCombinationOn_range (s : (i : ι) → Set (α i)) :
    LinearMap.range (multilinearCombinationOn α R v s) = ⊤ := by
  rw [multilinearCombinationOn, LinearMap.range_eq_map, LinearMap.map_codRestrict,
    ← LinearMap.range_le_iff_comap, range_subtype, Submodule.map_top, LinearMap.range_comp,
    range_subtype]
  exact (span_image_eq_map_multilinearCombination _ _).le

end Finsupp
