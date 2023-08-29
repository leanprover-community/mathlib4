/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.MonoidAlgebra.Basic

#align_import algebra.monoid_algebra.support from "leanprover-community/mathlib"@"16749fc4661828cba18cd0f4e3c5eb66a8e80598"

/-!
#  Lemmas about the support of a finitely supported function
-/


universe u₁ u₂ u₃

namespace MonoidAlgebra

open Finset Finsupp

variable {k : Type u₁} {G : Type u₂} [Semiring k]

theorem support_single_mul_subset [DecidableEq G] [Mul G] (f : MonoidAlgebra k G) (r : k) (a : G) :
    (single a r * f : MonoidAlgebra k G).support ⊆ Finset.image ((· * ·) a) f.support := by
  intro x hx
  -- ⊢ x ∈ image ((fun x x_1 => x * x_1) a) f.support
  contrapose hx
  -- ⊢ ¬x ∈ (single a r * f).support
  have : ∀ y, a * y = x → f y = 0 := by
    simpa only [not_and', mem_image, mem_support_iff, exists_prop, not_exists,
      Classical.not_not] using hx
  simp only [mem_support_iff, mul_apply, sum_single_index, zero_mul, ite_self, sum_zero,
    Classical.not_not]
  exact
    Finset.sum_eq_zero
      (by
        simp (config := { contextual := true }) only [this, mem_support_iff, mul_zero, Ne.def,
          ite_eq_right_iff, eq_self_iff_true, imp_true_iff])
#align monoid_algebra.support_single_mul_subset MonoidAlgebra.support_single_mul_subset

theorem support_mul_single_subset [DecidableEq G] [Mul G] (f : MonoidAlgebra k G) (r : k) (a : G) :
    (f * single a r).support ⊆ Finset.image (· * a) f.support := by
  intro x hx
  -- ⊢ x ∈ image (fun x => x * a) f.support
  contrapose hx
  -- ⊢ ¬x ∈ (f * single a r).support
  have : ∀ y, y * a = x → f y = 0 := by
    simpa only [not_and', mem_image, mem_support_iff, exists_prop, not_exists,
      Classical.not_not] using hx
  simp only [mem_support_iff, mul_apply, sum_single_index, zero_mul, ite_self, sum_zero,
    Classical.not_not]
  exact
    Finset.sum_eq_zero
      (by
        simp (config := { contextual := true }) only [this, sum_single_index, ite_eq_right_iff,
          eq_self_iff_true, imp_true_iff, zero_mul])
#align monoid_algebra.support_mul_single_subset MonoidAlgebra.support_mul_single_subset

theorem support_single_mul_eq_image [DecidableEq G] [Mul G] (f : MonoidAlgebra k G) {r : k}
    (hr : ∀ y, r * y = 0 ↔ y = 0) {x : G} (lx : IsLeftRegular x) :
    (single x r * f : MonoidAlgebra k G).support = Finset.image ((· * ·) x) f.support := by
  refine' subset_antisymm (support_single_mul_subset f _ _) fun y hy => _
  -- ⊢ y ∈ (single x r * f).support
  obtain ⟨y, yf, rfl⟩ : ∃ a : G, a ∈ f.support ∧ x * a = y := by
    simpa only [Finset.mem_image, exists_prop] using hy
  simp only [mul_apply, mem_support_iff.mp yf, hr, mem_support_iff, sum_single_index,
    Finsupp.sum_ite_eq', Ne.def, not_false_iff, if_true, zero_mul, ite_self, sum_zero, lx.eq_iff]
#align monoid_algebra.support_single_mul_eq_image MonoidAlgebra.support_single_mul_eq_image

theorem support_mul_single_eq_image [DecidableEq G] [Mul G] (f : MonoidAlgebra k G) {r : k}
    (hr : ∀ y, y * r = 0 ↔ y = 0) {x : G} (rx : IsRightRegular x) :
    (f * single x r).support = Finset.image (· * x) f.support := by
  refine' subset_antisymm (support_mul_single_subset f _ _) fun y hy => _
  -- ⊢ y ∈ (f * single x r).support
  obtain ⟨y, yf, rfl⟩ : ∃ a : G, a ∈ f.support ∧ a * x = y := by
    simpa only [Finset.mem_image, exists_prop] using hy
  simp only [mul_apply, mem_support_iff.mp yf, hr, mem_support_iff, sum_single_index,
    Finsupp.sum_ite_eq', Ne.def, not_false_iff, if_true, mul_zero, ite_self, sum_zero, rx.eq_iff]
#align monoid_algebra.support_mul_single_eq_image MonoidAlgebra.support_mul_single_eq_image

theorem support_mul [Mul G] [DecidableEq G] (a b : MonoidAlgebra k G) :
    (a * b).support ⊆ a.support.biUnion fun a₁ => b.support.biUnion fun a₂ => {a₁ * a₂} :=
  Subset.trans support_sum <|
    biUnion_mono fun _ _ =>
      Subset.trans support_sum <| biUnion_mono fun _a₂ _ => support_single_subset
#align monoid_algebra.support_mul MonoidAlgebra.support_mul

theorem support_mul_single [RightCancelSemigroup G] (f : MonoidAlgebra k G) (r : k)
    (hr : ∀ y, y * r = 0 ↔ y = 0) (x : G) :
    (f * single x r).support = f.support.map (mulRightEmbedding x) := by
  classical
    ext
    simp only [support_mul_single_eq_image f hr (isRightRegular_of_rightCancelSemigroup x),
      mem_image, mem_map, mulRightEmbedding_apply]
#align monoid_algebra.support_mul_single MonoidAlgebra.support_mul_single

theorem support_single_mul [LeftCancelSemigroup G] (f : MonoidAlgebra k G) (r : k)
    (hr : ∀ y, r * y = 0 ↔ y = 0) (x : G) :
    (single x r * f : MonoidAlgebra k G).support = f.support.map (mulLeftEmbedding x) := by
  classical
    ext
    simp only [support_single_mul_eq_image f hr (isLeftRegular_of_leftCancelSemigroup x), mem_image,
      mem_map, mulLeftEmbedding_apply]
#align monoid_algebra.support_single_mul MonoidAlgebra.support_single_mul

section Span

variable [MulOneClass G]

/-- An element of `MonoidAlgebra k G` is in the subalgebra generated by its support. -/
theorem mem_span_support (f : MonoidAlgebra k G) :
    f ∈ Submodule.span k (of k G '' (f.support : Set G)) := by
  erw [of, MonoidHom.coe_mk, ← supported_eq_span_single, Finsupp.mem_supported]
  -- 🎉 no goals
#align monoid_algebra.mem_span_support MonoidAlgebra.mem_span_support

end Span

end MonoidAlgebra

namespace AddMonoidAlgebra

open Finset Finsupp MulOpposite

variable {k : Type u₁} {G : Type u₂} [Semiring k]

theorem support_mul [DecidableEq G] [Add G] (a b : AddMonoidAlgebra k G) :
    (a * b).support ⊆ a.support.biUnion fun a₁ => b.support.biUnion fun a₂ => {a₁ + a₂} :=
  @MonoidAlgebra.support_mul k (Multiplicative G) _ _ _ _ _
#align add_monoid_algebra.support_mul AddMonoidAlgebra.support_mul

theorem support_mul_single [AddRightCancelSemigroup G] (f : AddMonoidAlgebra k G) (r : k)
    (hr : ∀ y, y * r = 0 ↔ y = 0) (x : G) :
    (f * single x r : AddMonoidAlgebra k G).support = f.support.map (addRightEmbedding x) :=
  @MonoidAlgebra.support_mul_single k (Multiplicative G) _ _ _ _ hr _
#align add_monoid_algebra.support_mul_single AddMonoidAlgebra.support_mul_single

theorem support_single_mul [AddLeftCancelSemigroup G] (f : AddMonoidAlgebra k G) (r : k)
    (hr : ∀ y, r * y = 0 ↔ y = 0) (x : G) :
    (single x r * f : AddMonoidAlgebra k G).support = f.support.map (addLeftEmbedding x) :=
  @MonoidAlgebra.support_single_mul k (Multiplicative G) _ _ _ _ hr _
#align add_monoid_algebra.support_single_mul AddMonoidAlgebra.support_single_mul

section Span

/-- An element of `AddMonoidAlgebra k G` is in the submodule generated by its support. -/
theorem mem_span_support [AddZeroClass G] (f : AddMonoidAlgebra k G) :
    f ∈ Submodule.span k (of k G '' (f.support : Set G)) := by
  erw [of, MonoidHom.coe_mk, ← Finsupp.supported_eq_span_single, Finsupp.mem_supported]
  -- 🎉 no goals
#align add_monoid_algebra.mem_span_support AddMonoidAlgebra.mem_span_support

/-- An element of `AddMonoidAlgebra k G` is in the subalgebra generated by its support, using
unbundled inclusion. -/
theorem mem_span_support' (f : AddMonoidAlgebra k G) :
    f ∈ Submodule.span k (of' k G '' (f.support : Set G)) := by
  delta of'
  -- ⊢ f ∈ Submodule.span k ((fun a => single a 1) '' ↑f.support)
  rw [← Finsupp.supported_eq_span_single, Finsupp.mem_supported]
  -- 🎉 no goals
#align add_monoid_algebra.mem_span_support' AddMonoidAlgebra.mem_span_support'

end Span

end AddMonoidAlgebra
