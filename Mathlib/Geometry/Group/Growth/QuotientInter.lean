/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Growth in the quotient and intersection with a subgroup

For a group `G` and a subgroup `H ≤ G`, this file gives upper and lower bounds on the growth of a
finset by its growth in `H` and `G ⧸ H`.
-/

open Finset Function
open scoped Pointwise

namespace Finset
variable {G : Type*} [Group G] [DecidableEq G] {H : Subgroup G} [DecidablePred (· ∈ H)] [H.Normal]
  {A : Finset G} {m n : ℕ}

@[to_additive]
lemma card_pow_quotient_mul_pow_inter_subgroup_le :
    #((A ^ m).image <| QuotientGroup.mk' H) * #{x ∈ A ^ n | x ∈ H} ≤ #(A ^ (m + n)) := by
  set π := QuotientGroup.mk' H
  let φ := invFunOn π (A ^ m)
  have hφ : Set.InjOn φ (π '' (A ^ m)) := invFunOn_injOn_image ..
  have hφA {a} (ha : a ∈ π '' (A ^ m)) : φ a ∈ A ^ m := by
    have := invFunOn_mem (by simpa using ha)
    norm_cast at this
    simpa using this
  have hπφ {a} (ha : a ∈ π '' (A ^ m)) : π (φ a) = a := invFunOn_eq (by simpa using ha)
  calc
    #((A ^ m).image π) * #{x ∈ A ^ n | x ∈ H}
    _ = #(((A ^ m).image π).image φ) * #{x ∈ A ^ n | x ∈ H} := by
      rw [Finset.card_image_of_injOn (f := φ) (mod_cast hφ)]
    _ ≤ #(((A ^ m).image π).image φ * {x ∈ A ^ n | x ∈ H}) := by
      rw [Finset.card_mul_iff.2]
      simp only [Set.InjOn, coe_image, coe_pow, coe_filter, Set.mem_prod, Set.mem_image,
        exists_exists_and_eq_and, Set.mem_setOf_eq, and_imp, forall_exists_index, Prod.forall,
        Prod.mk.injEq]
      rintro _ a₁ b₁ hb₁ rfl - ha₁ _ a₂ b₂ hb₂ rfl - ha₂ hab
      have hπa₁ : π a₁ = 1 := (QuotientGroup.eq_one_iff _).2 ha₁
      have hπa₂ : π a₂ = 1 := (QuotientGroup.eq_one_iff _).2 ha₂
      have hπb : π b₁ = π b₂ := by
        simpa [hπφ, Set.mem_image_of_mem π, hb₁, hb₂, hπa₁, hπa₂] using congr(π $hab)
      simp_all
    _ ≤ #(A ^ (m + n)) := by
      gcongr
      simp only [mul_subset_iff, mem_image, exists_exists_and_eq_and, Finset.mem_filter, and_imp,
        forall_exists_index, forall_apply_eq_imp_iff₂, pow_add]
      rintro a ha b hb -
      exact mul_mem_mul (hφA <| Set.mem_image_of_mem _ <| mod_cast ha) hb

@[to_additive]
lemma le_card_quotient_mul_sq_inter_subgroup (hAsymm : A⁻¹ = A) :
    #A ≤ #(A.image <| QuotientGroup.mk' H) * #{x ∈ A ^ 2 | x ∈ H} := by
  classical
  set π := QuotientGroup.mk' H
  rw [card_eq_sum_card_image π]
  refine sum_le_card_nsmul _ _ _ <| forall_mem_image.2 fun a ha ↦ ?_
  calc
    #{a' ∈ A | π a' = π a}
    _ ≤ #({a' ∈ A | π a' = π a}⁻¹ * {a' ∈ A | π a' = π a}) :=
      card_le_card_mul_left ⟨a⁻¹, by simpa⟩
    _ ≤ #{x ∈ A⁻¹ * A | x ∈ H} := by
      gcongr
      simp only [mul_subset_iff, mem_inv', map_inv, mem_filter, and_imp]
      rintro x hx hxa y hy hya
      refine ⟨mul_mem_mul (by simpa) hy, (QuotientGroup.eq_one_iff _).1 (?_ : π _ = _)⟩
      simp [hya, ← hxa]
    _ = #{x ∈ A ^ 2 | x ∈ H} := by simp [hAsymm, sq]

end Finset
