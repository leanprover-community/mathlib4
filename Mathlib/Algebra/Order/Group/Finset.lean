/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Data.Finset.Lattice.Prod

/-!
# `Finset.sup` in a group
-/

open scoped Finset

assert_not_exists MonoidWithZero

namespace Multiset
variable {α : Type*} [DecidableEq α]

@[simp] lemma toFinset_nsmul (s : Multiset α) : ∀ n ≠ 0, (n • s).toFinset = s.toFinset
  | 0, h => by contradiction
  | n + 1, _ => by
    by_cases h : n = 0
    · rw [h, zero_add, one_nsmul]
    · rw [add_nsmul, toFinset_add, one_nsmul, toFinset_nsmul s n h, Finset.union_idempotent]

lemma toFinset_eq_singleton_iff (s : Multiset α) (a : α) :
    s.toFinset = {a} ↔ card s ≠ 0 ∧ s = card s • {a} := by
  refine ⟨fun H ↦ ⟨fun h ↦ ?_, ext' fun x ↦ ?_⟩, fun H ↦ ?_⟩
  · rw [card_eq_zero.1 h, toFinset_zero] at H
    exact Finset.singleton_ne_empty _ H.symm
  · rw [count_nsmul, count_singleton]
    by_cases hx : x = a
    · simp_rw [hx, ite_true, mul_one, count_eq_card]
      intro y hy
      rw [← mem_toFinset, H, Finset.mem_singleton] at hy
      exact hy.symm
    have hx' : x ∉ s := fun h' ↦ hx <| by rwa [← mem_toFinset, H, Finset.mem_singleton] at h'
    simp_rw [count_eq_zero_of_notMem hx', hx, ite_false, Nat.mul_zero]
  simpa only [toFinset_nsmul _ _ H.1, toFinset_singleton] using congr($(H.2).toFinset)

lemma toFinset_card_eq_one_iff (s : Multiset α) :
    #s.toFinset = 1 ↔ Multiset.card s ≠ 0 ∧ ∃ a : α, s = Multiset.card s • {a} := by
  simp_rw [Finset.card_eq_one, Multiset.toFinset_eq_singleton_iff, exists_and_left]

end Multiset

namespace Finset
variable {ι κ M G : Type*}

lemma fold_max_add [LinearOrder M] [Add M] [AddRightMono M] (s : Finset ι) (a : WithBot M)
    (f : ι → M) : s.fold max ⊥ (fun i ↦ ↑(f i) + a) = s.fold max ⊥ ((↑) ∘ f) + a := by
  classical induction s using Finset.induction_on <;> simp [*, max_add_add_right]

@[to_additive nsmul_inf']
lemma inf'_pow [LinearOrder M] [Monoid M] [MulLeftMono M] [MulRightMono M] (s : Finset ι)
    (f : ι → M) (n : ℕ) (hs) : s.inf' hs f ^ n = s.inf' hs fun a ↦ f a ^ n :=
  map_finset_inf' (OrderHom.mk _ <| pow_left_mono n) hs _

@[to_additive nsmul_sup']
lemma sup'_pow [LinearOrder M] [Monoid M] [MulLeftMono M] [MulRightMono M] (s : Finset ι)
    (f : ι → M) (n : ℕ) (hs) : s.sup' hs f ^ n = s.sup' hs fun a ↦ f a ^ n :=
  map_finset_sup' (OrderHom.mk _ <| pow_left_mono n) hs _

section Group
variable [Group G] [LinearOrder G]

@[to_additive /-- Also see `Finset.sup'_add'` that works for canonically ordered monoids. -/]
lemma sup'_mul [MulRightMono G] (s : Finset ι) (f : ι → G) (a : G) (hs) :
    s.sup' hs f * a = s.sup' hs fun i ↦ f i * a := map_finset_sup' (OrderIso.mulRight a) hs f

set_option linter.docPrime false in
@[to_additive /-- Also see `Finset.add_sup''` that works for canonically ordered monoids. -/]
lemma mul_sup' [MulLeftMono G] (s : Finset ι) (f : ι → G) (a : G) (hs) :
    a * s.sup' hs f = s.sup' hs fun i ↦ a * f i := map_finset_sup' (OrderIso.mulLeft a) hs f

end Group

section CanonicallyLinearOrderedAddCommMonoid
variable [AddCommMonoid M] [LinearOrder M] [CanonicallyOrderedAdd M]
  [Sub M] [AddLeftReflectLE M] [OrderedSub M] {s : Finset ι} {t : Finset κ}

/-- Also see `Finset.sup'_add` that works for ordered groups. -/
lemma sup'_add' (s : Finset ι) (f : ι → M) (a : M) (hs : s.Nonempty) :
    s.sup' hs f + a = s.sup' hs fun i ↦ f i + a := by
  apply le_antisymm
  · apply add_le_of_le_tsub_right_of_le
    · exact Finset.le_sup'_of_le _ hs.choose_spec le_add_self
    · exact Finset.sup'_le _ _ fun i hi ↦ le_tsub_of_add_le_right (Finset.le_sup' (f · + a) hi)
  · exact Finset.sup'_le _ _ fun i hi ↦ by grw [← Finset.le_sup' _ hi]

/-- Also see `Finset.add_sup'` that works for ordered groups. -/
lemma add_sup'' (hs : s.Nonempty) (f : ι → M) (a : M) :
    a + s.sup' hs f = s.sup' hs fun i ↦ a + f i := by simp_rw [add_comm a, Finset.sup'_add']

variable [OrderBot M]

protected lemma sup_add (hs : s.Nonempty) (f : ι → M) (a : M) :
    s.sup f + a = s.sup fun i ↦ f i + a := by
  rw [← Finset.sup'_eq_sup hs, ← Finset.sup'_eq_sup hs, sup'_add']

protected lemma add_sup (hs : s.Nonempty) (f : ι → M) (a : M) :
    a + s.sup f = s.sup fun i ↦ a + f i := by
  rw [← Finset.sup'_eq_sup hs, ← Finset.sup'_eq_sup hs, add_sup'']

lemma sup_add_sup (hs : s.Nonempty) (ht : t.Nonempty) (f : ι → M) (g : κ → M) :
    s.sup f + t.sup g = (s ×ˢ t).sup fun ij ↦ f ij.1 + g ij.2 := by
  simp only [Finset.sup_add hs, Finset.add_sup ht, Finset.sup_product_left]

end CanonicallyLinearOrderedAddCommMonoid
end Finset
