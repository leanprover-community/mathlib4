/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Polynomial.Roots

/-!
# Split polynomials

A polynomial `f : R[X]` factors if it is a product of constant and monic linear polynomials.

## Main definitions

* `Polynomial.Factors f`: A predicate on a polynomial `f` saying that `f` is a product of
  constant and monic linear polynomials.

-/

variable {R : Type*}

namespace Polynomial

section Semiring

variable [Semiring R]

/-- A polynomial factors if a product of constant and monic linear polynomials. -/
def Factors (f : R[X]) : Prop := f ∈ Submonoid.closure ({C a | a : R} ∪ {X + C a | a : R})

theorem factors_C (a : R) : Factors (C a) :=
  Submonoid.mem_closure_of_mem (Set.mem_union_left _ ⟨a, rfl⟩)

theorem factors_zero : Factors (0 : R[X]) := by
  simpa using factors_C (0 : R)

theorem factors_one : Factors (1 : R[X]) := by
  simpa using factors_C (1 : R)

theorem factors_X_add_C (a : R) : Factors (X + C a) :=
  Submonoid.mem_closure_of_mem (Set.mem_union_right _ ⟨a, rfl⟩)

theorem factors_X : Factors (X : R[X]) := by
  simpa using factors_X_add_C (0 : R)

protected theorem Factors.mul {f g : R[X]} (hf : Factors f) (hg : Factors g) :
    Factors (f * g) :=
  mul_mem hf hg

theorem Factors.C_mul {f : R[X]} (hf : Factors f) (a : R) : Factors (C a * f) :=
  (factors_C a).mul hf

theorem Factors.list_prod {l : List R[X]} (h : ∀ f ∈ l, Factors f) : Factors l.prod := by
  induction l with
  | nil => exact factors_one
  | cons f l ih =>
    exact (h f List.mem_cons_self).mul (ih (h · ∘ List.mem_cons_of_mem f))

protected theorem Factors.pow {f : R[X]} (hf : Factors f) (n : ℕ) : Factors (f ^ n) := by
  rw [← List.prod_replicate]
  exact Factors.list_prod (by simp [hf])

theorem factors_X_pow (n : ℕ) : Factors (X ^ n : R[X]) :=
  factors_X.pow n

theorem factors_C_mul_X_pow (a : R) (n : ℕ) : Factors (C a * X ^ n) :=
  (factors_X_pow n).C_mul a

theorem factors_monomial (n : ℕ) (a : R) : Factors (monomial n a) := by
  simp [← C_mul_X_pow_eq_monomial, factors_C_mul_X_pow]

protected theorem Factors.map {f : R[X]} (hf : Factors f) {S : Type*} [Semiring S] (i : R →+* S) :
    Factors (map i f) := by
  have h := Submonoid.mem_map_of_mem (mapRingHom i) hf
  rw [MonoidHom.map_mclosure, Set.image_union] at h
  refine Submonoid.closure_mono (Set.union_subset_union ?_ ?_) h <;>
    rintro - ⟨-, ⟨a, rfl⟩, rfl⟩ <;> exact ⟨i a, by simp⟩

theorem factors_of_isUnit [NoZeroDivisors R] {f : R[X]} (hf : IsUnit f) : Factors f :=
  (isUnit_iff.mp hf).choose_spec.2 ▸ factors_C _

end Semiring

section CommSemiring

variable [CommSemiring R]

theorem Factors.multiset_prod {m : Multiset R[X]} (hm : ∀ f ∈ m, Factors f) : Factors m.prod := by
  rw [← Multiset.prod_toList]
  exact Factors.list_prod (by simpa)

protected theorem Factors.prod {ι : Type*} {f : ι → R[X]} {s : Finset ι}
    (h : ∀ i ∈ s, Factors (f i)) : Factors (∏ i ∈ s, f i) := by
  rw [Finset.prod_eq_multiset_prod]
  exact Factors.multiset_prod (by simpa)

theorem factors_iff_exists_multiset_add {f : R[X]} :
    Factors f ↔ ∃ m : Multiset R, f = C f.leadingCoeff * (m.map (X + C ·)).prod := by
  refine ⟨fun hf ↦ ?_, ?_⟩
  · rw [Factors, Submonoid.closure_union, Submonoid.mem_sup] at hf
    obtain ⟨f, hf, g, hg, rfl⟩ := hf
    obtain ⟨mf, hmf, rfl⟩ := Submonoid.exists_multiset_of_mem_closure hf
    obtain ⟨mg, hmg, rfl⟩ := Submonoid.exists_multiset_of_mem_closure hg
    clear hf hg
    choose! i hi using hmf
    choose! j hj using hmg
    have hmf : mf = (mf.map i).map C := by simp [Multiset.map_congr rfl hi]
    have hmg : mg = (mg.map j).map (X + C ·) := by simp [Multiset.map_congr rfl hj]
    use mg.map j
    rw [← hmg, leadingCoeff_mul_monic]
    · have key := MonoidHom.map_multiset_prod C.toMonoidHom (mf.map i)
      rw [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at key
      rw [hmf, ← key, leadingCoeff_C]
    · rw [hmg]
      apply monic_multiset_prod_of_monic
      simp [monic_X_add_C]
  · rintro ⟨m, hm⟩
    exact hm ▸ (factors_C _).mul (Factors.multiset_prod (by simp [factors_X_add_C]))

end CommSemiring

section Ring

variable [Ring R]

theorem factors_X_sub_C (a : R) : Factors (X - C a) := by
  simpa using factors_X_add_C (-a)

protected theorem Factors.neg {f : R[X]} (hf : Factors f) : Factors (-f) := by
  rw [← neg_one_mul, ← C_1, ← C_neg]
  exact hf.C_mul (-1)

theorem factors_neg_iff {f : R[X]} : Factors (-f) ↔ Factors f :=
  ⟨fun hf ↦ neg_neg f ▸ hf.neg, Factors.neg⟩

end Ring

section CommRing

variable [CommRing R]

theorem factors_iff_exists_multiset {f : R[X]} :
    Factors f ↔ ∃ m : Multiset R, f = C f.leadingCoeff * (m.map (X - C ·)).prod := by
  refine factors_iff_exists_multiset_add.trans ⟨?_, ?_⟩ <;>
    rintro ⟨m, hm⟩ <;> exact ⟨m.map (- ·), by simpa⟩

variable [IsDomain R]

theorem Factors.eq_prod_roots {f : R[X]} (hf : Factors f) :
    f = C f.leadingCoeff * (f.roots.map (X - C ·)).prod := by
  by_cases hf0 : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf0]
  · obtain ⟨m, hm⟩ := factors_iff_exists_multiset.mp hf
    suffices hf : f.roots = m by rwa [hf]
    rw [hm, roots_C_mul _ hf0, roots_multiset_prod_X_sub_C]

theorem Factors.natDegree_eq_card_roots {f : R[X]} (hf : Factors f) :
    f.natDegree = f.roots.card := by
  by_cases hf0 : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf0]
  · conv_lhs => rw [hf.eq_prod_roots, natDegree_C_mul hf0, natDegree_multiset_prod_X_sub_C_eq_card]

theorem exists_root_of_factors {f : R[X]} (hf : Factors f) (hf0 : degree f ≠ 0) :
    ∃ a, eval a f = 0 := by
  rcases f.roots.empty_or_exists_mem with h | ⟨a, ha⟩
  · replace hf : f = 0 := by simpa [h, natDegree, hf0] using hf.natDegree_eq_card_roots
    exact ⟨0, hf ▸ eval_zero⟩
  · exact ⟨a, isRoot_of_mem_roots ha⟩

theorem roots_ne_zero_of_factors {f : R[X]} (hf : Factors f) (hf0 : natDegree f ≠ 0) :
    f.roots ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_root_of_factors hf (degree_ne_of_natDegree_ne hf0)
  contrapose! ha
  rw [Ne, ← IsRoot.def, ← mem_roots, ha]
  · exact Multiset.notMem_zero a
  · contrapose! hf0
    rw [hf0, natDegree_zero]

end CommRing

section Field

variable [Field R]

theorem factors_of_natDegree_le_one {f : R[X]} (hf : natDegree f ≤ 1) : Factors f := by
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hf
  by_cases ha : a = 0
  · simp [ha, factors_C]
  · rw [← mul_div_cancel₀ b ha, C_mul, ← mul_add]
    exact (factors_C a).mul (factors_X_add_C (b / a))

theorem factors_of_natDegree_eq_one {f : R[X]} (hf : natDegree f = 1) : Factors f :=
  factors_of_natDegree_le_one hf.le

theorem factors_of_degree_le_one {f : R[X]} (hf : degree f ≤ 1) : Factors f :=
  factors_of_natDegree_le_one (natDegree_le_of_degree_le hf)

theorem factors_of_degree_eq_one {f : R[X]} (hf : degree f = 1) : Factors f :=
  factors_of_degree_le_one hf.le

end Field

end Polynomial
