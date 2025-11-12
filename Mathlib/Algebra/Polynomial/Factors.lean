/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Split polynomials

A polynomial `f : R[X]` factors if it is a product of constant and monic linear polynomials.

## Main definitions

* `Polynomial.Factors f`: A predicate on a polynomial `f` saying that `f` is a product of
  constant and monic linear polynomials.

## TODO

- Redefine `Splits` in terms of `Factors` and then deprecate `Splits`.

-/

variable {R : Type*}

namespace Polynomial

section Semiring

variable [Semiring R]

/-- A polynomial `Factors` if it is a product of constant and monic linear polynomials.
This will eventually replace `Polynomial.Splits`. -/
def Factors (f : R[X]) : Prop := f ∈ Submonoid.closure ({C a | a : R} ∪ {X + C a | a : R})

@[simp, aesop safe apply]
protected theorem Factors.C (a : R) : Factors (C a) :=
  Submonoid.mem_closure_of_mem (Set.mem_union_left _ ⟨a, rfl⟩)

@[simp, aesop safe apply]
protected theorem Factors.zero : Factors (0 : R[X]) := by
  simpa using Factors.C (0 : R)

@[simp, aesop safe apply]
protected theorem Factors.one : Factors (1 : R[X]) :=
  Factors.C (1 : R)

@[simp, aesop safe apply]
theorem Factors.X_add_C (a : R) : Factors (X + C a) :=
  Submonoid.mem_closure_of_mem (Set.mem_union_right _ ⟨a, rfl⟩)

@[simp, aesop safe apply]
protected theorem Factors.X : Factors (X : R[X]) := by
  simpa using Factors.X_add_C (0 : R)

@[simp, aesop safe apply]
protected theorem Factors.mul {f g : R[X]} (hf : Factors f) (hg : Factors g) :
    Factors (f * g) :=
  mul_mem hf hg

protected theorem Factors.C_mul {f : R[X]} (hf : Factors f) (a : R) : Factors (C a * f) :=
  (Factors.C a).mul hf

@[simp, aesop safe apply]
theorem Factors.listProd {l : List R[X]} (h : ∀ f ∈ l, Factors f) : Factors l.prod :=
  list_prod_mem h

@[simp, aesop safe apply]
protected theorem Factors.pow {f : R[X]} (hf : Factors f) (n : ℕ) : Factors (f ^ n) :=
  pow_mem hf n

theorem Factors.X_pow (n : ℕ) : Factors (X ^ n : R[X]) :=
  Factors.X.pow n

theorem Factors.C_mul_X_pow (a : R) (n : ℕ) : Factors (C a * X ^ n) :=
  (Factors.X_pow n).C_mul a

@[simp, aesop safe apply]
theorem Factors.monomial (n : ℕ) (a : R) : Factors (monomial n a) := by
  simp [← C_mul_X_pow_eq_monomial]

protected theorem Factors.map {f : R[X]} (hf : Factors f) {S : Type*} [Semiring S] (i : R →+* S) :
    Factors (map i f) := by
  induction hf using Submonoid.closure_induction <;> aesop

theorem factors_of_natDegree_eq_zero {f : R[X]} (hf : natDegree f = 0) :
    Factors f :=
  (natDegree_eq_zero.mp hf).choose_spec ▸ by aesop

theorem factors_of_degree_le_zero {f : R[X]} (hf : degree f ≤ 0) :
    Factors f :=
  factors_of_natDegree_eq_zero (natDegree_eq_zero_iff_degree_le_zero.mpr hf)

end Semiring

section CommSemiring

variable [CommSemiring R]

@[simp, aesop safe apply]
theorem Factors.multisetProd {m : Multiset R[X]} (hm : ∀ f ∈ m, Factors f) : Factors m.prod :=
  multiset_prod_mem _ hm

@[simp, aesop safe apply]
protected theorem Factors.prod {ι : Type*} {f : ι → R[X]} {s : Finset ι}
    (h : ∀ i ∈ s, Factors (f i)) : Factors (∏ i ∈ s, f i) :=
  prod_mem h

/-- See `factors_iff_exists_multiset` for the version with subtraction. -/
theorem factors_iff_exists_multiset' {f : R[X]} :
    Factors f ↔ ∃ m : Multiset R, f = C f.leadingCoeff * (m.map (X + C ·)).prod := by
  refine ⟨fun hf ↦ ?_, ?_⟩
  · let S : Submonoid R[X] := MonoidHom.mrange C
    have hS : S = {C a | a : R} := MonoidHom.coe_mrange C
    rw [Factors, Submonoid.closure_union, ← hS, Submonoid.closure_eq, Submonoid.mem_sup] at hf
    obtain ⟨-, ⟨a, rfl⟩, g, hg, rfl⟩ := hf
    obtain ⟨mg, hmg, rfl⟩ := Submonoid.exists_multiset_of_mem_closure hg
    choose! j hj using hmg
    have hmg : mg = (mg.map j).map (X + C ·) := by simp [Multiset.map_congr rfl hj]
    rw [hmg, leadingCoeff_mul_monic, leadingCoeff_C]
    · use mg.map j
    · rw [hmg]
      apply monic_multiset_prod_of_monic
      simp [monic_X_add_C]
  · rintro ⟨m, hm⟩
    exact hm ▸ (Factors.C _).mul (.multisetProd (by simp [Factors.X_add_C]))

theorem Factors.natDegree_le_one_of_irreducible {f : R[X]} (hf : Factors f)
    (h : Irreducible f) : natDegree f ≤ 1 := by
  nontriviality R
  obtain ⟨m, hm⟩ := factors_iff_exists_multiset'.mp hf
  rcases m.empty_or_exists_mem with rfl | ⟨a, ha⟩
  · rw [hm]
    simp
  · obtain ⟨m, rfl⟩ := Multiset.exists_cons_of_mem ha
    rw [Multiset.map_cons, Multiset.prod_cons] at hm
    rw [hm] at h
    simp only [irreducible_mul_iff, IsUnit.mul_iff, not_isUnit_X_add_C, false_and, and_false,
      or_false, false_or, ← Multiset.prod_toList, List.prod_isUnit_iff] at h
    have : m = 0 := by simpa [not_isUnit_X_add_C, ← Multiset.eq_zero_iff_forall_notMem] using h.1.2
    grw [hm, this, natDegree_mul_le]
    simp

end CommSemiring

section Ring

variable [Ring R]

@[simp, aesop safe apply]
theorem Factors.X_sub_C (a : R) : Factors (X - C a) := by
  simpa using Factors.X_add_C (-a)

@[aesop safe apply]
protected theorem Factors.neg {f : R[X]} (hf : Factors f) : Factors (-f) := by
  rw [← neg_one_mul, ← C_1, ← C_neg]
  exact hf.C_mul (-1)

@[simp]
theorem factors_neg_iff {f : R[X]} : Factors (-f) ↔ Factors f :=
  ⟨fun hf ↦ neg_neg f ▸ hf.neg, .neg⟩

end Ring

section CommRing

variable [CommRing R] {f g : R[X]}

theorem factors_iff_exists_multiset :
    Factors f ↔ ∃ m : Multiset R, f = C f.leadingCoeff * (m.map (X - C ·)).prod := by
  refine factors_iff_exists_multiset'.trans ⟨?_, ?_⟩ <;>
    rintro ⟨m, hm⟩ <;> exact ⟨m.map (- ·), by simpa⟩

theorem Factors.exists_eval_eq_zero (hf : Factors f) (hf0 : degree f ≠ 0) :
    ∃ a, eval a f = 0 := by
  obtain ⟨m, hm⟩ := factors_iff_exists_multiset.mp hf
  by_cases hf₀ : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf₀]
  obtain rfl | ⟨a, ha⟩ := m.empty_or_exists_mem
  · rw [hm, Multiset.map_zero, Multiset.prod_zero, mul_one, degree_C hf₀] at hf0
    contradiction
  obtain ⟨m, rfl⟩ := Multiset.exists_cons_of_mem ha
  exact ⟨a, hm ▸ by simp⟩

variable [IsDomain R]

theorem Factors.eq_prod_roots (hf : Factors f) :
    f = C f.leadingCoeff * (f.roots.map (X - C ·)).prod := by
  by_cases hf0 : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf0]
  · obtain ⟨m, hm⟩ := factors_iff_exists_multiset.mp hf
    suffices hf : f.roots = m by rwa [hf]
    rw [hm, roots_C_mul _ hf0, roots_multiset_prod_X_sub_C]

theorem Factors.natDegree_eq_card_roots (hf : Factors f) :
    f.natDegree = f.roots.card := by
  by_cases hf0 : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf0]
  · conv_lhs => rw [hf.eq_prod_roots, natDegree_C_mul hf0, natDegree_multiset_prod_X_sub_C_eq_card]

theorem Factors.roots_ne_zero (hf : Factors f) (hf0 : natDegree f ≠ 0) :
    f.roots ≠ 0 := by
  obtain ⟨a, ha⟩ := hf.exists_eval_eq_zero (degree_ne_of_natDegree_ne hf0)
  exact mt (· ▸ (mem_roots (by aesop)).mpr ha) (Multiset.notMem_zero a)

theorem factors_X_sub_C_mul_iff {a : R} : Factors ((X - C a) * f) ↔ Factors f := by
  refine ⟨fun hf ↦ ?_, ((Factors.X_sub_C _).mul ·)⟩
  by_cases hf₀ : f = 0
  · aesop
  have := hf.eq_prod_roots
  rw [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul,
    roots_mul (mul_ne_zero (X_sub_C_ne_zero _) hf₀), roots_X_sub_C,
    Multiset.singleton_add, Multiset.map_cons, Multiset.prod_cons, mul_left_comm] at this
  rw [mul_left_cancel₀ (X_sub_C_ne_zero _) this]
  aesop

theorem factors_mul_iff (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) :
    Factors (f * g) ↔ Factors f ∧ Factors g := by
  refine ⟨fun h ↦ ?_, and_imp.mpr .mul⟩
  generalize hp : f * g = p at *
  generalize hn : p.natDegree = n
  induction n generalizing p f g with
  | zero =>
    rw [← hp, natDegree_mul hf₀ hg₀, Nat.add_eq_zero_iff] at hn
    exact ⟨factors_of_natDegree_eq_zero hn.1, factors_of_natDegree_eq_zero hn.2⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := Factors.exists_eval_eq_zero h (degree_ne_of_natDegree_ne <| hn ▸ by aesop)
    have := dvd_iff_isRoot.mpr ha
    rw [← hp, (prime_X_sub_C a).dvd_mul] at this
    wlog hf : X - C a ∣ f with hf2
    · exact .symm <| hf2 n ih hg₀ hf₀ p ((mul_comm g f).trans hp) h hn a ha this.symm <|
        this.resolve_left hf
    obtain ⟨f, rfl⟩ := hf
    rw [mul_assoc] at hp; subst hp
    rw [natDegree_mul (by aesop) (by aesop), natDegree_X_sub_C, add_comm, Nat.succ_inj] at hn
    have := ih (by aesop) hg₀ (f * g) rfl  (factors_X_sub_C_mul_iff.mp h) hn
    aesop

theorem Factors.of_dvd (hg : Factors g) (hg₀ : g ≠ 0) (hfg : f ∣ g) : Factors f := by
  obtain ⟨g, rfl⟩ := hfg
  exact ((factors_mul_iff (by aesop) (by aesop)).mp hg).1

-- Todo: Remove or fix name once `Splits` is gone.
theorem Factors.splits (hf : Factors f) :
    f = 0 ∨ ∀ {g : R[X]}, Irreducible g → g ∣ f → degree g ≤ 1 :=
  or_iff_not_imp_left.mpr fun hf0 _ hg hgf ↦ degree_le_of_natDegree_le <|
    (hf.of_dvd hf0 hgf).natDegree_le_one_of_irreducible hg

end CommRing

section DivisionSemiring

variable [DivisionSemiring R]

theorem Factors.of_natDegree_le_one {f : R[X]} (hf : natDegree f ≤ 1) : Factors f := by
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hf
  by_cases ha : a = 0
  · aesop
  · rw [← mul_inv_cancel_left₀ ha b, C_mul, ← mul_add]
    exact (X_add_C (a⁻¹ * b)).C_mul a

theorem Factors.of_natDegree_eq_one {f : R[X]} (hf : natDegree f = 1) : Factors f :=
  of_natDegree_le_one hf.le

theorem Factors.of_degree_le_one {f : R[X]} (hf : degree f ≤ 1) : Factors f :=
  of_natDegree_le_one (natDegree_le_of_degree_le hf)

theorem Factors.of_degree_eq_one {f : R[X]} (hf : degree f = 1) : Factors f :=
  of_degree_le_one hf.le

end DivisionSemiring

section Field

variable [Field R]

open UniqueFactorizationMonoid in
-- Todo: Remove or fix name once `Splits` is gone.
theorem factors_iff_splits {f : R[X]} :
    Factors f ↔ f = 0 ∨ ∀ {g : R[X]}, Irreducible g → g ∣ f → degree g = 1 := by
  refine ⟨fun hf ↦ hf.splits.imp_right (forall₃_imp fun g hg hgf ↦
    (le_antisymm · (Nat.WithBot.one_le_iff_zero_lt.mpr hg.degree_pos))), ?_⟩
  rintro (rfl | hf)
  · aesop
  classical
  by_cases hf0 : f = 0
  · simp [hf0]
  obtain ⟨u, hu⟩ := factors_prod hf0
  rw [← hu]
  refine (Factors.multisetProd fun g hg ↦ ?_).mul
    (factors_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit u.isUnit))
  exact Factors.of_degree_eq_one (hf (irreducible_of_factor g hg) (dvd_of_mem_factors hg))

end Field

end Polynomial
