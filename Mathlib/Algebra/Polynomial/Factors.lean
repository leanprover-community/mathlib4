/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# Split polynomials

A polynomial `f : R[X]` splits if it is a product of constant and monic linear polynomials.

## Main definitions

* `Polynomial.Splits f`: A predicate on a polynomial `f` saying that `f` is a product of
  constant and monic linear polynomials.

-/

@[expose] public section

variable {R : Type*}

namespace Polynomial

section Semiring

variable [Semiring R]

/-- A polynomial `Splits` if it is a product of constant and monic linear polynomials.
This will eventually replace `Polynomial.Splits`. -/
def Splits (f : R[X]) : Prop := f ∈ Submonoid.closure ({C a | a : R} ∪ {X + C a | a : R})

@[simp, aesop safe apply]
protected theorem Splits.C (a : R) : Splits (C a) :=
  Submonoid.mem_closure_of_mem (Set.mem_union_left _ ⟨a, rfl⟩)

@[simp, aesop safe apply]
protected theorem Splits.zero : Splits (0 : R[X]) := by
  simpa using Splits.C (0 : R)

@[simp, aesop safe apply]
protected theorem Splits.one : Splits (1 : R[X]) :=
  Splits.C (1 : R)

@[simp, aesop safe apply]
theorem Splits.X_add_C (a : R) : Splits (X + C a) :=
  Submonoid.mem_closure_of_mem (Set.mem_union_right _ ⟨a, rfl⟩)

@[simp, aesop safe apply]
protected theorem Splits.X : Splits (X : R[X]) := by
  simpa using Splits.X_add_C (0 : R)

@[simp, aesop safe apply]
protected theorem Splits.mul {f g : R[X]} (hf : Splits f) (hg : Splits g) :
    Splits (f * g) :=
  mul_mem hf hg

protected theorem Splits.C_mul {f : R[X]} (hf : Splits f) (a : R) : Splits (C a * f) :=
  (Splits.C a).mul hf

@[simp, aesop safe apply]
theorem Splits.listProd {l : List R[X]} (h : ∀ f ∈ l, Splits f) : Splits l.prod :=
  list_prod_mem h

@[simp, aesop safe apply]
protected theorem Splits.pow {f : R[X]} (hf : Splits f) (n : ℕ) : Splits (f ^ n) :=
  pow_mem hf n

theorem Splits.X_pow (n : ℕ) : Splits (X ^ n : R[X]) :=
  Splits.X.pow n

theorem Splits.C_mul_X_pow (a : R) (n : ℕ) : Splits (C a * X ^ n) :=
  (Splits.X_pow n).C_mul a

@[simp, aesop safe apply]
theorem Splits.monomial (n : ℕ) (a : R) : Splits (monomial n a) := by
  simp [← C_mul_X_pow_eq_monomial]

protected theorem Splits.map {f : R[X]} (hf : Splits f) {S : Type*} [Semiring S] (i : R →+* S) :
    Splits (map i f) := by
  induction hf using Submonoid.closure_induction <;> aesop

theorem splits_of_natDegree_eq_zero {f : R[X]} (hf : natDegree f = 0) :
    Splits f :=
  (natDegree_eq_zero.mp hf).choose_spec ▸ by aesop

theorem splits_of_degree_le_zero {f : R[X]} (hf : degree f ≤ 0) :
    Splits f :=
  splits_of_natDegree_eq_zero (natDegree_eq_zero_iff_degree_le_zero.mpr hf)

end Semiring

section CommSemiring

variable [CommSemiring R]

@[simp, aesop safe apply]
theorem Splits.multisetProd {m : Multiset R[X]} (hm : ∀ f ∈ m, Splits f) : Splits m.prod :=
  multiset_prod_mem _ hm

@[simp, aesop safe apply]
protected theorem Splits.prod {ι : Type*} {f : ι → R[X]} {s : Finset ι}
    (h : ∀ i ∈ s, Splits (f i)) : Splits (∏ i ∈ s, f i) :=
  prod_mem h

lemma Splits.taylor {p : R[X]} (hp : p.Splits) (r : R) : (p.taylor r).Splits := by
  have (i : _) : (X + C r + C i).Splits := by simpa [add_assoc] using Splits.X_add_C (r + i)
  induction hp using Submonoid.closure_induction <;> aesop

/-- See `splits_iff_exists_multiset` for the version with subtraction. -/
theorem splits_iff_exists_multiset' {f : R[X]} :
    Splits f ↔ ∃ m : Multiset R, f = C f.leadingCoeff * (m.map (X + C ·)).prod := by
  refine ⟨fun hf ↦ ?_, ?_⟩
  · let S : Submonoid R[X] := MonoidHom.mrange C
    have hS : S = {C a | a : R} := MonoidHom.coe_mrange C
    rw [Splits, Submonoid.closure_union, ← hS, Submonoid.closure_eq, Submonoid.mem_sup] at hf
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
    exact hm ▸ (Splits.C _).mul (.multisetProd (by simp [Splits.X_add_C]))

theorem Splits.natDegree_le_one_of_irreducible {f : R[X]} (hf : Splits f)
    (h : Irreducible f) : natDegree f ≤ 1 := by
  nontriviality R
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset'.mp hf
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
theorem Splits.X_sub_C (a : R) : Splits (X - C a) := by
  simpa using Splits.X_add_C (-a)

@[aesop safe apply]
protected theorem Splits.neg {f : R[X]} (hf : Splits f) : Splits (-f) := by
  rw [← neg_one_mul, ← C_1, ← C_neg]
  exact hf.C_mul (-1)

@[simp]
theorem splits_neg_iff {f : R[X]} : Splits (-f) ↔ Splits f :=
  ⟨fun hf ↦ neg_neg f ▸ hf.neg, .neg⟩

theorem Splits.comp_neg_X {f : R[X]} (hf : f.Splits) : (f.comp (-X)).Splits := by
  refine Submonoid.closure_induction ?_ (by simp)
    (fun f g _ _ hf hg ↦ mul_comp_neg_X f g ▸ hf.mul hg) hf
  · rintro f (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · simp
    · rw [add_comp, X_comp, C_comp, neg_add_eq_sub, ← neg_sub]
      exact (X_sub_C a).neg

end Ring

section CommRing

variable [CommRing R] {f g : R[X]}

theorem splits_iff_exists_multiset :
    Splits f ↔ ∃ m : Multiset R, f = C f.leadingCoeff * (m.map (X - C ·)).prod := by
  refine splits_iff_exists_multiset'.trans ⟨?_, ?_⟩ <;>
    rintro ⟨m, hm⟩ <;> exact ⟨m.map (- ·), by simpa⟩

theorem Splits.exists_eval_eq_zero (hf : Splits f) (hf0 : degree f ≠ 0) :
    ∃ a, eval a f = 0 := by
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset.mp hf
  by_cases hf₀ : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf₀]
  obtain rfl | ⟨a, ha⟩ := m.empty_or_exists_mem
  · rw [hm, Multiset.map_zero, Multiset.prod_zero, mul_one, degree_C hf₀] at hf0
    contradiction
  obtain ⟨m, rfl⟩ := Multiset.exists_cons_of_mem ha
  exact ⟨a, hm ▸ by simp⟩

variable [IsDomain R]

theorem Splits.eq_prod_roots (hf : Splits f) :
    f = C f.leadingCoeff * (f.roots.map (X - C ·)).prod := by
  by_cases hf0 : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf0]
  · obtain ⟨m, hm⟩ := splits_iff_exists_multiset.mp hf
    suffices hf : f.roots = m by rwa [hf]
    rw [hm, roots_C_mul _ hf0, roots_multiset_prod_X_sub_C]

theorem Splits.natDegree_eq_card_roots (hf : Splits f) :
    f.natDegree = f.roots.card := by
  by_cases hf0 : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf0]
  · conv_lhs => rw [hf.eq_prod_roots, natDegree_C_mul hf0, natDegree_multiset_prod_X_sub_C_eq_card]

theorem Splits.roots_ne_zero (hf : Splits f) (hf0 : natDegree f ≠ 0) :
    f.roots ≠ 0 := by
  obtain ⟨a, ha⟩ := hf.exists_eval_eq_zero (degree_ne_of_natDegree_ne hf0)
  exact mt (· ▸ (mem_roots (by aesop)).mpr ha) (Multiset.notMem_zero a)

theorem splits_X_sub_C_mul_iff {a : R} : Splits ((X - C a) * f) ↔ Splits f := by
  refine ⟨fun hf ↦ ?_, ((Splits.X_sub_C _).mul ·)⟩
  by_cases hf₀ : f = 0
  · aesop
  have := hf.eq_prod_roots
  rw [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul,
    roots_mul (mul_ne_zero (X_sub_C_ne_zero _) hf₀), roots_X_sub_C,
    Multiset.singleton_add, Multiset.map_cons, Multiset.prod_cons, mul_left_comm] at this
  rw [mul_left_cancel₀ (X_sub_C_ne_zero _) this]
  aesop

theorem splits_mul_iff (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) :
    Splits (f * g) ↔ Splits f ∧ Splits g := by
  refine ⟨fun h ↦ ?_, and_imp.mpr .mul⟩
  generalize hp : f * g = p at *
  generalize hn : p.natDegree = n
  induction n generalizing p f g with
  | zero =>
    rw [← hp, natDegree_mul hf₀ hg₀, Nat.add_eq_zero_iff] at hn
    exact ⟨splits_of_natDegree_eq_zero hn.1, splits_of_natDegree_eq_zero hn.2⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := Splits.exists_eval_eq_zero h (degree_ne_of_natDegree_ne <| hn ▸ by aesop)
    have := dvd_iff_isRoot.mpr ha
    rw [← hp, (prime_X_sub_C a).dvd_mul] at this
    wlog hf : X - C a ∣ f with hf2
    · exact .symm <| hf2 n ih hg₀ hf₀ p ((mul_comm g f).trans hp) h hn a ha this.symm <|
        this.resolve_left hf
    obtain ⟨f, rfl⟩ := hf
    rw [mul_assoc] at hp; subst hp
    rw [natDegree_mul (by aesop) (by aesop), natDegree_X_sub_C, add_comm, Nat.succ_inj] at hn
    have := ih (by aesop) hg₀ (f * g) rfl  (splits_X_sub_C_mul_iff.mp h) hn
    aesop

theorem Splits.of_dvd (hg : Splits g) (hg₀ : g ≠ 0) (hfg : f ∣ g) : Splits f := by
  obtain ⟨g, rfl⟩ := hfg
  exact ((splits_mul_iff (by aesop) (by aesop)).mp hg).1

-- Todo: Remove or fix name once `Splits` is gone.
theorem Splits.splits (hf : Splits f) :
    f = 0 ∨ ∀ {g : R[X]}, Irreducible g → g ∣ f → degree g ≤ 1 :=
  or_iff_not_imp_left.mpr fun hf0 _ hg hgf ↦ degree_le_of_natDegree_le <|
    (hf.of_dvd hf0 hgf).natDegree_le_one_of_irreducible hg

lemma map_sub_sprod_roots_eq_prod_map_eval
    (s : Multiset R) (g : R[X]) (hg : g.Monic) (hg' : g.Splits) :
    ((s ×ˢ g.roots).map fun ij ↦ ij.1 - ij.2).prod = (s.map g.eval).prod := by
  have := hg'.eq_prod_roots
  rw [hg.leadingCoeff, map_one, one_mul] at this
  conv_rhs => rw [this]
  simp_rw [eval_multiset_prod, Multiset.prod_map_product_eq_prod_prod, Multiset.map_map]
  congr! with x hx
  ext; simp

lemma map_sub_roots_sprod_eq_prod_map_eval
    (s : Multiset R) (g : R[X]) (hg : g.Monic) (hg' : g.Splits) :
    ((g.roots ×ˢ s).map fun ij ↦ ij.1 - ij.2).prod =
      (-1) ^ (s.card * g.roots.card) * (s.map g.eval).prod := by
  trans ((s ×ˢ g.roots).map fun ij ↦ (-1) * (ij.1 - ij.2)).prod
  · rw [← Multiset.map_swap_product, Multiset.map_map]; simp
  · rw [Multiset.prod_map_mul]; simp [map_sub_sprod_roots_eq_prod_map_eval _ _ hg hg']
end CommRing

section DivisionSemiring

variable [DivisionSemiring R]

theorem Splits.of_natDegree_le_one {f : R[X]} (hf : natDegree f ≤ 1) : Splits f := by
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hf
  by_cases ha : a = 0
  · aesop
  · rw [← mul_inv_cancel_left₀ ha b, C_mul, ← mul_add]
    exact (X_add_C (a⁻¹ * b)).C_mul a

theorem Splits.of_natDegree_eq_one {f : R[X]} (hf : natDegree f = 1) : Splits f :=
  of_natDegree_le_one hf.le

theorem Splits.of_degree_le_one {f : R[X]} (hf : degree f ≤ 1) : Splits f :=
  of_natDegree_le_one (natDegree_le_of_degree_le hf)

theorem Splits.of_degree_eq_one {f : R[X]} (hf : degree f = 1) : Splits f :=
  of_degree_le_one hf.le

end DivisionSemiring

section Field

variable [Field R]

open UniqueFactorizationMonoid in
-- Todo: Remove or fix name.
theorem splits_iff_splits {f : R[X]} :
    Splits f ↔ f = 0 ∨ ∀ {g : R[X]}, Irreducible g → g ∣ f → degree g = 1 := by
  refine ⟨fun hf ↦ hf.splits.imp_right (forall₃_imp fun g hg hgf ↦
    (le_antisymm · (Nat.WithBot.one_le_iff_zero_lt.mpr hg.degree_pos))), ?_⟩
  rintro (rfl | hf)
  · aesop
  classical
  by_cases hf0 : f = 0
  · simp [hf0]
  obtain ⟨u, hu⟩ := factors_prod hf0
  rw [← hu]
  refine (Splits.multisetProd fun g hg ↦ ?_).mul
    (splits_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit u.isUnit))
  exact Splits.of_degree_eq_one (hf (irreducible_of_factor g hg) (dvd_of_mem_factors hg))

end Field

end Polynomial
