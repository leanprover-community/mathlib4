/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Kim Morrison
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.AbelRuffini
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import HexBerlekampZassenhausMathlib.FactorTactic
public meta import HexBerlekampZassenhausMathlib.FactorTactic
public import HexRealRootsMathlib.IsolateRootsElab

/-!
# Construction of an algebraic number that is not solvable by radicals

The polynomial `X ^ 5 - 4 * X + 2` is irreducible and has exactly three real roots.
Hex certifies these two computations using `irreducibility` and `isolate_roots`.
Its Galois group is therefore the symmetric group on five letters, which is not solvable.
The Abel–Ruffini theorem implies that none of its roots is solvable by radicals.
-/

public section

namespace AbelRuffini

open Function Polynomial Polynomial.Gal

attribute [local instance] splits_ℚ_ℂ

/-- The quintic used to construct an algebraic number not solvable by radicals. -/
noncomputable def quintic (R : Type*) [CommRing R] : R[X] := X ^ 5 - 4 * X + 2

private theorem quintic_monic (R : Type*) [CommRing R] [Nontrivial R] :
    (quintic R).Monic := by
  dsimp [quintic]
  monicity <;> norm_num

private theorem quintic_irreducible : Irreducible (quintic ℚ) := by
  have h : Irreducible (quintic ℤ) := irreducibility (quintic ℤ)
  simpa [quintic] using
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      (quintic_monic ℤ).isPrimitive).mp h

private noncomputable def quintic_isolation : Hex.IsolatedRealRoots (quintic ℚ) 3 :=
  isolate_roots (X ^ 5 - 4 * X + 2 : ℚ[X])

private theorem card_rootSet_of_isolation {p : ℚ[X]} {n : ℕ}
    (H : Hex.IsolatedRealRoots p n) (hp : p ≠ 0) :
    Fintype.card (p.rootSet ℝ) = n := by
  classical
  choose r hr hu using H.unique_root
  have hm : StrictMono r := by
    intro i j hij
    have ho : (H.intervals[i].2 : ℝ) ≤ (H.intervals[j].1 : ℝ) := by
      exact_mod_cast H.ordered i j hij
    exact ((hr i).2.2.trans ho).trans_lt (hr j).2.1
  let f : Fin n → p.rootSet ℝ := fun i => ⟨r i, (mem_rootSet_of_ne hp).2 (hr i).1⟩
  have hinj : Injective f := fun _ _ hij => hm.injective (congrArg Subtype.val hij)
  have hsurj : Surjective f := by
    rintro ⟨x, hx⟩
    have hx0 := (mem_rootSet_of_ne hp).1 hx
    obtain ⟨i, hi⟩ := H.covers x hx0
    exact ⟨i, Subtype.ext (hu i x ⟨hx0, hi⟩).symm⟩
  simpa using (Fintype.card_of_bijective ⟨hinj, hsurj⟩).symm

private theorem quintic_real_roots : Fintype.card ((quintic ℚ).rootSet ℝ) = 3 :=
  card_rootSet_of_isolation quintic_isolation (quintic_monic ℚ).ne_zero

private theorem quintic_natDegree : (quintic ℚ).natDegree = 5 := by
  dsimp [quintic]
  compute_degree <;> norm_num

private theorem quintic_complex_roots : Fintype.card ((quintic ℚ).rootSet ℂ) = 5 :=
  (card_rootSet_eq_natDegree quintic_irreducible.separable (IsAlgClosed.splits _)).trans
    quintic_natDegree

private theorem quintic_gal : Bijective (galActionHom (quintic ℚ) ℂ) := by
  apply galActionHom_bijective_of_prime_degree' quintic_irreducible
  · rw [quintic_natDegree]
    decide
  · rw [quintic_real_roots, quintic_complex_roots]
    decide
  · rw [quintic_real_roots, quintic_complex_roots]
    decide

/-- No complex root of `X ^ 5 - 4 * X + 2` is solvable by radicals over `ℚ`. -/
theorem not_solvable_by_rad (x : ℂ) (hx : aeval x (quintic ℚ) = 0) :
    x ∉ solvableByRad ℚ ℂ := by
  apply mt (isSolvable_gal_of_irreducible · quintic_irreducible hx)
  intro h
  refine Equiv.Perm.not_isSolvable _ (le_of_eq ?_)
    (Group.isSolvable_of_surjective quintic_gal.2)
  rw_mod_cast [Cardinal.mk_fintype, quintic_complex_roots]

/-- **Abel–Ruffini theorem** -/
theorem exists_not_solvable_by_rad : ∃ x : ℂ, IsAlgebraic ℚ x ∧ x ∉ solvableByRad ℚ ℂ := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ (quintic ℚ)
    (by rw [degree_eq_natDegree (quintic_monic ℚ).ne_zero, quintic_natDegree]; norm_num)
  exact ⟨x, ⟨quintic ℚ, (quintic_monic ℚ).ne_zero, hx⟩, not_solvable_by_rad x hx⟩

end AbelRuffini
