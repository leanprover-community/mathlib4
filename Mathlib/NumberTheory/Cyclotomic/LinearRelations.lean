/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.NumberTheory.Cyclotomic.LinearDisjoint

/-!
# Linear relations among roots of unity in cyclotomic fields

For `p` prime and coprime to `m`, a `ℚ⟮ζ^p⟯`-linear relation among the powers of `ζ^m` in the
cyclotomic field of order `p * m` forces all coefficients to be equal.
-/

@[expose] public section

noncomputable section

open Algebra IntermediateField
open scoped IntermediateField

set_option backward.isDefEq.respectTransparency false in
/-- In the cyclotomic field of order `p * m`, with `p` prime and coprime to `m`, a relation
`∑ bᵢ η^i = 0` over the `m`-part subfield forces all coefficients to be equal. -/
theorem IsPrimitiveRoot.coeffs_eq_of_sum_pow_eq_zero_prime_coprime
    {K : Type*} [Field K] [CharZero K] [Algebra.IsIntegral ℚ K]
    {p m : ℕ} (hp : Nat.Prime p) [NeZero p] [NeZero m]
    [IsCyclotomicExtension {p * m} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ (p * m)) (hcop : p.Coprime m) :
    let η : K := ζ ^ m
    let B : IntermediateField ℚ K := ℚ⟮ζ ^ p⟯
    ∀ (b : Fin p → B),
      (∑ i : Fin p, (algebraMap B K (b i)) * η ^ (i : ℕ)) = 0 →
        ∃ c : B, ∀ i : Fin p, b i = c := by
  classical
  intro η B b hsum
  have hη : IsPrimitiveRoot η p := by
    change IsPrimitiveRoot (ζ ^ m) p
    exact hζ.pow (mul_pos hp.pos (Nat.pos_of_neZero m)) (by rw [mul_comm])
  have linInd : LinearIndependent B (fun i : Fin (p - 1) => (η : K) ^ (i : ℕ)) := by
    let A : IntermediateField ℚ K := ℚ⟮η⟯
    haveI : IsScalarTower ℚ ↥B K :=
      @IntermediateField.isScalarTower_mid' ℚ K _ _ _ B
    haveI : IsCyclotomicExtension {p} ℚ A :=
      hη.intermediateField_adjoin_isCyclotomicExtension (K := ℚ) (L := K)
    haveI : IsScalarTower ℚ ↥A K :=
      @IntermediateField.isScalarTower_mid' ℚ K _ _ _ A
    let ηA : A := ⟨η, IntermediateField.subset_adjoin (F := ℚ) (S := ({η} : Set K))
      (Set.mem_singleton _)⟩
    have hηA : IsPrimitiveRoot ηA p := IsPrimitiveRoot.coe_submonoidClass_iff.mp hη
    have hdeg : (minpoly ℚ ηA).natDegree = p - 1 := by
      rw [show minpoly ℚ ηA = Polynomial.cyclotomic p ℚ from
        (IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible hηA
          (Polynomial.cyclotomic.irreducible_rat hp.pos)).symm,
        Polynomial.natDegree_cyclotomic, Nat.totient_prime hp]
    have ha : LinearIndependent ℚ (fun i : Fin (p - 1) => (ηA : A) ^ (i : ℕ)) :=
      (linearIndependent_pow (K := ℚ) (S := A) ηA).comp (finCongr hdeg.symm)
        (finCongr hdeg.symm).injective
    exact (hζ.linearDisjoint_adjoin_pow_of_coprime hcop).linearIndependent_left
      (ι := Fin (p - 1)) (a := fun i => ηA ^ (i : ℕ)) ha
  let v : Fin p → K := fun i => η ^ (i : ℕ)
  exact exists_eq_const_of_sum_smul_eq_zero_of_sum_eq_zero_of_linearIndependent hp.one_lt
    v (by rw [Fin.sum_univ_eq_sum_range]; exact hη.geom_sum_eq_zero hp.one_lt)
    (by simpa [v, finCongr] using linInd) b (by simpa [v, Algebra.smul_def] using hsum)

end
