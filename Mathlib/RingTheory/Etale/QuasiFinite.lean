/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# Etale local structure of finite maps

We construct etale neighborhoods that split fibers of finite algebras.

## Main results
- `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`:
Let `S` be a module-finite `R`-algebra, and `q` a prime lying over `p`.
We may construct an etale `R`-algebra `R'` and a prime `P` lying over `p` with `κ(P) = κ(p)`,
such that `R' ⊗[R] S = A × B` and there exists a unique prime in `A` lying over `P`.
This prime will also lie over `q`.

-/

@[expose] public section

open TensorProduct

section BijectiveResidueField

variable {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R S]
    {p : Ideal R} {q : Ideal R'} [p.IsPrime] [q.IsPrime] [q.LiesOver p]

/-- If `q` is a prime of `R'` lying over `p`, a prime of `R`, such that `κ(q) = κ(p)`, then
the fiber of `R' → R' ⊗[R] S` over `q` is in bijection with the fiber of `R → S` over `p`. -/
noncomputable
def Ideal.fiberIsoOfBijectiveResidueField
    (H : Function.Bijective (Ideal.ResidueField.mapₐ p q (Algebra.ofId _ _) (q.over_def p))) :
    q.primesOver (R' ⊗[R] S) ≃o p.primesOver S :=
  let e : q.Fiber (R' ⊗[R] S) ≃ₐ[p.ResidueField] p.Fiber S :=
    ((Algebra.TensorProduct.cancelBaseChange _ _ q.ResidueField _ _).restrictScalars _).trans
      (Algebra.TensorProduct.congr (.symm <| .ofBijective (Algebra.ofId _ _) H) .refl)
  (PrimeSpectrum.primesOverOrderIsoFiber ..).trans <|
    (PrimeSpectrum.comapEquiv e.toRingEquiv).trans (PrimeSpectrum.primesOverOrderIsoFiber ..).symm

lemma Ideal.comap_fiberIsoOfBijectiveResidueField_symm
    (H : Function.Bijective (Ideal.ResidueField.mapₐ p q (Algebra.ofId _ _) (q.over_def p)))
    (Q : p.primesOver S) :
    ((Ideal.fiberIsoOfBijectiveResidueField H).symm Q).1.comap
      (RingHomClass.toRingHom Algebra.TensorProduct.includeRight) = Q.1 := by
  ext x
  simp [Ideal.fiberIsoOfBijectiveResidueField,
    PrimeSpectrum.primesOverOrderIsoFiber, PrimeSpectrum.preimageOrderIsoFiber,
    PrimeSpectrum.preimageEquivFiber]

@[simp]
lemma Ideal.comap_fiberIsoOfBijectiveResidueField_apply
    (H : Function.Bijective (Ideal.ResidueField.mapₐ p q (Algebra.ofId _ _) (q.over_def p)))
    (Q : q.primesOver (R' ⊗[R] S)) :
    (Ideal.fiberIsoOfBijectiveResidueField H Q).1 =
      Q.1.comap Algebra.TensorProduct.includeRight := by
  simpa using (Ideal.comap_fiberIsoOfBijectiveResidueField_symm H
    (Ideal.fiberIsoOfBijectiveResidueField H Q)).symm

lemma Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap
    (H : Function.Bijective (Ideal.ResidueField.mapₐ p q (Algebra.ofId _ _) (q.over_def p)))
    (P₁ P₂ : Ideal (R' ⊗[R] S)) [P₁.IsPrime] [P₂.IsPrime] [P₁.LiesOver q] [P₂.LiesOver q]
    (H₂ : P₁.comap Algebra.TensorProduct.includeRight.toRingHom =
      P₂.comap Algebra.TensorProduct.includeRight.toRingHom) : P₁ = P₂ := by
  refine congr_arg Subtype.val ((Ideal.fiberIsoOfBijectiveResidueField
  (S := S) H).injective (a₁ := ⟨P₁, ‹_›, ‹_›⟩) (a₂ := ⟨P₂, ‹_›, ‹_›⟩) (by ext1; simpa))

end BijectiveResidueField

section

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

open Polynomial in
/--
Let `S` be a module-finite `R`-algebra, and `q` a prime lying over `p`.
We may construct an etale `R`-algebra `R'` and a prime `P` lying over `p` with `κ(P) = κ(p)`,
such that `R' ⊗[R] S = A × B` and there exists a unique prime in `A` lying over `P`.
This prime will also lie over `q`.

The actual lemma is stated in terms of the idempotent element `e = (1, 0)`.
-/
@[stacks 00UJ]
lemma Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P : Ideal R')
      (_ : P.IsPrime) (_ : P.LiesOver p) (e : R' ⊗[R] S) (_ : IsIdempotentElem e)
      (P' : Ideal (R' ⊗[R] S)) (_ : P'.IsPrime) (_ : P'.LiesOver P), P'.comap
        Algebra.TensorProduct.includeRight.toRingHom = q ∧ e ∉ P' ∧
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
      ∀ P'' : Ideal (R' ⊗[R] S), P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P' := by
  classical
  obtain ⟨s, hsq, hs⟩ := Ideal.exists_not_mem_forall_mem_of_ne_of_liesOver p q
  obtain ⟨m, f, b, hfm, hbm, hab, hfab, hf⟩ : ∃ (m : ℕ) (f : R[X])
      (b : p.ResidueField[X]), f.Monic ∧ b.Monic ∧ IsCoprime (X ^ (m + 1)) b ∧
        f.map (algebraMap _ _) = X ^ (m + 1) * b ∧ aeval s f = 0 := by
    have hs := Algebra.IsIntegral.isIntegral (R := R) s
    let f := X * minpoly R s
    obtain ⟨q, hq, hq'⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd
      ((minpoly R s).map (algebraMap R p.ResidueField)) ((minpoly.monic hs).map _).ne_zero 0
    have hqm : q.Monic := by
      simpa [((minpoly.monic hs).map _).leadingCoeff] using congr(leadingCoeff $hq).symm
    set m' := rootMultiplicity 0 ((minpoly R s).map (algebraMap R p.ResidueField))
    refine ⟨m', f, q, monic_X.mul (minpoly.monic hs), hqm, ?_,
      by simp [f, hq, pow_succ', mul_assoc], by simp [f]⟩
    simpa [IsCoprime.pow_left_iff,
      (prime_X (R := p.ResidueField)).irreducible.coprime_iff_not_dvd] using hq'
  obtain ⟨R', _, _, _, P, _, _, a', b', hP, ha'm, hb'm, hfab', ⟨c, d, hcd⟩, ha', hb'⟩ :=
    exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime p f
      (X ^ (m + 1)) b hfm (monic_X.pow _) hbm hfab hab
  let s' : R' ⊗[R] S := 1 ⊗ₜ s
  have hs'f : aeval s' f = 0 :=
    show aeval (Algebra.TensorProduct.includeRight s) f = 0 by rw [aeval_algHom_apply, hf, map_zero]
  let e := aeval s' (c * a')
  have he : IsIdempotentElem e := by
    dsimp only [e, IsIdempotentElem]
    nth_rw 2 [eq_sub_iff_add_eq.mpr hcd]
    rw [← map_mul, mul_sub, mul_one, mul_mul_mul_comm, ← hfab']
    simp only [map_mul, map_sub, aeval_map_algebraMap, hs'f, mul_zero, sub_zero]
  let P' := (Ideal.fiberIsoOfBijectiveResidueField hP).symm ⟨q, ‹_›, ‹_›⟩
  have hP'q : P'.1.comap Algebra.TensorProduct.includeRight.toRingHom = q :=
    Ideal.comap_fiberIsoOfBijectiveResidueField_symm ..
  have hs'P' : s' ∉ P'.1 := mt (fun h ↦ hP'q.le h) hsq
  have ha'P' : aeval s' a' ∉ P'.1 := by
    simpa using show IsScalarTower.toAlgHom R' _ P'.1.ResidueField (aeval s' a') ≠ 0 by
      rw [← aeval_algHom_apply, ← aeval_map_algebraMap P.ResidueField, ← ha']; simpa
  have hb'P' : aeval s' b' ∈ P'.1 := by
    rw [← Ideal.IsPrime.mul_mem_left_iff ha'P', ← map_mul, ← hfab']
    simp [hs'f]
  have heP' : e ∉ P'.1 := by
    intro H
    have := P'.1.mul_mem_left (aeval s' d) hb'P'
    rw [← map_mul, eq_sub_iff_add_eq'.mpr hcd, map_sub, Submodule.sub_mem_iff_left _ H,
      map_one] at this
    exact Ideal.one_notMem _ this
  refine ⟨_, inferInstance, inferInstance, inferInstance, P, ‹_›, ‹_›,
    e, he, P', inferInstance, P'.2.2, hP'q, heP', hP, fun P'' _ _ H ↦ ?_⟩
  apply Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hP
  rw [hP'q]
  contrapose! H
  have : s' ∈ P'' := hs _ inferInstance H (by simp [Ideal.liesOver_iff, Ideal.under,
    Ideal.comap_comap, Ideal.over_def P p, Ideal.over_def P'' P, ← IsScalarTower.algebraMap_eq])
  rw [← Ideal.algebraMap_residueField_eq_zero, ← aeval_algebraMap_apply,
    Ideal.algebraMap_residueField_eq_zero.mpr this, ← eval_map_algebraMap, Polynomial.map_mul,
    mul_comm, ← (Ideal.ResidueField.mapₐ P P'' (Algebra.ofId _ _) (P''.over_def P)).comp_algebraMap,
    ← Polynomial.map_map, ← ha']
  simp

end
