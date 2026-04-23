/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.QuasiFinite.Weakly
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.LocalRing.ResidueField.Polynomial
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic.Algebraize
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-! # Quasi-finite primes in polynomial algebras -/

@[expose] public section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

namespace Polynomial

attribute [local instance] Algebra.WeaklyQuasiFiniteAt.finite_locoalization in
lemma not_weaklyQuasiFiniteAt (P : Ideal R[X]) [P.IsPrime] : ¬ Algebra.WeaklyQuasiFiniteAt R P := by
  intro H
  wlog hR : IsField R
  · let p := P.under R
    obtain ⟨Q, hQ⟩ := (PrimeSpectrum.preimageEquivFiber R R[X]
        ⟨p, inferInstance⟩).symm.surjective ⟨⟨P, ‹_›⟩, rfl⟩
    have inst : Algebra.WeaklyQuasiFiniteAt p.ResidueField Q.asIdeal :=
      .baseChange P Q.asIdeal congr($(hQ.symm).1.1)
    exact this (Q.asIdeal.comap (polyEquivTensor' R p.ResidueField).toRingHom)
      inferInstance (Field.toIsField _)
  let := hR.toField
  have := Module.Finite.of_injective
    (IsScalarTower.toAlgHom R R[X] (Localization.AtPrime P)).toLinearMap
    (IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors)
  exact transcendental_X R (Algebra.IsIntegral.isIntegral X).isAlgebraic

/-- `R[X]` is not quasi-finite over `R` at any prime. -/
lemma not_quasiFiniteAt (P : Ideal R[X]) [P.IsPrime] : ¬ Algebra.QuasiFiniteAt R P :=
  fun _ ↦ not_weaklyQuasiFiniteAt P inferInstance

lemma map_under_lt_comap_of_weaklyQuasiFiniteAt
    (f : R[X] →ₐ[R] S) (P : Ideal S) [P.IsPrime] [Algebra.WeaklyQuasiFiniteAt R P] :
    (P.under R).map C < P.comap (f : R[X] →+* S) := by
  algebraize [f.toRingHom]
  refine lt_of_le_of_ne (Ideal.map_le_iff_le_comap.mpr ?_) fun e ↦ ?_
  · rw [Ideal.comap_comap, ← algebraMap_eq, f.comp_algebraMap]
  have : Module.Finite (Ideal.under R P).ResidueField P.ResidueField :=
    Algebra.WeaklyQuasiFiniteAt.finite_residueField ..
  have : Module.Finite (P.under R).ResidueField (P.under R[X]).ResidueField :=
    .of_injective (IsScalarTower.toAlgHom _ _ P.ResidueField).toLinearMap
      (algebraMap (P.under R[X]).ResidueField P.ResidueField).injective
  have : Module.Finite (P.under R).ResidueField (RatFunc (P.under R).ResidueField) :=
    .of_surjective (residueFieldMapCAlgEquiv _ (P.under _) e.symm).toLinearMap
      (residueFieldMapCAlgEquiv _ (P.under _) e.symm).surjective
  exact RatFunc.transcendental_X (K := (P.under R).ResidueField)
    (Algebra.IsIntegral.isIntegral _).isAlgebraic

lemma map_under_lt_comap_of_quasiFiniteAt
    (f : R[X] →ₐ[R] S) (P : Ideal S) [P.IsPrime] [Algebra.QuasiFiniteAt R P] :
    (P.under R).map C < P.comap (f : R[X] →+* S) :=
  map_under_lt_comap_of_weaklyQuasiFiniteAt f P

lemma not_ker_le_map_C_of_surjective_of_weaklyQuasiFiniteAt
    (f : R[X] →ₐ[R] S) (hf : Function.Surjective f)
    (P : Ideal S) [P.IsPrime] [Algebra.WeaklyQuasiFiniteAt R P] :
    ¬ RingHom.ker f ≤ (P.under R).map C := by
  intro H
  algebraize [f.toRingHom]
  let p := P.under R
  have H' : (RingHom.ker f).map (mapRingHom (algebraMap R p.ResidueField)) = ⊥ := by
    rw [← le_bot_iff, Ideal.map_le_iff_le_comap]
    intro x hx
    simpa [Polynomial.ext_iff, Ideal.mem_map_C_iff] using H hx
  let g' : p.ResidueField[X] ≃ₐ[p.ResidueField] p.Fiber S :=
    .trans ((AlgEquiv.quotientBot _ _).symm.trans (Ideal.quotientEquivAlgOfEq _ H'.symm))
      (Polynomial.fiberEquivQuotient f hf _).symm
  obtain ⟨Q, hQ⟩ := (PrimeSpectrum.preimageEquivFiber _ _
      ⟨p, inferInstance⟩).symm.surjective ⟨⟨P, ‹_›⟩, PrimeSpectrum.ext (P.over_def p).symm⟩
  have inst : Algebra.WeaklyQuasiFiniteAt p.ResidueField Q.asIdeal :=
    .baseChange P Q.asIdeal congr($(hQ.symm).1.1)
  exact Polynomial.not_weaklyQuasiFiniteAt (Q.asIdeal.comap g'.toRingHom) inferInstance

/--
If `P` is a prime of `R[X]/I` that is quasi finite over `R`,
then `I` is not contained in `(P ∩ R)[X]`.

For usability, we replace `I` by the kernel of a surjective map `R[X] →ₐ[R] S`. -/
lemma not_ker_le_map_C_of_surjective_of_quasiFiniteAt
    (f : R[X] →ₐ[R] S) (hf : Function.Surjective f)
    (P : Ideal S) [P.IsPrime] [Algebra.QuasiFiniteAt R P] :
    ¬ RingHom.ker f ≤ (P.under R).map C :=
  not_ker_le_map_C_of_surjective_of_weaklyQuasiFiniteAt f hf P

end Polynomial
