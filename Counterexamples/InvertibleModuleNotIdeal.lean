/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.Data.DFinsupp.Module
import Mathlib.RingTheory.PicardGroup

/-!
# A class of examples of invertible modules that are not isomorphic to ideals

References: https://math.stackexchange.com/a/5090562 or https://mathoverflow.net/a/499258
-/

variable (R : Type*) [CommRing R]

/-- The trivial square-zero extension of a commutative ring R given by the direct sum
R ⊕ ⨁ₘ R⧸m where m ranges over maximal ideals of R. -/
abbrev SqZeroExtQuotMax := TrivSqZeroExt R (Π₀ m : MaximalSpectrum R, R ⧸ m.1)

instance : IsFractionRing (SqZeroExtQuotMax R) (SqZeroExtQuotMax R) :=
  IsFractionRing.self_iff_nonZeroDivisors_le_isUnit.mpr fun x hx ↦
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr <| of_not_not fun hr ↦ by
    have ⟨M, hM, hrM⟩ := exists_max_ideal_of_mem_nonunits hr
    classical
    have := hx.1 (.inr <| .single ⟨M, hM⟩ 1) <| by
      ext1; · simp
      simpa [-DFinsupp.single_apply, ← DFinsupp.single_smul, DFinsupp.single_eq_zero]
        using (Ideal.Quotient.mk_eq_mk_iff_sub_mem ..).mpr (by simpa)
    simpa using congr(($this).snd)

/-- R as an algebra over `SqZeroExtQuotMax R`. -/
abbrev SqZeroExtQuotMax.algebraBase : Algebra (SqZeroExtQuotMax R) R := TrivSqZeroExt.algebraBase ..

open CommRing (Pic) in
/-- If the Picard group of a commutative ring R is nontrivial, then `SqZeroExtQuotMax R`
has an invertible module (which is the base change of an invertible ideal of R)
not isomorphic to any ideal. -/
theorem SqZeroExtQuotMax.not_exists_linearEquiv_ideal_of_invertible [Nontrivial (Pic R)] :
    ∃ M : Pic (SqZeroExtQuotMax R),
    ¬ ∃ I : Ideal (SqZeroExtQuotMax R), Nonempty (M ≃ₗ[SqZeroExtQuotMax R] I) := by
  by_contra! h
  have ⟨M, hM⟩ := exists_ne (1 : Pic R)
  have ⟨I, ⟨eI⟩⟩ := h (M.mapAlgebra R _)
  have ⟨J, ⟨eJ⟩⟩ := h (M⁻¹.mapAlgebra R _)
  have := Module.Invertible.congr eI
  have := Module.Invertible.congr eJ
  obtain ⟨rfl | rfl⟩ := I.eq_top_of_mk_tensor_eq_one J <| by
    rw [Pic.mk_tensor, ← Pic.mk_eq_mk_iff.mpr ⟨eI⟩, ← Pic.mk_eq_mk_iff.mpr ⟨eJ⟩,
      Pic.mk_eq_self, Pic.mk_eq_self, ← map_mul, mul_inv_cancel, map_one]
  have eq := Pic.mk_eq_one_iff.mpr ⟨eI ≪≫ₗ Submodule.topEquiv⟩
  rw [Pic.mk_eq_self] at eq
  let := TrivSqZeroExt.algebraBase
  have eq := congr(Pic.mapAlgebra (SqZeroExtQuotMax R) R $eq)
  exact hM <| by rwa [map_one, Pic.mapAlgebra_mapAlgebra, Pic.mapAlgebra_self] at eq
