/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
## The Hopkins–Levitzki theorem

## Main results

* `IsSemiprimaryRing.isNoetherian_iff_isArtinian`: the Hopkins–Levitzki theorem, which states
  that for a module over a semiprimary ring (in particular, an Artinian ring),
  `IsNoetherian` is equivalent to `IsArtinian` (and therefore also to `IsFiniteLength`).

* In particular, for a module over an Artinian ring, `Module.Finite`, `IsNoetherian`, `IsArtinian`,
  and `IsFiniteLength` are all equivalent (`IsArtinianRing.tfae`),
  and a (left) Artinian ring is also (left) Noetherian.

* `isArtinianRing_iff_isNoetherianRing_krullDimLE_zero`: a commutative ring is Artinian iff
  it is Noetherian with Krull dimension at most 0.

## Reference

* [F. Lorenz, *Algebra: Volume II: Fields with Structure, Algebras and Advanced Topics*][Lorenz2008]
-/

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

open Ideal in
theorem IsSemiprimaryRing.isNoetherian_iff_isArtinian [IsSemiprimaryRing R] :
    IsNoetherian R M ↔ IsArtinian R M := by
  have ⟨ss, n, hn⟩ := (isSemiprimaryRing_iff R).mp ‹_›
  set Jac := Ring.jacobson R
  replace hn : Jac ^ n ≤ Module.annihilator R M := hn ▸ bot_le
  induction' n with n ih generalizing M
  · rw [Submodule.pow_zero, one_eq_top, top_le_iff, Module.annihilator_eq_top_iff] at hn
    constructor <;> infer_instance
  obtain _ | n := n
  · rw [Submodule.pow_one, ← SetLike.coe_subset_coe,
      ← Module.isTorsionBySet_iff_subset_annihilator] at hn
    let _ := hn.module
    have := hn.isSemisimpleModule_iff.mp inferInstance
    exact IsSemisimpleModule.finite_tfae.out 1 2
  let N := Jac ^ (n + 1) • (⊤ : Submodule R M)
  simp_rw [iff_iff_eq] at ih -- otherwise `rw [ih]` below fails!
  rw [isNoetherian_iff_submodule_quotient N, isArtinian_iff_submodule_quotient N, ih, ih]
  · rw [← SetLike.coe_subset_coe, ← Module.isTorsionBySet_iff_subset_annihilator,
      Module.isTorsionBySet_quotient_iff]
    intro m i hi; exact Submodule.smul_mem_smul hi trivial
  · rw [← Submodule.annihilator_top, Submodule.le_annihilator_iff, Ideal.IsTwoSided.pow_succ,
      Submodule.mul_smul, ← Submodule.le_annihilator_iff] at hn
    exact (Ideal.pow_le_self n.succ_ne_zero).trans hn

variable (R M)

theorem IsArtinianRing.tfae [IsArtinianRing R] :
    List.TFAE [Module.Finite R M, IsNoetherian R M, IsArtinian R M, IsFiniteLength R M] := by
  tfae_have 2 ↔ 3 := IsSemiprimaryRing.isNoetherian_iff_isArtinian
  tfae_have 2 → 1 := fun _ ↦ inferInstance
  tfae_have 1 → 3 := fun _ ↦ inferInstance
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  tfae_have 4 → 2 := And.left
  tfae_have 2 → 4 := fun h ↦ ⟨h, tfae_2_iff_3.mp h⟩
  tfae_finish

@[stacks 00JB "A ring is Artinian if and only if it has finite length as a module over itself."]
theorem isArtinianRing_iff_isFiniteLength : IsArtinianRing R ↔ IsFiniteLength R R :=
  ⟨fun h ↦ ((IsArtinianRing.tfae R R).out 2 3).mp h,
    fun h ↦ (isFiniteLength_iff_isNoetherian_isArtinian.mp h).2⟩

@[stacks 00JB "A ring is Artinian if and only if it has finite length as a module over itself.
**Any such ring is both Artinian and Noetherian.**"]
instance [IsArtinianRing R] : IsNoetherianRing R := ((IsArtinianRing.tfae R R).out 2 1).mp ‹_›

/-- A finitely generated Artinian module over a commutative ring is Noetherian. This is not
necessarily the case over a noncommutative ring, see https://mathoverflow.net/a/61700. -/
theorem isNoetherian_of_finite_isArtinian {R} [CommRing R] [Module R M]
    [Module.Finite R M] [IsArtinian R M] : IsNoetherian R M := by
  obtain ⟨s, fin, span⟩ := Submodule.fg_def.mp (Module.finite_def.mp ‹_›)
  rw [← s.iUnion_of_singleton_coe, Submodule.span_iUnion] at span
  rw [← Set.finite_coe_iff] at fin
  rw [← isNoetherian_top_iff, ← span]
  have _ (i : M) : IsNoetherian R (Submodule.span R {i}) := by
    rw [LinearMap.span_singleton_eq_range, ← (LinearMap.quotKerEquivRange _).isNoetherian_iff]
    let e (I : Ideal R) : R ⧸ I →ₛₗ[Ideal.Quotient.mk I] R ⧸ I := ⟨.id _, fun _ _ ↦ rfl⟩
    rw [(e _).isNoetherian_iff_of_bijective Function.bijective_id]
    refine @instIsNoetherianRingOfIsArtinianRing _ _ ?_
    rw [IsArtinianRing, ← (e _).isArtinian_iff_of_bijective Function.bijective_id,
      (LinearMap.quotKerEquivRange _).isArtinian_iff]
    infer_instance
  infer_instance

theorem IsNoetherianRing.isArtinianRing_of_krullDimLE_zero {R} [CommRing R]
    [IsNoetherianRing R] [Ring.KrullDimLE 0 R] : IsArtinianRing R :=
  have eq := Ring.jacobson_eq_nilradical_of_krullDimLE_zero R
  let Spec := {I : Ideal R | I.IsPrime}
  have : Finite Spec :=
    (minimalPrimes.finite_of_isNoetherianRing R).subset Ideal.mem_minimalPrimes_of_krullDimLE_zero
  have (I : Spec) : I.1.IsPrime := I.2
  have (I : Spec) : IsSemisimpleRing (R ⧸ I.1) := let _ := Ideal.Quotient.field I.1; inferInstance
  have : IsSemisimpleRing (R ⧸ Ring.jacobson R) := by
    rw [eq, nilradical_eq_sInf, sInf_eq_iInf']
    exact (Ideal.quotientInfRingEquivPiQuotient _ fun I J ne ↦
      Ideal.isCoprime_of_isMaximal <| Subtype.coe_ne_coe.mpr ne).symm.isSemisimpleRing
  have : IsSemiprimaryRing R := ⟨this, eq ▸ IsNoetherianRing.isNilpotent_nilradical R⟩
  IsSemiprimaryRing.isNoetherian_iff_isArtinian.mp ‹_›

@[stacks 00KH] theorem isArtinianRing_iff_isNoetherianRing_krullDimLE_zero {R} [CommRing R] :
    IsArtinianRing R ↔ IsNoetherianRing R ∧ Ring.KrullDimLE 0 R :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨h, _⟩ ↦ h.isArtinianRing_of_krullDimLE_zero⟩
