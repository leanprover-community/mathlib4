/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.KrullDimension.Zero

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

universe u

variable (R₀ R : Type*) (M : Type u) [Ring R₀] [Ring R] [Module R₀ R]
  [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M]

namespace IsSemiprimaryRing

variable [IsSemiprimaryRing R]

@[elab_as_elim] protected theorem induction
    {P : ∀ (M : Type u) [AddCommGroup M] [Module R₀ M] [Module R M], Prop}
    (h0 : ∀ (M) [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M]
      [IsSemisimpleModule R M], Module.IsTorsionBySet R M (Ring.jacobson R) → P M)
    (h1 : ∀ (M) [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M],
      let N := Ring.jacobson R • (⊤ : Submodule R M); P N → P (M ⧸ N) → P M) :
    P M := by
  have ⟨ss, n, hn⟩ := (isSemiprimaryRing_iff R).mp ‹_›
  set Jac := Ring.jacobson R
  replace hn : Jac ^ n ≤ Module.annihilator R M := hn ▸ bot_le
  have {M} [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M] :
      Jac ≤ Module.annihilator R M → P M := by
    rw [← SetLike.coe_subset_coe, ← Module.isTorsionBySet_iff_subset_annihilator]
    intro h
    let _ := h.module
    have := (h.semilinearMap.isSemisimpleModule_iff_of_bijective Function.bijective_id).2
      inferInstance
    exact h0 _ h
  induction' n with n ih generalizing M
  · rw [Jac.pow_zero, Ideal.one_eq_top] at hn; exact this (le_top.trans hn)
  obtain _ | n := n
  · rw [Jac.pow_one] at hn; exact this hn
  refine h1 _ (ih _ ?_) (ih _ ?_)
  · rwa [← Submodule.annihilator_top, Submodule.le_annihilator_iff, Jac.pow_succ,
      Submodule.mul_smul, ← Submodule.le_annihilator_iff] at hn
  · rw [← SetLike.coe_subset_coe, ← Module.isTorsionBySet_iff_subset_annihilator,
      Module.isTorsionBySet_quotient_iff]
    exact fun m i hi ↦ Submodule.smul_mem_smul (Ideal.pow_le_self n.succ_ne_zero hi) trivial

section

variable [IsScalarTower R₀ R R] [Module.Finite R₀ (R ⧸ Ring.jacobson R)]

private theorem finite_of_isNoetherian_or_isArtinian :
    IsNoetherian R M ∨ IsArtinian R M → Module.Finite R₀ M := by
  refine IsSemiprimaryRing.induction R₀ R M (P := fun M ↦ IsNoetherian R M ∨ IsArtinian R M →
    Module.Finite R₀ M) (fun M _ _ _ _ _ hJ h ↦ ?_) (fun M _ _ _ _ hs hq h ↦ ?_)
  · let _ := hJ.module
    have := IsSemisimpleModule.finite_tfae (R := R) (M := M)
    simp_rw [this.out 1 0, this.out 2 0, or_self,
      hJ.semilinearMap.finite_iff_of_bijective Function.bijective_id] at h
    exact .trans (R ⧸ Ring.jacobson R) M
  · let N := (Ring.jacobson R • ⊤ : Submodule R M).restrictScalars R₀
    have : Module.Finite R₀ N := by refine hs (h.imp ?_ ?_) <;> (intro; infer_instance)
    have : Module.Finite R₀ (M ⧸ N) := by refine hq (h.imp ?_ ?_) <;> (intro; infer_instance)
    exact .of_submodule_quotient N

theorem finite_of_isNoetherian [IsNoetherian R M] : Module.Finite R₀ M :=
  finite_of_isNoetherian_or_isArtinian R₀ R M (.inl ‹_›)

theorem finite_of_isArtinian [IsArtinian R M] : Module.Finite R₀ M :=
  finite_of_isNoetherian_or_isArtinian R₀ R M (.inr ‹_›)

end

variable {R M}

theorem isNoetherian_iff_isArtinian : IsNoetherian R M ↔ IsArtinian R M :=
  IsSemiprimaryRing.induction R R M (P := fun M ↦ IsNoetherian R M ↔ IsArtinian R M)
    (fun M _ _ _ _ _ _ ↦ IsSemisimpleModule.finite_tfae.out 1 2)
    fun M _ _ _ _ h h' ↦ let N : Submodule R M := Ring.jacobson R • ⊤; by
      simp_rw [isNoetherian_iff_submodule_quotient N, isArtinian_iff_submodule_quotient N, N, h, h']

end IsSemiprimaryRing

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

theorem isArtinianRing_iff_krullDimLE_zero {R : Type*} [CommRing R] [IsNoetherianRing R] :
    IsArtinianRing R ↔ Ring.KrullDimLE 0 R := by
  rwa [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero, and_iff_right]

lemma isArtinianRing_iff_isNilpotent_maximalIdeal (R : Type*) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] : IsArtinianRing R ↔ IsNilpotent (IsLocalRing.maximalIdeal R) := by
  rw [isArtinianRing_iff_krullDimLE_zero,
    Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _),
    ← and_iff_left (a := Ring.KrullDimLE 0 R) ‹IsLocalRing R›,
    (Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 3 rfl rfl,
    IsLocalRing.isMaximal_iff, le_antisymm_iff, and_iff_right]
  exact IsLocalRing.le_maximalIdeal (by simp [nilradical, Ideal.radical_eq_top])
