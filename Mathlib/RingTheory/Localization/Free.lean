/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Localization.Finiteness

/-!
# Free modules and localization

## Main result
- `exists_free_localizedModule_powers`: If `M` is a finitely presented `R`-module
  such that `Mₛ` is free over `Rₛ` for some `S : Submonoid R`,
  then `Mᵣ` is already free over `Rᵣ` for some `r ∈ S`.

## Future projects
- Show that finitely presented flat module has locally constant dimension.
- Show that the flat locus of a finitely presented module is open.

-/

variable {R M N N'} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (S : Submonoid R) [AddCommGroup N'] [Module R N']

variable {M' : Type*} [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') [IsLocalizedModule S f]
variable {N' : Type*} [AddCommGroup N'] [Module R N'] (g : N →ₗ[R] N') [IsLocalizedModule S g]

include f in
/--
If `M` is a finitely presented `R`-module
such that `Mₛ` is free over `Rₛ` for some `S : Submonoid R`,
then `Mᵣ` is already free over `Rᵣ` for some `r ∈ S`.
-/
lemma exists_free_localizedModule_powers
    (Rₛ) [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ M'] [IsScalarTower R Rₛ M']
    [IsLocalization S Rₛ] [Module.FinitePresentation R M] [Module.Free Rₛ M'] :
    ∃ r, r ∈ S ∧ Module.Free (Localization (.powers r)) (LocalizedModule (.powers r) M) := by
  let I := Module.Free.ChooseBasisIndex Rₛ M'
  let b : Basis I Rₛ M' := Module.Free.chooseBasis Rₛ M'
  have : Module.Finite Rₛ M' := Module.Finite.of_isLocalizedModule S (Rₚ := Rₛ) f
  have : Module.FinitePresentation R (I →₀ R) := Module.finitePresentation_of_free _ _
  obtain ⟨l, s, hl⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule S f
    (b.repr.symm.toLinearMap.restrictScalars R ∘ₗ
      Finsupp.mapRange.linearMap (Algebra.linearMap R Rₛ))
  have : Function.Bijective (IsLocalizedModule.map S
      (Finsupp.mapRange.linearMap (Algebra.linearMap R Rₛ)) f l) := by
    have : (IsLocalizedModule.map S (Finsupp.mapRange.linearMap (Algebra.linearMap R Rₛ)) f l) =
        (s • LinearMap.id) ∘ₗ b.repr.symm.toLinearMap.restrictScalars R := by
      apply IsLocalizedModule.ringHom_ext S (Finsupp.mapRange.linearMap (Algebra.linearMap R Rₛ))
        (IsLocalizedModule.map_units f)
      apply LinearMap.ext fun x ↦ ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, IsLocalizedModule.map_apply,
        Basis.coe_repr_symm, LinearMap.coe_restrictScalars]
      rw [← LinearMap.comp_apply, hl]
      simp
    rw [this]
    exact ((Module.End_isUnit_iff _).mp
      (IsLocalizedModule.map_units f s)).comp b.repr.symm.bijective
  obtain ⟨r, hr, H⟩ := exists_bijective_map_powers S _ f l this
  refine ⟨r, hr, ?_⟩
  have : Module.Free (Localization (.powers r)) (LocalizedModule (.powers r) (I →₀ R)) :=
    Module.Free.of_equiv ((isLocalizedModule_iff_isBaseChange (.powers r) (Localization (.powers r))
      ((LocalizedModule.mkLinearMap (.powers r) (I →₀ R)))).mp inferInstance).equiv
  exact Module.Free.of_equiv (LinearEquiv.ofBijective _ H)
