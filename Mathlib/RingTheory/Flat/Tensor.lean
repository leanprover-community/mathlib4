/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Jujian Zhang
-/
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.RingTheory.Flat.Basic

/-!
# Flat modules

`M` is flat if `· ⊗ M` preserves finite limits (equivalently, pullbacks, or equalizers).
If `R` is a ring, an `R`-module `M` is flat if and only if it is mono-flat, and to show
a module is flat, it suffices to check inclusions of finitely generated ideals into `R`.
See <https://stacks.math.columbia.edu/tag/00HD>.

## Main theorems

* `Module.Flat.iff_characterModule_injective`: `CharacterModule M` is an injective module iff
  `M` is flat.
* `Module.Flat.iff_lTensor_injective`, `Module.Flat.iff_rTensor_injective`,
  `Module.Flat.iff_lTensor_injective'`, `Module.Flat.iff_rTensor_injective'`:
  A module `M` over a ring `R` is flat iff for all (finitely generated) ideals `I` of `R`, the
  tensor product of the inclusion `I → R` and the identity `M → M` is injective.
-/

universe u v

namespace Module.Flat

open Function (Surjective)

open LinearMap

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/--
Define the character module of `M` to be `M →+ ℚ ⧸ ℤ`.
The character module of `M` is an injective module if and only if
`f ⊗ 𝟙 M` is injective for any linear map `f` in the same universe as `M`.
-/
lemma injective_characterModule_iff_rTensor_preserves_injective_linearMap :
    Module.Injective R (CharacterModule M) ↔
    ∀ ⦃N N' : Type v⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N'), Function.Injective f → Function.Injective (f.rTensor M) := by
  simp_rw [injective_iff, rTensor_injective_iff_lcomp_surjective, Surjective, DFunLike.ext_iff]; rfl

/-- `CharacterModule M` is an injective module iff `M` is flat.
See [Lambek_1964] for a self-contained proof. -/
theorem iff_characterModule_injective [Small.{v} R] :
    Flat R M ↔ Module.Injective R (CharacterModule M) := by
  rw [injective_characterModule_iff_rTensor_preserves_injective_linearMap,
    iff_rTensor_preserves_injective_linearMap']

/-- `CharacterModule M` is Baer iff `M` is flat. -/
theorem iff_characterModule_baer : Flat R M ↔ Baer R (CharacterModule M) := by
  rw [equiv_iff (N := ULift.{u} M) ULift.moduleEquiv.symm, iff_characterModule_injective,
    ← Baer.iff_injective, Baer.congr (CharacterModule.congr ULift.moduleEquiv)]

/-- An `R`-module `M` is flat iff for all ideals `I` of `R`, the tensor product of the
inclusion `I → R` and the identity `M → M` is injective. See `iff_rTensor_injective` to
restrict to finitely generated ideals `I`. -/
theorem iff_rTensor_injective' :
    Flat R M ↔ ∀ I : Ideal R, Function.Injective (rTensor M I.subtype) := by
  simp_rw [iff_characterModule_baer, Baer, rTensor_injective_iff_lcomp_surjective,
    Surjective, DFunLike.ext_iff, Subtype.forall, lcomp_apply, Submodule.subtype_apply]

/-- The `lTensor`-variant of `iff_rTensor_injective'`. . -/
theorem iff_lTensor_injective' :
    Flat R M ↔ ∀ (I : Ideal R), Function.Injective (lTensor M I.subtype) := by
  simpa [← comm_comp_rTensor_comp_comm_eq] using iff_rTensor_injective'

/-- A module `M` over a ring `R` is flat iff for all finitely generated ideals `I` of `R`, the
tensor product of the inclusion `I → R` and the identity `M → M` is injective. See
`iff_rTensor_injective'` to extend to all ideals `I`. -/
lemma iff_rTensor_injective :
    Flat R M ↔ ∀ ⦃I : Ideal R⦄, I.FG → Function.Injective (I.subtype.rTensor M) := by
  refine iff_rTensor_injective'.trans ⟨fun h I _ ↦ h I,
    fun h I ↦ (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_⟩
  obtain ⟨J, hfg, hle, y, rfl⟩ := Submodule.exists_fg_le_eq_rTensor_inclusion x
  rw [← rTensor_comp_apply] at hx
  rw [(injective_iff_map_eq_zero _).mp (h hfg) y hx, map_zero]

/-- The `lTensor`-variant of `iff_rTensor_injective`. -/
theorem iff_lTensor_injective :
    Flat R M ↔ ∀ ⦃I : Ideal R⦄, I.FG → Function.Injective (I.subtype.lTensor M) := by
  simpa [← comm_comp_rTensor_comp_comm_eq] using iff_rTensor_injective

/-- An `R`-module `M` is flat if for all finitely generated ideals `I` of `R`,
the canonical map `I ⊗ M →ₗ M` is injective. -/
lemma iff_lift_lsmul_comp_subtype_injective : Flat R M ↔ ∀ ⦃I : Ideal R⦄, I.FG →
    Function.Injective (TensorProduct.lift ((lsmul R M).comp I.subtype)) := by
  simp [iff_rTensor_injective, ← lid_comp_rTensor]

end Module.Flat
