/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.RingTheory.Noetherian
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Module.Projective

#align_import ring_theory.flat from "leanprover-community/mathlib"@"62c0a4ef1441edb463095ea02a06e87f3dfe135c"

/-!
# Flat modules

A module `M` over a commutative ring `R` is *flat*
if for all finitely generated ideals `I` of `R`,
the canonical map `I ⊗ M →ₗ M` is injective.

This is equivalent to the claim that for all injective `R`-linear maps `f : M₁ → M₂`
the induced map `M₁ ⊗ M → M₂ ⊗ M` is injective.
See <https://stacks.math.columbia.edu/tag/00HD>.
This result is not yet formalised.

## Main declaration

* `Module.Flat`: the predicate asserting that an `R`-module `M` is flat.

## TODO

* Show that tensoring with a flat module preserves injective morphisms.
  Show that this is equivalent to be flat.
  See <https://stacks.math.columbia.edu/tag/00HD>.
  To do this, it is probably a good idea to think about a suitable
  categorical induction principle that should be applied to the category of `R`-modules,
  and that will take care of the administrative side of the proof.
* Define flat `R`-algebras
* Define flat ring homomorphisms
  - Show that the identity is flat
  - Show that composition of flat morphisms is flat
* Show that flatness is stable under base change (aka extension of scalars)
  For base change, it will be very useful to have a "characteristic predicate"
  instead of relying on the construction `A ⊗ B`.
  Indeed, such a predicate should allow us to treat both
  `A[X]` and `A ⊗ R[X]` as the base change of `R[X]` to `A`.
  (Similar examples exist with `Fin n → R`, `R × R`, `ℤ[i] ⊗ ℝ`, etc...)
* Generalize flatness to noncommutative rings.

-/


universe u v w

namespace Module

open Function (Injective Surjective)

open LinearMap (lsmul rTensor lTensor)

open TensorProduct

/-- An `R`-module `M` is flat if for all finitely generated ideals `I` of `R`,
the canonical map `I ⊗ M →ₗ M` is injective. -/
class Flat (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] : Prop where
  out : ∀ ⦃I : Ideal R⦄ (_ : I.FG), Injective (TensorProduct.lift ((lsmul R M).comp I.subtype))
#align module.flat Module.Flat

namespace Flat

/-- A reformulation of the flat property. -/
lemma iff_rTensor_injective (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] :
    Flat R M ↔ (∀ ⦃I : Ideal R⦄ (_ : I.FG), Injective (rTensor M I.subtype)) := by
  have aux : ∀ (I : Ideal R), ((TensorProduct.lid R M).comp (rTensor M I.subtype)) =
    (TensorProduct.lift ((lsmul R M).comp I.subtype))
  · intro I; apply TensorProduct.ext'; intro x y; simp
  constructor
  · intro F I hI
    erw [← Equiv.comp_injective _ (TensorProduct.lid R M).toEquiv]
    have h₁ := F.out hI
    rw [← aux] at h₁
    refine h₁
  · intro h₁
    constructor
    intro I hI
    rw [← aux]
    simp [h₁ hI]

open LinearMap Submodule

instance self (R : Type u) [CommRing R] : Flat R R :=
  ⟨by
    intro I _
    rw [← Equiv.injective_comp (TensorProduct.rid R I).symm.toEquiv]
    convert Subtype.coe_injective using 1
    ext x
    simp only [Function.comp_apply, LinearEquiv.coe_toEquiv, rid_symm_apply, comp_apply, mul_one,
      lift.tmul, Submodule.subtype_apply, Algebra.id.smul_eq_mul, lsmul_apply]⟩
#align module.flat.self Module.Flat.self


/-- A retract of a flat `R`-module is flat. -/
lemma of_retract (R : Type u) (M : Type v) (N : Type w)
    [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (i : N →ₗ[R] M) (r : M →ₗ[R] N) (h : r.comp i = LinearMap.id)
    (f : Flat R M) : Flat R N := by
  rw [iff_rTensor_injective] at *
  intro I hI
  have h₁ : Function.Injective (lTensor R i)
  · apply Function.RightInverse.injective (g := (lTensor R r))
    intro x
    rw [← LinearMap.comp_apply, ← lTensor_comp, h]
    simp
  rw [← Function.Injective.of_comp_iff h₁ (rTensor N I.subtype), ← LinearMap.coe_comp]
  rw [LinearMap.lTensor_comp_rTensor, ←LinearMap.rTensor_comp_lTensor]
  rw [LinearMap.coe_comp, Function.Injective.of_comp_iff (f hI)]
  apply Function.RightInverse.injective (g := lTensor _ r)
  intro x
  rw [← LinearMap.comp_apply, ← lTensor_comp, h]
  simp

/-- A `R`-module isomorphic to a flat `R`-module is flat. -/
lemma of_iso (R : Type u) (M : Type v) (N : Type w) [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (e : N ≃ₗ[R] M) (f : Flat R M) : Flat R N := by
  have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by simp
  exact of_retract _ _ _ e.toLinearMap e.symm.toLinearMap h f

open DirectSum

/-- A direct sum of flat `R`-modules is flat. -/
lemma directSum (R : Type u) [CommRing R] (ι : Type v) [dec_ι : DecidableEq ι] (M : ι → Type w)
    [(i : ι) → AddCommGroup (M i)] [(i : ι) → Module R (M i)] (F : (i : ι) → (Flat R (M i))) :
    Flat R (⨁ i, M i) := by
  rw [iff_rTensor_injective]
  intro I hI
  rw [← Equiv.comp_injective _ (TensorProduct.lid R (⨁ i, M i)).toEquiv]
  set η₁ := TensorProduct.lid R (⨁ i, M i)
  set η := (fun i ↦ TensorProduct.lid R (M i))
  set φ := (fun i ↦ rTensor (M i) I.subtype)
  set π := (fun i ↦ component R ι (fun j ↦ M j) i)
  set ψ := (TensorProduct.directSumRight R {x // x ∈ I} (fun i ↦ M i)).symm.toLinearMap with psi_def
  set ρ := rTensor (⨁ i, M i) I.subtype
  set τ := (fun i ↦ component R ι (fun j ↦ ({x // x ∈ I} ⊗[R] (M j))) i)
  rw [← Equiv.injective_comp (TensorProduct.directSumRight _ _ _).symm.toEquiv]
  rw [LinearEquiv.coe_toEquiv, ← LinearEquiv.coe_coe, ← LinearMap.coe_comp]
  rw [LinearEquiv.coe_toEquiv, ← LinearEquiv.coe_coe, ← LinearMap.coe_comp]
  rw [← psi_def, injective_iff_map_eq_zero ((η₁.comp ρ).comp ψ)]
  have h₁ : ∀ (i : ι), (π i).comp ((η₁.comp ρ).comp ψ) = (η i).comp ((φ i).comp (τ i))
  · intro i
    apply DirectSum.linearMap_ext
    intro j
    apply TensorProduct.ext'
    intro a m
    simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, directSumRight_symm_lof_tmul,
      rTensor_tmul, coeSubtype, lid_tmul, map_smul]
    rw [DirectSum.component.of, DirectSum.component.of]
    by_cases h₂ : j = i
    · subst j; simp
    · simp [h₂]
  intro a ha; rw [DirectSum.ext_iff R]; intro i
  have f := LinearMap.congr_arg (f:= (π i)) ha
  erw [LinearMap.congr_fun (h₁ i) a] at f
  rw [(map_zero (π i) : (π i) 0 = (0 : M i))] at f
  have h₂ := (F i)
  rw [iff_rTensor_injective] at h₂
  have h₃ := h₂ hI
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, AddEquivClass.map_eq_zero_iff,
    h₃, LinearMap.map_eq_zero_iff] at f
  simp [f]

set_option linter.unusedVariables false in
/-- Free `R`-modules over discrete types are flat. -/
instance finsupp (R : Type u) [CommRing R] (ι : Type v) [dec_ι : DecidableEq ι] :
    Flat R (ι →₀ R) :=
  of_iso R _ _ (finsuppLEquivDirectSum R R ι) (directSum R ι _ (fun _ ↦ (self R)))

noncomputable instance of_free (R : Type) [CommRing R] (M: Type w)
    [AddCommGroup M] [Module R M] [Free R M] : Flat R M :=
  of_iso R _ _ (Free.repr R M) (finsupp R _ )

/-- A projective module with a discrete type of generator is flat -/
lemma of_projective_surj (R : Type u) [CommRing R] (ι : Type v) [DecidableEq ι] (M : Type w)
    [AddCommGroup M] [Module R M] [Projective R M] (p : (ι →₀ R) →ₗ[R] M) (hp : Surjective p) :
    Flat R M := by
  have h := Module.projective_lifting_property p (LinearMap.id) hp
  cases h with
    | _ e he => exact of_retract R _ _ _ _ he (finsupp R _)

noncomputable instance of_projective (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M]
    [Module R M] [h : Projective R M] : Flat R M := by
  rw [Module.projective_def'] at h
  cases h with
    | _ e he => exact of_retract R _ _ _ _ he (@finsupp R _ (dec_ι := Classical.decEq _))

end Flat

end Module
