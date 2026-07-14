/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.CategoryTheory.Discrete.SumsProducts

/-!
# Tensor product of free sheaves of modules

In this file, we show that the tensor product of free sheaves of modules
identifies to the free sheaf on the product type.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{w}}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat)]
  [(W R).IsMonoidal]

variable (I₁ I₂ : Type w)

/-- The free sheaf of modules on a product type identifies to the tensor product
of the corresponding free sheaves of modules. -/
noncomputable def freeProdIso :
    free (R := (sheafCompose J (forget₂ _ RingCat)).obj R) (I₁ × I₂) ≅
      free I₁ ⊗ free I₂ :=
  IsColimit.coconePointUniqueUpToIso (isColimitFreeCofan (I₁ × I₂))
    ((IsColimit.precomposeHomEquiv (Discrete.natIso (fun _ ↦ (λ_ _).symm)) _).2
      ((((isColimitFreeCofan I₁).tensor₂
        (isColimitFreeCofan I₂)).whiskerEquivalence Discrete.productEquiv)))

@[reassoc (attr := simp)]
lemma ι_freeProdIso_hom (i₁ : I₁) (i₂ : I₂) :
    ιFree (i₁, i₂) ≫ (freeProdIso (R := R) I₁ I₂).hom =
      (λ_ _).inv ≫ (ιFree i₁ ⊗ₘ ιFree i₂) := by
  have := IsColimit.comp_coconePointUniqueUpToIso_hom
    (isColimitFreeCofan (R := (sheafCompose J (forget₂ _ RingCat)).obj R) (I₁ × I₂))
      ((IsColimit.precomposeHomEquiv (Discrete.natIso (fun _ ↦ (λ_ _).symm)) _).2
        ((((isColimitFreeCofan I₁).tensor₂
          (isColimitFreeCofan I₂)).whiskerEquivalence Discrete.productEquiv))) (.mk (i₁, i₂))
  exact this

end SheafOfModules
