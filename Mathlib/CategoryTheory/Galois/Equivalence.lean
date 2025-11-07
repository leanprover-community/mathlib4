/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Galois.EssSurj
import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.Topology.Category.FinTopCat

/-!
# Fiber functors induce an equivalence of categories

Let `C` be a Galois category with fiber functor `F`.

In this file we conclude that the induced functor from `C` to the category of finite,
discrete `Aut F`-sets is an equivalence of categories.
-/

universe u₂ u₁ w

open CategoryTheory

namespace CategoryTheory

variable {C : Type u₁} [Category.{u₂} C] {F : C ⥤ FintypeCat.{w}}

namespace PreGaloisCategory

variable [GaloisCategory C] [FiberFunctor F]

open scoped FintypeCatDiscrete

variable (F) in
/-- The induced functor from `C` to the category of finite, discrete `Aut F`-sets. -/
@[simps! obj_obj map]
def functorToContAction : C ⥤ ContAction FintypeCat (Aut F) :=
  ObjectProperty.lift _ (functorToAction F) (fun X ↦ continuousSMul_aut_fiber F X)

instance : (functorToContAction F).Faithful :=
  inferInstanceAs <| (ObjectProperty.lift _ _ _).Faithful

instance : (functorToContAction F).Full :=
  inferInstanceAs <| (ObjectProperty.lift _ _ _).Full

instance {F : C ⥤ FintypeCat.{u₁}} [FiberFunctor F] : (functorToContAction F).EssSurj where
  mem_essImage X := by
    have : ContinuousSMul (Aut F) X.obj.V.carrier := X.2
    obtain ⟨A, ⟨i⟩⟩ := exists_lift_of_continuous (F := F) X
    exact ⟨A, ⟨ObjectProperty.isoMk _ i⟩⟩

instance : (functorToContAction F).EssSurj := by
  let F' : C ⥤ FintypeCat.{u₁} := F ⋙ FintypeCat.uSwitch.{w, u₁}
  letI : FiberFunctor F' := FiberFunctor.comp_right _
  have : (functorToContAction F').EssSurj := inferInstance
  let f : Aut F ≃ₜ* Aut F' :=
    (autEquivAutWhiskerRight F (FintypeCat.uSwitchEquivalence.{w, u₁}).fullyFaithfulFunctor)
  let equiv : ContAction FintypeCat.{u₁} (Aut F') ≌ ContAction FintypeCat.{w} (Aut F) :=
    (FintypeCat.uSwitchEquivalence.{u₁, w}.mapContAction (Aut F')
       (fun X ↦ by
          rw [Action.isContinuous_def]
          change Continuous ((fun p ↦ (FintypeCat.uSwitchEquiv X.obj.V).symm p) ∘
              (fun p : Aut F' × _ ↦ (X.obj.ρ p.1) p.2) ∘
              (fun p : Aut F' × _ ↦ (p.1, FintypeCat.uSwitchEquiv _ p.2)))
          have : Continuous (fun p : Aut F' × _ ↦ (X.obj.ρ p.1) p.2) := X.2.1
          fun_prop)
       (fun X ↦ by
          rw [Action.isContinuous_def]
          change Continuous ((fun p ↦ (FintypeCat.uSwitchEquiv X.obj.V).symm p) ∘
              (fun p : Aut F' × _ ↦ (X.obj.ρ p.1) p.2) ∘
              (fun p : Aut F' × _ ↦ (p.1, FintypeCat.uSwitchEquiv _ p.2)))
          have : Continuous (fun p : Aut F' × _ ↦ (X.obj.ρ p.1) p.2) := X.2.1
          fun_prop)).trans <|
      ContAction.resEquiv _ f
  have : functorToContAction F ≅ functorToContAction F' ⋙ equiv.functor :=
    NatIso.ofComponents
      (fun X ↦ ObjectProperty.isoMk _ (Action.mkIso (FintypeCat.uSwitchEquivalence.unitIso.app _)
      (fun g ↦ FintypeCat.uSwitchEquivalence.unitIso.hom.naturality (g.hom.app X))))
      (fun f ↦ by
        ext : 2
        exact FintypeCat.uSwitchEquivalence.unitIso.hom.naturality (F.map f))
  exact Functor.essSurj_of_iso this.symm

/-- Any fiber functor `F` induces an equivalence of categories with the category of finite and
discrete `Aut F`-sets. -/
@[stacks 0BN4]
instance : (functorToContAction F).IsEquivalence where

end PreGaloisCategory

end CategoryTheory
