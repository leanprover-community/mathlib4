/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Fernando Chu, Christian Merten
-/

import Mathlib.CategoryTheory.Bicategory.Grothendieck
import Mathlib.CategoryTheory.FiberedCategory.HasFibers

/-!
# The Grothendieck construction gives a fibered category

In this file we show that the Grothendieck construction of a pseudofunctor `F`
gives a fibered category over the base category.

We also provide a `HasFibers` instance to `∫ F`, such that the fiber over `S` is the
category `F(S)`.

## References
[Vistoli2008] "Notes on Grothendieck Topologies, Fibered Categories and Descent Theory" by
Angelo Vistoli

-/

namespace CategoryTheory.Pseudofunctor.Grothendieck

open Functor Opposite Bicategory

variable {𝒮 : Type*} [Category 𝒮] {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat}

section

variable {R S : 𝒮} (a : F.obj ⟨op S⟩) (f : R ⟶ S)

/-- The domain of the cartesian lift of `f`. -/
abbrev domainCartesianLift : ∫ F := ⟨R, (F.map f.op.toLoc).obj a⟩

/-- The cartesian lift of `f`. -/
abbrev cartesianLift : domainCartesianLift a f ⟶ ⟨S, a⟩ := ⟨f, 𝟙 _⟩

instance isHomLift_cartesianLift : IsHomLift (forget F) f (cartesianLift a f) :=
  IsHomLift.map (forget F) (cartesianLift a f)

variable {a} in
/-- Given some lift `g` of `f`, the canonical map from the domain of `g` to the domain of
the cartesian lift of `f`. -/
abbrev homCartesianLift {a' : ∫ F} (g : a'.1 ⟶ R) (φ' : a' ⟶ ⟨S, a⟩)
    [IsHomLift (forget F) (g ≫ f) φ'] : a' ⟶ domainCartesianLift a f where
  base := g
  fiber :=
    have : φ'.base = g ≫ f := by simpa using IsHomLift.fac' (forget F) (g ≫ f) φ'
    φ'.fiber ≫ eqToHom (by simp [this]) ≫ (F.mapComp f.op.toLoc g.op.toLoc).hom.app a

instance isHomLift_homCartesianLift {a' : ∫ F} {φ' : a' ⟶ ⟨S, a⟩} {g : a'.1 ⟶ R}
    [IsHomLift (forget F) (g ≫ f) φ'] : IsHomLift (forget F) g (homCartesianLift f g φ') :=
  IsHomLift.map (forget F) (homCartesianLift f g φ')

lemma isStronglyCartesian_homCartesianLift :
    IsStronglyCartesian (forget F) f (cartesianLift a f) where
  universal_property' {a'} g φ' hφ' := by
    refine ⟨homCartesianLift f g φ', ⟨inferInstance, ?_⟩, ?_⟩
    · exact Hom.ext _ _ (by simpa using IsHomLift.fac (forget F) (g ≫ f) φ') (by simp)
    rintro χ' ⟨hχ'.symm, rfl⟩
    obtain ⟨rfl⟩ : g = χ'.1 := by simpa using IsHomLift.fac (forget F) g χ'
    ext <;> simp

end

/-- `forget F : ∫ F ⥤ 𝒮` is a fibered category. -/
instance : IsFibered (forget F) :=
  IsFibered.of_exists_isStronglyCartesian (fun a _ f ↦
    ⟨domainCartesianLift a.2 f, cartesianLift a.2 f, isStronglyCartesian_homCartesianLift a.2 f⟩)

variable (F) (S : 𝒮)

/-- The inclusion map from `F(S)` into `∫ F`. -/
@[simps]
def ι : F.obj ⟨op S⟩ ⥤ ∫ F where
  obj a := { base := S, fiber := a}
  map {a b} φ := { base := 𝟙 S, fiber := φ ≫ (F.mapId ⟨op S⟩).inv.app b}
  map_comp {a b c} φ ψ := by
    ext
    · simp
    · simp [← (F.mapId ⟨op S⟩).inv.naturality_assoc ψ, F.whiskerRight_mapId_inv_app,
        Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso]

/-- The natural isomorphism encoding `comp_const`. -/
@[simps!]
def compIso : (ι F S) ⋙ forget F ≅ (const (F.obj ⟨op S⟩)).obj S :=
  NatIso.ofComponents (fun a => eqToIso rfl)

lemma comp_const : (ι F S) ⋙ forget F = (const (F.obj ⟨op S⟩)).obj S := by
  apply Functor.ext_of_iso (compIso F S) <;> simp

noncomputable instance : Functor.Full (Fiber.inducedFunctor (comp_const F S)) where
  map_surjective {X Y} f := by
    have := f.2 -- TODO: synthesize this
    have hf : (Fiber.fiberInclusion.map f).base = 𝟙 S := by
      simpa using (IsHomLift.fac (forget F) (𝟙 S) f.1).symm
    use (Fiber.fiberInclusion.map f).2 ≫ eqToHom ?_ ≫ (F.mapId ⟨op S⟩).hom.app Y
    rotate_left
    -- TODO: more simp lemmas, should not need this...
    · simp [Fiber.inducedFunctor, hf]
      simp [Fiber.fiberInclusion]
    ext
    · simp [Fiber.inducedFunctor, hf]
      simp [Fiber.fiberInclusion]
    · simp

instance : Functor.Faithful (Fiber.inducedFunctor (comp_const F S)) where
  map_injective := by
    intros a b f g heq
    -- can be made a one liner...
    rw [← Subtype.val_inj] at heq
    simp only [Fiber.inducedFunctor] at heq -- TODO...
    obtain ⟨_, heq₂⟩ := (Hom.ext_iff _ _).1 heq
    simpa [cancel_mono] using heq₂

noncomputable instance : Functor.EssSurj (Fiber.inducedFunctor (comp_const F S)) := by
  apply essSurj_of_surj
  intro Y
  simp only [Fiber.inducedFunctor] -- TODO...
  have hYS : S = Y.1.1 := by simpa using Y.2.symm
  use (hYS.symm ▸ Y.1.2)
  apply Subtype.val_inj.1
  ext <;> simp [hYS]

noncomputable instance : Functor.IsEquivalence (Fiber.inducedFunctor (comp_const F S)) where

noncomputable instance : HasFibers (forget F) where
  Fib S := F.obj ⟨op S⟩
  ι := ι F
  comp_const := comp_const F

end CategoryTheory.Pseudofunctor.Grothendieck
