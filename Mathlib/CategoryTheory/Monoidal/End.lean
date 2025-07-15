/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Endofunctors as a monoidal category.

We give the monoidal category structure on `C ⥤ C`,
and show that when `C` itself is monoidal, it embeds via a monoidal functor into `C ⥤ C`.

## TODO

Can we use this to show coherence results, e.g. a cheap proof that `λ_ (𝟙_ C) = ρ_ (𝟙_ C)`?
I suspect this is harder than is usually made out.
-/


universe v u

namespace CategoryTheory

open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

variable (C : Type u) [Category.{v} C]

/-- The category of endofunctors of any category is a monoidal category,
with tensor product given by composition of functors
(and horizontal composition of natural transformations).

Note: due to the fact that composition of functors in mathlib is reversed compared to the
one usually found in the literature, this monoidal structure is in fact the monoidal
opposite of the one usually considered in the literature.
-/
def endofunctorMonoidalCategory : MonoidalCategory (C ⥤ C) where
  tensorObj F G := F ⋙ G
  whiskerLeft X _ _ F := whiskerLeft X F
  whiskerRight F X := whiskerRight F X
  tensorHom α β := α ◫ β
  tensorUnit := 𝟭 C
  associator F G H := Functor.associator F G H
  leftUnitor F := Functor.leftUnitor F
  rightUnitor F := Functor.rightUnitor F

open CategoryTheory.MonoidalCategory

attribute [local instance] endofunctorMonoidalCategory

@[simp] theorem endofunctorMonoidalCategory_tensorUnit_obj (X : C) :
    (𝟙_ (C ⥤ C)).obj X = X := rfl

@[simp] theorem endofunctorMonoidalCategory_tensorUnit_map {X Y : C} (f : X ⟶ Y) :
    (𝟙_ (C ⥤ C)).map f = f := rfl

@[simp] theorem endofunctorMonoidalCategory_tensorObj_obj (F G : C ⥤ C) (X : C) :
    (F ⊗ G).obj X = G.obj (F.obj X) := rfl

@[simp] theorem endofunctorMonoidalCategory_tensorObj_map (F G : C ⥤ C) {X Y : C} (f : X ⟶ Y) :
    (F ⊗ G).map f = G.map (F.map f) := rfl

@[simp] theorem endofunctorMonoidalCategory_tensorMap_app
    {F G H K : C ⥤ C} {α : F ⟶ G} {β : H ⟶ K} (X : C) :
    (α ⊗ₘ β).app X = β.app (F.obj X) ≫ K.map (α.app X) := rfl

@[simp] theorem endofunctorMonoidalCategory_whiskerLeft_app
    {F H K : C ⥤ C} {β : H ⟶ K} (X : C) :
    (F ◁ β).app X = β.app (F.obj X) := rfl

@[simp] theorem endofunctorMonoidalCategory_whiskerRight_app
    {F G H : C ⥤ C} {α : F ⟶ G} (X : C) :
    (α ▷ H).app X = H.map (α.app X) := rfl

@[simp] theorem endofunctorMonoidalCategory_associator_hom_app (F G H : C ⥤ C) (X : C) :
  (α_ F G H).hom.app X = 𝟙 _ := rfl

@[simp] theorem endofunctorMonoidalCategory_associator_inv_app (F G H : C ⥤ C) (X : C) :
  (α_ F G H).inv.app X = 𝟙 _ := rfl

@[simp] theorem endofunctorMonoidalCategory_leftUnitor_hom_app (F : C ⥤ C) (X : C) :
  (λ_ F).hom.app X = 𝟙 _ := rfl

@[simp] theorem endofunctorMonoidalCategory_leftUnitor_inv_app (F : C ⥤ C) (X : C) :
  (λ_ F).inv.app X = 𝟙 _ := rfl

@[simp] theorem endofunctorMonoidalCategory_rightUnitor_hom_app (F : C ⥤ C) (X : C) :
  (ρ_ F).hom.app X = 𝟙 _ := rfl

@[simp] theorem endofunctorMonoidalCategory_rightUnitor_inv_app (F : C ⥤ C) (X : C) :
  (ρ_ F).inv.app X = 𝟙 _ := rfl

namespace MonoidalCategory

variable [MonoidalCategory C]

/-- Tensoring on the right gives a monoidal functor from `C` into endofunctors of `C`.
-/
instance : (tensoringRight C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := (rightUnitorNatIso C).symm
      μIso := fun X Y => (isoWhiskerRight (curriedAssociatorNatIso C)
      ((evaluation C (C ⥤ C)).obj X ⋙ (evaluation C C).obj Y)) }

@[simp] lemma tensoringRight_ε :
    ε (tensoringRight C) = (rightUnitorNatIso C).inv := rfl

@[simp] lemma tensoringRight_η :
    η (tensoringRight C) = (rightUnitorNatIso C).hom := rfl

@[simp] lemma tensoringRight_μ (X Y : C) (Z : C) :
    (μ (tensoringRight C) X Y).app Z = (α_ Z X Y).hom := rfl

@[simp] lemma tensoringRight_δ (X Y : C) (Z : C) :
    (δ (tensoringRight C) X Y).app Z = (α_ Z X Y).inv := rfl

end MonoidalCategory

variable {C}
variable {M : Type*} [Category M] [MonoidalCategory M] (F : M ⥤ (C ⥤ C))

@[reassoc (attr := simp)]
theorem μ_δ_app (i j : M) (X : C) [F.Monoidal] :
    (μ F i j).app X ≫ (δ F i j).app X = 𝟙 _ :=
  (μIso F i j).hom_inv_id_app X

@[reassoc (attr := simp)]
theorem δ_μ_app (i j : M) (X : C) [F.Monoidal] :
    (δ F i j).app X ≫ (μ F i j).app X = 𝟙 _ :=
  (μIso F i j).inv_hom_id_app X

@[reassoc (attr := simp)]
theorem ε_η_app (X : C) [F.Monoidal] : (ε F).app X ≫ (η F).app X = 𝟙 _ :=
  (εIso F).hom_inv_id_app X

@[reassoc (attr := simp)]
theorem η_ε_app (X : C) [F.Monoidal] : (η F).app X ≫ (ε F).app X = 𝟙 _ :=
  (εIso F).inv_hom_id_app X

@[reassoc (attr := simp)]
theorem ε_naturality {X Y : C} (f : X ⟶ Y) [F.LaxMonoidal] :
    (ε F).app X ≫ (F.obj (𝟙_ M)).map f = f ≫ (ε F).app Y :=
  ((ε F).naturality f).symm

@[reassoc (attr := simp)]
theorem η_naturality {X Y : C} (f : X ⟶ Y) [F.OplaxMonoidal]:
    (η F).app X ≫ (𝟙_ (C ⥤ C)).map f = (η F).app X ≫ f := by
  simp

@[reassoc (attr := simp)]
theorem μ_naturality {m n : M} {X Y : C} (f : X ⟶ Y) [F.LaxMonoidal] :
    (F.obj n).map ((F.obj m).map f) ≫ (μ F m n).app Y = (μ F m n).app X ≫ (F.obj _).map f :=
  (μ F m n).naturality f

-- This is a simp lemma in the reverse direction via `NatTrans.naturality`.
@[reassoc]
theorem δ_naturality {m n : M} {X Y : C} (f : X ⟶ Y) [F.OplaxMonoidal]:
    (δ F m n).app X ≫ (F.obj n).map ((F.obj m).map f) =
      (F.obj _).map f ≫ (δ F m n).app Y := by simp

-- This is not a simp lemma since it could be proved by the lemmas later.
@[reassoc]
theorem μ_naturality₂ {m n m' n' : M} (f : m ⟶ m') (g : n ⟶ n') (X : C) [F.LaxMonoidal] :
    (F.map g).app ((F.obj m).obj X) ≫ (F.obj n').map ((F.map f).app X) ≫ (μ F m' n').app X =
      (μ F m n).app X ≫ (F.map (f ⊗ₘ g)).app X := by
  have := congr_app (μ_natural F f g) X
  dsimp at this
  simpa using this

@[reassoc (attr := simp)]
theorem μ_naturalityₗ {m n m' : M} (f : m ⟶ m') (X : C) [F.LaxMonoidal]:
    (F.obj n).map ((F.map f).app X) ≫ (μ F m' n).app X =
      (μ F m n).app X ≫ (F.map (f ▷ n)).app X := by
  rw [← tensorHom_id, ← μ_naturality₂ F f (𝟙 n) X]
  simp

@[reassoc (attr := simp)]
theorem μ_naturalityᵣ {m n n' : M} (g : n ⟶ n') (X : C) [F.LaxMonoidal] :
    (F.map g).app ((F.obj m).obj X) ≫ (μ F m n').app X =
      (μ F m n).app X ≫ (F.map (m ◁ g)).app X := by
  rw [← id_tensorHom, ← μ_naturality₂ F (𝟙 m) g X]
  simp

@[reassoc (attr := simp)]
theorem δ_naturalityₗ {m n m' : M} (f : m ⟶ m') (X : C) [F.OplaxMonoidal] :
    (δ F m n).app X ≫ (F.obj n).map ((F.map f).app X) =
      (F.map (f ▷ n)).app X ≫ (δ F m' n).app X :=
  congr_app (δ_natural_left F f n) X

@[reassoc (attr := simp)]
theorem δ_naturalityᵣ {m n n' : M} (g : n ⟶ n') (X : C) [F.OplaxMonoidal]:
    (δ F m n).app X ≫ (F.map g).app ((F.obj m).obj X) =
      (F.map (m ◁ g)).app X ≫ (δ F m n').app X :=
  congr_app (δ_natural_right F m g) X

@[reassoc]
theorem left_unitality_app (n : M) (X : C) [F.LaxMonoidal]:
    (F.obj n).map ((ε F).app X) ≫ (μ F (𝟙_ M) n).app X ≫ (F.map (λ_ n).hom).app X = 𝟙 _ :=
  congr_app (left_unitality F n).symm X

@[simp, reassoc]
theorem obj_ε_app (n : M) (X : C) [F.Monoidal]:
    (F.obj n).map ((ε F).app X) = (F.map (λ_ n).inv).app X ≫ (δ F (𝟙_ M) n).app X := by
  rw [map_leftUnitor_inv]
  dsimp
  simp only [Category.id_comp, Category.assoc, μ_δ_app, endofunctorMonoidalCategory_tensorObj_obj,
    Category.comp_id]

@[simp, reassoc]
theorem obj_η_app (n : M) (X : C) [F.Monoidal] :
    (F.obj n).map ((η F).app X) = (μ F (𝟙_ M) n).app X ≫ (F.map (λ_ n).hom).app X := by
  rw [← cancel_mono ((F.obj n).map ((ε F).app X)), ← Functor.map_comp]
  simp

@[reassoc]
theorem right_unitality_app (n : M) (X : C) [F.Monoidal] :
    (ε F).app ((F.obj n).obj X) ≫ (μ F n (𝟙_ M)).app X ≫ (F.map (ρ_ n).hom).app X = 𝟙 _ :=
  congr_app (Functor.LaxMonoidal.right_unitality F n).symm X

@[simp]
theorem ε_app_obj (n : M) (X : C) [F.Monoidal] :
    (ε F).app ((F.obj n).obj X) = (F.map (ρ_ n).inv).app X ≫ (δ F n (𝟙_ M)).app X := by
  rw [map_rightUnitor_inv]
  dsimp
  simp only [Category.id_comp, Category.assoc, μ_δ_app,
    endofunctorMonoidalCategory_tensorObj_obj, Category.comp_id]

@[simp]
theorem η_app_obj (n : M) (X : C) [F.Monoidal] :
    (η F).app ((F.obj n).obj X) = (μ F n (𝟙_ M)).app X ≫ (F.map (ρ_ n).hom).app X := by
  rw [map_rightUnitor]
  dsimp
  simp only [Category.comp_id, μ_δ_app_assoc]

@[reassoc]
theorem associativity_app (m₁ m₂ m₃ : M) (X : C) [F.LaxMonoidal] :
    (F.obj m₃).map ((μ F m₁ m₂).app X) ≫
        (μ F (m₁ ⊗ m₂) m₃).app X ≫ (F.map (α_ m₁ m₂ m₃).hom).app X =
      (μ F m₂ m₃).app ((F.obj m₁).obj X) ≫ (μ F m₁ (m₂ ⊗ m₃)).app X := by
  have := congr_app (associativity F m₁ m₂ m₃) X
  dsimp at this
  simpa using this

@[simp, reassoc]
theorem obj_μ_app (m₁ m₂ m₃ : M) (X : C) [F.Monoidal] :
    (F.obj m₃).map ((μ F m₁ m₂).app X) =
      (μ F m₂ m₃).app ((F.obj m₁).obj X) ≫
        (μ F m₁ (m₂ ⊗ m₃)).app X ≫
          (F.map (α_ m₁ m₂ m₃).inv).app X ≫ (δ F (m₁ ⊗ m₂) m₃).app X := by
  rw [← associativity_app_assoc]
  simp

@[simp, reassoc]
theorem obj_μ_inv_app (m₁ m₂ m₃ : M) (X : C) [F.Monoidal] :
    (F.obj m₃).map ((δ F m₁ m₂).app X) =
      (μ F (m₁ ⊗ m₂) m₃).app X ≫
        (F.map (α_ m₁ m₂ m₃).hom).app X ≫
          (δ F m₁ (m₂ ⊗ m₃)).app X ≫ (δ F m₂ m₃).app ((F.obj m₁).obj X) := by
  rw [map_associator]
  dsimp
  simp only [Category.id_comp, Category.assoc, μ_δ_app_assoc, μ_δ_app,
    endofunctorMonoidalCategory_tensorObj_obj, Category.comp_id]

@[reassoc (attr := simp)]
theorem obj_zero_map_μ_app {m : M} {X Y : C} (f : X ⟶ (F.obj m).obj Y) [F.Monoidal] :
    (F.obj (𝟙_ M)).map f ≫ (μ F m (𝟙_ M)).app _ =
    (η F).app _ ≫ f ≫ (F.map (ρ_ m).inv).app _ := by
  rw [← cancel_epi ((ε F).app _), ← cancel_mono ((δ F _ _).app _)]
  simp

@[simp]
theorem obj_μ_zero_app (m₁ m₂ : M) (X : C) [F.Monoidal]:
    (μ F (𝟙_ M) m₂).app ((F.obj m₁).obj X) ≫ (μ F m₁ (𝟙_ M ⊗ m₂)).app X ≫
    (F.map (α_ m₁ (𝟙_ M) m₂).inv).app X ≫ (δ F (m₁ ⊗ 𝟙_ M) m₂).app X =
    (μ F (𝟙_ M) m₂).app ((F.obj m₁).obj X) ≫
    (F.map (λ_ m₂).hom).app ((F.obj m₁).obj X) ≫ (F.obj m₂).map ((F.map (ρ_ m₁).inv).app X) := by
  rw [← obj_η_app_assoc, ← Functor.map_comp]
  simp

/-- If `m ⊗ n ≅ 𝟙_M`, then `F.obj m` is a left inverse of `F.obj n`. -/
@[simps!]
noncomputable def unitOfTensorIsoUnit (m n : M) (h : m ⊗ n ≅ 𝟙_ M) [F.Monoidal] :
    F.obj m ⋙ F.obj n ≅ 𝟭 C :=
  μIso F m n ≪≫ F.mapIso h ≪≫ (εIso F).symm

/-- If `m ⊗ n ≅ 𝟙_M` and `n ⊗ m ≅ 𝟙_M` (subject to some commuting constraints),
  then `F.obj m` and `F.obj n` forms a self-equivalence of `C`. -/
@[simps]
noncomputable def equivOfTensorIsoUnit (m n : M) (h₁ : m ⊗ n ≅ 𝟙_ M) (h₂ : n ⊗ m ≅ 𝟙_ M)
    (H : h₁.hom ▷ m ≫ (λ_ m).hom = (α_ m n m).hom ≫ m ◁ h₂.hom ≫ (ρ_ m).hom) [F.Monoidal] :
    C ≌ C where
  functor := F.obj m
  inverse := F.obj n
  unitIso := (unitOfTensorIsoUnit F m n h₁).symm
  counitIso := unitOfTensorIsoUnit F n m h₂
  functor_unitIso_comp X := by
    dsimp
    simp only [μ_naturalityᵣ_assoc, μ_naturalityₗ_assoc, η_app_obj, Category.assoc,
      obj_μ_inv_app, Functor.map_comp, δ_μ_app_assoc, obj_ε_app,
      unitOfTensorIsoUnit_inv_app]
    simp only [← NatTrans.comp_app, ← F.map_comp, ← H, inv_hom_whiskerRight_assoc,
      Iso.inv_hom_id, Functor.map_id, NatTrans.id_app]

end CategoryTheory
