/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.AlgebraicTopology.SimplicialObject
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Arrow

#align_import algebraic_topology.cech_nerve from "leanprover-community/mathlib"@"618ea3d5c99240cd7000d8376924906a148bf9ff"

/-!

# The Čech Nerve

This file provides a definition of the Čech nerve associated to an arrow, provided
the base category has the correct wide pullbacks.

Several variants are provided, given `f : Arrow C`:
1. `f.cechNerve` is the Čech nerve, considered as a simplicial object in `C`.
2. `f.augmentedCechNerve` is the augmented Čech nerve, considered as an
  augmented simplicial object in `C`.
3. `SimplicialObject.cechNerve` and `SimplicialObject.augmentedCechNerve` are
  functorial versions of 1 resp. 2.

We end the file with a description of the Čech nerve of an arrow `X ⟶ ⊤_ C` to a terminal
object, when `C` has finite products. We call this `cechNerveTerminalFrom`. When `C` is
`G`-Set this gives us `EG` (the universal cover of the classifying space of `G`) as a simplicial
`G`-set, which is useful for group cohomology.

-/


open CategoryTheory

open CategoryTheory.Limits

noncomputable section

universe v u w

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory.Arrow

variable (f : Arrow C)

variable [∀ n : ℕ, HasWidePullback.{0} f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]

/-- The Čech nerve associated to an arrow. -/
@[simps]
def cechNerve : SimplicialObject C where
  obj n := widePullback.{0} f.right (fun _ : Fin (n.unop.len + 1) => f.left) fun _ => f.hom
  map g := WidePullback.lift (WidePullback.base _)
    (fun i => WidePullback.π _ (g.unop.toOrderHom i)) (by aesop_cat)
                                                          -- 🎉 no goals
#align category_theory.arrow.cech_nerve CategoryTheory.Arrow.cechNerve

/-- The morphism between Čech nerves associated to a morphism of arrows. -/
@[simps]
def mapCechNerve {f g : Arrow C}
    [∀ n : ℕ, HasWidePullback f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]
    [∀ n : ℕ, HasWidePullback g.right (fun _ : Fin (n + 1) => g.left) fun _ => g.hom] (F : f ⟶ g) :
    f.cechNerve ⟶ g.cechNerve where
  app n :=
    WidePullback.lift (WidePullback.base _ ≫ F.right) (fun i => WidePullback.π _ i ≫ F.left)
      fun j => by simp
                  -- 🎉 no goals
#align category_theory.arrow.map_cech_nerve CategoryTheory.Arrow.mapCechNerve

/-- The augmented Čech nerve associated to an arrow. -/
@[simps]
def augmentedCechNerve : SimplicialObject.Augmented C where
  left := f.cechNerve
  right := f.right
  hom := { app := fun i => WidePullback.base _ }
#align category_theory.arrow.augmented_cech_nerve CategoryTheory.Arrow.augmentedCechNerve

/-- The morphism between augmented Čech nerve associated to a morphism of arrows. -/
@[simps]
def mapAugmentedCechNerve {f g : Arrow C}
    [∀ n : ℕ, HasWidePullback f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]
    [∀ n : ℕ, HasWidePullback g.right (fun _ : Fin (n + 1) => g.left) fun _ => g.hom] (F : f ⟶ g) :
    f.augmentedCechNerve ⟶ g.augmentedCechNerve where
  left := mapCechNerve F
  right := F.right
#align category_theory.arrow.map_augmented_cech_nerve CategoryTheory.Arrow.mapAugmentedCechNerve

end CategoryTheory.Arrow

namespace CategoryTheory

namespace SimplicialObject

variable
  [∀ (n : ℕ) (f : Arrow C), HasWidePullback f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]

/-- The Čech nerve construction, as a functor from `Arrow C`. -/
@[simps]
def cechNerve : Arrow C ⥤ SimplicialObject C where
  obj f := f.cechNerve
  map F := Arrow.mapCechNerve F
#align category_theory.simplicial_object.cech_nerve CategoryTheory.SimplicialObject.cechNerve

/-- The augmented Čech nerve construction, as a functor from `Arrow C`. -/
@[simps!]
def augmentedCechNerve : Arrow C ⥤ SimplicialObject.Augmented C where
  obj f := f.augmentedCechNerve
  map F := Arrow.mapAugmentedCechNerve F
#align category_theory.simplicial_object.augmented_cech_nerve CategoryTheory.SimplicialObject.augmentedCechNerve

/-- A helper function used in defining the Čech adjunction. -/
@[simps]
def equivalenceRightToLeft (X : SimplicialObject.Augmented C) (F : Arrow C)
    (G : X ⟶ F.augmentedCechNerve) : Augmented.toArrow.obj X ⟶ F where
  left := G.left.app _ ≫ WidePullback.π _ 0
  right := G.right
  w := by
    have := G.w
    -- ⊢ (𝟭 C).map (NatTrans.app G.left (Opposite.op (SimplexCategory.mk 0)) ≫ WidePu …
    apply_fun fun e => e.app (Opposite.op <| SimplexCategory.mk 0) at this
    -- ⊢ (𝟭 C).map (NatTrans.app G.left (Opposite.op (SimplexCategory.mk 0)) ≫ WidePu …
    simpa using this
    -- 🎉 no goals
#align category_theory.simplicial_object.equivalence_right_to_left CategoryTheory.SimplicialObject.equivalenceRightToLeft

/-- A helper function used in defining the Čech adjunction. -/
@[simps]
def equivalenceLeftToRight (X : SimplicialObject.Augmented C) (F : Arrow C)
    (G : Augmented.toArrow.obj X ⟶ F) : X ⟶ F.augmentedCechNerve where
  left :=
    { app := fun x =>
        Limits.WidePullback.lift (X.hom.app _ ≫ G.right)
          (fun i => X.left.map (SimplexCategory.const x.unop i).op ≫ G.left) fun i => by
          dsimp
          -- ⊢ (X.left.map (SimplexCategory.const x.unop i).op ≫ G.left) ≫ F.hom = NatTrans …
          erw [Category.assoc, Arrow.w, Augmented.toArrow_obj_hom, NatTrans.naturality_assoc,
            Functor.const_obj_map, Category.id_comp]
      naturality := by
        intro x y f
        -- ⊢ X.left.map f ≫ (fun x => WidePullback.lift (NatTrans.app X.hom x ≫ G.right)  …
        dsimp
        -- ⊢ X.left.map f ≫ WidePullback.lift (NatTrans.app X.hom y ≫ G.right) (fun i =>  …
        ext
        -- ⊢ (X.left.map f ≫ WidePullback.lift (NatTrans.app X.hom y ≫ G.right) (fun i => …
        · dsimp
          -- ⊢ (X.left.map f ≫ WidePullback.lift (NatTrans.app X.hom y ≫ G.right) (fun i => …
          simp only [WidePullback.lift_π, Category.assoc, ← X.left.map_comp_assoc]
          -- ⊢ X.left.map (f ≫ (SimplexCategory.const y.unop j✝).op) ≫ G.left = X.left.map  …
          rfl
          -- 🎉 no goals
        · dsimp
          -- ⊢ ((X.left.map f ≫ WidePullback.lift (NatTrans.app X.hom y ≫ G.right) (fun i = …
          simp }
          -- 🎉 no goals
  right := G.right
#align category_theory.simplicial_object.equivalence_left_to_right CategoryTheory.SimplicialObject.equivalenceLeftToRight

/-- A helper function used in defining the Čech adjunction. -/
@[simps]
def cechNerveEquiv (X : SimplicialObject.Augmented C) (F : Arrow C) :
    (Augmented.toArrow.obj X ⟶ F) ≃ (X ⟶ F.augmentedCechNerve) where
  toFun := equivalenceLeftToRight _ _
  invFun := equivalenceRightToLeft _ _
  left_inv := by
    intro A
    -- ⊢ equivalenceRightToLeft X F (equivalenceLeftToRight X F A) = A
    ext
    -- ⊢ (equivalenceRightToLeft X F (equivalenceLeftToRight X F A)).left = A.left
    · dsimp
      -- ⊢ WidePullback.lift (NatTrans.app X.hom (Opposite.op (SimplexCategory.mk 0)) ≫ …
      erw [WidePullback.lift_π]
      -- ⊢ X.left.map (SimplexCategory.const (SimplexCategory.mk 0) 0).op ≫ A.left = A. …
      nth_rw 2 [← Category.id_comp A.left]
      -- ⊢ X.left.map (SimplexCategory.const (SimplexCategory.mk 0) 0).op ≫ A.left = 𝟙  …
      congr 1
      -- ⊢ X.left.map (SimplexCategory.const (SimplexCategory.mk 0) 0).op = 𝟙 (Augmente …
      convert X.left.map_id _
      -- ⊢ (SimplexCategory.const (SimplexCategory.mk 0) 0).op = 𝟙 (Opposite.op (Simple …
      rw [← op_id]
      -- ⊢ (SimplexCategory.const (SimplexCategory.mk 0) 0).op = (𝟙 (SimplexCategory.mk …
      congr 1
      -- ⊢ SimplexCategory.const (SimplexCategory.mk 0) 0 = 𝟙 (SimplexCategory.mk 0)
      ext ⟨a, ha⟩
      -- ⊢ ↑(↑(SimplexCategory.Hom.toOrderHom (SimplexCategory.const (SimplexCategory.m …
      change a < 1 at ha
      -- ⊢ ↑(↑(SimplexCategory.Hom.toOrderHom (SimplexCategory.const (SimplexCategory.m …
      change 0 = a
      -- ⊢ 0 = a
      linarith
      -- 🎉 no goals
    · rfl
      -- 🎉 no goals
  right_inv := by
    intro A
    -- ⊢ equivalenceLeftToRight X F (equivalenceRightToLeft X F A) = A
    ext x : 2
    -- ⊢ NatTrans.app (equivalenceLeftToRight X F (equivalenceRightToLeft X F A)).lef …
    · refine' WidePullback.hom_ext _ _ _ (fun j => _) _
      -- ⊢ NatTrans.app (equivalenceLeftToRight X F (equivalenceRightToLeft X F A)).lef …
      · dsimp
        -- ⊢ WidePullback.lift (NatTrans.app X.hom x ≫ A.right) (fun i => X.left.map (Sim …
        simp
        -- ⊢ NatTrans.app A.left x ≫ WidePullback.π (fun x => F.hom) (↑(SimplexCategory.H …
        rfl
        -- 🎉 no goals
      · simpa using congr_app A.w.symm x
        -- 🎉 no goals
    · rfl
      -- 🎉 no goals
#align category_theory.simplicial_object.cech_nerve_equiv CategoryTheory.SimplicialObject.cechNerveEquiv

/-- The augmented Čech nerve construction is right adjoint to the `toArrow` functor. -/
abbrev cechNerveAdjunction : (Augmented.toArrow : _ ⥤ Arrow C) ⊣ augmentedCechNerve :=
  Adjunction.mkOfHomEquiv
    { homEquiv := cechNerveEquiv
      homEquiv_naturality_left_symm := by dsimp [cechNerveEquiv]; aesop_cat
                                          -- ⊢ ∀ {X' X : Augmented C} {Y : Arrow C} (f : X' ⟶ X) (g : X ⟶ augmentedCechNerv …
                                                                  -- 🎉 no goals
      homEquiv_naturality_right := by dsimp [cechNerveEquiv]; aesop_cat }
                                      -- ⊢ ∀ {X : Augmented C} {Y Y' : Arrow C} (f : Augmented.toArrow.obj X ⟶ Y) (g :  …
                                                              -- 🎉 no goals
#align category_theory.simplicial_object.cech_nerve_adjunction CategoryTheory.SimplicialObject.cechNerveAdjunction

end SimplicialObject

end CategoryTheory

namespace CategoryTheory.Arrow

variable (f : Arrow C)

variable [∀ n : ℕ, HasWidePushout f.left (fun _ : Fin (n + 1) => f.right) fun _ => f.hom]

/-- The Čech conerve associated to an arrow. -/
@[simps]
def cechConerve : CosimplicialObject C where
  obj n := widePushout f.left (fun _ : Fin (n.len + 1) => f.right) fun _ => f.hom
  map {x y} g := by
    refine' WidePushout.desc (WidePushout.head _)
      (fun i => (@WidePushout.ι _ _ _ _ _ (fun _ => f.hom) ?_ (g.toOrderHom i))) (fun j => _)
    erw [← WidePushout.arrow_ι]
    -- 🎉 no goals
#align category_theory.arrow.cech_conerve CategoryTheory.Arrow.cechConerve

/-- The morphism between Čech conerves associated to a morphism of arrows. -/
@[simps]
def mapCechConerve {f g : Arrow C}
    [∀ n : ℕ, HasWidePushout f.left (fun _ : Fin (n + 1) => f.right) fun _ => f.hom]
    [∀ n : ℕ, HasWidePushout g.left (fun _ : Fin (n + 1) => g.right) fun _ => g.hom] (F : f ⟶ g) :
    f.cechConerve ⟶ g.cechConerve where
  app n := WidePushout.desc (F.left ≫ WidePushout.head _)
    (fun i => F.right ≫ (by apply WidePushout.ι _ i))
                            -- 🎉 no goals
    (fun i => (by rw [← Arrow.w_assoc F, ← WidePushout.arrow_ι]))
                  -- 🎉 no goals
#align category_theory.arrow.map_cech_conerve CategoryTheory.Arrow.mapCechConerve

/-- The augmented Čech conerve associated to an arrow. -/
@[simps]
def augmentedCechConerve : CosimplicialObject.Augmented C where
  left := f.left
  right := f.cechConerve
  hom :=
    { app := fun i => (WidePushout.head _ : f.left ⟶ _) }
#align category_theory.arrow.augmented_cech_conerve CategoryTheory.Arrow.augmentedCechConerve

/-- The morphism between augmented Čech conerves associated to a morphism of arrows. -/
@[simps]
def mapAugmentedCechConerve {f g : Arrow C}
    [∀ n : ℕ, HasWidePushout f.left (fun _ : Fin (n + 1) => f.right) fun _ => f.hom]
    [∀ n : ℕ, HasWidePushout g.left (fun _ : Fin (n + 1) => g.right) fun _ => g.hom] (F : f ⟶ g) :
    f.augmentedCechConerve ⟶ g.augmentedCechConerve where
  left := F.left
  right := mapCechConerve F
#align category_theory.arrow.map_augmented_cech_conerve CategoryTheory.Arrow.mapAugmentedCechConerve

end CategoryTheory.Arrow

namespace CategoryTheory

namespace CosimplicialObject

variable
  [∀ (n : ℕ) (f : Arrow C), HasWidePushout f.left (fun _ : Fin (n + 1) => f.right) fun _ => f.hom]

/-- The Čech conerve construction, as a functor from `Arrow C`. -/
@[simps]
def cechConerve : Arrow C ⥤ CosimplicialObject C where
  obj f := f.cechConerve
  map F := Arrow.mapCechConerve F
#align category_theory.cosimplicial_object.cech_conerve CategoryTheory.CosimplicialObject.cechConerve

/-- The augmented Čech conerve construction, as a functor from `Arrow C`. -/
@[simps]
def augmentedCechConerve : Arrow C ⥤ CosimplicialObject.Augmented C where
  obj f := f.augmentedCechConerve
  map F := Arrow.mapAugmentedCechConerve F
#align category_theory.cosimplicial_object.augmented_cech_conerve CategoryTheory.CosimplicialObject.augmentedCechConerve

/-- A helper function used in defining the Čech conerve adjunction. -/
@[simps]
def equivalenceLeftToRight (F : Arrow C) (X : CosimplicialObject.Augmented C)
    (G : F.augmentedCechConerve ⟶ X) : F ⟶ Augmented.toArrow.obj X where
  left := G.left
  right := (WidePushout.ι _ 0 ≫ G.right.app (SimplexCategory.mk 0) : _)
  w := by
    dsimp
    -- ⊢ G.left ≫ NatTrans.app X.hom (SimplexCategory.mk 0) = F.hom ≫ WidePushout.ι ( …
    rw [@WidePushout.arrow_ι_assoc _ _ _ _ _ (fun (_ : Fin 1) => F.hom)
      (by dsimp; infer_instance)]
    exact congr_app G.w (SimplexCategory.mk 0)
    -- 🎉 no goals
#align category_theory.cosimplicial_object.equivalence_left_to_right CategoryTheory.CosimplicialObject.equivalenceLeftToRight

/-- A helper function used in defining the Čech conerve adjunction. -/
@[simps!]
def equivalenceRightToLeft (F : Arrow C) (X : CosimplicialObject.Augmented C)
    (G : F ⟶ Augmented.toArrow.obj X) : F.augmentedCechConerve ⟶ X where
  left := G.left
  right :=
    { app := fun x =>
        Limits.WidePushout.desc (G.left ≫ X.hom.app _)
          (fun i => G.right ≫ X.right.map (SimplexCategory.const x i))
          (by
            rintro j
            -- ⊢ F.hom ≫ (fun i => G.right ≫ X.right.map (SimplexCategory.const x i)) j = G.l …
            rw [← Arrow.w_assoc G]
            -- ⊢ G.left ≫ (Augmented.toArrow.obj X).hom ≫ X.right.map (SimplexCategory.const  …
            have t := X.hom.naturality (x.const j)
            -- ⊢ G.left ≫ (Augmented.toArrow.obj X).hom ≫ X.right.map (SimplexCategory.const  …
            dsimp at t ⊢
            -- ⊢ G.left ≫ NatTrans.app X.hom (SimplexCategory.mk 0) ≫ X.right.map (SimplexCat …
            simp only [Category.id_comp] at t
            -- ⊢ G.left ≫ NatTrans.app X.hom (SimplexCategory.mk 0) ≫ X.right.map (SimplexCat …
            rw [← t])
            -- 🎉 no goals
      naturality := by
        intro x y f
        -- ⊢ (Arrow.augmentedCechConerve F).right.map f ≫ (fun x => WidePushout.desc (G.l …
        dsimp
        -- ⊢ WidePushout.desc (WidePushout.head fun x => F.hom) (fun i => WidePushout.ι ( …
        ext
        -- ⊢ WidePushout.ι (fun x => F.hom) j✝ ≫ WidePushout.desc (WidePushout.head fun x …
        · dsimp
          -- ⊢ WidePushout.ι (fun x => F.hom) j✝ ≫ WidePushout.desc (WidePushout.head fun x …
          simp only [WidePushout.ι_desc_assoc, WidePushout.ι_desc]
          -- ⊢ G.right ≫ X.right.map (SimplexCategory.const y (↑(SimplexCategory.Hom.toOrde …
          rw [Category.assoc, ← X.right.map_comp]
          -- ⊢ G.right ≫ X.right.map (SimplexCategory.const y (↑(SimplexCategory.Hom.toOrde …
          rfl
          -- 🎉 no goals
        · dsimp
          -- ⊢ (WidePushout.head fun x => F.hom) ≫ WidePushout.desc (WidePushout.head fun x …
          simp only [Functor.const_obj_map, ← NatTrans.naturality, WidePushout.head_desc_assoc,
            WidePushout.head_desc, Category.assoc]
          erw [Category.id_comp] }
          -- 🎉 no goals
#align category_theory.cosimplicial_object.equivalence_right_to_left CategoryTheory.CosimplicialObject.equivalenceRightToLeft

/-- A helper function used in defining the Čech conerve adjunction. -/
@[simps]
def cechConerveEquiv (F : Arrow C) (X : CosimplicialObject.Augmented C) :
    (F.augmentedCechConerve ⟶ X) ≃ (F ⟶ Augmented.toArrow.obj X) where
  toFun := equivalenceLeftToRight _ _
  invFun := equivalenceRightToLeft _ _
  left_inv := by
    intro A
    -- ⊢ equivalenceRightToLeft F X (equivalenceLeftToRight F X A) = A
    ext x : 2
    -- ⊢ (equivalenceRightToLeft F X (equivalenceLeftToRight F X A)).left = A.left
    · rfl
      -- 🎉 no goals
    · refine' WidePushout.hom_ext _ _ _ (fun j => _) _
      -- ⊢ WidePushout.ι (fun x => F.hom) j ≫ NatTrans.app (equivalenceRightToLeft F X  …
      · dsimp
        -- ⊢ WidePushout.ι (fun x => F.hom) j ≫ WidePushout.desc (A.left ≫ NatTrans.app X …
        simp only [Category.assoc, ← NatTrans.naturality A.right, Arrow.augmentedCechConerve_right,
          SimplexCategory.len_mk, Arrow.cechConerve_map, colimit.ι_desc,
          WidePushoutShape.mkCocone_ι_app, colimit.ι_desc_assoc]
        rfl
        -- 🎉 no goals
      · dsimp
        -- ⊢ (WidePushout.head fun x => F.hom) ≫ WidePushout.desc (A.left ≫ NatTrans.app  …
        rw [colimit.ι_desc]
        -- ⊢ NatTrans.app (WidePushoutShape.mkCocone (A.left ≫ NatTrans.app X.hom x) (fun …
        exact congr_app A.w x
        -- 🎉 no goals
  right_inv := by
    intro A
    -- ⊢ equivalenceLeftToRight F X (equivalenceRightToLeft F X A) = A
    ext
    -- ⊢ (equivalenceLeftToRight F X (equivalenceRightToLeft F X A)).left = A.left
    · rfl
      -- 🎉 no goals
    · dsimp
      -- ⊢ WidePushout.ι (fun x => F.hom) 0 ≫ WidePushout.desc (A.left ≫ NatTrans.app X …
      erw [WidePushout.ι_desc]
      -- ⊢ A.right ≫ X.right.map (SimplexCategory.const (SimplexCategory.mk 0) 0) = A.r …
      nth_rw 2 [← Category.comp_id A.right]
      -- ⊢ A.right ≫ X.right.map (SimplexCategory.const (SimplexCategory.mk 0) 0) = A.r …
      congr 1
      -- ⊢ X.right.map (SimplexCategory.const (SimplexCategory.mk 0) 0) = 𝟙 (Augmented. …
      convert X.right.map_id _
      -- ⊢ SimplexCategory.const (SimplexCategory.mk 0) 0 = 𝟙 (SimplexCategory.mk 0)
      ext ⟨a, ha⟩
      -- ⊢ ↑(↑(SimplexCategory.Hom.toOrderHom (SimplexCategory.const (SimplexCategory.m …
      change a < 1 at ha
      -- ⊢ ↑(↑(SimplexCategory.Hom.toOrderHom (SimplexCategory.const (SimplexCategory.m …
      change 0 = a
      -- ⊢ 0 = a
      linarith
      -- 🎉 no goals
#align category_theory.cosimplicial_object.cech_conerve_equiv CategoryTheory.CosimplicialObject.cechConerveEquiv

/-- The augmented Čech conerve construction is left adjoint to the `toArrow` functor. -/
abbrev cechConerveAdjunction : augmentedCechConerve ⊣ (Augmented.toArrow : _ ⥤ Arrow C) :=
  Adjunction.mkOfHomEquiv { homEquiv := cechConerveEquiv }
#align category_theory.cosimplicial_object.cech_conerve_adjunction CategoryTheory.CosimplicialObject.cechConerveAdjunction

end CosimplicialObject

/-- Given an object `X : C`, the natural simplicial object sending `[n]` to `Xⁿ⁺¹`. -/
def cechNerveTerminalFrom {C : Type u} [Category.{v} C] [HasFiniteProducts C] (X : C) :
    SimplicialObject C where
  obj n := ∏ fun _ : Fin (n.unop.len + 1) => X
  map f := Limits.Pi.lift fun i => Limits.Pi.π _ (f.unop.toOrderHom i)
#align category_theory.cech_nerve_terminal_from CategoryTheory.cechNerveTerminalFrom

namespace CechNerveTerminalFrom

variable [HasTerminal C] (ι : Type w)

/-- The diagram `Option ι ⥤ C` sending `none` to the terminal object and `some j` to `X`. -/
def wideCospan (X : C) : WidePullbackShape ι ⥤ C :=
  WidePullbackShape.wideCospan (terminal C) (fun _ : ι => X) fun _ => terminal.from X
#align category_theory.cech_nerve_terminal_from.wide_cospan CategoryTheory.CechNerveTerminalFrom.wideCospan

instance uniqueToWideCospanNone (X Y : C) : Unique (Y ⟶ (wideCospan ι X).obj none) := by
  dsimp [wideCospan]
  -- ⊢ Unique (Y ⟶ ⊤_ C)
  infer_instance
  -- 🎉 no goals
#align category_theory.cech_nerve_terminal_from.unique_to_wide_cospan_none CategoryTheory.CechNerveTerminalFrom.uniqueToWideCospanNone

variable [HasFiniteProducts C]

/-- The product `Xᶥ` is the vertex of a limit cone on `wideCospan ι X`. -/
def wideCospan.limitCone [Finite ι] (X : C) : LimitCone (wideCospan ι X) where
  cone :=
    { pt := ∏ fun _ : ι => X
      π :=
        { app := fun X => Option.casesOn X (terminal.from _) fun i => limit.π _ ⟨i⟩
          naturality := fun i j f => by
            cases f
            -- ⊢ ((Functor.const (WidePullbackShape ι)).obj (∏ fun x => X)).map (WidePullback …
            · cases i
              -- ⊢ ((Functor.const (WidePullbackShape ι)).obj (∏ fun x => X)).map (WidePullback …
              all_goals dsimp; simp
              -- 🎉 no goals
            · dsimp
              -- ⊢ 𝟙 (∏ fun x => X) ≫ terminal.from (∏ fun x => X) = limit.π (Discrete.functor  …
              simp only [terminal.comp_from]
              -- ⊢ terminal.from (∏ fun x => X) = limit.π (Discrete.functor fun x => X) { as := …
              exact Subsingleton.elim _ _ } }
              -- 🎉 no goals
  isLimit :=
    { lift := fun s => Limits.Pi.lift fun j => s.π.app (some j)
      fac := fun s j => Option.casesOn j (Subsingleton.elim _ _) fun j => limit.lift_π _ _
      uniq := fun s f h => by
        dsimp
        -- ⊢ f = Pi.lift fun j => NatTrans.app s.π (some j)
        ext j
        -- ⊢ f ≫ Pi.π (fun x => X) j = (Pi.lift fun j => NatTrans.app s.π (some j)) ≫ Pi. …
        dsimp only [Limits.Pi.lift]
        -- ⊢ f ≫ Pi.π (fun x => X) j = limit.lift (Discrete.functor fun b => X) (Fan.mk s …
        rw [limit.lift_π]
        -- ⊢ f ≫ Pi.π (fun x => X) j = NatTrans.app (Fan.mk s.pt fun j => NatTrans.app s. …
        dsimp
        -- ⊢ f ≫ Pi.π (fun x => X) j = NatTrans.app s.π (some j)
        rw [← h (some j)] }
        -- 🎉 no goals
#align category_theory.cech_nerve_terminal_from.wide_cospan.limit_cone CategoryTheory.CechNerveTerminalFrom.wideCospan.limitCone

instance hasWidePullback [Finite ι] (X : C) :
    HasWidePullback (Arrow.mk (terminal.from X)).right
      (fun _ : ι => (Arrow.mk (terminal.from X)).left)
      (fun _ => (Arrow.mk (terminal.from X)).hom) := by
  cases nonempty_fintype ι
  -- ⊢ HasWidePullback (Arrow.mk (terminal.from X)).right (fun x => (Arrow.mk (term …
  exact ⟨⟨wideCospan.limitCone ι X⟩⟩
  -- 🎉 no goals
#align category_theory.cech_nerve_terminal_from.has_wide_pullback CategoryTheory.CechNerveTerminalFrom.hasWidePullback

-- porting note: added to make the following definitions work
instance hasWidePullback' [Finite ι] (X : C) :
    HasWidePullback (⊤_ C)
      (fun _ : ι => X)
      (fun _ => terminal.from X) :=
  hasWidePullback _ _

-- porting note: added to make the following definitions work
instance hasLimit_wideCospan [Finite ι] (X : C) : HasLimit (wideCospan ι X) := hasWidePullback _ _

-- porting note: added to ease the definition of `iso`
/-- the isomorphism to the product induced by the limit cone `wideCospan ι X` -/
def wideCospan.limitIsoPi [Finite ι] (X : C) :
    limit (wideCospan ι X) ≅ ∏ fun _ : ι => X :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
    (wideCospan.limitCone ι X).2)

-- porting note: added to ease the definition of `iso`
@[reassoc (attr := simp)]
lemma wideCospan.limitIsoPi_inv_comp_pi [Finite ι] (X : C) (j : ι) :
    (wideCospan.limitIsoPi ι X).inv ≫ WidePullback.π _ j = Pi.π _ j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ _

@[reassoc (attr := simp)]
lemma wideCospan.limitIsoPi_hom_comp_pi [Finite ι] (X : C) (j : ι) :
    (wideCospan.limitIsoPi ι X).hom ≫ Pi.π _ j = WidePullback.π _ j := by
  rw [← wideCospan.limitIsoPi_inv_comp_pi, Iso.hom_inv_id_assoc]
  -- 🎉 no goals

/-- Given an object `X : C`, the Čech nerve of the hom to the terminal object `X ⟶ ⊤_ C` is
naturally isomorphic to a simplicial object sending `[n]` to `Xⁿ⁺¹` (when `C` is `G-Set`, this is
`EG`, the universal cover of the classifying space of `G`. -/
def iso (X : C) : (Arrow.mk (terminal.from X)).cechNerve ≅ cechNerveTerminalFrom X :=
  NatIso.ofComponents (fun m => wideCospan.limitIsoPi _ _) (fun {m n} f => by
    dsimp only [cechNerveTerminalFrom, Arrow.cechNerve]
    -- ⊢ WidePullback.lift (WidePullback.base fun x => (Arrow.mk (terminal.from X)).h …
    ext ⟨j⟩
    -- ⊢ (WidePullback.lift (WidePullback.base fun x => (Arrow.mk (terminal.from X)). …
    simp only [Category.assoc, limit.lift_π, Fan.mk_π_app]
    -- ⊢ WidePullback.lift (WidePullback.base fun x => (Arrow.mk (terminal.from X)).h …
    erw [wideCospan.limitIsoPi_hom_comp_pi,
      wideCospan.limitIsoPi_hom_comp_pi, limit.lift_π]
    rfl)
    -- 🎉 no goals
#align category_theory.cech_nerve_terminal_from.iso CategoryTheory.CechNerveTerminalFrom.iso

end CechNerveTerminalFrom

end CategoryTheory
