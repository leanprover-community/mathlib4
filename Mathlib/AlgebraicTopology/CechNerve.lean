/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz

! This file was ported from Lean 3 source module algebraic_topology.cech_nerve
! leanprover-community/mathlib commit 618ea3d5c99240cd7000d8376924906a148bf9ff
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.AlgebraicTopology.SimplicialObject
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Arrow

/-!

# The Čech Nerve

This file provides a definition of the Čech nerve associated to an arrow, provided
the base category has the correct wide pullbacks.

Several variants are provided, given `f : arrow C`:
1. `f.cech_nerve` is the Čech nerve, considered as a simplicial object in `C`.
2. `f.augmented_cech_nerve` is the augmented Čech nerve, considered as an
  augmented simplicial object in `C`.
3. `simplicial_object.cech_nerve` and `simplicial_object.augmented_cech_nerve` are
  functorial versions of 1 resp. 2.

We end the file with a description of the Čech nerve of an arrow `X ⟶ ⊤_ C` to a terminal
object, when `C` has finite products. We call this `cech_nerve_terminal_from`. When `C` is
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

/-- The Čech nerve construction, as a functor from `arrow C`. -/
@[simps]
def cechNerve : Arrow C ⥤ SimplicialObject C where
  obj f := f.cechNerve
  map F := Arrow.mapCechNerve F
#align category_theory.simplicial_object.cech_nerve CategoryTheory.SimplicialObject.cechNerve

/-- The augmented Čech nerve construction, as a functor from `arrow C`. -/
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
    apply_fun fun e => e.app (Opposite.op <| SimplexCategory.mk 0) at this
    simpa using this
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
          erw [Category.assoc, Arrow.w, Augmented.toArrow_obj_hom, NatTrans.naturality_assoc,
            Functor.const_obj_map, Category.id_comp]
      naturality := by
        intro x y f
        dsimp
        ext
        . dsimp
          simp only [WidePullback.lift_π, Category.assoc, ← X.left.map_comp_assoc]
          rfl
        . dsimp
          simp }
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
    dsimp
    ext
    · dsimp
      erw [WidePullback.lift_π]
      nth_rw 2 [← Category.id_comp A.left]
      congr 1
      convert X.left.map_id _
      rw [← op_id]
      congr 1
      ext ⟨a, ha⟩
      change a < 1 at ha
      change 0 = a
      linarith
    · rfl
  right_inv := by
    intro A
    dsimp
    ext x : 2
    · refine' WidePullback.hom_ext _ _ _ (fun j => _) _
      . dsimp
        simp
        rfl
      . simpa using congr_app A.w.symm x
    . rfl
#align category_theory.simplicial_object.cech_nerve_equiv CategoryTheory.SimplicialObject.cechNerveEquiv

/-- The augmented Čech nerve construction is right adjoint to the `to_arrow` functor. -/
abbrev cechNerveAdjunction : (Augmented.toArrow : _ ⥤ Arrow C) ⊣ augmentedCechNerve :=
  Adjunction.mkOfHomEquiv
    { homEquiv := cechNerveEquiv
      homEquiv_naturality_left_symm := by dsimp [cechNerveEquiv] ; aesop_cat
      homEquiv_naturality_right := by dsimp [cechNerveEquiv] ; aesop_cat }
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
#align category_theory.arrow.cech_conerve CategoryTheory.Arrow.cechConerve

/-- The morphism between Čech conerves associated to a morphism of arrows. -/
@[simps]
def mapCechConerve {f g : Arrow C}
    [∀ n : ℕ, HasWidePushout f.left (fun _ : Fin (n + 1) => f.right) fun _ => f.hom]
    [∀ n : ℕ, HasWidePushout g.left (fun _ : Fin (n + 1) => g.right) fun _ => g.hom] (F : f ⟶ g) :
    f.cechConerve ⟶ g.cechConerve where
  app n := WidePushout.desc (F.left ≫ WidePushout.head _)
    (fun i => F.right ≫ (by apply WidePushout.ι _ i))
    (fun i => (by rw [← Arrow.w_assoc F, ← WidePushout.arrow_ι]))
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

/-- The Čech conerve construction, as a functor from `arrow C`. -/
@[simps]
def cechConerve : Arrow C ⥤ CosimplicialObject C where
  obj f := f.cechConerve
  map F := Arrow.mapCechConerve F
#align category_theory.cosimplicial_object.cech_conerve CategoryTheory.CosimplicialObject.cechConerve

/-- The augmented Čech conerve construction, as a functor from `arrow C`. -/
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
    rw [@WidePushout.arrow_ι_assoc _ _ _ _ _ (fun (_ : Fin 1) => F.hom)
      (by dsimp ; infer_instance)]
    exact congr_app G.w (SimplexCategory.mk 0)
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
            rw [← Arrow.w_assoc G]
            have t := X.hom.naturality (x.const j)
            dsimp at t ⊢
            simp only [Category.id_comp] at t
            rw [← t])
      naturality := by
        intro x y f
        dsimp
        ext
        · dsimp
          simp only [WidePushout.ι_desc_assoc, WidePushout.ι_desc]
          rw [Category.assoc, ← X.right.map_comp]
          rfl
        · dsimp
          simp only [Functor.const_obj_map, ← NatTrans.naturality, WidePushout.head_desc_assoc,
            WidePushout.head_desc, Category.assoc]
          erw [Category.id_comp] }
#align category_theory.cosimplicial_object.equivalence_right_to_left CategoryTheory.CosimplicialObject.equivalenceRightToLeft

/-- A helper function used in defining the Čech conerve adjunction. -/
@[simps]
def cechConerveEquiv (F : Arrow C) (X : CosimplicialObject.Augmented C) :
    (F.augmentedCechConerve ⟶ X) ≃ (F ⟶ Augmented.toArrow.obj X) where
  toFun := equivalenceLeftToRight _ _
  invFun := equivalenceRightToLeft _ _
  left_inv := by
    intro A
    dsimp
    ext x : 2
    . rfl
    . refine' WidePushout.hom_ext _ _ _ (fun j => _) _
      . dsimp
        simp only [Category.assoc, ← NatTrans.naturality A.right, Arrow.augmentedCechConerve_right,
          SimplexCategory.len_mk, Arrow.cechConerve_map, colimit.ι_desc,
          WidePushoutShape.mkCocone_ι_app, colimit.ι_desc_assoc]
        rfl
      . dsimp
        rw [colimit.ι_desc]
        exact congr_app A.w x
  right_inv := by
    intro A
    ext
    · rfl
    · dsimp
      erw [WidePushout.ι_desc]
      nth_rw 2 [← Category.comp_id A.right]
      congr 1
      convert X.right.map_id _
      ext ⟨a, ha⟩
      change a < 1 at ha
      change 0 = a
      linarith
#align category_theory.cosimplicial_object.cech_conerve_equiv CategoryTheory.CosimplicialObject.cechConerveEquiv

/-- The augmented Čech conerve construction is left adjoint to the `to_arrow` functor. -/
abbrev cechConerveAdjunction : augmentedCechConerve ⊣ (Augmented.toArrow : _ ⥤ Arrow C) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := cechConerveEquiv
      homEquiv_naturality_left_symm := by aesop_cat
      homEquiv_naturality_right := by aesop_cat }
#align category_theory.cosimplicial_object.cech_conerve_adjunction CategoryTheory.CosimplicialObject.cechConerveAdjunction

end CosimplicialObject

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `discrete_cases #[] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `discrete_cases #[] -/
/-- Given an object `X : C`, the natural simplicial object sending `[n]` to `Xⁿ⁺¹`. -/
def cechNerveTerminalFrom {C : Type u} [Category.{v} C] [HasFiniteProducts C] (X : C) :
    SimplicialObject C where
  obj n := ∏ fun i : Fin (n.unop.len + 1) => X
  map m n f := Limits.Pi.lift fun i => Limits.Pi.π _ (f.unop.toOrderHom i)
  map_id' f :=
    limit.hom_ext fun j => by
      trace
          "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `discrete_cases #[]" <;>
        simpa only [limit.lift_π, category.id_comp]
  map_comp' m n o f g :=
    limit.hom_ext fun j => by
      trace
          "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `discrete_cases #[]" <;>
        simpa only [category.assoc, limit.lift_π, fan.mk_π_app]
#align category_theory.cech_nerve_terminal_from CategoryTheory.cechNerveTerminalFrom

namespace CechNerveTerminalFrom

variable [HasTerminal C] (ι : Type w)

/-- The diagram `option ι ⥤ C` sending `none` to the terminal object and `some j` to `X`. -/
def wideCospan (X : C) : WidePullbackShape ι ⥤ C :=
  WidePullbackShape.wideCospan (terminal C) (fun i : ι => X) fun i => terminal.from X
#align category_theory.cech_nerve_terminal_from.wide_cospan CategoryTheory.cechNerveTerminalFrom.wideCospan

instance uniqueToWideCospanNone (X Y : C) : Unique (Y ⟶ (wideCospan ι X).obj none) := by
  unfold wide_cospan <;> dsimp <;> infer_instance
#align category_theory.cech_nerve_terminal_from.unique_to_wide_cospan_none CategoryTheory.cechNerveTerminalFrom.uniqueToWideCospanNone

variable [HasFiniteProducts C]

/-- The product `Xᶥ` is the vertex of a limit cone on `wide_cospan ι X`. -/
def wideCospan.limitCone [Fintype ι] (X : C) : LimitCone (wideCospan ι X) where
  Cone :=
    { pt := ∏ fun i : ι => X
      π :=
        { app := fun X => Option.casesOn X (terminal.from _) fun i => limit.π _ ⟨i⟩
          naturality' := fun i j f => by
            cases f
            · cases i
              all_goals dsimp; simp
            · dsimp
              simp only [terminal.comp_from]
              exact Subsingleton.elim _ _ } }
  IsLimit :=
    { lift := fun s => Limits.Pi.lift fun j => s.π.app (some j)
      fac := fun s j => Option.casesOn j (Subsingleton.elim _ _) fun j => limit.lift_π _ _
      uniq := fun s f h => by
        ext j
        dsimp only [limits.pi.lift]
        rw [limit.lift_π]
        dsimp
        rw [← h (some j.as)]
        congr
        ext
        rfl }
#align category_theory.cech_nerve_terminal_from.wide_cospan.limit_cone CategoryTheory.cechNerveTerminalFrom.wideCospan.limitCone

instance hasWidePullback [Finite ι] (X : C) :
    HasWidePullback (Arrow.mk (terminal.from X)).right
      (fun i : ι => (Arrow.mk (terminal.from X)).left) fun i => (Arrow.mk (terminal.from X)).Hom :=
  by
  cases nonempty_fintype ι
  exact ⟨⟨wide_cospan.limit_cone ι X⟩⟩
#align category_theory.cech_nerve_terminal_from.has_wide_pullback CategoryTheory.cechNerveTerminalFrom.hasWidePullback

/-- Given an object `X : C`, the Čech nerve of the hom to the terminal object `X ⟶ ⊤_ C` is
naturally isomorphic to a simplicial object sending `[n]` to `Xⁿ⁺¹` (when `C` is `G-Set`, this is
`EG`, the universal cover of the classifying space of `G`. -/
def iso (X : C) : (Arrow.mk (terminal.from X)).cechNerve ≅ cechNerveTerminalFrom X :=
  Iso.symm
    (NatIso.ofComponents
      (fun m =>
        ((limit.isLimit _).conePointUniqueUpToIso
            (wideCospan.limitCone (Fin (m.unop.len + 1)) X).2).symm)
      fun m n f =>
      WidePullback.hom_ext _ _ _
        (by
          intro j
          simp only [category.assoc]
          dsimp only [cech_nerve_terminal_from, wide_pullback.π, pi.lift]
          erw [wide_pullback.lift_π,
            limit.cone_point_unique_up_to_iso_inv_comp (wide_cospan.limit_cone _ _).2,
            (limit.is_limit _).conePointUniqueUpToIso_inv_comp (wide_cospan.limit_cone _ _).2,
            limit.lift_π]
          rfl)
        (@Subsingleton.elim _ (@Unique.subsingleton _ (Limits.uniqueToTerminal _)) _ _))
#align category_theory.cech_nerve_terminal_from.iso CategoryTheory.cechNerveTerminalFrom.iso

end CechNerveTerminalFrom

end CategoryTheory
