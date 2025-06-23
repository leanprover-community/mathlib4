/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.Action.Basic
import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Fubini
import Mathlib.CategoryTheory.Discrete.SumsProducts

/-! # Actions of `Type u` on categories with (co)products

If `C` is a category with all coproducts, then `C` admits
a left action from the monoidal category of types. The
action is given by `J ⊙ₗ c := ∐ (fun _ : J ↦ c)`.
We bundle this action through a `ChosenTypeCopowers` typeclass
that lets users "bring their own colimit cocone" if wanted.
See `sigmaConstAction` for a constructor.


## TODOs

* More interestingly, we should show that if a w-small monoidal category
`C` acts on a `w`-cocomplete category `D`,
then `Cᵒᵖ ⥤ Type w` (with Day convolution monoidal structure) act on the
left on `D`.
* A coproduct-preserving functor is left linear for these structures
* A product-preserving functor is right linear for these structures
* The chosenTypeCopowers structure on Type _
* The chosenTypeCopowers structure on functor categories

-/

universe w v u

namespace CategoryTheory.MonoidalCategory

variable (C : Type u) [Category.{v} C]
open Limits

section

section

variable [HasCoproducts.{w} C]

variable {C}

noncomputable def sigmaConstAssocIso (J J' : Type w) (c : C) :
  (sigmaConst.obj c).obj (J ⊗ J') ≅ (sigmaConst.obj ((sigmaConst.obj c).obj J')).obj J :=
    (HasColimit.isoOfEquivalence (G := Discrete.functor (fun x ↦ c))
      (Discrete.productEquiv (J := J) (K := J')).symm
      (.refl _)).symm ≪≫
      (colimitIsoColimitCurryCompColim _) ≪≫
      HasColimit.isoOfNatIso
        (NatIso.ofComponents
          (fun _ ↦ HasColimit.isoOfNatIso <| .refl _)
          (fun {x y} f ↦ by discrete_cases; dsimp at f; subst f; simp))

@[simps]
noncomputable def sigmaConstUnitIso (c : C) :
  (sigmaConst.obj c).obj (𝟙_ (Type w)) ≅ c where
  hom := Sigma.desc (fun _ ↦ 𝟙 _)
  inv := Sigma.ι (fun _ ↦ c) (PUnit.unit)
  inv_hom_id := Sigma.ι_desc _ _
  hom_inv_id := by
    apply colimit.hom_ext
    intro _
    simp only [Discrete.functor_obj_eq_as, sigmaConst_obj_obj, Sigma.ι, colimit.ι_desc_assoc,
      Cofan.mk_pt, Cofan.mk_ι_app, Category.id_comp, Category.comp_id]
    rfl

section

variable {J J' : Type w}

@[reassoc (attr := simp)]
lemma ι_comp_sigmaConstAssocIso_hom (c : C) (j : J ⊗ J') :
    Sigma.ι (fun _ : J ⊗ J' ↦ c) j ≫ (sigmaConstAssocIso J J' c).hom =
    Sigma.ι _ j.2 ≫ Sigma.ι (fun _ : J ↦ ∐ fun _ ↦ c) j.1 := by
  change _ × _ at j
  change Sigma.ι (fun _ : J × J' ↦ c) j ≫ (sigmaConstAssocIso J J' c).hom =
    Sigma.ι _ j.2 ≫ Sigma.ι (fun _ : J ↦ ∐ fun _ ↦ c) j.1
  simp [sigmaConstAssocIso, Sigma.ι,
    HasColimit.isoOfEquivalence, colimitIsoColimitCurryCompColim_ι_hom_assoc]

@[reassoc (attr := simp)]
lemma ι_comp_ι_comp_sigmaConstAssocIso_inv (c : C) (j : J ⊗ J') :
    Sigma.ι _ j.2 ≫ Sigma.ι (fun _ : J ↦ ∐ fun _ ↦ c) j.1 ≫ (sigmaConstAssocIso J J' c).inv =
    Sigma.ι (fun _ : J ⊗ J' ↦ c) j := by
  simp [← Category.assoc, Iso.comp_inv_eq]

end

variable (C) in
@[simps -isSimp]
noncomputable def typeLeftActionOfHasCoproducts : MonoidalLeftAction (Type w) C where
  actionObj J c := (sigmaConst.obj c).obj J
  actionHomLeft f c := (sigmaConst.obj c).map f
  actionHomRight J _ _ f := (sigmaConst.map f).app J
  actionAssocIso := sigmaConstAssocIso
  actionUnitIso := sigmaConstUnitIso
  whiskerLeft_actionHomLeft J J' J'' f c := by
    apply Sigma.hom_ext
    intro b
    simp [ι_comp_ι_comp_sigmaConstAssocIso_inv (j := (b.1, f b.2))]
  whiskerRight_actionHomLeft _ f c := by
    apply Sigma.hom_ext
    intro b
    simp [ι_comp_ι_comp_sigmaConstAssocIso_inv (j := (f b.1, b.2))]

end

open scoped MonoidalLeftAction

class ChosenTypeCopowers [MonoidalLeftAction (Type w) C] where
  ι {J : Type w} (c : C) (j : J) : c ⟶ (J ⊙ₗ c)
  ι_def {J : Type w} (c : C) (j : J) : c ⟶ J ⊙ₗ c := (λₗ c).inv ≫ (fun _ ↦ j) ⊵ₗ c
  ι_naturality_left {J J' : Type w} (f : J ⟶ J') (c : C) (j : J) :
      ι c j ≫ f ⊵ₗ c = ι c (f j) := by
    aesop_cat

  ι_naturality_right {J : Type w} {c c' : C} (f : c ⟶ c') (j : J) :
      ι c j ≫ J ⊴ₗ f = f ≫ ι c' j := by
    aesop_cat
  ι_unit (c : C) :
      ι c (.unit : 𝟙_ (Type w)) = (λₗ c).inv := by
    aesop_cat
  ιIsColimit (J : Type w) (c : C) : IsColimit <| Cofan.mk (J ⊙ₗ c) (ι c)

namespace ChosenTypeCopowers

attribute [reassoc (attr := simp)] ι_naturality_left ι_naturality_right ι_unit

section

variable {C} [MonoidalLeftAction (Type w) C] [ChosenTypeCopowers.{w} C]

/-- The canonical map `c ⟶ J ⊙ₗ c` corresponding to `j : J`.
If we are to think of `J ⊙ₗ c` as a `J`-indexed coproduct of copies of `c`, this is the
inclusion at the component corresponding to `j`. This is proved in `ι_eq_ι`, but this
definition should be the one that is used when working with the left action
of types on `C`. -/
@[ext 1050]
lemma hom_ext {J : Type w} {c c' : C} {f g : J ⊙ₗ c ⟶ c'} (h : ∀ j, ι c j ≫ f = ι c j ≫ g) :
    f = g :=
  (ιIsColimit J c).hom_ext (fun ⟨j⟩ ↦ by simpa using h j)

/-- Construct a morphism `J ⊙ₗ c ⟶ c'` from a familiy of maps `c ⟶ c' -/
noncomputable def desc {J : Type w} {c c' : C} (φ : J → (c ⟶ c')) : J ⊙ₗ c ⟶ c' :=
   Cofan.IsColimit.desc (ιIsColimit J c) φ

@[reassoc (attr := simp)]
lemma ι_desc {J : Type w} {c c' : C} (φ : J → (c ⟶ c')) (j : J) :
   ι c j ≫ desc φ = φ j :=
  Cofan.IsColimit.fac (ιIsColimit J c) _ _

@[simp, reassoc]
lemma desc_map {J J' : Type w} {c c' : C} (φ : J → (c ⟶ c')) (f : J' ⟶ J) :
    desc (φ ∘ f) = f ⊵ₗ c ≫ desc φ := by
  aesop_cat

@[simp, reassoc]
lemma desc_postcompose {J : Type w} {c c' c'' : C} (φ : J → (c ⟶ c')) (f : c' ⟶ c'') :
    desc ((· ≫ f) ∘ φ) = desc φ ≫ f := by
  aesop_cat

/-- An abstract isomorphism with the abstract J-indexed coproduct of copies of `c`. -/
noncomputable def isoSigmaConst [HasCoproducts.{w} C] (J : Type w) (c : C) :
    (J ⊙ₗ c) ≅ (sigmaConst.obj c).obj J :=
  (ιIsColimit J c).coconePointUniqueUpToIso (coproductIsCoproduct _)

section
variable [HasCoproducts.{w} C] {J : Type w} (c : C)

@[reassoc (attr := simp)]
lemma ι_comp_isoSigmaConst_hom (j : J) :
    ι c j ≫ (isoSigmaConst J c).hom = Sigma.ι (fun _ ↦ c) j :=
  (ιIsColimit J c).comp_coconePointUniqueUpToIso_hom _ _

@[reassoc (attr := simp)]
lemma ι_comp_isoSigmaConst_inv (j : J) :
    Sigma.ι (fun _ ↦ c) j ≫ (isoSigmaConst J c).inv = ι c j :=
  (ιIsColimit J c).comp_coconePointUniqueUpToIso_inv _ _

end

end

section

/-- Construct a `ChosenTypeCopowers` from the assumption that
coproducts of relevant sizes exist. -/
noncomputable def monoidalLeftActionOfHasCoproducts [HasCoproducts.{w} C] :
    letI := typeLeftActionOfHasCoproducts C
    ChosenTypeCopowers.{w} C :=
  letI := typeLeftActionOfHasCoproducts C
  { ι c j := Sigma.ι (fun _ ↦ c) j
    ι_naturality_left := by
      simp [typeLeftActionOfHasCoproducts]
    ι_naturality_right := by
      simp [typeLeftActionOfHasCoproducts]
    ιIsColimit J c := coproductIsCoproduct _ }

end

end ChosenTypeCopowers

end

end CategoryTheory.MonoidalCategory
