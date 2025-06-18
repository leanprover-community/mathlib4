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

## TODOs

* More interestingly, we should show that if a w-small monoidal category
`C` acts on a `w`-cocomplete category `D`,
then `Cᵒᵖ ⥤ Type w` (with Day convolution monoidal structure) act on the
left on `D`.
* A coproduct-preserving functor is left linear for these structures
* A product-preserving functor is right linear for these structures

-/

universe w v u

namespace CategoryTheory.MonoidalCategory

variable (C : Type u) [Category.{v} C]
open Limits

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

@[simps -isSimp]
noncomputable instance typeAction : MonoidalLeftAction (Type w) C where
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

namespace typeAction
open scoped MonoidalLeftAction

/-- The canonical map `c ⟶ J ⊙ₗ c` corresponding to `j : J`.
If we are to think of `J ⊙ₗ c` as a `J`-indexed coproduct of copies of `c`, this is the
inclusion at the component corresponding to `j`. This is proved in `ι_eq_ι`, but this
definition should be the one that is used when working with the left action
of types on `C`. -/
noncomputable def ι {J : Type w} (c : C) (j : J) : c ⟶ J ⊙ₗ c := (λₗ c).inv ≫ (fun _ ↦ j) ⊵ₗ c

-- not simp to keep API leakage minimal.
lemma ι_eq_ι {J : Type w} (j : J) (c : C) :
    ι c j = Sigma.ι (fun _ ↦ c) j := by
  simp [ι, MonoidalLeftAction.actionObj, MonoidalLeftAction.actionHomLeft,
    MonoidalLeftAction.actionUnitIso]

@[ext]
lemma hom_ext {J : Type w} {c c' : C} {f g : J ⊙ₗ c ⟶ c'} (h : ∀ j, ι c j ≫ f = ι c j ≫ g) :
    f = g :=
  Sigma.hom_ext _ _ (fun j ↦ by simpa [ι_eq_ι] using h j)

@[reassoc (attr := simp)]
lemma ι_nat {J J' : Type w} (f : J ⟶ J') (c : C) (j : J) : ι c j ≫ f ⊵ₗ c = ι c (f j) := by
  simp [ι, MonoidalLeftAction.actionObj, MonoidalLeftAction.actionHomLeft,
  MonoidalLeftAction.actionUnitIso]

@[simp]
lemma ι_unit (c : C) : ι c (.unit : 𝟙_ (Type w)) = (λₗ c).inv := by
  dsimp [ι]
  rw [Iso.inv_comp_eq]
  change 𝟙 _ ⊵ₗ c = _
  simp

/-- Construct a morphism `J ⊙ₗ c ⟶ c'` from a familiy of maps `c ⟶ c' -/
noncomputable def desc {J : Type w} {c c' : C} (φ : J → (c ⟶ c')) : J ⊙ₗ c ⟶ c' := 
    Sigma.desc φ

@[reassoc (attr := simp)]
lemma ι_desc {J : Type w} {c c' : C} (φ : J → (c ⟶ c')) (j : J) :
   ι c j ≫ desc φ = φ j := by 
  simp[desc, ι_eq_ι]

@[reassoc (attr := simp)]
lemma desc_map {J J' : Type w} {c c' : C} (φ : J → (c ⟶ c')) (f : J' ⟶ J) :
    desc (φ ∘ f) = f ⊵ₗ c ≫ desc φ := by 
  aesop_cat

end typeAction

end

end CategoryTheory.MonoidalCategory
