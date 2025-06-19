/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!

# Topological subcategories of `Action V G`

For a concrete category `V`, where the forgetful functor factors via `TopCat`,
and a monoid `G`, equipped with a topological space instance,
we define the full subcategory `ContAction V G` of all objects of `Action V G`
where the induced action is continuous.

We also define a category `DiscreteContAction V G` as the full subcategory of `ContAction V G`,
where the underlying topological space is discrete.

Finally we define inclusion functors into `Action V G` and `TopCat` in terms
of `HasForget₂` instances.

-/

open CategoryTheory Limits

variable (V : Type*) [Category V] [HasForget V] [HasForget₂ V TopCat]
variable (G : Type*) [Monoid G] [TopologicalSpace G]

namespace Action

instance : HasForget₂ (Action V G) TopCat :=
  HasForget₂.trans (Action V G) V TopCat

instance (X : Action V G) : MulAction G ((CategoryTheory.forget₂ _ TopCat).obj X) where
  smul g x := ((CategoryTheory.forget₂ _ TopCat).map (X.ρ g)) x
  one_smul x := by
    show ((CategoryTheory.forget₂ _ TopCat).map (X.ρ 1)) x = x
    simp
  mul_smul g h x := by
    show (CategoryTheory.forget₂ _ TopCat).map (X.ρ (g * h)) x =
      ((CategoryTheory.forget₂ _ TopCat).map (X.ρ h) ≫
        (CategoryTheory.forget₂ _ TopCat).map (X.ρ g)) x
    rw [← Functor.map_comp, map_mul]
    rfl

variable {V G}

/-- For `HasForget₂ V TopCat` a predicate on an `X : Action V G` saying that the induced action on
the underlying topological space is continuous. -/
abbrev IsContinuous (X : Action V G) : Prop :=
  ContinuousSMul G ((CategoryTheory.forget₂ _ TopCat).obj X)

lemma isContinuous_def (X : Action V G) :
    X.IsContinuous ↔ Continuous (fun p : G × (forget₂ _ TopCat).obj X ↦
      (forget₂ _ TopCat).map (X.ρ p.1) p.2) :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

end Action

open Action

/-- For `HasForget₂ V TopCat`, this is the full subcategory of `Action V G` where the induced
action is continuous. -/
def ContAction : Type _ := ObjectProperty.FullSubcategory (IsContinuous (V := V) (G := G))

namespace ContAction

instance : Category (ContAction V G) :=
  ObjectProperty.FullSubcategory.category (IsContinuous (V := V) (G := G))

instance : HasForget (ContAction V G) :=
  FullSubcategory.hasForget (IsContinuous (V := V) (G := G))

instance {FV : V → V → Type*} {CV : V → Type*} [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)]
    [ConcreteCategory V FV] :
    ConcreteCategory (ContAction V G) (fun X Y => Action.HomSubtype V G X.1 Y.1) :=
  FullSubcategory.concreteCategory (IsContinuous (V := V) (G := G))

instance : HasForget₂ (ContAction V G) (Action V G) :=
  FullSubcategory.hasForget₂ (IsContinuous (V := V) (G := G))

instance : HasForget₂ (ContAction V G) V :=
  HasForget₂.trans (ContAction V G) (Action V G) V

instance : HasForget₂ (ContAction V G) TopCat :=
  HasForget₂.trans (ContAction V G) (Action V G) TopCat

instance : Coe (ContAction V G) (Action V G) where
  coe X := X.obj

variable {V G}

/-- A predicate on an `X : ContAction V G` saying that the topology on the underlying type of `X`
is discrete. -/
abbrev IsDiscrete (X : ContAction V G) : Prop :=
  DiscreteTopology ((CategoryTheory.forget₂ _ TopCat).obj X)

variable (V) {H : Type*} [Monoid H] [TopologicalSpace H]

/-- The "restriction" functor along a monoid homomorphism `f : G →* H`,
taking actions of `H` to actions of `G`. This is the analogue of
`Action.res` in the continuous setting. -/
@[simps! obj_obj map]
def res (f : G →ₜ* H) : ContAction V H ⥤ ContAction V G :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Action.res _ f) fun X ↦ by
    constructor
    let v : G × (forget₂ _ TopCat).obj X → H × (forget₂ _ TopCat).obj X := fun p ↦ (f p.1, p.2)
    have : Continuous v := by fun_prop
    let u : H × (forget₂ _ TopCat).obj X → (forget₂ _ TopCat).obj X :=
      fun p ↦ (forget₂ _ TopCat).map (X.obj.ρ p.1) p.2
    have : Continuous u := X.2.1
    show Continuous (u ∘ v)
    fun_prop

/-- Restricting scalars along a composition is naturally isomorphic to restricting scalars twice. -/
@[simps! hom inv]
def resComp {K : Type*} [Monoid K] [TopologicalSpace K]
    (f : G →ₜ* H) (h : H →ₜ* K) :
    ContAction.res V (h.comp f) ≅ ContAction.res V h ⋙ ContAction.res V f :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- If `f = f'`, restriction of scalars along `f` and `f'` is the same. -/
@[simps! hom inv]
def resCongr (f f' : G →ₜ* H) (h : f = f') : ContAction.res V f ≅ ContAction.res V f' :=
  NatIso.ofComponents (fun _ ↦ ObjectProperty.isoMk _ (Action.mkIso (Iso.refl _)
    (by subst h; simp))) fun f ↦ by
      apply Action.Hom.ext
      rw [ObjectProperty.FullSubcategory.comp_def, ObjectProperty.FullSubcategory.comp_def]
      simp

/-- Restriction of scalars along a topological monoid isomorphism induces an equivalence of
categories. -/
@[simps! functor inverse]
def resEquiv (f : G ≃ₜ* H) : ContAction V H ≌ ContAction V G where
  functor := res _ f
  inverse := res _ f.symm
  unitIso := resCongr V (ContinuousMonoidHom.id H) _ (by ext; simp) ≪≫
    ContAction.resComp _ _ _
  counitIso := (ContAction.resComp _ _ _).symm ≪≫
    ContAction.resCongr V _ (ContinuousMonoidHom.id G) (by ext; simp)
  functor_unitIso_comp X := (Action.resEquiv V f.toMulEquiv).functor_unitIso_comp X.obj

end ContAction

open ContAction

/-- The subcategory of `ContAction V G` where the topology is discrete. -/
def DiscreteContAction : Type _ := ObjectProperty.FullSubcategory (IsDiscrete (V := V) (G := G))

namespace DiscreteContAction

instance : Category (DiscreteContAction V G) :=
  ObjectProperty.FullSubcategory.category (IsDiscrete (V := V) (G := G))

instance : HasForget (DiscreteContAction V G) :=
  FullSubcategory.hasForget (IsDiscrete (V := V) (G := G))

instance {FV : V → V → Type*} {CV : V → Type*} [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)]
    [ConcreteCategory V FV] :
    ConcreteCategory (DiscreteContAction V G) (fun X Y => Action.HomSubtype V G X.1 Y.1) :=
  FullSubcategory.concreteCategory (IsDiscrete (V := V) (G := G))

instance : HasForget₂ (DiscreteContAction V G) (ContAction V G) :=
  FullSubcategory.hasForget₂ (IsDiscrete (V := V) (G := G))

instance : HasForget₂ (DiscreteContAction V G) TopCat :=
  HasForget₂.trans (DiscreteContAction V G) (ContAction V G) TopCat

variable {V G}

instance (X : DiscreteContAction V G) :
    DiscreteTopology ((CategoryTheory.forget₂ _ TopCat).obj X) :=
  X.property

end DiscreteContAction

namespace CategoryTheory

variable {V W : Type*} [Category V] [HasForget V] [HasForget₂ V TopCat]
  [Category W] [HasForget W] [HasForget₂ W TopCat]
  (G : Type*) [Monoid G] [TopologicalSpace G]

namespace Functor

/-- Continuous version of `Functor.mapAction`. -/
@[simps! obj_obj map]
def mapContAction (F : V ⥤ W) (H : ∀ X : ContAction V G, ((F.mapAction G).obj X.obj).IsContinuous) :
    ContAction V G ⥤ ContAction W G :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ F.mapAction G) H

/-- Continuous version of `Functor.mapActionComp`. -/
@[simps! hom inv]
def mapContActionComp {T : Type*} [Category T] [HasForget T] [HasForget₂ T TopCat]
    (F : V ⥤ W) (H : ∀ X : ContAction V G, ((F.mapAction G).obj X.obj).IsContinuous)
    (F' : W ⥤ T) (H' : ∀ X : ContAction W G, ((F'.mapAction G).obj X.obj).IsContinuous) :
    Functor.mapContAction G (F ⋙ F') (fun X ↦ H' ((F.mapContAction G H).obj X)) ≅
      Functor.mapContAction G F H ⋙ Functor.mapContAction G F' H' :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- Continuous version of `Functor.mapActionCongr`. -/
@[simps! hom inv]
def mapContActionCongr
    {F : V ⥤ W} {F' : V ⥤ W} (e : F ≅ F')
    (H : ∀ X : ContAction V G, ((F.mapAction G).obj X.obj).IsContinuous)
    (H' : ∀ X : ContAction V G, ((F'.mapAction G).obj X.obj).IsContinuous) :
    Functor.mapContAction G F H ≅ Functor.mapContAction G F' H' :=
  NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _ (Action.mkIso (e.app X.obj.V) (by simp))) <|
    (fun f ↦ (Functor.mapActionCongr G e).hom.naturality f)

end Functor

/-- Continuous version of `Equivalence.mapAction`. -/
@[simps functor inverse]
def Equivalence.mapContAction (E : V ≌ W)
    (H₁ : ∀ X : ContAction V G, ((E.functor.mapAction G).obj X.obj).IsContinuous)
    (H₂ : ∀ X : ContAction W G, ((E.inverse.mapAction G).obj X.obj).IsContinuous) :
    ContAction V G ≌ ContAction W G where
  functor := E.functor.mapContAction G H₁
  inverse := E.inverse.mapContAction G H₂
  unitIso := Functor.mapContActionCongr G E.unitIso
      (fun X ↦ X.2) (fun X ↦ H₂ ((E.functor.mapContAction G H₁).obj X))  ≪≫
    Functor.mapContActionComp G _ _ _ _
  counitIso := (Functor.mapContActionComp G _ _ _ _).symm ≪≫
    Functor.mapContActionCongr G E.counitIso _ (fun X ↦ X.2)
  functor_unitIso_comp X := (E.mapAction G).functor_unitIso_comp X.obj

end CategoryTheory
