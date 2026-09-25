/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Ring.PUnit
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Tactic.ApplyFun

/-!
# `Action V G`, the category of actions of a monoid `G` inside some category `V`.

The prototypical example is `V = ModuleCat R`,
where `Action (ModuleCat R) G` is the category of `R`-linear representations of `G`.

We check `Action V G ≌ (CategoryTheory.SingleObj G ⥤ V)`,
and construct the restriction functors
`res {G H} [Monoid G] [Monoid H] (f : G →* H) : Action V H ⥤ Action V G`.
-/

@[expose] public section


universe u v

open CategoryTheory Limits

variable (V : Type*) [Category* V]

-- Note: this is _not_ a categorical action of `G` on `V`.
/-- An `Action V G` represents a bundled action of
the monoid `G` on an object of some category `V`.

As an example, when `V = ModuleCat R`, this is an `R`-linear representation of `G`,
while when `V = Type` this is a `G`-action.
-/
structure Action (G : Type*) [Monoid G] where
  /-- The object this action acts on -/
  V : V
  /-- The underlying monoid homomorphism of this action -/
  ρ : G →* End V

namespace Action

variable {V}

theorem ρ_one {G : Type*} [Monoid G] (A : Action V G) : A.ρ 1 = 𝟙 A.V := by simp

/-- When a group acts, we can lift the action to the group of automorphisms. -/
@[simps]
def ρAut {G : Type*} [Group G] (A : Action V G) : G →* Aut A.V where
  toFun g :=
    { hom := A.ρ g
      inv := A.ρ (g⁻¹ : G)
      hom_inv_id := (A.ρ.map_mul (g⁻¹ : G) g).symm.trans (by rw [inv_mul_cancel, ρ_one])
      inv_hom_id := (A.ρ.map_mul g (g⁻¹ : G)).symm.trans (by rw [mul_inv_cancel, ρ_one]) }
  map_one' := Aut.ext A.ρ.map_one
  map_mul' x y := Aut.ext (A.ρ.map_mul x y)

variable (G : Type*) [Monoid G]

section

/-- The action defined by sending every monoid element to the identity. -/
@[simps]
def trivial (X : V) : Action V G := { V := X, ρ := 1 }

instance inhabited' : Inhabited (Action (Type*) G) :=
  ⟨⟨PUnit, 1⟩⟩

instance : Inhabited (Action AddCommGrpCat G) :=
  ⟨trivial G <| AddCommGrpCat.of PUnit⟩

end

variable {G}

/-- A homomorphism of `Action V G`s is a morphism between the underlying objects,
commuting with the action of `G`.
-/
@[ext]
structure Hom (M N : Action V G) where
  /-- The morphism between the underlying objects of this action -/
  hom : M.V ⟶ N.V
  comm : ∀ g : G, M.ρ g ≫ hom = hom ≫ N.ρ g := by cat_disch

namespace Hom

attribute [reassoc] comm
attribute [local simp] comm comm_assoc

/-- The identity morphism on an `Action V G`. -/
@[simps]
def id (M : Action V G) : Action.Hom M M where hom := 𝟙 M.V

instance (M : Action V G) : Inhabited (Action.Hom M M) :=
  ⟨id M⟩

/-- The composition of two `Action V G` homomorphisms is the composition of the underlying maps.
-/
@[simps]
def comp {M N K : Action V G} (p : Action.Hom M N) (q : Action.Hom N K) : Action.Hom M K where
  hom := p.hom ≫ q.hom

end Hom

instance : Category (Action V G) where
  Hom M N := Hom M N
  id M := Hom.id M
  comp f g := Hom.comp f g

lemma hom_injective {M N : Action V G} : Function.Injective (Hom.hom : (M ⟶ N) → (M.V ⟶ N.V)) :=
  fun _ _ ↦ Hom.ext

@[ext]
lemma hom_ext {M N : Action V G} (φ₁ φ₂ : M ⟶ N) (h : φ₁.hom = φ₂.hom) : φ₁ = φ₂ :=
  Hom.ext h

@[simp]
theorem id_hom (M : Action V G) : (𝟙 M : Hom M M).hom = 𝟙 M.V :=
  rfl

@[simp, reassoc]
theorem comp_hom {M N K : Action V G} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).hom = f.hom ≫ g.hom :=
  rfl

@[reassoc (attr := simp)]
theorem hom_inv_hom {M N : Action V G} (f : M ≅ N) :
    f.hom.hom ≫ f.inv.hom = 𝟙 M.V := by
  rw [← comp_hom, Iso.hom_inv_id, id_hom]

@[reassoc (attr := simp)]
theorem inv_hom_hom {M N : Action V G} (f : M ≅ N) :
    f.inv.hom ≫ f.hom.hom = 𝟙 N.V := by
  rw [← comp_hom, Iso.inv_hom_id, id_hom]

/-- Construct an isomorphism of `G` actions/representations
from an isomorphism of the underlying objects,
where the forward direction commutes with the group action. -/
@[simps]
def mkIso {M N : Action V G} (f : M.V ≅ N.V)
    (comm : ∀ g : G, M.ρ g ≫ f.hom = f.hom ≫ N.ρ g := by cat_disch) : M ≅ N where
  hom :=
    { hom := f.hom
      comm := comm }
  inv :=
    { hom := f.inv
      comm := fun g => by have w := comm g =≫ f.inv; simp at w; simp [w] }

instance (priority := 100) isIso_of_hom_isIso {M N : Action V G} (f : M ⟶ N) [IsIso f.hom] :
    IsIso f := (mkIso (asIso f.hom) f.comm).isIso_hom

instance isIso_hom_mk {M N : Action V G} (f : M.V ⟶ N.V) [IsIso f] (w) :
    @IsIso _ _ M N (Hom.mk f w) :=
  (mkIso (asIso f) w).isIso_hom

instance {M N : Action V G} (f : M ≅ N) : IsIso f.hom.hom where
  out := ⟨f.inv.hom, by simp⟩

instance {M N : Action V G} (f : M ≅ N) : IsIso f.inv.hom where
  out := ⟨f.hom.hom, by simp⟩

namespace FunctorCategoryEquivalence

/-- Auxiliary definition for `functorCategoryEquivalence`. -/
@[simps]
def functor : Action V G ⥤ SingleObj G ⥤ V where
  obj M :=
    { obj := fun _ => M.V
      map := fun g => M.ρ g
      map_id := fun _ => M.ρ.map_one
      map_comp := fun g h => M.ρ.map_mul h g }
  map f :=
    { app := fun _ => f.hom
      naturality := fun _ _ g => f.comm g }

/-- Auxiliary definition for `functorCategoryEquivalence`. -/
@[simps]
def inverse : (SingleObj G ⥤ V) ⥤ Action V G where
  obj F :=
    { V := F.obj PUnit.unit
      ρ :=
        { toFun := fun g => F.map g
          map_one' := F.map_id PUnit.unit
          map_mul' := fun g h => F.map_comp h g } }
  map f :=
    { hom := f.app PUnit.unit
      comm := fun g => f.naturality g }

/-- Auxiliary definition for `functorCategoryEquivalence`. -/
@[simps!]
def unitIso : 𝟭 (Action V G) ≅ functor ⋙ inverse :=
  NatIso.ofComponents fun M => mkIso (Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `functorCategoryEquivalence`. -/
@[simps!]
def counitIso : inverse ⋙ functor ≅ 𝟭 (SingleObj G ⥤ V) :=
  NatIso.ofComponents fun M => NatIso.ofComponents fun _ => Iso.refl _

end FunctorCategoryEquivalence

section

open FunctorCategoryEquivalence

variable (V G)

/-- The category of actions of `G` in the category `V`
is equivalent to the functor category `SingleObj G ⥤ V`.
-/
@[simps]
def functorCategoryEquivalence : Action V G ≌ SingleObj G ⥤ V where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

instance : (FunctorCategoryEquivalence.functor (V := V) (G := G)).IsEquivalence :=
  (functorCategoryEquivalence V G).isEquivalence_functor

instance : (FunctorCategoryEquivalence.inverse (V := V) (G := G)).IsEquivalence :=
  (functorCategoryEquivalence V G).isEquivalence_inverse

end

section Forget

variable (V G)

/-- (implementation) The forgetful functor from bundled actions to the underlying objects.

Use the `CategoryTheory.forget` API provided by the `ConcreteCategory` instance below,
rather than using this directly.
-/
@[simps]
def forget : Action V G ⥤ V where
  obj M := M.V
  map f := f.hom

instance : (forget V G).Faithful where map_injective w := Hom.ext w

/-- The type of `V`-morphisms that can be lifted back to morphisms in the category `Action`. -/
abbrev HomSubtype {FV : V → V → Type*} {CV : V → Type*} [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)]
    [ConcreteCategory V FV] (M N : Action V G) :=
  { f : FV M.V N.V // ∀ g : G,
      f ∘ ConcreteCategory.hom (M.ρ g) = ConcreteCategory.hom (N.ρ g) ∘ f }

instance {FV : V → V → Type*} {CV : V → Type*} [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)]
    [ConcreteCategory V FV] (M N : Action V G) :
    FunLike (HomSubtype V G M N) (CV M.V) (CV N.V) where
  coe f := f.1
  coe_injective' _ _ h := Subtype.ext (DFunLike.coe_injective h)

instance {FV : V → V → Type*} {CV : V → Type*} [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)]
    [ConcreteCategory V FV] : ConcreteCategory (Action V G) (HomSubtype V G) where
  hom f := ⟨ConcreteCategory.hom (C := V) f.1, fun g => by
    ext
    simpa using CategoryTheory.congr_fun (f.2 g) _⟩
  ofHom f := ⟨ConcreteCategory.ofHom (C := V) f, fun g => ConcreteCategory.ext_apply fun x => by
    simpa [ConcreteCategory.hom_ofHom] using congr_fun (f.2 g) x⟩
  hom_ofHom _ := by dsimp; ext; simp [ConcreteCategory.hom_ofHom]
  ofHom_hom _ := by ext; simp [ConcreteCategory.ofHom_hom]
  id_apply := ConcreteCategory.id_apply (C := V)
  comp_apply _ _ := ConcreteCategory.comp_apply (C := V) _ _

instance hasForgetToV {FV : V → V → Type*} {CV : V → Type*} [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)]
    [ConcreteCategory V FV] : HasForget₂ (Action V G) V where forget₂ := forget V G

/-- The forgetful functor is intertwined by `functorCategoryEquivalence` with
evaluation at `PUnit.star`. -/
def functorCategoryEquivalenceCompEvaluation :
    (functorCategoryEquivalence V G).functor ⋙ (evaluation _ _).obj PUnit.unit ≅ forget V G :=
  Iso.refl _

noncomputable instance preservesLimits_forget [HasLimits V] :
    PreservesLimits (forget V G) :=
  Limits.preservesLimits_of_natIso (Action.functorCategoryEquivalenceCompEvaluation V G)

noncomputable instance preservesColimits_forget [HasColimits V] :
    PreservesColimits (forget V G) :=
  preservesColimits_of_natIso (Action.functorCategoryEquivalenceCompEvaluation V G)

-- TODO construct categorical images?
end Forget

set_option backward.isDefEq.respectTransparency false in
theorem Iso.conj_ρ {M N : Action V G} (f : M ≅ N) (g : G) :
    N.ρ g = ((forget V G).mapIso f).conj (M.ρ g) := by
      rw [Iso.conj_apply, Iso.eq_inv_comp]; simp [f.hom.comm]

set_option backward.isDefEq.respectTransparency false in
/-- Actions/representations of the trivial monoid are just objects in the ambient category. -/
def actionPUnitEquivalence : Action V PUnit ≌ V where
  functor := forget V _
  inverse :=
    { obj := fun X => ⟨X, 1⟩
      map := fun f => ⟨f, fun ⟨⟩ => by simp⟩ }
  unitIso :=
    NatIso.ofComponents fun X => mkIso (Iso.refl _) fun ⟨⟩ => by
      simp only [Functor.id_obj, MonoidHom.one_apply, End.one_def, Functor.comp_obj,
        forget_obj, Iso.refl_hom, Category.comp_id]
      exact ρ_one X
  counitIso := NatIso.ofComponents fun _ => Iso.refl _

@[deprecated (since := "2026-02-08")] alias actionPunitEquivalence := actionPUnitEquivalence

variable (V)

/-- The "restriction" functor along a monoid homomorphism `f : G →* H`,
taking actions of `H` to actions of `G`.

(This makes sense for any homomorphism, but the name is natural when `f` is a monomorphism.)
-/
@[simps]
def res {G H : Type*} [Monoid G] [Monoid H] (f : G →* H) : Action V H ⥤ Action V G where
  obj M :=
    { V := M.V
      ρ := M.ρ.comp f }
  map p :=
    { hom := p.hom
      comm := fun g => p.comm (f g) }

/-- The natural isomorphism from restriction along the identity homomorphism to
the identity functor on `Action V G`.
-/
@[simps!]
def resId {G : Type*} [Monoid G] : res V (MonoidHom.id G) ≅ 𝟭 (Action V G) :=
  NatIso.ofComponents fun M => mkIso (Iso.refl _)

/-- The natural isomorphism from the composition of restrictions along homomorphisms
to the restriction along the composition of homomorphism.
-/
@[simps!]
def resComp {G H K : Type*} [Monoid G] [Monoid H] [Monoid K]
    (f : G →* H) (g : H →* K) : res V g ⋙ res V f ≅ res V (g.comp f) :=
  NatIso.ofComponents fun M => mkIso (Iso.refl _)

/-- Restricting scalars along equal maps is naturally isomorphic. -/
@[simps! hom inv]
def resCongr {G H : Type*} [Monoid G] [Monoid H] {f f' : G →* H} (h : f = f') :
    Action.res V f ≅ Action.res V f' :=
  NatIso.ofComponents (fun _ ↦ Action.mkIso (Iso.refl _))

/-- Restricting scalars along a monoid isomorphism induces an equivalence of categories. -/
@[simps! functor inverse]
def resEquiv {G H : Type*} [Monoid G] [Monoid H] (f : G ≃* H) :
    Action V H ≌ Action V G where
  functor := Action.res _ f
  inverse := Action.res _ f.symm
  unitIso := Action.resCongr (f := MonoidHom.id H) V (by ext; simp) ≪≫ (Action.resComp _ _ _).symm
  counitIso := Action.resComp _ _ _ ≪≫
    Action.resCongr (f' := MonoidHom.id G) V (by ext; simp)

-- TODO promote `res` to a pseudofunctor from
-- the locally discrete bicategory constructed from `Monᵒᵖ` to `Cat`, sending `G` to `Action V G`.

variable {G H : Type*} [Monoid G] [Monoid H] (f : G →* H)

/-- The functor from `Action V H` to `Action V G` induced by a monoid homomorphism
`f : G →* H` is faithful. -/
instance : (res V f).Faithful where
  map_injective {X} {Y} g₁ g₂ h := by
    ext
    rw [← res_map_hom _ f g₁, ← res_map_hom _ f g₂, h]

set_option backward.isDefEq.respectTransparency false in
/-- The functor from `Action V H` to `Action V G` induced by a monoid homomorphism
`f : G →* H` is full if `f` is surjective. -/
lemma full_res (f_surj : Function.Surjective f) : (res V f).Full where
  map_surjective {X} {Y} g := by
    use ⟨g.hom, fun h ↦ ?_⟩
    · ext
      simp
    · obtain ⟨a, rfl⟩ := f_surj h
      have : X.ρ (f a) = ((res V f).obj X).ρ a := rfl
      rw [this, g.comm a]
      simp

end Action

namespace CategoryTheory.Functor

variable {V} {W : Type*} [Category* W]

/-- A functor between categories induces a functor between
the categories of `G`-actions within those categories. -/
@[simps]
def mapAction (F : V ⥤ W) (G : Type*) [Monoid G] : Action V G ⥤ Action W G where
  obj M :=
    { V := F.obj M.V
      ρ :=
        { toFun := fun g => F.map (M.ρ g)
          map_one' := by simp
          map_mul' := fun g h => by
            dsimp
            rw [map_mul, End.mul_def, F.map_comp] } }
  map f :=
    { hom := F.map f.hom
      comm := fun g => by dsimp; rw [← F.map_comp, f.comm, F.map_comp] }
  map_id M := by ext; simp only [Action.id_hom, F.map_id]
  map_comp f g := by ext; simp only [Action.comp_hom, F.map_comp]

instance (F : V ⥤ W) (G : Type*) [Monoid G] [F.Faithful] : (F.mapAction G).Faithful where
  map_injective eq := by
    ext
    apply_fun (fun f ↦ f.hom) at eq
    exact F.map_injective eq

/--
A fully faithful functor between categories induces a fully faithful functor between
the categories of `G`-actions within those categories. -/
def FullyFaithful.mapAction {F : V ⥤ W} (h : F.FullyFaithful) (G : Type*) [Monoid G] :
    (F.mapAction G).FullyFaithful where
  preimage f := by
    refine ⟨h.preimage f.hom, fun _ ↦ h.map_injective ?_⟩
    simp only [map_comp, map_preimage]
    exact f.comm _

instance (F : V ⥤ W) (G : Type*) [Monoid G] [F.Faithful] [F.Full] : (F.mapAction G).Full :=
  ((Functor.FullyFaithful.ofFullyFaithful F).mapAction G).full

variable (G : Type*) [Monoid G]

/-- `Functor.mapAction` is functorial in the functor. -/
@[simps! hom inv]
def mapActionComp {T : Type*} [Category* T] (F : V ⥤ W) (F' : W ⥤ T) :
    (F ⋙ F').mapAction G ≅ F.mapAction G ⋙ F'.mapAction G :=
  NatIso.ofComponents (fun X ↦ Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
/-- `Functor.mapAction` preserves isomorphisms of functors. -/
@[simps! hom inv]
def mapActionCongr {F F' : V ⥤ W} (e : F ≅ F') :
    F.mapAction G ≅ F'.mapAction G :=
  NatIso.ofComponents (fun X ↦ Action.mkIso (e.app X.V))

end Functor

/-- An equivalence of categories induces an equivalence of
the categories of `G`-actions within those categories. -/
@[simps functor inverse]
def Equivalence.mapAction {V W : Type*} [Category* V] [Category* W] (G : Type*) [Monoid G]
    (E : V ≌ W) : Action V G ≌ Action W G where
  functor := E.functor.mapAction G
  inverse := E.inverse.mapAction G
  unitIso := Functor.mapActionCongr G E.unitIso ≪≫ Functor.mapActionComp G _ _
  counitIso := (Functor.mapActionComp G _ _).symm ≪≫ Functor.mapActionCongr G E.counitIso
  functor_unitIso_comp X := by ext; simp

end CategoryTheory
