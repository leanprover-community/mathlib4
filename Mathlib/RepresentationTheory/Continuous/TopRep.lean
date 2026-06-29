/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Richard Hill
-/
module

public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Algebra.Homology.Functor

/-!
# Topological representations

This file defines the category `TopRep k G` of topological representations of a monoid `G` over a
topological ring `k`, and shows that it is equivalent to the category `Action (TopModuleCat k) G`.
-/

@[expose] public section

universe w u v

/-- The category of topological representations of a monoid `G` over a topological ring `k`, and
their morphisms. -/
structure TopRep (k : Type u) (G : Type v) [TopologicalSpace k] [Ring k]
    [IsTopologicalRing k] [Monoid G] where
  private mk ::
  /-- the underlying type of an object in `TopRep k G` -/
  V : Type w
  [hV1 : AddCommGroup V]
  [hV2 : Module k V]
  [hV3 : TopologicalSpace V]
  [hV4 : IsTopologicalAddGroup V]
  [hV5 : ContinuousSMul k V]
  /-- the underlying continuous representation of an object in `TopRep k G` -/
  ρ : ContRepresentation k G V

namespace TopRep

variable {k : Type u} {G : Type v} {X Y : Type w} [TopologicalSpace k] [Ring k]
  [IsTopologicalRing k] [Monoid G] [AddCommGroup X] [Module k X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul k X] [AddCommGroup Y] [Module k Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul k Y] {ρ : ContRepresentation k G X}
  {σ : ContRepresentation k G Y}

open ContRepresentation CategoryTheory

attribute [instance] hV1 hV2 hV3 hV4 hV5

initialize_simps_projections TopRep (-hV1, -hV2)

instance : CoeSort (TopRep k G) (Type w) := ⟨TopRep.V⟩

attribute [coe] V

variable (ρ) in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The object in the category of topological representations associated to a type equipped with a
continuous representation. This is the preferred way to construct a term of `TopRep k G`. -/
abbrev of : TopRep k G := ⟨X, ρ⟩

variable (X ρ) in
lemma of_V : (of ρ).V = X := by with_reducible rfl

variable (X ρ) in
lemma of_ρ : (of ρ).ρ = ρ := by with_reducible rfl

set_option backward.privateInPublic true in
/-- The type of morphisms in `TopRep k G`. -/
@[ext]
structure Hom (A B : TopRep k G) where
  private mk ::
  /-- The underlying `G`-equivariant linear map. -/
  hom' : A.ρ →ⁱL B.ρ

variable (A B C : TopRep.{w} k G)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Category (TopRep.{w} k G) where
  Hom A B := Hom A B
  id A := ⟨.id (π₁ := A.ρ)⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ConcreteCategory (TopRep.{w} k G) (fun A B ↦ A.ρ →ⁱL B.ρ) where
  hom := Hom.hom'
  ofHom := Hom.mk

variable {A B} in
/-- Turn a morphism in `TopRep` back into an `IntertwiningMap`. -/
abbrev Hom.hom (f : Hom A B) := ConcreteCategory.hom (C := TopRep k G) f

variable {A B} in
/-- Typecheck an `IntertwiningMap` as a morphism in `TopRep`. -/
abbrev ofHom (f : ρ →ⁱL σ) : of ρ ⟶ of σ :=
  ConcreteCategory.ofHom (C := TopRep.{w} k G) f

@[simp] lemma hom_ofHom (f : ρ →ⁱL σ) : (ofHom f).hom = f := rfl

@[simp] lemma ofHom_hom (f : A ⟶ B) : ofHom f.hom = f := rfl

variable {A B} in
/-- The morphism of topological modules underlying a morphism in `TopRep k G`. -/
abbrev Hom.toTopModuleCatHom (f : Hom A B) :
    TopModuleCat.of k A ⟶ TopModuleCat.of k B :=
  TopModuleCat.ofHom f.hom.toContinuousLinearMap

/-
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/
@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = .id (π₁ := A.ρ) := rfl

/- Provided for rewriting. -/
lemma id_apply (a : A) : (𝟙 A : A ⟶ A) a = a := rfl

@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
variable {A B C} in
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := rfl

variable {A B} in
@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g := Hom.ext hf

variable {A B} in
lemma hom_comm_apply (f : A ⟶ B) (g : G) (a : A) : f.hom (A.ρ g a) = B.ρ g (f.hom a) := by
  simpa using! congr($(f.hom.2 g) a)

instance : AddCommGroup (A ⟶ B) := fast_instance% ConcreteCategory.homEquiv.addCommGroup

@[simp] lemma hom_zero : (0 : A ⟶ B).hom = 0 := rfl

lemma hom_add (f g : A ⟶ B) : (f + g).hom = f.hom + g.hom := rfl

lemma hom_sub (f g : A ⟶ B) : (f - g).hom = f.hom - g.hom := rfl

lemma ofHom_add (f g : ρ →ⁱL σ) : ofHom (f + g) = ofHom f + ofHom g := rfl

lemma ofHom_sub (f g : ρ →ⁱL σ) : ofHom (f - g) = ofHom f - ofHom g := rfl

lemma comp_add' (f : A ⟶ B) (g h : B ⟶ C) : f ≫ (g + h) = f ≫ g + f ≫ h := by
  ext : 1; simp [hom_add, ContIntertwiningMap.add_comp]

lemma add_comp' (f g : A ⟶ B) (h : B ⟶ C) : (f + g) ≫ h = f ≫ h + g ≫ h := by
  ext : 1; simp [hom_add, ContIntertwiningMap.comp_add]

instance : Preadditive (TopRep k G) where
  homGroup := inferInstance
  add_comp := TopRep.add_comp'
  comp_add := TopRep.comp_add'

section Linear

variable {k : Type u} {G : Type v} {X Y : Type w} [TopologicalSpace k] [CommRing k]
  [IsTopologicalRing k] [Monoid G] [AddCommGroup X] [Module k X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul k X] [AddCommGroup Y] [Module k Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul k Y] {ρ : ContRepresentation k G X}
  {σ : ContRepresentation k G Y} {A B C : TopRep k G}

instance : Module k (A ⟶ B) := fast_instance% ConcreteCategory.homEquiv.module k

lemma hom_smul (r : k) (f : A ⟶ B) : (r • f).hom = r • f.hom := rfl

lemma ofHom_smul (r : k) (f : ρ →ⁱL σ) : ofHom (r • f) = r • ofHom f := rfl

variable (A B C) in
lemma smul_comp' (r : k) (f : A ⟶ B) (g : B ⟶ C) : (r • f) ≫ g = r • (f ≫ g) := by
  ext; simp [hom_smul, ContIntertwiningMap.comp_smul]

variable (A B C) in
lemma comp_smul' (f : A ⟶ B) (r : k) (g : B ⟶ C) : f ≫ (r • g) = r • (f ≫ g) := by
  ext; simp [hom_smul, ContIntertwiningMap.smul_comp]

instance : CategoryTheory.Linear k (TopRep k G) where
  homModule := inferInstance
  smul_comp := smul_comp'
  comp_smul := comp_smul'

end Linear

section equivAction

/-- The functor sending a topological representation to the corresponding object in
`Action (TopModuleCat k) G`. -/
def toActionTopModFunc : TopRep k G ⥤ Action (TopModuleCat k) G where
  obj X := ⟨.of k X.V, (TopModuleCat.endRingEquiv (.of k X.V)).symm.toMonoidHom.comp X.ρ⟩
  map f := ⟨f.toTopModuleCatHom, fun g => by ext1; simp [TopModuleCat.endRingEquiv, f.hom.2 g]⟩

/-- The functor sending an object in `Action (TopModuleCat k) G` to the corresponding topological
representation. -/
def fromActionTopModFunc : Action (TopModuleCat.{w} k) G ⥤ TopRep k G where
  obj X := .of <| (TopModuleCat.endRingEquiv X.V).toMonoidHom.comp X.ρ
  map {X Y} f := ofHom ⟨f.hom.hom, fun g ↦ by simpa using congr(TopModuleCat.Hom.hom $(f.comm g))⟩

/-- The unit isomorphism of the equivalence `TopRepIsoActionTop`. -/
def toActionFromAction (X : TopRep.{w} k G) :
    fromActionTopModFunc.obj (toActionTopModFunc.obj X) ≅ X where
  hom := ofHom ⟨ContinuousLinearMap.id k X.V, fun _ ↦ rfl⟩
  inv := ofHom ⟨ContinuousLinearMap.id k X.V, fun _ ↦ rfl⟩

/-- The counit isomorphism of the equivalence `TopRepIsoActionTop`. -/
def fromActionToAction (X : Action (TopModuleCat.{w} k) G) :
    toActionTopModFunc.obj (fromActionTopModFunc.obj X) ≅ X where
  hom := ⟨𝟙 _, fun _ ↦ rfl⟩
  inv := ⟨𝟙 _, fun _ ↦ rfl⟩

/-- The equivalence of categories between `TopRep k G` and `Action (TopModuleCat k) G`. -/
def TopRepEquivActionTop : TopRep.{w} k G ≌ Action (TopModuleCat.{w} k) G where
  functor := toActionTopModFunc
  inverse := fromActionTopModFunc
  unitIso := NatIso.ofComponents toActionFromAction
  counitIso := NatIso.ofComponents fromActionToAction

instance : (toActionTopModFunc (k := k) (G := G)).IsEquivalence :=
  TopRepEquivActionTop (k := k) (G := G).isEquivalence_functor

instance : (fromActionTopModFunc (k := k) (G := G)).IsEquivalence :=
  TopRepEquivActionTop (k := k) (G := G).isEquivalence_inverse

end equivAction

section Homological

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (k G) in
/-- The functor taking an `R`-linear `G`-representation to its `G`-invariant submodule. -/
abbrev invariants : TopRep k G ⥤ TopModuleCat k where
  obj A := .of k A.ρ.invariants
  map f  := TopModuleCat.ofHom f.hom.invariants

instance : (invariants k G).Additive where

instance {k : Type u} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k] :
    (invariants k G).Linear k where

variable (k G) in
/-- The functor taking a representation `rep` to the representation `C(G, rep)`.
The `G` action is defined by `g • f := x ↦ g • f (g⁻¹ * x)`. -/
abbrev coind₁ : TopRep k G ⥤ TopRep k G where
  obj A := of A.ρ.coind₁
  map φ := ofHom <| ContRepresentation.coind₁Map _ _ φ.hom

instance : (TopRep.coind₁ k G).Additive where

instance {k : Type u} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k] :
    (coind₁ k G).Linear k where

/-- The constant function `rep ⟶ C(G, rep)` as a natural transformation. -/
@[implicit_reducible, simps]
def coind₁ι : 𝟭 (TopRep k G) ⟶ coind₁ k G where
  app rep := ofHom rep.ρ.coind₁ι

namespace MultiInd

variable (k G) in
/-- The n-th functor taking `M` to `C(G, C(G,...,C(G, M)))` (with n `G`s).
These functors form a complex, see `MultiInd.complex`. -/
abbrev functor : ℕ → TopRep k G ⥤ TopRep k G
  | 0 => 𝟭 _
  | n + 1 => functor n ⋙ TopRep.coind₁ k G

instance (A : TopRep k G) (n : ℕ) :
    FunLike ((functor k G (n + 1)).obj A) G ((functor k G n).obj A) where
  coe σ := σ.toFun
  coe_injective := ContinuousMap.coe_injective

lemma functor_toFun_apply {A : TopRep k G} {n : ℕ} (σ : (functor k G (n + 1)).obj A)
    (g : G) : σ.toFun g = σ g := rfl

variable (k G) in
/-- The differential map in `MultiInd.complex`. -/
@[implicit_reducible]
def d : ∀ n : ℕ, functor k G n ⟶ functor k G (n + 1)
  | 0 => coind₁ι
  | n + 1 => (functor k G (n + 1)).whiskerLeft coind₁ι
    - (functor k G (n + 1)).rightUnitor.hom ≫ Functor.whiskerRight (d n) (coind₁ k G)

@[simp] lemma d_zero : d k G 0 = coind₁ι := dsimp% rfl

lemma d_succ (n : ℕ) :
    d k G (n + 1) = (functor k G (n + 1)).whiskerLeft coind₁ι -
      (functor k G (n + 1)).rightUnitor.hom ≫ Functor.whiskerRight (d k G n) (coind₁ k G) :=
  rfl

lemma d_succ_app (n : ℕ) (A : TopRep k G) :
    (d k G (n + 1)).app A = (functor k G (n + 1)).rightUnitor.hom.app A ≫
      coind₁ι.app ((functor k G (n + 1)).obj A) -
      (functor k G (n + 1)).rightUnitor.hom.app A ≫ ((coind₁ k G).map ((d k G n).app A)) :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma d_comp_d (n : ℕ) :
    d k G n ≫ d k G (n + 1) = 0 := by
  induction n with
  | zero =>
    simp only [Nat.reduceAdd, d_zero, d_succ, functor,
      Functor.id_comp, Preadditive.comp_sub]
    ext A : 3
    simp only [Functor.id_obj, Functor.comp_obj, NatTrans.app_sub, NatTrans.comp_app, coind₁ι_app,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.whiskerRight_app,
      ConcreteCategory.hom_ofHom, Category.id_comp, hom_sub, hom_comp, Limits.zero_app, hom_zero]
    ext x
    simp [ContIntertwiningMap.toContinuousLinearMap_apply]
  | succ n ih =>
    rw [d_succ (n + 1), Preadditive.comp_sub]
    nth_rw 2 [d_succ]
    rw [Preadditive.sub_comp, ]
    change _ - (_ - (_ ≫ _) ≫ Functor.whiskerRight (d k G (n + 1)) (coind₁ k G)) = 0
    rw [Category.assoc, ← Functor.whiskerRight_comp]
    rw [ih, Functor.whiskerRight_zero, Limits.comp_zero, sub_zero, sub_eq_zero]
    rfl

open CategoryTheory
variable (k G) in
/-- The complex of functors whose behaviour pointwise takes an `R`-linear `G`-representation `M`
to the complex `M → C(G, M) → ⋯ → C(G, C(G,...,C(G, M))) → ⋯`
The `G`-invariant submodules of it is the homogeneous cochains (shifted by one). -/
abbrev complex : CochainComplex (TopRep k G ⥤ TopRep k G) ℕ :=
  CochainComplex.of (functor k G) (d k G) d_comp_d

lemma complex_d (A : TopRep k G) (n : ℕ) :
    ((complex k G).asFunctor.obj A).d n (n + 1) = (d k G n).app A := by
  rw [HomologicalComplex.asFunctor_obj_d]
  simp_rw [CochainComplex.of_d]

end MultiInd

end Homological

end TopRep
