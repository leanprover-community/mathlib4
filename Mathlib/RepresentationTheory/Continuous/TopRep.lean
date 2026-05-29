module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.Topology.ContinuousMap.Algebra

@[expose] public section

universe w u v

structure TopRep (k : Type u) (G : Type v) [TopologicalSpace k] [Ring k]
    [IsTopologicalRing k] [Monoid G] where
  private mk ::
  /-- the underlying type of an object in `Rep k G` -/
  V : Type w
  [hV1 : AddCommGroup V]
  [hV2 : Module k V]
  [hV3 : TopologicalSpace V]
  [hV4 : IsTopologicalAddGroup V]
  [hV5 : ContinuousSMul k V]
  /-- the underlying representation of an object in `Rep k G` -/
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
abbrev of : TopRep k G := ⟨X, ρ⟩

variable (X ρ) in
lemma of_V : (of ρ).V = X := by with_reducible rfl

variable (X ρ) in
lemma of_ρ : (of ρ).ρ = ρ := by with_reducible rfl

set_option backward.privateInPublic true in
/-- The type of morphisms in `Rep.{w} k G`. -/
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
/-- Turn a morphism in `Rep` back into an `IntertwiningMap`. -/
abbrev Hom.hom (f : Hom A B) := ConcreteCategory.hom (C := TopRep k G) f

variable {A B} in
/-- Typecheck an `IntertwiningMap` as a morphism in `Rep`. -/
abbrev ofHom (f : ρ →ⁱL σ) : of ρ ⟶ of σ :=
  ConcreteCategory.ofHom (C := TopRep.{w} k G) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (f : Hom A B) := f.hom

/-
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/
@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = .id (π₁ := A.ρ) := rfl

/- Provided for rewriting. -/
lemma id_apply (a : A) : (𝟙 A : A ⟶ A) a = a := rfl -- add `id_apply` as simp lemma!

@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
variable {A B C} in
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := rfl
-- add `comp_apply` as simp lemma!

variable {A B} in
@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g := Hom.ext hf

variable {A B} in
lemma hom_comm_apply (f : A ⟶ B) (g : G) (a : A) : f.hom (A.ρ g a) = B.ρ g (f.hom a) := by
  simpa using congr($(f.hom.2 g) a)

end TopRep
