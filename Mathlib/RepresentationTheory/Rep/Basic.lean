/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.RepresentationTheory.Intertwining

/-!
# `Rep k G` is the category of `k`-linear representations of `G`.

If `V : Rep k G`, there is a coercion that allows you to treat `V` as a type,
and this type comes equipped with a `Module k V` instance.
Also `V.ρ` gives the homomorphism `G →* (V →ₗ[k] V)`.

Conversely, given a homomorphism `ρ : G →* (V →ₗ[k] V)`,
you can construct the bundled representation as `Rep.of ρ`.

We construct the categorical equivalence `Rep k G ≌ ModuleCat k[G]`.
We verify that `Rep k G` is a `k`-linear abelian symmetric monoidal category with all (co)limits.
-/

@[expose] public section
suppress_compilation

open CategoryTheory Limits Representation.IntertwiningMap
open scoped MonoidAlgebra

universe w u v

/-- The category of `k`-linear representations of a monoid `G`. -/
def Rep (k : Type u) (G : Type v) [Ring k] [Monoid G] := Action (ModuleCat.{w, u} k) G

namespace Rep

def Hom {k : Type u} {G : Type v} [Ring k] [Monoid G] (A B : Rep k G) : Type w := Action.Hom A B

instance (k : Type u) (G : Type v) [Ring k] [Monoid G] : Category (Rep k G) where
  Hom := Rep.Hom
  __ := inferInstanceAs (Category (Action (ModuleCat.{w, u} k) G))

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

def V (A : Rep k G) : ModuleCat k := Action.V A

instance : CoeSort (Rep.{w} k G) (Type _) := ⟨fun V => V.V⟩

def ρ (A : Rep k G) : Representation k G A.V :=
  (ModuleCat.endRingEquiv A.V).toMonoidHom.comp (Action.ρ A)

instance : ConcreteCategory (Rep k G) (fun A B ↦ A.ρ.IntertwiningMap B.ρ) where
  hom f :=
  { __ := (Action.Hom.hom f).hom
    isIntertwining' g v := congr($(f.comm g) v)}
  ofHom f := {
    hom := ModuleCat.ofHom f.toLinearMap
    comm g := by ext; exact f.isIntertwining' g _
  }

abbrev Hom.hom {A B : Rep k G} (f : A ⟶ B) : A.ρ.IntertwiningMap B.ρ :=
  ConcreteCategory.hom (C := Rep k G) f

def of {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k G V) : Rep k G :=
  ⟨ModuleCat.of k V, (ModuleCat.endRingEquiv _).symm.toMonoidHom.comp ρ⟩

abbrev ofHom {A B : Type w} [AddCommGroup A] [AddCommGroup B] [Module k A] [Module k B]
    {σ : Representation k G A} {ρ : Representation k G B} (f : σ.IntertwiningMap ρ) :
    Rep.of σ ⟶ Rep.of ρ := ConcreteCategory.ofHom (C := Rep k G) f

@[simp]
lemma coe_of {V : Type u} [AddCommGroup V] [Module k V] (ρ : G →* V →ₗ[k] V) :
    (of ρ : Type u) = V := rfl

@[simp]
theorem of_ρ {V : Type u} [AddCommGroup V] [Module k V] (ρ : G →* V →ₗ[k] V) : (of ρ).ρ = ρ :=
  rfl

lemma hom_comm_apply {A B : Rep k G} (f : A ⟶ B) (g : G) (x : A) :
    f.hom (A.ρ g x) = B.ρ g (f.hom x) := congr($(f.comm g) x)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/
@[simp]
lemma hom_id {M : Rep k G} : (𝟙 M : M ⟶ M).hom = Representation.IntertwiningMap.id _ := rfl

/- Provided for rewriting. -/
lemma hom_hom_id (M : Rep k G) :
    (𝟙 M : M ⟶ M).hom.toLinearMap = LinearMap.id := by rfl

lemma id_hom_apply {M : Rep k G} (x : M) : (𝟙 M : M ⟶ M) x = x := by
  simp [Representation.IntertwiningMap.id_apply]

@[simp]
lemma hom_comp {M N O : Rep k G} (f : M ⟶ N) (g : N ⟶ O) :
    (f ≫ g).hom = f.hom.comp g.hom := rfl

lemma hom_comp_toLinearMap {M N O : Rep k G} (f : M ⟶ N) (g : N ⟶ O) :
    (f ≫ g).hom.toLinearMap = g.hom.toLinearMap ∘ₗ f.hom.toLinearMap := rfl

/- Provided for rewriting. -/
lemma comp_apply {M N O : Rep k G} (f : M ⟶ N) (g : N ⟶ O) (x : M) :
    (f ≫ g) x = g (f x) := by rfl

@[ext]
lemma hom_ext {M N : Rep k G} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  ConcreteCategory.ext hf

@[simp]
lemma ofHom_hom {M N : Rep k G} (f : M ⟶ N) :
    Rep.ofHom f.hom = f := rfl

@[simp]
lemma hom_ofHom {X Y : Type w} [AddCommGroup X] [Module k X] [AddCommGroup Y]
    [Module k Y] {σ : Representation k G X} {ρ : Representation k G Y} (f : σ.IntertwiningMap ρ) :
    (Rep.ofHom f).hom = f := rfl

lemma hom_bijective {M N : Rep k G} :
    Function.Bijective (Rep.Hom.hom : (M ⟶ N) → (M.ρ.IntertwiningMap N.ρ)) where
  left _ _ h := hom_ext h
  right f := ⟨Rep.ofHom f, Rep.hom_ofHom f⟩

/-- Convenience shortcut for `ModuleCat.hom_bijective.injective`. -/
lemma hom_injective {M N : Rep k G} :
    Function.Injective (Hom.hom : (M ⟶ N) → (M.ρ.IntertwiningMap N.ρ)) :=
  hom_bijective.injective

/-- Convenience shortcut for `ModuleCat.hom_bijective.surjective`. -/
lemma hom_surjective {M N : Rep k G} :
    Function.Surjective (Hom.hom : (M ⟶ N) → (M.ρ.IntertwiningMap N.ρ)) :=
  hom_bijective.surjective

@[simp]
lemma ofHom_id {M : Type w} [AddCommGroup M] [Module k M] (σ : Representation k G M) :
  ofHom (.id σ) = 𝟙 (of σ) := rfl

@[simp]
lemma ofHom_comp {M N O : Type w} [AddCommGroup M] [AddCommGroup N] [AddCommGroup O] [Module k M]
    [Module k N] [Module k O] {σ : Representation k G M} {ρ : Representation k G N}
    {τ : Representation k G O} (f : σ.IntertwiningMap ρ) (g : ρ.IntertwiningMap τ) :
    ofHom (f.comp g) = ofHom f ≫ ofHom g := rfl

/- Doesn't need to be `@[simp]` since `simp only` can solve this. -/
lemma ofHom_apply {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    {σ : Representation k G M} {ρ : Representation k G N} (f : σ.IntertwiningMap ρ) (x : M) :
    ofHom f x = f x := rfl

lemma inv_hom_apply {M N : Rep k G} (e : M ≅ N) (x : M) : e.inv.hom (e.hom.hom x) = x := by
  simp

lemma hom_inv_apply {M N : Rep k G} (e : M ≅ N) (x : N) : e.hom.hom (e.inv.hom x) = x := by
  simp

/-- `ModuleCat.Hom.hom` bundled as an `Equiv`. -/
def homEquiv {M N : Rep k G} : (M ⟶ N) ≃ (M.ρ.IntertwiningMap N.ρ) where
  toFun := Hom.hom
  invFun := ofHom

def Hom.toModuleCatHom {M N : Rep k G} (f : M ⟶ N) : M.V ⟶ N.V := ModuleCat.ofHom f.hom.toLinearMap

instance : HasForget₂ (Rep k G) (ModuleCat.{w, u} k) where
  forget₂ := {
    obj A := A.V
    map f := f.toModuleCatHom
  }

lemma forget₂_map {M N : Rep k G} (f : M ⟶ N) :
    (forget₂ (Rep k G) (ModuleCat.{w, u} k)).map f = ModuleCat.ofHom f.hom.toLinearMap :=
  rfl

@[simp]
lemma forget₂_obj {M : Rep k G} : (forget₂ (Rep k G) (ModuleCat.{w, u} k)).obj M = M.V := rfl

variable (k G) in
/-- The trivial `k`-linear `G`-representation on a `k`-module `V.` -/
abbrev trivial (V : Type u) [AddCommGroup V] [Module k V] : Rep k G :=
  Rep.of (Representation.trivial k G V)

theorem trivial_def {V : Type u} [AddCommGroup V] [Module k V] (g : G) :
    (trivial k G V).ρ g = LinearMap.id :=
  rfl

variable (k G) in
/-- The functor equipping a module with the trivial representation. -/
@[simps! obj_V map_hom]
def trivialFunctor : ModuleCat k ⥤ Rep k G where
  obj V := trivial k G V
  map f := { hom := f, comm := fun _ => rfl }

/-- A predicate for representations that fix every element. -/
abbrev IsTrivial (A : Rep k G) := A.ρ.IsTrivial

instance (X : ModuleCat k) : ((trivialFunctor k G).obj X).IsTrivial where

instance {V : Type u} [AddCommGroup V] [Module k V] :
    IsTrivial (Rep.trivial k G V) where

instance {V : Type u} [AddCommGroup V] [Module k V] (ρ : Representation k G V) [ρ.IsTrivial] :
    IsTrivial (Rep.of ρ) where

instance {H V : Type u} [Group H] [AddCommGroup V] [Module k V] (ρ : Representation k H V)
    (f : G →* H) [Representation.IsTrivial (ρ.comp f)] :
    Representation.IsTrivial ((Rep.of ρ).ρ.comp f) := ‹_›

section Commutative

def _root_.Action.applyAsHom {V : Type*} [Category* V] {G : Type*} [CommMonoid G]
    (ρ : Action V G) (g : G) : ρ ⟶ ρ where
  hom := ρ.ρ g
  comm := by simp [← End.mul_def, ← map_mul, mul_comm]

variable {G : Type v} [CommMonoid G]
variable (A : Rep k G)

/-- Given a representation `A` of a commutative monoid `G`, the map `ρ_A(g)` is a representation
morphism `A ⟶ A` for any `g : G`. -/
def applyAsHom (g : G) : A ⟶ A := Action.applyAsHom A g

@[simp]
lemma applyAsHom_apply {A : Rep k G} (g : G) (x : A) : (A.applyAsHom g).hom x = A.ρ g x := rfl

@[reassoc, elementwise]
lemma applyAsHom_comm {A B : Rep k G} (f : A ⟶ B) (g : G) :
    A.applyAsHom g ≫ f = f ≫ B.applyAsHom g := by
  ext; simp [hom_comm_apply]

end Commutative

end Rep
