/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
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

def V {k : Type u} {G : Type v} [Ring k] [Monoid G] (A : Rep k G) : ModuleCat k := Action.V A

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

instance : CoeSort (Rep.{w} k G) (Type _) := ⟨fun V => V.V⟩

def ρ (A : Rep k G) : Representation k G A.V :=
  (ModuleCat.endRingEquiv A.V).toMonoidHom.comp (Action.ρ A)
set_option pp.universes true in

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

@[simp]
lemma forget₂_map {M N : Rep k G} (f : M ⟶ N) :
    (forget₂ (Rep k G) (ModuleCat.{w, u} k)).map f = ModuleCat.ofHom f.hom.toLinearMap :=
  rfl

@[simp]
lemma forget₂_obj {M : Rep k G} : (forget₂ (Rep k G) (ModuleCat.{w, u} k)).obj M = M.V := rfl

instance : (forget₂ (Rep k G) (ModuleCat.{w, u} k)).Faithful where
  map_injective {X Y} _ _ h := hom_ext <| by ext1; simpa [ModuleCat.hom_ext_iff] using h

instance preservesLimits_forget :
    PreservesLimits (forget₂ (Rep.{w} k G) (ModuleCat k)) :=
  Action.preservesLimits_forget (ModuleCat.{w} k) G

instance preservesColimits_forget :
    PreservesColimits (forget₂ (Rep.{w} k G) (ModuleCat k)) :=
  Action.preservesColimits_forget (ModuleCat.{w} k) G

instance {M N : Rep k G} : Add (M ⟶ N) where
  add f g := ofHom (f.hom + g.hom)

lemma ofHom_add {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    {σ : Representation k G M} {ρ : Representation k G N} (f g : σ.IntertwiningMap ρ) :
    ofHom (f + g) = ofHom f + ofHom g := rfl

lemma add_hom {M N : Rep k G} (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom := rfl

lemma add_comp {M N O : Rep k G} (f₁ f₂ : M ⟶ N) (g : N ⟶ O) :
    (f₁ + f₂) ≫ g = f₁ ≫ g + f₂ ≫ g := by
  ext1
  simp [add_hom, Representation.IntertwiningMap.comp_add]

lemma comp_add {M N O : Rep k G} (f : M ⟶ N) (g₁ g₂ : N ⟶ O) :
    f ≫ (g₁ + g₂) = f ≫ g₁ + f ≫ g₂ := by
  ext1
  simp [add_hom, Representation.IntertwiningMap.add_comp]

instance {M N : Rep k G} : Zero (M ⟶ N) where
  zero := ofHom (0 : M.ρ.IntertwiningMap N.ρ)

lemma ofHom_zero {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    {σ : Representation k G M} {ρ : Representation k G N} :
    ofHom (0 : σ.IntertwiningMap ρ) = 0 := rfl

lemma zero_hom {M N : Rep k G} : (0 : M ⟶ N).hom = 0 := rfl

instance {M N : Rep k G} : SMul ℕ (M ⟶ N) where
  smul n f := ofHom (n • f.hom)

lemma ofHom_nsmul {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    {σ : Representation k G M} {ρ : Representation k G N} (f : σ.IntertwiningMap ρ) (n : ℕ) :
    ofHom (n • f) = n • ofHom f := rfl

lemma nsmul_hom {M N : Rep k G} (f : M ⟶ N) (n : ℕ) : (n • f).hom = n • f.hom := rfl

instance {M N : Rep k G} : Neg (M ⟶ N) where
  neg f := ofHom (-f.hom)

lemma ofHom_neg {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    {σ : Representation k G M} {ρ : Representation k G N} (f : σ.IntertwiningMap ρ) :
    ofHom (-f) = -ofHom f := rfl

lemma neg_hom {M N : Rep k G} (f : M ⟶ N) : (-f).hom = -f.hom := rfl

instance {M N : Rep k G} : Sub (M ⟶ N) where
  sub f g := ofHom (f.hom - g.hom)

lemma ofHom_sub {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    {σ : Representation k G M} {ρ : Representation k G N} (f g : σ.IntertwiningMap ρ) :
    ofHom (f - g) = ofHom f - ofHom g := rfl

lemma sub_hom {M N : Rep k G} (f g : M ⟶ N) : (f - g).hom = f.hom - g.hom := rfl

instance {M N : Rep k G} : SMul ℤ (M ⟶ N) where
  smul n f := ofHom (n • f.hom)

lemma ofHom_zsmul {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    {σ : Representation k G M} {ρ : Representation k G N} (f : σ.IntertwiningMap ρ) (n : ℤ) :
    ofHom (n • f) = n • ofHom f := rfl

lemma zsmul_hom {M N : Rep k G} (f : M ⟶ N) (n : ℤ) : (n • f).hom = n • f.hom := rfl

instance : Preadditive (Rep k G) where
  homGroup _ _ := hom_injective.addCommGroup _ zero_hom add_hom neg_hom sub_hom nsmul_hom zsmul_hom
  add_comp _ _ _ := add_comp
  comp_add _ _ _ := comp_add

instance {M N : Rep k G} : SMul k (M ⟶ N) where
  smul r f := ofHom (r • f.hom)

lemma ofHom_smul {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    {σ : Representation k G M} {ρ : Representation k G N} (f : σ.IntertwiningMap ρ) (r : k) :
    ofHom (r • f) = r • ofHom f := rfl

lemma smul_hom {M N : Rep k G} (f : M ⟶ N) (r : k) : (r • f).hom = r • f.hom := rfl

lemma smul_comp {M N O : Rep k G} (r : k) (f : M ⟶ N) (g : N ⟶ O) :
    (r • f) ≫ g = r • (f ≫ g) := by
  ext1
  simp [smul_hom, Representation.IntertwiningMap.smul_comp]

lemma comp_smul {M N O : Rep k G} (f : M ⟶ N) (r : k) (g : N ⟶ O) :
    f ≫ (r • g) = r • (f ≫ g) := by
  ext1
  simp [smul_hom, Representation.IntertwiningMap.comp_smul]

instance : Linear k (Rep k G) where
  homModule X Y := hom_injective.module _ ⟨⟨_, zero_hom⟩, add_hom⟩ <| by simp [smul_hom]
  smul_comp _ _ _ := smul_comp
  comp_smul _ _ _ := comp_smul

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
