/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Kim Morrison
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.RepresentationTheory.Action
public import Mathlib.RepresentationTheory.Equiv

/-!
# `Rep k G` is the category of `k`-linear representations of `G`.

Given a `G`-representation `ρ` on a module `V`, you can construct the bundled representation as
`Rep.of ρ`. Conversely, given a bundled representation `A : Rep k G`, you can get the underlying
module as `A.V` and the representation on it as `A.ρ`.

-/

@[expose] public section

universe w w' u u' v v'

open CategoryTheory

set_option backward.privateInPublic true in
/-- The category of representations of monoid `G` and their morphisms. -/
structure Rep (k : Type u) (G : Type v) [Semiring k] [Monoid G] where
  private mk ::
  /-- the underlying type of an object in `Rep k G` -/
  V : Type w
  [hV1 : AddCommGroup V]
  [hV2 : Module k V]
  /-- the underlying representation of an object in `Rep k G` -/
  ρ : Representation k G V

namespace Rep

noncomputable section

section semiring

variable {k : Type u} {G : Type v} [Semiring k] [Monoid G] {X Y : Type w} [AddCommGroup X]
  [AddCommGroup Y] [Module k X] [Module k Y] {ρ : Representation k G X} {σ : Representation k G Y}
  (A B C : Rep.{w} k G)

attribute [instance] hV1 hV2

initialize_simps_projections Rep (-hV1, -hV2)

instance : CoeSort (Rep k G) (Type w) := ⟨Rep.V⟩

attribute [coe] V

variable (ρ) in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The object in the category of representations associated to a type equipped a representation.
This is the preferred way to construct a term of `Rep k G`. -/
abbrev of : Rep.{w} k G := ⟨X, ρ⟩

variable (X ρ) in
lemma of_V : (of ρ).V = X := by with_reducible rfl

variable (X ρ) in
lemma of_ρ : (of ρ).ρ = ρ := by with_reducible rfl

set_option backward.privateInPublic true in
/-- The type of morphisms in `Rep.{w} k G`. -/
@[ext]
structure Hom where
  private mk ::
  /-- The underlying `G`-equivariant linear map. -/
  hom' : A.ρ.IntertwiningMap B.ρ

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Category (Rep.{w} k G) where
  Hom A B := Hom A B
  id A := ⟨.id A.ρ⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ConcreteCategory (Rep.{w} k G) (fun A B ↦ A.ρ.IntertwiningMap B.ρ) where
  hom := Hom.hom'
  ofHom := Hom.mk

variable {A B} in
/-- Turn a morphism in `Rep` back into an `IntertwiningMap`. -/
abbrev Hom.hom (f : Hom A B) := ConcreteCategory.hom (C := Rep k G) f

variable {A B} in
/-- Typecheck an `IntertwiningMap` as a morphism in `Rep`. -/
abbrev ofHom (f : ρ.IntertwiningMap σ) : of ρ ⟶ of σ :=
  ConcreteCategory.ofHom (C := Rep.{w} k G) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' → hom)

/-
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/
@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = .id A.ρ := rfl

/- Provided for rewriting. -/
lemma id_apply (a : A) : (𝟙 A : A ⟶ A) a = a := by
  simp [Representation.IntertwiningMap.id]

@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
variable {A B C} in
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp

variable {A B} in
@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g := Hom.ext hf

variable {A B} in
lemma hom_comm_apply (f : A ⟶ B) (g : G) (a : A) : f.hom (A.ρ g a) = B.ρ g (f.hom a) := by
  simpa using congr($(f.hom.2 g) a)

variable {Z : Type w} [AddCommGroup Z] [Module k Z] {τ : Representation k G Z}

@[simp] lemma hom_ofHom (f : ρ.IntertwiningMap σ) : (ofHom f).hom = f := rfl
@[simp] lemma ofHom_hom (f : A ⟶ B) : ofHom f.hom = f := rfl

@[simp] lemma ofHom_id : ofHom (.id σ) = 𝟙 (of σ) := rfl

@[simp]
lemma ofHom_comp (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) :
  ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

lemma ofHom_apply (f : ρ.IntertwiningMap σ) (x : X) : ofHom f x = f x := rfl

lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv.hom (e.hom.hom x) = x := by simp

lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom.hom (e.inv.hom x) = x := by simp

instance : Inhabited (Rep.{u} k G) := ⟨of (Representation.trivial k G PUnit)⟩

lemma forget_obj : (forget (Rep.{w} k G)).obj A = A := rfl

lemma forget_map (f : A ⟶ B) : (forget (Rep.{w} k G)).map f = (f : _ → _) := rfl

/-- An equiv between the underlying representations induce isomorphism between objects in
  `Rep k G`. -/
def mkIso (e : ρ.Equiv σ) : of ρ ≅ of σ where
  hom := ofHom e.toIntertwiningMap
  inv := ofHom e.symm.toIntertwiningMap

@[simp]
lemma mkIso_hom_hom_apply (e : ρ.Equiv σ) (x : X) :
    (mkIso e).hom.hom x = e.toLinearMap x := rfl

@[simp]
lemma mkIso_hom_hom_toLinearMap (e : ρ.Equiv σ) :
    (mkIso e).hom.hom.toLinearMap = e.toLinearMap := rfl

@[simp]
lemma mkIso_inv_hom_toLinearMap (e : ρ.Equiv σ) :
    (mkIso e).inv.hom.toLinearMap = e.symm.toIntertwiningMap.toLinearMap := rfl

@[simp]
lemma mkIso_inv_hom_apply (e : ρ.Equiv σ) (y : Y) :
    (mkIso e).inv.hom y = e.symm y := rfl

@[simp]
lemma mkIso_hom_hom (e : ρ.Equiv σ) :
    (mkIso e).hom.hom = e.toIntertwiningMap := rfl

variable {A B C}

/-- The equivalence between representations induced from iso between objects in `Rep k G`. -/
@[simps]
def _root_.Representation.equivOfIso (i : A ≅ B) : A.ρ.Equiv B.ρ where
  __ := i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

instance reflectsIsomorphisms_forget : (forget (Rep.{w} k G)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (Rep.{w} k G)).map f)
    let e : X.ρ.Equiv Y.ρ := { f.hom, i.toEquiv with }
    exact (mkIso e).isIso_hom

lemma hom_bijective :
    Function.Bijective (Rep.Hom.hom : (A ⟶ B) → (A.ρ.IntertwiningMap B.ρ)) where
  left _ _ h := Rep.hom_ext h
  right f := ⟨Rep.ofHom f, Rep.hom_ofHom f⟩

/-- Convenience shortcut for `Rep.hom_bijective.injective`. -/
lemma hom_injective :
    Function.Injective (Hom.hom : (A ⟶ B) → (A.ρ.IntertwiningMap B.ρ)) :=
  hom_bijective.injective

/-- Convenience shortcut for `Rep.hom_bijective.surjective`. -/
lemma hom_surjective :
    Function.Surjective (Hom.hom : (A ⟶ B) → (A.ρ.IntertwiningMap B.ρ)) :=
  hom_bijective.surjective

/-- The morphisms between two objects in `Rep k G` has an equivalence to the intertwining maps
  between their underlying representations. -/
@[simps]
def homEquiv : (A ⟶ B) ≃ (A.ρ.IntertwiningMap B.ρ) where
  toFun := Hom.hom
  invFun := ofHom

instance : Add (A ⟶ B) where add f g := ofHom (f.hom + g.hom)

lemma ofHom_add (f g : ρ.IntertwiningMap σ) :
    ofHom (f + g) = ofHom f + ofHom g := rfl

lemma add_hom (f g : A ⟶ B) : (f + g).hom = f.hom + g.hom := rfl

lemma hom_comp_toLinearMap (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom.toLinearMap = g.hom.toLinearMap ∘ₗ f.hom.toLinearMap := rfl

lemma add_comp (f₁ f₂ : A ⟶ B) (g : B ⟶ C) :
    (f₁ + f₂) ≫ g = f₁ ≫ g + f₂ ≫ g := by
  ext1
  simp [add_hom, Representation.IntertwiningMap.add_comp]

lemma comp_add (f : A ⟶ B) (g₁ g₂ : B ⟶ C) :
    f ≫ (g₁ + g₂) = f ≫ g₁ + f ≫ g₂ := by
  ext1
  simp [add_hom, Representation.IntertwiningMap.comp_add]

instance : Zero (A ⟶ B) where
  zero := ofHom (0 : A.ρ.IntertwiningMap B.ρ)

@[simp]
lemma ofHom_zero : ofHom (0 : ρ.IntertwiningMap σ) = 0 := rfl

@[simp]
lemma zero_hom : (0 : A ⟶ B).hom = 0 := rfl

instance : SMul ℕ (A ⟶ B) where smul n f := ofHom (n • f.hom)

lemma ofHom_nsmul (f : ρ.IntertwiningMap σ) (n : ℕ) :
    ofHom (n • f) = n • ofHom f := rfl

lemma nsmul_hom (f : A ⟶ B) (n : ℕ) : (n • f).hom = n • f.hom := rfl

instance : Neg (A ⟶ B) where neg f := ofHom (-f.hom)

lemma ofHom_neg (f : ρ.IntertwiningMap σ) : ofHom (-f) = -ofHom f := rfl

lemma neg_hom (f : A ⟶ B) : (-f).hom = -f.hom := rfl

instance : Sub (A ⟶ B) where sub f g := ofHom (f.hom - g.hom)

lemma ofHom_sub (f g : ρ.IntertwiningMap σ) : ofHom (f - g) = ofHom f - ofHom g := rfl

lemma sub_hom (f g : A ⟶ B) : (f - g).hom = f.hom - g.hom := rfl

instance : SMul ℤ (A ⟶ B) where smul n f := ofHom (n • f.hom)

lemma ofHom_zsmul (f : ρ.IntertwiningMap σ) (n : ℤ) : ofHom (n • f) = n • ofHom f := rfl

lemma zsmul_hom (f : A ⟶ B) (n : ℤ) : (n • f).hom = n • f.hom := rfl

instance : AddCommGroup (A ⟶ B) := fast_instance% hom_injective.addCommGroup
    Rep.Hom.hom zero_hom add_hom neg_hom sub_hom nsmul_hom zsmul_hom

instance : Preadditive (Rep.{w} k G) where
  add_comp _ _ _ := add_comp
  comp_add _ _ _ := comp_add

lemma sum_hom {ι : Type u'} (f : ι → (A ⟶ B)) (s : Finset ι) :
    (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom := by
  classical induction s using Finset.induction with
  | empty => simp
  | insert a s ha h => simp [Finset.sum_insert ha, add_hom, h]

lemma ofHom_sum {ι : Type u'} {M N : Type v'} [AddCommGroup M] [AddCommGroup N] [Module k M]
    [Module k N] {σ : Representation k G M} {ρ : Representation k G N} (f : ι → σ.IntertwiningMap ρ)
    (s : Finset ι) :
    ofHom (∑ i ∈ s, f i) = ∑ i ∈ s, ofHom (f i) := by
  classical induction s using Finset.induction with
  | empty => simp
  | insert a s ha h => simp [Finset.sum_insert ha, ofHom_add, h]

variable (k G) in
/-- The trivial `k`-linear `G`-representation on a `k`-module `V.` -/
abbrev trivial (V : Type w) [AddCommGroup V] [Module k V] : Rep k G :=
  Rep.of (Representation.trivial k G V)

lemma trivial_V {V : Type w} [AddCommGroup V] [Module k V] : (trivial k G V).V = V := rfl

lemma trivial_ρ {V : Type w} [AddCommGroup V] [Module k V] (g : G) :
    (trivial k G V).ρ g = LinearMap.id := rfl

@[simp]
lemma trivial_ρ_apply {V : Type w} [AddCommGroup V] [Module k V] (g : G) (v : V) :
    (trivial k G V).ρ g v = v := rfl

lemma ρ_mul (g1 g2 : G) : A.ρ (g1 * g2) = A.ρ g1 ∘ₗ A.ρ g2 := by ext; simp

section Commutative

variable {G : Type v} [CommMonoid G]
variable (A : Rep k G)

/-- Given a representation `A` of a commutative monoid `G`, the map `ρ_A(g)` is a representation
morphism `A ⟶ A` for any `g : G`. -/
def applyAsHom (g : G) : A ⟶ A := Rep.ofHom ⟨A.ρ g, by simp [← ρ_mul, mul_comm]⟩

@[simp]
lemma applyAsHom_apply {A : Rep k G} (g : G) (x : A) : (A.applyAsHom g).hom x = A.ρ g x := rfl

@[reassoc, elementwise]
lemma applyAsHom_comm {A B : Rep k G} (f : A ⟶ B) (g : G) :
    A.applyAsHom g ≫ f = f ≫ B.applyAsHom g := by
  ext; simp [hom_comm_apply]

end Commutative

end semiring

section ring

variable {k : Type u} {G : Type v} [Ring k] [Monoid G]

section setup

variable (k G)

/-- Given a `G`-action on `H`, this is `k[H]` bundled with the natural representation
`G →* End(k[H])` as a term of type `Rep k G`. -/
abbrev ofMulAction (H : Type w') [MulAction G H] : Rep k G :=
  of <| Representation.ofMulAction k G H

/-- The `k`-linear `G`-representation on `k[G]`, induced by left multiplication. -/
abbrev leftRegular : Rep k G :=
  ofMulAction k G G

/-- The `k`-linear `G`-representation on `k[Gⁿ]`, induced by left multiplication. -/
abbrev diagonal (n : ℕ) : Rep k G :=
  ofMulAction k G (Fin n → G)

/-- The natural isomorphism between the representations on `k[G¹]` and `k[G]` induced by left
multiplication in `G`. -/
abbrev diagonalOneIsoLeftRegular :
    diagonal k G 1 ≅ leftRegular k G := Rep.mkIso (Representation.diagonalOneEquivLeftRegular k G)

/-- When `H = {1}`, the `G`-representation on `k[H]` induced by an action of `G` on `H` is
isomorphic to the trivial representation on `k`. -/
abbrev ofMulActionSubsingletonIsoTrivial
    (H : Type u) [Subsingleton H] [MulOneClass H] [MulAction G H] :
    ofMulAction k G H ≅ trivial k G k :=
  mkIso <| Representation.ofMulActionSubsingletonEquivTrivial k G H

section

variable (A : Type w') [AddCommGroup A] [Module k A] [DistribMulAction G A] [SMulCommClass G k A]

/-- Turns a `k`-module `A` with a compatible `DistribMulAction` of a monoid `G` into a
`k`-linear `G`-representation on `A`. -/
def ofDistribMulAction : Rep k G := Rep.of (Representation.ofDistribMulAction k G A)

@[simp] theorem ofDistribMulAction_ρ_apply_apply (g : G) (a : A) :
    (ofDistribMulAction k G A).ρ g a = g • a := rfl

/-- Given an `R`-algebra `S`, the `ℤ`-linear representation associated to the natural action of
`S ≃ₐ[R] S` on `S`. -/
@[simp] def ofAlgebraAut (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    Rep ℤ (S ≃ₐ[R] S) := ofDistribMulAction ℤ (S ≃ₐ[R] S) S

end

section
variable (M G : Type*) [Monoid M] [CommGroup G] [MulDistribMulAction M G]

/-- Turns a `CommGroup` `G` with a `MulDistribMulAction` of a monoid `M` into a
`ℤ`-linear `M`-representation on `Additive G`. -/
def ofMulDistribMulAction : Rep ℤ M := Rep.of (Representation.ofMulDistribMulAction M G)

variable {G M}

/-- Unfolds `ofMulDistribMulAction`; useful to keep track of additivity. -/
@[simps!]
def toAdditive : ofMulDistribMulAction M G ≃+ Additive G := AddEquiv.refl _

@[simp] theorem ofMulDistribMulAction_ρ_apply_apply (g : M) (a : Additive G) :
    (ofMulDistribMulAction M G).ρ g a = Additive.ofMul (g • a.toMul) := rfl

/-- Given an `R`-algebra `S`, the `ℤ`-linear representation associated to the natural action of
`S ≃ₐ[R] S` on `Sˣ`. -/
@[simp] def ofAlgebraAutOnUnits (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    Rep ℤ (S ≃ₐ[R] S) := Rep.ofMulDistribMulAction (S ≃ₐ[R] S) Sˣ

end

variable {k G}

/-- Given an element `x : A`, there is a natural morphism of representations `k[G] ⟶ A` sending
`g ↦ A.ρ(g)(x).` -/
abbrev leftRegularHom (A : Rep k G) (x : A) : leftRegular k G ⟶ A :=
  Rep.ofHom ⟨Finsupp.lift A k G fun g ↦ A.ρ g x, fun g ↦ by ext; simp⟩

theorem leftRegularHom_hom_single {A : Rep k G} (g : G) (x : A) (r : k) :
    (leftRegularHom A x).hom (.single g r) = r • A.ρ g x := by
  simp [leftRegularHom]

variable (A : Rep k G)

/-- Given a `k`-linear `G`-representation `(V, ρ)`, this is the representation defined by
restricting `ρ` to a `G`-invariant `k`-submodule of `V`. -/
abbrev subrepresentation (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    Rep k G := Rep.of (A.ρ.subrepresentation W le_comap)

/-- The natural inclusion of a subrepresentation into the ambient representation. -/
@[simps!]
def subtype (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    subrepresentation A W le_comap ⟶ A := Rep.ofHom ⟨W.subtype, fun _ ↦ rfl⟩

/-- Given a `k`-linear `G`-representation `(V, ρ)` and a `G`-invariant `k`-submodule `W ≤ V`, this
is the representation induced on `V ⧸ W` by `ρ`. -/
abbrev quotient (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    Rep k G := Rep.of (A.ρ.quotient W le_comap)

/-- The natural projection from a representation to its quotient by a subrepresentation. -/
@[simps!]
def mkQ (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    A ⟶ quotient A W le_comap := Rep.ofHom ⟨W.mkQ, fun _ ↦ rfl⟩

end setup

variable (k G) in
/-- The functor equipping a module with the trivial representation. -/
@[simps! obj_V map_hom]
def trivialFunctor : ModuleCat.{w} k ⥤ Rep.{w} k G where
  obj V := trivial k G V
  map f := ofHom ⟨f.hom, fun _ ↦ rfl⟩

/-- A predicate for representations that fix every element. -/
abbrev IsTrivial (A : Rep k G) := A.ρ.IsTrivial

instance (X : ModuleCat k) : ((trivialFunctor k G).obj X).IsTrivial where

instance {V : Type w} [AddCommGroup V] [Module k V] :
    IsTrivial (Rep.trivial k G V) where

instance {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k G V) [ρ.IsTrivial] :
    IsTrivial (Rep.of ρ) where
  out := Representation.isTrivial_def ρ

instance {H : Type u'} {V : Type w} [Group H] [AddCommGroup V] [Module k V]
    (ρ : Representation k H V) (f : G →* H) [Representation.IsTrivial (ρ.comp f)] :
    Representation.IsTrivial ((Rep.of ρ).ρ.comp f) := ‹_›

variable {A B C : Rep.{w} k G}

instance hasForgetToModuleCat :
    HasForget₂ (Rep.{w} k G) (ModuleCat.{w} k) where
  forget₂.obj A := .of k A
  forget₂.map f := ModuleCat.ofHom f.hom.toLinearMap

/-- A morphism in `Rep k G` has an underlying linear map attached to it hence induce a morphism in
  `ModuleCat k`. -/
abbrev Hom.toModuleCatHom (f : A ⟶ B) : ModuleCat.of k A.V ⟶ ModuleCat.of k B.V :=
  ModuleCat.ofHom f.hom.toLinearMap

@[simp] lemma forget₂_moduleCat_obj (A : Rep.{w} k G) :
    (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).obj A = .of k A := rfl

@[simp] lemma forget₂_moduleCat_map (f : A ⟶ B) :
    (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).map f = ModuleCat.ofHom f.hom.toLinearMap := rfl

instance : (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).Faithful := inferInstance

section Action

variable (k G)

/-- Every object in `Rep k G` naturally correspond to an object in `Action`. -/
@[simps]
def RepToAction : Rep.{w} k G ⥤ Action (ModuleCat.{w} k) G where
  obj X := ⟨.of k X, (ModuleCat.endRingEquiv (.of k X)).symm.toMonoidHom.comp X.ρ⟩
  map f := ⟨f.toModuleCatHom, fun g ↦ ModuleCat.hom_ext <| by
    simp [ModuleCat.endRingEquiv, f.hom.2]⟩

lemma RepToAction_obj (X : Rep.{w} k G) : (RepToAction k G).obj X =
  ⟨.of k X, (ModuleCat.endRingEquiv (.of k X)).symm.toMonoidHom.comp X.ρ⟩ := rfl

/-- Every object in `ModuleCat k` that `G` acts on is an object in `Rep k G`. -/
@[simps]
def ActionToRep : Action (ModuleCat.{w} k) G ⥤ Rep.{w} k G where
  obj X := of <| (ModuleCat.endRingEquiv X.V).toMonoidHom.comp X.ρ
  map f := ofHom ⟨f.hom.hom, fun g ↦ by simpa using ModuleCat.hom_ext_iff.1 (f.comm g)⟩

/-- `unitIso` of the equivalence between `Action` and `Rep`. -/
def RepToAction_ActionToRep (A : Action (ModuleCat.{w} k) G) :
    (RepToAction k G).obj ((ActionToRep k G).obj A) ≅ A where
  hom := ⟨𝟙 _, fun g ↦ by rfl⟩
  inv := ⟨𝟙 _, fun g ↦ by rfl⟩

/-- `counitIso` of the equivalence between `Action` and `Rep`. -/
def ActionToRep_RepToAction (X : Rep.{w} k G) :
    (ActionToRep k G).obj ((RepToAction k G).obj X) ≅ X where
  hom := ofHom ⟨LinearMap.id, fun g ↦ show LinearMap.id ∘ₗ X.ρ g = X.ρ g ∘ₗ LinearMap.id by simp⟩
  inv := ofHom ⟨LinearMap.id, fun g ↦ show LinearMap.id ∘ₗ X.ρ g = X.ρ g ∘ₗ LinearMap.id by simp⟩

/-- The category equivalence between `Rep` and `Action`. -/
def repIsoAction : Rep.{w} k G ≌ Action (ModuleCat.{w} k) G where
  functor := RepToAction k G
  inverse := ActionToRep k G
  unitIso := NatIso.ofComponents (ActionToRep_RepToAction k G)
  counitIso := NatIso.ofComponents (RepToAction_ActionToRep k G)

instance : (RepToAction k G).IsEquivalence :=
  repIsoAction k G |>.isEquivalence_functor

instance : (ActionToRep k G).IsEquivalence :=
  repIsoAction k G |>.isEquivalence_inverse

instance : (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).Additive where
  map_add {X Y} f g := by ext1; simp [add_hom]

/-- Forgetting `Rep` to `ModuleCat` is the same as first map to `Action`
  then forget to `ModuleCat`. -/
abbrev forgetNatIsoActionForget : forget₂ (Rep.{w} k G) (ModuleCat k) ≅ (RepToAction k G) ⋙
    Action.forget (ModuleCat k) G := .refl _

instance preservesLimits_forget :
    Limits.PreservesLimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k)) :=
  Limits.preservesLimits_of_natIso (forgetNatIsoActionForget k G).symm

instance preservesColimits_forget :
    Limits.PreservesColimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k)) :=
  Limits.preservesColimits_of_natIso (forgetNatIsoActionForget k G).symm

variable {k G} in
theorem epi_iff_surjective (f : A ⟶ B) : Epi f ↔ Function.Surjective f.hom :=
  ⟨fun _ => (ModuleCat.epi_iff_surjective ((forget₂ _ _).map f)).1 inferInstance,
  fun h => (forget₂ _ _).epi_of_epi_map ((ModuleCat.epi_iff_surjective <|
    (forget₂ _ _).map f).2 h)⟩

variable {k G} in
theorem mono_iff_injective (f : A ⟶ B) : Mono f ↔ Function.Injective f.hom :=
  ⟨fun _ => (ModuleCat.mono_iff_injective ((forget₂ _ _).map f)).1 inferInstance,
  fun h => (forget₂ _ _).mono_of_mono_map ((ModuleCat.mono_iff_injective <|
    (forget₂ _ _).map f).2 h)⟩

instance (f : A ⟶ B) [Mono f] : Mono f.toModuleCatHom :=
  inferInstanceAs <| Mono ((forget₂ _ _).map f)

instance (f : A ⟶ B) [Epi f] : Epi f.toModuleCatHom :=
  inferInstanceAs <| Epi ((forget₂ _ _).map f)

end Action

end ring

section CommSemiring

variable {k : Type u} {G : Type v} [CommSemiring k] [Monoid G]

instance {M N : Rep k G} : SMul k (M ⟶ N) where
  smul r f := ofHom (r • f.hom)

lemma ofHom_smul {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    {σ : Representation k G M} {ρ : Representation k G N} (f : σ.IntertwiningMap ρ) (r : k) :
    ofHom (r • f) = r • ofHom f := rfl

lemma smul_hom {M N : Rep k G} (f : M ⟶ N) (r : k) : (r • f).hom = r • f.hom := rfl

lemma smul_comp {M N O : Rep k G} (r : k) (f : M ⟶ N) (g : N ⟶ O) :
    (r • f) ≫ g = r • (f ≫ g) := by
  ext1
  simp [smul_hom, Representation.IntertwiningMap.comp_smul]

lemma comp_smul {M N O : Rep k G} (f : M ⟶ N) (r : k) (g : N ⟶ O) :
    f ≫ (r • g) = r • (f ≫ g) := by
  ext
  simp [smul_hom, Representation.IntertwiningMap.smul_comp]

instance {M N : Rep k G} : Module k (M ⟶ N) := fast_instance% hom_injective.module
  _ ⟨⟨_, zero_hom⟩, add_hom⟩ <| by simp [smul_hom]

instance : Linear k (Rep k G) where
  smul_comp _ _ _ := smul_comp
  comp_smul _ _ _ := comp_smul

end CommSemiring

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

instance : Functor.Linear k (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)) where
  map_smul {X Y} f r := by
    ext
    simp [smul_hom]

/-- The equivalence between `IntertwiningMap`s and morphism between `X Y : Rep k G` is linear. -/
abbrev homLinearEquiv (X Y : Rep k G) : (X ⟶ Y) ≃ₗ[k] (X.ρ.IntertwiningMap Y.ρ) where
  __ := homEquiv
  map_add' := add_hom
  map_smul' _ _ := smul_hom _ _

section monoidal

open MonoidalCategory CategoryTheory Representation.IntertwiningMap
  Representation.TensorProduct

instance : MonoidalCategory (Rep.{u} k G) where
  tensorObj X Y := of (X.ρ.tprod Y.ρ)
  whiskerLeft X _ _ f := ofHom (lTensor X.ρ f.hom)
  whiskerRight f Z := ofHom (rTensor Z.ρ f.hom)
  tensorUnit := Rep.trivial k G k
  tensorHom f g := ofHom (f.hom.tensor g.hom)
  associator X Y Z := Rep.mkIso (assoc X.ρ Y.ρ Z.ρ)
  leftUnitor X := Rep.mkIso (lid k X.ρ)
  rightUnitor X := Rep.mkIso (rid k X.ρ)
  associator_naturality _ _ _ := by ext; simp
  leftUnitor_naturality _ := by ext; simp [trivial_V]
  rightUnitor_naturality _ := by ext; simp [trivial_V]
  pentagon _ _ _ _ := by ext; simp
  triangle X Y := by ext; simp

@[simp]
lemma tensorUnit_V : (𝟙_ (Rep.{u} k G)).V = k := rfl

@[simp]
lemma tensorUnit_ρ : (𝟙_ (Rep.{u} k G)).ρ = Representation.trivial k G k := rfl

@[simp]
lemma tensor_V {X Y : Rep k G} : (X ⊗ Y).V = TensorProduct k X.V Y.V := rfl

@[simp]
lemma tensor_ρ {X Y : Rep k G} : (X ⊗ Y).ρ = X.ρ.tprod Y.ρ := rfl

@[simp]
lemma hom_whiskerRight {X₁ X₂ Y : Rep k G} (f : X₁ ⟶ X₂) :
    (f ▷ Y).hom = .rTensor _ f.hom := rfl

@[simp]
lemma hom_whiskerLeft {X Y₁ Y₂ : Rep k G} (f : Y₁ ⟶ Y₂) :
    (X ◁ f).hom = .lTensor _ f.hom := rfl

@[simp]
lemma hom_tensorHom {X₁ X₂ Y₁ Y₂ : Rep k G} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g).hom = f.hom.tensor g.hom := rfl

@[simp]
lemma of_tensor {X Y : Type u} [AddCommGroup X] [AddCommGroup Y] [Module k X] [Module k Y]
    (σ : Representation k G X) (ρ : Representation k G Y) :
    of (σ.tprod ρ) = of σ ⊗ of ρ := rfl

@[simp]
lemma hom_hom_associator {X Y Z : Rep k G} : (α_ X Y Z).hom.hom =
    (Representation.TensorProduct.assoc X.ρ Y.ρ Z.ρ).toIntertwiningMap := by
  ext1
  refine TensorProduct.ext_threefold fun x y z ↦ by rfl

@[simp]
lemma hom_inv_associator {X Y Z : Rep k G} : (α_ X Y Z).inv.hom =
    (Representation.TensorProduct.assoc X.ρ Y.ρ Z.ρ).symm.toIntertwiningMap := rfl

@[simp]
lemma hom_hom_leftUnitor {X : Rep k G} : (λ_ X).hom.hom =
    (Representation.TensorProduct.lid k X.ρ).toIntertwiningMap :=
  rfl

@[simp]
lemma hom_inv_leftUnitor {X : Rep k G} : (λ_ X).inv.hom =
    (Representation.TensorProduct.lid k X.ρ).symm.toIntertwiningMap := rfl

@[simp]
lemma hom_hom_rightUnitor {X : Rep k G} : (ρ_ X).hom.hom =
    (Representation.TensorProduct.rid k X.ρ).toIntertwiningMap :=
  rfl

@[simp]
lemma hom_inv_rightUnitor {X : Rep k G} : (ρ_ X).inv.hom =
    (Representation.TensorProduct.rid k X.ρ).symm.toIntertwiningMap := rfl

instance : MonoidalPreadditive (Rep.{u} k G) where
  whiskerLeft_zero {_ _ _} := by ext1; simp
  zero_whiskerRight {_ _ _} := by ext1; simp
  whiskerLeft_add _ _ := by ext1; simp [add_hom]
  add_whiskerRight _ _ := by ext1; simp [add_hom]

instance : MonoidalLinear k (Rep.{u} k G) where
  whiskerLeft_smul _ _ _ _ _ := by ext1; simp [smul_hom]
  smul_whiskerRight _ _ _ _ _ := by ext1; simp [smul_hom]

instance : BraidedCategory (Rep.{u} k G) where
  braiding X Y := Rep.mkIso (Representation.TensorProduct.comm X.ρ Y.ρ)
  braiding_naturality_right _ _ _ _ := by ext1; simp [comm_comp_lTensor]
  braiding_naturality_left _ _ := by ext1; simp [comm_comp_rTensor]
  hexagon_forward _ _ _ := by
    ext : 2
    exact TensorProduct.ext_threefold <| fun _ _ _ ↦ by simp
  hexagon_reverse X Y Z := by
    ext : 2
    simp only [tensor_V, tensor_ρ, hom_comp, hom_inv_associator, mkIso_hom_hom, comp_toLinearMap,
      assoc_symm_toLinearMap, toLinearMap_comm, LinearEquiv.comp_coe, hom_whiskerRight,
      hom_whiskerLeft, toLinearMap_rTensor, toLinearMap_lTensor]
    ext; simp

@[simp]
lemma hom_braiding {X Y : Rep k G} : (β_ X Y).hom.hom =
    (Representation.TensorProduct.comm X.ρ Y.ρ).toIntertwiningMap := rfl

open Representation.Equiv in
instance : SymmetricCategory (Rep.{u} k G) where
  symmetry X Y := by ext1; simp [← comm_symm Y.ρ X.ρ, ← toIntertwiningMap_trans,
    trans_symm, toIntertwiningMap_refl]

end monoidal

section MonoidalClosed
open MonoidalCategory Action

variable {G : Type v} [Group G] (A B C : Rep.{w} k G)

/-- Given a `k`-linear `G`-representation `(A, ρ₁)`, this is the 'internal Hom' functor sending
`(B, ρ₂)` to the representation `Homₖ(A, B)` that maps `g : G` and `f : A →ₗ[k] B` to
`(ρ₂ g) ∘ₗ f ∘ₗ (ρ₁ g⁻¹)`. -/
@[simps]
protected noncomputable def ihom : Rep k G ⥤ Rep k G where
  obj B := Rep.of (Representation.linHom A.ρ B.ρ)
  map {X} {Y} f := Rep.ofHom ⟨LinearMap.llcomp k _ _ _ f.hom.toLinearMap, fun g ↦ by
    ext; simp [Representation.IntertwiningMap.toLinearMap_apply, ← hom_comm_apply]⟩
  map_id := fun _ => by ext; rfl
  map_comp := fun _ _ => by ext; rfl

@[simp] theorem ihom_obj_ρ_apply {A B : Rep k G} (g : G) (x : A →ₗ[k] B) :
    -- Hint to put this lemma into `simp`-normal form.
    DFunLike.coe (F := (Representation k G (↑A.V →ₗ[k] ↑B.V)))
    ((Rep.ihom A).obj B).ρ g x = B.ρ g ∘ₗ x ∘ₗ A.ρ g⁻¹ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Given a `k`-linear `G`-representation `A`, this is the Hom-set bijection in the adjunction
`A ⊗ - ⊣ ihom(A, -)`. It sends `f : A ⊗ B ⟶ C` to a `Rep k G` morphism defined by currying the
`k`-linear map underlying `f`, giving a map `A →ₗ[k] B →ₗ[k] C`, then flipping the arguments. -/
@[simps]
def tensorHomEquiv (A B C : Rep.{u} k G) : (A ⊗ B ⟶ C) ≃ (B ⟶ (Rep.ihom A).obj C) where
  toFun f := Rep.ofHom ⟨(TensorProduct.curry f.hom.toLinearMap).flip, fun g ↦ by
    ext x y
    simp only [tensor_V, tensor_ρ, LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
      TensorProduct.curry_apply, Representation.IntertwiningMap.toLinearMap_apply,
      Representation.linHom_apply]
    have := by simpa using (hom_comm_apply f g (A.ρ g⁻¹ y ⊗ₜ[k] x)).symm
    simp [this]⟩
  invFun f := Rep.ofHom ⟨TensorProduct.uncurry (.id k) _ _ _
    f.hom.toLinearMap.flip, fun g ↦ TensorProduct.ext' fun x y => by
    simpa using LinearMap.ext_iff.1 (hom_comm_apply f g y) (A.ρ g x)⟩
  left_inv _ := Rep.Hom.ext <| Representation.IntertwiningMap.ext <|
    TensorProduct.ext' fun _ _ => rfl

variable {A B C}

noncomputable instance : MonoidalClosed (Rep k G) where
  closed A :=
    { rightAdj := Rep.ihom A
      adj := Adjunction.mkOfHomEquiv ({
        homEquiv := Rep.tensorHomEquiv A
        homEquiv_naturality_left_symm := fun _ _ => Rep.hom_ext <|
          Representation.IntertwiningMap.ext <| TensorProduct.ext' fun _ _ => rfl
        homEquiv_naturality_right _ _ := Rep.hom_ext <|
          Representation.IntertwiningMap.ext <|
            LinearMap.ext fun _ ↦ LinearMap.ext fun _ => rfl }) }

@[simp]
theorem ihom_obj_ρ_def (A B : Rep k G) : ((ihom A).obj B).ρ = ((Rep.ihom A).obj B).ρ :=
  rfl

@[simp]
theorem homEquiv_def (A B C : Rep k G) : (ihom.adjunction A).homEquiv B C =
    Rep.tensorHomEquiv A B C :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _

@[simp]
theorem ihom_ev_app_hom (A B : Rep k G) :
    ((ihom.ev A).app B).hom.toLinearMap = (TensorProduct.uncurry (.id k) A (A →ₗ[k] B) B
      LinearMap.id.flip) := by
  ext; rfl

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem ihom_coev_app_hom (A B : Rep k G) :
    ((ihom.coev A).app B).hom.toLinearMap = (TensorProduct.mk k _ _).flip :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

/-- There is a `k`-linear isomorphism between the sets of representation morphisms `Hom(A ⊗ B, C)`
and `Hom(B, Homₖ(A, C))`. -/
def MonoidalClosed.linearHomEquiv (A B C : Rep.{u} k G) : (A ⊗ B ⟶ C) ≃ₗ[k] B ⟶ A ⟶[Rep k G] C :=
  { (ihom.adjunction A).homEquiv _ _ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- There is a `k`-linear isomorphism between the sets of representation morphisms `Hom(A ⊗ B, C)`
and `Hom(A, Homₖ(B, C))`. -/
def MonoidalClosed.linearHomEquivComm (A B C : Rep.{u} k G) : (A ⊗ B ⟶ C) ≃ₗ[k] A ⟶ B
    ⟶[Rep k G] C :=
  Linear.homCongr k (β_ A B) (Iso.refl _) ≪≫ₗ MonoidalClosed.linearHomEquiv _ _ _

@[simp]
theorem MonoidalClosed.linearHomEquiv_hom (A B C : Rep.{u} k G) (f : A ⊗ B ⟶ C) :
    (MonoidalClosed.linearHomEquiv A B C f).hom.toLinearMap =
    (TensorProduct.curry f.hom.toLinearMap).flip :=
  rfl

@[simp]
theorem MonoidalClosed.linearHomEquivComm_hom (A B C : Rep.{u} k G) (f : A ⊗ B ⟶ C) :
    (MonoidalClosed.linearHomEquivComm A B C f).hom.toLinearMap =
    TensorProduct.curry f.hom.toLinearMap :=
  rfl

theorem MonoidalClosed.linearHomEquiv_symm_hom (A B C : Rep.{u} k G) (f : B ⟶ A ⟶[Rep k G] C) :
    ((MonoidalClosed.linearHomEquiv A B C).symm f).hom.toLinearMap =
      TensorProduct.uncurry (.id k) A B C f.hom.toLinearMap.flip := by
  simp [linearHomEquiv]
  rfl

theorem MonoidalClosed.linearHomEquivComm_symm_hom (A B C : Rep.{u} k G) (f : A ⟶ B ⟶[Rep k G] C) :
    ((MonoidalClosed.linearHomEquivComm A B C).symm f).hom.toLinearMap =
      TensorProduct.uncurry (.id k) A B C f.hom.toLinearMap :=
  TensorProduct.ext' fun _ _ => rfl

end MonoidalClosed

section

variable {k : Type u} [Semiring k] {G : Type v} [Group G] [Fintype G] (A : Rep.{w} k G)

/-- Given a representation `A` of a finite group `G`, `norm A` is the representation morphism
`A ⟶ A` defined by `x ↦ ∑ A.ρ g x` for `g` in `G`. -/
def norm : End A := Rep.ofHom (σ := A.ρ) (ρ := A.ρ) ⟨Representation.norm A.ρ,
    fun g ↦ by ext; simp⟩

@[simp]
lemma norm_apply {x : A} : (norm A).hom x = A.ρ.norm x := rfl

@[reassoc, elementwise]
lemma norm_comm {A B : Rep k G} (f : A ⟶ B) : f ≫ norm B = norm A ≫ f := by
  ext; simp [Representation.norm, hom_comm_apply]

/-- Given a representation `A` of a finite group `G`, the norm map `A ⟶ A` defined by
`x ↦ ∑ A.ρ g x` for `g` in `G` defines a natural endomorphism of the identity functor. -/
@[simps]
def normNatTrans : End (𝟭 (Rep k G)) where
  app := norm
  naturality _ _ := norm_comm

end

noncomputable section Linearization

variable (k G)

noncomputable section Finsupp

open Finsupp

variable (α : Type u') (A : Rep k G)

variable {k G} in
/-- The representation on `α →₀ A` defined pointwise by a representation on `A`. -/
abbrev finsupp : Rep k G :=
  Rep.of (Representation.finsupp A.ρ α)

@[simp] lemma finsupp_V : (finsupp α A).V = (α →₀ A.V) := rfl

/-- The representation on `α →₀ k[G]` defined pointwise by the left regular representation on
`k[G]`. -/
abbrev free : Rep k G := Rep.of (Representation.free k G α)

variable {α}

/-- Given `f : α → A`, the natural representation morphism `(α →₀ k[G]) ⟶ A` sending
`single a (single g r) ↦ r • A.ρ g (f a)`. -/
abbrev freeLift (f : α → A) :
    free k G α ⟶ A := Rep.ofHom (Representation.freeLift A.ρ f)

variable (α) in
/-- The natural linear equivalence between functions `α → A` and representation morphisms
`(α →₀ k[G]) ⟶ A`. -/
abbrev freeLiftLEquiv :
    (free k G α ⟶ A) ≃ₗ[k] (α → A) :=
  homLinearEquiv _ _ ≪≫ₗ Representation.freeLiftLEquiv A.ρ α

lemma free_ext (f g : free k G α ⟶ A)
    (h : ∀ i : α, f.hom (single i (single 1 1)) = g.hom (single i (single 1 1))) : f = g := by
  classical exact (freeLiftLEquiv k G α A).injective (funext_iff.2 h)

variable {A}
section

open MonoidalCategory

variable (A B : Rep.{u} k G) (α : Type u) [DecidableEq α]

open TensorProduct in
/-- Given representations `A, B` and a type `α`, this is the natural representation isomorphism
`(α →₀ A) ⊗ B ≅ (A ⊗ B) →₀ α` sending `single x a ⊗ₜ b ↦ single x (a ⊗ₜ b)`. -/
abbrev finsuppTensorLeft : A.finsupp α ⊗ B ≅ (A ⊗ B).finsupp α :=
  mkIso (Representation.finsuppTensorLeft A.ρ B.ρ α)

/-- Given representations `A, B` and a type `α`, this is the natural representation isomorphism
`A ⊗ (α →₀ B) ≅ (A ⊗ B) →₀ α` sending `a ⊗ₜ single x b ↦ single x (a ⊗ₜ b)`. -/
abbrev finsuppTensorRight : A ⊗ B.finsupp α ≅ (A ⊗ B).finsupp α :=
  mkIso (Representation.finsuppTensorRight A.ρ B.ρ α)

section

variable (k G α : Type u) [DecidableEq α] [CommRing k] [Monoid G]

/-- The natural isomorphism sending `single g r₁ ⊗ single a r₂ ↦ single a (single g r₁r₂)`. -/
abbrev leftRegularTensorTrivialIsoFree :
    leftRegular k G ⊗ trivial k G (α →₀ k) ≅ free k G α :=
  mkIso (Representation.leftRegularTensorTrivialIsoFree α)

end
end
end Finsupp

/-- The monoidal functor sending a type `H` with a `G`-action to the induced `k`-linear
`G`-representation on `k[H].` -/
@[simps]
abbrev linearization : (Action (Type w) G) ⥤ (Rep.{max w u} k G) where
  obj X := Rep.of (X := X.V →₀ k) <| Representation.linearize k G X
  map f := Rep.ofHom <| Representation.linearizeMap f

open MonoidalCategory Representation.LinearizeMonoidal in
instance : (linearization k G).Monoidal where
  ε := ofHom (ε k G)
  μ X Y := ofHom (μ X Y)
  μ_natural_left f Z := hom_ext <| μ_comp_rTensor f Z
  μ_natural_right Z f := by ext1; simp [μ_comp_lTensor _]
  associativity X Y Z := by ext1; simp [μ_comp_assoc _]
  left_unitality X := hom_ext <| μ_leftUnitor X
  right_unitality X := hom_ext <| μ_rightUnitor X
  η := ofHom (η k G)
  δ X Y := ofHom (δ X Y)
  δ_natural_left f Z := hom_ext <| rTensor_comp_δ Z f
  δ_natural_right Z f := hom_ext <| lTensor_comp_δ Z f
  oplax_associativity X Y Z := hom_ext <| assoc_comp_δ X Y Z
  oplax_left_unitality X := hom_ext <| leftUnitor_δ X
  oplax_right_unitality X := hom_ext <| rightUnitor_δ X
  ε_η := hom_ext <| η_ε k G
  η_ε := hom_ext <| ε_η k G
  μ_δ X Y := hom_ext <| δ_μ (k := k) X Y
  δ_μ X Y := hom_ext <| μ_δ (k := k) X Y

variable {k G}

open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

open scoped MonoidalCategory

section

open MonoidalCategory Representation.LinearizeMonoidal

lemma μ_def {X Y : Action (Type u) G} : Functor.LaxMonoidal.μ (linearization k G) X Y =
    ofHom (μ X Y) := rfl

lemma μ_hom {X Y : Action (Type u) G} : (Functor.LaxMonoidal.μ (linearization k G) X Y).hom
    = μ X Y := rfl

lemma ε_def : Functor.LaxMonoidal.ε (linearization k G) = ofHom (ε k G) := rfl

lemma ε_hom : (Functor.LaxMonoidal.ε (linearization k G)).hom = ε k G := rfl

lemma δ_def {X Y : Action (Type u) G} : Functor.OplaxMonoidal.δ (linearization k G) X Y =
    ofHom (δ X Y) := rfl

lemma δ_hom {X Y : Action (Type u) G} : (Functor.OplaxMonoidal.δ (linearization k G) X Y).hom
    = δ X Y := rfl

lemma η_def : Functor.OplaxMonoidal.η (linearization k G) = ofHom (η k G) := rfl

lemma η_hom : (Functor.OplaxMonoidal.η (linearization k G)).hom = η k G := rfl

end

variable (k G) in
/-- The linearization of a type `X` on which `G` acts trivially is the trivial `G`-representation
on `k[X]`. -/
abbrev linearizationTrivialIso (X : Type u) :
    (linearization k G).obj (Action.trivial _ X) ≅ trivial k G (X →₀ k) :=
  Rep.mkIso (Representation.linearizeTrivialIso k G X)

variable (k G) in
/-- The linearization of a type `H` with a `G`-action is definitionally isomorphic to the
`k`-linear `G`-representation on `k[H]` induced by the `G`-action on `H`. -/
abbrev linearizationOfMulActionIso (H : Type u) [MulAction G H] :
    (linearization k G).obj (Action.ofMulAction G H) ≅ ofMulAction k G H :=
  Rep.mkIso (Representation.linearizeOfMulActionIso k G H)

/-- Given a `k`-linear `G`-representation `A`, there is a `k`-linear isomorphism between
representation morphisms `Hom(k[G], A)` and `A`. -/
abbrev leftRegularHomEquiv (A : Rep k G) : (leftRegular k G ⟶ A) ≃ₗ[k] A :=
  homLinearEquiv _ _ ≪≫ₗ Representation.leftRegularMapEquiv A.ρ

theorem leftRegularHomEquiv_symm_single {A : Rep k G} (x : A) (g : G) :
    ((leftRegularHomEquiv A).symm x).hom (.single g 1) = A.ρ g x := by
  simp [homEquiv]

end Linearization

end

end Rep
