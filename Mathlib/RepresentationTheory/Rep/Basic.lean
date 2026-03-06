/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Action.Monoidal
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

universe w u u1 v w'

/-- The category of `k`-linear representations of a monoid `G`. -/
def Rep (k : Type u) (G : Type v) [Ring k] [Monoid G] := Action (ModuleCat.{w, u} k) G

suppress_compilation

attribute [local simp] ModuleCat.MonoidalCategory.tensorObj_carrier

namespace Rep

section non_comm

variable {k : Type u} {G : Type v} [Ring k] [Monoid G]

def Hom {k : Type u} {G : Type v} [Ring k] [Monoid G] (A B : Rep k G) : Type w := Action.Hom A B

instance (k : Type u) (G : Type v) [Ring k] [Monoid G] : Category (Rep k G) where
  Hom := Rep.Hom
  __ := inferInstanceAs (Category (Action (ModuleCat.{w, u} k) G))

abbrev V {k : Type u} {G : Type v} [Ring k] [Monoid G] (A : Rep k G) : ModuleCat k := Action.V A

instance : CoeSort (Rep.{w} k G) (Type _) := ⟨fun V => V.V⟩

def ρ (A : Rep k G) : Representation k G A.V :=
  (ModuleCat.endRingEquiv A.V).toMonoidHom.comp (Action.ρ A)

instance : ConcreteCategory (Rep k G) (fun A B ↦ A.ρ.IntertwiningMap B.ρ) where
  hom f :=
  { __ := (Action.Hom.hom f).hom
    isIntertwining' g := ModuleCat.hom_ext_iff.1 (f.comm g)}
  ofHom f :=
  { hom := ModuleCat.ofHom f.toLinearMap
    comm g := ModuleCat.hom_ext <| f.2 g }

abbrev Hom.hom {A B : Rep k G} (f : A ⟶ B) : A.ρ.IntertwiningMap B.ρ :=
  ConcreteCategory.hom (C := Rep k G) f

abbrev of {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k G V) : Rep k G :=
  ⟨ModuleCat.of k V, (ModuleCat.endRingEquiv _).symm.toMonoidHom.comp ρ⟩

-- Ensure the roundtrips are reducibly defeq (so tactics like `rw` can see through them).
example {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k G V) :
    (of ρ : Type w) = V := by with_reducible rfl

abbrev ofHom {A B : Type w} [AddCommGroup A] [AddCommGroup B] [Module k A] [Module k B]
    {σ : Representation k G A} {ρ : Representation k G B} (f : σ.IntertwiningMap ρ) :
    Rep.of σ ⟶ Rep.of ρ := ConcreteCategory.ofHom (C := Rep k G) f

@[simp]
lemma coe_of {V : Type w} [AddCommGroup V] [Module k V] (ρ : G →* V →ₗ[k] V) :
    (of ρ : Type w) = V := rfl

@[simp]
theorem of_ρ {V : Type w} [AddCommGroup V] [Module k V] (ρ : G →* V →ₗ[k] V) : (of ρ).ρ = ρ :=
  rfl

@[simp]
lemma of_V {V : Type w} [AddCommGroup V] [Module k V] (ρ : G →* V →ₗ[k] V) : (of ρ).V = V := rfl

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
  simp [Representation.IntertwiningMap.id]

@[simp]
lemma ofHom_hom {M N : Rep k G} (f : M ⟶ N) :
    Rep.ofHom f.hom = f := rfl

@[ext]
lemma hom_ext {M N : Rep k G} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  ConcreteCategory.ext hf

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
  forget₂ :=
  { obj A := A.V
    map f := f.toModuleCatHom}

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

@[simp]
lemma hom_comp {M N O : Rep k G} (f : M ⟶ N) (g : N ⟶ O) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

lemma hom_comp_toLinearMap {M N O : Rep k G} (f : M ⟶ N) (g : N ⟶ O) :
    (f ≫ g).hom.toLinearMap = g.hom.toLinearMap ∘ₗ f.hom.toLinearMap := rfl

/- Provided for rewriting. -/
lemma comp_apply {M N O : Rep k G} (f : M ⟶ N) (g : N ⟶ O) (x : M) :
    (f ≫ g) x = g (f x) := by rfl

lemma add_comp {M N O : Rep k G} (f₁ f₂ : M ⟶ N) (g : N ⟶ O) :
    (f₁ + f₂) ≫ g = f₁ ≫ g + f₂ ≫ g := by
  ext1
  simp [add_hom, Representation.IntertwiningMap.add_comp]

lemma comp_add {M N O : Rep k G} (f : M ⟶ N) (g₁ g₂ : N ⟶ O) :
    f ≫ (g₁ + g₂) = f ≫ g₁ + f ≫ g₂ := by
  ext1
  simp [add_hom, Representation.IntertwiningMap.comp_add]

instance {M N : Rep k G} : Zero (M ⟶ N) where
  zero := ofHom (0 : M.ρ.IntertwiningMap N.ρ)

lemma ofHom_zero {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    {σ : Representation k G M} {ρ : Representation k G N} :
    ofHom (0 : σ.IntertwiningMap ρ) = 0 := rfl

lemma zero_hom {M N : Rep k G} : (0 : M ⟶ N).hom = 0 := rfl

instance {M N : Rep k G} : SMul ℕ (M ⟶ N) where
  smul n f := ofHom (n • f.hom)

@[simp]
lemma ofHom_comp {M N O : Type w} [AddCommGroup M] [AddCommGroup N] [AddCommGroup O] [Module k M]
    [Module k N] [Module k O] {σ : Representation k G M} {ρ : Representation k G N}
    {τ : Representation k G O} (f : σ.IntertwiningMap ρ) (g : ρ.IntertwiningMap τ) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

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

instance : (forget₂ (Rep k G) (ModuleCat k)).Additive :=
  inferInstanceAs (Action.forget (ModuleCat k) G).Additive

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
  out := Representation.isTrivial_def ρ

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

variable (A : Rep k G)

/-- Given a `k`-linear `G`-representation `(V, ρ)`, this is the representation defined by
restricting `ρ` to a `G`-invariant `k`-submodule of `V`. -/
abbrev subrepresentation (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    Rep k G :=
  Rep.of (A.ρ.subrepresentation W le_comap)

/-- The natural inclusion of a subrepresentation into the ambient representation. -/
@[simps]
def subtype (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    subrepresentation A W le_comap ⟶ A where
  hom := ModuleCat.ofHom W.subtype
  comm _ := rfl

/-- Given a `k`-linear `G`-representation `(V, ρ)` and a `G`-invariant `k`-submodule `W ≤ V`, this
is the representation induced on `V ⧸ W` by `ρ`. -/
abbrev quotient (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    Rep k G :=
  Rep.of (A.ρ.quotient W le_comap)

/-- The natural projection from a representation to its quotient by a subrepresentation. -/
@[simps]
def mkQ (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    A ⟶ quotient A W le_comap where
  hom := ModuleCat.ofHom <| Submodule.mkQ _
  comm _ := rfl

end Commutative

theorem epi_iff_surjective {A B : Rep k G} (f : A ⟶ B) : Epi f ↔ Function.Surjective f.hom :=
  ⟨fun _ => (ModuleCat.epi_iff_surjective ((forget₂ _ _).map f)).1 inferInstance,
  fun h => (forget₂ _ _).epi_of_epi_map ((ModuleCat.epi_iff_surjective <|
    (forget₂ _ _).map f).2 h)⟩

theorem mono_iff_injective {A B : Rep k G} (f : A ⟶ B) : Mono f ↔ Function.Injective f.hom :=
  ⟨fun _ => (ModuleCat.mono_iff_injective ((forget₂ _ _).map f)).1 inferInstance,
  fun h => (forget₂ _ _).mono_of_mono_map ((ModuleCat.mono_iff_injective <|
    (forget₂ _ _).map f).2 h)⟩

instance {A B : Rep k G} (f : A ⟶ B) [Mono f] : Mono f.toModuleCatHom :=
  inferInstanceAs <| Mono ((forget₂ _ _).map f)

instance {A B : Rep k G} (f : A ⟶ B) [Epi f] : Epi f.toModuleCatHom :=
  inferInstanceAs <| Epi ((forget₂ _ _).map f)

variable (k G)

/-- Given a `G`-action on `H`, this is `k[H]` bundled with the natural representation
`G →* End(k[H])` as a term of type `Rep k G`. -/
def ofMulAction (H : Type w') [MulAction G H] : Rep k G :=
  of <| Representation.ofMulAction k G H

def ofMulAction.equivFinsupp (H : Type w') [MulAction G H] :
  ofMulAction k G H ≃ₗ[k] (H →₀ k) := .refl _ _

variable {k} in
def ofMulAction.single {H : Type w'} [MulAction G H] (g : H) :
    k →ₗ[k] ofMulAction k G H := Finsupp.lsingle g

lemma ofMulAction.single_def {H : Type w'} [MulAction G H] (g : H) (x : k) :
    ofMulAction.single G g x = Finsupp.single g x := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma ofMulAction.ρ_single (H : Type w') [MulAction G H] (g : G) (h : H) (x : k) :
    (ofMulAction k G H).ρ g (ofMulAction.single G h x) = ofMulAction.single G (g • h) x := by
  simp [ofMulAction, ofMulAction.single]

@[simp]
lemma ofMulAction.ρ_comp_single (H : Type w') [MulAction G H] (g : G) (h : H) :
    (ofMulAction k G H).ρ g ∘ₗ ofMulAction.single G h = ofMulAction.single G (g • h) :=
  LinearMap.ext (by simp)

@[simp]
lemma ofMulAction.equivFinsupp_single (H : Type w') [MulAction G H] (h : H) (x : k) :
    ofMulAction.equivFinsupp k G H (ofMulAction.single G h x) = .single h x := rfl

@[simp]
lemma ofMulAction.equivFinsupp_symm_single (H : Type w') [MulAction G H] (h : H) (x : k) :
    (ofMulAction.equivFinsupp k G H).symm (.single h x) = ofMulAction.single G h x := rfl

@[ext high]
lemma ofMulAction.hom_ext {H : Type w'} [MulAction G H]
    {M : Type*} [AddCommGroup M] [Module k M]
    (l₁ l₂ : ofMulAction k G H →ₗ[k] M) (heq : ∀ g, l₁ ∘ₗ single G g = l₂ ∘ₗ single G g) :
    l₁ = l₂ := Finsupp.lhom_ext' heq

/-- The `k`-linear `G`-representation on `k[G]`, induced by left multiplication. -/
abbrev leftRegular : Rep k G :=
  ofMulAction k G G

/-- The `k`-linear `G`-representation on `k[Gⁿ]`, induced by left multiplication. -/
abbrev diagonal (n : ℕ) : Rep k G :=
  ofMulAction k G (Fin n → G)

set_option backward.isDefEq.respectTransparency false in
variable {k G} in
@[simps]
def mkIso (M₁ M₂ : Rep.{w} k G) (f : M₁.V ≃ₗ[k] M₂.V) (hf : ∀ g : G, f ∘ₗ M₁.ρ g =
    M₂.ρ g ∘ₗ f := by aesop) : M₁ ≅ M₂ where
  hom := ofHom (σ := M₁.ρ) (ρ := M₂.ρ) ⟨f, fun g ↦ congr($(hf g))⟩
  inv := ofHom (σ := M₂.ρ) (ρ := M₁.ρ) ⟨f.symm, fun g ↦ by
    rw [← LinearMap.cancel_left f.injective, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc,
      hf g, LinearEquiv.comp_symm, LinearMap.id_comp, LinearMap.comp_assoc,
      LinearEquiv.comp_symm, LinearMap.comp_id]⟩

/-- The natural isomorphism between the representations on `k[G¹]` and `k[G]` induced by left
multiplication in `G`. -/
@[simps! hom_hom inv_hom]
def diagonalOneIsoLeftRegular :
    diagonal k G 1 ≅ leftRegular k G :=
  Rep.mkIso (diagonal k G 1) (leftRegular k G) (ofMulAction.equivFinsupp _ _ _ ≪≫ₗ
    Finsupp.domLCongr (Equiv.funUnique (Fin 1) G) ≪≫ₗ (ofMulAction.equivFinsupp _ _ _).symm)
    fun g ↦ by ext; simp

set_option backward.isDefEq.respectTransparency false in
/-- When `H = {1}`, the `G`-representation on `k[H]` induced by an action of `G` on `H` is
isomorphic to the trivial representation on `k`. -/
@[simps! hom_hom inv_hom]
def ofMulActionSubsingletonIsoTrivial
    (H : Type u) [Subsingleton H] [MulOneClass H] [MulAction G H] :
    ofMulAction k G H ≅ trivial k G k :=
  letI : Unique H := uniqueOfSubsingleton 1
  mkIso _ _ (ofMulAction.equivFinsupp _ _ _ ≪≫ₗ Finsupp.LinearEquiv.finsuppUnique _ _ _) fun g ↦ by
  ext x; simp [Subsingleton.elim (g • x) x]

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

set_option backward.isDefEq.respectTransparency false in
/-- Given an element `x : A`, there is a natural morphism of representations `k[G] ⟶ A` sending
`g ↦ A.ρ(g)(x).` -/
def leftRegularHom (A : Rep k G) (x : A) : leftRegular k G ⟶ A :=
  Rep.ofHom (σ := (leftRegular k G).ρ) (ρ := A.ρ) ⟨(Finsupp.lift A k G fun g ↦ A.ρ g x) ∘ₗ
    (ofMulAction.equivFinsupp k G G).toLinearMap, fun g ↦ by ext; simp⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem leftRegularHom_hom_single {A : Rep k G} (g : G) (x : A) (r : k) :
    (leftRegularHom A x).hom (ofMulAction.single G g r) = r • A.ρ g x := by
  simp [leftRegularHom]

end non_comm

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

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
  ext1
  simp [smul_hom, Representation.IntertwiningMap.smul_comp]

instance : Linear k (Rep k G) where
  homModule X Y := hom_injective.module _ ⟨⟨_, zero_hom⟩, add_hom⟩ <| by simp [smul_hom]
  smul_comp _ _ _ := smul_comp
  comp_smul _ _ _ := comp_smul

section Monoidal

open MonoidalCategory

noncomputable
instance : MonoidalCategory (Rep.{u} k G) where
  tensorObj ρ σ := Rep.of (ρ.ρ.tprod σ.ρ)
  __ := Action.instMonoidalCategory

@[simp]
theorem tensor_ρ {A B : Rep k G} : (A ⊗ B).ρ = A.ρ.tprod B.ρ := rfl

@[simp]
lemma tensor_V {A B : Rep k G} : (A ⊗ B).V = A.V ⊗ B.V := rfl

@[simp]
lemma tensorUnit_ρ_apply {g : G} : (𝟙_ (Rep k G)).ρ g = LinearMap.id := rfl

instance : Functor.Linear k (forget₂ (Rep k G) (ModuleCat k)) :=
  inferInstanceAs <| Functor.Linear k (Action.forget (ModuleCat k) G)

instance : (forget₂ (Rep k G) (ModuleCat k)).Monoidal := Action.instMonoidalForget (ModuleCat k) G

instance : BraidedCategory (Rep k G) := Action.instBraidedCategory (ModuleCat k) G

instance : SymmetricCategory (Rep k G) := Action.instSymmetricCategory (ModuleCat k) G

instance : MonoidalPreadditive (Rep k G) := Action.instMonoidalPreadditive (ModuleCat k) G

instance : MonoidalLinear k (Rep k G) := Action.instMonoidalLinear (ModuleCat k) G

lemma β_hom_hom {A B : Rep k G} : (β_ A B).hom.toModuleCatHom = (β_ A.V B.V).hom := rfl

@[simp]
lemma β_hom_toLinearMap {A B : Rep k G} :
    (β_ A B).hom.hom.toLinearMap = (TensorProduct.comm k A.V B.V).toLinearMap := rfl

lemma β_inv_hom {A B : Rep k G} : (β_ A B).inv.toModuleCatHom = (β_ A.V B.V).inv := rfl

@[simp]
lemma β_inv_toLinearMap {A B : Rep k G} :
    (β_ A B).inv.hom.toLinearMap = (TensorProduct.comm k B.V A.V).toLinearMap := rfl

@[simp]
lemma hom_tensorHom {A₁ A₂ B₁ B₂ : Rep.{u} k G} (f₁ : A₁ ⟶ A₂) (f₂ : B₁ ⟶ B₂) :
    (f₁ ⊗ₘ f₂).hom = f₁.hom.tensor f₂.hom := rfl

@[simp]
lemma hom_whiskerRIght {A₁ A₂ B : Rep.{u} k G} (f : A₁ ⟶ A₂) :
    (f ▷ B).hom = f.hom.rTensor _ := rfl

@[simp]
lemma hom_whiskerLeft {A B₁ B₂ : Rep.{u} k G} (f : B₁ ⟶ B₂) :
    (A ◁ f).hom = f.hom.lTensor _ := rfl

end Monoidal

section

variable {G : Type v} [Group G] [Fintype G] (A : Rep.{w} k G)

set_option backward.isDefEq.respectTransparency false in
/-- Given a representation `A` of a finite group `G`, `norm A` is the representation morphism
`A ⟶ A` defined by `x ↦ ∑ A.ρ g x` for `g` in `G`. -/
def norm : End A := Rep.ofHom (σ := A.ρ) (ρ := A.ρ) ⟨Representation.norm A.ρ,
    fun g ↦ by ext; simp⟩

@[simp]
lemma norm_apply {x : A} : (norm A).hom x = A.ρ.norm x := rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc, elementwise]
lemma norm_comm {A B : Rep k G} (f : A ⟶ B) : f ≫ norm B = norm A ≫ f := by
  ext
  simp [Representation.norm, hom_comm_apply]

/-- Given a representation `A` of a finite group `G`, the norm map `A ⟶ A` defined by
`x ↦ ∑ A.ρ g x` for `g` in `G` defines a natural endomorphism of the identity functor. -/
@[simps]
def normNatTrans : End (𝟭 (Rep k G)) where
  app := norm
  naturality _ _ := norm_comm

end

namespace Representation
open MonoidalCategory
variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]
    {V W : Type u} [AddCommGroup V] [AddCommGroup W]
    [Module k V] [Module k W] (ρ : Representation k G V) (τ : Representation k G W)

/-- Tautological isomorphism to help Lean in typechecking. -/
noncomputable def repOfTprodIso : Rep.of (ρ.tprod τ) ≅ Rep.of ρ ⊗ Rep.of τ :=
  Iso.refl _

theorem repOfTprodIso_apply (x : TensorProduct k V W) : (repOfTprodIso ρ τ).hom.hom x = x :=
  rfl

theorem repOfTprodIso_inv_apply (x : TensorProduct k V W) : (repOfTprodIso ρ τ).inv.hom x = x :=
  rfl

end Representation

section MonoidalClosed
open MonoidalCategory Action

variable {G : Type v} [Group G] (A B C : Rep.{w} k G)

set_option backward.isDefEq.respectTransparency false in
/-- Given a `k`-linear `G`-representation `(A, ρ₁)`, this is the 'internal Hom' functor sending
`(B, ρ₂)` to the representation `Homₖ(A, B)` that maps `g : G` and `f : A →ₗ[k] B` to
`(ρ₂ g) ∘ₗ f ∘ₗ (ρ₁ g⁻¹)`. -/
@[simps]
protected noncomputable def ihom (A : Rep k G) : Rep k G ⥤ Rep k G where
  obj B := Rep.of (Representation.linHom A.ρ B.ρ)
  map {X} {Y} f := Rep.ofHom ⟨LinearMap.llcomp k _ _ _ f.hom.toLinearMap, fun g ↦ by
    ext; simp [← hom_comm_apply]⟩
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
  toFun f := Rep.ofHom (σ := B.ρ) ⟨(TensorProduct.curry f.hom.toLinearMap).flip, fun g ↦ by
    ext x y
    simp only [tensor_V, ModuleCat.MonoidalCategory.tensorObj_carrier, tensor_ρ, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.flip_apply, TensorProduct.curry_apply, toLinearMap_apply,
      Representation.linHom_apply]
    have := by simpa using (hom_comm_apply f g (A.ρ g⁻¹ y ⊗ₜ[k] x)).symm
    simp [this]⟩
  invFun f := Rep.ofHom (σ := (A ⊗ B).ρ) (ρ := C.ρ) ⟨TensorProduct.uncurry (.id k) _ _ _
    f.hom.toLinearMap.flip, fun g ↦ TensorProduct.ext' fun x y => by
    -- simpa using LinearMap.ext_iff.1 (hom_comm_apply f g y) (A.ρ g x)
    simp
    -- erw? [toLinearMap_apply]
    sorry
    ⟩
  left_inv _ := Action.Hom.ext (ModuleCat.hom_ext <| TensorProduct.ext' fun _ _ => rfl)

variable {A B C}

noncomputable instance : MonoidalClosed (Rep k G) where
  closed A :=
    { rightAdj := Rep.ihom A
      adj := Adjunction.mkOfHomEquiv ({
        homEquiv := Rep.tensorHomEquiv A
        homEquiv_naturality_left_symm := fun _ _ => Action.Hom.ext
          (ModuleCat.hom_ext (TensorProduct.ext' fun _ _ => rfl))
        homEquiv_naturality_right := fun _ _ => Action.Hom.ext (ModuleCat.hom_ext (LinearMap.ext
          fun _ => LinearMap.ext fun _ => rfl)) }) }

@[simp]
theorem ihom_obj_ρ_def (A B : Rep k G) : ((ihom A).obj B).ρ = ((Rep.ihom A).obj B).ρ :=
  rfl

@[simp]
theorem homEquiv_def (A B C : Rep k G) : (ihom.adjunction A).homEquiv B C =
    Rep.tensorHomEquiv A B C :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _

@[simp]
theorem ihom_ev_app_hom (A B : Rep k G) :
    Action.Hom.hom ((ihom.ev A).app B) = ModuleCat.ofHom
      (TensorProduct.uncurry (.id k) A (A →ₗ[k] B) B LinearMap.id.flip) := by
  ext; rfl

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem ihom_coev_app_hom (A B : Rep k G) :
    Action.Hom.hom ((ihom.coev A).app B) = ModuleCat.ofHom (TensorProduct.mk k _ _).flip :=
  ModuleCat.hom_ext <| LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

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

set_option backward.isDefEq.respectTransparency false in
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

noncomputable section Linearization

variable (k G)

/-- The monoidal functor sending a type `H` with a `G`-action to the induced `k`-linear
`G`-representation on `k[H].` -/
def linearization : (Action (Type u) G) ⥤ (Rep k G) :=
  Functor.mapAction (ModuleCat.free k) G

instance : (linearization k G).Monoidal := by
  dsimp only [linearization]
  exact Functor.instMonoidalActionMapAction _

variable {k G}

def linearizationSingle (X : Action (Type u) G) (x : X.V) :
    k →ₗ[k] (linearization k G).obj X := Finsupp.lsingle x

def linearizationObjEquiv (X : Action (Type u) G) :
    ((linearization k G).obj X).V ≃ₗ[k] (X.V →₀ k) := .refl _ _

@[simp]
lemma linearizationObjEquiv_single (X : Action (Type u) G) (x : X.V) (r : k) :
    linearizationObjEquiv X (linearizationSingle X x r) = Finsupp.single x r := rfl

@[simp]
lemma linearizationObjEquiv_symm_single (X : Action (Type u) G) (x : X.V) (r : k) :
    (linearizationObjEquiv X).symm (Finsupp.single x r) = linearizationSingle X x r := rfl

@[ext high]
lemma linearizationObj_ext {M : Type*} [AddCommGroup M] [Module k M] (X : Action (Type u) G)
    {f1 f2 : (linearization k G).obj X →ₗ[k] M} (h : ∀ x, f1 ∘ₗ linearizationSingle X x =
    f2 ∘ₗ linearizationSingle X x) : f1 = f2 :=
  Finsupp.lhom_ext' h

theorem linearization_obj_ρ (X : Action (Type u) G) (g : G) :
    ((linearization k G).obj X).ρ g = Finsupp.lmapDomain k k (X.ρ g) :=
  rfl

@[simp]
theorem coe_linearization_obj_ρ (X : Action (Type u) G) (g : G) :
    @DFunLike.coe (no_index G →* ((X.V →₀ k) →ₗ[k] (X.V →₀ k))) _
      (fun _ => (X.V →₀ k) →ₗ[k] (X.V →₀ k)) _
      ((linearization k G).obj X).ρ g = Finsupp.lmapDomain k k (X.ρ g) := rfl

@[simp]
theorem linearization_single (X : Action (Type u) G) (g : G) (x : X.V) (y : k) :
    ((linearization k G).obj X).ρ g (linearizationSingle X x y) =
      linearizationSingle X (X.ρ g x) y :=
  Finsupp.mapDomain_single ..

set_option backward.isDefEq.respectTransparency false in
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): helps fixing `linearizationTrivialIso` since change in behaviour of `ext`.
theorem linearization_comp_single (X : Action (Type u) G) (g : G) (x : X.V) :
    (((linearization k G).obj X).ρ g) ∘ₗ (linearizationSingle X x) =
      linearizationSingle X (X.ρ g x) :=
  LinearMap.ext <| linearization_single X g x

variable {X Y : Action (Type u) G} (f : X ⟶ Y)

-- @[simp]
theorem linearization_map_hom : ((linearization k G).map f).hom.toLinearMap =
    Finsupp.lmapDomain k k f.hom :=
  rfl

@[simp]
lemma linearization_map_hom_single (x : X.V) (r : k) :
    ((linearization k G).map f).hom (linearizationSingle _ x r) =
    linearizationSingle _ (f.hom x) r :=
  Finsupp.mapDomain_single

open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

@[simp]
theorem linearization_μ_hom (X Y : Action (Type u) G) :
    (μ (linearization k G) X Y).hom.toLinearMap =
      (linearizationObjEquiv _).symm.toLinearMap ∘ₗ
      (finsuppTensorFinsupp' k X.V Y.V).toLinearMap ∘ₗ
      (TensorProduct.congr (linearizationObjEquiv X) (linearizationObjEquiv Y)).toLinearMap := by
  convert (LinearMap.id_comp _).symm using 1
  congr 1
  convert_to (finsuppTensorFinsupp' k X.V Y.V).toLinearMap ∘ₗ LinearMap.id =
    (Hom.hom (μ (linearization k G) X Y)).toLinearMap using 1
  · congr 1
    exact congr(($(TensorProduct.congr_refl_refl ..)).toLinearMap)
  rfl

open TensorProduct in
@[simp]
lemma linearization_μ_apply (X Y : Action (Type u) G)
    (x : ((linearization k G).obj X).V ⊗[k] ((linearization k G).obj Y).V) :
    (μ (linearization k G) X Y).hom x =
      (linearizationObjEquiv _).symm.toLinearMap
      ((finsuppTensorFinsupp' k X.V Y.V).toLinearMap ((TensorProduct.congr (linearizationObjEquiv X)
        (linearizationObjEquiv Y)).toLinearMap x)) :=
  congr($(linearization_μ_hom X Y) x)

@[simp]
theorem linearization_δ_hom (X Y : Action (Type u) G) :
    (δ (linearization k G) X Y).hom.toLinearMap =
      (TensorProduct.congr (linearizationObjEquiv _) (linearizationObjEquiv _)).symm.toLinearMap ∘ₗ
      (finsuppTensorFinsupp' k X.V Y.V).symm.toLinearMap ∘ₗ
      (linearizationObjEquiv _).toLinearMap := by
  convert (LinearMap.id_comp _).symm using 1
  congr
  exact congr(($(TensorProduct.congr_refl_refl ..)).toLinearMap)

@[simp]
theorem linearization_δ_apply (X Y : Action (Type u) G) (x) :
    (δ (linearization k G) X Y).hom x =
      (TensorProduct.congr (linearizationObjEquiv _) (linearizationObjEquiv _)).symm.toLinearMap
      ((finsuppTensorFinsupp' k X.V Y.V).symm.toLinearMap ((linearizationObjEquiv _ x))) :=
  congr($(linearization_δ_hom X Y) x)

@[simp]
theorem linearization_ε_hom : (ε (linearization k G)).hom.toLinearMap =
    linearizationSingle _ PUnit.unit :=
  rfl

theorem linearization_η_hom_apply (r : k) :
    (η (linearization k G)).hom (Finsupp.single PUnit.unit r) = r :=
  (εIso (linearization k G)).hom_inv_id_apply r

variable (k G) in
/-- The linearization of a type `X` on which `G` acts trivially is the trivial `G`-representation
on `k[X]`. -/
@[simps! hom_hom inv_hom]
def linearizationTrivialIso (X : Type u) :
    (linearization k G).obj (Action.trivial _ X) ≅ trivial k G (X →₀ k) :=
  Rep.mkIso _ _ (linearizationObjEquiv (Action.mk X 1)) fun g => by
  rw [Rep.trivial_def, LinearMap.id_comp]
  convert_to LinearMap.id ∘ₗ _ = LinearMap.id
  simp only [LinearMap.id_comp]
  exact Finsupp.lmapDomain_id k k

@[simp]
lemma linearizationTrivialIso_hom_single (X : Type u) (x : X) (r : k) :
    (linearizationTrivialIso k G X).hom.hom (linearizationSingle _ x r) = Finsupp.single x r := rfl

@[simp]
lemma linearizationTrivialIso_inv_single (X : Type u) (x : X) (r : k) :
    (linearizationTrivialIso k G X).inv.hom (Finsupp.single x r) = linearizationSingle _ x r := rfl

/-- The linearization of a type `H` with a `G`-action is definitionally isomorphic to the
`k`-linear `G`-representation on `k[H]` induced by the `G`-action on `H`. -/
def linearizationOfMulActionIso (H : Type _) [MulAction G H] :
    (linearization k G).obj (Action.ofMulAction G H) ≅ ofMulAction k G H :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-- Given a `k`-linear `G`-representation `A`, there is a `k`-linear isomorphism between
representation morphisms `Hom(k[G], A)` and `A`. -/
@[simps]
def leftRegularHomEquiv (A : Rep k G) : (leftRegular k G ⟶ A) ≃ₗ[k] A where
  toFun f := f.hom (ofMulAction.single G 1 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := leftRegularHom A x
  left_inv f := by
    ext; simp [← hom_comm_apply f]
  right_inv x := by simp

set_option backward.isDefEq.respectTransparency false in
theorem leftRegularHomEquiv_symm_single {A : Rep k G} (x : A) (g : G) :
    ((leftRegularHomEquiv A).symm x).hom (ofMulAction.single G g 1) = A.ρ g x := by
  simp

end Linearization


noncomputable section Finsupp

open Finsupp

variable (α : Type u1) (A : Rep k G)

/-- The representation on `α →₀ A` defined pointwise by a representation on `A`. -/
abbrev finsupp : Rep k G :=
  Rep.of (Representation.finsupp A.ρ α)

@[simp] lemma finsupp_V : (finsupp α A).V = (α →₀ A.V) := rfl

set_option backward.isDefEq.respectTransparency false in
variable (k G) in
/-- The representation on `α →₀ k[G]` defined pointwise by the left regular representation on
`k[G]`. -/
def free : Rep k G :=
  Rep.of (V := (α →₀ G →₀ k)) (Representation.free k G α)

def free.single (i : α) : (G →₀ k) →ₗ[k] free k G α := Finsupp.lsingle i

lemma free.single_def (i : α) (f : G →₀ k) :
    free.single α i f = Finsupp.single i f := rfl

variable (k G) in
def freeEquivFinsupp : free k G α ≃ₗ[k] (α →₀ G →₀ k) := .refl _ _

@[simp]
lemma freeEquivFinsupp_single (i : α) (g : G) (r : k) :
    freeEquivFinsupp k G α (free.single α i (Finsupp.single g r)) =
    Finsupp.single i (Finsupp.single g r) := rfl

@[simp]
lemma freeEquivFinsupp_symm_single (i : α) (g : G) (r : k) :
    (freeEquivFinsupp k G α).symm (Finsupp.single i (Finsupp.single g r)) =
    free.single α i (Finsupp.single g r) := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma free.ρ_single (i : α) (g g' : G) (r : k) :
    (free k G α).ρ g' (free.single α i (Finsupp.single g r)) =
    free.single α i (Finsupp.single (g' * g) r) := by
  simp [free, free.single]

lemma free.single_single (i : α) (g : G) (r : k) :
    free.single α i (Finsupp.single g r) = (freeEquivFinsupp k G α).symm
    (Finsupp.single i (Finsupp.single g r)) := rfl

lemma freeEquivFinsupp_comp_single (i : α) :
    (freeEquivFinsupp k G α).toLinearMap ∘ₗ free.single α i = Finsupp.lsingle i := by
  ext; simp

@[ext high]
lemma free_ext {M : Type*} [AddCommGroup M] [Module k M] {f1 f2 : free k G α →ₗ[k] M}
    (h : ∀ i, f1 ∘ₗ (free.single α i) = f2 ∘ₗ (free.single α i)) : f1 = f2 :=
  Finsupp.lhom_ext' h

variable {α}

set_option backward.isDefEq.respectTransparency false in
/-- Given `f : α → A`, the natural representation morphism `(α →₀ k[G]) ⟶ A` sending
`single a (single g r) ↦ r • A.ρ g (f a)`. -/
-- @[simps]
def freeLift (f : α → A) :
    free k G α ⟶ A := Rep.ofHom (σ := (free k G α).ρ) (ρ := A.ρ)
  ⟨linearCombination k (fun x => A.ρ x.2 (f x.1)) ∘ₗ (curryLinearEquiv k).symm.toLinearMap ∘ₗ
    freeEquivFinsupp k G α, fun g ↦ by ext; simp ⟩

set_option backward.isDefEq.respectTransparency false in
variable {A} in
@[simp]
lemma freeLift_hom_single_single (f : α → A) (i : α) (g : G) (r : k) :
    (freeLift A f).hom (free.single α i (single g r)) = r • A.ρ g (f i) := by
  simp [freeLift]

set_option backward.isDefEq.respectTransparency false in
variable (α) in
/-- The natural linear equivalence between functions `α → A` and representation morphisms
`(α →₀ k[G]) ⟶ A`. -/
@[simps]
def freeLiftLEquiv :
    (free k G α ⟶ A) ≃ₗ[k] (α → A) where
  toFun f i := f.hom (free.single _ i (single 1 1))
  invFun := freeLift A
  left_inv x := by ext; simp [← hom_comm_apply]
  right_inv _ := by ext; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {A}
section

open MonoidalCategory

variable (A B : Rep.{u} k G) (α : Type u) [DecidableEq α]

open ModuleCat.MonoidalCategory

set_option backward.isDefEq.respectTransparency false in
-- set_option pp.all true in
open TensorProduct in
-- the proof below can be simplified after https://github.com/leanprover-community/mathlib4/issues/24823 is merged
/-- Given representations `A, B` and a type `α`, this is the natural representation isomorphism
`(α →₀ A) ⊗ B ≅ (A ⊗ B) →₀ α` sending `single x a ⊗ₜ b ↦ single x (a ⊗ₜ b)`. -/
@[simps! hom_hom inv_hom]
def finsuppTensorLeft :
    A.finsupp α ⊗ B ≅ (A ⊗ B).finsupp α :=
  Rep.mkIso _ _ (TensorProduct.finsuppLeft k _ A B α) fun g ↦ by
    dsimp [tensorObj_carrier]
    ext
    simp [finsuppLeft_apply_tmul]

set_option backward.isDefEq.respectTransparency false in
/-- Given representations `A, B` and a type `α`, this is the natural representation isomorphism
`A ⊗ (α →₀ B) ≅ (A ⊗ B) →₀ α` sending `a ⊗ₜ single x b ↦ single x (a ⊗ₜ b)`. -/
@[simps! hom_hom inv_hom]
def finsuppTensorRight :
    A ⊗ B.finsupp α ≅ (A ⊗ B).finsupp α :=
  Rep.mkIso _ _ (TensorProduct.finsuppRight k _ A B α) fun _ => by
    dsimp
    ext
    simp

section

variable (k G α : Type u) [CommRing k] [Monoid G]

set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism sending `single g r₁ ⊗ single a r₂ ↦ single a (single g r₁r₂)`. -/
@[simps! -isSimp hom_hom inv_hom]
def leftRegularTensorTrivialIsoFree :
    leftRegular k G ⊗ trivial k G (α →₀ k) ≅ free k G α :=
  Rep.mkIso _ _ (TensorProduct.congr (ofMulAction.equivFinsupp k G G) (.refl k _) ≪≫ₗ
    finsuppTensorFinsupp' k G α ≪≫ₗ Finsupp.domLCongr (Equiv.prodComm G α) ≪≫ₗ
    curryLinearEquiv k ≪≫ₗ (freeEquivFinsupp k G α).symm) fun g ↦ by
  dsimp; ext; simp

variable {α}

-- omit [DecidableEq α]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma leftRegularTensorTrivialIsoFree_hom_hom_single_tmul_single (i : α) (g : G) (r s : k) :
    (leftRegularTensorTrivialIsoFree k G α).hom.hom.toLinearMap
      (ofMulAction.single G g r ⊗ₜ[k] single i s) =
      free.single α i (single g (r * s)) := by
  simp [leftRegularTensorTrivialIsoFree]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma leftRegularTensorTrivialIsoFree_inv_hom_single_single (i : α) (g : G) (r : k) :
    (leftRegularTensorTrivialIsoFree k G α).inv.hom.toLinearMap (free.single α i (single g r)) =
      ofMulAction.single G g r ⊗ₜ[k] single i 1 := by
  dsimp
  suffices ofMulAction.single G g 1 ⊗ₜ[k] single i r = ofMulAction.single G g r ⊗ₜ[k] single i 1 by
    simpa [leftRegularTensorTrivialIsoFree, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]
  rw [← mul_one r, ← smul_eq_mul, ← Finsupp.smul_single, ← TensorProduct.smul_tmul]
  simp [ofMulAction.single_def, (Finsupp.smul_single)]

end
end
end Finsupp



variable {k G : Type u} [CommRing k]

section Group

open Finsupp MonoidalCategory ModuleCat.MonoidalCategory
open Representation

section
variable (k : Type u) (G : Type v) (H : Type u) [Monoid G] [MulAction G H] [CommRing k]
set_option backward.isDefEq.respectTransparency false in
def linearizarionObjOfMulAction : (linearization k G).obj (Action.ofMulAction G H) ≅
    ofMulAction k G H :=
  Rep.mkIso _ _ (linearizationObjEquiv _ ≪≫ₗ (ofMulAction.equivFinsupp k G H).symm) <| fun g ↦ by
    ext
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, linearization_single,
      Action.ofMulAction_apply, LinearEquiv.trans_apply, linearizationObjEquiv_single]
    simp [Action.ofMulAction]

@[simp]
lemma linearizarionObjOfMulAction_single (h : H) (r : k) :
    (linearizarionObjOfMulAction k G H).hom (linearizationSingle _ h r) =
    ofMulAction.single G h r := rfl

@[simp]
lemma linearizarionObjOfMulAction_inv_single (h : H) (r : k) :
    (linearizarionObjOfMulAction k G H).inv.hom (ofMulAction.single G h r) =
    linearizationSingle _ h r := rfl
end

end Group

end Rep
