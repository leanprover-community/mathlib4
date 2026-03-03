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

namespace Rep

section non_comm

variable {k : Type u} {G : Type v} [Ring k] [Monoid G]

def Hom {k : Type u} {G : Type v} [Ring k] [Monoid G] (A B : Rep k G) : Type w := Action.Hom A B

instance (k : Type u) (G : Type v) [Ring k] [Monoid G] : Category (Rep k G) where
  Hom := Rep.Hom
  __ := inferInstanceAs (Category (Action (ModuleCat.{w, u} k) G))

def V {k : Type u} {G : Type v} [Ring k] [Monoid G] (A : Rep k G) : ModuleCat k := Action.V A

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

def of {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k G V) : Rep k G :=
  ⟨ModuleCat.of k V, (ModuleCat.endRingEquiv _).symm.toMonoidHom.comp ρ⟩

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

end Commutative

suppress_compilation

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

@[simp]
lemma ofMulAction.ρ_single (H : Type w') [MulAction G H] (g : G) (h : H) (x : k) :
    (ofMulAction k G H).ρ g (ofMulAction.single G h x) = ofMulAction.single G (g • h) x := by
  simp only [ofMulAction, coe_of, of_ρ, single]
  conv_lhs => enter [2]; tactic => convert Finsupp.lsingle_apply (M := k) _ _
  exact Representation.ofMulAction_single g h x

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

variable {k G} in
@[simps]
def mkIso (M₁ M₂ : Rep.{w} k G) (f : M₁.V ≃ₗ[k] M₂.V) (hf : ∀ g : G, f ∘ₗ M₁.ρ g =
    M₂.ρ g ∘ₗ f := by aesop) : M₁ ≅ M₂ where
  hom := ofHom (σ := M₁.ρ) (ρ := M₂.ρ) ⟨f, fun g ↦ congr($(hf g))⟩
  inv := ofHom (σ := M₂.ρ) (ρ := M₁.ρ) ⟨f.symm, fun g ↦ by
    rw [← LinearMap.cancel_left f.injective, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc,
      hf g, LinearEquiv.comp_symm, LinearMap.id_comp, LinearMap.comp_assoc,
      LinearEquiv.comp_symm, LinearMap.comp_id]⟩
  hom_inv_id := by
    conv_rhs => tactic => convert (ofHom_id (σ := M₁.ρ)).symm -- how to get rid of this
    conv_lhs => tactic => convert (ofHom_comp (σ := M₁.ρ) (ρ := M₂.ρ) (τ := M₁.ρ) _ _).symm
    congr 1
    ext1
    simp [Representation.IntertwiningMap.id ]
  inv_hom_id := by
    conv_rhs => tactic => convert (ofHom_id (σ := M₂.ρ)).symm
    conv_lhs => tactic => convert (ofHom_comp (σ := M₂.ρ) (ρ := M₁.ρ) (τ := M₂.ρ) _ _).symm
    congr 1
    ext1
    simp [Representation.IntertwiningMap.id ]

/-- The natural isomorphism between the representations on `k[G¹]` and `k[G]` induced by left
multiplication in `G`. -/
@[simps! hom_hom inv_hom]
def diagonalOneIsoLeftRegular :
    diagonal k G 1 ≅ leftRegular k G :=
  Rep.mkIso (diagonal k G 1) (leftRegular k G) (ofMulAction.equivFinsupp _ _ _ ≪≫ₗ
    Finsupp.domLCongr (Equiv.funUnique (Fin 1) G) ≪≫ₗ (ofMulAction.equivFinsupp _ _ _).symm)
    fun g ↦ by ext; simp

/-- When `H = {1}`, the `G`-representation on `k[H]` induced by an action of `G` on `H` is
isomorphic to the trivial representation on `k`. -/
@[simps! hom_hom inv_hom]
def ofMulActionSubsingletonIsoTrivial
    (H : Type u) [Subsingleton H] [MulOneClass H] [MulAction G H] :
    ofMulAction k G H ≅ trivial k G k :=
  letI : Unique H := uniqueOfSubsingleton 1
  mkIso _ _ (ofMulAction.equivFinsupp _ _ _ ≪≫ₗ Finsupp.LinearEquiv.finsuppUnique _ _ _) fun g ↦ by
  ext x; --simp [Subsingleton.elim (g • x) x]
  sorry -- types

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

-- set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem leftRegularHom_hom_single {A : Rep k G} (g : G) (x : A) (r : k) :
    (leftRegularHom A x).hom (ofMulAction.single G g r) = r • A.ρ g x := by
  simp only [leftRegularHom]
  conv_lhs => enter [1]; tactic => convert hom_ofHom _ -- why???
  simp

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

instance : MonoidalCategory (Rep.{u} k G) := Action.instMonoidalCategory

open MonoidalCategory in
@[simp]
theorem tensor_ρ {A B : Rep k G} : (A ⊗ B).ρ = A.ρ.tprod B.ρ := rfl

@[simp]
lemma tensorUnit_ρ_apply {g : G} : (𝟙_ (Rep k G)).ρ g = LinearMap.id := rfl

instance : (forget₂ (Rep k G) (ModuleCat k)).Additive :=
  inferInstanceAs (Action.forget (ModuleCat k) G).Additive

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

end Monoidal

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

@[simp]
theorem coe_linearization_obj (X : Action (Type u) G) :
    (linearization k G).obj X = (X.V →₀ k) := rfl

theorem linearization_obj_ρ (X : Action (Type u) G) (g : G) :
    ((linearization k G).obj X).ρ g = Finsupp.lmapDomain k k (X.ρ g) :=
  rfl

@[simp]
theorem coe_linearization_obj_ρ (X : Action (Type u) G) (g : G) :
    @DFunLike.coe (no_index G →* ((X.V →₀ k) →ₗ[k] (X.V →₀ k))) _
      (fun _ => (X.V →₀ k) →ₗ[k] (X.V →₀ k)) _
      ((linearization k G).obj X).ρ g = Finsupp.lmapDomain k k (X.ρ g) := rfl

set_option backward.isDefEq.respectTransparency false in
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): helps fixing `linearizationTrivialIso` since change in behaviour of `ext`.
theorem linearization_single (X : Action (Type u) G) (g : G) (x : X.V) (r : k) :
    ((linearization k G).obj X).ρ g (Finsupp.single x r) = Finsupp.single (X.ρ g x) r := by
  simp

variable {X Y : Action (Type u) G} (f : X ⟶ Y)

@[simp]
theorem linearization_map_hom : ((linearization k G).map f).hom.toLinearMap =
    Finsupp.lmapDomain k k f.hom :=
  rfl

theorem linearization_map_hom_single (x : X.V) (r : k) :
    ((linearization k G).map f).hom (Finsupp.single x r) = Finsupp.single (f.hom x) r :=
  Finsupp.mapDomain_single

open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

@[simp]
theorem linearization_μ_hom (X Y : Action (Type u) G) :
    (μ (linearization k G) X Y).hom.toLinearMap =
      (finsuppTensorFinsupp' k X.V Y.V).toLinearMap :=
  rfl

@[simp]
theorem linearization_δ_hom (X Y : Action (Type u) G) :
    (δ (linearization k G) X Y).hom.toLinearMap =
      (finsuppTensorFinsupp' k X.V Y.V).symm.toLinearMap :=
  rfl

@[simp]
theorem linearization_ε_hom : (ε (linearization k G)).hom.toLinearMap =
    Finsupp.lsingle PUnit.unit :=
  rfl

theorem linearization_η_hom_apply (r : k) :
    (η (linearization k G)).hom (Finsupp.single PUnit.unit r) = r :=
  (εIso (linearization k G)).hom_inv_id_apply r

/-- The linearization of a type `X` on which `G` acts trivially is the trivial `G`-representation
on `k[X]`. -/
@[simps! hom_hom inv_hom]
def linearizationTrivialIso (X : Type u) :
    (linearization k G).obj (Action.mk X 1) ≅ trivial k G (X →₀ k) :=
  Action.mkIso (Iso.refl _) fun _ => ModuleCat.hom_ext <| Finsupp.lhom_ext' fun _ => LinearMap.ext
    fun _ => linearization_single ..




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
  -- .ofLinear ((LinearMap.id (M := _ →ₗ[k] _)).flip (Finsupp.single (1 : G) (1 : k)) ∘ₗ
  --   ModuleCat.homLinearEquiv.toLinearMap ∘ₗ (forget₂ _ (ModuleCat k)).mapLinearMap k)
  --   (leftRegularHom A) _ _
  -- where
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

set_option backward.isDefEq.respectTransparency false in
variable (k G) in
/-- The representation on `α →₀ k[G]` defined pointwise by the left regular representation on
`k[G]`. -/
def free : Rep k G :=
  Rep.of (V := (α →₀ G →₀ k)) (Representation.free k G α)

def free.single (i : α) : (G →₀ k) →ₗ[k] free k G α := Finsupp.lsingle i

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

@[simp]
lemma free.ρ_single (i : α) (g g' : G) (r : k) :
    (free k G α).ρ g' (free.single α i (Finsupp.single g r)) =
    free.single α i (Finsupp.single (g' * g) r) := by
  simp [free, free.single]
  erw? [Finsupp.lsingle_apply]
  sorry

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
  toFun f i := f.hom (single i (single 1 1))
  invFun := freeLift A
  left_inv x := by
    ext i j
    simp [← hom_comm_apply, free.ρ_single]
      -- ext : 2
      -- dsimp -- this has to be added otherwise the `ext` don't `ext` into two variables
      -- ext i j
      -- simpa [freeLift, ← map_smul] using (hom_comm_apply x j (single i (single 1 1))).symm
  right_inv _ := by ext; simp [freeLift]
    -- erw? [freeLift_hom_single_single] -- why doesn't this work?
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {A}

@[ext]
lemma free_ext (f g : free k G α ⟶ A)
    (h : ∀ i : α, f.hom (single i (single 1 1)) = g.hom (single i (single 1 1))) : f = g := by
  classical exact (freeLiftLEquiv α A).injective (funext_iff.2 h)

section

open MonoidalCategory

variable (A B : Rep.{u} k G) (α : Type u) [DecidableEq α]

open ModuleCat.MonoidalCategory

set_option backward.isDefEq.respectTransparency false in
-- the proof below can be simplified after https://github.com/leanprover-community/mathlib4/issues/24823 is merged
/-- Given representations `A, B` and a type `α`, this is the natural representation isomorphism
`(α →₀ A) ⊗ B ≅ (A ⊗ B) →₀ α` sending `single x a ⊗ₜ b ↦ single x (a ⊗ₜ b)`. -/
@[simps! hom_hom inv_hom]
def finsuppTensorLeft :
    A.finsupp α ⊗ B ≅ (A ⊗ B).finsupp α :=
  Rep.mkIso _ _ (TensorProduct.finsuppLeft k _ A B α).toModuleIso
    fun _ => TensorProduct.ext <| lhom_ext fun _ _ => by
      dsimp

      -- ext1
      -- simp only [coe_of, Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
      --   Action.FunctorCategoryEquivalence.functor_obj_obj, LinearEquiv.toModuleIso_hom,
      --   ModuleCat.hom_ofHom, tensor_ρ, of_ρ, LinearMap.compr₂ₛₗ_apply, LinearMap.coe_comp,
      --   Function.comp_apply]
      -- erw? [TensorProduct.mk_apply]
      sorry

set_option backward.isDefEq.respectTransparency false in
/-- Given representations `A, B` and a type `α`, this is the natural representation isomorphism
`A ⊗ (α →₀ B) ≅ (A ⊗ B) →₀ α` sending `a ⊗ₜ single x b ↦ single x (a ⊗ₜ b)`. -/
@[simps! hom_hom inv_hom]
def finsuppTensorRight :
    A ⊗ B.finsupp α ≅ (A ⊗ B).finsupp α :=
  Action.mkIso (TensorProduct.finsuppRight k _ A B α).toModuleIso fun _ => ModuleCat.hom_ext <|
      TensorProduct.ext <| LinearMap.ext fun _ => lhom_ext fun _ _ => by
      ext
      simp [Action_ρ_eq_ρ, TensorProduct.finsuppRight_apply_tmul, ModuleCat.endRingEquiv,
        tensorObj_carrier]

set_option backward.isDefEq.respectTransparency false in
variable (k G) in
/-- The natural isomorphism sending `single g r₁ ⊗ single a r₂ ↦ single a (single g r₁r₂)`. -/
@[simps! -isSimp hom_hom inv_hom]
def leftRegularTensorTrivialIsoFree :
    leftRegular k G ⊗ trivial k G (α →₀ k) ≅ free k G α :=
  Action.mkIso (finsuppTensorFinsupp' k G α ≪≫ₗ Finsupp.domLCongr (Equiv.prodComm G α) ≪≫ₗ
    curryLinearEquiv k).toModuleIso fun _ =>
      ModuleCat.hom_ext <| TensorProduct.ext <| lhom_ext fun _ _ => lhom_ext fun _ _ => by
        ext
        simp [Action_ρ_eq_ρ, tensorObj_carrier, ModuleCat.endRingEquiv]

variable {α}

omit [DecidableEq α]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma leftRegularTensorTrivialIsoFree_hom_hom_single_tmul_single (i : α) (g : G) (r s : k) :
    DFunLike.coe (F := ↑(ModuleCat.of k (G →₀ k) ⊗ ModuleCat.of k (α →₀ k)) →ₗ[k] α →₀ G →₀ k)
    (leftRegularTensorTrivialIsoFree k G α).hom.hom.hom (single g r ⊗ₜ[k] single i s) =
      single i (single g (r * s)) := by
  simp [leftRegularTensorTrivialIsoFree, tensorObj_carrier]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma leftRegularTensorTrivialIsoFree_inv_hom_single_single (i : α) (g : G) (r : k) :
    DFunLike.coe (F := (α →₀ G →₀ k) →ₗ[k] ↑(ModuleCat.of k (G →₀ k) ⊗ ModuleCat.of k (α →₀ k)))
    (leftRegularTensorTrivialIsoFree k G α).inv.hom.hom (single i (single g r)) =
      single g r ⊗ₜ[k] single i 1 := by
  simp [leftRegularTensorTrivialIsoFree, finsuppTensorFinsupp'_symm_single_eq_tmul_single_one,
    tensorObj_carrier]

end
end Finsupp

end Rep
