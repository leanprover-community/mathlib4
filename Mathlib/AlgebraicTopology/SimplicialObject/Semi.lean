/-
Copyright (c) 2026 Robin Carlier, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier, Christian Merten
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular
public import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory

/-!
# Semi-simplicial objects
-/

@[expose] public section

universe w u

open Simplicial CategoryTheory Limits Opposite

namespace SemiSimplexCategory

set_option backward.isDefEq.respectTransparency false in
@[simps]
def lift {C : Type*} [Category* C] (F : C ⥤ SimplexCategory)
    (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Mono (F.map f) := by infer_instance) :
    C ⥤ SemiSimplexCategory where
  obj X := .mk (F.obj X).len
  map f :=
    haveI : Mono (F.map f) := h f
    homOfMono (F.map f)

set_option backward.isDefEq.respectTransparency false in
@[simps!]
def liftComp {C : Type*} [Category* C] (F : C ⥤ SimplexCategory)
    (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Mono (F.map f) := by infer_instance) :
    lift F h ⋙ toSimplexCategory ≅ F :=
  NatIso.ofComponents (fun X ↦ Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
lemma homOfMono_id (n : ℕ) :
    homOfMono (𝟙 <| toSimplexCategory.obj ⦋n⦌ₛ) = 𝟙 (⦋n⦌ₛ) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
def δ {n} (i : Fin (n + 2)) : ⦋n⦌ₛ ⟶ ⦋n + 1⦌ₛ :=
  homOfMono (SimplexCategory.δ i)

@[simp]
lemma toSimplexCategory_map_δ {n} (i : Fin (n + 2)) :
    toSimplexCategory.map (δ i) = SimplexCategory.δ i :=
  rfl

/-- Recover the monotone map from a morphism in the semi-simplex category. -/
def Hom.toOrderHom {a b : SemiSimplexCategory} (f : a ⟶ b) :
    Fin (a.len + 1) →o Fin (b.len + 1) :=
  (homEquiv f).toOrderHom

end SemiSimplexCategory

namespace CategoryTheory

variable {C : Type*} [Category* C] (X : SimplicialObject C) (K : SSet.{w})

/-- The category of semi-simplicial objects in a category `C`. This is the category of contravariant
functors from `SemiSimplexCategory` to `C`. -/
abbrev SemiSimplicialObject (C : Type*) [Category* C] : Type _ :=
  SemiSimplexCategoryᵒᵖ ⥤ C

/-- The category of semi-cosimplicial objects in a category `C`. This is the category of
covariant functors from `SemiSimplexCategory` to `C`. -/
abbrev SemiCosimplicialObject (C : Type*) [Category* C] : Type _ :=
  SemiSimplexCategory ⥤ C

set_option quotPrecheck false in
/-- `X _⦋n⦌ₛ` denotes the `n`th-term of the semi-simplicial object X -/
scoped[Simplicial]
  notation3:1000 X " _⦋" n "⦌ₛ" =>
      (X : CategoryTheory.SemiSimplicialObject _).obj (Opposite.op (SemiSimplexCategory.mk n))

def SemiSimplicialObject.δ (X : SemiSimplicialObject C) {n : ℕ} (i : Fin (n + 2)) :
    X _⦋n + 1⦌ₛ ⟶ X _⦋n⦌ₛ :=
  X.map (SemiSimplexCategory.δ i).op

end CategoryTheory

/-- The category of semi-simplicial sets. This is the category of semi-simplicial objects
in `Type u`. -/
abbrev SemiSSet : Type (u + 1):= SemiSimplicialObject (Type u)

namespace SemiSSet

/-- The functor `SemiSimplexCategory ⥤ SemiSSet` which sends `⦋n⦌ₛ` to the standard
simplex `Δ[n]` is a semi-cosimplicial object in the category of semi-simplicial sets.
(This functor is essentially given by the Yoneda embedding). -/
def stdSimplex : SemiCosimplicialObject SemiSSet :=
  uliftYoneda

/-- The canonical bijection `(stdSimplex.obj n ⟶ X) ≃ X.obj (op n)`. -/
def yonedaEquiv {X : SemiSSet.{u}} {n : SemiSimplexCategory} :
    (stdSimplex.obj n ⟶ X) ≃ X.obj (op n) :=
  uliftYonedaEquiv

@[inherit_doc SemiSSet.stdSimplex]
scoped[Simplicial]
notation3 "Δ[" n "]ₛ" => SemiSSet.stdSimplex.obj (SemiSimplexCategory.mk n)

/-- The complete lattice of subcomplexes of a semi-simplicial set. -/
abbrev Subcomplex (X : SemiSSet.{u}) : Type _ := Subfunctor X

variable {X : SemiSSet.{u}}

namespace Subcomplex

/-- The underlying simplicial set of a subcomplex. -/
abbrev toSemiSSet (A : X.Subcomplex) : SemiSSet.{u} := A.toFunctor

instance : CoeOut X.Subcomplex SemiSSet.{u} where
  coe := fun S ↦ S.toSemiSSet

end Subcomplex

/-- The `m`-simplices of the `n`-th standard simplex are
the monotone maps from `Fin (m+1)` to `Fin (n+1)`. -/
def stdSimplex.asOrderHom {n} {m} (α : Δ[n]ₛ.obj m) : (Fin (m.unop.len + 1)) →o (Fin (n + 1)) :=
  α.down.toOrderHom

/-- The boundary `∂Δ[n]` of the `n`-th standard semi-simplex consists of
all `m`-simplices of `stdSimplex n` that are not surjective
(when viewed as monotone function `m → n`). -/
def boundary (n : ℕ) : (Δ[n]ₛ : SemiSSet.{u}).Subcomplex where
  obj _ := setOf (fun s ↦ ¬Function.Surjective (stdSimplex.asOrderHom s))
  map _ _ hs h := hs (Function.Surjective.of_comp h)

/-- The boundary `∂Δ[n]ₛ` of the `n`-th standard semi-simplex -/
scoped[Simplicial] notation3 "∂Δ[" n "]ₛ" => SemiSSet.boundary n

/-- An `n`-simplex of a semi-simplicial set `X` is degenerate if it is in the range
of `X.map f.op` for some morphism `f : [n] ⟶ [m]` with `m < n`. -/
def degenerate (X : SemiSSet.{u}) (n : ℕ) : Set (X _⦋n⦌ₛ) :=
  setOf (fun x ↦ ∃ (m : ℕ) (_ : m < n) (f : ⦋n⦌ₛ ⟶ ⦋m⦌ₛ),
    x ∈ Set.range (X.map f.op))

/-- The set of `n`-dimensional non-degenerate simplices in a semi-simplicial
set `X` is the complement of `X.degenerate n`. -/
def nonDegenerate (X : SemiSSet.{u}) (n : ℕ) : Set (X _⦋n⦌ₛ) := (X.degenerate n)ᶜ

variable (X : SemiSSet.{u})

/-- The type of simplices of a semi-simplicial set `X`. This type `X.S` is in bijection
with `X.Elements` (see `SSet.S.equivElements`), but `X.S` is not what the literature
names "category of simplices of `X`", as the category on `X.S` comes from
a preorder (see `S.le_iff_nonempty_hom`). -/
structure S where
  /-- the dimension of the simplex -/
  {dim : ℕ}
  /-- the simplex -/
  simplex : X _⦋dim⦌ₛ

/-- The type of non degenerate simplices of a semi-simplicial set. -/
structure N extends X.S where mk' ::
  nonDegenerate : simplex ∈ X.nonDegenerate _

instance : Preorder X.N :=
  sorry

/-- A semi-simplicial set is finite if it has finitely many nondegenerate simplices. -/
protected class Finite : Prop where
  finite : _root_.Finite X.N

instance (n : ℕ) : Δ[n]ₛ.Finite :=
  sorry

instance (n : ℕ) : (∂Δ[n]ₛ : SemiSSet.{u}).Finite :=
  sorry

attribute [instance] Finite.finite
class Nonsingular (X : SemiSSet) where
  mono {n : ℕ} (x : X.nonDegenerate n) : Mono (yonedaEquiv.symm x.val)

instance (n : ℕ) : Δ[n]ₛ.Nonsingular :=
  sorry

instance (n : ℕ) : Nonsingular (∂Δ[n]ₛ : SemiSSet.{u}) :=
  sorry

end SemiSSet
