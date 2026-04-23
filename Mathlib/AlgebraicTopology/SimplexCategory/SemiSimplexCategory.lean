/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.Tactic.Attr.Core
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.ToAdditive
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# The semi-simplex category

We define a category `SemiSimplexCategory` so that semi-simplicial objects
can be defined (TODO) as functors from `SemiSimplexCategoryᵒᵖ` similarly
as simplicial objects are functors from `SimplexCategory`.

-/

@[expose] public section

open CategoryTheory Simplicial

/-- The category whose objects are denoted `⦋n⦌ₛ` for `n : ℕ` and
morphisms `⦋n⦌ₛ ⟶ ⦋m⦌ₛ` are order embeddings `Fin (n.len + 1) ↪o Fin (m.len + 1)`.
(This identifies to a wide subcategory of the category `SemiSimplex`, which
has the "same" objects, and morphisms `Fin (n.len + 1) →o Fin (m.len + 1)`,
see the faithful functor `SemiSimplexCategory.toSimplexCategory`.) -/
@[ext]
structure SemiSimplexCategory : Type where
  /-- Constructor `ℕ → SemiSimplexCategory`. -/
  mk ::
  /-- The length of an object in `SemiSimplexCategory` -/
  len : ℕ

namespace SemiSimplexCategory

/-- The object of `SemiSimplexCategory` corresponding to `n : ℕ` is denoted `⦋n⦌ₛ`. -/
scoped[Simplicial] notation "⦋" n "⦌ₛ" => SemiSimplexCategory.mk n

/-- The type of morphisms in the semi-simplex category are order embeddings.
This type is made irreducible: use `SemiSimplexCategory.homEquiv` to make
the conversion. -/
def Hom (n m : SemiSimplexCategory) := Fin (n.len + 1) ↪o Fin (m.len + 1)

instance smallCategory : SmallCategory.{0} SemiSimplexCategory where
  Hom := Hom
  id _ := .refl _
  comp f g := f.trans g

/-- Morphisms `n ⟶ m` in `SemiSimplexCategory` identify to order embeddings
`Fin (n.len + 1) ↪o Fin (m.len + 1)`. -/
def homEquiv {n m : SemiSimplexCategory} :
    (n ⟶ m) ≃ (Fin (n.len + 1) ↪o Fin (m.len + 1)) :=
  .refl _

@[simp]
lemma homEquiv_id (a : SemiSimplexCategory) :
    homEquiv (𝟙 a) = .refl _ := rfl

@[simp]
lemma homEquiv_comp {a b c : SemiSimplexCategory} (f : a ⟶ b) (g : b ⟶ c) :
    homEquiv (f ≫ g) = (homEquiv f).trans (homEquiv g) := rfl

attribute [irreducible] Hom

@[ext]
theorem hom_ext {a b : SemiSimplexCategory} {f g : a ⟶ b}
    (h : homEquiv f = homEquiv g) : f = g :=
  homEquiv.injective h

/-- The inclusion functor `SemiSimplexCategory ⥤ SimplexCategory`. -/
def toSimplexCategory : SemiSimplexCategory ⥤ SimplexCategory where
  obj n := ⦋n.len⦌
  map f := SimplexCategory.Hom.mk (homEquiv f).toOrderHom

@[simp]
lemma toSimplexCategory_obj (n : ℕ) :
    toSimplexCategory.obj ⦋n⦌ₛ = ⦋n⦌ := rfl

instance : toSimplexCategory.Faithful where
  map_injective h := by
    ext : 2
    apply ConcreteCategory.congr_hom h

instance {n m : SemiSimplexCategory} (f : n ⟶ m) : Mono (toSimplexCategory.map f) := by
  rw [SimplexCategory.mono_iff_injective]
  exact (homEquiv f).injective

instance {n m : SemiSimplexCategory} (f : n ⟶ m) : Mono f where
  right_cancellation g₁ g₂ h := by
    apply toSimplexCategory.map_injective
    simp only [← cancel_mono (toSimplexCategory.map f), ← Functor.map_comp, h]

/-- Constructor for morphisms in `SemiSimplexCategory` which takes as an input
a monomorphism in `SimplexCategory`. -/
def homOfMono {n m : SemiSimplexCategory}
    (f : toSimplexCategory.obj n ⟶ toSimplexCategory.obj m) [Mono f] : n ⟶ m :=
  homEquiv.symm (OrderEmbedding.ofStrictMono f.toOrderHom
    ((SimplexCategory.Hom.toOrderHom f).monotone.strictMono_of_injective
      (by rwa [← SimplexCategory.mono_iff_injective])))

@[simp]
lemma toSimplexCategory_map_homOfMono {n m : SemiSimplexCategory}
    (f : toSimplexCategory.obj n ⟶ toSimplexCategory.obj m) [Mono f] :
    toSimplexCategory.map (homOfMono f) = f := by
  aesop

end SemiSimplexCategory
