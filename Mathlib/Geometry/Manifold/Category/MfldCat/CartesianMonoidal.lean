/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Geometry.Manifold.Category.MfldCat.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Cartesian monoidal structure on `MfldCat`

We endow `MfldCat 𝕜 n` with its cartesian monoidal structure: the monoidal product is the
product manifold, and the unit is `PUnit`, viewed as a zero-dimensional `𝕜`-manifold.
We also derive the induced braided category structure.

## Implementation notes

We use `PUnit.{u + 1}` (rather than `Fin 0 → 𝕜`, which lives in `𝕜`'s universe) for the unit
object so that it exists in `MfldCat.{u} 𝕜 n` for any universe of `𝕜`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory
open scoped Manifold ContDiff

universe u v

namespace MfldCat

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}

/-- Limit data for a binary product in `MfldCat`, using the product manifold `M × N`. -/
@[simps! cone_pt isLimit_lift]
def binaryProductLimitCone (M N : MfldCat.{u} 𝕜 n) : LimitCone (pair M N) where
  cone := BinaryFan.mk (ofHom .fst) (ofHom .snd)
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (l.hom.prodMk r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

/-- We choose `MfldCat.of (M ⨯ N) (M.E × N.E) (ModelProd M.H N.H) (M.I.prod N.I)` as product  of `M`
and `N`, and `ofNormedSpace n PUnit` as the terminal object. -/
noncomputable instance cartesianMonoidalCategory :
    CartesianMonoidalCategory (MfldCat.{u} 𝕜 n) :=
  .ofChosenFiniteProducts
    ⟨_, IsTerminal.ofUniqueHom (Y := ofNormedSpace n PUnit.{u + 1})
      (fun _ => const PUnit.unit) (fun _ _ => by ext)⟩
    binaryProductLimitCone

noncomputable instance : BraidedCategory (MfldCat.{u} 𝕜 n) := .ofCartesianMonoidalCategory

theorem tensorObj_eq (M N : MfldCat.{u} 𝕜 n) :
    (M ⊗ N) = of (M × N) (M.E × N.E) (ModelProd M.H N.H) (M.I.prod N.I) := rfl

end MfldCat
