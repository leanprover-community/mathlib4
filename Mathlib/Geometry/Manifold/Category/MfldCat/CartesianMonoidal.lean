/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Geometry.Manifold.Category.MfldCat.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# The cartesian monoidal structure on `MfldCat`

We endow `MfldCat 𝕜 n` with its cartesian monoidal structure: the monoidal product is the
product manifold `prodObj M N`, and the unit is the singleton `PUnit`, viewed as a
zero-dimensional `𝕜`-manifold. We also derive the induced braided category structure.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory
open scoped Manifold ContDiff

universe u v

namespace MfldCat

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}

/-- The product of two manifolds as an object of `MfldCat`. The chart space is
`ModelProd M.H N.H` and the model is `M.I.prod N.I`, so `prodObj M N` is the product manifold
in the standard sense. -/
def prodObj (M N : MfldCat.{u} 𝕜 n) : MfldCat.{u} 𝕜 n :=
  of (M × N) (M.E × N.E) (ModelProd M.H N.H) (M.I.prod N.I)

/-- Limit data for the binary product of `M` and `N` in `MfldCat`, using `prodObj M N`. -/
def binaryProductLimitCone (M N : MfldCat.{u} 𝕜 n) : LimitCone (pair M N) where
  cone := BinaryFan.mk (ofHom ⟨Prod.fst, contMDiff_fst⟩) (ofHom ⟨Prod.snd, contMDiff_snd⟩)
  isLimit := BinaryFan.IsLimit.mk _
    (fun l r => ofHom ⟨fun s => (l s, r s), l.hom.contMDiff.prodMk r.hom.contMDiff⟩)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ h₁ h₂ => by
      ext x
      exact Prod.ext (ConcreteCategory.congr_hom h₁ x) (ConcreteCategory.congr_hom h₂ x))

/-- We choose `prodObj M N` as the product of `M` and `N`, and the singleton `PUnit.{u + 1}`
(viewed as a zero-dimensional `𝕜`-manifold via `ofNormedSpace`) as the terminal object. We use
`PUnit.{u + 1}` rather than `Fin 0 → 𝕜` so that the unit object exists in `MfldCat.{u} 𝕜 n` for
any universe `v` of `𝕜`. -/
noncomputable instance cartesianMonoidalCategory :
    CartesianMonoidalCategory (MfldCat.{u} 𝕜 n) :=
  .ofChosenFiniteProducts
    ⟨_, IsTerminal.ofUniqueHom (Y := ofNormedSpace n PUnit.{u + 1})
      (fun _ => ofHom ⟨fun _ => PUnit.unit, contMDiff_const⟩) (fun _ _ => by ext)⟩
    binaryProductLimitCone

noncomputable instance : BraidedCategory (MfldCat.{u} 𝕜 n) := .ofCartesianMonoidalCategory

@[simp] theorem tensorObj_eq (M N : MfldCat.{u} 𝕜 n) : (M ⊗ N) = prodObj M N := rfl

end MfldCat
