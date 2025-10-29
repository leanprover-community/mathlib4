/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Simplices

/-!
# Simplices that are uniquely codimensional one faces

Let `X` be a simplicial set. If `x : X _⦋d⦌` and `y : X _⦋d + 1⦌`,
we say that `x` is uniquely a `1`-codimensional face of `y` if there
exists a unique `i : Fin (d + 2)` such that `X.δ i y = x`. In this file,
we extend this to a predicate `IsUniquelyCodimOneFace` involving two terms
in the type `X.S` of simplices of `X`. This is used in the
file `AlgebraicTopology.SimplicialSet.AnodyneExtensions.Pairing` for the
study of strong (inner) anodyne extensions.

## References
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

-/

universe u

open CategoryTheory Simplicial

namespace SSet.S

variable {X : SSet.{u}} (x y : X.S)

/-- The property that a simplex is uniquely a `1`-codimensional face of another simplex -/
def IsUniquelyCodimOneFace : Prop :=
  y.dim = x.dim + 1 ∧ ∃! (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌), Mono f ∧ X.map f.op y.simplex = x.simplex

namespace IsUniquelyCodimOneFace

lemma iff {d : ℕ} (x : X _⦋d⦌) (y : X _⦋d + 1⦌) :
    IsUniquelyCodimOneFace (S.mk x) (S.mk y) ↔
      ∃! (i : Fin (d + 2)), X.δ i y = x := by
  constructor
  · rintro ⟨_, ⟨f, ⟨_, h₁⟩, h₂⟩⟩
    obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono f
    exact ⟨i, h₁, fun j hj ↦ SimplexCategory.δ_injective (h₂ _ ⟨inferInstance, hj⟩)⟩
  · rintro ⟨i, h₁, h₂⟩
    refine ⟨rfl, SimplexCategory.δ i, ⟨inferInstance, h₁⟩, fun f ⟨h₃, h₄⟩ ↦ ?_⟩
    obtain ⟨j, rfl⟩ := SimplexCategory.eq_δ_of_mono f
    obtain rfl : j = i := h₂ _ h₄
    rfl

variable {x y} (hxy : IsUniquelyCodimOneFace x y)

include hxy in
lemma dim_eq : y.dim = x.dim + 1 := hxy.1

section

variable {d : ℕ} (hd : x.dim = d)

lemma cast : IsUniquelyCodimOneFace (x.cast hd) (y.cast (by rw [hxy.dim_eq, hd])) := by
  simpa only [cast_eq_self]

lemma existsUnique_δ_cast_simplex :
    ∃! (i : Fin (d + 2)), X.δ i (y.cast (by rw [hxy.dim_eq, hd])).simplex =
      (x.cast hd).simplex := by
  simpa only [S.cast, iff] using hxy.cast hd

include hxy in
/-- When a `d`-dimensional simplex `x` is a `1`-codimensional face of `y`, this is
the only `i : Fin (d + 2)`, such that `X.δ i y = x` (with an abuse of notation:
see `δ_index` and `δ_eq_iff` for well typed statements). -/
noncomputable def index : Fin (d + 2) :=
  (hxy.existsUnique_δ_cast_simplex hd).exists.choose

lemma δ_index :
    X.δ (hxy.index hd) (y.cast (by rw [hxy.dim_eq, hd])).simplex = (x.cast hd).simplex :=
  (hxy.existsUnique_δ_cast_simplex hd).exists.choose_spec

lemma δ_eq_iff (i : Fin (d + 2)) :
    X.δ i (y.cast (by rw [hxy.dim_eq, hd])).simplex = (x.cast hd).simplex ↔
      i = hxy.index hd :=
  ⟨fun h ↦ (hxy.existsUnique_δ_cast_simplex hd).unique h (hxy.δ_index hd),
    by rintro rfl; apply δ_index⟩

end

end IsUniquelyCodimOneFace

end SSet.S
