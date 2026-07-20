/-
Copyright (c) 2026 Hang Lu Su, Valerio Proietti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su, Valerio Proietti
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Quasi-isometries

A map `f : X → Y` between pseudometric spaces is a *quasi-isometric embedding* if it distorts
distances by at most a bounded affine amount in both directions, and a *quasi-isometry* if
moreover its image is coarsely dense. Quasi-isometry is the basic equivalence relation of coarse
geometry: it forgets everything about a metric space at small scales and remembers its large-scale
shape.

## Main definitions

* `IsQuasiIsometricEmbeddingWith K C f`: `dist x y ≤ K * dist (f x) (f y) + C` and
  `dist (f x) (f y) ≤ K * dist x y + C`.
* `IsQuasiIsometryWith K C f`: the above, plus every point of `Y` is within `C` of the image.
* `IsQuasiIsometry f`, `IsQuasiIsometricEmbedding f`: the unquantified versions.
* `IsQuasiIsometricTo X Y`: there exists a quasi-isometry `X → Y`.

## Main results

* `IsQuasiIsometryWith.exists_quasiInverse`: a quasi-isometry has a quasi-inverse, which is again a
  quasi-isometry. This is what makes `IsQuasiIsometricTo` symmetric.
* `isQuasiIsometricTo_equivalence`: `IsQuasiIsometricTo` is an equivalence relation.

## Design notes

* The lower bound is written `dist x y ≤ K * dist (f x) (f y) + C` rather than the more familiar
  `K⁻¹ * dist x y - C ≤ dist (f x) (f y)`. The two are equivalent after changing `K` and `C`, and
  this form avoids both division and subtraction, which keeps the arithmetic in the (many)
  downstream estimates painless.
* `IsQuasiIsometricEmbeddingWith` carries `0 ≤ K` and `0 ≤ C` as fields. They are almost always
  needed to combine two estimates, they are free to supply when building an instance, and carrying
  them avoids threading side conditions through every lemma.

## Tags

quasi-isometry, coarse geometry, large scale geometry
-/

@[expose] public section

variable {X Y Z : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]

/-- `f` is a `(K, C)`-quasi-isometric embedding: it distorts distances by at most the affine amount
`K * · + C`, in both directions. -/
structure IsQuasiIsometricEmbeddingWith (K C : ℝ) (f : X → Y) : Prop where
  /-- The multiplicative constant is nonnegative. -/
  K_nonneg : 0 ≤ K
  /-- The additive constant is nonnegative. -/
  C_nonneg : 0 ≤ C
  /-- `f` does not contract distances by more than `K * · + C`. -/
  dist_le : ∀ x y, dist x y ≤ K * dist (f x) (f y) + C
  /-- `f` does not expand distances by more than `K * · + C`. -/
  dist_image_le : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C

/-- `f` is a quasi-isometric embedding: it is a `(K, C)`-quasi-isometric embedding for some
constants. -/
def IsQuasiIsometricEmbedding (f : X → Y) : Prop :=
  ∃ K C, IsQuasiIsometricEmbeddingWith K C f

/-- `f` is a `(K, C)`-quasi-isometry: a `(K, C)`-quasi-isometric embedding whose image is
`C`-coarsely dense. -/
structure IsQuasiIsometryWith (K C : ℝ) (f : X → Y) : Prop
    extends IsQuasiIsometricEmbeddingWith K C f where
  /-- Every point of the target is within `C` of the image. -/
  exists_dist_le : ∀ y, ∃ x, dist (f x) y ≤ C

/-- `f` is a quasi-isometry: it is a `(K, C)`-quasi-isometry for some constants. -/
def IsQuasiIsometry (f : X → Y) : Prop :=
  ∃ K C, IsQuasiIsometryWith K C f

variable (X Y) in
/-- `X` and `Y` are quasi-isometric: there is a quasi-isometry `X → Y`. This is an equivalence
relation, see `isQuasiIsometricTo_equivalence`. -/
def IsQuasiIsometricTo : Prop :=
  ∃ f : X → Y, IsQuasiIsometry f

namespace IsQuasiIsometricEmbeddingWith

variable {K C K' C' : ℝ} {f : X → Y} {g : Y → Z}

theorem isQuasiIsometricEmbedding (h : IsQuasiIsometricEmbeddingWith K C f) :
    IsQuasiIsometricEmbedding f := ⟨K, C, h⟩

/-- The constants in a quasi-isometric embedding may be enlarged. -/
theorem mono (h : IsQuasiIsometricEmbeddingWith K C f) (hK : K ≤ K') (hC : C ≤ C') :
    IsQuasiIsometricEmbeddingWith K' C' f where
  K_nonneg := h.K_nonneg.trans hK
  C_nonneg := h.C_nonneg.trans hC
  dist_le x y := (h.dist_le x y).trans (by gcongr)
  dist_image_le x y := (h.dist_image_le x y).trans (by gcongr)

theorem id : IsQuasiIsometricEmbeddingWith 1 0 (id : X → X) where
  K_nonneg := zero_le_one
  C_nonneg := le_rfl
  dist_le x y := by simp
  dist_image_le x y := by simp

/-- A composition of quasi-isometric embeddings is a quasi-isometric embedding. -/
theorem comp (hg : IsQuasiIsometricEmbeddingWith K' C' g)
    (hf : IsQuasiIsometricEmbeddingWith K C f) :
    IsQuasiIsometricEmbeddingWith (K * K') (K * C' + C + K' * C + C') (g ∘ f) where
  K_nonneg := mul_nonneg hf.K_nonneg hg.K_nonneg
  C_nonneg := by
    have := hf.K_nonneg; have := hf.C_nonneg; have := hg.K_nonneg; have := hg.C_nonneg
    positivity
  dist_le x y := by
    calc dist x y ≤ K * dist (f x) (f y) + C := hf.dist_le x y
      _ ≤ K * (K' * dist (g (f x)) (g (f y)) + C') + C := by
          gcongr; exacts [hf.K_nonneg, hg.dist_le _ _]
      _ ≤ K * K' * dist ((g ∘ f) x) ((g ∘ f) y) + (K * C' + C + K' * C + C') := by
          have := hf.K_nonneg; have := hf.C_nonneg; have := hg.K_nonneg; have := hg.C_nonneg
          simp only [Function.comp_apply]; nlinarith [dist_nonneg (x := g (f x)) (y := g (f y))]
  dist_image_le x y := by
    calc dist ((g ∘ f) x) ((g ∘ f) y) ≤ K' * dist (f x) (f y) + C' := hg.dist_image_le _ _
      _ ≤ K' * (K * dist x y + C) + C' := by gcongr; exacts [hg.K_nonneg, hf.dist_image_le _ _]
      _ ≤ K * K' * dist x y + (K * C' + C + K' * C + C') := by
          have := hf.K_nonneg; have := hf.C_nonneg; have := hg.K_nonneg; have := hg.C_nonneg
          nlinarith [dist_nonneg (x := x) (y := y)]

end IsQuasiIsometricEmbeddingWith

namespace IsQuasiIsometryWith

variable {K C K' C' : ℝ} {f : X → Y} {g : Y → Z}

theorem isQuasiIsometry (h : IsQuasiIsometryWith K C f) : IsQuasiIsometry f := ⟨K, C, h⟩

theorem isQuasiIsometricTo (h : IsQuasiIsometryWith K C f) : IsQuasiIsometricTo X Y :=
  ⟨f, h.isQuasiIsometry⟩

/-- The constants in a quasi-isometry may be enlarged. -/
theorem mono (h : IsQuasiIsometryWith K C f) (hK : K ≤ K') (hC : C ≤ C') :
    IsQuasiIsometryWith K' C' f where
  __ := h.toIsQuasiIsometricEmbeddingWith.mono hK hC
  exists_dist_le y := let ⟨x, hx⟩ := h.exists_dist_le y; ⟨x, hx.trans hC⟩

theorem id : IsQuasiIsometryWith 1 0 (id : X → X) where
  __ := IsQuasiIsometricEmbeddingWith.id
  exists_dist_le y := ⟨y, by simp⟩

/-- A composition of quasi-isometries is a quasi-isometry. -/
theorem comp (hg : IsQuasiIsometryWith K' C' g) (hf : IsQuasiIsometryWith K C f) :
    IsQuasiIsometryWith (K * K') (K * C' + C + K' * C + 2 * C') (g ∘ f) where
  __ := (hg.toIsQuasiIsometricEmbeddingWith.comp
    hf.toIsQuasiIsometricEmbeddingWith).mono le_rfl (by have := hg.C_nonneg; linarith)
  exists_dist_le z := by
    obtain ⟨y, hy⟩ := hg.exists_dist_le z
    obtain ⟨x, hx⟩ := hf.exists_dist_le y
    have := hf.C_nonneg
    have := hg.K_nonneg
    have := hg.C_nonneg
    have := hf.K_nonneg
    refine ⟨x, ?_⟩
    calc dist ((g ∘ f) x) z ≤ dist (g (f x)) (g y) + dist (g y) z := dist_triangle _ _ _
      _ ≤ (K' * dist (f x) y + C') + C' := by gcongr; exact hg.dist_image_le _ _
      _ ≤ (K' * C + C') + C' := by gcongr
      _ ≤ K * C' + C + K' * C + 2 * C' := by nlinarith

/-- **A quasi-isometry has a quasi-inverse.** Any right inverse up to bounded error is
automatically a quasi-isometry, and a left inverse up to bounded error as well. This is what makes
`IsQuasiIsometricTo` a symmetric relation. -/
theorem exists_quasiInverse (h : IsQuasiIsometryWith K C f) :
    ∃ (g : Y → X) (K' C' : ℝ), IsQuasiIsometryWith K' C' g ∧
      (∀ y, dist (f (g y)) y ≤ C) ∧ (∀ x, dist (g (f x)) x ≤ K * C + C) := by
  have hK := h.K_nonneg
  have hC := h.C_nonneg
  choose g hg using h.exists_dist_le
  -- `g` is a right inverse of `f` up to the error `C`, hence a left inverse up to `K * C + C`.
  have hgf : ∀ x, dist (g (f x)) x ≤ K * C + C := fun x =>
    (h.dist_le (g (f x)) x).trans (by gcongr; exact hg (f x))
  have hKC : 0 ≤ K * C := mul_nonneg hK hC
  refine ⟨g, K, 2 * K * C + 4 * C, ⟨⟨hK, by positivity, fun y y' => ?_, fun y y' => ?_⟩,
    fun x => ⟨f x, ?_⟩⟩, hg, hgf⟩
  · -- `dist y y' ≤ K * dist (g y) (g y') + _`, via the triangle inequality through `f (g y)`.
    calc dist y y' ≤ dist y (f (g y)) + dist (f (g y)) (f (g y')) + dist (f (g y')) y' :=
          dist_triangle4 _ _ _ _
      _ ≤ C + (K * dist (g y) (g y') + C) + C := by
          gcongr
          exacts [(dist_comm y _ ▸ hg y), h.dist_image_le _ _, hg y']
      _ ≤ K * dist (g y) (g y') + (2 * K * C + 4 * C) := by linarith
  · -- `dist (g y) (g y') ≤ K * dist y y' + _`, likewise.
    calc dist (g y) (g y') ≤ K * dist (f (g y)) (f (g y')) + C := h.dist_le _ _
      _ ≤ K * (dist (f (g y)) y + dist y y' + dist y' (f (g y'))) + C := by
          gcongr; exact dist_triangle4 _ _ _ _
      _ ≤ K * (C + dist y y' + C) + C := by
          gcongr
          exacts [hg y, dist_comm y' _ ▸ hg y']
      _ ≤ K * dist y y' + (2 * K * C + 4 * C) := by nlinarith
  · calc dist (g (f x)) x ≤ K * C + C := hgf x
      _ ≤ 2 * K * C + 4 * C := by linarith

end IsQuasiIsometryWith

namespace IsQuasiIsometry

variable {f : X → Y} {g : Y → Z}

theorem id : IsQuasiIsometry (id : X → X) := IsQuasiIsometryWith.id.isQuasiIsometry

theorem comp (hg : IsQuasiIsometry g) (hf : IsQuasiIsometry f) : IsQuasiIsometry (g ∘ f) :=
  let ⟨_, _, hg⟩ := hg; let ⟨_, _, hf⟩ := hf; (hg.comp hf).isQuasiIsometry

/-- A quasi-isometry has a quasi-inverse, which is itself a quasi-isometry. -/
theorem exists_quasiInverse (h : IsQuasiIsometry f) : ∃ g : Y → X, IsQuasiIsometry g :=
  let ⟨_, _, h⟩ := h
  let ⟨g, _, _, hg, _, _⟩ := h.exists_quasiInverse
  ⟨g, hg.isQuasiIsometry⟩

end IsQuasiIsometry

namespace IsQuasiIsometricTo

@[refl]
theorem refl : IsQuasiIsometricTo X X := ⟨id, IsQuasiIsometry.id⟩

theorem symm (h : IsQuasiIsometricTo X Y) : IsQuasiIsometricTo Y X :=
  let ⟨_, hf⟩ := h; hf.exists_quasiInverse

theorem trans (h : IsQuasiIsometricTo X Y) (h' : IsQuasiIsometricTo Y Z) :
    IsQuasiIsometricTo X Z :=
  let ⟨_, hf⟩ := h; let ⟨_, hg⟩ := h'; ⟨_, hg.comp hf⟩

end IsQuasiIsometricTo
