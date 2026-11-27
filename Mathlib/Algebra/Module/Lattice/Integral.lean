/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Algebra.Module.Submodule.Bilinear
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.LinearAlgebra.BilinearForm.Hom

/-!
# Integral lattices with respect to a bilinear form

Let `S` be an `R`-algebra and let `B` be an `S`-bilinear form on `M`. An `R`-submodule `L` of `M` is
*integral* with respect to `B` if `B x y` lies in the image of `R` in `S` for all `x, y ∈ L`. The
typical example is `R = ℤ` and `S = ℚ` or `S = ℝ`. The form `B` is not assumed to be symmetric,
nondegenerate or definite, so this covers indefinite lattices as well.

## Main definitions

* `LinearMap.BilinForm.IsIntegral B L`: the predicate that `B x y ∈ (1 : Submodule R S)` for all
  `x, y ∈ L`.

## Main results

* `LinearMap.BilinForm.isIntegral_iff_le_dualSubmodule`: `L` is integral if and only if it is
  contained in its dual submodule with respect to `B`.
* `LinearMap.BilinForm.isIntegral_span_iff`: the `R`-span of a set `s` is integral if and only if
  `B x y ∈ 1` for all `x, y ∈ s`. See also `LinearMap.BilinForm.isIntegral_iff_of_basis`.
* `LinearMap.BilinForm.isIntegral_sup_iff`: `L₁ ⊔ L₂` is integral if and only if `L₁` and `L₂` are
  integral and `B` takes values in `1` on `L₁ × L₂` and `L₂ × L₁`.
* `LinearMap.BilinForm.isIntegral_map_iff`, `LinearMap.BilinForm.IsIntegral.comap`: integrality
  under images and preimages along linear maps.
-/

@[expose] public section

open LinearMap (BilinForm)
open Submodule

namespace LinearMap.BilinForm

variable {R S M M' : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [AddCommGroup M'] [Module R M'] [Module S M']
  {B : BilinForm S M} {L L' : Submodule R M}

/-- An `R`-submodule `L` is *integral* with respect to an `S`-bilinear form `B` if `B x y` lies in
the image of `R` in `S` for all `x, y ∈ L`. -/
def IsIntegral (B : BilinForm S M) (L : Submodule R M) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, B x y ∈ (1 : Submodule R S)

lemma isIntegral_bot : B.IsIntegral (⊥ : Submodule R M) := by
  rintro x hx y -
  simp [(mem_bot R).1 hx]

lemma IsIntegral.mono (hL : B.IsIntegral L) (h : L' ≤ L) : B.IsIntegral L' :=
  fun x hx y hy ↦ hL x (h hx) y (h hy)

variable [IsScalarTower R S M] [IsScalarTower R S M']

/-- The `R`-span of a set `s` is integral if and only if `B x y` lies in the image of `R` for all
`x, y ∈ s`. -/
lemma isIntegral_span_iff {s : Set M} :
    B.IsIntegral (span R s) ↔ ∀ x ∈ s, ∀ y ∈ s, B x y ∈ (1 : Submodule R S) := by
  have := map₂_le (f := B.restrictScalars₁₂ R R) (p := span R s) (q := span R s) (r := 1)
  rw [map₂_span_span, span_le, Set.image2_subset_iff] at this
  exact this.symm

lemma isIntegral_span_range_iff {ι : Type*} {v : ι → M} :
    B.IsIntegral (span R (Set.range v)) ↔ ∀ i j, B (v i) (v j) ∈ (1 : Submodule R S) := by
  simp [isIntegral_span_iff]

lemma isIntegral_span_singleton_iff {v : M} :
    B.IsIntegral (R ∙ v) ↔ B v v ∈ (1 : Submodule R S) := by
  simp [isIntegral_span_iff]

/-- A submodule is integral if and only if `B` takes values in the image of `R` on a basis. -/
lemma isIntegral_iff_of_basis {ι : Type*} (b : Module.Basis ι R L) :
    B.IsIntegral L ↔ ∀ i j, B (b i : M) (b j) ∈ (1 : Submodule R S) := by
  have h : span R (Set.range fun i ↦ (b i : M)) = L :=
    (span_range_subtype_eq_top_iff L fun i ↦ (b i).property).1 b.span_eq
  rw [← isIntegral_span_range_iff, h]

lemma isIntegral_sup_iff {L₁ L₂ : Submodule R M} :
    B.IsIntegral (L₁ ⊔ L₂) ↔ B.IsIntegral L₁ ∧ B.IsIntegral L₂ ∧
      (∀ x ∈ L₁, ∀ y ∈ L₂, B x y ∈ (1 : Submodule R S)) ∧
      ∀ x ∈ L₁, ∀ y ∈ L₂, B y x ∈ (1 : Submodule R S) := by
  refine ⟨fun h ↦ ⟨h.mono le_sup_left, h.mono le_sup_right,
    fun x hx y hy ↦ h x (mem_sup_left hx) y (mem_sup_right hy),
    fun x hx y hy ↦ h y (mem_sup_right hy) x (mem_sup_left hx)⟩, fun ⟨h₁, h₂, h₁₂, h₂₁⟩ ↦ ?_⟩
  rw [← span_eq L₁, ← span_eq L₂, ← span_union, isIntegral_span_iff]
  rintro x (hx | hx) y (hy | hy)
  exacts [h₁ x hx y hy, h₁₂ x hx y hy, h₂₁ y hy x hx, h₂ x hx y hy]

/-- The image of `L` under a linear map `f` is integral with respect to `B` if and only if `L` is
integral with respect to the pullback of `B` along `f`. -/
lemma isIntegral_map_iff {B : BilinForm S M'} {f : M →ₗ[S] M'} :
    B.IsIntegral (L.map (f.restrictScalars R)) ↔ (B.comp f f).IsIntegral L := by
  simp [IsIntegral]

/-- The preimage of an integral submodule under a linear map `f` is integral with respect to the
pullback of the bilinear form along `f`. -/
lemma IsIntegral.comap {B : BilinForm S M'} {L : Submodule R M'} (hL : B.IsIntegral L)
    (f : M →ₗ[S] M') : (B.comp f f).IsIntegral (L.comap (f.restrictScalars R)) :=
  fun _ hx _ hy ↦ hL _ hx _ hy

section Field

variable {K : Type*} [Field K] [Algebra R K] [Module K M] [IsScalarTower R K M]
  {B : BilinForm K M}

/-- A submodule is integral if and only if it is contained in its dual submodule. -/
lemma isIntegral_iff_le_dualSubmodule : B.IsIntegral L ↔ L ≤ B.dualSubmodule L :=
  Iff.rfl

end Field

end LinearMap.BilinForm
