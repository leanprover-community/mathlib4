/-
Copyright (c) 2022 Apurva Nakade All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint

#align_import analysis.convex.cone.proper from "leanprover-community/mathlib"@"147b294346843885f952c5171e9606616a8fd869"

/-!
# Proper cones

We define a proper cone as a nonempty, closed, convex cone. Proper cones are used in defining conic
programs which generalize linear programs. A linear program is a conic program for the positive
cone. We then prove Farkas' lemma for conic programs following the proof in the reference below.
Farkas' lemma is equivalent to strong duality. So, once have the definitions of conic programs and
linear programs, the results from this file can be used to prove duality theorems.

## TODO

The next steps are:
- Add convex_cone_class that extends set_like and replace the below instance
- Define primal and dual cone programs and prove weak duality.
- Prove regular and strong duality for cone programs using Farkas' lemma (see reference).
- Define linear programs and prove LP duality as a special case of cone duality.
- Find a better reference (textbook instead of lecture notes).
- Show submodules are (proper) cones.

## References

- [B. Gartner and J. Matousek, Cone Programming][gartnerMatousek]

-/

open ContinuousLinearMap Filter Set

namespace ConvexCone

variable {𝕜 : Type*} [OrderedSemiring 𝕜]

variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [ContinuousAdd E] [SMul 𝕜 E]
  [ContinuousConstSMul 𝕜 E]

/-- The closure of a convex cone inside a topological space as a convex cone. This
construction is mainly used for defining maps between proper cones. -/
protected def closure (K : ConvexCone 𝕜 E) : ConvexCone 𝕜 E where
  carrier := closure ↑K
  smul_mem' c hc _ h₁ :=
    map_mem_closure (continuous_id'.const_smul c) h₁ fun _ h₂ => K.smul_mem hc h₂
  add_mem' _ h₁ _ h₂ := map_mem_closure₂ continuous_add h₁ h₂ K.add_mem
#align convex_cone.closure ConvexCone.closure

@[simp, norm_cast]
theorem coe_closure (K : ConvexCone 𝕜 E) : (K.closure : Set E) = closure K :=
  rfl
#align convex_cone.coe_closure ConvexCone.coe_closure

@[simp]
protected theorem mem_closure {K : ConvexCone 𝕜 E} {a : E} :
    a ∈ K.closure ↔ a ∈ closure (K : Set E) :=
  Iff.rfl
#align convex_cone.mem_closure ConvexCone.mem_closure

@[simp]
theorem closure_eq {K L : ConvexCone 𝕜 E} : K.closure = L ↔ closure (K : Set E) = L :=
  SetLike.ext'_iff
#align convex_cone.closure_eq ConvexCone.closure_eq

end ConvexCone

/-- A proper cone is a convex cone `K` that is nonempty and closed. Proper cones have the nice
property that the dual of the dual of a proper cone is itself. This makes them useful for defining
cone programs and proving duality theorems. -/
structure ProperCone (𝕜 : Type*) (E : Type*) [OrderedSemiring 𝕜] [AddCommMonoid E]
    [TopologicalSpace E] [SMul 𝕜 E] extends ConvexCone 𝕜 E where
  nonempty' : (carrier : Set E).Nonempty
  isClosed' : IsClosed (carrier : Set E)
#align proper_cone ProperCone

namespace ProperCone

section SMul

variable {𝕜 : Type*} [OrderedSemiring 𝕜]

variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [SMul 𝕜 E]

attribute [coe] toConvexCone

instance : Coe (ProperCone 𝕜 E) (ConvexCone 𝕜 E) :=
  ⟨toConvexCone⟩

-- Porting note: now a syntactic tautology
-- @[simp]
-- theorem toConvexCone_eq_coe (K : ProperCone 𝕜 E) : K.toConvexCone = K :=
--   rfl
#noalign proper_cone.to_convex_cone_eq_coe

theorem ext' : Function.Injective ((↑) : ProperCone 𝕜 E → ConvexCone 𝕜 E) := fun S T h => by
  cases S; cases T; congr
#align proper_cone.ext' ProperCone.ext'

-- TODO: add `ConvexConeClass` that extends `SetLike` and replace the below instance
instance : SetLike (ProperCone 𝕜 E) E where
  coe K := K.carrier
  coe_injective' _ _ h := ProperCone.ext' (SetLike.coe_injective h)

@[ext]
theorem ext {S T : ProperCone 𝕜 E} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
#align proper_cone.ext ProperCone.ext

@[simp]
theorem mem_coe {x : E} {K : ProperCone 𝕜 E} : x ∈ (K : ConvexCone 𝕜 E) ↔ x ∈ K :=
  Iff.rfl
#align proper_cone.mem_coe ProperCone.mem_coe

protected theorem nonempty (K : ProperCone 𝕜 E) : (K : Set E).Nonempty :=
  K.nonempty'
#align proper_cone.nonempty ProperCone.nonempty

protected theorem isClosed (K : ProperCone 𝕜 E) : IsClosed (K : Set E) :=
  K.isClosed'
#align proper_cone.is_closed ProperCone.isClosed

end SMul

section PositiveCone

variable (𝕜 E)
variable [OrderedSemiring 𝕜] [OrderedAddCommGroup E] [Module 𝕜 E] [OrderedSMul 𝕜 E]
  [TopologicalSpace E] [OrderClosedTopology E]

/-- The positive cone is the proper cone formed by the set of nonnegative elements in an ordered
module. -/
def positive : ProperCone 𝕜 E where
  toConvexCone := ConvexCone.positive 𝕜 E
  nonempty' := ⟨0, ConvexCone.pointed_positive _ _⟩
  isClosed' := isClosed_Ici

@[simp]
theorem mem_positive {x : E} : x ∈ positive 𝕜 E ↔ 0 ≤ x :=
  Iff.rfl

@[simp]
theorem coe_positive : ↑(positive 𝕜 E) = ConvexCone.positive 𝕜 E :=
  rfl

end PositiveCone

section Module

variable {𝕜 : Type*} [OrderedSemiring 𝕜]

variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [T1Space E] [Module 𝕜 E]

instance : Zero (ProperCone 𝕜 E) :=
  ⟨{  toConvexCone := 0
      nonempty' := ⟨0, rfl⟩
      isClosed' := isClosed_singleton }⟩

instance : Inhabited (ProperCone 𝕜 E) :=
  ⟨0⟩

@[simp]
theorem mem_zero (x : E) : x ∈ (0 : ProperCone 𝕜 E) ↔ x = 0 :=
  Iff.rfl
#align proper_cone.mem_zero ProperCone.mem_zero

@[simp, norm_cast]
theorem coe_zero : ↑(0 : ProperCone 𝕜 E) = (0 : ConvexCone 𝕜 E) :=
  rfl
#align proper_cone.coe_zero ProperCone.coe_zero

theorem pointed_zero : (0 : ProperCone 𝕜 E).Pointed := by simp [ConvexCone.pointed_zero]
#align proper_cone.pointed_zero ProperCone.pointed_zero

end Module

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

protected theorem pointed (K : ProperCone ℝ E) : (K : ConvexCone ℝ E).Pointed :=
  (K : ConvexCone ℝ E).pointed_of_nonempty_of_isClosed K.nonempty' K.isClosed
#align proper_cone.pointed ProperCone.pointed

/-- The closure of image of a proper cone under a continuous `ℝ`-linear map is a proper cone. We
use continuous maps here so that the comap of f is also a map between proper cones. -/
noncomputable def map (f : E →L[ℝ] F) (K : ProperCone ℝ E) : ProperCone ℝ F where
  toConvexCone := ConvexCone.closure (ConvexCone.map (f : E →ₗ[ℝ] F) ↑K)
  nonempty' :=
    ⟨0, subset_closure <| SetLike.mem_coe.2 <| ConvexCone.mem_map.2 ⟨0, K.pointed, map_zero _⟩⟩
  isClosed' := isClosed_closure
#align proper_cone.map ProperCone.map

@[simp, norm_cast]
theorem coe_map (f : E →L[ℝ] F) (K : ProperCone ℝ E) :
    ↑(K.map f) = (ConvexCone.map (f : E →ₗ[ℝ] F) ↑K).closure :=
  rfl
#align proper_cone.coe_map ProperCone.coe_map

@[simp]
theorem mem_map {f : E →L[ℝ] F} {K : ProperCone ℝ E} {y : F} :
    y ∈ K.map f ↔ y ∈ (ConvexCone.map (f : E →ₗ[ℝ] F) ↑K).closure :=
  Iff.rfl
#align proper_cone.mem_map ProperCone.mem_map

@[simp]
theorem map_id (K : ProperCone ℝ E) : K.map (ContinuousLinearMap.id ℝ E) = K :=
  ProperCone.ext' <| by simpa using IsClosed.closure_eq K.isClosed
#align proper_cone.map_id ProperCone.map_id

/-- The inner dual cone of a proper cone is a proper cone. -/
def dual (K : ProperCone ℝ E) : ProperCone ℝ E where
  toConvexCone := (K : Set E).innerDualCone
  nonempty' := ⟨0, pointed_innerDualCone _⟩
  isClosed' := isClosed_innerDualCone _
#align proper_cone.dual ProperCone.dual

@[simp, norm_cast]
theorem coe_dual (K : ProperCone ℝ E) : ↑(dual K) = (K : Set E).innerDualCone :=
  rfl
#align proper_cone.coe_dual ProperCone.coe_dual

@[simp]
theorem mem_dual {K : ProperCone ℝ E} {y : E} : y ∈ dual K ↔ ∀ ⦃x⦄, x ∈ K → 0 ≤ ⟪x, y⟫_ℝ := by
  rw [← mem_coe, coe_dual, mem_innerDualCone _ _]; rfl
#align proper_cone.mem_dual ProperCone.mem_dual

/-- The preimage of a proper cone under a continuous `ℝ`-linear map is a proper cone. -/
noncomputable def comap (f : E →L[ℝ] F) (S : ProperCone ℝ F) : ProperCone ℝ E where
  toConvexCone := ConvexCone.comap (f : E →ₗ[ℝ] F) S
  nonempty' :=
    ⟨0, by
      simp only [ConvexCone.comap, mem_preimage, map_zero, SetLike.mem_coe, mem_coe]
      apply ProperCone.pointed⟩
  isClosed' := by
    simp only [ConvexCone.comap, ContinuousLinearMap.coe_coe]
    apply IsClosed.preimage f.2 S.isClosed
#align proper_cone.comap ProperCone.comap

@[simp]
theorem coe_comap (f : E →L[ℝ] F) (S : ProperCone ℝ F) : (S.comap f : Set E) = f ⁻¹' S :=
  rfl
#align proper_cone.coe_comap ProperCone.coe_comap

@[simp]
theorem comap_id (S : ConvexCone ℝ E) : S.comap LinearMap.id = S :=
  SetLike.coe_injective preimage_id
#align proper_cone.comap_id ProperCone.comap_id

theorem comap_comap (g : F →L[ℝ] G) (f : E →L[ℝ] F) (S : ProperCone ℝ G) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  SetLike.coe_injective <| by congr
#align proper_cone.comap_comap ProperCone.comap_comap

@[simp]
theorem mem_comap {f : E →L[ℝ] F} {S : ProperCone ℝ F} {x : E} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl
#align proper_cone.mem_comap ProperCone.mem_comap

end InnerProductSpace

section CompleteSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The dual of the dual of a proper cone is itself. -/
@[simp]
theorem dual_dual (K : ProperCone ℝ E) : K.dual.dual = K :=
  ProperCone.ext' <|
    (K : ConvexCone ℝ E).innerDualCone_of_innerDualCone_eq_self K.nonempty' K.isClosed
#align proper_cone.dual_dual ProperCone.dual_dual

/-- This is a relative version of
`ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_nmem`, which we recover by setting
`f` to be the identity map. This is a geometric interpretation of the Farkas' lemma
stated using proper cones. -/
theorem hyperplane_separation (K : ProperCone ℝ E) {f : E →L[ℝ] F} {b : F} :
    b ∈ K.map f ↔ ∀ y : F, adjoint f y ∈ K.dual → 0 ≤ ⟪y, b⟫_ℝ :=
  Iff.intro
    (by
      -- suppose `b ∈ K.map f`
      simp only [ProperCone.mem_map, ProperCone.mem_dual, adjoint_inner_right,
        ConvexCone.mem_closure, mem_closure_iff_seq_limit]
      -- there is a sequence `seq : ℕ → F` in the image of `f` that converges to `b`
      rintro ⟨seq, hmem, htends⟩ y hinner
      suffices h : ∀ n, 0 ≤ ⟪y, seq n⟫_ℝ from
        ge_of_tendsto'
          (Continuous.seqContinuous (Continuous.inner (@continuous_const _ _ _ _ y) continuous_id)
            htends)
          h
      intro n
      obtain ⟨_, h, hseq⟩ := hmem n
      simpa only [← hseq, real_inner_comm] using hinner h)
    (by
      -- proof by contradiction
      -- suppose `b ∉ K.map f`
      intro h
      contrapose! h
      -- as `b ∉ K.map f`, there is a hyperplane `y` separating `b` from `K.map f`
      obtain ⟨y, hxy, hyb⟩ :=
        ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_nmem _ (K.map f).nonempty
          (K.map f).isClosed h
      -- the rest of the proof is a straightforward algebraic manipulation
      refine' ⟨y, _, hyb⟩
      simp_rw [ProperCone.mem_dual, adjoint_inner_right]
      intro x hxK
      apply hxy (f x)
      rw [ProperCone.coe_map]
      apply subset_closure
      rw [SetLike.mem_coe, ConvexCone.mem_map]
      refine' ⟨x, hxK, by rw [coe_coe]⟩)
#align proper_cone.hyperplane_separation ProperCone.hyperplane_separation

theorem hyperplane_separation_of_nmem (K : ProperCone ℝ E) {f : E →L[ℝ] F} {b : F}
    (disj : b ∉ K.map f) : ∃ y : F, adjoint f y ∈ K.dual ∧ ⟪y, b⟫_ℝ < 0 := by
  contrapose! disj; rwa [K.hyperplane_separation]
#align proper_cone.hyperplane_separation_of_nmem ProperCone.hyperplane_separation_of_nmem

end CompleteSpace

end ProperCone
