/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Newell Jensen
-/
module

public import Mathlib.Topology.MetricSpace.Dilation
import Batteries.Tactic.Trans
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
meta import Mathlib.Tactic.Attr.Register
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
# Congruences

This file defines `Congruent`, i.e., the equivalence between indexed families of points in a metric
space where all corresponding pairwise distances are the same. The motivating example are
triangles in the plane.

## Implementation notes

After considering two possible approaches to defining congruence — either based on equal pairwise
distances or the existence of an isometric equivalence — we have opted for the broader concept of
equal pairwise distances. This notion is commonly employed in the literature across various metric
spaces that lack an isometric equivalence.

For more details see the [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Euclidean.20Geometry).

## Notation

* `v₁ ≅ v₂`: for `Congruent v₁ v₂`.
-/

@[expose] public section

variable {ι ι' : Type*} {P₁ P₂ P₃ P₄ : Type*} {v₁ : ι → P₁} {v₂ : ι → P₂} {v₃ : ι → P₃}

section PseudoEMetricSpace

variable [PseudoEMetricSpace P₁] [PseudoEMetricSpace P₂]
variable [PseudoEMetricSpace P₃] [PseudoEMetricSpace P₄]

/-- A congruence between indexed sets of vertices v₁ and v₂.
Use `open scoped Congruent` to access the `v₁ ≅ v₂` notation. -/
def Congruent (v₁ : ι → P₁) (v₂ : ι → P₂) : Prop :=
  ∀ i₁ i₂, edist (v₁ i₁) (v₁ i₂) = edist (v₂ i₁) (v₂ i₂)

@[inherit_doc]
scoped[Congruent] infixl:25 " ≅ " => Congruent

/-- Congruence holds if and only if all extended distances are the same. -/
lemma congruent_iff_edist_eq :
    Congruent v₁ v₂ ↔ ∀ i₁ i₂, edist (v₁ i₁) (v₁ i₂) = edist (v₂ i₁) (v₂ i₂) :=
  Iff.rfl

/-- Congruence holds if and only if all extended distances between points with different
indices are the same. -/
lemma congruent_iff_pairwise_edist_eq :
    Congruent v₁ v₂ ↔ Pairwise fun i₁ i₂ ↦ edist (v₁ i₁) (v₁ i₂) = edist (v₂ i₁) (v₂ i₂) := by
  refine ⟨fun h ↦ fun _ _ _ ↦ h _ _, fun h ↦ fun i₁ i₂ ↦ ?_⟩
  by_cases hi : i₁ = i₂
  · simp [hi]
  · exact h hi

namespace Congruent

/-- A congruence preserves extended distance. Forward direction of `congruent_iff_edist_eq`. -/
alias ⟨edist_eq, _⟩ := congruent_iff_edist_eq

/-- Congruence follows from preserved extended distance. Backward direction of
`congruent_iff_edist_eq`. -/
alias ⟨_, of_edist_eq⟩ := congruent_iff_edist_eq

/-- A congruence pairwise preserves extended distance. Forward direction of
`congruent_iff_pairwise_edist_eq`. -/
alias ⟨pairwise_edist_eq, _⟩ := congruent_iff_pairwise_edist_eq

/-- Congruence follows from pairwise preserved extended distance. Backward direction of
`congruent_iff_pairwise_edist_eq`. -/
alias ⟨_, of_pairwise_edist_eq⟩ := congruent_iff_pairwise_edist_eq

@[refl] protected lemma refl (v₁ : ι → P₁) : v₁ ≅ v₁ := fun _ _ ↦ rfl

@[symm] protected lemma symm (h : v₁ ≅ v₂) : v₂ ≅ v₁ := fun i₁ i₂ ↦ (h i₁ i₂).symm

lemma _root_.congruent_comm : v₁ ≅ v₂ ↔ v₂ ≅ v₁ :=
  ⟨Congruent.symm, Congruent.symm⟩

@[trans] protected lemma trans (h₁₂ : v₁ ≅ v₂) (h₂₃ : v₂ ≅ v₃) : v₁ ≅ v₃ :=
  fun i₁ i₂ ↦ (h₁₂ i₁ i₂).trans (h₂₃ i₁ i₂)

/-- Change the index set ι to an index ι' that maps to ι. -/
lemma index_map (h : v₁ ≅ v₂) (f : ι' → ι) : (v₁ ∘ f) ≅ (v₂ ∘ f) :=
  fun i₁ i₂ ↦ edist_eq h (f i₁) (f i₂)

/-- Change between equivalent index sets ι and ι'. -/
@[simp] lemma index_equiv {E : Type*} [EquivLike E ι' ι] (f : E) (v₁ : ι → P₁) (v₂ : ι → P₂) :
    v₁ ∘ f ≅ v₂ ∘ f ↔ v₁ ≅ v₂ := by
  refine ⟨fun h i₁ i₂ ↦ ?_, fun h ↦ index_map h f⟩
  simpa [(EquivLike.toEquiv f).right_inv i₁, (EquivLike.toEquiv f).right_inv i₂]
    using edist_eq h ((EquivLike.toEquiv f).symm i₁) ((EquivLike.toEquiv f).symm i₂)

/-- Families with at most a single point are always congruent. -/
@[nontriviality, simp]
lemma of_subsingleton_index [Subsingleton ι] : v₁ ≅ v₂ :=
  fun i j => by simp [Subsingleton.elim i j]

lemma comp_left {f : P₁ → P₃} (hf : Isometry f) (h : v₁ ≅ v₂) : f ∘ v₁ ≅ v₂ :=
  .trans (fun _ _ ↦ hf _ _) h

lemma comp_right {f : P₂ → P₃} (hf : Isometry f) (h : v₁ ≅ v₂) : v₁ ≅ f ∘ v₂ :=
  .trans h (.symm <| fun _ _ ↦ hf _ _)

@[simp]
lemma comp_left_iff {f : P₁ → P₃} (hf : Isometry f) : f ∘ v₁ ≅ v₂ ↔ v₁ ≅ v₂ :=
  ⟨.trans <| .comp_right hf (.refl _), .comp_left hf⟩

@[simp]
lemma comp_right_iff {f : P₂ → P₃} (hf : Isometry f) : v₁ ≅ f ∘ v₂ ↔ v₁ ≅ v₂ := by
  rw [congruent_comm, comp_left_iff hf, congruent_comm]

/-- Two sets of vertices remain congruent under a dilation if the dilations have equal ratios. -/
lemma comp_dilation {F₁ F₂}
    [FunLike F₁ P₁ P₃] [DilationClass F₁ P₁ P₃] [FunLike F₂ P₂ P₄] [DilationClass F₂ P₂ P₄]
    {f₁ : F₁} {f₂ : F₂} (h : v₁ ≅ v₂) (hf : Dilation.ratio f₁ = Dilation.ratio f₂) :
    f₁ ∘ v₁ ≅ f₂ ∘ v₂ :=
  fun i j => by simp [hf, h i j]

end Congruent

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace P₁] [PseudoMetricSpace P₂]

/-- Congruence holds if and only if all non-negative distances are the same. -/
lemma congruent_iff_nndist_eq :
    Congruent v₁ v₂ ↔ ∀ i₁ i₂, nndist (v₁ i₁) (v₁ i₂) = nndist (v₂ i₁) (v₂ i₂) :=
  forall₂_congr (fun _ _ ↦ by rw [edist_nndist, edist_nndist]; norm_cast)

/-- Congruence holds if and only if all non-negative distances between points with different
indices are the same. -/
lemma congruent_iff_pairwise_nndist_eq :
    Congruent v₁ v₂ ↔ Pairwise fun i₁ i₂ ↦ nndist (v₁ i₁) (v₁ i₂) = nndist (v₂ i₁) (v₂ i₂) := by
  simp_rw [congruent_iff_pairwise_edist_eq, edist_nndist]
  exact_mod_cast Iff.rfl

/-- Congruence holds if and only if all distances are the same. -/
lemma congruent_iff_dist_eq :
    Congruent v₁ v₂ ↔ ∀ i₁ i₂, dist (v₁ i₁) (v₁ i₂) = dist (v₂ i₁) (v₂ i₂) :=
  congruent_iff_nndist_eq.trans
    (forall₂_congr (fun _ _ ↦ by rw [dist_nndist, dist_nndist]; norm_cast))

/-- Congruence holds if and only if all non-negative distances between points with different
indices are the same. -/
lemma congruent_iff_pairwise_dist_eq :
    Congruent v₁ v₂ ↔ Pairwise fun i₁ i₂ ↦ dist (v₁ i₁) (v₁ i₂) = dist (v₂ i₁) (v₂ i₂) := by
  simp_rw [congruent_iff_pairwise_nndist_eq, dist_nndist]
  exact_mod_cast Iff.rfl

namespace Congruent

/-- A congruence preserves non-negative distance. Forward direction of `congruent_iff_nndist_eq`. -/
alias ⟨nndist_eq, _⟩ := congruent_iff_nndist_eq

/-- Congruence follows from preserved non-negative distance. Backward direction of
`congruent_iff_nndist_eq`. -/
alias ⟨_, of_nndist_eq⟩ := congruent_iff_nndist_eq

/-- A congruence preserves distance. Forward direction of `congruent_iff_dist_eq`. -/
alias ⟨dist_eq, _⟩ := congruent_iff_dist_eq

/-- Congruence follows from preserved distance. Backward direction of `congruent_iff_dist_eq`. -/
alias ⟨_, of_dist_eq⟩ := congruent_iff_dist_eq

/-- A congruence pairwise preserves non-negative distance. Forward direction of
`congruent_iff_pairwise_nndist_eq`. -/
alias ⟨pairwise_nndist_eq, _⟩ := congruent_iff_pairwise_nndist_eq

/-- Congruence follows from pairwise preserved non-negative distance. Backward direction of
`congruent_iff_pairwise_nndist_eq`. -/
alias ⟨_, of_pairwise_nndist_eq⟩ := congruent_iff_pairwise_nndist_eq

/-- A congruence pairwise preserves distance. Forward direction of
`congruent_iff_pairwise_dist_eq`. -/
alias ⟨pairwise_dist_eq, _⟩ := congruent_iff_pairwise_dist_eq

/-- Congruence follows from pairwise preserved distance. Backward direction of
`congruent_iff_pairwise_dist_eq`. -/
alias ⟨_, of_pairwise_dist_eq⟩ := congruent_iff_pairwise_dist_eq

end Congruent

end PseudoMetricSpace
