/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Newell Jensen
-/
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Congruences

In this file we define congruence, i.e., the equivalence between sets of points in
a metric space where all corresponding pairwise distances are the same. The motivating
example are triangles in the plane.

## Main results

In the case of an `EMetricSpace` we show an `IsometryEquiv` between the points:
`Set.range v₁ ≃ᵢ Set.range v₂`.

## Notation

* `v₁ ≅ v₂`: for `congruence v₁ v₂`.
-/

variable {ι ι' : Type*} {P₁ P₂ P₃ : Type*} {v₁ : ι → P₁} {v₂ : ι → P₂} {v₃ : ι → P₃}

noncomputable section

/-- A congruence between indexed sets of vertices v₁ and v₂.
Use `open scoped Congruence` to access the `v₁ ≅ v₂` notation. -/
def congruence (v₁ : ι → P₁) (v₂ : ι → P₂) [PseudoEMetricSpace P₁]
    [PseudoEMetricSpace P₂] : Prop :=
  ∀ (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) = edist (v₂ i₁) (v₂ i₂))

@[inherit_doc]
scoped[Congruence] infixl:25 " ≅ " => congruence

/-- A congruence holds if and only if all extended distances are the same. -/
lemma congruence_iff_edist_eq [PseudoEMetricSpace P₁] [PseudoEMetricSpace P₂] :
    congruence v₁ v₂ ↔ (∀ (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) = edist (v₂ i₁) (v₂ i₂))) :=
  forall₂_congr (fun _ _ => by simp only [edist])

/-- A congruence holds if and only if all non-negative distances are the same. -/
lemma congruence_iff_nndist_eq [PseudoMetricSpace P₁] [PseudoMetricSpace P₂] :
    congruence v₁ v₂ ↔ (∀ (i₁ i₂ : ι), (nndist (v₁ i₁) (v₁ i₂) = nndist (v₂ i₁) (v₂ i₂))) :=
  forall₂_congr (fun _ _ => by rw [edist_nndist, edist_nndist]; norm_cast )

/-- A congruence holds if and only if all distances are the same. -/
lemma congruence_iff_dist_eq [PseudoMetricSpace P₁] [PseudoMetricSpace P₂] :
    congruence v₁ v₂ ↔ (∀ (i₁ i₂ : ι), (dist (v₁ i₁) (v₁ i₂) = dist (v₂ i₁) (v₂ i₂))) :=
  congruence_iff_nndist_eq.trans
    (forall₂_congr (fun _ _ => by rw [dist_nndist, dist_nndist]; norm_cast))


namespace Congruence

/-- A congruence preserves extended distance. -/
alias ⟨edist_eq, _⟩ := congruence_iff_edist_eq

/-- A congruence follows from preserved extended distance. -/
alias ⟨_, of_edist_eq⟩ := congruence_iff_edist_eq

/-- A congruence preserves non-negative distance. -/
alias ⟨nndist_eq, _⟩ := congruence_iff_nndist_eq

/-- A congruence follows from preserved non-negative distance. -/
alias ⟨_, of_nndist_eq⟩ := congruence_iff_nndist_eq

/-- A congruence preserves distance. -/
alias ⟨dist_eq, _⟩ := congruence_iff_dist_eq

/-- A congruence follows from preserved distance. -/
alias ⟨_, of_dist_eq⟩ := congruence_iff_dist_eq

/-- A congruence follows from pairwise preserved extended distance. -/
lemma of_Pairwise_edist_eq [PseudoEMetricSpace P₁] [PseudoEMetricSpace P₂] [DecidableEq ι]
    (h : Pairwise (fun i₁ i₂ => (edist (v₁ i₁) (v₁ i₂) =
      edist (v₂ i₁) (v₂ i₂)))) : v₁ ≅ v₂ :=
  fun i₁ i₂ => if g : i₁ = i₂ then by rw [g]; simp else h g

/-- A congruence follows from pairwise preserved non-negative distance. -/
lemma of_Pairwise_nndist_eq [PseudoMetricSpace P₁] [PseudoMetricSpace P₂] [DecidableEq ι]
    (h : Pairwise (fun i₁ i₂ => (nndist (v₁ i₁) (v₁ i₂) = nndist (v₂ i₁) (v₂ i₂)))) : v₁ ≅ v₂ :=
  of_Pairwise_edist_eq (fun i₁ i₂ hn => by
    simp only [edist_nndist]
    norm_cast
    exact h hn)

/-- A congruence follows from pairwise preserved distance. -/
lemma of_Pairwise_dist_eq [PseudoMetricSpace P₁] [PseudoMetricSpace P₂] [DecidableEq ι]
    (h : Pairwise (fun i₁ i₂ => dist (v₁ i₁) (v₁ i₂) = dist (v₂ i₁) (v₂ i₂))) : v₁ ≅ v₂ :=
  of_Pairwise_nndist_eq (fun i₁ i₂ hn => by
    have := h hn
    simp only [dist_nndist] at this
    norm_cast at this)


section PseudoEMetricSpace

variable [PseudoEMetricSpace P₁] [PseudoEMetricSpace P₂] [PseudoEMetricSpace P₃]


@[refl] protected lemma refl (v₁ : ι → P₁): v₁ ≅ v₁ := fun _ _ => rfl

@[symm] protected lemma symm (h : v₁ ≅ v₂) : v₂ ≅ v₁ := fun i₁ i₂ => (h i₁ i₂).symm

lemma _root_.congruence_comm : v₁ ≅ v₂ ↔ v₂ ≅ v₁ :=
  ⟨Congruence.symm, Congruence.symm⟩

@[trans] protected lemma trans (h₁₂ : v₁ ≅ v₂) (h₂₃ : v₂ ≅ v₃) : v₁ ≅ v₃ :=
  fun i₁ i₂ => (h₁₂ i₁ i₂).trans (h₂₃ i₁ i₂)

/-- Change the index set ι to an index ι' that maps to ι. -/
lemma index_map (h : v₁ ≅ v₂) (f : ι' → ι) : (v₁ ∘ f) ≅ (v₂ ∘ f) :=
  fun i₁ i₂ => edist_eq h (f i₁) (f i₂)

/-- Change between equivalent index sets ι and ι'. -/
lemma index_equiv (f : ι' ≃ ι) (v₁ : ι → P₁) (v₂ : ι → P₂) :
    v₁ ∘ f ≅ v₂ ∘ f ↔ v₁ ≅ v₂ := by
  refine' ⟨fun h i₁ i₂ => _, fun h => index_map h f⟩
  simpa [Equiv.right_inv f i₁, Equiv.right_inv f i₂] using edist_eq h (f.symm i₁) (f.symm i₂)

end PseudoEMetricSpace


section EMetricSpace

variable [EMetricSpace P₁] [EMetricSpace P₂] [EMetricSpace P₃]

/-- `congruence_map` maps the congruent points in one space to the corresponding points
in the other space. -/
def congruence_map (v₁ : ι → P₁) (v₂ : ι → P₂) : Set.range v₁ → Set.range v₂ :=
  fun a => Set.rangeFactorization v₂ <| Set.rangeSplitting v₁ a

lemma map_refl_apply (a : Set.range v₁) : congruence_map v₁ v₁ a = a := by
  rw [Subtype.ext_iff]
  apply Set.apply_rangeSplitting v₁

/-- `congruence_map` does indeed preserve corresponding points -/
lemma map_sound (h : v₁ ≅ v₂) (i : ι) :
    (congruence_map v₁ v₂ (Set.rangeFactorization v₁ i)) = v₂ i := by
  unfold congruence_map
  rw [Set.rangeFactorization_coe v₂, ← edist_eq_zero, ← h, edist_eq_zero,
    Set.apply_rangeSplitting v₁, Set.rangeFactorization_coe v₁]

lemma map_comp_apply (h : v₂ ≅ v₃) (a : Set.range v₁) :
    congruence_map v₂ v₃ (congruence_map v₁ v₂ a) = congruence_map v₁ v₃ a := by
  rw [Subtype.ext_iff]
  unfold congruence_map
  rw [Set.rangeFactorization_coe v₃]
  exact map_sound h (Set.rangeSplitting v₁ a)

lemma map_comp (v₁ : ι → P₁) (h : v₂ ≅ v₃) :
    (congruence_map v₂ v₃) ∘ congruence_map v₁ v₂ = congruence_map v₁ v₃ :=
  funext <| fun a => map_comp_apply h a

/-- `congruence_map v₁ v₂` and `congruence_map v₂ v₁` are inverses to eachother -/
lemma map_inverse_self (h : v₁ ≅ v₂) :
    Function.LeftInverse (congruence_map v₂ v₁) (congruence_map v₁ v₂) := by
  intro x
  rw [map_comp_apply <| Congruence.symm h]
  exact map_refl_apply x

/-- `congruence_map` as an `IsometryEquiv` -/
protected def isometry (h : v₁ ≅ v₂) : Set.range v₁ ≃ᵢ Set.range v₂ :=
{ toFun := congruence_map v₁ v₂
  invFun := congruence_map v₂ v₁
  left_inv := map_inverse_self h
  right_inv := map_inverse_self <| Congruence.symm h
  isometry_toFun := by
    intros fx fy
    rw [Subtype.edist_eq fx fy]
    rw [← Set.apply_rangeSplitting v₁ fx, ← Set.apply_rangeSplitting v₁ fy]
    rw [edist_eq h]
    rfl
}

lemma isometry_refl_apply (a : Set.range v₁) :
    Congruence.isometry (Congruence.refl v₁) a = a :=
  map_refl_apply a

lemma isometry_symm (h : v₁ ≅ v₂) : Congruence.isometry (Congruence.symm h) =
    IsometryEquiv.symm (Congruence.isometry h) :=
  rfl

lemma isometry_sound (h : v₁ ≅ v₂) (i : ι) :
    (Congruence.isometry h (Set.rangeFactorization v₁ i)) = v₂ i :=
  map_sound h i

lemma isometry_comp_apply (h₁₂ : v₁ ≅ v₂) (h₂₃ : v₂ ≅ v₃) (a : Set.range v₁) :
    Congruence.isometry h₂₃ (Congruence.isometry h₁₂ a) =
    Congruence.isometry (Congruence.trans h₁₂ h₂₃) a :=
  map_comp_apply h₂₃ a

lemma isometry_comp (h₁₂ : v₁ ≅ v₂) (h₂₃ : v₂ ≅ v₃) :
    Congruence.isometry h₂₃ ∘ Congruence.isometry h₁₂ =
    Congruence.isometry (Congruence.trans h₁₂ h₂₃) :=
  map_comp v₁ h₂₃

lemma isometry_trans (h₁₂ : v₁ ≅ v₂) (h₂₃ : v₂ ≅ v₃) :
    Congruence.isometry (Congruence.trans h₁₂ h₂₃) =
    IsometryEquiv.trans (Congruence.isometry h₁₂) (Congruence.isometry h₂₃) := by
  simp only [Congruence.isometry]
  congr
  · rw [← map_comp v₁ h₂₃]; rfl
  · rw [← map_comp v₃ (Congruence.symm h₁₂)]; rfl

end EMetricSpace

end Congruence
