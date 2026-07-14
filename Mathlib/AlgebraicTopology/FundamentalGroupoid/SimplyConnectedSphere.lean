/-
Copyright (c) 2026 Sebastian Kumar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Kumar
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# The `n`-dimensional sphere is simply connected for `n ≥ 2`.

This file follows the proof from [hatcher02] that the `n`-sphere is simply connected for `n ≥ 2`,
culminating in `EuclideanSphere.simplyConnectedSpace`.

## Notations

- `𝕊 n` denotes the `n`-sphere in `EuclideanSpace ℝ (Fin (n + 1))`.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher02]
-/

@[expose] public section

open Fin Function Path Set unitInterval
open scoped EuclideanSpace

-- We first establish some lemmas about the Euclidean sphere.
namespace EuclideanSphere

/-- `𝕊 n` is the `n`-dimensional sphere, so it lives in `(n + 1)`-dimensional Euclidean space. -/
scoped notation "𝕊" => fun (n : ℕ) ↦ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

variable {n : ℕ}

instance : Nonempty (𝕊 n) := Nonempty.to_subtype (NormedSpace.sphere_nonempty.mpr (by norm_num))

instance : Infinite (𝕊 (n + 1)) := by
  rw [← infinite_univ_iff]
  have v : 𝕊 (n + 1) := Nonempty.some inferInstance
  apply Infinite.of_image (stereographic' (n + 1) v)
  rw [image_univ]
  apply Infinite.mono (PartialEquiv.target_subset_range (stereographic' (n + 1) v).toPartialEquiv)
  rw [stereographic'_target]
  exact infinite_univ

instance (n : ℕ) : PathConnectedSpace (𝕊 (n + 1)) := by
  rw [← isPathConnected_iff_pathConnectedSpace]
  apply isPathConnected_sphere
  · rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact Nat.one_lt_ofNat
  · exact zero_le_one' ℝ

/-- The sphere minus a point is contractible. -/
instance (v : 𝕊 n) : ContractibleSpace ({v}ᶜ : Set (𝕊 n)) := by
  let proj := stereographic' n v
  have : ContractibleSpace proj.target := by
    rw [stereographic'_target]
    exact Homeomorph.contractibleSpace (Homeomorph.Set.univ (EuclideanSpace ℝ (Fin n)))
  convert Homeomorph.contractibleSpace proj.toHomeomorphSourceTarget <;>
    exact (stereographic'_source v).symm

/-- The Euclidean `n`-sphere minus a point is path connected for `n ≥ 1`. -/
theorem isPathConnected_compl_singleton (v : 𝕊 (n + 1)) : IsPathConnected ({v}ᶜ) := by
  rw [isPathConnected_iff_pathConnectedSpace]
  infer_instance

lemma stereographic'_symm_zero (v : 𝕊 n) : (stereographic' n v).toPartialEquiv.symm 0 = -v := by
  ext
  simp [stereographic', stereographic, stereoInvFun]

/-- The Euclidean `n`-sphere minus two antipodal points is path connected for `n ≥ 2`. -/
theorem isPathConnected_compl_singleton_inter_neg (v : 𝕊 (n + 2)) :
    IsPathConnected ({v}ᶜ ∩ {-v}ᶜ) := by
  let proj := stereographic' (n + 2) v
  have : proj.toPartialEquiv.symm '' (proj.target \ {0}) = {v}ᶜ ∩ {-v}ᶜ := by
    rw [PartialEquiv.symm_image_target_minus_singleton_eq, stereographic'_source,
      stereographic'_symm_zero, sdiff_eq]
    rw [stereographic'_target]
    exact mem_univ 0
  rw [← this]
  apply IsPathConnected.image'
  · rw [stereographic'_target, ← compl_eq_univ_sdiff]
    exact isPathConnected_compl_singleton_of_one_lt_rank
      (by rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; exact Nat.one_lt_ofNat) 0
  · exact ContinuousOn.mono proj.continuousOn_invFun sdiff_subset

-- We now define the cover of `S n` to be used in `exists_loops_homotopic_concat_of_open_cover`.
variable {n : ℕ}

/-- `c v` is the open cover of `S n` by the complement of `v` and the complement of `-v`. -/
private abbrev c (v : 𝕊 n) : Fin 2 → Set (𝕊 n) := cases {v}ᶜ (fun _ ↦ {-v}ᶜ)

private lemma hc₁ (v : 𝕊 n) : ∀ i, IsOpen (c v i) := by apply cases <;> simp

private lemma hc₂ (v : 𝕊 n) : univ ⊆ ⋃ i, c v i := by
  intro s _
  rcases eq_or_ne s v with rfl | h
  · rw [mem_iUnion]
    use 1
    change s ∈ ({-s}ᶜ : Set (𝕊 n))
    rw [mem_compl_iff, mem_singleton_iff, ← Ne, ← Subtype.coe_ne_coe, coe_neg_sphere]
    intro hv
    apply (ne_zero_of_mem_unit_sphere s)
    ext k
    rw [PiLp.zero_apply, ← CharZero.eq_neg_self_iff, ← PiLp.neg_apply, ← hv]
  · rw [Set.mem_iUnion]
    use 0
    exact h

private lemma hc₃ (v : 𝕊 (n + 2)) : ∀ i j, IsPathConnected (c v i ∩ c v j) := by
  apply cases
  · apply cases
    · simp only [cases_zero, inter_self]
      exact isPathConnected_compl_singleton v
    · intro _
      simp only [cases_zero, cases_succ]
      exact isPathConnected_compl_singleton_inter_neg v
  · intro _
    apply cases
    · simp only [cases_succ, cases_zero, inter_comm]
      exact isPathConnected_compl_singleton_inter_neg v
    · intro _
      simp only [cases_succ, inter_self]
      exact isPathConnected_compl_singleton (-v)

private lemma hx (x : 𝕊 (n + 1)) : ∃ v, ∀ i : Fin 2, x ∈ c v i := by
  have ⟨v, hv⟩ := Infinite.exists_notMem_finset {x, -x}
  use v
  apply cases
  · simp only [cases_zero, mem_compl_singleton_iff]
    intro h
    apply hv
    rw [Finset.mem_insert]
    exact Or.inl h.symm
  · simp only [cases_succ, mem_compl_singleton_iff]
    intro _ h
    apply hv
    rw [Finset.mem_insert, Finset.mem_singleton, h]
    exact Or.inr (neg_neg v).symm

/-- A non-surjective path in the Euclidean sphere is homotopic to a constant path. -/
theorem homotopic_refl_of_not_surjective {n : ℕ} {v : 𝕊 n} (γ : Path v v)
    (h : ¬(Surjective γ)) : γ.Homotopic (refl v) := by
  unfold Surjective at h
  push Not at h
  obtain ⟨w, hw⟩ := h
  let w_compl : Set (𝕊 n) := {w}ᶜ
  let v' : w_compl := ⟨v, by
    rw [mem_compl_singleton_iff]
    convert hw 0
    exact γ.source.symm⟩
  let f : I → γ⁻¹' {w}ᶜ := fun x ↦ ⟨x, hw x⟩
  let γ' : Path v' v' := {
    toFun := γ.restrictPreimage {w}ᶜ ∘ f
    source' := by rw [comp_apply, ContinuousMap.restrictPreimage_apply]; ext; simp [f, v']
    target' := by rw [comp_apply, ContinuousMap.restrictPreimage_apply]; ext; simp [f, v']
  }
  have h : SimplyConnectedSpace w_compl := inferInstance
  let incl : C(w_compl, 𝕊 n) := ⟨Subtype.val, continuous_subtype_val⟩
  exact Homotopic.map ((simply_connected_iff_loops_nullhomotopic.mp h).right v' γ') incl

/-- The Euclidean `n`-sphere is simply connected for `n ≥ 2`. -/
protected theorem simplyConnectedSpace (n : ℕ) : SimplyConnectedSpace (𝕊 (n + 2)) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  constructor
  · infer_instance
  · intro x p
    let ⟨v, hv⟩ := hx x
    have ⟨m, D, hDh, hDr⟩ := Homotopic.exists_loops_homotopic_concat_of_open_cover
      (hc₁ v) (hc₂ v) (hc₃ v) hv p
    apply Homotopic.trans hDh.symm
    rw [← concat_refl]
    apply Homotopic.concat_hcomp
    intro k
    have ⟨i, hi⟩ := hDr k
    fin_cases i
    · simp only [zero_eta, cases_zero] at hi
      apply homotopic_refl_of_not_surjective
      exact fun h ↦ hi (h v) rfl
    · have : (1 : Fin 2) = succ 0 := rfl
      simp only [mk_one, this, cases_succ] at hi
      apply homotopic_refl_of_not_surjective
      exact fun a ↦ hi (a (-v)) rfl

instance (n : ℕ) : SimplyConnectedSpace (𝕊 (n + 2)) := EuclideanSphere.simplyConnectedSpace n

end EuclideanSphere
