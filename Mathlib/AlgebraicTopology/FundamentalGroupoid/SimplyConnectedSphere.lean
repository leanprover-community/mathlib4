/-
Copyright (c) 2025 Sebastian Kumar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Kumar
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Tactic.DepRewrite
import Mathlib.Topology.FoldTrans

/-!
# The `n`-dimensional sphere is simply connected for `n ≥ 2`.

This file follows the proof from [hatcher02] that the `n`-sphere is simply connected for `n ≥ 2`.

## Main results

- `exists_loops_homotopic_foldTrans_of_open_cover`: lemma 1.15 from [hatcher02].
- `homotopic_refl_of_not_surjective`: non-surjective loops in the sphere are homotopically trivial.
- `EuclideanSphere.simplyConnectedSpace`: the `n`-sphere is simply connected for `n ≥ 2`.

## Notations

- `S n` denotes the `n`-sphere in `EuclideanSpace ℝ (Fin (n + 1))`.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher02]
-/

open CategoryTheory Fin Function FundamentalGroupoid PartialEquiv Path PiLp Set unitInterval

universe u v

-- This first section builds up to proving `exists_loops_homotopic_foldTrans_of_open_cover`.
section

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {c : ι → Set X} {a b : X}

namespace Path

/-- Given a path `γ` in a space `X` and an open cover of `X`, we can pull back to a partition
of `[0, 1]` such that, on each element, `γ` is contained in a fixed element of our open cover. -/
theorem exists_partition_unitInterval_of_open_cover (hc₁ : ∀ i, IsOpen (c i))
    (hc₂ : univ ⊆ ⋃ i, c i) (γ : Path a a) : ∃ (n : ℕ) (t : Fin (n + 2) → I),
    t 0 = 0 ∧ t (last (n + 1)) = 1 ∧
      ∀ k : Fin (n + 1), ∃ i, γ '' (uIcc (t k.castSucc) (t k.succ)) ⊆ c i := by
  have ⟨t, ht₀, ht_mono, ⟨n, ht₁⟩, ht_sub⟩ := exists_monotone_Icc_subset_open_cover_unitInterval
    (fun i ↦ IsOpen.preimage (Path.continuous γ) (hc₁ i))
    (fun s _ ↦ (preimage_iUnion ▸ hc₂ (mem_univ _)))
  use n, t ∘ Fin.toNat
  simp [ht₀, ht₁]
  intro k
  have ⟨i, hi⟩ := ht_sub k
  use i
  rwa [uIcc_of_le]
  exact ht_mono (Nat.le_add_right _ _)

/-- If we have a cover with pairwise path connected intersections, then we can extract a sequence
of paths whose range lie in such intersections. -/
theorem exists_path_range_of_isPathConnected_inter (hc₃ : ∀ i j, IsPathConnected (c i ∩ c j))
    (ha : ∀ i, a ∈ c i) {n : ℕ} (τ : Fin (n + 1) → ι) (p : Fin (n + 2) → X)
    (hτ₁ : ∀ k, p k.castSucc ∈ c (τ k)) (hτ₂ : ∀ k, p k.succ ∈ c (τ k)) :
    ∀ k : Fin n, ∃ g : Path a (p k.succ.castSucc),
      Set.range g ⊆ c (τ k.castSucc) ∩ c (τ k.succ) := by
  intro k
  have ⟨γ, hγ⟩ := (hc₃ (τ k.castSucc) (τ k.succ)).joinedIn
    a ⟨ha (τ k.castSucc), ha (τ k.succ)⟩ (p k.castSucc.succ) ⟨hτ₂ k.castSucc, hτ₁ k.succ⟩
  use γ
  exact range_subset_iff.mpr hγ

namespace Homotopic

/-- This lemma looks complicated but amounts to cancelling out each path `G k` with its reverse. -/
lemma foldTrans_trans_trans_symm {n : ℕ} (p q : Fin (n + 1) → X)
    (F : ∀ k : Fin n, Path (p k.castSucc) (p k.succ)) (G : ∀ k : Fin (n + 1), Path (q k) (p k)) :
    (foldTrans q (fun k ↦ ((G (k.castSucc)).trans (F k)).trans (G (k.succ)).symm)).Homotopic
      (((G 0).trans (foldTrans p F)).trans (G (last n)).symm) := by
  induction' n with n hn
  · simp_rw [foldTrans_zero, ← fromPath'_eq_iff_homotopic]
    aesop_cat
  · simp_rw [foldTrans_succ]
    have := fromPath'_eq_iff_homotopic.mpr
      (hn (p ∘ castSucc) (q ∘ castSucc) (fun k ↦ F (k.castSucc)) (fun k ↦ G (k.castSucc)))
    rw [← fromPath'_eq_iff_homotopic]
    aesop_cat

/-- Technical lemma to prove homotopy in `exists_loops_homotopic_foldTrans_of_open_cover`. -/
lemma cast_trans_trans_homotopic_of_homotopic_cast {x x₀ x₁ : X} {h₀ : x₀ = x} {h₁ : x₁ = x}
    {p : Path x₀ x₁} {q : Path x x} (h : p.Homotopic (q.cast h₀ h₁)) :
    ((((Path.refl x).cast rfl h₀).trans p).trans ((Path.refl x).cast h₁ rfl)).Homotopic q := by
  cases h₀; cases h₁
  exact trans (trans ⟨Homotopy.transRefl _⟩ ⟨Homotopy.reflTrans _⟩) h

/-- If a topological space `X` can be covered by open sets `c i` whose pairwise intersections
are path-connected, then for any path `γ` with basepoint `a` in the intersection of the `c i`'s
we may find a sequence of loops `D k`, each contained in some `c i`, such that `γ` is homotopic
to the concatenation of the `D k`'s.

This is Lemma 1.15 from [hatcher02]. -/
theorem exists_loops_homotopic_foldTrans_of_open_cover (hc₁ : ∀ i, IsOpen (c i))
    (hc₂ : univ ⊆ ⋃ i, c i) (hc₃ : ∀ i j, IsPathConnected (c i ∩ c j)) (ha : ∀ i, a ∈ c i)
    (γ : Path a a) : ∃ (n : ℕ) (D : Fin (n + 1) → Path a a), Homotopic (foldTrans (fun _ ↦ a) D) γ
      ∧ (∀ k, ∃ i : ι , Set.range (D k) ⊆ c i) := by
  have ⟨n, t, ht₀, ht₁, ht_range⟩ := exists_partition_unitInterval_of_open_cover hc₁ hc₂ γ
  -- `τ` indexes a sequence of sets in our open cover which our path traverses between.
  choose τ hτ using ht_range
  have := exists_path_range_of_isPathConnected_inter hc₃ ha τ (γ ∘ t)
    (fun k ↦ hτ k (mem_image_of_mem γ left_mem_uIcc))
    (fun k ↦ hτ k (mem_image_of_mem γ right_mem_uIcc))
  /- `G k` is a path lying in `c (τ k.castSucc) ∩ c (τ k.succ)` which connects our basepoint `a`
  to the point `γ (t k)`. Note that `γ (t k)` is where our path changes from lying in
  `c (τ k.castSucc)` to lying in `c (τ k.succ)`. -/
  choose G hG using this
  -- We add `Path.refl a` to the start and end of `G` to obtain `G'`.
  let G' := snoc (α := fun k ↦ Path a (γ (t k)))
    (cons (α := fun k ↦ Path a (γ (t k.castSucc))) ((Path.refl a).cast rfl (ht₀ ▸ γ.source)) G)
    ((Path.refl a).cast rfl (ht₁ ▸ γ.target))
  -- We now list some basic properties of `G'` to be used later in the proof.
  have hG'₀ : G' 0 = (Path.refl a).cast rfl (ht₀ ▸ γ.source) :=
    (snoc_apply_zero _ _).trans (cons_zero _ _)
  have hG'₁ : G' (last (n + 1)) = (Path.refl a).cast rfl (ht₁ ▸ γ.target) := snoc_last _ _
  have hG'_range₀ k : Set.range (G' k.castSucc) ⊆ c (τ k) := by
    unfold G'
    rw [snoc_castSucc]
    rcases k.eq_zero_or_eq_succ with rfl | ⟨j, rfl⟩
    · simp only [cons_zero, cast_coe, refl_range, singleton_subset_iff]
      exact ha _
    · exact (subset_inter_iff.mp (hG j)).right
  have hG'_range₁ k : Set.range (G' k.succ) ⊆ c (τ k) := by
    unfold G'
    rcases k.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl
    · rw [succ_castSucc, snoc_castSucc]
      exact (subset_inter_iff.mp (hG j)).left
    · simp only [succ_last, snoc_last, cast_coe, refl_range, singleton_subset_iff]
      exact ha _
  /- Our desired sequence of loops is obtained by concatenating each subpath of `γ` lying in some
  element `c (τ k)` of our open cover with the paths `G' (k.castSucc)` and `(G' (k. succ)).symm`.
  Intuitively, we are attaching both ends of our subpath to our basepoint by leveraging `G'`.
  Our previously established results then make it relatively easy to prove that the concatenation
  of these loops is homotopic to `γ`, and that each loop has the appropriate range. -/
  use n, fun k ↦
    ((G' (k.castSucc)).trans (γ.subpath (t k.castSucc) (t k.succ))).trans (G' (k.succ)).symm
  constructor
  · apply trans (foldTrans_trans_trans_symm _ _ _ _)
    rw [hG'₀, hG'₁, symm_cast, refl_symm]
    refine cast_trans_trans_homotopic_of_homotopic_cast (trans (foldTrans_subpath _ _) ?_)
    rw! (castMode := .all) [ht₀, ht₁, subpath_zero_one]
    rfl
  · intro k
    use τ k
    simp_rw [trans_range, symm_range]
    apply union_subset
    · apply union_subset (hG'_range₀ k)
      rw [range_subpath]
      exact hτ k
    · exact hG'_range₁ k

end Path.Homotopic

end

/-- Technical lemma to prove `isPathConnected_compl_singleton_inter_neg`. -/
lemma PartialEquiv.symm_image_target_minus_singleton_eq {α β : Type*} (e : PartialEquiv α β)
    {b : β} (h : b ∈ e.target) : e.symm '' (e.target \ {b}) = e.source \ {e.symm b} := by
  rw [image_diff_of_injOn, symm_image_target_eq_source, image_singleton]
  · exact e.symm.injOn
  · exact singleton_subset_iff.mpr h

-- We now establish some lemmas about the Euclidean sphere before proving our main result.
namespace EuclideanSphere

/-- `S n` is the `n`-dimensional sphere (so it lives in `(n + 1)`-dimensional Euclidean space). -/
abbrev S (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

variable {n : ℕ}

instance : Nonempty (S n) := Nonempty.to_subtype (NormedSpace.sphere_nonempty.mpr (by norm_num))

instance : Infinite (S (n + 1)) := by
  rw [← infinite_univ_iff]
  have v : S (n + 1) := Nonempty.some inferInstance
  apply Infinite.of_image (stereographic' (n + 1) v)
  rw [image_univ]
  apply Infinite.mono (target_subset_range (stereographic' (n + 1) v).toPartialEquiv)
  rw [stereographic'_target]
  exact infinite_univ

instance (n : ℕ) : PathConnectedSpace (S (n + 1)) := by
  rw [← isPathConnected_iff_pathConnectedSpace]
  apply isPathConnected_sphere
  · rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact Nat.one_lt_ofNat
  · exact zero_le_one' ℝ

/-- The sphere minus a point is contractible. -/
instance (v : S n) : ContractibleSpace ({v}ᶜ : Set (S n)) := by
  let proj := stereographic' n v
  have : ContractibleSpace proj.target := by
    rw [stereographic'_target]
    exact Homeomorph.contractibleSpace (Homeomorph.Set.univ (EuclideanSpace ℝ (Fin n)))
  convert Homeomorph.contractibleSpace proj.toHomeomorphSourceTarget
  repeat exact (stereographic'_source v).symm

/-- The Euclidean `n`-sphere minus a point is path connected for `n ≥ 1`. -/
theorem isPathConnected_compl_singleton (v : S (n + 1)) : IsPathConnected ({v}ᶜ) := by
  rw [isPathConnected_iff_pathConnectedSpace]
  infer_instance

lemma stereographic'_symm_zero (v : S n) : (stereographic' n v).toPartialEquiv.symm 0 = -v := by
  simp [stereographic', stereographic, stereoInvFun]
  rfl

/-- The Euclidean `n`-sphere minus two antipodal points is path connected for `n ≥ 2`. -/
theorem isPathConnected_compl_singleton_inter_neg (v : S (n + 2)) :
    IsPathConnected ({v}ᶜ ∩ {-v}ᶜ) := by
  let proj := stereographic' (n + 2) v
  have : proj.toPartialEquiv.symm '' (proj.target \ {0}) = {v}ᶜ ∩ {-v}ᶜ := by
    rw [symm_image_target_minus_singleton_eq, stereographic'_source, stereographic'_symm_zero,
      diff_eq]
    rw [stereographic'_target]
    exact mem_univ 0
  rw [← this]
  apply IsPathConnected.image'
  · rw [stereographic'_target, ← compl_eq_univ_diff]
    exact isPathConnected_compl_singleton_of_one_lt_rank
      (by rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; exact Nat.one_lt_ofNat) 0
  · exact ContinuousOn.mono proj.continuousOn_invFun diff_subset

-- We now define the cover of `S n` to be used in `exists_loops_homotopic_foldTrans_of_open_cover`.
variable {n : ℕ}

/-- `c v` is the open cover of `S n` by the complement of `v` and the complement of `-v`. -/
private abbrev c (v : S n) : Fin 2 → Set (S n) := cases {v}ᶜ (fun _ ↦ {-v}ᶜ)

private lemma hc₁ (v : S n) : ∀ i, IsOpen (c v i) := by
  apply cases
  · simp
  · simp

private lemma hc₂ (v : S n) : univ ⊆ ⋃ i, c v i := by
  intro s _
  rcases eq_or_ne s v with rfl | h
  · rw [mem_iUnion]
    use 1
    change s ∈ ({-s}ᶜ : Set (S n))
    rw [mem_compl_iff, mem_singleton_iff, ← Ne, ← Subtype.coe_ne_coe, coe_neg_sphere]
    intro hv
    apply (ne_zero_of_mem_unit_sphere s)
    ext k
    rw [zero_apply, ← CharZero.eq_neg_self_iff, ← PiLp.neg_apply, ← hv]
  · rw [Set.mem_iUnion]
    use 0
    exact h

private lemma hc₃ (v : S (n + 2)) : ∀ i j, IsPathConnected (c v i ∩ c v j) := by
  apply cases
  · apply cases
    · simp_rw [cases_zero, inter_self]
      exact isPathConnected_compl_singleton v
    · intro _
      simp_rw [cases_zero, cases_succ]
      exact isPathConnected_compl_singleton_inter_neg v
  · intro _
    apply cases
    · simp_rw [cases_succ, cases_zero, inter_comm]
      exact isPathConnected_compl_singleton_inter_neg v
    · intro _
      simp_rw [cases_succ, inter_self]
      exact isPathConnected_compl_singleton (-v)

private lemma hx (x : S (n + 1)) : ∃ v, ∀ i : Fin 2, x ∈ c v i := by
  have ⟨v, hv⟩ := Infinite.exists_notMem_finset {x, -x}
  use v
  apply cases
  · simp_rw [cases_zero, mem_compl_singleton_iff]
    intro h
    apply hv
    rw [Finset.mem_insert]
    exact Or.inl h.symm
  · simp_rw [cases_succ, mem_compl_singleton_iff]
    intro _ h
    apply hv
    rw [Finset.mem_insert, Finset.mem_singleton, h]
    exact Or.inr (neg_neg v).symm

/-- A non-surjective path in the Euclidean sphere is homotopic to a constant path. -/
theorem homotopic_refl_of_not_surjective {n : ℕ} {v : S n} (γ : Path v v)
    (h : ¬(Surjective γ)) : γ.Homotopic (refl v) := by
  unfold Surjective at h
  push_neg at h
  obtain ⟨w, hw⟩ := h
  let w_compl : Set (S n) := {w}ᶜ
  let v' : w_compl := ⟨v, by
    rw [mem_compl_singleton_iff]
    convert hw 0
    exact γ.source.symm⟩
  let f : I → γ⁻¹' {w}ᶜ := fun x ↦ ⟨x, hw x⟩
  let γ' : Path v' v' := {
    toFun := γ.restrictPreimage {w}ᶜ ∘ f
    source' := by simp [f, ContinuousMap.restrictPreimage, v']
    target' := by simp [f, ContinuousMap.restrictPreimage, v']
  }
  have h : SimplyConnectedSpace w_compl := inferInstance
  let incl : C(w_compl, S n) := ⟨Subtype.val, continuous_subtype_val⟩
  exact Homotopic.map ((simply_connected_iff_loops_trivial.mp h).right γ') incl

/-- The Euclidean `n`-sphere is simply connected for `n ≥ 2`. -/
protected theorem simplyConnectedSpace (n : ℕ) : SimplyConnectedSpace (S (n + 2)) := by
  rw [simply_connected_iff_loops_trivial]
  constructor
  · infer_instance
  · intro x p
    let ⟨v, hv⟩ := hx x
    have ⟨m, D, hDh, hDr⟩ := Homotopic.exists_loops_homotopic_foldTrans_of_open_cover
      (hc₁ v) (hc₂ v) (hc₃ v) hv p
    apply Homotopic.trans hDh.symm
    rw [← foldTrans_refl]
    apply Homotopic.fold_hcomp
    intro k
    have ⟨i, hi⟩ := hDr k
    fin_cases i
    · simp_rw [zero_eta, cases_zero] at hi
      apply homotopic_refl_of_not_surjective
      exact fun h ↦ hi (h v) rfl
    · have : (1 : Fin 2) = succ 0 := rfl
      simp_rw [mk_one, this, cases_succ] at hi
      apply homotopic_refl_of_not_surjective
      exact fun a ↦ hi (a (-v)) rfl

instance (n : ℕ) : SimplyConnectedSpace (S (n + 2)) := EuclideanSphere.simplyConnectedSpace n

end EuclideanSphere
