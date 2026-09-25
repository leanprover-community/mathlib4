/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Subpath
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.UnitInterval

/-!
# Tube neighborhoods in path space

A *tube* in the space of paths in `X` is determined by a partition `0 = t₀ ≤ ⋯ ≤ tₙ = 1` of the
unit interval, open sets `Uᵢ` for the segments `[tᵢ, tᵢ₊₁]`, and open path-connected sets `Vⱼ` for
the vertices `tⱼ`, each contained in the adjacent segment sets. A path lies in the tube if it
maps each segment into `Uᵢ` and each vertex into `Vⱼ`. Tubes are open in the compact-open
topology. When each `Uᵢ` is *path-homotopy-trivial* (any two paths in `Uᵢ` with the same
endpoints are homotopic in `X`), two paths with the same endpoints in a common tube are homotopic:
connect corresponding vertices by paths in `Vⱼ`, use homotopy triviality of `Uᵢ` on each rectangle,
and paste.

## Main definitions

* `IsPathHomotopyTrivial U`: any two paths in `U` with the same endpoints are homotopic in `X`.
* `unitInterval.Partition n`: a monotone sequence `0 = t₀ ≤ ⋯ ≤ tₙ = 1` in the unit interval.
* `Path.Tube X n`: the segment sets `Uᵢ` and vertex sets `Vⱼ` of a tube, with their properties.
* `Path.IsInTube f part T`: the predicate that `f : I → X` lies in the tube.

## Main statements

* `Path.exists_isInTube`: in a locally path-connected space, a path lies in a tube if each
  point on it has an open, path-homotopy-trivial neighborhood.
* `Path.Tube.isOpen_setOf_isInTube`: tubes are open in the compact-open topology.
* `Path.IsInTube.exists_trans_homotopic`: two paths with the same source in a common tube become
  homotopic after appending to the first a path in the last vertex set.
* `Path.IsInTube.homotopic`: two paths with the same endpoints in a common tube are homotopic.

The application to semilocally simply connected spaces (path-homotopy classes are open, so
`Path.Homotopic.Quotient` is discrete) is in
`Mathlib/AlgebraicTopology/FundamentalGroupoid/SemilocallySimplyConnected.lean`.
-/

noncomputable section

open Set Topology unitInterval

variable {X : Type*} [TopologicalSpace X]

/-- A set `U` is *path-homotopy-trivial* if any two paths in `U` with the same endpoints are
homotopic in the ambient space. This is weaker than `U` being simply connected, since the homotopy
need not stay in `U`. -/
@[expose] public def IsPathHomotopyTrivial (U : Set X) : Prop :=
  ∀ ⦃a b : X⦄ (p q : Path a b), range p ⊆ U → range q ⊆ U → p.Homotopic q

/-- A loop in a path-homotopy-trivial set is nullhomotopic. -/
public theorem IsPathHomotopyTrivial.nullhomotopic {U : Set X} (hU : IsPathHomotopyTrivial U)
    {x : X} (γ : Path x x) (hγ : range γ ⊆ U) : γ.Homotopic (Path.refl x) :=
  hU γ _ hγ (by simpa using hγ γ.source_mem_range)

/-- The data of a tube with `n` segments: open path-homotopy-trivial sets `U i` for the segments,
and open path-connected sets `V j` for the vertices, with `V j` contained in the `U i` of the
adjacent segments. -/
public structure Path.Tube (X : Type*) [TopologicalSpace X] (n : ℕ) where
  /-- The segment sets. -/
  U : Fin n → Set X
  /-- The vertex sets. -/
  V : Fin (n + 1) → Set X
  isOpen_U : ∀ i, IsOpen (U i)
  isPathHomotopyTrivial_U : ∀ i, IsPathHomotopyTrivial (U i)
  isOpen_V : ∀ j, IsOpen (V j)
  isPathConnected_V : ∀ j, IsPathConnected (V j)
  V_castSucc_subset : ∀ i : Fin n, V i.castSucc ⊆ U i
  V_succ_subset : ∀ i : Fin n, V i.succ ⊆ U i

/-- `f : I → X` lies in the tube determined by `part` and `T` if it maps each segment
`[tᵢ, tᵢ₊₁]` into `U i` and each vertex `tⱼ` into `V j`. -/
public structure Path.IsInTube {n : ℕ} (f : I → X) (part : unitInterval.Partition n)
    (T : Path.Tube X n) : Prop where
  mapsTo : ∀ i : Fin n, MapsTo f (Icc (part.t i.castSucc) (part.t i.succ)) (T.U i)
  mem_V : ∀ j, f (part.t j) ∈ T.V j

variable {n : ℕ} {part : unitInterval.Partition n} {T : Path.Tube X n}

public theorem Path.isInTube_iff {f : I → X} :
    Path.IsInTube f part T ↔
      (∀ i : Fin n, MapsTo f (Icc (part.t i.castSucc) (part.t i.succ)) (T.U i)) ∧
        ∀ j, f (part.t j) ∈ T.V j :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

public theorem Path.IsInTube.range_subpath_subset {x y : X} {γ : Path x y}
    (hγ : Path.IsInTube γ part T) (i : Fin n) :
    range (γ.subpath (part.t i.castSucc) (part.t i.succ)) ⊆ T.U i := by
  rintro _ ⟨t, rfl⟩
  exact hγ.mapsTo i
    ⟨Icc.le_convexComb (part.t_castSucc_le_succ i) t,
      Icc.convexComb_le (part.t_castSucc_le_succ i) t⟩

/-! ### Openness of tubes -/

/-- A tube is open in the compact-open topology on `C(I, X)`. -/
public theorem Path.Tube.isOpen_setOf_isInTube (part : unitInterval.Partition n)
    (T : Path.Tube X n) :
    IsOpen {f : C(I, X) | Path.IsInTube f part T} := by
  simp only [Path.isInTube_iff, ofPred_and, ofPred_forall]
  refine (isOpen_iInter_of_finite fun i ↦ ?_).inter (isOpen_iInter_of_finite fun j ↦ ?_)
  · exact ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc (T.isOpen_U i)
  · exact (T.isOpen_V j).preimage (continuous_eval_const _)

/-- A tube is open in the path space `Path x y`. -/
public theorem Path.Tube.isOpen_setOf_isInTube_path (part : unitInterval.Partition n)
    (T : Path.Tube X n) (x y : X) : IsOpen {γ : Path x y | Path.IsInTube γ part T} :=
  (T.isOpen_setOf_isInTube part).preimage continuous_induced_dom

/-! ### Existence of tubes -/

/-- Given segment sets `U i` for `f`, the path components of `f (t j)` in the intersections of
the adjacent `U i` are suitable vertex sets. -/
private theorem exists_vertex_family [LocallyPathConnectedSpace X] {f : I → X}
    {t : Fin (n + 1) → I} {U : Fin n → Set X} (h_mono : Monotone t)
    (hU_open : ∀ i, IsOpen (U i))
    (hU : ∀ i : Fin n, MapsTo f (Icc (t i.castSucc) (t i.succ)) (U i)) :
    ∃ V : Fin (n + 1) → Set X, (∀ j, IsOpen (V j)) ∧ (∀ j, IsPathConnected (V j)) ∧
      (∀ j, f (t j) ∈ V j) ∧ (∀ i : Fin n, V i.castSucc ⊆ U i) ∧ ∀ i : Fin n, V i.succ ⊆ U i := by
  let W : Fin (n + 1) → Set X := fun j ↦ ⋂ i : Fin n, ⋂ (_ : j = i.castSucc ∨ j = i.succ), U i
  have hW_open : ∀ j, IsOpen (W j) := fun j ↦
    isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun _ ↦ hU_open i
  have hfW : ∀ j, f (t j) ∈ W j := by
    intro j
    simp only [W, mem_iInter]
    rintro i (rfl | rfl)
    · exact hU i ⟨le_rfl, h_mono i.castSucc_lt_succ.le⟩
    · exact hU i ⟨h_mono i.castSucc_lt_succ.le, le_rfl⟩
  refine ⟨fun j ↦ pathComponentIn (W j) (f (t j)), fun j ↦ (hW_open j).pathComponentIn _,
    fun j ↦ isPathConnected_pathComponentIn (hfW j), fun j ↦ mem_pathComponentIn_self (hfW j),
    fun i ↦ pathComponentIn_subset.trans ?_, fun i ↦ pathComponentIn_subset.trans ?_⟩
  · exact iInter_subset_of_subset i (iInter_subset _ (Or.inl rfl))
  · exact iInter_subset_of_subset i (iInter_subset _ (Or.inr rfl))

/-- If every point on a path has an open, path-homotopy-trivial neighborhood, then the path
lies in a tube. -/
public theorem Path.exists_isInTube [LocallyPathConnectedSpace X] {x y : X} (γ : Path x y)
    (h : ∀ z ∈ range γ, ∃ U : Set X, IsOpen U ∧ z ∈ U ∧ IsPathHomotopyTrivial U) :
    ∃ (n : ℕ) (part : unitInterval.Partition n) (T : Path.Tube X n), Path.IsInTube γ part T := by
  obtain ⟨n, part, h_seg⟩ := γ.exists_partition_with_property
    IsPathHomotopyTrivial h
  choose U hU_open hU hU_mapsTo using h_seg
  obtain ⟨V, hV_open, hV_pathConn, hγV, hV_castSucc, hV_succ⟩ :=
    exists_vertex_family part.mono hU_open hU_mapsTo
  exact ⟨n, part,
    ⟨U, V, hU_open, hU, hV_open, hV_pathConn, hV_castSucc, hV_succ⟩,
    hU_mapsTo, hγV⟩

/-! ### Paths in a common tube are homotopic -/

/-- The class of `p.subpath` over the endpoints of a partition is the class of `p`. Casts keep the
endpoints fixed when rewriting the partition endpoints. -/
private theorem Path.Homotopic.Quotient.cast_mk_subpath_t_zero_t_last {x y : X} (p : Path x y)
    (part : unitInterval.Partition n) (h₁ : x = p (part.t 0)) (h₂ : y = p (part.t (Fin.last n))) :
    (Path.Homotopic.Quotient.mk (p.subpath (part.t 0) (part.t (Fin.last n)))).cast h₁ h₂ =
      Path.Homotopic.Quotient.mk p := by
  revert h₁ h₂
  rw [part.t_zero, part.t_last]
  intro h₁ h₂
  rw [Path.Homotopic.Quotient.mk_subpath_zero_one]
  simp

/-- The pasting lemma. Let `γ : Path x y` and `γ' : Path x' y'`, and let `α j` be "rung" paths
from `γ (t j)` to `γ' (t j)` at the vertices of a partition. If on each segment
`γ|[tᵢ, tᵢ₊₁] · αᵢ₊₁` is homotopic to `αᵢ · γ'|[tᵢ, tᵢ₊₁]`, then `γ · αₙ` is homotopic to
`α₀ · γ'`. -/
public theorem Path.Homotopic.trans_of_subpath_trans {x y x' y' : X}
    (γ : Path x y) (γ' : Path x' y') (part : unitInterval.Partition n)
    (α : (j : Fin (n + 1)) → Path (γ (part.t j)) (γ' (part.t j)))
    (h_rect : ∀ i : Fin n,
      ((γ.subpath (part.t i.castSucc) (part.t i.succ)).trans (α i.succ)).Homotopic
        ((α i.castSucc).trans (γ'.subpath (part.t i.castSucc) (part.t i.succ)))) :
    (γ.trans ((α (Fin.last n)).cast (by simp) (by simp))).Homotopic
      (((α 0).cast (by simp) (by simp)).trans γ') := by
  open Path.Homotopic.Quotient in
  -- `γ_aux j` follows `γ` up to `t j`, crosses along `α j`, then follows `γ'`.
  let γ_aux : Fin (n + 1) → Path x y' := fun j ↦
    (((γ.subpath (part.t 0) (part.t j)).trans (α j)).trans
      (γ'.subpath (part.t j) (part.t (Fin.last n)))).cast (by simp) (by simp)
  have h_zero : (γ_aux 0).Homotopic (((α 0).cast (by simp) (by simp)).trans γ') := by
    apply Path.Homotopic.Quotient.exact
    dsimp [γ_aux]
    rw [mk_subpath_self, cast_mk_subpath_t_zero_t_last γ' part]
    simp
  have h_last : (γ_aux (Fin.last n)).Homotopic
      (γ.trans ((α (Fin.last n)).cast (by simp) (by simp))) := by
    apply Path.Homotopic.Quotient.exact
    dsimp [γ_aux]
    rw [mk_subpath_self, cast_mk_subpath_t_zero_t_last γ part]
    simp
  have h_rect' : ∀ (i : Fin n) {w : X} (q : Path.Homotopic.Quotient (γ' (part.t i.succ)) w),
      (Path.Homotopic.Quotient.mk (γ.subpath (part.t i.castSucc) (part.t i.succ))).trans
          ((Path.Homotopic.Quotient.mk (α i.succ)).trans q) =
        (Path.Homotopic.Quotient.mk (α i.castSucc)).trans
          ((Path.Homotopic.Quotient.mk (γ'.subpath (part.t i.castSucc) (part.t i.succ))).trans
            q) := by
    intro i w q
    rw [← Path.Homotopic.Quotient.trans_assoc, ← Path.Homotopic.Quotient.trans_assoc]
    rw [← mk_trans, ← mk_trans, Path.Homotopic.Quotient.eq.mpr (h_rect i)]
  have h_step : ∀ i : Fin n, (γ_aux i.succ).Homotopic (γ_aux i.castSucc) := by
    intro i
    apply Path.Homotopic.Quotient.exact
    simp only [γ_aux, mk_trans, mk_cast]
    rw [← Path.Homotopic.mk_subpath_trans_mk_subpath γ (part.t 0) (part.t i.castSucc),
      ← Path.Homotopic.mk_subpath_trans_mk_subpath γ' (part.t i.castSucc) (part.t i.succ)]
    simp only [Path.Homotopic.Quotient.trans_assoc]
    rw [h_rect']
  have h_chain : ∀ j : Fin (n + 1), (γ_aux j).Homotopic (γ_aux 0) := by
    intro j
    induction j using Fin.induction with
    | zero => exact .refl _
    | succ i ih => exact (h_step i).trans ih
  exact h_last.symm.trans ((h_chain (Fin.last n)).trans h_zero)

/-- Rung paths at the vertices, connecting two functions in a common tube. -/
private theorem Path.IsInTube.exists_rungs {x y x' y' : X} {γ : Path x y} {γ' : Path x' y'}
    (hγ : Path.IsInTube γ part T) (hγ' : Path.IsInTube γ' part T) :
    ∃ α : (j : Fin (n + 1)) → Path (γ (part.t j)) (γ' (part.t j)), ∀ j, range (α j) ⊆ T.V j := by
  choose α hα using fun j ↦ (T.isPathConnected_V j).exists_path (hγ.mem_V j) (hγ'.mem_V j)
  exact ⟨α, hα⟩

/-- Two paths with the same source in a common tube are homotopic after appending to the first
a path in the last vertex set of the tube. -/
public theorem Path.IsInTube.exists_trans_homotopic {x y y' : X} {γ : Path x y} {γ' : Path x y'}
    (hγ : Path.IsInTube γ part T) (hγ' : Path.IsInTube γ' part T) :
    ∃ ρ : Path y y', range ρ ⊆ T.V (Fin.last n) ∧ (γ.trans ρ).Homotopic γ' := by
  cases n with
  | zero => exact isEmptyElim part
  | succ n =>
  obtain ⟨α, hα⟩ := hγ.exists_rungs hγ'
  have h_rect : ∀ i : Fin (n + 1),
      ((γ.subpath (part.t i.castSucc) (part.t i.succ)).trans (α i.succ)).Homotopic
        ((α i.castSucc).trans (γ'.subpath (part.t i.castSucc) (part.t i.succ))) := fun i ↦
    T.isPathHomotopyTrivial_U i _ _
      (by
        rw [Path.trans_range]
        exact union_subset (hγ.range_subpath_subset i) ((hα _).trans (T.V_succ_subset i)))
      (by
        rw [Path.trans_range]
        exact union_subset ((hα _).trans (T.V_castSucc_subset i)) (hγ'.range_subpath_subset i))
  have h_α₀ : ((α 0).cast (by simp) (by simp)).Homotopic (Path.refl x) :=
    (T.isPathHomotopyTrivial_U 0).nullhomotopic _
      (by simpa using (hα 0).trans (T.V_castSucc_subset 0))
  exact ⟨(α (Fin.last _)).cast (by simp) (by simp), by simpa using hα _,
    (Path.Homotopic.trans_of_subpath_trans γ γ' part α h_rect).trans
      (Path.Homotopic.trans_left_of_nullhomotopic h_α₀)⟩

/-- Two paths with the same endpoints in a common tube are homotopic. -/
public theorem Path.IsInTube.homotopic {x y : X} {γ γ' : Path x y}
    (hγ : Path.IsInTube γ part T) (hγ' : Path.IsInTube γ' part T) : γ.Homotopic γ' := by
  cases n with
  | zero => exact isEmptyElim part
  | succ n =>
  obtain ⟨ρ, hρ, h⟩ := hγ.exists_trans_homotopic hγ'
  have hρ_null : ρ.Homotopic (Path.refl y) :=
    (T.isPathHomotopyTrivial_U (Fin.last n)).nullhomotopic ρ
      (hρ.trans (T.V_succ_subset (Fin.last n)))
  exact (Path.Homotopic.trans_right_of_nullhomotopic hρ_null).symm.trans h

end
