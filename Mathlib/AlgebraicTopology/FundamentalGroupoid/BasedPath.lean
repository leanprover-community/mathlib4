/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SemilocallySimplyConnected
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Order.Basic

/-!
# Based paths

For a topological space `X` and basepoint `x₀ : X`, this file introduces the space
`BasedPath x₀` of continuous maps `γ : C(I, X)` with `γ 0 = x₀`, topologised as a subspace
of the compact-open topology on `C(I, X)`. It then develops the path-component machinery of
`endpoint ⁻¹' U` that feeds the universal-cover construction.

## Main definitions

* `BasedPath x₀`: the compact-open space of based paths out of `x₀`.
* `BasedPath.endpoint`, `BasedPath.toPath`, `BasedPath.ofPath`, `BasedPath.append`:
  basic API for operating on based paths.
* `BasedPath.deformTerminal`: a reparameterisation that traverses a compressed tail of the
  original path and then a new path from its endpoint.
* `Path.initialSegmentFamily`: the family `t ↦ γ|_[0, t]` of initial segments of a path.

## Main results

* `BasedPath.isOpenMap_endpoint`: the endpoint map `BasedPath x₀ → X` is open when `X` is
  locally path-connected.
* `BasedPath.joinedIn_preimage_of_append`: appending a path inside `U` moves a based path
  within the same path component of `endpoint ⁻¹' U`.
* `BasedPath.exists_open_nhd_pathComponent_preimage`: variable-endpoint tube/component theorem.
* `BasedPath.isOpen_pathComponent_preimage`: in a semilocally simply connected, locally
  path-connected space, path components of `endpoint ⁻¹' U` (for good `U`) are open.
* `BasedPath.pathComponent_preimage_saturated`: path components of `endpoint ⁻¹' U` are
  invariant under endpoint-preserving homotopy.
-/

@[expose] public section

open scoped unitInterval
open Topology

variable {X : Type*} [TopologicalSpace X]

/-- The quotient of paths by homotopy inherits its topology as a quotient of the path space. -/
instance instTopologicalSpaceHomotopicQuotient (x₀ x : X) :
    TopologicalSpace (Path.Homotopic.Quotient x₀ x) := by
  delta Path.Homotopic.Quotient
  infer_instance

/-- The compact-open based-path space out of `x₀`. -/
def BasedPath (x₀ : X) :=
  { γ : C(I, X) // γ 0 = x₀ }

namespace BasedPath

variable {x₀ : X}

instance : TopologicalSpace (BasedPath x₀) := instTopologicalSpaceSubtype

/-- The endpoint of a based path. -/
def endpoint (γ : BasedPath x₀) : X := γ.1 1

/-- View a based path as a path to its endpoint. -/
def toPath (γ : BasedPath x₀) : Path x₀ (endpoint γ) where
  toContinuousMap := γ.1
  source' := γ.2
  target' := rfl

@[simp] theorem endpoint_def (γ : BasedPath x₀) : endpoint γ = γ.1 1 := rfl
@[simp] theorem toPath_apply (γ : BasedPath x₀) (t : I) : toPath γ t = γ.1 t := rfl
@[simp] theorem toPath_source (γ : BasedPath x₀) : toPath γ 0 = x₀ := γ.2
@[simp] theorem toPath_target (γ : BasedPath x₀) : toPath γ 1 = endpoint γ := rfl

@[ext] theorem ext {γ γ' : BasedPath x₀} (h : ∀ t, γ.1 t = γ'.1 t) : γ = γ' := by
  cases γ with
  | mk γ hγ =>
    cases γ' with
    | mk γ' hγ' =>
      simp only at h
      have hfun : γ = γ' := by
        ext t
        exact h t
      subst hfun
      simp

/-- View an ordinary path out of `x₀` as a based path. -/
def ofPath {y : X} (γ : Path x₀ y) : BasedPath x₀ :=
  ⟨γ.toContinuousMap, γ.source⟩

@[simp] theorem ofPath_toPath {y : X} (γ : Path x₀ y) :
    (ofPath γ).toPath = γ.cast rfl (by simp [endpoint, ofPath]) := by
  ext t
  rfl

theorem endpoint_ofPath {y : X} (γ : Path x₀ y) : endpoint (ofPath γ) = y := by
  simp [endpoint, ofPath, γ.target]

/-- Append a path at the endpoint of a based path. -/
noncomputable def append {y : X} (γ : BasedPath x₀) (δ : Path (endpoint γ) y) :
    BasedPath x₀ :=
  ofPath (γ.toPath.trans δ)

theorem endpoint_append {y : X} (γ : BasedPath x₀) (δ : Path (endpoint γ) y) :
    endpoint (append γ δ) = y := endpoint_ofPath _

/-- The tail of a based path from time `a` to the endpoint. -/
noncomputable def terminalTail {u : X} (γ : BasedPath x₀) (hu : endpoint γ = u) (a : ℝ)
    (ha1 : a ≤ 1) :
    Path (γ.toPath.extend a) u :=
  (γ.toPath.truncateOfLE (t₀ := a) (t₁ := 1) ha1).cast rfl
    (by simpa [BasedPath.endpoint] using hu.symm)

@[simp] theorem terminalTail_source {u : X} (γ : BasedPath x₀) (hu : endpoint γ = u) (a : ℝ)
    (ha1 : a ≤ 1) :
    terminalTail γ hu a ha1 0 = γ.toPath.extend a := by
  simpa [terminalTail] using (γ.toPath.truncateOfLE ha1).source

@[simp] theorem terminalTail_target {u : X} (γ : BasedPath x₀) (hu : endpoint γ = u) (a : ℝ)
    (ha1 : a ≤ 1) :
    terminalTail γ hu a ha1 1 = u := by
  have htail : terminalTail γ hu a ha1 1 = γ.toPath 1 := by
    simpa [terminalTail] using (γ.toPath.truncateOfLE ha1).target
  exact htail.trans hu

/-- Replace the terminal interval of a based path by first traversing a compressed tail of the
original path and then a new endpoint path. -/
noncomputable def deformTerminal {u v : X} (γ : BasedPath x₀) (hu : endpoint γ = u)
    (δ : Path u v) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) : BasedPath x₀ := by
  let tail : Path (γ.toPath.extend a) u := terminalTail γ hu a (by linarith)
  let f : ℝ → X := fun t ↦
    if hta : t ≤ a then γ.toPath.extend t else
      if htb : t ≤ b then tail.extend ((t - a) / (b - a)) else δ.extend ((t - b) / (1 - b))
  have hf_cont : Continuous f := by
    refine Continuous.if_le γ.toPath.continuous_extend ?_ continuous_id continuous_const ?_
    · refine Continuous.if_le
        (tail.continuous_extend.comp (by fun_prop))
        (δ.continuous_extend.comp (by fun_prop))
        continuous_id continuous_const ?_
      · intro t htb
        have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne.symm
        subst t
        simpa [tail, hba] using terminalTail_target γ hu a (by linarith)
    · intro t hta
      subst t
      simpa [tail, hab.le] using (terminalTail_source γ hu a (by linarith)).symm
  refine ⟨ContinuousMap.mk
    (fun t : I ↦ f t)
    (hf_cont.comp continuous_subtype_val), ?_⟩
  simpa [f, ha] using γ.toPath.source

@[simp] theorem deformTerminal_apply_of_le {u v : X} (γ : BasedPath x₀) (hu : endpoint γ = u)
    (δ : Path u v) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1)
    (t : I) (ht : (t : ℝ) ≤ a) :
    (deformTerminal γ hu δ ha hab hb).1 t = γ.toPath.extend t := by
  simp [deformTerminal, ht]

@[simp] theorem deformTerminal_apply_of_lt_of_le {u v : X} (γ : BasedPath x₀)
    (hu : endpoint γ = u) (δ : Path u v) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1)
    (t : I) (hta : a < (t : ℝ)) (htb : (t : ℝ) ≤ b) :
    (deformTerminal γ hu δ ha hab hb).1 t =
      (terminalTail γ hu a (by linarith)).extend (((t : ℝ) - a) / (b - a)) := by
  simp [deformTerminal, not_le_of_gt hta, htb]

@[simp] theorem deformTerminal_apply_of_lt {u v : X} (γ : BasedPath x₀) (hu : endpoint γ = u)
    (δ : Path u v) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1)
    (t : I) (ht : b < (t : ℝ)) :
    (deformTerminal γ hu δ ha hab hb).1 t = δ.extend (((t : ℝ) - b) / (1 - b)) := by
  simp [deformTerminal, not_le_of_gt (lt_trans hab ht), not_le_of_gt ht]

end BasedPath

namespace Path

theorem truncateOfLE_range_subset_preimage {a b : X} (γ : Path a b) {t₀ t₁ : ℝ}
    (h : t₀ ≤ t₁) {U : Set X} (hU : Set.Icc t₀ t₁ ⊆ γ.extend ⁻¹' U) :
    Set.range (γ.truncateOfLE h) ⊆ U := by
  rintro _ ⟨s, rfl⟩
  dsimp [truncateOfLE, truncate]
  apply hU
  constructor
  · exact le_min (le_max_right _ _) h
  · exact min_le_right _ _

/-- The initial segment of a path up to time `t`. -/
noncomputable def initialSegmentFamily {a b : X} (γ : Path a b) (t : I) : Path a (γ t) :=
  (γ.truncate 0 t).cast (by rw [min_eq_left t.2.1, γ.extend_zero]) (γ.extend_apply t.2).symm

theorem continuous_initialSegmentFamily_uncurry {a b : X} (γ : Path a b) :
    Continuous ↿(initialSegmentFamily γ) := by
  have htrunc : Continuous (fun ts : I × I ↦ γ.truncate 0 ts.1 ts.2 : I × I → X) := by
    let key : I × I → ℝ × ℝ × I := fun ts ↦ (0, ts.1, ts.2)
    have hkey : Continuous key := by fun_prop
    simpa [key] using γ.truncate_continuous_family.comp hkey
  simpa [initialSegmentFamily] using htrunc

theorem initialSegmentFamily_zero {a b : X} (γ : Path a b) :
    initialSegmentFamily γ 0 = (Path.refl a).cast rfl (by simp) := by
  ext s
  simp [initialSegmentFamily, Path.refl]

theorem initialSegmentFamily_one {a b : X} (γ : Path a b) :
    initialSegmentFamily γ 1 = γ.cast rfl (by simp) := by
  ext s
  simp [initialSegmentFamily, Path.truncate_zero_one]

end Path

namespace BasedPath

/-- The endpoint map `BasedPath x₀ → X` is an open map when `X` is locally path-connected. -/
theorem isOpenMap_endpoint [LocPathConnectedSpace X] (x₀ : X) :
    IsOpenMap (endpoint (x₀ := x₀)) := by
  classical
  refine IsOpenMap.of_nhds_le ?_
  intro γ
  rw [Filter.le_def]
  intro s hs
  rw [Filter.mem_map'] at hs
  have hsub := mem_nhds_subtype (s := {γ : C(I, X) | γ 0 = x₀}) γ
    ({η : BasedPath x₀ | endpoint η ∈ s})
  rcases hsub.mp hs with ⟨V, hVγ, hVs⟩
  rcases ContinuousMap.mem_nhds_iff.1 hVγ with ⟨S, hSfin, hSdata, hSV⟩
  let T : Finset (Set I × Set X) := hSfin.toFinset
  let Tgood : Finset (Set I × Set X) := T.filter fun KU ↦ (1 : I) ∈ KU.1
  let Tbad : Finset (Set I × Set X) := T.filter fun KU ↦ (1 : I) ∉ KU.1
  let O : Set X := ⋂ KU ∈ Tgood, KU.2
  -- Sub-basis entries of either `Tgood` or `Tbad` are entries of `S`, so their data applies.
  have hS_of_T : ∀ KU, KU ∈ T → KU ∈ S := fun _ ↦ hSfin.mem_toFinset.mp
  have hOopen : IsOpen O :=
    isOpen_biInter_finset fun KU hKU ↦
      (hSdata KU.1 KU.2 (hS_of_T KU (Finset.mem_filter.mp hKU).1)).2.1
  have huO : endpoint γ ∈ O := by
    simp only [O, Set.mem_iInter]
    exact fun KU hKU ↦ (hSdata KU.1 KU.2 (hS_of_T KU (Finset.mem_filter.mp hKU).1)).2.2
      (by simpa using (Finset.mem_filter.1 hKU).2)
  rcases (isOpen_isPathConnected_basis (x := endpoint γ)).mem_iff.mp
      (hOopen.mem_nhds huO) with ⟨W, ⟨hWopen, huW, hWpath⟩, hWO⟩
  let N : Set I := γ.toPath ⁻¹' W ∩ ⋂ KU ∈ Tbad, KU.1ᶜ
  have hNnhds : N ∈ 𝓝 (1 : I) := by
    refine Filter.inter_mem
      ((hWopen.preimage γ.toPath.continuous).mem_nhds (by simpa [endpoint] using huW)) ?_
    refine (isOpen_biInter_finset ?_).mem_nhds (by simp [Tbad])
    exact fun KU hKU ↦
      ((hSdata KU.1 KU.2 (hS_of_T KU (Finset.mem_filter.mp hKU).1)).1.isClosed).isOpen_compl
  rcases exists_Ioc_subset_of_mem_nhds' hNnhds (show (0 : I) < 1 by simp)
    with ⟨a₀, ha₀, hIoc⟩
  let a : ℝ := (((a₀ : I) : ℝ) + 1) / 2
  let b : ℝ := (a + 1) / 2
  -- `ha₀_nonneg`, `ha₀_lt_one` are kept in scope for `nlinarith` to pick up.
  have ha₀_nonneg : 0 ≤ ((a₀ : I) : ℝ) := a₀.2.1
  have ha₀_lt_one : ((a₀ : I) : ℝ) < 1 := ha₀.2
  have ha₀_lt_a : ((a₀ : I) : ℝ) < a := by dsimp [a]; nlinarith
  have ha0 : 0 ≤ a := by dsimp [a]; nlinarith
  have ha1 : a ≤ 1 := by dsimp [a]; nlinarith
  have ha_lt_one : a < 1 := by dsimp [a]; nlinarith
  have hab : a < b := by dsimp [b]; nlinarith
  have hb1 : b < 1 := by dsimp [b]; nlinarith
  refine mem_nhds_iff.mpr ⟨W, ?_, hWopen, huW⟩
  intro v hvW
  obtain ⟨δ, hδW⟩ := hWpath.exists_path huW hvW
  let η := deformTerminal γ rfl δ ha0 hab hb1
  have hηV : η.1 ∈ V := by
    apply hSV
    intro K U hKU
    have hKUT : (K, U) ∈ T := hSfin.mem_toFinset.mpr hKU
    by_cases h1K : (1 : I) ∈ K
    · have hKUgood : (K, U) ∈ Tgood := Finset.mem_filter.mpr ⟨hKUT, h1K⟩
      have hOU : O ⊆ U := by
        intro z hz
        have hz' : ∀ KU ∈ Tgood, z ∈ KU.2 := by
          simpa [O] using hz
        exact hz' (K, U) hKUgood
      intro t ht
      by_cases hta : (t : ℝ) ≤ a
      · rw [BasedPath.deformTerminal_apply_of_le γ rfl δ ha0 hab hb1 t hta,
          Path.extend_apply _ t.2]
        exact (hSdata K U hKU).2.2 ht
      · have hat : a < (t : ℝ) := lt_of_not_ge hta
        by_cases htb : (t : ℝ) ≤ b
        · have hrange :
              Set.range (terminalTail γ rfl a (by linarith)) ⊆ W := by
            apply Path.truncateOfLE_range_subset_preimage (h := ha1)
            intro s hs
            have hs01 : s ∈ (Set.Icc 0 1 : Set ℝ) := ⟨le_trans ha0 hs.1, hs.2⟩
            change γ.toPath.extend s ∈ W
            rw [Path.extend_apply _ hs01]
            apply (hIoc ?_).1
            constructor
            · change ((a₀ : I) : ℝ) < s
              exact lt_of_lt_of_le ha₀_lt_a hs.1
            · change s ≤ 1
              exact hs.2
          have hparam :
              (((t : ℝ) - a) / (b - a)) ∈ (Set.Icc 0 1 : Set ℝ) := by
            have hba : 0 < b - a := sub_pos.mpr hab
            constructor
            · exact div_nonneg (sub_nonneg.mpr (le_of_lt hat)) (le_of_lt hba)
            · refine (div_le_one hba).2 ?_
              exact sub_le_sub_right htb a
          have htailW :
              (terminalTail γ rfl a (by linarith)).extend (((t : ℝ) - a) / (b - a)) ∈ W := by
            rw [Path.extend_apply _ hparam]
            apply hrange
            exact ⟨⟨((t : ℝ) - a) / (b - a), hparam⟩, rfl⟩
          rw [BasedPath.deformTerminal_apply_of_lt_of_le γ rfl δ ha0 hab hb1 t hat htb]
          exact hOU (hWO htailW)
        · have hbt : b < (t : ℝ) := lt_of_not_ge htb
          have hparam : (((t : ℝ) - b) / (1 - b)) ∈ (Set.Icc 0 1 : Set ℝ) := by
            have hb : 0 < 1 - b := sub_pos.mpr hb1
            constructor
            · exact div_nonneg (sub_nonneg.mpr (le_of_lt hbt)) (le_of_lt hb)
            · refine (div_le_one hb).2 ?_
              exact sub_le_sub_right t.2.2 b
          have hδt :
              δ.extend (((t : ℝ) - b) / (1 - b)) ∈ W := by
            rw [Path.extend_apply _ hparam]
            apply hδW
            exact ⟨⟨((t : ℝ) - b) / (1 - b), hparam⟩, rfl⟩
          rw [BasedPath.deformTerminal_apply_of_lt γ rfl δ ha0 hab hb1 t hbt]
          exact hOU (hWO hδt)
    · intro t ht
      have hKUbad : (K, U) ∈ Tbad := Finset.mem_filter.mpr ⟨hKUT, h1K⟩
      have ht_not_Ioc : t ∉ Set.Ioc a₀ 1 := by
        intro htIoc
        have htN : t ∈ N := hIoc htIoc
        have htN' : ∀ KU ∈ Tbad, t ∉ KU.1 := by
          simpa [N] using htN.2
        exact htN' (K, U) hKUbad ht
      have htle : (t : ℝ) ≤ a := by
        by_contra hgt
        have hat : a < (t : ℝ) := lt_of_not_ge hgt
        have hat₀ : ((a₀ : I) : ℝ) < t := lt_trans ha₀_lt_a hat
        exact ht_not_Ioc ⟨hat₀, t.2.2⟩
      rw [BasedPath.deformTerminal_apply_of_le γ rfl δ ha0 hab hb1 t htle,
        Path.extend_apply _ t.2]
      exact (hSdata K U hKU).2.2 ht
  have hηs : endpoint η ∈ s := hVs hηV
  have hend : endpoint η = v := by
    change η.1 1 = v
    rw [BasedPath.deformTerminal_apply_of_lt γ rfl δ ha0 hab hb1 1 hb1]
    have hbne : 1 - b ≠ 0 := sub_ne_zero.mpr hb1.ne'
    have hratio : ((((1 : I) : ℝ) - b) / (1 - b) : ℝ) = 1 := by
      change (1 - b) / (1 - b) = 1
      field_simp [hbne]
    rw [hratio]
    simpa using δ.extend_one
  rw [hend] at hηs
  exact hηs

variable {x₀ : X}

theorem joined_of_homotopic (x₀ : X) {y : X} {p q : Path x₀ y} (h : Path.Homotopic p q) :
    Joined (ofPath p) (ofPath q) := by
  rcases h with ⟨H⟩
  refine ⟨{
    toFun := fun t ↦ ofPath (H.eval t)
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_induced_dom.comp <| (Path.continuous_uncurry_iff.mp <| by
        change Continuous fun ts : I × I ↦ H ts
        exact H.continuous)
    source' := by
      ext s
      simp [ofPath]
    target' := by
      ext s
      simp [ofPath]
  }⟩

theorem joinedIn_preimage_singleton_of_homotopic (x₀ : X) {y : X} {U : Set X} (hy : y ∈ U)
    {p q : Path x₀ y} (h : Path.Homotopic p q) :
    JoinedIn (endpoint (x₀ := x₀) ⁻¹' U) (ofPath p) (ofPath q) := by
  rcases h with ⟨H⟩
  let γ : Path (ofPath p) (ofPath q) :=
    { toFun := fun t ↦ ofPath (H.eval t)
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_induced_dom.comp <| (Path.continuous_uncurry_iff.mp <| by
          change Continuous fun ts : I × I ↦ H ts
          exact H.continuous)
      source' := by
        ext s
        simp [ofPath]
      target' := by
        ext s
        simp [ofPath] }
  refine ⟨γ, ?_⟩
  intro t
  -- Unfold `γ t = ofPath (H.eval t)` and apply `endpoint_ofPath`.
  change endpoint (ofPath (H.eval t)) ∈ U
  rw [endpoint_ofPath]
  exact hy

/-- Appending a path that stays inside `U` moves a based path within the same path component of
the endpoint preimage of `U`. -/
theorem joinedIn_preimage_of_append {U : Set X} {z : X} (γ : BasedPath x₀)
    (hγU : endpoint γ ∈ U) (δ : Path (endpoint γ) z) (hδU : Set.range δ ⊆ U) :
    JoinedIn (endpoint (x₀ := x₀) ⁻¹' U) γ (append γ δ) := by
  let γrefl : Path (endpoint γ) (endpoint γ) := Path.refl (endpoint γ)
  have h_start :
      JoinedIn (endpoint (x₀ := x₀) ⁻¹' U) γ (append γ γrefl) := by
    simpa [γrefl, BasedPath.append] using
      (joinedIn_preimage_singleton_of_homotopic (x₀ := x₀) (U := U) hγU
        (p := γ.toPath.trans (Path.refl (endpoint γ))) (q := γ.toPath)
        (Path.Homotopic.trans_refl γ.toPath)).symm
  have h_move :
      JoinedIn (endpoint (x₀ := x₀) ⁻¹' U) (append γ γrefl) (append γ δ) := by
    let η : Path (append γ γrefl) (append γ δ) := {
      toFun := fun t ↦ append γ (Path.initialSegmentFamily δ t)
      continuous_toFun := by
        apply Continuous.subtype_mk
        refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
        simpa [BasedPath.append, BasedPath.ofPath] using
          Path.trans_continuous_family (fun _ : I ↦ γ.toPath)
            (Path.continuous_uncurry_iff.mpr continuous_const) (Path.initialSegmentFamily δ)
            (Path.continuous_initialSegmentFamily_uncurry δ)
      source' := by
        simpa [BasedPath.append, BasedPath.ofPath, γrefl] using
          congrArg (append γ) (Path.initialSegmentFamily_zero δ)
      target' := by
        simpa [BasedPath.append, BasedPath.ofPath] using
          congrArg (append γ) (Path.initialSegmentFamily_one δ) }
    refine ⟨η, ?_⟩
    intro t
    -- Unfold `η t = append γ (Path.initialSegmentFamily δ t)` and apply `endpoint_append`.
    change endpoint (append γ (Path.initialSegmentFamily δ t)) ∈ U
    rw [BasedPath.endpoint_append]
    exact hδU ⟨t, rfl⟩
  exact h_start.trans h_move

/-- Variable-endpoint tube/component theorem.

If `α : BasedPath x₀` has endpoint in a neighborhood `U` satisfying the path-uniqueness
(`SLSC`) condition, then `α` has an open neighborhood `N` in `BasedPath x₀` such that every
element of `N` has endpoint in `U` and lies in the same path component of `endpoint ⁻¹' U` as
`α`. -/
theorem exists_open_nhd_pathComponent_preimage
    [SemilocallySimplyConnectedSpace X] [LocPathConnectedSpace X]
    {U : Set X} (hU_open : IsOpen U)
    (α : BasedPath x₀) (hα : endpoint α ∈ U) :
    ∃ N : Set (BasedPath x₀), IsOpen N ∧ α ∈ N ∧
      N ⊆ endpoint (x₀ := x₀) ⁻¹' U ∧
      ∀ β ∈ N, JoinedIn (endpoint (x₀ := x₀) ⁻¹' U) α β := by
  classical
  obtain ⟨n, part, T, hα_tube⟩ := α.toPath.exists_partition_in_slsc_neighborhoods
  -- Rule out `n = 0`; the rest of the proof assumes `n = n' + 1`.
  match n, part, T, hα_tube with
  | 0, part, _, _ => exact (IntervalPartition.not_zero part).elim
  | n' + 1, part, T, hα_tube =>
  -- Endpoint of α at the last partition point equals `endpoint α`.
  have hα_at_last : α.toPath (part.t (Fin.last (n' + 1))) = endpoint α := by
    rw [part.h_end]; exact α.toPath.target
  -- Refine `T.V (Fin.last (n' + 1))` by intersecting with `U` and taking a path component.
  set V_last := T.V (Fin.last (n' + 1)) with hV_last_def
  have hα_V_last : endpoint α ∈ V_last := hα_at_last ▸ hα_tube.passes_through_V _
  set W : Set X := V_last ∩ U with hW_def
  have hW_open : IsOpen W := (T.h_V_open _).inter hU_open
  have hα_W : endpoint α ∈ W := ⟨hα_V_last, hα⟩
  set V_last' : Set X := pathComponentIn W (endpoint α) with hV_last'_def
  have hV'_open : IsOpen V_last' := hW_open.pathComponentIn _
  have hV'_pathConn : IsPathConnected V_last' := isPathConnected_pathComponentIn hα_W
  have hV'_sub_V : V_last' ⊆ V_last := pathComponentIn_subset.trans Set.inter_subset_left
  have hV'_sub_U : V_last' ⊆ U := pathComponentIn_subset.trans Set.inter_subset_right
  have hα_V' : endpoint α ∈ V_last' := mem_pathComponentIn_self hα_W
  -- Refined V function: `V_last'` at the last partition point, `T.V` elsewhere.
  set V' : Fin (n' + 2) → Set X :=
    Fin.snoc (fun j : Fin (n' + 1) ↦ T.V j.castSucc) V_last' with hV'_def
  have hV'_last_eq : V' (Fin.last (n' + 1)) = V_last' := Fin.snoc_last ..
  have hV'_castSucc_eq : ∀ j : Fin (n' + 1), V' j.castSucc = T.V j.castSucc := fun j ↦
    Fin.snoc_castSucc ..
  have hV'_sub_TV : ∀ j : Fin (n' + 2), V' j ⊆ T.V j := by
    intro j
    induction j using Fin.lastCases with
    | last => rw [hV'_last_eq]; exact hV'_sub_V
    | cast k => rw [hV'_castSucc_eq]
  have hV'_open_all : ∀ j, IsOpen (V' j) := by
    intro j
    induction j using Fin.lastCases with
    | last => rw [hV'_last_eq]; exact hV'_open
    | cast k => rw [hV'_castSucc_eq]; exact T.h_V_open _
  have hV'_pathConn_all : ∀ j, IsPathConnected (V' j) := by
    intro j
    induction j using Fin.lastCases with
    | last => rw [hV'_last_eq]; exact hV'_pathConn
    | cast k => rw [hV'_castSucc_eq]; exact T.h_V_pathConn _
  have hα_passes_V' : ∀ j, α.toPath (part.t j) ∈ V' j := by
    intro j
    induction j using Fin.lastCases with
    | last => rw [hV'_last_eq, hα_at_last]; exact hα_V'
    | cast k => rw [hV'_castSucc_eq]; exact hα_tube.passes_through_V _
  -- The neighborhood `N` of `α`: based paths satisfying the refined tube conditions.
  set N : Set (BasedPath x₀) := {β : BasedPath x₀ |
      (∀ (i : Fin (n' + 1)) (s : I),
          (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → β.1 s ∈ T.U i) ∧
      (∀ j, β.1 (part.t j) ∈ V' j)} with hN_def
  refine ⟨N, ?_, ?_, ?_, ?_⟩
  · -- `N` is open: it is the intersection of a finite family of open segment/point conditions.
    rw [show N = {β : BasedPath x₀ | ∀ (i : Fin (n' + 1)) (s : I),
          (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → β.1 s ∈ T.U i} ∩
        {β : BasedPath x₀ | ∀ j, β.1 (part.t j) ∈ V' j} from rfl]
    refine IsOpen.inter ?_ ?_
    · -- Segment conditions: pulled back from `C(I, X)` tubes.
      rw [show {β : BasedPath x₀ | ∀ (i : Fin (n' + 1)) (s : I),
            (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → β.1 s ∈ T.U i} =
          ⋂ i : Fin (n' + 1), {β : BasedPath x₀ | ∀ s : I,
              (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → β.1 s ∈ T.U i} from
        by ext β; simp]
      refine isOpen_iInter_of_finite fun i ↦ ?_
      rw [show {β : BasedPath x₀ | ∀ s : I,
            (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → β.1 s ∈ T.U i} =
          (fun β : BasedPath x₀ ↦ (β.1 : C(I, X))) ⁻¹'
            {f : C(I, X) | Set.MapsTo f
              (Set.Icc (part.t i.castSucc) (part.t i.succ) : Set I) (T.U i)} from
        by ext β; simp [Set.MapsTo, Set.mem_Icc]]
      exact (ContinuousMap.isOpen_setOf_mapsTo isCompact_Icc (T.h_U_open i)).preimage
        continuous_subtype_val
    · -- Point conditions at partition points.
      rw [show {β : BasedPath x₀ | ∀ j, β.1 (part.t j) ∈ V' j} =
          ⋂ j : Fin (n' + 2), {β : BasedPath x₀ | β.1 (part.t j) ∈ V' j} from by ext β; simp]
      exact isOpen_iInter_of_finite fun j ↦ (hV'_open_all j).preimage
        ((continuous_eval_const (part.t j)).comp continuous_subtype_val)
  · -- `α ∈ N`.
    exact ⟨hα_tube.stays_in_U, hα_passes_V'⟩
  · -- `N ⊆ endpoint ⁻¹' U`.
    intro β hβ
    have h1 : β.1 (part.t (Fin.last (n' + 1))) ∈ V' (Fin.last (n' + 1)) := hβ.2 _
    rw [hV'_last_eq] at h1
    exact hV'_sub_U (by simpa [part.h_end] using h1)
  · -- Every `β ∈ N` is `JoinedIn (endpoint ⁻¹' U)` to `α`.
    intro β hβ
    obtain ⟨hβ_stays, hβ_passes⟩ := hβ
    -- Endpoint of `β` lies in `U`.
    have hβ_end_U : endpoint β ∈ U := by
      have h1 : β.1 (part.t (Fin.last (n' + 1))) ∈ V' (Fin.last (n' + 1)) := hβ_passes _
      rw [hV'_last_eq] at h1
      exact hV'_sub_U (by simpa [BasedPath.endpoint, part.h_end] using h1)
    -- Rung paths in `V' j`.
    choose ρ hρ_range using fun j : Fin (n' + 2) ↦
      (hV'_pathConn_all j).exists_path (hα_passes_V' j) (hβ_passes j)
    -- Rectangle homotopies on each segment.
    have h_rectangles : ∀ i : Fin (n' + 1),
        Path.Homotopic
          ((α.toPath.subpathOn (part.t i.castSucc) (part.t i.succ)).trans (ρ i.succ))
          ((ρ i.castSucc).trans
            (β.toPath.subpathOn (part.t i.castSucc) (part.t i.succ))) := by
      intro i
      have hab : (part.t i.castSucc : ℝ) ≤ part.t i.succ :=
        part.h_mono i.castSucc_lt_succ.le
      have hα_sub :
          Set.range (α.toPath.subpathOn (part.t i.castSucc) (part.t i.succ)) ⊆ T.U i :=
        hα_tube.subpathOn_range_subset i
      have hβ_sub :
          Set.range (β.toPath.subpathOn (part.t i.castSucc) (part.t i.succ)) ⊆ T.U i := by
        rintro _ ⟨t, rfl⟩
        simp only [Path.subpathOn_apply]
        exact hβ_stays i _ ⟨Set.Icc.le_convexCombo hab t, Set.Icc.convexCombo_le hab t⟩
      have hρ_cast : Set.range (ρ i.castSucc) ⊆ T.U i := by
        refine (hρ_range _).trans ?_
        rw [hV'_castSucc_eq]; exact T.h_V_left_subset i
      have hρ_succ : Set.range (ρ i.succ) ⊆ T.U i :=
        (hρ_range _).trans ((hV'_sub_TV _).trans (T.h_V_right_subset i))
      exact Path.segment_rung_homotopy (T.U i)
        (fun p q hp_a hp_d hp_range hq_range ↦ T.h_U_slsc i hp_a hp_d p q hp_range hq_range)
        _ _ _ _ hα_sub hβ_sub hρ_cast hρ_succ
    -- Paste the segment homotopies; use `T.U 0` as the enclosing SLSC neighborhood.
    have h_paste :=
      Path.paste_segment_homotopies_slsc_source α.toPath β.toPath part ρ h_rectangles
        (T.U ⟨0, Nat.succ_pos n'⟩)
        (fun p q hp_a hp_d hp_range hq_range ↦
          T.h_U_slsc ⟨0, Nat.succ_pos n'⟩ hp_a hp_d p q hp_range hq_range)
        ((hρ_range 0).trans (by
          rw [show (0 : Fin (n' + 2)) = (⟨0, Nat.succ_pos n'⟩ : Fin (n' + 1)).castSucc from rfl,
            hV'_castSucc_eq]
          exact T.h_V_left_subset ⟨0, Nat.succ_pos n'⟩))
    -- Package the final rung as a path from `endpoint α` to `endpoint β`.
    have hβ_at_last : β.toPath (part.t (Fin.last (n' + 1))) = endpoint β := by
      rw [part.h_end]; exact β.toPath.target
    let ρ_final : Path (endpoint α) (endpoint β) :=
      (ρ (Fin.last (n' + 1))).cast hα_at_last.symm hβ_at_last.symm
    have hρ_final_range : Set.range ρ_final ⊆ U :=
      (hρ_range (Fin.last (n' + 1))).trans (by rw [hV'_last_eq]; exact hV'_sub_U)
    -- Join `α` to `append α ρ_final`, then deform `append α ρ_final` to `β` via `h_paste`.
    refine (joinedIn_preimage_of_append α hα ρ_final hρ_final_range).trans ?_
    obtain ⟨γ, hγ⟩ :=
      (joinedIn_preimage_singleton_of_homotopic (x₀ := x₀) (U := ({endpoint β} : Set X))
        (show endpoint β ∈ ({endpoint β} : Set X) from rfl)
        (show Path.Homotopic (α.toPath.trans ρ_final) β.toPath from h_paste)).mono
        (Set.preimage_mono (Set.singleton_subset_iff.mpr hβ_end_U))
    exact ⟨γ.cast rfl (by ext t; rfl), hγ⟩

/-- For an open neighborhood `U`, path components of `endpoint ⁻¹' U` are open. -/
theorem isOpen_pathComponent_preimage
    [SemilocallySimplyConnectedSpace X] [LocPathConnectedSpace X]
    {U : Set X} (hU_open : IsOpen U) (α : BasedPath x₀) :
    IsOpen (pathComponentIn (endpoint (x₀ := x₀) ⁻¹' U) α) := by
  apply isOpen_iff_mem_nhds.mpr
  intro β hβ
  have hβ_end_U : endpoint β ∈ U := hβ.target_mem
  obtain ⟨N, hN_open, hβ_N, _, hN_joined⟩ :=
    exists_open_nhd_pathComponent_preimage hU_open β hβ_end_U
  refine mem_nhds_iff.mpr ⟨N, ?_, hN_open, hβ_N⟩
  intro γ hγ_N
  exact hβ.trans (hN_joined γ hγ_N)

/-- If `α` and `β` are based paths with the same endpoint `v ∈ U`, joined inside
`endpoint ⁻¹' U`, and `U` has the SLSC uniqueness property, then their associated paths
`α.toPath` and `β.toPath` are homotopic (after casting to a common endpoint).

This is the heart of the sheet-injectivity argument: a path in the based-path space descends
to a free homotopy of paths in `X` whose endpoint trace is a loop in `U`, which is killed by
the SLSC hypothesis. -/
theorem toPath_homotopic_of_joinedIn_slsc
    {U : Set X}
    (hU_slsc : ∀ {a b : X}, a ∈ U → b ∈ U → ∀ (p q : Path a b),
      Set.range p ⊆ U → Set.range q ⊆ U → Path.Homotopic p q)
    {α β : BasedPath x₀} (hα_end : endpoint α ∈ U)
    (heq : endpoint α = endpoint β)
    (hAB : JoinedIn (endpoint (x₀ := x₀) ⁻¹' U) α β) :
    Path.Homotopic (α.toPath.cast rfl heq.symm) β.toPath := by
  obtain ⟨F, hF_U⟩ := hAB
  set v : X := endpoint β with hv_def
  have hv : v ∈ U := heq ▸ hα_end
  -- Uncurry F to get a continuous map (t, s) ↦ (F t).1 s.
  have hFv_cont : Continuous (fun ts : I × I ↦ (F ts.1).1 ts.2) := by
    have h1 : Continuous (fun t : I ↦ ((F t).1 : C(I, X))) :=
      continuous_subtype_val.comp F.continuous
    exact ContinuousMap.continuous_uncurry_of_continuous ⟨_, h1⟩
  -- The endpoint-trace loop `L : Path v v`.
  have hF0_eq : (F (0 : I)).1 = α.1 := congrArg Subtype.val F.source
  have hF1_eq : (F (1 : I)).1 = β.1 := congrArg Subtype.val F.target
  let L : Path v v :=
    { toFun := fun t ↦ (F t).1 1
      continuous_toFun := by
        simpa using hFv_cont.comp (continuous_id.prodMk (continuous_const (y := (1 : I))))
      source' := by rw [hF0_eq]; exact heq
      target' := by rw [hF1_eq]; rfl }
  have hL_refl : L.Homotopic (Path.refl v) :=
    hU_slsc hv hv L (Path.refl v) (by rintro _ ⟨t, rfl⟩; exact hF_U t) (by
      rintro _ ⟨_, rfl⟩; simpa using hv)
  -- Cast α.toPath to target `v`.
  let α' : Path x₀ v := α.toPath.cast rfl heq.symm
  -- Reparameterization functions.
  let u_real : ℝ × ℝ → ℝ := fun ts ↦ ts.1 + max 0 (2 * ts.2 - 1) * (1 - ts.1)
  let v_real : ℝ × ℝ → ℝ := fun ts ↦ min (2 * ts.2) 1
  have hu_cont : Continuous u_real :=
    (continuous_fst).add <|
      (Continuous.max continuous_const (by fun_prop)).mul (by fun_prop)
  have hv_cont_real : Continuous v_real :=
    Continuous.min (by fun_prop) continuous_const
  have hu_mem : ∀ t s : I, u_real ((t : ℝ), (s : ℝ)) ∈ I := by
    intro t s
    simp only [u_real]
    have hm_nn : (0 : ℝ) ≤ max 0 (2 * (s : ℝ) - 1) := le_max_left _ _
    have hm_le : max 0 (2 * (s : ℝ) - 1) ≤ 1 := max_le zero_le_one (by linarith [s.2.2])
    refine ⟨?_, ?_⟩
    · have h0 : 0 ≤ max 0 (2 * (s : ℝ) - 1) * (1 - (t : ℝ)) :=
        mul_nonneg hm_nn (by linarith [t.2.2])
      linarith [t.2.1]
    · -- t + m(1 - t) = (1 - m) t + m ≤ (1 - m) · 1 + m = 1
      nlinarith [t.2.1, t.2.2]
  have hv_mem : ∀ t s : I, v_real ((t : ℝ), (s : ℝ)) ∈ I := by
    intro _ s
    refine ⟨le_min (by linarith [s.2.1]) zero_le_one, min_le_right _ _⟩
  let u_fn : I × I → I := fun ts ↦ ⟨u_real ((ts.1 : ℝ), (ts.2 : ℝ)), hu_mem ts.1 ts.2⟩
  let v_fn : I × I → I := fun ts ↦ ⟨v_real ((ts.1 : ℝ), (ts.2 : ℝ)), hv_mem ts.1 ts.2⟩
  have hu_fn_cont : Continuous u_fn := by
    refine Continuous.subtype_mk ?_ _
    exact hu_cont.comp (by fun_prop)
  have hv_fn_cont : Continuous v_fn := by
    refine Continuous.subtype_mk ?_ _
    exact hv_cont_real.comp (by fun_prop)
  -- The rectangle homotopy.
  let K_fn : I × I → X := fun ts ↦ (F (u_fn ts)).1 (v_fn ts)
  have K_fn_apply : ∀ ts : I × I, K_fn ts = (F (u_fn ts)).1 (v_fn ts) := fun _ ↦ rfl
  -- Coordinate reductions of `u_fn`/`v_fn` at the four corners/edges. These are the forms
  -- that appear after `K_fn_apply` unfolds `K_fn`.
  have u_fn_zero_left : ∀ s : I, (u_fn (0, s) : ℝ) = max 0 (2 * (s : ℝ) - 1) := fun _ ↦ by
    simp [u_fn, u_real]
  have u_fn_one_left : ∀ s : I, u_fn (1, s) = 1 :=
    fun _ ↦ Subtype.ext (by simp [u_fn, u_real])
  have u_fn_one_right : ∀ t : I, u_fn (t, 1) = 1 :=
    fun _ ↦ Subtype.ext (by simp [u_fn, u_real]; ring)
  have v_fn_left : ∀ t s : I, (v_fn (t, s) : ℝ) = min (2 * (s : ℝ)) 1 := fun _ _ ↦ by
    simp [v_fn, v_real]
  have v_fn_zero_right : ∀ t : I, v_fn (t, 0) = 0 :=
    fun _ ↦ Subtype.ext (by simp [v_fn, v_real])
  have v_fn_one_right : ∀ t : I, v_fn (t, 1) = 1 :=
    fun _ ↦ Subtype.ext (by simp [v_fn, v_real])
  have hK_cont : Continuous K_fn :=
    hFv_cont.comp (hu_fn_cont.prodMk hv_fn_cont)
  -- Auxiliary identities evaluating K at corners/edges.
  have hK_zero : ∀ s : I, K_fn (0, s) = (α'.trans L) s := by
    intro s
    rw [K_fn_apply, Path.trans_apply]
    by_cases hs : (s : ℝ) ≤ 1 / 2
    · rw [dif_pos hs]
      have h2s : 2 * (s : ℝ) - 1 ≤ 0 := by linarith
      have hu_subt : u_fn (0, s) = (0 : I) :=
        Subtype.ext (by rw [u_fn_zero_left, max_eq_left h2s]; rfl)
      have hv_subt : v_fn (0, s) =
          ⟨2 * (s : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩ :=
        Subtype.ext (by rw [v_fn_left, min_eq_left (by linarith)])
      rw [hu_subt, hv_subt, hF0_eq]
      rfl
    · rw [dif_neg hs]
      have h2s : 0 ≤ 2 * (s : ℝ) - 1 := by linarith [not_le.mp hs]
      have hu_subt : u_fn (0, s) =
          ⟨2 * (s : ℝ) - 1,
            unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.mp hs).le, s.2.2⟩⟩ :=
        Subtype.ext (by rw [u_fn_zero_left, max_eq_right h2s])
      have hv_subt : v_fn (0, s) = (1 : I) :=
        Subtype.ext (by rw [v_fn_left, min_eq_right (by linarith)]; rfl)
      rw [hu_subt, hv_subt]
      rfl
  have hK_one : ∀ s : I, K_fn (1, s) = (β.toPath.trans (Path.refl v)) s := by
    intro s
    rw [K_fn_apply, Path.trans_apply, u_fn_one_left]
    by_cases hs : (s : ℝ) ≤ 1 / 2
    · rw [dif_pos hs]
      have hv_subt : v_fn (1, s) =
          ⟨2 * (s : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩ :=
        Subtype.ext (by rw [v_fn_left, min_eq_left (by linarith)])
      rw [hv_subt, hF1_eq]
      rfl
    · rw [dif_neg hs]
      have hv_subt : v_fn (1, s) = (1 : I) :=
        Subtype.ext (by rw [v_fn_left, min_eq_right (by linarith [not_le.mp hs])]; rfl)
      rw [hv_subt, hF1_eq]
      rfl
  have hK_at_zero : ∀ t : I, K_fn (t, 0) = x₀ := fun t ↦ by
    rw [K_fn_apply, v_fn_zero_right]; exact (F (u_fn (t, 0))).2
  have hK_at_one : ∀ t : I, K_fn (t, 1) = v := fun t ↦ by
    rw [K_fn_apply, u_fn_one_right, v_fn_one_right, hF1_eq]; rfl
  let K : Path.Homotopy (α'.trans L) (β.toPath.trans (Path.refl v)) :=
    { toFun := K_fn
      continuous_toFun := hK_cont
      map_zero_left := hK_zero
      map_one_left := hK_one
      prop' := by
        intro t s hs
        rcases hs with rfl | hs
        · change K_fn (t, (0 : I)) = (α'.trans L) 0
          rw [hK_at_zero, (α'.trans L).source]
        · rw [Set.mem_singleton_iff] at hs
          subst hs
          change K_fn (t, (1 : I)) = (α'.trans L) 1
          rw [hK_at_one, (α'.trans L).target] }
  have h_rect : (α'.trans L).Homotopic (β.toPath.trans (Path.refl v)) := ⟨K⟩
  -- Combine: α' ≃ α'.trans (refl v) ≃ α'.trans L ≃ β.trans (refl v) ≃ β.
  have h_α_trans_refl : (α'.trans (Path.refl v)).Homotopic α' := Path.Homotopic.trans_refl α'
  have h_α_L_refl : (α'.trans (Path.refl v)).Homotopic (α'.trans L) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl α') hL_refl.symm
  have h_β_trans_refl : (β.toPath.trans (Path.refl v)).Homotopic β.toPath :=
    Path.Homotopic.trans_refl β.toPath
  exact h_α_trans_refl.symm.trans <| h_α_L_refl.trans <| h_rect.trans h_β_trans_refl

/-- Path components of `endpoint ⁻¹' U` are invariant under endpoint-preserving homotopy:
if `p ≃ q` are homotopic paths from `x₀` to `y ∈ U`, then the based paths `ofPath p` and
`ofPath q` lie in the same path component of `endpoint ⁻¹' U`. -/
theorem pathComponent_preimage_saturated
    {U : Set X} {y : X} (hy : y ∈ U)
    {p q : Path x₀ y} (h : Path.Homotopic p q) :
    pathComponentIn (endpoint (x₀ := x₀) ⁻¹' U) (ofPath p) =
      pathComponentIn (endpoint (x₀ := x₀) ⁻¹' U) (ofPath q) :=
  pathComponentIn_congr (joinedIn_preimage_singleton_of_homotopic x₀ hy h).symm

end BasedPath
