/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SemilocallySimplyConnected
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Order.Basic

/-!
# Universal cover

This file introduces the based-path quotient model for the universal cover based at a point `x₀`.

The underlying point of the universal cover is still represented by an endpoint together with a
homotopy class of paths from `x₀`, but the topology is not the naive sigma topology. Instead it is
the quotient topology coming from the compact-open based-path space.
-/

@[expose] public section

open scoped unitInterval
open Topology

variable {X : Type*} [TopologicalSpace X]

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

@[simp] theorem eta (γ : BasedPath x₀) :
    (⟨endpoint γ, Path.Homotopic.Quotient.mk (toPath γ)⟩ :
      Σ x : X, Path.Homotopic.Quotient x₀ x) =
    ⟨γ.1 1, Path.Homotopic.Quotient.mk (toPath γ)⟩ := rfl

/-- View an ordinary path out of `x₀` as a based path. -/
def ofPath {y : X} (γ : Path x₀ y) : BasedPath x₀ :=
  ⟨γ.toContinuousMap, γ.source⟩

@[simp] theorem ofPath_toPath {y : X} (γ : Path x₀ y) :
    (ofPath γ).toPath = γ.cast rfl (by simp [endpoint, ofPath]) := by
  ext t
  rfl

@[simp] theorem endpoint_ofPath {y : X} (γ : Path x₀ y) : endpoint (ofPath γ) = y := by
  simp [endpoint, ofPath, γ.target]

/-- Append a path at the endpoint of a based path. -/
noncomputable def append {y : X} (γ : BasedPath x₀) (δ : Path (endpoint γ) y) : BasedPath x₀ :=
  ofPath (γ.toPath.trans δ)

@[simp] theorem endpoint_append {y : X} (γ : BasedPath x₀) (δ : Path (endpoint γ) y) :
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
  let f : ℝ → X := fun t =>
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
    (fun t : I => f t)
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

theorem truncateOfLE_range_subset_preimage {a b : X} (γ : Path a b) {t₀ t₁ : ℝ} (h : t₀ ≤ t₁)
    {U : Set X} (hU : Set.Icc t₀ t₁ ⊆ γ.extend ⁻¹' U) :
    Set.range (γ.truncateOfLE h) ⊆ U := by
  rintro _ ⟨s, rfl⟩
  dsimp [truncateOfLE, truncate]
  apply hU
  constructor
  · exact le_min (le_max_right _ _) h
  · exact min_le_right _ _

end Path

namespace BasedPath

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
  let Tgood : Finset (Set I × Set X) := T.filter fun KU => (1 : I) ∈ KU.1
  let Tbad : Finset (Set I × Set X) := T.filter fun KU => (1 : I) ∉ KU.1
  let O : Set X := ⋂ KU ∈ Tgood, KU.2
  have hOopen : IsOpen O := by
    have hOpen : ∀ KU ∈ Tgood, IsOpen KU.2 := by
      intro KU hKU
      have hKU' : KU ∈ T := (Finset.mem_filter.mp hKU).1
      have hKU'' : KU ∈ S := hSfin.mem_toFinset.mp hKU'
      exact (hSdata KU.1 KU.2 hKU'').2.1
    simpa [O] using isOpen_biInter_finset hOpen
  have huO : endpoint γ ∈ O := by
    have hmem : ∀ KU ∈ Tgood, endpoint γ ∈ KU.2 := by
      intro KU hKU
      have hKU' : KU ∈ T := (Finset.mem_filter.mp hKU).1
      have hKU'' : KU ∈ S := hSfin.mem_toFinset.mp hKU'
      exact (hSdata KU.1 KU.2 hKU'').2.2 (by
        simpa using (Finset.mem_filter.1 hKU).2)
    simpa [O] using hmem
  rcases (isOpen_isPathConnected_basis (x := endpoint γ)).mem_iff.mp
      (hOopen.mem_nhds huO) with ⟨W, hWbasis, hWO⟩
  rcases hWbasis with ⟨hWopen, huW, hWpath⟩
  let N : Set I := γ.toPath ⁻¹' W ∩ ⋂ KU ∈ Tbad, KU.1ᶜ
  have hNnhds : N ∈ 𝓝 (1 : I) := by
    refine Filter.inter_mem ?_ ?_
    · exact (hWopen.preimage γ.toPath.continuous).mem_nhds (by simpa [endpoint] using huW)
    · have hbadOpen : ∀ KU ∈ Tbad, IsOpen KU.1ᶜ := by
        intro KU hKU
        have hKU' : KU ∈ T := (Finset.mem_filter.mp hKU).1
        have hKU'' : KU ∈ S := hSfin.mem_toFinset.mp hKU'
        have hKclosed : IsClosed KU.1 := (hSdata KU.1 KU.2 hKU'').1.isClosed
        exact hKclosed.isOpen_compl
      have h1bad : (1 : I) ∈ ⋂ KU ∈ Tbad, KU.1ᶜ := by
        simpa [Tbad] using fun KU hKU => (Finset.mem_filter.mp hKU).2
      exact (isOpen_biInter_finset hbadOpen).mem_nhds h1bad
  rcases exists_Ioc_subset_of_mem_nhds' hNnhds (show (0 : I) < 1 by simp) with ⟨a₀, ha₀, hIoc⟩
  let a : ℝ := (((a₀ : I) : ℝ) + 1) / 2
  let b : ℝ := (a + 1) / 2
  have ha₀_nonneg : 0 ≤ ((a₀ : I) : ℝ) := a₀.2.1
  have ha₀_lt_one : ((a₀ : I) : ℝ) < 1 := ha₀.2
  have ha₀_lt_a : ((a₀ : I) : ℝ) < a := by
    dsimp [a]
    nlinarith
  have ha0 : 0 ≤ a := by
    dsimp [a]
    nlinarith
  have ha1 : a ≤ 1 := by
    dsimp [a]
    nlinarith
  have hab : a < b := by
    dsimp [b]
    have ha_lt_one : a < 1 := by
      dsimp [a]
      nlinarith
    nlinarith
  have hb1 : b < 1 := by
    dsimp [b]
    have ha_lt_one : a < 1 := by
      dsimp [a]
      nlinarith
    nlinarith
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
    toFun := fun t => ofPath (H.eval t)
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_induced_dom.comp <| (Path.continuous_uncurry_iff.mp <| by
        change Continuous fun ts : I × I => H ts
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
    { toFun := fun t => ofPath (H.eval t)
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_induced_dom.comp <| (Path.continuous_uncurry_iff.mp <| by
          change Continuous fun ts : I × I => H ts
          exact H.continuous)
      source' := by
        ext s
        simp [ofPath]
      target' := by
        ext s
        simp [ofPath] }
  refine ⟨γ, ?_⟩
  intro t
  change endpoint (ofPath (H.eval t)) ∈ U
  have hty : endpoint (ofPath (H.eval t)) = y := by
    simp [BasedPath.endpoint, ofPath]
  rw [hty]
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
  let ε : (t : I) → Path (endpoint γ) (δ t) := fun t =>
    (δ.truncate 0 t).cast (by rw [min_eq_left t.2.1, δ.extend_zero]) (δ.extend_apply t.2).symm
  have hε_uncurry : Continuous ↿ε := by
    have htrunc : Continuous (fun ts : I × I => δ.truncate 0 ts.1 ts.2 : I × I → X) := by
      let key : I × I → ℝ × ℝ × I := fun ts => (0, ts.1, ts.2)
      have hkey : Continuous key := by fun_prop
      simpa [key] using δ.truncate_continuous_family.comp hkey
    simpa [ε]
      using htrunc
  have h_move :
      JoinedIn (endpoint (x₀ := x₀) ⁻¹' U) (append γ γrefl) (append γ δ) := by
    have hε0 : ε 0 = γrefl.cast rfl (by simpa using δ.source) := by
      ext s
      dsimp [ε, γrefl]
      simpa [Path.truncate_zero_zero, Path.refl] using δ.extend_zero
    have hε1 : ε 1 = δ.cast rfl (by simpa using δ.target) := by
      ext s
      simp [ε, Path.truncate_zero_one]
    let η : Path (append γ γrefl) (append γ δ) := {
      toFun := fun t => append γ (ε t)
      continuous_toFun := by
        apply Continuous.subtype_mk
        refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
        simpa [BasedPath.append, BasedPath.ofPath] using
          Path.trans_continuous_family (fun _ : I => γ.toPath)
            (Path.continuous_uncurry_iff.mpr continuous_const) ε hε_uncurry
      source' := by
        simpa [BasedPath.append, BasedPath.ofPath] using congrArg (append γ) hε0
      target' := by
        simpa [BasedPath.append, BasedPath.ofPath] using congrArg (append γ) hε1 }
    refine ⟨η, ?_⟩
    intro t
    change endpoint (append γ (ε t)) ∈ U
    rw [BasedPath.endpoint_append]
    exact hδU ⟨t, rfl⟩
  exact h_start.trans h_move

/-- Variable-endpoint tube/component theorem.

If `α : BasedPath x₀` has endpoint in a neighborhood `U` satisfying the path-uniqueness
(`SLSC`) condition, then `α` has an open neighborhood `N` in `BasedPath x₀` such that every
element of `N` has endpoint in `U` and lies in the same path component of `endpoint ⁻¹' U` as
`α`. -/
theorem exists_open_nhd_pathComponent_preimage
    (hX : SemilocallySimplyConnected X) [LocPathConnectedSpace X]
    {U : Set X} (hU_open : IsOpen U)
    (α : BasedPath x₀) (hα : endpoint α ∈ U) :
    ∃ N : Set (BasedPath x₀), IsOpen N ∧ α ∈ N ∧ N ⊆ endpoint (x₀ := x₀) ⁻¹' U ∧
      ∀ β ∈ N, JoinedIn (endpoint (x₀ := x₀) ⁻¹' U) α β := by
  classical
  obtain ⟨n, part, T, hα_tube⟩ := α.toPath.exists_partition_in_slsc_neighborhoods hX
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
    Fin.snoc (fun j : Fin (n' + 1) => T.V j.castSucc) V_last' with hV'_def
  have hV'_last_eq : V' (Fin.last (n' + 1)) = V_last' := Fin.snoc_last ..
  have hV'_castSucc_eq : ∀ j : Fin (n' + 1), V' j.castSucc = T.V j.castSucc := fun j =>
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
  · -- `N` is open.
    have hN_split : N =
        {β : BasedPath x₀ | ∀ (i : Fin (n' + 1)) (s : I),
            (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → β.1 s ∈ T.U i} ∩
        {β : BasedPath x₀ | ∀ j, β.1 (part.t j) ∈ V' j} := rfl
    rw [hN_split]
    refine IsOpen.inter ?_ ?_
    · -- Segment conditions: pulled back from `C(I, X)` tubes.
      have hrewrite : {β : BasedPath x₀ | ∀ (i : Fin (n' + 1)) (s : I),
            (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → β.1 s ∈ T.U i} =
          ⋂ i : Fin (n' + 1), {β : BasedPath x₀ | ∀ s : I,
              (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → β.1 s ∈ T.U i} := by
        ext β; simp
      rw [hrewrite]
      apply isOpen_iInter_of_finite
      intro i
      have heq : {β : BasedPath x₀ | ∀ s : I,
              (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → β.1 s ∈ T.U i} =
          (fun β : BasedPath x₀ => (β.1 : C(I, X))) ⁻¹'
            {f : C(I, X) | Set.MapsTo f
              (Set.Icc (part.t i.castSucc) (part.t i.succ) : Set I) (T.U i)} := by
        ext β
        simp [Set.MapsTo, Set.mem_Icc]
      rw [heq]
      exact (ContinuousMap.isOpen_setOf_mapsTo isCompact_Icc (T.h_U_open i)).preimage
        continuous_subtype_val
    · -- Point conditions at partition points.
      have hrewrite2 : {β : BasedPath x₀ | ∀ j, β.1 (part.t j) ∈ V' j} =
          ⋂ j : Fin (n' + 2), {β : BasedPath x₀ | β.1 (part.t j) ∈ V' j} := by
        ext β; simp
      rw [hrewrite2]
      apply isOpen_iInter_of_finite
      intro j
      exact (hV'_open_all j).preimage
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
    have hβ_end_V' : endpoint β ∈ V_last' := by
      have h1 : β.1 (part.t (Fin.last (n' + 1))) ∈ V' (Fin.last (n' + 1)) := hβ_passes _
      rw [hV'_last_eq] at h1
      simpa [BasedPath.endpoint, part.h_end] using h1
    have hβ_end_U : endpoint β ∈ U := hV'_sub_U hβ_end_V'
    -- Construct rung paths in `V' j`.
    have hrung : ∀ j : Fin (n' + 2),
        ∃ ρ : Path (α.toPath (part.t j)) (β.toPath (part.t j)),
          Set.range ρ ⊆ V' j := by
      intro j
      exact (hV'_pathConn_all j).exists_path (hα_passes_V' j) (hβ_passes j)
    choose ρ hρ_range using hrung
    -- Rectangle homotopies on each segment.
    have h_rectangles : ∀ i : Fin (n' + 1),
        Path.Homotopic
          ((α.toPath.subpathOn (part.t i.castSucc) (part.t i.succ)).trans (ρ i.succ))
          ((ρ i.castSucc).trans
            (β.toPath.subpathOn (part.t i.castSucc) (part.t i.succ))) := by
      intro i
      have hab : (part.t i.castSucc : ℝ) ≤ part.t i.succ :=
        part.h_mono.monotone i.castSucc_lt_succ.le
      have hα_sub : Set.range (α.toPath.subpathOn (part.t i.castSucc) (part.t i.succ)) ⊆ T.U i :=
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
        (fun p q hp_a hp_d hp_range hq_range => T.h_U_slsc i hp_a hp_d p q hp_range hq_range)
        _ _ _ _ hα_sub hβ_sub hρ_cast hρ_succ
    -- Use `T.U 0` as the SLSC neighborhood that contains the initial rung.
    have h_zero_cast : (0 : Fin (n' + 2)) =
        ((⟨0, Nat.succ_pos n'⟩ : Fin (n' + 1)).castSucc) := rfl
    have hρ0_range : Set.range (ρ 0) ⊆ T.U ⟨0, Nat.succ_pos n'⟩ := by
      refine (hρ_range 0).trans ?_
      rw [h_zero_cast, hV'_castSucc_eq]
      exact T.h_V_left_subset ⟨0, Nat.succ_pos n'⟩
    -- Paste segment homotopies.
    have h_paste :=
      Path.paste_segment_homotopies_slsc_source α.toPath β.toPath part ρ h_rectangles
        (T.U ⟨0, Nat.succ_pos n'⟩)
        (fun p q hp_a hp_d hp_range hq_range =>
          T.h_U_slsc ⟨0, Nat.succ_pos n'⟩ hp_a hp_d p q hp_range hq_range)
        hρ0_range
    -- Package the final rung as a path from `endpoint α` to `endpoint β`.
    have hβ_at_last : β.toPath (part.t (Fin.last (n' + 1))) = endpoint β := by
      rw [part.h_end]; exact β.toPath.target
    let ρ_final : Path (endpoint α) (endpoint β) :=
      (ρ (Fin.last (n' + 1))).cast hα_at_last.symm hβ_at_last.symm
    have hρ_final_range : Set.range ρ_final ⊆ U := by
      refine (hρ_range (Fin.last (n' + 1))).trans ?_
      rw [hV'_last_eq]; exact hV'_sub_U
    have h_homotopic : Path.Homotopic (α.toPath.trans ρ_final) β.toPath := h_paste
    have h_α_to_append :
        JoinedIn (endpoint (x₀ := x₀) ⁻¹' U) α (append α ρ_final) :=
      joinedIn_preimage_of_append α hα ρ_final hρ_final_range
    have h_singleton :
        JoinedIn (endpoint (x₀ := x₀) ⁻¹' ({endpoint β} : Set X))
          (ofPath (α.toPath.trans ρ_final)) (ofPath β.toPath) :=
      joinedIn_preimage_singleton_of_homotopic (x₀ := x₀) (U := ({endpoint β} : Set X))
        (show endpoint β ∈ ({endpoint β} : Set X) from rfl) h_homotopic
    have h_subset_U : ({endpoint β} : Set X) ⊆ U := Set.singleton_subset_iff.mpr hβ_end_U
    have h_β_eq : (ofPath β.toPath : BasedPath x₀) = β := by ext t; rfl
    have h_append_to_β :
        JoinedIn (endpoint (x₀ := x₀) ⁻¹' U) (append α ρ_final) β := by
      obtain ⟨γ, hγ⟩ := h_singleton.mono (Set.preimage_mono h_subset_U)
      exact ⟨γ.cast rfl h_β_eq.symm, fun t => hγ t⟩
    exact h_α_to_append.trans h_append_to_β

/-- For an open neighborhood `U`, path components of `endpoint ⁻¹' U` are open. -/
theorem isOpen_pathComponent_preimage
    (hX : SemilocallySimplyConnected X) [LocPathConnectedSpace X]
    {U : Set X} (hU_open : IsOpen U) (α : BasedPath x₀) :
    IsOpen (pathComponentIn (endpoint (x₀ := x₀) ⁻¹' U) α) := by
  apply isOpen_iff_mem_nhds.mpr
  intro β hβ
  have hβ_end_U : endpoint β ∈ U := hβ.target_mem
  obtain ⟨N, hN_open, hβ_N, _, hN_joined⟩ :=
    exists_open_nhd_pathComponent_preimage hX hU_open β hβ_end_U
  refine mem_nhds_iff.mpr ⟨N, ?_, hN_open, hβ_N⟩
  intro γ hγ_N
  exact hβ.trans (hN_joined γ hγ_N)

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

/-- The endpoint-plus-homotopy-class model for the universal cover. The topology is supplied below
as the quotient topology from `BasedPath x₀`. -/
abbrev UniversalCover (x₀ : X) :=
  Σ x : X, Path.Homotopic.Quotient x₀ x

namespace UniversalCover

variable {x₀ x : X}

/-- The quotient map from based paths to endpoint/path-homotopy classes. -/
def ofBasedPath (x₀ : X) : BasedPath x₀ → UniversalCover x₀
  | ⟨γ, hγ⟩ =>
      ⟨γ 1, Path.Homotopic.Quotient.mk
        ({ toContinuousMap := γ, source' := hγ, target' := rfl } : Path x₀ (γ 1))⟩

instance instTopologicalSpaceUniversalCover (x₀ : X) : TopologicalSpace (UniversalCover x₀) :=
  TopologicalSpace.coinduced (ofBasedPath x₀) inferInstance

@[continuity] theorem continuous_ofBasedPath (x₀ : X) : Continuous (ofBasedPath x₀) :=
  continuous_coinduced_rng

theorem surjective_ofBasedPath (x₀ : X) : Function.Surjective (ofBasedPath x₀) := by
  intro z
  rcases z with ⟨x, q⟩
  induction q using Quotient.inductionOn with
  | h γ =>
      refine ⟨⟨γ.toContinuousMap, γ.source⟩, ?_⟩
      cases γ with
      | mk f hs ht =>
          subst x
          rfl

theorem isQuotientMap_ofBasedPath (x₀ : X) : IsQuotientMap (ofBasedPath x₀) := by
  refine ⟨?_, surjective_ofBasedPath x₀⟩
  exact ⟨rfl⟩

/-- The raw quotient relation on based paths induced by endpoint-preserving homotopy. -/
abbrev BasedPathSetoid (x₀ : X) : Setoid (BasedPath x₀) :=
  Setoid.ker (ofBasedPath x₀)

instance instSetoidBasedPath (x₀ : X) : Setoid (BasedPath x₀) :=
  BasedPathSetoid x₀

/-- The raw quotient of based paths by endpoint-preserving homotopy. -/
abbrev RawUniversalCover (x₀ : X) :=
  Quotient (BasedPathSetoid x₀)

instance instTopologicalSpaceRawUniversalCover (x₀ : X) :
    TopologicalSpace (RawUniversalCover x₀) := by
  delta RawUniversalCover BasedPathSetoid
  infer_instance

/-- The canonical quotient map from based paths to the raw universal-cover quotient. -/
def quotientMk (x₀ : X) : BasedPath x₀ → RawUniversalCover x₀ :=
  @Quotient.mk' _ (BasedPathSetoid x₀)

@[continuity] theorem continuous_quotientMk (x₀ : X) :
    Continuous (quotientMk (x₀ := x₀)) :=
  continuous_quotient_mk'

/-- The raw quotient maps continuously to `UniversalCover`. -/
noncomputable def quotientToUniversalCover (x₀ : X) :
    RawUniversalCover x₀ → UniversalCover x₀ :=
  Quotient.lift (ofBasedPath x₀) fun _ _ h => h

@[simp] theorem quotientToUniversalCover_mk (x₀ : X) (p : BasedPath x₀) :
    quotientToUniversalCover x₀ (quotientMk x₀ p) = ofBasedPath x₀ p :=
  rfl

@[continuity] theorem continuous_quotientToUniversalCover (x₀ : X) :
    Continuous (quotientToUniversalCover x₀) :=
  (continuous_ofBasedPath x₀).quotient_lift fun _ _ h => h

/-- `UniversalCover x₀` really is the quotient of based paths by endpoint-preserving homotopy. -/
noncomputable def quotientHomeomorph (x₀ : X) :
    RawUniversalCover x₀ ≃ₜ UniversalCover x₀ :=
  by
    let f : C(BasedPath x₀, UniversalCover x₀) := ⟨ofBasedPath x₀, continuous_ofBasedPath x₀⟩
    let hq : IsQuotientMap f := isQuotientMap_ofBasedPath x₀
    simpa [RawUniversalCover, BasedPathSetoid] using
      (Topology.IsQuotientMap.homeomorph hq)

@[simp] theorem quotientHomeomorph_mk (x₀ : X) (p : BasedPath x₀) :
    quotientHomeomorph x₀ (quotientMk x₀ p) = ofBasedPath x₀ p := by
  rfl

/-- The endpoint projection. -/
def proj : UniversalCover x₀ → X :=
  Sigma.fst

@[simp] theorem proj_mk (q : Path.Homotopic.Quotient x₀ x) :
    proj ⟨x, q⟩ = x := rfl

@[simp] theorem proj_ofBasedPath (x₀ : X) (γ : BasedPath x₀) :
    proj (ofBasedPath x₀ γ) = BasedPath.endpoint γ :=
  rfl

@[continuity] theorem continuous_proj (x₀ : X) : Continuous (proj (x₀ := x₀)) := by
  rw [(isQuotientMap_ofBasedPath x₀).continuous_iff]
  change Continuous fun γ : BasedPath x₀ => γ.1 1
  exact (continuous_eval_const (1 : I)).comp continuous_subtype_val

theorem isOpenMap_proj [LocPathConnectedSpace X] (x₀ : X) :
    IsOpenMap (proj (x₀ := x₀)) := by
  intro s hs
  have hs_pre : IsOpen (ofBasedPath x₀ ⁻¹' s) :=
    (isQuotientMap_ofBasedPath x₀).isOpen_preimage.2 hs
  have himage :
      proj (x₀ := x₀) '' s = BasedPath.endpoint '' (ofBasedPath x₀ ⁻¹' s) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases surjective_ofBasedPath x₀ z with ⟨γ, rfl⟩
      exact ⟨γ, hz, by simp [proj_ofBasedPath]⟩
    · rintro ⟨γ, hsγ, hγ⟩
      exact ⟨ofBasedPath x₀ γ, hsγ, by simpa [proj_ofBasedPath] using hγ⟩
  rw [himage]
  exact BasedPath.isOpenMap_endpoint x₀ _ hs_pre

/-- A point in the universal cover determines a point of the fiber over its endpoint. -/
abbrev Fiber (x₀ x : X) :=
  {p : UniversalCover x₀ // proj p = x}

/-- The fiber over `x` is equivalent to the quotient of paths from `x₀` to `x`. -/
noncomputable def fiberEquiv (x₀ x : X) :
    Fiber x₀ x ≃ Path.Homotopic.Quotient x₀ x where
  toFun p := p.1.2.cast rfl p.2.symm
  invFun q := ⟨⟨x, q⟩, by simp [proj]⟩
  left_inv p := by
    rcases p with ⟨⟨y, q⟩, hp⟩
    dsimp [proj] at hp ⊢
    subst hp
    simp
  right_inv q := by
    change q.cast rfl rfl = q
    simp

/-! ### Sheet construction over a good neighborhood

Below we construct, for each point `x` and a good neighborhood `U` of `x`, the sheets indexed by
the homotopy classes `q : Path.Homotopic.Quotient x₀ x`. -/

/-- The path component (in `endpoint ⁻¹' U`) of the based path `ofPath p`. -/
def basedPathComponent (U : Set X) {y : X} (p : Path x₀ y) : Set (BasedPath x₀) :=
  pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) (BasedPath.ofPath p)

/-- The sheet over `U` (with `x ∈ U`) corresponding to a homotopy class
`q : Path.Homotopic.Quotient x₀ x`, expressed as a set of based paths. -/
noncomputable def basedPathSheet (U : Set X) (hxU : x ∈ U)
    (q : Path.Homotopic.Quotient x₀ x) : Set (BasedPath x₀) :=
  Quotient.liftOn q (fun p : Path x₀ x => basedPathComponent U p)
    fun _ _ h => BasedPath.pathComponent_preimage_saturated hxU h

@[simp] theorem basedPathSheet_mk (U : Set X) (hxU : x ∈ U) (p : Path x₀ x) :
    basedPathSheet U hxU (Path.Homotopic.Quotient.mk p) = basedPathComponent U p := rfl

theorem basedPathSheet_subset_endpoint_preimage (U : Set X) (hxU : x ∈ U)
    (q : Path.Homotopic.Quotient x₀ x) :
    basedPathSheet U hxU q ⊆ BasedPath.endpoint (x₀ := x₀) ⁻¹' U := by
  induction q using Quotient.inductionOn with
  | h p =>
    intro β hβ
    exact hβ.target_mem

/-- The sheet over `U` corresponding to `q`, viewed as a subset of `UniversalCover x₀`. -/
noncomputable def sheet (U : Set X) (hxU : x ∈ U)
    (q : Path.Homotopic.Quotient x₀ x) : Set (UniversalCover x₀) :=
  ofBasedPath x₀ '' basedPathSheet U hxU q

theorem sheet_subset_proj_preimage (U : Set X) (hxU : x ∈ U)
    (q : Path.Homotopic.Quotient x₀ x) :
    sheet U hxU q ⊆ proj (x₀ := x₀) ⁻¹' U := by
  rintro _ ⟨α, hα, rfl⟩
  change BasedPath.endpoint α ∈ U
  exact basedPathSheet_subset_endpoint_preimage U hxU q hα

/-- Two based paths with equal `ofBasedPath` images lie in the same path component of any
endpoint preimage of a set containing their common endpoint.

This is the saturation property of sheets under the quotient map `ofBasedPath`. -/
theorem pathComponentIn_endpoint_preimage_eq_of_ofBasedPath_eq
    {U : Set X} {α β : BasedPath x₀}
    (hα_end : BasedPath.endpoint α ∈ U)
    (hαβ : ofBasedPath x₀ α = ofBasedPath x₀ β) :
    pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) α =
      pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) β := by
  -- This requires extracting a path homotopy `α.toPath ≃ β.toPath` from the sigma equality
  -- `ofBasedPath α = ofBasedPath β`, modulo dependent-type casts. The argument uses
  -- `Path.Homotopic.Quotient.exact` plus saturation (`pathComponent_preimage_saturated`).
  -- See `PLAN.md` for the full proof outline.
  sorry

/-- The preimage of a sheet under `ofBasedPath` is the corresponding `basedPathSheet`.
This expresses that the sheet is saturated under the `ofBasedPath` quotient. -/
theorem preimage_sheet (U : Set X) (hxU : x ∈ U) (q : Path.Homotopic.Quotient x₀ x) :
    ofBasedPath x₀ ⁻¹' sheet U hxU q = basedPathSheet U hxU q := by
  apply Set.Subset.antisymm
  · intro α hα
    obtain ⟨β, hβ, hαβ⟩ := hα
    induction q using Quotient.inductionOn with
    | h p =>
      change β ∈ basedPathComponent U p at hβ
      change α ∈ basedPathComponent U p
      have hβ_end : BasedPath.endpoint β ∈ U := hβ.target_mem
      have hα_end : BasedPath.endpoint α ∈ U := by
        have h_proj : proj (x₀ := x₀) (ofBasedPath x₀ β) =
            proj (x₀ := x₀) (ofBasedPath x₀ α) := by rw [hαβ]
        rw [proj_ofBasedPath, proj_ofBasedPath] at h_proj
        exact h_proj ▸ hβ_end
      have h_α_β : pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) α =
          pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) β :=
        pathComponentIn_endpoint_preimage_eq_of_ofBasedPath_eq hα_end hαβ.symm
      change α ∈ pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) (BasedPath.ofPath p)
      rw [← pathComponentIn_congr hβ, ← h_α_β]
      exact mem_pathComponentIn_self hα_end
  · intro α hα
    exact ⟨α, hα, rfl⟩

theorem isOpen_sheet [LocPathConnectedSpace X] (hX : SemilocallySimplyConnected X)
    (U : Set X) (hU_open : IsOpen U) (hxU : x ∈ U)
    (q : Path.Homotopic.Quotient x₀ x) :
    IsOpen (sheet U hxU q) := by
  rw [(isQuotientMap_ofBasedPath x₀).isOpen_preimage.symm]
  rw [preimage_sheet]
  induction q using Quotient.inductionOn with
  | h p => exact BasedPath.isOpen_pathComponent_preimage hX hU_open _

theorem mem_sheet_self {U : Set X} (hxU : x ∈ U) (p : Path x₀ x) :
    ofBasedPath x₀ (BasedPath.ofPath p) ∈ sheet U hxU (Path.Homotopic.Quotient.mk p) :=
  ⟨BasedPath.ofPath p, mem_pathComponentIn_self
    (by simpa [BasedPath.endpoint, BasedPath.ofPath, p.target] using hxU), rfl⟩

/-! ### Steps 6-11

The remaining steps require additional proofs that we sketch below. The core difficulty is the
**SLSC injectivity argument** (step 6): two based paths joined in `endpoint ⁻¹' U` with the same
endpoint `y ∈ U` have homotopic `toPath`s. The proof uses a homotopy-rectangle argument with the
loop trace `t ↦ endpoint(γ t)` killed by SLSC of `U`. This is left as `sorry` here. -/

/-- **Step 6 (sheet injectivity), stated with `sorry`.** In a good neighborhood `U`, the
projection `proj` is injective on each sheet. -/
theorem sheet_proj_injOn [LocPathConnectedSpace X] (hX : SemilocallySimplyConnected X)
    {U : Set X} (hU_open : IsOpen U)
    (hU_slsc : ∀ {a b : X}, a ∈ U → b ∈ U → ∀ (p q : Path a b),
      Set.range p ⊆ U → Set.range q ⊆ U → Path.Homotopic p q)
    (hxU : x ∈ U) (q : Path.Homotopic.Quotient x₀ x) :
    (sheet U hxU q).InjOn (proj (x₀ := x₀)) := by
  sorry

/-- **Step 7, stated with `sorry`.** The endpoint projection `proj` is a covering map under
`SemilocallySimplyConnected X`, `LocPathConnectedSpace X`, and `PathConnectedSpace X`. -/
theorem isCoveringMap [LocPathConnectedSpace X] [PathConnectedSpace X]
    (hX : SemilocallySimplyConnected X) (x₀ : X) :
    IsCoveringMap (proj (x₀ := x₀)) := by
  sorry

/-- **Step 8.** Fibers of the universal cover are discrete; immediate from the covering-map
property via `IsEvenlyCovered.discreteTopology_fiber`. -/
theorem discreteTopology_fiber [LocPathConnectedSpace X] [PathConnectedSpace X]
    (hX : SemilocallySimplyConnected X) (x₀ x : X) :
    DiscreteTopology (proj (x₀ := x₀) ⁻¹' {x}) :=
  ((isCoveringMap hX x₀) x).discreteTopology_fiber

/-- **Step 9, stated with `sorry`.** The universal cover is path-connected. -/
theorem pathConnectedSpace [LocPathConnectedSpace X] [PathConnectedSpace X]
    (hX : SemilocallySimplyConnected X) (x₀ : X) :
    PathConnectedSpace (UniversalCover x₀) := by
  sorry

/-- **Step 10, stated with `sorry`.** The universal cover is simply connected. -/
theorem simplyConnectedSpace [LocPathConnectedSpace X] [PathConnectedSpace X]
    (hX : SemilocallySimplyConnected X) (x₀ : X) :
    SimplyConnectedSpace (UniversalCover x₀) := by
  sorry

end UniversalCover
