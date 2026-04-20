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

end UniversalCover
