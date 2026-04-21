/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.BasedPath

/-!
# Universal cover: quotient model and sheets

This file introduces the based-path quotient model for the universal cover based at a point `x₀`,
and builds the sheet decomposition of `proj ⁻¹' U` over a good neighborhood `U`.

The underlying point of the universal cover is still represented by an endpoint together with a
homotopy class of paths from `x₀`, but the topology is not the naive sigma topology. Instead it is
the quotient topology coming from the compact-open based-path space.

## Main definitions

* `UniversalCover x₀ := Σ x : X, Path.Homotopic.Quotient x₀ x`, topologised as the quotient
  of `BasedPath x₀` under endpoint-preserving homotopy.
* `UniversalCover.proj : UniversalCover x₀ → X`: the endpoint projection.
* `UniversalCover.Fiber x₀ x`, `UniversalCover.fiberEquiv`: the fiber over `x` and its
  identification with the homotopy class of paths.
* `UniversalCover.sheet`: the sheet indexed by `q : Path.Homotopic.Quotient x₀ x` over a good
  neighborhood `U`, viewed as a subset of `UniversalCover x₀`.

## Main results

* `UniversalCover.isOpenMap_proj`: the endpoint projection is an open map.
* `UniversalCover.toPath_homotopic_of_ofBasedPath_eq` and
  `UniversalCover.ofBasedPath_eq_of_homotopic_toPath`: equality in the universal cover is
  equivalent to endpoint-preserving path homotopy of representatives.
* `UniversalCover.sheet_surjOn`, `UniversalCover.sheet_pairwise_disjoint`,
  `UniversalCover.sheet_exhaustive`, `UniversalCover.sheet_proj_injOn`: structure of the sheet
  decomposition over a good neighborhood `U`.
-/

@[expose] public section

open scoped unitInterval
open Topology

variable {X : Type*} [TopologicalSpace X]

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

/-- Every point of `UniversalCover x₀` is represented by some based path. -/
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

/-- `ofBasedPath` is a quotient map: `UniversalCover x₀` carries the quotient topology from
`BasedPath x₀` under endpoint-preserving path homotopy. -/
theorem isQuotientMap_ofBasedPath (x₀ : X) : IsQuotientMap (ofBasedPath x₀) := by
  refine ⟨?_, surjective_ofBasedPath x₀⟩
  exact ⟨rfl⟩

/-- The endpoint projection. -/
def proj : UniversalCover x₀ → X :=
  Sigma.fst

@[simp] theorem proj_mk (q : Path.Homotopic.Quotient x₀ x) :
    proj ⟨x, q⟩ = x := rfl

@[simp] theorem proj_ofBasedPath (x₀ : X) (γ : BasedPath x₀) :
    proj (ofBasedPath x₀ γ) = BasedPath.endpoint γ :=
  rfl

@[simp] theorem ofBasedPath_ofPath {y : X} (p : Path x₀ y) :
    ofBasedPath x₀ (BasedPath.ofPath p) = ⟨y, Path.Homotopic.Quotient.mk p⟩ := by
  refine Sigma.ext p.target ?_
  apply Path.Homotopic.hpath_hext
  intro t
  rfl

/-- Equality in the universal cover induces an endpoint-preserving homotopy of representative
based paths. -/
theorem toPath_homotopic_of_ofBasedPath_eq {α β : BasedPath x₀}
    (h : ofBasedPath x₀ α = ofBasedPath x₀ β) :
    Path.Homotopic
      (α.toPath.cast rfl (by
        have heq : BasedPath.endpoint α = BasedPath.endpoint β := by
          simpa [proj_ofBasedPath] using congrArg (proj (x₀ := x₀)) h
        exact heq.symm))
      β.toPath := by
  cases α with
  | mk αf hα0 =>
    cases β with
    | mk βf hβ0 =>
      simp only [ofBasedPath, Sigma.mk.injEq] at h
      obtain ⟨hend, hq⟩ := h
      let p : Path x₀ (βf 1) :=
        ({ toContinuousMap := αf, source' := hα0, target' := rfl } : Path x₀ (αf 1)).cast
          rfl hend.symm
      have hp_heq : HEq
          (Path.Homotopic.Quotient.mk
            ({ toContinuousMap := αf, source' := hα0, target' := rfl } : Path x₀ (αf 1)))
          (Path.Homotopic.Quotient.mk p) := by
        apply Path.Homotopic.hpath_hext
        intro t
        rfl
      have hq' : Path.Homotopic.Quotient.mk p =
          Path.Homotopic.Quotient.mk
            ({ toContinuousMap := βf, source' := hβ0, target' := rfl } : Path x₀ (βf 1)) := by
        exact eq_of_heq (HEq.trans hp_heq.symm hq)
      exact Path.Homotopic.Quotient.exact hq'

/-- If two based paths have the same endpoint and homotopic `toPath`s (after casting to a
common target), then they represent the same element of the `UniversalCover`. -/
theorem ofBasedPath_eq_of_homotopic_toPath {α β : BasedPath x₀}
    (heq : BasedPath.endpoint α = BasedPath.endpoint β)
    (h : Path.Homotopic (α.toPath.cast rfl heq.symm) β.toPath) :
    ofBasedPath x₀ α = ofBasedPath x₀ β := by
  obtain ⟨αf, hα0⟩ := α
  obtain ⟨βf, hβ0⟩ := β
  change αf 1 = βf 1 at heq
  change (⟨αf 1, Path.Homotopic.Quotient.mk
      (⟨αf, hα0, rfl⟩ : Path x₀ (αf 1))⟩ : Σ _ : X, _) =
    ⟨βf 1, Path.Homotopic.Quotient.mk (⟨βf, hβ0, rfl⟩ : Path x₀ (βf 1))⟩
  refine Sigma.ext heq ?_
  have h1 :
      HEq (Path.Homotopic.Quotient.mk (⟨αf, hα0, rfl⟩ : Path x₀ (αf 1)))
        (Path.Homotopic.Quotient.mk
          ((⟨αf, hα0, rfl⟩ : Path x₀ (αf 1)).cast rfl heq.symm)) :=
    Path.Homotopic.hpath_hext (fun _ => rfl)
  have h2 :
      Path.Homotopic.Quotient.mk ((⟨αf, hα0, rfl⟩ : Path x₀ (αf 1)).cast rfl heq.symm) =
        Path.Homotopic.Quotient.mk (⟨βf, hβ0, rfl⟩ : Path x₀ (βf 1)) :=
    Quotient.sound h
  exact h1.trans (heq_of_eq h2)

@[continuity] theorem continuous_proj (x₀ : X) : Continuous (proj (x₀ := x₀)) := by
  rw [(isQuotientMap_ofBasedPath x₀).continuous_iff]
  change Continuous fun γ : BasedPath x₀ => γ.1 1
  exact (continuous_eval_const (1 : I)).comp continuous_subtype_val

/-- The endpoint projection `UniversalCover x₀ → X` is an open map when `X` is locally
path-connected. -/
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
theorem pathComponent_preimage_eq_of_ofBasedPath_eq
    {U : Set X} {α β : BasedPath x₀}
    (hα_end : BasedPath.endpoint α ∈ U)
    (hαβ : ofBasedPath x₀ α = ofBasedPath x₀ β) :
    pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) α =
      pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) β := by
  have hβ_end : BasedPath.endpoint β ∈ U := by
    have heq : BasedPath.endpoint α = BasedPath.endpoint β := by
      simpa [proj_ofBasedPath] using congrArg (proj (x₀ := x₀)) hαβ
    exact heq ▸ hα_end
  exact BasedPath.pathComponent_preimage_saturated (x₀ := x₀) hβ_end
    (toPath_homotopic_of_ofBasedPath_eq hαβ)

/-- Membership in a based-path component is preserved under equality in the universal cover. -/
theorem mem_basedPathComponent_of_ofBasedPath_eq {U : Set X} {y : X} {p : Path x₀ y}
    {α β : BasedPath x₀} (hβ : β ∈ basedPathComponent U p)
    (hαβ : ofBasedPath x₀ α = ofBasedPath x₀ β) :
    α ∈ basedPathComponent U p := by
  have hα_end : BasedPath.endpoint α ∈ U := by
    have heq : BasedPath.endpoint α = BasedPath.endpoint β := by
      simpa [proj_ofBasedPath] using congrArg (proj (x₀ := x₀)) hαβ
    exact heq ▸ hβ.target_mem
  change α ∈ pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) (BasedPath.ofPath p)
  have hself : α ∈ pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) α :=
    mem_pathComponentIn_self hα_end
  rw [pathComponent_preimage_eq_of_ofBasedPath_eq hα_end hαβ,
    pathComponentIn_congr hβ] at hself
  exact hself

/-- The preimage of a sheet under `ofBasedPath` is the corresponding `basedPathSheet`.
This expresses that the sheet is saturated under the `ofBasedPath` quotient. -/
theorem ofBasedPath_preimage_sheet (U : Set X) (hxU : x ∈ U)
    (q : Path.Homotopic.Quotient x₀ x) :
    ofBasedPath x₀ ⁻¹' sheet U hxU q = basedPathSheet U hxU q := by
  apply Set.Subset.antisymm
  · intro α hα
    obtain ⟨β, hβ, hαβ⟩ := hα
    induction q using Quotient.inductionOn with
    | h p =>
      change β ∈ basedPathComponent U p at hβ
      change α ∈ basedPathComponent U p
      exact mem_basedPathComponent_of_ofBasedPath_eq hβ hαβ.symm
  · intro α hα
    exact ⟨α, hα, rfl⟩

theorem isOpen_sheet [LocPathConnectedSpace X] (hX : SemilocallySimplyConnected X)
    (U : Set X) (hU_open : IsOpen U) (hxU : x ∈ U)
    (q : Path.Homotopic.Quotient x₀ x) :
    IsOpen (sheet U hxU q) := by
  rw [(isQuotientMap_ofBasedPath x₀).isOpen_preimage.symm]
  rw [ofBasedPath_preimage_sheet]
  induction q using Quotient.inductionOn with
  | h p => exact BasedPath.isOpen_pathComponent_preimage hX hU_open _

theorem mem_sheet_self {U : Set X} (hxU : x ∈ U) (p : Path x₀ x) :
    ofBasedPath x₀ (BasedPath.ofPath p) ∈ sheet U hxU (Path.Homotopic.Quotient.mk p) :=
  ⟨BasedPath.ofPath p, mem_pathComponentIn_self
    (by simpa [BasedPath.endpoint, BasedPath.ofPath, p.target] using hxU), rfl⟩

/-- Sheet surjection onto `U`: every point of `U` is the projection of a point of the sheet. -/
theorem sheet_surjOn [LocPathConnectedSpace X]
    {U : Set X} (hU_pathConn : IsPathConnected U)
    (hxU : x ∈ U) (q : Path.Homotopic.Quotient x₀ x) :
    (sheet U hxU q).SurjOn (proj (x₀ := x₀)) U := by
  intro v hvU
  induction q using Quotient.inductionOn with
  | h p =>
    have hp_end : BasedPath.endpoint (BasedPath.ofPath p) ∈ U :=
      (BasedPath.endpoint_ofPath p).symm ▸ hxU
    obtain ⟨δ, hδU⟩ := hU_pathConn.exists_path hxU hvU
    let δ' : Path (BasedPath.endpoint (BasedPath.ofPath p)) v :=
      δ.cast (BasedPath.endpoint_ofPath p) rfl
    have hδ'_range : Set.range δ' ⊆ U := by
      rintro _ ⟨t, rfl⟩
      exact hδU ⟨t, rfl⟩
    let γ := BasedPath.append (BasedPath.ofPath p) δ'
    have h_joined : JoinedIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U)
        (BasedPath.ofPath p) γ :=
      BasedPath.joinedIn_preimage_of_append (BasedPath.ofPath p) hp_end δ' hδ'_range
    have hγ_in : γ ∈ basedPathComponent U p := h_joined
    refine ⟨ofBasedPath x₀ γ, ⟨γ, hγ_in, rfl⟩, ?_⟩
    change BasedPath.endpoint γ = v
    exact BasedPath.endpoint_append _ _

/-- Sheets over the same good neighborhood, indexed by `Path.Homotopic.Quotient`, are pairwise
disjoint. -/
theorem sheet_pairwise_disjoint [LocPathConnectedSpace X]
    {U : Set X}
    (hU_slsc : ∀ {a b : X}, a ∈ U → b ∈ U → ∀ (p q : Path a b),
      Set.range p ⊆ U → Set.range q ⊆ U → Path.Homotopic p q)
    (hxU : x ∈ U) :
    Pairwise fun (q₁ q₂ : Path.Homotopic.Quotient x₀ x) =>
      Disjoint (sheet U hxU q₁) (sheet U hxU q₂) := by
  intro q₁ q₂ hne
  refine Set.disjoint_iff.mpr ?_
  rintro e ⟨he₁, he₂⟩
  apply hne
  induction q₁ using Quotient.inductionOn with
  | h p₁ =>
    induction q₂ using Quotient.inductionOn with
    | h p₂ =>
      obtain ⟨α₁, hα₁, rfl⟩ := he₁
      obtain ⟨α₂, hα₂, hαeq⟩ := he₂
      change α₁ ∈ basedPathComponent U p₁ at hα₁
      change α₂ ∈ basedPathComponent U p₂ at hα₂
      have hα₁_end : BasedPath.endpoint α₁ ∈ U := hα₁.target_mem
      have h_same : pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) α₁ =
          pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) α₂ :=
        pathComponent_preimage_eq_of_ofBasedPath_eq hα₁_end hαeq.symm
      have hp₁_end : BasedPath.endpoint (BasedPath.ofPath p₁) ∈ U :=
        (BasedPath.endpoint_ofPath p₁).symm ▸ hxU
      have h_joined_p : JoinedIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U)
          (BasedPath.ofPath p₁) (BasedPath.ofPath p₂) := by
        have h_α₁_eq_p₁ : pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) α₁ =
            pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) (BasedPath.ofPath p₁) :=
          pathComponentIn_congr hα₁
        have h_α₂_eq_p₂ : pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) α₂ =
            pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) (BasedPath.ofPath p₂) :=
          pathComponentIn_congr hα₂
        have hp₁_mem : BasedPath.ofPath p₁ ∈
            pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U)
              (BasedPath.ofPath p₂) := by
          rw [← h_α₂_eq_p₂, ← h_same, h_α₁_eq_p₁]
          exact mem_pathComponentIn_self hp₁_end
        exact hp₁_mem.symm
      have h_end_eq : BasedPath.endpoint (BasedPath.ofPath p₁) =
          BasedPath.endpoint (BasedPath.ofPath p₂) := by
        rw [BasedPath.endpoint_ofPath, BasedPath.endpoint_ofPath]
      have h_hom := BasedPath.toPath_homotopic_of_joinedIn_slsc
        hU_slsc hp₁_end h_end_eq h_joined_p
      have h_uc_eq : ofBasedPath x₀ (BasedPath.ofPath p₁) =
          ofBasedPath x₀ (BasedPath.ofPath p₂) :=
        ofBasedPath_eq_of_homotopic_toPath h_end_eq h_hom
      -- Extract `⟦p₁⟧ = ⟦p₂⟧` from the `ofBasedPath` equality.
      change (Path.Homotopic.Quotient.mk p₁ : Path.Homotopic.Quotient x₀ x) =
        Path.Homotopic.Quotient.mk p₂
      rw [ofBasedPath_ofPath, ofBasedPath_ofPath] at h_uc_eq
      exact eq_of_heq ((Sigma.mk.injEq _ _ _ _).mp h_uc_eq).2

/-- Sheets exhaust `proj ⁻¹' U`: every element of the preimage lies in some sheet. -/
theorem sheet_exhaustive [LocPathConnectedSpace X]
    {U : Set X} (hU_pathConn : IsPathConnected U)
    (hxU : x ∈ U) :
    (proj (x₀ := x₀) ⁻¹' U) ⊆ ⋃ q : Path.Homotopic.Quotient x₀ x, sheet U hxU q := by
  intro e he
  obtain ⟨α, rfl⟩ := surjective_ofBasedPath x₀ e
  change BasedPath.endpoint α ∈ U at he
  -- Get a path from `endpoint α` to `x` inside `U`.
  obtain ⟨η, hη_range⟩ := hU_pathConn.exists_path he hxU
  -- Use `p := α.toPath.trans η : Path x₀ x` as the sheet index.
  let p : Path x₀ x := α.toPath.trans η
  refine Set.mem_iUnion.mpr ⟨Path.Homotopic.Quotient.mk p, α, ?_, rfl⟩
  -- Show α ∈ basedPathComponent U p.
  change α ∈ pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) (BasedPath.ofPath p)
  -- `BasedPath.ofPath p = append α η`, so α is joined to it by `joinedIn_preimage_of_append`.
  have h_join : JoinedIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) α
      (BasedPath.append α η) :=
    BasedPath.joinedIn_preimage_of_append α he η hη_range
  -- `BasedPath.append α η = BasedPath.ofPath p` by definition.
  change JoinedIn _ α (BasedPath.ofPath (α.toPath.trans η)) at h_join
  exact h_join.symm

/-- In a good neighborhood `U`, the projection `proj` is injective on each sheet. -/
theorem sheet_proj_injOn [LocPathConnectedSpace X]
    {U : Set X}
    (hU_slsc : ∀ {a b : X}, a ∈ U → b ∈ U → ∀ (p q : Path a b),
      Set.range p ⊆ U → Set.range q ⊆ U → Path.Homotopic p q)
    (hxU : x ∈ U) (q : Path.Homotopic.Quotient x₀ x) :
    (sheet U hxU q).InjOn (proj (x₀ := x₀)) := by
  rintro _ ⟨α₁, hα₁, rfl⟩ _ ⟨α₂, hα₂, rfl⟩ h_proj
  rw [proj_ofBasedPath, proj_ofBasedPath] at h_proj
  have hα₁_end : BasedPath.endpoint α₁ ∈ U :=
    basedPathSheet_subset_endpoint_preimage U hxU q hα₁
  induction q using Quotient.inductionOn with
  | h p =>
    change α₁ ∈ basedPathComponent U p at hα₁
    change α₂ ∈ basedPathComponent U p at hα₂
    have h_joined : JoinedIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) α₁ α₂ :=
      hα₁.symm.trans hα₂
    have h_homotopic : Path.Homotopic (α₁.toPath.cast rfl h_proj.symm) α₂.toPath :=
      BasedPath.toPath_homotopic_of_joinedIn_slsc hU_slsc hα₁_end h_proj h_joined
    exact ofBasedPath_eq_of_homotopic_toPath h_proj h_homotopic

end UniversalCover
