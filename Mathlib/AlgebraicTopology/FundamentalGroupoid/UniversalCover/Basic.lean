/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.BasedPath

/-!
# The universal cover: definition and sheets

For a topological space `X` with basepoint `x₀`, this file defines the universal cover
`UniversalCover x₀` as the quotient of the based-path space `BasedPath x₀` by endpoint-preserving
homotopy, and constructs the sheets of the projection `UniversalCover x₀ → X` over a good
neighborhood `U`.

## Main definitions

* `UniversalCover x₀`: pairs of a point `proj : X` and a homotopy class
  `path : Path.Homotopic.Quotient x₀ proj`, with the quotient topology from `BasedPath x₀`.
* `UniversalCover.ofBasedPath`: the quotient map `BasedPath x₀ → UniversalCover x₀`.
* `UniversalCover.sheet U hxU q`: the sheet over `U` indexed by `q : Path.Homotopic.Quotient x₀ x`.

## Main statements

* `UniversalCover.isOpenMap_proj`: the projection is an open map.
* `UniversalCover.toPath_homotopic_of_ofBasedPath_eq` and
  `UniversalCover.ofBasedPath_eq_of_homotopic_toPath`: two based paths have the same image in the
  universal cover iff they are homotopic rel endpoints.
* `UniversalCover.isOpen_sheet`, `UniversalCover.sheet_surjOn`,
  `UniversalCover.sheet_pairwise_disjoint`, `UniversalCover.sheet_exhaustive`,
  `UniversalCover.sheet_proj_injOn`: the sheets over a good neighborhood `U` are open, disjoint,
  cover `proj ⁻¹' U`, and each maps bijectively onto `U`.

## Implementation notes

Textbook treatments (e.g. Hatcher, Section 1.3) topologize the universal cover directly, by
declaring a basic open set for each pair `(q, U)` of a homotopy class `q` and a good
neighborhood `U`. We instead take the quotient topology from the compact-open topology on
`BasedPath x₀`. This makes the comparison with the path-space topology automatic, at the cost
of having to prove openness of sheets (`BasedPath.isOpen_pathComponent_preimage`).
-/

public section
noncomputable section

open scoped unitInterval
open Function Topology

variable {X : Type*} [TopologicalSpace X]

/-- A point of the universal cover: a point `proj` of `X` together with a homotopy class of paths
from the basepoint to `proj`. The topology is the quotient topology from `BasedPath x₀`, see
`UniversalCover.instTopologicalSpace`. -/
@[ext]
structure UniversalCover (x₀ : X) where
  /-- The point of `X` lying under this point of the universal cover. -/
  proj : X
  /-- The homotopy class of paths from the basepoint to `proj`. -/
  path : Path.Homotopic.Quotient x₀ proj

namespace UniversalCover

variable {x₀ x : X}

theorem mk_inj {q₁ q₂ : Path.Homotopic.Quotient x₀ x} : mk x q₁ = mk x q₂ ↔ q₁ = q₂ := by
  simp

/-- The quotient map from based paths to the universal cover. -/
@[expose] def ofBasedPath (x₀ : X) (α : BasedPath x₀) : UniversalCover x₀ :=
  mk (BasedPath.endpoint α) (Path.Homotopic.Quotient.mk α.toPath)

/-- The quotient topology from the compact-open topology on `BasedPath x₀`. -/
instance instTopologicalSpace (x₀ : X) : TopologicalSpace (UniversalCover x₀) :=
  TopologicalSpace.coinduced (ofBasedPath x₀) inferInstance

@[fun_prop] theorem continuous_ofBasedPath (x₀ : X) : Continuous (ofBasedPath x₀) :=
  continuous_coinduced_rng

theorem ofBasedPath_ofPath {y : X} (p : Path x₀ y) :
    ofBasedPath x₀ (BasedPath.ofPath p) = mk y (Path.Homotopic.Quotient.mk p) :=
  UniversalCover.ext p.target (Path.Homotopic.hpath_hext fun _ ↦ rfl)

theorem surjective_ofBasedPath (x₀ : X) : Function.Surjective (ofBasedPath x₀) := by
  rintro ⟨x, q⟩
  induction q using Quotient.inductionOn with
  | h γ => exact ⟨BasedPath.ofPath γ, ofBasedPath_ofPath γ⟩

theorem isQuotientMap_ofBasedPath (x₀ : X) : IsQuotientMap (ofBasedPath x₀) :=
  ⟨⟨rfl⟩, surjective_ofBasedPath x₀⟩

@[simp]
theorem proj_ofBasedPath (x₀ : X) (γ : BasedPath x₀) :
    proj (ofBasedPath x₀ γ) = BasedPath.endpoint γ :=
  rfl

theorem endpoint_eq_of_ofBasedPath_eq {α β : BasedPath x₀}
    (h : ofBasedPath x₀ α = ofBasedPath x₀ β) :
    BasedPath.endpoint α = BasedPath.endpoint β := by
  simpa using congrArg (proj (x₀ := x₀)) h

theorem ofBasedPath_eq (α : BasedPath x₀) :
    ofBasedPath x₀ α = mk (BasedPath.endpoint α) (Path.Homotopic.Quotient.mk α.toPath) :=
  rfl

/-- Based paths with the same image in the universal cover are homotopic rel endpoints. -/
theorem toPath_homotopic_of_ofBasedPath_eq {α β : BasedPath x₀}
    (h : ofBasedPath x₀ α = ofBasedPath x₀ β) :
    (α.toPath.cast rfl (endpoint_eq_of_ofBasedPath_eq h).symm).Homotopic β.toPath := by
  rw [ofBasedPath_eq α, ofBasedPath_eq β] at h
  obtain ⟨hend, hq⟩ := UniversalCover.mk.injEq .. |>.mp h
  have hcast : HEq (Path.Homotopic.Quotient.mk α.toPath)
      (Path.Homotopic.Quotient.mk (α.toPath.cast rfl hend.symm)) :=
    Path.Homotopic.hpath_hext fun _ ↦ rfl
  exact Path.Homotopic.Quotient.exact (eq_of_heq (hcast.symm.trans hq))

/-- Based paths that are homotopic rel endpoints have the same image in the universal cover. -/
theorem ofBasedPath_eq_of_homotopic_toPath {α β : BasedPath x₀}
    (heq : BasedPath.endpoint α = BasedPath.endpoint β)
    (h : (α.toPath.cast rfl heq.symm).Homotopic β.toPath) :
    ofBasedPath x₀ α = ofBasedPath x₀ β := by
  rw [ofBasedPath_eq α, ofBasedPath_eq β]
  refine UniversalCover.ext heq ?_
  have hcast : HEq (Path.Homotopic.Quotient.mk α.toPath)
      (Path.Homotopic.Quotient.mk (α.toPath.cast rfl heq.symm)) :=
    Path.Homotopic.hpath_hext fun _ ↦ rfl
  exact hcast.trans (heq_of_eq (Quotient.sound h))

@[fun_prop] theorem continuous_proj (x₀ : X) : Continuous (proj (x₀ := x₀)) := by
  rw [(isQuotientMap_ofBasedPath x₀).continuous_iff]
  exact BasedPath.continuous_endpoint

/-- The projection `UniversalCover x₀ → X` is open when `X` is locally path-connected. -/
theorem isOpenMap_proj [LocallyPathConnectedSpace X] (x₀ : X) :
    IsOpenMap (proj (x₀ := x₀)) := by
  intro s hs
  have himage : BasedPath.endpoint '' (ofBasedPath x₀ ⁻¹' s) = proj (x₀ := x₀) '' s := by
    rw [show BasedPath.endpoint (x₀ := x₀) = proj ∘ ofBasedPath x₀ from rfl, Set.image_comp,
      Set.image_preimage_eq s (surjective_ofBasedPath x₀)]
  rw [← himage]
  exact BasedPath.isOpenMap_endpoint x₀ _ ((isQuotientMap_ofBasedPath x₀).isOpen_preimage.2 hs)

/-! ### Sheets over a good neighborhood

For `x ∈ U`, the sheets of `proj ⁻¹' U` are indexed by the homotopy classes
`q : Path.Homotopic.Quotient x₀ x`: the sheet of `q = ⟦p⟧` is the image of the path component of
`BasedPath.ofPath p` in `endpoint ⁻¹' U`. -/

/-- The path component of `BasedPath.ofPath p` in `endpoint ⁻¹' U`. -/
def basedPathComponent (U : Set X) {y : X} (p : Path x₀ y) : Set (BasedPath x₀) :=
  pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) (BasedPath.ofPath p)

/-- The sheet over `U` indexed by `q : Path.Homotopic.Quotient x₀ x`, as a set of based paths.
This is well defined by `BasedPath.pathComponent_preimage_saturated`. -/
def basedPathSheet (U : Set X) (hxU : x ∈ U) (q : Path.Homotopic.Quotient x₀ x) :
    Set (BasedPath x₀) :=
  Quotient.liftOn q (fun p : Path x₀ x ↦ basedPathComponent U p)
    fun _ _ h ↦ BasedPath.pathComponent_preimage_saturated hxU h

theorem basedPathSheet_mk (U : Set X) (hxU : x ∈ U) (p : Path x₀ x) :
    basedPathSheet U hxU (Path.Homotopic.Quotient.mk p) = basedPathComponent U p :=
  (rfl)

theorem basedPathSheet_subset_endpoint_preimage (U : Set X) (hxU : x ∈ U)
    (q : Path.Homotopic.Quotient x₀ x) :
    basedPathSheet U hxU q ⊆ BasedPath.endpoint (x₀ := x₀) ⁻¹' U := by
  induction q using Quotient.inductionOn with
  | h p => exact fun _ hβ ↦ hβ.target_mem

/-- The sheet over `U` indexed by `q : Path.Homotopic.Quotient x₀ x`, as a subset of the universal
cover. -/
def sheet (U : Set X) (hxU : x ∈ U) (q : Path.Homotopic.Quotient x₀ x) :
    Set (UniversalCover x₀) :=
  ofBasedPath x₀ '' basedPathSheet U hxU q

/-- Based paths with the same image in the universal cover lie in the same path component of
`endpoint ⁻¹' U`. -/
theorem pathComponent_preimage_eq_of_ofBasedPath_eq {U : Set X} {α β : BasedPath x₀}
    (hα : BasedPath.endpoint α ∈ U) (hαβ : ofBasedPath x₀ α = ofBasedPath x₀ β) :
    pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) α =
      pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) β :=
  BasedPath.pathComponent_preimage_saturated (x₀ := x₀) (endpoint_eq_of_ofBasedPath_eq hαβ ▸ hα)
    (toPath_homotopic_of_ofBasedPath_eq hαβ)

theorem mem_basedPathComponent_of_ofBasedPath_eq {U : Set X} {y : X} {p : Path x₀ y}
    {α β : BasedPath x₀} (hβ : β ∈ basedPathComponent U p)
    (hαβ : ofBasedPath x₀ α = ofBasedPath x₀ β) :
    α ∈ basedPathComponent U p := by
  have hα : BasedPath.endpoint α ∈ U := (endpoint_eq_of_ofBasedPath_eq hαβ).symm ▸ hβ.target_mem
  have hself := mem_pathComponentIn_self (F := BasedPath.endpoint (x₀ := x₀) ⁻¹' U) hα
  rwa [pathComponent_preimage_eq_of_ofBasedPath_eq hα hαβ, pathComponentIn_congr hβ] at hself

/-- Sheets are saturated for the quotient map `ofBasedPath`. -/
theorem ofBasedPath_preimage_sheet (U : Set X) (hxU : x ∈ U) (q : Path.Homotopic.Quotient x₀ x) :
    ofBasedPath x₀ ⁻¹' sheet U hxU q = basedPathSheet U hxU q := by
  refine Set.Subset.antisymm (fun α ⟨β, hβ, hαβ⟩ ↦ ?_) fun α hα ↦ ⟨α, hα, rfl⟩
  induction q using Quotient.inductionOn with
  | h p => exact mem_basedPathComponent_of_ofBasedPath_eq hβ hαβ.symm

theorem isOpen_sheet [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) (q : Path.Homotopic.Quotient x₀ x) :
    IsOpen (sheet U hxU q) := by
  rw [← (isQuotientMap_ofBasedPath x₀).isOpen_preimage, ofBasedPath_preimage_sheet]
  induction q using Quotient.inductionOn with
  | h p => exact BasedPath.isOpen_pathComponent_preimage hU _

theorem mem_sheet_self {U : Set X} (hxU : x ∈ U) (p : Path x₀ x) :
    ofBasedPath x₀ (BasedPath.ofPath p) ∈ sheet U hxU (Path.Homotopic.Quotient.mk p) :=
  ⟨BasedPath.ofPath p, mem_pathComponentIn_self (by simpa [BasedPath.endpoint_ofPath] using hxU),
    rfl⟩

/-- Each sheet over a path-connected `U` projects onto `U`. -/
theorem sheet_surjOn {U : Set X} (hU : IsPathConnected U) (hxU : x ∈ U)
    (q : Path.Homotopic.Quotient x₀ x) :
    (sheet U hxU q).SurjOn (proj (x₀ := x₀)) U := by
  intro v hv
  induction q using Quotient.inductionOn with
  | h p =>
    obtain ⟨δ, hδ⟩ := hU.exists_path hxU hv
    let δ' : Path (BasedPath.endpoint (BasedPath.ofPath p)) v :=
      δ.cast (BasedPath.endpoint_ofPath p) rfl
    have hp : BasedPath.endpoint (BasedPath.ofPath p) ∈ U :=
      (BasedPath.endpoint_ofPath p).symm ▸ hxU
    refine ⟨ofBasedPath x₀ (BasedPath.append (BasedPath.ofPath p) δ'),
      ⟨_, BasedPath.joinedIn_preimage_of_append (BasedPath.ofPath p) hp δ' hδ, rfl⟩, ?_⟩
    rw [proj_ofBasedPath]
    exact BasedPath.endpoint_append _ _

/-- Sheets over a path-homotopy-trivial `U` are pairwise disjoint. -/
theorem sheet_pairwise_disjoint {U : Set X} (hU : IsPathHomotopyTrivial U) (hxU : x ∈ U) :
    Pairwise (Disjoint on sheet (x₀ := x₀) U hxU) := by
  intro q₁ q₂ hne
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨α₁, hα₁, rfl⟩ ⟨α₂, hα₂, hαeq⟩
  apply hne
  induction q₁ using Quotient.inductionOn with
  | h p₁ =>
    induction q₂ using Quotient.inductionOn with
    | h p₂ =>
      have hp₁ : BasedPath.endpoint (BasedPath.ofPath p₁) ∈ U :=
        (BasedPath.endpoint_ofPath p₁).symm ▸ hxU
      have h_end : BasedPath.endpoint (BasedPath.ofPath p₁) =
          BasedPath.endpoint (BasedPath.ofPath p₂) := by
        rw [BasedPath.endpoint_ofPath, BasedPath.endpoint_ofPath]
      have h_join : JoinedIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U)
          (BasedPath.ofPath p₁) (BasedPath.ofPath p₂) :=
        hα₁.trans (mem_basedPathComponent_of_ofBasedPath_eq hα₂ hαeq.symm).symm
      have h_eq := ofBasedPath_eq_of_homotopic_toPath h_end
        (BasedPath.toPath_homotopic_of_joinedIn hU h_end h_join)
      rw [ofBasedPath_ofPath, ofBasedPath_ofPath] at h_eq
      exact eq_of_heq ((UniversalCover.mk.injEq _ _ _ _).mp h_eq).2

/-- Over a path-connected `U`, the sheets cover `proj ⁻¹' U`. -/
theorem sheet_exhaustive {U : Set X} (hU : IsPathConnected U) (hxU : x ∈ U) :
    proj (x₀ := x₀) ⁻¹' U ⊆ ⋃ q : Path.Homotopic.Quotient x₀ x, sheet U hxU q := by
  intro e he
  obtain ⟨α, rfl⟩ := surjective_ofBasedPath x₀ e
  rw [Set.mem_preimage, proj_ofBasedPath] at he
  obtain ⟨η, hη⟩ := hU.exists_path he hxU
  -- `α` is joined to `ofPath (α.toPath.trans η) = append α η` inside `endpoint ⁻¹' U`.
  refine Set.mem_iUnion.mpr ⟨Path.Homotopic.Quotient.mk (α.toPath.trans η),
    α, (BasedPath.joinedIn_preimage_of_append α he η hη).symm, rfl⟩

/-- Over a path-homotopy-trivial `U`, the projection is injective on each sheet. -/
theorem sheet_proj_injOn {U : Set X} (hU : IsPathHomotopyTrivial U) (hxU : x ∈ U)
    (q : Path.Homotopic.Quotient x₀ x) :
    (sheet U hxU q).InjOn (proj (x₀ := x₀)) := by
  rintro _ ⟨α₁, hα₁, rfl⟩ _ ⟨α₂, hα₂, rfl⟩ h_proj
  rw [proj_ofBasedPath, proj_ofBasedPath] at h_proj
  have hα₁_end : BasedPath.endpoint α₁ ∈ U := basedPathSheet_subset_endpoint_preimage U hxU q hα₁
  induction q using Quotient.inductionOn with
  | h p =>
    exact ofBasedPath_eq_of_homotopic_toPath h_proj
      (BasedPath.toPath_homotopic_of_joinedIn hU h_proj (hα₁.symm.trans hα₂))

end UniversalCover
