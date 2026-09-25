/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SemilocallySimplyConnected

/-!
# Based paths

For a topological space `X` and a basepoint `x₀ : X`, this file introduces the space
`BasedPath x₀` of continuous maps `γ : C(I, X)` with `γ 0 = x₀`, topologized as a subspace of
`C(I, X)` with the compact-open topology. This is the space whose quotient by endpoint-preserving
homotopy is the universal cover of `X` at `x₀`.

The main results concern the path components of `endpoint ⁻¹' U` for an open set `U ⊆ X`: these
are the sheets of the universal cover over `U`.

## Main definitions

* `BasedPath x₀`: the space of based paths out of `x₀`.
* `BasedPath.endpoint`, `BasedPath.toPath`, `BasedPath.ofPath`, `BasedPath.append`: basic API.
* `BasedPath.deformTerminal`: modify a based path near its endpoint by a short path, without
  moving far in the compact-open topology.
* `BasedPath.initialSegmentFamily`: the family `t ↦ γ|_[0, t]` of initial segments.

## Main statements

* `BasedPath.isOpenMap_endpoint`: the endpoint map `BasedPath x₀ → X` is open when `X` is
  locally path-connected.
* `BasedPath.joinedIn_preimage_of_append`: appending a path inside `U` stays in the same path
  component of `endpoint ⁻¹' U`.
* `BasedPath.isOpen_pathComponent_preimage`: in a semilocally simply connected, locally
  path-connected space, path components of `endpoint ⁻¹' U` are open for open `U`.
* `BasedPath.toPath_homotopic_of_joinedIn`: based paths with the same endpoint in a common path
  component of `endpoint ⁻¹' U`, for `U` path-homotopy-trivial, are homotopic.
* `BasedPath.pathComponent_preimage_saturated`: path components of `endpoint ⁻¹' U` are
  invariant under endpoint-preserving homotopy.
-/

open scoped unitInterval
open Set Topology

variable {X : Type*} [TopologicalSpace X]

/-- The space of paths in `X` starting at `x₀`, as a subspace of `C(I, X)`. -/
@[expose] public def BasedPath (x₀ : X) :=
  { γ : C(I, X) // γ 0 = x₀ }

namespace BasedPath

variable {x₀ : X}

public instance : TopologicalSpace (BasedPath x₀) :=
  inferInstanceAs (TopologicalSpace { γ : C(I, X) // γ 0 = x₀ })

public instance : FunLike (BasedPath x₀) I X where
  coe γ := γ.1
  coe_injective _ _ h := Subtype.ext (DFunLike.coe_injective h)

/-- Evaluation `BasedPath x₀ × I → X` is jointly continuous. -/
public instance : ContinuousEval (BasedPath x₀) I X :=
  .of_continuous_forget continuous_subtype_val

@[simp] public theorem mk_apply (γ : C(I, X)) (h : γ 0 = x₀) (t : I) :
    (show BasedPath x₀ from ⟨γ, h⟩) t = γ t := rfl

@[simp] public theorem val_apply (γ : BasedPath x₀) (t : I) : γ.1 t = γ t := rfl

/-- A map into `BasedPath x₀` is continuous iff its uncurried form is. -/
public theorem continuous_iff {Y : Type*} [TopologicalSpace Y] {f : Y → BasedPath x₀} :
    Continuous f ↔ Continuous fun p : Y × I ↦ f p.1 p.2 :=
  ⟨fun hf ↦ continuous_eval.comp ((continuous_subtype_val.comp hf).prodMap continuous_id),
    fun h ↦ Continuous.subtype_mk (ContinuousMap.continuous_of_continuous_uncurry _ h) _⟩

@[simp] public theorem source (γ : BasedPath x₀) : γ 0 = x₀ := γ.2

/-- The endpoint of a based path. -/
@[expose] public def endpoint (γ : BasedPath x₀) : X := γ 1

/-- A based path as a path to its endpoint. -/
@[expose] public def toPath (γ : BasedPath x₀) : Path x₀ (endpoint γ) where
  toContinuousMap := γ.1
  source' := γ.2
  target' := rfl

/-- Not a simp lemma, since it would conflict with `endpoint_refl` and friends. -/
public theorem endpoint_def (γ : BasedPath x₀) : endpoint γ = γ 1 := rfl

@[fun_prop] public theorem continuous_endpoint : Continuous (endpoint (x₀ := x₀)) :=
  continuous_eval_const 1

@[simp] public theorem toPath_apply (γ : BasedPath x₀) (t : I) : toPath γ t = γ t := rfl

@[ext] public theorem ext {γ γ' : BasedPath x₀} (h : ∀ t, γ t = γ' t) : γ = γ' :=
  DFunLike.ext γ γ' h

/-- A path out of `x₀` as a based path. -/
@[expose] public def ofPath {y : X} (γ : Path x₀ y) : BasedPath x₀ :=
  ⟨γ.toContinuousMap, γ.source⟩

@[simp] public theorem ofPath_apply {y : X} (γ : Path x₀ y) (t : I) : ofPath γ t = γ t := rfl

@[simp] public theorem ofPath_toPath {y : X} (γ : Path x₀ y) :
    (ofPath γ).toPath = γ.cast rfl γ.target := by
  ext t
  rfl

public theorem endpoint_ofPath {y : X} (γ : Path x₀ y) : endpoint (ofPath γ) = y :=
  γ.target

@[simp] public theorem ofPath_toPath_self (γ : BasedPath x₀) : ofPath γ.toPath = γ := rfl

@[simp] public theorem ofPath_cast {y y' : X} (γ : Path x₀ y) (h : y' = y) :
    ofPath (γ.cast rfl h) = ofPath γ := rfl

/-- The constant based path at `x₀`. -/
@[expose] public def refl (x₀ : X) : BasedPath x₀ :=
  ofPath (Path.refl x₀)

@[simp] public theorem endpoint_refl (x₀ : X) : endpoint (refl x₀) = x₀ :=
  endpoint_ofPath _

@[simp] public theorem toPath_refl (x₀ : X) : (refl x₀).toPath = Path.refl x₀ := by
  ext
  rfl

@[simp] public theorem ofPath_refl (x₀ : X) : ofPath (Path.refl x₀) = refl x₀ := rfl

/-- Append a path `δ` at the endpoint of a based path `γ`. -/
@[expose] public noncomputable def append {y : X} (γ : BasedPath x₀)
    (δ : Path (endpoint γ) y) : BasedPath x₀ :=
  ofPath (γ.toPath.trans δ)

public theorem endpoint_append {y : X} (γ : BasedPath x₀) (δ : Path (endpoint γ) y) :
    endpoint (append γ δ) = y :=
  endpoint_ofPath _

/-! ### Deforming the end of a based path -/

section deformTerminal

variable {v : X} (γ : BasedPath x₀) (δ : Path (endpoint γ) v) {a b : ℝ}

/-- Replace the end of a based path `γ` by a path `δ` out of its endpoint: the result agrees with
`γ` on `[0, a]`, traverses `γ|_[a, 1]` on `[a, b]`, and traverses `δ` on `[b, 1]`. When `a` is
close to `1` and `δ` is short, this is close to `γ` in the compact-open topology; this is the key
to `isOpenMap_endpoint`. -/
@[expose] public noncomputable def deformTerminal (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) :
    BasedPath x₀ :=
  let f : ℝ → X := fun t ↦
    if t ≤ a then γ.toPath.extend t
    else if t ≤ b then γ.toPath.extend (a + (t - a) / (b - a) * (1 - a))
    else δ.extend ((t - b) / (1 - b))
  have hf : Continuous f := by
    refine Continuous.if_le γ.toPath.continuous_extend ?_ continuous_id continuous_const ?_
    · refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const ?_
      rintro t rfl
      simp [div_self (sub_ne_zero.2 hab.ne')]
    · rintro t rfl
      simp [hab.le]
  ⟨⟨fun t ↦ f t, hf.comp continuous_subtype_val⟩, by simp [f, ha]⟩

variable (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) {t : I}

public theorem deformTerminal_apply_of_le (ht : (t : ℝ) ≤ a) :
    deformTerminal γ δ ha hab hb t = γ t := by
  simp [deformTerminal, ht]

public theorem deformTerminal_apply_of_lt_of_le (hat : a < t) (htb : (t : ℝ) ≤ b) :
    deformTerminal γ δ ha hab hb t = γ.toPath.extend (a + (t - a) / (b - a) * (1 - a)) := by
  simp [deformTerminal, not_le.2 hat, htb]

public theorem deformTerminal_apply_of_lt (hbt : b < t) :
    deformTerminal γ δ ha hab hb t = δ.extend ((t - b) / (1 - b)) := by
  simp [deformTerminal, not_le.2 (hab.trans hbt), not_le.2 hbt]

@[simp] public theorem endpoint_deformTerminal : endpoint (deformTerminal γ δ ha hab hb) = v := by
  rw [endpoint_def, deformTerminal_apply_of_lt γ δ ha hab hb (by simpa using hb)]
  simp [div_self (sub_ne_zero.2 hb.ne')]

/-- Past time `a`, the deformed path stays in any set containing `γ [a, 1]` and the range of
`δ`. -/
public theorem deformTerminal_apply_mem_of_lt {W : Set X}
    (hγW : MapsTo γ.toPath.extend (Icc a 1) W) (hδW : range δ ⊆ W) (hat : a < t) :
    deformTerminal γ δ ha hab hb t ∈ W := by
  by_cases htb : (t : ℝ) ≤ b
  · rw [deformTerminal_apply_of_lt_of_le γ δ ha hab hb hat htb]
    have h₀ : 0 ≤ (t - a) / (b - a) := div_nonneg (by linarith) (by linarith)
    have h₁ : (t - a) / (b - a) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    exact hγW ⟨by nlinarith, by nlinarith⟩
  · rw [deformTerminal_apply_of_lt γ δ ha hab hb (not_le.1 htb), Path.extend_apply _
      ⟨div_nonneg (by linarith) (by linarith), (div_le_one (by linarith)).2 (by linarith [t.2.2])⟩]
    exact hδW (mem_range_self _)

end deformTerminal

/-! ### The endpoint map is open -/

/-- Given a basic compact-open neighborhood of `γ` (finitely many constraints `MapsTo γ K U`),
there is a path-connected neighborhood `W` of `endpoint γ` and a terminal interval `[a, 1]` such
that deforming `γ` on `[a, 1]` by any path in `W` stays inside the neighborhood. -/
private theorem exists_deformTerminal_mapsTo [LocallyPathConnectedSpace X] (γ : BasedPath x₀)
    {S : Set (Set I × Set X)} (hS_fin : S.Finite)
    (hS : ∀ K U, (K, U) ∈ S → IsCompact K ∧ IsOpen U ∧ MapsTo γ K U) :
    ∃ W : Set X, IsOpen W ∧ endpoint γ ∈ W ∧ IsPathConnected W ∧
      ∃ (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b < 1),
        ∀ v ∈ W, ∀ δ : Path (endpoint γ) v, range δ ⊆ W →
          ∀ K U, (K, U) ∈ S → MapsTo (deformTerminal γ δ ha hab hb) K U := by
  classical
  -- `W`: a path-connected neighborhood of `endpoint γ` inside every `U` whose `K` contains `1`.
  have hO : IsOpen (⋂ KU ∈ S, ⋂ (_ : (1 : I) ∈ KU.1), KU.2) :=
    hS_fin.isOpen_biInter fun KU hKU ↦ isOpen_iInter_of_finite fun _ ↦ (hS KU.1 KU.2 hKU).2.1
  have hγO : endpoint γ ∈ ⋂ KU ∈ S, ⋂ (_ : (1 : I) ∈ KU.1), KU.2 := by
    simp only [mem_iInter]
    exact fun KU hKU h1 ↦ (hS KU.1 KU.2 hKU).2.2 h1
  obtain ⟨W, ⟨hW_open, hW, hW_pc⟩, hWO⟩ :=
    (isOpen_isPathConnected_basis (endpoint γ)).mem_iff.mp (hO.mem_nhds hγO)
  -- Times near `1` at which `γ` lies in `W`, avoiding every `K` not containing `1`.
  have hN : γ ⁻¹' W ∩ ⋂ KU ∈ S, ⋂ (_ : (1 : I) ∉ KU.1), KU.1ᶜ ∈ 𝓝 (1 : I) := by
    refine Filter.inter_mem ((hW_open.preimage (map_continuous γ)).mem_nhds hW) ?_
    refine (hS_fin.isOpen_biInter fun KU hKU ↦ isOpen_iInter_of_finite fun _ ↦
      (hS KU.1 KU.2 hKU).1.isClosed.isOpen_compl).mem_nhds ?_
    simp only [mem_iInter, mem_compl_iff]
    exact fun _ _ h ↦ h
  obtain ⟨a₀, ⟨-, ha₀⟩, hIoc⟩ := exists_Ioc_subset_of_mem_nhds' hN (show (0 : I) < 1 by simp)
  have ha₀' : (a₀ : ℝ) < 1 := ha₀
  have ha : 0 ≤ ((a₀ : ℝ) + 1) / 2 := by linarith [a₀.2.1]
  have hab : ((a₀ : ℝ) + 1) / 2 < (((a₀ : ℝ) + 1) / 2 + 1) / 2 := by linarith
  have hb : (((a₀ : ℝ) + 1) / 2 + 1) / 2 < 1 := by linarith
  refine ⟨W, hW_open, hW, hW_pc, _, _, ha, hab, hb, fun v hv δ hδ K U hKU t ht ↦ ?_⟩
  by_cases hta : (t : ℝ) ≤ ((a₀ : ℝ) + 1) / 2
  · rw [deformTerminal_apply_of_le γ δ ha hab hb hta]
    exact (hS K U hKU).2.2 ht
  · rw [not_le] at hta
    have htIoc : t ∈ Ioc a₀ 1 := ⟨show (a₀ : ℝ) < t by linarith, t.2.2⟩
    -- `t` avoids every `K` not containing `1`, so `1 ∈ K` and hence `W ⊆ U`.
    have h1K : (1 : I) ∈ K := by
      by_contra h1K
      exact mem_iInter.1 (mem_iInter₂.1 (hIoc htIoc).2 (K, U) hKU) h1K ht
    refine (hWO.trans ((biInter_subset_of_mem hKU).trans (iInter_subset _ h1K)))
      (deformTerminal_apply_mem_of_lt γ δ ha hab hb (fun s hs ↦ ?_) hδ hta)
    rw [Path.extend_apply _ ⟨ha.trans hs.1, hs.2⟩]
    exact (hIoc ⟨show (a₀ : ℝ) < s by linarith [hs.1], hs.2⟩).1

/-- The endpoint map `BasedPath x₀ → X` is open when `X` is locally path-connected. -/
public theorem isOpenMap_endpoint [LocallyPathConnectedSpace X] (x₀ : X) :
    IsOpenMap (endpoint (x₀ := x₀)) := by
  refine IsOpenMap.of_nhds_le fun γ s hs ↦ ?_
  obtain ⟨N, hN, hNs⟩ := (mem_nhds_subtype {γ : C(I, X) | γ 0 = x₀} γ _).mp (Filter.mem_map.mp hs)
  obtain ⟨S, hS_fin, hS, hSN⟩ := ContinuousMap.mem_nhds_iff.mp hN
  obtain ⟨W, hW_open, hW, hW_pc, a, b, ha, hab, hb, hη⟩ := exists_deformTerminal_mapsTo γ hS_fin hS
  refine Filter.mem_of_superset (hW_open.mem_nhds hW) fun v hv ↦ ?_
  obtain ⟨δ, hδ⟩ := hW_pc.exists_path hW hv
  exact endpoint_deformTerminal γ δ ha hab hb ▸ hNs (hSN (hη v hv δ hδ))

/-! ### Initial segments -/

/-- The family `t ↦ γ|_[0, t]` of initial segments of a based path. -/
@[expose] public noncomputable def initialSegmentFamily (γ : BasedPath x₀) (t : I) :
    BasedPath x₀ :=
  ofPath (γ.toPath.initialSegmentFamily t)

@[simp] public theorem initialSegmentFamily_zero (γ : BasedPath x₀) :
    γ.initialSegmentFamily 0 = refl x₀ := by
  rw [initialSegmentFamily, Path.initialSegmentFamily_zero, ofPath_cast, ofPath_refl]

@[simp] public theorem initialSegmentFamily_one (γ : BasedPath x₀) :
    γ.initialSegmentFamily 1 = γ := by
  rw [initialSegmentFamily, Path.initialSegmentFamily_one, ofPath_cast, ofPath_toPath_self]

@[fun_prop] public theorem continuous_initialSegmentFamily (γ : BasedPath x₀) :
    Continuous γ.initialSegmentFamily :=
  continuous_iff.mpr (by simpa only using! γ.toPath.continuous_initialSegmentFamily_uncurry)

/-- Appending the initial segments of a path `δ` to a based path is continuous in the
parameter. -/
@[fun_prop] public theorem continuous_append_initialSegmentFamily {z : X}
    (γ : BasedPath x₀) (δ : Path (endpoint γ) z) :
    Continuous fun t : I ↦ γ.append (δ.initialSegmentFamily t) := by
  refine continuous_iff.mpr ?_
  simpa using!
    Path.trans_continuous_family (fun _ : I ↦ γ.toPath)
      (Path.continuous_uncurry_iff.mpr continuous_const) δ.initialSegmentFamily
      δ.continuous_initialSegmentFamily_uncurry

/-! ### Path components of `endpoint ⁻¹' U` -/

/-- Homotopic paths give based paths in the same path component of `endpoint ⁻¹' U`. -/
public theorem joinedIn_preimage_of_homotopic {y : X} {U : Set X} (hy : y ∈ U) {p q : Path x₀ y}
    (h : p.Homotopic q) : JoinedIn (endpoint (x₀ := x₀) ⁻¹' U) (ofPath p) (ofPath q) := by
  obtain ⟨H⟩ := h
  refine ⟨⟨⟨fun t ↦ ofPath (H.eval t), continuous_iff.mpr H.continuous⟩, by simp, by simp⟩,
    fun t ↦ ?_⟩
  change endpoint (ofPath (H.eval t)) ∈ U
  rw [endpoint_ofPath]
  exact hy

/-- Appending a path inside `U` stays in the same path component of `endpoint ⁻¹' U`. -/
public theorem joinedIn_preimage_of_append {U : Set X} {z : X} (γ : BasedPath x₀)
    (hγ : endpoint γ ∈ U) (δ : Path (endpoint γ) z) (hδ : range δ ⊆ U) :
    JoinedIn (endpoint (x₀ := x₀) ⁻¹' U) γ (append γ δ) := by
  -- Slide `γ` to `append γ (Path.refl _)`, then grow the appended path along `δ`.
  refine (joinedIn_preimage_of_homotopic hγ (Path.Homotopic.trans_refl γ.toPath)).symm.trans ?_
  refine ⟨⟨⟨fun t ↦ append γ (δ.initialSegmentFamily t), by fun_prop⟩, ?_, ?_⟩, fun t ↦ ?_⟩
  · simpa using! congrArg (append γ) (Path.initialSegmentFamily_zero δ)
  · simpa using! congrArg (append γ) (Path.initialSegmentFamily_one δ)
  · change endpoint (append γ (δ.initialSegmentFamily t)) ∈ U
    rw [endpoint_append]
    exact hδ (mem_range_self _)

/-- In a semilocally simply connected, locally path-connected space, a based path `α` with
endpoint in an open set `U` has an open neighborhood all of whose members are joined to `α`
inside `endpoint ⁻¹' U`. -/
public theorem exists_open_nhds_pathComponent_preimage
    [SemilocallySimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {U : Set X} (hU : IsOpen U) (α : BasedPath x₀) (hα : endpoint α ∈ U) :
    ∃ N : Set (BasedPath x₀), IsOpen N ∧ α ∈ N ∧
      ∀ β ∈ N, JoinedIn (endpoint (x₀ := x₀) ⁻¹' U) α β := by
  classical
  obtain ⟨n, part, T, hα_tube⟩ := α.toPath.exists_pathInTube_of_semilocallySimplyConnectedSpace
  -- Shrink the last vertex set of the tube to a path-connected neighborhood of `endpoint α`
  -- inside `U`.
  have hα_last : α (part.t (Fin.last n)) ∈ T.V (Fin.last n) ∩ U := by
    refine ⟨hα_tube.mem_V _, ?_⟩
    rw [part.t_last]
    exact hα
  set W := pathComponentIn (T.V (Fin.last n) ∩ U) (α (part.t (Fin.last n))) with hW
  have hV' : ∀ j, Function.update T.V (Fin.last n) W j ⊆ T.V j := fun j ↦ by
    rw [Function.update_apply]
    split_ifs with h
    · exact h ▸ pathComponentIn_subset.trans inter_subset_left
    · exact subset_rfl
  let T' : TubeData X n :=
    { T with
      V := Function.update T.V (Fin.last n) W
      isOpen_V := fun j ↦ by
        rw [Function.update_apply]
        split_ifs
        · exact ((T.isOpen_V _).inter hU).pathComponentIn _
        · exact T.isOpen_V j
      isPathConnected_V := fun j ↦ by
        rw [Function.update_apply]
        split_ifs with h
        · exact isPathConnected_pathComponentIn hα_last
        · exact T.isPathConnected_V j
      V_castSucc_subset := fun i ↦ (hV' _).trans (T.V_castSucc_subset i)
      V_succ_subset := fun i ↦ (hV' _).trans (T.V_succ_subset i) }
  have hα_tube' : PathInTube α.toPath part T' :=
    ⟨hα_tube.mapsTo, fun j ↦ by
      change α (part.t j) ∈ Function.update T.V (Fin.last n) W j
      rw [Function.update_apply]
      split_ifs with h
      · exact h ▸ mem_pathComponentIn_self hα_last
      · exact hα_tube.mem_V j⟩
  refine ⟨{β | PathInTube β.toPath part T'},
    (T'.isOpen_setOf_pathInTube part).preimage continuous_subtype_val, hα_tube', fun β hβ ↦ ?_⟩
  obtain ⟨ρ, hρ, h⟩ := hα_tube'.exists_trans_homotopic hβ
  have hρU : range ρ ⊆ U := by
    refine hρ.trans ?_
    change Function.update T.V (Fin.last n) W (Fin.last n) ⊆ U
    rw [Function.update_self]
    exact pathComponentIn_subset.trans inter_subset_right
  exact (joinedIn_preimage_of_append α hα ρ hρU).trans
    (joinedIn_preimage_of_homotopic (hρU ρ.target_mem_range) h)

/-- In a semilocally simply connected, locally path-connected space, the path components of
`endpoint ⁻¹' U` are open for open `U`. -/
public theorem isOpen_pathComponent_preimage
    [SemilocallySimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {U : Set X} (hU : IsOpen U) (α : BasedPath x₀) :
    IsOpen (pathComponentIn (endpoint (x₀ := x₀) ⁻¹' U) α) := by
  refine isOpen_iff_forall_mem_open.mpr fun β hβ ↦ ?_
  obtain ⟨N, hN_open, hβN, hN⟩ := exists_open_nhds_pathComponent_preimage hU β hβ.target_mem
  exact ⟨N, fun γ hγ ↦ hβ.trans (hN γ hγ), hN_open, hβN⟩

/-- Two based paths with the same endpoint, joined inside `endpoint ⁻¹' U` for a
path-homotopy-trivial set `U`, are homotopic as paths. A path in `BasedPath x₀` from `α` to `β`
is a free homotopy from `α` to `β` whose endpoint trace is a loop in `U`, and that loop is
nullhomotopic. -/
public theorem toPath_homotopic_of_joinedIn {U : Set X} (hU : IsPathHomotopyTrivial U)
    {α β : BasedPath x₀} (heq : endpoint α = endpoint β)
    (hαβ : JoinedIn (endpoint (x₀ := x₀) ⁻¹' U) α β) :
    (α.toPath.cast rfl heq.symm).Homotopic β.toPath := by
  obtain ⟨F, hF⟩ := hαβ
  -- The free homotopy `H : α ∼ β` given by `H (t, s) = F t s`.
  let H : ContinuousMap.Homotopy α.1 β.1 :=
    { toFun := fun ts ↦ F ts.1 ts.2
      continuous_toFun := continuous_iff.mp F.continuous
      map_zero_left := fun s ↦ by simp
      map_one_left := fun s ↦ by simp }
  -- The endpoint trace of `F` is a loop `L` in `U`, hence nullhomotopic.
  let L : Path (endpoint β) (endpoint β) := (H.evalAt 1).cast heq.symm rfl
  have hL : L.Homotopic (Path.refl _) := hU.nullhomotopic L (by
    rintro _ ⟨t, rfl⟩
    exact hF t)
  -- Naturality of `H`: `α · L` is homotopic to `H.evalAt 0 · β`, and `H.evalAt 0` is constant.
  have key : ((α.toPath.cast rfl heq.symm).trans L).Homotopic ((Path.refl x₀).trans β.toPath) := by
    have h := (Path.Homotopic.map_trans_evalAt H Path.id).pathCast α.2.symm
      (show endpoint β = β.1 1 from rfl)
    have h0 : H.evalAt 0 = (Path.refl x₀).cast α.2 β.2 := Path.ext <| funext fun t ↦ (F t).2
    rw [h0] at h
    convert h using 1 <;> exact Path.ext rfl
  exact (Path.Homotopic.trans_right_of_nullhomotopic hL).symm.trans
    (key.trans (Path.Homotopic.refl_trans _))

/-- Path components of `endpoint ⁻¹' U` are invariant under endpoint-preserving homotopy. -/
public theorem pathComponent_preimage_saturated {U : Set X} {y : X} (hy : y ∈ U)
    {p q : Path x₀ y} (h : p.Homotopic q) :
    pathComponentIn (endpoint (x₀ := x₀) ⁻¹' U) (ofPath p) =
      pathComponentIn (endpoint (x₀ := x₀) ⁻¹' U) (ofPath q) :=
  pathComponentIn_congr (joinedIn_preimage_of_homotopic hy h).symm

end BasedPath
