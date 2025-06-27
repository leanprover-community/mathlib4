/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Local frames in a vector bundle

TODO add a more complete doc-string!

-/
open Bundle Filter Function Topology

open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 0 M]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle n F V I]
  -- `V` vector bundle

namespace Basis

variable {ι : Type*}

noncomputable def localFrame_toBasis_at
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e]
    (b : Basis ι 𝕜 F) {x : M} (hx : x ∈ e.baseSet) : Basis ι 𝕜 (V x) :=
  b.map (e.linearEquivAt (R := 𝕜) x hx).symm

open scoped Classical in
-- If x is outside of `e.baseSet`, this returns the junk value 0.
noncomputable def localFrame
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e]
    (b : Basis ι 𝕜 F) : ι → (x : M) → V x := fun i x ↦
  -- idea: take the vector b i and apply the trivialisation e to it.
  if hx : x ∈ e.baseSet then b.localFrame_toBasis_at e hx i else 0

-- TODO: understand why this isn’t already a simp lemma
attribute [simp] Trivialization.apply_mk_symm

omit [IsManifold I 0 M]
    [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
    [ContMDiffVectorBundle n F V I] in
/-- Each local frame `s^i ∈ Γ(E)` of a `C^k` vector bundle, defined by a local trivialisation `e`,
is `C^k` on `e.baseSet`. -/
lemma contMDiffOn_localFrame_baseSet
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] (b : Basis ι 𝕜 F) (i : ι) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) n
      (fun x ↦ TotalSpace.mk' F x (b.localFrame e i x)) e.baseSet := by
  rw [contMDiffOn_section_of_mem_baseSet₀]
  apply (contMDiffOn_const (c := b i)).congr
  intro y hy
  simp [localFrame, hy, localFrame_toBasis_at]

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)] in
@[simp]
lemma localFrame_apply_of_mem_baseSet
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] (b : Basis ι 𝕜 F) {i : ι} {x : M} (hx : x ∈ e.baseSet) :
    b.localFrame e i x = b.localFrame_toBasis_at e hx i := by
  simp [localFrame, hx]

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)] in
@[simp]
lemma localFrame_apply_of_notMem
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] (b : Basis ι 𝕜 F) {i : ι} {x : M} (hx : x ∉ e.baseSet) :
    b.localFrame e i x = 0 := by
  simp [localFrame, hx]

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)] in
lemma localFrame_toBasis_at_coe
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e]
    (b : Basis ι 𝕜 F) {x : M} (i : ι) (hx : x ∈ e.baseSet) :
    b.localFrame_toBasis_at e hx i = b.localFrame e i x := by simp [hx]

-- XXX: is this result actually needed now? perhaps not, because of the toBasis definition?
/-- At each point `x ∈ M`, the sections `{sⁱ(x)}` of a local frame form a basis for `V x`. -/
def isBasis_localFrame
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e]
    (b : Basis ι 𝕜 F) : sorry := by
  -- the b i form a basis of F,
  -- and the trivialisation e is a linear equivalence (thus preserves bases)
  sorry

open scoped Classical in
/-- Coefficients of a section `s` of `V` w.r.t. the local frame `b.localFrame e i` -/
-- If x is outside of `e.baseSet`, this returns the junk value 0.
-- NB. We don't use simps here, as we prefer to have dedicated `_apply` lemmas for the separate
-- cases.
noncomputable def localFrame_repr
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e]
    (b : Basis ι 𝕜 F) (i : ι) : (Π x : M, V x) →ₗ[𝕜] M → 𝕜 where
  toFun s x := if hx : x ∈ e.baseSet then (b.localFrame_toBasis_at e hx).repr (s x) i else 0
  map_add' s s' := by
    ext x
    by_cases hx : x ∈ e.baseSet <;> simp [hx]
  map_smul' c s := by
    ext x
    by_cases hx : x ∈ e.baseSet <;> simp [hx]

variable {e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [MemTrivializationAtlas e] {b : Basis ι 𝕜 F}

variable (e b) in
omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)] in
@[simp]
lemma localFrame_repr_apply_of_notMem_baseSet {x : M}
    (hx : x ∉ e.baseSet) (s : Π x : M, V x) (i : ι) : b.localFrame_repr e i s x = 0 := by
  simpa [localFrame_repr] using fun hx' ↦ (hx hx').elim

variable (e b) in
omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)] in
@[simp]
lemma localFrame_repr_apply_of_mem_baseSet {x : M}
    (hx : x ∈ e.baseSet) (s : Π x : M, V x) (i : ι) :
    b.localFrame_repr e i s x = (b.localFrame_toBasis_at e hx).repr (s x) i := by
  simp [localFrame_repr, hx]

-- uniqueness of the decomposition: follows from the IsBasis property above

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)] in
variable (b) in
lemma localFrame_repr_spec [Fintype ι] {x : M} (hxe : x ∈ e.baseSet) (s : Π x : M,  V x) :
    ∀ᶠ x' in 𝓝 x, s x' = ∑ i, (b.localFrame_repr e i s x') • b.localFrame e i x' := by
  have {x'} (hx : x' ∈ e.baseSet) :
      s x' = (∑ i, (b.localFrame_repr e i s x') • b.localFrame e i x') := by
    simp [Basis.localFrame_repr, hx]
    exact (sum_repr (localFrame_toBasis_at e b hx) (s x')).symm
  exact eventually_nhds_iff.mpr ⟨e.baseSet, fun y a ↦ this a, e.open_baseSet, hxe⟩

variable {ι : Type*} [Fintype ι] {x : M}
  {e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
  [MemTrivializationAtlas e]

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)] [Fintype ι] in
/-- The representation of `s` in a local frame at `x` only depends on `s` at `x`. -/
lemma localFrame_repr_congr (b : Basis ι 𝕜 F)
    {s s' : Π x : M,  V x} {i : ι} (hss' : s x = s' x) :
    b.localFrame_repr e i s x = b.localFrame_repr e i s' x := by
  by_cases hxe : x ∈ e.baseSet
  · simp [localFrame_repr, hxe, localFrame_toBasis_at]
    congr
  · simp [localFrame_repr, hxe]

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)] [Fintype ι] in
lemma localFrame_repr_apply_zero_at
    (b : Basis ι 𝕜 F) {s : Π x : M, V x} (hs : s x = 0) (i : ι) :
    b.localFrame_repr e i s x = 0 := by
  rw [b.localFrame_repr_congr (s' := 0) (by simp [hs])]
  simp
  -- This proof may indicate a missing simp lemma.
  -- by_cases hxe : x ∈ e.baseSet; swap
  -- · simp [localFrame_repr, hxe]
  -- simp [localFrame_repr, localFrame_toBasis_at, hxe, hs]
  -- have : e.symm x = 0 := sorry
  -- have : (e { proj := x, snd := 0 }).2 = 0 := by
  --   trans (e { proj := x, snd := e.symm x 0 }).2
  --   · simp [this]
  --   · simp [e.apply_mk_symm hxe]
  -- simp [this]

variable {n}

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)] [Fintype ι] in
/-- Suppose `e` is a compatible trivialisation around `x ∈ M`, and `s` a bundle section.
Then the coefficient of `s` w.r.t. the local frame induced by `b` and `e`
equals the cofficient of "`s x` read in the trivialisation `e`" for `b i`. -/
lemma localFrame_repr_eq_repr (hxe : x ∈ e.baseSet) (b : Basis ι 𝕜 F) {i : ι} {s : Π x : M, V x} :
    b.localFrame_repr e i s x = b.repr (e (s x)).2 i := by
  simp [b.localFrame_repr_apply_of_mem_baseSet e hxe, Basis.localFrame_toBasis_at]

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [ContMDiffVectorBundle n F V I] [Fintype ι] in
lemma contMDiffAt_localFrame_repr [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    (hxe : x ∈ e.baseSet) (b : Basis ι 𝕜 F)
    {s : Π x : M,  V x} {k : WithTop ℕ∞}
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) k (fun x ↦ TotalSpace.mk' F x (s x)) x)
    (i : ι) : ContMDiffAt I 𝓘(𝕜) k (b.localFrame_repr e i s) x := by
  -- This boils down to computing the frame coefficients in a local trivialisation.
  classical
  -- step 1: on e.baseSet, can compute the coefficient very well
  let aux := fun x ↦ b.repr (e (s x)).2 i
  -- Since e.baseSet is open, this is sufficient.
  suffices ContMDiffAt I 𝓘(𝕜) k aux x by
    apply this.congr_of_eventuallyEq_of_mem ?_ trivial
    apply eventuallyEq_of_mem (s := e.baseSet) (by simp [e.open_baseSet.mem_nhds hxe])
    intro y hy
    simp [aux, hy, Basis.localFrame_repr_eq_repr hy]
  simp only [aux]

  -- step 2: `s` read in trivialization `e` is `C^k`
  have h₁ : ContMDiffAt I 𝓘(𝕜, F) k (fun x ↦ (e (s x)).2) x := by
    rw [contMDiffAt_section_of_mem_baseSet _ _ hxe] at hs
    exact hs
  -- step 3: `b.repr` is a linear map, so the composition is smooth
  let bas := fun v ↦ b.repr v i
  let basl : F →ₗ[𝕜] 𝕜 := {
    toFun := bas
    map_add' m m' := by simp [bas]
    map_smul' m x := by simp [bas]
  }
  let basL : F →L[𝕜] 𝕜 := {
    toLinearMap := basl
    cont := basl.continuous_of_finiteDimensional
  }
  have hbas : ContMDiffAt 𝓘(𝕜, F) 𝓘(𝕜) k basL (e (s x)).2 :=
    contMDiffAt_iff_contDiffAt.mpr <| (basL.contDiff (n := k)).contDiffAt
  exact hbas.comp x h₁

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [ContMDiffVectorBundle n F V I] [Fintype ι] in
lemma contMDiffOn_localFrame_repr [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] (b : Basis ι 𝕜 F)
    {s : Π x : M,  V x} {k : WithTop ℕ∞} {t : Set M}
    (ht : IsOpen t) (ht' : t ⊆ e.baseSet)
    (hs : ContMDiffOn I (I.prod 𝓘(𝕜, F)) k (fun x ↦ TotalSpace.mk' F x (s x)) t) (i : ι) :
    ContMDiffOn I 𝓘(𝕜) k (b.localFrame_repr e i s) t :=
  fun _ hx ↦ (b.contMDiffAt_localFrame_repr (ht' hx)
    (hs.contMDiffAt (ht.mem_nhds hx)) i).contMDiffWithinAt

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [ContMDiffVectorBundle n F V I] [Fintype ι] in
lemma contMDiffOn_baseSet_localFrame_repr [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    (b : Basis ι 𝕜 F) {s : Π x : M,  V x} {k : WithTop ℕ∞}
    (hs : ContMDiffOn I (I.prod 𝓘(𝕜, F)) k (fun x ↦ TotalSpace.mk' F x (s x)) e.baseSet) (i : ι) :
    ContMDiffOn I 𝓘(𝕜) k (b.localFrame_repr e i s) e.baseSet :=
  contMDiffOn_localFrame_repr b e.open_baseSet (subset_refl _) hs _

end Basis
