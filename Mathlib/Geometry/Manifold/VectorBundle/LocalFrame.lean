/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.Elaborators

/-!
# Local frames in a vector bundle

Let `V → M` be a finite rank smooth vector bundle with standard fiber `F`.
Given a basis `b` for `F` and a local trivialisation `e` for `V`,
we construct a **smooth local frame** on `V` w.r.t. `e` and `b`,
i.e. a collection of sections `s_i` of `V` which is smooth on `e.baseSet` such that `{s_i x}` is a
basis of `V x` for each `x ∈ e.baseSet`. Any section `s` of `e` can be uniquely written as
`s = ∑ i, f^i s_i` near `x`, and `s` is smooth at `x` iff the functions `f^i` are.

We use this to construct local extensions of a vector to a section which is smooth on the
trivialisation domain.

## Main definitions and results
* `Basis.localFrame e b`: the local frame on `V` w.r.t. a local trivialisation `e` of `V` and a
  basis `b` of `F`. Use `b.localFrame e i` to access the i-th section in that frame.
* `b.contMDiffOn_localFrame_baseSet`: each section `b.localFrame e i` is smooth on `e.baseSet`
* `b.localFrame_toBasis_at e`: for each `x ∈ e.baseSet`, the vectors `b.localFrame e i x` form
  a basis of `F`
* `Basis.localFrame_repr e b i` describes the coefficient of sections of `V` w.r.t.`b.localFrame e`:
  `b.localFrame e i` is a linear map from sections of `V` to functions `M → 𝕜`.
* `b.localFrame_repr_spec e`: near `x`, we have
  `s = ∑ i, (b.localFrame_repr e i s) • b.localFrame e i`
* `b.localFrame_repr_congr e`: the coefficient `b.localFrame_repr e b i` of `s` in the local frame
  induced by `e` and `b` at `x` only depends on `s` at `x`.
* `b.contMDiffOn_localFrame_repr`: if `s` is a `C^k` section, each coefficient
  `b.localFrame_repr e i s` is `C^k` on `e.baseSet`
* `b.contMDiffAt_iff_localFrame_repr e`: a section `s` is `C^k` at `x ∈ e.baseSet`
  iff all of its frame coefficients are
* `b.contMDiffOn_iff_localFrame_repr e`: a section `s` is `C^k` on an open set `t ⊆ e.baseSet`
  iff all of its frame coefficients are

* TODO: mention all the localExtensionOn definitions and results

TODO add a more complete doc-string!

## Implementation notes
* local frames use the junk value pattern: they are defined on all of `M`, but their value is
  only meaningful inside `e.baseSet`
* something about local extensions (and different fields)

## Tags
vector bundle, local frame, smoothness

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
  [∀ x : M, TopologicalSpace (V x)]
  -- not needed in this file
  -- [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle n F V I]
  -- `V` vector bundle

noncomputable section

section IsLocalFrame

omit [IsManifold I 0 M] [VectorBundle 𝕜 F V]

variable {ι : Type*} {s : ι → (x : M) → V x} {u : Set M}

variable (I F) in
/-
A family of sections `s i` of `V → M` is called a **C^k local frame** on a set `U ⊆ M` iff
- the section values `s i x` form a basis for each `x ∈ U`,
- each section `s i` is `C^k` on `U`.
-/
structure IsLocalFrameOn (s : ι → (x : M) → V x) (u : Set M) where
  linearIndependent {x : M} (hx : x ∈ u) : LinearIndependent 𝕜 (s · x)
  generating {x : M} (hx : x ∈ u) : ⊤ ≤ Submodule.span 𝕜 (Set.range (s · x))
  contMDiffOn (i : ι) : CMDiff 1 (T% (s i))

namespace IsLocalFrameOn

/-- Given a local frame `{s i}` on `U ∋ x`, returns the basis `{s i}` of `V x` -/
def toBasisAt (hs : IsLocalFrameOn I F s u) {x} (hx : x ∈ u) : Basis ι 𝕜 (V x) :=
  Basis.mk (hs.linearIndependent hx) (hs.generating hx)

@[simp]
lemma toBasisAt_coe (hs : IsLocalFrameOn I F s u) {x} (hx : x ∈ u) (i : ι) :
    (toBasisAt hs hx) i = s i x := by
  simpa only [toBasisAt] using Basis.mk_apply (hs.linearIndependent hx) (hs.generating hx) i

open scoped Classical in
/-- Coefficients of a section `s` of `V` w.r.t. a local frame `{s i}` on `u`.
Outside of `u`, this returns the junk value 0. -/
-- NB. We don't use simps here, as we prefer to have dedicated `_apply` lemmas for the separate
-- cases.
def repr (hs : IsLocalFrameOn I F s u) (i : ι) : (Π x : M, V x) →ₗ[𝕜] M → 𝕜 where
  toFun s x := if hx : x ∈ u then (hs.toBasisAt hx).repr (s x) i else 0
  map_add' s s' := by
    ext x
    by_cases hx : x ∈ u <;> simp [hx]
  map_smul' c s := by
    ext x
    by_cases hx : x ∈ u <;> simp [hx]

variable {x : M}

@[simp]
lemma repr_apply_of_notMem (hs : IsLocalFrameOn I F s u) (hx : x ∉ u) (t : Π x : M, V x) (i : ι) :
    hs.repr i t x = 0 := by
  simp [repr, hx]

@[simp]
lemma repr_apply_of_mem (hs : IsLocalFrameOn I F s u) (hx : x ∈ u) (t : Π x : M, V x) (i : ι) :
    hs.repr i t x = (hs.toBasisAt hx).repr (t x) i := by
  simp [repr, hx]

-- TODO: add uniqueness of the decomposition; follows from the IsBasis property in the definition

lemma repr_sum_eq [Fintype ι] (hs : IsLocalFrameOn I F s u) (t : Π x : M,  V x) (hx : x ∈ u) :
    t x = (∑ i, (hs.repr i t x) • (s i x)) := by
  simpa [repr, hx] using (Basis.sum_repr (hs.toBasisAt hx) (t x)).symm

/-- A local frame locally spans the space of sections for `V`: for each local frame `s i` on an open
set `u` around `x`, we have `t = ∑ i, (hs.repr i t) • (s i x)` near `x`. -/
lemma repr_spec [Fintype ι] (hs : IsLocalFrameOn I F s u)
    (t : Π x : M,  V x) (hx : x ∈ u) (hu : IsOpen u) :
    ∀ᶠ x' in 𝓝 x, t x' = ∑ i, (hs.repr i t x') • (s i x') :=
  eventually_nhds_iff.mpr ⟨u, fun _ h ↦ hs.repr_sum_eq t h, hu, hx⟩

/-- The representation of `s` in a local frame at `x` only depends on `s` at `x`. -/
lemma repr_congr (hs : IsLocalFrameOn I F s u) {t t' : Π x : M,  V x}-- (hx : x ∈ u)
    {i : ι} (htt' : t x = t' x) :
    hs.repr i t x = hs.repr i t' x := by
  by_cases hxe : x ∈ u
  · simp [repr, hxe]
    congr
  · simp [repr, hxe]

lemma repr_apply_zero_at (hs : IsLocalFrameOn I F s u) {t : Π x : M, V x} (ht : t x = 0) (i : ι) :
    hs.repr i t x = 0 := by
  simp [hs.repr_congr (t' := 0) ht]

-- XXX: this statement does not readily transfer, but probably I won't need this particular
-- result in this general setting
-- /-- Suppose `e` is a compatible trivialisation around `x ∈ M`, and `t` a bundle section.
-- Then the coefficient of `t` w.r.t. a local frame `s i` near `x`
-- equals the cofficient of "`t x` read in the trivialisation `e`" for `b i`. -/
-- lemma localFrame_repr_eq_repr (hs : IsLocalFrameOn I F s u) (hxe : x ∈ u) {i : ι} {t : Π x : M, V x} :
--     hs.repr i t x = b.repr (e (s x)).2 i := by
--   simp [b.localFrame_repr_apply_of_mem_baseSet e hxe, Basis.localFrame_toBasis_at]

end IsLocalFrameOn

end IsLocalFrame

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

omit [IsManifold I 0 M] in
/-- Each local frame `s^i ∈ Γ(E)` of a `C^k` vector bundle, defined by a local trivialisation `e`,
is `C^k` on `e.baseSet`. -/
lemma contMDiffOn_localFrame_baseSet
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] (b : Basis ι 𝕜 F) (i : ι) :
    CMDiff[e.baseSet] n (T% b.localFrame e i) := by
  rw [contMDiffOn_section_of_mem_baseSet₀]
  apply (contMDiffOn_const (c := b i)).congr
  intro y hy
  simp [localFrame, hy, localFrame_toBasis_at]

omit [IsManifold I 0 M] in
lemma _root_.contMDiffAt_localFrame_of_mem
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] (b : Basis ι 𝕜 F) (i : ι) {x : M} (hx : x ∈ e.baseSet) :
    CMDiffAt n (T% b.localFrame e i) x :=
  (contMDiffOn_localFrame_baseSet n e b i).contMDiffAt <| e.open_baseSet.mem_nhds hx

@[simp]
lemma localFrame_apply_of_mem_baseSet
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] (b : Basis ι 𝕜 F) {i : ι} {x : M} (hx : x ∈ e.baseSet) :
    b.localFrame e i x = b.localFrame_toBasis_at e hx i := by
  simp [localFrame, hx]

@[simp]
lemma localFrame_apply_of_notMem
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] (b : Basis ι 𝕜 F) {i : ι} {x : M} (hx : x ∉ e.baseSet) :
    b.localFrame e i x = 0 := by
  simp [localFrame, hx]

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
  [MemTrivializationAtlas e] {b : Basis ι 𝕜 F} {x : M}

variable (e b) in
@[simp]
lemma localFrame_repr_apply_of_notMem_baseSet (hx : x ∉ e.baseSet) (s : Π x : M, V x) (i : ι) :
    b.localFrame_repr e i s x = 0 := by
  simpa [localFrame_repr] using fun hx' ↦ (hx hx').elim

variable (e b) in
@[simp]
lemma localFrame_repr_apply_of_mem_baseSet (hx : x ∈ e.baseSet) (s : Π x : M, V x) (i : ι) :
    b.localFrame_repr e i s x = (b.localFrame_toBasis_at e hx).repr (s x) i := by
  simp [localFrame_repr, hx]

-- uniqueness of the decomposition: follows from the IsBasis property above

-- TODO: better name?
lemma localFrame_repr_sum_eq [Fintype ι] (s : Π x : M,  V x) {x'} (hx : x' ∈ e.baseSet) :
    s x' = (∑ i, (b.localFrame_repr e i s x') • b.localFrame e i x') := by
  simp [Basis.localFrame_repr, hx]
  exact (sum_repr (localFrame_toBasis_at e b hx) (s x')).symm

variable (b) in
/-- A local frame locally spans the space of sections for `V`: for each local trivialisation `e`
  of `V` around `x`, we have `s = ∑ i, (b.localFrame_repr e i s) • b.localFrame e i` -/
lemma localFrame_repr_spec [Fintype ι] {x : M} (hxe : x ∈ e.baseSet) (s : Π x : M,  V x) :
    ∀ᶠ x' in 𝓝 x, s x' = ∑ i, (b.localFrame_repr e i s x') • b.localFrame e i x' :=
  eventually_nhds_iff.mpr ⟨e.baseSet, fun _ h ↦ localFrame_repr_sum_eq s h, e.open_baseSet, hxe⟩

/-- The representation of `s` in a local frame at `x` only depends on `s` at `x`. -/
lemma localFrame_repr_congr (b : Basis ι 𝕜 F)
    {s s' : Π x : M,  V x} {i : ι} (hss' : s x = s' x) :
    b.localFrame_repr e i s x = b.localFrame_repr e i s' x := by
  by_cases hxe : x ∈ e.baseSet
  · simp [localFrame_repr, hxe, localFrame_toBasis_at]
    congr
  · simp [localFrame_repr, hxe]

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

/-- Suppose `e` is a compatible trivialisation around `x ∈ M`, and `s` a bundle section.
Then the coefficient of `s` w.r.t. the local frame induced by `b` and `e`
equals the cofficient of "`s x` read in the trivialisation `e`" for `b i`. -/
lemma localFrame_repr_eq_repr (hxe : x ∈ e.baseSet) (b : Basis ι 𝕜 F) {i : ι} {s : Π x : M, V x} :
    b.localFrame_repr e i s x = b.repr (e (s x)).2 i := by
  simp [b.localFrame_repr_apply_of_mem_baseSet e hxe, Basis.localFrame_toBasis_at]

end Basis

variable {ι : Type*} {e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [MemTrivializationAtlas e] {b : Basis ι 𝕜 F} {x : M}

omit [IsManifold I 0 M] in
/-- If `s` is `C^k` at `x`, so is its coefficient `b.localFrame_repr e i` in the local frame
near `x` induced by `e` and `b` -/
lemma contMDiffAt_localFrame_repr [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    (hxe : x ∈ e.baseSet) (b : Basis ι 𝕜 F)
    {s : Π x : M,  V x} {k : WithTop ℕ∞} [ContMDiffVectorBundle k F V I]
    (hs : CMDiffAt k (T% s) x) (i : ι) :
    CMDiffAt k (b.localFrame_repr e i s) x := by
  -- This boils down to computing the frame coefficients in a local trivialisation.
  classical
  -- step 1: on e.baseSet, can compute the coefficient very well
  let aux := fun x ↦ b.repr (e (s x)).2 i
  -- Since e.baseSet is open, this is sufficient.
  suffices CMDiffAt k aux x by
    apply this.congr_of_eventuallyEq ?_
    apply eventuallyEq_of_mem (s := e.baseSet) (by simp [e.open_baseSet.mem_nhds hxe])
    intro y hy
    simp [aux, Basis.localFrame_repr_eq_repr hy]
  simp only [aux]

  -- step 2: `s` read in trivialization `e` is `C^k`
  have h₁ : CMDiffAt k (fun x ↦ (e (s x)).2) x := by
    exact contMDiffAt_section_of_mem_baseSet hxe |>.1 hs
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

omit [IsManifold I 0 M] in
/-- If `s` is `C^k` on `t ⊆ e.baseSet`, so is its coefficient `b.localFrame_repr e i`
in the local frame induced by `e` -/
lemma contMDiffOn_localFrame_repr [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] (b : Basis ι 𝕜 F)
    {s : Π x : M,  V x} {k : WithTop ℕ∞} {t : Set M} [ContMDiffVectorBundle k F V I]
    (ht : IsOpen t) (ht' : t ⊆ e.baseSet)
    (hs : CMDiff[t] k (T% s)) (i : ι) : CMDiff[t] k (b.localFrame_repr e i s) :=
  fun _ hx ↦ (contMDiffAt_localFrame_repr (ht' hx) b
    (hs.contMDiffAt (ht.mem_nhds hx)) i).contMDiffWithinAt

omit [IsManifold I 0 M] [ContMDiffVectorBundle n F V I] in
/-- If `s` is `C^k` on `e.baseSet`, so is its coefficient `b.localFrame_repr e i` in the local frame
induced by `e` -/
lemma contMDiffOn_baseSet_localFrame_repr [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    (b : Basis ι 𝕜 F) {s : Π x : M,  V x} {k : WithTop ℕ∞} [ContMDiffVectorBundle k F V I]
    (hs : CMDiff[e.baseSet] k (T% s)) (i : ι) : CMDiff[e.baseSet] k (b.localFrame_repr e i s) :=
  contMDiffOn_localFrame_repr b e.open_baseSet (subset_refl _) hs _

omit [IsManifold I 0 M] in
/-- A section `s` of `V` is `C^k` at `x ∈ e.baseSet` iff each of its
coefficients `b.localFrame_repr e i s` in a local frame near `x` is -/
lemma contMDiffAt_iff_localFrame_repr [Fintype ι] [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    (b : Basis ι 𝕜 F) {s : Π x : M,  V x} {k : WithTop ℕ∞} [ContMDiffVectorBundle k F V I]
    {x' : M} (hx : x' ∈ e.baseSet) :
    CMDiffAt k (T% s) x' ↔ ∀ i, CMDiffAt k (b.localFrame_repr e i s) x' := by
  refine ⟨fun h i ↦ contMDiffAt_localFrame_repr hx b h i, fun hi ↦ ?_⟩
  have this (i) : CMDiffAt k (T% ((b.localFrame_repr e i) s • b.localFrame e i)) x' :=
    (hi i).smul_section (contMDiffAt_localFrame_of_mem k e b i hx)
  have almost : CMDiffAt k
      (T% (fun x ↦ ∑ i, (b.localFrame_repr e i) s x • b.localFrame e i x)) x' :=
    .sum_section fun i _ ↦ this i
  apply almost.congr_of_eventuallyEq ?_
  obtain ⟨u, heq, hu, hxu⟩ := eventually_nhds_iff.mp (b.localFrame_repr_spec hx s)
  exact eventually_of_mem (hu.mem_nhds hxu) fun x hx ↦ by simp [heq x hx]

omit [IsManifold I 0 M] in
/-- A section `s` of `V` is `C^k` on `t ⊆ e.baseSet` iff each of its
coefficients `b.localFrame_repr e i s` in a local frame near `x` is -/
lemma contMDiffOn_iff_localFrame_repr [Fintype ι] [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    (b : Basis ι 𝕜 F) {s : Π x : M,  V x} {k : WithTop ℕ∞} [ContMDiffVectorBundle k F V I]
    {t : Set M} (ht : IsOpen t) (ht' : t ⊆ e.baseSet) :
    CMDiff[t] k (T% s) ↔ ∀ i, CMDiff[t] k (b.localFrame_repr e i s) := by
  refine ⟨fun h i ↦ contMDiffOn_localFrame_repr b ht ht' h i, fun hi ↦ ?_⟩
  have this (i) : CMDiff[t] k (T% ((b.localFrame_repr e i) s • b.localFrame e i)) :=
    (hi i).smul_section ((b.contMDiffOn_localFrame_baseSet k e i).mono ht')
  let rhs := fun x' ↦ ∑ i, (b.localFrame_repr e i) s x' • b.localFrame e i x'
  have almost : CMDiff[t] k (T% rhs) := .sum_section fun i _ ↦ this i
  apply almost.congr
  intro y hy
  congr
  exact b.localFrame_repr_sum_eq s (ht' hy)

omit [IsManifold I 0 M] in
/-- A section `s` of `V` is `C^k` on a trivialisation domain `e.baseSet` iff each of its
coefficients `b.localFrame_repr e i s` in a local frame near `x` is -/
lemma contMDiffOn_baseSet_iff_localFrame_repr [Fintype ι] [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    (b : Basis ι 𝕜 F) {s : Π x : M,  V x} {k : WithTop ℕ∞} [ContMDiffVectorBundle k F V I] :
    CMDiff[e.baseSet] k (T% s) ↔ ∀ i, CMDiff[e.baseSet] k (b.localFrame_repr e i s) := by
  rw [contMDiffOn_iff_localFrame_repr b e.open_baseSet (subset_refl _)]

-- Differentiability of a section can be checked in terms of its local frame coefficients
section MDifferentiable

omit [IsManifold I 0 M] in
/-- If `s` is diffentiable at `x`, so is its coefficient `b.localFrame_repr e i` in the local frame
near `x` induced by `e` and `b` -/
lemma mdifferentiableAt_localFrame_repr [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    [ContMDiffVectorBundle 1 F V I]
    (hxe : x ∈ e.baseSet) (b : Basis ι 𝕜 F) {s : Π x : M,  V x} (hs : MDiffAt (T% s) x) (i : ι) :
    MDiffAt (b.localFrame_repr e i s) x := by
  -- This boils down to computing the frame coefficients in a local trivialisation.
  classical
  -- step 1: on e.baseSet, can compute the coefficient very well
  let aux := fun x ↦ b.repr (e (s x)).2 i
  -- Since e.baseSet is open, this is sufficient.
  suffices MDiffAt aux x by
    apply this.congr_of_eventuallyEq
    apply eventuallyEq_of_mem (s := e.baseSet) (by simp [e.open_baseSet.mem_nhds hxe])
    intro y hy
    simp [aux, Basis.localFrame_repr_eq_repr hy]
  simp only [aux]

  -- step 2: `s` read in trivialization `e` is differentiable
  have h₁ : MDiffAt (fun x ↦ (e (s x)).2) x := e.mdifferentiableAt_section_iff I s hxe |>.1 hs
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
  have hbas : MDifferentiableAt 𝓘(𝕜, F) 𝓘(𝕜) basL (e (s x)).2 :=
    mdifferentiableAt_iff_differentiableAt.mpr (basL.differentiable _)
  exact hbas.comp x h₁

omit [IsManifold I 0 M] in
/-- If `s` is differentiable on `t ⊆ e.baseSet`, so is its coefficient `b.localFrame_repr e i`
in the local frame induced by `e` -/
lemma mdifferentiableOn_localFrame_repr [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] (b : Basis ι 𝕜 F)
    [ContMDiffVectorBundle 1 F V I] {s : Π x : M,  V x} {t : Set M}
    (ht : IsOpen t) (ht' : t ⊆ e.baseSet) (hs : MDiff[t] (T% s)) (i : ι) :
    MDiff[t] (b.localFrame_repr e i s) :=
  fun _ hx ↦ (mdifferentiableAt_localFrame_repr (ht' hx) b
    (hs.mdifferentiableAt (ht.mem_nhds hx)) i).mdifferentiableWithinAt

omit [IsManifold I 0 M] in
/-- If `s` is differentiable on `e.baseSet`, so is its coefficient `b.localFrame_repr e i` in the
local frame induced by `e` -/
lemma mdifferentiableOn_baseSet_localFrame_repr [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    [ContMDiffVectorBundle 1 F V I] (b : Basis ι 𝕜 F) {s : Π x : M,  V x}
    (hs : MDiff[e.baseSet] (T% s)) (i : ι) :
    MDiff[e.baseSet] (b.localFrame_repr e i s) :=
  mdifferentiableOn_localFrame_repr b e.open_baseSet (subset_refl _) hs _

omit [IsManifold I 0 M] in
/-- A section `s` of `V` is differentiable at `x ∈ e.baseSet` iff each of its
coefficients `b.localFrame_repr e i s` in a local frame near `x` is -/
lemma mdifferentiableAt_iff_localFrame_repr [Fintype ι] [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    [ContMDiffVectorBundle 1 F V I]
    (b : Basis ι 𝕜 F) {s : Π x : M,  V x} {x' : M} (hx : x' ∈ e.baseSet) :
    MDiffAt (T% s) x' ↔ ∀ i, MDiffAt (b.localFrame_repr e i s) x' := by
  refine ⟨fun h i ↦ mdifferentiableAt_localFrame_repr hx b h i, fun hi ↦ ?_⟩
  have this (i) : MDiffAt (T% (b.localFrame_repr e i) s • b.localFrame e i) x' :=
    mdifferentiableAt_smul_section (hi i)
      ((contMDiffAt_localFrame_of_mem 1 e b i hx).mdifferentiableAt le_rfl)
  have almost : MDiffAt
      (T% (fun x ↦ ∑ i, (b.localFrame_repr e i) s x • b.localFrame e i x)) x' :=
    mdifferentiableAt_finsum_section fun i ↦ this i
  apply almost.congr_of_eventuallyEq ?_
  obtain ⟨u, heq, hu, hxu⟩ := eventually_nhds_iff.mp (b.localFrame_repr_spec hx s)
  exact eventually_of_mem (hu.mem_nhds hxu) fun x hx ↦ by simp [heq x hx]

omit [IsManifold I 0 M] in
/-- A section `s` of `V` is differentiable on `t ⊆ e.baseSet` iff each of its
coefficients `b.localFrame_repr e i s` in a local frame near `x` is -/
lemma mdifferentiableOn_iff_localFrame_repr [Fintype ι] [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    [ContMDiffVectorBundle 1 F V I] (b : Basis ι 𝕜 F) {s : Π x : M,  V x} {t : Set M}
    (ht : IsOpen t) (ht' : t ⊆ e.baseSet) :
    MDiff[t] (T% s) ↔ ∀ i, MDiff[t] (b.localFrame_repr e i s) := by
  refine ⟨fun h i ↦ mdifferentiableOn_localFrame_repr b ht ht' h i, fun hi ↦ ?_⟩
  have this (i) : MDiff[t] (T% ((b.localFrame_repr e i) s • b.localFrame e i)) :=
    mdifferentiableOn_smul_section (hi i) <|
      ((b.contMDiffOn_localFrame_baseSet 1 e i).mono ht').mdifferentiableOn le_rfl
  let rhs := fun x' ↦ ∑ i, (b.localFrame_repr e i) s x' • b.localFrame e i x'
  have almost : MDiff[t] (T% rhs) := mdifferentiableOn_finsum_section fun i ↦ this i
  apply almost.congr
  intro y hy
  congr
  exact b.localFrame_repr_sum_eq s (ht' hy)

omit [IsManifold I 0 M] in
/-- A section `s` of `V` is differentiable on a trivialisation domain `e.baseSet` iff each of its
coefficients `b.localFrame_repr e i s` in a local frame near `x` is -/
lemma mdifferentiableOn_baseSet_iff_localFrame_repr
    [Fintype ι] [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] [ContMDiffVectorBundle 1 F V I]
    (b : Basis ι 𝕜 F) {s : Π x : M,  V x} :
    MDiff[e.baseSet] (T% s) ↔ ∀ i, MDiff[e.baseSet] (b.localFrame_repr e i s) := by
  rw [mdifferentiableOn_iff_localFrame_repr b e.open_baseSet (subset_refl _)]

end MDifferentiable

end

-- local extension of a vector field in a trivialisation's base set
section extendLocally

variable {ι : Type*} [Fintype ι] {b : Basis ι 𝕜 F}
  {e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
  [MemTrivializationAtlas e] {x : M}

open scoped Classical in
-- TODO: add longer docs!
-- a starting point (not fully updated any more) is this:
/- Extend a vector `v ∈ V x` to a section of the bundle `V`, whose value at `x` is `v`.
The details of the extension are mostly unspecified: for covariant derivatives, the value of
`s` at points other than `x` will not matter (except for shorter proofs).
Thus, we choose `s` to be somewhat nice: our chosen construction is linear in `v`.
-/

-- comment: need not be smooth (outside of e.baseSet), but this is a useful building block for
-- global smooth extensions of vector fields
-- the latter caps this with a smooth bump function, which need not exist if k=C
-- In contrast, this definition makes sense over any field
-- (for example, *locally* holomorphic sections always exist),

/--
Extend a vector `v ∈ V x` to a local section of `V`, w.r.t. a chosen local trivialisation.
This construction uses a choice of local frame near `x`, w.r.t. to a basis `b` of `F` and a
compatible local trivialisation `e` of `V` near `x`: the resulting extension has constant
coefficients on `e.baseSet` w.r.t. this trivialisation (and is zero otherwise).

In particular, our construction is smooth on `e.baseSet`, and linear in the input vector `v`.
-/
noncomputable def localExtensionOn (b : Basis ι 𝕜 F)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
    (x : M) (v : V x) : (x' : M) → V x' :=
  fun x' ↦ if hx : x ∈ e.baseSet then
    letI bV := b.localFrame_toBasis_at e hx; ∑ i, bV.repr v i • b.localFrame e i x'
    else 0

variable (b e) in
@[simp]
lemma localExtensionOn_apply_self (hx : x ∈ e.baseSet) (v : V x) :
    ((localExtensionOn b e x v) x) = v := by
  simp [localExtensionOn, hx]
  nth_rw 2 [← (b.localFrame_toBasis_at e hx).sum_repr v]

/-- A local extension has constant frame coefficients within its defining trivialisation. -/
lemma localExtensionOn_localFrame_repr (b : Basis ι 𝕜 F)
    {e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [MemTrivializationAtlas e] {x : M} (hx : x ∈ e.baseSet) (v : V x) (i : ι)
    {x' : M} (hx' : x' ∈ e.baseSet):
    b.localFrame_repr e i (localExtensionOn b e x v) x' =
      b.localFrame_repr e i (localExtensionOn b e x v) x := by
  simp [localExtensionOn, hx, hx']

-- By construction, localExtensionOn is a linear map.

variable (b e) in
lemma localExtensionOn_add (v v' : V x) :
    localExtensionOn b e x (v + v') = localExtensionOn b e x v + localExtensionOn b e x v' := by
  ext x'
  by_cases hx: x ∈ e.baseSet; swap
  · simp [hx, localExtensionOn]
  · simp [hx, localExtensionOn, add_smul, Finset.sum_add_distrib]

variable (b e) in
lemma localExtensionOn_smul (a : 𝕜) (v : V x) :
    localExtensionOn b e x (a • v) = a • localExtensionOn b e x v := by
  ext x'
  by_cases hx: x ∈ e.baseSet; swap
  · simp [hx, localExtensionOn]
  · simp [hx, localExtensionOn, Finset.smul_sum]
    set B := Basis.localFrame_toBasis_at e b hx
    congr
    ext i
    rw [mul_smul a ((B.repr v) i)]

variable (F) in
omit [IsManifold I 0 M] in
lemma contMDiffOn_localExtensionOn [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    {x : M} (hx : x ∈ e.baseSet) (v : V x) [ContMDiffVectorBundle ∞ F V I] :
    CMDiff[e.baseSet] ∞ (T% (localExtensionOn b e x v)) := by
  -- The local frame coefficients of `localExtensionOn` w.r.t. the frame induced by `e` are
  -- constant, hence smoothness follows.
  rw [contMDiffOn_baseSet_iff_localFrame_repr b]
  intro i
  apply (contMDiffOn_const (c := (b.localFrame_repr e i) (localExtensionOn b e x v) x)).congr
  intro y hy
  rw [localExtensionOn_localFrame_repr b hx v i hy]

end extendLocally
