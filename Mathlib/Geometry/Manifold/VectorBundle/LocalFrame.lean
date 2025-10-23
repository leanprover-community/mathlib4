/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection


/-!
# Local frames in a vector bundle

Let `V → M` be a finite rank smooth vector bundle with standard fiber `F`.
A family of sections `s i` of `V → M` is called a **C^k local frame** on a set `U ⊆ M` iff each
section `s i` is `C^k` on `U`, and the section values `s i x` form a basis for each `x ∈ U`.
We define a predicate `IsLocalFrame` for a collection of sections to be a local frame on a set,
and define basic notions (such as the coefficients of a section w.r.t. a local frame, and
checking the smoothness of `t` via its coefficients in a local frame).

Given a basis `b` for `F` and a local trivialisation `e` for `V`, we construct a
**smooth local frame** on `V` w.r.t. `e` and `b`, i.e. a collection of sections `sᵢ` of `V`
which is smooth on `e.baseSet` such that `{sᵢ x}` is a basis of `V x` for each `x ∈ e.baseSet`.
Any section `s` of `e` can be uniquely written as `s = ∑ i, f^i sᵢ` near `x`,
and `s` is smooth at `x` iff the functions `f^i` are.

In this file, we prove the latter statement for finite-rank bundles (with coefficients in a
complete field). In `OrthonormalFrame.lean`, we will prove the same for real vector bundles of any
rank which admit a `C^n` bundle metric. This includes bundles of finite rank, modelled on a Hilbert
space or on a Banach space which has smooth partitions of unity.

We also use this to extend a vector in a single fiber `V x` to a section near `x` which is
smooth on the trivialisation domain.

## Main definitions and results

* `IsLocalFrameOn`: a family of sections `s i` of `V → M` is called a **C^k local frame** on a set
  `U ⊆ M` iff each section `s i` is `C^k` on `U`, and the section values `s i x` form a basis for
  each `x ∈ U`

Suppose `{sᵢ}` is a local frame on `U`, and `hs : IsLocalFrameOn s U`.
* `IsLocalFrameOn.toBasisAt hs`: for each `x ∈ U`, the vectors `sᵢ x` form a basis of `F`
* `IsLocalFrameOn.coeff hs` describes the coefficient of sections of `V` w.r.t. `{sᵢ}`.
  `hs.coeff i` is a linear map from sections of `V` to functions `M → 𝕜`.
* `IsLocalFrameOn.eventually_eq_sum_coeff_smul hs`: for a local frame `{sᵢ}` near `x`,
  for each section `t` we have `t = ∑ i, (hs.coeff i t) • sᵢ`.
* `IsLocalFrameOn.coeff_sum_eq hs t hx` proves that `t x = ∑ i, (hs.coeff i t) x • sᵢ x`, provided
  that `hx : x ∈ U`.
* `IsLocalFrameOn.coeff_congr hs`: the coefficient `hs.coeff i` of `t` in the local frame `{sᵢ}`
  only depends on `t` at `x`.
* `IsLocalFrameOn.eq_iff_coeff hs`: two sections `t` and `t'` are equal at `x` if and only if their
  coefficients at `x` w.r.t. `{sᵢ}` agree.
* `IsLocalFrameOn.contMDiffOn_of_coeff hs`: a section `t` is `C^k` on `U` if each coefficient
  `hs.coeff i t` is `C^k` on `U`
* `IsLocalFrameOn.contMDiffAt_of_coeff hs`: a section `t` is `C^k` at `x ∈ U`
  if all of its frame coefficients are
* `IsLocalFrameOn.contMDiffOn_off_coeff hs`: a section `t` is `C^k` on an open set `t ⊆ U`
  ff all of its frame coefficients are
* `MDifferentiable` versions of the previous three statements

Given a basis of the standard fibre `F` of `V`, a compatible trivialisation of `V` near `x`
induces a local frame for `V` on `e.baseSet`:
* `Basis.localFrame e b`: the local frame on `V` w.r.t. a local trivialisation `e` of `V` and a
  basis `b` of `F`. Use `b.localFrame e i` to access the i-th section in that frame.
* `b.contMDiffOn_localFrame_baseSet`: each section `b.localFrame e i` is smooth on `e.baseSet`
* `b.localFrame_toBasis_at e`: for each `x ∈ e.baseSet`, the vectors `b.localFrame e i x` form
  a basis of `F`
* `Basis.localFrame_coeff e b i` describes the coefficient of sections of `V` w.r.t.
  `b.localFrame e`: `b.localFrame e i` is a linear map from sections of `V` to functions `M → 𝕜`.
* `b.localFrame_eventually_eq_sum_coeff_smul e`: near `x`, we have
  `s = ∑ i, (b.localFrame_coeff e i s) • b.localFrame e i`
* `b.localFrame_coeff_congr e`: the coefficient `b.localFrame_coeff e b i` of `s` in the local frame
  induced by `e` and `b` at `x` only depends on `s` at `x`.
* `b.contMDiffOn_localFrame_coeff`: if `s` is a `C^k` section, each coefficient
  `b.localFrame_coeff e i s` is `C^k` on `e.baseSet`
* `b.contMDiffAt_iff_localFrame_coeff e`: a section `s` is `C^k` at `x ∈ e.baseSet`
  iff all of its frame coefficients are
* `b.contMDiffOn_iff_localFrame_coeff e`: a section `s` is `C^k` on an open set `t ⊆ e.baseSet`
  iff all of its frame coefficients are

A local frame can be used to extend any single vector `v : V x` to a section which is smooth near
`x`, such that the construction is linear in `v`.
* `localExtensionOn b e v`: given a basis `b` and a compatible trivialisation `e` of `V` near `x`,
  extend the vector `v : V x` to a section of `V` which is smooth on `e.baseSet`
* `localExtensionOn_apply_self`: `localExtensionOn b e v x = v`, i.e. we really extend `v` at `x`
* `contMDiffOn_localExtensionOn`: `localExtensionOn b e v` is `C^n` on `e.baseSet`
* `localExtensionOn_localFrame_coeff`: `localExtensionOn` has constant frame coefficients
  (knowing this is sometimes useful when working with local extensions for covariant derivatives)
* `localExtensionOn_add`, `localExtensionOn_zero` and `localExtensionOn_smul` prove that
  `v ↦ localExtensionON b e v` is a linear map.


# TODO
* `IsLocalFrameOn.contMDiffOn_coeff hs`: if `t` is a `C^k` section, each coefficient
  `hs.coeff i t` is `C^k` on `U`
* `IsLocalFrameOn.contMDiffAt_iff_coeff hs`: a section `t` is `C^k` at `x ∈ U`
  iff all of its frame coefficients are
* `IsLocalFrameOn.contMDiffOn_iff_coeff hs`: a section `t` is `C^k` on an open set `t ⊆ U`
  iff all of its frame coefficients are
* a `MDifferentiable` version of each of these

## Implementation notes

Local frames use the junk value pattern: they are defined on all of `M`, but their value is
only meaningful on the set on which they are a local frame.

Note that `localExtensionOn` need not be smooth globally; in turn, this definition makes sense over
any field. In contrast, an extension to a global holomorphic vector field is more delicate for
complex vector bundles (whereas *locally* holomorphic sections always exist).
For real bundles, global extensions always exist and can be constructed by scalar multiplication
of a local extension with a smooth bump function of sufficiently small support.


## Tags
vector bundle, local frame, smoothness, local extension of section

-/
open Bundle Filter Function Topology Module

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
  [FiberBundle F V] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle n F V I]
  -- `V` vector bundle

noncomputable section

section IsLocalFrame

omit [IsManifold I 0 M] [VectorBundle 𝕜 F V]

variable {ι : Type*} {s s' : ι → (x : M) → V x} {u u' : Set M} {x : M} {n : WithTop ℕ∞}

variable (I F n) in
/--
A family of sections `s i` of `V → M` is called a **C^k local frame** on a set `U ⊆ M` iff
- the section values `s i x` form a basis for each `x ∈ U`,
- each section `s i` is `C^k` on `U`.
-/
structure IsLocalFrameOn (s : ι → (x : M) → V x) (u : Set M) where
  linearIndependent {x : M} (hx : x ∈ u) : LinearIndependent 𝕜 (s · x)
  generating {x : M} (hx : x ∈ u) : ⊤ ≤ Submodule.span 𝕜 (Set.range (s · x))
  contMDiffOn (i : ι) : CMDiff[u] n (T% (s i))

namespace IsLocalFrameOn

/-- If `s = s'` on `u` and `s i` is a local frame on `u`, then so is `s'`. -/
lemma congr (hs : IsLocalFrameOn I F n s u) (hs' : ∀ i, ∀ x, x ∈ u → s i x = s' i x) :
    IsLocalFrameOn I F n s' u where
  linearIndependent := by
    intro x hx
    have := hs.linearIndependent hx
    simp_all
  generating := by
    intro x hx
    have := hs.generating hx
    simp_all
  contMDiffOn i := (hs.contMDiffOn i).congr (by simp +contextual [hs'])

lemma mono (hs : IsLocalFrameOn I F n s u) (hu'u : u' ⊆ u) : IsLocalFrameOn I F n s u' where
  linearIndependent := by
    intro x hx
    exact hs.linearIndependent (hu'u hx)
  generating := by
    intro x hx
    exact hs.generating (hu'u hx)
  contMDiffOn i := (hs.contMDiffOn i).mono hu'u

lemma contMDiffAt (hs : IsLocalFrameOn I F n s u) (hu : IsOpen u) (hx : x ∈ u) (i : ι) :
    CMDiffAt n (T% (s i)) x :=
  (hs.contMDiffOn i).contMDiffAt <| hu.mem_nhds hx

/-- Given a local frame `{s i}` on `U ∋ x`, returns the basis `{s i}` of `V x` -/
def toBasisAt (hs : IsLocalFrameOn I F n s u) (hx : x ∈ u) : Basis ι 𝕜 (V x) :=
  Basis.mk (hs.linearIndependent hx) (hs.generating hx)

@[simp]
lemma toBasisAt_coe (hs : IsLocalFrameOn I F n s u) (hx : x ∈ u) (i : ι) :
    toBasisAt hs hx i = s i x := by
  simpa only [toBasisAt] using Basis.mk_apply (hs.linearIndependent hx) (hs.generating hx) i

open scoped Classical in
/-- Coefficients of a section `s` of `V` w.r.t. a local frame `{s i}` on `u`.
Outside of `u`, this returns the junk value 0. -/
def coeff (hs : IsLocalFrameOn I F n s u) (i : ι) : (Π x : M, V x) →ₗ[𝕜] M → 𝕜 where
  toFun s x := if hx : x ∈ u then (hs.toBasisAt hx).repr (s x) i else 0
  map_add' s s' := by
    ext x
    by_cases hx : x ∈ u <;> simp [hx]
  map_smul' c s := by
    ext x
    by_cases hx : x ∈ u <;> simp [hx]

variable {x : M}

@[simp]
lemma coeff_apply_of_notMem (hs : IsLocalFrameOn I F n s u) (hx : x ∉ u) (t : Π x : M, V x)
    (i : ι) : hs.coeff i t x = 0 := by
  simp [coeff, hx]

@[simp]
lemma coeff_apply_of_mem (hs : IsLocalFrameOn I F n s u) (hx : x ∈ u) (t : Π x : M, V x) (i : ι) :
    hs.coeff i t x = (hs.toBasisAt hx).repr (t x) i := by
  simp [coeff, hx]

-- TODO: add uniqueness of the decomposition; follows from the IsBasis property in the definition

lemma coeff_sum_eq [Fintype ι] (hs : IsLocalFrameOn I F n s u) (t : Π x : M,  V x) (hx : x ∈ u) :
    t x = ∑ i, (hs.coeff i t x) • (s i x) := by
  simpa [coeff, hx] using (Basis.sum_repr (hs.toBasisAt hx) (t x)).symm

/-- A local frame locally spans the space of sections for `V`: for each local frame `s i` on an open
set `u` around `x`, we have `t = ∑ i, (hs.coeff i t) • (s i x)` near `x`. -/
lemma eventually_eq_sum_coeff_smul [Fintype ι]
    (hs : IsLocalFrameOn I F n s u) (t : Π x : M,  V x) (hu'' : u ∈ 𝓝 x) :
    ∀ᶠ x' in 𝓝 x, t x' = ∑ i, (hs.coeff i t x') • (s i x') :=
  eventually_of_mem hu'' fun _ hx ↦ hs.coeff_sum_eq _ hx

variable {t t' : Π x : M, V x}

/-- The coefficients of `t` in a local frame at `x` only depend on `t` at `x`. -/
lemma coeff_congr (hs : IsLocalFrameOn I F n s u) (htt' : t x = t' x) (i : ι) :
    hs.coeff i t x = hs.coeff i t' x := by
  by_cases hxe : x ∈ u
  · simp [coeff, hxe]
    congr
  · simp [coeff, hxe]

/-- If `s` and `s'` are local frames which are equal at `x`,
a section `t` has equal frame coefficients in them. -/
lemma coeff_eq_of_eq (hs : IsLocalFrameOn I F n s u) (hs' : IsLocalFrameOn I F n s' u)
    (hss' : ∀ i, s i x = s' i x) {t : Π x : M,  V x} (i : ι) :
    hs.coeff i t x = hs'.coeff i t x := by
  by_cases hxe : x ∈ u
  · simp [coeff, hxe]
    simp_all [toBasisAt]
  · simp [coeff, hxe]

/-- Two sections `s` and `t` are equal at `x` if and only if their coefficients w.r.t. some local
frame at `x` agree. -/
lemma eq_iff_coeff [Fintype ι] (hs : IsLocalFrameOn I F n s u) (hx : x ∈ u) :
    t x = t' x ↔ ∀ i, hs.coeff i t x = hs.coeff i t' x :=
  ⟨fun h i ↦ hs.coeff_congr h i, fun h ↦ by
    simp +contextual [h, hs.coeff_sum_eq t hx, hs.coeff_sum_eq t' hx]⟩

lemma coeff_apply_zero_at (hs : IsLocalFrameOn I F n s u) (ht : t x = 0) (i : ι) :
    hs.coeff i t x = 0 := by
  simp [hs.coeff_congr (t' := 0) ht]

variable (hs : IsLocalFrameOn I F n s u) [VectorBundle 𝕜 F V]

/-- Given a local frame `s i ` on `u`, if a section `t` has `C^k` coefficients on `u` w.r.t. `s i`,
then `t` is `C^n` on `u`. -/
lemma contMDiffOn_of_coeff [Fintype ι] (h : ∀ i, CMDiff[u] n (hs.coeff i t)) :
    CMDiff[u] n (T% t) := by
  have this (i) : CMDiff[u] n (T% (hs.coeff i t • s i)) :=
    (h i).smul_section (hs.contMDiffOn i)
  have almost : CMDiff[u] n (T% (fun x ↦ ∑ i, (hs.coeff i t) x • s i x)) :=
    .sum_section fun i _ ↦ this i
  apply almost.congr
  intro y hy
  simp [hs.coeff_sum_eq t hy]

/-- Given a local frame `s i` on a neighbourhood `u` of `x`,
if a section `t` has `C^k` coefficients at `x` w.r.t. `s i`, then `t` is `C^n` at `x`. -/
lemma contMDiffAt_of_coeff [Fintype ι]
    (h : ∀ i, CMDiffAt n (hs.coeff i t) x) (hu : u ∈ 𝓝 x) : CMDiffAt n (T% t) x := by
  have almost : CMDiffAt n (T% (fun x ↦ ∑ i, (hs.coeff i t) x • s i x)) x :=
    .sum_section (fun i _ ↦ (h i).smul_section <| (hs.contMDiffOn i).contMDiffAt hu)
  exact almost.congr_of_eventuallyEq <| (hs.eventually_eq_sum_coeff_smul t hu).mono (by simp)

/-- Given a local frame `s i` on an open set `u` containing `x`, if a section `t` has `C^k`
coefficients at `x ∈ u` w.r.t. `s i`, then `t` is `C^n` at `x`. -/
lemma contMDiffAt_of_coeff_aux [Fintype ι] (h : ∀ i, CMDiffAt n (hs.coeff i t) x)
    (hu : IsOpen u) (hx : x ∈ u) : CMDiffAt n (T% t) x :=
  hs.contMDiffAt_of_coeff h (hu.mem_nhds hx)

section

variable (hs : IsLocalFrameOn I F 1 s u)

/-- Given a local frame `s i ` on `u`, if a section `t` has differentiable coefficients on `u`
w.r.t. `s i`, then `t` is differentiable on `u`. -/
lemma mdifferentiableOn_of_coeff [Fintype ι] (h : ∀ i, MDiff[u] (hs.coeff i t)) :
    MDiff[u] (T% t) := by
  have this (i) : MDiff[u] (T% (hs.coeff i t • s i)) :=
    (h i).smul_section ((hs.contMDiffOn i).mdifferentiableOn le_rfl)
  have almost : MDiff[u] (T% (fun x ↦ ∑ i, (hs.coeff i t) x • s i x)) :=
    .sum_section (fun i _ hx ↦ this i _ hx)
  apply almost.congr
  intro y hy
  simp [hs.coeff_sum_eq t hy]

/-- Given a local frame `s i` on a neighbourhood `u` of `x`, if a section `t` has differentiable
coefficients at `x` w.r.t. `s i`, then `t` is differentiable at `x`. -/
lemma mdifferentiableAt_of_coeff [Fintype ι]
    (h : ∀ i, MDiffAt (hs.coeff i t) x) (hu : u ∈ 𝓝 x) : MDiffAt (T% t) x := by
  have almost : MDiffAt (T% (fun x ↦ ∑ i, (hs.coeff i t) x • s i x)) x :=
    .sum_section (fun i ↦ (h i).smul_section <|
      ((hs.contMDiffOn i).mdifferentiableOn le_rfl).mdifferentiableAt hu)
  exact almost.congr_of_eventuallyEq <| (hs.eventually_eq_sum_coeff_smul t hu).mono (by simp)

/-- Given a local frame `s i` on open set `u` containing `x`, if a section `t`
has differentiable coefficients at `x ∈ u` w.r.t. `s i`, then `t` is differentiable at `x`. -/
lemma mdifferentiableAt_of_coeff_aux [Fintype ι] (h : ∀ i, MDiffAt (hs.coeff i t) x)
    (hu : IsOpen u) (hx : x ∈ u) : MDiffAt (T% t) x :=
  hs.mdifferentiableAt_of_coeff h (hu.mem_nhds hx)

end

end IsLocalFrameOn

end IsLocalFrame

namespace Module.Basis

variable {ι : Type*} {x : M}

noncomputable def localFrame_toBasis_at
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e]
    (b : Basis ι 𝕜 F) (hx : x ∈ e.baseSet) : Basis ι 𝕜 (V x) :=
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
    CMDiff[e.baseSet] n (T% (b.localFrame e i)) := by
  rw [e.contMDiffOn_section_baseSet_iff]
  apply (contMDiffOn_const (c := b i)).congr
  intro y hy
  simp [localFrame, hy, localFrame_toBasis_at]

omit [IsManifold I 0 M] in
variable (I) in
/-- `b.localFrame e i` is indeed a local frame on `e.baseSet` -/
lemma localFrame_isLocalFrameOn_baseSet
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] (b : Basis ι 𝕜 F) : IsLocalFrameOn I F n (b.localFrame e) e.baseSet
    where
  contMDiffOn i := b.contMDiffOn_localFrame_baseSet _ e i
  linearIndependent := by
    intro x hx
    convert (b.localFrame_toBasis_at e hx).linearIndependent
    simp [localFrame, hx, localFrame_toBasis_at]
  generating := by
    intro x hx
    convert (b.localFrame_toBasis_at e hx).span_eq.ge
    simp [localFrame, hx, localFrame_toBasis_at]

omit [IsManifold I 0 M] in
lemma _root_.contMDiffAt_localFrame_of_mem
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] (b : Basis ι 𝕜 F) (i : ι) (hx : x ∈ e.baseSet) :
    CMDiffAt n (T% (b.localFrame e i)) x :=
  (b.localFrame_isLocalFrameOn_baseSet I n e).contMDiffAt e.open_baseSet hx _

@[simp]
lemma localFrame_apply_of_mem_baseSet
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] (b : Basis ι 𝕜 F) {i : ι} (hx : x ∈ e.baseSet) :
    b.localFrame e i x = b.localFrame_toBasis_at e hx i := by
  simp [localFrame, hx]

@[simp]
lemma localFrame_apply_of_notMem
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] (b : Basis ι 𝕜 F) {i : ι} (hx : x ∉ e.baseSet) :
    b.localFrame e i x = 0 := by
  simp [localFrame, hx]

lemma localFrame_toBasis_at_coe
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] (b : Basis ι 𝕜 F) (i : ι) (hx : x ∈ e.baseSet) :
    b.localFrame_toBasis_at e hx i = b.localFrame e i x := by simp [hx]

variable [ContMDiffVectorBundle 1 F V I]

open scoped Classical in
variable (I) in
/-- Coefficients of a section `s` of `V` w.r.t. the local frame `b.localFrame e i`.

If x is outside of `e.baseSet`, this returns the junk value 0. -/
noncomputable def localFrame_coeff
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e]
    (b : Basis ι 𝕜 F) (i : ι) : (Π x : M, V x) →ₗ[𝕜] M → 𝕜 :=
  (b.localFrame_isLocalFrameOn_baseSet I 1 e).coeff i

variable {e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
  [MemTrivializationAtlas e] {b : Basis ι 𝕜 F} {x : M}

omit [IsManifold I 0 M] in
variable (e b) in
@[simp]
lemma localFrame_coeff_apply_of_notMem_baseSet (hx : x ∉ e.baseSet) (s : Π x : M, V x) (i : ι) :
    b.localFrame_coeff I e i s x = 0 := by
  simpa [localFrame_coeff] using
    (localFrame_isLocalFrameOn_baseSet I 1 e b).coeff_apply_of_notMem hx s i

omit [IsManifold I 0 M] in
variable (e b) in
@[simp]
lemma localFrame_coeff_apply_of_mem_baseSet (hx : x ∈ e.baseSet) (s : Π x : M, V x) (i : ι) :
    b.localFrame_coeff I e i s x = (b.localFrame_toBasis_at e hx).repr (s x) i := by
  have ilf := b.localFrame_isLocalFrameOn_baseSet I 1 e
  rw [show localFrame_toBasis_at e b hx = ilf.toBasisAt hx by ext j; simp [localFrame, hx]]
  exact ilf.coeff_apply_of_mem hx s i -- XXX better variable name!

-- TODO: better name?
omit [IsManifold I 0 M] in
lemma localFrame_coeff_sum_eq [Fintype ι] (s : Π x : M,  V x) {x'} (hx : x' ∈ e.baseSet) :
    s x' = (∑ i, (b.localFrame_coeff I e i s x') • b.localFrame e i x') := by
  simp only [localFrame_coeff]
  exact (localFrame_isLocalFrameOn_baseSet I 1 e b).coeff_sum_eq s hx

variable (b) in
omit [IsManifold I 0 M] in
/-- A local frame locally spans the space of sections for `V`: for each local trivialisation `e`
  of `V` around `x`, we have `s = ∑ i, (b.localFrame_coeff e i s) • b.localFrame e i` -/
lemma localFrame_eventually_eq_sum_coeff_smul [Fintype ι]
    (hxe : x ∈ e.baseSet) (s : Π x : M,  V x) :
    ∀ᶠ x' in 𝓝 x, s x' = ∑ i, (b.localFrame_coeff I e i s x') • b.localFrame e i x' :=
  eventually_nhds_iff.mpr ⟨e.baseSet, fun _ h ↦ localFrame_coeff_sum_eq s h, e.open_baseSet, hxe⟩

omit [IsManifold I 0 M] in
/-- The representation of `s` in a local frame at `x` only depends on `s` at `x`. -/
lemma localFrame_coeff_congr (b : Basis ι 𝕜 F)
    {s s' : Π x : M,  V x} {i : ι} (hss' : s x = s' x) :
    b.localFrame_coeff I e i s x = b.localFrame_coeff I e i s' x := by
  by_cases hxe : x ∈ e.baseSet
  · simp [localFrame_coeff, hxe]
    congr
  · simp [localFrame_coeff, hxe]

omit [IsManifold I 0 M] in
lemma localFrame_coeff_apply_zero_at
    (b : Basis ι 𝕜 F) {s : Π x : M, V x} (hs : s x = 0) (i : ι) :
    b.localFrame_coeff I e i s x = 0 := by
  simp only [localFrame_coeff]
  exact (localFrame_isLocalFrameOn_baseSet I 1 e b).coeff_apply_zero_at hs i

variable {n}

omit [IsManifold I 0 M] in
/-- Suppose `e` is a compatible trivialisation around `x ∈ M`, and `s` a bundle section.
Then the coefficient of `s` w.r.t. the local frame induced by `b` and `e`
equals the cofficient of "`s x` read in the trivialisation `e`" for `b i`. -/
lemma localFrame_coeff_eq_coeff (hxe : x ∈ e.baseSet) (b : Basis ι 𝕜 F) {i : ι} {s : Π x : M, V x} :
    b.localFrame_coeff I e i s x = b.repr (e (s x)).2 i := by
  --simp only [localFrame_coeff]
  simp [b.localFrame_coeff_apply_of_mem_baseSet e hxe, Basis.localFrame_toBasis_at]

end Module.Basis

/-! # Determining smoothness of a section via its local frame coefficients
We show that for finite rank bundles over a complete field, a section is smooth iff its coefficients
in a local frame induced by a local trivialisation are. In many contexts, this statement holds for
*any* local frame (e.g., for all real bundles which admit a continuous bundle metric, as is
proven in `OrthonormalFrame.lean`).
-/

variable {ι : Type*} {e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [MemTrivializationAtlas e] {b : Basis ι 𝕜 F} {x : M}
    [ContMDiffVectorBundle 1 F V I]

-- TODO: can this be proven more generally, for any local frame?
omit [IsManifold I 0 M] in
/-- If `s` is `C^k` at `x`, so is its coefficient `b.localFrame_coeff e i` in the local frame
near `x` induced by `e` and `b` -/
lemma contMDiffAt_localFrame_coeff [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    (hxe : x ∈ e.baseSet) (b : Basis ι 𝕜 F)
    {s : Π x : M,  V x} {k : WithTop ℕ∞} [ContMDiffVectorBundle k F V I]
    (hs : CMDiffAt k (T% s) x) (i : ι) :
    CMDiffAt k (b.localFrame_coeff I e i s) x := by
  -- This boils down to computing the frame coefficients in a local trivialisation.
  classical
  -- step 1: on e.baseSet, can compute the coefficient very well
  let aux := fun x ↦ b.repr (e (s x)).2 i
  -- Since e.baseSet is open, this is sufficient.
  suffices CMDiffAt k aux x by
    apply this.congr_of_eventuallyEq ?_
    apply eventuallyEq_of_mem (s := e.baseSet) (by simp [e.open_baseSet.mem_nhds hxe])
    intro y hy
    simp [aux, Basis.localFrame_coeff_eq_coeff hy]
  simp only [aux]

  -- step 2: `s` read in trivialization `e` is `C^k`
  have h₁ : CMDiffAt k (fun x ↦ (e (s x)).2) x := e.contMDiffAt_section_iff hxe |>.1 hs
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
/-- If `s` is `C^k` on `t ⊆ e.baseSet`, so is its coefficient `b.localFrame_coeff e i`
in the local frame induced by `e` -/
lemma contMDiffOn_localFrame_coeff [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] (b : Basis ι 𝕜 F)
    {s : Π x : M,  V x} {k : WithTop ℕ∞} {t : Set M} [ContMDiffVectorBundle k F V I]
    (ht : IsOpen t) (ht' : t ⊆ e.baseSet)
    (hs : CMDiff[t] k (T% s)) (i : ι) : CMDiff[t] k (b.localFrame_coeff I e i s) :=
  fun _ hx ↦ (contMDiffAt_localFrame_coeff (ht' hx) b
    (hs.contMDiffAt (ht.mem_nhds hx)) i).contMDiffWithinAt

omit [IsManifold I 0 M] in
/-- If `s` is `C^k` on `e.baseSet`, so is its coefficient `b.localFrame_coeff e i`
in the local frame induced by `e` -/
lemma contMDiffOn_baseSet_localFrame_coeff [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    (b : Basis ι 𝕜 F) {s : Π x : M,  V x} {k : WithTop ℕ∞} [ContMDiffVectorBundle k F V I]
    (hs : CMDiff[e.baseSet] k (T% s)) (i : ι) : CMDiff[e.baseSet] k (b.localFrame_coeff I e i s) :=
  contMDiffOn_localFrame_coeff b e.open_baseSet (subset_refl _) hs _

omit [IsManifold I 0 M] in
/-- A section `s` of `V` is `C^k` at `x ∈ e.baseSet` iff each of its
coefficients `b.localFrame_coeff e i s` in a local frame near `x` is -/
lemma contMDiffAt_iff_localFrame_coeff [Fintype ι] [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    (b : Basis ι 𝕜 F) {s : Π x : M,  V x} {k : WithTop ℕ∞} [ContMDiffVectorBundle k F V I]
    {x' : M} (hx : x' ∈ e.baseSet) :
    CMDiffAt k (T% s) x' ↔ ∀ i, CMDiffAt k (b.localFrame_coeff I e i s) x' :=
  ⟨fun h i ↦ contMDiffAt_localFrame_coeff hx b h i,
    fun hi ↦ (b.localFrame_isLocalFrameOn_baseSet I k e).contMDiffAt_of_coeff hi
    (e.open_baseSet.mem_nhds hx)⟩

omit [IsManifold I 0 M] in
/-- A section `s` of `V` is `C^k` on `t ⊆ e.baseSet` iff each of its
coefficients `b.localFrame_coeff e i s` in a local frame near `x` is -/
lemma contMDiffOn_iff_localFrame_coeff [Fintype ι] [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    (b : Basis ι 𝕜 F) {s : Π x : M,  V x} {k : WithTop ℕ∞} [ContMDiffVectorBundle k F V I]
    {t : Set M} (ht : IsOpen t) (ht' : t ⊆ e.baseSet) :
    CMDiff[t] k (T% s) ↔ ∀ i, CMDiff[t] k (b.localFrame_coeff I e i s) := by
  refine ⟨fun h i ↦ contMDiffOn_localFrame_coeff b ht ht' h i, fun hi ↦ ?_⟩
  -- TODO: golf this using the lemmas above
  -- intro x hx
  -- let aux := (b.localFrame_isLocalFrameOn_baseSet I k e).contMDiffAt_of_coeff (t := s) (x := x)
  have this (i) : CMDiff[t] k (T% ((b.localFrame_coeff I e i) s • b.localFrame e i)) :=
    (hi i).smul_section ((b.contMDiffOn_localFrame_baseSet k e i).mono ht')
  let rhs := fun x' ↦ ∑ i, (b.localFrame_coeff I e i) s x' • b.localFrame e i x'
  have almost : CMDiff[t] k (T% rhs) := .sum_section fun i _ ↦ this i
  apply almost.congr
  intro y hy
  simpa using b.localFrame_coeff_sum_eq s (ht' hy)

omit [IsManifold I 0 M] in
/-- A section `s` of `V` is `C^k` on a trivialisation domain `e.baseSet` iff each of its
coefficients `b.localFrame_coeff e i s` in a local frame near `x` is -/
lemma contMDiffOn_baseSet_iff_localFrame_coeff [Fintype ι] [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    (b : Basis ι 𝕜 F) {s : Π x : M,  V x} {k : WithTop ℕ∞} [ContMDiffVectorBundle k F V I] :
    CMDiff[e.baseSet] k (T% s) ↔ ∀ i, CMDiff[e.baseSet] k (b.localFrame_coeff I e i s) := by
  rw [contMDiffOn_iff_localFrame_coeff b e.open_baseSet (subset_refl _)]

-- Differentiability of a section can be checked in terms of its local frame coefficients
section MDifferentiable

omit [IsManifold I 0 M] in
/-- If `s` is diffentiable at `x`, so is its coefficient `b.localFrame_coeff e i` in the local frame
near `x` induced by `e` and `b` -/
lemma mdifferentiableAt_localFrame_coeff [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    (hxe : x ∈ e.baseSet) (b : Basis ι 𝕜 F) {s : Π x : M,  V x} (hs : MDiffAt (T% s) x) (i : ι) :
    MDiffAt (b.localFrame_coeff I e i s) x := by
  -- This boils down to computing the frame coefficients in a local trivialisation.
  classical
  -- step 1: on e.baseSet, can compute the coefficient very well
  let aux := fun x ↦ b.repr (e (s x)).2 i
  -- Since e.baseSet is open, this is sufficient.
  suffices MDiffAt aux x by
    apply this.congr_of_eventuallyEq
    apply eventuallyEq_of_mem (s := e.baseSet) (by simp [e.open_baseSet.mem_nhds hxe])
    intro y hy
    simp [aux, Basis.localFrame_coeff_eq_coeff hy]
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
/-- If `s` is differentiable on `t ⊆ e.baseSet`, so is its coefficient `b.localFrame_coeff e i`
in the local frame induced by `e` -/
lemma mdifferentiableOn_localFrame_coeff [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] (b : Basis ι 𝕜 F)
    {s : Π x : M,  V x} {t : Set M}
    (ht : IsOpen t) (ht' : t ⊆ e.baseSet) (hs : MDiff[t] (T% s)) (i : ι) :
    MDiff[t] (b.localFrame_coeff I e i s) :=
  fun _ hx ↦ (mdifferentiableAt_localFrame_coeff (ht' hx) b
    (hs.mdifferentiableAt (ht.mem_nhds hx)) i).mdifferentiableWithinAt

omit [IsManifold I 0 M] in
/-- If `s` is differentiable on `e.baseSet`, so is its coefficient `b.localFrame_coeff e i` in the
local frame induced by `e` -/
lemma mdifferentiableOn_baseSet_localFrame_coeff [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    (b : Basis ι 𝕜 F) {s : Π x : M,  V x}
    (hs : MDiff[e.baseSet] (T% s)) (i : ι) :
    MDiff[e.baseSet] (b.localFrame_coeff I e i s) :=
  mdifferentiableOn_localFrame_coeff b e.open_baseSet (subset_refl _) hs _

omit [IsManifold I 0 M] in
/-- A section `s` of `V` is differentiable at `x ∈ e.baseSet` iff each of its
coefficients `b.localFrame_coeff e i s` in a local frame near `x` is -/
lemma mdifferentiableAt_iff_localFrame_coeff [Fintype ι] [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    (b : Basis ι 𝕜 F) {s : Π x : M,  V x} {x' : M} (hx : x' ∈ e.baseSet) :
    MDiffAt (T% s) x' ↔ ∀ i, MDiffAt (b.localFrame_coeff I e i s) x' :=
  ⟨fun h i ↦ mdifferentiableAt_localFrame_coeff hx b h i, fun hi ↦
    (b.localFrame_isLocalFrameOn_baseSet I 1 e).mdifferentiableAt_of_coeff_aux hi e.open_baseSet hx⟩

end MDifferentiable

end

-- local extension of a vector field in a trivialisation's base set
section localExtensionOn

variable {ι : Type*} [Fintype ι] {b : Basis ι 𝕜 F}
  {e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
  [MemTrivializationAtlas e] {x x' : M}

open scoped Classical in

/- Extend a vector `v ∈ V x` to a section `s` of the bundle `V` which is smooth near `x`,
such that `s x = v` and this construction is linear in `v`.

The details of this extension are unspecified (and could be subject to change).
Currently, we construct this extension using a local frame induced by a choose of basis of the
fibre `F` and a compatible trivialisation `e` of `V` around `x`.
(Allowing any local frame near `x` would be easy to implement.)
Our construction has constant coefficients on `e.baseSet` w.r.t. this local frame, and is zero
otherwise. In particular, it is smooth on `e.baseSet`, and (globally) linear in `v`.

We choose an extension with these particularly nice properties because this simplifies later
constructions on covariant derivatives (and in this context, the value at `s` at points other than
`x` does not matter, but constant frame coefficients are useful).
-/
-- XXX: we could generalise this definition to any local frame on `U ∋ x`, with smoothness on `U`.
-- Would this be useful? Should do this?
noncomputable def localExtensionOn (b : Basis ι 𝕜 F)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
    {x : M} (v : V x) : (x' : M) → V x' :=
  fun x' ↦ if hx : x ∈ e.baseSet then
    ∑ i, (b.localFrame_toBasis_at e hx).repr v i • b.localFrame e i x'
  else 0

variable (b e) in
@[simp]
lemma localExtensionOn_apply_self (hx : x ∈ e.baseSet) (v : V x) :
    (localExtensionOn b e v) x = v := by
  simp [localExtensionOn, hx]

omit [IsManifold I 0 M] in
variable (b) in
/-- A local extension has constant frame coefficients within its defining trivialisation. -/
lemma localExtensionOn_localFrame_coeff [ContMDiffVectorBundle 1 F V I]
    (hx : x ∈ e.baseSet) (hx' : x' ∈ e.baseSet) (v : V x) (i : ι) :
    b.localFrame_coeff I e i (localExtensionOn b e v) x' =
      b.localFrame_coeff I e i (localExtensionOn b e v) x := by
  simp [localExtensionOn, hx, hx']

-- By construction, localExtensionOn is a linear map.

variable (b e) in
lemma localExtensionOn_add (v v' : V x) :
    localExtensionOn b e (v + v') = localExtensionOn b e v + localExtensionOn b e v' := by
  ext x'
  by_cases hx: x ∈ e.baseSet; swap
  · simp [hx, localExtensionOn]
  · simp [hx, localExtensionOn, add_smul, Finset.sum_add_distrib]

variable (b e) in
lemma localExtensionOn_zero : localExtensionOn b e (x := x) 0 = 0 := by
  ext x'
  by_cases hx: x ∈ e.baseSet <;> simp [hx, localExtensionOn]

variable (b e) in
lemma localExtensionOn_smul (a : 𝕜) (v : V x) :
    localExtensionOn b e (a • v) = a • localExtensionOn b e v := by
  ext x'
  by_cases hx: x ∈ e.baseSet; swap
  · simp [hx, localExtensionOn]
  · simp only [localExtensionOn, hx, ↓reduceDIte, map_smul, Finsupp.coe_smul, Pi.smul_apply,
      smul_eq_mul, Finset.smul_sum]
    congr with i
    rw [mul_smul a (((b.localFrame_toBasis_at e hx).repr v) i)]

variable (F) in
omit [IsManifold I 0 M] in
lemma contMDiffOn_localExtensionOn [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    {x : M} (hx : x ∈ e.baseSet) (v : V x) [ContMDiffVectorBundle ∞ F V I] :
    CMDiff[e.baseSet] ∞ (T% (localExtensionOn b e v)) := by
  -- The local frame coefficients of `localExtensionOn` w.r.t. the frame induced by `e` are
  -- constant, hence smoothness follows.
  rw [contMDiffOn_baseSet_iff_localFrame_coeff b]
  intro i
  apply (contMDiffOn_const (c := (b.localFrame_coeff I e i) (localExtensionOn b e v) x)).congr
  intro y hy
  rw [localExtensionOn_localFrame_coeff b hx hy v i]

end localExtensionOn
