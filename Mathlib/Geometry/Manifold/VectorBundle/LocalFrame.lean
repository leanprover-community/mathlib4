/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

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
complete field). In `Mathlib/Geometry/Manifold/VectorBundle/OrthonormalFrame.lean` (#26221),
we will prove the same for real vector bundles of any rank which admit a `C^n` bundle metric.
This includes bundles of finite rank, modelled on a Hilbert space or on a Banach space which has
smooth partitions of unity.

We will use this to construct local extensions of a vector to a section which is smooth on the
trivialisation domain.

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

In the following lemmas, let `e` be a compatible local trivialisation of `V`, and `b` a basis of
the model fiber `F`.
* `Trivialization.basisAt e b`: for each `x ∈ e.baseSet`,
  return the basis of `V x` induced by `e` and `b`
* `e.localFrame b`: the local frame on `V` induced by `e` and `b`.
  Use `e.localFrame b i` to access the i-th section in that frame.
* `e.contMDiffOn_localFrame_baseSet`: each section `e.localFrame b i` is smooth on `e.baseSet`

## TODO

Strengthen the proof of smoothness in terms of the local frame coefficients.
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

## Tags
vector bundle, local frame, smoothness

-/

@[expose] public section
open Bundle Filter Function Topology Module

open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [FiberBundle F V]

noncomputable section

section IsLocalFrame

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

/-- If `{sᵢ}` is a local frame on a vector bundle, `F` being finite-dimensional implies the
indexing set being finite. -/
def fintype_of_finiteDimensional [VectorBundle 𝕜 F V] [FiniteDimensional 𝕜 F]
    (hs : IsLocalFrameOn I F n s u) (hx : x ∈ u) : Fintype ι := by
  have : FiniteDimensional 𝕜 (V x) := by
    let phi := (trivializationAt F V x).linearEquivAt 𝕜 x
      (FiberBundle.mem_baseSet_trivializationAt' x)
    exact Finite.equiv phi.symm
  exact FiniteDimensional.fintypeBasisIndex (hs.toBasisAt hx)

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

lemma coeff_sum_eq [Fintype ι] (hs : IsLocalFrameOn I F n s u) (t : Π x : M, V x) (hx : x ∈ u) :
    t x = ∑ i, (hs.coeff i t x) • (s i x) := by
  simpa [coeff, hx] using (Basis.sum_repr (hs.toBasisAt hx) (t x)).symm

/-- A local frame locally spans the space of sections for `V`: for each local frame `s i` on an open
set `u` around `x`, we have `t = ∑ i, (hs.coeff i t) • (s i x)` near `x`. -/
lemma eventually_eq_sum_coeff_smul [Fintype ι]
    (hs : IsLocalFrameOn I F n s u) (t : Π x : M, V x) (hu'' : u ∈ 𝓝 x) :
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
    (hss' : ∀ i, s i x = s' i x) {t : Π x : M, V x} (i : ι) :
    hs.coeff i t x = hs'.coeff i t x := by
  by_cases hxe : x ∈ u
  · simp [coeff, hxe]
    simp_all [toBasisAt]
  · simp [coeff, hxe]

/-- Two sections `s` and `t` are equal at `x` if and only if their coefficients w.r.t. some local
frame at `x` agree. -/
lemma eq_iff_coeff [VectorBundle 𝕜 F V] [FiniteDimensional 𝕜 F]
    (hs : IsLocalFrameOn I F n s u) (hx : x ∈ u) :
    t x = t' x ↔ ∀ i, hs.coeff i t x = hs.coeff i t' x := by
  have := fintype_of_finiteDimensional hs hx
  exact ⟨fun h i ↦ hs.coeff_congr h i, fun h ↦ by
    simp +contextual [h, hs.coeff_sum_eq t hx, hs.coeff_sum_eq t' hx]⟩

lemma coeff_apply_zero_at (hs : IsLocalFrameOn I F n s u) (ht : t x = 0) (i : ι) :
    hs.coeff i t x = 0 := by
  simp [hs.coeff_congr (t' := 0) ht]

variable (hs : IsLocalFrameOn I F n s u) [VectorBundle 𝕜 F V]

/-- Given a local frame `s i ` on `u`, if a section `t` has `C^k` coefficients on `u` w.r.t. `s i`,
then `t` is `C^n` on `u`. -/
lemma contMDiffOn_of_coeff [FiniteDimensional 𝕜 F] (h : ∀ i, CMDiff[u] n (hs.coeff i t)) :
    CMDiff[u] n (T% t) := by
  rcases u.eq_empty_or_nonempty with rfl | ⟨x, hx⟩; · simp
  have := fintype_of_finiteDimensional hs hx
  have this (i) : CMDiff[u] n (T% (hs.coeff i t • s i)) :=
    (h i).smul_section (hs.contMDiffOn i)
  have almost : CMDiff[u] n (T% (fun x ↦ ∑ i, (hs.coeff i t) x • s i x)) :=
    .sum_section fun i _ ↦ this i
  apply almost.congr
  intro y hy
  simp [hs.coeff_sum_eq t hy]

/-- Given a local frame `s i` on a neighbourhood `u` of `x`,
if a section `t` has `C^k` coefficients at `x` w.r.t. `s i`, then `t` is `C^n` at `x`. -/
lemma contMDiffAt_of_coeff [FiniteDimensional 𝕜 F]
    (h : ∀ i, CMDiffAt n (hs.coeff i t) x) (hu : u ∈ 𝓝 x) : CMDiffAt n (T% t) x := by
  have := fintype_of_finiteDimensional hs (mem_of_mem_nhds hu)
  have almost : CMDiffAt n (T% (fun x ↦ ∑ i, (hs.coeff i t) x • s i x)) x :=
    .sum_section (fun i _ ↦ (h i).smul_section <| (hs.contMDiffOn i).contMDiffAt hu)
  exact almost.congr_of_eventuallyEq <| (hs.eventually_eq_sum_coeff_smul t hu).mono (by simp)

/-- Given a local frame `s i` on an open set `u` containing `x`, if a section `t` has `C^k`
coefficients at `x ∈ u` w.r.t. `s i`, then `t` is `C^n` at `x`. -/
lemma contMDiffAt_of_coeff_aux [FiniteDimensional 𝕜 F] (h : ∀ i, CMDiffAt n (hs.coeff i t) x)
    (hu : IsOpen u) (hx : x ∈ u) : CMDiffAt n (T% t) x := by
  have := fintype_of_finiteDimensional hs hx
  exact hs.contMDiffAt_of_coeff h (hu.mem_nhds hx)

section

variable (hs : IsLocalFrameOn I F 1 s u)

/-- Given a local frame `s i ` on `u`, if a section `t` has differentiable coefficients on `u`
w.r.t. `s i`, then `t` is differentiable on `u`. -/
lemma mdifferentiableOn_of_coeff [FiniteDimensional 𝕜 F] (h : ∀ i, MDiff[u] (hs.coeff i t)) :
    MDiff[u] (T% t) := by
  rcases u.eq_empty_or_nonempty with rfl | ⟨x, hx⟩; · simp
  have := fintype_of_finiteDimensional hs hx
  have this (i) : MDiff[u] (T% (hs.coeff i t • s i)) :=
    (h i).smul_section ((hs.contMDiffOn i).mdifferentiableOn le_rfl)
  have almost : MDiff[u] (T% (fun x ↦ ∑ i, (hs.coeff i t) x • s i x)) :=
    .sum_section (fun i _ hx ↦ this i _ hx)
  apply almost.congr
  intro y hy
  simp [hs.coeff_sum_eq t hy]

/-- Given a local frame `s i` on a neighbourhood `u` of `x`, if a section `t` has differentiable
coefficients at `x` w.r.t. `s i`, then `t` is differentiable at `x`. -/
lemma mdifferentiableAt_of_coeff [FiniteDimensional 𝕜 F]
    (h : ∀ i, MDiffAt (hs.coeff i t) x) (hu : u ∈ 𝓝 x) : MDiffAt (T% t) x := by
  have := fintype_of_finiteDimensional hs (mem_of_mem_nhds hu)
  have almost : MDiffAt (T% (fun x ↦ ∑ i, (hs.coeff i t) x • s i x)) x :=
    .sum_section (fun i ↦ (h i).smul_section <|
      ((hs.contMDiffOn i).mdifferentiableOn le_rfl).mdifferentiableAt hu)
  exact almost.congr_of_eventuallyEq <| (hs.eventually_eq_sum_coeff_smul t hu).mono (by simp)

/-- Given a local frame `s i` on open set `u` containing `x`, if a section `t`
has differentiable coefficients at `x ∈ u` w.r.t. `s i`, then `t` is differentiable at `x`. -/
lemma mdifferentiableAt_of_coeff_aux [FiniteDimensional 𝕜 F] (h : ∀ i, MDiffAt (hs.coeff i t) x)
    (hu : IsOpen u) (hx : x ∈ u) : MDiffAt (T% t) x :=
  hs.mdifferentiableAt_of_coeff h (hu.mem_nhds hx)

end

end IsLocalFrameOn

end IsLocalFrame

namespace Trivialization

variable [VectorBundle 𝕜 F V] [ContMDiffVectorBundle n F V I] {ι : Type*} {x : M}
  (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
  (b : Basis ι 𝕜 F)

/-- Given a compatible local trivialisation `e` of `V` and a basis `b` of the model fiber `F`,
return the corresponding basis of `V x`. -/
def basisAt (hx : x ∈ e.baseSet) : Basis ι 𝕜 (V x) :=
  b.map (e.linearEquivAt (R := 𝕜) x hx).symm

open scoped Classical in
/-- The local frame on `V` induced by a compatible local trivialization `e` of `V` and a basis
`b` of the model fiber `F`. Use `e.localFrame b i` to access the `i`-th section in that frame.

If `x` is outside of `e.baseSet`, this returns the junk value 0. -/
def localFrame : ι → (x : M) → V x :=
  fun i x ↦ if hx : x ∈ e.baseSet then e.basisAt b hx i else 0

@[simp]
lemma localFrame_apply_of_mem_baseSet {i : ι} (hx : x ∈ e.baseSet) :
    e.localFrame b i x = e.basisAt b hx i := by
  simp [localFrame, hx]

lemma localFrame_apply_of_notMem {i : ι} (hx : x ∉ e.baseSet) : e.localFrame b i x = 0 := by
  simp [localFrame, hx]

/-- Each local frame `{sᵢ} ∈ Γ(E)` of a `C^k` vector bundle, defined by a local trivialisation `e`,
is `C^k` on `e.baseSet`. -/
lemma contMDiffOn_localFrame_baseSet (i : ι) : CMDiff[e.baseSet] n (T% (e.localFrame b i)) := by
  rw [e.contMDiffOn_section_baseSet_iff]
  apply (contMDiffOn_const (c := b i)).congr
  intro y hy
  simp [hy, basisAt]

variable (I) in
/-- `b.localFrame e i` is indeed a local frame on `e.baseSet` -/
lemma isLocalFrameOn_localFrame_baseSet : IsLocalFrameOn I F n (e.localFrame b) e.baseSet where
  contMDiffOn i := e.contMDiffOn_localFrame_baseSet _ b i
  linearIndependent := by
    intro x hx
    convert (e.basisAt b hx).linearIndependent
    simp [hx, basisAt]
  generating := by
    intro x hx
    convert (e.basisAt b hx).span_eq.ge
    simp [hx, basisAt]

lemma _root_.contMDiffAt_localFrame_of_mem (i : ι) (hx : x ∈ e.baseSet) :
    CMDiffAt n (T% (e.localFrame b i)) x :=
  (e.isLocalFrameOn_localFrame_baseSet I n b).contMDiffAt e.open_baseSet hx _

end Trivialization

end
