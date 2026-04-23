/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Init
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Neighborhoods

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
complete field). In the planned file `Mathlib/Geometry/Manifold/VectorBundle/OrthonormalFrame.lean`
(#26221), we will prove the same for real vector bundles of any rank which admit a `C^n` bundle
metric. This includes bundles of finite rank, modelled on a Hilbert space or on a Banach space which
has smooth partitions of unity.

We will use this to construct local extensions of a vector to a section which is smooth on the
trivialisation domain.

## Main definitions and results

* `IsLocalFrameOn`: a family of sections `s i` of `V → M` is called a **C^k local frame** on a set
  `U ⊆ M` iff each section `s i` is `C^k` on `U`, and the section values `s i x` form a basis for
  each `x ∈ U`

Suppose `{sᵢ}` is a local frame on `U`, and `hs : IsLocalFrameOn s U`.
* `IsLocalFrameOn.toBasisAt hs`: for each `x ∈ U`, the vectors `sᵢ x` form a basis of `F`
* `IsLocalFrameOn.coeff hs` describes the coefficient of sections of `V` w.r.t. `{sᵢ}`.
  `hs.coeff i` is a family of fiberwise linear maps `Π x, V x →ₗ[𝕜] 𝕜`.
  The coefficient function of a section `t` is `(LinearMap.piApply (hs.coeff i)) t`.
* `IsLocalFrameOn.eventually_eq_sum_coeff_smul hs`: for a local frame `{sᵢ}` near `x`,
  for each section `t` we have `t = ∑ i, (LinearMap.piApply (hs.coeff i) t) • sᵢ` near `x`.
* `IsLocalFrameOn.coeff_sum_eq hs t hx` proves that
  `t x = ∑ i, hs.coeff i x (t x) • sᵢ x`, provided that `hx : x ∈ U`.
* `IsLocalFrameOn.coeff_congr hs`: the coefficient `hs.coeff i` of `t` in the local frame `{sᵢ}`
  only depends on `t` at `x`.
* `IsLocalFrameOn.eq_iff_coeff hs`: two sections `t` and `t'` are equal at `x` if and only if their
  coefficients at `x` w.r.t. `{sᵢ}` agree.
* `IsLocalFrameOn.contMDiffOn_of_coeff hs`: a section `t` is `C^k` on `U` if each coefficient
  `(LinearMap.piApply (hs.coeff i) t)` is `C^k` on `U`
* `IsLocalFrameOn.contMDiffAt_of_coeff hs`: a section `t` is `C^k` at `x ∈ U`
  if all of its frame coefficients are
* `IsLocalFrameOn.contMDiffOn_off_coeff hs`: a section `t` is `C^k` on an open set `t ⊆ U`
  ff all of its frame coefficients are
* `MDifferentiable` versions of the previous three statements

In the following lemmas, let `e` be a compatible local trivialisation of `V`, and `b` a basis of
the model fiber `F`.
* `Bundle.Trivialization.basisAt e b`: for each `x ∈ e.baseSet`,
  return the basis of `V x` induced by `e` and `b`
* `e.localFrame b`: the local frame on `V` induced by `e` and `b`.
  Use `e.localFrame b i` to access the i-th section in that frame.
* `e.contMDiffOn_localFrame_baseSet`: each section `e.localFrame b i` is smooth on `e.baseSet`
* `e.localFrame_coeff b i` describes the `i`-th coefficient of sections of `V` w.r.t.
  `e.localFrame b`: it is a family of fiberwise linear maps `Π x, V x →ₗ[𝕜] 𝕜`, and the coefficient
  function of a section `s` is `(LinearMap.piApply (e.localFrame_coeff b i)) s`.
* `e.eventually_eq_localFrame_sum_coeff_smul b`: near `x`, we have
  `s = ∑ i, (LinearMap.piApply (e.localFrame_coeff b i) s) • e.localFrame b i`
* `e.localFrame_coeff_congr b`: the coefficient `e.localFrame_coeff b i` of `s` in the local frame
  induced by `e` and `b` at `x` only depends on `s` at `x`.
* `e.contMDiffOn_localFrame_coeff`: if `s` is a `C^k` section, each coefficient
  `(LinearMap.piApply (e.localFrame_coeff b i) s)` is `C^k` on `e.baseSet`
* `e.contMDiffAt_iff_localFrame_coeff b`: a section `s` is `C^k` at `x ∈ e.baseSet`
  iff all of its frame coefficients are
* `e.contMDiffOn_iff_localFrame_coeff b`: a section `s` is `C^k` on an open set `t ⊆ e.baseSet`
  iff all of its frame coefficients are

## Note

This file proves smoothness criteria in terms of coefficients for local frames induced by a
trivialization. A fully frame-intrinsic converse for `IsLocalFrameOn` will be added later.

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
  (n : ℕ∞ω)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [FiberBundle F V]

noncomputable section

section IsLocalFrame

variable {ι : Type*} {s s' : ι → (x : M) → V x} {u u' : Set M} {x : M} {n : ℕ∞ω}

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
@[implicit_reducible]
noncomputable def fintypeOfFiniteDimensional [VectorBundle 𝕜 F V] [FiniteDimensional 𝕜 F]
    (hs : IsLocalFrameOn I F n s u) (hx : x ∈ u) : Fintype ι := by
  have : FiniteDimensional 𝕜 (V x) := by
    let phi := (trivializationAt F V x).linearEquivAt 𝕜 x
      (FiberBundle.mem_baseSet_trivializationAt' x)
    exact Finite.equiv phi.symm
  exact FiniteDimensional.fintypeBasisIndex (hs.toBasisAt hx)

@[deprecated (since := "2025-12-19")]
alias fintype_of_finiteDimensional := fintypeOfFiniteDimensional

open scoped Classical in
/-- Coefficients of a section `s` of `V` w.r.t. a local frame `{s i}` on `u`.
Outside of `u`, this returns the junk value 0. -/
def coeff (hs : IsLocalFrameOn I F n s u) (i : ι) : Π x : M, (V x →ₗ[𝕜] 𝕜) := fun x ↦
  if hx : x ∈ u then (hs.toBasisAt hx).coord i else 0

variable {x : M}

@[simp]
lemma coeff_apply_of_notMem (hs : IsLocalFrameOn I F n s u) (hx : x ∉ u) (i : ι) :
    hs.coeff i x = 0 := by
  simp [coeff, hx]

@[simp]
lemma coeff_apply_of_mem (hs : IsLocalFrameOn I F n s u) (hx : x ∈ u) (t : Π x : M, V x) (i : ι) :
    hs.coeff i x (t x) = (hs.toBasisAt hx).repr (t x) i := by
  simp [coeff, hx]

lemma coeff_sum_eq [Fintype ι] (hs : IsLocalFrameOn I F n s u) (t : Π x : M, V x) (hx : x ∈ u) :
    t x = ∑ i, hs.coeff i x (t x) • (s i x) := by
  simpa [coeff, hx] using (Basis.sum_repr (hs.toBasisAt hx) (t x)).symm

lemma eq_of_coeff_eq [Finite ι] (hs : IsLocalFrameOn I F n s u) (hx : x ∈ u)
    {t t' : Π x : M, V x}
    (h : ∀ i, hs.coeff i x (t x) = hs.coeff i x (t' x)) :
    t x = t' x := by
  let : Fintype ι := Fintype.ofFinite ι
  calc
    t x = ∑ i, hs.coeff i x (t x) • (s i x) := hs.coeff_sum_eq t hx
    _ = ∑ i, hs.coeff i x (t' x) • (s i x) := by simp [h]
    _ = t' x := (hs.coeff_sum_eq t' hx).symm

/-- A local frame locally spans the space of sections for `V`: for each local frame `s i` on an open
set `u` around `x`, we have `t = ∑ i, hs.coeff i x (t x) • (s i x)` near `x`. -/
lemma eventually_eq_sum_coeff_smul [Fintype ι]
    (hs : IsLocalFrameOn I F n s u) (t : Π x : M, V x) (hu'' : u ∈ 𝓝 x) :
    ∀ᶠ x' in 𝓝 x, t x' = ∑ i, hs.coeff i x' (t x') • (s i x') :=
  eventually_of_mem hu'' fun _ hx ↦ hs.coeff_sum_eq _ hx

variable {t t' : Π x : M, V x}

/-- The coefficients of `t` in a local frame at `x` only depend on `t` at `x`. -/
lemma coeff_congr (hs : IsLocalFrameOn I F n s u) (htt' : t x = t' x) (i : ι) :
    hs.coeff i x (t x) = hs.coeff i x (t' x) := by
  by_cases hxe : x ∈ u <;> simp [coeff, hxe, htt']

/-- If `s` and `s'` are local frames which are equal at `x`,
a section `t` has equal frame coefficients in them. -/
lemma coeff_eq_of_eq (hs : IsLocalFrameOn I F n s u) (hs' : IsLocalFrameOn I F n s' u)
    (hss' : ∀ i, s i x = s' i x) {t : Π x : M, V x} (i : ι) :
    hs.coeff i x (t x) = hs'.coeff i x (t x) := by
  by_cases hxe : x ∈ u
  · simp [coeff, hxe]
    simp_all only [toBasisAt]
  · simp [coeff, hxe]

/-- Two sections `s` and `t` are equal at `x` if and only if their coefficients w.r.t. some local
frame at `x` agree. -/
lemma eq_iff_coeff [VectorBundle 𝕜 F V] [FiniteDimensional 𝕜 F]
    (hs : IsLocalFrameOn I F n s u) (hx : x ∈ u) :
    t x = t' x ↔ ∀ i, hs.coeff i x (t x) = hs.coeff i x (t' x) := by
  let := fintypeOfFiniteDimensional hs hx
  exact ⟨fun h i ↦ hs.coeff_congr h i, fun h ↦ hs.eq_of_coeff_eq hx h⟩

variable (hs : IsLocalFrameOn I F n s u) [VectorBundle 𝕜 F V]

/-- Given a local frame `s i ` on `u`, if a section `t` has `C^k` coefficients on `u` w.r.t. `s i`,
then `t` is `C^n` on `u`. -/
lemma contMDiffOn_of_coeff [FiniteDimensional 𝕜 F]
    (h : ∀ i, CMDiff[u] n ((LinearMap.piApply (hs.coeff i)) t)) :
    CMDiff[u] n (T% t) := by
  rcases u.eq_empty_or_nonempty with rfl | ⟨x, hx⟩; · simp
  have := fintypeOfFiniteDimensional hs hx
  have this (i) : CMDiff[u] n (T% ((LinearMap.piApply (hs.coeff i)) t • s i)) :=
    (h i).smul_section (hs.contMDiffOn i)
  have almost : CMDiff[u] n (T% (fun x ↦ ∑ i, ((LinearMap.piApply (hs.coeff i)) t) x • s i x)) :=
    .sum_section fun i _ ↦ this i
  apply almost.congr
  intro y hy
  simpa using congrArg (TotalSpace.mk' F y) (hs.coeff_sum_eq t hy)

/-- Given a local frame `s i` on a neighbourhood `u` of `x`,
if a section `t` has `C^k` coefficients at `x` w.r.t. `s i`, then `t` is `C^n` at `x`. -/
lemma contMDiffAt_of_coeff [FiniteDimensional 𝕜 F]
    (h : ∀ i, CMDiffAt n ((LinearMap.piApply (hs.coeff i)) t) x) (hu : u ∈ 𝓝 x) :
    CMDiffAt n (T% t) x := by
  have := fintypeOfFiniteDimensional hs (mem_of_mem_nhds hu)
  have almost : CMDiffAt n (T% (fun x ↦ ∑ i, ((LinearMap.piApply (hs.coeff i)) t) x • s i x)) x :=
    .sum_section (fun i _ ↦ (h i).smul_section <| (hs.contMDiffOn i).contMDiffAt hu)
  exact almost.congr_of_eventuallyEq <| (hs.eventually_eq_sum_coeff_smul t hu).mono (by simp)

/-- Given a local frame `s i` on an open set `u` containing `x`, if a section `t` has `C^k`
coefficients at `x ∈ u` w.r.t. `s i`, then `t` is `C^n` at `x`. -/
lemma contMDiffAt_of_coeff_aux [FiniteDimensional 𝕜 F]
    (h : ∀ i, CMDiffAt n ((LinearMap.piApply (hs.coeff i)) t) x)
    (hu : IsOpen u) (hx : x ∈ u) : CMDiffAt n (T% t) x := by
  have := fintypeOfFiniteDimensional hs hx
  exact hs.contMDiffAt_of_coeff h (hu.mem_nhds hx)

section

variable (hs : IsLocalFrameOn I F 1 s u)

/-- Given a local frame `s i ` on `u`, if a section `t` has differentiable coefficients on `u`
w.r.t. `s i`, then `t` is differentiable on `u`. -/
lemma mdifferentiableOn_of_coeff [FiniteDimensional 𝕜 F]
    (h : ∀ i, MDiff[u] ((LinearMap.piApply (hs.coeff i)) t)) :
    MDiff[u] (T% t) := by
  rcases u.eq_empty_or_nonempty with rfl | ⟨x, hx⟩; · simp
  have := fintypeOfFiniteDimensional hs hx
  have this (i) : MDiff[u] (T% ((LinearMap.piApply (hs.coeff i)) t • s i)) :=
    (h i).smul_section ((hs.contMDiffOn i).mdifferentiableOn one_ne_zero)
  have almost : MDiff[u] (T% (fun x ↦ ∑ i, hs.coeff i x (t x) • s i x)) :=
    .sum_section (fun i _ hx ↦ this i _ hx)
  apply almost.congr
  intro y hy
  simpa using congrArg (TotalSpace.mk' F y) (hs.coeff_sum_eq t hy)

/-- Given a local frame `s i` on a neighbourhood `u` of `x`, if a section `t` has differentiable
coefficients at `x` w.r.t. `s i`, then `t` is differentiable at `x`. -/
lemma mdifferentiableAt_of_coeff [FiniteDimensional 𝕜 F]
    (h : ∀ i, MDiffAt ((LinearMap.piApply (hs.coeff i)) t) x) (hu : u ∈ 𝓝 x) :
    MDiffAt (T% t) x := by
  have := fintypeOfFiniteDimensional hs (mem_of_mem_nhds hu)
  have almost : MDiffAt (T% (fun x ↦ ∑ i, hs.coeff i x (t x) • s i x)) x :=
    .sum_section (fun i ↦ (h i).smul_section <|
      ((hs.contMDiffOn i).mdifferentiableOn one_ne_zero).mdifferentiableAt hu)
  exact almost.congr_of_eventuallyEq <| (hs.eventually_eq_sum_coeff_smul t hu).mono (by simp)

/-- Given a local frame `s i` on open set `u` containing `x`, if a section `t`
has differentiable coefficients at `x ∈ u` w.r.t. `s i`, then `t` is differentiable at `x`. -/
lemma mdifferentiableAt_of_coeff_aux [FiniteDimensional 𝕜 F]
    (h : ∀ i, MDiffAt ((LinearMap.piApply (hs.coeff i)) t) x)
    (hu : IsOpen u) (hx : x ∈ u) : MDiffAt (T% t) x :=
  hs.mdifferentiableAt_of_coeff h (hu.mem_nhds hx)

end

end IsLocalFrameOn

end IsLocalFrame

namespace Bundle.Trivialization

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

variable [ContMDiffVectorBundle 1 F V I]

variable (I) in
/-- Coefficients of a section `s` of `V` w.r.t. the local frame `b.localFrame e i`.

If x is outside of `e.baseSet`, this returns the junk value 0. -/
def localFrame_coeff (i : ι) : Π x : M, (V x →ₗ[𝕜] 𝕜) :=
  (e.isLocalFrameOn_localFrame_baseSet I 1 b).coeff i

variable {e b}
variable {x x' : M}

variable (e b) in
@[simp]
lemma localFrame_coeff_apply_of_notMem_baseSet (hx : x ∉ e.baseSet) (i : ι) :
    e.localFrame_coeff I b i x = 0 := by
  simpa [localFrame_coeff] using
    (e.isLocalFrameOn_localFrame_baseSet I 1 b).coeff_apply_of_notMem hx i

variable (e b) in
@[simp]
lemma localFrame_coeff_apply_of_mem_baseSet (hx : x ∈ e.baseSet) (s : Π x : M, V x) (i : ι) :
    (localFrame_coeff I e b i x) (s x) = (e.basisAt b hx).repr (s x) i := by
  have he := e.isLocalFrameOn_localFrame_baseSet I 1 b
  have hbasis : e.basisAt b hx = he.toBasisAt hx := by
    ext j
    simp [IsLocalFrameOn.toBasisAt, localFrame, basisAt, hx]
  simp [localFrame_coeff, IsLocalFrameOn.coeff, hx, hbasis]

variable {s s' : Π x : M, V x}

lemma eq_sum_localFrame_coeff_smul [Fintype ι] (hx : x' ∈ e.baseSet) :
    s x' = ∑ i, e.localFrame_coeff I b i x' (s x') • e.localFrame b i x' :=
  (isLocalFrameOn_localFrame_baseSet I 1 e b).coeff_sum_eq s hx

variable (e b) in
/-- A local frame locally spans the space of sections for `V`: for each local trivialisation `e`
of `V` around `x`, we have
`s = ∑ i, (LinearMap.piApply (b.localFrame_coeff e i) s) • b.localFrame e i` near `x`. -/
lemma eventually_eq_localFrame_sum_coeff_smul [Fintype ι] (hxe : x ∈ e.baseSet) :
    ∀ᶠ x' in 𝓝 x, s x' = ∑ i, e.localFrame_coeff I b i x' (s x') • e.localFrame b i x' :=
  eventually_nhds_iff.mpr ⟨e.baseSet, fun _ ↦ e.eq_sum_localFrame_coeff_smul, e.open_baseSet, hxe⟩

variable (e b) in
/-- The representation of `s` in a local frame at `x` only depends on `s` at `x`. -/
lemma localFrame_coeff_congr {i : ι} (hss' : s x = s' x) :
    e.localFrame_coeff I b i x (s x) = e.localFrame_coeff I b i x (s' x) := by
  simpa using (isLocalFrameOn_localFrame_baseSet I 1 e b).coeff_congr hss' i

variable {n}

variable (e) in
/-- Suppose `e` is a compatible trivialisation around `x ∈ M`, and `s` a bundle section.
Then the coefficient of `s` w.r.t. the local frame induced by `b` and `e`
equals the coefficient of "`s x` read in the trivialisation `e`" for `b i`. -/
lemma localFrame_coeff_eq_coeff (hxe : x ∈ e.baseSet) {i : ι} :
    e.localFrame_coeff I b i x (s x) = b.repr (e ((T% s) x)).2 i := by
  simp [e.localFrame_coeff_apply_of_mem_baseSet b hxe, basisAt]

end Bundle.Trivialization

/-! # Determining smoothness of a section via its local frame coefficients
We show that for finite rank bundles over a complete field, a section is smooth iff its coefficients
in a local frame induced by a local trivialisation are. In many contexts, this statement holds for
*any* local frame (e.g., for all real bundles which admit a continuous bundle metric, as is
proven in `OrthonormalFrame.lean`).
-/

variable [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
  {e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e]
  {ι : Type*} (b : Basis ι 𝕜 F) {s : Π x : M, V x} {t : Set M} {k : ℕ∞ω} {x x' : M}
  [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] [ContMDiffVectorBundle k F V I]

/-- If `s` is `C^k` at `x`, so is its coefficient `b.localFrame_coeff e i` in the local frame
near `x` induced by `e` and `b` -/
lemma contMDiffAt_localFrame_coeff (hxe : x ∈ e.baseSet) (hs : CMDiffAt k (T% s) x) (i : ι) :
    CMDiffAt k ((LinearMap.piApply (e.localFrame_coeff I b i)) s) x := by
  -- This boils down to computing the frame coefficients in a local trivialisation.
  classical
  -- step 1: on e.baseSet, we know compute the coefficient very well
  let aux := fun x ↦ b.repr (e ((T% s) x)).2 i
  -- Since `e.baseSet` is open, this is sufficient.
  suffices CMDiffAt k aux x by
    apply this.congr_of_eventuallyEq ?_
    apply eventuallyEq_of_mem (s := e.baseSet) (by simp [e.open_baseSet.mem_nhds hxe])
    intro y hy
    simp [aux, e.localFrame_coeff_eq_coeff hy]
  simp only [aux]
  -- step 2: `s` read in trivialization `e` is `C^k`
  have h₁ : CMDiffAt k (fun x ↦ (e ((T% s) x)).2) x := by
    simpa using (e.contMDiffAt_section_iff hxe).1 hs
  -- step 3: `b.repr` is a linear map, so the composition is smooth
  let breprl : F →ₗ[𝕜] 𝕜 :=
    { toFun v := b.repr v i
      map_add' m m' := by simp
      map_smul' m x := by simp }
  have : ContMDiffAt 𝓘(𝕜, F) 𝓘(𝕜) k breprl.toContinuousLinearMap (e ((T% s) x)).2 :=
    contMDiffAt_iff_contDiffAt.mpr <| by fun_prop
  exact this.comp x h₁

/-- If `s` is `C^k` on `t ⊆ e.baseSet`, so is its coefficient `b.localFrame_coeff e i`
in the local frame induced by `e` -/
lemma contMDiffOn_localFrame_coeff (ht : IsOpen t) (ht' : t ⊆ e.baseSet)
    (hs : CMDiff[t] k (T% s)) (i : ι) :
    CMDiff[t] k ((LinearMap.piApply (e.localFrame_coeff I b i)) s) :=
  fun _ hx ↦ (contMDiffAt_localFrame_coeff b (ht' hx)
    (hs.contMDiffAt (ht.mem_nhds hx)) i).contMDiffWithinAt

/-- If `s` is `C^k` on `e.baseSet`, so is its coefficient `b.localFrame_coeff e i`
in the local frame induced by `e` -/
lemma contMDiffOn_baseSet_localFrame_coeff (hs : CMDiff[e.baseSet] k (T% s)) (i : ι) :
    CMDiff[e.baseSet] k ((LinearMap.piApply (e.localFrame_coeff I b i)) s) :=
  contMDiffOn_localFrame_coeff b e.open_baseSet (subset_refl _) hs _

/-- A section `s` of `V` is `C^k` at `x ∈ e.baseSet` iff each of its
coefficients `(LinearMap.piApply (b.localFrame_coeff e i) s)` in a local frame near `x` is -/
lemma contMDiffAt_iff_localFrame_coeff (hx : x' ∈ e.baseSet) :
    CMDiffAt k (T% s) x' ↔ ∀ i, CMDiffAt k ((LinearMap.piApply (e.localFrame_coeff I b i)) s) x' :=
  ⟨fun h i ↦ contMDiffAt_localFrame_coeff b hx h i,
    fun hi ↦ (e.isLocalFrameOn_localFrame_baseSet I k b).contMDiffAt_of_coeff hi
    (e.open_baseSet.mem_nhds hx)⟩

/-- A section `s` of `V` is `C^k` on `t ⊆ e.baseSet` iff each of its
coefficients `(LinearMap.piApply (b.localFrame_coeff e i) s)` in a local frame near `x` is -/
lemma contMDiffOn_iff_localFrame_coeff (ht : IsOpen t) (ht' : t ⊆ e.baseSet) :
    CMDiff[t] k (T% s) ↔ ∀ i, CMDiff[t] k ((LinearMap.piApply (e.localFrame_coeff I b i)) s) := by
  refine ⟨fun h i ↦ contMDiffOn_localFrame_coeff b ht ht' h _, fun h x hx ↦ ?_⟩
  exact (contMDiffAt_iff_localFrame_coeff b (ht' hx)).mpr
    (fun i ↦ (h i x hx).contMDiffAt (ht.mem_nhds hx)) |>.contMDiffWithinAt

/-- A section `s` of `V` is `C^k` on a trivialisation domain `e.baseSet` iff each of its
coefficients `(LinearMap.piApply (b.localFrame_coeff e i) s)` in a local frame near `x` is -/
lemma contMDiffOn_baseSet_iff_localFrame_coeff :
    CMDiff[e.baseSet] k (T% s) ↔
      ∀ i, CMDiff[e.baseSet] k ((LinearMap.piApply (e.localFrame_coeff I b i)) s) := by
  rw [contMDiffOn_iff_localFrame_coeff b e.open_baseSet (subset_refl _)]

-- Differentiability of a section can be checked in terms of its local frame coefficients
section MDifferentiable

/-- If `s` is differentiable at `x`, so is its coefficient `b.localFrame_coeff e i` in the local
frame near `x` induced by `e` and `b` -/
lemma mdifferentiableAt_localFrame_coeff
    (hxe : x ∈ e.baseSet) (hs : MDiffAt (T% s) x) (i : ι) :
    MDiffAt ((LinearMap.piApply (e.localFrame_coeff I b i)) s) x := by
  -- This boils down to computing the frame coefficients in a local trivialisation.
  classical
  -- step 1: on `e.baseSet`, we know the coefficient very well
  let aux := fun x ↦ b.repr (e ((T% s) x)).2 i
  -- Since `e.baseSet` is open, this is sufficient.
  suffices MDiffAt aux x by
    apply this.congr_of_eventuallyEq
    apply eventuallyEq_of_mem (s := e.baseSet) (by simp [e.open_baseSet.mem_nhds hxe])
    intro y hy
    simp [aux, e.localFrame_coeff_eq_coeff hy]
  simp only [aux]
  -- step 2: `s` read in trivialization `e` is differentiable
  have h₁ : MDiffAt (fun x ↦ (e ((T% s) x)).2) x := by
    simpa using (e.mdifferentiableAt_section_iff I s hxe).1 hs
  -- step 3: `b.repr` is a linear map, so the composition is smooth
  let breprl : F →ₗ[𝕜] 𝕜 :=
    { toFun v := b.repr v i
      map_add' m m' := by simp
      map_smul' m x := by simp }
  have : MDifferentiableAt 𝓘(𝕜, F) 𝓘(𝕜) breprl.toContinuousLinearMap (e ((T% s) x)).2 :=
    mdifferentiableAt_iff_differentiableAt.mpr <| by fun_prop
  exact this.comp x h₁

/-- If `s` is differentiable on `t ⊆ e.baseSet`, so is its coefficient `b.localFrame_coeff e i`
in the local frame induced by `e` -/
lemma mdifferentiableOn_localFrame_coeff (ht : IsOpen t) (ht' : t ⊆ e.baseSet)
    (hs : MDiff[t] (T% s)) (i : ι) : MDiff[t] ((LinearMap.piApply (e.localFrame_coeff I b i)) s) :=
  fun _ hx ↦ (mdifferentiableAt_localFrame_coeff b (ht' hx)
    (hs.mdifferentiableAt (ht.mem_nhds hx)) i).mdifferentiableWithinAt

/-- If `s` is differentiable on `e.baseSet`, so is its coefficient `b.localFrame_coeff e i` in the
local frame induced by `e` -/
lemma mdifferentiableOn_baseSet_localFrame_coeff (hs : MDiff[e.baseSet] (T% s)) (i : ι) :
    MDiff[e.baseSet] ((LinearMap.piApply (e.localFrame_coeff I b i)) s) :=
  mdifferentiableOn_localFrame_coeff b e.open_baseSet (subset_refl _) hs _

/-- A section `s` of `V` is differentiable at `x ∈ e.baseSet` iff each of its
coefficients `(LinearMap.piApply (b.localFrame_coeff e i) s)` in a local frame near `x` is -/
lemma mdifferentiableAt_iff_localFrame_coeff (hx : x' ∈ e.baseSet) :
    MDiffAt (T% s) x' ↔ ∀ i, MDiffAt ((LinearMap.piApply (e.localFrame_coeff I b i)) s) x' :=
  ⟨fun h i ↦ mdifferentiableAt_localFrame_coeff b hx h i, fun hi ↦
    (e.isLocalFrameOn_localFrame_baseSet I 1 b).mdifferentiableAt_of_coeff_aux hi e.open_baseSet hx⟩

end MDifferentiable

end
