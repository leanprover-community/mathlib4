/-
Copyright (c) 2026 Octavian Halmaghi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Octavian Halmaghi
-/
module

public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.Normed.Operator.Fredholm.Open
public import Mathlib.Analysis.RCLike.Lemmas

/-!
# Compact perturbations of Fredholm operators

Let `E` be a Banach space over `𝕜 = ℝ` or `ℂ` and let `c : E →L[𝕜] E` be a compact operator.
This file proves the **Riesz–Schauder theorem**: `1 + c` is a Fredholm operator of index `0`,
and deduces that adding a compact operator to a Fredholm operator changes neither the Fredholm
property nor the index.

## Main results

* `IsCompactOperator.isFredholm_one_add`: `1 + c` is Fredholm for `c` compact.
* `IsCompactOperator.index_one_add`: `(1 + c).index = 0` for `c` compact.
* `ContinuousLinearMap.IsFredholm.add_isCompactOperator`: `u + k` is Fredholm when `u` is
  Fredholm and `k` is compact.
* `ContinuousLinearMap.IsFredholm.index_add_isCompactOperator`: `(u + k).index = u.index` when
  `u` is Fredholm and `k` is compact.

## Proof outline

Write `T = 1 + c`, `N = T.ker` and `R = T.range`. The proof avoids both the Riesz theory of
ascent and descent and the adjoint operator, using instead the Fredholm alternative
`IsCompactOperator.hasEigenvalue_or_mem_resolventSet` and a counting argument.

* `N` is finite-dimensional: `c` restricts to `-1` on `N`, so the identity of `N` is a compact
  operator (`IsCompactOperator.finiteDimensional_ker_one_add`).
* `N` has a closed complement `M` (Hahn–Banach), and `T` is bounded below on `M`: otherwise
  unit vectors `xₙ ∈ M` with `T xₙ → 0` would have, after extracting a convergent subsequence
  of `c xₙ`, a limit `x ∈ M` of norm one with `T x = 0`
  (`IsCompactOperator.exists_norm_le_of_isTopCompl_ker_one_add`). Hence `R = T '' M` is closed
  (`IsCompactOperator.isClosed_range_one_add`).
* `R` has finite codimension (`IsCompactOperator.finiteDimensional_coker_one_add`). If not,
  there is a linear map `h : N → E` which is injective modulo `R`; the finite-rank correction
  `S = T + h ∘ P`, with `P` the projection onto `N` along `M`, is injective, so by the Fredholm
  alternative it is surjective. But its range is `R + h '' N`, which would make `E ⧸ R` a
  quotient of the finite-dimensional `N`.
* The index vanishes because `t ↦ (1 + t • c).index` is locally constant
  (`ContinuousLinearMap.IsFredholm.eventually_nhds_index_eq`) on the connected `ℝ`, and
  equals `0` at `t = 0`.

For the perturbation statement, let `q` be a quasi-inverse of the Fredholm operator `u`. Then
`q ∘L (u + k) = 1 + ((q ∘L u - 1) + q ∘L k)` is a compact perturbation of the identity, hence
Fredholm of index `0`; `u + k` is Fredholm because `q` is, and the index follows from
additivity under composition, `ContinuousLinearMap.IsFredholm.index_comp`.

The scalars are restricted to `RCLike 𝕜` because the closed complement of the
finite-dimensional kernel comes from the Hahn–Banach theorem
(`Submodule.ClosedComplemented.of_finiteDimensional`).

## References

* [H. Brezis, *Functional analysis, Sobolev spaces and partial differential equations*]
  [brezis2011], Theorem 6.6
-/

@[expose] public section

open Filter Topology Submodule Set
open scoped LinearMap.FiniteRangeSetoid NNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A continuous linear map with finite-dimensional range is a compact operator: it factors
through a finite-dimensional, hence locally compact, space. -/
theorem isCompactOperator_of_hasNoetherianRange {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {f : E →L[𝕜] F} (hf : (f : E →ₗ[𝕜] F).HasNoetherianRange) :
    IsCompactOperator f := by
  have : IsNoetherian 𝕜 (LinearMap.range (f : E →ₗ[𝕜] F)) := hf
  have : ProperSpace (LinearMap.range (f : E →ₗ[𝕜] F)) := FiniteDimensional.proper_rclike 𝕜 _
  have h1 : IsCompactOperator (f.codRestrict (LinearMap.range (f : E →ₗ[𝕜] F))
      fun x ↦ LinearMap.mem_range_self _ x) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  exact h1.clm_comp (LinearMap.range (f : E →ₗ[𝕜] F)).subtypeL

namespace IsCompactOperator

variable {c : E →L[𝕜] E}

/-- The kernel of `1 + c` is finite-dimensional for `c` compact: on it, `c` is `-1`, so the
identity of the kernel is a compact operator. -/
theorem finiteDimensional_ker_one_add (hc : IsCompactOperator c) :
    FiniteDimensional 𝕜 (1 + c : E →L[𝕜] E).ker := by
  set N := LinearMap.ker ((1 + c : E →L[𝕜] E) : E →ₗ[𝕜] E) with hN
  have hker : ∀ v ∈ N, v + c v = 0 := fun v hv ↦ by
    have h := LinearMap.mem_ker.mp hv
    change v + c v = 0 at h
    exact h
  have hmem : ∀ v ∈ N, (c : E →ₗ[𝕜] E) v ∈ N := by
    intro v hv
    have h : (c : E →ₗ[𝕜] E) v = -v := by
      rw [ContinuousLinearMap.coe_coe]
      exact eq_neg_of_add_eq_zero_right (hker v hv)
    rw [h]
    exact N.neg_mem hv
  have hcl : IsClosed (N : Set E) := (1 + c).isClosed_ker
  have hres : IsCompactOperator ((c : E →ₗ[𝕜] E).restrict hmem) :=
    IsCompactOperator.restrict (f := (c : E →ₗ[𝕜] E)) hc hmem hcl
  have hid : IsCompactOperator (id : N → N) := by
    have h := hres.neg
    have heq : (-⇑((c : E →ₗ[𝕜] E).restrict hmem)) = (id : N → N) := by
      funext v
      apply Subtype.ext
      simp only [Pi.neg_apply, LinearMap.restrict_apply, Submodule.coe_neg,
        ContinuousLinearMap.coe_coe, id_eq]
      exact neg_eq_of_add_eq_zero_left (hker v v.2)
    rw [heq] at h
    exact h
  exact FiniteDimensional.of_isCompactOperator_id hid

/-- The kernel of `1 + c` has a closed complement. -/
theorem exists_isTopCompl_ker_one_add (hc : IsCompactOperator c) :
    ∃ M : Submodule 𝕜 E, IsTopCompl (1 + c : E →L[𝕜] E).ker M := by
  have := hc.finiteDimensional_ker_one_add
  exact (Submodule.ClosedComplemented.of_finiteDimensional _).exists_isTopCompl

/-- `1 + c` is bounded below on a closed complement of its kernel. -/
theorem exists_norm_le_of_isTopCompl_ker_one_add (hc : IsCompactOperator c)
    {M : Submodule 𝕜 E} (hM : IsTopCompl (1 + c : E →L[𝕜] E).ker M) :
    ∃ K : ℝ≥0, ∀ x ∈ M, ‖x‖ ≤ K * ‖(1 + c) x‖ := by
  set T : E →L[𝕜] E := 1 + c with hT
  set N := LinearMap.ker (T : E →ₗ[𝕜] E) with hN
  have hMc : IsClosed (M : Set E) := hM.isClosed'
  by_contra hcon
  have hseq : ∀ n : ℕ, ∃ x ∈ M, ((n : ℝ) + 1) * ‖T x‖ < ‖x‖ := by
    intro n
    by_contra hn
    apply hcon
    refine ⟨((n + 1 : ℕ) : ℝ≥0), fun x hx ↦ ?_⟩
    by_contra hlt
    apply hn
    refine ⟨x, hx, ?_⟩
    rw [not_le, NNReal.coe_natCast, Nat.cast_add_one] at hlt
    exact hlt
  choose x hxM hx using hseq
  have hx0 : ∀ n, x n ≠ 0 := fun n h ↦ by
    have := hx n
    rw [h, norm_zero] at this
    have : (0 : ℝ) ≤ ((n : ℝ) + 1) * ‖T 0‖ := by positivity
    linarith
  set y : ℕ → E := fun n ↦ (‖x n‖⁻¹ : 𝕜) • x n with hy
  have hy1 : ∀ n, ‖y n‖ = 1 := fun n ↦ norm_smul_inv_norm (hx0 n)
  have hyM : ∀ n, y n ∈ M := fun n ↦ M.smul_mem _ (hxM n)
  have hTy : ∀ n, ‖T (y n)‖ ≤ 1 / ((n : ℝ) + 1) := fun n ↦ by
    have hpos : 0 < ‖x n‖ := norm_pos_iff.mpr (hx0 n)
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have : ‖T (y n)‖ = ‖x n‖⁻¹ * ‖T (x n)‖ := by
      simp only [hy, map_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm]
    rw [this, inv_mul_le_iff₀ hpos, mul_one_div, le_div_iff₀ hn1]
    linarith [hx n]
  have hT0 : Tendsto (fun n ↦ T (y n)) atTop (𝓝 0) :=
    squeeze_zero_norm hTy tendsto_one_div_add_atTop_nhds_zero_nat
  have hK : IsCompact (closure (c '' Metric.closedBall 0 1)) :=
    hc.isCompact_closure_image_closedBall 1
  have hmem : ∀ n, c (y n) ∈ closure (c '' Metric.closedBall 0 1) := fun n ↦
    subset_closure (Set.mem_image_of_mem c (mem_closedBall_zero_iff.mpr (hy1 n).le))
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hyφ : Tendsto (fun n ↦ y (φ n)) atTop (𝓝 (0 - a)) := by
    have h := (hT0.comp hφ.tendsto_atTop).sub hlim
    refine h.congr fun n ↦ ?_
    change y (φ n) + c (y (φ n)) - c (y (φ n)) = y (φ n)
    exact add_sub_cancel_right _ _
  have haM : 0 - a ∈ M := hMc.mem_of_tendsto hyφ (Eventually.of_forall fun n ↦ hyM (φ n))
  have hanorm : ‖0 - a‖ = 1 := by
    have h1 : Tendsto (fun n ↦ ‖y (φ n)‖) atTop (𝓝 ‖0 - a‖) := hyφ.norm
    have h2 : Tendsto (fun n ↦ ‖y (φ n)‖) atTop (𝓝 1) := by
      simp only [hy1]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  have haN : 0 - a ∈ N := by
    have h1 : Tendsto (fun n ↦ T (y (φ n))) atTop (𝓝 (T (0 - a))) :=
      (T.continuous.tendsto _).comp hyφ
    have h2 : Tendsto (fun n ↦ T (y (φ n))) atTop (𝓝 0) := hT0.comp hφ.tendsto_atTop
    exact LinearMap.mem_ker.mpr (tendsto_nhds_unique h1 h2)
  have hzero : 0 - a = 0 := Submodule.disjoint_def.mp hM.isCompl.disjoint _ haN haM
  rw [hzero, norm_zero] at hanorm
  exact zero_ne_one hanorm

variable [CompleteSpace E]

/-- The range of `1 + c` is closed: it is the image of a closed complement of the kernel, on
which `1 + c` is bounded below. -/
theorem isClosed_range_one_add (hc : IsCompactOperator c) :
    IsClosed ((1 + c : E →L[𝕜] E).range : Set E) := by
  obtain ⟨M, hM⟩ := hc.exists_isTopCompl_ker_one_add
  obtain ⟨K, hK⟩ := hc.exists_norm_le_of_isTopCompl_ker_one_add hM
  set T : E →L[𝕜] E := 1 + c with hT
  set N := LinearMap.ker (T : E →ₗ[𝕜] E) with hN
  have hMc : IsClosed (M : Set E) := hM.isClosed'
  have : CompleteSpace M := hMc.completeSpace_coe
  have hanti : AntilipschitzWith K (T ∘L M.subtypeL) :=
    (T ∘L M.subtypeL).antilipschitz_of_bound fun x ↦ hK x x.2
  have hcl : IsClosed (Set.range (T ∘L M.subtypeL)) :=
    hanti.isClosed_range (T ∘L M.subtypeL).uniformContinuous
  have heq : ((LinearMap.range (T : E →ₗ[𝕜] E) : Submodule 𝕜 E) : Set E)
      = Set.range (T ∘L M.subtypeL) := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      have hw : w ∈ N ⊔ M := by rw [hM.isCompl.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨n, hn, m, hm, rfl⟩ := Submodule.mem_sup.mp hw
      refine ⟨⟨m, hm⟩, ?_⟩
      have hTn : T n = 0 := LinearMap.mem_ker.mp hn
      change T m = T (n + m)
      rw [map_add, hTn, zero_add]
    · rintro ⟨⟨m, hm⟩, rfl⟩
      exact ⟨m, rfl⟩
  exact heq ▸ hcl

/-- The cokernel of `1 + c` is finite-dimensional. This is where the Fredholm alternative enters:
an injective finite-rank correction of `1 + c` would be surjective, so its range `R + h '' N`
would be all of `E`, making `E ⧸ R` a quotient of the finite-dimensional kernel `N`; such a
correction exists as soon as `E ⧸ R` is infinite-dimensional. -/
theorem finiteDimensional_coker_one_add (hc : IsCompactOperator c) :
    FiniteDimensional 𝕜 (E ⧸ (1 + c : E →L[𝕜] E).range) := by
  set T : E →L[𝕜] E := 1 + c with hT
  set N := LinearMap.ker (T : E →ₗ[𝕜] E) with hN
  set R := LinearMap.range (T : E →ₗ[𝕜] E) with hR
  have hNfin : FiniteDimensional 𝕜 N := hc.finiteDimensional_ker_one_add
  obtain ⟨M, hM⟩ := hc.exists_isTopCompl_ker_one_add
  have hdecomp : ∀ w : E, ∃ n ∈ N, ∃ m ∈ M, n + m = w := fun w ↦ by
    have hw : w ∈ N ⊔ M := by rw [hM.isCompl.sup_eq_top]; exact Submodule.mem_top
    exact Submodule.mem_sup.mp hw
  by_contra hinf
  -- an injective map `N → E ⧸ R`, lifted to `E`
  obtain ⟨h, hh⟩ : ∃ h : N →ₗ[𝕜] E, Function.Injective (R.mkQ ∘ₗ h) := by
    have hrank : (Module.finrank 𝕜 N : Cardinal) ≤ Module.rank 𝕜 (E ⧸ R) := by
      have h1 : ¬ Module.rank 𝕜 (E ⧸ R) < Cardinal.aleph0 := fun h ↦
        hinf (Module.rank_lt_aleph0_iff.mp h)
      exact Cardinal.natCast_lt_aleph0.le.trans (not_lt.mp h1)
    obtain ⟨s, hs, hsli⟩ := le_rank_iff_exists_linearIndependent_finset.mp hrank
    have hcard : Cardinal.mk {x // x ∈ (↑s : Set (E ⧸ R))} = s.card := Cardinal.mk_coe_finset
    obtain ⟨j, hj⟩ := Module.Free.exists_linearMap_injective_of_linearIndependent_of_rank_le
      (M := N) hsli (le_of_eq (by rw [hcard, hs, Module.finrank_eq_rank]))
    obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective R.mkQ R.range_mkQ
    refine ⟨g ∘ₗ j, ?_⟩
    rw [← LinearMap.comp_assoc, hg, LinearMap.id_comp]
    exact hj
  -- the projection onto `N` along `M`, and the corrected operator `S = T + h ∘ P`
  set P : E →L[𝕜] N := N.projectionOntoL M hM with hP
  set hL : N →L[𝕜] E := LinearMap.toContinuousLinearMap h with hhL
  set S : E →L[𝕜] E := T + hL ∘L P with hS
  have hPn : ∀ n (hn : n ∈ N), P n = ⟨n, hn⟩ := fun n hn ↦
    N.projectionOntoL_apply_left hM ⟨n, hn⟩
  have hPm : ∀ m ∈ M, P m = 0 := fun m hm ↦ N.projectionOntoL_apply_right hM ⟨m, hm⟩
  have hSapply : ∀ n (hn : n ∈ N), ∀ m ∈ M, S (n + m) = T m + h ⟨n, hn⟩ := by
    intro n hn m hm
    have hTn : T n = 0 := LinearMap.mem_ker.mp hn
    change T (n + m) + hL (P (n + m)) = T m + h ⟨n, hn⟩
    rw [map_add, map_add, hPn n hn, hPm m hm, add_zero, hTn, zero_add]
    rfl
  have hmkQ_T : ∀ m, R.mkQ (T m) = 0 := fun m ↦
    (Submodule.Quotient.mk_eq_zero R).mpr (LinearMap.mem_range_self (T : E →ₗ[𝕜] E) m)
  -- `S` is injective
  have hSinj : Function.Injective S := by
    refine (injective_iff_map_eq_zero S).mpr fun w hw ↦ ?_
    obtain ⟨n, hn, m, hm, rfl⟩ := hdecomp w
    rw [hSapply n hn m hm] at hw
    have h1 : (R.mkQ ∘ₗ h) ⟨n, hn⟩ = 0 := by
      have := congrArg R.mkQ hw
      rw [map_add, hmkQ_T, zero_add, map_zero] at this
      exact this
    have hn0 : (⟨n, hn⟩ : N) = 0 := hh (by rw [h1, map_zero])
    have hn0' : n = 0 := congrArg Subtype.val hn0
    rw [hn0, map_zero, add_zero] at hw
    have hmN : m ∈ N := LinearMap.mem_ker.mpr hw
    have hm0 : m = 0 := Submodule.disjoint_def.mp hM.isCompl.disjoint _ hmN hm
    rw [hn0', hm0, add_zero]
  -- `S = 1 + c'` with `c'` compact
  have hc' : IsCompactOperator (c + hL ∘L P : E →L[𝕜] E) := by
    have : ProperSpace N := FiniteDimensional.proper_rclike 𝕜 N
    have hPc : IsCompactOperator P := isCompactOperator_of_locallyCompactSpace_dom P
    exact hc.add (hPc.clm_comp hL)
  have hSeq : S = 1 + (c + hL ∘L P) := by rw [hS, hT, add_assoc]
  rcases IsCompactOperator.hasEigenvalue_or_mem_resolventSet (T := -(c + hL ∘L P)) (μ := 1)
      hc'.neg one_ne_zero with heig | hres
  · exfalso
    obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
    have h1 : -((c + hL ∘L P) v) = v := by
      have := hv.apply_eq_smul
      rwa [one_smul] at this
    have h2 : S v = 0 := by
      have h1' : (c + hL ∘L P) v = -v := neg_eq_iff_eq_neg.mp h1
      rw [hSeq]
      change v + (c + hL ∘L P) v = 0
      rw [h1', add_neg_cancel]
    exact hv.2 (hSinj (by rw [h2, map_zero]))
  · rw [spectrum.mem_resolventSet_iff, map_one, sub_neg_eq_add, ← hSeq] at hres
    obtain ⟨w, hw⟩ := hres.exists_right_inv
    have hsurj : Function.Surjective S := fun z ↦ ⟨w z, by
      have := ContinuousLinearMap.ext_iff.mp hw z
      change S (w z) = z at this
      exact this⟩
    have hsurj' : Function.Surjective (R.mkQ ∘ₗ h) := by
      intro q
      obtain ⟨z, rfl⟩ := R.mkQ_surjective q
      obtain ⟨w', rfl⟩ := hsurj z
      obtain ⟨n, hn, m, hm, rfl⟩ := hdecomp w'
      refine ⟨⟨n, hn⟩, ?_⟩
      rw [hSapply n hn m hm, map_add, hmkQ_T, zero_add]
      rfl
    exact hinf (Module.Finite.of_surjective (R.mkQ ∘ₗ h) hsurj')

/-- **Riesz–Schauder.** For a compact operator `c` on a Banach space, `1 + c` is Fredholm. -/
theorem isFredholm_one_add (hc : IsCompactOperator c) :
    (1 + c : E →L[𝕜] E).IsFredholm := by
  set T : E →L[𝕜] E := 1 + c with hT
  set N := LinearMap.ker (T : E →ₗ[𝕜] E) with hN
  set R := LinearMap.range (T : E →ₗ[𝕜] E) with hR
  have hNfin : FiniteDimensional 𝕜 N := hc.finiteDimensional_ker_one_add
  have hRcofg : R.CoFG := hc.finiteDimensional_coker_one_add
  obtain ⟨M, hM⟩ := hc.exists_isTopCompl_ker_one_add
  have hMc : IsClosed (M : Set E) := hM.isClosed'
  have hRc : IsClosed (R : Set E) := hc.isClosed_range_one_add
  have hMcofg : M.CoFG :=
    Module.Finite.equiv (Submodule.quotientEquivOfIsCompl M N hM.isCompl.symm).symm
  have hmaps : Set.MapsTo T M R := fun w _ ↦ LinearMap.mem_range_self (T : E →ₗ[𝕜] E) w
  have : CompleteSpace M := hMc.completeSpace_coe
  have hdecomp : ∀ w : E, ∃ n ∈ N, ∃ m ∈ M, n + m = w := fun w ↦ by
    have hw : w ∈ N ⊔ M := by rw [hM.isCompl.sup_eq_top]; exact Submodule.mem_top
    exact Submodule.mem_sup.mp hw
  have hinj : (T.restrict hmaps).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    have h1 : T (x : E) = T (y : E) := congrArg Subtype.val hxy
    have h2 : (x : E) - y ∈ N := LinearMap.mem_ker.mpr (by
      change T ((x : E) - y) = 0
      rw [map_sub, h1, sub_self])
    have h3 : (x : E) - y ∈ M := M.sub_mem x.2 y.2
    exact Subtype.ext (sub_eq_zero.mp (Submodule.disjoint_def.mp hM.isCompl.disjoint _ h2 h3))
  have hsurj : (T.restrict hmaps).range = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨z, w, rfl⟩
    obtain ⟨n, hn, m, hm, rfl⟩ := hdecomp w
    refine ⟨⟨m, hm⟩, Subtype.ext ?_⟩
    have hTn : T n = 0 := LinearMap.mem_ker.mp hn
    change T m = T (n + m)
    rw [map_add, hTn, zero_add]
  exact ContinuousLinearMap.IsFredholm.of_isInvertible_restrict hMc hRc hmaps
    ⟨ContinuousLinearEquiv.ofBijective (T.restrict hmaps) hinj hsurj,
      ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

/-- **Riesz–Schauder**, the index. `(1 + c).index = 0` for `c` compact: the index of
`1 + t • c` is locally constant in `t`, hence constant on the connected `ℝ`, and it vanishes at
`t = 0`. -/
theorem index_one_add (hc : IsCompactOperator c) : (1 + c : E →L[𝕜] E).index = 0 := by
  have hF : ∀ t : ℝ, (1 + (t : 𝕜) • c : E →L[𝕜] E).IsFredholm := fun t ↦
    (hc.smul (t : 𝕜)).isFredholm_one_add
  have hsmul : Continuous fun t : ℝ ↦ (t : 𝕜) • c := by fun_prop
  have hpath : Continuous fun t : ℝ ↦ (1 + (t : 𝕜) • c : E →L[𝕜] E) := continuous_const.add hsmul
  have hcont : Continuous fun t : ℝ ↦ (1 + (t : 𝕜) • c : E →L[𝕜] E).index := by
    rw [continuous_iff_continuousAt]
    intro t
    have hev := (hpath.continuousAt (x := t)).eventually (hF t).eventually_nhds_index_eq
    rw [ContinuousAt, nhds_discrete ℤ, tendsto_pure]
    exact hev
  have h01 : (1 + ((0 : ℝ) : 𝕜) • c : E →L[𝕜] E).index
      = (1 + ((1 : ℝ) : 𝕜) • c : E →L[𝕜] E).index :=
    PreconnectedSpace.constant inferInstance hcont
  rw [RCLike.ofReal_zero, zero_smul, add_zero, RCLike.ofReal_one, one_smul] at h01
  rw [← h01]
  exact LinearMap.index_id

end IsCompactOperator

namespace ContinuousLinearMap.IsFredholm

variable [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {u k : E →L[𝕜] F}

omit [CompleteSpace E] in
/-- The composition of a quasi-inverse `q` of `u` with `u + k`, `k` compact, is a compact
perturbation of the identity. -/
private theorem exists_isCompactOperator_comp_add (hk : IsCompactOperator k)
    {q : F →L[𝕜] E} (hq : q.IsQuasiInverse u) :
    ∃ c : E →L[𝕜] E, IsCompactOperator c ∧ q ∘L (u + k) = 1 + c ∧
      ∃ c' : E →L[𝕜] E, IsCompactOperator c' ∧ q ∘L u = 1 + c' := by
  have hA : ((q ∘L u - 1 : E →L[𝕜] E) : E →ₗ[𝕜] E).HasNoetherianRange := by
    have h0 : ((q ∘L u - 1 : E →L[𝕜] E) : E →ₗ[𝕜] E)
        = (q : F →ₗ[𝕜] E) ∘ₗ (u : E →ₗ[𝕜] F) - LinearMap.id := rfl
    rw [h0]
    exact LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange.mp hq.1
  refine ⟨(q ∘L u - 1) + q ∘L k, (isCompactOperator_of_hasNoetherianRange hA).add (hk.clm_comp q),
    by rw [ContinuousLinearMap.comp_add]; abel, q ∘L u - 1,
    isCompactOperator_of_hasNoetherianRange hA, by abel⟩

/-- Adding a compact operator to a Fredholm operator gives a Fredholm operator. -/
theorem add_isCompactOperator (hu : u.IsFredholm) (hk : IsCompactOperator k) :
    (u + k).IsFredholm := by
  obtain ⟨q, hq⟩ := hu.exists_isQuasiInverse
  have hqF : q.IsFredholm := .of_isQuasiInverse hq.symm
  obtain ⟨c, hc, hqc, -⟩ := exists_isCompactOperator_comp_add hk hq
  have : (q ∘L (u + k)).IsFredholm := by rw [hqc]; exact hc.isFredholm_one_add
  exact hqF.comp_iff_right.mp this

/-- Adding a compact operator to a Fredholm operator does not change the index. -/
theorem index_add_isCompactOperator (hu : u.IsFredholm) (hk : IsCompactOperator k) :
    (u + k).index = u.index := by
  obtain ⟨q, hq⟩ := hu.exists_isQuasiInverse
  have hqF : q.IsFredholm := .of_isQuasiInverse hq.symm
  obtain ⟨c, hc, hqc, c', hc', hqc'⟩ := exists_isCompactOperator_comp_add hk hq
  have h1 : (q ∘L (u + k)).index = 0 := by rw [hqc]; exact hc.index_one_add
  have h2 : (q ∘L u).index = 0 := by rw [hqc']; exact hc'.index_one_add
  rw [hqF.index_comp (hu.add_isCompactOperator hk)] at h1
  rw [hqF.index_comp hu] at h2
  omega

end ContinuousLinearMap.IsFredholm
