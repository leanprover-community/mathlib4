/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Lie.AdjointAction.JordanChevalley
public import Mathlib.Algebra.Lie.IdealOperations
public import Mathlib.Algebra.Lie.Solvable
public import Mathlib.Algebra.Lie.TraceForm
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Trace

/-!
# Trace-nilpotency criterion

If the trace form of a finite-dimensional representation of a Lie algebra `L` vanishes
identically, then every element of `⁅L, L⁆` acts nilpotently. This is the key technical
lemma behind Cartan's criterion.

## Main results

* `LieModule.isNilpotent_toEnd_of_traceForm_eq_zero_algClosed`: if `K` is an algebraically closed
  field of characteristic zero, `M` is a finite-dimensional `L`-module with `traceForm K L M = 0`,
  then every `x ∈ ⁅L, L⁆` acts nilpotently on `M`.

## References

* [J. Humphreys, *Introduction to Lie Algebras and Representation Theory*] Section 4.3
-/

@[expose] public section

namespace NilpotentOfTrace

open LinearMap Module.End Polynomial

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

lemma aeval_apply_of_mem_eigenspace {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {f : Module.End R M} {p : R[X]} {μ : R} {x : M}
    (hx : f x = μ • x) : aeval f p x = p.eval μ • x := by
  rcases eq_or_ne x 0 with rfl | hne
  · simp
  · exact Module.End.aeval_apply_of_hasEigenvector ⟨mem_eigenspace_iff.mpr hx, hne⟩

lemma ad_diag_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (a : ι → K) (s : Module.End K V)
    (hs : ∀ k, s (b k) = a k • b k) (i j : ι) :
    ⁅s, b.end (i, j)⁆ = (a i - a j) • b.end (i, j) := by
  refine b.ext fun k => ?_
  change s (b.end (i, j) (b k)) - b.end (i, j) (s (b k)) = (a i - a j) • b.end (i, j) (b k)
  simp only [Module.Basis.end_apply_apply, hs k, map_smul]
  by_cases hjk : j = k
  · subst hjk; simp [hs i, sub_smul]
  · simp [hjk]

lemma trace_lie_mul_eq (x y z : Module.End K V) :
    trace K V (⁅x, y⁆ * z) = trace K V (x * ⁅y, z⁆) := by
  have h := LieModule.traceForm_apply_lie_apply K (Module.End K V) V x y z
  simp only [LieModule.traceForm_apply_apply, ← mul_eq_comp] at h
  exact h

section Lagrange

variable {K : Type*} [Field K]

lemma exists_polynomial_eval_eq
    {ι : Type*} [Finite ι] (a c : ι → K) (hwd : ∀ i j, a i = a j → c i = c j) :
    ∃ q : Polynomial K, ∀ i, eval (a i) q = c i := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  let c_fn : K → K := fun d => if h : ∃ i, a i = d then c h.choose else 0
  have hinj : Set.InjOn (fun d : K => d) (Finset.univ.image a) :=
    Set.injOn_of_injective Function.injective_id
  have hc_fn : ∀ i, c_fn (a i) = c i := fun i => by
    have h : ∃ j, a j = a i := ⟨i, rfl⟩
    change (if h : ∃ j, a j = a i then c h.choose else 0) = c i
    rw [dif_pos h]
    exact hwd _ _ h.choose_spec
  refine ⟨Lagrange.interpolate (Finset.univ.image a) (fun d : K => d) c_fn, fun i => ?_⟩
  have hmem : a i ∈ Finset.univ.image a := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  rw [Lagrange.eval_interpolate_at_node c_fn hinj hmem, hc_fn]

lemma exists_polynomial_eval_sub [CharZero K]
    {ι : Type*} [Finite ι] {E : Submodule ℚ K}
    (a : ι → K) (ha : ∀ i, a i ∈ E) (f : E →ₗ[ℚ] ℚ) :
    ∃ r : Polynomial K, ∀ i j, eval (a i - a j) r =
      algebraMap ℚ K (f ⟨a i, ha i⟩) - algebraMap ℚ K (f ⟨a j, ha j⟩) := by
  have hwd : ∀ ij kl : ι × ι, a ij.1 - a ij.2 = a kl.1 - a kl.2 →
      algebraMap ℚ K (f ⟨a ij.1, ha ij.1⟩) - algebraMap ℚ K (f ⟨a ij.2, ha ij.2⟩) =
      algebraMap ℚ K (f ⟨a kl.1, ha kl.1⟩) - algebraMap ℚ K (f ⟨a kl.2, ha kl.2⟩) := by
    rintro ⟨i, j⟩ ⟨k, l⟩ hij
    have heq : (⟨a i, ha i⟩ - ⟨a j, ha j⟩ : E) = ⟨a k, ha k⟩ - ⟨a l, ha l⟩ := Subtype.ext hij
    rw [← (algebraMap ℚ K).map_sub, ← (algebraMap ℚ K).map_sub, ← map_sub, ← map_sub, heq]
  obtain ⟨r, hr⟩ := exists_polynomial_eval_eq _ _ hwd
  exact ⟨r, fun i j => hr (i, j)⟩

end Lagrange

end NilpotentOfTrace

namespace LieModule

open Algebra LieAlgebra LinearMap Module Module.End NilpotentOfTrace Polynomial
/-- If the trace form of `M` vanishes identically and `x ∈ ⁅L, L⁆`, then `x` acts nilpotently
on `M`. -/
theorem isNilpotent_toEnd_of_traceForm_eq_zero_algClosed {K L M : Type*}
    [Field K] [CharZero K] [IsAlgClosed K]
    [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M]
    (h : traceForm K L M = 0) (x : L) (hx : x ∈ (derivedSeries K L 1 : Submodule K L)) :
    _root_.IsNilpotent (toEnd K L M x) := by
  set X : Module.End K M := toEnd K L M x with hX_def
  rcases eq_or_ne X 0 with hX_zero | hX_ne
  · rw [hX_zero]; exact IsNilpotent.zero
  obtain ⟨n, hn_adj, s, hs_adj, hn_nil, hs_ss, hX_ns⟩ := X.exists_isNilpotent_isSemisimple
  classical
  let eigenDecomp := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    s.eigenspaces_iSupIndep hs_ss.iSup_eigenspace_eq_top
  let v := eigenDecomp.collectedBasis (fun μ => finBasis K (s.eigenspace μ))
  let μ : (Σ ν, Fin (finrank K (s.eigenspace ν))) → K := fun i => i.1
  have hv_diag : ∀ i, s (v i) = μ i • v i := fun i =>
    mem_eigenspace_iff.mp (eigenDecomp.collectedBasis_mem _ i)
  let E : Submodule ℚ K := Submodule.span ℚ (Set.range μ)
  suffices hs_zero : s = 0 by rw [hX_ns, hs_zero, add_zero]; exact hn_nil
  suffices hf_zero : ∀ f : Module.Dual ℚ E, f = 0 by
    have : Subsingleton E := (subsingleton_dual_iff ℚ).mp
      ⟨fun a b => by rw [hf_zero a, hf_zero b]⟩
    refine hs_ss.eq_zero_iff_forall_eigenvalue.mpr fun ν hν => ?_
    have : Nontrivial (s.eigenspace ν) :=
      Submodule.nontrivial_iff_ne_bot.mpr (hasEigenvalue_iff.mp hν)
    have hν_E : ν ∈ E := Submodule.subset_span ⟨⟨ν, ⟨0, finrank_pos⟩⟩, rfl⟩
    simpa using Subsingleton.elim (⟨ν, hν_E⟩ : E) 0
  intro f
  have hμ : ∀ i, μ i ∈ E := fun i => Submodule.subset_span (Set.mem_range_self i)
  have : Fintype (Σ ν, Fin (finrank K (s.eigenspace ν))) :=
    v.fintypeIndexOfRankLtAleph0 (rank_lt_aleph0 K M)
  let c := fun i => algebraMap ℚ K (f ⟨μ i, hμ i⟩)
  let y : Module.End K M := Matrix.toLin v v (Matrix.diagonal c)
  have hy_diag : ∀ i, y (v i) = c i • v i := fun i =>
    mem_eigenspace_iff.mp (hasEigenvector_toLin_diagonal c i v).1
  have had_s : ∀ i j, ⁅s, v.end (i, j)⁆ = (μ i - μ j) • v.end (i, j) := ad_diag_basis v μ s hv_diag
  have had_y : ∀ i j, ⁅y, v.end (i, j)⁆ = (c i - c j) • v.end (i, j) := ad_diag_basis v c y hy_diag
  obtain ⟨r, hr_eval⟩ := exists_polynomial_eval_sub μ hμ f
  let ad_X := ad K (Module.End K M) X
  let ad_s := ad K (Module.End K M) s
  let ad_y := ad K (Module.End K M) y
  have hns_comm : Commute n s :=
    commute_of_mem_adjoin_singleton_of_commute hs_adj (commute_of_mem_adjoin_self hn_adj).symm
  have h_ad_s_mem : ad_s ∈ K[ad_X] := by
    have h := ad_mem_adjoin_of_isSemisimple hns_comm hn_nil hs_ss
    rwa [← hX_ns] at h
  obtain ⟨p, hp_eq⟩ := adjoin_mem_exists_aeval K ad_X h_ad_s_mem
  let g : LieSubalgebra K (Module.End K M) := (toEnd K L M).range
  have hxg : ∀ b ∈ g, ⁅X, b⁆ ∈ g := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⁅x, b⁆, LieHom.map_lie (toEnd K L M) x b⟩
  have hyg : ∀ b ∈ g, ⁅y, b⁆ ∈ g := by
    have had_y_eq : ad_y = aeval ad_s r := by
      apply v.end.ext; intro ⟨i, j⟩
      change ⁅y, v.end (i, j)⁆ = (aeval ad_s r) (v.end (i, j))
      rw [aeval_apply_of_mem_eigenspace (had_s i j), hr_eval i j, had_y i j]
    have had_y_X : ad_y = aeval ad_X (r.comp p) := by
      rw [had_y_eq, hp_eq.symm, ← aeval_comp]
    intro b hb
    change ad_y b ∈ g.toSubmodule
    rw [had_y_X]
    exact aeval_apply_smul_mem_of_le_comap hb (r.comp p) _ fun _ hb' => hxg _ hb'
  have htr_xy : trace K M (X * y) = 0 := by
    have hcomm : ∀ a b : L, trace K M (toEnd K L M ⁅a, b⁆ * y) = 0 := fun a b => by
      obtain ⟨c, hbc⟩ := hyg (toEnd K L M b) ((toEnd K L M).mem_range_self b)
      have hbc' : ⁅toEnd K L M b, y⁆ = -toEnd K L M c := calc
        _ = -⁅y, toEnd K L M b⁆ := (lie_skew _ _).symm
        _ = -toEnd K L M c := neg_inj.mpr hbc.symm
      rw [LieHom.map_lie]
      refine (trace_lie_mul_eq _ _ _).trans ?_
      rw [hbc', mul_neg, map_neg, neg_eq_zero, mul_eq_comp, ← traceForm_apply_apply, h]
      simp
    rw [hX_def]
    obtain ⟨coef, t, hts, _, hxeq⟩ := Submodule.mem_span_iff_exists_finset_subset.mp
      ((LieSubmodule.lieIdeal_oper_eq_linear_span' (⊤ : LieIdeal K L) ⊤).le hx)
    simp only [← hxeq, map_sum, Finset.sum_mul, map_smul, smul_mul_assoc, smul_eq_mul]
    refine Finset.sum_eq_zero fun z hz => ?_
    obtain ⟨a, _, b, _, rfl⟩ := hts hz
    rw [hcomm a b, mul_zero]
  have hny_comm : Commute n y := by
    have hy_adj : y ∈ K[s] := by
      rw [adjoin_singleton_eq_range_aeval]
      obtain ⟨q, hq⟩ := exists_polynomial_eval_eq μ c fun i j hij => by
        have heq : (⟨μ i, hμ i⟩ : E) = ⟨μ j, hμ j⟩ := Subtype.ext hij
        change algebraMap ℚ K (f ⟨μ i, hμ i⟩) = algebraMap ℚ K (f ⟨μ j, hμ j⟩)
        rw [heq]
      refine ⟨q, v.ext fun i => ?_⟩
      change (aeval s q) (v i) = y (v i)
      rw [aeval_apply_of_mem_eigenspace (hv_diag i), hq i, hy_diag i]
    exact commute_of_mem_adjoin_singleton_of_commute hy_adj hns_comm
  have htr_ny : trace K M (n * y) = 0 :=
    (isNilpotent_trace_of_isNilpotent (hny_comm.isNilpotent_mul_right hn_nil)).eq_zero
  have htr_sy : trace K M (s * y) = ∑ i, μ i * c i := by
    rw [trace_eq_matrix_trace (b := v), Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.diag, toMatrix_apply, mul_apply, hy_diag i, map_smul, hv_diag i, smul_smul,
      mul_comm (c i)]
  have htr_sum : ∑ i : (Σ ν, Fin (finrank K (s.eigenspace ν))), μ i * c i = 0 := by
    rw [← htr_sy, ← htr_xy, hX_ns, add_mul, map_add, htr_ny, zero_add]
  have h_sum_sq : ∑ i : (Σ ν, Fin (finrank K (s.eigenspace ν))), f ⟨μ i, hμ i⟩ ^ 2 = 0 := by
    have h_sum_E : ∑ i, (f ⟨μ i, hμ i⟩) • (⟨μ i, hμ i⟩ : E) = 0 := by
      apply_fun E.subtype using Subtype.val_injective
      simp only [map_sum, map_smul, map_zero, Submodule.subtype_apply]
      exact (Finset.sum_congr rfl fun i _ => by rw [smul_def, mul_comm]).trans htr_sum
    have h : f (∑ i, (f ⟨μ i, hμ i⟩) • (⟨μ i, hμ i⟩ : E)) = 0 := by rw [h_sum_E, map_zero]
    simp only [map_sum, map_smul, smul_eq_mul] at h
    simpa [sq] using h
  have h_each_zero : ∀ i, f ⟨μ i, hμ i⟩ = 0 := by
    intro i
    have h_nonneg : ∀ j ∈ Finset.univ, 0 ≤ f ⟨μ j, hμ j⟩ ^ 2 := fun j _ => sq_nonneg _
    have h_sq_zero := (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h_sum_sq i (Finset.mem_univ _)
    exact eq_zero_of_pow_eq_zero h_sq_zero
  rw [Submodule.linearMap_eq_zero_iff_of_eq_span f rfl]
  rintro ⟨_, ⟨i, rfl⟩⟩
  exact h_each_zero i

end LieModule
