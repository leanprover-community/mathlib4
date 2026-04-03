/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Lie.AdjointAction.JordanChevalley
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Trace

/-!
# Trace-nilpotency criterion

Given subspaces `A ≤ B` of `Module.End K V` and the set
`M = {x ∈ Module.End K V | ∀ b ∈ B, ⁅x, b⁆ ∈ A}`, any `x ∈ M` that is trace-orthogonal to all
of `M` is nilpotent. This is the key technical lemma behind Cartan's criterion for semisimplicity.

## Main results

* `isNilpotent_of_trace_orthogonal_algClosed`: if `K` is an algebraically closed field of
  characteristic zero and `V` is finite-dimensional, then any `x ∈ M` satisfying
  `LinearMap.trace K V (x * y) = 0` for all `y ∈ M` is nilpotent.

## References

* [J. Humphreys, *Introduction to Lie Algebras and Representation Theory*] Chapter 4
-/

@[expose] public section

namespace NilpotentOfTrace

open LinearMap Module.End Polynomial

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- The set `M = {x ∈ Module.End K V | ∀ b ∈ B, ⁅x, b⁆ ∈ A}`. -/
abbrev M (A B : Submodule K (Module.End K V)) : Set (Module.End K V) := {x | ∀ b ∈ B, ⁅x, b⁆ ∈ A}

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

section Lagrange

variable {K : Type*} [Field K] [CharZero K]

lemma exists_polynomial_eval_sub
    {ι : Type*} [Finite ι]
    (a : ι → K) (E : Submodule ℚ K) (f : E →ₗ[ℚ] ℚ)
    (ha : ∀ i, a i ∈ E) :
    ∃ r : Polynomial K,
      (∀ i j, eval (a i - a j) r =
        algebraMap ℚ K (f ⟨a i, ha i⟩) - algebraMap ℚ K (f ⟨a j, ha j⟩)) ∧ eval 0 r = 0 := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  let diffs := insert 0 (Finset.univ.image fun (i, j) => a i - a j)
  let g : K → K := fun d => if hd : d ∈ E then algebraMap ℚ K (f ⟨d, hd⟩) else 0
  have hinj : Set.InjOn (fun d : K => d) diffs := Set.injOn_of_injective Function.injective_id
  have hg : ∀ d (hd : d ∈ E), g d = algebraMap ℚ K (f ⟨d, hd⟩) := fun _ hd => dif_pos hd
  have hmem : ∀ i j, a i - a j ∈ diffs :=
    fun i j => Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
  refine ⟨Lagrange.interpolate diffs (fun d : K => d) g, fun i j => ?_, ?_⟩
  · rw [Lagrange.eval_interpolate_at_node g hinj (hmem i j), hg _ (E.sub_mem (ha i) (ha j))]
    change algebraMap ℚ K (f (⟨a i, ha i⟩ - ⟨a j, ha j⟩)) = _
    rw [map_sub, map_sub]
  · rw [Lagrange.eval_interpolate_at_node g hinj (Finset.mem_insert_self 0 _), hg _ E.zero_mem]
    change algebraMap ℚ K (f 0) = 0
    rw [map_zero, map_zero]

end Lagrange

end NilpotentOfTrace

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

open Algebra LieAlgebra LinearMap Module.End NilpotentOfTrace Polynomial in
/-- If `x ∈ M A B` is trace-orthogonal to all of `M A B`, then `x` is nilpotent. -/
theorem isNilpotent_of_trace_orthogonal_algClosed
    (A B : Submodule K (Module.End K V))
    (hAB : A ≤ B)
    (x : Module.End K V)
    (hxM : x ∈ M A B)
    (htr : ∀ y ∈ M A B, trace K V (x * y) = 0) :
    IsNilpotent x := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact IsNilpotent.zero
  obtain ⟨n, hn_adj, s, hs_adj, hn_nil, hs_ss, hxns⟩ := x.exists_isNilpotent_isSemisimple
  classical
  let eigenDecomp := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    s.eigenspaces_iSupIndep hs_ss.iSup_eigenspace_eq_top
  let v := eigenDecomp.collectedBasis (fun μ => Module.finBasis K (s.eigenspace μ))
  let a : (Σ μ : K, Fin (Module.finrank K (s.eigenspace μ))) → K := fun i => i.1
  have hv_diag : ∀ i, s (v i) = a i • v i := fun i =>
    mem_eigenspace_iff.mp (eigenDecomp.collectedBasis_mem _ i)
  let E : Submodule ℚ K := Submodule.span ℚ (Set.range a)
  suffices hs_zero : s = 0 by rw [hxns, hs_zero, add_zero]; exact hn_nil
  suffices h_f_zero : ∀ f : E →ₗ[ℚ] ℚ, f = 0 by
    have : Subsingleton E :=
      (Module.subsingleton_dual_iff ℚ).mp ⟨fun a b => by rw [h_f_zero a, h_f_zero b]⟩
    refine hs_ss.eq_zero_iff_forall_eigenvalue.mpr fun μ hμ => ?_
    have : Nontrivial (s.eigenspace μ) :=
      Submodule.nontrivial_iff_ne_bot.mpr (hasEigenvalue_iff.mp hμ)
    have hμ_E : μ ∈ E := Submodule.subset_span ⟨⟨μ, ⟨0, Module.finrank_pos⟩⟩, rfl⟩
    simpa using Subsingleton.elim (⟨μ, hμ_E⟩ : E) 0
  intro f
  have ha : ∀ i, a i ∈ E := fun i => Submodule.subset_span (Set.mem_range_self i)
  have : Fintype (Σ μ : K, Fin (Module.finrank K (s.eigenspace μ))) :=
    v.fintypeIndexOfRankLtAleph0 (Module.rank_lt_aleph0 K V)
  let c := fun i => algebraMap ℚ K (f ⟨a i, ha i⟩)
  let y := Matrix.toLin v v (Matrix.diagonal c)
  have hy_diag : ∀ i, y (v i) = c i • v i := fun i =>
    mem_eigenspace_iff.mp (hasEigenvector_toLin_diagonal c i v).1
  have had_s : ∀ i j, ⁅s, v.end (i, j)⁆ = (a i - a j) • v.end (i, j) := ad_diag_basis v a s hv_diag
  have had_y : ∀ i j, ⁅y, v.end (i, j)⁆ = (c i - c j) • v.end (i, j) := ad_diag_basis v _ y hy_diag
  obtain ⟨r, hr_eval, hr_zero⟩ := exists_polynomial_eval_sub a E f ha
  let ad_s := ad K (Module.End K V) s
  have had_y_eq : ad K (Module.End K V) y = aeval ad_s r := by
    apply v.end.ext; intro ⟨i, j⟩
    change ⁅y, v.end (i, j)⁆ = (aeval ad_s r) (v.end (i, j))
    rw [Module.End.aeval_apply_of_mem_eigenspace (had_s i j), hr_eval i j, had_y i j]
  have hns_comm : Commute n s :=
    commute_of_mem_adjoin_singleton_of_commute hs_adj
      (commute_of_mem_adjoin_self hn_adj).symm
  have h_ad_s_mem : ad_s ∈ adjoin K {ad K _ x} := by
    rw [hxns]; exact ad_mem_adjoin_of_isSemisimple hns_comm hn_nil hs_ss
  rw [adjoin_singleton_eq_range_aeval] at h_ad_s_mem
  obtain ⟨p, hp_eq⟩ := h_ad_s_mem
  have hp_zero : eval 0 p = 0 := eval_zero_of_aeval_ad_eq hx
    (commute_of_mem_adjoin_self hs_adj).symm hp_eq.symm
  have hyM : y ∈ M A B := by
    have hp_ad_s : ad_s = aeval (ad K _ x) p := hp_eq.symm
    have had_y_adx : ad K _ y = aeval (ad K _ x) (r.comp p) := by
      rw [had_y_eq, hp_ad_s, ← aeval_comp]
    obtain ⟨q', hq'⟩ : X ∣ r.comp p := by
      simpa using dvd_iff_isRoot.mpr
        (show eval 0 (r.comp p) = 0 by simp [eval_comp, hp_zero, hr_zero])
    intro b hb
    change (ad K _ y) b ∈ A
    rw [had_y_adx, hq', map_mul, aeval_X, Module.End.mul_apply]
    exact hxM _ (aeval_apply_smul_mem_of_le_comap hb q' _ fun _ h => hAB (hxM _ h))
  have htr_xy : trace K V (x * y) = 0 := htr y hyM
  have hy_adj : y ∈ adjoin K {s} := by
    rw [adjoin_singleton_eq_range_aeval]
    let g := Lagrange.interpolate (Finset.univ.image a) (fun d : K => d)
      (fun μ => if hμ : μ ∈ E then algebraMap ℚ K (f ⟨μ, hμ⟩) else 0)
    have hg_eval : ∀ i, eval (a i) g = c i := fun i =>
      (Lagrange.eval_interpolate_at_node _ (Set.injOn_of_injective Function.injective_id)
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)).trans (dif_pos (ha i))
    exact ⟨g, v.ext fun i => by
      change (aeval s g) (v i) = y (v i)
      rw [Module.End.aeval_apply_of_mem_eigenspace (hv_diag i), hg_eval i, hy_diag i]⟩
  have hny_comm : Commute n y :=
    commute_of_mem_adjoin_singleton_of_commute hy_adj hns_comm
  have htr_ny : trace K V (n * y) = 0 :=
    (LinearMap.isNilpotent_trace_of_isNilpotent
      (hny_comm.isNilpotent_mul_right hn_nil)).eq_zero
  have htr_sy : trace K V (s * y) = ∑ i, a i * c i := by
    have : s * y = Matrix.toLin v v (Matrix.diagonal (fun i => a i * c i)) :=
      v.ext fun i => by
        simp only [Module.End.mul_apply, hy_diag i, map_smul, hv_diag i, smul_smul, mul_comm (c i)]
        exact (mem_eigenspace_iff.mp
          (hasEigenvector_toLin_diagonal (fun i => a i * c i) i v).1).symm
    rw [this, Matrix.trace_toLin_eq, Matrix.trace_diagonal]
  have htr_sum : ∑ i : (Σ μ : K, Fin (Module.finrank K (s.eigenspace μ))), a i * c i = 0 := by
    rw [← htr_sy, ← htr_xy, hxns, add_mul, map_add, htr_ny, zero_add]
  have h_sum_sq : ∑ i : (Σ μ : K, Fin (Module.finrank K (s.eigenspace μ))),
      f ⟨a i, ha i⟩ ^ 2 = (0 : ℚ) := by
    have h_sum_E : ∑ i, (f ⟨a i, ha i⟩) • (⟨a i, ha i⟩ : E) = 0 := by
      apply_fun E.subtype using Subtype.val_injective
      simp only [map_sum, map_smul, map_zero, Submodule.subtype_apply]
      convert htr_sum using 1; congr 1; ext i; rw [smul_def, mul_comm]
    have := congr_arg f h_sum_E
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at this
    convert this using 1; congr 1; ext i; ring
  have h_each_zero : ∀ i, f ⟨a i, ha i⟩ = 0 := fun i =>
    eq_zero_of_pow_eq_zero ((Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg _)).mp h_sum_sq i (Finset.mem_univ _))
  exact (Submodule.linearMap_eq_zero_iff_of_eq_span f rfl).mpr fun ⟨_, ⟨i, rfl⟩⟩ => h_each_zero i
