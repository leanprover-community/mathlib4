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
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Trace

/-!
# Trace-nilpotency criterion

For a Lie ideal `I` contained in the kernel of `LieModule.traceForm K L M`, every element
`x ∈ I ⊓ ⁅L, L⁆` acts nilpotently on `M`. This is the key technical lemma behind Cartan's
criterion for solvability.

## Main results

* `LieModule.isNilpotent_toEnd_of_mem_ker_traceForm`: if `K` is an algebraically closed field of
  characteristic zero and `M` is a finite-dimensional `L`-module, then any `x` lying in a Lie
  ideal `I ≤ (traceForm K L M).ker` and in `⁅L, L⁆` acts nilpotently on `M`.

## References

* [J. Humphreys, *Introduction to Lie Algebras and Representation Theory*] Section 4.3
-/

@[expose] public section

namespace NilpotentOfTrace

open LinearMap Module.End Polynomial

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

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

namespace LieModule

open Algebra LieAlgebra LinearMap Module Module.End NilpotentOfTrace Polynomial
/-- If `I` is a Lie ideal contained in the kernel of `traceForm K L M`, then every
`x ∈ I ⊓ ⁅L, L⁆` acts nilpotently on `M`. -/
theorem isNilpotent_toEnd_of_mem_ker_traceForm {K L M : Type*}
    [Field K] [CharZero K] [IsAlgClosed K]
    [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M]
    (I : LieIdeal K L) (hI : I ≤ (traceForm K L M).ker)
    (x : L) (hx : x ∈ I ⊓ LieAlgebra.derivedSeries K L 1) :
    _root_.IsNilpotent (toEnd K L M x) := by
  obtain ⟨hxI, hx_der⟩ := (LieSubmodule.mem_inf (N := I) (N' := derivedSeries K L 1) x).mp hx
  set X : Module.End K M := toEnd K L M x with hX_def
  rcases eq_or_ne X 0 with hX0 | hX_ne
  · rw [hX0]; exact IsNilpotent.zero
  obtain ⟨n, hn_adj, s, hs_adj, hn_nil, hs_ss, hX_ns⟩ := X.exists_isNilpotent_isSemisimple
  classical
  let eigenDecomp := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    s.eigenspaces_iSupIndep hs_ss.iSup_eigenspace_eq_top
  let v := eigenDecomp.collectedBasis (fun μ => Module.finBasis K (s.eigenspace μ))
  let a : (Σ μ, Fin (Module.finrank K (s.eigenspace μ))) → K := fun i => i.1
  have hv_diag : ∀ i, s (v i) = a i • v i := fun i =>
    mem_eigenspace_iff.mp (eigenDecomp.collectedBasis_mem _ i)
  let E : Submodule ℚ K := Submodule.span ℚ (Set.range a)
  suffices hs_zero : s = 0 by rw [hX_ns, hs_zero, add_zero]; exact hn_nil
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
  have : Fintype (Σ μ, Fin (Module.finrank K (s.eigenspace μ))) :=
    v.fintypeIndexOfRankLtAleph0 (Module.rank_lt_aleph0 K M)
  let c := fun i => algebraMap ℚ K (f ⟨a i, ha i⟩)
  let y : Module.End K M := Matrix.toLin v v (Matrix.diagonal c)
  have hy_diag : ∀ i, y (v i) = c i • v i := fun i =>
    mem_eigenspace_iff.mp (hasEigenvector_toLin_diagonal c i v).1
  have had_s : ∀ i j, ⁅s, v.end (i, j)⁆ = (a i - a j) • v.end (i, j) := ad_diag_basis v a s hv_diag
  have had_y : ∀ i j, ⁅y, v.end (i, j)⁆ = (c i - c j) • v.end (i, j) := ad_diag_basis v c y hy_diag
  obtain ⟨r, hr_eval, hr_zero⟩ := exists_polynomial_eval_sub a E f ha
  let ad_s := ad K (Module.End K M) s
  have had_y_eq : ad K (Module.End K M) y = aeval ad_s r := by
    apply v.end.ext; intro ⟨i, j⟩
    change ⁅y, v.end (i, j)⁆ = (aeval ad_s r) (v.end (i, j))
    rw [Module.End.aeval_apply_of_mem_eigenspace (had_s i j), hr_eval i j, had_y i j]
  have hns_comm : Commute n s :=
    commute_of_mem_adjoin_singleton_of_commute hs_adj (commute_of_mem_adjoin_self hn_adj).symm
  have h_ad_s_mem : ad_s ∈ adjoin K {ad K _ X} := by
    rw [hX_ns]; exact ad_mem_adjoin_of_isSemisimple hns_comm hn_nil hs_ss
  rw [adjoin_singleton_eq_range_aeval] at h_ad_s_mem
  obtain ⟨p, hp_eq⟩ := h_ad_s_mem
  have hp_zero : eval 0 p = 0 := eval_zero_of_aeval_ad_eq hX_ne
    (commute_of_mem_adjoin_self hs_adj).symm hp_eq.symm
  let A : Submodule K (Module.End K M) := Submodule.map (toEnd K L M).toLinearMap I
  let B : Submodule K (Module.End K M) := LinearMap.range (toEnd K L M).toLinearMap
  have hAB : A ≤ B := fun _ ⟨c, _, h⟩ => ⟨c, h⟩
  have hxM : ∀ b ∈ B, ⁅X, b⁆ ∈ A := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⁅x, b⁆, lie_mem_left K L I x b hxI, LieHom.map_lie (toEnd K L M) x b⟩
  have hyM : ∀ b ∈ B, ⁅y, b⁆ ∈ A := by
    have hp_ad_s : ad_s = aeval (ad K _ X) p := hp_eq.symm
    have had_y_X : ad K _ y = aeval (ad K _ X) (r.comp p) := by
      rw [had_y_eq, hp_ad_s, ← aeval_comp]
    obtain ⟨q', hq'⟩ : (Polynomial.X : K[X]) ∣ r.comp p := by
      rw [X_dvd_iff, coeff_zero_eq_eval_zero, eval_comp, hp_zero, hr_zero]
    intro b hb
    change (ad K _ y) b ∈ A
    rw [had_y_X, hq', map_mul, aeval_X, Module.End.mul_apply]
    exact hxM _ (aeval_apply_smul_mem_of_le_comap hb q' _ fun _ h => hAB (hxM _ h))
  have htr_xy : trace K M (X * y) = 0 := by
    let ψ : L →ₗ[K] K := (trace K M).comp ((mulRight K y).comp (toEnd K L M).toLinearMap)
    suffices h : ψ x = 0 by simpa [ψ, hX_def] using h
    refine (?_ : (LieAlgebra.derivedSeries K L 1 : Submodule K L) ≤ LinearMap.ker ψ) hx_der
    rw [show (LieAlgebra.derivedSeries K L 1 : Submodule K L) = _ from
      LieSubmodule.lieIdeal_oper_eq_linear_span' (⊤ : LieIdeal K L) ⊤, Submodule.span_le]
    rintro _ ⟨a, _, b, _, rfl⟩
    obtain ⟨c, hcI, hbc⟩ := hyM (toEnd K L M b) (LinearMap.mem_range_self _ b)
    have hbc' : ⁅toEnd K L M b, y⁆ = -toEnd K L M c :=
      (lie_skew _ _).symm.trans (congrArg Neg.neg hbc.symm)
    have hcyc : trace K M (⁅toEnd K L M a, toEnd K L M b⁆ * y) =
        trace K M (toEnd K L M a * ⁅toEnd K L M b, y⁆) := by
      simpa [traceForm_apply_apply, ← Module.End.mul_eq_comp] using
        traceForm_apply_lie_apply K (Module.End K M) M (toEnd K L M a) (toEnd K L M b) y
    change trace K M (toEnd K L M ⁅a, b⁆ * y) = 0
    rw [LieHom.map_lie]
    refine hcyc.trans ?_
    rw [hbc', mul_neg, map_neg, neg_eq_zero, Module.End.mul_eq_comp, ← traceForm_apply_apply,
      traceForm_comm]
    exact LinearMap.congr_fun (hI hcI) a
  have hny_comm : Commute n y := by
    have hy_adj : y ∈ adjoin K {s} := by
      rw [adjoin_singleton_eq_range_aeval]
      let c_ext : K → K := fun μ => if hμ : μ ∈ E then algebraMap ℚ K (f ⟨μ, hμ⟩) else 0
      let g := Lagrange.interpolate (Finset.univ.image a) (fun d : K => d) c_ext
      refine ⟨g, v.ext fun i => ?_⟩
      have hg : eval (a i) g = c i := by
        have hmem : a i ∈ Finset.univ.image a := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
        have h := Lagrange.eval_interpolate_at_node c_ext
          (Set.injOn_of_injective Function.injective_id) hmem
        exact h.trans (dif_pos (ha i))
      change (aeval s g) (v i) = y (v i)
      rw [Module.End.aeval_apply_of_mem_eigenspace (hv_diag i), hg, hy_diag i]
    exact commute_of_mem_adjoin_singleton_of_commute hy_adj hns_comm
  have htr_ny : trace K M (n * y) = 0 :=
    (LinearMap.isNilpotent_trace_of_isNilpotent (hny_comm.isNilpotent_mul_right hn_nil)).eq_zero
  have htr_sy : trace K M (s * y) = ∑ i, a i * c i := by
    rw [trace_eq_matrix_trace (b := v), Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.diag, toMatrix_apply, Module.End.mul_apply, hy_diag i, map_smul,
      hv_diag i, smul_smul, mul_comm (c i)]
  have htr_sum : ∑ i : (Σ μ, Fin (Module.finrank K (s.eigenspace μ))), a i * c i = 0 := by
    rw [← htr_sy, ← htr_xy, hX_ns, add_mul, map_add, htr_ny, zero_add]
  have h_sum_sq : ∑ i : (Σ μ, Fin (Module.finrank K (s.eigenspace μ))), f ⟨a i, ha i⟩ ^ 2 = 0 := by
    have h_sum_E : ∑ i, (f ⟨a i, ha i⟩) • (⟨a i, ha i⟩ : E) = 0 := by
      apply_fun E.subtype using Subtype.val_injective
      simp only [map_sum, map_smul, map_zero, Submodule.subtype_apply]
      exact (Finset.sum_congr rfl fun i _ => by rw [smul_def, mul_comm]).trans htr_sum
    have h : f (∑ i, (f ⟨a i, ha i⟩) • (⟨a i, ha i⟩ : E)) = 0 := by rw [h_sum_E, map_zero]
    simp only [map_sum, map_smul, smul_eq_mul] at h
    simpa [sq] using h
  have h_each_zero : ∀ i, f ⟨a i, ha i⟩ = 0 := by
    intro i
    have h_nonneg : ∀ j ∈ Finset.univ, 0 ≤ f ⟨a j, ha j⟩ ^ 2 := fun j _ => sq_nonneg _
    have h_sq_zero := (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h_sum_sq i (Finset.mem_univ _)
    exact eq_zero_of_pow_eq_zero h_sq_zero
  rw [Submodule.linearMap_eq_zero_iff_of_eq_span f rfl]
  rintro ⟨_, ⟨i, rfl⟩⟩
  exact h_each_zero i

end LieModule
