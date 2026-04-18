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

If the trace form of a finite-dimensional representation `M` of a Lie algebra `L` is zero,
then the `⁅L, L⁆`-module `M` is nilpotent. This is the key technical lemma behind Cartan's
criterion.

## Main results

* `LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero_algClosed`: over an algebraically
  closed field of characteristic zero, if a finite-dimensional representation `M` of `L` satisfies
  `traceForm K L M = 0`, then the `⁅L, L⁆`-module `M` is nilpotent.

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975) Chapter I. §5.4
* [J. Humphreys, *Introduction to Lie Algebras and ...*](humphreys1972) Chapter II 4.3
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
  · exact aeval_apply_of_hasEigenvector ⟨mem_eigenspace_iff.mpr hx, hne⟩

lemma ad_diag_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (a : ι → K) (s : Module.End K V)
    (hs : ∀ k, s (b k) = a k • b k) (i j : ι) :
    ⁅s, b.end (i, j)⁆ = (a i - a j) • b.end (i, j) := by
  refine b.ext fun k ↦ ?_
  simp only [LieHom.lie_apply, lie_apply, smul_apply, Module.Basis.end_apply_apply, hs k, map_smul]
  by_cases hjk : j = k
  · subst hjk; simp [hs i, sub_smul]
  · simp [hjk]

section Lagrange

lemma exists_polynomial_eval_eq
    {ι : Type*} [Finite ι] (a c : ι → K) (hwd : ∀ i j, a i = a j → c i = c j) :
    ∃ q : Polynomial K, ∀ i, eval (a i) q = c i := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  let c_fn : K → K := fun d ↦ if h : ∃ i, a i = d then c h.choose else 0
  have hinj : Set.InjOn (fun d : K ↦ d) (Finset.univ.image a) :=
    Set.injOn_of_injective Function.injective_id
  have hc_fn : ∀ i, c_fn (a i) = c i := fun i ↦ by
    have h : ∃ j, a j = a i := ⟨i, rfl⟩
    change (if h : ∃ j, a j = a i then c h.choose else 0) = c i
    rw [dif_pos h]
    exact hwd _ _ h.choose_spec
  refine ⟨Lagrange.interpolate (Finset.univ.image a) (fun d : K ↦ d) c_fn, fun i ↦ ?_⟩
  have hmem : a i ∈ Finset.univ.image a := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  rw [Lagrange.eval_interpolate_at_node c_fn hinj hmem, hc_fn]

lemma exists_polynomial_eval_sub [CharZero K]
    {ι : Type*} [Finite ι] {E : Submodule ℚ K}
    (a : ι → K) (ha : ∀ i, a i ∈ E) (f : E →ₗ[ℚ] ℚ) :
    ∃ r : Polynomial K, ∀ i j, eval (a i - a j) r = f ⟨a i, ha i⟩ - f ⟨a j, ha j⟩ := by
  have hwd : ∀ ij kl : ι × ι, a ij.1 - a ij.2 = a kl.1 - a kl.2 →
      algebraMap ℚ K (f ⟨a ij.1, ha ij.1⟩) - algebraMap ℚ K (f ⟨a ij.2, ha ij.2⟩) =
      algebraMap ℚ K (f ⟨a kl.1, ha kl.1⟩) - algebraMap ℚ K (f ⟨a kl.2, ha kl.2⟩) := by
    rintro ⟨i, j⟩ ⟨k, l⟩ hij
    have heq : (⟨a i, ha i⟩ - ⟨a j, ha j⟩ : E) = ⟨a k, ha k⟩ - ⟨a l, ha l⟩ := Subtype.ext hij
    rw [← (algebraMap ℚ K).map_sub, ← (algebraMap ℚ K).map_sub, ← map_sub, ← map_sub, heq]
  obtain ⟨r, hr⟩ := exists_polynomial_eval_eq _ _ hwd
  exact ⟨r, fun i j ↦ hr (i, j)⟩

end Lagrange

end NilpotentOfTrace

namespace LieModule

variable {K L M : Type*}
  [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M]

local notation "φ" => toEnd K L M

open Algebra LieAlgebra LinearMap Module Module.End NilpotentOfTrace Polynomial

/-- If the trace form of `M` is zero, then the `⁅L, L⁆`-module `M` is nilpotent. -/
theorem isNilpotent_derivedSeries_of_traceForm_eq_zero_algClosed (h : traceForm K L M = 0) :
    IsNilpotent (derivedSeries K L 1) M := by
  /- By Engel's theorem it suffices to prove that `⁅L, L⁆` acts nilpotently on `M`. -/
  suffices ∀ x ∈ derivedSeries K L 1, _root_.IsNilpotent (φ x) from
    isNilpotent_iff_forall'.mpr fun ⟨x, hx⟩ ↦ this x hx
  intro x hx
  /- Using Jordan-Chevalley, let `s` and `n` be the semisimple and nilpotent parts of `φ x`. -/
  obtain ⟨n, hn_adj, s, hns, hn_nil, hs_ss, hX_ns⟩ := (φ x).exists_isNilpotent_isSemisimple
  replace hns : Commute n s :=
    commute_of_mem_adjoin_singleton_of_commute hns (commute_of_mem_adjoin_self hn_adj).symm
  /- It suffices to prove `s = 0`. -/
  suffices s = 0 by aesop
  classical
  /- Decompose `M` as a direct sum of eigenspaces of `s`. -/
  let eigenDecomp := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    s.eigenspaces_iSupIndep hs_ss.iSup_eigenspace_eq_top
  let I := (ν : K) × Fin (finrank K (s.eigenspace ν))
  let v : Basis I K M := eigenDecomp.collectedBasis fun μ ↦ finBasis K (s.eigenspace μ)
  have : Fintype I := v.fintypeIndexOfRankLtAleph0 (rank_lt_aleph0 K M)
  let μ : I → K := Sigma.fst
  have hsv (i : I) : s (v i) = μ i • v i :=
    mem_eigenspace_iff.mp (eigenDecomp.collectedBasis_mem _ i)
  /- Let `E ⊆ K` be the `ℚ`-submodule of scalars spanned by the eigenvalues of `s`. -/
  let E : Submodule ℚ K := Submodule.span ℚ (Set.range μ)
  have hμ (i : I) : μ i ∈ E := Submodule.subset_span (Set.mem_range_self i)
  /- It suffices to prove that the `ℚ`-dual of `E` is trivial.  This can be regarded as a trick to
     handle the fact that our scalars `K` are not ordered. -/
  suffices ∀ f : Dual ℚ E, f = 0 by
    suffices ∀ ν, s.HasEigenvalue ν → ν = 0 from hs_ss.eq_zero_iff_forall_eigenvalue.mpr this
    intro ν hν
    have : Nontrivial (s.eigenspace ν) :=
      Submodule.nontrivial_iff_ne_bot.mpr (hasEigenvalue_iff.mp hν)
    replace hν : ν ∈ E := Submodule.subset_span ⟨⟨ν, ⟨0, finrank_pos⟩⟩, rfl⟩
    have : Subsingleton E := (subsingleton_dual_iff ℚ).mp ⟨by aesop⟩
    simpa using Subsingleton.elim (⟨ν, hν⟩ : E) 0
  intro f
  /- It suffices to show that any `f : Dual ℚ E` vanishes on all the eigenvalues of `s`. -/
  suffices ∀ i, f ⟨μ i, hμ i⟩ = 0 by
    rw [Submodule.linearMap_eq_zero_iff_of_eq_span f rfl]
    rintro ⟨-, ⟨i, rfl⟩⟩
    exact this i
  /- We will deduce this by proving that the sum of the squares of all such values vanishes. -/
  suffices ∑ i, f ⟨μ i, hμ i⟩ ^ 2 = 0 from fun i ↦ eq_zero_of_pow_eq_zero <|
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ sq_nonneg _)).mp this i (Finset.mem_univ _)
  /- Which will follow from the fact that the following `f`-linear expression vanishes. -/
  suffices ∑ i, (f ⟨μ i, hμ i⟩) • (⟨μ i, hμ i⟩ : E) = 0 by
    simpa only [map_sum, map_zero, map_smul, sq] using f.congr_arg this
  let fμ (i : I) : K := f ⟨μ i, hμ i⟩
  /- Defining `fμ i = f ⟨μ i, hμ i⟩`, we can restate our goal as `∑ i, fμ i * μ i = 0`. -/
  suffices ∑ i, fμ i * μ i = 0 by simp [Subtype.ext_iff, fμ, ← this, Algebra.smul_def]
  /- We will do this by constructing endomorphism `y` such that `trace K M (φ x * y) = 0` and also
     `trace K M (φ x * y) = ∑ i, fμ i * μ i`. -/
  suffices ∃ y : End K M, trace K M (φ x * y) = 0 ∧ trace K M (φ x * y) = ∑ i, fμ i * μ i by grind
  /- We define `y` diagonal wrt our basis `v` and takes the values `fμ` on the diagonal. -/
  let y : End K M := (Matrix.diagonal fμ).toLin v v
  have hy (i : I) : y (v i) = fμ i • v i :=
    mem_eigenspace_iff.mp (hasEigenvector_toLin_diagonal fμ i v).1
  /- Using Lagrange interpolation, we can show that the representation is stable under `y`. -/
  have hy_range (z : End K M) (hz : z ∈ LieHom.range φ) : ⁅y, z⁆ ∈ LieHom.range φ := by
    obtain ⟨q, hq⟩ : ∃ q : K[X], q.aeval (ad K _ (φ x)) = ad K _ y := by
      obtain ⟨r, hr⟩ : ∃ r : K[X], r.aeval (ad K _ s) = ad K _ y := by
        have h₁ : ∀ i j, ⁅s, v.end (i, j)⁆ = (μ i - μ j) • v.end (i, j) := ad_diag_basis v μ s hsv
        have h₂ : ∀ i j, ⁅y, v.end (i, j)⁆ = (fμ i - fμ j) • v.end (i, j) := ad_diag_basis v fμ y hy
        obtain ⟨r, hr⟩ := exists_polynomial_eval_sub μ hμ f
        refine ⟨r, v.end.ext fun ⟨i, j⟩ ↦ ?_⟩
        rw [ad_apply, ← instLieRingModule_eq, aeval_apply_of_mem_eigenspace (h₁ i j), hr, h₂]
      obtain ⟨p, hp⟩ : ∃ p : K[X], p.aeval (ad K _ (φ x)) = ad K _ s :=
        adjoin_mem_exists_aeval K _ <| by
          simpa only [← hX_ns] using ad_mem_adjoin_of_isSemisimple hns hn_nil hs_ss
      exact ⟨r.comp p, by rw [aeval_comp, hp, hr]⟩
    rw [instLieRingModule_eq, ← ad_apply K, ← hq]
    apply q.aeval_apply_smul_mem_of_le_comap hz _ ?_
    rintro - ⟨w, rfl⟩
    exact ⟨⁅x, w⁆, LieHom.map_lie φ x w⟩
  /- Using Lagrange interpolation again we can show that `n` and `y` commute. -/
  have hny_comm : Commute n y := by
    suffices y ∈ K[s] from commute_of_mem_adjoin_singleton_of_commute this hns
    rw [adjoin_singleton_eq_range_aeval]
    obtain ⟨q, hq⟩ : ∃ q : K[X], ∀ i, q.eval (μ i) = fμ i :=
      exists_polynomial_eval_eq μ fμ <| by aesop
    refine ⟨q, v.ext fun i ↦ ?_⟩
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_apply_of_mem_eigenspace (hsv i), hq, hy]
  /- By general results we need only prove `trace K M (φ x * y) = ∑ i, fμ i * μ i`. -/
  suffices trace K M (φ x * y) = ∑ i, fμ i * μ i from
    ⟨y, trace_toEnd_mul_eq_zero_of_traceForm_eq_zero h y hy_range x hx, this⟩
  /- And this is an easy calculation. -/
  have h₁ : trace K M (n * y) = 0 :=
    (isNilpotent_trace_of_isNilpotent (hny_comm.isNilpotent_mul_right hn_nil)).eq_zero
  have h₂ : trace K M (s * y) = ∑ i, fμ i * μ i := by
    rw [trace_eq_matrix_trace _ v, Matrix.trace]
    exact Finset.sum_congr rfl <| by simp [toMatrix_apply, hy, hsv]
  rw [hX_ns, add_mul, map_add, h₁, h₂, zero_add]

end LieModule
