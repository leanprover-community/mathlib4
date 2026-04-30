/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Lie.AdjointAction.JordanChevalley
public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Algebra.Lie.TraceForm
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.Flat.Localization

/-!
# Cartan's criteria

The two **Cartan criteria** characterise solvability and semisimplicity of finite-dimensional
Lie algebras over fields of characteristic zero in terms of the Killing form: solvability
via its vanishing on `L × ⁅L, L⁆`, semisimplicity via its non-degeneracy.

## Main results

* `LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero`: over a field of characteristic zero,
  if a finite-dimensional representation `M` of `L` has trivial trace form, then `M` is nilpotent
  as a `⁅L, L⁆`-module.
* `LieIdeal.isSolvable_of_killingForm_apply_lie_eq_zero`: for an ideal `I` of a
  finite-dimensional Lie algebra `L` over a field of characteristic zero, if the Killing form
  of `L` vanishes on `I × ⁅I, I⁆`, then `I` is solvable. This is one direction of
  **Cartan's criterion for solvability**; the converse is left as a TODO.
* `LieAlgebra.killingCompl_top_le_radical`: the kernel of the Killing form of a finite-dimensional
  Lie algebra over a field of characteristic zero is contained in the solvable radical.
* `LieAlgebra.HasTrivialRadical.instIsKilling`: a finite-dimensional Lie algebra over a field of
  characteristic zero with trivial radical has non-degenerate Killing form. This is one direction
  of **Cartan's criterion for semisimplicity**; the converse is the existing
  `LieAlgebra.IsKilling.instHasTrivialRadical` (which holds in greater generality, over any PID).

## TODO

* The converse direction of `LieIdeal.isSolvable_of_killingForm_apply_lie_eq_zero`, i.e.
  `IsSolvable I → ∀ x ∈ I, ∀ y ∈ ⁅I, I⁆, killingForm K L x y = 0`. Together with the
  sufficient direction it gives the iff form of Cartan's criterion for solvability.

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975) Chapter I. §5.4
* [J. Humphreys, *Introduction to Lie Algebras and ...*](humphreys1972) Chapter II 4.3
-/

namespace LieModule

variable {R K L M : Type*}
  [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M]
  [CommRing R] [CharZero R] [IsDomain R]
  [LieAlgebra R L] [Module R M] [LieModule R L M] [IsNoetherian R M] [Module.Free R M]

local notation "φ" => toEnd K L M

open Algebra Function LieAlgebra LinearMap Module Module.End Polynomial
open scoped TensorProduct

lemma exists_polynomial_eval_sub_aux
    {ι R K : Type*} [Finite ι] [CommRing R] [Field K] [Algebra R K]
    {E : Submodule R K} (a : ι → K) (ha : ∀ i, a i ∈ E) (f : E →+ R) :
    ∃ r : K[X], ∀ i j, r.eval (a i - a j) =
      algebraMap R K (f ⟨a i, ha i⟩) - algebraMap R K (f ⟨a j, ha j⟩) := by
  suffices ∀ (ij kl : ι × ι) (hij : a ij.1 - a ij.2 = a kl.1 - a kl.2),
      algebraMap R K (f ⟨a ij.1, ha ij.1⟩) - algebraMap R K (f ⟨a ij.2, ha ij.2⟩) =
      algebraMap R K (f ⟨a kl.1, ha kl.1⟩) - algebraMap R K (f ⟨a kl.2, ha kl.2⟩) by
    obtain ⟨r, hr⟩ := (Polynomial.exists_eval_eq_iff _ _).mpr this
    exact ⟨r, fun i j ↦ hr (i, j)⟩
  rintro ⟨i, j⟩ ⟨k, l⟩ hij
  have heq : (⟨a i, ha i⟩ - ⟨a j, ha j⟩ : E) = ⟨a k, ha k⟩ - ⟨a l, ha l⟩ := Subtype.ext hij
  rw [← (algebraMap R K).map_sub, ← (algebraMap R K).map_sub, ← map_sub, ← map_sub, heq]

/-- An auxiliary lemma used to prove `LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero`
which proves the same result except without the algebraically closed assumption. -/
theorem isNilpotent_derivedSeries_of_traceForm_eq_zero_aux [IsAlgClosed K]
    (h : traceForm K L M = 0) :
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
  have : Fintype I := FiniteDimensional.fintypeBasisIndex v
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
  suffices ∑ i, fμ i * μ i = 0 by simp [Subtype.ext_iff, fμ, ← this, smul_def]
  /- We will do this by constructing endomorphism `y` such that `trace K M (φ x * y) = 0` and also
     `trace K M (φ x * y) = ∑ i, fμ i * μ i`. -/
  suffices ∃ y : End K M, trace K M (φ x * y) = 0 ∧ trace K M (φ x * y) = ∑ i, fμ i * μ i by grind
  /- We define `y` diagonal wrt our basis `v` and takes the values `fμ` on the diagonal. -/
  let y : End K M := (Matrix.diagonal fμ).toLin v v
  have hyv (i : I) : y (v i) = fμ i • v i :=
    mem_eigenspace_iff.mp (hasEigenvector_toLin_diagonal fμ i v).1
  /- Using Lagrange interpolation, we can show that the representation is stable under `y`. -/
  have hy_range (z : End K M) (hz : z ∈ LieHom.range φ) : ⁅y, z⁆ ∈ LieHom.range φ := by
    obtain ⟨q, hq⟩ : ∃ q : K[X], q.aeval (ad K _ (φ x)) = ad K _ y := by
      obtain ⟨r, hr⟩ : ∃ r : K[X], r.aeval (ad K _ s) = ad K _ y := by
        have h₁ (i j : I) : ⁅s, v.end (i, j)⁆ = (μ i - μ j) • v.end (i, j) := by
          rw [instLieRingModule_eq, v.lie_end_of_apply_eq_smul μ s hsv]
        have h₂ (i j : I) : ⁅y, v.end (i, j)⁆ = (fμ i - fμ j) • v.end (i, j) := by
          rw [instLieRingModule_eq, v.lie_end_of_apply_eq_smul fμ y hyv]
        obtain ⟨r, hr⟩ := exists_polynomial_eval_sub_aux μ hμ f
        refine ⟨r, v.end.ext fun ⟨i, j⟩ ↦ ?_⟩
        rw [ad_apply, ← instLieRingModule_eq, aeval_apply_of_mem_apply_eq_smul (h₁ i j), hr, h₂]
        rfl
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
      (Polynomial.exists_eval_eq_iff μ fμ).mpr <| by aesop
    refine ⟨q, v.ext fun i ↦ ?_⟩
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_apply_of_mem_apply_eq_smul (hsv i), hq, hyv]
  /- By general results we need only prove `trace K M (φ x * y) = ∑ i, fμ i * μ i`. -/
  suffices trace K M (φ x * y) = ∑ i, fμ i * μ i from
    ⟨y, trace_toEnd_mul_eq_zero_of_traceForm_eq_zero h y hy_range x hx, this⟩
  /- And this is an easy calculation. -/
  have htr_n : trace K M (n * y) = 0 :=
    (isNilpotent_trace_of_isNilpotent (hny_comm.isNilpotent_mul_right hn_nil)).eq_zero
  have htr_s : trace K M (s * y) = ∑ i, fμ i * μ i := by
    rw [trace_eq_matrix_trace _ v, Matrix.trace]
    exact Finset.sum_congr rfl <| by simp [toMatrix_apply, hyv, hsv]
  rw [hX_ns, add_mul, map_add, htr_n, htr_s, zero_add]

/-- If the trace form of `M` is zero, then the `⁅L, L⁆`-module `M` is nilpotent. -/
public theorem isNilpotent_derivedSeries_of_traceForm_eq_zero (h : traceForm R L M = 0) :
    IsNilpotent (derivedSeries R L 1) M := by
  set A := AlgebraicClosure (FractionRing R)
  have _i : FaithfulSMul R A := FaithfulSMul.trans R (FractionRing R) A
  have nilp_ext : IsNilpotent (derivedSeries A (A ⊗[R] L) 1) (A ⊗[R] M) :=
    isNilpotent_derivedSeries_of_traceForm_eq_zero_aux <| by simpa
  rw [isNilpotent_iff_forall' (R := R)]
  rw [isNilpotent_iff_forall' (R := A)] at nilp_ext
  intro ⟨x, hx⟩
  have hx_ext : 1 ⊗ₜ[R] x ∈ derivedSeries A (A ⊗[R] L) 1 := by
    rw [derivedSeries_baseChange]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hx
  have hbc_inj : Injective (End.baseChangeHom R A M) := LinearMap.baseChangeHom_injective R M A
  have aux : (toEnd R (derivedSeries R L 1) M ⟨x, hx⟩).baseChangeHom R A M =
      (toEnd R L M x).baseChange A := rfl
  rw [← IsNilpotent.map_iff hbc_inj, aux, ← toEnd_baseChange]
  exact nilp_ext ⟨_, hx_ext⟩

end LieModule

namespace LieIdeal

open LieAlgebra LieModule LinearMap Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]

/-- For an ideal `I` of a finite-dimensional Lie algebra `L` over a field of characteristic zero,
if the Killing form of `L` vanishes on `I × ⁅I, I⁆`, then `I` is solvable. The converse is
left as a TODO; together they give the iff form of **Cartan's criterion for solvability**. -/
public theorem isSolvable_of_killingForm_apply_lie_eq_zero
    (I : LieIdeal K L)
    (h : ∀ x ∈ I, ∀ y ∈ ⁅I, I⁆, killingForm K L x y = 0) :
    IsSolvable I := by
  set DI : LieIdeal K L := ⁅I, I⁆
  set DDI : LieIdeal K L := ⁅DI, DI⁆
  have h_tf : LieModule.traceForm K DI L = 0 := by
    ext ⟨x, hx⟩ ⟨y, hy⟩
    change trace K L ((ad K L) x ∘ₗ (ad K L) y) = 0
    rw [← killingForm_apply_apply]
    exact h x (LieSubmodule.lie_le_left I I hx) y hy
  have key : LieModule.IsNilpotent (LieAlgebra.derivedSeries K DI 1) L :=
    isNilpotent_derivedSeries_of_traceForm_eq_zero h_tf
  rw [isNilpotent_iff_forall' (R := K)] at key
  have ad_nil : ∀ x ∈ (DDI : LieSubmodule K L L).toSubmodule, IsNilpotent (ad K L x) := by
    intro x hx
    have hxDI : x ∈ DI := LieSubmodule.lie_le_left DI DI hx
    have hxDS : (⟨x, hxDI⟩ : DI) ∈ derivedSeries K DI 1 := by
      rw [derivedSeries_eq_derivedSeriesOfIdeal_comap, mem_comap]
      exact hx
    exact key ⟨⟨x, hxDI⟩, hxDS⟩
  have ddi_nilpotent : LieRing.IsNilpotent DDI := by
    have : IsNoetherian K DDI := isNoetherian_submodule' (DDI : LieSubmodule K L L).toSubmodule
    rw [LieAlgebra.isNilpotent_iff_forall (R := K)]
    rintro ⟨x, hx⟩
    rw [show ad K DDI ⟨x, hx⟩ = (ad K L x).restrict fun _ hy ↦ DDI.lie_mem hy from
      by ext ⟨_, _⟩; rfl]
    exact Module.End.isNilpotent.restrict _ (ad_nil x hx)
  obtain ⟨k, hk⟩ := IsSolvable.solvable K DDI
  rw [derivedSeries_eq_bot_iff] at hk
  refine .mk (k := k + 2) ((derivedSeries_eq_bot_iff I (k + 2)).mpr ?_)
  rwa [derivedSeriesOfIdeal_add, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_succ,
    derivedSeriesOfIdeal_zero]

end LieIdeal

namespace LieAlgebra

variable (K L : Type*) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]

/-- The kernel of the Killing form of a finite-dimensional Lie algebra over a field of
characteristic zero is contained in the solvable radical. -/
public lemma killingCompl_top_le_radical :
    LieIdeal.killingCompl K L ⊤ ≤ radical K L := by
  rw [← LieIdeal.solvable_iff_le_radical]
  refine LieIdeal.isSolvable_of_killingForm_apply_lie_eq_zero _ ?_
  intro x hx y _
  rw [LieModule.traceForm_comm]
  exact (LieIdeal.mem_killingCompl K L ⊤).mp hx y (LieSubmodule.mem_top y)

/-- A finite-dimensional Lie algebra over a field of characteristic zero with trivial radical
has non-degenerate Killing form. This is the converse of
`LieAlgebra.IsKilling.instHasTrivialRadical` in the finite-dimensional, characteristic-zero
setting; together they give the iff `HasTrivialRadical ↔ IsKilling`, which is
**Cartan's criterion for semisimplicity**. -/
public instance HasTrivialRadical.instIsKilling [HasTrivialRadical K L] : IsKilling K L where
  killingCompl_top_eq_bot := by
    have h := killingCompl_top_le_radical K L
    rwa [HasTrivialRadical.radical_eq_bot, le_bot_iff] at h

end LieAlgebra
