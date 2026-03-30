/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.Lie.AdjointAction.JordanChevalley
public import Mathlib.Algebra.Lie.Nilpotent
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Trace-nilpotency criterion in gl(V)

Given subspaces `A ≤ B` of `gl(V)` and the set `M = {x ∈ gl(V) : [x, B] ⊆ A}`, any `x ∈ M`
that is trace-orthogonal to all of `M` is nilpotent. This is the key technical lemma behind
Cartan's criterion for semisimplicity.

## Main definitions

* `NilpotentOfTrace.M`: the set `{x ∈ gl(V) : [x, B] ⊆ A}`.
* `NilpotentOfTrace.diagEnd`: the diagonal endomorphism `b i ↦ c i • b i` relative to a basis `b`.
* `NilpotentOfTrace.eigenbasis`: an eigenbasis for a semisimple endomorphism over an algebraically
  closed field.

## Main results

* `isNilpotent_of_trace_orthogonal_algClosed`: if `x ∈ M` satisfies `tr(xz) = 0` for all `z ∈ M`,
  then `x` is nilpotent.

## References

* [J.E. Humphreys, *Introduction to Lie Algebras and Representation Theory*][humphreys1972]
-/

@[expose] public section

namespace NilpotentOfTrace

open LinearMap Module.End

section General

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- The diagonal endomorphism `b i ↦ c i • b i` relative to a basis `b`. -/
noncomputable def diagEnd {ι : Type*}
    (b : Module.Basis ι K V) (c : ι → K) : Module.End K V :=
  b.constr K (fun i => c i • b i)

theorem diagEnd_apply_basis {ι : Type*}
    (b : Module.Basis ι K V) (c : ι → K) (k : ι) :
    diagEnd b c (b k) = c k • b k := by
  simp [diagEnd, Module.Basis.constr_basis]

theorem trace_diagEnd {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K V) (c : ι → K) :
    trace K V (diagEnd b c) = ∑ i, c i := by
  classical
  have : LinearMap.toMatrix b b (diagEnd b c) = Matrix.diagonal c := by
    ext i j
    rw [LinearMap.toMatrix_apply, diagEnd_apply_basis]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
      Matrix.diagonal_apply]
    by_cases h : i = j <;> simp [h]
  rw [trace_eq_matrix_trace K b, this, Matrix.trace_diagonal]

open Classical in
theorem ad_diag_basis {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K V) (a : ι → K) (s : Module.End K V)
    (hs : ∀ k, s (b k) = a k • b k)
    (i j : ι) :
    ⁅s, b.end (i, j)⁆ = (a i - a j) • b.end (i, j) := by
  apply b.ext; intro k
  change s (b.end (i, j) (b k)) - b.end (i, j) (s (b k)) =
    (a i - a j) • b.end (i, j) (b k)
  simp only [Module.Basis.end_apply_apply, hs k, map_smul]
  by_cases hjk : j = k
  · subst hjk; simp [hs i, sub_smul]
  · simp [hjk]

/-- The set `M = {x ∈ gl(V) : [x, B] ⊆ A}`. -/
abbrev M (A B : Submodule K (Module.End K V)) : Set (Module.End K V) :=
  {x | ∀ b ∈ B, ⁅x, b⁆ ∈ A}

lemma aeval_ad_maps_to
    (A B : Submodule K (Module.End K V)) (hAB : A ≤ B)
    (x : Module.End K V) (hxM : ∀ b ∈ B, ⁅x, b⁆ ∈ A)
    (q : Polynomial K) (hq : Polynomial.eval 0 q = 0) :
    ∀ b ∈ B, (Polynomial.aeval (LieAlgebra.ad K (Module.End K V) x) q) b ∈ A := by
  set ad_x := LieAlgebra.ad K (Module.End K V) x
  obtain ⟨q', rfl⟩ : Polynomial.X ∣ q := by simpa using Polynomial.dvd_iff_isRoot.mpr hq
  have had_B : ∀ b ∈ B, ad_x b ∈ B := fun b hb => hAB (hxM b hb)
  have hpow_B : ∀ (n : ℕ) (b : Module.End K V), b ∈ B → (ad_x ^ n) b ∈ B := by
    intro n; induction n with
    | zero => simp
    | succ n ih => intro b hb; rw [pow_succ', Module.End.mul_apply]; exact had_B _ (ih b hb)
  have hpoly_B : ∀ (p : Polynomial K) (b : Module.End K V), b ∈ B →
      (Polynomial.aeval ad_x p) b ∈ B := by
    intro p; induction p using Polynomial.induction_on' with
    | add p q ihp ihq =>
      intro b hb; simp only [map_add, LinearMap.add_apply]; exact B.add_mem (ihp b hb) (ihq b hb)
    | monomial n c =>
      intro b hb
      simp only [Polynomial.aeval_monomial, Algebra.smul_def, Module.End.mul_apply,
        Module.algebraMap_end_apply]
      exact B.smul_mem c (hpow_B n b hb)
  intro b hb
  rw [map_mul, Polynomial.aeval_X, Module.End.mul_apply]
  exact hxM _ (hpoly_B q' b hb)

end General

section EigenBasis

variable {K : Type*} [Field K] [IsAlgClosed K]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

open Classical in
/-- The eigenspaces of a semisimple endomorphism over an algebraically closed field form an
internal direct sum decomposition. -/
noncomputable def eigenspaceIsInternal
    (s : Module.End K V) (hs : s.IsSemisimple) :
    DirectSum.IsInternal (fun μ : K => s.eigenspace μ) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  exact ⟨s.eigenspaces_iSupIndep, by
    have := iSup_maxGenEigenspace_eq_top s
    simp_rw [hs.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at this
    exact this⟩

open Classical in
/-- An eigenbasis for a semisimple endomorphism over an algebraically closed field. -/
noncomputable def eigenbasis (s : Module.End K V) (hs : s.IsSemisimple) :=
  (eigenspaceIsInternal s hs).collectedBasis
    (fun μ => Module.finBasis K (s.eigenspace μ))

open Classical in
noncomputable instance eigenbasisFintype (s : Module.End K V) (hs : s.IsSemisimple) :
    Fintype (Σ μ : K, Fin (Module.finrank K (s.eigenspace μ))) :=
  Module.Basis.fintypeIndexOfRankLtAleph0 (eigenbasis s hs)
    (Module.rank_lt_aleph0 K V)

open Classical in
theorem eigenbasis_eigenvalue (s : Module.End K V) (hs : s.IsSemisimple)
    (σ : Σ μ : K, Fin (Module.finrank K (s.eigenspace μ))) :
    s (eigenbasis s hs σ) = σ.1 • eigenbasis s hs σ := by
  have hmem := (eigenspaceIsInternal s hs).collectedBasis_mem
    (fun μ => Module.finBasis K (s.eigenspace μ)) σ
  exact mem_eigenspace_iff.mp hmem

end EigenBasis

section Lagrange

variable {K : Type*} [Field K] [CharZero K]

lemma exists_lagrange_polynomial
    {ι : Type*} [Finite ι]
    (a : ι → K) (E : Submodule ℚ K) (f : E →ₗ[ℚ] ℚ)
    (ha : ∀ i, a i ∈ E) :
    ∃ r : Polynomial K,
      (∀ i j, Polynomial.eval (a i - a j) r =
        algebraMap ℚ K (f ⟨a i, ha i⟩) - algebraMap ℚ K (f ⟨a j, ha j⟩)) ∧
      Polynomial.eval 0 r = 0 := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  let diffs : Finset K := Finset.univ.image (fun p : ι × ι => a p.1 - a p.2)
  have ha_diff : ∀ i j, a i - a j ∈ E := fun i j => E.sub_mem (ha i) (ha j)
  let g : K → K := fun d => if hd : d ∈ E then algebraMap ℚ K (f ⟨d, hd⟩) else 0
  let v : K → K := fun x => x
  refine ⟨Lagrange.interpolate diffs v g, fun i j => ?_, ?_⟩
  · have h_mem : a i - a j ∈ diffs :=
      Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩
    rw [Lagrange.eval_interpolate_at_node g (fun _ _ _ _ h => h) h_mem,
      show g (a i - a j) = algebraMap ℚ K (f ⟨a i - a j, ha_diff i j⟩) from
        dif_pos (ha_diff i j)]
    have : (⟨a i - a j, ha_diff i j⟩ : E) = ⟨a i, ha i⟩ - ⟨a j, ha j⟩ := rfl
    rw [this, map_sub, map_sub]
  · by_cases h_ne : Nonempty ι
    · obtain ⟨i⟩ := h_ne
      have h_mem : (0 : K) ∈ diffs :=
        Finset.mem_image.mpr ⟨(i, i), Finset.mem_univ _, sub_self _⟩
      rw [Lagrange.eval_interpolate_at_node g (fun _ _ _ _ h => h) h_mem,
        show g 0 = algebraMap ℚ K (f ⟨0, E.zero_mem⟩) from dif_pos E.zero_mem]
      have : (⟨(0 : K), E.zero_mem⟩ : E) = 0 := rfl
      rw [this, map_zero, map_zero]
    · rw [not_nonempty_iff] at h_ne
      have h_empty : diffs = ∅ := by
        simp only [diffs, Finset.image_eq_empty]; exact Finset.univ_eq_empty
      simp [Lagrange.interpolate_apply, h_empty]

end Lagrange

end NilpotentOfTrace

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

open LinearMap Module.End NilpotentOfTrace in
/-- If `x ∈ M(A, B)` is trace-orthogonal to all of `M(A, B)`, then `x` is nilpotent. -/
theorem isNilpotent_of_trace_orthogonal_algClosed
    (A B : Submodule K (Module.End K V))
    (hAB : A ≤ B)
    (x : Module.End K V)
    (hxM : x ∈ M A B)
    (htr : ∀ y ∈ M A B, trace K V (x * y) = 0) :
    IsNilpotent x := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact .zero
  obtain ⟨n, hn_adj, s, hs_adj, hn_nil, hs_ss, hxns⟩ :=
    x.exists_isNilpotent_isSemisimple
  let v := eigenbasis s hs_ss
  let a : (Σ μ : K, Fin (Module.finrank K (s.eigenspace μ))) → K := fun i => i.1
  have hv_diag : ∀ i, s (v i) = a i • v i := eigenbasis_eigenvalue s hs_ss
  let E : Submodule ℚ K := Submodule.span ℚ (Set.range a)
  suffices hs_zero : s = 0 by rw [hxns, hs_zero, add_zero]; exact hn_nil
  suffices h_f_zero : ∀ f : E →ₗ[ℚ] ℚ, f = 0 by
    refine hs_ss.eq_zero_iff_forall_eigenvalue.mpr fun μ hμ => ?_
    have : Nontrivial (s.eigenspace μ) :=
      Submodule.nontrivial_iff_ne_bot.mpr (hasEigenvalue_iff.mp hμ)
    have hμ_E : μ ∈ E := Submodule.subset_span ⟨⟨μ, ⟨0, Module.finrank_pos⟩⟩, rfl⟩
    have hφ : ∀ φ : Module.Dual ℚ E, φ ⟨μ, hμ_E⟩ = 0 := fun φ => by simp [h_f_zero φ]
    exact congr_arg Subtype.val <| (Module.forall_dual_apply_eq_zero_iff ℚ ⟨μ, hμ_E⟩).mp hφ
  intro f
  have ha : ∀ i, a i ∈ E := fun i => Submodule.subset_span (Set.mem_range_self i)
  classical
  haveI : Fintype (Σ μ : K, Fin (Module.finrank K (s.eigenspace μ))) :=
    eigenbasisFintype s hs_ss
  let y := diagEnd v (fun i => algebraMap ℚ K (f ⟨a i, ha i⟩))
  have had_s : ∀ i j, ⁅s, v.end (i, j)⁆ =
      (a i - a j) • v.end (i, j) := ad_diag_basis v a s hv_diag
  have had_y : ∀ i j, ⁅y, v.end (i, j)⁆ =
      (algebraMap ℚ K (f ⟨a i, ha i⟩) - algebraMap ℚ K (f ⟨a j, ha j⟩)) •
        v.end (i, j) :=
    fun i j => ad_diag_basis v _ (diagEnd v _) (diagEnd_apply_basis v _) i j
  obtain ⟨r, hr_eval, hr_zero⟩ := exists_lagrange_polynomial a E f ha
  let ad_s := LieAlgebra.ad K (Module.End K V) s
  have had_y_eq : LieAlgebra.ad K (Module.End K V) y = Polynomial.aeval ad_s r := by
    apply v.end.ext; intro ⟨i, j⟩
    change ⁅y, v.end (i, j)⁆ = (Polynomial.aeval ad_s r) (v.end (i, j))
    rw [Module.End.aeval_apply_of_mem_eigenspace (had_s i j), hr_eval i j, had_y i j]
  have h_ad_s_mem : ad_s ∈ Algebra.adjoin K {LieAlgebra.ad K _ x} := by
    rw [hxns]; exact LieAlgebra.ad_mem_adjoin_of_isSemisimple
      (Algebra.commute_of_mem_adjoin_singleton_of_commute hs_adj
        (Algebra.commute_of_mem_adjoin_self hn_adj).symm) hn_nil hs_ss
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h_ad_s_mem
  obtain ⟨p, hp_eq⟩ := h_ad_s_mem
  have hp_zero : Polynomial.eval 0 p = 0 :=
    LieAlgebra.eval_zero_of_aeval_ad_eq hx
      (Algebra.commute_of_mem_adjoin_self hs_adj).symm hp_eq.symm
  have hyM : y ∈ M A B := by
    have had_y_adx : LieAlgebra.ad K _ y =
        Polynomial.aeval (LieAlgebra.ad K _ x) (r.comp p) := by
      rw [had_y_eq, show ad_s = Polynomial.aeval (LieAlgebra.ad K _ x) p from hp_eq.symm,
        ← Polynomial.aeval_comp]
    intro b hb
    change (LieAlgebra.ad K _ y) b ∈ A
    rw [had_y_adx]
    exact aeval_ad_maps_to A B hAB x hxM _ (by simp [Polynomial.eval_comp, hp_zero, hr_zero]) b hb
  have htr_xy : trace K V (x * y) = 0 := htr y hyM
  let eigenvals : Finset K := Finset.univ.image a
  let c_val : K → K := fun μ => if hμ : μ ∈ E then algebraMap ℚ K (f ⟨μ, hμ⟩) else 0
  let g := Lagrange.interpolate eigenvals _root_.id c_val
  have hg_eval : ∀ i, Polynomial.eval (a i) g = algebraMap ℚ K (f ⟨a i, ha i⟩) := fun i =>
    (Lagrange.eval_interpolate_at_node c_val (fun _ _ _ _ h => h)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)).trans (dif_pos (ha i))
  have hy_eq : Polynomial.aeval s g = y := v.ext fun i => by
    rw [Module.End.aeval_apply_of_mem_eigenspace (hv_diag i), hg_eval i, diagEnd_apply_basis]
  have hy_adj : y ∈ Algebra.adjoin K {s} := by
    rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨g, hy_eq⟩
  have hny_comm : Commute n y :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute
      (Algebra.adjoin_singleton_le hs_adj hy_adj)
      (Algebra.commute_of_mem_adjoin_self hn_adj).symm
  have htr_ny : trace K V (n * y) = 0 :=
    (LinearMap.isNilpotent_trace_of_isNilpotent
      (hny_comm.isNilpotent_mul_right hn_nil)).eq_zero
  have htr_sy : trace K V (s * y) = ∑ i, a i * algebraMap ℚ K (f ⟨a i, ha i⟩) := by
    have : s * y = diagEnd v (fun i => a i * algebraMap ℚ K (f ⟨a i, ha i⟩)) := v.ext fun i => by
      change s (y (v i)) = _
      rw [show y (v i) = algebraMap ℚ K (f ⟨a i, ha i⟩) • v i from diagEnd_apply_basis v _ i,
        diagEnd_apply_basis, map_smul, hv_diag i, smul_smul, mul_comm]
    rw [this, trace_diagEnd]
  -- Combine: tr(xy) = tr(ny) + tr(sy) = 0 + Σ aᵢ f(aᵢ), so Σ aᵢ f(aᵢ) = 0
  have htr_sum : ∑ i : (Σ μ : K, Fin (Module.finrank K (s.eigenspace μ))),
      a i * algebraMap ℚ K (f ⟨a i, ha i⟩) = 0 := by
    rw [← htr_sy]
    have : trace K V (x * y) = trace K V (n * y) + trace K V (s * y) := by
      rw [hxns, add_mul]; exact map_add _ _ _
    rw [this, htr_ny, zero_add] at htr_xy
    exact htr_xy
  have h_sum_E : ∑ i : (Σ μ : K, Fin (Module.finrank K (s.eigenspace μ))),
      (f ⟨a i, ha i⟩) • (⟨a i, ha i⟩ : E) = 0 := by
    apply_fun E.subtype using Subtype.val_injective
    simp only [map_sum, map_smul, map_zero, Submodule.subtype_apply]
    convert htr_sum using 1; congr 1; ext i; rw [Algebra.smul_def, mul_comm]
  have h_sum_sq : ∑ i : (Σ μ : K, Fin (Module.finrank K (s.eigenspace μ))),
      f ⟨a i, ha i⟩ ^ 2 = (0 : ℚ) := by
    have := congr_arg f h_sum_E
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at this
    convert this using 1; congr 1; ext i; ring
  have h_each_zero : ∀ i, f ⟨a i, ha i⟩ = 0 := fun i =>
    eq_zero_of_pow_eq_zero ((Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg _)).mp h_sum_sq i (Finset.mem_univ _))
  exact (Submodule.linearMap_eq_zero_iff_of_eq_span f rfl).mpr fun ⟨_, ⟨i, rfl⟩⟩ => h_each_zero i
