/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.Algebra.AlgebraicCard
public import Mathlib.Analysis.Normed.Field.Approximation
public import Mathlib.Analysis.Normed.Field.Krasner

/-!
# Transfer properties from dense subfields

In this file, we prove that algebraic normed field extensions of a complete nontrivially normed
nonarchimedean field with a countable dense subfield are separable. We also prove that algebraic
closedness of a complete normed field of characteristic zero can be inherited from a dense
algebraically closed subfield.

## Main results

- `Algebra.IsAlgebraic.separableSpace_of_denseRange`: Every algebraic normed field extension of a
  complete nontrivially normed nonarchimedean field with a countable dense subfield is separable.
- `IsAlgClosed.of_denseRange`: If `K` is an algebraically closed dense subfield of a complete
  nonarchimedean normed field `L` of characteristic zero, then `L` is also algebraically closed.

## TODO
Show that
1. if `K` is perfect, then `L` is perfect;
2. if `L` is separably closed, then `K` is separably closed;
3. upgrade `IsAlgClosed.of_denseRange` to:  If `K` is separably closed, then `L` is
algebraically closed.

2 and 3 will be easy to implement once we establish the result that every polynomial can be
approximated by a *separable* polynomial.

## References

[Notes](https://math.stanford.edu/%7Econrad/248APage/handouts/algclosurecomp.pdf) by Brian Conrad.

## Tags

normed field, algebraically closedness, separable space, dense subfield
-/

public section

open Polynomial

open TopologicalSpace in
/-- Every algebraic normed field extension of a complete nontrivially normed nonarchimedean field
with a countable dense subfield is a separable space. -/
theorem Algebra.IsAlgebraic.separableSpace_of_denseRange {K : Type*} [Field K] [Countable K]
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hden : DenseRange (algebraMap K L))
    (F : Type*) [NormedField F] [NormedAlgebra L F] [Algebra.IsAlgebraic L F] :
    SeparableSpace F := by
  let E := AlgebraicClosure L
  letI : NormedField E := spectralNorm.normedField L E
  letI : NormedAlgebra L E := spectralNorm.normedAlgebra L E
  haveI hEsep : SeparableSpace E := by
    refine ⟨{z : E | IsAlgebraic K z}, Algebraic.countable K E,
      Metric.dense_iff.mpr <| fun α ε hε ↦ ?_⟩
    have hα : IsIntegral L α := Algebra.IsIntegral.isIntegral α
    set f := minpoly L α
    have hf : Monic f := minpoly.monic hα
    set n := f.natDegree with hn
    have hnpos : 0 < n := minpoly.natDegree_pos hα
    set M := max ‖α‖ 1 with hM
    have hMpos : M ≠ 0 := by positivity
    set δ := (ε / M) ^ n / (n + 1) with hδ_def
    have hδpos : 0 < δ := by positivity
    obtain ⟨g, hgm, hdeg, hgcoeff⟩ :=
      exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hden hf hδpos
    obtain ⟨β, hβroot, hβnorm⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      hδpos (f := f) (minpoly.aeval _ _) hf (hgm.map _)
      (by rw [natDegree_map_eq_of_injective (algebraMap K L).injective]; omega)
      (fun i ↦ by simpa using hgcoeff i) (IsAlgClosed.splits _)
    refine ⟨β, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_comm, dist_eq_norm]
      refine hβnorm.trans_le ?_
      rw [← hn, ← hM, show (↑n + 1) * δ = (ε / M) ^ n by rw [hδ_def]; field_simp,
        Real.pow_rpow_inv_natCast (by positivity) hnpos.ne', div_mul_cancel₀ _ hMpos]
    · rw [mem_aroots, aeval_map_algebraMap] at hβroot
      exact ⟨g, hgm.ne_zero, hβroot.2⟩
  let e : F →ₐ[L] E := IsAlgClosed.lift
  have he_inj : Function.Injective e := (e : F →+* E).injective
  have he_isom : Isometry e := AddMonoidHomClass.isometry_of_norm e fun x ↦ by
    rw [NormedAlgebra.norm_eq_spectralNorm L, NormedAlgebra.norm_eq_spectralNorm L]
    rw [spectralNorm, spectralNorm, minpoly.algHom_eq e he_inj]
  have hsep := he_isom.isEmbedding.isSeparable_preimage
    (IsSeparable.of_separableSpace (Set.univ : Set E))
  simpa [Set.preimage_univ] using isSeparable_univ_iff.mp hsep

/-- If `K` is an algebraically closed dense subfield of a complete nonarchimedean normed field `L`
of characteristic zero, then `L` is also algebraically closed. -/
theorem IsAlgClosed.of_denseRange {K L : Type*} [Field K] [NontriviallyNormedField L]
    [CompleteSpace L] [CharZero L] [IsUltrametricDist L] [Algebra K L]
    (hi : DenseRange (algebraMap K L)) [IsAlgClosed K] : IsAlgClosed L := by
  -- Fix any monic irreducible polynomial `f` in `L`.
  -- Let `F` be the splitting field of `f`. Let `a` be a root of `f` in `F`.
  apply IsAlgClosed.of_exists_root
  intro f fmon firr
  have fnatdeg0 : f.natDegree ≠ 0 := (Irreducible.natDegree_pos firr).ne'
  let F := f.SplittingField
  let : NormedField F := spectralNorm.normedField L F
  let : NormedAlgebra L F := spectralNorm.normedAlgebra L F
  let a := rootOfSplits (SplittingField.splits f)
      (by simpa using degree_ne_of_natDegree_ne fnatdeg0)
  have fa0 : f.aeval a = 0 := by
    rw [← eval_map_algebraMap]
    exact eval_rootOfSplits (Polynomial.SplittingField.splits f)
      (by simpa using degree_ne_of_natDegree_ne fnatdeg0)
  -- Let `δ` be a positive real number such that `δ ≤ ‖a - a'‖` for
  -- every Galois conjugates `a'` of `a`
  classical
    let S : Finset F := {x ∈ (f.rootSet F).toFinset | x ≠ a}
  let δ : ℝ := if hS : S.Nonempty then Finset.min' (S.image fun x => ‖a - x‖)
      (Finset.image_nonempty.mpr hS) else 1
  have norm_sub_le : ∀ a' : F, IsConjRoot L a a' → a ≠ a' → δ ≤ ‖a - a'‖ := by
    intro a' conj ne
    by_cases hS : S.Nonempty <;> simp only [hS, ↓reduceDIte, δ]
    · apply Finset.min'_le (S.image fun x => ‖a - x‖) (‖a - a'‖)
      apply Finset.mem_image_of_mem
      simp only [minpoly.eq_of_irreducible_of_monic firr fa0 fmon, Finset.mem_filter,
        Set.mem_toFinset, S]
      rw [← (isConjRoot_iff_mem_minpoly_rootSet ⟨f, fmon, fa0⟩)]
      exact ⟨conj, ne.symm⟩
    · simp only [ne_eq, Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff,
      Set.mem_toFinset, not_not, S] at hS
      rw [isConjRoot_iff_mem_minpoly_rootSet ⟨f, fmon, fa0⟩,
          ← minpoly.eq_of_irreducible_of_monic firr fa0 fmon] at conj
      exact (ne (hS conj).symm).elim
  have δpos : δ > 0 := by
    by_cases hS : S.Nonempty <;> simp only [hS, ↓reduceDIte, δ]
    · simp only [gt_iff_lt, Finset.lt_min'_iff, Finset.mem_image, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      rintro a' ha'
      simp only [Finset.mem_filter, Set.mem_toFinset, S] at ha'
      rw [norm_pos_iff, sub_ne_zero]
      exact ha'.2.symm
    · linarith
  have hε : (δ / (max ‖a‖ 1)) ^ f.natDegree / (f.natDegree + 1) > 0 := by positivity
  -- We can find a `g ∈ K[X]` whose coefficients sufficiently close to coefficients of `f`.
  -- By continuity of roots, there exists a root `b` of `g` in `K` such that `‖a - b‖ ≤ δ`.
  obtain ⟨g, gmon, gdeg, gcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hi fmon hε
  let ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff
      (by simpa [Polynomial.map_map] using (IsAlgClosed.splits g).map ((algebraMap L F).comp _))
  have hab : ‖a - b‖ < δ := by
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hab
    · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖a‖ 1) > 0).ne'] using hab
    · simp [fnatdeg0]
    · positivity
  have bbot : b ∈ (⊥ : IntermediateField L F) := by
    rw [Polynomial.aroots_def, Splits.roots_map ((IsAlgClosed.splits g).map _),
        Multiset.mem_map] at hb
    obtain ⟨bCp, _, hbCp⟩ := hb
    rw [IntermediateField.mem_bot]
    exact ⟨bCp, hbCp⟩
  simp only [Polynomial.mem_roots', ne_eq, Polynomial.map_eq_zero, Polynomial.IsRoot.def,
    Polynomial.eval_map_algebraMap] at hb
  -- By Krasner's lemma, `a ∈ L(b) = L`. Thus `f` has a root in `L`.
  have abot : a ∈ (⊥ : IntermediateField L F) := by
    have masp : ((minpoly L a).map (algebraMap L F)).Splits := by
      simpa [minpoly.eq_of_irreducible_of_monic firr fa0 fmon] using
        (Polynomial.SplittingField.splits f)
    simpa [IntermediateField.adjoin_simple_eq_bot_iff.mpr bbot] using
      IsKrasner.krasner (minpoly.irreducible ⟨f, fmon, fa0⟩).separable
        masp ⟨(g.map _), gmon.map _, hb.2⟩ fun a' h1 h2 ↦ lt_of_lt_of_le hab (norm_sub_le a' h1 h2)
  obtain ⟨aCp, haCp⟩ := IntermediateField.mem_bot.mp abot
  use aCp
  apply_fun algebraMap L F
  · rwa [← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, haCp, map_zero]
  · exact RingHom.injective _
