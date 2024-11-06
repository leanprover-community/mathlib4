/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/

import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.IntermediateField
import Mathlib.Analysis.Normed.Group.Hom
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Algebra.Norm
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.FieldTheory.IntermediateField.Algebraic
-- import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.Normed.Ring.Ultra
/-!
# Krasner's Lemma

In this file, we prove Krasner's lemma. Instead of state and prove the Krasner's lemma directly,
we define a predicate `IsKrasner K L` for arbitary field extensions `L / K` with a normed/valued
instance on `L` as the abstraction of the conclusion of the Krasner's lemma. Then we prove the
Krasner's lemma holds for `L / K` if `K` is a complete normed/valued field and the norm/valuation
on `L` is compatible with the one on `K`.

## Main definitions

* `IsKrasner K L`

* `IsKrasnerNorm K L`

## Main results

* `of_complete` : If `K` is a complete normed/valued field, such that there exists a
unique norm extension on every algebraic extension `L` of `K`, then `IsKrasner K L` holds for every
algebraic extension `L` over `K`.

## Tags

## TODO
1. The condition `Algebra.IsAlgebraic` can be dropped in `of_complete`. This needs a generalization
of the field `Mathlib.FieldTheory.Extension` to trancendental cases. Almost all theorems in that
file still holds without the assumption of being algebraic.

2. After the definition of `Valued` is fixed, the valued version can be proved under the assumption
`IsValExtension K L`

3. Show that if `IsKrasner K (AlgebraicClosure K)` holds, then the completion of
`(AlgebraicClosure K)` is algebraically closed.

4. After the uniqueness of norm extension of complete normed field is in mathlib, drop the
conditions about `uniqueNormExtension` in `of_complete`.
If `K` is a complete normed/valued field and the norm/valuation on `L` is
compatible with the one on `K`, then `IsKrasnerNorm K L` holds.

5. After 3 and 4 are proved, show that $\mathbb{C}_p$ is algebraically closed.

-/

section test

theorem IsUltrametricDist.isNonarchimedean {R} [NormedRing R] [IsUltrametricDist R] :
    IsNonarchimedean (‖·‖ : R → ℝ) := by
  intro x y
  convert dist_triangle_max 0 x (x+y) using 1
  · simp
  · congr <;> simp

theorem isUltrametricDist_iff_isNonarchimedean {R} [NormedRing R] :
    IsUltrametricDist R ↔ IsNonarchimedean (‖·‖ : R → ℝ) := by

#check IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one

theorem IsUltrametricDist.isUltrametricDist_iff_forall_norm_natCast_le_one {R : Type*}
    [NormedDivisionRing R] : IsUltrametricDist R ↔ ∀ n : ℕ, ‖(n : R)‖ ≤ 1 :=
  ⟨fun _ => IsUltrametricDist.norm_natCast_le_one R,
      isUltrametricDist_of_forall_norm_natCast_le_one⟩

theorem IsUltrametricDist.extension 

/-- K : field L : division ring-/
theorem IsNonarchimedean.norm_extension (is_na : IsNonarchimedean (‖·‖ : K → ℝ))
    (extd : ∀ x : K, ‖x‖  = ‖algebraMap K L x‖) : IsNonarchimedean (‖·‖ : L → ℝ) := by
  refine @IsUltrametricDist.isNonarchimedean L _ ?_
  rw [IsUltrametricDist.isUltrametricDist_iff_forall_norm_natCast_le_one]

  apply IsNonarchimedean.of_algebraMap_nat
  intro x y
  simp only [IsScalarTower.algebraMap_apply ℕ K L, ← extd]
  exact map_add ((algebraMap ℕ K)) _ _ ▸ is_na _ _

-- this is another PR, showing that fron any divisionring, nonarch is equiv to nonarch
-- pullback to natural numbers

open IntermediateField
theorem IsConjRoot.exists_algEquiv_of_minpoly_split {K L} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] {x y: L}
    (h : IsConjRoot K x y) (sp : (minpoly K x).Splits (algebraMap K L)) :
    ∃ σ : L ≃ₐ[K] L, σ y = x := by
  obtain ⟨σ, hσ⟩ :=
    exists_algHom_of_splits_of_aeval (fun s => ⟨sorry, sorry⟩)
    --minpoly_add_algebraMap_splits
      (h ▸ minpoly.aeval K x)
  exact ⟨AlgEquiv.ofBijective σ sorry, hσ⟩ -- fin dim vector space inj => bij
-- another PR

end test

def uniqueNormExtension (K L : Type*) [NormedCommRing K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] :=
  ∃! (_ : NormedField L), ∀ (x : K), ‖x‖ = ‖algebraMap K L x‖

-- def uniqueNormExtension' (K L : Type*) [NormedCommRing K] [Field L] [Algebra K L]
--     [Algebra.IsAlgebraic K L] :=
--   Singleton (MulAlgebraNorm K L)

-- variable (K L) [NormedField K] [Nm_L : NormedField L]
--     [Algebra K L]
-- #check RingHomClass.toNonUnitalRingHomClass
-- #synth RingEquivClass (L ≃ₐ[K] L) L L
-- #synth NonUnitalRingHomClass (L ≃ₐ[K] L) L L
theorem IsConjRoot.norm_eq_of_uniqueNormExtension (K L) [NormedField K] [Nm_L : NormedField L]
    [Algebra K L]
    [Algebra.IsAlgebraic K L] (x y: L) (uniq : uniqueNormExtension K L)
    (extd : ∀ x : K, ‖x‖  = ‖algebraMap K L x‖) (sp : (minpoly K x).Splits (algebraMap K L))
    (h : IsConjRoot K x y) : ‖x‖ = ‖y‖ := by
  obtain ⟨σ, hσ⟩ := IsConjRoot.exists_algEquiv_of_minpoly_split h sp
  symm
  calc
    ‖y‖ = (NormedField.induced L L σ σ.injective).norm y := by
      apply congrArg (a₁ := Nm_L) (a₂ := (NormedField.induced L L σ σ.injective))
      exact uniq.unique extd fun _ => congrArg Nm_L.norm (σ.commutes _).symm ▸ extd _
    _ = ‖x‖ := hσ ▸ rfl

-- #check Algebra.smul_def
-- #synth UniformContinuousConstSMul K L
-- instance uniformContinuousConstSMul:
--   UniformContinuousConstSMul K L:= uniformContinuousConstSMul_of_continuousConstSMul K L

-- #synth UniformContinuousConstSMul K L

-- theorem boundedSMul_of_extd (extd : ∀ x : K, ‖x‖  = ‖algebraMap K L x‖) : BoundedSMul K L :=
--   BoundedSMul.of_norm_smul_le
--     (fun r x => Algebra.smul_def r x ▸ extd r ▸ NonUnitalSeminormedRing.norm_mul _ x)

-- def NormedField.mulAlgebraNorm (K L : Type*) [NormedField K] [NormedField L] [Algebra K L]
--     (extd : ∀ x : K, ‖x‖  = ‖algebraMap K L x‖) : MulAlgebraNorm K L where
--       toFun := (‖·‖)
--       map_zero' := norm_zero
--       add_le' := norm_add_le
--       neg' := norm_neg
--       map_one' := norm_one
--       map_mul' := norm_mul
--       eq_zero_of_map_eq_zero' _ := norm_eq_zero.mp
--       smul' := norm_smul

-- theorem IsConjRoot.norm_eq_of_uniqueNormExtension (K L) [NormedField K]
--     [Nm_L : MulAlgebraNorm K L]
--     [Algebra K L]
--     [Algebra.IsAlgebraic K L] (x y: L) (uniq : uniqueNormExtension' K L)
--     (extd : ∀ x : K, ‖x‖  = ‖algebraMap K L x‖) (sp : (minpoly K x).Splits (algebraMap K L))
--     (h : IsConjRoot K x y) : ‖x‖ = ‖y‖ := by
--   obtain ⟨σ, hσ⟩ := IsConjRoot.exists_algEquiv_of_minpoly_split h sp
--   symm
--   calc
--     ‖y‖ = (NormedField.induced L L σ σ.injective).norm y := by
--       apply congrArg (a₁ := Nm_L) (a₂ := (NormedField.induced L L σ σ.injective))
--       exact uniq.unique extd fun _ => congrArg Nm_L.norm (σ.commutes _).symm ▸ extd _
--     _ = ‖x‖ := hσ ▸ rfl



open IntermediateField Valued

variable (K L : Type*) {ΓL : Type*} [LinearOrderedCommGroupWithZero ΓL] [Field K]

section Normed

variable [NormedField L] [Algebra K L]

class IsKrasnerNorm : Prop where
  krasner_norm' : ∀ {x y : L}, IsSeparable K x → (minpoly K x).Splits (algebraMap K L) →
    IsIntegral K y → (∀ x' : L, IsConjRoot K x x' →  x ≠ x' → ‖x - y‖ < ‖x - x'‖) →
      x ∈ K⟮y⟯

theorem IsKrasnerNorm.krasner_norm [IsKrasnerNorm K L] {x y : L} (hx : (minpoly K x).Separable)
    (sp : (minpoly K x).Splits (algebraMap K L)) (hy : IsIntegral K y)
    (h : (∀ x' : L, IsConjRoot K x x' → x ≠ x' → ‖x - y‖ < ‖x - x'‖)) : x ∈ K⟮y⟯ :=
  IsKrasnerNorm.krasner_norm' hx sp hy h

theorem of_completeSpace {K L : Type*} [Nm_K : NontriviallyNormedField K] [CompleteSpace K] [Nm_L : NormedField L] [Algebra K L] (is_na : IsNonarchimedean (‖·‖ : K → ℝ)) [Algebra.IsAlgebraic K L] (extd : ∀ x : K, ‖x‖  = ‖algebraMap K L x‖) (uniq : ∀ M : IntermediateField K L, uniqueNormExtension K M) : IsKrasnerNorm K L := by
  constructor
  intro x y xsep sp yint kr
  let z := x - y
  let M := K⟮y⟯
  have _ := IntermediateField.adjoin.finiteDimensional yint
  let i_K : NormedAddGroupHom K (⊥ : IntermediateField K L) :=
    (AddMonoidHomClass.toAddMonoidHom (botEquiv K L).symm).mkNormedAddGroupHom 1 (by simp [extd])
  have _ : ContinuousSMul K M := by
    apply IsInducing.continuousSMul (N := K) (M := (⊥ : IntermediateField K L)) (X := M) (Y := M)
      (f := (IntermediateField.botEquiv K L).symm) IsInducing.id i_K.continuous
    intros c x
    rw [Algebra.smul_def, @Algebra.smul_def (⊥ : IntermediateField K L) M _ _ _]
    rfl -- note to reviewers: This is an ugly `rfl`. I'm not sure how to make it better.
  let _ : CompleteSpace M := FiniteDimensional.complete K M
  have hy : y ∈ K⟮y⟯ := IntermediateField.subset_adjoin K {y} rfl
  have zsep : IsSeparable M z := by
    apply Field.isSeparable_sub (IsSeparable.tower_top M xsep)
    simpa using isSeparable_algebraMap (⟨y, hy⟩ : M)
  suffices z ∈ K⟮y⟯ by simpa [z] using add_mem this hy
  by_contra hz
  have : z ∈ K⟮y⟯ ↔ z ∈ (⊥ : Subalgebra M L) := by simp [Algebra.mem_bot]
  rw [this.not] at hz
  obtain ⟨z', hne, h1⟩ := (not_mem_iff_exists_ne_and_isConjRoot zsep
      (minpoly_sub_algebraMap_splits ⟨y, hy⟩ (IsIntegral.minpoly_splits_tower_top
        xsep.isIntegral sp))).mp hz
  simp only [ne_eq, Subtype.mk.injEq] at hne

  -- have eq_spnM : (norm : M → ℝ) = spectralNorm K M :=
  --   funext <| spectralNorm_unique_field_norm_ext
  --     (f := instNormedIntermediateField.toMulRingNorm) extd is_na
  -- have eq_spnL : (norm : L → ℝ) = spectralNorm K L :=
  --   funext <| spectralNorm_unique_field_norm_ext (f := NL.toMulRingNorm) extd is_na
  -- have is_naM : IsNonarchimedean (norm : M → ℝ) := eq_spnM ▸ spectralNorm_isNonarchimedean K M is_na
  -- have is_naL : IsNonarchimedean (norm : L → ℝ) := eq_spnL ▸ spectralNorm_isNonarchimedean K L is_na

  letI : NontriviallyNormedField M := {
    SubfieldClass.toNormedField M with
    non_trivial := by
      obtain ⟨k, hk⟩ :=  @NontriviallyNormedField.non_trivial K _
      use algebraMap K M k
      change 1 < ‖(algebraMap K L) k‖
      simp [(extd k).symm, hk]-- a lemma for extends nontrivial implies nontrivial
    }
  -- have eq_spnML: (norm : L → ℝ) = spectralNorm M L := by
  --   apply Eq.trans eq_spnL
  --   apply (_root_.funext <| spectralNorm_unique_field_norm_ext (K := K)
  --     (f := (spectralMulAlgNorm is_naM).toMulRingNorm) _ is_na).symm
  --   apply functionExtends_of_functionExtends_of_functionExtends (fA := (norm : M → ℝ))
  --   · intro m
  --     exact extd m
  --   · exact spectralNorm_extends M L -- a lemma for extends extends
  -- have norm_eq: ‖z‖ = ‖z'‖ := by -- a lemma
  --   simp only [eq_spnML, spectralNorm]
  --   congr 1
    -- spectralNorm K L = spectralnorm M L
  -- IsConjRoot.val_eq M hM (Polynomial.Separable.isIntegral zsep) h1
  -- need rank one -- exist_algEquiv
  have extdM : ∀ x : M, ‖x‖ = ‖algebraMap M L x‖ := by
    sorry
  have uniqM : uniqueNormExtension M L := by
    sorry
  have : ‖z - z'‖ < ‖z - z'‖ := by
    calc
      _ ≤ max ‖z‖ ‖z'‖ := by
        simpa only [norm_neg, sub_eq_add_neg] using (is_na.norm_extension extd z (- z'))
      _ ≤ ‖x - y‖ := by
        rw [h1.norm_eq_of_uniqueNormExtension M L z z' uniqM extdM
              (minpoly_sub_algebraMap_splits ⟨y, hy⟩ (xsep.isIntegral.minpoly_splits_tower_top sp))]
        simp only [max_self, le_refl]
      _ < ‖x - (z' + y)‖ := by
        apply kr (z' + y)
        · apply IsConjRoot.of_isScalarTower (L := M) xsep.isIntegral
          simpa only [IntermediateField.algebraMap_apply, sub_add_cancel, z] using
            IsConjRoot.add_algebraMap ⟨y, hy⟩ h1
        · simpa [z, sub_eq_iff_eq_add] using hne
      _ = ‖z - z'‖ := by congr 1; ring
  simp only [lt_self_iff_false] at this


theorem of_completeSpace {K L : Type*} [Nm_K : NontriviallyNormedField K] [NormedField L]
    [Algebra K L] (is_na : IsNonarchimedean (‖·‖ : K → ℝ)) [Algebra.IsAlgebraic K L]
    [CompleteSpace K] (extd : ∀ x : K, ‖x‖  = ‖algebraMap K L x‖) : IsKrasnerNorm K L := by
  constructor
  intro x y xsep sp yint kr
  let z := x - y
  let M := K⟮y⟯
  have _ := IntermediateField.adjoin.finiteDimensional yint
  let i_K : NormedAddGroupHom K (⊥ : IntermediateField K L) :=
    (AddMonoidHomClass.toAddMonoidHom (botEquiv K L).symm).mkNormedAddGroupHom 1 (by simp [extd])
  have _ : ContinuousSMul K M := by
    apply Inducing.continuousSMul (N := K) (M := (⊥ : IntermediateField K L)) (X := M) (Y := M)
      (f := (IntermediateField.botEquiv K L).symm) inducing_id i_K.continuous
    intros c x
    rw [Algebra.smul_def, @Algebra.smul_def (⊥ : IntermediateField K L) M _ _ _]
    rfl
  let _ : CompleteSpace M := FiniteDimensional.complete K M
  have hy : y ∈ K⟮y⟯ := IntermediateField.subset_adjoin K {y} rfl
  have zsep : IsSeparable M z := by
    apply Field.isSeparable_sub (IsSeparable.tower_top M xsep)
    simpa using isSeparable_algebraMap (⟨y, hy⟩ : M)
  suffices z ∈ K⟮y⟯ by simpa [z] using add_mem this hy
  by_contra hz
  have : z ∈ K⟮y⟯ ↔ z ∈ (⊥ : Subalgebra M L) := by simp [Algebra.mem_bot]
  rw [this.not] at hz
  -- need + algebra map split and split tower.
  obtain ⟨z', hne, h1⟩ := (not_mem_iff_exists_ne_and_isConjRoot zsep
      (minpoly_sub_algebraMap_splits ⟨y, hy⟩ (IsIntegral.minpoly_splits_tower_top
        xsep.isIntegral sp))).mp hz
  -- this is where the separablity is used.
  simp only [ne_eq, Subtype.mk.injEq] at hne
  have eq_spnM : (norm : M → ℝ) = spectralNorm K M :=
    funext <| spectralNorm_unique_field_norm_ext
      (f := instNormedIntermediateField.toMulRingNorm) extd is_na
  have eq_spnL : (norm : L → ℝ) = spectralNorm K L :=
    funext <| spectralNorm_unique_field_norm_ext (f := NL.toMulRingNorm) extd is_na
  have is_naM : IsNonarchimedean (norm : M → ℝ) := eq_spnM ▸ spectralNorm_isNonarchimedean K M is_na
  have is_naL : IsNonarchimedean (norm : L → ℝ) := eq_spnL ▸ spectralNorm_isNonarchimedean K L is_na
  letI : NontriviallyNormedField M := {
    instNormedIntermediateField with
    non_trivial := by
      obtain ⟨k, hk⟩ :=  @NontriviallyNormedField.non_trivial K _
      use algebraMap K M k
      change 1 < ‖(algebraMap K L) k‖
      simp [extd k, hk]-- a lemma for extends nontrivial implies nontrivial
  }
  have eq_spnML: (norm : L → ℝ) = spectralNorm M L := by
    apply Eq.trans eq_spnL
    apply (_root_.funext <| spectralNorm_unique_field_norm_ext (K := K)
      (f := (spectralMulAlgNorm is_naM).toMulRingNorm) _ is_na).symm
    apply functionExtends_of_functionExtends_of_functionExtends (fA := (norm : M → ℝ))
    · intro m
      exact extd m
    · exact spectralNorm_extends M L -- a lemma for extends extends
  have norm_eq: ‖z‖ = ‖z'‖ := by -- a lemma
    simp only [eq_spnML, spectralNorm]
    congr 1
    -- spectralNorm K L = spectralnorm M L
  -- IsConjRoot.val_eq M hM (Polynomial.Separable.isIntegral zsep) h1
  -- need rank one -- exist_algEquiv
  have : ‖z - z'‖ < ‖z - z'‖ := by
    calc
      _ ≤ max ‖z‖ ‖z'‖ := by
        simpa only [norm_neg, sub_eq_add_neg] using (is_naL z (- z'))
      _ ≤ ‖x - y‖ := by
        simp only [← norm_eq, max_self, le_refl]
      _ < ‖x - (z' + y)‖ := by
        apply kr (z' + y)
        · apply IsConjRoot.of_isScalarTower (L := M) xsep.isIntegral
          simpa only [IntermediateField.algebraMap_apply, sub_add_cancel, z] using
            IsConjRoot.add_algebraMap ⟨y, hy⟩ h1
        · simpa [z, sub_eq_iff_eq_add] using hne
      _ = ‖z - z'‖ := by congr 1; ring
  simp only [lt_self_iff_false] at this


-- add a requirement that the uniquess is need and
-- TODO: we know this is true and after it is in mathlib we can remove this condition.
theorem of_completeSpace [CompleteSpace K] : IsKrasnerNorm K L := by
  constructor
  intro x y xsep sp yint kr
  let L' := algebraicClosure K L
  let xL : L' := ⟨x, IsSeparable.isIntegral xsep⟩
  let yL : L' := ⟨y, yint⟩
  suffices xL ∈ K⟮yL⟯ by
    rwa [← IntermediateField.lift_adjoin_simple K L' yL, IntermediateField.mem_lift xL]
  have hL' : IsKrasnerNorm K L' := IsKrasnerNorm.of_completeSpace_aux is_na extd
  apply hL'.krasner_norm
  · exact IsSeparable.of_algHom L'.val xsep
  · rw [← (minpoly.algHom_eq L'.val Subtype.val_injective xL)]
    apply minpoly_split_algebraClosure (x := x) xsep.isIntegral sp
  · exact (isIntegral_algHom_iff _ L'.val.toRingHom.injective).mp yint
  · exact fun x' hx' hne => kr x' ((isConjRoot_algHom_iff L'.val).mpr hx')
      (Subtype.coe_ne_coe.mpr hne)

end Normed

section Valued

variable [Field L] [Algebra K L] [vL : Valued L ΓL]

class IsKrasner : Prop where
  krasner' : ∀ {x y : L}, IsSeparable K x → (minpoly K x).Splits (algebraMap K L) →
    IsIntegral K y → (∀ x' : L, IsConjRoot K x x' → x ≠ x' → v (x - y) < v (x - x')) →
      x ∈ K⟮y⟯

variable {K L}

theorem IsKrasner.krasner [IsKrasner K L] {x y : L} (hx : IsSeparable K x)
    (sp : (minpoly K x).Splits (algebraMap K L)) (hy : IsIntegral K y)
    (h : (∀ x' : L, IsConjRoot K x x' → x ≠ x' → vL.v (x - y) < vL.v (x - x'))) : x ∈ K⟮y⟯ :=
  IsKrasner.krasner' hx sp hy h

end Valued
