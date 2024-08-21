/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Matrix
import Mathlib.Topology.UniformSpace.Matrix

/-!
# Matrices with entries in a C⋆-algebra

This file creates a type copy of `Matrix m n A` called `CstarMatrix m n A` meant for vectors with
entries in a C⋆-algebra `A`. Its action on `CstarVec n A` (via `Matrix.mulVec`) gives it the
operator norm, and this norm makes `CstarMatrix n n A` a C⋆-algebra.

## Main declarations

+ `CstarMatrix m n A`: the type copy
+ `CstarMatrix.instCstarRing`: square matrices with entries in a C⋆-algebra form a C⋆-algebra

## Implementation notes

The norm on this type induces the product uniformity and bornology, but these are not defeq to
`Pi.uniformSpace` and `Pi.instBornology`. Hence, we prove the equality to the Pi instances and
replace the uniformity and bornology by the Pi ones when registering the
`NormedAddCommGroup (CstarMatrix m n A)` instance. See the docstring of the `TopologyAux` section
below for more details.

-/

open scoped ComplexOrder Topology Uniformity Bornology Matrix NNReal

/-- Type copy `Matrix m n A` meant for matrices with entries in a C⋆-algebra. This is
a C⋆-algebra when `m = n`. This is an abbrev in order to inherit all instances from `Matrix`,
which includes the product uniformity, but not a norm. -/
abbrev CStarMatrix (m : Type*) (n : Type*) (A : Type*) := Matrix m n A

namespace CStarMatrix

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [PartialOrder A]
  [CompleteSpace A] [StarOrderedRing A] [NormedSpace ℂ A]
  [StarModule ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The equivalence between `CStarMatrix m n A` and `Matrix m n A`. -/
def ofMatrix : (Matrix m n A) ≃ CStarMatrix m n A := Equiv.refl _

lemma ofMatrix_symm_apply {M : Matrix m n A} {i : m} : (ofMatrix.symm M) i = M i := rfl

@[ext]
lemma ext {M₁ M₂ : CStarMatrix m n A} (h : ∀ i j, M₁ i j = M₂ i j) : M₁ = M₂ := Matrix.ext h

variable (A) in
/-- Interpret a `CStarMatrix m n A` as a continuous linear map acting on `CStarVec n A`. -/
def toCLM : CStarMatrix m n A →ₗ[ℂ] CStarVec n A →L[ℂ] CStarVec m A where
  toFun M := { toFun := M.mulVec
               map_add' := M.mulVec_add
               map_smul' := M.mulVec_smul
               cont := by simp only [LinearMap.coe_mk, AddHom.coe_mk]; fun_prop }
  map_add' M₁ M₂ := by ext; simp [Matrix.add_mulVec]
  map_smul' c M := by
    ext i j
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec,
      Matrix.dotProduct, Matrix.smul_apply, MonoidHom.id_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply]
    apply Eq.symm
    simp [Finset.smul_sum, smul_mul_assoc]

variable (A) in
/-- Interpret a `CStarMatrix m n A` as a continuous linear map acting on `CStarVec n A`. This
version is specialized to the case `m = n` and is bundled as a non-unital algebra homomorphism. -/
def toCLMNonUnitalAlgHom : CStarMatrix n n A →ₙₐ[ℂ] CStarVec n A →L[ℂ] CStarVec n A :=
  { toCLM (n := n) (m := n) A with
    map_zero' := by ext; simp [Matrix.mulVec]
    map_mul' := by intros; ext; simp [toCLM] }

lemma toCLMNonUnitalAlgHom_eq_toCLM {M : CStarMatrix n n A} :
    toCLMNonUnitalAlgHom A M = toCLM A M := rfl

lemma toCLM_apply {M : CStarMatrix m n A} {v : CStarVec n A} : toCLM A M v = M.mulVec v := rfl

lemma toCLM_apply_eq_sum {M : CStarMatrix m n A} {v : CStarVec n A} :
    toCLM A M v = CStarVec.ofFun (fun i => ∑ j, M i j * v j) := by
  ext i
  simp only [toCLM_apply, Matrix.mulVec, Matrix.dotProduct, CStarVec.ofFun_apply]

lemma toCLM_apply_single {M : CStarMatrix m n A} {j : n} (a : A) :
    (toCLM A M) (Pi.single j a) = CStarVec.ofFun (fun i => M i j * a) := by
  ext
  simp [toCLM]

lemma toCLM_apply_single_apply {M : CStarMatrix m n A} {i : m} {j : n} (a : A) :
    (toCLM A M) (Pi.single j a) i = M i j * a := by
  simp [toCLM_apply_single]

lemma mul_entry_mul_eq_inner_toCLM [DecidableEq m] {M : CStarMatrix m n A} {i : m} {j : n}
    (a b : A) :
    star a * M i j * b = ⟪CStarVec.ofFun (Pi.single i a), toCLM A M (Pi.single j b)⟫_A := by
  rw [toCLM_apply_single, CStarVec.inner_single_eq_entry, CStarVec.ofFun_apply, mul_assoc]

lemma toCLM_eq_zero_iff {M : CStarMatrix m n A} : toCLM A M = 0 ↔ M = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · ext i j
    simp only [Matrix.zero_apply]
    rw [← norm_eq_zero]
    apply eq_zero_of_mul_self_eq_zero
    simp only [← CStarRing.norm_self_mul_star, ← toCLM_apply_single_apply, h,
      ContinuousLinearMap.zero_apply, CStarVec.zero_apply, norm_zero]
  · simp [h]

lemma toCLM_inner_right_eq_left [DecidableEq m] {M : CStarMatrix m n A} {v : CStarVec m A}
    {w : CStarVec n A} : ⟪v, toCLM A M w⟫_A = ⟪toCLM A Mᴴ v, w⟫_A := by
  simp only [toCLM, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
  unfold Matrix.mulVec
  simp only [Matrix.dotProduct, NonUnitalAlgHom.coe_mk, ContinuousLinearMap.coe_mk',
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.conjTranspose_apply]
  simp_rw [← CStarVec.finset_sum_fn]
  rw [CStarModule.inner_sum_left (E := CStarVec n A)]
  simp only [CStarVec.inner_eq_sum, CStarVec.ofFun_apply]
  conv_lhs =>
    change ∑ i, star (v i) * ((∑ k : n, fun j => M j k * w k) i)
  simp only [star_sum, Finset.sum_apply, Pi.star_apply, star_mul, star_star, Finset.mul_sum,
    ← mul_assoc]

lemma toCLM_inner_conjTranspose_right_eq_left {M : CStarMatrix m n A} {v : CStarVec n A}
    {w : CStarVec m A} : ⟪v, toCLM A Mᴴ w⟫_A = ⟪toCLM A M v, w⟫_A := by
  have : M = Mᴴᴴ := by simp
  nth_rewrite 2 [this]
  rw [toCLM_inner_right_eq_left]

/-- The operator norm on `CStarMatrix m n A`. -/
noncomputable instance instNorm : Norm (CStarMatrix m n A) where
  norm M := ‖toCLM A M‖

lemma normedSpaceCore : NormedSpace.Core ℂ (CStarMatrix m n A) where
  norm_nonneg M := (toCLM A M).opNorm_nonneg
  norm_smul c M := by
    change ‖toCLM A (c • M)‖ = ‖c‖ * ‖toCLM A M‖
    rw [map_smul, norm_smul c (toCLM A M)]
  norm_triangle M₁ M₂ := by
    change ‖toCLM A (M₁ + M₂)‖ ≤ ‖toCLM A M₁‖ + ‖toCLM A M₂‖
    simp [norm_add_le]
  norm_eq_zero_iff M := by
    change ‖toCLM A M‖ = 0 ↔ M = 0
    rw [norm_eq_zero]
    exact toCLM_eq_zero_iff

open CStarModule in
lemma norm_entry_le_norm [DecidableEq m] {M : CStarMatrix m n A} {i : m} {j : n} :
    ‖M i j‖ ≤ ‖M‖ := by
  let instNACG : NormedAddCommGroup (CStarMatrix m n A) := NormedAddCommGroup.ofCore normedSpaceCore
  have hmain : ‖M i j‖ ^ 3 * ‖M i j‖ ≤ ‖M i j‖ ^ 3 * ‖M‖ := calc
        ‖M i j‖ ^ 4 = (‖M i j‖ * ‖M i j‖) * (‖M i j‖ * ‖M i j‖) := by ring
        _ = ‖star (M i j * star (M i j)) * (M i j * star (M i j))‖ := by
                rw [CStarRing.norm_star_mul_self, CStarRing.norm_self_mul_star]
        _ = ‖⟪CStarVec.ofFun (Pi.single i (M i j * star (M i j))),
                  toCLM A M (Pi.single j (star (M i j)))⟫_A‖ := by
                simp [← mul_entry_mul_eq_inner_toCLM, mul_assoc]
        _ ≤ ‖CStarVec.ofFun (Pi.single i (M i j * star (M i j)))‖
                  * ‖toCLM A M (Pi.single j (star (M i j)))‖ :=
                norm_inner_le (CStarVec m A)
        _ ≤ ‖M i j * star (M i j)‖ * ‖toCLM A M‖
                  * ‖CStarVec.ofFun <| Pi.single j (star (M i j))‖ := by
                rw [mul_assoc]
                gcongr
                · rw [CStarVec.norm_single]
                · exact ContinuousLinearMap.le_opNorm (toCLM A M) _
        _ = ‖M i j‖ ^ 2 * ‖M‖ * ‖M i j‖ := by
                congr
                · rw [CStarRing.norm_self_mul_star, pow_two]
                · simp
        _ = ‖M i j‖ ^ 3 * ‖M‖ := by ring
  by_cases htriv : M i j = 0
  · simp [htriv]
  · have h₁ : 0 < ‖M i j‖ := by rwa [norm_pos_iff]
    have h₂ : 0 < ‖M i j‖ ^ 3 := by positivity
    rwa [← mul_le_mul_left h₂]

open CStarModule in
lemma norm_le_of_forall_inner_le {M : CStarMatrix m n A} {C : ℝ≥0}
    (h : ∀ v w, ‖⟪w, toCLM A M v⟫_A‖ ≤ C * ‖v‖ * ‖w‖) : ‖M‖ ≤ C := by
  let instNACG : NormedAddCommGroup (CStarMatrix m n A) := NormedAddCommGroup.ofCore normedSpaceCore
  change ‖toCLM A M‖ ≤ C
  rw [ContinuousLinearMap.opNorm_le_iff NNReal.zero_le_coe]
  intro v
  rw [norm_eq_csSup]
  refine (csSup_le_iff ?bddAbove ?nonempty).mpr ?bound
  case bddAbove =>
    refine ⟨‖M‖ * ‖v‖, ?_⟩
    rw [mem_upperBounds]
    intro b hb
    obtain ⟨w, hw₁, hw₂⟩ := hb
    rw [← hw₂]
    calc _ ≤ ‖w‖ * ‖toCLM A M v‖ := norm_inner_le (CStarVec m A)
      _ ≤ ‖w‖ * (‖M‖ * ‖v‖) := by
            gcongr
            exact ContinuousLinearMap.le_opNorm ((toCLM A) M) v
      _ ≤ 1 * (‖M‖ * ‖v‖) := by gcongr
      _ = ‖M‖ * ‖v‖ := by simp
  case nonempty => exact ⟨0, 0, by simp, by simp⟩
  case bound =>
    intro b hb
    obtain ⟨w, hw₁, hw₂⟩ := hb
    rw [← hw₂]
    calc _ ≤ C * ‖v‖ * ‖w‖ := h v w
      _ ≤ C * ‖v‖ * 1 := by gcongr
      _ = C * ‖v‖ := by simp

end CStarMatrix

section TopologyAux
/-
## Replacing the uniformity and bornology

Note that while the norm that we have defined on `CStarMatrix m n A` induces the product uniformity,
it is not defeq to `Pi.uniformSpace`. In this section, we show that the norm indeed does induce
the product topology and use this fact to properly set up the
`NormedAddCommGroup (CStarMatrix m n A)` instance such that the uniformity is still
`Pi.uniformSpace` and the bornology is `Pi.instBornology`.

To do this, we first set up another type copy `CStarMatrixAux` to host the "bad"
`NormedAddCommGroup (CStarMatrix m n A)` instance and locally use the matrix norm
`Matrix.normedAddCommGroup` (which takes the norm of the biggest entry as the norm of the matrix)
in order to show that the map `ofMatrix.symm : CStarMatrix n A → Matrix m n A` is both Lipschitz
and Antilipschitz.  We then finally register the `NormedAddCommGroup (CStarVec n A)` instance via
`NormedAddCommGroup.ofCoreReplaceAll`.
-/

/-- The temporary type copy to host the bad instances -/
private def CStarMatrixAux (m n : Type*) (A : Type*) := Matrix m n A

namespace CStarMatrixAux

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [PartialOrder A]
  [CompleteSpace A] [StarOrderedRing A] [NormedSpace ℂ A]
  [StarModule ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

private instance : AddCommGroup (CStaCStarixAux m n A) :=
  inferInstanceAs <| AddCommGroup (CStarMatrix m n A)
private instance : Module ℂ (CStarMatrixAux m n A) :=
  inferInstanceAs <| Module ℂ (CStarMatrix m n A)
private noncomputable instance : Norm (CStarMatrixAux m n A) :=
  inferInstanceAs <| Norm (CStarMatrix m n A)

/-- The equivalence to matrices -/
private def ofMatrix : (Matrix m n A) ≃ₗ[ℂ] CStarMatrixAux m n A := LinearEquiv.refl _ _

@[ext]
private lemma ext {M₁ M₂ : CStarMatrixAux m n A} (h : ∀ i j, M₁ i j = M₂ i j) : M₁ = M₂ :=
  Matrix.ext h

private noncomputable instance normedAddCommGroupAux : NormedAddCommGroup (CStarMatrixAux m n A) :=
  .ofCore CStarMatrix.normedSpaceCore

private instance normedSpaceAux : NormedSpace ℂ (CStarMatrixAux m n A) :=
  .ofCore CStarMatrix.normedSpaceCore

-- In this `Aux` section, we locally put the above instances on `CStarMatrix` (which induce a
-- topology that is not defeq with the matrix one) and the elementwise norm on matrices, in order
-- to show that the two topologies are in fact equal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private lemma nnnorm_le_of_forall_inner_le {M : CStarMatrixAux m n A} {C : ℝ≥0}
    (h : ∀ v w, ‖⟪w, CStarMatrix.toCLM A M v⟫_A‖₊ ≤ C * ‖v‖₊ * ‖w‖₊) : ‖M‖₊ ≤ C :=
  CStarMatrix.norm_le_of_forall_inner_le fun v w => h v w

open Finset in
private lemma lipschitzWith_ofMatrix_symm_aux :
    LipschitzWith 1 (ofMatrix.symm : CStarMatrixAux m n A → Matrix m n A) := by
  refine LipschitzWith.of_dist_le_mul fun M₁ M₂ => ?_
  simp only [dist_eq_norm, NNReal.coe_one, one_mul]
  simp [← map_sub]
  set M := M₁ - M₂
  change ‖ofMatrix.symm M‖₊ ≤ ‖M‖₊
  simp_rw [Matrix.nnnorm_def, Pi.nnnorm_def]
  by_cases hm_triv : Nonempty m
  · by_cases hn_triv : Nonempty n
    · obtain ⟨i, _, hi⟩ := exists_mem_eq_sup (univ : Finset m) (univ_nonempty_iff.mpr hm_triv)
        fun b => Finset.univ.sup fun b_1 => ‖ofMatrix.symm M b b_1‖₊
      obtain ⟨j, _, hj⟩ := exists_mem_eq_sup (univ : Finset n) (univ_nonempty_iff.mpr hn_triv)
        fun b_1 => ‖ofMatrix.symm M i b_1‖₊
      rw [hi, hj]
      exact CStarMatrix.norm_entry_le_norm
    · simp only [not_nonempty_iff] at hn_triv
      simp [Finset.sup_eq_bot_of_isEmpty, bot_eq_zero]
  · simp only [not_nonempty_iff] at hm_triv
    simp [Finset.sup_eq_bot_of_isEmpty, bot_eq_zero]

open Finset in
private lemma antilipschitzWith_ofMatrix_symm_aux :
    AntilipschitzWith (Fintype.card n * Fintype.card m)
      (ofMatrix.symm : CStarMatrixAux m n A → Matrix m n A) := by
  refine AntilipschitzWith.of_le_mul_dist fun M₁ M₂ => ?_
  set Dn := Fintype.card n
  set Dm := Fintype.card m
  simp only [dist_eq_norm, ← map_sub]
  set M := M₁ - M₂
  change ‖M‖₊ ≤ Dn * Dm * ‖ofMatrix.symm M‖₊
  simp_rw [Matrix.nnnorm_def, Pi.nnnorm_def]
  by_cases hm_triv : Nonempty m
  · by_cases hn_triv : Nonempty n
    · obtain ⟨i, _, hi⟩ := exists_mem_eq_sup (univ : Finset m) (univ_nonempty_iff.mpr hm_triv)
        fun b => Finset.univ.sup fun b_1 => ‖ofMatrix.symm M b b_1‖₊
      obtain ⟨j, _, hj⟩ := exists_mem_eq_sup (univ : Finset n) (univ_nonempty_iff.mpr hn_triv)
        fun b_1 => ‖ofMatrix.symm M i b_1‖₊
      rw [hi, hj]
      change ‖M‖₊ ≤ ↑Dn * ↑Dm * ‖M i j‖₊
      refine nnnorm_le_of_forall_inner_le fun v w => ?_
      simp only [CStarVec.inner_eq_sum, CStarMatrix.toCLM_apply_eq_sum, CStarVec.ofFun_apply,
                 mul_sum]
      have hmax : ∀ k l, ‖M k l‖₊ ≤ ‖M i j‖₊ := fun k l => by
        change (univ.sup fun b => univ.sup fun b_1 => ‖M b b_1‖₊)
          = univ.sup fun b_1 => ‖M i b_1‖₊ at hi
        change (univ.sup fun b_1 => ‖M i b_1‖₊) = ‖M i j‖₊ at hj
        calc ‖M k l‖₊ ≤ univ.sup fun l' => ‖M k l'‖₊ :=
                  Finset.le_sup (f := fun l' => ‖M k l'‖₊) (mem_univ l)
          _ ≤ univ.sup fun k' => univ.sup fun l' => ‖M k' l'‖₊ :=
                  Finset.le_sup (f := fun k' => univ.sup fun l' => ‖M k' l'‖₊) (mem_univ k)
          _ = ‖M i j‖₊ := by rw [← hj, ← hi]
      calc _ ≤ ∑ k, ‖∑ l, star (w k) * M k l * v l‖₊ := by
                  simp_rw [← mul_assoc]
                  exact nnnorm_sum_le (E := A) _ _
        _ ≤ ∑ k, ∑ l, ‖star (w k) * M k l * v l‖₊ := by gcongr; exact nnnorm_sum_le _ _
        _ ≤ ∑ k, ∑ l, ‖star (w k) * M k l‖₊ * ‖v l‖₊ := by gcongr; exact nnnorm_mul_le _ _
        _ ≤ ∑ k, ∑ l, ‖w k‖₊ * ‖M k l‖₊ * ‖v l‖₊ := by
                  gcongr with k _ l _
                  refine (nnnorm_mul_le _ _).trans_eq ?_
                  simp_rw [nnnorm_star (w k)]
        _ ≤ ∑ k, ∑ l, ‖w k‖₊ * ‖M i j‖₊ * ‖v l‖₊ := by gcongr with k _ l _; exact hmax k l
        _ = ∑ k, ∑ l, ‖M i j‖₊ * (‖w k‖₊ * ‖v l‖₊) := by
                  congr 1; ext k; norm_cast
                  congr 1; ext l; norm_cast
                  ring
        _ = ‖M i j‖₊ * (∑ k, ∑ l, ‖w k‖₊ * ‖v l‖₊) := by simp [← mul_sum]
        _ = (∑ k, ∑ l, ‖w k‖₊ * ‖v l‖₊) * ‖M i j‖₊ := by rw [mul_comm]
        _ ≤ (∑ (_ : m), ∑ (_ : n), ‖w‖₊ * ‖v‖₊) * ‖M i j‖₊ := by
                  gcongr <;> exact CStarVec.norm_entry_le_norm
        _ = (Dm * (Dn * (‖w‖₊ * ‖v‖₊))) * ‖M i j‖₊ := by congr; simp [sum_const]
        _ = Dn * Dm * ‖M i j‖₊ * ‖v‖₊ * ‖w‖₊ := by ring
    · simp only [not_nonempty_iff] at hn_triv
      simp only [Finset.sup_eq_bot_of_isEmpty, Finset.sup_bot]
      rw [bot_eq_zero, mul_zero]
      simp only [nonpos_iff_eq_zero, nnnorm_eq_zero]
      ext i j
      exact False.elim <| IsEmpty.false j
  · simp only [not_nonempty_iff] at hm_triv
    simp [Finset.sup_eq_bot_of_isEmpty, bot_eq_zero]
    ext i j
    exact False.elim <| IsEmpty.false i

private lemma uniformInducing_ofMatrix_symm_aux :
    UniformInducing (ofMatrix.symm : CStarMatrixAux m n A → Matrix m n A) :=
  AntilipschitzWith.uniformInducing antilipschitzWith_ofMatrix_symm_aux
    lipschitzWith_ofMatrix_symm_aux.uniformContinuous

private lemma uniformity_eq_aux :
    𝓤 (CStarMatrixAux m n A) = (𝓤[Pi.uniformSpace _] :
    Filter (CStarMatrixAux m n A × CStarMatrixAux m n A)) := by
  have :
    (fun x : CStarMatrixAux m n A × CStarMatrixAux m n A => ⟨ofMatrix.symm x.1, ofMatrix.symm x.2⟩)
      = id := by
    ext i <;> rfl
  rw [← uniformInducing_ofMatrix_symm_aux.comap_uniformity, this, Filter.comap_id]
  rfl

open Bornology in
private lemma cobounded_eq_aux :
    cobounded (CStarMatrixAux m n A) = @cobounded _ Pi.instBornology := by
  have : cobounded (CStarMatrixAux m n A) = Filter.comap ofMatrix.symm (cobounded _) := by
    refine le_antisymm ?_ ?_
    · exact antilipschitzWith_ofMatrix_symm_aux.tendsto_cobounded.le_comap
    · exact lipschitzWith_ofMatrix_symm_aux.comap_cobounded_le
  exact this.trans Filter.comap_id

end CStarMatrixAux

end TopologyAux

namespace CStarMatrix

section non_unital

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [PartialOrder A]
  [CompleteSpace A] [StarOrderedRing A] [NormedSpace ℂ A]
  [StarModule ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

instance instBornology : Bornology (CStarMatrix m n A) := Pi.instBornology

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (CStarMatrix m n A) :=
  .ofCoreReplaceAll CStarMatrix.normedSpaceCore
    CStarMatrixAux.uniformity_eq_aux.symm
      fun _ => Filter.ext_iff.1 CStarMatrixAux.cobounded_eq_aux.symm _

instance instNormedSpace : NormedSpace ℂ (CStarMatrix m n A) :=
  .ofCore CStarMatrix.normedSpaceCore

protected lemma norm_mul {M₁ M₂ : CStarMatrix n n A} : ‖M₁ * M₂‖ ≤ ‖M₁‖ * ‖M₂‖ := by
  change ‖toCLMNonUnitalAlgHom A (M₁ * M₂)‖
    ≤ ‖toCLMNonUnitalAlgHom A M₁‖ * ‖toCLMNonUnitalAlgHom A M₂‖
  rw [map_mul]
  exact NormedRing.norm_mul ((toCLMNonUnitalAlgHom A) M₁) ((toCLMNonUnitalAlgHom A) M₂)

noncomputable instance instNonUnitalNormedRing : NonUnitalNormedRing (CStarMatrix n n A) where
  dist_eq _ _ := rfl
  norm_mul _ _ := CStarMatrix.norm_mul

open ContinuousLinearMap CStarModule in
instance instCStarRing : CStarRing (CStarMatrix n n A) where
  norm_mul_self_le M := by
    have hmain : ‖M‖ ≤ √‖star M * M‖ := by
      change ‖toCLM A M‖ ≤ √‖star M * M‖
      rw [opNorm_le_iff (by positivity)]
      intro v
      rw [norm_eq_sqrt_norm_inner_self, ← toCLM_inner_conjTranspose_right_eq_left]
      have h₁ : ‖⟪v, ((toCLM A) Mᴴ) (((toCLM A) M) v)⟫_A‖ ≤ ‖star M * M‖ * ‖v‖ ^ 2 := calc
          _ ≤ ‖v‖ * ‖((toCLM A) Mᴴ) ((toCLM A) M v)‖ := norm_inner_le (CStarVec n A)
          _ ≤ ‖v‖ * ‖((toCLM A) Mᴴ).comp ((toCLM A) M)‖ * ‖v‖ := by
                    rw [mul_assoc]
                    gcongr
                    rw [← ContinuousLinearMap.comp_apply]
                    exact le_opNorm (((toCLM A) Mᴴ).comp ((toCLM A) M)) v
          _ = ‖((toCLM A) Mᴴ).comp ((toCLM A) M)‖ * ‖v‖ ^ 2 := by ring
          _ = ‖star M * M‖ * ‖v‖ ^ 2 := by
                    congr
                    simp only [← toCLMNonUnitalAlgHom_eq_toCLM, Matrix.star_eq_conjTranspose,
                      map_mul]
                    rfl
      have h₂ : ‖v‖ = √(‖v‖ ^ 2) := by simp
      rw [h₂, ← Real.sqrt_mul]
      gcongr
      positivity
    rw [← pow_two, ← Real.sqrt_le_sqrt_iff (by positivity)]
    simp [hmain]

end non_unital

section unital

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A] [PartialOrder A]
  [CompleteSpace A] [StarOrderedRing A] [NormedAlgebra ℂ A] [StarModule ℂ A]

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable instance instNormedRing : NormedRing (CStarMatrix n n A) where
  dist_eq _ _ := rfl
  norm_mul _ _  := CStarMatrix.norm_mul

noncomputable instance instNormedAlgebra : NormedAlgebra ℂ (CStarMatrix n n A) where
  norm_smul_le r M := by
    change ‖toCLM A (r • M)‖ ≤ ‖r‖ * ‖toCLM A M‖
    simp only [map_smul]
    exact ContinuousLinearMap.opNorm_smul_le r ((toCLM A) M)

-- TODO: make this non-unital
instance instPartialOrder : PartialOrder (CStarMatrix n n A) := CStarRing.spectralOrder _
instance instStarOrderedRing : StarOrderedRing (CStarMatrix n n A) :=
  CStarRing.spectralOrderedRing _

end unital

end CStarMatrix
