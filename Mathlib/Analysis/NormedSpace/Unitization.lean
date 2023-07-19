/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import Mathlib.Algebra.Algebra.Unitization
import Mathlib.Analysis.NormedSpace.OperatorNorm

/-!
# Unitization norms

Given a not necessarily unital normed `𝕜`-algebra `A`, it is frequently of interest to equip its
`Unitization` with a norm which simultaneously makes it into a normed algebra and also satisfies
two properties:

- `‖1‖ = 1` (i.e., `NormOneClass`)
- The embedding of `A` in `Unitization 𝕜 A` is an isometry. (i.e., `Isometry Unitization.inr`)

One way to do this is to equip it with the norm from `PiLp 1` (actually, it should be
`ProdLp 1`, but that doesn't exist), that is, `‖(k, a)‖ = ‖k‖ + ‖a‖`. However, when the norm on `A`
is *regular* (i.e., `ContinuousLinearMap.mul`) is an isometry, there is another natural choice:
the pullback of the norm on `𝕜 × (A →L[𝕜] A)` under the map
`(k, a) ↦ (k, k • 1 + ContinuousLinearMap.mul 𝕜 A a)`. It turns out that among all norms on the
unitization satisfying the properties specified above, the norm inherited from `PiLp 1` is maximal,
and the norm inherited from this pullback is minimal.

For possibly non-unital `RegularNormedAlgebra`s  `A` (over `𝕜`), we construct a `NormedAlgebra`
structure on `Unitization 𝕜 A` using the pullback described above. The reason for choosing this norm
is that for a C⋆-algebra `A` its norm is always regular, and the pullback norm on `Unitization 𝕜 A`
is then also a C⋆-norm.

## Main definitions

- `NonUnitalAlgHom.Lmul : A →ₙₐ[𝕜] A →L[𝕜] A`: `ContinuousLinearMap.mul` upgraded to a non-unital
  algebra homomorphism.
- `Unitization.leftRegRep : Unitization 𝕜 A →ₐ[𝕜] (𝕜 × (A →L[𝕜] A))`: The first coordinate of this
  map is just `Unitization.fst` and the second is the left regular representation of
  `Unitization 𝕜 A` *acting on `A`*. This is the `Unitization.lift` of `NonUnitalAlgHom.Lmul`.
  We use this map to pull back the `NormedRing` and `NormedAlgebra` structures.

## Implementation details

We ensure that the uniform structure, and hence also the topological structure, is definitionally
equal to `instUniformSpaceProd` (viewing `Unitization 𝕜 A` as `𝕜 × A`) by means of forgetful
inheritance. The same is true of the bornology.

-/

variable (𝕜 A : Type _) [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
variable [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

open ContinuousLinearMap

/-- Multiplication on the left in a non-unital algebra `A` as a non-unital algebra homomorphism
into the algebra of *continuous* linear maps. This has more algebraic structure than
`ContinuousLinearMap.mul`, but there is no longer continuity bundled in the first coordinate. -/
noncomputable def NonUnitalAlgHom.Lmul : A →ₙₐ[𝕜] A →L[𝕜] A :=
  { mul 𝕜 A with
    toFun := fun a => mul 𝕜 A a
    map_mul' := fun a b => by ext x; simp [mul_assoc a b x]
    map_zero' := by ext x; simp only [map_zero] }

variable {𝕜 A}

@[simp]
theorem NonUnitalAlgHom.coe_Lmul : ⇑(NonUnitalAlgHom.Lmul 𝕜 A) = mul 𝕜 A :=
  rfl

variable (𝕜 A)

namespace Unitization

/-- `leftRegRep` stands for "left regular representation" which is multiplication on the left. So,
given `(k, a) : Unitization 𝕜 A`, the second coordinate of `Unitization.leftRegRep (k, a)` should
be the representation of `Unitization 𝕜 A` on `A →L[𝕜] A`; note that this is not just
`NonUnitalAlgHom.Lmul` for a few reasons: (a) that would either be `A` acting on `A`, or
(b) `Unitization 𝕜 A` acting on `Unitization 𝕜 A`, and (c) that's a `NonUnitalAlgHom` but
here we need an `AlgHom`. In addition, the first coordinate of `Unitization.leftRegRep (k, a)`
should just be `k`. See `Unitization.leftRegRep_apply` also. -/
noncomputable def leftRegRep : Unitization 𝕜 A →ₐ[𝕜] 𝕜 × (A →L[𝕜] A) :=
  (lift 0).prod (lift <| NonUnitalAlgHom.Lmul 𝕜 A)

variable {𝕜 A}

@[simp]
theorem leftRegRep_apply (x : Unitization 𝕜 A) :
    leftRegRep 𝕜 A x = (x.fst, algebraMap 𝕜 (A →L[𝕜] A) x.fst + mul 𝕜 A x.snd) :=
  show (x.fst + 0, _) = (x.fst, _) by rw [add_zero]; rfl

/-- this lemma establishes that if `ContinuousLinearMap.mul 𝕜 A` is injective, then so is
`Unitization.leftRegRep 𝕜 A`. When `A` is a `RegularNormedAlgebra`, then
`ContinuousLinearMap.mul 𝕜 A` is an isometry, and is therefore automatically injective. -/
theorem leftRegRep_injective_of_clm_mul_injective
    (h : Function.Injective (mul 𝕜 A)) :
    Function.Injective (leftRegRep 𝕜 A) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Unitization.ind
  rw [map_add] at hx
  simp only [Prod.mk_add_mk, add_zero, fst_inl, leftRegRep_apply,
    snd_inl, snd_inr, Prod.mk_eq_zero, zero_add, fst_inr,
    map_zero, leftRegRep_apply, add_zero, Prod.mk_eq_zero] at hx
  obtain ⟨rfl, hx⟩ := hx
  simp only [map_zero, zero_add, inl_zero] at hx ⊢
  rw [← map_zero (mul 𝕜 A)] at hx
  rw [h hx, inr_zero]

variable [RegularNormedAlgebra 𝕜 A]
variable (𝕜 A)

/- In a `RegularNormedAlgebra`, the map `Unitization.leftRegRep 𝕜 A` is injective. We will use this
to pull back the norm from `𝕜 × (A →L[𝕜] A)` to `Unitization 𝕜 A`. -/
theorem leftRegRep_injective : Function.Injective (leftRegRep 𝕜 A) :=
  leftRegRep_injective_of_clm_mul_injective (isometry_mul 𝕜 A).injective

variable {𝕜 A}

section Aux

/-- Pull back the normed ring structure from `(A →L[𝕜] A) × 𝕜` to `Unitization 𝕜 A` using the
algebra homomorphism `Unitization.leftRegRep 𝕜 A`. This does not give us the desired topology,
uniformity or bornology on `Unitization 𝕜 A` (which we want to agree with `Prod`), so we only use
it as a local instance to build the real one. -/
@[reducible]
noncomputable def normedRingAux : NormedRing (Unitization 𝕜 A) :=
  @NormedRing.induced _ (Unitization 𝕜 A) (𝕜 × (A →L[𝕜] A)) Unitization.instRing
    Prod.normedRing _ (leftRegRep 𝕜 A) (leftRegRep_injective 𝕜 A)
-- ummmm... what? why does Lean need me to fill in these instances?

attribute [local instance] Unitization.normedRingAux

/-- Pull back the normed algebra structure from `(A →L[𝕜] A) × 𝕜` to `Unitization 𝕜 A` using the
algebra homomorphism `Unitization.leftRegRep 𝕜 A`. This uses the wrong `NormedRing` instance (i.e.,
`Unitization.normedRingAux`), so we only use it as a local instance to build the real one.-/
@[reducible]
noncomputable def normedAlgebraAux : NormedAlgebra 𝕜 (Unitization 𝕜 A) :=
  NormedAlgebra.induced 𝕜 (Unitization 𝕜 A) (𝕜 × (A →L[𝕜] A)) (leftRegRep 𝕜 A)

attribute [local instance] Unitization.normedAlgebraAux

theorem norm_def (x : Unitization 𝕜 A) : ‖x‖ = ‖leftRegRep 𝕜 A x‖ :=
  rfl

/-- This is often the more useful lemma to rewrite the norm as opposed to `Unitization.norm_def`. -/
theorem norm_eq_sup (x : Unitization 𝕜 A) :
    ‖x‖ = ‖x.fst‖ ⊔ ‖algebraMap 𝕜 (A →L[𝕜] A) x.fst + mul 𝕜 A x.snd‖ := by
  rw [norm_def, leftRegRep_apply, Prod.norm_def, sup_eq_max]

variable (𝕜 A)

/-- The identity map between `Unitization 𝕜 A` and `𝕜 × A` as an `AddEquiv`. -/
protected def addEquiv : Unitization 𝕜 A ≃+ 𝕜 × A :=
  AddEquiv.refl _

variable {𝕜 A}

theorem lipschitzWith_addEquiv :
    LipschitzWith (2 : ℝ).toNNReal (Unitization.addEquiv 𝕜 A) := by
  refine' AddMonoidHomClass.lipschitz_of_bound (Unitization.addEquiv 𝕜 A) 2 fun x => _
  rw [norm_eq_sup, Prod.norm_def]
  refine' max_le _ _
  · rw [sup_eq_max, mul_max_of_nonneg _ _ (zero_le_two : (0 : ℝ) ≤ 2)]
    exact le_max_of_le_left ((le_add_of_nonneg_left (norm_nonneg _)).trans_eq (two_mul _).symm)
  · change ‖x.snd‖ ≤ _
    nontriviality A
    rw [two_mul]
    calc
      ‖x.snd‖ = ‖mul 𝕜 A x.snd‖ :=
        ((AddMonoidHomClass.isometry_iff_norm (mul 𝕜 A)).mp (isometry_mul 𝕜 A) _).symm
      _ ≤ ‖algebraMap 𝕜 _ x.fst + mul 𝕜 A x.snd‖ + ‖x.fst‖ := by
        simpa only [add_comm _ (mul 𝕜 A x.snd), norm_algebraMap'] using
          norm_le_add_norm_add (mul 𝕜 A x.snd) (algebraMap 𝕜 _ x.fst)
      _ ≤ _ := add_le_add le_sup_right le_sup_left

theorem antilipschitzWith_addEquiv :
    AntilipschitzWith 2 (Unitization.addEquiv 𝕜 A) := by
  refine' AddMonoidHomClass.antilipschitz_of_bound (Unitization.addEquiv 𝕜 A) fun x => _
  rw [norm_eq_sup, Prod.norm_def, NNReal.coe_two]
  refine' max_le _ _
  · rw [mul_max_of_nonneg _ _ (zero_le_two : (0 : ℝ) ≤ 2)]
    exact le_max_of_le_left ((le_add_of_nonneg_left (norm_nonneg _)).trans_eq (two_mul _).symm)
  · nontriviality A
    calc
      ‖algebraMap 𝕜 _ x.fst + mul 𝕜 A x.snd‖ ≤ ‖algebraMap 𝕜 _ x.fst‖ + ‖mul 𝕜 A x.snd‖ :=
        norm_add_le _ _
      _ = ‖x.fst‖ + ‖x.snd‖ := by
        rw [norm_algebraMap', (AddMonoidHomClass.isometry_iff_norm (mul 𝕜 A)).mp (isometry_mul 𝕜 A)]
      _ ≤ _ := (add_le_add (le_max_left _ _) (le_max_right _ _)).trans_eq (two_mul _).symm

open Bornology Filter
open scoped Uniformity

theorem uniformity_eq_aux :
    @uniformity (Unitization 𝕜 A) instUniformSpaceProd = 𝓤 (Unitization 𝕜 A) := by
  have key : UniformInducing (Unitization.addEquiv 𝕜 A) :=
    antilipschitzWith_addEquiv.uniformInducing lipschitzWith_addEquiv.uniformContinuous
  rw [← key.comap_uniformity]
  exact comap_id.symm

theorem cobounded_eq_aux :
    @cobounded (Unitization 𝕜 A) Prod.instBornology = cobounded (Unitization 𝕜 A) :=
  calc
    _ = comap (Unitization.addEquiv 𝕜 A) (cobounded _) := comap_id.symm
    _ = cobounded (Unitization 𝕜 A) :=
      le_antisymm lipschitzWith_addEquiv.comap_cobounded_le
        antilipschitzWith_addEquiv.tendsto_cobounded.le_comap

end Aux

/-- The uniformity on `Unitization 𝕜 A` is inherited from `𝕜 × A`. -/
instance instUniformSpace : UniformSpace (Unitization 𝕜 A) :=
  instUniformSpaceProd

/-- The bornology on `Unitization 𝕜 A` is inherited from `𝕜 × A`. -/
instance instBornology : Bornology (Unitization 𝕜 A) :=
  Prod.instBornology

/-- `Unitization 𝕜 A` is complete whenever `𝕜` and `A` are also.  -/
instance instCompleteSpace [CompleteSpace 𝕜] [CompleteSpace A] :
    CompleteSpace (Unitization 𝕜 A) :=
  CompleteSpace.prod

/-- Pull back the metric structure from `𝕜 × (A →L[𝕜] A)` to `Unitization 𝕜 A` using the
algebra homomorphism `Unitization.leftRegRep 𝕜 A`, but replace the bornology and the uniformity so
that they coincide with `𝕜 × A`. -/
noncomputable instance instMetricSpace : MetricSpace (Unitization 𝕜 A) :=
  (normedRingAux.toMetricSpace.replaceUniformity uniformity_eq_aux).replaceBornology
    fun s => Filter.ext_iff.1 cobounded_eq_aux (sᶜ)

/-- Pull back the normed ring structure from `𝕜 × (A →L[𝕜] A)` to `Unitization 𝕜 A` using the
algebra homomorphism `Unitization.leftRegRep 𝕜 A`. -/
noncomputable instance instNormedRing : NormedRing (Unitization 𝕜 A)
    where
  dist_eq := normedRingAux.dist_eq
  norm_mul := normedRingAux.norm_mul
  norm := normedRingAux.norm

/-- Pull back the normed algebra structure from `𝕜 × (A →L[𝕜] A)` to `Unitization 𝕜 A` using the
algebra homomorphism `Unitization.leftRegRep 𝕜 A`. -/
instance instNormedAlgebra : NormedAlgebra 𝕜 (Unitization 𝕜 A) where
  norm_smul_le k x := by
    rw [norm_def, map_smul, norm_smul, ← norm_def]

-- this should go in `Algebra.Algebra.Unitization`
instance instNontrivial {𝕜 A} [Nontrivial 𝕜] [Nonempty A] :
    Nontrivial (Unitization 𝕜 A) :=
  nontrivial_prod_left

instance instNormOneClass : NormOneClass (Unitization 𝕜 A) where
  norm_one := by simpa only [norm_eq_sup, fst_one, norm_one, snd_one, map_one, map_zero,
      add_zero, ge_iff_le, sup_eq_left] using op_norm_le_bound _ zero_le_one fun x => by simp

lemma norm_inr (a : A) : ‖(a : Unitization 𝕜 A)‖ = ‖a‖ := by
  simp [norm_eq_sup]

lemma isometry_inr : Isometry ((↑) : A → Unitization 𝕜 A) :=
  AddMonoidHomClass.isometry_of_norm (inrNonUnitalAlgHom 𝕜 A) norm_inr

/- These examples verify that the bornology and uniformity (hence also the topology) are the
correct ones. -/
example : (instNormedRing (𝕜 := 𝕜) (A := A)).toMetricSpace = instMetricSpace := rfl
example : (instMetricSpace (𝕜 := 𝕜) (A := A)).toBornology = instBornology := rfl
example : (instMetricSpace (𝕜 := 𝕜) (A := A)).toUniformSpace = instUniformSpace := rfl
