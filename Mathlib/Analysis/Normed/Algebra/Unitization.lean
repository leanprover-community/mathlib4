/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Init
import Mathlib.Order.Filter.Tendsto
meta import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Nontriviality.Core
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.SuppressCompilation
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Metrizable.Uniformity

/-!
# Unitization norms

Given a not-necessarily-unital normed `𝕜`-algebra `A`, it is frequently of interest to equip its
`Unitization` with a norm which simultaneously makes it into a normed algebra and also satisfies
two properties:

- `‖1‖ = 1` (i.e., `NormOneClass`)
- The embedding of `A` in `Unitization 𝕜 A` is an isometry. (i.e., `Isometry Unitization.inr`)

One way to do this is to pull back the norm from `WithLp 1 (𝕜 × A)`, that is,
`‖(k, a)‖ = ‖k‖ + ‖a‖` using `Unitization.addEquiv` (i.e., the identity map).
This is implemented for the type synonym `WithLp 1 (Unitization 𝕜 A)` in
`WithLp.instUnitizationNormedAddCommGroup`, and it is shown there that this is a Banach algebra.
However, when the norm on `A` is *regular* (i.e., `ContinuousLinearMap.mul` is an isometry), there
is another natural choice: the pullback of the norm on `𝕜 × (A →L[𝕜] A)` under the map
`(k, a) ↦ (k, k • 1 + ContinuousLinearMap.mul 𝕜 A a)`. It turns out that among all norms on the
unitization satisfying the properties specified above, the norm inherited from
`WithLp 1 (𝕜 × A)` is maximal, and the norm inherited from this pullback is minimal.
Of course, this means that `WithLp.equiv : WithLp 1 (Unitization 𝕜 A) → Unitization 𝕜 A` can be
upgraded to a continuous linear equivalence (when `𝕜` and `A` are complete).

structure on `Unitization 𝕜 A` using the pullback described above. The reason for choosing this norm
is that for a C⋆-algebra `A` its norm is always regular, and the pullback norm on `Unitization 𝕜 A`
is then also a C⋆-norm.

## Main definitions

- `Unitization.splitMul : Unitization 𝕜 A →ₐ[𝕜] (𝕜 × (A →L[𝕜] A))`: The first coordinate of this
  map is just `Unitization.fst` and the second is the `Unitization.lift` of the left regular
  representation of `A` (i.e., `NonUnitalAlgHom.Lmul`). We use this map to pull back the
  `NormedRing` and `NormedAlgebra` structures.

## Main statements

- `Unitization.instNormedRing`, `Unitization.instNormedAlgebra`, `Unitization.instNormOneClass`,
  `Unitization.instCompleteSpace`: when `A` is a non-unital Banach `𝕜`-algebra with a regular norm,
  then `Unitization 𝕜 A` is a unital Banach `𝕜`-algebra with `‖1‖ = 1`.
- `Unitization.norm_inr`, `Unitization.isometry_inr`: the natural inclusion `A → Unitization 𝕜 A`
  is an isometry, or in mathematical parlance, the norm on `A` extends to a norm on
  `Unitization 𝕜 A`.

## Implementation details

We ensure that the uniform structure, and hence also the topological structure, is definitionally
equal to the pullback of `instUniformSpaceProd` along `Unitization.addEquiv` (this is essentially
viewing `Unitization 𝕜 A` as `𝕜 × A`) by means of forgetful inheritance. The same is true of the
bornology.

-/

@[expose] public section

suppress_compilation

variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
variable [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

open ContinuousLinearMap

namespace Unitization

/-- Given `(k, a) : Unitization 𝕜 A`, the second coordinate of `Unitization.splitMul (k, a)` is
the natural representation of `Unitization 𝕜 A` on `A` given by multiplication on the left in
`A →L[𝕜] A`; note that this is not just `NonUnitalAlgHom.Lmul` for a few reasons: (a) that would
either be `A` acting on `A`, or (b) `Unitization 𝕜 A` acting on `Unitization 𝕜 A`, and (c) that's a
`NonUnitalAlgHom` but here we need an `AlgHom`. In addition, the first coordinate of
`Unitization.splitMul (k, a)` should just be `k`. See `Unitization.splitMul_apply` also. -/
def splitMul : Unitization 𝕜 A →ₐ[𝕜] 𝕜 × (A →L[𝕜] A) :=
  (lift 0).prod (lift <| NonUnitalAlgHom.Lmul 𝕜 A)

variable {𝕜 A}

@[simp]
theorem splitMul_apply (x : Unitization 𝕜 A) :
    splitMul 𝕜 A x = (x.fst, algebraMap 𝕜 (A →L[𝕜] A) x.fst + mul 𝕜 A x.snd) :=
  show (x.fst + 0, _) = (x.fst, _) by rw [add_zero]; rfl

/-- this lemma establishes that if `ContinuousLinearMap.mul 𝕜 A` is injective, then so is
`Unitization.splitMul 𝕜 A`. When `A` is a `RegularNormedAlgebra`, then
`ContinuousLinearMap.mul 𝕜 A` is an isometry, and is therefore automatically injective. -/
theorem splitMul_injective_of_clm_mul_injective
    (h : Function.Injective (mul 𝕜 A)) :
    Function.Injective (splitMul 𝕜 A) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x
  rw [map_add] at hx
  simp only [splitMul_apply, fst_inl, snd_inl, map_zero, add_zero, fst_inr, snd_inr,
    zero_add, Prod.mk_add_mk, Prod.mk_eq_zero] at hx
  obtain ⟨rfl, hx⟩ := hx
  simp only [map_zero, zero_add, inl_zero] at hx ⊢
  rw [← map_zero (mul 𝕜 A)] at hx
  rw [h hx, inr_zero]

variable [RegularNormedAlgebra 𝕜 A]
variable (𝕜 A)

/-- In a `RegularNormedAlgebra`, the map `Unitization.splitMul 𝕜 A` is injective.
We will use this to pull back the norm from `𝕜 × (A →L[𝕜] A)` to `Unitization 𝕜 A`. -/
theorem splitMul_injective : Function.Injective (splitMul 𝕜 A) :=
  splitMul_injective_of_clm_mul_injective (isometry_mul 𝕜 A).injective

variable {𝕜 A}

section Aux

/-- Pull back the normed ring structure from `𝕜 × (A →L[𝕜] A)` to `Unitization 𝕜 A` using the
algebra homomorphism `Unitization.splitMul 𝕜 A`. This does not give us the desired topology,
uniformity or bornology on `Unitization 𝕜 A` (which we want to agree with `Prod`), so we only use
it as a local instance to build the real one. -/
noncomputable abbrev normedRingAux : NormedRing (Unitization 𝕜 A) :=
  NormedRing.induced (Unitization 𝕜 A) (𝕜 × (A →L[𝕜] A)) (splitMul 𝕜 A) (splitMul_injective 𝕜 A)

attribute [local instance] Unitization.normedRingAux

/-- Pull back the normed algebra structure from `𝕜 × (A →L[𝕜] A)` to `Unitization 𝕜 A` using the
algebra homomorphism `Unitization.splitMul 𝕜 A`. This uses the wrong `NormedRing` instance (i.e.,
`Unitization.normedRingAux`), so we only use it as a local instance to build the real one. -/
noncomputable abbrev normedAlgebraAux : NormedAlgebra 𝕜 (Unitization 𝕜 A) :=
  NormedAlgebra.induced 𝕜 (Unitization 𝕜 A) (𝕜 × (A →L[𝕜] A)) (splitMul 𝕜 A)

attribute [local instance] Unitization.normedAlgebraAux

theorem norm_def (x : Unitization 𝕜 A) : ‖x‖ = ‖splitMul 𝕜 A x‖ :=
  rfl

theorem nnnorm_def (x : Unitization 𝕜 A) : ‖x‖₊ = ‖splitMul 𝕜 A x‖₊ :=
  rfl

/-- This is often the more useful lemma to rewrite the norm as opposed to `Unitization.norm_def`. -/
theorem norm_eq_sup (x : Unitization 𝕜 A) :
    ‖x‖ = ‖x.fst‖ ⊔ ‖algebraMap 𝕜 (A →L[𝕜] A) x.fst + mul 𝕜 A x.snd‖ := by
  rw [norm_def, splitMul_apply, Prod.norm_def]

/-- This is often the more useful lemma to rewrite the norm as opposed to
`Unitization.nnnorm_def`. -/
theorem nnnorm_eq_sup (x : Unitization 𝕜 A) :
    ‖x‖₊ = ‖x.fst‖₊ ⊔ ‖algebraMap 𝕜 (A →L[𝕜] A) x.fst + mul 𝕜 A x.snd‖₊ :=
  NNReal.eq <| norm_eq_sup x

theorem lipschitzWith_addEquiv :
    LipschitzWith 2 (Unitization.addEquiv 𝕜 A) := by
  rw [← Real.toNNReal_ofNat]
  refine AddMonoidHomClass.lipschitz_of_bound (Unitization.addEquiv 𝕜 A) 2 fun x => ?_
  rw [norm_eq_sup, Prod.norm_def]
  refine max_le ?_ ?_
  · rw [mul_max_of_nonneg _ _ (zero_le_two : (0 : ℝ) ≤ 2)]
    exact le_max_of_le_left ((le_add_of_nonneg_left (norm_nonneg _)).trans_eq (two_mul _).symm)
  · nontriviality A
    rw [two_mul]
    calc
      ‖x.snd‖ = ‖mul 𝕜 A x.snd‖ :=
        .symm <| (isometry_mul 𝕜 A).norm_map_of_map_zero (map_zero _) _
      _ ≤ ‖algebraMap 𝕜 _ x.fst + mul 𝕜 A x.snd‖ + ‖x.fst‖ := by
        simpa only [add_comm _ (mul 𝕜 A x.snd), norm_algebraMap'] using
          norm_le_add_norm_add (mul 𝕜 A x.snd) (algebraMap 𝕜 _ x.fst)
      _ ≤ _ := add_le_add le_sup_right le_sup_left

theorem antilipschitzWith_addEquiv :
    AntilipschitzWith 2 (addEquiv 𝕜 A) := by
  refine AddMonoidHomClass.antilipschitz_of_bound (addEquiv 𝕜 A) fun x => ?_
  rw [norm_eq_sup, Prod.norm_def, NNReal.coe_two]
  refine max_le ?_ ?_
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
open scoped Uniformity Topology

theorem uniformity_eq_aux :
    𝓤[instUniformSpaceProd.comap <| addEquiv 𝕜 A] = 𝓤 (Unitization 𝕜 A) := by
  have key : IsUniformInducing (addEquiv 𝕜 A) :=
    antilipschitzWith_addEquiv.isUniformInducing lipschitzWith_addEquiv.uniformContinuous
  rw [← key.comap_uniformity]
  rfl

theorem cobounded_eq_aux :
    @cobounded _ (Bornology.induced <| addEquiv 𝕜 A) = cobounded (Unitization 𝕜 A) :=
  le_antisymm lipschitzWith_addEquiv.comap_cobounded_le
    antilipschitzWith_addEquiv.tendsto_cobounded.le_comap

end Aux

/-- The uniformity on `Unitization 𝕜 A` is inherited from `𝕜 × A`. -/
instance instUniformSpace : UniformSpace (Unitization 𝕜 A) :=
  instUniformSpaceProd.comap (addEquiv 𝕜 A)

/-- The natural equivalence between `Unitization 𝕜 A` and `𝕜 × A` as a uniform equivalence. -/
def uniformEquivProd : (Unitization 𝕜 A) ≃ᵤ (𝕜 × A) :=
  Equiv.toUniformEquivOfIsUniformInducing (addEquiv 𝕜 A) ⟨rfl⟩

/-- The bornology on `Unitization 𝕜 A` is inherited from `𝕜 × A`. -/
instance instBornology : Bornology (Unitization 𝕜 A) :=
  Bornology.induced <| addEquiv 𝕜 A

theorem isUniformEmbedding_addEquiv {𝕜} [NontriviallyNormedField 𝕜] :
    IsUniformEmbedding (addEquiv 𝕜 A) where
  comap_uniformity := rfl
  injective := (addEquiv 𝕜 A).injective

/-- `Unitization 𝕜 A` is complete whenever `𝕜` and `A` are also. -/
instance instCompleteSpace [CompleteSpace 𝕜] [CompleteSpace A] :
    CompleteSpace (Unitization 𝕜 A) :=
  uniformEquivProd.completeSpace_iff.2 .prod

instance instT2Space : T2Space (Unitization 𝕜 A) :=
  Unitization.uniformEquivProd.symm.toHomeomorph.t2Space

/-- Pull back the metric structure from `𝕜 × (A →L[𝕜] A)` to `Unitization 𝕜 A` using the
algebra homomorphism `Unitization.splitMul 𝕜 A`, but replace the bornology and the uniformity so
that they coincide with `𝕜 × A`. -/
noncomputable instance instMetricSpace : MetricSpace (Unitization 𝕜 A) :=
  (normedRingAux.toMetricSpace.replaceUniformity uniformity_eq_aux).replaceBornology
    fun s => Filter.ext_iff.1 cobounded_eq_aux (sᶜ)

/-- Pull back the normed ring structure from `𝕜 × (A →L[𝕜] A)` to `Unitization 𝕜 A` using the
algebra homomorphism `Unitization.splitMul 𝕜 A`. -/
noncomputable instance instNormedRing : NormedRing (Unitization 𝕜 A) where
  dist_eq := normedRingAux.dist_eq
  norm_mul_le := normedRingAux.norm_mul_le
  norm := normedRingAux.norm

/-- Pull back the normed algebra structure from `𝕜 × (A →L[𝕜] A)` to `Unitization 𝕜 A` using the
algebra homomorphism `Unitization.splitMul 𝕜 A`. -/
instance instNormedAlgebra : NormedAlgebra 𝕜 (Unitization 𝕜 A) where
  norm_smul_le k x := by rw [norm_def, map_smul, norm_smul, ← norm_def]

instance instNormOneClass : NormOneClass (Unitization 𝕜 A) where
  norm_one := by simpa only [norm_eq_sup, fst_one, norm_one, snd_one, map_one, map_zero,
      add_zero, sup_eq_left] using opNorm_le_bound _ zero_le_one fun x => by simp

lemma norm_inr (a : A) : ‖(a : Unitization 𝕜 A)‖ = ‖a‖ := by
  simp [norm_eq_sup]

lemma nnnorm_inr (a : A) : ‖(a : Unitization 𝕜 A)‖₊ = ‖a‖₊ :=
  NNReal.eq <| norm_inr a

lemma isometry_inr : Isometry ((↑) : A → Unitization 𝕜 A) :=
  AddMonoidHomClass.isometry_of_norm (inrNonUnitalAlgHom 𝕜 A) norm_inr

@[fun_prop]
theorem continuous_inr : Continuous (inr : A → Unitization 𝕜 A) :=
  isometry_inr.continuous

lemma dist_inr (a b : A) : dist (a : Unitization 𝕜 A) (b : Unitization 𝕜 A) = dist a b :=
  isometry_inr.dist_eq a b

lemma nndist_inr (a b : A) : nndist (a : Unitization 𝕜 A) (b : Unitization 𝕜 A) = nndist a b :=
  isometry_inr.nndist_eq a b

/- These examples verify that the bornology and uniformity (hence also the topology) are the
correct ones. -/
example : (instNormedRing (𝕜 := 𝕜) (A := A)).toMetricSpace = instMetricSpace := rfl
example : (instMetricSpace (𝕜 := 𝕜) (A := A)).toBornology = instBornology := rfl
example : (instMetricSpace (𝕜 := 𝕜) (A := A)).toUniformSpace = instUniformSpace := rfl

section

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]

protected theorem uniformContinuous_fst : UniformContinuous (fun x : Unitization 𝕜 A ↦ x.fst) :=
  uniformContinuous_fst.comp Unitization.uniformEquivProd.uniformContinuous

protected theorem uniformContinuous_snd : UniformContinuous (fun x : Unitization 𝕜 A ↦ x.snd) :=
  uniformContinuous_snd.comp Unitization.uniformEquivProd.uniformContinuous

@[fun_prop]
protected theorem continuous_fst : Continuous (fun x : Unitization 𝕜 A ↦ x.fst) :=
  Unitization.uniformContinuous_fst.continuous

@[fun_prop]
protected theorem continuous_snd : Continuous (fun x : Unitization 𝕜 A ↦ x.snd) :=
  Unitization.uniformContinuous_snd.continuous

end

end Unitization
