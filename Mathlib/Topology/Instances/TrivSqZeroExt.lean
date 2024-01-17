/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Algebra.Module.Prod

#align_import topology.instances.triv_sq_zero_ext from "leanprover-community/mathlib"@"b8d2eaa69d69ce8f03179a5cda774fc0cde984e4"

/-!
# Topology on `TrivSqZeroExt R M`

The type `TrivSqZeroExt R M` inherits the topology from `R × M`.

Note that this is not the topology induced by the seminorm on the dual numbers suggested by
[this Math.SE answer](https://math.stackexchange.com/a/1056378/1896), which instead induces
the topology pulled back through the projection map `TrivSqZeroExt.fst : tsze R M → R`.
Obviously, that topology is not Hausdorff and using it would result in `exp` converging to more than
one value.

## Main results

* `TrivSqZeroExt.topologicalRing`: the ring operations are continuous

-/


variable {α S R M : Type*}

-- mathport name: exprtsze
local notation "tsze" => TrivSqZeroExt

namespace TrivSqZeroExt

variable [TopologicalSpace R] [TopologicalSpace M]

instance : TopologicalSpace (tsze R M) :=
  TopologicalSpace.induced fst ‹_› ⊓ TopologicalSpace.induced snd ‹_›

instance [T2Space R] [T2Space M] : T2Space (tsze R M) :=
  Prod.t2Space

theorem nhds_def (x : tsze R M) : nhds x = (nhds x.fst).prod (nhds x.snd) := by
  cases x
  exact nhds_prod_eq
#align triv_sq_zero_ext.nhds_def TrivSqZeroExt.nhds_def

theorem nhds_inl [Zero M] (x : R) : nhds (inl x : tsze R M) = (nhds x).prod (nhds 0) :=
  nhds_def _
#align triv_sq_zero_ext.nhds_inl TrivSqZeroExt.nhds_inl

theorem nhds_inr [Zero R] (m : M) : nhds (inr m : tsze R M) = (nhds 0).prod (nhds m) :=
  nhds_def _
#align triv_sq_zero_ext.nhds_inr TrivSqZeroExt.nhds_inr

nonrec theorem continuous_fst : Continuous (fst : tsze R M → R) :=
  continuous_fst
#align triv_sq_zero_ext.continuous_fst TrivSqZeroExt.continuous_fst

nonrec theorem continuous_snd : Continuous (snd : tsze R M → M) :=
  continuous_snd
#align triv_sq_zero_ext.continuous_snd TrivSqZeroExt.continuous_snd

theorem continuous_inl [Zero M] : Continuous (inl : R → tsze R M) :=
  continuous_id.prod_mk continuous_const
#align triv_sq_zero_ext.continuous_inl TrivSqZeroExt.continuous_inl

theorem continuous_inr [Zero R] : Continuous (inr : M → tsze R M) :=
  continuous_const.prod_mk continuous_id
#align triv_sq_zero_ext.continuous_inr TrivSqZeroExt.continuous_inr

theorem embedding_inl [Zero M] : Embedding (inl : R → tsze R M) :=
  embedding_of_embedding_compose continuous_inl continuous_fst embedding_id
#align triv_sq_zero_ext.embedding_inl TrivSqZeroExt.embedding_inl

theorem embedding_inr [Zero R] : Embedding (inr : M → tsze R M) :=
  embedding_of_embedding_compose continuous_inr continuous_snd embedding_id
#align triv_sq_zero_ext.embedding_inr TrivSqZeroExt.embedding_inr

variable (R M)

/-- `TrivSqZeroExt.fst` as a continuous linear map. -/
@[simps]
def fstClm [CommSemiring R] [AddCommMonoid M] [Module R M] : tsze R M →L[R] R :=
  { ContinuousLinearMap.fst R R M with toFun := fst }
#align triv_sq_zero_ext.fst_clm TrivSqZeroExt.fstClm

/-- `TrivSqZeroExt.snd` as a continuous linear map. -/
@[simps]
def sndClm [CommSemiring R] [AddCommMonoid M] [Module R M] : tsze R M →L[R] M :=
  { ContinuousLinearMap.snd R R M with
    toFun := snd
    cont := continuous_snd }
#align triv_sq_zero_ext.snd_clm TrivSqZeroExt.sndClm

/-- `TrivSqZeroExt.inl` as a continuous linear map. -/
@[simps]
def inlClm [CommSemiring R] [AddCommMonoid M] [Module R M] : R →L[R] tsze R M :=
  { ContinuousLinearMap.inl R R M with toFun := inl }
#align triv_sq_zero_ext.inl_clm TrivSqZeroExt.inlClm

/-- `TrivSqZeroExt.inr` as a continuous linear map. -/
@[simps]
def inrClm [CommSemiring R] [AddCommMonoid M] [Module R M] : M →L[R] tsze R M :=
  { ContinuousLinearMap.inr R R M with toFun := inr }
#align triv_sq_zero_ext.inr_clm TrivSqZeroExt.inrClm

variable {R M}

instance [Add R] [Add M] [ContinuousAdd R] [ContinuousAdd M] : ContinuousAdd (tsze R M) :=
  Prod.continuousAdd

instance [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] [ContinuousMul R] [ContinuousSMul R M]
    [ContinuousSMul Rᵐᵒᵖ M] [ContinuousAdd M] : ContinuousMul (tsze R M) :=
  ⟨((continuous_fst.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).prod_mk <|
      ((continuous_fst.comp continuous_fst).smul (continuous_snd.comp continuous_snd)).add
        ((MulOpposite.continuous_op.comp <| continuous_fst.comp <| continuous_snd).smul
          (continuous_snd.comp continuous_fst))⟩

instance [Neg R] [Neg M] [ContinuousNeg R] [ContinuousNeg M] : ContinuousNeg (tsze R M) :=
  Prod.continuousNeg

/-- This is not an instance due to complaints by the `fails_quickly` linter. At any rate, we only
really care about the `TopologicalRing` instance below. -/
theorem topologicalSemiring [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
    [TopologicalSemiring R] [ContinuousAdd M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M] :
    TopologicalSemiring (tsze R M) := { }
#align triv_sq_zero_ext.topological_semiring TrivSqZeroExt.topologicalSemiring

instance [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [TopologicalRing R]
    [TopologicalAddGroup M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M] :
    TopologicalRing (tsze R M) where

instance [SMul S R] [SMul S M] [ContinuousConstSMul S R] [ContinuousConstSMul S M] :
    ContinuousConstSMul S (tsze R M) :=
  Prod.continuousConstSMul

instance [TopologicalSpace S] [SMul S R] [SMul S M] [ContinuousSMul S R] [ContinuousSMul S M] :
    ContinuousSMul S (tsze R M) :=
  Prod.continuousSMul

variable (M)

theorem hasSum_inl [AddCommMonoid R] [AddCommMonoid M] {f : α → R} {a : R} (h : HasSum f a) :
    HasSum (fun x ↦ inl (f x)) (inl a : tsze R M) :=
  h.map (⟨⟨inl, inl_zero _⟩, inl_add _⟩ : R →+ tsze R M) continuous_inl
#align triv_sq_zero_ext.has_sum_inl TrivSqZeroExt.hasSum_inl

theorem hasSum_inr [AddCommMonoid R] [AddCommMonoid M] {f : α → M} {a : M} (h : HasSum f a) :
    HasSum (fun x ↦ inr (f x)) (inr a : tsze R M) :=
  h.map (⟨⟨inr, inr_zero _⟩, inr_add _⟩ : M →+ tsze R M) continuous_inr
#align triv_sq_zero_ext.has_sum_inr TrivSqZeroExt.hasSum_inr

theorem hasSum_fst [AddCommMonoid R] [AddCommMonoid M] {f : α → tsze R M} {a : tsze R M}
    (h : HasSum f a) : HasSum (fun x ↦ fst (f x)) (fst a) :=
  h.map (⟨⟨fst, fst_zero⟩, fst_add⟩ : tsze R M →+ R) continuous_fst
#align triv_sq_zero_ext.has_sum_fst TrivSqZeroExt.hasSum_fst

theorem hasSum_snd [AddCommMonoid R] [AddCommMonoid M] {f : α → tsze R M} {a : tsze R M}
    (h : HasSum f a) : HasSum (fun x ↦ snd (f x)) (snd a) :=
  h.map (⟨⟨snd, snd_zero⟩, snd_add⟩ : tsze R M →+ M) continuous_snd
#align triv_sq_zero_ext.has_sum_snd TrivSqZeroExt.hasSum_snd

end TrivSqZeroExt
