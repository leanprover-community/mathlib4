/-
Copyright (c) 2025 Hanliu Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanwen Wang, Hanliu Jiang
-/
import Mathlib.NumberTheory.Padics.AmiceTrans
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.Algebra.Exact

set_option maxHeartbeats 1000000000000000000000000000000000000000000
set_option synthInstance.maxHeartbeats 1000000000000000000000000000000
open Finset IsUltrametricDist NNReal Filter

open scoped fwdDiff ZeroAtInfty Topology
open scoped fwdDiff ZeroAtInfty Topology  LaurentSeries PowerSeries
variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {P : Type*} [AddCommGroup P] [Module R P]
variable {T : Type*} [AddCommGroup T] [Module (AdicCompletion I R) T]

namespace LinearMap
noncomputable def adicCompletionAux (f : M →ₗ[R] N) :
    AdicCompletion I M →ₗ[R] AdicCompletion I N :=
  AdicCompletion.lift I (fun n ↦ reduceModIdeal (I ^ n) f ∘ₗ AdicCompletion.eval I M n)
    (fun {m n} hmn ↦ by rw [← comp_assoc, AdicCompletion.transitionMap_comp_reduceModIdeal,
        comp_assoc, AdicCompletion.transitionMap_comp_eval])

@[local simp]
 theorem adicCompletionAux_val_apply (f : M →ₗ[R] N) {n : ℕ} (x : AdicCompletion I M) :
    (adicCompletionAux I f x).val n = f.reduceModIdeal (I ^ n) (x.val n) :=
  rfl
end LinearMap
variable {p : ℕ} [hp : Fact p.Prime]

namespace PadicInt


noncomputable def Amice_Trans_in_P:ℤ_[p]⟦X⟧ →ₗ[ℤ_[p]]
AdicCompletion (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]⸨X⸩ where
  toFun a:=(AdicCompletion.of (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]⸨X⸩) a
  map_add' a b:=by
   simp

  map_smul' z b:=by
    simp


noncomputable def HahnSeries.coeff_map_0 (a:ℤ):ℤ_[p]⸨X⸩ →ₗ[ℤ_[p]]
 ℤ_[p]where
   toFun b:=(HahnSeries.coeff b) a
   map_add' _ _:=rfl
   map_smul' _ _:=rfl


noncomputable def Cauchy_p_adic (f:AdicCompletion.AdicCauchySequence
 (IsLocalRing.maximalIdeal ℤ_[p]) (ℤ_[p])): CauSeq ℤ_[p] norm where
   val :=f.1
   property :=by
     rcases f with ⟨f_s,hx⟩
     unfold AdicCompletion.IsAdicCauchy at hx
     intro ε hε
     simp only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.sub_mem, maximalIdeal_eq_span_p,
      Ideal.span_singleton_pow, ← norm_le_pow_iff_mem_span_pow] at hx ⊢
     obtain ⟨m, hm⟩ := exists_pow_neg_lt p hε
     refine ⟨m, fun n hn => lt_of_le_of_lt ?_ hm⟩
     rw [← neg_sub, norm_neg]
     exact hx hn
lemma CauchyL (b:ℝ)(a:CauSeq ℤ_[p] norm)(hs:∀n , ‖a.val n‖≤ b):‖a.lim‖≤b:=by

     sorry



noncomputable def Cauchy.seq_map :AdicCompletion.AdicCauchySequence
 (IsLocalRing.maximalIdeal ℤ_[p]) (ℤ_[p])
  →ₗ[ℤ_[p]] (ℤ_[p])where
    toFun a:=(Cauchy_p_adic a).lim
    map_add' a b:=by
      unfold Cauchy_p_adic
      rw[CauSeq.lim_add]
      exact rfl
    map_smul' u v:=by
      simp
      unfold Cauchy_p_adic
      rw[mul_comm,CauSeq.lim_mul]
      refine CauSeq.lim_eq_lim_of_equiv ?_
      unfold CauSeq.const
      have:(u • v).1 =(v.1)*(fun n=> u):=by
          ext n
          simp
          ring
      simp[this]
      exact CauSeq.Completion.mk_eq.mp rfl

#check
(Cauchy.seq_map (p:=p))∘ₗ(AdicCompletion.AdicCauchySequence.map  (IsLocalRing.maximalIdeal ℤ_[p])
 (HahnSeries.coeff_map_0 (p:=p) 1))
noncomputable abbrev cauchy_sequence_coeff (a:ℤ ) :=(Cauchy.seq_map (p:=p))∘ₗ(AdicCompletion.AdicCauchySequence.map  (IsLocalRing.maximalIdeal ℤ_[p])
 (HahnSeries.coeff_map_0 (p:=p) a))
lemma cauchy_sequence_coeff_tends_to_zero
  (f:AdicCompletion.AdicCauchySequence (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]⸨X⸩ ):
  Filter.Tendsto (fun n:ℕ => cauchy_sequence_coeff (p:=p) (-n:ℤ ) f) Filter.atTop
(nhds 0):=by
  refine NormedAddCommGroup.tendsto_atTop.mpr ?_
  intro h sh
  simp only [sub_zero]
  obtain ⟨m, hm⟩ := exists_pow_neg_lt p sh
  use ((f.1 m).order).toNat
  intro n sn
  refine lt_of_le_of_lt ?_ hm
  simp only [LinearMap.coe_comp, Function.comp_apply]
  unfold Cauchy.seq_map
  simp only [LinearMap.coe_mk, AddHom.coe_mk]


  sorry
noncomputable def Cauchy_p_adic_2:AdicCompletion.AdicCauchySequence
 (IsLocalRing.maximalIdeal ℤ_[p]) (ℤ_[p])
  →ₗ[ℤ_[p]] AdicCompletion
 (IsLocalRing.maximalIdeal ℤ_[p]) (ℤ_[p]):=(AdicCompletion.mk (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p])
lemma ss: LinearMap.ker ((AdicCompletion.mk (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]))
 ≤ LinearMap.ker (Cauchy.seq_map (p:=p)):=by
   intro x hs
   simp_all
   have (n:ℕ):( (AdicCompletion.mk (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]) x).val n  = 0:=by
    rw[hs]
    simp
   unfold AdicCompletion.mk at this
   simp at this
   unfold Cauchy.seq_map
   simp
   have:CauSeq.LimZero (Cauchy_p_adic x) :=by
    unfold CauSeq.LimZero Cauchy_p_adic
    intro a ha
    simp
    obtain ⟨m, hm⟩ := exists_pow_neg_lt p ha
    use m
    intro j sj
    refine  lt_of_le_of_lt ?_ hm
    have:x j ∈ (IsLocalRing.maximalIdeal ℤ_[p] ^ j * ⊤):=by exact
      (Submodule.Quotient.mk_eq_zero (IsLocalRing.maximalIdeal ℤ_[p] ^ j * ⊤)).mp (this j)
    simp only [Ideal.mul_top,maximalIdeal_eq_span_p] at this
    rw[norm_le_pow_iff_mem_span_pow,←Ideal.span_singleton_pow]
    exact (Ideal.pow_le_pow_right sj) this
   exact (CauSeq.lim_eq_zero_iff (Cauchy_p_adic x)).mpr this
#check Submodule.liftQ (LinearMap.ker ((AdicCompletion.mk (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p])))
 (Cauchy.seq_map (p:=p)) (ss (p:=p))

noncomputable def FunctionTrans_1:(AdicCompletion.AdicCauchySequence (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p] ⧸
    LinearMap.ker (AdicCompletion.mk (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]))≃ₗ[ℤ_[p]]
    AdicCompletion (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]:=by
     refine
      (AdicCompletion.mk (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]).quotKerEquivOfSurjective
       (AdicCompletion.mk_surjective (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p])

noncomputable abbrev p_sequence_coeff (a:ℤ ):=
    Submodule.liftQ (LinearMap.ker ((AdicCompletion.mk (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p])))
 (Cauchy.seq_map (p:=p)) (ss (p:=p))∘ₗ  ((FunctionTrans_1 (p:=p )).symm).toLinearMap
  ∘ₗ  (LinearMap.adicCompletionAux (IsLocalRing.maximalIdeal ℤ_[p]) (HahnSeries.coeff_map_0 (p:=p) a))
#check p_sequence_coeff (p:=p) (1)
lemma Tends_to_Zero_0(a:(AdicCompletion (IsLocalRing.maximalIdeal ℤ_[p]) (ℤ_[p]⸨X⸩)))
:Filter.Tendsto (fun n:ℕ => p_sequence_coeff (-n:ℤ ) a) Filter.atTop
(nhds 0):=by
  refine NormedAddCommGroup.tendsto_atTop.mpr ?_
  intro h sh
  simp only [sub_zero]


  sorry
lemma Tends_to_Zero(a:(AdicCompletion (IsLocalRing.maximalIdeal ℤ_[p]) (ℤ_[p]⸨X⸩)))
:Filter.Tendsto (fun n:ℕ => p_sequence_coeff (-n-1:ℤ ) a-p_sequence_coeff (-n-2:ℤ ) a) Filter.atTop
(nhds 0):=by


  sorry
noncomputable def FunctionTrans_2: (AdicCompletion (IsLocalRing.maximalIdeal ℤ_[p]) (ℤ_[p]⸨X⸩)) →ₗ[ℤ_[p]]
 C₀(ℕ, ℤ_[p]) where
   toFun a :=⟨⟨(fun n:ℕ => p_sequence_coeff (-n-1:ℤ ) a-p_sequence_coeff (-n-2:ℤ ) a)
    ,continuous_of_discreteTopology⟩, cocompact_eq_atTop (α := ℕ) ▸ Tends_to_Zero a⟩
   map_add'  a b:=by
     ext n
     simp
     ring
   map_smul' a b:=by
     ext s
     simp
     ring

noncomputable def mahler_Int:C₀(ℕ, ℤ_[p]) ≃ₗ[ℤ_[p]]C(ℤ_[p], ℤ_[p])  :=sorry
noncomputable def Amice_Int:(ContinuousLinearMap (RingHom.id ℤ_[p]) C(ℤ_[p],ℤ_[p]) ℤ_[p])
 ≃ₗ[ℤ_[p]] ℤ_[p]⟦X⟧ :=sorry
lemma exact :Function.Exact (Amice_Trans_in_P (p:=p) ∘ₗ Amice_Int.toLinearMap)
  ( (mahler_Int (p:=p)).toLinearMap ∘ₗ FunctionTrans_2 (p:=p) ) :=by
   refine  LinearMap.exact_iff.mpr ?_

   sorry
