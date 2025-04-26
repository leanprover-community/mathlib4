/-
Copyright (c) 2025 Hanliu Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanwen Wang, Hanliu Jiang
-/

import Mathlib.NumberTheory.Padics.PSAC2
import Mathlib.RingTheory.Kaehler.Basic


set_option maxHeartbeats 10000000000000
set_option synthInstance.maxHeartbeats 10000000000000


open Finset IsUltrametricDist NNReal Filter  CauSeq  zero_atBot KaehlerDifferential
open scoped fwdDiff ZeroAtInfty Topology  LaurentSeries PowerSeries
variable {p : ℕ} [hp : Fact p.Prime]

namespace PadicInt

lemma ds4(a:C_₀(ℤ,ℤ_[p]))(r:ℤ) :p_sequence_coeff (p:=p) r
 (AdicCompletion.mk (Ideal.span {(p:ℤ_[p]⸨X⸩)})
 ℤ_[p]⸨X⸩ (Adic_Complection_tofun a))= a r:=by
  have:=esg (p:=p) r (AdicCompletion.mk (Ideal.span {(p:ℤ_[p]⸨X⸩)})
 ℤ_[p]⸨X⸩ (Adic_Complection_tofun a)) (Adic_Complection_tofun a) rfl
  rw[this]
  unfold cauchy_sequence_coeff AdicCompletion.mapAlg
   Cauchy.seq_map Cauchy_p_adic  HahnSeries.coeff_map_0 Adic_Complection_tofun
  simp only [LinearMap.coe_mk, AddHom.coe_mk,LinearMap.coe_comp,
    Function.comp_apply, HahnSeries.ofSuppBddBelow_coeff]
  refine helper3 _ _ ?_
  unfold CauSeq.LimZero
  intro s hs
  rcases (LE.le.eq_or_gt (norm_nonneg (a r))) with r1|r2
  · use 0
    intro e sr
    simp only [ sub_apply, const_apply]
    rw[r1]
    simp
    rw[r1]
    exact hs
  · obtain ⟨m, hm⟩ := exists_pow_neg_lt p r2
    use m
    intro t tm
    simp only [ sub_apply, const_apply]
    have:¬  ‖a r‖ ≤ (p:ℝ) ^ (-t:ℤ):=by
      by_contra se
      have:¬ (p:ℝ) ^ (-t:ℤ) > (p:ℝ) ^ (-m:ℤ) :=by
        simp only [ gt_iff_lt, not_lt]
        refine (zpow_le_zpow_iff_right₀ ?_).mpr ?_
        simp
        refine Nat.Prime.one_lt (hp.1)
        simp
        exact tm
      exact this (gt_of_ge_of_gt se hm)
    simp only[this]
    simp
    exact hs
noncomputable def Adic_Complection_equiv_srmm: (AdicCompletion (Ideal.span {(p:ℤ_[p]⸨X⸩)})
 (ℤ_[p]⸨X⸩)) ≃ₗ[ℤ_[p]]
 C_₀(ℤ,ℤ_[p]) where
   toFun a:= ⟨⟨fun n ↦  p_sequence_coeff (p:=p) n a,continuous_of_discreteTopology⟩,
    Tends_to_Zero' a⟩
   map_add' a b:=by
     ext s
     simp
   map_smul' a b:=by
     ext s
     simp
   invFun a :=AdicCompletion.mk (Ideal.span {(p:ℤ_[p]⸨X⸩)}) ℤ_[p]⸨X⸩
    (Adic_Complection_tofun a)
   left_inv r:=by exact ds3 r
   right_inv m:= by
    ext n
    exact ds4  m n

#check HahnSeries.coeff_mul
#check  Set.Elem

lemma  help6 (f:(AdicCompletion.AdicCauchySequence (Ideal.span {(p:ℤ_[p]⸨X⸩)}) (ℤ_[p]⸨X⸩))):
     ((AdicCompletion.mk (Ideal.span {(p:ℤ_[p]⸨X⸩)}) ℤ_[p]⸨X⸩) f)=
     ((AdicCompletion.mkₐ (Ideal.span {(p:ℤ_[p]⸨X⸩)})) f) :=by rfl
theorem p_sequence_coeff_mul (n:ℤ)
(f g:(AdicCompletion (Ideal.span {(p:ℤ_[p]⸨X⸩)}) (ℤ_[p]⸨X⸩))):
p_sequence_coeff (p:=p) n (f*g) =∑' ( a : (Set.mulAntidiagonal ⊤ ⊤ n) ),
p_sequence_coeff (p:=p) a.1.1 f* p_sequence_coeff (p:=p) a.1.2 g :=by
  have:=by
      exact AdicCompletion.mk_surjective (Ideal.span {(p:ℤ_[p]⸨X⸩)}) ℤ_[p]⸨X⸩
  unfold Function.Surjective at this
  rcases (this (f)) with ⟨f1,f2⟩
  rcases (this (g)) with ⟨g1,g2⟩
  have le:
  ((AdicCompletion.mk (Ideal.span {(p:ℤ_[p]⸨X⸩)}) ℤ_[p]⸨X⸩) (f1*g1))=f*g :=by
    rw[help6,map_mul,← help6,← help6,f2,g2]
  have( a : (Set.mulAntidiagonal ⊤ ⊤ n) ):
p_sequence_coeff (p:=p) a.1.1 f* p_sequence_coeff (p:=p) a.1.2 g =
    cauchy_sequence_coeff (p:=p) a.1.1 f1* cauchy_sequence_coeff (p:=p) a.1.2 g1 :=by
     rw[esg a.1.1 f f1 f2,esg a.1.2 g g1 g2]
  rw[tsum_congr this,esg _ _  _ le]
  unfold cauchy_sequence_coeff AdicCompletion.mapAlg
   Cauchy.seq_map Cauchy_p_adic  HahnSeries.coeff_map_0
  simp
  have:(fun m =>(f1 m * g1 m).coeff n)=fun m => (∑ ij ∈ addAntidiagonal (f1 m).isPWO_support
    (g1 m).isPWO_support n,
   (f1 m).coeff ij.1 * (g1 m).coeff ij.2 ):=by rfl
  simp[this]
  


  sorry




end PadicInt
