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
import Mathlib.Topology.ContinuousMap.ZeroAtBot

set_option maxHeartbeats 1000000000000000000000000000000000000000000
set_option synthInstance.maxHeartbeats 1000000000000000000000000000000

open Finset IsUltrametricDist NNReal Filter  CauSeq  zero_atBot


open scoped fwdDiff ZeroAtInfty Topology
open scoped fwdDiff ZeroAtInfty Topology  LaurentSeries PowerSeries
variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {P : Type*} [AddCommGroup P] [Module R P]
variable {T : Type*} [AddCommGroup T] [Module (AdicCompletion I R) T]

/-
theorem NormedAddCommGroup.tendsto_atBot [Nonempty α] [Preorder α] [IsDirected α (· ≥  ·)]
    {β : Type*} [SeminormedAddCommGroup β] {f : α → β} {b : β} :
    Tendsto f atBot (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N ≥ n → ‖f n - b‖ < ε :=
  (atBot_basis.tendsto_iff Metric.nhds_basis_ball).trans (by simp [dist_eq_norm])
  -/
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
lemma CauchyL (b:ℝ)(a:CauSeq ℤ_[p] norm)(hs:∃ m ,∀ n≥ m , ‖a.val n‖≤ b):‖a.lim‖≤b:=by
   by_contra sr
   simp at sr
   obtain ⟨m,hm⟩:=hs
   obtain ⟨i,sh⟩:=equiv_def₃ (equiv_lim a) (sub_pos.mpr sr)
   have:=sh  (max m i) ( Nat.le_max_right m i) (max m i) (Nat.le_refl (max m i))
   simp at this
   have:¬ ‖(a.val (max m i))-a.lim‖ < ‖a.lim‖ - b :=by
       simp
       have: ‖a.lim‖≤ ‖(a.val (max m i))-a.lim‖+‖(a.val (max m i))‖:=by
        rw[Eq.symm (norm_neg a.lim),Eq.symm (norm_neg (a.val (max m i)))]
        have:-a.lim=(a.val (max m i))-a.lim +(- (a.val (max m i))) :=by ring_nf
        rw[this]
        exact norm_add_le (a.val (max m i) - a.lim) (-a.val (max m i))
       exact le_add_of_le_add_left this (hm (max m i)  ( Nat.le_max_left m i))
   (expose_names; exact this this_1)

#check C_₀(ℤ,ℤ_[p])


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
noncomputable abbrev cauchy_sequence_coeff (a:ℤ ) :=
 (Cauchy.seq_map (p:=p))∘ₗ(AdicCompletion.AdicCauchySequence.map  (IsLocalRing.maximalIdeal ℤ_[p])
 (HahnSeries.coeff_map_0 (p:=p) a))
lemma powerseries_equiv(m:ℕ)(s :ℤ)(f g :ℤ_[p]⸨X⸩)
   (hs:f ≡ g [SMOD  (IsLocalRing.maximalIdeal ℤ_[p] ^ m • ⊤ : Submodule ℤ_[p] ℤ_[p]⸨X⸩)]):
((HahnSeries.coeff_map_0 s) f) -
   ((HahnSeries.coeff_map_0 s) g) ∈ Ideal.span {↑p} ^ m:=by
    simp only [SModEq.sub_mem,zero_sub, neg_mem_iff,
     maximalIdeal_eq_span_p,Ideal.span_singleton_pow]
    simp only [SModEq.sub_mem,zero_sub, neg_mem_iff ,
     maximalIdeal_eq_span_p,Ideal.span_singleton_pow,Submodule.ideal_span_singleton_smul]
      at hs
    rw[← Submodule.singleton_set_smul,Submodule.mem_singleton_set_smul ] at hs
    choose u se1 se2 using hs
    rw[Eq.symm (LinearMap.map_sub (HahnSeries.coeff_map_0 s) f g),Ideal.mem_span_singleton']
    rw[se2]
    simp
    use (HahnSeries.coeff_map_0 s) u
    ring

lemma cauchy_sequence_coeff_tends_to_zero
  (f:AdicCompletion.AdicCauchySequence (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]⸨X⸩ ):
  Filter.Tendsto (fun n:ℕ => cauchy_sequence_coeff (p:=p) (-n:ℤ ) f) Filter.atTop
(nhds 0):=by
  refine NormedAddCommGroup.tendsto_atTop.mpr ?_
  intro h sh
  simp only [sub_zero]
  obtain ⟨m, hm⟩ := exists_pow_neg_lt p sh
  have:∃ w:ℕ , -w<(f.1 m).order :=by
     rcases Int.lt_or_le 0 (HahnSeries.order (f.1 m)) with r1|r2
     use 0
     simp
     exact r1
     have:∃ a:ℕ , a=(-HahnSeries.order (f.1 m) +1 ):=by
       refine CanLift.prf (-HahnSeries.order (f.1 m) + 1) ?_
       refine Int.le_neg_add_of_add_le ?_
       simp
       refine Int.le_of_lt (Int.lt_of_le_sub_one r2)
     choose a sa using this
     use a
     rw[sa]
     simp
  choose w sw using this
  use w
  intro n sn
  refine lt_of_le_of_lt ?_ hm
  have:∀ {m n : ℕ}, m ≤ n → f.1 m ≡ f.1 n
   [SMOD ( IsLocalRing.maximalIdeal ℤ_[p] ^ m • ⊤ : Submodule ℤ_[p] ℤ_[p]⸨X⸩)]:=by
    rcases f with ⟨w1,w2⟩
    simp
    exact w2
  unfold cauchy_sequence_coeff Cauchy.seq_map
  simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
  refine CauchyL (p:=p) ((p:ℝ)^ (-m:ℤ)) (Cauchy_p_adic ((AdicCompletion.AdicCauchySequence.map
    (IsLocalRing.maximalIdeal ℤ_[p]) (HahnSeries.coeff_map_0 (-n:ℤ))) f)) ?_
  use m
  intro l sl
  unfold Cauchy_p_adic
  simp only [AdicCompletion.AdicCauchySequence.map_apply_coe]

  have s1:=by
      exact powerseries_equiv m (-↑n) (f.1 m) (f.1 l) (this sl)

  have s2 :((HahnSeries.coeff_map_0 (-n:ℤ)) (f.1 m))=0 :=by
     refine HahnSeries.coeff_eq_zero_of_lt_order ?_
     have:(-n:ℤ)≤ -w :=by
        simp only [neg_le_neg_iff, Nat.cast_le,sn]
     exact Int.lt_of_le_of_lt this sw

  rw[s2] at s1
  simp only [maximalIdeal_eq_span_p,SModEq.sub_mem,zero_sub, neg_mem_iff] at s1
  rw[norm_le_pow_iff_mem_span_pow,←Ideal.span_singleton_pow]
  exact s1



noncomputable def Cauchy_p_adic_2:AdicCompletion.AdicCauchySequence
 (IsLocalRing.maximalIdeal ℤ_[p]) (ℤ_[p])
  →ₗ[ℤ_[p]] AdicCompletion
 (IsLocalRing.maximalIdeal ℤ_[p]) (ℤ_[p]):=
 (AdicCompletion.mk (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p])
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



   -- exact (LinearMap.ker (AdicCompletion.mk (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p])).mkQ

noncomputable def FunctionTrans_1:(AdicCompletion.AdicCauchySequence
(IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p] ⧸
    LinearMap.ker (AdicCompletion.mk (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]))≃ₗ[ℤ_[p]]
    AdicCompletion (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]:=by
     refine
      (AdicCompletion.mk (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]).quotKerEquivOfSurjective
       (AdicCompletion.mk_surjective (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p])
 noncomputable abbrev p_sequence_coeff_0 (a:ℤ ):=((FunctionTrans_1 (p:=p )).symm).toLinearMap
  ∘ₗ  (LinearMap.adicCompletionAux (IsLocalRing.maximalIdeal ℤ_[p])
   (HahnSeries.coeff_map_0 (p:=p) a))
noncomputable abbrev p_sequence_coeff (a:ℤ ):=
    Submodule.liftQ (LinearMap.ker ((AdicCompletion.mk (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p])))
 (Cauchy.seq_map (p:=p)) (ss (p:=p))∘ₗ (p_sequence_coeff_0 a)


lemma Tends_to_Zero_3(f:(AdicCompletion (IsLocalRing.maximalIdeal ℤ_[p]) (ℤ_[p]⸨X⸩)))
:Tendsto (fun n ↦ (p_sequence_coeff n) f) atBot (𝓝 0):=by
  sorry
lemma Tends_to_Zero_0(f:(AdicCompletion (IsLocalRing.maximalIdeal ℤ_[p]) (ℤ_[p]⸨X⸩)))
:Filter.Tendsto (fun n:ℕ => p_sequence_coeff (-n:ℤ ) f) Filter.atTop
(nhds 0):=by
  have:=by
   exact AdicCompletion.mk_surjective (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]⸨X⸩
  unfold Function.Surjective at this
  rcases (this f) with ⟨r,rs⟩
  have :(fun n:ℕ => p_sequence_coeff (-n:ℤ ) f)=
    (fun n:ℕ => cauchy_sequence_coeff (p:=p) (-n:ℤ ) r) :=by
      ext n
      have: (p_sequence_coeff_0 (-n:ℤ ) f)=
       (LinearMap.ker (AdicCompletion.mk
        (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p])).mkQ
         ((AdicCompletion.AdicCauchySequence.map  (IsLocalRing.maximalIdeal ℤ_[p])
           (HahnSeries.coeff_map_0 (p:=p) (-n:ℤ ))) r ):=by
           rw[← rs]
           simp
           unfold FunctionTrans_1
           exact
             (LinearEquiv.symm_apply_eq
                   ((AdicCompletion.mk (IsLocalRing.maximalIdeal ℤ_[p])
                         ℤ_[p]).quotKerEquivOfSurjective
                     FunctionTrans_1._proof_25)).mpr
               rfl
      simp
      simp at this
      rw[this]
      simp
  rw[this]
  exact cauchy_sequence_coeff_tends_to_zero r
lemma Tends_to_Zero_1(f:(AdicCompletion (IsLocalRing.maximalIdeal ℤ_[p]) (ℤ_[p]⸨X⸩)))
:Filter.Tendsto (fun n:ℕ => p_sequence_coeff (-((n+1):ℕ ):ℤ ) f) Filter.atTop
(nhds 0):=by
  have:=Tends_to_Zero_0  (p:=p) f
  rw[NormedAddCommGroup.tendsto_atTop] at this
  refine NormedAddCommGroup.tendsto_atTop.mpr ?_
  intro h sh
  simp only [sub_zero]
  choose e se using (this h sh)
  use e
  intro r sf
  have:=se (r+1) (Nat.le_add_right_of_le sf)
  simp only [sub_zero] at this
  exact this
lemma Tends_to_Zero(a:(AdicCompletion (IsLocalRing.maximalIdeal ℤ_[p]) (ℤ_[p]⸨X⸩)))
:Filter.Tendsto (fun n:ℕ => p_sequence_coeff (-((n+1):ℕ ):ℤ ) a
-p_sequence_coeff (-((n+2):ℕ ):ℤ ) a) Filter.atTop
(nhds 0):=by
  have:=Tends_to_Zero_0  (p:=p) a
  rw[NormedAddCommGroup.tendsto_atTop] at this
  refine NormedAddCommGroup.tendsto_atTop.mpr ?_
  intro h sh
  simp only [sub_zero]
  choose e se using (this h sh)
  use e
  intro r sf
  rw[sub_eq_add_neg]
  have  := nonarchimedean ((p_sequence_coeff (-↑(r+ 1))) a)  (-(p_sequence_coeff (-↑(r+ 2))) a)
  have m : ‖(p_sequence_coeff (-↑(r+ 1))) a‖ ⊔ ‖-(p_sequence_coeff (-↑(r+ 2))) a‖ <h :=by
    refine max_lt ?_ ?_
    · have:=se (r+1) (Nat.le_add_right_of_le sf)
      simp only [sub_zero] at this
      exact this
    · have:=se (r+2) (Nat.le_add_right_of_le sf)
      simp only [sub_zero] at this
      simp only [norm_neg]
      exact this

  exact lt_of_le_of_lt this m

noncomputable def FunctionTrans_2: (AdicCompletion (IsLocalRing.maximalIdeal ℤ_[p])
 (ℤ_[p]⸨X⸩)) →ₗ[ℤ_[p]]
 C₀(ℕ, ℤ_[p]) where
   toFun a :=⟨⟨(fun n:ℕ => p_sequence_coeff (-((n+1):ℕ ):ℤ ) a-p_sequence_coeff (-((n+2):ℕ ):ℤ ) a)
    ,continuous_of_discreteTopology⟩, cocompact_eq_atTop (α := ℕ) ▸ Tends_to_Zero a⟩
   map_add'  a b:=by
     ext n
     simp
     ring
   map_smul' a b:=by
     ext s
     simp
     ring
#check C₀(ℤ, ℤ_[p])

noncomputable def Adic_Complection_tofun : C_₀(ℤ,ℤ_[p]) →ₗ[ℤ_[p]]
 (AdicCompletion.AdicCauchySequence (IsLocalRing.maximalIdeal ℤ_[p])
 (ℤ_[p]⸨X⸩)) where
   toFun a:=sorry
   map_add' := sorry
   map_smul' := sorry
noncomputable def Adic_Complection_equiv_srmm: (AdicCompletion (IsLocalRing.maximalIdeal ℤ_[p])
 (ℤ_[p]⸨X⸩)) ≃ₗ[ℤ_[p]]
 C_₀(ℤ,ℤ_[p]) where
   toFun a:={
     toFun n:= p_sequence_coeff n a
     continuous_toFun := continuous_of_discreteTopology
     zero_atBot' := sorry
   }
   map_add' a b:=by
     ext s
     simp

   map_smul' a b:=by
     ext s
     simp

   invFun := sorry
   left_inv := sorry
   right_inv := sorry

lemma exact :Function.Exact (Amice_Trans_in_P (p:=p) ∘ₗ Amice_iso_2.toLinearMap)
  ( (mahlerEquiv (p:=p) ℤ_[p]).symm.toLinearMap ∘ₗ FunctionTrans_2 (p:=p) ) :=by
   refine  LinearMap.exact_iff.mpr ?_


   sorry
