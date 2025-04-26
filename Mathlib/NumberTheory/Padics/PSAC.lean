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
import Mathlib.Analysis.Normed.Ring.Lemmas2
import Mathlib.RingTheory.AdicCompletion.Lemma
import Mathlib.RingTheory.AdicCompletion.Algebra

set_option maxHeartbeats 10000000000000
set_option synthInstance.maxHeartbeats 10000000000000

open Finset IsUltrametricDist NNReal Filter  CauSeq  zero_atBot


open scoped fwdDiff ZeroAtInfty Topology
open scoped fwdDiff ZeroAtInfty Topology  LaurentSeries PowerSeries

variable {p : ℕ} [hp : Fact p.Prime]

namespace PadicInt


noncomputable def Amice_Trans_PowerSeries:ℤ_[p]⟦X⟧ →ₐ[ℤ_[p]]
AdicCompletion (Ideal.span {(p:ℤ_[p]⸨X⸩)}) ℤ_[p]⸨X⸩  where
    toFun r := ⟨algebraMap _ (∀ _, _) r, fun _ ↦ rfl⟩
    map_one' := Subtype.ext <| map_one _
    map_mul' x y := Subtype.ext <| map_mul _ x y
    map_zero' := Subtype.ext <| map_zero _
    map_add' x y := Subtype.ext <| map_add _ x y
    commutes' r :=by
      ext n
      simp

      rfl
noncomputable instance : Algebra ℤ_[p] ℤ_[p]⸨X⸩ :=by exact HahnSeries.instAlgebra
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
lemma CauchyHanser (a:ℤ): ∀ n,
((Ideal.span {(p:ℤ_[p]⸨X⸩)})^n • ⊤ : Submodule ℤ_[p]⸨X⸩ ℤ_[p]⸨X⸩).1 ≤
 (Submodule.comap (HahnSeries.coeff_map_0 a)
 ((IsLocalRing.maximalIdeal ℤ_[p])^n • ⊤ : Submodule ℤ_[p] ℤ_[p])).1:=by
  intro c  b hb
  simp only [Submodule.mem_toAddSubmonoid,
   Ideal.span_singleton_pow,Submodule.ideal_span_singleton_smul,← Submodule.singleton_set_smul,
    Submodule.mem_singleton_set_smul] at hb
  choose m hm hse using hb
  simp
  rw[hse]
  have:(p^ c:ℤ_[p]⸨X⸩)  • m =
   (p)^c•  (m):=by
     simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_pow]
  rw[this]
  rw[LinearMap.CompatibleSMul.map_smul (HahnSeries.coeff_map_0 a) (p ^ c) m]
  simp only [nsmul_eq_mul, Nat.cast_pow]
  rw[maximalIdeal_eq_span_p,Ideal.span_singleton_pow,Ideal.mem_span_singleton']
  use (HahnSeries.coeff_map_0 a) m
  ring



#check
(Cauchy.seq_map (p:=p))∘ₗ(AdicCompletion.AdicCauchySequence.map  (IsLocalRing.maximalIdeal ℤ_[p])
 (HahnSeries.coeff_map_0 (p:=p) 1))
noncomputable abbrev cauchy_sequence_coeff (a:ℤ ) :=
 (Cauchy.seq_map (p:=p))∘ₗ (AdicCompletion.mapAlg (IsLocalRing.maximalIdeal ℤ_[p])
    (Ideal.span {(p:ℤ_[p]⸨X⸩)}) (HahnSeries.coeff_map_0 (p:=p) a) (CauchyHanser a))
lemma powerseries_equiv(m:ℕ)(s :ℤ)(f g :ℤ_[p]⸨X⸩)
   (hs:f ≡ g [SMOD  ((Ideal.span {(p:ℤ_[p]⸨X⸩)}) ^ m • ⊤ : Submodule ℤ_[p]⸨X⸩ ℤ_[p]⸨X⸩)]):
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
    have:(p^ m:ℤ_[p]⸨X⸩)  • u =
      (p)^m•  u:=by
       simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_pow]
    rw[this]
    rw[LinearMap.CompatibleSMul.map_smul]
    simp
    use (HahnSeries.coeff_map_0 s) u
    ring

lemma powerseries_equiv_2(m:ℕ)(f g :ℤ_[p]⸨X⸩)
   (res :∀ s:ℤ ,((HahnSeries.coeff_map_0 s) f) -
   ((HahnSeries.coeff_map_0 s) g) ∈ Ideal.span {↑p} ^ m):
f ≡ g [SMOD  ((Ideal.span {(p:ℤ_[p]⸨X⸩)}) ^ m • ⊤ : Submodule ℤ_[p]⸨X⸩ ℤ_[p]⸨X⸩)]:=by
    simp only [SModEq.sub_mem,zero_sub, neg_mem_iff,
     maximalIdeal_eq_span_p,Ideal.span_singleton_pow]
    simp only [SModEq.sub_mem,zero_sub, neg_mem_iff ,
     maximalIdeal_eq_span_p,Ideal.span_singleton_pow,Submodule.ideal_span_singleton_smul]
      at res
    have(s:ℤ):∃ r , (HahnSeries.coeff_map_0 s) f -
     (HahnSeries.coeff_map_0 s) g = (p:ℤ_[p])^m • r :=by
       have:=res s
       rw[←Ideal.mul_top  (Ideal.span {(p:ℤ_[p]) ^ m}),← smul_eq_mul ,
       Submodule.ideal_span_singleton_smul,← Submodule.singleton_set_smul,
       Submodule.mem_singleton_set_smul ] at this
       choose r er1 er2 using this
       use r
    choose ds1 ds2 using this
    have hel: BddBelow (Function.support (fun s => (ds1 s))) :=by
      refine HahnSeries.forallLTEqZero_supp_BddBelow _  (min f.order  g.order) ?_
      intro q1 sm
      have:=ds2 q1
      have e1:(HahnSeries.coeff_map_0 q1) f =0 :=by
        unfold HahnSeries.coeff_map_0
        simp
        refine HahnSeries.coeff_eq_zero_of_lt_order (Int.lt_of_lt_of_le sm
         (Int.min_le_left (HahnSeries.order f) (HahnSeries.order g)))
      have e2:(HahnSeries.coeff_map_0 q1) g =0 :=by
        unfold HahnSeries.coeff_map_0
        simp
        refine HahnSeries.coeff_eq_zero_of_lt_order (Int.lt_of_lt_of_le sm
         (Int.min_le_right (HahnSeries.order f) (HahnSeries.order g)))
      rw[e1,e2] at this
      simp only [sub_self, smul_eq_mul, zero_eq_mul] at this
      rcases this with d1|d2
      · exact False.elim ((NeZero.ne ((p:ℤ_[p])^m)) (d1))
      · exact d2
    rw[Submodule.ideal_span_singleton_smul,← Submodule.singleton_set_smul,
       Submodule.mem_singleton_set_smul ]

    use (HahnSeries.ofSuppBddBelow (fun s => (ds1 s)) hel)
    constructor
    · simp
    · ext r
      have:(p^ m:ℤ_[p]⸨X⸩)  • (HahnSeries.ofSuppBddBelow (fun s => (ds1 s)) hel) =
         (p)^m•  (HahnSeries.ofSuppBddBelow (fun s => (ds1 s)) hel):=by
         simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_pow]
      rw[this]
      have(a:ℤ_[p]⸨X⸩)(s:ℤ): a.coeff s= (HahnSeries.coeff_map_0 s) a :=by rfl
      rw[this,this,LinearMap.CompatibleSMul.map_smul,← this,← this,this]
      simp only [HahnSeries.coeff_sub', Pi.sub_apply, HahnSeries.ofSuppBddBelow_coeff,
      LinearMap.map_sub ]
      rw [nsmul_eq_mul, Nat.cast_pow,ds2 r,smul_eq_mul]






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
  ∘ₗ  (AdicCompletion.adicCompletionAux (IsLocalRing.maximalIdeal ℤ_[p])
  (Ideal.span {(p:ℤ_[p]⸨X⸩)})
   (HahnSeries.coeff_map_0 (p:=p) a) (CauchyHanser a) )
noncomputable abbrev p_sequence_coeff (a:ℤ ):=
    Submodule.liftQ (LinearMap.ker ((AdicCompletion.mk (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p])))
 (Cauchy.seq_map (p:=p)) (ss (p:=p))∘ₗ (p_sequence_coeff_0 a)

lemma cauchy_sequence_coeff_tends_to_zero'
  (f:AdicCompletion.AdicCauchySequence (Ideal.span {(p:ℤ_[p]⸨X⸩)}) ℤ_[p]⸨X⸩ ):
  Filter.Tendsto (fun n => cauchy_sequence_coeff (p:=p) n f) Filter.atBot
(nhds 0):=by
  refine NormedAddCommGroup.tendsto_atBot.mpr ?_
  intro h sh
  simp only [sub_zero]
  obtain ⟨m, hm⟩ := exists_pow_neg_lt p sh
  use ((f.1 m).order-1)
  intro n sn
  refine lt_of_le_of_lt ?_ hm
  have:∀ {m n : ℕ}, m ≤ n → f.1 m ≡ f.1 n
   [SMOD ( (Ideal.span {(p:ℤ_[p]⸨X⸩)}) ^ m • ⊤ : Submodule ℤ_[p]⸨X⸩ ℤ_[p]⸨X⸩)]:=by
    rcases f with ⟨w1,w2⟩
    exact w2
  unfold cauchy_sequence_coeff Cauchy.seq_map
  simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
  refine CauchyL (p:=p) ((p:ℝ)^ (-m:ℤ)) (Cauchy_p_adic (((AdicCompletion.mapAlg
   (IsLocalRing.maximalIdeal ℤ_[p])
    (Ideal.span {(p:ℤ_[p]⸨X⸩)}) (HahnSeries.coeff_map_0 (p:=p) n) (CauchyHanser n))) f)) ?_
  use m
  intro l sl
  unfold Cauchy_p_adic
  simp only [AdicCompletion.AdicCauchySequence.map_apply_coe]

  have s1:=by
      exact powerseries_equiv m n (f.1 m) (f.1 l) (this sl)

  have s2 :((HahnSeries.coeff_map_0 n) (f.1 m))=0 :=by
     refine HahnSeries.coeff_eq_zero_of_lt_order (Int.lt_of_le_sub_one sn
)

  rw[s2] at s1
  simp only [maximalIdeal_eq_span_p,SModEq.sub_mem,zero_sub, neg_mem_iff] at s1
  rw[norm_le_pow_iff_mem_span_pow,←Ideal.span_singleton_pow]
  exact s1








#check         (LinearMap.ker (AdicCompletion.mk
        (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p])).mkQ ∘ₗ
         ((AdicCompletion.mapAlg (IsLocalRing.maximalIdeal ℤ_[p])
    (Ideal.span {(p:ℤ_[p]⸨X⸩)}) (HahnSeries.coeff_map_0 (p:=p) 1) (CauchyHanser 1)))

lemma esg (n:ℤ)(f:(AdicCompletion (Ideal.span {(p:ℤ_[p]⸨X⸩)}) (ℤ_[p]⸨X⸩)))
(r : AdicCompletion.AdicCauchySequence (Ideal.span {(p:ℤ_[p]⸨X⸩)}) ℤ_[p]⸨X⸩)
(rs : (AdicCompletion.mk (Ideal.span {(p:ℤ_[p]⸨X⸩)}) ℤ_[p]⸨X⸩) r = f):
p_sequence_coeff (p:=p) n f=cauchy_sequence_coeff (p:=p) n r :=by
  have:(p_sequence_coeff_0 (p:=p) n f)= (LinearMap.ker (AdicCompletion.mk
        (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p])).mkQ (
         ((AdicCompletion.mapAlg (IsLocalRing.maximalIdeal ℤ_[p])
    (Ideal.span {(p:ℤ_[p]⸨X⸩)}) (HahnSeries.coeff_map_0 (p:=p) n) (CauchyHanser n))) r) :=by
           rw[← rs]
           simp
           unfold FunctionTrans_1
           exact
             (LinearEquiv.symm_apply_eq
                   ((AdicCompletion.mk (IsLocalRing.maximalIdeal ℤ_[p])
                         ℤ_[p]).quotKerEquivOfSurjective
                     FunctionTrans_1._proof_28)).mpr
               rfl
  simp
  simp at this
  rw[this]
  simp


end PadicInt
