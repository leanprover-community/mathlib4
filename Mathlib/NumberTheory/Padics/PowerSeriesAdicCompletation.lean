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

lemma powerseries_equiv_2(m:ℕ)(f g :ℤ_[p]⸨X⸩)
   (res :∀ s:ℤ ,((HahnSeries.coeff_map_0 s) f) -
   ((HahnSeries.coeff_map_0 s) g) ∈ Ideal.span {↑p} ^ m):
f ≡ g [SMOD  (IsLocalRing.maximalIdeal ℤ_[p] ^ m • ⊤ : Submodule ℤ_[p] ℤ_[p]⸨X⸩)]:=by
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
    have: BddBelow (Function.support (fun s => (ds1 s))) :=by
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
    use (HahnSeries.ofSuppBddBelow (fun s => (ds1 s)) this)
    constructor
    · simp
    · ext r
      simp only [HahnSeries.coeff_sub', Pi.sub_apply, HahnSeries.coeff_smul,
        HahnSeries.ofSuppBddBelow_coeff]
      exact ds2 r


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

lemma cauchy_sequence_coeff_tends_to_zero'
  (f:AdicCompletion.AdicCauchySequence (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]⸨X⸩ ):
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
   [SMOD ( IsLocalRing.maximalIdeal ℤ_[p] ^ m • ⊤ : Submodule ℤ_[p] ℤ_[p]⸨X⸩)]:=by
    rcases f with ⟨w1,w2⟩
    simp
    exact w2
  unfold cauchy_sequence_coeff Cauchy.seq_map
  simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
  refine CauchyL (p:=p) ((p:ℝ)^ (-m:ℤ)) (Cauchy_p_adic ((AdicCompletion.AdicCauchySequence.map
    (IsLocalRing.maximalIdeal ℤ_[p]) (HahnSeries.coeff_map_0 n)) f)) ?_
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

lemma esg (n:ℤ)(f:(AdicCompletion (IsLocalRing.maximalIdeal ℤ_[p]) (ℤ_[p]⸨X⸩)))
(r : AdicCompletion.AdicCauchySequence (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]⸨X⸩)
(rs : (AdicCompletion.mk (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]⸨X⸩) r = f):
 p_sequence_coeff n f=cauchy_sequence_coeff (p:=p) n r
:=by
  have:(p_sequence_coeff_0 n f)=
       (LinearMap.ker (AdicCompletion.mk
        (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p])).mkQ
         ((AdicCompletion.AdicCauchySequence.map  (IsLocalRing.maximalIdeal ℤ_[p])
           (HahnSeries.coeff_map_0 (p:=p) n)) r ):=by
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
lemma Tends_to_Zero'(f:(AdicCompletion (IsLocalRing.maximalIdeal ℤ_[p]) (ℤ_[p]⸨X⸩)))
:Tendsto (fun n ↦ (p_sequence_coeff n) f) atBot (𝓝 0):=by
  have:=by
   exact AdicCompletion.mk_surjective (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]⸨X⸩
  unfold Function.Surjective at this
  rcases (this f) with ⟨r,rs⟩
  have :(fun n ↦  p_sequence_coeff n f)=
    (fun n  ↦  cauchy_sequence_coeff (p:=p) n r) :=by
      ext n
      rw[esg n f r rs]

  rw[this]
  exact cauchy_sequence_coeff_tends_to_zero' r

lemma Tends_to_Zero_0(f:(AdicCompletion (IsLocalRing.maximalIdeal ℤ_[p]) (ℤ_[p]⸨X⸩)))
:Filter.Tendsto (fun n:ℕ => p_sequence_coeff (-n:ℤ ) f) Filter.atTop
(nhds 0):=by
 have:=Tends_to_Zero' f
 rw[NormedAddCommGroup.tendsto_atBot] at this
 refine NormedAddCommGroup.tendsto_atTop.mpr ?_
 intro s rs
 choose m sm using (this s rs)
 use (-m).natAbs
 intro e de
 have: m ≥  (-↑e):=by
   simp
   have:-(e:ℤ) ≤ -↑(-m).natAbs :=by
     simp only [ neg_le_neg_iff, sup_le_iff, Nat.cast_nonneg, and_true]
     exact Int.ofNat_le.mpr de
   have: -↑(-m).natAbs ≤ m :=by
     simp
     exact neg_abs_le m
   (expose_names; exact Int.le_trans this_2 this)
 exact (sm (-(e:ℤ)) this)
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

noncomputable def asd (a:C_₀(ℤ,ℤ_[p]))(t:ℕ): BddBelow (Function.support
 (fun (n : ℤ) => if ‖a n‖≤(p:ℝ)^(-t:ℤ) then 0 else (a n))) :=by

  have e:= zero_atBot a
  rw[NormedAddCommGroup.tendsto_atBot] at e
  have:(p:ℝ )^(-t:ℤ) >0 :=by
    simp
    refine pow_pos ?_ t
    simp
    exact Nat.pos_of_neZero p
  have:=e ((p:ℝ )^(-t:ℤ)) this
  choose m fs using this
  refine HahnSeries.forallLTEqZero_supp_BddBelow _  m ?_
  intro s js
  have:‖a s‖≤(p:ℝ)^(-t:ℤ) :=by
    refine le_of_lt ?_
    have:=fs s (Int.le_of_lt js)
    simp only [sub_zero] at this
    exact this
  exact if_pos this



noncomputable def Adic_Complection_tofun : C_₀(ℤ,ℤ_[p]) →
 (AdicCompletion.AdicCauchySequence (IsLocalRing.maximalIdeal ℤ_[p])
 (ℤ_[p]⸨X⸩)) :=fun
   | a => {
     val t :=HahnSeries.ofSuppBddBelow (fun (n : ℤ) => if ‖a n‖≤(p:ℝ)^(-t:ℤ) then 0 else (a n))
       (asd a t)
     property :=by
       intro m n  sn
       simp only
       refine powerseries_equiv_2 m _ _ ?_
       intro s
       unfold HahnSeries.coeff_map_0
       simp only [LinearMap.coe_mk, AddHom.coe_mk,
         HahnSeries.ofSuppBddBelow_coeff]
       rcases Decidable.em (‖a s‖ ≤ (p:ℝ)^(-m:ℤ)) with r1|r2
       · rcases Decidable.em (‖a s‖ ≤ (p:ℝ)^(-n:ℤ)) with r3|r4
         · simp only [r1, r3]
           simp
         · simp only[r1 ,r4]
           simp only [↓reduceIte, zero_sub, neg_mem_iff,
           Ideal.span_singleton_pow]
           rw[norm_le_pow_iff_mem_span_pow] at r1
           exact r1
       · rcases Decidable.em (‖a s‖ ≤ (p:ℝ)^(-n:ℤ)) with r3|r4
         · simp only[r2,r3]
           simp
           rw[norm_le_pow_iff_mem_span_pow,← Ideal.span_singleton_pow] at r3
           exact (Ideal.pow_le_pow_right sn) r3
         · simp only[r2,r4]
           simp





   }

lemma help1 (r:
 AdicCompletion.AdicCauchySequence (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]⸨X⸩)(s:ℤ):
 IsCauSeq norm ( fun n ↦ (r n).coeff s ) :=by
    have: ( fun n ↦ (r n).coeff s ) =
     Cauchy_p_adic ((AdicCompletion.AdicCauchySequence.map (IsLocalRing.maximalIdeal ℤ_[p])
   (HahnSeries.coeff_map_0 (p:=p) s)) r ):=by
      unfold  HahnSeries.coeff_map_0 Cauchy_p_adic
      ext n
      simp
    rw[this]
    rcases (Cauchy_p_adic ((AdicCompletion.AdicCauchySequence.map (IsLocalRing.maximalIdeal ℤ_[p])
   (HahnSeries.coeff_map_0 (p:=p) s)) r )) with ⟨l1,l2⟩
    simp
    exact l2


lemma help2 (r:
 AdicCompletion.AdicCauchySequence (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]⸨X⸩):
∀ ε >0 , ∃ N ,∀ n≥ N ,∀  (s:ℤ),‖(r n).coeff s-
 CauSeq.lim ⟨fun n ↦ (r n).coeff s, help1 r s⟩‖ <  ε  :=by
  intro ε hε
  obtain ⟨m, hm⟩ := exists_pow_neg_lt p hε
  use m
  intro s hs s_1
  have: (r s).coeff s_1-
   CauSeq.lim ⟨fun n ↦ (r n).coeff s_1, help1 r s_1⟩=
   CauSeq.lim (const norm ((r s).coeff s_1)-⟨ fun n ↦ (r n).coeff s_1, help1 r s_1⟩) :=by
     nth_rw  2 [← Mathlib.Tactic.RingNF.add_neg]
     rw[← lim_add,lim_neg,lim_const ]
     ring
  rw[this]
  refine  lt_of_le_of_lt ?_ hm
  refine CauchyL _ _ ?_
  use m
  intro g3 sr3
  simp only [sub_apply, const_apply]
  have:=powerseries_equiv (p:=p)  m s_1
  unfold HahnSeries.coeff_map_0 at this
  simp at this
  rw[norm_le_pow_iff_mem_span_pow,←Ideal.span_singleton_pow]
  refine this (r s) (r g3) ?_
  rcases r with ⟨l1,l2⟩
  simp
  unfold AdicCompletion.IsAdicCauchy at l2
  exact SModEq.trans (id (SModEq.symm (l2 hs))) (l2 sr3)



theorem zpow_adds ( x : ℝ)(hx : ¬ x=0)(y z:ℤ)  : x ^ (y + z) = x ^ y * x ^ z := by
  have:∃ r:ℝˣ, x= r :=by
    refine Units.exists_iff_ne_zero.mpr ?_
    use x
  choose r hr using this
  rw[hr]
  have(m:ℤ ): (r:ℝ)^m =Units.val (r^m) :=by
    simp
  rw[this]
  rw[zpow_add r y z]
  simp
#check zpow_add
  lemma sselw (a b c :ℝ)(hc:c >0 ) (hb :a≤ b) :a*c≤  b*c :=by
    exact (mul_le_mul_iff_of_pos_right hc).mpr hb
lemma ds3(a:AdicCompletion (IsLocalRing.maximalIdeal ℤ_[p])
 (ℤ_[p]⸨X⸩)) :AdicCompletion.mk (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]⸨X⸩
    (Adic_Complection_tofun ⟨⟨(fun n => (p_sequence_coeff n a)),
     continuous_of_discreteTopology⟩,Tends_to_Zero' a⟩) = a :=by
  have:=by
   exact AdicCompletion.mk_surjective (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]⸨X⸩
  unfold Function.Surjective at this
  rcases (this a) with ⟨r,rs⟩
  rw[← sub_eq_zero,← rs,← LinearMap.map_sub]
  refine AdicCompletion.mk_zero_of (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]⸨X⸩ _ ?_
  rw[rs]
  simp only [
    AdicCompletion.AdicCauchySequence.sub_apply,← SModEq.sub_mem]
  use 0
  intro g sefg
  have: (p:ℝ)^(-g:ℤ)>0 :=by
     simp
     refine pow_pos ?_ g
     simp
     exact Nat.pos_of_neZero p


  choose seg theg  using (help2 r ((p:ℝ)^(-g:ℤ)) this)
  use (max g seg)
  constructor
  · exact Nat.le_max_left g seg
  · use g
    constructor
    · exact Nat.le_refl g
    · refine powerseries_equiv_2 g  _ _ ?_
      intro s
      unfold HahnSeries.coeff_map_0 Adic_Complection_tofun
      simp only [
        ZeroAtBotContinuousMap.coe_mk,  LinearMap.coe_mk, AddHom.coe_mk,
        HahnSeries.ofSuppBddBelow_coeff]
      have:=esg s a r rs
      rcases Decidable.em (‖(p_sequence_coeff s) a‖≤ (p:ℝ)^(-(max g seg):ℤ)) with r3|r4
      · simp only [r3]
        simp only [↓reduceIte, zero_sub, neg_mem_iff]
        rw[this] at r3
        unfold cauchy_sequence_coeff Cauchy.seq_map Cauchy_p_adic HahnSeries.coeff_map_0
         AdicCompletion.AdicCauchySequence.map at r3
        simp only[Ideal.span_singleton_pow, ← norm_le_pow_iff_mem_span_pow,
        LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, Function.comp_apply] at r3
        simp only[Ideal.span_singleton_pow, ← norm_le_pow_iff_mem_span_pow]
        have ln:=theg (max g seg) (Nat.le_max_right g seg) s
        have :=norm_add_le  ((r (g ⊔ seg)).coeff s -
         CauSeq.lim ⟨fun n ↦ (r n).coeff s,  help1 r s⟩)
          (CauSeq.lim ⟨fun n ↦ (r n).coeff s,  help1 r s⟩)
        rw[sub_add_cancel] at this
        have ln2:=add_lt_add_of_lt_of_le ln r3
        have:=lt_of_le_of_lt this ln2
        have gf:(p:ℝ) ^ (-g:ℤ) + (p:ℝ)^ (-(g ⊔ seg):ℤ) ≤ (p:ℝ) ^ (-(g:ℤ)+ 1) :=by
          have: (p:ℝ)^ (-(g ⊔ seg):ℤ) ≤ (p:ℝ)^ (-g:ℤ) :=by
             refine (zpow_le_zpow_iff_right₀ ?_).mpr ?_
             simp
             refine Nat.Prime.one_lt (hp.1)
             simp
          have:=add_le_add (Preorder.le_refl ((p:ℝ)^ (-g:ℤ))) this
          refine le_trans this ?_
          rw[← (two_mul)]
          have:(p:ℝ) ^ (-(g:ℤ)+ 1)=p *(p:ℝ)^ (-g:ℤ) :=by
                have:¬ (p:ℝ)=0 :=by
                    simp
                    exact NeZero.ne p
                rw[(zpow_adds (p:ℝ) this (-(g:ℤ))  1 )]
                simp
                ring
          rw[this]
          refine (mul_le_mul_iff_of_pos_right ?_).mpr ?_
          simp
          refine pow_pos ?_ g
          simp
          exact Nat.pos_of_neZero p
          simp
          exact Nat.Prime.two_le hp.1
        exact (norm_le_pow_iff_norm_lt_pow_add_one ((r (g ⊔ seg)).coeff s) (-g:ℤ)).mpr
          (gt_of_ge_of_gt gf this)
      · simp only [r4,↓reduceIte]
        rw[esg s a r rs]
        unfold cauchy_sequence_coeff Cauchy.seq_map Cauchy_p_adic HahnSeries.coeff_map_0
         AdicCompletion.AdicCauchySequence.map
        simp only[Ideal.span_singleton_pow, ← norm_le_pow_iff_mem_span_pow,
        LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, Function.comp_apply]
        have ln:=theg (max g seg) (Nat.le_max_right g seg) s
        rw[← (neg_sub),norm_neg] at ln
        exact le_of_lt ln
lemma helper3 (a:CauSeq ℤ_[p] norm)(b:ℤ_[p])(hs :CauSeq.LimZero (a-const norm b)):
 a.lim =b:=by
  rw[← lim_eq_zero_iff ,← Mathlib.Tactic.RingNF.add_neg,← lim_add,lim_neg,lim_const ] at hs
  calc
  _=(a.lim+ (-b))+b :=by ring
  _=_:=by
    rw[hs]
    simp

lemma ds4(a:C_₀(ℤ,ℤ_[p]))(r:ℤ) :p_sequence_coeff r
 (AdicCompletion.mk (IsLocalRing.maximalIdeal ℤ_[p])
 ℤ_[p]⸨X⸩ (Adic_Complection_tofun a))= a r:=by
  have:=esg r (AdicCompletion.mk (IsLocalRing.maximalIdeal ℤ_[p])
 ℤ_[p]⸨X⸩ (Adic_Complection_tofun a)) (Adic_Complection_tofun a) rfl
  rw[this]
  unfold cauchy_sequence_coeff AdicCompletion.AdicCauchySequence.map
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


noncomputable def Adic_Complection_equiv_srmm: (AdicCompletion (IsLocalRing.maximalIdeal ℤ_[p])
 (ℤ_[p]⸨X⸩)) ≃ₗ[ℤ_[p]]
 C_₀(ℤ,ℤ_[p]) where
   toFun a:={
     toFun n:= p_sequence_coeff n a
     continuous_toFun := continuous_of_discreteTopology
     zero_atBot' :=Tends_to_Zero' a
   }
   map_add' a b:=by
     ext s
     simp
   map_smul' a b:=by
     ext s
     simp
   invFun a :=AdicCompletion.mk (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]⸨X⸩
    (Adic_Complection_tofun a)
   left_inv r:=by exact ds3 r
   right_inv m:= by
    ext n
    exact ds4  m n

end PadicInt
