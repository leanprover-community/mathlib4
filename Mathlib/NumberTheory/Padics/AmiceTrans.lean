/-
Copyright (c) 2025 Hanliu Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanwen Wang, Hanliu Jiang
-/
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.RingTheory.PowerSeries.Basic
/-!
# The Amice Transform of p-adic measure


## References

* [P. Colmez, *Fonctions d'une variable p-adique*][colmez2010]

## Tags

Bojanic
-/

open Finset IsUltrametricDist NNReal Filter PowerSeries

open scoped fwdDiff ZeroAtInfty Topology

variable {p : ℕ} [hp : Fact p.Prime]

namespace PadicInt


lemma dns (b: ℕ→ ℤ_[p])(f:C(ℤ_[p], ℤ_[p])):HasSum
  (fun n=> (b n)*( Δ_[1] ^[n] (⇑f) 0))
   (∑'(n:ℕ ),(b n)*( Δ_[1] ^[n] (⇑f) 0)):=by
  refine (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_).hasSum
  rw [Nat.cofinite_eq_atTop,Metric.tendsto_atTop]
  have m:=PadicInt.fwdDiff_tendsto_zero f
  rw [Metric.tendsto_atTop] at m
  simp at m
  intro q qe
  choose N sN using (m q qe)
  use N
  intro s Hs
  have:=sN s Hs
  simp only [dist_zero_right, norm_mul, gt_iff_lt]
  rw[←one_mul q]
  refine mul_lt_mul_of_nonneg_of_pos' (norm_le_one (b s)) (sN s Hs)
   (norm_nonneg (Δ_[1]^[s] (⇑f) 0)) ( Real.zero_lt_one)
lemma find(x:ℤ_[p])(n:ℕ):
 ∀ a b:ℤ_[p]→ ℤ_[p],Δ_[1] ^[n] (a - b) x= Δ_[1] ^[n] (a ) x- Δ_[1] ^[n] ( b) x:=by
            induction' n with i si
            ·  simp
            · simp_all
              intro a b
              rw[← si ]
              have:Δ_[1] (a - b)=Δ_[1] a - Δ_[1] b :=by
                unfold fwdDiff
                ext n
                simp
                ring
              rw[this]
noncomputable def Amice_iso_1 (b: ℕ→ ℤ_[p]):C(ℤ_[p],ℤ_[p]) →L[ℤ_[p]]  ℤ_[p] where
  toFun f:=∑'(n:ℕ ),(b n)*( Δ_[1] ^[n] (⇑f) 0)
  map_add' x y:= by
        simp
        ring_nf
        refine tsum_add (HasSum.summable (dns  b x)) (HasSum.summable (dns  b y))
  map_smul' x u:= by
    simp_all
    ring_nf
    refine HasSum.tsum_eq ?_
    have:(fun n => b n * x * Δ_[1] ^[n] (⇑u) 0) =(fun n =>  x*(b n  * Δ_[1] ^[n] (⇑u) 0)):=by
      ext n
      ring
    rw[this]
    exact HasSum.mul_left x (dns  b u)
  cont :=by
       rw[continuous_iff_continuousAt]
       intro g
       unfold ContinuousAt
       simp
       rw[NormedAddCommGroup.tendsto_nhds_nhds]
       intro s es
       use s/2
       constructor
       · exact _root_.div_pos es (zero_lt_two)
       · intro x' sx'
         rw[Eq.symm (tsum_sub (HasSum.summable (dns  b x')) (HasSum.summable (dns  b g)))]
         refine lt_of_le_of_lt (IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
          (le_of_lt  (_root_.div_pos es  (zero_lt_two))) ?_) ( div_two_lt_of_pos es)
         intro i
         rw[←(mul_sub_left_distrib ),norm_mul,←one_mul (s/2)]
         refine mul_le_mul_of_nonneg (norm_le_one (b i)) ?_ (norm_nonneg (b i))
          (le_of_lt ( _root_.div_pos es zero_lt_two))
         rw[←(find (p:=p) 0 i (⇑x') (⇑g)),←ContinuousMap.coe_sub]
         exact le_of_lt (lt_of_le_of_lt (IsUltrametricDist.norm_fwdDiff_iter_apply_le
          (1:ℤ_[p])  (x' - g) 0 i) sx')





--这个代码我不知道为什么会报错

lemma dts (s:C(ℤ_[p],ℤ_[p]))(f:C(ℤ_[p],ℤ_[p]) →L[ℤ_[p]]  ℤ_[p] )
 :∑' (n : ℕ), (f (mahler n))*( Δ_[1] ^[n] (⇑s) 0) = f s :=by
   have:=(PadicInt.hasSum_mahler s).tsum_eq
   rw[congrArg (⇑f) (id (Eq.symm this)),
      ContinuousLinearMap.map_tsum f (HasSum.summable (PadicInt.hasSum_mahler s))]
   refine tsum_congr ?_
   intro n
   have: PadicInt.mahlerTerm (Δ_[1] ^[n] (⇑s) 0) n= (Δ_[1] ^[n] (⇑s) 0) •mahler n :=by
       unfold PadicInt.mahlerTerm
       ext q
       simp
       ring
   rw[this,ContinuousLinearMap.map_smul_of_tower f (Δ_[1] ^[n] (⇑s) 0) (mahler n)]
   simp
   ring

variable(b n_1:ℕ)
lemma sss(x:ℕ )(hx : x ∈ range b): ↑(Ring.choose  (x:ℤ_[p]) b)=0 :=by
  rw[Ring.choose_natCast x b]
  simp
  refine Nat.choose_eq_zero_iff.mpr (List.mem_range.mp hx)

lemma sse: ∑ x ∈ range b, (-(1)) ^ (b - x) * ((b.choose x):ℤ_[p]) * (Ring.choose (x:ℤ_[p]) b)=0:=by
  have: ∀ x ∈ range b,(-(1)) ^ (b - x) * ((b.choose x):ℤ_[p]) * (Ring.choose (x:ℤ_[p]) b)=0:=by
     intro x hx
     rw[Ring.choose_natCast x b]
     rw[Nat.choose_eq_zero_iff.mpr (List.mem_range.mp hx)]
     simp
  exact sum_eq_zero this
lemma sh: ((mahlerEquiv ℤ_[p]) (mahler b)) n_1 = if n_1 = b then 1 else 0 :=by
 have:Tendsto (fun n_1=>if n_1 = b then (1 : ℤ_[p]) else 0) (cocompact ℕ) (𝓝 0) :=by
   rw[cocompact_eq_atTop,Metric.tendsto_atTop]
   intro s hs
   use b+1
   intro n sd
   simp[Nat.ne_of_lt' sd]
   exact hs
 let qo:C₀(ℕ, ℤ_[p]):=⟨⟨(fun n_1=>if n_1 = b then (1 : ℤ_[p]) else 0)
  ,continuous_of_discreteTopology⟩,this⟩
 have:((mahlerEquiv ℤ_[p])).symm qo
    =(mahler b) :=by
       unfold PadicInt.mahlerEquiv PadicInt.mahlerSeries PadicInt.mahlerTerm
       have:∑' (n : ℕ), mahler (p:=p) n • (ContinuousMap.const ℤ_[p] (qo n))=mahler b :=by
           have sh: ∀ n ∉ (({b}:Finset ℕ )), mahler (p:=p) n •
            (ContinuousMap.const ℤ_[p] (qo n))=0:=by
             intro n sb
             unfold qo ContinuousMap.const
             simp_all
             ext s
             simp
           rw[tsum_eq_sum  sh ]
           rw[sum_singleton]
           unfold qo ContinuousMap.const
           simp
           ext m
           simp

       exact this
 rw[← this]
 simp
 exact rfl


noncomputable def Amice_iso :(C(ℤ_[p],ℤ_[p]) →L[ℤ_[p]]  ℤ_[p] ) ≃ₗ[ℤ_[p]]
   (ℕ→ ℤ_[p])where
     toFun a :=fun n => a (mahler n)
     map_add' f g:=rfl
     map_smul' f g :=rfl
     invFun b:=Amice_iso_1 b
     left_inv f :=by
       ext s
       unfold Amice_iso_1
       simp_all
       exact dts s f

     right_inv s :=by
        ext b
        simp_all
        unfold Amice_iso_1
        simp
        have sh1: ∀ n_1 ∉ (({b}:Finset ℕ )), s n_1 *
          ((PadicInt.mahlerEquiv ℤ_[p]) (mahler b)) n_1=0:=by
             intro n sb
             rw[sh b n]
             simp_all
        unfold mahlerEquiv at sh1
        simp only [ LinearIsometryEquiv.coe_mk, LinearEquiv.coe_mk,
          ZeroAtInftyContinuousMap.coe_mk] at sh1
        rw[tsum_eq_sum (sh1 ),sum_singleton]
        have:Δ_[1]^[b] (⇑(mahler b)) 0=((mahlerEquiv ℤ_[p]) (mahler b)) b :=by
          exact rfl
        rw[this,sh b b]
        simp
end PadicInt
