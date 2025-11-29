import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.RingTheory.Binomial
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.MetricSpace.Ultra.ContinuousMaps
import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.Topology.Algebra.Module.LinearMap
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
open Finset IsUltrametricDist NNReal Filter

open scoped fwdDiff ZeroAtInfty Topology
set_option maxHeartbeats 200000000000000000
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

namespace PadicInt



lemma Bound_has_Sum (b: (BoundedContinuousFunction ℕ ℤ_[p]))(f:C(ℤ_[p], ℤ_[p])):HasSum
  (fun n=> (b n)*( Δ_[1] ^[n] (⇑f) 0))
   (∑'(n:ℕ ),(b n)*( Δ_[1] ^[n] (⇑f) 0)):=by
  refine (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_).hasSum
  rw [Nat.cofinite_eq_atTop,Metric.tendsto_atTop]
  have m:=fwdDiff_tendsto_zero f
  rw [Metric.tendsto_atTop] at m
  simp at m
  intro q qe
  rcases (LE.le.gt_or_eq (norm_nonneg b)) with j1|j2
  · have:=_root_.div_pos qe j1
    choose M HN using (m (q / ‖b‖) (_root_.div_pos qe j1))
    use M
    intro o hs
    simp only [_root_.dist_zero_right, padicNormE.mul,norm_mul, gt_iff_lt]
    have:=mul_lt_mul_of_nonneg_of_pos' (BoundedContinuousFunction.norm_coe_le_norm b o) (HN o hs)
      (norm_nonneg (Δ_[1] ^[o] (⇑f) 0)) j1
    rw[mul_div_cancel₀ q (Ne.symm (_root_.ne_of_lt j1))] at this
    exact this
  use 0
  simp
  intro n
  have:‖b n‖= 0 :=by
    apply le_antisymm
    rw[← j2]
    exact (BoundedContinuousFunction.norm_coe_le_norm b n)
    exact norm_nonneg (b n)
  rw[this]
  simp
  exact qe

noncomputable def Amice_iso_1 (b: (BoundedContinuousFunction ℕ ℤ_[p]))
:(ContinuousLinearMap (RingHom.id ℤ_[p]) C(ℤ_[p],ℤ_[p])  ℤ_[p]) where
  toFun f:=∑'(n:ℕ ),(b n)*( Δ_[1] ^[n] (⇑f) 0)
  map_add' x y:= by
        simp
        ring_nf
        refine tsum_add (HasSum.summable (Bound_has_Sum b x)) (HasSum.summable (Bound_has_Sum  b y))
  map_smul' x u:= by
    simp_all
    ring_nf
    refine HasSum.tsum_eq ?_
    have:(fun n => b n * x * Δ_[1] ^[n] (⇑u) 0) =(fun n =>  x*(b n  * Δ_[1] ^[n] (⇑u) 0)):=by
      ext n
      ring
    rw[this]
    exact HasSum.mul_left x (Bound_has_Sum  b u)
  cont :=by
      rw[continuous_iff_continuousAt]
      intro g
      unfold ContinuousAt
      simp
      rw[NormedAddCommGroup.tendsto_nhds_nhds]
      intro s es
      rcases (LE.le.gt_or_eq (norm_nonneg b)) with j1|j2
      · use s/(2*‖b‖)
        constructor
        · exact _root_.div_pos es (mul_pos (zero_lt_two) j1)

        · intro x' sx'
          rw[Eq.symm (tsum_sub (HasSum.summable
            (Bound_has_Sum  b x')) (HasSum.summable (Bound_has_Sum b g)))]
          have fi (n:ℕ ):‖(b n * Δ_[1] ^[n] (⇑x') 0 - b n * Δ_[1] ^[n] (⇑g) 0)‖≤ s/2 :=by
            have:(b n * Δ_[1] ^[n] (⇑x') 0 - b n * Δ_[1] ^[n] (⇑g) 0)=
            b n*(Δ_[1] ^[n] (x'- g) 0) :=by
              simp
              have(x:ℤ_[p]): ∀ a b:ℤ_[p]→ ℤ_[p],Δ_[1] ^[n] (a - b) x=
              Δ_[1] ^[n] (a ) x- Δ_[1] ^[n] ( b) x:=by

                 induction' n with i si
                 simp
                 simp_all
                 intro a b
                 rw[← si ]
                 have:Δ_[1] (a - b)=Δ_[1] a - Δ_[1] b :=by
                   unfold fwdDiff
                   ext n
                   simp
                   ring
                 rw[this]
              rw[(this 0)]
              ring
            rw[this]
            simp
            have l2:=lt_of_le_of_lt (IsUltrametricDist.norm_fwdDiff_iter_apply_le (1:ℤ_[p])
               (x' - g) 0 n) sx'
            simp at this
            have:‖b‖*(s/(2*‖b‖))=s/2 :=by
             ring_nf
             rw[mul_comm ‖b‖ s ,mul_assoc s ‖b‖ ‖b‖⁻¹,
              CommGroupWithZero.mul_inv_cancel ‖b‖ (Ne.symm (_root_.ne_of_lt j1))]
             simp
            rw[← this]
            refine mul_le_mul_of_nonneg  (BoundedContinuousFunction.norm_coe_le_norm b n)
               (le_of_lt l2) (norm_nonneg (b n))
               (le_of_lt ( _root_.div_pos es (mul_pos (zero_lt_two) j1)))

          ·   exact lt_of_le_of_lt (IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
                (le_of_lt  (_root_.div_pos es  (zero_lt_two))) fi) ( div_two_lt_of_pos es)
      · use 1
        constructor
        ·exact Real.zero_lt_one
        · intro r hs
          have: b=0 :=by
            sorry
          simp[this]
          exact es

--这个代码我不知道为什么会报错

lemma dts (s:C(ℤ_[p],ℤ_[p]))(f:(ContinuousLinearMap (RingHom.id ℤ_[p]) C(ℤ_[p],ℤ_[p])  ℤ_[p]))
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
lemma sss(x b:ℕ )(hx : x ∈ range b): ↑(Ring.choose  (x:ℤ_[p]) b)=0 :=by
  rw[Ring.choose_natCast x b]
  simp
  refine Nat.choose_eq_zero_iff.mpr (List.mem_range.mp hx)

lemma sse( b:ℕ ): ∑ x ∈ range b, (-(1)) ^ (b - x) *
((b.choose x):ℚ_[p]) * (Ring.choose (x:ℤ_[p]) b)=0:=by
  have: ∀ x ∈ range b,(-(1)) ^ (b - x) * ((b.choose x):ℚ_[p]) * (Ring.choose (x:ℤ_[p]) b)=0:=by
     intro x hx
     rw[Ring.choose_natCast x b]
     rw[Nat.choose_eq_zero_iff.mpr (List.mem_range.mp hx)]
     simp
  exact sum_eq_zero this
lemma sh (n_1 b:ℕ ): ((mahlerEquiv ℤ_[p]) (mahler b)) n_1 = if n_1 = b then 1 else 0 :=by
 have:Tendsto (fun n_1=>if n_1 = b then (1 : ℤ_[p]) else 0) (cocompact ℕ) (𝓝 0) :=by
   rw[cocompact_eq_atTop,Metric.tendsto_atTop]
   intro s hs
   use b+1
   intro n sd
   simp[Nat.ne_of_lt' sd]
   exact hs
 let qo:C₀(ℕ, ℤ_[p]):=⟨⟨(fun n_1=>if n_1 = b then (1 : ℤ_[p]) else 0),
 continuous_of_discreteTopology⟩,this⟩
 have:(mahlerEquiv  (p:=p) ℤ_[p]).symm qo
    =(mahler b) :=by
       unfold mahlerEquiv mahlerSeries mahlerTerm
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


noncomputable def Amice_iso_2 (a: (C(ℤ_[p],ℤ_[p]) →L[ℤ_[p]] ℤ_[p])) :
 (BoundedContinuousFunction ℕ ℤ_[p])where
  toFun := fun n=> a  (mahler (p:=p) n)
  map_bounded' := by

         use 1
         intro x y
         have s (n:ℕ ):‖a (mahler (p:=p) n)‖ ≤ 1 :=by
           exact norm_le_one (a (mahler n))
         have:Dist.dist (a (mahler x)) (a (mahler y))=‖a (mahler x) + -a (mahler y)‖ :=by
            ring_nf
            rfl
         rw[this]
         have:=padicNormE.nonarchimedean (p:=p) (a (mahler x)) (-a (mahler y))
         simp at this
         rcases this with l1|l2
         · exact Preorder.le_trans ‖a (mahler x) + -a (mahler y)‖ ‖a (mahler x)‖ 1 l1 (s x)
         · exact Preorder.le_trans ‖a (mahler x) + -a (mahler y)‖ ‖a (mahler y)‖ 1 l2 (s y)

noncomputable def Amice_iso :
 (C(ℤ_[p],ℤ_[p]) →L[ℤ_[p]] ℤ_[p]) ≃ₗᵢ[ℤ_[p]]
   (BoundedContinuousFunction ℕ ℤ_[p]) where
     toFun a :=Amice_iso_2 a
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
        have:∑' (n_1 : ℕ), s n_1 * ((PadicInt.mahlerEquiv ℚ_[p]) (mahler b)) n_1 = s b :=by
          have (n_1 : ℕ):((PadicInt.mahlerEquiv ℚ_[p]) (mahler b)) n_1 =
          if ( n_1=b ) then (1: ℚ_[p] )else 0 :=by
           rcases (eq_or_ne n_1 b) with d1|d2
           rw[d1]
           simp
           unfold PadicInt.mahlerEquiv
           simp
           rw [fwdDiff_iter_eq_sum_shift]
           unfold mahler
           simp
           rw[Finset.sum_range_succ,sse]
           simp
           rw[Ring.choose_natCast b b]
           simp
           exact sh
          have sh1: ∀ n_1 ∉ (({b}:Finset ℕ )), s n_1 * ((PadicInt.mahlerEquiv ℚ_[p]) (mahler b)) n_1=0:=by
             intro n sb
             rw[this n]
             simp_all
          rw[tsum_eq_sum  sh1 ,sum_singleton,sh]
          simp
        exact this

--norm_nonneg ⟨⟨a (mahler n),
        --continuous_of_discreteTopology⟩,sBound a f⟩
     norm_map' a:=by
       simp only [LinearEquiv.coe_mk]
       apply le_antisymm
       have s (n:ℕ ):‖a (mahler (p:=p) n)‖ ≤ ‖a‖ :=by
           refine ContinuousLinearMap.unit_le_opNorm a (mahler n) ?_
           rw[norm_mahler_eq]
       exact BoundedContinuousFunction.norm_le_of_nonempty.mpr s
       refine ContinuousLinearMap.opNorm_le_bound a (norm_nonneg (Amice_iso_2 a)) ?_
       intro f
       nth_rw 1 [← (PadicInt.hasSum_mahler f).tsum_eq]
       unfold PadicInt.mahlerTerm
       rw[ContinuousLinearMap.map_tsum]
       refine norm_tsum_le_of_forall_le_of_nonneg (Left.mul_nonneg (norm_nonneg (Amice_iso_2 a) )
         (norm_nonneg f))  ?_
       intro i
       have:mahler (p:=p) i • ContinuousMap.const ℤ_[p] (Δ_[1] ^[i] (⇑f) 0)= (Δ_[1] ^[i] (⇑f) 0)•mahler (p:=p) i:=by
          ext s
          unfold ContinuousMap.const
          simp
          ring
       rw[this,ContinuousLinearMap.map_smul_of_tower]
       simp
       rw[mul_comm]
       refine mul_le_mul_of_nonneg  (BoundedContinuousFunction.norm_coe_le_norm (Amice_iso_2 a) i)
         (IsUltrametricDist.norm_fwdDiff_iter_apply_le 1 f 0 i) ((norm_nonneg (a (mahler i)))) ((norm_nonneg f))
       exact HasSum.summable ((PadicInt.hasSum_mahler f))
