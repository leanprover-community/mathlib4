import Mathlib.NumberTheory.Padics.PSAC3
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Group.Ultra


variable {p : ℕ} [hp : Fact p.Prime]

namespace PadicInt

noncomputable def Mul_of_a_measure :  C(ℤ_[p],ℤ_[p])→ (C(ℤ_[p],ℤ_[p]) →L[ℤ_[p]]  ℤ_[p] ) →
(C(ℤ_[p],ℤ_[p]) →L[ℤ_[p]]  ℤ_[p] )
  | a, f =>{
    toFun g:=f (g • a)
    map_add' x y:=by
     simp
     rw[RightDistribClass.right_distrib ]
     exact ContinuousLinearMap.map_add f (x*a  ) (y* a )
    map_smul' x y:=by
      simp

    cont :=by
     refine Continuous.comp'  f.2 (continuous_mul_right a)

  }
--(ContinuousMap.restrict s)
--TopologicalSpace.Opens α
#check LinearMap.id
--实际上是

noncomputable def continues_locally_char :TopologicalSpace.Clopens ℤ_[p]→ C(ℤ_[p], ℤ_[p])
  | U =>{toFun := Set.indicator U 1
         continuous_toFun :=IsClopen.continuous_indicator U.2 continuous_one}
noncomputable def restriction :TopologicalSpace.Clopens ℤ_[p] →
(C(ℤ_[p],ℤ_[p]) →L[ℤ_[p]]  ℤ_[p] )→
(C(ℤ_[p],ℤ_[p]) →L[ℤ_[p]]  ℤ_[p] )
 | U ,a=> Mul_of_a_measure (continues_locally_char U) a

#check ContinuousMap.const  ℤ_[p] 1
noncomputable def action (c:ℤ_[p]):(C(ℤ_[p],ℤ_[p]) →L[ℤ_[p]]  ℤ_[p] ) →ₗ[ℤ_[p]]
(C(ℤ_[p],ℤ_[p]) →L[ℤ_[p]]  ℤ_[p] ) where
  toFun a:= {
     toFun g :=  a (⟨g ∘ (c•ContinuousMap.id ℤ_[p]),
      Continuous.comp g.2 (ContinuousMap.continuous (c•ContinuousMap.id ℤ_[p]))⟩)
     map_add' x y :=by
      rw[(ContinuousLinearMap.map_add a
       ⟨x ∘ (c•ContinuousMap.id ℤ_[p]),_⟩
      ⟨y ∘ (c•ContinuousMap.id ℤ_[p]),_⟩).symm]
      exact rfl
     map_smul' u y:=by
      simp
      exact id (Eq.symm
      ((ContinuousLinearMap.map_smul_of_tower a u
       ⟨y ∘ (c•ContinuousMap.id ℤ_[p]),_⟩).symm))

     cont :=by
      simp
      refine Continuous.comp a.2 ?_
      rw[continuous_iff_continuousAt]
      intro g
      unfold ContinuousAt
      simp
      rw[NormedAddCommGroup.tendsto_nhds_nhds]
      intro s rs
      use s
      constructor
      · exact rs
      · intro k ks
        rw[ContinuousMap.norm_lt_iff]
        · intro x
          simp
          have:k (c * x)-g (c * x)=(k -g ) (c * x) :=by exact rfl
          rw[this]
          exact lt_of_le_of_lt (ContinuousMap.norm_coe_le_norm (k - g) (c * x)) ks
        · exact rs

  }
  map_add' a b :=by
    ext c
    simp


  map_smul' a b :=by
     ext c
     simp


noncomputable def ϕ :(C(ℤ_[p],ℤ_[p]) →L[ℤ_[p]]  ℤ_[p] ) →ₗ[ℤ_[p]]
(C(ℤ_[p],ℤ_[p]) →L[ℤ_[p]]  ℤ_[p] ) := (action p)

noncomputable def Clopen_set_padic_nonunit :TopologicalSpace.Clopens ℤ_[p] where
  carrier :=(nonunits ℤ_[p])
  isClopen' :=by
    constructor
    · exact nonunits.isClosed
    · have:(nonunits ℤ_[p])ᶜ={a |‖a‖=1}:=by
         have: (nonunits ℤ_[p])ᶜ={x | IsUnit x}:=by
           have: {x | IsUnit x}ᶜ=(nonunits ℤ_[p]):=rfl
           exact compl_eq_comm.mp this
         rw[this]
         ext x
         constructor
         · intro ha
           refine Set.mem_setOf.mpr (PadicInt.isUnit_iff.mp ha)
         · intro  ha
           refine Set.mem_setOf.mpr (PadicInt.isUnit_iff.mpr ha)


      refine isClosed_compl_iff.mp ?_
      rw[this]
      refine isClosed_eq (continuous_norm) (continuous_const)

noncomputable def Clopen_set_padic_unit :TopologicalSpace.Clopens ℤ_[p] where
  carrier :={x | IsUnit x}
  isClopen' :=by
     have: {x | IsUnit x}ᶜ=(nonunits ℤ_[p]):=rfl
     refine isClopen_compl_iff.mp ?_
     rw[this]
     exact Clopen_set_padic_nonunit.2

lemma div_p (b:ℤ_[p])(sh:b∈ (Clopen_set_padic_nonunit)) :  ‖b.1 / ↑p‖ ≤ 1 :=by
  have:‖b.1‖<(p:ℝ)^(-1+1:ℤ ):=by
     simp
     exact  PadicInt.mem_nonunits.mp sh
  have:=(Padic.norm_le_pow_iff_norm_lt_pow_add_one (b.1) (-1)).mpr this
  simp
  simp at this
  have:=mul_le_mul_of_nonneg_right this (Nat.cast_nonneg' p)
  simp at this
  rw[inv_mul_cancel₀ (Ne.symm (NeZero.ne' (p:ℝ )))] at this
  exact this


noncomputable def ψ_function_1 (g:C(ℤ_[p], ℤ_[p])):C(ℤ_[p],ℤ_[p])where
  toFun b:= letI:Decidable (b∈ (Clopen_set_padic_nonunit)) :=
               by exact Classical.propDecidable (b ∈ nonunits ℤ_[p])
        if a:(b∈(Clopen_set_padic_nonunit)) then g ⟨b.1/p,div_p b a⟩ else 0
  continuous_toFun :=by
     let s:=(fun (b:ℤ_[p]) =>
        letI:Decidable (b∈ (Clopen_set_padic_nonunit)) :=
           by exact  Classical.propDecidable (b ∈ nonunits ℤ_[p])
       if a:(b∈(Clopen_set_padic_nonunit)) then g ⟨b.1/p, div_p b a⟩ else 0  )
     rw[continuous_iff_continuousAt]
     intro x
     rcases (Classical.em (x ∈ Clopen_set_padic_nonunit)) with A|B
     ·have:Filter.Tendsto s (nhds x) ( nhds (s x) ):=by
        rw[NormedAddCommGroup.tendsto_nhds_nhds]
        intro m hs
        have dt (x' : ℤ_[p])(es: ‖x' - x‖ < 1) :x'∈ (Clopen_set_padic_nonunit) :=by

          have:‖x'‖<1:=by
            have :=by exact PadicInt.nonarchimedean  (p:=p) (x' - x) x
            simp at this
            rcases this with s1|s2
            exact lt_of_le_of_lt s1 es
            exact lt_of_le_of_lt s2 (PadicInt.mem_nonunits.mp A)
          have:=PadicInt.mem_nonunits.mpr this
          exact this
        have dt2 (x' : ℤ_[p])(re: x'∈ (Clopen_set_padic_nonunit)):
           s x' =  g ⟨x'.1/p,div_p x' re⟩ :=by exact dif_pos re
        have:∃ δ > 0, ∀ (x' : ℤ_[p]), ‖x' - ⟨↑x / ↑p, div_p x A⟩‖ < δ
           → ‖g x' - g ⟨↑x / ↑p, div_p x A⟩‖ < m :=by
         have:=g.2
         rw[continuous_iff_continuousAt] at this
         have:=(this ⟨↑x / ↑p, div_p x A⟩)
         unfold ContinuousAt at this
         rw[NormedAddCommGroup.tendsto_nhds_nhds] at this
         exact this m hs
        choose u_1 j1 j2 using this
        use min ((p:ℝ)⁻¹) (u_1*(p:ℝ)⁻¹)
        constructor
        · simp
          constructor
          · exact Nat.pos_of_neZero p
          · refine mul_pos j1 (?_)
            simp
            exact Nat.pos_of_neZero p
        · intro j rj
          have: ‖j - x‖ < 1:=by

             have:(↑p)⁻¹ ⊓ u_1 * (p:ℝ)⁻¹≤ 1 :=by
                 simp
                 exact Or.symm (Or.inr (Nat.cast_inv_le_one p))
             exact gt_of_ge_of_gt this rj

          rw[dt2 j (dt j this)]
          rw[dt2 x A]
          let ej:ℤ_[p]:=⟨j.1 / p, (div_p j (dt j this)) ⟩
          have:‖ej-(⟨x.1 /p, (div_p x A)⟩)‖ <u_1 :=by
            unfold ej
            have:‖ej-(⟨x.1 /p, (div_p x A)⟩)‖ =‖j.1 / p-x.1 /p‖ :=rfl
            rw[this]
            have:j.1 / p-x.1 /p=(j.1 -x.1 )/ p:=by ring
            rw[this]
            simp
            have:‖j.1-x.1‖<u_1 * (p:ℝ)⁻¹:=by
               have:‖j.1-x.1‖=‖j-x‖:=rfl
               rw[this]
               have:=min_le_right (↑p)⁻¹ (u_1 * (↑p)⁻¹)
               exact gt_of_ge_of_gt this rj

            have:‖j.1-x.1‖*(p:ℝ)<u_1 * (p:ℝ)⁻¹*(p:ℝ):=by
              have y:(p:ℝ)>0 :=by
                      simp
                      exact Nat.pos_of_neZero p
              exact (mul_lt_mul_iff_of_pos_right y).mpr this
            have s:u_1 * (p:ℝ)⁻¹*(p:ℝ)=u_1 :=by
                      ring_nf
                      refine mul_inv_cancel_right₀ ?_ u_1
                      simp
                      exact NeZero.ne p
            rw[s] at this
            exact this

          exact j2 ej this
      exact this
     ·have:Filter.Tendsto s (nhds x) ( nhds (s x) ):=by
        rw[NormedAddCommGroup.tendsto_nhds_nhds]
        intro m hs
        have dt (x' : ℤ_[p])(es: ‖x' - x‖ < 1) :x'∉ (Clopen_set_padic_nonunit) :=by
          have g1:=PadicInt.isUnit_iff.mp (IsLocalRing.not_mem_maximalIdeal.mp B)
          have e:‖x'‖ =1 :=by
             have:‖(x' - x) +x‖=max ‖x' - x‖  ‖x‖ :=by
               refine IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm ?_
               by_contra s
               rw[g1] at s
               rw[s] at es
               exact (lt_self_iff_false 1).mp es
             simp at this
             rw[this]
             apply le_antisymm
             simp
             rw[g1]
             simp
             exact PadicInt.norm_le_one (x' - x)
             simp
             rw[g1]
             simp
          have:x'∉(nonunits ℤ_[p]):=by
            refine (Set.mem_compl_iff (nonunits ℤ_[p]) x').mp ?_
            have: (nonunits ℤ_[p])ᶜ={x | IsUnit x}:=by
              have: {x | IsUnit x}ᶜ=(nonunits ℤ_[p]):=rfl
              exact compl_eq_comm.mp this
            rw[this]
            refine Set.mem_setOf.mpr ?_
            exact PadicInt.isUnit_iff.mpr e
          exact this

        have dt2 (x' : ℤ_[p])(re: x'∉ (Clopen_set_padic_nonunit)):
         s x' =  0:=by
            unfold s
            simp [re]

        use 1
        constructor
        simp
        intro j sj
        rw[dt2 x B]
        rw[dt2 j (dt j sj)]
        simp
        exact hs
      exact this



noncomputable def ψ_function: C(ℤ_[p], ℤ_[p]) →L[ℤ_[p]] C(ℤ_[p],ℤ_[p]) where
  toFun g:=ψ_function_1 g

  map_add' a b :=by

    ext x
    simp
    rcases (Classical.em (x ∈ Clopen_set_padic_nonunit)) with A|B
    · unfold ψ_function_1
      simp[A]
    · unfold ψ_function_1
      simp[B]



  map_smul' s e:=by

    ext x
    simp
    rcases (Classical.em (x ∈ Clopen_set_padic_nonunit)) with A|B
    · unfold ψ_function_1
      simp[A]
    · unfold ψ_function_1
      simp[B]
  cont :=by
      rw[continuous_iff_continuousAt]
      intro g
      unfold ContinuousAt
      simp
      rw[NormedAddCommGroup.tendsto_nhds_nhds]
      intro s rs
      use s
      constructor
      · exact rs
      ·  intro x sx
         rw[ContinuousMap.norm_lt_iff ]
         ·intro y
          rcases (Classical.em (y ∈ Clopen_set_padic_nonunit)) with A|B
          · unfold ψ_function_1
            simp[A]
            have:‖x ⟨↑y / ↑p, div_p y A⟩ - g ⟨↑y / ↑p, div_p y A⟩‖
             =‖(x -g) ⟨↑y / ↑p, div_p y A⟩‖:=rfl
            rw[this]
            exact lt_of_le_of_lt (ContinuousMap.norm_coe_le_norm (x - g) ⟨y.1 / p, div_p y A⟩) sx
          · unfold ψ_function_1
            simp[B]
            exact rs
         ·exact rs






noncomputable def ψ :(C(ℤ_[p],ℤ_[p]) →L[ℤ_[p]]  ℤ_[p] ) →ₗ[ℤ_[p]]
(C(ℤ_[p],ℤ_[p]) →L[ℤ_[p]]  ℤ_[p] ) where
   toFun a:={
    toFun g := a ( ψ_function g)

    map_add' x y:=by
      simp



    map_smul' :=by simp
    cont :=by
     refine Continuous.comp' a.2 (ContinuousLinearMap.continuous ψ_function)

  }
   map_add' a b :=by
      simp
      exact rfl

   map_smul' a b :=by
    simp
    exact rfl


lemma c1:IsClopen (nonunits ℤ_[p]) :=by
  constructor
  · exact nonunits.isClosed
  · have:(nonunits ℤ_[p])ᶜ={a |‖a‖=1}:=by
       have: (nonunits ℤ_[p])ᶜ={x | IsUnit x}:=compl_eq_comm.mp rfl
       rw[this]
       ext x
       constructor
       · intro s
         refine Set.mem_setOf.mpr (PadicInt.isUnit_iff.mp s)
       · intro s
         refine Set.mem_setOf.mpr (PadicInt.isUnit_iff.mpr s)
    refine isClosed_compl_iff.mp ?_
    rw[this]
    refine isClosed_eq (continuous_norm) (continuous_const)
lemma ns :IsClopen ({a | IsUnit a}: Set ℤ_[p]):=by
  have:({a | IsUnit a}: Set ℤ_[p])ᶜ=(nonunits ℤ_[p]) :=rfl
  refine isClopen_compl_iff.mp c1



lemma lema_1: (ψ (p:=p))∘(ϕ (p:=p)) = id :=by
   ext c hs
   unfold ψ ϕ ψ_function action ψ_function_1
   simp_all
   refine DFunLike.congr_arg c ?_
   ext r
   simp
   have:p * r∈ (Clopen_set_padic_nonunit) :=mul_mem_nonunits_left (PadicInt.p_nonnunit)
   simp[this]
   refine DFunLike.congr_arg hs ?_
   refine ext ?_
   simp
   refine Eq.symm (CancelDenoms.cancel_factors_eq_div rfl ?_)
   simp
   exact NeZero.ne p

lemma lema_11 (a:(ℤ_[p])ˣ): (action (p:=p) a.1)∘(ψ (p:=p)) = (ψ (p:=p))∘(action (p:=p) a.1):=by
  unfold ψ action ψ_function ψ_function_1
  ext f x
  simp
  refine DFunLike.congr_arg f ?_
  ext y
  simp
  rcases (Classical.em (y ∈ Clopen_set_padic_nonunit)) with l1|l2
  · refine Lean.Grind.dite_cond_eq_true' (eq_true l1) ?_
    rw[Lean.Grind.dite_cond_eq_true']
    · simp
      exact mul_mem_nonunits_right l1
    refine ContinuousMap.congr_arg x ?_
    refine PadicInt.ext ?_
    simp
    ring
  simp[l2]
  have: ↑a * y ∉ Clopen_set_padic_nonunit :=by
    unfold Clopen_set_padic_nonunit
    simp
    exact IsLocalRing.not_mem_maximalIdeal.mp l2
  simp[this]
lemma lema_3 : id-(ϕ (p:=p))∘(ψ (p:=p))= restriction (p:=p) ⟨({a | IsUnit a}: Set ℤ_[p]),ns⟩
:=by
  ext a b
  unfold ψ ϕ ψ_function restriction action ψ_function_1 continues_locally_char Mul_of_a_measure
  simp_all
  rw[← ContinuousLinearMap.map_sub]
  refine DFunLike.congr_arg a ?_
  ext x
  simp
  have: Decidable (x ∈ Clopen_set_padic_nonunit):=by
   exact Classical.propDecidable (x ∈ Clopen_set_padic_nonunit)
  rcases (Decidable.em ( x ∈ Clopen_set_padic_nonunit )) with j1|j2
  · simp[j1]
    have: ↑p* ⟨x.1 / ↑p, div_p x j1⟩=x :=by
     refine PadicInt.ext ?_
     simp
     ring_nf
     refine (mul_inv_eq_iff_eq_mul₀ (Ne.symm (NeZero.ne' (p:ℚ_[p])))).mpr ?_
     ring
    rw[this]
    simp
    exact Or.symm (Or.intro_left (b x = 0) j1)
  · simp[j2]
    simp[IsLocalRing.not_mem_maximalIdeal.mp j2]


noncomputable def Convolution :(C(ℤ_[p],ℤ_[p]) →L[ℤ_[p]]  ℤ_[p] ) →
(C(ℤ_[p],ℤ_[p]) →L[ℤ_[p]]  ℤ_[p] )→ (C(ℤ_[p],ℤ_[p]) →L[ℤ_[p]]  ℤ_[p] )
| f_1 ,f_2 => {
    toFun g:=f_2 {
       toFun b:= f_1 ⟨(g)∘(fun( x :ℤ_[p])=> x+b),Continuous.comp g.2 (continuous_add_right b)⟩
       continuous_toFun :=by
         refine Continuous.comp' f_1.2 ?_
         rw[continuous_iff_continuousAt]
         intro x
         unfold ContinuousAt
         simp
         rw[NormedAddCommGroup.tendsto_nhds_nhds]
         intro s hs
         choose e se hsw using (ContinuousMap.uniform_continuity g s hs)
         use e
         constructor
         · exact se
         · intro x' fs
           rw[ContinuousMap.norm_lt_iff _ hs ]
           intro m
           simp only [ContinuousMap.sub_apply, ContinuousMap.coe_mk, Function.comp_apply]
           have:‖(m+x') -(m+x)‖ < e :=by
             rw[add_sub_add_left_eq_sub]
             exact fs
           exact hsw this
           }

--这些括号可能可以修剪更加简单
    map_add' x y:=by
       simp
       rw[← ContinuousLinearMap.map_add ]
       refine DFunLike.congr rfl ?_
       ext s
       simp
       rw[← ContinuousLinearMap.map_add ]
       refine DFunLike.congr rfl ?_
       ext s
       simp

    map_smul' a b :=by
       simp only [ContinuousMap.coe_smul, RingHom.id_apply]
       rw[←ContinuousLinearMap.map_smul_of_tower]
       refine DFunLike.congr rfl ?_
       ext s
       simp only [ContinuousMap.coe_mk, ContinuousMap.coe_smul, Pi.smul_apply]
       rw[←ContinuousLinearMap.map_smul_of_tower]
       refine DFunLike.congr rfl ?_
       ext s
       simp
    cont :=by
         refine Continuous.comp' f_2.2 ?_
         rw[continuous_iff_continuousAt]
         intro x
         unfold ContinuousAt
         simp
         rw[NormedAddCommGroup.tendsto_nhds_nhds]
         intro s rs
         sorry
  }


end PadicInt
