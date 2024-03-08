import Mathlib

section UniqueUnital

section IsROrC

variable {𝕜 A : Type*} [IsROrC 𝕜] [NormedRing A] [StarRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
instance : UniqueContinuousFunctionalCalculus 𝕜 A where
  eq_of_continuous_of_map_id s hs φ ψ hφ hψ h :=
    ContinuousMap.starAlgHom_ext_map_X hφ hψ <| by
      convert h using 1
      all_goals exact congr_arg _ (by ext; simp)
  compactSpace_spectrum a := inferInstance

end IsROrC

section NNReal
open NNReal

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
variable {X : Type*} [TopologicalSpace X]

lemma max_neg_zero {α : Type*} [AddCommGroup α] [LinearOrder α] [CovariantClass α α (· + ·) (· ≤ ·)]
    (a : α) : max (-a) 0 = max a 0 - a := by
  have := congr(-$(max_zero_sub_eq_self a))
  rwa [neg_sub, sub_eq_iff_eq_add', ← sub_eq_add_neg] at this

/-- This map sends `f : C(X, ℝ)` to `f ⊔ 0`, bundled as a continuous map `C(X, ℝ≥0)`. -/
@[pp_dot]
noncomputable def ContinuousMap.toNNReal (f : C(X, ℝ)) : C(X, ℝ≥0) :=
  .realToNNReal |>.comp f

@[fun_prop]
lemma ContinuousMap.continuous_toNNReal : Continuous (ContinuousMap.toNNReal (X := X)) :=
  ContinuousMap.continuous_comp _

@[simp]
lemma ContinuousMap.toNNReal_apply (f : C(X, ℝ)) (x : X) : f.toNNReal x = (f x).toNNReal := rfl

lemma ContinuousMap.toNNReal_add (f g : C(X, ℝ)) :
    (f + g).toNNReal + (-f).toNNReal + (-g).toNNReal =
      (-(f + g)).toNNReal + f.toNNReal + g.toNNReal := by
  ext x
  simp [max_neg_zero, -neg_add_rev]
  abel

lemma ContinuousMap.toNNReal_mul (f g : C(X, ℝ)) :
    (f * g).toNNReal + (-f).toNNReal * g.toNNReal + f.toNNReal * (-g).toNNReal=
      (-(f * g)).toNNReal + f.toNNReal * g.toNNReal + (-f).toNNReal * (-g).toNNReal := by
  ext x
  simp [max_neg_zero, mul_sub, sub_mul]
  abel

@[simp]
lemma ContinuousMap.toNNReal_algebraMap (r : ℝ≥0) :
    (algebraMap ℝ C(X, ℝ) r).toNNReal = algebraMap ℝ≥0 C(X, ℝ≥0) r := by
  ext; simp

@[simp]
lemma ContinuousMap.toNNReal_neg_algebraMap (r : ℝ≥0) :
    (- algebraMap ℝ C(X, ℝ) r).toNNReal = 0 := by
  ext; simp

/-- Given a star `ℝ≥0`-algebra homomorphism `φ` from `C(X, ℝ≥0)` into an `ℝ`-algebra `A`, this is
the unique extension of `φ` from `C(X, ℝ)` to `A` as a star `ℝ`-algebra homomorphism. -/
@[simps]
noncomputable def StarAlgHom.realContinuousMapOfNNReal (φ : C(X, ℝ≥0) →⋆ₐ[ℝ≥0] A) :
    C(X, ℝ) →⋆ₐ[ℝ] A where
  toFun f := φ f.toNNReal - φ (-f).toNNReal
  map_one' := by
    have h₁ : (1 : C(X, ℝ)).toNNReal = 1 := ?_
    have h₂ : (-1 : C(X, ℝ)).toNNReal = 0 := ?_
    · simp only [h₁, map_one φ, h₂, map_zero φ, sub_zero]
    all_goals ext x; simp
  map_zero' := by simp only [neg_zero, sub_self]
  map_mul' f g := by
    have := congr(φ $(f.toNNReal_mul g))
    simp only [map_add, map_mul, sub_mul, mul_sub] at this ⊢
    rw [← sub_eq_zero] at this ⊢
    convert this using 1
    abel
  map_add' f g := by
    have := congr(φ $(f.toNNReal_add g))
    simp only [map_add] at this ⊢
    rw [← sub_eq_zero] at this ⊢
    convert this using 1
    abel
  commutes' r := by
    simp only
    obtain (hr | hr) := le_total 0 r
    · lift r to ℝ≥0 using hr
      simpa only [ContinuousMap.toNNReal_algebraMap, ContinuousMap.toNNReal_neg_algebraMap,
        map_zero, sub_zero] using AlgHomClass.commutes φ r
    · rw [← neg_neg r, ← map_neg, neg_neg (-r)]
      rw [← neg_nonneg] at hr
      lift -r to ℝ≥0 using hr with r
      simpa only [map_neg, ContinuousMap.toNNReal_neg_algebraMap, map_zero,
        ContinuousMap.toNNReal_algebraMap, zero_sub, neg_inj] using AlgHomClass.commutes φ r
  map_star' f := by simp only [star_trivial, star_sub, ← map_star]

@[fun_prop]
lemma StarAlgHom.continuous_realContinuousMapOfNNReal (φ : C(X, ℝ≥0) →⋆ₐ[ℝ≥0] A)
    (hφ : Continuous φ) : Continuous φ.realContinuousMapOfNNReal := by
  simp [realContinuousMapOfNNReal]
  fun_prop

@[simp high]
lemma StarAlgHom.realContinuousMapOfNNReal_apply_comp_toReal (φ : C(X, ℝ≥0) →⋆ₐ[ℝ≥0] A)
    (f : C(X, ℝ≥0)) :
    φ.realContinuousMapOfNNReal ((ContinuousMap.mk toReal continuous_coe).comp f) = φ f := by
  simp only [realContinuousMapOfNNReal_apply]
  convert_to φ f - φ 0 = φ f using 2
  on_goal -1 => rw [map_zero, sub_zero]
  all_goals
    congr
    ext x
    simp

lemma StarAlgHom.injective_realContinuousMapOfNNReal :
    Function.Injective (realContinuousMapOfNNReal (X := X) (A := A)) := by
  intro φ ψ h
  ext f
  simpa using congr($(h) ((ContinuousMap.mk toReal continuous_coe).comp f))

attribute [pp_dot] ContinuousMap.comp

instance : UniqueContinuousFunctionalCalculus ℝ≥0 A where
  compactSpace_spectrum := inferInstance
  eq_of_continuous_of_map_id s hs φ ψ hφ hψ h := by
    let s' : Set ℝ := (↑) '' s
    let e : s ≃ₜ s' :=
      { toFun := Subtype.map (↑) (by simp [s'])
        invFun := Subtype.map Real.toNNReal (by simp [s'])
        left_inv := fun _ ↦ by ext; simp
        right_inv := fun x ↦ by
          ext
          obtain ⟨y, -, hy⟩ := x.2
          simpa using hy ▸ NNReal.coe_nonneg y
        continuous_toFun := continuous_coe.subtype_map (by simp [s'])
        continuous_invFun := continuous_real_toNNReal.subtype_map (by simp [s']) }
    have (ξ : C(s, ℝ≥0) →⋆ₐ[ℝ≥0] A) (hξ : Continuous ξ) :
        (let ξ' := ξ.realContinuousMapOfNNReal.comp <| ContinuousMap.compStarAlgHom' ℝ ℝ e;
        Continuous ξ' ∧ ξ' (.restrict s' <| .id ℝ) = ξ (.restrict s <| .id ℝ≥0)) := by
      intro ξ'
      refine ⟨ξ.continuous_realContinuousMapOfNNReal hξ |>.comp <|
        ContinuousMap.continuous_comp_left _, ?_⟩
      exact ξ.realContinuousMapOfNNReal_apply_comp_toReal (.restrict s <| .id ℝ≥0)
    obtain ⟨hφ', hφ_id⟩ := this φ hφ
    obtain ⟨hψ', hψ_id⟩ := this ψ hψ
    have hs' : CompactSpace s' := e.compactSpace
    have h' := UniqueContinuousFunctionalCalculus.eq_of_continuous_of_map_id s' _ _ hφ' hψ'
      (hφ_id ▸ hψ_id ▸ h)
    have h'' := congr($(h').comp <| ContinuousMap.compStarAlgHom' ℝ ℝ (e.symm : C(s', s)))
    have : (ContinuousMap.compStarAlgHom' ℝ ℝ (e : C(s, s'))).comp
        (ContinuousMap.compStarAlgHom' ℝ ℝ (e.symm : C(s', s))) = StarAlgHom.id _ _ := by
      ext1; simp
    simp only [StarAlgHom.comp_assoc, this, StarAlgHom.comp_id] at h''
    exact StarAlgHom.injective_realContinuousMapOfNNReal h''

end NNReal

end UniqueUnital
