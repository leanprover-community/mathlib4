import Mathlib.InformationTheory.Code.Equiv
import Mathlib.InformationTheory.Code.Linear.SemiHom

open Set GMetric

variable {T K: Type*} [Field K] {σ₁₂ : K →+* K} {σ₂₁ : K →+* K} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂]
  {γ Tₖ M Tₘ M₂ Tₘ₂ :Type*}
variable [AddCommMonoid M] [AddCommMonoid M₂] [Module K M] [Module K M₂]
variable [Semiring γ] [CompleteLinearOrder γ] [ContravariantClass γ γ (.+.) (.<.)]
variable {gdistₖ : Tₖ}
variable {gdistₘ : Tₘ} {sₘ:Submodule K M}
variable--? [_LinearCode γ K gdistₖ gdistₘ s] =>
  [CovariantClass γ γ (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1] [FunLike Tₖ K (K → γ)]
  [GPseudoMetricClass Tₖ K γ] [AddGNorm K γ gdistₖ] [FunLike Tₘ M (M → γ)]
  [GPseudoMetricClass Tₘ M γ] [AddGNorm M γ gdistₘ] [IsDelone gdistₘ ↑sₘ] [Nontrivial γ]
  [PosMulMono γ] [MulPosMono γ] [ZeroLEOneClass γ]
  [StrictModuleGNorm K K gdistₖ gdistₖ] [StrictModuleGNorm K M gdistₖ gdistₘ]
variable {gdistₘ₂ : Tₘ₂} {sₘ₂:Submodule K M₂}
variable--? [_LinearCode γ K gdistₖ gdistₘ₂ s₂] =>
  [FunLike Tₘ₂ M₂ (M₂ → γ)] [GPseudoMetricClass Tₘ₂ M₂ γ] [AddGNorm M₂ γ gdistₘ₂]
  [IsDelone gdistₘ₂ ↑sₘ₂] [StrictModuleGNorm K M₂ gdistₖ gdistₘ₂]


@[simps!]
def SemilinearCodeHom.inverse
    (f:SemilinearCodeHom σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (g:M₂ → M) (h₁ : Function.LeftInverse g ⇑f)
    (h₂ : Function.RightInverse g ⇑f) (h₃: ∀ y∈ sₘ₂,g y ∈ sₘ):
  SemilinearCodeHom σ₂₁ gdistₖ gdistₘ₂ sₘ₂ gdistₘ sₘ := {
    f.toCodeHom.inverse g h₂ h₃,f.toLinearMap.inverse g h₁ h₂ with
  }

section
variable (T σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂)

structure SemilinearCodeEquiv [_LinearCode γ K gdistₖ gdistₘ sₘ]
  [_LinearCode γ K gdistₖ gdistₘ₂ sₘ₂]
  extends M ≃ₛₗ[σ₁₂] M₂, CodeEquiv gdistₘ sₘ gdistₘ₂ sₘ₂ -- tricky to get working

section
variable (K)
abbrev LinearCodeEquiv [_LinearCode γ K gdistₖ gdistₘ sₘ]
    [_LinearCode γ K gdistₖ gdistₘ₂ sₘ₂] :=
  SemilinearCodeEquiv (RingHom.id K) gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂
end

class SemilinearCodeEquivClass (T:Type*)
  {γ :outParam Type*} [Semiring γ] [CompleteLinearOrder γ] [ContravariantClass γ γ (.+.) (.<.)]
  [CovariantClass γ γ (.+.) (.≤.)] [Nontrivial γ] [PosMulMono γ] [MulPosMono γ] [ZeroLEOneClass γ]
  {K:outParam Type*} [Field K] (σ₁₂: outParam (K →+* K)) {σ₂₁ : outParam (K →+* K)}
  [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {Tₖ:outParam Type*} (gdistₖ : outParam Tₖ)
  [FunLike Tₖ K (K → γ)] [GPseudoMetricClass Tₖ K γ] [AddGNorm K γ gdistₖ]
  [StrictModuleGNorm K K gdistₖ gdistₖ] {M Tₘ:outParam Type*} [AddCommMonoid M] [Module K M]
  (gdistₘ : outParam Tₘ) (sₘ: outParam (Submodule K M)) [FunLike Tₘ M (M → γ)]
  [GPseudoMetricClass Tₘ M γ] [AddGNorm M γ gdistₘ] [StrictModuleGNorm K M gdistₖ gdistₘ]
  [IsDelone gdistₘ sₘ] -- [_LinearCode γ K gdistₖ gdistₘ sₘ]
  {M₂ Tₘ₂ : outParam Type*} [AddCommMonoid M₂] [Module K M₂]
  (gdistₘ₂ : outParam Tₘ₂) (sₘ₂ : outParam (Submodule K M₂)) [FunLike Tₘ₂ M₂ (M₂ → γ)]
  [GPseudoMetricClass Tₘ₂ M₂ γ] [AddGNorm M₂ γ gdistₘ₂] [StrictModuleGNorm K M₂ gdistₖ gdistₘ₂]
  [IsDelone gdistₘ₂ ↑sₘ₂] -- [_LinearCode γ K gdistₖ gdistₘ₂ sₘ₂]
  [EquivLike T M M₂]
  extends SemilinearEquivClass T σ₁₂ M M₂, CodeEquivClass T gdistₘ sₘ gdistₘ₂ sₘ₂

abbrev LinearCodeEquivClass (T:Type*)
  {γ :outParam Type*} [Semiring γ] [CompleteLinearOrder γ] [ContravariantClass γ γ (.+.) (.<.)]
  [CovariantClass γ γ (.+.) (.≤.)] [Nontrivial γ] [PosMulMono γ] [MulPosMono γ] [ZeroLEOneClass γ]
  (K:outParam Type*) [Field K] {Tₖ:outParam Type*} (gdistₖ : outParam Tₖ)
  [FunLike Tₖ K (K → γ)] [GPseudoMetricClass Tₖ K γ] [AddGNorm K γ gdistₖ]
  [StrictModuleGNorm K K gdistₖ gdistₖ] {M Tₘ:outParam Type*} [AddCommMonoid M] [Module K M]
  (gdistₘ : outParam Tₘ) (sₘ: outParam (Submodule K M)) [FunLike Tₘ M (M → γ)]
  [GPseudoMetricClass Tₘ M γ] [AddGNorm M γ gdistₘ] [StrictModuleGNorm K M gdistₖ gdistₘ]
  [IsDelone gdistₘ sₘ] -- [_LinearCode γ K gdistₖ gdistₘ sₘ]
  {M₂ Tₘ₂ : outParam Type*} [AddCommMonoid M₂] [Module K M₂]
  (gdistₘ₂ : outParam Tₘ₂) (sₘ₂ : outParam (Submodule K M₂)) [FunLike Tₘ₂ M₂ (M₂ → γ)]
  [GPseudoMetricClass Tₘ₂ M₂ γ] [AddGNorm M₂ γ gdistₘ₂] [StrictModuleGNorm K M₂ gdistₖ gdistₘ₂]
  [IsDelone gdistₘ₂ ↑sₘ₂] -- [_LinearCode γ K gdistₖ gdistₘ₂ sₘ₂]
  [EquivLike T M M₂]
  := SemilinearCodeEquivClass T (RingHom.id K) gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂

instance SemilinearCodeEquivClass.toSemilinearCodeHomClass (T:Type*)
    {γ :outParam Type*} [Semiring γ] [CompleteLinearOrder γ] [ContravariantClass γ γ (.+.) (.<.)]
    [CovariantClass γ γ (.+.) (.≤.)] [Nontrivial γ] [PosMulMono γ] [MulPosMono γ] [ZeroLEOneClass γ]
    {K:outParam Type*} [Field K] (σ₁₂: outParam (K →+* K)) {σ₂₁ : outParam (K →+* K)}
    [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {Tₖ:outParam Type*} (gdistₖ : outParam Tₖ)
    [FunLike Tₖ K (K → γ)] [GPseudoMetricClass Tₖ K γ] [AddGNorm K γ gdistₖ]
    [StrictModuleGNorm K K gdistₖ gdistₖ] {M Tₘ:outParam Type*} [AddCommMonoid M] [Module K M]
    (gdistₘ : outParam Tₘ) (sₘ: outParam (Submodule K M)) [FunLike Tₘ M (M → γ)]
    [GPseudoMetricClass Tₘ M γ] [AddGNorm M γ gdistₘ] [StrictModuleGNorm K M gdistₖ gdistₘ]
    [IsDelone gdistₘ sₘ] -- [_LinearCode γ K gdistₖ gdistₘ sₘ]
    {M₂ Tₘ₂ : outParam Type*} [AddCommMonoid M₂] [Module K M₂]
    (gdistₘ₂ : outParam Tₘ₂) (sₘ₂ : outParam (Submodule K M₂)) [FunLike Tₘ₂ M₂ (M₂ → γ)]
    [GPseudoMetricClass Tₘ₂ M₂ γ] [AddGNorm M₂ γ gdistₘ₂] [StrictModuleGNorm K M₂ gdistₖ gdistₘ₂]
    [IsDelone gdistₘ₂ ↑sₘ₂] -- [_LinearCode γ K gdistₖ gdistₘ₂ sₘ₂]
    [EquivLike T M M₂]
    [SemilinearCodeEquivClass T σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂]:
    SemilinearCodeHomClass T σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂ :=
  {‹SemilinearCodeEquivClass T σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂› with}
end


namespace SemilinearCodeEquiv

instance : EquivLike (SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) M M₂ where
  coe := fun f => f.toFun
  inv := fun f => f.invFun
  left_inv := fun f => f.left_inv
  right_inv := fun f => f.right_inv
  coe_injective' := fun f g h h₂ => by cases f; cases g; congr; simp_all

instance instSemilinearCodeEquivClass :
  SemilinearCodeEquivClass
    (SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂ where
    map_dist' := fun f => f.map_dist
    map_code' := fun f => f.map_code
    invMap_code' := fun f => f.invMap_code
    map_add := fun f => f.map_add'
    map_smulₛₗ := fun f => f.map_smul'

def toSemilinearCodeHom (φ : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
    SemilinearCodeHom σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂ := {φ with}


@[ext]
lemma ext ⦃φ φ₂:SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂⦄ (h:∀ x, φ x = φ₂ x) :
  φ = φ₂ := DFunLike.ext _ _ h

protected def copy (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (f' : M → M₂)
    (f_inv : M₂ → M) (hf : f' = ↑f) (hf_inv : f_inv = ↑f.symm) :
    SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂ :=
  {f.toCodeEquiv.copy f' f_inv hf hf_inv, f.toLinearEquiv.copy f' hf with}
end SemilinearCodeEquiv

variable [EquivLike T M M₂] [SemilinearCodeEquivClass T σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂]

@[coe]
def SemilinearCodeEquivClass.toSemilinearCodeEquiv [SemilinearCodeEquivClass T σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂]
  (f:T) : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂ := {
    ‹SemilinearCodeEquivClass T σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂›.toCodeEquiv f with
    map_add' := ‹SemilinearCodeEquivClass T σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂›.map_add f
    map_smul' := ‹SemilinearCodeEquivClass T σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂›.map_smulₛₗ f
  }

instance [SemilinearCodeEquivClass T σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂]:
    CoeTC T (SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :=
  ⟨SemilinearCodeEquivClass.toSemilinearCodeEquiv⟩


namespace SemilinearCodeEquiv

@[simp]
theorem toCodeEquiv_eq_coe (f :SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) : f.toCodeEquiv = f :=
  rfl

@[simp]
theorem toSemilinearCodeHom_eq_coe (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  f.toSemilinearCodeHom = f := rfl

@[simp]
theorem toLinearEquiv_eq_coe (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  f.toLinearEquiv = f := rfl

@[simp]
theorem coe_toCodeEquiv (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  ⇑(f : CodeEquiv gdistₘ sₘ gdistₘ₂ sₘ₂) = f := rfl

@[simp]
theorem coe_toLinearEquiv (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  ⇑(f : M ≃ₛₗ[σ₁₂] M₂) = f := rfl

@[simp 1100]
theorem coe_toLinearCodeHom (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  (f.toSemilinearCodeHom : M → M₂) = f := rfl

def mk'
    (f : M ≃ₛₗ[σ₁₂] M₂)
    (h₁ : ∀ x y, gdistₘ x y = gdistₘ₂ (f x) (f y)) (h₂ : ∀ x ∈ sₘ, f x ∈ sₘ₂)
    (h₃: ∀ (x : M), f x ∈ sₘ₂ → x ∈ sₘ) :
    SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂ :=  ⟨f, h₁,h₂,h₃⟩

protected theorem bijective
    (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) : Function.Bijective f :=
  EquivLike.bijective f

protected theorem injective
    (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) : Function.Injective f :=
  EquivLike.injective f

protected theorem surjective
    (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) : Function.Surjective f :=
  EquivLike.surjective f

section
variable (K gdistₖ gdistₘ sₘ)

@[refl]
def refl [_LinearCode γ K gdistₖ gdistₘ sₘ]:
  LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ sₘ := {
    CodeEquiv.refl gdistₘ sₘ with
    map_add' := by apply (LinearEquiv.refl K M).map_add'
    map_smul' := by apply (LinearEquiv.refl K M).map_smul'
    }


end
instance : Inhabited (LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ sₘ) := ⟨refl K gdistₖ gdistₘ sₘ⟩

@[symm]
def symm
    (f:SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂):
    SemilinearCodeEquiv σ₂₁ gdistₖ gdistₘ₂ sₘ₂ gdistₘ sₘ := {
  f.toLinearEquiv.symm,f.toCodeEquiv.symm with}

theorem invFun_eq_symm {f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂} : f.invFun = f.symm := rfl

@[simp]
theorem coe_toCodeEquiv_symm (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  ((f : CodeEquiv gdistₘ sₘ gdistₘ₂ sₘ₂).symm : M₂→ M) = f.symm := rfl

@[simp]
theorem coe_toLinearEquiv_symm (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  ((f : M ≃ₛₗ[σ₁₂] M₂).symm : M₂→ M) = f.symm := rfl

@[simp]
theorem equivLike_inv_eq_symm (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  EquivLike.inv f = f.symm := rfl

@[simp]
theorem toCodeEquiv_symm (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  (f.symm : CodeEquiv gdistₘ₂ sₘ₂ gdistₘ sₘ) = (f : CodeEquiv gdistₘ sₘ gdistₘ₂ sₘ₂).symm := rfl

@[simp]
theorem toLinearEquiv_symm (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  (f.symm : M₂ ≃ₛₗ[σ₂₁] M) = (f : M ≃ₛₗ[σ₁₂] M₂).symm := rfl

@[simp]
theorem coe_mk [StrictModuleGNorm K K gdistₖ gdistₖ] [StrictModuleGNorm K M gdistₖ gdistₘ]
    [StrictModuleGNorm K M₂ gdistₖ gdistₘ₂]
    (f : M ≃ₛₗ[σ₁₂] M₂) (map_dist : ∀ x y, gdistₘ x y = gdistₘ₂ (f x) (f y))
    (map_code : ∀ x ∈ sₘ, f x ∈ sₘ₂)
    (invMap_code: ∀ (x : M), f x ∈ sₘ₂ → x ∈ sₘ):
    ((⟨f,map_dist,map_code, invMap_code⟩:
    SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) : M → M₂) = ⇑f := rfl

@[simp]
theorem symm_symm (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) : f.symm.symm = f := rfl

theorem symm_bijective :
    Function.Bijective
      (symm : (SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) →
        SemilinearCodeEquiv σ₂₁ gdistₖ gdistₘ₂ sₘ₂ gdistₘ sₘ) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem symm_mk
    (f : M ≃ₛₗ[σ₁₂] M₂ ) (map_dist : ∀ x y, gdistₘ x y = gdistₘ₂ (f x) (f y))
    (map_code : ∀ x ∈ sₘ, f x ∈ sₘ₂) (invMap_code: ∀ (x : M), f x ∈ sₘ₂ → x ∈ sₘ):
    (mk f map_dist map_code invMap_code).symm = (⟨f.symm,
    fun x y => by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
      nth_rw 1 [← f.right_inv x, ← f.right_inv y]
      rw [map_dist]
      simp only [LinearEquiv.invFun_eq_symm, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply],
    fun x hx => by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe, SetLike.mem_coe]
      apply invMap_code
      simp only [LinearEquiv.apply_symm_apply]
      exact hx,
    fun x hx => by
      simp only [SetLike.mem_coe]
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        SetLike.mem_coe] at hx
      rw [← f.right_inv x]
      apply map_code
      exact hx⟩:
    SemilinearCodeEquiv σ₂₁ gdistₖ gdistₘ₂ sₘ₂ gdistₘ sₘ) := rfl


@[simp]
theorem refl_symm : (refl K gdistₖ gdistₘ sₘ).symm = refl K gdistₖ gdistₘ sₘ := rfl

@[simp]
theorem coe_copy
    (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (f' : M → M₂) (f_inv : M₂ → M) (hf : f' = ↑f)
    (hf_inv : f_inv = ⇑f.symm) : (f.copy f' f_inv hf hf_inv) = f' := rfl

theorem coe_copy_eq
    (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (f' : M → M₂) (f_inv : M₂ → M) (hf : f' = ↑f)
    (hf_inv : f_inv = ⇑f.symm) : (f.copy f' f_inv hf hf_inv) = f := by
  apply DFunLike.ext'
  rw [coe_copy,hf]

variable {σ₂₃ : K →+* K} {σ₁₃ : K →+* K} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
  {σ₃₂: K →+* K} {σ₃₁ : K →+* K} [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]
  [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
  [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
  {Tₘ₃ M₃:Type*} {gdistₘ₃:Tₘ₃} [AddCommMonoid M₃] [Module K M₃] {sₘ₃:Submodule K M₃}
variable--? [_LinearCode γ K gdistₖ gdistₘ₃ sₘ₃] =>
  [FunLike Tₘ₃ M₃ (M₃ → γ)] [GPseudoMetricClass Tₘ₃ M₃ γ] [AddGNorm M₃ γ gdistₘ₃]
  [IsDelone gdistₘ₃ ↑sₘ₃] [StrictModuleGNorm K M₃ gdistₖ gdistₘ₃]

@[trans]
def trans
    (φ:SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂)
    (φ₂:SemilinearCodeEquiv σ₂₃ gdistₖ gdistₘ₂ sₘ₂ gdistₘ₃ sₘ₃):
    SemilinearCodeEquiv σ₁₃ gdistₖ gdistₘ sₘ gdistₘ₃ sₘ₃ := {
  φ.toLinearEquiv.trans φ₂.toLinearEquiv,φ.toCodeEquiv.trans φ₂.toCodeEquiv with}

@[simp]
theorem apply_symm_apply (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (y : M₂) :
  f (f.symm y) = y := f.toEquiv.apply_symm_apply y

@[simp]
theorem symm_apply_apply (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (x : M) :
  f.symm (f x) = x := f.toEquiv.symm_apply_apply x

@[simp]
theorem symm_comp_self (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  f.symm ∘ f = _root_.id := funext f.symm_apply_apply

@[simp]
theorem self_comp_symm (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  f ∘ f.symm = _root_.id := funext f.apply_symm_apply

@[simp]
theorem coe_refl : ↑(refl K gdistₖ gdistₘ sₘ) = _root_.id := rfl

@[simp]
theorem refl_apply (x : M) : refl K gdistₖ gdistₘ sₘ x = x := rfl

@[simp]
theorem coe_trans
    (f₁ : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂)
    (f₂ : SemilinearCodeEquiv σ₂₃ gdistₖ gdistₘ₂ sₘ₂ gdistₘ₃ sₘ₃) :
  ↑(f₁.trans f₂) = f₂ ∘ f₁ := rfl

@[simp]
theorem trans_apply
    (f₁ : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂)
    (f₂ : SemilinearCodeEquiv σ₂₃ gdistₖ gdistₘ₂ sₘ₂ gdistₘ₃ sₘ₃) (x : M) :
    f₁.trans f₂ x = f₂ (f₁ x) := rfl

@[simp]
theorem symm_trans_apply
    (f₁ : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂)
    (f₂ : SemilinearCodeEquiv σ₂₃ gdistₖ gdistₘ₂ sₘ₂ gdistₘ₃ sₘ₃) (y : M₃) :
    (f₁.trans f₂).symm y = f₁.symm (f₂.symm y) := rfl

-- simp can prove this
theorem apply_eq_iff_eq
    (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) {x y : M} :
  f x = f y ↔ x = y := f.injective.eq_iff

theorem apply_eq_iff_symm_apply
    (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) {x : M} {y : M₂} :
  f x = y ↔ x = f.symm y := f.toEquiv.apply_eq_iff_eq_symm_apply

theorem symm_apply_eq
    (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) {x y} :
  f.symm x = y ↔ x = f y := f.toEquiv.symm_apply_eq

theorem eq_symm_apply
    (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) {x y} :
  y = f.symm x ↔ f y = x := f.toEquiv.eq_symm_apply

theorem eq_comp_symm
    {α : Type*} (e : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (f : M₂ → α) (g : M → α) :
  f = g ∘ e.symm ↔ f ∘ e = g :=
  e.toEquiv.eq_comp_symm f g

theorem comp_symm_eq
    {α : Type*} (e : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (f : M₂ → α) (g : M → α) :
  g ∘ e.symm = f ↔ g = f ∘ e := e.toEquiv.comp_symm_eq f g

theorem eq_symm_comp
    {α : Type*} (e : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (f : α → M) (g : α → M₂) :
  f = e.symm ∘ g ↔ e ∘ f = g := e.toEquiv.eq_symm_comp f g

theorem symm_comp_eq
    {α : Type*} (e : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (f : α → M) (g : α → M₂) :
  e.symm ∘ g = f ↔ g = e ∘ f := e.toEquiv.symm_comp_eq f g

@[simp]
theorem symm_trans_self
    (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂):
  f.symm.trans f = refl K gdistₖ gdistₘ₂ sₘ₂ := DFunLike.ext _ _ f.apply_symm_apply

@[simp]
theorem self_trans_symm
    (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  f.trans f.symm = refl K gdistₖ gdistₘ sₘ := DFunLike.ext _ _ f.symm_apply_apply

theorem ext_iff {f g : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂} : f = g ↔ ∀ x, f x = g x :=
  DFunLike.ext_iff

@[simp]
theorem mk_coe
    (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (f' h₁ h₂ h₃ h₄ h₅ h₆ h₇) :
    (⟨⟨⟨⟨f,h₁⟩,h₂⟩,f',h₃,h₄⟩,h₅,h₆,h₇⟩ : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) = f :=
  ext fun _ => rfl

@[simp]
theorem mk_coe' (f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (g h₁ h₂ h₃ h₄ h₅ h₆ h₇) :
    (SemilinearCodeEquiv.mk ⟨⟨⟨g,h₁⟩,h₂⟩,f,h₃,h₄⟩ h₅ h₆ h₇ :
    SemilinearCodeEquiv σ₂₁ gdistₖ gdistₘ₂ sₘ₂ gdistₘ sₘ) = f.symm :=
  symm_bijective.injective <| ext fun _ => rfl

protected theorem congr_arg
    {f : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂} {x x' : M} :
  x = x' → f x = f x' := DFunLike.congr_arg f

protected theorem congr_fun
    {f g : SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂} (h : f = g) (x : M) :
  f x = g x := DFunLike.congr_fun h x

@[simp]
lemma mk_apply (σ : RingAut K) (e :
  letI inst := RingHomInvPair.of_ringEquiv σ;
  letI := inst.symm;
  M ≃ₛₗ[(σ : K →+* K)] M₂) (m:M) (map_dist) (map_code) (invMap_code): (
    letI inst := RingHomInvPair.of_ringEquiv σ;
    letI := inst.symm;
    ⟨e,map_dist,map_code,invMap_code⟩ :
    letI inst := RingHomInvPair.of_ringEquiv σ;
    letI := inst.symm;
    SemilinearCodeEquiv σ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂ ) m = e m := rfl

end SemilinearCodeEquiv
