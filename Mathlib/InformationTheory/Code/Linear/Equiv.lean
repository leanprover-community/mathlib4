import Mathlib.InformationTheory.Code.Equiv
import Mathlib.InformationTheory.Code.Linear.Hom

open Set GMetric

variable {T K: Type*} {γ Tₖ M Tₘ M₂ Tₘ₂ :Type*}
variable [Field K] [AddCommMonoid M] [AddCommMonoid M₂] [Module K M] [Module K M₂]
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
def LinearCodeHom.inverse
    (f:LinearCodeHom K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (g:M₂ → M) (h₁ : Function.LeftInverse g ⇑f)
    (h₂ : Function.RightInverse g ⇑f) (h₃: ∀ y∈ sₘ₂,g y ∈ sₘ):
  LinearCodeHom K gdistₖ gdistₘ₂ sₘ₂ gdistₘ sₘ := {
    f.toCodeHom.inverse g h₂ h₃,f.toLinearMap.inverse g h₁ h₂ with
  }

section
variable (T K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂)

structure LinearCodeEquiv [_LinearCode γ K gdistₖ gdistₘ sₘ]
  [_LinearCode γ K gdistₖ gdistₘ₂ sₘ₂]
  extends CodeEquiv gdistₘ sₘ gdistₘ₂ sₘ₂, LinearEquiv (RingHom.id K) M M₂

class LinearCodeEquivClass (T:Type*)
  {γ :outParam Type*} [Semiring γ] [CompleteLinearOrder γ] [ContravariantClass γ γ (.+.) (.<.)]
  [CovariantClass γ γ (.+.) (.≤.)] [Nontrivial γ] [PosMulMono γ] [MulPosMono γ] [ZeroLEOneClass γ]
  (K:outParam Type*) [Field K] {Tₖ:outParam Type*} (gdistₖ : outParam Tₖ) [FunLike Tₖ K (K → γ)]
  [GPseudoMetricClass Tₖ K γ] [AddGNorm K γ gdistₖ] [StrictModuleGNorm K K gdistₖ gdistₖ]
  {M Tₘ:outParam Type*} [AddCommMonoid M] [Module K M]
  (gdistₘ : outParam Tₘ) (sₘ: outParam (Submodule K M)) [FunLike Tₘ M (M → γ)]
  [GPseudoMetricClass Tₘ M γ] [AddGNorm M γ gdistₘ] [StrictModuleGNorm K M gdistₖ gdistₘ]
  [IsDelone gdistₘ sₘ] -- [_LinearCode γ K gdistₖ gdistₘ sₘ]
  {M₂ Tₘ₂ : outParam Type*} [AddCommMonoid M₂] [Module K M₂]
  (gdistₘ₂ : outParam Tₘ₂) (sₘ₂ : outParam (Submodule K M₂)) [FunLike Tₘ₂ M₂ (M₂ → γ)]
  [GPseudoMetricClass Tₘ₂ M₂ γ] [AddGNorm M₂ γ gdistₘ₂] [StrictModuleGNorm K M₂ gdistₖ gdistₘ₂]
  [IsDelone gdistₘ₂ ↑sₘ₂] -- [_LinearCode γ K gdistₖ gdistₘ₂ sₘ₂]
  extends EquivLike T M M₂, LinearCodeHomClass T K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂ where
  invMap_code' : ∀ (φ:T), ∀ x, φ x ∈ sₘ₂ → x ∈ sₘ

instance LinearCodeEquivClass.toCodeEquivClass (T:Type*)
  {γ :outParam Type*} [Semiring γ] [CompleteLinearOrder γ] [ContravariantClass γ γ (.+.) (.<.)]
  [CovariantClass γ γ (.+.) (.≤.)] [Nontrivial γ] [PosMulMono γ] [MulPosMono γ] [ZeroLEOneClass γ]
  (K:outParam Type*) [Field K] {Tₖ:outParam Type*} (gdistₖ : outParam Tₖ) [FunLike Tₖ K (K → γ)]
  [GPseudoMetricClass Tₖ K γ] [AddGNorm K γ gdistₖ] [StrictModuleGNorm K K gdistₖ gdistₖ]
  {M Tₘ:outParam Type*} [AddCommMonoid M] [Module K M]
  (gdistₘ : outParam Tₘ) (sₘ: outParam (Submodule K M)) [FunLike Tₘ M (M → γ)]
  [GPseudoMetricClass Tₘ M γ] [AddGNorm M γ gdistₘ] [StrictModuleGNorm K M gdistₖ gdistₘ]
  [IsDelone gdistₘ sₘ] -- [_LinearCode γ K gdistₖ gdistₘ sₘ]
  {M₂ Tₘ₂ : outParam Type*} [AddCommMonoid M₂] [Module K M₂]
  (gdistₘ₂ : outParam Tₘ₂) (sₘ₂ : outParam (Submodule K M₂)) [FunLike Tₘ₂ M₂ (M₂ → γ)]
  [GPseudoMetricClass Tₘ₂ M₂ γ] [AddGNorm M₂ γ gdistₘ₂] [StrictModuleGNorm K M₂ gdistₖ gdistₘ₂]
  [IsDelone gdistₘ₂ ↑sₘ₂] -- [_LinearCode γ K gdistₖ gdistₘ₂ sₘ₂]
  [LinearCodeEquivClass T K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂]: CodeEquivClass T gdistₘ sₘ gdistₘ₂ sₘ₂ where
  map_dist' := GIsometryClass.map_dist'
  map_code' := CodeHomClass.map_code'
  invMap_code' := LinearCodeEquivClass.invMap_code'


instance LinearCodeEquivClass.toLinearEquivClass (T:Type*)
  {γ :outParam Type*} [Semiring γ] [CompleteLinearOrder γ] [ContravariantClass γ γ (.+.) (.<.)]
  [CovariantClass γ γ (.+.) (.≤.)] [Nontrivial γ] [PosMulMono γ] [MulPosMono γ] [ZeroLEOneClass γ]
  (K:outParam Type*) [Field K] {Tₖ:outParam Type*} (gdistₖ : outParam Tₖ) [FunLike Tₖ K (K → γ)]
  [GPseudoMetricClass Tₖ K γ] [AddGNorm K γ gdistₖ] [StrictModuleGNorm K K gdistₖ gdistₖ]
  {M Tₘ:outParam Type*} [AddCommMonoid M] [Module K M]
  (gdistₘ : outParam Tₘ) (sₘ: outParam (Submodule K M)) [FunLike Tₘ M (M → γ)]
  [GPseudoMetricClass Tₘ M γ] [AddGNorm M γ gdistₘ] [StrictModuleGNorm K M gdistₖ gdistₘ]
  [IsDelone gdistₘ sₘ] -- [_LinearCode γ K gdistₖ gdistₘ sₘ]
  {M₂ Tₘ₂ : outParam Type*} [AddCommMonoid M₂] [Module K M₂]
  (gdistₘ₂ : outParam Tₘ₂) (sₘ₂ : outParam (Submodule K M₂)) [FunLike Tₘ₂ M₂ (M₂ → γ)]
  [GPseudoMetricClass Tₘ₂ M₂ γ] [AddGNorm M₂ γ gdistₘ₂] [StrictModuleGNorm K M₂ gdistₖ gdistₘ₂]
  [IsDelone gdistₘ₂ ↑sₘ₂] -- [_LinearCode γ K gdistₖ gdistₘ₂ sₘ₂]
  [LinearCodeEquivClass T K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂]: LinearEquivClass T K M M₂ where
  map_add := AddHomClass.map_add
  map_smulₛₗ := SemilinearMapClass.map_smulₛₗ
end


namespace LinearCodeEquiv

instance instLinearCodeEquivClass :
  LinearCodeEquivClass
    (LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂ := {({
      coe := fun f => f.toFun
      inv := fun f => f.invFun
      left_inv := fun f => f.left_inv
      right_inv := fun f => f.right_inv
      coe_injective' := fun f g h h₂ => by cases f; cases g; congr; simp_all
    }:EquivLike (LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) M M₂) with
    map_dist' := fun f => f.map_dist
    map_code' := fun f => f.map_code
    invMap_code' := fun f => f.invMap_code
    map_add := fun f => f.map_add'
    map_smulₛₗ := fun f => f.map_smul'
    }

def toLinearCodeHom (φ : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :LinearCodeHom K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂ := {
  φ with
}


@[ext]
lemma ext ⦃φ φ₂:LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂⦄ (h:∀ x, φ x = φ₂ x) :
  φ = φ₂ := DFunLike.ext _ _ h

protected def copy (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (f' : M → M₂)
  (f_inv : M₂ → M) (hf : f' = ↑f) (hf_inv : f_inv = ↑f.toGIsometryEquiv.symm) :
    LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂ := {
      f.toCodeEquiv.copy f' f_inv hf hf_inv, f.toLinearEquiv.copy f' hf with
    }
end LinearCodeEquiv

variable [LinearCodeEquivClass T K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂]

@[coe]
def LinearCodeEquivClass.toLinearCodeEquiv [LinearCodeEquivClass T K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂]
  (f:T) : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂ := {
    CodeEquivClass.toCodeEquiv f, LinearCodeHomClass.toLinearCodeHom f with
  }

instance [LinearCodeEquivClass T K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂]:
  CoeTC T (LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) := ⟨LinearCodeEquivClass.toLinearCodeEquiv⟩


namespace LinearCodeEquiv

@[simp]
theorem toCodeEquiv_eq_coe (f :LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) : f.toCodeEquiv = f :=
  rfl

@[simp]
theorem toLinearCodeHom_eq_coe (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  f.toLinearCodeHom = f := rfl

@[simp]
theorem toLinearEquiv_eq_coe (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  f.toLinearEquiv = f := rfl

@[simp]
theorem coe_toCodeEquiv (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  ⇑(f : CodeEquiv gdistₘ sₘ gdistₘ₂ sₘ₂) = f := rfl

@[simp]
theorem coe_toLinearEquiv (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  ⇑(f : M ≃ₗ[K] M₂) = f := rfl

@[simp 1100]
theorem coe_toLinearCodeHom (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  (f.toLinearCodeHom : M → M₂) = f := rfl

def mk'
    (f : CodeEquiv gdistₘ sₘ gdistₘ₂ sₘ₂)
    (h₁ : ∀ x y, f (x + y) = f x + f y) (h₂ : ∀ (r:K) (x:M), f (r • x) = r • f x) :
    LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂ :=  ⟨f, h₁,h₂⟩

protected theorem bijective
    (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) : Function.Bijective f :=
  EquivLike.bijective f

protected theorem injective
    (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) : Function.Injective f :=
  EquivLike.injective f

protected theorem surjective
    (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) : Function.Surjective f :=
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
    (f:LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂):
    LinearCodeEquiv K gdistₖ gdistₘ₂ sₘ₂ gdistₘ sₘ := {
  f.toLinearEquiv.symm,f.toCodeEquiv.symm with}

theorem invFun_eq_symm {f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂} : f.invFun = f.symm := rfl

@[simp]
theorem coe_toCodeEquiv_symm (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  ((f : CodeEquiv gdistₘ sₘ gdistₘ₂ sₘ₂).symm : M₂→ M) = f.symm := rfl

@[simp]
theorem coe_toLinearEquiv_symm (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  ((f : M ≃ₗ[K] M₂).symm : M₂→ M) = f.symm := rfl

@[simp]
theorem equivLike_inv_eq_symm (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  EquivLike.inv f = f.symm := rfl

@[simp]
theorem toCodeEquiv_symm (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  (f.symm : CodeEquiv gdistₘ₂ sₘ₂ gdistₘ sₘ) = (f : CodeEquiv gdistₘ sₘ gdistₘ₂ sₘ₂).symm := rfl

@[simp]
theorem toLinearEquiv_symm (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  (f.symm : M₂ ≃ₗ[K] M) = (f : M ≃ₗ[K] M₂).symm := rfl

@[simp]
theorem coe_mk [StrictModuleGNorm K K gdistₖ gdistₖ] [StrictModuleGNorm K M gdistₖ gdistₘ]
    [StrictModuleGNorm K M₂ gdistₖ gdistₘ₂]
    (f : CodeEquiv gdistₘ sₘ gdistₘ₂ sₘ₂)
    (map_add' : ∀ (x y : M), f (x + y) = f x + f y)
    (map_smul' : ∀ (r : K) (x : M), f (r • x) = (RingHom.id K) r • f x):
    ((⟨f,map_add', map_smul'⟩: LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) : M → M₂) = ⇑f := rfl

@[simp]
theorem symm_symm (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) : f.symm.symm = f := rfl

theorem symm_bijective :
    Function.Bijective
      (symm : (LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) →
        LinearCodeEquiv K gdistₖ gdistₘ₂ sₘ₂ gdistₘ sₘ) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem symm_mk
    (f : CodeEquiv gdistₘ sₘ gdistₘ₂ sₘ₂) (map_add : ∀ x y, f (x + y) = f x + f y)
    (map_smul : ∀ (k:K) (m:M), f (k • m) = k • f m):
    (mk f map_add map_smul).symm = (⟨f.symm,
      fun x y => by
        nth_rw 1 [← f.right_inv x,← f.right_inv y]
        simp only [CodeEquiv.toGIsometryEquiv_eq_coe, CodeEquiv.toGIsometryEquiv_symm,
          GIsometryEquiv.toEquiv_eq_coe, GIsometryEquiv.toEquiv_symm, Equiv.invFun_as_coe,
          GIsometryEquiv.coe_toEquiv_symm, CodeEquiv.coe_toGIsometryEquiv_symm, Equiv.toFun_as_coe,
          EquivLike.coe_coe, CodeEquiv.coe_toGIsometryEquiv]
        rw [← map_add (CodeEquiv.symm f x) (CodeEquiv.symm f y)]
        simp only [CodeEquiv.symm_apply_apply],
      fun k m => by
        nth_rw 1 [← f.right_inv m]
        simp only [CodeEquiv.toGIsometryEquiv_eq_coe, CodeEquiv.toGIsometryEquiv_symm,
          GIsometryEquiv.toEquiv_eq_coe, GIsometryEquiv.toEquiv_symm, Equiv.invFun_as_coe,
          GIsometryEquiv.coe_toEquiv_symm, CodeEquiv.coe_toGIsometryEquiv_symm, Equiv.toFun_as_coe,
          EquivLike.coe_coe, CodeEquiv.coe_toGIsometryEquiv, RingHom.id_apply]
        rw [← map_smul k (CodeEquiv.symm f m)]
        simp only [CodeEquiv.symm_apply_apply]⟩:LinearCodeEquiv K gdistₖ gdistₘ₂ sₘ₂ gdistₘ sₘ) := rfl


@[simp]
theorem refl_symm : (refl K gdistₖ gdistₘ sₘ).symm = refl K gdistₖ gdistₘ sₘ := rfl

@[simp]
theorem coe_copy
    (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (f' : M → M₂) (f_inv : M₂ → M) (hf : f' = ↑f)
    (hf_inv : f_inv = ⇑f.toGIsometryEquiv.symm) : (f.copy f' f_inv hf hf_inv) = f' := rfl

theorem coe_copy_eq
    (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (f' : M → M₂) (f_inv : M₂ → M) (hf : f' = ↑f)
    (hf_inv : f_inv = ⇑f.toGIsometryEquiv.symm) : (f.copy f' f_inv hf hf_inv) = f := by
  apply DFunLike.ext'
  rw [coe_copy,hf]



variable {Tₘ₃ M₃:Type*} {gdistₘ₃:Tₘ₃} [AddCommMonoid M₃] [Module K M₃] {sₘ₃:Submodule K M₃}
variable--? [_LinearCode γ K gdistₖ gdistₘ₃ sₘ₃] =>
  [FunLike Tₘ₃ M₃ (M₃ → γ)] [GPseudoMetricClass Tₘ₃ M₃ γ] [AddGNorm M₃ γ gdistₘ₃]
  [IsDelone gdistₘ₃ ↑sₘ₃] [StrictModuleGNorm K M₃ gdistₖ gdistₘ₃]

@[trans]
def trans
    (φ:LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂)
    (φ₂:LinearCodeEquiv K gdistₖ gdistₘ₂ sₘ₂ gdistₘ₃ sₘ₃):
    LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₃ sₘ₃ := {
  φ.toLinearEquiv.trans φ₂.toLinearEquiv,φ.toCodeEquiv.trans φ₂.toCodeEquiv with}

@[simp]
theorem apply_symm_apply (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (y : M₂) :
  f (f.symm y) = y := f.toEquiv.apply_symm_apply y

@[simp]
theorem symm_apply_apply (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (x : M) :
  f.symm (f x) = x := f.toEquiv.symm_apply_apply x

@[simp]
theorem symm_comp_self (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  f.symm ∘ f = _root_.id := funext f.symm_apply_apply

@[simp]
theorem self_comp_symm (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  f ∘ f.symm = _root_.id := funext f.apply_symm_apply

@[simp]
theorem coe_refl : ↑(refl K gdistₖ gdistₘ sₘ) = _root_.id := rfl

@[simp]
theorem refl_apply (x : M) : refl K gdistₖ gdistₘ sₘ x = x := rfl

@[simp]
theorem coe_trans
    (f₁ : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂)
    (f₂ : LinearCodeEquiv K gdistₖ gdistₘ₂ sₘ₂ gdistₘ₃ sₘ₃) :
  ↑(f₁.trans f₂) = f₂ ∘ f₁ := rfl

@[simp]
theorem trans_apply
    (f₁ : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂)
    (f₂ : LinearCodeEquiv K gdistₖ gdistₘ₂ sₘ₂ gdistₘ₃ sₘ₃) (x : M) :
    f₁.trans f₂ x = f₂ (f₁ x) := rfl

@[simp]
theorem symm_trans_apply
    (f₁ : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂)
    (f₂ : LinearCodeEquiv K gdistₖ gdistₘ₂ sₘ₂ gdistₘ₃ sₘ₃) (y : M₃) :
    (f₁.trans f₂).symm y = f₁.symm (f₂.symm y) := rfl

-- simp can prove this
theorem apply_eq_iff_eq
    (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) {x y : M} :
  f x = f y ↔ x = y := f.injective.eq_iff

theorem apply_eq_iff_symm_apply
    (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) {x : M} {y : M₂} :
  f x = y ↔ x = f.symm y := f.toEquiv.apply_eq_iff_eq_symm_apply

theorem symm_apply_eq
    (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) {x y} :
  f.symm x = y ↔ x = f y := f.toEquiv.symm_apply_eq

theorem eq_symm_apply
    (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) {x y} :
  y = f.symm x ↔ f y = x := f.toEquiv.eq_symm_apply

theorem eq_comp_symm
    {α : Type*} (e : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (f : M₂ → α) (g : M → α) :
  f = g ∘ e.symm ↔ f ∘ e = g :=
  e.toEquiv.eq_comp_symm f g

theorem comp_symm_eq
    {α : Type*} (e : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (f : M₂ → α) (g : M → α) :
  g ∘ e.symm = f ↔ g = f ∘ e := e.toEquiv.comp_symm_eq f g

theorem eq_symm_comp
    {α : Type*} (e : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (f : α → M) (g : α → M₂) :
  f = e.symm ∘ g ↔ e ∘ f = g := e.toEquiv.eq_symm_comp f g

theorem symm_comp_eq
    {α : Type*} (e : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (f : α → M) (g : α → M₂) :
  e.symm ∘ g = f ↔ g = e ∘ f := e.toEquiv.symm_comp_eq f g

@[simp]
theorem symm_trans_self
    (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂):
  f.symm.trans f = refl K gdistₖ gdistₘ₂ sₘ₂ := DFunLike.ext _ _ f.apply_symm_apply

@[simp]
theorem self_trans_symm
    (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
  f.trans f.symm = refl K gdistₖ gdistₘ sₘ := DFunLike.ext _ _ f.symm_apply_apply

theorem ext_iff {f g : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂} : f = g ↔ ∀ x, f x = g x :=
  DFunLike.ext_iff

@[simp]
theorem mk_coe
    (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (f' h₁ h₂ h₃ h₄ h₅ h₆ h₇) :
    (⟨⟨⟨⟨f,f',h₁,h₂⟩,h₃⟩,h₄,h₅⟩,h₆,h₇⟩ : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) = f :=
  ext fun _ => rfl

@[simp]
theorem mk_coe' (f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (g h₁ h₂ h₃ h₄ h₅ h₆ h₇) :
    (LinearCodeEquiv.mk ⟨⟨⟨g, f, h₁, h₂⟩,h₃⟩, h₄,h₅⟩ h₆ h₇ : LinearCodeEquiv K gdistₖ gdistₘ₂ sₘ₂ gdistₘ sₘ) = f.symm :=
  symm_bijective.injective <| ext fun _ => rfl

protected theorem congr_arg
    {f : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂} {x x' : M} :
  x = x' → f x = f x' := DFunLike.congr_arg f

protected theorem congr_fun
    {f g : LinearCodeEquiv K gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂} (h : f = g) (x : M) :
  f x = g x := DFunLike.congr_fun h x


end LinearCodeEquiv
