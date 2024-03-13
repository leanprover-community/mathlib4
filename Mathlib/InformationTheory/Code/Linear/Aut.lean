import Mathlib.InformationTheory.Code.Basic
import Mathlib.InformationTheory.Code.Aut

import Mathlib.InformationTheory.Code.Linear.Equiv

open Code
open LinearCode
open CodeAut
variable {γ K Tₖ M Tₘ:Type*} {gdistₖ: Tₖ} {gdistₘ:Tₘ}
variable [Semiring γ] [CompleteLinearOrder γ]
  [CovariantClass γ γ (.+.) (.≤.)] [FunLike Tₖ K (K → γ)]
  [GPseudoMetricClass Tₖ K γ]

variable [Field K] [AddCommMonoid M]
variable? [AddGNorm K γ gdistₖ] => [AddGNorm K γ gdistₖ]
variable? [AddGNorm M γ gdistₘ] => [FunLike Tₘ M (M → γ)] [GPseudoMetricClass Tₘ M γ]
  [AddGNorm M γ gdistₘ]

variable--? {s : Submodule K M} =>
  [Module K M] {s : Submodule K M}

variable-- ? [_LinearCode γ K gdistₖ gdistₘ sₘ] =>
  [Set.IsDelone gdistₘ ↑s] [Nontrivial γ]
  [PosMulMono γ] [MulPosMono γ] [ZeroLEOneClass γ] [StrictModuleGNorm K K gdistₖ gdistₖ]
  [StrictModuleGNorm K M gdistₖ gdistₘ]

section
variable (K gdistₖ gdistₘ s)

@[reducible]
def LinearCodeAut [_LinearCode γ K gdistₖ gdistₘ s] :Type _ := LinearCodeEquiv K gdistₖ gdistₘ s gdistₘ s
end

namespace LinearCodeAut

instance instGroup [_LinearCode γ K gdistₖ gdistₘ s] : Group (LinearCodeAut K gdistₖ gdistₘ s) := {
    mul := fun f g => g.trans f
    mul_assoc := fun a b c ↦ rfl
    one := LinearCodeEquiv.refl K gdistₖ gdistₘ s
    one_mul := fun a ↦ rfl
    mul_one := fun a ↦ rfl
    inv := LinearCodeEquiv.symm
    mul_left_inv := LinearCodeEquiv.self_trans_symm
    }

@[simp]
theorem coe_mul (e₁ e₂ : LinearCodeAut K gdistₖ gdistₘ s) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl

@[simp]
theorem coe_one : ⇑(1 : LinearCodeAut K gdistₖ gdistₘ s) = id :=
  rfl

theorem mul_def (e₁ e₂ : LinearCodeAut K gdistₖ gdistₘ s) : e₁ * e₂ = e₂.trans e₁ :=
  rfl

theorem one_def : (1 : LinearCodeAut K gdistₖ gdistₘ s) = LinearCodeEquiv.refl _ _ _ _ :=
  rfl

theorem inv_def (e₁ : LinearCodeAut K gdistₖ gdistₘ s) : e₁⁻¹ = e₁.symm :=
  rfl


@[simp]
theorem mul_apply (e₁ e₂ : LinearCodeAut K gdistₖ gdistₘ s) (m : M) : (e₁ * e₂) m = e₁ (e₂ m) :=
  rfl

@[simp]
theorem one_apply (m : M) : (1 : LinearCodeAut K gdistₖ gdistₘ s) m = m :=
  rfl

@[simp]
theorem apply_inv_self (e : LinearCodeAut K gdistₖ gdistₘ s) (m : M) : e (e⁻¹ m) = m :=
  LinearCodeEquiv.apply_symm_apply _ _

@[simp]
theorem inv_apply_self (e : LinearCodeAut K gdistₖ gdistₘ s) (m : M) : e⁻¹ (e m) = m :=
  LinearCodeEquiv.apply_symm_apply _ _


def toCodeAut : (LinearCodeAut K gdistₖ gdistₘ s) →* (CodeAut gdistₘ s) where
  toFun := LinearCodeEquiv.toCodeEquiv
  map_one' := by simp_all only [LinearCodeEquiv.toCodeEquiv_eq_coe]; rfl
  map_mul' := fun x y => by simp_all only [LinearCodeEquiv.toCodeEquiv_eq_coe]; rfl

def toLinearAut : (LinearCodeAut K gdistₖ gdistₘ s) →* (M ≃ₗ[K] M) where
  toFun := LinearCodeEquiv.toLinearEquiv
  map_one':= by simp_all only [LinearCodeEquiv.toLinearEquiv_eq_coe]; rfl
  map_mul' := fun x y => by simp_all only [LinearCodeEquiv.toLinearEquiv_eq_coe]; rfl


instance applyMulDistribMulAction :
    MulDistribMulAction (LinearCodeAut K gdistₖ gdistₘ s) (Multiplicative M) where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_one := fun f => (f: M →+ M).map_zero'
  smul_mul := fun f => (f: M →+ M).map_add'

@[simp]
protected theorem smul_def (f : LinearCodeAut K gdistₖ gdistₘ s) (a :Multiplicative M) :
  f • a = f a := rfl

instance apply_faithfulSMul : FaithfulSMul (LinearCodeAut K gdistₖ gdistₘ s) (Multiplicative M) :=
  ⟨fun h => LinearCodeEquiv.ext h⟩

end LinearCodeAut
