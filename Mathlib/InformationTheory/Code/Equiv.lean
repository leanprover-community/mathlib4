import Mathlib.InformationTheory.Code.Hom
import Mathlib.Algebra.Module.Equiv

namespace Code
open GMetric
open GIsometry
open Set
section code
variable (T₃:Type*)
variable {α γ :Type*} [CompleteLinearOrder γ] [AddCommMonoid γ]

variable {T:Type*} (gdist:T)
variable (s:Set α)
variable [CovariantClass γ γ (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
  [FunLike T α (α → γ)] [GPseudoMetricClass T α γ] [IsDelone gdist s] [_Code γ gdist s]
variable {α₂ T₂ :Type*} (gdist₂:T₂)(s₂ : Set α₂)
variable [FunLike T₂ α₂ (α₂ → γ)] [GPseudoMetricClass T₂ α₂ γ]
  [IsDelone gdist₂ s₂] [_Code γ gdist₂ s₂]

@[ext]
structure CodeEquiv extends CodeHom gdist s gdist₂ s₂, α ≃ α₂ where
  invMap_code : invFun '' s₂ ⊆ s

instance CodeEquiv.instEquivLike : EquivLike (CodeEquiv gdist s gdist₂ s₂) α α₂ where
  coe := fun φ => φ.toFun
  inv := fun φ => φ.invFun
  left_inv := fun φ => φ.left_inv
  right_inv := fun φ => φ.right_inv
  coe_injective' := fun φ₁ φ₂ => by
    simp only
    intro h1 h2
    ext x
    . rw [h1]
    . rw [h2]

instance CodeEquiv.instGIsometryClass : GIsometryClass (CodeEquiv gdist s gdist₂ s₂) gdist gdist₂ where
  map_dist := fun φ => φ.map_dist

variable [FunLike T₃ α α₂]
  [GIsometryClass T₃ gdist gdist₂] [EquivLike T₃ α α₂]

class CodeEquivClass
    [_Code γ gdist s]
    [_Code γ gdist₂ s₂] [GIsometryClass T₃ gdist gdist₂] [EquivLike T₃ α α₂]
    extends CodeHomClass T₃ gdist s gdist₂ s₂ :Prop where
  invMap_code : ∀ (φ:T₃), Equiv.invFun φ '' s₂ ⊆ s

instance CodeEquiv.instCodeEquivClass :
    CodeEquivClass (CodeEquiv gdist s gdist₂ s₂) gdist s gdist₂ s₂ where
  map_code := fun φ => φ.map_code
  invMap_code := fun φ => φ.invMap_code
end code

section linearcode
set_option variable?.maxSteps 20
variable (T₃ K: Type*) {γ Tₖ M Tₘ M₂ Tₘ₂ :Type*}
variable [Field K] [AddCommMonoid M] [AddCommMonoid M₂] [Module K M] [Module K M₂]
variable [Semiring γ] [CompleteLinearOrder γ] [ContravariantClass γ γ (.+.) (.<.)]
variable (gdist_k : Tₖ)
variable (gdist_m : Tₘ) (s:Submodule K M)
variable
  [CovariantClass γ γ (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1] [FunLike Tₖ K (K → γ)]
  [GPseudoMetricClass Tₖ K γ] [AddGNorm K γ gdist_k] [FunLike Tₘ M (M → γ)]
  [GPseudoMetricClass Tₘ M γ] [AddGNorm M γ gdist_m] [IsDelone gdist_m ↑s] [Nontrivial γ]
  [PosMulMono γ] [MulPosMono γ] [ZeroLEOneClass γ]
  [StrictModuleGNorm K K gdist_k gdist_k] [StrictModuleGNorm K M gdist_k gdist_m]
  [_Code γ gdist_m ↑s] [_LinearCode γ K gdist_k gdist_m s]
variable (gdist_m₂ : Tₘ₂) (s₂:Submodule K M₂)
variable [FunLike Tₘ₂ M₂ (M₂ → γ)]
  [GPseudoMetricClass Tₘ₂ M₂ γ] [AddGNorm M₂ γ gdist_m₂] [IsDelone gdist_m₂ ↑s₂]
  [StrictModuleGNorm K M₂ gdist_k gdist_m₂] [_Code γ gdist_m₂ ↑s₂]
  [_LinearCode γ K gdist_k gdist_m₂ s₂]
variable [EquivLike T₃ M M₂]
  [GIsometryClass T₃ gdist_m gdist_m₂] [CodeHomClass T₃ gdist_m (↑s) gdist_m₂ ↑s₂]
  [LinearMapClass T₃ K M M₂] [_LinearCodeHomClass T₃ K gdist_k gdist_m s gdist_m₂ s₂]

@[ext]
structure LinearCodeEquiv [_LinearCode γ K gdist_k gdist_m s]
  [_LinearCode γ K gdist_k gdist_m₂ s₂]
  extends CodeEquiv gdist_m s gdist_m₂ s₂, M ≃ₗ[K] M₂

instance LinearCodeEquiv.instEquivLike:
    EquivLike (LinearCodeEquiv K gdist_k gdist_m s gdist_m₂ s₂) M M₂ where
  coe := fun φ => φ.toFun
  inv := fun φ => φ.invFun
  left_inv := fun φ => φ.left_inv
  right_inv := fun φ => φ.right_inv
  coe_injective' := fun φ φ₂ => by
    intro h1 h2
    simp_all only
    ext x
    rw [h1]; rw [h2]

instance LinearCodeEquiv.instGIsometryClass :
    GIsometryClass (LinearCodeEquiv K gdist_k gdist_m s gdist_m₂ s₂) gdist_m gdist_m₂ where
  map_dist := fun φ => φ.map_dist

instance LinearCodeEquiv.instSemilinearEquivClass :
    SemilinearEquivClass (LinearCodeEquiv K gdist_k gdist_m s gdist_m₂ s₂) (RingHom.id K) M M₂ where
  map_add := fun φ => φ.map_add'
  map_smulₛₗ := fun φ => φ.map_smul'

instance LinearCodeEquiv.instCodeEquivClass :
    CodeEquivClass (LinearCodeEquiv K gdist_k gdist_m s gdist_m₂ s₂) gdist_m (↑s) gdist_m₂ ↑s₂ where
  map_code := fun φ => φ.map_code
  invMap_code := fun φ => φ.invMap_code

instance LinearCodeEquiv.inst_LinearCodeHomClass:
  _LinearCodeHomClass (LinearCodeEquiv K gdist_k gdist_m s gdist_m₂ s₂)
    K gdist_k gdist_m s gdist_m₂ s₂ where

class _LinearCodeEquivClass
  [_LinearCode γ K gdist_k gdist_m s]
  [_LinearCode γ K gdist_k gdist_m₂ s₂]
  [CodeEquivClass T₃ gdist_m s gdist_m₂ s₂]
  [_LinearCodeHomClass T₃ K gdist_k gdist_m s gdist_m₂ s₂]
  [LinearEquivClass T₃ K M M₂]
  where

instance LinearCodeEquiv.inst_LinearCodeEquivClass :
  _LinearCodeEquivClass (LinearCodeEquiv K gdist_k gdist_m s gdist_m₂ s₂)
    K gdist_k gdist_m s gdist_m₂ s₂ where

end linearcode
