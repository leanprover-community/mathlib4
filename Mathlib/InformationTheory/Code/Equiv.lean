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
variable--? [_Code γ gdist s] =>
  [CovariantClass γ γ (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
  [FunLike T α (α → γ)] [GPseudoMetricClass T α γ] [IsDelone gdist s]
variable {α₂ T₂ :Type*} (gdist₂:T₂)(s₂ : Set α₂)
variable--? [_Code γ gdist₂ s₂] =>
  [FunLike T₂ α₂ (α₂ → γ)] [GPseudoMetricClass T₂ α₂ γ]
  [IsDelone gdist₂ s₂]

structure CodeEquiv [_Code γ gdist s] [_Code γ gdist₂ s₂] extends α ≃ α₂, CodeHom gdist s gdist₂ s₂ where
  invMap_code : ∀ y ∈ s₂, invFun y ∈ s

instance CodeEquiv.instEquivLike : EquivLike (CodeEquiv gdist s gdist₂ s₂) α α₂ := {
  coe := fun φ => φ.toFun
  inv := fun φ => φ.invFun
  left_inv := fun φ => φ.left_inv
  right_inv := fun φ => φ.right_inv
  coe_injective' := fun φ₁ φ₂ h=> by
    cases φ₁; cases φ₂; --aesop?
    intro
    simp_all only [Equiv.toFun_as_coe, DFunLike.coe_fn_eq, Equiv.invFun_as_coe]
}

@[ext]
lemma CodeEquiv.ext
    (φ:CodeEquiv gdist s gdist₂ s₂)
    (φ₂:CodeEquiv gdist s gdist₂ s₂)
    (h:∀ x, φ x = φ₂ x) : φ = φ₂ := by
  apply DFunLike.ext _ _ h


instance CodeEquiv.instGIsometryClass : GIsometryClass (CodeEquiv gdist s gdist₂ s₂) gdist gdist₂ where
  map_dist := fun φ => φ.map_dist



section
variable {gdist₂ s₂} {T₃ α₃:Type*} {gdist₃:T₃} {s₃:Set α₃}
variable--? [_Code γ gdist₃ s₃] =>
  [FunLike T₃ α₃ (α₃ → γ)] [GPseudoMetricClass T₃ α₃ γ] [IsDelone gdist₃ s₃]

def CodeEquiv.refl : CodeEquiv gdist s gdist s :=
  {Equiv.refl _, CodeHom.id gdist s with
  invMap_code :=  fun _ hy ↦ hy}

variable {gdist s}

@[symm]
def CodeEquiv.symm (φ:CodeEquiv gdist s gdist₂ s₂) : CodeEquiv gdist₂ s₂ gdist s := {
  φ.toEquiv.symm with
  map_dist := fun x y => by
    rw [φ.map_dist]
    nth_rw 1 [← φ.right_inv x,← φ.right_inv y]
    simp only [Equiv.invFun_as_coe, Equiv.toFun_as_coe, Equiv.apply_symm_apply]
  map_code := φ.invMap_code
  invMap_code := φ.map_code}

@[trans]
def CodeEquiv.trans
    (φ:CodeEquiv gdist s gdist₂ s₂) (φ₂:CodeEquiv gdist₂ s₂ gdist₃ s₃) :
    CodeEquiv gdist s gdist₃ s₃ := {
  φ₂.toCodeHom.comp φ.toCodeHom,φ.toEquiv.trans φ₂.toEquiv with
  invMap_code := by simp only; apply ((φ.symm).toCodeHom.comp (φ₂.symm).toCodeHom).map_code}
end

variable [EquivLike T₃ α α₂]
  [GIsometryClass T₃ gdist gdist₂]

class CodeEquivClass
    [_Code γ gdist s]
    [_Code γ gdist₂ s₂] [EquivLike T₃ α α₂] [GIsometryClass T₃ gdist gdist₂]
    extends CodeHomClass T₃ gdist s gdist₂ s₂ :Prop where
  invMap_code : ∀ (φ:T₃), ∀ y∈ s₂, Equiv.invFun φ y ∈ s

instance CodeEquiv.instCodeEquivClass:
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
variable--? [_LinearCode γ K gdist_k gdist_m s] =>
  [CovariantClass γ γ (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1] [FunLike Tₖ K (K → γ)]
  [GPseudoMetricClass Tₖ K γ] [AddGNorm K γ gdist_k] [FunLike Tₘ M (M → γ)]
  [GPseudoMetricClass Tₘ M γ] [AddGNorm M γ gdist_m] [IsDelone gdist_m ↑s] [Nontrivial γ]
  [PosMulMono γ] [MulPosMono γ] [ZeroLEOneClass γ]
  [StrictModuleGNorm K K gdist_k gdist_k] [StrictModuleGNorm K M gdist_k gdist_m]
variable (gdist_m₂ : Tₘ₂) (s₂:Submodule K M₂)
variable--? [_LinearCode γ K gdist_k gdist_m₂ s₂] =>
  [FunLike Tₘ₂ M₂ (M₂ → γ)] [GPseudoMetricClass Tₘ₂ M₂ γ] [AddGNorm M₂ γ gdist_m₂]
  [IsDelone gdist_m₂ ↑s₂] [StrictModuleGNorm K M₂ gdist_k gdist_m₂]
variable--? [_LinearCodeHomClass T₃ K gdist_k gdist_m s gdist_m₂ s₂] =>
  [EquivLike T₃ M M₂] [GIsometryClass T₃ gdist_m gdist_m₂]
  [CodeHomClass T₃ gdist_m (↑s) gdist_m₂ ↑s₂] [LinearMapClass T₃ K M M₂]

@[ext]
structure LinearCodeEquiv [_LinearCode γ K gdist_k gdist_m s]
  [_LinearCode γ K gdist_k gdist_m₂ s₂]
  extends CodeEquiv gdist_m s gdist_m₂ s₂, LinearEquiv (RingHom.id K) M M₂

instance LinearCodeEquiv.toLinearCodeHom (φ : LinearCodeEquiv K gdist_k gdist_m s gdist_m₂ s₂) :LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂ := {
  φ with
}

instance LinearCodeEquiv.instEquivLike:
    EquivLike (LinearCodeEquiv K gdist_k gdist_m s gdist_m₂ s₂) M M₂ where
  coe := fun φ => φ.toFun
  inv := fun φ => φ.invFun
  left_inv := fun φ => φ.left_inv
  right_inv := fun φ => φ.right_inv
  coe_injective' := fun φ φ₂ h1 h2=> by
    unhygienic cases φ;unhygienic cases φ₂; congr; simp_all
    cases toCodeEquiv; cases toCodeEquiv_1; congr


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


section
variable {Tₘ₃ M₃:Type*} {gdist_m₃:Tₘ₃} [AddCommMonoid M₃] [Module K M₃] {s₃:Submodule K M₃}
variable--? [_LinearCode γ K gdist_k gdist_m₃ s₃] =>
  [FunLike Tₘ₃ M₃ (M₃ → γ)] [GPseudoMetricClass Tₘ₃ M₃ γ] [AddGNorm M₃ γ gdist_m₃]
  [IsDelone gdist_m₃ ↑s₃] [StrictModuleGNorm K M₃ gdist_k gdist_m₃]

def LinearCodeEquiv.refl
    [_LinearCode γ K gdist_k gdist_m s] : LinearCodeEquiv K gdist_k gdist_m s gdist_m s := {
  LinearEquiv.refl K M, CodeEquiv.refl gdist_m s with
  -- for some reason, reversing the order breaks this
}
variable {gdist_m s gdist_m₂ s₂}
def LinearCodeEquiv.symm
    (φ:LinearCodeEquiv K gdist_k gdist_m s gdist_m₂ s₂):
    LinearCodeEquiv K gdist_k gdist_m₂ s₂ gdist_m s := {
  φ.toLinearEquiv.symm,φ.toCodeEquiv.symm with}

def LinearCodeEquiv.trans
    (φ:LinearCodeEquiv K gdist_k gdist_m s gdist_m₂ s₂)
    (φ₂:LinearCodeEquiv K gdist_k gdist_m₂ s₂ gdist_m₃ s₃):
    LinearCodeEquiv K gdist_k gdist_m s gdist_m₃ s₃ := {
  φ.toLinearEquiv.trans φ₂.toLinearEquiv,φ.toCodeEquiv.trans φ₂.toCodeEquiv with}
end

-- @[abbrev_class].
class _LinearCodeEquivClass
  [CodeEquivClass T₃ gdist_m s gdist_m₂ s₂]
  [LinearEquivClass T₃ K M M₂]
  [_LinearCodeHomClass T₃ K gdist_k gdist_m s gdist_m₂ s₂] :Prop
  where

instance inst_LinearCodeEquivClass [CodeEquivClass T₃ gdist_m s gdist_m₂ s₂]
  [_LinearCodeHomClass T₃ K gdist_k gdist_m s gdist_m₂ s₂]
  [LinearEquivClass T₃ K M M₂]:
  _LinearCodeEquivClass T₃ K gdist_k gdist_m s gdist_m₂ s₂ where

end linearcode
