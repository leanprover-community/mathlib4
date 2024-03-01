import Mathlib.InformationTheory.Code.Basic
import Mathlib.Topology.GMetric.Isometry
import Mathlib.Topology.GMetric.GNorm


namespace Code

open Set
open GMetric
open GIsometry

section code
variable (T₃:Type*)
variable {γ :Type*} [CompleteLinearOrder γ] [AddCommMonoid γ]

variable {α T:Type*} (gdist:T) (s:Set α)
variable [FunLike T α (α → γ)]
  [CovariantClass γ γ (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1] [GPseudoMetricClass T α γ]
  [IsDelone gdist s] [_Code γ gdist s]

variable {α₂ T₂ :Type*} (gdist₂:T₂) (s₂ : Set α₂)
variable? [_Code γ gdist₂ s₂] => [FunLike T₂ α₂ (α₂ → γ)] [GPseudoMetricClass T₂ α₂ γ]
  [IsDelone gdist₂ s₂] [_Code γ gdist₂ s₂]

variable [FunLike T₃ α α₂] [GIsometryClass T₃ gdist gdist₂]

@[ext]
structure CodeHom [_Code γ gdist s] [_Code γ gdist₂ s₂] extends GIsometry gdist gdist₂ where
  map_code : toGIsometry '' s ⊆ s₂

instance CodeHom.instFunLike : FunLike (CodeHom gdist s gdist₂ s₂) α α₂ where
  coe := fun φ => φ.toGIsometry
  coe_injective' := fun φ₁ φ₂ h => by
    ext y
    simp at h
    rw [h]

instance CodeHom.instGIsometryClass : GIsometryClass (CodeHom gdist s gdist₂ s₂) gdist gdist₂ where
  map_dist := fun φ => φ.map_dist

class CodeHomClass [_Code γ gdist s] [_Code γ gdist₂ s₂]
    [GIsometryClass T₃ gdist gdist₂] :Prop where
  map_code : ∀ (φ:T₃), φ '' s ⊆ s₂

instance CodeHom.instCodeHomClass : CodeHomClass (CodeHom gdist s gdist₂ s₂) gdist s gdist₂ s₂ where
  map_code := fun φ => φ.map_code
end code

section linear_code
variable (T₃:Type*)

variable {γ : Type*} [Semiring γ] [CompleteLinearOrder γ] [Nontrivial γ]
set_option variable?.maxSteps 20
variable (K : Type*) [Field K] {Tₖ : Type*} (gdist_k:Tₖ)
variable {M : Type*} {Tₘ : Type*} (gdist_m:Tₘ) [AddCommMonoid M] [Module K M]
variable (s : Submodule K M)
variable
  [CovariantClass γ γ (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1] [FunLike Tₖ K (K → γ)]
  [GPseudoMetricClass Tₖ K γ] [AddGNorm K γ gdist_k] [FunLike Tₘ M (M → γ)]
  [GPseudoMetricClass Tₘ M γ] [AddGNorm M γ gdist_m] [IsDelone gdist_m ↑s]
  [ContravariantClass γ γ (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1] [PosMulStrictMono γ]
  [MulPosStrictMono γ] [ZeroLEOneClass γ] [StrictModuleGNorm K K gdist_k gdist_k]
  [StrictModuleGNorm K M gdist_k gdist_m] [_Code γ gdist_m ↑s] [_LinearCode γ K gdist_k gdist_m s]
variable {M₂ : Type*} {Tₘ₂ : Type*} (gdist_m₂:Tₘ₂) [AddCommMonoid M₂] [Module K M₂]
variable (s₂ : Submodule K M₂)
variable [FunLike Tₘ₂ M₂ (M₂ → γ)]
  [GPseudoMetricClass Tₘ₂ M₂ γ] [AddGNorm M₂ γ gdist_m₂] [IsDelone gdist_m₂ ↑s₂]
  [StrictModuleGNorm K M₂ gdist_k gdist_m₂] [_Code γ gdist_m₂ ↑s₂]
  [_LinearCode γ K gdist_k gdist_m₂ s₂]
variable [FunLike T₃ M M₂]
  [GIsometryClass T₃ gdist_m gdist_m₂] [CodeHomClass T₃ gdist_m s gdist_m₂ s₂]


@[ext]
structure LinearCodeHom [_LinearCode γ K gdist_k gdist_m s]
  [_LinearCode γ K gdist_k gdist_m₂ s₂]
  extends CodeHom gdist_m s gdist_m₂ s₂, M →ₗ[K] M₂

instance LinearCodeHom.instFunLike :
    FunLike (LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) M M₂ where
  coe := fun φ => φ.toFun
  coe_injective' := fun φ₁ φ₂ h => by
    ext z
    simp at h
    rw [h]

instance LinearCodeHom.instSemiLinearMapClass :
    LinearMapClass (LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) K M M₂ where
  map_add := fun φ => φ.toLinearMap.map_add
  map_smulₛₗ := fun φ => φ.toLinearMap.map_smulₛₗ

instance LinearCodeHom.instGIsometryClass :
    GIsometryClass (LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) gdist_m gdist_m₂ where
  map_dist := fun φ => φ.toCodeHom.map_dist

instance LinearCodeHom.instCodeHomClass :
    CodeHomClass (LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) gdist_m s gdist_m₂ s₂ where
  map_code := fun φ => φ.toCodeHom.map_code

/-- this class doesn't really do anything
there is no extra info needed on top of the parameters,
but it does help remind you what instances you need in order to have the property
this represents.
it also allows `variable? [LinearCodeHomClass T₃ K gdist_k gdist_m s gdist_m₂ s₂]` to
expand into all the right variables
-/
class _LinearCodeHomClass
    [_LinearCode γ K gdist_k gdist_m s]
    [_LinearCode γ K gdist_k gdist_m₂ s₂]
    [CodeHomClass T₃ gdist_m s gdist_m₂ s₂]
    [LinearMapClass T₃ K M M₂] : Prop
    where

instance LinearCodeHom.inst_LinearCodeHomClass :
  _LinearCodeHomClass (LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂)
  K gdist_k gdist_m s gdist_m₂ s₂ where

end linear_code
