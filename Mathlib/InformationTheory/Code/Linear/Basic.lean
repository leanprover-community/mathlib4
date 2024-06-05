import Mathlib.InformationTheory.Code.Basic
import Mathlib.Algebra.Module.Submodule.Basic

open Code Set GMetric

variable (γ :Type*) [CompleteLinearOrder γ] [Semiring γ] [CovariantClass γ γ (. + .) (. ≤ .)]
  [Nontrivial γ] [ContravariantClass γ γ (.+.) (.<.)] [PosMulMono γ] [MulPosMono γ]
  [ZeroLEOneClass γ]
variable (K : Type*) [Field K] {Tₖ : Type*} (gdist_k:Tₖ)
variable {M : Type*} {Tₘ : Type*} (gdist_m:Tₘ)
variable--? [AddGNorm K γ gdist_k] [StrictModuleGNorm K K gdist_k gdist_k] =>
  [FunLike Tₖ K (K → γ)]
  [GPseudoMetricClass Tₖ K γ] [AddGNorm K γ gdist_k] [StrictModuleGNorm K K gdist_k gdist_k]
variable--? [StrictModuleGNorm K M gdist_k gdist_m] =>
  [FunLike Tₘ M (M → γ)] [GPseudoMetricClass Tₘ M γ] [AddCommMonoid M] [Module K M]
  [AddGNorm M γ gdist_m] [StrictModuleGNorm K M gdist_k gdist_m]
variable (s : Submodule K M) [IsDelone gdist_m s]

-- @[abbrev_class]
class _LinearCode [Nontrivial γ] [ContravariantClass γ γ (.+.) (.<.)]
  [PosMulMono γ] [MulPosMono γ] [ZeroLEOneClass γ]
  [StrictModuleGNorm K K gdist_k gdist_k]
  [StrictModuleGNorm K M gdist_k gdist_m] [_Code γ gdist_m s] : Prop where

namespace LinearCode
instance inst_LinearCode [Nontrivial γ][ContravariantClass γ γ (.+.) (.<.)]
  [PosMulMono γ] [MulPosMono γ] [ZeroLEOneClass γ]
  [StrictModuleGNorm K K gdist_k gdist_k] [StrictModuleGNorm K M gdist_k gdist_m]
  [_Code γ gdist_m s] : _LinearCode γ K gdist_k gdist_m s where
