import Mathlib.Topology.GMetric.WellSpaced
import Mathlib.Topology.GMetric.GNorm
import Mathlib.Topology.GMetric.Isometry

namespace Code
open Set
open GMetric
section code

variable {γ :Type*} [CompleteLinearOrder γ] [AddCommMonoid γ] [CovariantClass γ γ (. + .) (. ≤ .)]
variable {α :Type*} {T:Type*} [FunLike T α (α → γ)] [GPseudoMetricClass T α γ] {gdist:T}
variable {s:Set α}

class IsDecodingMap {r:γ} (hUDis:UniformlyDiscreteWith gdist s r) (decode : α → α) : Prop :=
  image_eq_s : decode '' univ ⊆ s
  image_ball_eq_cw : ∀ cw ∈ s, decode '' (ball gdist cw r) ⊆ {cw}

variable (γ) (gdist) (s)
-- @[abbrev_class]
class _Code [GPseudoMetricClass T α γ] [IsDelone gdist s] : Prop
  where

instance Code.inst_Code [GPseudoMetricClass T α γ] [IsDelone gdist s]: _Code γ gdist s where

end code


section linearcode

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

instance Code.inst_LinearCode [Nontrivial γ][ContravariantClass γ γ (.+.) (.<.)]
  [PosMulMono γ] [MulPosMono γ] [ZeroLEOneClass γ]
  [StrictModuleGNorm K K gdist_k gdist_k] [StrictModuleGNorm K M gdist_k gdist_m]
  [_Code γ gdist_m s] : _LinearCode γ K gdist_k gdist_m s where

end linearcode
