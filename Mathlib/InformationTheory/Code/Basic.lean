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
class _Code [GPseudoMetricClass T α γ] [IsDelone gdist s] : Prop
  where
-- use: [_Code γ gdist s]
end code


section linearcode

variable (γ :Type*) [CompleteLinearOrder γ] [Semiring γ] [CovariantClass γ γ (. + .) (. ≤ .)]
  [Nontrivial γ] [ContravariantClass γ γ (.+.) (.<.)] [PosMulMono γ] [MulPosMono γ]
  [ZeroLEOneClass γ]
variable (K : Type*) [Field K] {Tₖ : Type*} (gdist_k:Tₖ)
variable {M : Type*} {Tₘ : Type*} (gdist_m:Tₘ)
variable? [AddGNorm K γ gdist_k] [StrictModuleGNorm K K gdist_k gdist_k] -- [NormedField K]
variable? [StrictModuleGNorm K M gdist_k gdist_m] -- [NormedSpace K M]
variable (s : Submodule K M) [IsDelone gdist_m s]

class _LinearCode [Nontrivial γ] [ContravariantClass γ γ (.+.) (.<.)]
  [PosMulMono γ] [MulPosMono γ] [ZeroLEOneClass γ]
  [StrictModuleGNorm K K gdist_k gdist_k] [StrictModuleGNorm K M gdist_k gdist_m] [_Code γ gdist_m s]
end linearcode
