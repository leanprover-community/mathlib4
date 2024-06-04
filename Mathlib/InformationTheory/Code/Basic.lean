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

instance inst_Code [GPseudoMetricClass T α γ] [IsDelone gdist s]: _Code γ gdist s where

end code
