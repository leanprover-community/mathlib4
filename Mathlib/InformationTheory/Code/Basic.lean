import Mathlib.Topology.GMetric.WellSpaced
import Mathlib.Topology.GMetric.Isometry

namespace Code
open Set
open GMetric
variable {α γ :Type*} [CompleteLinearOrder γ] [AddCommMonoid γ] [CovariantClass γ γ (. + .) (. ≤ .)]


variable {T:Type*} [FunLike T α (α → γ)] [GMetricClass T α γ] {gdist:T}
variable {s:Set α}

class IsDecodingMap {r:γ} (hUDis:UniformlyDiscreteWith gdist s r) (decode : α → α) : Prop :=
  image_eq_s : decode '' univ ⊆ s
  image_ball_eq_cw : ∀ cw ∈ s, decode '' (ball gdist cw r) ⊆ {cw}
