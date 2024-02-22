import Mathlib.Topology.GMetric.Basic
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.ENNReal.Basic

variable {α :Type*}
namespace Metric
open Real

instance: FunLike (PseudoMetricSpace α) α (α → ℝ) where
  coe := fun x => x.dist
  coe_injective' := fun x y => by
    simp only
    intro h
    ext
    rw [h]

instance: FunLike (PseudoMetricSpace α) α (α → ℝ) where
  coe := fun x => x.dist
  coe_injective' := fun X Y => by
    cases X; cases Y; congr; simp; intro h; ext ;rw [h]

instance : GPseudoMetricClass (PseudoMetricSpace α) α ℝ where
  gdist_self := fun x => x.dist_self
  comm' := fun x => x.dist_comm
  triangle' := fun x => x.dist_triangle

instance: FunLike (MetricSpace α) α (α → ℝ) where
  coe := fun x => x.dist
  coe_injective' := fun X Y => by
    cases X; cases Y; congr; simp; intro h; ext; rw [h]

instance: GMetricClass (MetricSpace α) α ℝ where
  gdist_self := fun x => x.dist_self
  comm' := fun x => x.dist_comm
  triangle' := fun x => x.dist_triangle
  eq_of_dist_eq_zero := fun x => x.eq_of_dist_eq_zero

end Metric

namespace EMetricSpace
open ENNReal

instance: FunLike (PseudoEMetricSpace α) α (α → ℝ≥0∞) where
  coe := fun x => x.edist
  coe_injective' := fun X Y => by
    cases X; cases Y; congr; simp; intro h; ext; rw [h]

instance: FunLike (EMetricSpace α) α (α → ℝ≥0∞) where
  coe := fun x => x.edist
  coe_injective' := fun X Y => by
    cases X; cases Y; congr; simp; intro h; ext; rw [h]

instance: GPseudoMetricClass (PseudoEMetricSpace α) α ℝ≥0∞ where
  gdist_self := fun x => x.edist_self
  comm' := fun x => x.edist_comm
  triangle' := fun x => x.edist_triangle

instance: GMetricClass (EMetricSpace α) α ℝ≥0∞ where
  gdist_self := fun x => x.edist_self
  comm' := fun x => x.edist_comm
  triangle' := fun x => x.edist_triangle
  eq_of_dist_eq_zero := fun x => x.eq_of_edist_eq_zero
end EMetricSpace


namespace Set
open GMetric
section GinfSep
variable {β:Type*} [CompleteLinearOrder β] [AddCommMonoid β] [CovariantClass β β (.+.) (.≤.)]

variable {T:Type*} [FunLike T α (α → β)] [GPseudoMetricClass T α β]
variable (gdist:T) (s:Set α)

noncomputable def ginfsep : β :=
  ⨅ (x ∈ s) (y ∈ s) (_:x ≠ y), gdist x y

theorem le_ginfsep_iff {d} :
    d ≤ ginfsep gdist s ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ gdist x y := by
  simp_rw [ginfsep, le_iInf_iff]

lemma zero_le_ginfsep: 0 ≤ ginfsep gdist s := by
  rw [le_ginfsep_iff]; intros; exact gdist_nonneg gdist

-- theorem ginfsep_eq_iff {d}: ginfsep gdist s = d ↔ ∀ x ∈ s, ∀ y∈ s, x ≠ y → d ≤ gdist x y := sorry

theorem ginfsep_pos : 0 < ginfsep gdist s ↔ ∃ C > 0, ∀ x ∈ s, ∀ y ∈ s, x ≠ y → C ≤ gdist x y := by
  constructor
  . intro h
    use ginfsep gdist s
    use h
    rw [ginfsep]
    intro x hx y hy hneq
    rw [iInf_le_iff]
    intro d hd
    obtain hsimp := le_iInf_iff.mp (hd x) hx
    obtain hsimp := le_iInf_iff.mp hsimp y
    obtain hsimp := le_iInf_iff.mp hsimp hy
    obtain hsimp := le_iInf_iff.mp hsimp hneq
    exact hsimp
  intro ⟨c,⟨hcpos,hc⟩⟩
  suffices c ≤ ginfsep gdist s by exact gt_of_ge_of_gt this hcpos
  rw [ginfsep, le_iInf_iff]
  intro x
  rw [le_iInf_iff]
  intro hx
  rw [le_iInf_iff]
  intro y
  rw [le_iInf_iff]
  intro hy
  rw [le_iInf_iff]
  intro hneq
  exact hc x hx y hy hneq

end GinfSep
