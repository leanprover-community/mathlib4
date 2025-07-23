import Mathlib.Analysis.Normed.Lp.PiLp

open WithLp

open scoped ENNReal Uniformity

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] {α β : Type*} [SeminormedAddCommGroup α]
    [SeminormedAddCommGroup β]

def WithLp.addEquiv {α : Type*} [AddCommGroup α] : α ≃+ (WithLp p α) where
  toFun := toLp p
  invFun := ofLp
  map_add' := toLp_add p

private noncomputable def aux : SeminormedAddCommGroup (α × β) :=
  SeminormedAddCommGroup.induced (α × β) (WithLp p (α × β)) (WithLp.addEquiv p)

attribute [local instance] aux in
lemma test : 𝓤 (α × β) = 𝓤[(aux p).toPseudoMetricSpace.toUniformSpace] := by


example (p : ℝ≥0∞) [Fact (1 ≤ p)] {α β : Type*} [SeminormedAddCommGroup α]
    [SeminormedAddCommGroup β] : SeminormedAddCommGroup (α × β) :=
