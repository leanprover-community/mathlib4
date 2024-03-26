import Mathlib.Topology.GMetric.Basic
import Mathlib.Algebra.Module.Basic


variable {α:Type*}
variable {γ:Type*} [AddCommMonoid γ] [LinearOrder γ]
variable [CovariantClass γ γ (.+.) (.≤.)]
variable {T:Type*} [FunLike T α (α → γ)] [GPseudoMetricClass T α γ]

section multiplicative
section monoid
variable [Monoid α]


-- adding a constant is an isometry
-- i'm not sure if you can specify this explicitly some way, with the isometry structure i defined...
-- but it can probably be a conclusion/instance/something
class GNorm (α : Type*) (γ : Type*) [AddCommMonoid γ] [LinearOrder γ]
  [CovariantClass γ γ (. + .) (. ≤ .)] {T : Type*} [FunLike T α (α → γ)] [GPseudoMetricClass T α γ]
  [Monoid α] (gdist:T) : Prop where
  gdist_absorb_mul : ∀ z x y, (gdist (x*z) (y*z)) = gdist x y

def gnorm (gdist:T) [GNorm α γ gdist] (x :α) :γ := gdist x 1

lemma gdist_absorb_mul
    (gdist:T) [h:GNorm α γ gdist] : ∀ z x y, (gdist (x*z) (y*z)) = gdist x y := by
  exact h.gdist_absorb_mul
end monoid

section group
lemma dist_eq [Group α] (gdist:T) [GNorm α γ gdist] :
    ∀ x y, gdist x y = gnorm gdist (x / y):= by
  intro x y
  rw [gnorm]
  nth_rw 2 [← gdist_absorb_mul gdist y]
  simp only [one_mul, div_mul_cancel']

end group
end multiplicative

section additive
section addmonoid
variable [AddMonoid α]

class AddGNorm (α : Type*) (γ : Type*) [AddCommMonoid γ] [LinearOrder γ] [CovariantClass γ γ (. + .) (. ≤ .)]
  {T : Type*} [FunLike T α (α → γ)] [GPseudoMetricClass T α γ] [AddMonoid α] (gdist:T) :Prop where
  gdist_absorb_add : ∀ z x y, (gdist (x+z) (y+z)) = gdist x y

lemma gdist_absorb_add
    (gdist:T) [h:AddGNorm α γ gdist] : ∀ z x y, (gdist (x+z) (y+z)) = gdist x y:= by
  exact h.gdist_absorb_add

def addGNorm (gdist:T) [AddGNorm α γ gdist] (x:α) : γ :=
  gdist x 0
end addmonoid

section addcommgroup
variable [AddGroup α]

lemma addDist_eq (gdist:T) [AddGNorm α γ gdist] :
    ∀ x y, gdist x y = addGNorm gdist (x - y):= by
  intro x y
  rw [addGNorm]
  nth_rw 2 [← gdist_absorb_add gdist y]
  simp only [zero_add, sub_add_cancel]

end addcommgroup

section module
variable {K M:Type*}
variable {Δ:Type*} [Semiring Δ] [CompleteLinearOrder Δ]
variable [CovariantClass Δ Δ (.+.) (.≤.)] [PosMulMono Δ] [MulPosMono Δ] [ZeroLEOneClass Δ]

variable {Tₖ:Type*} [FunLike Tₖ K (K → Δ)] [GPseudoMetricClass Tₖ K Δ]
variable {Tₘ:Type*} [FunLike Tₘ M (M → Δ)] [GPseudoMetricClass Tₘ M Δ]
class GBoundSMul [Zero K] [Zero M] [SMul K M] (gdist_k:Tₖ) (gdist_m:Tₘ) where
  dist_smul_pair' :
    ∀ (x : K) (y₁ y₂ : M), gdist_m (x • y₁) (x • y₂) ≤ gdist_k x 0 * gdist_m y₁ y₂
  dist_pair_smul' :
    ∀ (x₁ x₂ : K) (y : M), gdist_m (x₁ • y) (x₂ • y) ≤ gdist_k x₁ x₂ * gdist_m y 0
variable [Semiring K] [AddCommMonoid M] [Module K M]
variable (gdist_k:Tₖ) [AddGNorm K Δ gdist_k] (gdist_m:Tₘ) [AddGNorm M Δ gdist_m]
variable (K M)
-- this is a mixin version of NormedSpace
class ModuleGNorm :Prop where
  norm_smul_le' : ∀ (a : K) (b : M),
    addGNorm gdist_m (a • b) ≤ addGNorm gdist_k a * addGNorm gdist_m b


class StrictModuleGNorm extends ModuleGNorm K M gdist_k gdist_m where
  smul_norm_le' :
    ∀ (a:K) (b:M), addGNorm gdist_k a * addGNorm gdist_m b ≤ addGNorm gdist_m (a • b)

lemma smul_norm [StrictModuleGNorm K M gdist_k gdist_m] :
    ∀ (a:K) (b:M), addGNorm gdist_m (a • b) = addGNorm gdist_k a * addGNorm gdist_m b := by
  intro a b
  apply le_antisymm
  exact ModuleGNorm.norm_smul_le' a b
  exact StrictModuleGNorm.smul_norm_le' a b



end module

end additive
