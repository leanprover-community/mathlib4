import Mathlib.Topology.GMetric.GInfSep

namespace Set

variable {α γ :Type*} [CompleteLinearOrder γ] [AddCommMonoid γ] [CovariantClass γ γ (. + .) (. ≤ .)]
variable (gdist : α → α → γ)

namespace WellSpaced

section discrete
def WeakDiscreteGDistWith (d:γ) :Prop := ∀ x y, x ≠ y → d ≤ gdist x y

def WeakDiscreteGDist : Prop := ∃ d:γ, WeakDiscreteGDistWith gdist d

def DiscreteGDistWith (d:γ) : Prop := ∀ x y, x ≠ y → d < gdist x y

def DiscreteGDist : Prop := ∃ d:γ, DiscreteGDistWith gdist d
end discrete

section bounded
def WeakBoundedGDistWith (d:γ):Prop := ∀ x y, gdist x y ≤ d

def WeakBoundedGDist :Prop := ∃ d, WeakBoundedGDistWith gdist d

def BoundedGDistWith (d:γ):Prop := ∀ x y, gdist x y < d

def BoundedGDist : Prop := ∃ d, BoundedGDistWith gdist d

end bounded

variable {T:Type} [FunLike T α (α → γ)] (gdist:T) (s:Set α)
section packing

open GMetric Set

def IsWeakPackingWith (d:γ) : Prop := s.PairwiseDisjoint (ball gdist . d)

def IsPackingWith (d:γ) : Prop := s.PairwiseDisjoint (closedBall gdist . d)

-- do i rather want `⨅ (d:γ) (_:IsPackingWith gdist s d), d`?
def packing_radius : γ := ⨆ (x ∈ s) (y:α) (_ : IsPackingWith gdist s (gdist (x:α) y)), gdist (x:α) y

end packing



end WellSpaced

end Set
