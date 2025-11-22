import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Data.Finsupp.Sigma
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.Algebra.Order.Ring.Defs

universe u v

noncomputable section

open Classical

structure FiniteProbability (R : Type u) [LE R] [AddCommMonoid R] [One R] (ι : Type v)
    extends weights : ι →₀ R where
  nonneg : ∀ m, 0 ≤ weights m
  total : weights.sum (fun _ r => r) = 1

namespace FiniteProbability

variable {R : Type u} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
  {κ : Type v} {ι : κ → Type v}

open Classical in
def single {ι : Type v} (i : ι) : FiniteProbability R ι where
  weights := Finsupp.single i 1
  nonneg m := by
    rw [Finsupp.single_apply]
    split
    · exact zero_le_one' R
    · grind
  total := by simp

def comp (f : FiniteProbability R κ) (g : (k : κ) → FiniteProbability R (ι k)) :
    FiniteProbability R (Σ k, ι k) where
  weights := f.sum (fun m r => (r • (g m).weights).embSigma)
  nonneg := by
    intro ⟨k, i⟩
    sorry
  total := by
    sorry

end FiniteProbability

class ConvexSpace (R : Type u) (M : Type v)
    [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] where
  convexCombination {ι : Type v} (f : FiniteProbability R ι) (xs : ι → M) : M
  /-- Associativity of convex combination. -/
  assoc
    {κ : Type v} (f₀ : FiniteProbability R κ)
    {ι : κ → Type v} (f₁ : (k : κ) → FiniteProbability R (ι k))
    (xs : (k : κ) → (ι k) → M) :
    convexCombination f₀ (fun m => convexCombination (f₁ m) (xs m)) =
      convexCombination (f₀.comp f₁) (fun ⟨k, i⟩ => xs k i)
  /-- A convex combination of a single point is that point. -/
  single {ι : Type v} (i : ι) (x : M) : convexCombination (.single i) (fun _ => x) = x
  /-- Convex combinations are determined by the points with non-zero weights. -/
  -- Perhaps this follows from `assoc`, but I don't see how.
  ext {ι : Type v} (f : FiniteProbability R ι) (xs xs' : ι → M)
    (h : ∀ i, i ∈ f.support → xs i = xs' i) : convexCombination f xs = convexCombination f xs'
