import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.Regular.Depth

namespace CategoryTheory

universe w v u

open Abelian Limits ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {X : C} {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₂]
  (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (h0 : n₀ ≠ 0)

def dim_shifting (n : ℕ) : Ext X S.X₃ n₀ ≃ Ext X S.X₁ n₁ := by sorry

end CategoryTheory

universe v u

open IsLocalRing
open RingTheory.Sequence Ideal CategoryTheory CategoryTheory.Abelian

variable {R : Type u} [CommRing R] [Small.{v} R]

open scoped Classical in
theorem AuslanderBuchsbaum [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) [Nontrivial M] [Module.Finite R M]
    [Small.{v} (R ⧸ (IsLocalRing.maximalIdeal R))]
    (h : ∃ i : ℕ, CategoryTheory.HasProjectiveDimensionLE M i) :
    Nat.find h + IsLocalRing.depth M = IsLocalRing.depth (ModuleCat.of R R) := by sorry
