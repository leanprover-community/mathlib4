import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.Regular.Depth

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
