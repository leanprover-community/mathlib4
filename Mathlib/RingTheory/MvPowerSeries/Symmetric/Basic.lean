import Mathlib.Tactic.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Degree
import Mathlib.RingTheory.MvPowerSeries.Rename

open Equiv (Perm)

variable {σ : Type*} {R : Type*} [CommSemiring R] [DecidableEq σ]

namespace MvPowerSeries

/-- A `MvPowerSeries φ` is symmetric if it is invariant under
permutations of its variables by the `rename` operation -/
def IsSymmetric (φ : MvPowerSeries σ R) : Prop :=
  ∀ e : Perm σ, rename e φ = φ

variable (σ R)

/-- The subalgebra of symmetric `MvPowerSeries`s. -/
def symmetricSubalgebra : Subalgebra R (MvPowerSeries σ R) where
  carrier := setOf IsSymmetric
  algebraMap_mem' r e := rename_C e r
  mul_mem' ha hb e := by simp only [map_mul, ha e, hb e]
  add_mem' ha hb e := by simp only [map_add, ha e, hb e]

/-- The algebra of symmetric functions. -/
def SymmetricFunction : Subalgebra R (MvPowerSeries σ R) where
  carrier := (symmetricSubalgebra σ R ⊓ boundedDegreeSubalgebra σ R)
  algebraMap_mem' r := by
    constructor
    · apply Subalgebra.algebraMap_mem
    · apply Subalgebra.algebraMap_mem
  mul_mem' := by
    intros a b ha hb
    constructor
    · apply Subalgebra.mul_mem
      · exact ha.1
      · exact hb.1
    · apply Subalgebra.mul_mem
      · exact ha.2
      · exact hb.2
  add_mem' := by
    intros a b ha hb
    constructor
    · apply Subalgebra.add_mem
      · exact ha.1
      · exact hb.1
    · apply Subalgebra.add_mem
      · exact ha.2
      · exact hb.2

end MvPowerSeries
