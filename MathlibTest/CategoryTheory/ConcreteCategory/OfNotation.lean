module
-- The delaborator tests below define public `meta` declarations mentioning `Delab` and
-- `CategoryTheory.delabOf`, so both must be publicly imported.
public import Lean.PrettyPrinter.Delaborator.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.CoalgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.Order.Category.BddOrd
import Mathlib.Order.Category.BoolAlg
import Mathlib.Order.Category.Lat
import Mathlib.Order.Category.OmegaCompletePartialOrder
import Mathlib.Order.Category.Semilat
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.Stonean.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCommRingCat

open CategoryTheory

/-! ### Categories whose `of` is the structure constructor -/

example : CommRingCat := ↧ℤ
example : RingCat := ↧ℤ
example : SemiRingCat := ↧ℕ
example : CommSemiRingCat := ↧ℕ
example : TopCat := ↧ℕ
example : Lat := ↧ℕ
example : BoolAlg := ↧Prop

/-! ### Categories whose `of` is a def -/

example : GrpCat := ↧(Multiplicative ℤ)
example : CommGrpCat := ↧(Multiplicative ℤ)
example : MonCat := ↧ℕ
example (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] : CompHaus := ↧X
example (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [ExtremallyDisconnected X] :
    Stonean := ↧X

-- `Profinite` is reducibly `CompHausLike _`, but has its own `Profinite.of`.
example (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] :
    (↧X : Profinite) = Profinite.of X := rfl

/-! ### Parameterised categories

The parameters are recovered from the expected type.
-/

example : ModuleCat ℤ := ↧ℤ
example (R : Type) [Ring R] (M : Type) [AddCommGroup M] [Module R M] : ModuleCat R := ↧M
example (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] : CommAlgCat R := ↧A
example (R : Type) [CommRing R] (A : Type) [Ring A] [Algebra R A] : AlgCat R := ↧A
example (R : Type) [Ring R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    FGModuleCat R := ↧M
example (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Coalgebra R M] :
    CoalgCat R := ↧M

/-! ### Universes -/

example : CommRingCat.{7} := ↧(ULift.{7} ℤ)
example (R : Type) [Ring R] (M : Type 5) [AddCommGroup M] [Module R M] : ModuleCat.{5} R := ↧M

/-! ### `↧X` is syntactically `C.of X` -/

example : (↧ℤ : CommRingCat) = CommRingCat.of ℤ := rfl
example : (↧ℤ : ModuleCat ℤ) = ModuleCat.of ℤ ℤ := rfl

-- `rw` needs the term to match `C.of` syntactically.
example : ((↧ℤ : CommRingCat) : Type) = ℤ := by rw [CommRingCat.coe_of]

/-! ### The expected type may only be known after postponement -/

example : ModuleCat ℤ := id ↧ℤ
example (f : CommRingCat ⥤ TopCat) : TopCat := f.obj ↧ℤ
example : (↧ℤ : CommRingCat) ⟶ ↧ℤ := CommRingCat.ofHom (RingHom.id _)

/-! ### Error messages -/

/-- error: `↧` failed: no bundling map found for the expected type
  ℕ
Expected a type whose head constant `FooCat` has an associated declaration `FooCat.of`. -/
#guard_msgs in
example : ℕ := ↧ℤ

/-- error: `↧` failed: the expected type must be known, but it is
  ?m.1 -/
#guard_msgs in
example := ↧ℤ

/-! ### Delaborator

`CategoryTheory.delabOf` is opt-in per category: a category prints via `↧` iff it registers
`@[app_delab C.of] ... := CategoryTheory.delabOf`. The categories below opt in in Mathlib itself,
so `C.of X` prints as `↧X`.
-/

section Delab

universe u

variable (R : Type u)

variable [Semiring R] in
/-- info: ↧R : SemiRingCat -/
#guard_msgs in #check SemiRingCat.of R

variable [CommSemiring R] in
/-- info: ↧R : CommSemiRingCat -/
#guard_msgs in #check CommSemiRingCat.of R

variable [Ring R] in
/-- info: ↧R : RingCat -/
#guard_msgs in #check RingCat.of R

variable [CommRing R] in
/-- info: ↧R : CommRingCat -/
#guard_msgs in #check CommRingCat.of R

variable [TopologicalSpace R] in
/-- info: ↧R : TopCat -/
#guard_msgs in #check TopCat.of R

variable [TopologicalSpace R] [CommRing R] [IsTopologicalRing R] in
/-- info: ↧R : TopCommRingCat -/
#guard_msgs in #check TopCommRingCat.of R

variable [Finite R] in
/-- info: ↧R : FintypeCat -/
#guard_msgs in #check FintypeCat.of R

-- Order categories: both the `of ::` structure-constructor style ...
variable [BooleanAlgebra R] in
/-- info: ↧R : BoolAlg -/
#guard_msgs in #check BoolAlg.of R

variable [SemilatticeSup R] [OrderBot R] in
/-- info: ↧R : SemilatSupCat -/
#guard_msgs in #check SemilatSupCat.of R

-- ... and the `abbrev of` style.
variable [Lattice R] in
/-- info: ↧R : Lat -/
#guard_msgs in #check Lat.of R

variable [PartialOrder R] [BoundedOrder R] in
/-- info: ↧R : BddOrd -/
#guard_msgs in #check BddOrd.of R

-- A category may also opt in downstream. `ModuleCat` does not opt in in Mathlib, so it still
-- prints using `.of`, ...
/-- info: ModuleCat.of ℤ ℤ : ModuleCat ℤ -/
#guard_msgs in
#check (↧ℤ : ModuleCat ℤ)

-- ... unless it is opted in, which also covers the parameterised case.
@[app_delab ModuleCat.of] public meta def ModuleCat.delabOf := CategoryTheory.delabOf

/-- info: ↧ℤ : ModuleCat ℤ -/
#guard_msgs in
#check (↧ℤ : ModuleCat ℤ)

-- `pp.explicit` falls back to `delabApp`.
/-- info: @CommRingCat.of Int Int.instCommRing : CommRingCat -/
#guard_msgs in
set_option pp.explicit true in
#check (↧ℤ : CommRingCat)

-- `pp.notation false` falls back to `delabApp`, rather than to structure instance notation.
/-- info: CommRingCat.of Int : CommRingCat -/
#guard_msgs in
set_option pp.notation false in
#check (↧ℤ : CommRingCat)

end Delab
