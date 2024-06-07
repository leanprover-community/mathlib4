/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Bryan Gin-ge Chen
-/
import Mathlib.Order.Heyting.Basic

#align_import order.boolean_algebra from "leanprover-community/mathlib"@"9ac7c0c8c4d7a535ec3e5b34b8859aab9233b2f4"

/-!
# (Generalized) Boolean algebras

A Boolean algebra is a bounded distributive lattice with a complement operator. Boolean algebras
generalize the (classical) logic of propositions and the lattice of subsets of a set.

Generalized Boolean algebras may be less familiar, but they are essentially Boolean algebras which
do not necessarily have a top element (`⊤`) (and hence not all elements may have complements). One
example in mathlib is `Finset α`, the type of all finite subsets of an arbitrary
(not-necessarily-finite) type `α`.

`GeneralizedBooleanAlgebra α` is defined to be a distributive lattice with bottom (`⊥`) admitting
a *relative* complement operator, written using "set difference" notation as `x \ y` (`sdiff x y`).
For convenience, the `BooleanAlgebra` type class is defined to extend `GeneralizedBooleanAlgebra`
so that it is also bundled with a `\` operator.

(A terminological point: `x \ y` is the complement of `y` relative to the interval `[⊥, x]`. We do
not yet have relative complements for arbitrary intervals, as we do not even have lattice
intervals.)

## Main declarations

* `GeneralizedBooleanAlgebra`: a type class for generalized Boolean algebras
* `BooleanAlgebra`: a type class for Boolean algebras.
* `Prop.booleanAlgebra`: the Boolean algebra instance on `Prop`

## Implementation notes

The `sup_inf_sdiff` and `inf_inf_sdiff` axioms for the relative complement operator in
`GeneralizedBooleanAlgebra` are taken from
[Wikipedia](https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Generalizations).

[Stone's paper introducing generalized Boolean algebras][Stone1935] does not define a relative
complement operator `a \ b` for all `a`, `b`. Instead, the postulates there amount to an assumption
that for all `a, b : α` where `a ≤ b`, the equations `x ⊔ a = b` and `x ⊓ a = ⊥` have a solution
`x`. `Disjoint.sdiff_unique` proves that this `x` is in fact `b \ a`.

## References

* <https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Generalizations>
* [*Postulates for Boolean Algebras and Generalized Boolean Algebras*, M.H. Stone][Stone1935]
* [*Lattice Theory: Foundation*, George Grätzer][Gratzer2011]

## Tags

generalized Boolean algebras, Boolean algebras, lattices, sdiff, compl
-/


open Function OrderDual

universe u v

variable {α : Type u} {β : Type*} {w x y z : α}

/-!
### Generalized Boolean algebras

Some of the lemmas in this section are from:

* [*Lattice Theory: Foundation*, George Grätzer][Gratzer2011]
* <https://ncatlab.org/nlab/show/relative+complement>
* <https://people.math.gatech.edu/~mccuan/courses/4317/symmetricdifference.pdf>

-/


/-- A generalized Boolean algebra is a distributive lattice with `⊥` and a relative complement
operation `\` (called `sdiff`, after "set difference") satisfying `(a ⊓ b) ⊔ (a \ b) = a` and
`(a ⊓ b) ⊓ (a \ b) = ⊥`, i.e. `a \ b` is the complement of `b` in `a`.

This is a generalization of Boolean algebras which applies to `Finset α` for arbitrary
(not-necessarily-`Fintype`) `α`. -/
class GeneralizedBooleanAlgebra (α : Type u) extends DistribLattice α, SDiff α, Bot α where
  /-- For any `a`, `b`, `(a ⊓ b) ⊔ (a / b) = a` -/
  sup_inf_sdiff : ∀ a b : α, a ⊓ b ⊔ a \ b = a
  /-- For any `a`, `b`, `(a ⊓ b) ⊓ (a / b) = ⊥` -/
  inf_inf_sdiff : ∀ a b : α, a ⊓ b ⊓ a \ b = ⊥
#align generalized_boolean_algebra GeneralizedBooleanAlgebra

-- We might want an `IsCompl_of` predicate (for relative complements) generalizing `IsCompl`,
-- however we'd need another type class for lattices with bot, and all the API for that.
section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α]

@[simp]
theorem sup_inf_sdiff (x y : α) : x ⊓ y ⊔ x \ y = x :=
  GeneralizedBooleanAlgebra.sup_inf_sdiff _ _
#align sup_inf_sdiff sup_inf_sdiff

@[simp]
theorem inf_inf_sdiff (x y : α) : x ⊓ y ⊓ x \ y = ⊥ :=
  GeneralizedBooleanAlgebra.inf_inf_sdiff _ _
#align inf_inf_sdiff inf_inf_sdiff

@[simp]
theorem sup_sdiff_inf (x y : α) : x \ y ⊔ x ⊓ y = x := by rw [sup_comm, sup_inf_sdiff]
#align sup_sdiff_inf sup_sdiff_inf

@[simp]
theorem inf_sdiff_inf (x y : α) : x \ y ⊓ (x ⊓ y) = ⊥ := by rw [inf_comm, inf_inf_sdiff]
#align inf_sdiff_inf inf_sdiff_inf

-- see Note [lower instance priority]
instance (priority := 100) GeneralizedBooleanAlgebra.toOrderBot : OrderBot α where
  __ := GeneralizedBooleanAlgebra.toBot
  bot_le a := by
    rw [← inf_inf_sdiff a a, inf_assoc]
    exact inf_le_left
#align generalized_boolean_algebra.to_order_bot GeneralizedBooleanAlgebra.toOrderBot

theorem disjoint_inf_sdiff : Disjoint (x ⊓ y) (x \ y) :=
  disjoint_iff_inf_le.mpr (inf_inf_sdiff x y).le
#align disjoint_inf_sdiff disjoint_inf_sdiff

-- TODO: in distributive lattices, relative complements are unique when they exist
theorem sdiff_unique (s : x ⊓ y ⊔ z = x) (i : x ⊓ y ⊓ z = ⊥) : x \ y = z := by
  conv_rhs at s => rw [← sup_inf_sdiff x y, sup_comm]
  rw [sup_comm] at s
  conv_rhs at i => rw [← inf_inf_sdiff x y, inf_comm]
  rw [inf_comm] at i
  exact (eq_of_inf_eq_sup_eq i s).symm
#align sdiff_unique sdiff_unique

-- Use `sdiff_le`
private theorem sdiff_le' : x \ y ≤ x :=
  calc
    x \ y ≤ x ⊓ y ⊔ x \ y := le_sup_right
    _ = x := sup_inf_sdiff x y

-- Use `sdiff_sup_self`
private theorem sdiff_sup_self' : y \ x ⊔ x = y ⊔ x :=
  calc
    y \ x ⊔ x = y \ x ⊔ (x ⊔ x ⊓ y) := by rw [sup_inf_self]
    _ = y ⊓ x ⊔ y \ x ⊔ x := by ac_rfl
    _ = y ⊔ x := by rw [sup_inf_sdiff]

@[simp]
theorem sdiff_inf_sdiff : x \ y ⊓ y \ x = ⊥ :=
  Eq.symm <|
    calc
      ⊥ = x ⊓ y ⊓ x \ y := by rw [inf_inf_sdiff]
      _ = x ⊓ (y ⊓ x ⊔ y \ x) ⊓ x \ y := by rw [sup_inf_sdiff]
      _ = (x ⊓ (y ⊓ x) ⊔ x ⊓ y \ x) ⊓ x \ y := by rw [inf_sup_left]
      _ = (y ⊓ (x ⊓ x) ⊔ x ⊓ y \ x) ⊓ x \ y := by ac_rfl
      _ = (y ⊓ x ⊔ x ⊓ y \ x) ⊓ x \ y := by rw [inf_idem]
      _ = x ⊓ y ⊓ x \ y ⊔ x ⊓ y \ x ⊓ x \ y := by rw [inf_sup_right, inf_comm x y]
      _ = x ⊓ y \ x ⊓ x \ y := by rw [inf_inf_sdiff, bot_sup_eq]
      _ = x ⊓ x \ y ⊓ y \ x := by ac_rfl
      _ = x \ y ⊓ y \ x := by rw [inf_of_le_right sdiff_le']
#align sdiff_inf_sdiff sdiff_inf_sdiff

theorem disjoint_sdiff_sdiff : Disjoint (x \ y) (y \ x) :=
  disjoint_iff_inf_le.mpr sdiff_inf_sdiff.le
#align disjoint_sdiff_sdiff disjoint_sdiff_sdiff

@[simp]
theorem inf_sdiff_self_right : x ⊓ y \ x = ⊥ :=
  calc
    x ⊓ y \ x = (x ⊓ y ⊔ x \ y) ⊓ y \ x := by rw [sup_inf_sdiff]
    _ = x ⊓ y ⊓ y \ x ⊔ x \ y ⊓ y \ x := by rw [inf_sup_right]
    _ = ⊥ := by rw [inf_comm x y, inf_inf_sdiff, sdiff_inf_sdiff, bot_sup_eq]
#align inf_sdiff_self_right inf_sdiff_self_right

@[simp]
theorem inf_sdiff_self_left : y \ x ⊓ x = ⊥ := by rw [inf_comm, inf_sdiff_self_right]
#align inf_sdiff_self_left inf_sdiff_self_left

-- see Note [lower instance priority]
instance (priority := 100) GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra :
    GeneralizedCoheytingAlgebra α where
  __ := ‹GeneralizedBooleanAlgebra α›
  __ := GeneralizedBooleanAlgebra.toOrderBot
  sdiff := (· \ ·)
  sdiff_le_iff y x z :=
    ⟨fun h =>
      le_of_inf_le_sup_le
        (le_of_eq
          (calc
            y ⊓ y \ x = y \ x := inf_of_le_right sdiff_le'
            _ = x ⊓ y \ x ⊔ z ⊓ y \ x := by
              rw [inf_eq_right.2 h, inf_sdiff_self_right, bot_sup_eq]
            _ = (x ⊔ z) ⊓ y \ x := by rw [← inf_sup_right]))
        (calc
          y ⊔ y \ x = y := sup_of_le_left sdiff_le'
          _ ≤ y ⊔ (x ⊔ z) := le_sup_left
          _ = y \ x ⊔ x ⊔ z := by rw [← sup_assoc, ← @sdiff_sup_self' _ x y]
          _ = x ⊔ z ⊔ y \ x := by ac_rfl),
      fun h =>
      le_of_inf_le_sup_le
        (calc
          y \ x ⊓ x = ⊥ := inf_sdiff_self_left
          _ ≤ z ⊓ x := bot_le)
        (calc
          y \ x ⊔ x = y ⊔ x := sdiff_sup_self'
          _ ≤ x ⊔ z ⊔ x := sup_le_sup_right h x
          _ ≤ z ⊔ x := by rw [sup_assoc, sup_comm, sup_assoc, sup_idem])⟩
#align generalized_boolean_algebra.to_generalized_coheyting_algebra GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra

theorem disjoint_sdiff_self_left : Disjoint (y \ x) x :=
  disjoint_iff_inf_le.mpr inf_sdiff_self_left.le
#align disjoint_sdiff_self_left disjoint_sdiff_self_left

theorem disjoint_sdiff_self_right : Disjoint x (y \ x) :=
  disjoint_iff_inf_le.mpr inf_sdiff_self_right.le
#align disjoint_sdiff_self_right disjoint_sdiff_self_right

lemma le_sdiff : x ≤ y \ z ↔ x ≤ y ∧ Disjoint x z :=
  ⟨fun h ↦ ⟨h.trans sdiff_le, disjoint_sdiff_self_left.mono_left h⟩, fun h ↦
    by rw [← h.2.sdiff_eq_left]; exact sdiff_le_sdiff_right h.1⟩
#align le_sdiff le_sdiff

@[simp] lemma sdiff_eq_left : x \ y = x ↔ Disjoint x y :=
  ⟨fun h ↦ disjoint_sdiff_self_left.mono_left h.ge, Disjoint.sdiff_eq_left⟩
#align sdiff_eq_left sdiff_eq_left

/- TODO: we could make an alternative constructor for `GeneralizedBooleanAlgebra` using
`Disjoint x (y \ x)` and `x ⊔ (y \ x) = y` as axioms. -/
theorem Disjoint.sdiff_eq_of_sup_eq (hi : Disjoint x z) (hs : x ⊔ z = y) : y \ x = z :=
  have h : y ⊓ x = x := inf_eq_right.2 <| le_sup_left.trans hs.le
  sdiff_unique (by rw [h, hs]) (by rw [h, hi.eq_bot])
#align disjoint.sdiff_eq_of_sup_eq Disjoint.sdiff_eq_of_sup_eq

protected theorem Disjoint.sdiff_unique (hd : Disjoint x z) (hz : z ≤ y) (hs : y ≤ x ⊔ z) :
    y \ x = z :=
  sdiff_unique
    (by
      rw [← inf_eq_right] at hs
      rwa [sup_inf_right, inf_sup_right, sup_comm x, inf_sup_self, inf_comm, sup_comm z,
        hs, sup_eq_left])
    (by rw [inf_assoc, hd.eq_bot, inf_bot_eq])
#align disjoint.sdiff_unique Disjoint.sdiff_unique

-- cf. `IsCompl.disjoint_left_iff` and `IsCompl.disjoint_right_iff`
theorem disjoint_sdiff_iff_le (hz : z ≤ y) (hx : x ≤ y) : Disjoint z (y \ x) ↔ z ≤ x :=
  ⟨fun H =>
    le_of_inf_le_sup_le (le_trans H.le_bot bot_le)
      (by
        rw [sup_sdiff_cancel_right hx]
        refine le_trans (sup_le_sup_left sdiff_le z) ?_
        rw [sup_eq_right.2 hz]),
    fun H => disjoint_sdiff_self_right.mono_left H⟩
#align disjoint_sdiff_iff_le disjoint_sdiff_iff_le

-- cf. `IsCompl.le_left_iff` and `IsCompl.le_right_iff`
theorem le_iff_disjoint_sdiff (hz : z ≤ y) (hx : x ≤ y) : z ≤ x ↔ Disjoint z (y \ x) :=
  (disjoint_sdiff_iff_le hz hx).symm
#align le_iff_disjoint_sdiff le_iff_disjoint_sdiff

-- cf. `IsCompl.inf_left_eq_bot_iff` and `IsCompl.inf_right_eq_bot_iff`
theorem inf_sdiff_eq_bot_iff (hz : z ≤ y) (hx : x ≤ y) : z ⊓ y \ x = ⊥ ↔ z ≤ x := by
  rw [← disjoint_iff]
  exact disjoint_sdiff_iff_le hz hx
#align inf_sdiff_eq_bot_iff inf_sdiff_eq_bot_iff

-- cf. `IsCompl.left_le_iff` and `IsCompl.right_le_iff`
theorem le_iff_eq_sup_sdiff (hz : z ≤ y) (hx : x ≤ y) : x ≤ z ↔ y = z ⊔ y \ x :=
  ⟨fun H => by
    apply le_antisymm
    · conv_lhs => rw [← sup_inf_sdiff y x]
      apply sup_le_sup_right
      rwa [inf_eq_right.2 hx]
    · apply le_trans
      · apply sup_le_sup_right hz
      · rw [sup_sdiff_left],
    fun H => by
    conv_lhs at H => rw [← sup_sdiff_cancel_right hx]
    refine le_of_inf_le_sup_le ?_ H.le
    rw [inf_sdiff_self_right]
    exact bot_le⟩
#align le_iff_eq_sup_sdiff le_iff_eq_sup_sdiff

-- cf. `IsCompl.sup_inf`
theorem sdiff_sup : y \ (x ⊔ z) = y \ x ⊓ y \ z :=
  sdiff_unique
    (calc
      y ⊓ (x ⊔ z) ⊔ y \ x ⊓ y \ z = (y ⊓ (x ⊔ z) ⊔ y \ x) ⊓ (y ⊓ (x ⊔ z) ⊔ y \ z) := by
          rw [sup_inf_left]
      _ = (y ⊓ x ⊔ y ⊓ z ⊔ y \ x) ⊓ (y ⊓ x ⊔ y ⊓ z ⊔ y \ z) := by rw [@inf_sup_left _ _ y]
      _ = (y ⊓ z ⊔ (y ⊓ x ⊔ y \ x)) ⊓ (y ⊓ x ⊔ (y ⊓ z ⊔ y \ z)) := by ac_rfl
      _ = (y ⊓ z ⊔ y) ⊓ (y ⊓ x ⊔ y) := by rw [sup_inf_sdiff, sup_inf_sdiff]
      _ = (y ⊔ y ⊓ z) ⊓ (y ⊔ y ⊓ x) := by ac_rfl
      _ = y := by rw [sup_inf_self, sup_inf_self, inf_idem])
    (calc
      y ⊓ (x ⊔ z) ⊓ (y \ x ⊓ y \ z) = (y ⊓ x ⊔ y ⊓ z) ⊓ (y \ x ⊓ y \ z) := by rw [inf_sup_left]
      _ = y ⊓ x ⊓ (y \ x ⊓ y \ z) ⊔ y ⊓ z ⊓ (y \ x ⊓ y \ z) := by rw [inf_sup_right]
      _ = y ⊓ x ⊓ y \ x ⊓ y \ z ⊔ y \ x ⊓ (y \ z ⊓ (y ⊓ z)) := by ac_rfl
      _ = ⊥ := by rw [inf_inf_sdiff, bot_inf_eq, bot_sup_eq, inf_comm (y \ z),
                      inf_inf_sdiff, inf_bot_eq])
#align sdiff_sup sdiff_sup

theorem sdiff_eq_sdiff_iff_inf_eq_inf : y \ x = y \ z ↔ y ⊓ x = y ⊓ z :=
  ⟨fun h => eq_of_inf_eq_sup_eq (by rw [inf_inf_sdiff, h, inf_inf_sdiff])
    (by rw [sup_inf_sdiff, h, sup_inf_sdiff]),
    fun h => by rw [← sdiff_inf_self_right, ← sdiff_inf_self_right z y, inf_comm, h, inf_comm]⟩
#align sdiff_eq_sdiff_iff_inf_eq_inf sdiff_eq_sdiff_iff_inf_eq_inf

theorem sdiff_eq_self_iff_disjoint : x \ y = x ↔ Disjoint y x :=
  calc
    x \ y = x ↔ x \ y = x \ ⊥ := by rw [sdiff_bot]
    _ ↔ x ⊓ y = x ⊓ ⊥ := sdiff_eq_sdiff_iff_inf_eq_inf
    _ ↔ Disjoint y x := by rw [inf_bot_eq, inf_comm, disjoint_iff]
#align sdiff_eq_self_iff_disjoint sdiff_eq_self_iff_disjoint

theorem sdiff_eq_self_iff_disjoint' : x \ y = x ↔ Disjoint x y := by
  rw [sdiff_eq_self_iff_disjoint, disjoint_comm]
#align sdiff_eq_self_iff_disjoint' sdiff_eq_self_iff_disjoint'

theorem sdiff_lt (hx : y ≤ x) (hy : y ≠ ⊥) : x \ y < x := by
  refine sdiff_le.lt_of_ne fun h => hy ?_
  rw [sdiff_eq_self_iff_disjoint', disjoint_iff] at h
  rw [← h, inf_eq_right.mpr hx]
#align sdiff_lt sdiff_lt

@[simp]
theorem le_sdiff_iff : x ≤ y \ x ↔ x = ⊥ :=
  ⟨fun h => disjoint_self.1 (disjoint_sdiff_self_right.mono_right h), fun h => h.le.trans bot_le⟩
#align le_sdiff_iff le_sdiff_iff

@[simp] lemma sdiff_eq_right : x \ y = y ↔ x = ⊥ ∧ y = ⊥ := by
  rw [disjoint_sdiff_self_left.eq_iff]; aesop

lemma sdiff_ne_right : x \ y ≠ y ↔ x ≠ ⊥ ∨ y ≠ ⊥ := sdiff_eq_right.not.trans not_and_or

theorem sdiff_lt_sdiff_right (h : x < y) (hz : z ≤ x) : x \ z < y \ z :=
  (sdiff_le_sdiff_right h.le).lt_of_not_le
    fun h' => h.not_le <| le_sdiff_sup.trans <| sup_le_of_le_sdiff_right h' hz
#align sdiff_lt_sdiff_right sdiff_lt_sdiff_right

theorem sup_inf_inf_sdiff : x ⊓ y ⊓ z ⊔ y \ z = x ⊓ y ⊔ y \ z :=
  calc
    x ⊓ y ⊓ z ⊔ y \ z = x ⊓ (y ⊓ z) ⊔ y \ z := by rw [inf_assoc]
    _ = (x ⊔ y \ z) ⊓ y := by rw [sup_inf_right, sup_inf_sdiff]
    _ = x ⊓ y ⊔ y \ z := by rw [inf_sup_right, inf_sdiff_left]
#align sup_inf_inf_sdiff sup_inf_inf_sdiff

theorem sdiff_sdiff_right : x \ (y \ z) = x \ y ⊔ x ⊓ y ⊓ z := by
  rw [sup_comm, inf_comm, ← inf_assoc, sup_inf_inf_sdiff]
  apply sdiff_unique
  · calc
      x ⊓ y \ z ⊔ (z ⊓ x ⊔ x \ y) = (x ⊔ (z ⊓ x ⊔ x \ y)) ⊓ (y \ z ⊔ (z ⊓ x ⊔ x \ y)) := by
          rw [sup_inf_right]
      _ = (x ⊔ x ⊓ z ⊔ x \ y) ⊓ (y \ z ⊔ (x ⊓ z ⊔ x \ y)) := by ac_rfl
      _ = x ⊓ (y \ z ⊔ x ⊓ z ⊔ x \ y) := by rw [sup_inf_self, sup_sdiff_left, ← sup_assoc]
      _ = x ⊓ (y \ z ⊓ (z ⊔ y) ⊔ x ⊓ (z ⊔ y) ⊔ x \ y) := by
          rw [sup_inf_left, sdiff_sup_self', inf_sup_right, sup_comm y]
      _ = x ⊓ (y \ z ⊔ (x ⊓ z ⊔ x ⊓ y) ⊔ x \ y) := by
          rw [inf_sdiff_sup_right, @inf_sup_left _ _ x z y]
      _ = x ⊓ (y \ z ⊔ (x ⊓ z ⊔ (x ⊓ y ⊔ x \ y))) := by ac_rfl
      _ = x ⊓ (y \ z ⊔ (x ⊔ x ⊓ z)) := by rw [sup_inf_sdiff, sup_comm (x ⊓ z)]
      _ = x := by rw [sup_inf_self, sup_comm, inf_sup_self]
  · calc
      x ⊓ y \ z ⊓ (z ⊓ x ⊔ x \ y) = x ⊓ y \ z ⊓ (z ⊓ x) ⊔ x ⊓ y \ z ⊓ x \ y := by rw [inf_sup_left]
      _ = x ⊓ (y \ z ⊓ z ⊓ x) ⊔ x ⊓ y \ z ⊓ x \ y := by ac_rfl
      _ = x ⊓ y \ z ⊓ x \ y := by rw [inf_sdiff_self_left, bot_inf_eq, inf_bot_eq, bot_sup_eq]
      _ = x ⊓ (y \ z ⊓ y) ⊓ x \ y := by conv_lhs => rw [← inf_sdiff_left]
      _ = x ⊓ (y \ z ⊓ (y ⊓ x \ y)) := by ac_rfl
      _ = ⊥ := by rw [inf_sdiff_self_right, inf_bot_eq, inf_bot_eq]
#align sdiff_sdiff_right sdiff_sdiff_right

theorem sdiff_sdiff_right' : x \ (y \ z) = x \ y ⊔ x ⊓ z :=
  calc
    x \ (y \ z) = x \ y ⊔ x ⊓ y ⊓ z := sdiff_sdiff_right
    _ = z ⊓ x ⊓ y ⊔ x \ y := by ac_rfl
    _ = x \ y ⊔ x ⊓ z := by rw [sup_inf_inf_sdiff, sup_comm, inf_comm]
#align sdiff_sdiff_right' sdiff_sdiff_right'

theorem sdiff_sdiff_eq_sdiff_sup (h : z ≤ x) : x \ (y \ z) = x \ y ⊔ z := by
  rw [sdiff_sdiff_right', inf_eq_right.2 h]
#align sdiff_sdiff_eq_sdiff_sup sdiff_sdiff_eq_sdiff_sup

@[simp]
theorem sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y := by
  rw [sdiff_sdiff_right, inf_idem, sdiff_self, bot_sup_eq]
#align sdiff_sdiff_right_self sdiff_sdiff_right_self

theorem sdiff_sdiff_eq_self (h : y ≤ x) : x \ (x \ y) = y := by
  rw [sdiff_sdiff_right_self, inf_of_le_right h]
#align sdiff_sdiff_eq_self sdiff_sdiff_eq_self

theorem sdiff_eq_symm (hy : y ≤ x) (h : x \ y = z) : x \ z = y := by
  rw [← h, sdiff_sdiff_eq_self hy]
#align sdiff_eq_symm sdiff_eq_symm

theorem sdiff_eq_comm (hy : y ≤ x) (hz : z ≤ x) : x \ y = z ↔ x \ z = y :=
  ⟨sdiff_eq_symm hy, sdiff_eq_symm hz⟩
#align sdiff_eq_comm sdiff_eq_comm

theorem eq_of_sdiff_eq_sdiff (hxz : x ≤ z) (hyz : y ≤ z) (h : z \ x = z \ y) : x = y := by
  rw [← sdiff_sdiff_eq_self hxz, h, sdiff_sdiff_eq_self hyz]
#align eq_of_sdiff_eq_sdiff eq_of_sdiff_eq_sdiff

theorem sdiff_sdiff_left' : (x \ y) \ z = x \ y ⊓ x \ z := by rw [sdiff_sdiff_left, sdiff_sup]
#align sdiff_sdiff_left' sdiff_sdiff_left'

theorem sdiff_sdiff_sup_sdiff : z \ (x \ y ⊔ y \ x) = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x) :=
  calc
    z \ (x \ y ⊔ y \ x) = (z \ x ⊔ z ⊓ x ⊓ y) ⊓ (z \ y ⊔ z ⊓ y ⊓ x) := by
        rw [sdiff_sup, sdiff_sdiff_right, sdiff_sdiff_right]
    _ = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ z ⊓ y ⊓ x) := by rw [sup_inf_left, sup_comm, sup_inf_sdiff]
    _ = z ⊓ (z \ x ⊔ y) ⊓ (z ⊓ (z \ y ⊔ x)) := by
        rw [sup_inf_left, sup_comm (z \ y), sup_inf_sdiff]
    _ = z ⊓ z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x) := by ac_rfl
    _ = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x) := by rw [inf_idem]
#align sdiff_sdiff_sup_sdiff sdiff_sdiff_sup_sdiff

theorem sdiff_sdiff_sup_sdiff' : z \ (x \ y ⊔ y \ x) = z ⊓ x ⊓ y ⊔ z \ x ⊓ z \ y :=
  calc
    z \ (x \ y ⊔ y \ x) = z \ (x \ y) ⊓ z \ (y \ x) := sdiff_sup
    _ = (z \ x ⊔ z ⊓ x ⊓ y) ⊓ (z \ y ⊔ z ⊓ y ⊓ x) := by rw [sdiff_sdiff_right, sdiff_sdiff_right]
    _ = (z \ x ⊔ z ⊓ y ⊓ x) ⊓ (z \ y ⊔ z ⊓ y ⊓ x) := by ac_rfl
    _ = z \ x ⊓ z \ y ⊔ z ⊓ y ⊓ x := by rw [← sup_inf_right]
    _ = z ⊓ x ⊓ y ⊔ z \ x ⊓ z \ y := by ac_rfl
#align sdiff_sdiff_sup_sdiff' sdiff_sdiff_sup_sdiff'

lemma sdiff_sdiff_sdiff_cancel_left (hca : z ≤ x) : (x \ y) \ (x \ z) = z \ y :=
  sdiff_sdiff_sdiff_le_sdiff.antisymm <|
    (disjoint_sdiff_self_right.mono_left sdiff_le).le_sdiff_of_le_left <| sdiff_le_sdiff_right hca

lemma sdiff_sdiff_sdiff_cancel_right (hcb : z ≤ y) : (x \ z) \ (y \ z) = x \ y := by
  rw [le_antisymm_iff, sdiff_le_comm]
  exact ⟨sdiff_sdiff_sdiff_le_sdiff,
    (disjoint_sdiff_self_left.mono_right sdiff_le).le_sdiff_of_le_left <| sdiff_le_sdiff_left hcb⟩

theorem inf_sdiff : (x ⊓ y) \ z = x \ z ⊓ y \ z :=
  sdiff_unique
    (calc
      x ⊓ y ⊓ z ⊔ x \ z ⊓ y \ z = (x ⊓ y ⊓ z ⊔ x \ z) ⊓ (x ⊓ y ⊓ z ⊔ y \ z) := by rw [sup_inf_left]
      _ = (x ⊓ y ⊓ (z ⊔ x) ⊔ x \ z) ⊓ (x ⊓ y ⊓ z ⊔ y \ z) := by
          rw [sup_inf_right, sup_sdiff_self_right, inf_sup_right, inf_sdiff_sup_right]
      _ = (y ⊓ (x ⊓ (x ⊔ z)) ⊔ x \ z) ⊓ (x ⊓ y ⊓ z ⊔ y \ z) := by ac_rfl
      _ = (y ⊓ x ⊔ x \ z) ⊓ (x ⊓ y ⊔ y \ z) := by rw [inf_sup_self, sup_inf_inf_sdiff]
      _ = x ⊓ y ⊔ x \ z ⊓ y \ z := by rw [inf_comm y, sup_inf_left]
      _ = x ⊓ y := sup_eq_left.2 (inf_le_inf sdiff_le sdiff_le))
    (calc
      x ⊓ y ⊓ z ⊓ (x \ z ⊓ y \ z) = x ⊓ y ⊓ (z ⊓ x \ z) ⊓ y \ z := by ac_rfl
      _ = ⊥ := by rw [inf_sdiff_self_right, inf_bot_eq, bot_inf_eq])
#align inf_sdiff inf_sdiff

theorem inf_sdiff_assoc : (x ⊓ y) \ z = x ⊓ y \ z :=
  sdiff_unique
    (calc
      x ⊓ y ⊓ z ⊔ x ⊓ y \ z = x ⊓ (y ⊓ z) ⊔ x ⊓ y \ z := by rw [inf_assoc]
      _ = x ⊓ (y ⊓ z ⊔ y \ z) := by rw [← inf_sup_left]
      _ = x ⊓ y := by rw [sup_inf_sdiff])
    (calc
      x ⊓ y ⊓ z ⊓ (x ⊓ y \ z) = x ⊓ x ⊓ (y ⊓ z ⊓ y \ z) := by ac_rfl
      _ = ⊥ := by rw [inf_inf_sdiff, inf_bot_eq])
#align inf_sdiff_assoc inf_sdiff_assoc

theorem inf_sdiff_right_comm : x \ z ⊓ y = (x ⊓ y) \ z := by
  rw [inf_comm x, inf_comm, inf_sdiff_assoc]
#align inf_sdiff_right_comm inf_sdiff_right_comm

theorem inf_sdiff_distrib_left (a b c : α) : a ⊓ b \ c = (a ⊓ b) \ (a ⊓ c) := by
  rw [sdiff_inf, sdiff_eq_bot_iff.2 inf_le_left, bot_sup_eq, inf_sdiff_assoc]
#align inf_sdiff_distrib_left inf_sdiff_distrib_left

theorem inf_sdiff_distrib_right (a b c : α) : a \ b ⊓ c = (a ⊓ c) \ (b ⊓ c) := by
  simp_rw [inf_comm _ c, inf_sdiff_distrib_left]
#align inf_sdiff_distrib_right inf_sdiff_distrib_right

theorem disjoint_sdiff_comm : Disjoint (x \ z) y ↔ Disjoint x (y \ z) := by
  simp_rw [disjoint_iff, inf_sdiff_right_comm, inf_sdiff_assoc]
#align disjoint_sdiff_comm disjoint_sdiff_comm

theorem sup_eq_sdiff_sup_sdiff_sup_inf : x ⊔ y = x \ y ⊔ y \ x ⊔ x ⊓ y :=
  Eq.symm <|
    calc
      x \ y ⊔ y \ x ⊔ x ⊓ y = (x \ y ⊔ y \ x ⊔ x) ⊓ (x \ y ⊔ y \ x ⊔ y) := by rw [sup_inf_left]
      _ = (x \ y ⊔ x ⊔ y \ x) ⊓ (x \ y ⊔ (y \ x ⊔ y)) := by ac_rfl
      _ = (x ⊔ y \ x) ⊓ (x \ y ⊔ y) := by rw [sup_sdiff_right, sup_sdiff_right]
      _ = x ⊔ y := by rw [sup_sdiff_self_right, sup_sdiff_self_left, inf_idem]
#align sup_eq_sdiff_sup_sdiff_sup_inf sup_eq_sdiff_sup_sdiff_sup_inf

theorem sup_lt_of_lt_sdiff_left (h : y < z \ x) (hxz : x ≤ z) : x ⊔ y < z := by
  rw [← sup_sdiff_cancel_right hxz]
  refine (sup_le_sup_left h.le _).lt_of_not_le fun h' => h.not_le ?_
  rw [← sdiff_idem]
  exact (sdiff_le_sdiff_of_sup_le_sup_left h').trans sdiff_le
#align sup_lt_of_lt_sdiff_left sup_lt_of_lt_sdiff_left

theorem sup_lt_of_lt_sdiff_right (h : x < z \ y) (hyz : y ≤ z) : x ⊔ y < z := by
  rw [← sdiff_sup_cancel hyz]
  refine (sup_le_sup_right h.le _).lt_of_not_le fun h' => h.not_le ?_
  rw [← sdiff_idem]
  exact (sdiff_le_sdiff_of_sup_le_sup_right h').trans sdiff_le
#align sup_lt_of_lt_sdiff_right sup_lt_of_lt_sdiff_right

instance Prod.instGeneralizedBooleanAlgebra [GeneralizedBooleanAlgebra β] :
    GeneralizedBooleanAlgebra (α × β) where
  sup_inf_sdiff _ _ := Prod.ext (sup_inf_sdiff _ _) (sup_inf_sdiff _ _)
  inf_inf_sdiff _ _ := Prod.ext (inf_inf_sdiff _ _) (inf_inf_sdiff _ _)

-- Porting note:
-- Once `pi_instance` has been ported, this is just `by pi_instance`.
instance Pi.instGeneralizedBooleanAlgebra {ι : Type*} {α : ι → Type*}
    [∀ i, GeneralizedBooleanAlgebra (α i)] : GeneralizedBooleanAlgebra (∀ i, α i) where
  sup_inf_sdiff := fun f g => funext fun a => sup_inf_sdiff (f a) (g a)
  inf_inf_sdiff := fun f g => funext fun a => inf_inf_sdiff (f a) (g a)
#align pi.generalized_boolean_algebra Pi.instGeneralizedBooleanAlgebra

end GeneralizedBooleanAlgebra

/-!
### Boolean algebras
-/


/-- A Boolean algebra is a bounded distributive lattice with a complement operator `ᶜ` such that
`x ⊓ xᶜ = ⊥` and `x ⊔ xᶜ = ⊤`. For convenience, it must also provide a set difference operation `\`
and a Heyting implication `⇨` satisfying `x \ y = x ⊓ yᶜ` and `x ⇨ y = y ⊔ xᶜ`.

This is a generalization of (classical) logic of propositions, or the powerset lattice.

Since `BoundedOrder`, `OrderBot`, and `OrderTop` are mixins that require `LE`
to be present at define-time, the `extends` mechanism does not work with them.
Instead, we extend using the underlying `Bot` and `Top` data typeclasses, and replicate the
order axioms of those classes here. A "forgetful" instance back to `BoundedOrder` is provided.
-/
class BooleanAlgebra (α : Type u) extends
    DistribLattice α, HasCompl α, SDiff α, HImp α, Top α, Bot α where
  /-- The infimum of `x` and `xᶜ` is at most `⊥` -/
  inf_compl_le_bot : ∀ x : α, x ⊓ xᶜ ≤ ⊥
  /-- The supremum of `x` and `xᶜ` is at least `⊤` -/
  top_le_sup_compl : ∀ x : α, ⊤ ≤ x ⊔ xᶜ
  /-- `⊤` is the greatest element -/
  le_top : ∀ a : α, a ≤ ⊤
  /-- `⊥` is the least element -/
  bot_le : ∀ a : α, ⊥ ≤ a
  /-- `x \ y` is equal to `x ⊓ yᶜ` -/
  sdiff := fun x y => x ⊓ yᶜ
  /-- `x ⇨ y` is equal to `y ⊔ xᶜ` -/
  himp := fun x y => y ⊔ xᶜ
  /-- `x \ y` is equal to `x ⊓ yᶜ` -/
  sdiff_eq : ∀ x y : α, x \ y = x ⊓ yᶜ := by aesop
  /-- `x ⇨ y` is equal to `y ⊔ xᶜ` -/
  himp_eq : ∀ x y : α, x ⇨ y = y ⊔ xᶜ := by aesop
#align boolean_algebra BooleanAlgebra

-- see Note [lower instance priority]
instance (priority := 100) BooleanAlgebra.toBoundedOrder [h : BooleanAlgebra α] : BoundedOrder α :=
  { h with }
#align boolean_algebra.to_bounded_order BooleanAlgebra.toBoundedOrder

-- See note [reducible non instances]
/-- A bounded generalized boolean algebra is a boolean algebra. -/
abbrev GeneralizedBooleanAlgebra.toBooleanAlgebra [GeneralizedBooleanAlgebra α] [OrderTop α] :
    BooleanAlgebra α where
  __ := ‹GeneralizedBooleanAlgebra α›
  __ := GeneralizedBooleanAlgebra.toOrderBot
  __ := ‹OrderTop α›
  compl a := ⊤ \ a
  inf_compl_le_bot _ := disjoint_sdiff_self_right.le_bot
  top_le_sup_compl _ := le_sup_sdiff
  sdiff_eq _ _ := by
      -- Porting note: changed `rw` to `erw` here.
      -- https://github.com/leanprover-community/mathlib4/issues/5164
      erw [← inf_sdiff_assoc, inf_top_eq]
#align generalized_boolean_algebra.to_boolean_algebra GeneralizedBooleanAlgebra.toBooleanAlgebra

section BooleanAlgebra

variable [BooleanAlgebra α]

theorem inf_compl_eq_bot' : x ⊓ xᶜ = ⊥ :=
  bot_unique <| BooleanAlgebra.inf_compl_le_bot x
#align inf_compl_eq_bot' inf_compl_eq_bot'

@[simp]
theorem sup_compl_eq_top : x ⊔ xᶜ = ⊤ :=
  top_unique <| BooleanAlgebra.top_le_sup_compl x
#align sup_compl_eq_top sup_compl_eq_top

@[simp]
theorem compl_sup_eq_top : xᶜ ⊔ x = ⊤ := by rw [sup_comm, sup_compl_eq_top]
#align compl_sup_eq_top compl_sup_eq_top

theorem isCompl_compl : IsCompl x xᶜ :=
  IsCompl.of_eq inf_compl_eq_bot' sup_compl_eq_top
#align is_compl_compl isCompl_compl

theorem sdiff_eq : x \ y = x ⊓ yᶜ :=
  BooleanAlgebra.sdiff_eq x y
#align sdiff_eq sdiff_eq

theorem himp_eq : x ⇨ y = y ⊔ xᶜ :=
  BooleanAlgebra.himp_eq x y
#align himp_eq himp_eq

instance (priority := 100) BooleanAlgebra.toComplementedLattice : ComplementedLattice α :=
  ⟨fun x => ⟨xᶜ, isCompl_compl⟩⟩
#align boolean_algebra.to_complemented_lattice BooleanAlgebra.toComplementedLattice

-- see Note [lower instance priority]
instance (priority := 100) BooleanAlgebra.toGeneralizedBooleanAlgebra :
    GeneralizedBooleanAlgebra α where
  __ := ‹BooleanAlgebra α›
  sup_inf_sdiff a b := by rw [sdiff_eq, ← inf_sup_left, sup_compl_eq_top, inf_top_eq]
  inf_inf_sdiff a b := by
    rw [sdiff_eq, ← inf_inf_distrib_left, inf_compl_eq_bot', inf_bot_eq]
#align boolean_algebra.to_generalized_boolean_algebra BooleanAlgebra.toGeneralizedBooleanAlgebra

-- See note [lower instance priority]
instance (priority := 100) BooleanAlgebra.toBiheytingAlgebra : BiheytingAlgebra α where
  __ := ‹BooleanAlgebra α›
  __ := GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra
  hnot := compl
  le_himp_iff a b c := by rw [himp_eq, isCompl_compl.le_sup_right_iff_inf_left_le]
  himp_bot _ := _root_.himp_eq.trans (bot_sup_eq _)
  top_sdiff a := by rw [sdiff_eq, top_inf_eq]; rfl
#align boolean_algebra.to_biheyting_algebra BooleanAlgebra.toBiheytingAlgebra

@[simp]
theorem hnot_eq_compl : ￢x = xᶜ :=
  rfl
#align hnot_eq_compl hnot_eq_compl

/- NOTE: Is this theorem needed at all or can we use `top_sdiff'`. -/
theorem top_sdiff : ⊤ \ x = xᶜ :=
  top_sdiff' x
#align top_sdiff top_sdiff

theorem eq_compl_iff_isCompl : x = yᶜ ↔ IsCompl x y :=
  ⟨fun h => by
    rw [h]
    exact isCompl_compl.symm, IsCompl.eq_compl⟩
#align eq_compl_iff_is_compl eq_compl_iff_isCompl

theorem compl_eq_iff_isCompl : xᶜ = y ↔ IsCompl x y :=
  ⟨fun h => by
    rw [← h]
    exact isCompl_compl, IsCompl.compl_eq⟩
#align compl_eq_iff_is_compl compl_eq_iff_isCompl

theorem compl_eq_comm : xᶜ = y ↔ yᶜ = x := by
  rw [eq_comm, compl_eq_iff_isCompl, eq_compl_iff_isCompl]
#align compl_eq_comm compl_eq_comm

theorem eq_compl_comm : x = yᶜ ↔ y = xᶜ := by
  rw [eq_comm, compl_eq_iff_isCompl, eq_compl_iff_isCompl]
#align eq_compl_comm eq_compl_comm

@[simp]
theorem compl_compl (x : α) : xᶜᶜ = x :=
  (@isCompl_compl _ x _).symm.compl_eq
#align compl_compl compl_compl

theorem compl_comp_compl : compl ∘ compl = @id α :=
  funext compl_compl
#align compl_comp_compl compl_comp_compl

@[simp]
theorem compl_involutive : Function.Involutive (compl : α → α) :=
  compl_compl
#align compl_involutive compl_involutive

theorem compl_bijective : Function.Bijective (compl : α → α) :=
  compl_involutive.bijective
#align compl_bijective compl_bijective

theorem compl_surjective : Function.Surjective (compl : α → α) :=
  compl_involutive.surjective
#align compl_surjective compl_surjective

theorem compl_injective : Function.Injective (compl : α → α) :=
  compl_involutive.injective
#align compl_injective compl_injective

@[simp]
theorem compl_inj_iff : xᶜ = yᶜ ↔ x = y :=
  compl_injective.eq_iff
#align compl_inj_iff compl_inj_iff

theorem IsCompl.compl_eq_iff (h : IsCompl x y) : zᶜ = y ↔ z = x :=
  h.compl_eq ▸ compl_inj_iff
#align is_compl.compl_eq_iff IsCompl.compl_eq_iff

@[simp]
theorem compl_eq_top : xᶜ = ⊤ ↔ x = ⊥ :=
  isCompl_bot_top.compl_eq_iff
#align compl_eq_top compl_eq_top

@[simp]
theorem compl_eq_bot : xᶜ = ⊥ ↔ x = ⊤ :=
  isCompl_top_bot.compl_eq_iff
#align compl_eq_bot compl_eq_bot

@[simp]
theorem compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ :=
  hnot_inf_distrib _ _
#align compl_inf compl_inf

@[simp]
theorem compl_le_compl_iff_le : yᶜ ≤ xᶜ ↔ x ≤ y :=
  ⟨fun h => by have h := compl_le_compl h; simpa using h, compl_le_compl⟩
#align compl_le_compl_iff_le compl_le_compl_iff_le

@[simp] lemma compl_lt_compl_iff_lt : yᶜ < xᶜ ↔ x < y :=
  lt_iff_lt_of_le_iff_le' compl_le_compl_iff_le compl_le_compl_iff_le

theorem compl_le_of_compl_le (h : yᶜ ≤ x) : xᶜ ≤ y := by
  simpa only [compl_compl] using compl_le_compl h
#align compl_le_of_compl_le compl_le_of_compl_le

theorem compl_le_iff_compl_le : xᶜ ≤ y ↔ yᶜ ≤ x :=
  ⟨compl_le_of_compl_le, compl_le_of_compl_le⟩
#align compl_le_iff_compl_le compl_le_iff_compl_le

@[simp] theorem compl_le_self : xᶜ ≤ x ↔ x = ⊤ := by simpa using le_compl_self (a := xᶜ)

@[simp] theorem compl_lt_self [Nontrivial α] : xᶜ < x ↔ x = ⊤ := by
  simpa using lt_compl_self (a := xᶜ)

@[simp]
theorem sdiff_compl : x \ yᶜ = x ⊓ y := by rw [sdiff_eq, compl_compl]
#align sdiff_compl sdiff_compl

instance OrderDual.instBooleanAlgebra : BooleanAlgebra αᵒᵈ where
  __ := instDistribLattice α
  __ := instHeytingAlgebra
  sdiff_eq _ _ := @himp_eq α _ _ _
  himp_eq _ _ := @sdiff_eq α _ _ _
  inf_compl_le_bot a := (@codisjoint_hnot_right _ _ (ofDual a)).top_le
  top_le_sup_compl a := (@disjoint_compl_right _ _ (ofDual a)).le_bot

@[simp]
theorem sup_inf_inf_compl : x ⊓ y ⊔ x ⊓ yᶜ = x := by rw [← sdiff_eq, sup_inf_sdiff _ _]
#align sup_inf_inf_compl sup_inf_inf_compl

@[simp]
theorem compl_sdiff : (x \ y)ᶜ = x ⇨ y := by
  rw [sdiff_eq, himp_eq, compl_inf, compl_compl, sup_comm]
#align compl_sdiff compl_sdiff

@[simp]
theorem compl_himp : (x ⇨ y)ᶜ = x \ y :=
  @compl_sdiff αᵒᵈ _ _ _
#align compl_himp compl_himp

theorem compl_sdiff_compl : xᶜ \ yᶜ = y \ x := by rw [sdiff_compl, sdiff_eq, inf_comm]
#align compl_sdiff_compl compl_sdiff_compl

@[simp]
theorem compl_himp_compl : xᶜ ⇨ yᶜ = y ⇨ x :=
  @compl_sdiff_compl αᵒᵈ _ _ _
#align compl_himp_compl compl_himp_compl

theorem disjoint_compl_left_iff : Disjoint xᶜ y ↔ y ≤ x := by
  rw [← le_compl_iff_disjoint_left, compl_compl]
#align disjoint_compl_left_iff disjoint_compl_left_iff

theorem disjoint_compl_right_iff : Disjoint x yᶜ ↔ x ≤ y := by
  rw [← le_compl_iff_disjoint_right, compl_compl]
#align disjoint_compl_right_iff disjoint_compl_right_iff

theorem codisjoint_himp_self_left : Codisjoint (x ⇨ y) x :=
  @disjoint_sdiff_self_left αᵒᵈ _ _ _
#align codisjoint_himp_self_left codisjoint_himp_self_left

theorem codisjoint_himp_self_right : Codisjoint x (x ⇨ y) :=
  @disjoint_sdiff_self_right αᵒᵈ _ _ _
#align codisjoint_himp_self_right codisjoint_himp_self_right

theorem himp_le : x ⇨ y ≤ z ↔ y ≤ z ∧ Codisjoint x z :=
  (@le_sdiff αᵒᵈ _ _ _ _).trans <| and_congr_right' <| @Codisjoint_comm _ (_) _ _ _
#align himp_le himp_le

@[simp] lemma himp_le_iff : x ⇨ y ≤ x ↔ x = ⊤ :=
  ⟨fun h ↦ codisjoint_self.1 <| codisjoint_himp_self_right.mono_right h, fun h ↦ le_top.trans h.ge⟩

@[simp] lemma himp_eq_left : x ⇨ y = x ↔ x = ⊤ ∧ y = ⊤ := by
  rw [codisjoint_himp_self_left.eq_iff]; aesop

lemma himp_ne_right : x ⇨ y ≠ x ↔ x ≠ ⊤ ∨ y ≠ ⊤ := himp_eq_left.not.trans not_and_or

end BooleanAlgebra

instance Prop.instBooleanAlgebra : BooleanAlgebra Prop where
  __ := Prop.instHeytingAlgebra
  __ := GeneralizedHeytingAlgebra.toDistribLattice
  compl := Not
  himp_eq p q := propext imp_iff_or_not
  inf_compl_le_bot p H := H.2 H.1
  top_le_sup_compl p _ := Classical.em p
#align Prop.boolean_algebra Prop.instBooleanAlgebra

instance Prod.instBooleanAlgebra [BooleanAlgebra α] [BooleanAlgebra β] :
    BooleanAlgebra (α × β) where
  __ := instDistribLattice α β
  __ := instHeytingAlgebra
  himp_eq x y := by ext <;> simp [himp_eq]
  sdiff_eq x y := by ext <;> simp [sdiff_eq]
  inf_compl_le_bot x := by constructor <;> simp
  top_le_sup_compl x := by constructor <;> simp

instance Pi.instBooleanAlgebra {ι : Type u} {α : ι → Type v} [∀ i, BooleanAlgebra (α i)] :
    BooleanAlgebra (∀ i, α i) where
  __ := instDistribLattice
  __ := instHeytingAlgebra
  sdiff_eq _ _ := funext fun _ => sdiff_eq
  himp_eq _ _ := funext fun _ => himp_eq
  inf_compl_le_bot _ _ := BooleanAlgebra.inf_compl_le_bot _
  top_le_sup_compl _ _ := BooleanAlgebra.top_le_sup_compl _
#align pi.boolean_algebra Pi.instBooleanAlgebra

instance Bool.instBooleanAlgebra : BooleanAlgebra Bool where
  __ := instDistribLattice
  __ := linearOrder
  __ := instBoundedOrder
  compl := not
  inf_compl_le_bot a := a.and_not_self.le
  top_le_sup_compl a := a.or_not_self.ge

@[simp]
theorem Bool.sup_eq_bor : (· ⊔ ·) = or :=
  rfl
#align bool.sup_eq_bor Bool.sup_eq_bor

@[simp]
theorem Bool.inf_eq_band : (· ⊓ ·) = and :=
  rfl
#align bool.inf_eq_band Bool.inf_eq_band

@[simp]
theorem Bool.compl_eq_bnot : HasCompl.compl = not :=
  rfl
#align bool.compl_eq_bnot Bool.compl_eq_bnot

section lift

-- See note [reducible non-instances]
/-- Pullback a `GeneralizedBooleanAlgebra` along an injection. -/
protected abbrev Function.Injective.generalizedBooleanAlgebra [Sup α] [Inf α] [Bot α] [SDiff α]
    [GeneralizedBooleanAlgebra β] (f : α → β) (hf : Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_bot : f ⊥ = ⊥) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    GeneralizedBooleanAlgebra α where
  __ := hf.generalizedCoheytingAlgebra f map_sup map_inf map_bot map_sdiff
  __ := hf.distribLattice f map_sup map_inf
  sup_inf_sdiff a b := hf <| by erw [map_sup, map_sdiff, map_inf, sup_inf_sdiff]
  inf_inf_sdiff a b := hf <| by erw [map_inf, map_sdiff, map_inf, inf_inf_sdiff, map_bot]
#align function.injective.generalized_boolean_algebra Function.Injective.generalizedBooleanAlgebra

-- See note [reducible non-instances]
/-- Pullback a `BooleanAlgebra` along an injection. -/
protected abbrev Function.Injective.booleanAlgebra [Sup α] [Inf α] [Top α] [Bot α] [HasCompl α]
    [SDiff α] [BooleanAlgebra β] (f : α → β) (hf : Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_compl : ∀ a, f aᶜ = (f a)ᶜ)
    (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) : BooleanAlgebra α where
  __ := hf.generalizedBooleanAlgebra f map_sup map_inf map_bot map_sdiff
  compl := compl
  top := ⊤
  le_top a := (@le_top β _ _ _).trans map_top.ge
  bot_le a := map_bot.le.trans bot_le
  inf_compl_le_bot a := ((map_inf _ _).trans <| by rw [map_compl, inf_compl_eq_bot, map_bot]).le
  top_le_sup_compl a := ((map_sup _ _).trans <| by rw [map_compl, sup_compl_eq_top, map_top]).ge
  sdiff_eq a b := by
    refine hf ((map_sdiff _ _).trans (sdiff_eq.trans ?_))
    rw [map_inf, map_compl]
#align function.injective.boolean_algebra Function.Injective.booleanAlgebra

end lift

instance PUnit.instBooleanAlgebra : BooleanAlgebra PUnit := by
  refine'
  { PUnit.instBiheytingAlgebra with
    .. } <;> (intros; trivial)

namespace DistribLattice

variable (α : Type*) [DistribLattice α]

/--
An alternative constructor for boolean algebras:
a distributive lattice that is complemented is a boolean algebra.

This is not an instance, because it creates data using choice.
-/
noncomputable
def booleanAlgebraOfComplemented [BoundedOrder α] [ComplementedLattice α] : BooleanAlgebra α where
  __ := (inferInstanceAs (DistribLattice α))
  __ := (inferInstanceAs (BoundedOrder α))
  compl a := Classical.choose <| exists_isCompl a
  inf_compl_le_bot a := (Classical.choose_spec (exists_isCompl a)).disjoint.le_bot
  top_le_sup_compl a := (Classical.choose_spec (exists_isCompl a)).codisjoint.top_le

end DistribLattice
