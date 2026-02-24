/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Bryan Gin-ge Chen
-/
module

public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Tactic.GRewrite

/-!
# Basic properties of Boolean algebras

This file provides some basic definitions, functions as well as lemmas for functions and type
classes related to Boolean algebras as defined in `Mathlib/Order/BooleanAlgebra/Defs.lean`.

## References

* <https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Generalizations>
* [*Postulates for Boolean Algebras and Generalized Boolean Algebras*, M.H. Stone][Stone1935]
* [*Lattice Theory: Foundation*, George Grätzer][Gratzer2011]

## Tags

generalized Boolean algebras, Boolean algebras, lattices, sdiff, compl

-/

@[expose] public section

universe u v

variable {α : Type u} {β : Type*} {x y z : α}

/-!
### Generalized Boolean algebras

Some of the lemmas in this section are from:

* [*Lattice Theory: Foundation*, George Grätzer][Gratzer2011]
* <https://ncatlab.org/nlab/show/relative+complement>
* <https://people.math.gatech.edu/~mccuan/courses/4317/symmetricdifference.pdf>

-/

-- We might want an `IsCompl_of` predicate (for relative complements) generalizing `IsCompl`,
-- however we'd need another type class for lattices with bot, and all the API for that.
section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α]

@[simp]
theorem sup_inf_sdiff (x y : α) : x ⊓ y ⊔ x \ y = x :=
  GeneralizedBooleanAlgebra.sup_inf_sdiff _ _

@[simp]
theorem inf_inf_sdiff (x y : α) : x ⊓ y ⊓ x \ y = ⊥ :=
  GeneralizedBooleanAlgebra.inf_inf_sdiff _ _

@[simp]
theorem sup_sdiff_inf (x y : α) : x \ y ⊔ x ⊓ y = x := by rw [sup_comm, sup_inf_sdiff]

@[simp]
theorem inf_sdiff_inf (x y : α) : x \ y ⊓ (x ⊓ y) = ⊥ := by rw [inf_comm, inf_inf_sdiff]

-- see Note [lower instance priority]
instance (priority := 100) GeneralizedBooleanAlgebra.toOrderBot : OrderBot α where
  __ := GeneralizedBooleanAlgebra.toBot
  bot_le a := by
    rw [← inf_inf_sdiff a a, inf_assoc]
    exact inf_le_left

theorem disjoint_inf_sdiff : Disjoint (x ⊓ y) (x \ y) :=
  disjoint_iff_inf_le.mpr (inf_inf_sdiff x y).le

-- TODO: in distributive lattices, relative complements are unique when they exist
theorem sdiff_unique (s : x ⊓ y ⊔ z = x) (i : x ⊓ y ⊓ z = ⊥) : x \ y = z := by
  conv_rhs at s => rw [← sup_inf_sdiff x y, sup_comm]
  rw [sup_comm] at s
  conv_rhs at i => rw [← inf_inf_sdiff x y, inf_comm]
  rw [inf_comm] at i
  exact (eq_of_inf_eq_sup_eq i s).symm

-- Use `sdiff_le`
private theorem sdiff_le' : x \ y ≤ x :=
  calc
    x \ y ≤ x ⊓ y ⊔ x \ y := le_sup_right
    _ = x := sup_inf_sdiff x y

set_option backward.privateInPublic true in
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
      ⊥ = x ⊓ (y ⊓ x ⊔ y \ x) ⊓ x \ y := by rw [← inf_inf_sdiff, sup_inf_sdiff]
      _ = (x ⊓ (y ⊓ x) ⊔ x ⊓ y \ x) ⊓ x \ y := by rw [inf_sup_left]
      _ = (y ⊓ (x ⊓ x) ⊔ x ⊓ y \ x) ⊓ x \ y := by ac_rfl
      _ = x ⊓ y \ x ⊓ x \ y := by
          rw [inf_idem, inf_sup_right, ← inf_comm x y, inf_inf_sdiff, bot_sup_eq]
      _ = x ⊓ x \ y ⊓ y \ x := by ac_rfl
      _ = x \ y ⊓ y \ x := by rw [inf_of_le_right sdiff_le']

theorem disjoint_sdiff_sdiff : Disjoint (x \ y) (y \ x) :=
  disjoint_iff_inf_le.mpr sdiff_inf_sdiff.le

@[simp]
theorem inf_sdiff_self_right : x ⊓ y \ x = ⊥ :=
  calc
    x ⊓ y \ x = (x ⊓ y ⊔ x \ y) ⊓ y \ x := by rw [sup_inf_sdiff]
    _ = ⊥ := by rw [inf_sup_right, inf_comm x y, inf_inf_sdiff, sdiff_inf_sdiff, bot_sup_eq]

@[simp]
theorem inf_sdiff_self_left : y \ x ⊓ x = ⊥ := by rw [inf_comm, inf_sdiff_self_right]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
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
          (by rw [inf_eq_right.mpr (le_sup_right.trans_eq (sup_inf_sdiff y x)),
                  inf_eq_right.mpr (h.trans le_sup_right)]))
        (calc
          y ⊔ y \ x = y := sup_eq_left.mpr (le_sup_right.trans_eq (sup_inf_sdiff y x))
          _ = y ⊓ x ⊔ y \ x := (sup_inf_sdiff y x).symm
          _ ≤ x ⊔ y \ x := sup_le_sup_right inf_le_right _
          _ ≤ x ⊔ z ⊔ y \ x := sup_le_sup_right le_sup_left _),
      fun h => le_of_inf_le_sup_le (inf_sdiff_self_left.trans_le bot_le) (calc
        y \ x ⊔ x = y ⊔ x := sdiff_sup_self'
        _ ≤ x ⊔ z ⊔ x := sup_le_sup_right h x
        _ ≤ z ⊔ x := by rw [sup_assoc, sup_comm, sup_assoc, sup_idem])⟩

theorem disjoint_sdiff_self_left : Disjoint (y \ x) x :=
  disjoint_iff_inf_le.mpr inf_sdiff_self_left.le

theorem disjoint_sdiff_self_right : Disjoint x (y \ x) :=
  disjoint_iff_inf_le.mpr inf_sdiff_self_right.le

lemma le_sdiff : x ≤ y \ z ↔ x ≤ y ∧ Disjoint x z :=
  ⟨fun h ↦ ⟨h.trans sdiff_le, disjoint_sdiff_self_left.mono_left h⟩, fun h ↦
    by rw [← h.2.sdiff_eq_left]; exact sdiff_le_sdiff_right h.1⟩

@[simp] lemma sdiff_eq_left : x \ y = x ↔ Disjoint x y :=
  ⟨fun h ↦ disjoint_sdiff_self_left.mono_left h.ge, Disjoint.sdiff_eq_left⟩

/- TODO: we could make an alternative constructor for `GeneralizedBooleanAlgebra` using
`Disjoint x (y \ x)` and `x ⊔ (y \ x) = y` as axioms. -/
theorem Disjoint.sdiff_eq_of_sup_eq (hi : Disjoint x z) (hs : x ⊔ z = y) : y \ x = z :=
  have h : y ⊓ x = x := inf_eq_right.2 <| le_sup_left.trans hs.le
  sdiff_unique (by rw [h, hs]) (by rw [h, hi.eq_bot])

protected theorem Disjoint.sdiff_unique (hd : Disjoint x z) (hz : z ≤ y) (hs : y ≤ x ⊔ z) :
    y \ x = z :=
  sdiff_unique
    (by
      rw [← inf_eq_right] at hs
      rwa [sup_inf_right, inf_sup_right, sup_comm x, inf_sup_self, inf_comm, sup_comm z,
        hs, sup_eq_left])
    (by rw [inf_assoc, hd.eq_bot, inf_bot_eq])

-- cf. `IsCompl.disjoint_left_iff` and `IsCompl.disjoint_right_iff`
theorem disjoint_sdiff_iff_le (hz : z ≤ y) (hx : x ≤ y) : Disjoint z (y \ x) ↔ z ≤ x :=
  ⟨fun H =>
    le_of_inf_le_sup_le (le_trans H.le_bot bot_le)
      (by
        rw [sup_sdiff_cancel_right hx]
        grw [sdiff_le]
        rw [sup_eq_right.2 hz]),
    fun H => disjoint_sdiff_self_right.mono_left H⟩

-- cf. `IsCompl.le_left_iff` and `IsCompl.le_right_iff`
theorem le_iff_disjoint_sdiff (hz : z ≤ y) (hx : x ≤ y) : z ≤ x ↔ Disjoint z (y \ x) :=
  (disjoint_sdiff_iff_le hz hx).symm

-- cf. `IsCompl.inf_left_eq_bot_iff` and `IsCompl.inf_right_eq_bot_iff`
theorem inf_sdiff_eq_bot_iff (hz : z ≤ y) (hx : x ≤ y) : z ⊓ y \ x = ⊥ ↔ z ≤ x := by
  rw [← disjoint_iff]
  exact disjoint_sdiff_iff_le hz hx

-- cf. `IsCompl.left_le_iff` and `IsCompl.right_le_iff`
theorem le_iff_eq_sup_sdiff (hz : z ≤ y) (hx : x ≤ y) : x ≤ z ↔ y = z ⊔ y \ x :=
  ⟨fun H => by
    apply le_antisymm
    · conv_lhs => rw [← sup_inf_sdiff y x]
      gcongr
      rwa [inf_eq_right.2 hx]
    · grw [hz]
      rw [sup_sdiff_left],
    fun H => by
    conv_lhs at H => rw [← sup_sdiff_cancel_right hx]
    refine le_of_inf_le_sup_le ?_ H.le
    rw [inf_sdiff_self_right]
    exact bot_le⟩

-- cf. `IsCompl.sup_inf`
theorem sdiff_sup : y \ (x ⊔ z) = y \ x ⊓ y \ z :=
  sdiff_unique
    (calc
      y ⊓ (x ⊔ z) ⊔ y \ x ⊓ y \ z = (y ⊓ x ⊔ y ⊓ z ⊔ y \ x) ⊓ (y ⊓ x ⊔ y ⊓ z ⊔ y \ z) := by
          rw [sup_inf_left, inf_sup_left y]
      _ = (y ⊓ z ⊔ (y ⊓ x ⊔ y \ x)) ⊓ (y ⊓ x ⊔ (y ⊓ z ⊔ y \ z)) := by ac_rfl
      _ = (y ⊓ z ⊔ y) ⊓ (y ⊓ x ⊔ y) := by rw [sup_inf_sdiff, sup_inf_sdiff]
      _ = (y ⊔ y ⊓ z) ⊓ (y ⊔ y ⊓ x) := by ac_rfl
      _ = y := by rw [sup_inf_self, sup_inf_self, inf_idem])
    (calc
      y ⊓ (x ⊔ z) ⊓ (y \ x ⊓ y \ z) = y ⊓ x ⊓ (y \ x ⊓ y \ z) ⊔ y ⊓ z ⊓ (y \ x ⊓ y \ z) := by
          rw [inf_sup_left, inf_sup_right]
      _ = y ⊓ x ⊓ y \ x ⊓ y \ z ⊔ y \ x ⊓ (y \ z ⊓ (y ⊓ z)) := by ac_rfl
      _ = ⊥ := by rw [inf_inf_sdiff, bot_inf_eq, bot_sup_eq, inf_comm (y \ z),
                      inf_inf_sdiff, inf_bot_eq])

theorem sdiff_eq_sdiff_iff_inf_eq_inf : y \ x = y \ z ↔ y ⊓ x = y ⊓ z :=
  ⟨fun h => eq_of_inf_eq_sup_eq (a := y \ x) (by rw [inf_inf_sdiff, h, inf_inf_sdiff])
    (by rw [sup_inf_sdiff, h, sup_inf_sdiff]),
    fun h => by rw [← sdiff_inf_self_right, ← sdiff_inf_self_right z y, inf_comm, h, inf_comm]⟩

theorem sdiff_eq_self_iff_disjoint : x \ y = x ↔ Disjoint y x := sdiff_eq_left.trans disjoint_comm

@[deprecated (since := "2025-10-12")] alias sdiff_eq_self_iff_disjoint' := sdiff_eq_left

theorem sdiff_lt (hx : y ≤ x) (hy : y ≠ ⊥) : x \ y < x := by
  refine sdiff_le.lt_of_ne fun h => hy ?_
  rw [sdiff_eq_left, disjoint_iff] at h
  rw [← h, inf_eq_right.mpr hx]

theorem sdiff_lt_left : x \ y < x ↔ ¬ Disjoint y x := by
  rw [lt_iff_le_and_ne, Ne, sdiff_eq_self_iff_disjoint, and_iff_right sdiff_le]

@[simp]
theorem le_sdiff_right : x ≤ y \ x ↔ x = ⊥ :=
  ⟨fun h => disjoint_self.1 (disjoint_sdiff_self_right.mono_right h), fun h => h.le.trans bot_le⟩

@[simp] lemma sdiff_eq_right : x \ y = y ↔ x = ⊥ ∧ y = ⊥ := by
  rw [disjoint_sdiff_self_left.eq_iff]; simp_all

lemma sdiff_ne_right : x \ y ≠ y ↔ x ≠ ⊥ ∨ y ≠ ⊥ := sdiff_eq_right.not.trans not_and_or

theorem sdiff_lt_sdiff_right (h : x < y) (hz : z ≤ x) : x \ z < y \ z :=
  (sdiff_le_sdiff_right h.le).lt_of_not_ge
    fun h' => h.not_ge <| le_sdiff_sup.trans <| sup_le_of_le_sdiff_right h' hz

theorem sup_inf_inf_sdiff : x ⊓ y ⊓ z ⊔ y \ z = x ⊓ y ⊔ y \ z := by
  rw [inf_assoc, sup_inf_right, sup_inf_sdiff, inf_sup_right, inf_sdiff_left]

theorem sdiff_sdiff_right : x \ (y \ z) = x \ y ⊔ x ⊓ y ⊓ z := by
  rw [sup_comm, inf_comm, ← inf_assoc, sup_inf_inf_sdiff]
  apply sdiff_unique
  · calc
      x ⊓ y \ z ⊔ (z ⊓ x ⊔ x \ y) = (x ⊔ (z ⊓ x ⊔ x \ y)) ⊓ (y \ z ⊔ (z ⊓ x ⊔ x \ y)) := by
          rw [sup_inf_right]
      _ = (x ⊔ x ⊓ z ⊔ x \ y) ⊓ (y \ z ⊔ (x ⊓ z ⊔ x \ y)) := by ac_rfl
      _ = x ⊓ (y \ z ⊔ (x ⊓ z ⊔ x ⊓ y) ⊔ x \ y) := by
          rw [sup_inf_self, sup_sdiff_left, ← sup_assoc, sup_inf_left, sdiff_sup_self',
            inf_sup_right, sup_comm y, inf_sdiff_sup_right, inf_sup_left x z y]
      _ = x ⊓ (y \ z ⊔ (x ⊓ z ⊔ (x ⊓ y ⊔ x \ y))) := by ac_rfl
      _ = x := by rw [sup_inf_sdiff, sup_comm (x ⊓ z), sup_inf_self, sup_comm, inf_sup_self]
  · calc
      x ⊓ y \ z ⊓ (z ⊓ x ⊔ x \ y) = x ⊓ y \ z ⊓ (z ⊓ x) ⊔ x ⊓ y \ z ⊓ x \ y := by rw [inf_sup_left]
      _ = x ⊓ (y \ z ⊓ z ⊓ x) ⊔ x ⊓ y \ z ⊓ x \ y := by ac_rfl
      _ = x ⊓ y \ z ⊓ x \ y := by rw [inf_sdiff_self_left, bot_inf_eq, inf_bot_eq, bot_sup_eq]
      _ = x ⊓ (y \ z ⊓ y) ⊓ x \ y := by conv_lhs => rw [← inf_sdiff_left]
      _ = x ⊓ (y \ z ⊓ (y ⊓ x \ y)) := by ac_rfl
      _ = ⊥ := by rw [inf_sdiff_self_right, inf_bot_eq, inf_bot_eq]

theorem sdiff_sdiff_right' : x \ (y \ z) = x \ y ⊔ x ⊓ z :=
  calc
    x \ (y \ z) = x \ y ⊔ x ⊓ y ⊓ z := sdiff_sdiff_right
    _ = z ⊓ x ⊓ y ⊔ x \ y := by ac_rfl
    _ = x \ y ⊔ x ⊓ z := by rw [sup_inf_inf_sdiff, sup_comm, inf_comm]

theorem sdiff_sdiff_eq_sdiff_sup (h : z ≤ x) : x \ (y \ z) = x \ y ⊔ z := by
  rw [sdiff_sdiff_right', inf_eq_right.2 h]

@[simp]
theorem sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y := by
  rw [sdiff_sdiff_right, inf_idem, sdiff_self, bot_sup_eq]

theorem sdiff_sdiff_eq_self (h : y ≤ x) : x \ (x \ y) = y := by
  rw [sdiff_sdiff_right_self, inf_of_le_right h]

theorem sdiff_eq_symm (hy : y ≤ x) (h : x \ y = z) : x \ z = y := by
  rw [← h, sdiff_sdiff_eq_self hy]

theorem sdiff_eq_comm (hy : y ≤ x) (hz : z ≤ x) : x \ y = z ↔ x \ z = y :=
  ⟨sdiff_eq_symm hy, sdiff_eq_symm hz⟩

theorem eq_of_sdiff_eq_sdiff (hxz : x ≤ z) (hyz : y ≤ z) (h : z \ x = z \ y) : x = y := by
  rw [← sdiff_sdiff_eq_self hxz, h, sdiff_sdiff_eq_self hyz]

theorem sdiff_le_sdiff_iff_le (hx : x ≤ z) (hy : y ≤ z) : z \ x ≤ z \ y ↔ y ≤ x := by
  refine ⟨fun h ↦ ?_, sdiff_le_sdiff_left⟩
  rw [← sdiff_sdiff_eq_self hx, ← sdiff_sdiff_eq_self hy]
  exact sdiff_le_sdiff_left h

theorem sdiff_sdiff_left' : (x \ y) \ z = x \ y ⊓ x \ z := by rw [sdiff_sdiff_left, sdiff_sup]

theorem sdiff_sdiff_sup_sdiff : z \ (x \ y ⊔ y \ x) = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x) :=
  calc
    z \ (x \ y ⊔ y \ x) = z ⊓ (z \ x ⊔ y) ⊓ (z ⊓ (z \ y ⊔ x)) := by
        rw [sdiff_sup, sdiff_sdiff_right, sdiff_sdiff_right, sup_inf_left, sup_comm, sup_inf_sdiff,
          sup_inf_left, sup_comm (z \ y), sup_inf_sdiff]
    _ = z ⊓ z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x) := by ac_rfl
    _ = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x) := by rw [inf_idem]

theorem sdiff_sdiff_sup_sdiff' : z \ (x \ y ⊔ y \ x) = z ⊓ x ⊓ y ⊔ z \ x ⊓ z \ y :=
  calc
    z \ (x \ y ⊔ y \ x) = z \ (x \ y) ⊓ z \ (y \ x) := sdiff_sup
    _ = (z \ x ⊔ z ⊓ x ⊓ y) ⊓ (z \ y ⊔ z ⊓ y ⊓ x) := by rw [sdiff_sdiff_right, sdiff_sdiff_right]
    _ = (z \ x ⊔ z ⊓ y ⊓ x) ⊓ (z \ y ⊔ z ⊓ y ⊓ x) := by ac_rfl
    _ = z \ x ⊓ z \ y ⊔ z ⊓ y ⊓ x := by rw [← sup_inf_right]
    _ = z ⊓ x ⊓ y ⊔ z \ x ⊓ z \ y := by ac_rfl

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
      _ = (x ⊓ y ⊓ (z ⊔ x) ⊔ x \ z) ⊓ (x ⊓ y ⊓ z ⊔ y \ z) := by
          rw [sup_inf_left, sup_inf_right, sup_sdiff_self_right, inf_sup_right, inf_sdiff_sup_right]
      _ = (y ⊓ (x ⊓ (x ⊔ z)) ⊔ x \ z) ⊓ (x ⊓ y ⊓ z ⊔ y \ z) := by ac_rfl
      _ = x ⊓ y ⊔ x \ z ⊓ y \ z := by rw [inf_sup_self, sup_inf_inf_sdiff, inf_comm y, sup_inf_left]
      _ = x ⊓ y := sup_eq_left.2 (inf_le_inf sdiff_le sdiff_le))
    (calc
      x ⊓ y ⊓ z ⊓ (x \ z ⊓ y \ z) = x ⊓ y ⊓ (z ⊓ x \ z) ⊓ y \ z := by ac_rfl
      _ = ⊥ := by rw [inf_sdiff_self_right, inf_bot_eq, bot_inf_eq])

/-- See also `sdiff_inf_right_comm`. -/
theorem inf_sdiff_assoc (x y z : α) : (x ⊓ y) \ z = x ⊓ y \ z :=
  sdiff_unique (by rw [inf_assoc, ← inf_sup_left, sup_inf_sdiff]) <| calc
    x ⊓ y ⊓ z ⊓ (x ⊓ y \ z) = x ⊓ x ⊓ (y ⊓ z ⊓ y \ z) := by ac_rfl
    _ = ⊥ := by rw [inf_inf_sdiff, inf_bot_eq]

/-- See also `inf_sdiff_assoc`. -/
theorem sdiff_inf_right_comm (x y z : α) : x \ z ⊓ y = (x ⊓ y) \ z := by
  rw [inf_comm x, inf_comm, inf_sdiff_assoc]

lemma inf_sdiff_left_comm (a b c : α) : a ⊓ (b \ c) = b ⊓ (a \ c) := by
  simp_rw [← inf_sdiff_assoc, inf_comm]

theorem inf_sdiff_distrib_left (a b c : α) : a ⊓ b \ c = (a ⊓ b) \ (a ⊓ c) := by
  rw [sdiff_inf, sdiff_eq_bot_iff.2 inf_le_left, bot_sup_eq, inf_sdiff_assoc]

theorem inf_sdiff_distrib_right (a b c : α) : a \ b ⊓ c = (a ⊓ c) \ (b ⊓ c) := by
  simp_rw [inf_comm _ c, inf_sdiff_distrib_left]

theorem disjoint_sdiff_comm : Disjoint (x \ z) y ↔ Disjoint x (y \ z) := by
  simp_rw [disjoint_iff, sdiff_inf_right_comm, inf_sdiff_assoc]

theorem sup_eq_sdiff_sup_sdiff_sup_inf : x ⊔ y = x \ y ⊔ y \ x ⊔ x ⊓ y :=
  Eq.symm <|
    calc
      x \ y ⊔ y \ x ⊔ x ⊓ y = (x \ y ⊔ y \ x ⊔ x) ⊓ (x \ y ⊔ y \ x ⊔ y) := by rw [sup_inf_left]
      _ = (x \ y ⊔ x ⊔ y \ x) ⊓ (x \ y ⊔ (y \ x ⊔ y)) := by ac_rfl
      _ = x ⊔ y := by simp

theorem sup_lt_of_lt_sdiff_left (h : y < z \ x) (hxz : x ≤ z) : x ⊔ y < z := by
  rw [← sup_sdiff_cancel_right hxz]
  refine (sup_le_sup_left h.le _).lt_of_not_ge fun h' => h.not_ge ?_
  rw [← sdiff_idem]
  exact (sdiff_le_sdiff_of_sup_le_sup_left h').trans sdiff_le

theorem sup_lt_of_lt_sdiff_right (h : x < z \ y) (hyz : y ≤ z) : x ⊔ y < z := by
  rw [← sdiff_sup_cancel hyz]
  refine lt_of_le_not_ge (by grw [h]) fun h' => h.not_ge ?_
  rw [← sdiff_idem]
  exact (sdiff_le_sdiff_of_sup_le_sup_right h').trans sdiff_le

instance Prod.instGeneralizedBooleanAlgebra [GeneralizedBooleanAlgebra β] :
    GeneralizedBooleanAlgebra (α × β) where
  sup_inf_sdiff _ _ := Prod.ext (sup_inf_sdiff _ _) (sup_inf_sdiff _ _)
  inf_inf_sdiff _ _ := Prod.ext (inf_inf_sdiff _ _) (inf_inf_sdiff _ _)

-- Porting note: Once `pi_instance` has been ported, this is just `by pi_instance`.
instance Pi.instGeneralizedBooleanAlgebra {ι : Type*} {α : ι → Type*}
    [∀ i, GeneralizedBooleanAlgebra (α i)] : GeneralizedBooleanAlgebra (∀ i, α i) where
  sup_inf_sdiff := fun f g => funext fun a => sup_inf_sdiff (f a) (g a)
  inf_inf_sdiff := fun f g => funext fun a => inf_inf_sdiff (f a) (g a)

end GeneralizedBooleanAlgebra


/-!
### Boolean algebras
-/
-- See note [reducible non-instances]
/-- A bounded generalized Boolean algebra is a Boolean algebra. -/
abbrev GeneralizedBooleanAlgebra.toBooleanAlgebra [GeneralizedBooleanAlgebra α] [OrderTop α] :
    BooleanAlgebra α where
  __ := ‹GeneralizedBooleanAlgebra α›
  __ := GeneralizedBooleanAlgebra.toOrderBot
  __ := ‹OrderTop α›
  compl a := ⊤ \ a
  inf_compl_le_bot _ := disjoint_sdiff_self_right.le_bot
  top_le_sup_compl _ := le_sup_sdiff
  sdiff_eq a b := by
    change _ = a ⊓ (⊤ \ b)
    rw [← inf_sdiff_assoc, inf_top_eq]

section BooleanAlgebra

variable [BooleanAlgebra α]

theorem inf_compl_eq_bot' : x ⊓ xᶜ = ⊥ :=
  bot_unique <| BooleanAlgebra.inf_compl_le_bot x

@[simp]
theorem sup_compl_eq_top : x ⊔ xᶜ = ⊤ :=
  top_unique <| BooleanAlgebra.top_le_sup_compl x

@[simp]
theorem compl_sup_eq_top : xᶜ ⊔ x = ⊤ := by rw [sup_comm, sup_compl_eq_top]

theorem isCompl_compl : IsCompl x xᶜ :=
  IsCompl.of_eq inf_compl_eq_bot' sup_compl_eq_top

theorem sdiff_eq : x \ y = x ⊓ yᶜ :=
  BooleanAlgebra.sdiff_eq x y

theorem himp_eq : x ⇨ y = y ⊔ xᶜ :=
  BooleanAlgebra.himp_eq x y

instance (priority := 100) BooleanAlgebra.toComplementedLattice : ComplementedLattice α :=
  ⟨fun x => ⟨xᶜ, isCompl_compl⟩⟩

-- see Note [lower instance priority]
instance (priority := 100) BooleanAlgebra.toGeneralizedBooleanAlgebra :
    GeneralizedBooleanAlgebra α where
  __ := ‹BooleanAlgebra α›
  sup_inf_sdiff a b := by rw [sdiff_eq, ← inf_sup_left, sup_compl_eq_top, inf_top_eq]
  inf_inf_sdiff a b := by
    rw [sdiff_eq, ← inf_inf_distrib_left, inf_compl_eq_bot', inf_bot_eq]

-- See note [lower instance priority]
instance (priority := 100) BooleanAlgebra.toBiheytingAlgebra : BiheytingAlgebra α where
  __ := ‹BooleanAlgebra α›
  __ := GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra
  hnot := compl
  le_himp_iff a b c := by rw [himp_eq, isCompl_compl.le_sup_right_iff_inf_left_le]
  himp_bot _ := _root_.himp_eq.trans (bot_sup_eq _)
  top_sdiff a := by rw [sdiff_eq, top_inf_eq]

@[simp]
theorem hnot_eq_compl : ￢x = xᶜ :=
  rfl

/- NOTE: Is this theorem needed at all or can we use `top_sdiff'`. -/
theorem top_sdiff : ⊤ \ x = xᶜ :=
  top_sdiff' x

theorem eq_compl_iff_isCompl : x = yᶜ ↔ IsCompl x y :=
  ⟨fun h => by
    rw [h]
    exact isCompl_compl.symm, IsCompl.eq_compl⟩

theorem compl_eq_iff_isCompl : xᶜ = y ↔ IsCompl x y :=
  ⟨fun h => by
    rw [← h]
    exact isCompl_compl, IsCompl.compl_eq⟩

theorem compl_eq_comm : xᶜ = y ↔ yᶜ = x := by
  rw [eq_comm, compl_eq_iff_isCompl, eq_compl_iff_isCompl]

theorem eq_compl_comm : x = yᶜ ↔ y = xᶜ := by
  rw [eq_comm, compl_eq_iff_isCompl, eq_compl_iff_isCompl]

@[simp]
theorem compl_compl (x : α) : xᶜᶜ = x :=
  (@isCompl_compl _ x _).symm.compl_eq

theorem compl_comp_compl : compl ∘ compl = @id α :=
  funext compl_compl

@[simp]
theorem compl_involutive : Function.Involutive (compl : α → α) :=
  compl_compl

theorem compl_bijective : Function.Bijective (compl : α → α) :=
  compl_involutive.bijective

theorem compl_surjective : Function.Surjective (compl : α → α) :=
  compl_involutive.surjective

theorem compl_injective : Function.Injective (compl : α → α) :=
  compl_involutive.injective

@[simp]
theorem compl_inj_iff : xᶜ = yᶜ ↔ x = y :=
  compl_injective.eq_iff

theorem IsCompl.compl_eq_iff (h : IsCompl x y) : zᶜ = y ↔ z = x :=
  h.compl_eq ▸ compl_inj_iff

@[simp]
theorem compl_eq_top : xᶜ = ⊤ ↔ x = ⊥ :=
  isCompl_bot_top.compl_eq_iff

@[simp]
theorem compl_eq_bot : xᶜ = ⊥ ↔ x = ⊤ :=
  isCompl_top_bot.compl_eq_iff

@[simp]
theorem compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ :=
  hnot_inf_distrib _ _

@[simp]
theorem compl_le_compl_iff_le : yᶜ ≤ xᶜ ↔ x ≤ y :=
  ⟨fun h => by have h := compl_le_compl h; simpa using h, compl_le_compl⟩

@[simp] lemma compl_lt_compl_iff_lt : yᶜ < xᶜ ↔ x < y :=
  lt_iff_lt_of_le_iff_le' compl_le_compl_iff_le compl_le_compl_iff_le

theorem compl_le_of_compl_le (h : yᶜ ≤ x) : xᶜ ≤ y := by
  simpa only [compl_compl] using compl_le_compl h

theorem compl_le_iff_compl_le : xᶜ ≤ y ↔ yᶜ ≤ x :=
  ⟨compl_le_of_compl_le, compl_le_of_compl_le⟩

@[simp] theorem compl_le_self : xᶜ ≤ x ↔ x = ⊤ := by simpa using le_compl_self (a := xᶜ)

@[simp] theorem compl_lt_self [Nontrivial α] : xᶜ < x ↔ x = ⊤ := by
  simpa using lt_compl_self (a := xᶜ)

@[simp]
theorem sdiff_compl : x \ yᶜ = x ⊓ y := by rw [sdiff_eq, compl_compl]

instance OrderDual.instBooleanAlgebra : BooleanAlgebra αᵒᵈ where
  __ := instDistribLattice α
  __ := instHeytingAlgebra
  sdiff_eq _ _ := @himp_eq α _ _ _
  himp_eq _ _ := @sdiff_eq α _ _ _
  inf_compl_le_bot a := (@codisjoint_hnot_right _ _ (ofDual a)).top_le
  top_le_sup_compl a := (@disjoint_compl_right _ _ (ofDual a)).le_bot

@[simp]
theorem sup_inf_inf_compl : x ⊓ y ⊔ x ⊓ yᶜ = x := by rw [← sdiff_eq, sup_inf_sdiff _ _]

theorem compl_sdiff : (x \ y)ᶜ = x ⇨ y := by
  rw [sdiff_eq, himp_eq, compl_inf, compl_compl, sup_comm]

@[simp]
theorem compl_himp : (x ⇨ y)ᶜ = x \ y :=
  @compl_sdiff αᵒᵈ _ _ _

theorem compl_sdiff_compl : xᶜ \ yᶜ = y \ x := by rw [sdiff_compl, sdiff_eq, inf_comm]

@[simp]
theorem compl_himp_compl : xᶜ ⇨ yᶜ = y ⇨ x :=
  @compl_sdiff_compl αᵒᵈ _ _ _

theorem disjoint_compl_left_iff : Disjoint xᶜ y ↔ y ≤ x := by
  rw [← le_compl_iff_disjoint_left, compl_compl]

theorem disjoint_compl_right_iff : Disjoint x yᶜ ↔ x ≤ y := by
  rw [← le_compl_iff_disjoint_right, compl_compl]

theorem codisjoint_himp_self_left : Codisjoint (x ⇨ y) x :=
  @disjoint_sdiff_self_left αᵒᵈ _ _ _

theorem codisjoint_himp_self_right : Codisjoint x (x ⇨ y) :=
  @disjoint_sdiff_self_right αᵒᵈ _ _ _

theorem himp_le : x ⇨ y ≤ z ↔ y ≤ z ∧ Codisjoint x z := by
  rw [himp_eq, sup_le_iff, and_congr_right_iff]
  exact fun _ => hnot_le_iff_codisjoint_right

@[simp] lemma himp_le_left : x ⇨ y ≤ x ↔ x = ⊤ :=
  ⟨fun h ↦ codisjoint_self.1 <| codisjoint_himp_self_right.mono_right h, fun h ↦ le_top.trans h.ge⟩

@[simp] lemma himp_eq_left : x ⇨ y = x ↔ x = ⊤ ∧ y = ⊤ := by
  rw [codisjoint_himp_self_left.eq_iff]; aesop

lemma himp_ne_right : x ⇨ y ≠ x ↔ x ≠ ⊤ ∨ y ≠ ⊤ := himp_eq_left.not.trans not_and_or

lemma codisjoint_iff_compl_le_left : Codisjoint x y ↔ yᶜ ≤ x :=
  hnot_le_iff_codisjoint_left.symm

lemma codisjoint_iff_compl_le_right : Codisjoint x y ↔ xᶜ ≤ y :=
  hnot_le_iff_codisjoint_right.symm

end BooleanAlgebra

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

section lift

-- See note [reducible non-instances]
/-- Pullback a `GeneralizedBooleanAlgebra` along an injection. -/
protected abbrev Function.Injective.generalizedBooleanAlgebra [Max α] [Min α]
    [LE α] [LT α] [Bot α] [SDiff α] [GeneralizedBooleanAlgebra β] (f : α → β) (hf : Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_bot : f ⊥ = ⊥) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    GeneralizedBooleanAlgebra α where
  __ := hf.generalizedCoheytingAlgebra f le lt map_sup map_inf map_bot map_sdiff
  __ := hf.distribLattice f le lt map_sup map_inf
  sup_inf_sdiff a b := hf <| by rw [map_sup, map_sdiff, map_inf, sup_inf_sdiff]
  inf_inf_sdiff a b := hf <| by rw [map_inf, map_sdiff, map_inf, inf_inf_sdiff, map_bot]

-- See note [reducible non-instances]
/-- Pullback a `BooleanAlgebra` along an injection. -/
protected abbrev Function.Injective.booleanAlgebra [Max α] [Min α] [LE α] [LT α] [Top α] [Bot α]
    [Compl α] [SDiff α] [HImp α] [BooleanAlgebra β] (f : α → β) (hf : Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_compl : ∀ a, f aᶜ = (f a)ᶜ)
    (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b) :
    BooleanAlgebra α where
  __ := hf.generalizedBooleanAlgebra f le lt map_sup map_inf map_bot map_sdiff
  le_top _ := le.1 <| (@le_top β _ _ _).trans map_top.ge
  bot_le _ := le.1 <| map_bot.le.trans bot_le
  inf_compl_le_bot a := le.1 ((map_inf _ _).trans <| by
    rw [map_compl, inf_compl_eq_bot, map_bot]).le
  top_le_sup_compl a := le.1 ((map_sup _ _).trans <| by
    rw [map_compl, sup_compl_eq_top, map_top]).ge
  sdiff_eq a b := hf <| (map_sdiff _ _).trans <| sdiff_eq.trans <| by rw [map_inf, map_compl]
  himp_eq a b := hf <| (map_himp _ _).trans <| himp_eq.trans <| by rw [map_sup, map_compl]

end lift
