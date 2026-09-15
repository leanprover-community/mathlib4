/-
Copyright (c) 2026 Aaron Liu, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Junyan Xu
-/
module

public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Order.Lattice.Constructor

/-!
# `Associates` in a `GCDMonoid` form a lattice
-/

public section

variable (α : Type*) [CommMonoidWithZero α] (a b c : α)

section GCDMonoid

variable [GCDMonoid α]

/-- If `α` is a GCD monoid, then `α ⧸ αˣ` is distributive lattice with `lcm` as `⊔` and
`gcd` as `⊓`. This is not an instance to avoid conflict with `Associates.instLattice` for
`UniqueFactorizationMonoid`s. -/
abbrev Associates.distribLattice : DistribLattice (Associates α) :=
  let : Lattice (Associates α) :=
  { sup := lcm
    le_sup_left := dvd_lcm_left
    le_sup_right := dvd_lcm_right
    sup_le _ _ _ := lcm_dvd
    inf := gcd
    inf_le_left := gcd_dvd_left
    inf_le_right := gcd_dvd_right
    le_inf _ _ _ := dvd_gcd }
  .ofEqOfInfSupEq _ fun a b c inf_eq sup_eq ↦ by
    obtain rfl | hx := eq_or_ne a 0
    · simpa using inf_eq
    apply mul_left_cancel₀ hx
    grw [← associated_iff_eq, ← gcd_mul_lcm, ← gcd_mul_lcm a c]
    exact .of_eq congr($inf_eq * $sup_eq)

variable {α}

attribute [local instance] Associates.distribLattice

theorem associated_gcd_lcm_left : Associated (gcd a (lcm b c)) (lcm (gcd a b) (gcd a c)) :=
  Associates.mk_eq_mk_iff_associated.mp (inf_sup_left (Associates.mk a) (.mk b) (.mk c))

theorem associated_gcd_lcm_right : Associated (gcd (lcm a b) c) (lcm (gcd a c) (gcd b c)) :=
  Associates.mk_eq_mk_iff_associated.mp (inf_sup_right (Associates.mk a) (.mk b) (.mk c))

theorem associated_lcm_gcd_left : Associated (lcm a (gcd b c)) (gcd (lcm a b) (lcm a c)) :=
  Associates.mk_eq_mk_iff_associated.mp (sup_inf_left (Associates.mk a) (.mk b) (.mk c))

theorem associated_lcm_gcd_right : Associated (lcm (gcd a b) c) (gcd (lcm a c) (lcm b c)) :=
  Associates.mk_eq_mk_iff_associated.mp (sup_inf_right (Associates.mk a) (.mk b) (.mk c))

end GCDMonoid

section NormalizedGCDMonoid

variable {α} [NormalizedGCDMonoid α] {a b c : α}

theorem gcd_lcm_left : gcd a (lcm b c) = lcm (gcd a b) (gcd a c) :=
  (associated_gcd_lcm_left a b c).eq_of_normalized (normalize_gcd ..) (normalize_lcm ..)

theorem gcd_lcm_right : gcd (lcm a b) c = lcm (gcd a c) (gcd b c) :=
  (associated_gcd_lcm_right a b c).eq_of_normalized (normalize_gcd ..) (normalize_lcm ..)

theorem lcm_gcd_left : lcm a (gcd b c) = gcd (lcm a b) (lcm a c) :=
  (associated_lcm_gcd_left a b c).eq_of_normalized (normalize_lcm ..) (normalize_gcd ..)

theorem lcm_gcd_right : lcm (gcd a b) c = gcd (lcm a c) (lcm b c) :=
  (associated_lcm_gcd_right a b c).eq_of_normalized (normalize_lcm ..) (normalize_gcd ..)

end NormalizedGCDMonoid

namespace Nat

variable {a b c : ℕ}

protected theorem gcd_lcm_left : gcd a (lcm b c) = lcm (gcd a b) (gcd a c) := gcd_lcm_left
protected theorem gcd_lcm_right : gcd (lcm a b) c = lcm (gcd a c) (gcd b c) := gcd_lcm_right
protected theorem lcm_gcd_left : lcm a (gcd b c) = gcd (lcm a b) (lcm a c) := lcm_gcd_left
protected theorem lcm_gcd_right : lcm (gcd a b) c = gcd (lcm a c) (lcm b c) := lcm_gcd_right

end Nat
