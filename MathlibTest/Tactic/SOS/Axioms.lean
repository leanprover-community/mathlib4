/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.SOS.Verifier

/-- info: 'SOS.sos_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SOS.sos_sound

/-- info: 'SOS.sos_strict_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SOS.sos_strict_sound

/-- info: 'SOS.sos_strict_product_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SOS.sos_strict_product_sound

/-- info: 'SOS.sos_nonneg_refutation_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SOS.sos_nonneg_refutation_sound

/-- info: 'SOS.sos_infeasible_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SOS.sos_infeasible_sound

/-- info: 'CPoly.CMvPolynomial.toMvPolynomial_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CPoly.CMvPolynomial.toMvPolynomial_mul
