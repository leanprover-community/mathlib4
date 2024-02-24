/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.EReal

/-!
# Half-planes in the complex plane

We show that the open left/right/lower/upper half-planes (with bound on the real or
imaginary part given by an `EReal`) are indeed open in the complex plane.
-/

namespace Complex

/-- An open left half plane in `ℂ` is open. -/
lemma isOpen_leftHalfPlane (x : EReal) : IsOpen {z : ℂ | z.re < x} :=
  isOpen_lt (EReal.continuous_coe_iff.mpr continuous_re) continuous_const

/-- An open right half plane in `ℂ` is open. -/
lemma isOpen_rightHalfPlane (x : EReal) : IsOpen {z : ℂ | x < z.re} :=
  isOpen_lt continuous_const <| EReal.continuous_coe_iff.mpr continuous_re

/-- An open lower half plane in `ℂ` is open. -/
lemma isOpen_lowerHalfPlane (x : EReal) : IsOpen {z : ℂ | z.im < x} :=
  isOpen_lt (EReal.continuous_coe_iff.mpr continuous_im) continuous_const

/-- An open upper half plane in `ℂ` is open. -/
lemma isOpen_upperHalfPlane (x : EReal) : IsOpen {z : ℂ | x < z.im} :=
  isOpen_lt continuous_const <| EReal.continuous_coe_iff.mpr continuous_im

end Complex
