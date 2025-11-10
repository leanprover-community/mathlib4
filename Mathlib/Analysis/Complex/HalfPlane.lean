/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Half-planes in ℂ are open

We state that open left, right, upper and lower half-planes in the complex numbers are open sets,
where the bounding value of the real or imaginary part is given by an `EReal` `x`.
So this includes the full plane and the empty set for `x = ⊤`/`x = ⊥`.
-/

namespace Complex

/-- An open left half-plane (with boundary real part given by an `EReal`) is an open set
in the complex plane. -/
lemma isOpen_re_lt_EReal (x : EReal) : IsOpen {z : ℂ | z.re < x} :=
  isOpen_lt (EReal.continuous_coe_iff.mpr continuous_re) continuous_const

/-- An open right half-plane (with boundary real part given by an `EReal`) is an open set
in the complex plane. -/
lemma isOpen_re_gt_EReal (x : EReal) : IsOpen {z : ℂ | x < z.re} :=
  isOpen_lt continuous_const <| EReal.continuous_coe_iff.mpr continuous_re

/-- An open lower half-plane (with boundary imaginary part given by an `EReal`) is an open set
in the complex plane. -/
lemma isOpen_im_lt_EReal (x : EReal) : IsOpen {z : ℂ | z.im < x} :=
  isOpen_lt (EReal.continuous_coe_iff.mpr continuous_im) continuous_const

/-- An open upper half-plane (with boundary imaginary part given by an `EReal`) is an open set
in the complex plane. -/
lemma isOpen_im_gt_EReal (x : EReal) : IsOpen {z : ℂ | x < z.im} :=
  isOpen_lt continuous_const <| EReal.continuous_coe_iff.mpr continuous_im

end Complex
