/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathlib.Algebra.Algebra.Nat
import Mathlib.RingTheory.Localization.Basic

/-!
# Results about localization explicitly using `Algebra ℕ R`

-/

variable {R : Type*} [CommRing R] {M : Submonoid R}

namespace Localization

theorem mk_natCast (m : ℕ) : (mk m 1 : Localization M) = m := by
  simpa using mk_algebraMap (R := R) (A := ℕ) _
#align localization.mk_nat_cast Localization.mk_natCast

@[deprecated (since := "2024-04-17")]
alias mk_nat_cast := mk_natCast


