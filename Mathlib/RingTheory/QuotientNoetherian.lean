/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module ring_theory.quotient_noetherian
! leanprover-community/mathlib commit da420a8c6dd5bdfb85c4ced85c34388f633bc6ff
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.RingTheory.Noetherian
import Mathlib.RingTheory.QuotientNilpotent

/-!
# Noetherian quotient rings and quotient modules
-/

instance Ideal.Quotient.isNoetherianRing {R : Type} [CommRing R] [h : IsNoetherianRing R]
    (I : Ideal R) : IsNoetherianRing (R ⧸ I) := by
  apply isNoetherianRing_iff.mpr
  apply isNoetherian_of_tower R
  set_option synthInstance.etaExperiment true in
  apply Submodule.Quotient.isNoetherian I
#align ideal.quotient.is_noetherian_ring Ideal.Quotient.isNoetherianRing
