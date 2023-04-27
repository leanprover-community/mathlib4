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

-- Porting note: we keep this instance local to avoid downstream effects.
-- I haven't been able to work out how to omit it or inline it into the the construction below.
-- The fact we need this issue is surely related to lean4#2074.
local instance {R : Type _} [CommRing R] : Module R R := eta_experiment% inferInstance

instance Ideal.Quotient.isNoetherianRing {R : Type _} [CommRing R] [h : IsNoetherianRing R]
    (I : Ideal R) : IsNoetherianRing (R ⧸ I) :=
  have : IsNoetherian R R := by simp_all only -- Porting note: this instance is needed
  isNoetherianRing_iff.mpr <| isNoetherian_of_tower R <| Submodule.Quotient.isNoetherian _
#align ideal.quotient.is_noetherian_ring Ideal.Quotient.isNoetherianRing
