/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Riccardo Brasca
-/

import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!

We gather results about the quotients of local rings.

-/

open Submodule

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [LocalRing R] [Module.Finite R S]

namespace LocalRing

local notation "p" => maximalIdeal R
local notation "pS" => Ideal.map (algebraMap R S) p

theorem quotient_span_eq_top_iff_span_eq_top (s : Set S) :
    span (R ⧸ p) ((Ideal.Quotient.mk (I := pS)) '' s) = ⊤ ↔ span R s = ⊤ := by
  have H : (span (R ⧸ p) ((Ideal.Quotient.mk (I := pS)) '' s)).restrictScalars R =
      (span R s).map (IsScalarTower.toAlgHom R S (S ⧸ pS)) := by
    rw [map_span, ← restrictScalars_span R (R ⧸ p) Ideal.Quotient.mk_surjective]
    rfl
  constructor
  · intro hs
    rw [← top_le_iff]
    apply le_of_le_smul_of_le_jacobson_bot
    · exact Module.finite_def.mp ‹_›
    · exact (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    · rw [Ideal.smul_top_eq_map]
      rintro x -
      have : LinearMap.ker (IsScalarTower.toAlgHom R S (S ⧸ pS)) =
          restrictScalars R pS := by
        ext; simp [Ideal.Quotient.eq_zero_iff_mem]
      rw [← this, ← comap_map_eq, mem_comap, ← H, hs]
      trivial
  · intro hs
    rw [hs, Submodule.map_top] at H
    change _ = LinearMap.range (Ideal.Quotient.mkₐ _ _) at H
    rwa [LinearMap.range_eq_top.mpr (Ideal.Quotient.mkₐ_surjective _ _),
      restrictScalars_eq_top_iff] at H

end LocalRing
