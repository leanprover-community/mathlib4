/-
Copyright (c) 2026 Pablo Cohen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Cohen
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Lattice
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.IsOpenUnits

/-!
# Closures of two-sided ideals in topological rings

In this file we define `TwoSidedIdeal.closure` to be the topological closure of a two-sided
ideal in a topological ring, together with its basic API. This mirrors `Ideal.closure` for
one-sided ideals (see `Mathlib.Topology.Algebra.Ring.Ideal`), but works in the generality of
non-unital non-associative topological rings.

## Main definitions and results

* `TwoSidedIdeal.closure`: the topological closure of a two-sided ideal in a topological ring
  is a two-sided ideal.
* `TwoSidedIdeal.le_closure`: a two-sided ideal is contained in its closure.
* `TwoSidedIdeal.closure_minimal`: the closure of `I` is the smallest two-sided ideal with
  closed carrier containing `I`.
* `TwoSidedIdeal.closure_eq_of_isClosed`: a two-sided ideal with closed carrier equals its
  closure.
* `TwoSidedIdeal.closure_ne_top`: in a unital topological ring whose set of units is open
  (`IsOpenUnits`, e.g. a Banach algebra), the closure of a proper two-sided ideal is proper.
-/

@[expose] public section

open Topology

namespace TwoSidedIdeal

section NonUnitalNonAssocRing

variable {R : Type*} [TopologicalSpace R] [NonUnitalNonAssocRing R] [IsTopologicalRing R]

/-- Left-multiplication by `x` maps a two-sided ideal `I` into itself (as `Set.MapsTo`). -/
theorem mapsTo_mul_left (I : TwoSidedIdeal R) (x : R) :
    Set.MapsTo (fun b => x * b) (I : Set R) (I : Set R) :=
  fun _ ha => I.mul_mem_left _ _ ha

/-- Right-multiplication by `y` maps a two-sided ideal `I` into itself (as `Set.MapsTo`). -/
theorem mapsTo_mul_right (I : TwoSidedIdeal R) (y : R) :
    Set.MapsTo (fun b => b * y) (I : Set R) (I : Set R) :=
  fun _ ha => I.mul_mem_right _ _ ha

/-- The closure of a two-sided ideal in a topological ring as a two-sided ideal. -/
protected def closure (I : TwoSidedIdeal R) : TwoSidedIdeal R :=
  .mk' (closure (I : Set R))
    (subset_closure I.zero_mem)
    (fun hx hy => map_mem_closure₂ continuous_add hx hy fun _ ha _ hb => I.add_mem ha hb)
    (fun hx => map_mem_closure continuous_neg hx fun _ ha => I.neg_mem ha)
    (fun {x _} hy => (I.mapsTo_mul_left x).closure (continuous_const_mul x) hy)
    (fun {_ y} hx => (I.mapsTo_mul_right y).closure (continuous_mul_const y) hx)

@[simp]
theorem coe_closure (I : TwoSidedIdeal R) : (I.closure : Set R) = closure (I : Set R) := by
  simp [TwoSidedIdeal.closure]

theorem mem_closure_iff {I : TwoSidedIdeal R} {x : R} :
    x ∈ I.closure ↔ x ∈ closure (I : Set R) := by
  rw [← SetLike.mem_coe, coe_closure]

theorem le_closure (I : TwoSidedIdeal R) : I ≤ I.closure :=
  fun _ hx => mem_closure_iff.2 <| subset_closure hx

@[gcongr]
theorem closure_mono {I J : TwoSidedIdeal R} (h : I ≤ J) : I.closure ≤ J.closure :=
  fun _ hx => mem_closure_iff.2 <| _root_.closure_mono (le_iff.1 h) (mem_closure_iff.1 hx)

/-- The closure of a two-sided ideal `I` is the smallest two-sided ideal with closed carrier
containing `I`. -/
theorem closure_minimal {I J : TwoSidedIdeal R} (h : I ≤ J) (hJ : IsClosed (J : Set R)) :
    I.closure ≤ J :=
  fun _ hx => _root_.closure_minimal (le_iff.1 h) hJ (mem_closure_iff.1 hx)

protected instance isClosed_closure (I : TwoSidedIdeal R) : IsClosed (I.closure : Set R) :=
  I.coe_closure ▸ isClosed_closure

theorem closure_eq_of_isClosed (I : TwoSidedIdeal R) (hI : IsClosed (I : Set R)) :
    I.closure = I :=
  SetLike.ext' <| (coe_closure I).trans hI.closure_eq

@[simp]
theorem closure_closure (I : TwoSidedIdeal R) : I.closure.closure = I.closure :=
  closure_eq_of_isClosed _ I.isClosed_closure

@[simp]
theorem closure_top : (⊤ : TwoSidedIdeal R).closure = ⊤ :=
  eq_top_iff.2 <| le_closure ⊤

end NonUnitalNonAssocRing

section Ring

variable {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]

/-- In a unital topological ring whose set of units is open (`IsOpenUnits`, e.g. a Banach
algebra), the topological closure of a proper two-sided ideal is again proper. -/
theorem closure_ne_top [IsOpenUnits R] {I : TwoSidedIdeal R} (hI : I ≠ ⊤) :
    I.closure ≠ ⊤ := by
  have hu : IsOpen {x : R | IsUnit x} := by
    have h := (IsOpenUnits.isOpenEmbedding_unitsVal (M := R)).isOpen_range
    convert h using 1
    ext x
    exact ⟨fun ⟨u, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨u, hu⟩⟩
  have hsub : (I : Set R) ⊆ {x : R | IsUnit x}ᶜ := by
    rintro x hx ⟨u, rfl⟩
    exact hI <| eq_top _ <| by simpa using I.mul_mem_left (↑u⁻¹) _ hx
  intro h
  have h1 : (1 : R) ∈ closure (I : Set R) := by
    rw [← coe_closure, h]
    exact mem_top R
  exact _root_.closure_minimal hsub hu.isClosed_compl h1 isUnit_one

end Ring

end TwoSidedIdeal
