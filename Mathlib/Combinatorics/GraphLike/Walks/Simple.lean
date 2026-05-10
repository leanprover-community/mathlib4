/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Walks.Basic
public import Mathlib.Combinatorics.GraphLike.Symm

/-!
# Walks over α × α as dart type

In this file we prove lemmas for walks over graph-like without multi-edge, e.g. `SimpleGraph` and
`Digraph`.
-/

public section

open SymmGraphLike GraphLike

variable {V D E Gr : Type*} {G : Gr} {u v w : V} {d : D} {e : E} [noMultiEdgeSymmGraphLike V D E Gr]
  {u v w : V} {p : Walk G u v}

namespace GraphLike.Walk

theorem mem_darts_iff_infix_support {u' v'} (s : step G u' v') :
    ⟨s.val, s.prop.1⟩ ∈ p.darts ↔ [u', v'] <:+: p.support := by
  refine .trans ⟨fun h ↦ ?_, fun ⟨i, hi, h⟩ ↦ ?_⟩ List.infix_iff_getElem?.symm
  · have ⟨i, hi, h⟩ := List.getElem_of_mem h
    exact ⟨i, by grind, fun j hj ↦ by grind [src_darts_getElem, tgt_darts_getElem]⟩
  · have := h 0
    have := h 1
    obtain rfl := by
      refine Subsingleton.allEq s ⟨p.darts[i]'(by grind), Subtype.coe_prop _, ?_, ?_⟩
      <;> grind [src_darts_getElem, tgt_darts_getElem]
    exact p.darts.getElem_mem (n := i) (by grind)

theorem mem_darts_iff_fst_snd_infix_support (d : GraphLike.darts G) :
    d ∈ p.darts ↔ [src G d.val, tgt G d.val] <:+: p.support :=
  mem_darts_iff_infix_support ⟨d.val, d.prop, rfl, rfl⟩

end GraphLike.Walk
