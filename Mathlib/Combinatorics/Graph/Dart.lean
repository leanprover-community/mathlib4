/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Data.PFun
public import Mathlib.Data.Set.Card

/-!
# Darts in graphs

A `Dart` or half-edge or bond in a graph is an ordered pair of adjacent vertices, regarded as an
oriented edge. This file defines darts and proves some of their basic properties.

`DartStructure` provides the flexibility to use an arbitrary custom type as the type of darts for a
given graph. If a specific custom dart type is not desired or available, the file also includes a
built-in `DartType` which can be used as a default option for the darts of a graph.
-/

public section

open Set PFun Part Equiv

variable {V E D : Type*} {G H : Graph V E} {e : E} {d d' : D} {u v : V}

namespace Graph

structure DartStructure (G : Graph V E) (D : Type*) where
  fₑ : D →. E
  ran_fₑ : fₑ.ran = E(G)
  preimage_encard ⦃e : E⦄ : e ∈ E(G) → (fₑ.preimage {e}).encard = 2
  fᵥ : D →. V
  dom_fᵥ : fᵥ.Dom = fₑ.Dom
  ran_fᵥ : fᵥ.ran ⊆ V(G)
  inc_iff_exists_dart : ∀ e v, G.Inc e v ↔ ∃ d, e ∈ fₑ d ∧ v ∈ fᵥ d

initialize_simps_projections DartStructure (as_prefix fₑ, as_prefix ran_fₑ, as_prefix fᵥ,
  as_prefix dom_fᵥ, as_prefix ran_fᵥ)

namespace DartStructure

variable (M : DartStructure G D)

attribute [simp, grind =] ran_fₑ preimage_encard dom_fᵥ
attribute [simp, grind .] ran_fᵥ

lemma mem_edgeSet_of_mem_fₑ (hd : e ∈ M.fₑ d) : e ∈ E(G) := M.ran_fₑ ▸ ⟨d, hd⟩

lemma mem_vertexSet_of_mem_fᵥ (hd : v ∈ M.fᵥ d) : v ∈ V(G) := M.ran_fᵥ ⟨d, hd⟩

@[expose, simps]
def copy (M : DartStructure G D) (h : G = H) : DartStructure H D where
  fₑ := M.fₑ
  ran_fₑ := by simp [h]
  preimage_encard e he := M.preimage_encard (h ▸ he)
  fᵥ := M.fᵥ
  dom_fᵥ := M.dom_fᵥ
  ran_fᵥ := h ▸ M.ran_fᵥ
  inc_iff_exists_dart := h ▸ M.inc_iff_exists_dart

/-- A type of darts for a graph `G : Graph V E`. -/
inductive DartType (α β : Type*) : Type _ where
  | dir : β → ∀ (u v : α), u ≠ v → DartType α β
  | fwd : β → α → DartType α β
  | bwd : β → α → DartType α β

namespace DartType

@[expose]
def edge (d : DartType V E) : E :=
  match d with
  | .dir e _ _ _ => e
  | .fwd e _ => e
  | .bwd e _ => e

@[expose]
def source (d : DartType V E) : V :=
  match d with
  | .dir _ u _ _ => u
  | .fwd _ v => v
  | .bwd _ v => v

@[expose]
def target (d : DartType V E) : V :=
  match d with
  | .dir _ _ v _ => v
  | .fwd _ v => v
  | .bwd _ v => v

def dartStructure (G : Graph V E) : DartStructure G (DartType V E) where
  fₑ d := Part.mk (G.IsLink (edge d) (source d) (target d)) (fun _ ↦ edge d)
  ran_fₑ := by
    ext e
    simp only [ran, mem_mk_iff, exists_prop, mem_setOf_eq]
    refine ⟨fun ⟨d, hd, h⟩ => h ▸ hd.edge_mem, fun he => ?_⟩
    obtain ⟨u, v, he⟩ := G.exists_isLink_of_mem_edgeSet he
    obtain rfl | hne := eq_or_ne u v
    · exact ⟨.fwd e u, he, rfl⟩
    exact ⟨.dir e u v hne, he, rfl⟩
  preimage_encard e he := by
    obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet he
    obtain rfl | hne := eq_or_ne u v
    · suffices h : PFun.preimage (fun d ↦ ⟨G.IsLink d.edge d.source d.target, fun _ ↦ d.edge⟩) {e}
        = {DartType.fwd e u, DartType.bwd e u} by rw [h, Set.encard_pair (by simp)]
      ext d
      simp only [PFun.mem_preimage, mem_singleton_iff, mem_mk_iff, exists_prop, exists_eq_left,
        mem_insert_iff]
      refine ⟨?_, by rintro (rfl | rfl) <;> simpa [edge, source, target]⟩
      rintro ⟨hl, rfl⟩
      obtain ⟨hu, hv⟩ | ⟨hu, hv⟩ := huv.eq_and_eq_or_eq_and_eq hl <;>
        obtain ⟨e', u', v', huv'⟩ | ⟨e', w⟩ | ⟨e', w⟩ := d <;> grind [edge, source, target]
    suffices h : PFun.preimage (fun d ↦ ⟨G.IsLink d.edge d.source d.target, fun _ ↦ d.edge⟩) {e} =
      {DartType.dir e u v hne, DartType.dir e v u hne.symm} by
      rw [h, Set.encard_pair (by simp [hne])]
    ext d
    simp only [PFun.mem_preimage, mem_singleton_iff, mem_mk_iff, exists_prop, exists_eq_left,
      mem_insert_iff]
    refine ⟨?_, by rintro (rfl | rfl) <;> simp [edge, source, target, huv, huv.symm]⟩
    rintro ⟨hl, rfl⟩
    obtain ⟨hu, hv⟩ | ⟨hu, hv⟩ := huv.eq_and_eq_or_eq_and_eq hl <;>
      obtain ⟨e', u', v', huv'⟩ | ⟨e', w⟩ | ⟨e', w⟩ := d <;> grind [edge, source, target]
  fᵥ d := Part.mk (G.IsLink (edge d) (source d) (target d)) (fun _ ↦ source d)
  dom_fᵥ := by
    ext d
    simp [dom_mk]
  ran_fᵥ := by
    rintro v ⟨d, hv⟩
    obtain ⟨huv, rfl⟩ := hv
    exact huv.left_mem
  inc_iff_exists_dart e v := by
    refine ⟨fun ⟨w, hw⟩ ↦ ?_, fun ⟨d, ⟨huv, h1⟩, ⟨_, h2⟩⟩ ↦ h1 ▸ h2 ▸ huv.inc_left⟩
    obtain rfl | hne := eq_or_ne v w
    · exact ⟨.fwd e v, ⟨hw, rfl⟩, ⟨hw, rfl⟩⟩
    exact ⟨.dir e v w hne, ⟨hw, rfl⟩, ⟨hw, rfl⟩⟩

end DartType
end DartStructure

end Graph
