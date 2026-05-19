/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon, Thomas Waring
-/
module

public import Mathlib.Data.PFun
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.Digraph.Basic

/-! # Typeclass for graph-like data -/

public section

open Prod Set

variable {V H I O E Gr : Type*}

class HyperGraphLike (V I O E : outParam Type*) (Gr : Type*) where
  verts : Gr → Set V
  edges : Gr → Set E
  input : Gr → I →. V × E
  output : Gr → O →. V × E
  ran_input_subset : ∀ ⦃G⦄, (input G).ran ⊆ verts G ×ˢ edges G
  ran_output_subset : ∀ ⦃G⦄, (output G).ran ⊆ verts G ×ˢ edges G
  eq_of_mem_input_of_mem_input : ∀ ⦃G i i' x e⦄,
      (x, e) ∈ input G i → (x, e) ∈ input G i' → i = i'
  eq_of_mem_output_of_mem_output : ∀ ⦃G o o' x e⦄,
      (x, e) ∈ output G o → (x, e) ∈ output G o' → o = o'

namespace HyperGraphLike

variable [HyperGraphLike V I O E Gr] {G : Gr}

@[expose]
def inFlags (G : Gr) : Set I := (input G).Dom

@[expose]
def outFlags (G : Gr) : Set O := (output G).Dom

@[expose]
def source (G : Gr) : I →. V := fun i => ⟨(input G i).Dom, fst ∘ (input G i).get⟩

@[expose]
def target (G : Gr) : O →. V := fun i => ⟨(output G i).Dom, fst ∘ (output G i).get⟩

@[expose]
def edgeIn (G : Gr) : I →. E := fun i => ⟨(input G i).Dom, snd ∘ (input G i).get⟩

@[expose]
def edgeOut (G : Gr) : O →. E := fun i => ⟨(output G i).Dom, snd ∘ (output G i).get⟩

lemma input_eq_source_edgeIn {G : Gr} {i : I} (hi : i ∈ inFlags G) :
    ⟨source G i |>.get hi, edgeIn G i |>.get hi⟩ = (input G i).get hi := by
  simp [source, edgeIn]

lemma output_eq_target_edgeOut {G : Gr} {o : O} (ho : o ∈ outFlags G) :
    ⟨target G o |>.get ho, edgeOut G o |>.get ho⟩ = (output G o).get ho := by
  simp [target, edgeOut]

lemma mem_verts_of_mem_source {v : V} {i : I} (h : v ∈ source G i) : v ∈ verts G := by
  obtain ⟨hi, h⟩ := h
  simp only [source, Function.comp_apply] at h
  exact h ▸ (ran_input_subset ⟨i, hi, rfl⟩).1

lemma mem_verts_of_mem_target {v : V} {o : O} (h : v ∈ target G o) : v ∈ verts G := by
  obtain ⟨ho, h⟩ := h
  simp only [target, Function.comp_apply] at h
  exact h ▸ (ran_output_subset ⟨o, ho, rfl⟩).1

lemma mem_edges_of_mem_edgeIn {e : E} {i : I} (h : e ∈ edgeIn G i) : e ∈ edges G := by
  obtain ⟨hi, h⟩ := h
  simp only [edgeIn, Function.comp_apply] at h
  exact h ▸ (ran_input_subset ⟨i, hi, rfl⟩).2

lemma mem_edges_of_mem_edgeOut {e : E} {o : O} (h : e ∈ edgeOut G o) : e ∈ edges G := by
  obtain ⟨ho, h⟩ := h
  simp only [edgeOut, Function.comp_apply] at h
  exact h ▸ (ran_output_subset ⟨o, ho, rfl⟩).2

def IsEdgeSource (G : Gr) (e : E) (v : V) : Prop := ⟨v, e⟩ ∈ (input G).ran

def IsEdgeTarget (G : Gr) (e : E) (v : V) : Prop := ⟨v, e⟩ ∈ (output G).ran

def IsLink (G : Gr) (e : E) (x y : V) : Prop := IsEdgeSource G e x ∧ IsEdgeTarget G e y

@[implicit_reducible]
def ofIsSourceIsTarget (verts : Gr → Set V) (edges : Gr → Set E)
    (IsEdgeSource : Gr → E → V → Prop) (IsEdgeTarget : Gr → E → V → Prop)
    (mem_verts_of_isEdgeSource : ∀ ⦃G e v⦄, IsEdgeSource G e v → v ∈ verts G)
    (mem_edges_of_isEdgeSource : ∀ ⦃G e v⦄, IsEdgeSource G e v → e ∈ edges G)
    (mem_verts_of_isEdgeTarget : ∀ ⦃G e v⦄, IsEdgeTarget G e v → v ∈ verts G)
    (mem_edges_of_isEdgeTarget : ∀ ⦃G e v⦄, IsEdgeTarget G e v → e ∈ edges G)
    : HyperGraphLike V (V × E) (V × E) E Gr where
  verts := verts
  edges := edges
  input G d := ⟨IsEdgeSource G d.2 d.1, fun _ => d⟩
  output G d := ⟨IsEdgeTarget G d.2 d.1, fun _ => d⟩
  ran_input_subset _ := by
    rintro ⟨v, e⟩ ⟨⟨v', e'⟩, hdom, rfl, _⟩
    exact ⟨mem_verts_of_isEdgeSource hdom, mem_edges_of_isEdgeSource hdom⟩
  ran_output_subset _ := by
    rintro ⟨v, e⟩ ⟨⟨v', e'⟩, hdom, rfl, _⟩
    exact ⟨mem_verts_of_isEdgeTarget hdom, mem_edges_of_isEdgeTarget hdom⟩
  eq_of_mem_input_of_mem_input := by simp_all
  eq_of_mem_output_of_mem_output := by simp_all

def Adj (G : Gr) (x y : V) : Prop := ∃ e, IsEdgeSource G e x ∧ IsEdgeTarget G e y

def FlagInc (G : Gr) (i : I) (o : O) : Prop := ∃ e, e ∈ edgeIn G i ∧ e ∈ edgeOut G o

lemma Adj.iff_exists_inFlags_outFlags {G : Gr} {x y : V} :
    Adj G x y ↔ ∃ i o, FlagInc G i o ∧ x ∈ source G i ∧ y ∈ target G o := by
  simp_rw [Adj, IsEdgeSource, IsEdgeTarget, FlagInc]
  constructor
  -- · intro ⟨e, o, ⟨i, hin, hxe⟩, ⟨o, hout, hye⟩⟩
  · intro ⟨e, ⟨i, hin, he⟩, ⟨o, hout, ho⟩⟩
    simp only [edgeIn, Part.mem_mk_iff, Function.comp_apply, edgeOut, exists_exists_eq_and, source,
      target]
    use! i, o, hin, hout, (by grind), hin, (by grind), (by grind)
  · rintro ⟨i, o, ⟨e, ⟨hin, rfl⟩, ⟨hout, heout⟩⟩, ⟨hin', rfl⟩, ⟨hout', rfl⟩⟩
    use (edgeIn G i).get hin
    constructor
    · use i, hin
      exact input_eq_source_edgeIn hin
    · use o, hout
      rw [←heout]
      exact (output_eq_target_edgeOut hout).symm

lemma FlagInc.mem_inFlags_left {i : I} {o : O} (h : FlagInc G i o) : i ∈ inFlags G := by
  obtain ⟨e, ⟨h, _⟩, _⟩ := h
  exact h

lemma FlagInc.mem_outFlags_right {i : I} {o : O} (h : FlagInc G i o) : o ∈ outFlags G := by
  obtain ⟨e, _, h, _⟩ := h
  exact h

lemma FlagInc.mem_edgeIn_iff_mem_edgeOut {i : I} {o : O} (h : FlagInc G i o) (e : E) :
    e ∈ edgeIn G i ↔ e ∈ edgeOut G o := by
  obtain ⟨e', hei, heo⟩ := h
  refine ⟨fun he => ?_, fun he => ?_⟩
  · rwa [Part.mem_unique he hei]
  · rwa [Part.mem_unique he heo]

lemma FlagInc.edgeIn_eq_edgeOut {i : I} {o : O} (h : FlagInc G i o) : edgeIn G i = edgeOut G o :=
    Part.ext h.mem_edgeIn_iff_mem_edgeOut

structure Dart (G : Gr) where
  i : I
  o : O
  inc : FlagInc G i o

namespace Dart

@[ext]
protected lemma ext {d d' : Dart G} (hi : d.i = d'.i) (ho : d.o = d'.o) : d = d' := by
  cases d; cases d'; congr

lemma mem_inFlags (d : Dart G) : d.i ∈ inFlags G := d.inc.mem_inFlags_left

lemma mem_outFlags (d : Dart G) : d.o ∈ outFlags G := d.inc.mem_outFlags_right

def src (d : Dart G) : V := (source G d.i).get d.mem_inFlags

lemma src_mem (d : Dart G) : d.src ∈ verts G :=
  mem_verts_of_mem_source (Part.get_mem _)

-- def isSource (d : Dart G) : IsSource G d.edge d.source := d.isLink.1

def tgt (d : Dart G) : V := (target G d.o).get d.mem_outFlags

lemma tgt_mem (d : Dart G) : d.tgt ∈ verts G :=
  mem_verts_of_mem_target (Part.get_mem _)

-- def isTarget (d : Dart G) : IsTarget G d.edge d.target := d.isLink.2

def edge (d : Dart G) : E := (edgeIn G d.i).get d.mem_inFlags

lemma edge_mem_edgeIn (d : Dart G) : d.edge ∈ edgeIn G d.i := Part.get_mem _

lemma edge_mem_edgeOut (d : Dart G) : d.edge ∈ edgeOut G d.o :=
  d.inc.mem_edgeIn_iff_mem_edgeOut _ |>.mp d.edge_mem_edgeIn

lemma isEdgeSource (d : Dart G) : IsEdgeSource G d.edge d.src := by
  refine ⟨d.i, d.mem_inFlags, ?_⟩
  simp [src, edge, input_eq_source_edgeIn]

lemma isEdgeTarget (d : Dart G) : IsEdgeTarget G d.edge d.tgt := by
  refine ⟨d.o, d.mem_outFlags, ?_⟩
  simp only [← output_eq_target_edgeOut, tgt, edge, d.inc.edgeIn_eq_edgeOut]

noncomputable def ofEdge {e : E} {x y : V} (hsrc : IsEdgeSource G e x) (htgt : IsEdgeTarget G e y) :
    Dart G where
  i := Classical.choose hsrc
  o := Classical.choose htgt
  inc := by
    have ⟨hin, hget⟩ := Classical.choose_spec hsrc
    have ⟨hout, hget'⟩ := Classical.choose_spec htgt
    refine ⟨e, ⟨hin, ?_⟩, ⟨hout, ?_⟩⟩
    · simp [edgeIn, hget]
    · simp [edgeOut, hget']

lemma ext_edge {d d' : Dart G} (hsrc : d.src = d'.src) (htgt : d.tgt = d'.tgt)
    (hedge : d.edge = d'.edge) : d = d' := by
  ext
  · apply eq_of_mem_input_of_mem_input (G := G) (x := d.src) (e := d.edge)
    all_goals simp_rw [Part.mem_eq, ←input_eq_source_edgeIn]
    · use d.mem_inFlags
      simpa using ⟨rfl, rfl⟩
    · use d'.mem_inFlags
      simpa [hsrc, hedge] using ⟨rfl, rfl⟩
  · apply eq_of_mem_output_of_mem_output (G := G) (x := d.tgt) (e := d.edge)
    all_goals simp_rw [Part.mem_eq, ←output_eq_target_edgeOut]
    · use d.mem_outFlags
      simpa [←d.inc.edgeIn_eq_edgeOut] using ⟨rfl, rfl⟩
    · use d'.mem_outFlags
      simpa [htgt, hedge, ←d'.inc.edgeIn_eq_edgeOut] using ⟨rfl, rfl⟩

lemma adj (d : Dart G) : Adj G d.src d.tgt := ⟨d.edge, d.isEdgeSource, d.isEdgeTarget⟩

def AdjDart (d d' : Dart G) : Prop := d.tgt = d'.src

end Dart

end HyperGraphLike

open HyperGraphLike

-- class UndirGraphLike (V I O E : outParam Type*) (Gr : Type*) extends
--     HyperGraphLike V I O E Gr where
--   exists_isLink_of_mem_edges : ∀ ⦃G e⦄, e ∈ edges G → ∃ x y, IsLink G e x y
--   eq_or_eq_of_isLink_of_isLink : ∀ ⦃G e x y x' y'⦄, IsLink (Gr := Gr) G e x y → IsLink G e x' y' →
--     x = x' ∧ y = y' ∨ x = y' ∧ y = x'

class DigraphLike (V I O E : outParam Type*) (Gr : Type*) extends
    HyperGraphLike V I O E Gr where
  exists_unique_mem_edgeIn_of_mem_edges : ∀ ⦃G e⦄, e ∈ edges G → ∃! i : I, e ∈ edgeIn G i
  exists_unique_mem_edgeOut_of_mem_edges : ∀ ⦃G e⦄, e ∈ edges G → ∃! o : O, e ∈ edgeOut G o

namespace DigraphLike

@[implicit_reducible]
def ofIsLink (verts : Gr → Set V) (edges : Gr → Set E)
    (IsLink : Gr → E → V → V → Prop)
    (mem_edges_iff_exists_isLink : ∀ ⦃G e⦄, e ∈ edges G ↔ ∃ x y, IsLink G e x y)
    (mem_verts_left_of_isLink : ∀ ⦃G e x y⦄, IsLink G e x y → x ∈ verts G)
    (mem_verts_right_of_isLink : ∀ ⦃G e x y⦄, IsLink G e x y → y ∈ verts G)
    (eq_and_eq_of_isLink_of_isLink : ∀ ⦃G e x x' y y'⦄,
      IsLink G e x y → IsLink G e x' y' → x = x' ∧ y = y') :
     DigraphLike V (V × E) (V × E) E Gr
    where
  verts := verts
  edges := edges
  input G d := ⟨∃ y, IsLink G d.2 d.1 y, fun _ => d⟩
  output G d := ⟨∃ x, IsLink G d.2 x d.1, fun _ => d⟩
  ran_input_subset G := by
    intro ⟨x, e⟩ ⟨⟨x', e'⟩, ⟨y, hlink⟩, heq⟩
    obtain ⟨rfl, rfl⟩ : x' = x ∧ e' = e := by simpa using heq
    exact ⟨mem_verts_left_of_isLink hlink, mem_edges_iff_exists_isLink.mpr ⟨x', y, hlink⟩⟩
  ran_output_subset G := by
    intro ⟨y, e⟩ ⟨⟨y', e'⟩, ⟨x, hlink⟩, heq⟩
    obtain ⟨rfl, rfl⟩ : y' = y ∧ e' = e := by simpa using heq
    exact ⟨mem_verts_right_of_isLink hlink, mem_edges_iff_exists_isLink.mpr ⟨x, y', hlink⟩⟩
  eq_of_mem_input_of_mem_input G := by simp; grind
  eq_of_mem_output_of_mem_output G := by simp; grind
  exists_unique_mem_edgeIn_of_mem_edges G e he := by
    obtain ⟨x, y, hlink⟩ := mem_edges_iff_exists_isLink.mp he
    use ⟨x, e⟩
    simp [edgeIn]
    grind
  exists_unique_mem_edgeOut_of_mem_edges G e he := by
    obtain ⟨x, y, hlink⟩ := mem_edges_iff_exists_isLink.mp he
    use ⟨y, e⟩
    simp [edgeOut]
    grind

@[implicit_reducible]
def ofSourceTarget (verts : Gr → Set V) (edges : Gr → Set E) (src : Gr → E → V) (tgt : Gr → E → V)
    (mem_verts_src : ∀ ⦃G e⦄, e ∈ edges G → src G e ∈ verts G)
    (mem_verts_tgt : ∀ ⦃G e⦄, e ∈ edges G → tgt G e ∈ verts G) :
    DigraphLike V (V × E) (V × E) E Gr where
  verts := verts
  edges := edges
  input G d := ⟨d.2 ∈ edges G ∧ src G d.2 = d.1, fun _ => d⟩
  output G d := ⟨d.2 ∈ edges G ∧ tgt G d.2 = d.1, fun _ => d⟩
  ran_input_subset G := by
    rintro ⟨x, e⟩ ⟨⟨x', e'⟩, ⟨hmem, h⟩, ⟨rfl, rfl⟩⟩
    exact ⟨h ▸ mem_verts_src hmem, hmem⟩
  ran_output_subset G := by
    rintro ⟨x, e⟩ ⟨⟨x', e'⟩, ⟨hmem, h⟩, ⟨rfl, rfl⟩⟩
    exact ⟨h ▸ mem_verts_tgt hmem, hmem⟩
  eq_of_mem_input_of_mem_input G := by
    intro ⟨x, e⟩ ⟨x', e'⟩ z f
    simp only [Part.mem_mk_iff, mk.injEq, exists_and_left, exists_prop, and_imp]
    rintro rfl _ rfl rfl rfl _ _ rfl
    exact ⟨rfl, rfl⟩
  eq_of_mem_output_of_mem_output G := by
    intro ⟨x, e⟩ ⟨x', e'⟩ z f
    simp only [Part.mem_mk_iff, mk.injEq, exists_and_left, exists_prop, and_imp]
    rintro rfl _ rfl rfl rfl _ _ rfl
    exact ⟨rfl, rfl⟩
  exists_unique_mem_edgeIn_of_mem_edges G := by
    intro e he
    apply existsUnique_of_exists_of_unique
    · use ⟨src G e, e⟩
      simpa [edgeIn]
    · rintro ⟨x, f⟩ ⟨x', f'⟩ ⟨⟨_, hx⟩, rfl⟩ ⟨⟨_, hx'⟩, h⟩
      simp_all [edgeIn]
      grind
  exists_unique_mem_edgeOut_of_mem_edges G := by
    intro e he
    apply existsUnique_of_exists_of_unique
    · use ⟨tgt G e, e⟩
      simpa [edgeOut]
    · rintro ⟨x, f⟩ ⟨x', f'⟩ ⟨⟨_, hx⟩, rfl⟩ ⟨⟨_, hx'⟩, h⟩
      simp_all [edgeOut]
      grind

variable [DigraphLike V I O E Gr] {G : Gr}

-- instance instGraphLike : GraphLike V I O E Gr where
--   exists_isLink_of_mem_edges G e he := by
--     obtain ⟨i, ⟨hi, heq⟩, _⟩ := exists_unique_mem_edgeIn_of_mem_edges he
--     obtain ⟨o, ⟨ho, heq'⟩, _⟩ := exists_unique_mem_edgeOut_of_mem_edges he
--     use (source G i).get hi, (target G o).get ho
--     refine ⟨⟨i, hi, ?_⟩, o, ho, ?_⟩
--       <;> grind [input_eq_source_edgeIn, output_eq_target_edgeOut]
--   eq_or_eq_of_isLink_of_isLink G e x y x' y' h h' := by
--     left
--     simp only [IsLink, IsEdgeSource, IsEdgeTarget] at h h'
--     obtain ⟨_, he⟩ := ran_input_subset h.1
--     obtain ⟨⟨i, hi, hxeq⟩, o, ho, hyeq⟩ := h
--     obtain ⟨⟨i', hi', hxeq'⟩, o', ho', hyeq'⟩ := h'
--     rw [←input_eq_source_edgeIn] at hxeq hxeq'
--     rw [←output_eq_target_edgeOut] at hyeq hyeq'
--     suffices i = i' ∧ o = o' by grind
--     refine ⟨ExistsUnique.unique (exists_unique_mem_edgeIn_of_mem_edges he) ?_ ?_,
--       ExistsUnique.unique (exists_unique_mem_edgeOut_of_mem_edges he) ?_ ?_⟩
--     all_goals
--       rw [Part.mem_eq]
--       use (by assumption)
--       grind

noncomputable def edgeInFlag {G : Gr} {e : E} (he : e ∈ edges G) : I :=
  Classical.choose (exists_unique_mem_edgeIn_of_mem_edges he)

lemma mem_edgeIn_iff (e : E) (i : I) : e ∈ edgeIn G i ↔ ∃ h : e ∈ edges G, edgeInFlag h = i := by
  simp_rw [edgeInFlag, ExistsUnique.choose_eq_iff]
  exact ⟨fun h => ⟨mem_edges_of_mem_edgeIn h, h⟩, fun ⟨_, h⟩ => h⟩

noncomputable def edgeOutFlag {G : Gr} {e : E} (he : e ∈ edges G) : O :=
  Classical.choose (exists_unique_mem_edgeOut_of_mem_edges he)

lemma mem_edgeOut_iff (e : E) (o : O) : e ∈ edgeOut G o ↔ ∃ h : e ∈ edges G, edgeOutFlag h = o := by
  simp_rw [edgeOutFlag, ExistsUnique.choose_eq_iff]
  exact ⟨fun h => ⟨mem_edges_of_mem_edgeOut h, h⟩, fun ⟨_, h⟩ => h⟩

protected class Simple (V I O E : outParam Type*) (Gr : Type*) [DigraphLike V I O E Gr] where
  eq_of_isLink_of_isLink : ∀ ⦃G e e' x y⦄, IsLink (Gr := Gr) G e x y → IsLink G e' x y → e = e'

end DigraphLike

open DigraphLike

-- class SimpleGraphLike (V I O E : outParam Type*) (Gr : Type*) extends
--     HyperGraphLike V I O E Gr where
--   eq_of_isLink_of_isLink : ∀ ⦃G e e' x y⦄, IsLink (Gr := Gr) G e x y → IsLink G e' x y → e = e'

class IrreflHyperGraphLike (V I O E : outParam Type*) (Gr : Type*) extends
    HyperGraphLike V I O E Gr where
  not_isSource_isTarget : ∀ ⦃G e x⦄, ¬ (IsEdgeSource (Gr := Gr) G e x ∧ IsEdgeTarget G e x)

class SymmHyperGraphLike (V I O E : outParam Type*) (Gr : Type*) extends
    HyperGraphLike V I O E Gr where
  swapIO : Gr → I →. O
  swapOI : Gr → O →. I
  dom_swapIO_eq : ∀ ⦃G⦄, (swapIO G).Dom = (input G).Dom
  dom_swapOI_eq : ∀ ⦃G⦄, (swapOI G).Dom = (output G).Dom
  inFlag_mem_comp : ∀ ⦃G i⦄, i ∈ (input G).Dom → i ∈ (swapOI G).comp (swapIO G) i
  outFlag_mem_comp : ∀ ⦃G o⦄, o ∈ (output G).Dom → o ∈ (swapIO G).comp (swapOI G) o
  edgeIn_eq_edgeOut_swapIO : ∀ ⦃G⦄, edgeIn G = (edgeOut G).comp (swapIO G)
  edgeOut_eq_edgeIn_swapOI : ∀ ⦃G⦄, edgeOut G = (edgeIn G).comp (swapOI G)

instance : DigraphLike V (V × V × V) (V × V × V) (V × V) (Digraph V) :=
  ofSourceTarget (Gr := Digraph V)
  (verts := fun _ => Set.univ) (edges := fun G => {p : V × V | G.Adj p.1 p.2})
  (src := fun _ => Prod.fst) (tgt := fun _ => Prod.snd)
  (mem_verts_src := fun _ _ _ => trivial) (mem_verts_tgt := fun _ _ _ => trivial)

instance : DigraphLike.Simple V (V × V × V) (V × V × V) (V × V) (Digraph V) where
  eq_of_isLink_of_isLink G e e' x y h h' := by
    simp [IsLink, IsEdgeSource, input, IsEdgeTarget, output, PFun.ran] at h h'
    grind

-- this is not quite right, bc `G.IsLink e x y` gives you `IsLink G e x x`
instance : HyperGraphLike V (V × E) (V × E) E (Graph V E) where
  verts := Graph.vertexSet
  edges := Graph.edgeSet
  input G d := ⟨∃ y, G.IsLink d.2 d.1 y, fun _ => d⟩
  output G d := ⟨∃ x, G.IsLink d.2 x d.1, fun _ => d⟩
  ran_input_subset G := by
    intro ⟨x, e⟩ ⟨⟨x', e'⟩, ⟨y, hlink⟩, heq⟩
    rw [mk.injEq] at heq
    exact ⟨heq.1 ▸ hlink.left_mem, heq.2 ▸ hlink.edge_mem⟩
  ran_output_subset G := by
    intro ⟨x, e⟩ ⟨⟨x', e'⟩, ⟨y, hlink⟩, heq⟩
    rw [mk.injEq] at heq
    exact ⟨heq.1 ▸ hlink.right_mem, heq.2 ▸ hlink.edge_mem⟩
  eq_of_mem_input_of_mem_input G := by
    intro ⟨x, e⟩ ⟨x', e'⟩ z f ⟨⟨y, hlink⟩, heq⟩ ⟨⟨y', hlink'⟩, heq'⟩
    simp_all
  eq_of_mem_output_of_mem_output G := by
    intro ⟨x, e⟩ ⟨x', e'⟩ z f ⟨⟨y, hlink⟩, heq⟩ ⟨⟨y', hlink'⟩, heq'⟩
    simp_all
  -- exists_isLink_of_mem_edges G e he := by
  --   obtain ⟨x, y, hlink⟩ := G.edge_mem_iff_exists_isLink e |>.mp he
  --   refine ⟨x, y, ?_, ?_⟩
  --   · use ⟨x, e⟩, ⟨y, hlink⟩
  --     rfl
  --   · use ⟨y, e⟩, ⟨x, hlink⟩
  --     rfl
  -- eq_or_eq_of_isLink_of_isLink G e x y x' y' h h' := by
  --   obtain ⟨⟨i, ⟨a, halink⟩, hi⟩, o, ⟨b, hblink⟩, ho⟩ := h
  --   obtain ⟨⟨i', ⟨a', halink'⟩, hi'⟩, o', ⟨b', hblink'⟩, ho'⟩ := h'
  --   subst_vars
  --   simp_all only
  --   sorry
    -- obtain (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) := halink.eq_and_eq_or_eq_and_eq halink'
    -- · obtain (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) := hblink.eq_and_eq_or_eq_and_eq hblink'
    --   · left; exact ⟨rfl, rfl⟩
    --   · obtain (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) := halink.eq_and_eq_or_eq_and_eq hblink
    -- obtain (rfl | rfl) := G.eq_or_eq_of_isLink_of_isLink halink hblink

    -- <;>  obtain (rfl | rfl) := G.eq_or_eq_of_isLink_of_isLink halink' hblink'
    -- <;>  obtain (rfl | rfl) := G.eq_or_eq_of_isLink_of_isLink halink hblink'
    -- · left; exact ⟨rfl, hblink.right_unique hblink'⟩
    -- · right; exact ⟨rfl, hblink.right_unique hblink'.symm⟩
    -- · obtain rfl := halink.right_unique hblink
    --   obtain rfl := hblink.right_unique hblink'
    --   sorry
    -- · sorry
    -- simp_all
    -- have h₁ := G.eq_or_eq_of_isLink_of_isLink halink' hblink
    -- have h₂ := G.eq_or_eq_of_isLink_of_isLink halink hblink'
    -- have h₃ := G.eq_or_eq_of_isLink_of_isLink halink' hblink'

    -- simp_all only
    -- obtain (rfl | rfl) := h₀
    --   <;> obtain (rfl | rfl) := h₁
    --   <;> obtain (rfl | rfl) := h₂
    --   <;> cases h₃

    -- obtain (rfl | rfl) := G.eq_or_eq_of_isLink_of_isLink halink hblink
    --   <;> obtain (rfl | rfl) := G.eq_or_eq_of_isLink_of_isLink halink' hblink'
    --   <;> obtain (rfl | rfl) := G.eq_or_eq_of_isLink_of_isLink halink hblink'
    --   <;> simp_all only


instance : SymmHyperGraphLike V (V × E) (V × E) E (Graph V E) where
  swapIO G d := ⟨(input G d).Dom, fun _ => d⟩
  swapOI G d := ⟨(output G d).Dom, fun _ => d⟩
  dom_swapIO_eq G := rfl
  dom_swapOI_eq G := rfl
  inFlag_mem_comp G := by
    intro ⟨x, e⟩ ⟨y, hlink⟩
    simp only [PFun.comp_apply, Part.mem_bind_iff, Part.mem_mk_iff, exists_prop,
      exists_eq_right_right, and_true]
    exact ⟨⟨y, hlink⟩, ⟨y, hlink.symm⟩⟩
  outFlag_mem_comp G := by
    intro ⟨x, e⟩ ⟨y, hlink⟩
    simp only [PFun.comp_apply, Part.mem_bind_iff, Part.mem_mk_iff, exists_prop,
      exists_eq_right_right, and_true]
    exact ⟨⟨y, hlink⟩, ⟨y, hlink.symm⟩⟩
  edgeIn_eq_edgeOut_swapIO G := by
    ext ⟨x, e⟩ e'
    simp only [edgeIn, input, Part.mem_mk_iff, Function.comp_apply, exists_prop, PFun.comp_apply,
      Part.mem_bind_iff, edgeOut, output, Prod.exists, mk.injEq, exists_eq_right_right,
      ↓existsAndEq, true_and, iff_self_and, and_imp, forall_exists_index]
    rintro y h rfl
    use y, h.symm
  edgeOut_eq_edgeIn_swapOI G := by
    ext ⟨x, e⟩ e'
    simp only [edgeOut, output, Part.mem_mk_iff, Function.comp_apply, exists_prop, PFun.comp_apply,
      Part.mem_bind_iff, edgeIn, input, Prod.exists, mk.injEq, exists_eq_right_right, ↓existsAndEq,
      true_and, iff_self_and, and_imp, forall_exists_index]
    intro y h rfl
    use y, h.symm

instance : HyperGraphLike V (V × V) (V × V) (Sym2 V) (SimpleGraph V) where
  verts _ := Set.univ
  edges G := G.edgeSet
  input G d := ⟨G.Adj d.1 d.2, fun _ => (d.1, .mk d.1 d.2)⟩
  output G d := ⟨G.Adj d.1 d.2, fun _ => (d.1, .mk d.1 d.2)⟩
  ran_input_subset G := by
    intro ⟨x, e⟩ ⟨⟨a, b⟩, hdom, h⟩
    simp_all only [mk.injEq, mem_prod, mem_univ, true_and]
    rw [←h.2, G.mem_edgeSet]
    exact hdom
  ran_output_subset G := by
    intro ⟨x, e⟩ ⟨⟨a, b⟩, hdom, h⟩
    simp_all only [mk.injEq, mem_prod, mem_univ, true_and]
    rw [←h.2, G.mem_edgeSet]
    exact hdom
  eq_of_mem_input_of_mem_input G := by
    intro ⟨x, y⟩ ⟨x', y'⟩ z e ⟨hdom, h⟩ ⟨hdom', h'⟩
    simp_all
    grind
  eq_of_mem_output_of_mem_output G := by
    intro ⟨x, y⟩ ⟨x', y'⟩ z e ⟨hdom, h⟩ ⟨hdom', h'⟩
    simp_all
    grind

instance : SymmHyperGraphLike V (V × V) (V × V) (Sym2 V) (SimpleGraph V) where
  swapIO G d := ⟨G.Adj d.1 d.2, fun _ => d.swap⟩
  swapOI G d := ⟨G.Adj d.1 d.2, fun _ => d.swap⟩
  dom_swapIO_eq G := rfl
  dom_swapOI_eq G := rfl
  inFlag_mem_comp G := by
    intro ⟨x, y⟩ (h : G.Adj x y)
    simp [h, h.symm]
  outFlag_mem_comp G := by
    intro ⟨x, y⟩ (h : G.Adj x y)
    simp [h, h.symm]
  edgeIn_eq_edgeOut_swapIO G := by
    ext ⟨x, y⟩ e
    simp [edgeIn, input, edgeOut, output]
    grind [G.adj_comm]
  edgeOut_eq_edgeIn_swapOI G := by
    ext ⟨x, y⟩ e
    simp [edgeIn, input, edgeOut, output]
    grind [G.adj_comm]

-- instance : IrreflHyperGraphLike V (V × V) (V × V) (Sym2 V) (SimpleGraph V) where
--   not_isSource_isTarget G := by
--     intro e x
--     simp [IsEdgeSource, input]

    -- simp only [IsSource, exists_and_left, ↓existsAndEq, true_and, IsTarget, exists_eq_left',
    --   not_and, and_imp]
    -- rintro rfl h rfl
    -- exact G.irrefl
