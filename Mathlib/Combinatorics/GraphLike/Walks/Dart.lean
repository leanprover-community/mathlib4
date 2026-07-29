/-
Copyright (c) 2026 Kyle Miller, Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Basic
public import Mathlib.Data.Sym.Sym2

/-!
# Darts in graph presentations

A `Dart` records a traversal of an edge from a source incidence to a distinct target incidence.
It is represented by the ordered pair of incidence identifiers; its edge, source vertex, and target
vertex are derived from the chosen presentation's incidence relation. This file defines darts and
proves some of their basic properties.
-/

public section

open Set

namespace HypergraphPresentation

variable {V I E Gr : Type*} {G : Gr} {Gₚ : HypergraphPresentation V I E G} {i j : I} {e : E}
  {u v : V}

/-- `Gₚ.IsTraversal u i e j v` means that the ordered pair of distinct incidences `i, j`
traverses the edge `e` from `u` to `v`. -/
def IsTraversal (Gₚ : HypergraphPresentation V I E G) (u : V) (i : I) (e : E) (j : I) (v : V) :
    Prop := i ≠ j ∧ Gₚ.IsSource i ∧ Gₚ.IsTarget j ∧ Gₚ.IsIncident i e u ∧ Gₚ.IsIncident j e v

namespace IsTraversal

@[grind .] lemma inc_ne (h : Gₚ.IsTraversal u i e j v) : i ≠ j := h.1

@[grind .]
lemma sourceInc_isSource (h : Gₚ.IsTraversal u i e j v) : Gₚ.IsSource i := h.2.1

@[grind .]
lemma targetInc_isTarget (h : Gₚ.IsTraversal u i e j v) : Gₚ.IsTarget j := h.2.2.1

lemma source_isIncident (h : Gₚ.IsTraversal u i e j v) : Gₚ.IsIncident i e u := h.2.2.2.1

lemma target_isIncident (h : Gₚ.IsTraversal u i e j v) : Gₚ.IsIncident j e v := h.2.2.2.2

@[grind .] lemma sourceInc_mem (h : Gₚ.IsTraversal u i e j v) : i ∈ I(Gₚ) :=
  h.sourceInc_isSource.mem

@[grind .] lemma targetInc_mem (h : Gₚ.IsTraversal u i e j v) : j ∈ I(Gₚ) :=
  h.targetInc_isTarget.mem

@[grind .] lemma edge_mem (h : Gₚ.IsTraversal u i e j v) : e ∈ E(Gₚ) :=
  h.source_isIncident.edge_mem

@[grind .] lemma source_mem (h : Gₚ.IsTraversal u i e j v) : u ∈ V(Gₚ) :=
  h.source_isIncident.vert_mem

@[grind →] lemma target_mem (h : Gₚ.IsTraversal u i e j v) : v ∈ V(Gₚ) :=
  h.target_isIncident.vert_mem

lemma isLink (h : Gₚ.IsTraversal u i e j v) : Gₚ.IsLink e u v := Gₚ.isLink_def.mpr
  ⟨i, j, h.inc_ne, h.sourceInc_isSource, h.targetInc_isTarget, h.source_isIncident,
    h.target_isIncident⟩

@[grind →] lemma adj (h : Gₚ.IsTraversal u i e j v) : Gₚ.Adj u v := h.isLink.adj

variable {e' : E} {u' v' : V}

/-- The ordered incidence identifiers of a traversal determine its edge and endpoints. -/
@[grind →]
lemma inj (h : Gₚ.IsTraversal u i e j v) (h' : Gₚ.IsTraversal u' i e' j v') :
    e = e' ∧ u = u' ∧ v = v' := by
  obtain ⟨he, hu⟩ := h.source_isIncident.inj h'.source_isIncident
  exact ⟨he, hu, (h.target_isIncident.inj h'.target_isIncident).2⟩

section Undirected

variable [Undirected Gₚ]

/-- Reverse a traversal in an undirected presentation. -/
@[symm]
lemma symm (h : Gₚ.IsTraversal u i e j v) : Gₚ.IsTraversal v j e i u :=
  ⟨h.inc_ne.symm, (isSource_iff Gₚ j).mpr h.targetInc_isTarget,
    (isSource_iff Gₚ i).mp h.sourceInc_isSource, h.target_isIncident, h.source_isIncident⟩

end Undirected

end IsTraversal

lemma isLink_iff_exists_isTraversal : Gₚ.IsLink e u v ↔ ∃ i j, Gₚ.IsTraversal u i e j v :=
  Gₚ.isLink_def (e := e) (u := u) (v := v)

lemma adj_iff_exists_isTraversal : Gₚ.Adj u v ↔ ∃ e i j, Gₚ.IsTraversal u i e j v :=
  Gₚ.adj_def (u := u) (v := v)

/-- The type of darts of a presentation. A dart consists of distinct source and target incidence
identifiers belonging to the same edge. -/
@[expose]
def Dart (Gₚ : HypergraphPresentation V I E G) :=
  {s : I × I // ∃ e u v, Gₚ.IsTraversal u s.1 e s.2 v}

namespace Dart

variable (d : Gₚ.Dart)

/-- The first incidence of a dart. -/
@[expose] def fst : I := d.val.fst

/-- The second incidence of a dart. -/
@[expose] def snd : I := d.val.snd

/-- The edge of a dart. -/
@[expose] noncomputable def edge : E := d.prop.choose

/-- The source of a dart. -/
@[expose] noncomputable def source : V := d.prop.choose_spec.choose

/-- The target of a dart. -/
@[expose] noncomputable def target : V := d.prop.choose_spec.choose_spec.choose

/-- The traversal certified by a dart. -/
lemma isTraversal : Gₚ.IsTraversal d.source d.fst d.edge d.snd d.target :=
  d.prop.choose_spec.choose_spec.choose_spec

@[grind .] lemma fst_ne_snd : d.fst ≠ d.snd := d.isTraversal.inc_ne

@[grind .] lemma fst_isSource : Gₚ.IsSource d.fst := d.isTraversal.sourceInc_isSource

@[grind .] lemma snd_isTarget : Gₚ.IsTarget d.snd := d.isTraversal.targetInc_isTarget

lemma source_isIncident : Gₚ.IsIncident d.fst d.edge d.source := d.isTraversal.source_isIncident

lemma target_isIncident : Gₚ.IsIncident d.snd d.edge d.target := d.isTraversal.target_isIncident

@[grind .] lemma fst_mem : d.fst ∈ I(Gₚ) := d.fst_isSource.mem

lemma edge_mem_edgeFun_fst : d.edge ∈ Gₚ.edgeFun d.fst :=
  d.source_isIncident.mem_edgeFun

@[grind .] lemma snd_mem : d.snd ∈ I(Gₚ) := d.snd_isTarget.mem

lemma edge_mem_edgeFun_snd : d.edge ∈ Gₚ.edgeFun d.snd :=
  d.target_isIncident.mem_edgeFun

@[grind .] lemma edge_mem : d.edge ∈ E(Gₚ) := d.source_isIncident.edge_mem

@[grind .] lemma source_mem : d.source ∈ V(Gₚ) := d.source_isIncident.vert_mem

@[grind .] lemma target_mem : d.target ∈ V(Gₚ) := d.target_isIncident.vert_mem

variable {d d₁ d₂ : Gₚ.Dart}

lemma edge_eq_of_isIncident_fst (h : Gₚ.IsIncident d.fst e v) : d.edge = e :=
  d.source_isIncident.inj h |>.1

lemma edge_eq_iff_source (d : Gₚ.Dart) : d.edge = e ↔ Gₚ.IsIncident d.fst e d.source :=
  ⟨(· ▸ d.source_isIncident), edge_eq_of_isIncident_fst⟩

lemma edge_eq_of_isIncident_snd (h : Gₚ.IsIncident d.snd e v) : d.edge = e :=
  d.target_isIncident.inj h |>.1

lemma edge_eq_iff_target (d : Gₚ.Dart) : d.edge = e ↔ Gₚ.IsIncident d.snd e d.target :=
  ⟨(· ▸ d.target_isIncident), edge_eq_of_isIncident_snd⟩

lemma source_eq_of_isIncident_fst (h : Gₚ.IsIncident d.fst e v) : d.source = v :=
  d.source_isIncident.inj h |>.2

lemma source_eq_iff (d : Gₚ.Dart) : d.source = v ↔ Gₚ.IsIncident d.fst d.edge v :=
  ⟨(· ▸ d.source_isIncident), source_eq_of_isIncident_fst⟩

lemma target_eq_of_isIncident_snd (h : Gₚ.IsIncident d.snd e v) : d.target = v :=
  d.target_isIncident.inj h |>.2

lemma target_eq_iff (d : Gₚ.Dart) : d.target = v ↔ Gₚ.IsIncident d.snd d.edge v :=
  ⟨(· ▸ d.target_isIncident), target_eq_of_isIncident_snd⟩

variable (h : Gₚ.IsTraversal u i e j v)

/-- Bundle a traversal as a dart. -/
@[expose]
def _root_.HypergraphPresentation.IsTraversal.toDart : Gₚ.Dart := ⟨(i, j), e, u, v, h⟩

@[simp, grind =]
lemma _root_.HypergraphPresentation.IsTraversal.toDart_fst : h.toDart.fst = i := rfl

@[simp, grind =]
lemma _root_.HypergraphPresentation.IsTraversal.toDart_snd : h.toDart.snd = j := rfl

@[simp, grind =]
lemma _root_.HypergraphPresentation.IsTraversal.toDart_edge : h.toDart.edge = e :=
  h.toDart.edge_eq_of_isIncident_fst h.source_isIncident

@[simp, grind =]
lemma _root_.HypergraphPresentation.IsTraversal.toDart_source : h.toDart.source = u :=
  h.toDart.source_eq_of_isIncident_fst h.source_isIncident

@[simp, grind =]
lemma _root_.HypergraphPresentation.IsTraversal.toDart_target : h.toDart.target = v :=
  h.toDart.target_eq_of_isIncident_snd h.target_isIncident

@[simp] lemma val_eq_iff : d.val = (i, j) ↔ d.fst = i ∧ d.snd = j := by grind [fst, snd]

@[ext]
lemma ext (hf : d₁.fst = d₂.fst) (hs : d₁.snd = d₂.snd) : d₁ = d₂ := Subtype.ext <| Prod.ext hf hs

@[simp]
lemma isTraversal_toDart (d : Gₚ.Dart) : d.isTraversal.toDart = d := by ext <;> simp

lemma _root_.HypergraphPresentation.isTraversal_iff_exists_dart :
    Gₚ.IsTraversal u i e j v ↔ ∃ d : Gₚ.Dart, d.fst = i ∧ d.snd = j ∧ d.edge = e ∧
      d.source = u ∧ d.target = v := by
  refine ⟨fun h ↦ ⟨h.toDart, by simp⟩, ?_⟩
  rintro ⟨d, rfl, rfl, rfl, rfl, rfl⟩
  exact d.isTraversal

lemma _root_.HypergraphPresentation.isLink_iff_exists_dart :
    Gₚ.IsLink e u v ↔ ∃ d : Gₚ.Dart, d.edge = e ∧ d.source = u ∧ d.target = v := by
  rw [isLink_iff_exists_isTraversal]
  refine ⟨fun ⟨i, j, h⟩ ↦ ⟨h.toDart, by simp⟩, ?_⟩
  rintro ⟨d, rfl, rfl, rfl⟩
  exact ⟨d.fst, d.snd, d.isTraversal⟩

lemma isLink (d : Gₚ.Dart) : Gₚ.IsLink d.edge d.source d.target := d.isTraversal.isLink

lemma _root_.HypergraphPresentation.adj_iff_exists_dart :
    Gₚ.Adj u v ↔ ∃ d : Gₚ.Dart, d.source = u ∧ d.target = v := by
  rw [adj_iff_exists_isTraversal]
  refine ⟨fun ⟨e, i, j, h⟩ ↦ ⟨h.toDart, by simp⟩, ?_⟩
  rintro ⟨d, rfl, rfl⟩
  exact ⟨d.edge, d.fst, d.snd, d.isTraversal⟩

@[grind .]
lemma adj (d : Gₚ.Dart) : Gₚ.Adj d.source d.target := d.isTraversal.adj

/-- The ordered pair consisting of the source and target vertices of a dart. -/
@[expose] noncomputable def toProd (d : Gₚ.Dart) : V × V := (d.source, d.target)

@[simp, grind =]
lemma toProd_eq_mk_iff (d : Gₚ.Dart) (u v : V) :
    d.toProd = (u, v) ↔ d.source = u ∧ d.target = v := by
  simp [toProd]

/-- The source and target vertices of a dart as an unordered pair. This is primarily useful for
undirected presentations. -/
@[expose] noncomputable def sym2 (d : Gₚ.Dart) : Sym2 V := s(d.source, d.target)

@[simp, grind =]
lemma sym2_eq_mk_iff : d.sym2 = s(u, v) ↔
    d.source = u ∧ d.target = v ∨ d.source = v ∧ d.target = u := by
  simp [sym2]

/-- Two darts are said to be adjacent if they could be consecutive darts in a walk -- that is, the
first dart's target is equal to the second dart's source. -/
@[expose] def _root_.HypergraphPresentation.DartAdj (d d' : Gₚ.Dart) : Prop := d.target = d'.source

instance [DecidableEq I] : DecidableEq (Gₚ.Dart) :=
  inferInstanceAs (DecidableEq (Subtype (α := I × I) _))

section GraphLike

variable [GraphLike Gₚ]

lemma edge_mem_edgeFun_iff_fst_or_snd (d : Gₚ.Dart) :
    ∀ (x : I), d.edge ∈ edgeFun Gₚ x ↔ x = d.fst ∨ x = d.snd := by
  obtain ⟨i, j, hne, h⟩ := exists_pair_mem_edgeFun_iff d.edge_mem
  grind [d.edge_mem_edgeFun_fst, d.edge_mem_edgeFun_snd]

lemma fst_or_snd_of_isIncident (h : Gₚ.IsIncident i d.edge v) : i = d.fst ∨ i = d.snd :=
  (d.edge_mem_edgeFun_iff_fst_or_snd i).mp h.mem_edgeFun

lemma eq_of_edge_source_eq [Loopless Gₚ] (he : d₁.edge = d₂.edge) (hs : d₁.source = d₂.source) :
    d₁ = d₂ := by
  have hfst : d₁.fst = d₂.fst := d₁.source_isIncident.inc_inj (he ▸ hs ▸ d₂.source_isIncident)
  obtain ⟨i, j, hij, hmem⟩ := exists_pair_mem_edgeFun_iff d₁.edge_mem
  apply Dart.ext hfst
  grind [d₁.edge_mem_edgeFun_fst, d₁.edge_mem_edgeFun_snd,
    he.symm ▸ d₂.edge_mem_edgeFun_fst, he.symm ▸ d₂.edge_mem_edgeFun_snd]

lemma edge_source_inj [Loopless Gₚ] : Function.Injective fun d : Gₚ.Dart ↦ (d.edge, d.source) :=
  fun _ _ h ↦ eq_of_edge_source_eq (congrArg Prod.fst h) (congrArg Prod.snd h)

end GraphLike

section Undirected

variable [Undirected Gₚ]

/-- The dart with reversed orientation from a given dart. -/
@[expose] def symm (d : Gₚ.Dart) : Gₚ.Dart :=
  ⟨d.val.swap, d.edge, d.target, d.source, d.isTraversal.symm⟩

@[simp, grind =]
lemma symm_fst (d : Gₚ.Dart) : d.symm.fst = d.snd := rfl

@[simp, grind =]
lemma symm_snd (d : Gₚ.Dart) : d.symm.snd = d.fst := rfl

@[simp, grind =]
lemma symm_edge (d : Gₚ.Dart) : d.symm.edge = d.edge :=
  d.edge_eq_of_isIncident_fst d.symm.target_isIncident |>.symm

@[simp, grind =]
lemma symm_source (d : Gₚ.Dart) : d.symm.source = d.target :=
  d.target_eq_of_isIncident_snd d.symm.source_isIncident |>.symm

@[simp, grind =]
lemma symm_target (d : Gₚ.Dart) : d.symm.target = d.source :=
  d.source_eq_of_isIncident_fst d.symm.target_isIncident |>.symm

@[simp, grind =]
lemma sym2_symm (d : Gₚ.Dart) : d.symm.sym2 = d.sym2 := by simp [sym2]

@[simp, grind =]
lemma symm_symm (d : Gₚ.Dart) : d.symm.symm = d := rfl

@[simp] lemma symm_involutive : Function.Involutive (symm : Gₚ.Dart → Gₚ.Dart) := symm_symm

lemma edge_eq_iff_of_undirected [GraphLike Gₚ] (d₁ d₂ : Gₚ.Dart) :
    d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁ = d₂.symm := by
  simp_rw [Dart.ext_iff, symm_fst, symm_snd]
  grind [fst_or_snd_of_isIncident, source_isIncident, target_isIncident]

end Undirected

section Directed

variable [Directed Gₚ]

lemma edge_eq_iff_of_directed [GraphLike Gₚ] (d₁ d₂ : Gₚ.Dart) : d₁.edge = d₂.edge ↔ d₁ = d₂ := by
  simp_rw [Dart.ext_iff]
  grind [fst_or_snd_of_isIncident, source_isIncident, target_isIncident]

end Directed

section NoParallelEdge

variable [GraphLike Gₚ] [NoParallelEdge Gₚ]

@[simp]
theorem sym2_eq_iff [Undirected Gₚ] (d₁ d₂ : Gₚ.Dart) :
    d₁.sym2 = d₂.sym2 ↔ d₁ = d₂ ∨ d₁ = d₂.symm := by
  simp only [sym2, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  refine ⟨?_, by rintro (rfl | rfl) <;> simp⟩
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact (edge_eq_iff_of_undirected d₁ d₂).mp <| d₁.isLink.edge_eq
      (h1 ▸ h2 ▸ d₂.isLink)
  have := (edge_eq_iff_of_undirected d₁ d₂.symm).mp <| d₁.isLink.edge_eq
    (by simpa [h1, h2] using d₂.symm.isLink)
  grind

lemma eq_of_source_target_eq_of_directed [Directed Gₚ] (hds : d₁.source = d₂.source)
    (hdt : d₁.target = d₂.target) : d₁ = d₂ :=
  (d₁.edge_eq_iff_of_directed d₂).mp <|
    d₁.isLink.edge_eq (hds ▸ hdt ▸ d₂.isLink)

lemma source_target_inj_of_directed [Directed Gₚ] :
    Function.Injective fun d : Gₚ.Dart ↦ (d.source, d.target) := by
  rintro d₁ d₂ h
  rw [Prod.mk.injEq] at h
  exact eq_of_source_target_eq_of_directed h.1 h.2

lemma eq_of_source_target_eq [Loopless Gₚ] (hds : d₁.source = d₂.source)
    (hdt : d₁.target = d₂.target) : d₁ = d₂ :=
  have := d₁.isLink.edge_eq (hds ▸ hdt ▸ d₂.isLink)
  ext (d₁.source_isIncident.inc_inj (hds ▸ this ▸ d₂.source_isIncident))
    (d₁.target_isIncident.inc_inj (hdt ▸ this ▸ d₂.target_isIncident))

lemma source_target_inj [Loopless Gₚ] :
    Function.Injective fun d : Gₚ.Dart ↦ (d.source, d.target) := by
  rintro d₁ d₂ h
  rw [Prod.mk.injEq] at h
  exact eq_of_source_target_eq h.1 h.2

end NoParallelEdge

end HypergraphPresentation.Dart
