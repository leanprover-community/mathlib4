/-
Copyright (c) 2026 Kyle Miller, Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Basic
public import Mathlib.Data.Fintype.Sigma

/-!
# Darts in graphs

A `Dart` records a traversal of an edge from a source incidence to a distinct target incidence.
It is represented by the ordered pair of incidence identifiers; its edge, source vertex, and target
vertex are derived from the incidence relation. This file defines darts and proves some of their
basic properties.
-/

public section

open Set HyperGraphLike

namespace HyperGraphLike

variable {V I E Gr : Type*} {G : Gr} {i j : I} {e : E} {u v : V} [HyperGraphLike V I E Gr]

/-- `IsTraversal G u i e j v` means that the ordered pair of distinct incidences `i, j`
traverses the edge `e` from `u` to `v`. -/
def IsTraversal (G : Gr) (u : V) (i : I) (e : E) (j : I) (v : V) : Prop :=
  i ≠ j ∧ IsSource G i ∧ IsTarget G j ∧ IsIncident G i e u ∧ IsIncident G j e v

namespace IsTraversal

@[grind .] lemma inc_ne (h : IsTraversal G u i e j v) : i ≠ j := h.1

@[grind .]
lemma sourceInc_isSource (h : IsTraversal G u i e j v) : IsSource G i := h.2.1

@[grind .]
lemma targetInc_isTarget (h : IsTraversal G u i e j v) : IsTarget G j := h.2.2.1

lemma source_isIncident (h : IsTraversal G u i e j v) : IsIncident G i e u := h.2.2.2.1

lemma target_isIncident (h : IsTraversal G u i e j v) : IsIncident G j e v := h.2.2.2.2

@[grind .] lemma sourceInc_mem (h : IsTraversal G u i e j v) : i ∈ I(G) :=
  h.sourceInc_isSource.mem

@[grind .] lemma targetInc_mem (h : IsTraversal G u i e j v) : j ∈ I(G) :=
  h.targetInc_isTarget.mem

@[grind .] lemma edge_mem (h : IsTraversal G u i e j v) : e ∈ E(G) :=
  h.source_isIncident.edge_mem

@[grind .] lemma source_mem (h : IsTraversal G u i e j v) : u ∈ V(G) :=
  h.source_isIncident.vert_mem

@[grind .] lemma target_mem (h : IsTraversal G u i e j v) : v ∈ V(G) :=
  h.target_isIncident.vert_mem

lemma isLink (h : IsTraversal G u i e j v) : IsLink G e u v := isLink_def.mpr
  ⟨i, j, h.inc_ne, h.sourceInc_isSource, h.targetInc_isTarget, h.source_isIncident,
    h.target_isIncident⟩

@[grind .] lemma adj (h : IsTraversal G u i e j v) : Adj G u v := h.isLink.adj

variable {e' : E} {u' v' : V}

/-- The ordered incidence identifiers of a traversal determine its edge and endpoints. -/
@[grind →]
lemma inj (h : IsTraversal G u i e j v) (h' : IsTraversal G u' i e' j v') :
    e = e' ∧ u = u' ∧ v = v' := by
  obtain ⟨he, hu⟩ := h.source_isIncident.inj h'.source_isIncident
  exact ⟨he, hu, (h.target_isIncident.inj h'.target_isIncident).2⟩

section Undirected

variable [Undirected V I E Gr]

/-- Reverse a traversal in an undirected graph-like structure. -/
@[symm]
lemma symm (h : IsTraversal G u i e j v) : IsTraversal G v j e i u :=
  ⟨h.inc_ne.symm, (isSource_iff G j).mpr h.targetInc_isTarget,
    (isSource_iff G i).mp h.sourceInc_isSource, h.target_isIncident, h.source_isIncident⟩

end Undirected

end IsTraversal

lemma isLink_iff_exists_isTraversal :
    IsLink G e u v ↔ ∃ i j, IsTraversal G u i e j v := by
  rw [isLink_def]
  rfl

lemma adj_iff_exists_isTraversal :
    Adj G u v ↔ ∃ e i j, IsTraversal G u i e j v := by
  rw [adj_def]
  rfl

/-- The type of darts of a graph-like structure. A dart consists of distinct source and target
incidence identifiers belonging to the same edge. -/
@[expose]
def Dart (G : Gr) := {s : I × I // ∃ e u v, IsTraversal G u s.1 e s.2 v}

namespace Dart

variable (d : Dart G)

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
lemma isTraversal : IsTraversal G d.source d.fst d.edge d.snd d.target :=
  d.prop.choose_spec.choose_spec.choose_spec

@[grind .] lemma fst_ne_snd : d.fst ≠ d.snd := d.isTraversal.inc_ne

@[grind .] lemma fst_isSource : IsSource G d.fst := d.isTraversal.sourceInc_isSource

@[grind .] lemma snd_isTarget : IsTarget G d.snd := d.isTraversal.targetInc_isTarget

lemma source_isIncident : IsIncident G d.fst d.edge d.source := d.isTraversal.source_isIncident

lemma target_isIncident : IsIncident G d.snd d.edge d.target := d.isTraversal.target_isIncident

@[grind .] lemma fst_mem : d.fst ∈ I(G) := d.fst_isSource.mem

lemma edge_mem_edgeFun_fst : d.edge ∈ edgeFun G d.fst :=
  d.source_isIncident.mem_edgeFun

@[grind .] lemma snd_mem : d.snd ∈ I(G) := d.snd_isTarget.mem

lemma edge_mem_edgeFun_snd : d.edge ∈ edgeFun G d.snd :=
  d.target_isIncident.mem_edgeFun

@[grind .] lemma edge_mem : d.edge ∈ E(G) := d.source_isIncident.edge_mem

@[grind .] lemma source_mem : d.source ∈ V(G) := d.source_isIncident.vert_mem

@[grind .] lemma target_mem : d.target ∈ V(G) := d.target_isIncident.vert_mem

variable {d d₁ d₂ : Dart G}

lemma edge_eq_of_isIncident_fst (h : IsIncident G d.fst e v) : d.edge = e :=
  d.source_isIncident.inj h |>.1

lemma edge_eq_iff_source (d : Dart G) : d.edge = e ↔ IsIncident G d.fst e d.source :=
  ⟨(· ▸ d.source_isIncident), edge_eq_of_isIncident_fst⟩

lemma edge_eq_of_isIncident_snd (h : IsIncident G d.snd e v) : d.edge = e :=
  d.target_isIncident.inj h |>.1

lemma edge_eq_iff_target (d : Dart G) : d.edge = e ↔ IsIncident G d.snd e d.target :=
  ⟨(· ▸ d.target_isIncident), edge_eq_of_isIncident_snd⟩

lemma source_eq_of_isIncident_fst (h : IsIncident G d.fst e v) : d.source = v :=
  d.source_isIncident.inj h |>.2

lemma source_eq_iff (d : Dart G) : d.source = v ↔ IsIncident G d.fst d.edge v :=
  ⟨(· ▸ d.source_isIncident), source_eq_of_isIncident_fst⟩

lemma target_eq_of_isIncident_snd (h : IsIncident G d.snd e v) : d.target = v :=
  d.target_isIncident.inj h |>.2

lemma target_eq_iff (d : Dart G) : d.target = v ↔ IsIncident G d.snd d.edge v :=
  ⟨(· ▸ d.target_isIncident), target_eq_of_isIncident_snd⟩

variable (h : IsTraversal G u i e j v)

/-- Bundle a traversal as a dart. -/
@[expose]
def _root_.HyperGraphLike.IsTraversal.toDart : Dart G := ⟨(i, j), e, u, v, h⟩

@[simp, grind =]
lemma _root_.HyperGraphLike.IsTraversal.toDart_fst : h.toDart.fst = i := rfl

@[simp, grind =]
lemma _root_.HyperGraphLike.IsTraversal.toDart_snd : h.toDart.snd = j := rfl

@[simp, grind =]
lemma _root_.HyperGraphLike.IsTraversal.toDart_edge : h.toDart.edge = e :=
  h.toDart.edge_eq_of_isIncident_fst h.source_isIncident

@[simp, grind =]
lemma _root_.HyperGraphLike.IsTraversal.toDart_source : h.toDart.source = u :=
  h.toDart.source_eq_of_isIncident_fst h.source_isIncident

@[simp, grind =]
lemma _root_.HyperGraphLike.IsTraversal.toDart_target : h.toDart.target = v :=
  h.toDart.target_eq_of_isIncident_snd h.target_isIncident

@[simp] lemma val_eq_iff : d.val = (i, j) ↔ d.fst = i ∧ d.snd = j := by grind [fst, snd]

@[ext]
lemma ext (hf : d₁.fst = d₂.fst) (hs : d₁.snd = d₂.snd) : d₁ = d₂ := Subtype.ext <| Prod.ext hf hs

@[simp]
lemma isTraversal_toDart (d : Dart G) : d.isTraversal.toDart = d := by ext <;> simp

lemma _root_.HyperGraphLike.isTraversal_iff_exists_dart :
    IsTraversal G u i e j v ↔ ∃ d : Dart G, d.fst = i ∧ d.snd = j ∧ d.edge = e ∧
      d.source = u ∧ d.target = v := by
  refine ⟨fun h ↦ ⟨h.toDart, by simp⟩, ?_⟩
  rintro ⟨d, rfl, rfl, rfl, rfl, rfl⟩
  exact d.isTraversal

lemma _root_.HyperGraphLike.isLink_iff_exists_dart :
    IsLink G e u v ↔ ∃ d : Dart G, d.edge = e ∧ d.source = u ∧ d.target = v := by
  rw [isLink_iff_exists_isTraversal]
  constructor
  · rintro ⟨i, j, h⟩
    exact ⟨h.toDart, by simp⟩
  · rintro ⟨d, rfl, rfl, rfl⟩
    exact ⟨d.fst, d.snd, d.isTraversal⟩

lemma IsLink (d : Dart G) : IsLink G d.edge d.source d.target := d.isTraversal.isLink

lemma _root_.HyperGraphLike.adj_iff_exists_dart :
    Adj G u v ↔ ∃ d : Dart G, d.source = u ∧ d.target = v := by
  rw [adj_iff_exists_isTraversal]
  constructor
  · rintro ⟨e, i, j, h⟩
    exact ⟨h.toDart, by simp⟩
  · rintro ⟨d, rfl, rfl⟩
    exact ⟨d.edge, d.fst, d.snd, d.isTraversal⟩

@[grind .]
lemma Adj (d : Dart G) : Adj G d.source d.target := d.isTraversal.adj

/-- The ordered pair consisting of the source and target vertices of a dart. -/
@[expose] noncomputable def toProd (d : Dart G) : V × V := (d.source, d.target)

@[simp, grind =]
lemma toProd_eq_mk_iff (d : Dart G) (u v : V) :
    d.toProd = (u, v) ↔ d.source = u ∧ d.target = v := by
  simp [toProd]

/-- The source and target vertices of a dart as an unordered pair. This is primarily useful for
undirected graph-like structures. -/
@[expose] noncomputable def sym2 (d : Dart G) : Sym2 V := s(d.source, d.target)

@[simp, grind =]
lemma sym2_eq_mk_iff : d.sym2 = s(u, v) ↔
    d.source = u ∧ d.target = v ∨ d.source = v ∧ d.target = u := by
  simp [sym2]

/-- Two darts are said to be adjacent if they could be consecutive darts in a walk -- that is, the
first dart's target is equal to the second dart's source. -/
@[expose] def _root_.HyperGraphLike.DartAdj (d d' : Dart G) : Prop := d.target = d'.source

instance [DecidableEq I] : DecidableEq (Dart G) :=
  inferInstanceAs (DecidableEq (Subtype (α := I × I) _))

section GraphLike

variable [GraphLike V I E Gr]

lemma edge_mem_edgeFun_iff_fst_or_snd (d : Dart G) :
    ∀ (x : I), d.edge ∈ edgeFun G x ↔ x = d.fst ∨ x = d.snd := by
  obtain ⟨i, j, hne, h⟩ := exists_pair_mem_edgeFun_iff d.edge_mem
  grind [d.edge_mem_edgeFun_fst, d.edge_mem_edgeFun_snd]

lemma fst_or_snd_of_isIncident (d : Dart G) (h : IsIncident G i d.edge v) :
    i = d.fst ∨ i = d.snd := (d.edge_mem_edgeFun_iff_fst_or_snd i).mp h.mem_edgeFun

lemma eq_of_edge_source_eq [Loopless V I E Gr] (he : d₁.edge = d₂.edge)
    (hs : d₁.source = d₂.source) : d₁ = d₂ := by
  have hfst : d₁.fst = d₂.fst :=
    d₁.source_isIncident.inc_inj (he ▸ hs ▸ d₂.source_isIncident)
  obtain ⟨i, j, hij, hmem⟩ := exists_pair_mem_edgeFun_iff d₁.edge_mem
  apply Dart.ext hfst
  grind [d₁.edge_mem_edgeFun_fst, d₁.edge_mem_edgeFun_snd,
    he.symm ▸ d₂.edge_mem_edgeFun_fst, he.symm ▸ d₂.edge_mem_edgeFun_snd]

lemma edge_source_inj [Loopless V I E Gr] :
    Function.Injective fun d : Dart G ↦ (d.edge, d.source) := by
  rintro d₁ d₂ h
  exact eq_of_edge_source_eq (congrArg Prod.fst h) (congrArg Prod.snd h)

end GraphLike

section Undirected

variable [Undirected V I E Gr]

lemma Adj' (d : Dart G) : HyperGraphLike.Adj G d.target d.source := d.Adj.symm

/-- The dart with reversed orientation from a given dart. -/
@[expose] def symm (d : Dart G) : Dart G :=
  ⟨d.val.swap, d.edge, d.target, d.source, d.isTraversal.symm⟩

@[simp, grind =]
lemma symm_fst (d : Dart G) : (d.symm).fst = d.snd := by rfl

@[simp, grind =]
lemma symm_snd (d : Dart G) : (d.symm).snd = d.fst := by rfl

@[simp, grind =]
lemma symm_edge (d : Dart G) : (d.symm).edge = d.edge :=
  d.edge_eq_of_isIncident_fst d.symm.target_isIncident |>.symm

@[simp, grind =]
lemma symm_source (d : Dart G) : (d.symm).source = d.target :=
  d.target_eq_of_isIncident_snd d.symm.source_isIncident |>.symm

@[simp, grind =]
lemma symm_target (d : Dart G) : (d.symm).target = d.source :=
  d.source_eq_of_isIncident_fst d.symm.target_isIncident |>.symm

@[simp, grind =]
lemma sym2_symm (d : Dart G) : (d.symm).sym2 = d.sym2 := by simp [sym2]

@[simp, grind =]
lemma symm_symm (d : Dart G) : (d.symm).symm = d := rfl

@[simp] lemma symm_involutive : Function.Involutive (symm : Dart G → Dart G) := symm_symm

lemma edge_eq_iff_of_undirected [GraphLike V I E Gr] (d₁ d₂ : Dart G) :
    d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁ = d₂.symm := by
  simp_rw [Dart.ext_iff, symm_fst, symm_snd]
  grind [fst_or_snd_of_isIncident, source_isIncident, target_isIncident]

end Undirected

section Directed

variable [Directed V I E Gr]

lemma edge_eq_iff_of_directed [GraphLike V I E Gr] (d₁ d₂ : Dart G) :
    d₁.edge = d₂.edge ↔ d₁ = d₂ := by
  simp_rw [Dart.ext_iff]
  grind [fst_or_snd_of_isIncident, source_isIncident, target_isIncident]

end Directed

section NoParallelEdge

variable [GraphLike V I E Gr] [NoParallelEdge V I E Gr]

@[simp]
theorem sym2_eq_iff [Undirected V I E Gr] (d₁ d₂ : Dart G) :
    d₁.sym2 = d₂.sym2 ↔ d₁ = d₂ ∨ d₁ = d₂.symm := by
  simp only [sym2, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  refine ⟨?_, by rintro (rfl | rfl) <;> simp⟩
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact (edge_eq_iff_of_undirected d₁ d₂).mp <| d₁.IsLink.edge_eq
      (h1 ▸ h2 ▸ d₂.IsLink)
  have := (edge_eq_iff_of_undirected d₁ d₂.symm).mp <| d₁.IsLink.edge_eq
    (by simpa [h1, h2] using d₂.symm.IsLink)
  grind

lemma eq_of_source_target_eq_of_directed [Directed V I E Gr] (hds : d₁.source = d₂.source)
    (hdt : d₁.target = d₂.target) : d₁ = d₂ :=
  (d₁.edge_eq_iff_of_directed d₂).mp <|
    d₁.IsLink.edge_eq (hds ▸ hdt ▸ d₂.IsLink)

lemma source_target_inj_of_directed [Directed V I E Gr] :
    Function.Injective fun d : Dart G ↦ (d.source, d.target) := by
  rintro d₁ d₂ h
  rw [Prod.mk.injEq] at h
  exact eq_of_source_target_eq_of_directed h.1 h.2

lemma eq_of_source_target_eq [Loopless V I E Gr] (hds : d₁.source = d₂.source)
    (hdt : d₁.target = d₂.target) : d₁ = d₂ :=
  have := d₁.IsLink.edge_eq (hds ▸ hdt ▸ d₂.IsLink)
  ext (d₁.source_isIncident.inc_inj (hds ▸ this ▸ d₂.source_isIncident))
    (d₁.target_isIncident.inc_inj (hdt ▸ this ▸ d₂.target_isIncident))

lemma source_target_inj [Loopless V I E Gr] :
    Function.Injective fun d : Dart G ↦ (d.source, d.target) := by
  rintro d₁ d₂ h
  rw [Prod.mk.injEq] at h
  exact eq_of_source_target_eq h.1 h.2

end NoParallelEdge

end HyperGraphLike.Dart
