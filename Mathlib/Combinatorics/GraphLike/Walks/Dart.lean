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

A `Dart` or half-edge or bond in a graph is an ordered pair of adjacent vertices, regarded as an
oriented edge. This file defines darts and proves some of their basic properties.
-/

public section

open Set HyperGraphLike

namespace HyperGraphLike

variable {V I E Gr : Type*} {G : Gr} {i j : I} {e : E} {u v : V} [HyperGraphLike V I E Gr]

/-- The set of darts of a graph-like structure. -/
@[expose]
def Dart (G : Gr) := {s : I × I // s.1 ≠ s.2 ∧ IsSource G s.1 ∧ IsTarget G s.2 ∧
    ∃ e u v, IsIncident G s.1 e u ∧ IsIncident G s.2 e v}

namespace Dart

variable (d : Dart G)

/-- The first incidence of a dart. -/
@[expose] def fst : I := d.val.fst

/-- The second incidence of a dart. -/
@[expose] def snd : I := d.val.snd

/-- The edge of a dart. -/
@[expose] noncomputable def edge : E := d.prop.2.2.2.choose

/-- The source of a dart. -/
@[expose] noncomputable def source : V := d.prop.2.2.2.choose_spec.choose

/-- The target of a dart. -/
@[expose] noncomputable def target : V := d.prop.2.2.2.choose_spec.choose_spec.choose

@[grind .] lemma fst_ne_snd : d.fst ≠ d.snd := d.prop.1

@[grind .] lemma fst_isSource : IsSource G d.fst := d.prop.2.1

@[grind .] lemma snd_isTarget : IsTarget G d.snd := d.prop.2.2.1

@[grind .]
lemma source_isIncident : IsIncident G d.fst d.edge d.source :=
  d.prop.2.2.2.choose_spec.choose_spec.choose_spec.1

@[grind .]
lemma target_isIncident : IsIncident G d.snd d.edge d.target :=
  d.prop.2.2.2.choose_spec.choose_spec.choose_spec.2

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

@[grind →]
lemma edge_eq_of_isIncident_fst (h : IsIncident G d.fst e v) : d.edge = e :=
  d.source_isIncident.inj h |>.1

lemma edge_eq_iff_source (d : Dart G) : d.edge = e ↔ IsIncident G d.fst e d.source :=
  ⟨(· ▸ d.source_isIncident), edge_eq_of_isIncident_fst⟩

@[grind →]
lemma edge_eq_of_isIncident_snd (h : IsIncident G d.snd e v) : d.edge = e :=
  d.target_isIncident.inj h |>.1

lemma edge_eq_iff_target (d : Dart G) : d.edge = e ↔ IsIncident G d.snd e d.target :=
  ⟨(· ▸ d.target_isIncident), edge_eq_of_isIncident_snd⟩

@[grind →]
lemma source_eq_of_isIncident_fst (h : IsIncident G d.fst e v) : d.source = v :=
  d.source_isIncident.inj h |>.2

lemma source_eq_iff (d : Dart G) : d.source = v ↔ IsIncident G d.fst d.edge v :=
  ⟨(· ▸ d.source_isIncident), source_eq_of_isIncident_fst⟩

@[grind →]
lemma target_eq_of_isIncident_snd (h : IsIncident G d.snd e v) : d.target = v :=
  d.target_isIncident.inj h |>.2

lemma target_eq_iff (d : Dart G) : d.target = v ↔ IsIncident G d.snd d.edge v :=
  ⟨(· ▸ d.target_isIncident), target_eq_of_isIncident_snd⟩

@[simp, grind =] lemma val_eq_iff : d.val = (i, j) ↔ d.fst = i ∧ d.snd = j := by grind [fst, snd]

@[ext]
lemma ext (hf : d₁.fst = d₂.fst) (hs : d₁.snd = d₂.snd) : d₁ = d₂ :=
  match d₁, d₂ with | ⟨⟨i₁, j₁⟩, h₁⟩, ⟨⟨i₂, j₂⟩, h₂⟩ => by simp_all [fst, snd]

lemma _root_.HyperGraphLike.isLink_iff_exists_dart :
    IsLink G e u v ↔ ∃ d : Dart G, d.edge = e ∧ d.source = u ∧ d.target = v := by
  refine ⟨fun h ↦ ?_, fun ⟨d, he, hs, ht⟩ ↦ isLink_def.mpr ⟨d.fst, d.snd, d.fst_ne_snd,
    d.fst_isSource, d.snd_isTarget, hs ▸ he ▸ d.source_isIncident, ht ▸ he ▸ d.target_isIncident⟩⟩
  obtain ⟨i, j, hne, hi, hj, hei, hej⟩ := isLink_def.mp h
  use ⟨(i, j), hne, hi, hj, e, u, v, hei, hej⟩, edge_eq_of_isIncident_fst hei,
    source_eq_of_isIncident_fst hei, target_eq_of_isIncident_snd hej

lemma IsLink (d : Dart G) : IsLink G d.edge d.source d.target := isLink_def.mpr ⟨d.fst, d.snd,
  d.fst_ne_snd, d.fst_isSource, d.snd_isTarget, d.source_isIncident, d.target_isIncident⟩

lemma _root_.HyperGraphLike.adj_iff_exists_dart :
    Adj G u v ↔ ∃ d : Dart G, d.source = u ∧ d.target = v := by
  refine ⟨fun h ↦ ?_, fun ⟨d, hs, ht⟩ ↦ adj_def.mpr ⟨d.edge, d.fst, d.snd, d.fst_ne_snd,
    d.fst_isSource, d.snd_isTarget, hs ▸ d.source_isIncident, ht ▸ d.target_isIncident⟩⟩
  obtain ⟨e, i, j, hne, hi, hj, hei, hej⟩ := adj_def.mp h
  use ⟨(i, j), hne, hi, hj, e, u, v, hei, hej⟩, source_eq_of_isIncident_fst hei,
    target_eq_of_isIncident_snd hej

@[grind .]
lemma Adj (d : Dart G) : Adj G d.source d.target := adj_def.mpr ⟨d.edge, d.fst, d.snd,
  d.fst_ne_snd, d.fst_isSource, d.snd_isTarget, d.source_isIncident, d.target_isIncident⟩

/-- Convert an incidence to a pair of vertices. -/
@[expose] noncomputable def toProd (d : Dart G) : V × V := (d.source, d.target)

@[simp, grind =]
lemma toProd_eq_mk_iff (d : Dart G) (u v : V) :
    d.toProd = (u, v) ↔ d.source = u ∧ d.target = v := by
  simp [toProd]

/-- The two vertices of the dart as an unordered pair. Not well-defined for not undirected graphs.
-/
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

lemma incMatrix_col_eq [DecidableEq V] {n : ℕ∞} (d : Dart G) :
    (incMatrix G n n n).col d.edge = Pi.single d.source n + Pi.single d.target n :=
  d.IsLink.incMatrix_col_eq

end GraphLike

section Undirected

variable [Undirected V I E Gr]

lemma Adj' (d : Dart G) : HyperGraphLike.Adj G d.target d.source := d.Adj.symm

/-- The dart with reversed orientation from a given dart. -/
@[expose] def symm (d : Dart G) : Dart G := ⟨d.val.swap, by grind⟩

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

section NoMultiEdge

variable [GraphLike V I E Gr] [NoMultiEdge V I E Gr]

@[simp]
theorem sym2_eq_iff [Undirected V I E Gr] (d₁ d₂ : Dart G) :
    d₁.sym2 = d₂.sym2 ↔ d₁ = d₂ ∨ d₁ = d₂.symm := by
  simp only [sym2, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  refine ⟨?_, by rintro (rfl | rfl) <;> simp⟩
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact (edge_eq_iff_of_undirected d₁ d₂).mp <| d₁.IsLink.edge_inj_of_isLink_of_undirected
      (h1 ▸ h2 ▸ d₂.IsLink)
  have := (edge_eq_iff_of_undirected d₁ d₂.symm).mp <| d₁.IsLink.edge_inj_of_isLink_of_undirected
    (by simpa [h1, h2] using d₂.symm.IsLink)
  grind

lemma eq_of_source_target_eq_of_directed [Directed V I E Gr] (hds : d₁.source = d₂.source)
    (hdt : d₁.target = d₂.target) : d₁ = d₂ :=
  (d₁.edge_eq_iff_of_directed d₂).mp <|
    d₁.IsLink.edge_inj_of_isLink_of_directed (hds ▸ hdt ▸ d₂.IsLink)

lemma source_target_inj_of_directed [Directed V I E Gr] :
    Function.Injective fun d : Dart G ↦ (d.source, d.target) := by
  rintro d₁ d₂ h
  rw [Prod.mk.injEq] at h
  exact eq_of_source_target_eq_of_directed h.1 h.2

lemma eq_of_source_target_eq_of_undirected [Undirected V I E Gr] [Loopless V I E Gr]
    (hds : d₁.source = d₂.source) (hdt : d₁.target = d₂.target) : d₁ = d₂ :=
  have := d₁.IsLink.edge_inj_of_isLink_of_undirected (hds ▸ hdt ▸ d₂.IsLink)
  ext (d₁.source_isIncident.inc_inj (hds ▸ this ▸ d₂.source_isIncident))
    (d₁.target_isIncident.inc_inj (hdt ▸ this ▸ d₂.target_isIncident))

lemma source_target_inj_of_undirected [Undirected V I E Gr] [Loopless V I E Gr] :
    Function.Injective fun d : Dart G ↦ (d.source, d.target) := by
  rintro d₁ d₂ h
  rw [Prod.mk.injEq] at h
  exact eq_of_source_target_eq_of_undirected h.1 h.2

end NoMultiEdge

end HyperGraphLike.Dart
