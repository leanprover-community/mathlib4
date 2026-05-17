/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon, Thomas Waring
-/
module

public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.Digraph.Basic

/-! # Typeclass for graph-like data

- packaging junk values problematic due to non-defeq instances for the same type, move to relations
(more ergononmic than partially defined functions i think)
- method of undirected graph = directed modulo involution means the definition of trail (walk with
no duplicated edges) no longer works, bc the same edge could be traversed both ways.
-/

public section

variable {V H I O E Gr : Type*}

class HyperGraphLike (V E : outParam Type*) (Gr : Type*) where
  verts : Gr → Set V
  edges : Gr → Set E
  IsSource : Gr → E → V → Prop
  IsTarget : Gr → E → V → Prop
  mem_verts_of_isSource : ∀ ⦃G e x⦄, IsSource G e x → x ∈ verts G
  mem_verts_of_isTarget : ∀ ⦃G e x⦄, IsTarget G e x → x ∈ verts G
  mem_edges_of_isSource : ∀ ⦃G e x⦄, IsSource G e x → e ∈ edges G
  mem_edges_of_isTarget : ∀ ⦃G e x⦄, IsTarget G e x → e ∈ edges G

namespace HyperGraphLike

variable [HyperGraphLike V E Gr] {G : Gr}

def IsLink (G : Gr) (e : E) (x y : V) : Prop := IsSource G e x ∧ IsTarget G e y

def Adj (G : Gr) (x y : V) : Prop := ∃ e, IsSource G e x ∧ IsTarget G e y

def sources (G : Gr) (e : E) : Set V := {x | IsSource G e x}

def targets (G : Gr) (e : E) : Set V := {y | IsTarget G e y}

structure Dart (G : Gr) where
  source : V
  target : V
  edge : E
  isLink : IsLink G edge source target

namespace Dart

@[ext]
protected lemma ext {d d' : Dart G} (hs : d.source = d'.source) (ho : d.target = d'.target)
    (he : d.edge = d'.edge) : d = d' := by
  cases d; cases d'; congr

def isSource (d : Dart G) : IsSource G d.edge d.source := d.isLink.1

lemma source_mem (d : Dart G) : d.source ∈ verts G := mem_verts_of_isSource d.isSource

def isTarget (d : Dart G) : IsTarget G d.edge d.target := d.isLink.2

lemma target_mem (d : Dart G) : d.target ∈ verts G := mem_verts_of_isTarget d.isLink.2

lemma edge_mem (d : Dart G) : d.edge ∈ edges G := mem_edges_of_isSource d.isSource

lemma adj (d : Dart G) : Adj G d.source d.target := ⟨d.edge, d.isSource, d.isTarget⟩

def AdjDart (d d' : Dart G) : Prop := d.target = d'.source

end Dart

end HyperGraphLike

open HyperGraphLike

class DirGraphLike (V E : outParam Type*) (Gr : Type*) extends
    HyperGraphLike V E Gr where
  exists_unique_isSource_of_mem_edges : ∀ ⦃G e⦄, e ∈ edges G → ∃! x, IsSource G e x
  exists_unique_isTarget_of_mem_edges : ∀ ⦃G e⦄, e ∈ edges G → ∃! x, IsTarget G e x

namespace DirGraphLike

@[implicit_reducible]
def ofIsLink (verts : Gr → Set V) (edges : Gr → Set E)
    (IsLink : Gr → E → V → V → Prop)
    (mem_edges_iff_exists_isLink : ∀ ⦃G e⦄, e ∈ edges G ↔ ∃ x y, IsLink G e x y)
    (mem_verts_left_of_isLink : ∀ ⦃G e x y⦄, IsLink G e x y → x ∈ verts G)
    (mem_verts_right_of_isLink : ∀ ⦃G e x y⦄, IsLink G e x y → y ∈ verts G)
    (eq_and_eq_of_isLink_of_isLink : ∀ ⦃G e x x' y y'⦄,
      IsLink G e x y → IsLink G e x' y' → x = x' ∧ y = y') :
    DirGraphLike V E Gr
    where
  verts := verts
  edges := edges
  IsSource G e x := ∃ y, IsLink G e x y
  IsTarget G e y := ∃ x, IsLink G e x y
  mem_verts_of_isSource G e x := fun ⟨_, h⟩ => mem_verts_left_of_isLink h
  mem_verts_of_isTarget G e y := fun ⟨_, h⟩ => mem_verts_right_of_isLink h
  mem_edges_of_isSource G e x := fun ⟨y, h⟩ => mem_edges_iff_exists_isLink |>.mpr ⟨x, y, h⟩
  mem_edges_of_isTarget G e y := fun ⟨x, h⟩ => mem_edges_iff_exists_isLink |>.mpr ⟨x, y, h⟩
  exists_unique_isSource_of_mem_edges G e he := by
    apply existsUnique_of_exists_of_unique (mem_edges_iff_exists_isLink.mp he)
    intro x x' ⟨_, hy⟩ ⟨_, hy'⟩
    exact eq_and_eq_of_isLink_of_isLink hy hy' |>.1
  exists_unique_isTarget_of_mem_edges G e he := by
    apply existsUnique_of_exists_of_unique
    · obtain ⟨x, y, h⟩ := mem_edges_iff_exists_isLink.mp he
      exact ⟨y, x, h⟩
    · intro y y' ⟨x, hx⟩ ⟨x', hx'⟩
      exact eq_and_eq_of_isLink_of_isLink hx hx' |>.2

@[implicit_reducible]
def ofSourceTarget (verts : Gr → Set V) (edges : Gr → Set E) (src : Gr → E → V) (tgt : Gr → E → V)
    (mem_verts_src : ∀ ⦃G e⦄, e ∈ edges G → src G e ∈ verts G)
    (mem_verts_tgt : ∀ ⦃G e⦄, e ∈ edges G → tgt G e ∈ verts G) :
    DirGraphLike V E Gr where
  verts := verts
  edges := edges
  IsSource G e x := e ∈ edges G ∧ src G e = x
  IsTarget G e y := e ∈ edges G ∧ tgt G e = y
  mem_verts_of_isSource G e x h := h.2 ▸ (mem_verts_src h.1)
  mem_verts_of_isTarget G e x h := h.2 ▸ (mem_verts_tgt h.1)
  mem_edges_of_isSource G e x h := h.1
  mem_edges_of_isTarget G e x h := h.1
  exists_unique_isSource_of_mem_edges G e he := by
    use src G e
    grind
  exists_unique_isTarget_of_mem_edges G e he := by
    use tgt G e
    grind

variable [DirGraphLike V E Gr] {G : Gr}

noncomputable def edgeSource {G : Gr} {e : E} (he : e ∈ edges G) : V :=
  Classical.choose (exists_unique_isSource_of_mem_edges he)

lemma isSource_iff (e : E) (x : V) : IsSource G e x ↔ ∃ h : e ∈ edges G, edgeSource h = x := by
  simp_rw [edgeSource, ExistsUnique.choose_eq_iff]
  exact ⟨fun h => ⟨mem_edges_of_isSource h, h⟩, fun ⟨_, h⟩ => h⟩

noncomputable def edgeTarget {G : Gr} {e : E} (he : e ∈ edges G) : V :=
  Classical.choose (exists_unique_isTarget_of_mem_edges he)

lemma isTarget_iff (e : E) (x : V) : IsTarget G e x ↔ ∃ h : e ∈ edges G, edgeTarget h = x := by
  simp_rw [edgeTarget, ExistsUnique.choose_eq_iff]
  exact ⟨fun h => ⟨mem_edges_of_isTarget h, h⟩, fun ⟨_, h⟩ => h⟩

end DirGraphLike

open DirGraphLike

class SimpleHyperGraphLike (V E : outParam Type*) (Gr : Type*) extends HyperGraphLike V E Gr where
  eq_of_isSource_eq_of_isTarget_eq : ∀ ⦃G e e'⦄, e ∈ edges G → e' ∈ edges G →
      (∀ x, IsSource G e x ↔ IsSource G e' x) → (∀ y, IsTarget G e y ↔ IsTarget G e' y) → e = e'

class IrreflHyperGraphLike (V E : outParam Type*) (Gr : Type*) extends
    HyperGraphLike V E Gr where
  not_isSource_isTarget : ∀ ⦃G e x⦄, ¬ (IsSource G e x ∧ IsTarget G e x)

class SymmHyperGraphLike (V E : outParam Type*) (Gr : Type*) extends
    HyperGraphLike V E Gr where
  isSource_iff_isTarget : ∀ ⦃G e x⦄, IsSource G e x ↔ IsTarget G e x

instance : DirGraphLike V (V × V) (Digraph V) := ofSourceTarget (Gr := Digraph V)
  (verts := fun _ => Set.univ) (edges := fun G => {p : V × V | G.Adj p.1 p.2})
  (src := fun _ => Prod.fst) (tgt := fun _ => Prod.snd)
  (mem_verts_src := fun _ _ _ => trivial) (mem_verts_tgt := fun _ _ _ => trivial)

instance : SimpleHyperGraphLike V (V × V) (Digraph V) where
  eq_of_isSource_eq_of_isTarget_eq := by
    intro G ⟨x, y⟩ ⟨x', y'⟩ h h' hx hy
    simp_all [IsSource, IsTarget, edges]

instance : DirGraphLike V (E × V × V) (Graph V E) := by
  refine ofIsLink Graph.vertexSet (fun G => {p | G.IsLink p.1 p.2.1 p.2.2})
    (fun G e x y => e.2.1 = x ∧ e.2.2 = y ∧ G.IsLink e.1 x y) ?_ ?_ ?_ ?_
  · simp
  · intro G ⟨e, _⟩ x y ⟨_, _, h⟩
    exact h.left_mem
  · intro G ⟨e, _⟩ x y ⟨_, _, h⟩
    exact h.right_mem
  · rintro G ⟨e, z⟩ x x' y y' ⟨rfl, rfl, h⟩ ⟨rfl, rfl, h'⟩
    simp

-- instance : SymmHyperGraphLike V (E × V × V) (Graph V E) where
--   inv G := fun ⟨e, x, y⟩ => ⟨e, y, x⟩
--   inv_inv_eq G := by simp
--   isSource_iff_isTarget_inv G := by
--     rintro ⟨e, x, y⟩ x'
--     simp only [IsSource, exists_and_left, ↓existsAndEq, true_and, IsTarget, exists_eq_left',
--       and_congr_right_iff]
--     rintro rfl
--     exact G.isLink_comm

instance : DirGraphLike V (V × V) (SimpleGraph V) := by
  refine ofIsLink (fun G => Set.univ) (fun G => {p | G.Adj p.1 p.2})
    (fun G e x y => e.1 = x ∧ e.2 = y ∧ G.Adj x y) ?_ ?_ ?_ ?uniq
  case uniq =>
    rintro G ⟨x, y⟩ _ _ _ _ ⟨rfl, rfl, h⟩ ⟨rfl, rfl, h'⟩
    exact ⟨rfl, rfl⟩
  all_goals simp

-- instance : SymmHyperGraphLike V (V × V) (SimpleGraph V) where
--   inv G := fun ⟨x, y⟩ => ⟨y, x⟩
--   inv_inv_eq G := by simp
--   isSource_iff_isTarget_inv G := by
--     intro ⟨x, y⟩ _
--     simp only [IsSource, exists_and_left, ↓existsAndEq, true_and, IsTarget, exists_eq_left',
--       and_congr_right_iff]
--     rintro rfl
--     exact G.adj_comm ..

instance : IrreflHyperGraphLike V (V × V) (SimpleGraph V) where
  not_isSource_isTarget G := by
    intro ⟨x, y⟩ _
    simp only [IsSource, exists_and_left, ↓existsAndEq, true_and, IsTarget, exists_eq_left',
      not_and, and_imp]
    rintro rfl h rfl
    exact G.irrefl
