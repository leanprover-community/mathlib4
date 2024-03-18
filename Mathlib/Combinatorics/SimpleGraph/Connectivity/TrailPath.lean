/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Walk

/-!
# Graph trails and paths

A trail in a simple graph is a walk with no repeating edges.
A path is a trail with no repeating vertices.

**Warning**: graph theorists mean something different by "path" than do homotopy theorists.
A "walk" in graph theory is a "path" in homotopy theory.
Another warning: some graph theorists use "path" and "simple path" for "walk" and "path".

Some definitions and theorems have inspiration from multigraph counterparts in [Chou1994].

## Main definitions

* `SimpleGraph.Walk.IsTrail` and `SimpleGraph.Walk.IsPath`: predicates for trails and paths.
* `SimpleGraph.Path` is the type of paths in a given graph.
* `SimpleGraph.Walk.map` and `SimpleGraph.Path.map` for the induced map on walks/paths,
  given an (injective) graph homomorphism.
-/

namespace SimpleGraph

variable {V V' : Type*} {G H : SimpleGraph V} {G' : SimpleGraph V'} {u v w u' v' : V}

namespace Walk

/-- A *trail* is a walk with no repeating edges. -/
@[mk_iff isTrail_def]
structure IsTrail (p : G.Walk u v) : Prop where
  edges_nodup : p.edges.Nodup
#align simple_graph.walk.is_trail SimpleGraph.Walk.IsTrail
#align simple_graph.walk.is_trail_def SimpleGraph.Walk.isTrail_def

/-- A *path* is a walk with no repeating vertices. Use `IsPath.mk'` for a simpler constructor. -/
structure IsPath (p : G.Walk u v) extends IsTrail p : Prop where
  support_nodup : p.support.Nodup
#align simple_graph.walk.is_path SimpleGraph.Walk.IsPath

-- Porting note: used to use `extends to_trail : is_trail p` in structure
protected lemma IsPath.isTrail {p : G.Walk u v} (h : IsPath p) : IsTrail p := h.toIsTrail
#align simple_graph.walk.is_path.to_trail SimpleGraph.Walk.IsPath.isTrail

@[simp]
theorem isTrail_copy (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).IsTrail ↔ p.IsTrail := by
  subst_vars
  rfl
#align simple_graph.walk.is_trail_copy SimpleGraph.Walk.isTrail_copy

theorem IsPath.mk' {p : G.Walk u v} (h : p.support.Nodup) : p.IsPath :=
  ⟨⟨edges_nodup_of_support_nodup h⟩, h⟩
#align simple_graph.walk.is_path.mk' SimpleGraph.Walk.IsPath.mk'

theorem isPath_def (p : G.Walk u v) : p.IsPath ↔ p.support.Nodup :=
  ⟨IsPath.support_nodup, IsPath.mk'⟩
#align simple_graph.walk.is_path_def SimpleGraph.Walk.isPath_def

@[simp]
theorem isPath_copy (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).IsPath ↔ p.IsPath := by
  subst_vars
  rfl
#align simple_graph.walk.is_path_copy SimpleGraph.Walk.isPath_copy

@[simp]
theorem IsTrail.nil : (nil : G.Walk u u).IsTrail :=
  ⟨by simp [edges]⟩
#align simple_graph.walk.is_trail.nil SimpleGraph.Walk.IsTrail.nil

theorem IsTrail.of_cons {h : G.Adj u v} {p : G.Walk v w} :
    (cons h p).IsTrail → p.IsTrail := by simp [isTrail_def]
#align simple_graph.walk.is_trail.of_cons SimpleGraph.Walk.IsTrail.of_cons

@[simp]
theorem cons_isTrail_iff (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).IsTrail ↔ p.IsTrail ∧ s(u, v) ∉ p.edges := by simp [isTrail_def, and_comm]
#align simple_graph.walk.cons_is_trail_iff SimpleGraph.Walk.cons_isTrail_iff

theorem IsTrail.reverse (p : G.Walk u v) (h : p.IsTrail) : p.reverse.IsTrail := by
  simpa [isTrail_def] using h
#align simple_graph.walk.is_trail.reverse SimpleGraph.Walk.IsTrail.reverse

@[simp]
theorem reverse_isTrail_iff (p : G.Walk u v) : p.reverse.IsTrail ↔ p.IsTrail := by
  constructor <;>
    · intro h
      convert h.reverse _
      try rw [reverse_reverse]
#align simple_graph.walk.reverse_is_trail_iff SimpleGraph.Walk.reverse_isTrail_iff

theorem IsTrail.of_append_left {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsTrail) : p.IsTrail := by
  rw [isTrail_def, edges_append, List.nodup_append] at h
  exact ⟨h.1⟩
#align simple_graph.walk.is_trail.of_append_left SimpleGraph.Walk.IsTrail.of_append_left

theorem IsTrail.of_append_right {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsTrail) : q.IsTrail := by
  rw [isTrail_def, edges_append, List.nodup_append] at h
  exact ⟨h.2.1⟩
#align simple_graph.walk.is_trail.of_append_right SimpleGraph.Walk.IsTrail.of_append_right

theorem IsTrail.count_edges_le_one [DecidableEq V] {p : G.Walk u v} (h : p.IsTrail)
    (e : Sym2 V) : p.edges.count e ≤ 1 :=
  List.nodup_iff_count_le_one.mp h.edges_nodup e
#align simple_graph.walk.is_trail.count_edges_le_one SimpleGraph.Walk.IsTrail.count_edges_le_one

theorem IsTrail.count_edges_eq_one [DecidableEq V] {p : G.Walk u v} (h : p.IsTrail)
    {e : Sym2 V} (he : e ∈ p.edges) : p.edges.count e = 1 :=
  List.count_eq_one_of_mem h.edges_nodup he
#align simple_graph.walk.is_trail.count_edges_eq_one SimpleGraph.Walk.IsTrail.count_edges_eq_one

theorem IsPath.nil : (nil : G.Walk u u).IsPath := by constructor <;> simp
#align simple_graph.walk.is_path.nil SimpleGraph.Walk.IsPath.nil

theorem IsPath.of_cons {h : G.Adj u v} {p : G.Walk v w} :
    (cons h p).IsPath → p.IsPath := by simp [isPath_def]
#align simple_graph.walk.is_path.of_cons SimpleGraph.Walk.IsPath.of_cons

@[simp]
theorem cons_isPath_iff (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).IsPath ↔ p.IsPath ∧ u ∉ p.support := by
  constructor <;> simp (config := { contextual := true }) [isPath_def]
#align simple_graph.walk.cons_is_path_iff SimpleGraph.Walk.cons_isPath_iff

protected lemma IsPath.cons {p : G.Walk v w} (hp : p.IsPath) (hu : u ∉ p.support) {h : G.Adj u v} :
    (cons h p).IsPath :=
  (cons_isPath_iff _ _).2 ⟨hp, hu⟩

@[simp]
theorem isPath_iff_eq_nil (p : G.Walk u u) : p.IsPath ↔ p = nil := by
  cases p <;> simp [IsPath.nil]
#align simple_graph.walk.is_path_iff_eq_nil SimpleGraph.Walk.isPath_iff_eq_nil

theorem IsPath.reverse {p : G.Walk u v} (h : p.IsPath) : p.reverse.IsPath := by
  simpa [isPath_def] using h
#align simple_graph.walk.is_path.reverse SimpleGraph.Walk.IsPath.reverse

@[simp]
theorem isPath_reverse_iff (p : G.Walk u v) : p.reverse.IsPath ↔ p.IsPath := by
  constructor <;> intro h <;> convert h.reverse; simp
#align simple_graph.walk.is_path_reverse_iff SimpleGraph.Walk.isPath_reverse_iff

theorem IsPath.of_append_left {p : G.Walk u v} {q : G.Walk v w} :
    (p.append q).IsPath → p.IsPath := by
  simp only [isPath_def, support_append]
  exact List.Nodup.of_append_left
#align simple_graph.walk.is_path.of_append_left SimpleGraph.Walk.IsPath.of_append_left

theorem IsPath.of_append_right {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsPath) : q.IsPath := by
  rw [← isPath_reverse_iff] at h ⊢
  rw [reverse_append] at h
  apply h.of_append_left
#align simple_graph.walk.is_path.of_append_right SimpleGraph.Walk.IsPath.of_append_right

lemma IsPath.tail {p : G.Walk u v} (hp : p.IsPath) (hp' : ¬p.Nil) : (p.tail hp').IsPath := by
  rw [Walk.isPath_def] at hp ⊢
  rw [← cons_support_tail _ hp', List.nodup_cons] at hp
  exact hp.2

instance [DecidableEq V] (p : G.Walk u v) : Decidable p.IsPath := by
  rw [isPath_def]
  infer_instance

theorem IsPath.length_lt [Fintype V] {p : G.Walk u v} (hp : p.IsPath) :
    p.length < Fintype.card V := by
  rw [Nat.lt_iff_add_one_le, ← length_support]
  exact hp.support_nodup.length_le_card
#align simple_graph.walk.is_path.length_lt SimpleGraph.Walk.IsPath.length_lt

end Walk

/-! ### Type of paths -/

/-- The type for paths between two vertices. -/
abbrev Path (u v : V) := { p : G.Walk u v // p.IsPath }
#align simple_graph.path SimpleGraph.Path

namespace Path

@[simp]
protected theorem isPath (p : G.Path u v) : (p : G.Walk u v).IsPath := p.property
#align simple_graph.path.is_path SimpleGraph.Path.isPath

@[simp]
protected theorem isTrail (p : G.Path u v) : (p : G.Walk u v).IsTrail :=
  p.property.isTrail
#align simple_graph.path.is_trail SimpleGraph.Path.isTrail

/-- The length-0 path at a vertex. -/
@[refl, simps]
protected def nil : G.Path u u :=
  ⟨Walk.nil, Walk.IsPath.nil⟩
#align simple_graph.path.nil SimpleGraph.Path.nil

/-- The length-1 path between a pair of adjacent vertices. -/
@[simps]
def singleton (h : G.Adj u v) : G.Path u v :=
  ⟨Walk.cons h Walk.nil, by simp [h.ne]⟩
#align simple_graph.path.singleton SimpleGraph.Path.singleton

theorem mk'_mem_edges_singleton (h : G.Adj u v) :
    s(u, v) ∈ (singleton h : G.Walk u v).edges := by simp [singleton]
#align simple_graph.path.mk_mem_edges_singleton SimpleGraph.Path.mk'_mem_edges_singleton

/-- The reverse of a path is another path.  See also `SimpleGraph.Walk.reverse`. -/
@[symm, simps]
def reverse (p : G.Path u v) : G.Path v u :=
  ⟨Walk.reverse p, p.property.reverse⟩
#align simple_graph.path.reverse SimpleGraph.Path.reverse

theorem count_support_eq_one [DecidableEq V] {p : G.Path u v}
    (hw : w ∈ (p : G.Walk u v).support) : (p : G.Walk u v).support.count w = 1 :=
  List.count_eq_one_of_mem p.property.support_nodup hw
#align simple_graph.path.count_support_eq_one SimpleGraph.Path.count_support_eq_one

theorem count_edges_eq_one [DecidableEq V] {p : G.Path u v} (e : Sym2 V)
    (hw : e ∈ (p : G.Walk u v).edges) : (p : G.Walk u v).edges.count e = 1 :=
  List.count_eq_one_of_mem p.property.isTrail.edges_nodup hw
#align simple_graph.path.count_edges_eq_one SimpleGraph.Path.count_edges_eq_one

@[simp]
theorem nodup_support (p : G.Path u v) : (p : G.Walk u v).support.Nodup :=
  (Walk.isPath_def _).mp p.property
#align simple_graph.path.nodup_support SimpleGraph.Path.nodup_support

theorem loop_eq (p : G.Path v v) : p = Path.nil := by
  obtain ⟨_ | _, h⟩ := p
  · rfl
  · simp at h
#align simple_graph.path.loop_eq SimpleGraph.Path.loop_eq

theorem not_mem_edges_of_loop {e : Sym2 V} {p : G.Path v v} : ¬e ∈ (p : G.Walk v v).edges :=
  by simp [p.loop_eq]
#align simple_graph.path.not_mem_edges_of_loop SimpleGraph.Path.not_mem_edges_of_loop

end Path

/-! ### Walks to paths -/

namespace Walk

variable [DecidableEq V]

protected theorem IsTrail.takeUntil {p : G.Walk v w} (hc : p.IsTrail)
    (h : u ∈ p.support) : (p.takeUntil u h).IsTrail :=
  IsTrail.of_append_left (by rwa [← take_spec _ h] at hc)
#align simple_graph.walk.is_trail.take_until SimpleGraph.Walk.IsTrail.takeUntil

protected theorem IsTrail.dropUntil {p : G.Walk v w} (hc : p.IsTrail)
    (h : u ∈ p.support) : (p.dropUntil u h).IsTrail :=
  IsTrail.of_append_right (by rwa [← take_spec _ h] at hc)
#align simple_graph.walk.is_trail.drop_until SimpleGraph.Walk.IsTrail.dropUntil

protected theorem IsPath.takeUntil {p : G.Walk v w} (hc : p.IsPath)
    (h : u ∈ p.support) : (p.takeUntil u h).IsPath :=
  IsPath.of_append_left (by rwa [← take_spec _ h] at hc)
#align simple_graph.walk.is_path.take_until SimpleGraph.Walk.IsPath.takeUntil

-- Porting note: p was previously accidentally an explicit argument
protected theorem IsPath.dropUntil {p : G.Walk v w} (hc : p.IsPath)
    (h : u ∈ p.support) : (p.dropUntil u h).IsPath :=
  IsPath.of_append_right (by rwa [← take_spec _ h] at hc)
#align simple_graph.walk.is_path.drop_until SimpleGraph.Walk.IsPath.dropUntil

protected theorem IsTrail.rotate {c : G.Walk v v} (hc : c.IsTrail) (h : u ∈ c.support) :
    (c.rotate h).IsTrail := by
  rw [isTrail_def, (c.rotate_edges h).perm.nodup_iff]
  exact hc.edges_nodup
#align simple_graph.walk.is_trail.rotate SimpleGraph.Walk.IsTrail.rotate

/-- Given a walk, produce a walk from it by bypassing subwalks between repeated vertices.
The result is a path, as shown in `SimpleGraph.Walk.bypass_isPath`.
This is packaged up in `SimpleGraph.Walk.toPath`. -/
def bypass {u v : V} : G.Walk u v → G.Walk u v
  | nil => nil
  | cons ha p =>
    let p' := p.bypass
    if hs : u ∈ p'.support then
      p'.dropUntil u hs
    else
      cons ha p'
#align simple_graph.walk.bypass SimpleGraph.Walk.bypass

@[simp]
theorem bypass_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).bypass = p.bypass.copy hu hv := by
  subst_vars
  rfl
#align simple_graph.walk.bypass_copy SimpleGraph.Walk.bypass_copy

theorem bypass_isPath {u v : V} (p : G.Walk u v) : p.bypass.IsPath := by
  induction p with
  | nil => simp!
  | cons _ p' ih =>
    simp only [bypass]
    split_ifs with hs
    · exact ih.dropUntil hs
    · simp [*, cons_isPath_iff]
#align simple_graph.walk.bypass_is_path SimpleGraph.Walk.bypass_isPath

theorem length_bypass_le {u v : V} (p : G.Walk u v) : p.bypass.length ≤ p.length := by
  induction p with
  | nil => rfl
  | cons _ _ ih =>
    simp only [bypass]
    split_ifs
    · trans
      apply length_dropUntil_le
      rw [length_cons]
      exact le_add_right ih
    · rw [length_cons, length_cons]
      exact add_le_add_right ih 1
#align simple_graph.walk.length_bypass_le SimpleGraph.Walk.length_bypass_le

/-- Given a walk, produces a path with the same endpoints using `SimpleGraph.Walk.bypass`. -/
def toPath {u v : V} (p : G.Walk u v) : G.Path u v :=
  ⟨p.bypass, p.bypass_isPath⟩
#align simple_graph.walk.to_path SimpleGraph.Walk.toPath

theorem support_bypass_subset {u v : V} (p : G.Walk u v) : p.bypass.support ⊆ p.support := by
  induction p with
  | nil => simp!
  | cons _ _ ih =>
    simp! only
    split_ifs
    · apply List.Subset.trans (support_dropUntil_subset _ _)
      apply List.subset_cons_of_subset
      assumption
    · rw [support_cons]
      apply List.cons_subset_cons
      assumption
#align simple_graph.walk.support_bypass_subset SimpleGraph.Walk.support_bypass_subset

theorem support_toPath_subset {u v : V} (p : G.Walk u v) :
    (p.toPath : G.Walk u v).support ⊆ p.support :=
  support_bypass_subset _
#align simple_graph.walk.support_to_path_subset SimpleGraph.Walk.support_toPath_subset

theorem darts_bypass_subset {u v : V} (p : G.Walk u v) : p.bypass.darts ⊆ p.darts := by
  induction p with
  | nil => simp!
  | cons _ _ ih =>
    simp! only
    split_ifs
    · apply List.Subset.trans (darts_dropUntil_subset _ _)
      apply List.subset_cons_of_subset _ ih
    · rw [darts_cons]
      exact List.cons_subset_cons _ ih
#align simple_graph.walk.darts_bypass_subset SimpleGraph.Walk.darts_bypass_subset

theorem edges_bypass_subset {u v : V} (p : G.Walk u v) : p.bypass.edges ⊆ p.edges :=
  List.map_subset _ p.darts_bypass_subset
#align simple_graph.walk.edges_bypass_subset SimpleGraph.Walk.edges_bypass_subset

theorem darts_toPath_subset {u v : V} (p : G.Walk u v) : (p.toPath : G.Walk u v).darts ⊆ p.darts :=
  darts_bypass_subset _
#align simple_graph.walk.darts_to_path_subset SimpleGraph.Walk.darts_toPath_subset

theorem edges_toPath_subset {u v : V} (p : G.Walk u v) : (p.toPath : G.Walk u v).edges ⊆ p.edges :=
  edges_bypass_subset _
#align simple_graph.walk.edges_to_path_subset SimpleGraph.Walk.edges_toPath_subset

end Walk

namespace Walk

variable {f : G →g G'} {p : G.Walk u v}

theorem map_isPath_of_injective (hinj : Function.Injective f) (hp : p.IsPath) :
    (p.map f).IsPath := by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    rw [Walk.cons_isPath_iff] at hp
    simp only [map_cons, cons_isPath_iff, ih hp.1, support_map, List.mem_map, not_exists, not_and,
      true_and]
    intro x hx hf
    cases hinj hf
    exact hp.2 hx
#align simple_graph.walk.map_is_path_of_injective SimpleGraph.Walk.map_isPath_of_injective

protected theorem IsPath.of_map (hp : (p.map f).IsPath) : p.IsPath := by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    rw [map_cons, Walk.cons_isPath_iff, support_map] at hp
    rw [Walk.cons_isPath_iff]
    cases' hp with hp1 hp2
    refine' ⟨ih hp1, _⟩
    contrapose! hp2
    exact List.mem_map_of_mem f hp2
#align simple_graph.walk.is_path.of_map SimpleGraph.Walk.IsPath.of_map

theorem map_isPath_iff_of_injective (hinj : Function.Injective f) : (p.map f).IsPath ↔ p.IsPath :=
  ⟨IsPath.of_map, map_isPath_of_injective hinj⟩
#align simple_graph.walk.map_is_path_iff_of_injective SimpleGraph.Walk.map_isPath_iff_of_injective

theorem map_isTrail_iff_of_injective (hinj : Function.Injective f) :
    (p.map f).IsTrail ↔ p.IsTrail := by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    rw [map_cons, cons_isTrail_iff, ih, cons_isTrail_iff]
    apply and_congr_right'
    rw [← Sym2.map_pair_eq, edges_map, ← List.mem_map_of_injective (Sym2.map.injective hinj)]
#align simple_graph.walk.map_is_trail_iff_of_injective SimpleGraph.Walk.map_isTrail_iff_of_injective

alias ⟨_, map_isTrail_of_injective⟩ := map_isTrail_iff_of_injective
#align simple_graph.walk.map_is_trail_of_injective SimpleGraph.Walk.map_isTrail_of_injective

@[simp]
theorem mapLe_isTrail {G G' : SimpleGraph V} (h : G ≤ G') {p : G.Walk u v} :
    (p.mapLe h).IsTrail ↔ p.IsTrail :=
  map_isTrail_iff_of_injective Function.injective_id
#align simple_graph.walk.map_le_is_trail SimpleGraph.Walk.mapLe_isTrail

alias ⟨IsTrail.of_mapLe, IsTrail.mapLe⟩ := mapLe_isTrail
#align simple_graph.walk.is_trail.of_map_le SimpleGraph.Walk.IsTrail.of_mapLe
#align simple_graph.walk.is_trail.map_le SimpleGraph.Walk.IsTrail.mapLe

@[simp]
theorem mapLe_isPath {G G' : SimpleGraph V} (h : G ≤ G') {p : G.Walk u v} :
    (p.mapLe h).IsPath ↔ p.IsPath :=
  map_isPath_iff_of_injective Function.injective_id
#align simple_graph.walk.map_le_is_path SimpleGraph.Walk.mapLe_isPath

alias ⟨IsPath.of_mapLe, IsPath.mapLe⟩ := mapLe_isPath
#align simple_graph.walk.is_path.of_map_le SimpleGraph.Walk.IsPath.of_mapLe
#align simple_graph.walk.is_path.map_le SimpleGraph.Walk.IsPath.mapLe

protected theorem IsPath.transfer (hp) (pp : p.IsPath) :
    (p.transfer H hp).IsPath := by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    simp only [Walk.transfer, cons_isPath_iff, support_transfer _ ] at pp ⊢
    exact ⟨ih _ pp.1, pp.2⟩
#align simple_graph.walk.is_path.transfer SimpleGraph.Walk.IsPath.transfer

protected theorem IsPath.toDeleteEdges (s : Set (Sym2 V))
    {p : G.Walk v w} (h : p.IsPath) (hp) : (p.toDeleteEdges s hp).IsPath :=
  h.transfer _
#align simple_graph.walk.is_path.to_delete_edges SimpleGraph.Walk.IsPath.toDeleteEdges

end Walk

namespace Path

/-- Given an injective graph homomorphism, map paths to paths. -/
@[simps]
protected def map (f : G →g G') (hinj : Function.Injective f) (p : G.Path u v) :
    G'.Path (f u) (f v) :=
  ⟨Walk.map f p, Walk.map_isPath_of_injective hinj p.2⟩
#align simple_graph.path.map SimpleGraph.Path.map

theorem map_injective {f : G →g G'} (hinj : Function.Injective f) (u v : V) :
    Function.Injective (Path.map f hinj : G.Path u v → G'.Path (f u) (f v)) := by
  rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
  simp only [Path.map, Subtype.coe_mk, Subtype.mk.injEq] at h
  simp [Walk.map_injective_of_injective hinj u v h]
#align simple_graph.path.map_injective SimpleGraph.Path.map_injective

/-- Given a graph embedding, map paths to paths. -/
@[simps!]
protected def mapEmbedding (f : G ↪g G') (p : G.Path u v) : G'.Path (f u) (f v) :=
  Path.map f.toHom f.injective p
#align simple_graph.path.map_embedding SimpleGraph.Path.mapEmbedding

theorem mapEmbedding_injective (f : G ↪g G') (u v : V) :
    Function.Injective (Path.mapEmbedding f : G.Path u v → G'.Path (f u) (f v)) :=
  map_injective f.injective u v
#align simple_graph.path.map_embedding_injective SimpleGraph.Path.mapEmbedding_injective

end Path

/-! ### Walks of a given length -/

section WalkCounting

variable (G)

theorem set_walk_self_length_zero_eq (u : V) : {p : G.Walk u u | p.length = 0} = {Walk.nil} := by
  ext p
  simp
#align simple_graph.set_walk_self_length_zero_eq SimpleGraph.set_walk_self_length_zero_eq

theorem set_walk_length_zero_eq_of_ne {u v : V} (h : u ≠ v) :
    {p : G.Walk u v | p.length = 0} = ∅ := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false_iff]
  exact fun h' => absurd (Walk.eq_of_length_eq_zero h') h
#align simple_graph.set_walk_length_zero_eq_of_ne SimpleGraph.set_walk_length_zero_eq_of_ne

theorem set_walk_length_succ_eq (u v : V) (n : ℕ) :
    {p : G.Walk u v | p.length = n.succ} =
      ⋃ (w : V) (h : G.Adj u w), Walk.cons h '' {p' : G.Walk w v | p'.length = n} := by
  ext p
  cases' p with _ _ w _ huw pwv
  · simp [eq_comm]
  · simp only [Nat.succ_eq_add_one, Set.mem_setOf_eq, Walk.length_cons, add_left_inj,
      Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · rintro rfl
      exact ⟨w, huw, pwv, rfl, rfl⟩
    · rintro ⟨w, huw, pwv, rfl, rfl, rfl⟩
      rfl
#align simple_graph.set_walk_length_succ_eq SimpleGraph.set_walk_length_succ_eq

variable [DecidableEq V]

/-- Walks of length two from `u` to `v` correspond bijectively to common neighbours of `u` and `v`.
Note that `u` and `v` may be the same. -/
@[simps]
def walkLengthTwoEquivCommonNeighbors (u v : V) :
    {p : G.Walk u v // p.length = 2} ≃ G.commonNeighbors u v where
  toFun p := ⟨p.val.getVert 1, match p with
    | ⟨.cons _ (.cons _ .nil), hp⟩ => ⟨‹G.Adj u _›, ‹G.Adj _ v›.symm⟩⟩
  invFun w := ⟨w.prop.1.toWalk.concat w.prop.2.symm, rfl⟩
  left_inv | ⟨.cons _ (.cons _ .nil), hp⟩ => by rfl
  right_inv _ := rfl

section LocallyFinite

variable [LocallyFinite G]

/-- The `Finset` of length-`n` walks from `u` to `v`.
This is used to give `{p : G.Walk u v | p.length = n}` a `Fintype` instance, and it
can also be useful as a recursive description of this set when `V` is finite.

See `SimpleGraph.coe_finsetWalkLength_eq` for the relationship between this `Finset` and
the set of length-`n` walks. -/
def finsetWalkLength (n : ℕ) (u v : V) : Finset (G.Walk u v) :=
  match n with
  | 0 =>
    if h : u = v then by
      subst u
      exact {Walk.nil}
    else ∅
  | n + 1 =>
    Finset.univ.biUnion fun (w : G.neighborSet u) =>
      (finsetWalkLength n w v).map ⟨fun p => Walk.cons w.property p, fun _ _ => by simp⟩
#align simple_graph.finset_walk_length SimpleGraph.finsetWalkLength

theorem coe_finsetWalkLength_eq (n : ℕ) (u v : V) :
    (G.finsetWalkLength n u v : Set (G.Walk u v)) = {p : G.Walk u v | p.length = n} := by
  induction' n with n ih generalizing u v
  · obtain rfl | huv := eq_or_ne u v <;> simp [finsetWalkLength, set_walk_length_zero_eq_of_ne, *]
  · simp only [finsetWalkLength, set_walk_length_succ_eq, Finset.coe_biUnion, Finset.mem_coe,
      Finset.mem_univ, Set.iUnion_true]
    ext p
    simp only [mem_neighborSet, Finset.coe_map, Function.Embedding.coeFn_mk, Set.iUnion_coe_set,
      Set.mem_iUnion, Set.mem_image, Finset.mem_coe, Set.mem_setOf_eq]
    congr!
    rename_i w _ q
    have := Set.ext_iff.mp (ih w v) q
    simp only [Finset.mem_coe, Set.mem_setOf_eq] at this
    rw [← this]
#align simple_graph.coe_finset_walk_length_eq SimpleGraph.coe_finsetWalkLength_eq

variable {G}

theorem Walk.mem_finsetWalkLength_iff_length_eq {n : ℕ} {u v : V} (p : G.Walk u v) :
    p ∈ G.finsetWalkLength n u v ↔ p.length = n :=
  Set.ext_iff.mp (G.coe_finsetWalkLength_eq n u v) p
#align simple_graph.walk.mem_finset_walk_length_iff_length_eq SimpleGraph.Walk.mem_finsetWalkLength_iff_length_eq

variable (G)

instance fintypeSetWalkLength (u v : V) (n : ℕ) : Fintype {p : G.Walk u v | p.length = n} :=
  Fintype.ofFinset (G.finsetWalkLength n u v) fun p => by
    rw [← Finset.mem_coe, coe_finsetWalkLength_eq]
#align simple_graph.fintype_set_walk_length SimpleGraph.fintypeSetWalkLength

instance fintypeSubtypeWalkLength (u v : V) (n : ℕ) : Fintype {p : G.Walk u v // p.length = n} :=
  fintypeSetWalkLength G u v n

theorem set_walk_length_toFinset_eq (n : ℕ) (u v : V) :
    {p : G.Walk u v | p.length = n}.toFinset = G.finsetWalkLength n u v := by
  ext p
  simp [← coe_finsetWalkLength_eq]
#align simple_graph.set_walk_length_to_finset_eq SimpleGraph.set_walk_length_toFinset_eq

/- See `SimpleGraph.adjMatrix_pow_apply_eq_card_walk` for the cardinality in terms of the `n`th
power of the adjacency matrix. -/
theorem card_set_walk_length_eq (u v : V) (n : ℕ) :
    Fintype.card {p : G.Walk u v | p.length = n} = (G.finsetWalkLength n u v).card :=
  Fintype.card_ofFinset (G.finsetWalkLength n u v) fun p => by
    rw [← Finset.mem_coe, coe_finsetWalkLength_eq]
#align simple_graph.card_set_walk_length_eq SimpleGraph.card_set_walk_length_eq

instance fintypeSetPathLength (u v : V) (n : ℕ) :
    Fintype {p : G.Walk u v | p.IsPath ∧ p.length = n} :=
  Fintype.ofFinset ((G.finsetWalkLength n u v).filter Walk.IsPath) <| by
    simp [Walk.mem_finsetWalkLength_iff_length_eq, and_comm]
#align simple_graph.fintype_set_path_length SimpleGraph.fintypeSetPathLength

end LocallyFinite

end WalkCounting

end SimpleGraph
