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

variable {V H I O E Gr : Type*}

class HyperGraphLike (V I O E : outParam Type*) (Gr : Type*) where
  verts : Gr → Set V
  edges : Gr → Set E
  source : Gr → I →. V
  target : Gr → O →. V
  edgeI : Gr → I →. E
  edgeO : Gr → O →. E
  dom_source_eq_dom_edgeI : ∀ ⦃G⦄, (source G).Dom = (edgeI G).Dom
  dom_target_eq_dom_edgeO : ∀ ⦃G⦄, (target G).Dom = (edgeO G).Dom
  ran_source_subset_verts : ∀ ⦃G⦄, (source G).ran ⊆ verts G
  ran_target_subset_verts : ∀ ⦃G⦄, (target G).ran ⊆ verts G
  ran_edgeI_subset_edges : ∀ ⦃G⦄, (edgeI G).ran ⊆ edges G
  ran_edgeO_subset_edges : ∀ ⦃G⦄, (edgeO G).ran ⊆ edges G

namespace HyperGraphLike

variable [HyperGraphLike V I O E Gr] {G : Gr}

-- def inFlags (G : Gr) : Set I := (source G).Dom

-- def outFlags (G : Gr) : Set O := (target G).Dom

def mem_verts_of_mem_source {v : V} {i : I} (h : v ∈ source G i) : v ∈ verts G :=
  ran_source_subset_verts ⟨i, h⟩

def mem_verts_of_mem_target {v : V} {o : O} (h : v ∈ target G o) : v ∈ verts G :=
  ran_target_subset_verts ⟨o, h⟩

def mem_edges_of_mem_edgeI {e : E} {i : I} (h : e ∈ edgeI G i) : e ∈ edges G :=
  ran_edgeI_subset_edges ⟨i, h⟩

def mem_edges_of_mem_edgeO {e : E} {o : O} (h : e ∈ edgeO G o) : e ∈ edges G :=
  ran_edgeO_subset_edges ⟨o, h⟩

def IsEdgeSource (G : Gr) (e : E) (v : V) : Prop := ∃ i, v ∈ source G i ∧ e ∈ edgeI G i

def IsEdgeTarget (G : Gr) (e : E) (v : V) : Prop := ∃ o, v ∈ target G o ∧ e ∈ edgeO G o

def IsLink (G : Gr) (e : E) (x y : V) : Prop := IsEdgeSource G e x ∧ IsEdgeTarget G e y

@[implicit_reducible]
def ofIsSourceIsTarget (verts : Gr → Set V) (edges : Gr → Set E)
    (IsEdgeSource : Gr → E → V → Prop) (IsEdgeTarget : Gr → E → V → Prop)
    (mem_verts_of_isEdgeSource : ∀ ⦃G e v⦄, IsEdgeSource G e v → v ∈ verts G)
    (mem_edges_of_isEdgeSource : ∀ ⦃G e v⦄, IsEdgeSource G e v → e ∈ edges G)
    (mem_verts_of_isEdgeTarget : ∀ ⦃G e v⦄, IsEdgeTarget G e v → v ∈ verts G)
    (mem_edges_of_isEdgeTarget : ∀ ⦃G e v⦄, IsEdgeTarget G e v → e ∈ edges G)
    : HyperGraphLike V (E × V) (E × V) E Gr where
  verts := verts
  edges := edges
  source G d := ⟨IsEdgeSource G d.1 d.2, fun _ => d.2⟩
  target G d := ⟨IsEdgeTarget G d.1 d.2, fun _ => d.2⟩
  edgeI G d := ⟨IsEdgeSource G d.1 d.2, fun _ => d.1⟩
  edgeO G d := ⟨IsEdgeTarget G d.1 d.2, fun _ => d.1⟩
  dom_source_eq_dom_edgeI _ := rfl
  dom_target_eq_dom_edgeO _ := rfl
  ran_source_subset_verts _ _ := fun ⟨_, h, h'⟩ => h' ▸ mem_verts_of_isEdgeSource h
  ran_target_subset_verts _ _ := fun ⟨_, h, h'⟩ => h' ▸ mem_verts_of_isEdgeTarget h
  ran_edgeI_subset_edges _ _ := fun ⟨_, h, h'⟩ => h' ▸ mem_edges_of_isEdgeSource h
  ran_edgeO_subset_edges _ _ := fun ⟨_, h, h'⟩ => h' ▸ mem_edges_of_isEdgeTarget h

def Adj (G : Gr) (x y : V) : Prop := ∃ e ∈ edges G, IsEdgeSource G e x ∧ IsEdgeTarget G e y

def FlagsInc (G : Gr) (i : I) (o : O) : Prop := ∃ e, e ∈ edgeI G i ∧ e ∈ edgeO G o

lemma Adj.iff_exists_inFlag_outFlag {G : Gr} {x y : V} :
    Adj G x y ↔ ∃ i o, FlagsInc G i o ∧ x ∈ source G i ∧ y ∈ target G o := by
  simp_rw [Adj, IsEdgeSource, IsEdgeTarget, FlagsInc]
  constructor
  · grind
  · rintro ⟨i, o, ⟨⟨e, he⟩, he'⟩⟩
    use! e, mem_edges_of_mem_edgeI he.1
    grind

structure Dart (G : Gr) where
  i : I
  o : O
  inc : FlagsInc G i o

namespace Dart

@[ext]
protected lemma ext {d d' : Dart G} (hi : d.i = d'.i) (ho : d.o = d'.o) : d = d' := by
  cases d; cases d'; congr

-- lemma inFlag_mem (d : Dart G) : d.i ∈ inFlags G := d.inc.2.1

-- lemma outFlag_mem (d : Dart G) : d.o ∈ outFlags G := d.inc.2.2

-- def src (d : Dart G) : V := source G d.i

-- lemma src_mem (d : Dart G) : d.src ∈ verts G := mapsTo_source d.inFlag_mem

def isSource (d : Dart G) : IsSource G d.edge d.source := d.isLink.1

lemma source_mem (d : Dart G) : d.source ∈ verts G := mem_verts_of_isSource d.isSource

-- def tgt (d : Dart G) : V := target G d.o

-- lemma tgt_mem (d : Dart G) : d.tgt ∈ verts G := mapsTo_target d.outFlag_mem

def isTarget (d : Dart G) : IsTarget G d.edge d.target := d.isLink.2

lemma target_mem (d : Dart G) : d.target ∈ verts G := mem_verts_of_isTarget d.isLink.2

-- def edge (d : Dart G) : E := edgeI G d.i

-- lemma edge_eq_edgeI (d : Dart G) : d.edge = edgeI G d.i := by rfl

-- lemma edge_eq_edgeO (d : Dart G) : d.edge = edgeO G d.o := by rw [←d.inc.1]; rfl

-- lemma edge_mem (d : Dart G) : d.edge ∈ edges G := mapsTo_edgeI d.inFlag_mem

lemma edge_mem (d : Dart G) : d.edge ∈ edges G := mem_edges_of_isSource d.isSource

-- lemma isEdgeSource (d : Dart G) : IsEdgeSource G d.edge d.src :=
--   ⟨d.i, d.inFlag_mem, rfl, d.edge_eq_edgeI⟩

-- lemma isEdgeTarget (d : Dart G) : IsEdgeTarget G d.edge d.tgt :=
--   ⟨d.o, d.outFlag_mem, rfl, d.edge_eq_edgeO.symm⟩

-- noncomputable def ofEdge {e : E} {x y : V} (hsrc : IsEdgeSource G e x) (htgt : IsEdgeTarget G e y) :
--     Dart G where
--   i := Classical.choose hsrc
--   o := Classical.choose htgt
--   inc :=
--     have ⟨hi, _, hei⟩ := Classical.choose_spec hsrc
--     have ⟨ho, _, heo⟩ := Classical.choose_spec htgt
--     ⟨hei.trans heo.symm, hi, ho⟩

-- lemma ext_edge {d d' : Dart G} (hsrc : d.src = d'.src) (htgt : d.tgt = d'.tgt)
--     (hedge : d.edge = d'.edge) : d = d' := by
--   ext
--   · exact eq_of_source_eq_of_edgeI_eq d.inFlag_mem d'.inFlag_mem hsrc hedge
--   · apply eq_of_target_eq_of_edgeO_eq d.outFlag_mem d'.outFlag_mem htgt
--     simp_rw [←edge_eq_edgeO]
--     assumption

-- lemma adj (d : Dart G) : Adj G d.src d.tgt := ⟨d.edge, d.edge_mem, d.isEdgeSource, d.isEdgeTarget⟩

lemma adj (d : Dart G) : Adj G d.source d.target := ⟨d.edge, d.isSource, d.isTarget⟩

def AdjDart (d d' : Dart G) : Prop := d.target = d'.source

end Dart

end HyperGraphLike

open HyperGraphLike

class GraphLike (V E : outParam Type*) (Gr : Type*) extends
    HyperGraphLike V E Gr where
  -- injOn_edgeI : ∀ ⦃G⦄, Set.InjOn (edgeI G) (inFlags G)
  -- injOn_edgeO : ∀ ⦃G⦄, Set.InjOn (edgeO G) (outFlags G)
  exists_unique_isSource_of_mem_edges : ∀ ⦃G e⦄, e ∈ edges G → ∃! x, IsSource G e x
  exists_unique_isTarget_of_mem_edges : ∀ ⦃G e⦄, e ∈ edges G → ∃! x, IsTarget G e x
  -- flagI : Gr → E → I
  -- flagO : Gr → E → O
  -- mapsTo_flagI : ∀ ⦃G⦄, Set.MapsTo (flagI G) (edges G) (inFlags G)
  -- invOn_flagI : ∀ ⦃G⦄, Set.InvOn (flagI G) (edgeI G) (inFlags G) (edges G)
  -- mapsTo_flagO : ∀ ⦃G⦄, Set.MapsTo (flagO G) (edges G) (outFlags G)
  -- invOn_flagO : ∀ ⦃G⦄, Set.InvOn (flagO G) (edgeO G) (outFlags G) (edges G)

namespace GraphLike

@[implicit_reducible]
def ofIsLink (verts : Gr → Set V) (edges : Gr → Set E)
    (IsLink : Gr → E → V → V → Prop)
    (mem_edges_iff_exists_isLink : ∀ ⦃G e⦄, e ∈ edges G ↔ ∃ x y, IsLink G e x y)
    (mem_verts_left_of_isLink : ∀ ⦃G e x y⦄, IsLink G e x y → x ∈ verts G)
    (mem_verts_right_of_isLink : ∀ ⦃G e x y⦄, IsLink G e x y → y ∈ verts G)
    (eq_and_eq_of_isLink_of_isLink : ∀ ⦃G e x x' y y'⦄,
      IsLink G e x y → IsLink G e x' y' → x = x' ∧ y = y') :
    GraphLike V E Gr
    where
  verts := verts
  -- inFlags G := {d | ∃ y, IsLink G d.1 d.2 y}
  -- outFlags G := {d | ∃ x, IsLink G d.1 x d.2}
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
  -- target G d := d.2
  -- source G d := d.2
  -- edgeI G d := d.1
  -- edgeO G d := d.1
  -- mapsTo_source G d := fun ⟨_, hd⟩ => mem_verts_left_of_isLink hd
  -- mapsTo_target G d := fun ⟨_, hd⟩ => mem_verts_right_of_isLink hd
  -- mapsTo_edgeI G d := fun ⟨y, hd⟩ => mem_edges_iff_exists_isLink.mpr ⟨d.2, y, hd⟩
  -- mapsTo_edgeO G d := fun ⟨x, hd⟩ => mem_edges_iff_exists_isLink.mpr ⟨x, d.2, hd⟩
  -- eq_of_source_eq_of_edgeI_eq _ i i' _ _ _ _ := by cases i; cases i'; congr
  -- eq_of_target_eq_of_edgeO_eq _ o o' _ _ _ _ := by cases o; cases o'; congr
  -- flagI G e :=
  --   have : Decidable (∃ x y, IsLink G e x y) := Classical.propDecidable _
  --   if h : ∃ x y, IsLink G e x y then ⟨e, Classical.choose h⟩ else ⟨e, Classical.arbitrary V⟩
  -- flagO G e :=
  --   have : Decidable (∃ y x, IsLink G e x y) := Classical.propDecidable _
  --   if h : ∃ y x, IsLink G e x y then ⟨e, Classical.choose h⟩ else ⟨e, Classical.arbitrary V⟩
  -- mapsTo_flagI G e he := by
  --   rw [mem_edges_iff_exists_isLink] at he
  --   simp [he, Classical.choose_spec he]
  -- invOn_flagI G := by
  --   refine ⟨?_, ?_⟩
  --   · intro ⟨e, x⟩ ⟨y, h⟩
  --     have h' : ∃ x y, IsLink G e x y := ⟨x, y, h⟩
  --     simp only [h', ↓reduceDIte, Prod.mk.injEq, true_and]
  --     exact eq_and_eq_of_isLink_of_isLink (Classical.choose_spec <| Classical.choose_spec h') h |>.1
  --   · intro e he
  --     have h' : ∃ x y, IsLink G e x y := mem_edges_iff_exists_isLink.mp he
  --     simp only [h', ↓reduceDIte]
  -- mapsTo_flagO G e he := by
  --   obtain ⟨x, y, he⟩ := by rwa [mem_edges_iff_exists_isLink] at he
  --   replace he : ∃ y x, IsLink G e x y := ⟨y, x, he⟩
  --   simp [he, Classical.choose_spec he]
  -- invOn_flagO G := by
  --   refine ⟨?_, ?_⟩
  --   · intro ⟨e, y⟩ ⟨x, h⟩
  --     have h' : ∃ y x, IsLink G e x y := ⟨y, x, h⟩
  --     simp only [h', ↓reduceDIte, Prod.mk.injEq, true_and]
  --     exact eq_and_eq_of_isLink_of_isLink (Classical.choose_spec <| Classical.choose_spec h') h |>.2
  --   · intro e he
  --     obtain ⟨x, y, h⟩ : ∃ x y, IsLink G e x y := mem_edges_iff_exists_isLink.mp he
  --     have h' : ∃ y x, IsLink G e x y := ⟨y, x, h⟩
  --     simp only [h', ↓reduceDIte]

@[implicit_reducible]
def ofSourceTarget (verts : Gr → Set V) (edges : Gr → Set E) (src : Gr → E → V) (tgt : Gr → E → V)
    (mem_verts_src : ∀ ⦃G e⦄, e ∈ edges G → src G e ∈ verts G)
    (mem_verts_tgt : ∀ ⦃G e⦄, e ∈ edges G → tgt G e ∈ verts G) :
    GraphLike V E Gr where
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
  -- inFlags := edges
  -- outFlags := edges
  -- source := src
  -- target := tgt
  -- edgeI _ := id
  -- edgeO _ := id
  -- mapsTo_source := mem_verts_src
  -- mapsTo_target := mem_verts_tgt
  -- mapsTo_edgeI _ _ := id
  -- mapsTo_edgeO _ _ := id
  -- eq_of_source_eq_of_edgeI_eq _ _ _ _ _ _ := id
  -- eq_of_target_eq_of_edgeO_eq _ _ _ _ _ _ := id
  -- injOn_edgeI _ := Set.injOn_id _
  -- injOn_edgeO _ := Set.injOn_id _

variable [GraphLike V E Gr] {G : Gr}

-- lemma invOn_edgeI : Set.InvOn (edgeI G) (flagI G) (edges G) (inFlags G) :=
--   (invOn_flagI (G := G)).symm

-- lemma bijOn_flagI : Set.BijOn (flagI G) (edges G) (inFlags G) :=
--   invOn_flagI.symm.bijOn (mapsTo_flagI (G := G)) (mapsTo_edgeI (G := G))

-- lemma bijOn_edgeI : Set.BijOn (edgeI G) (inFlags G) (edges G) :=
--   invOn_flagI.bijOn (mapsTo_edgeI (G := G)) (mapsTo_flagI (G := G))

noncomputable def edgeSource {G : Gr} {e : E} (he : e ∈ edges G) : V :=
  Classical.choose (exists_unique_isSource_of_mem_edges he)

lemma isSource_iff (e : E) (x : V) : IsSource G e x ↔ ∃ h : e ∈ edges G, edgeSource h = x := by
  simp_rw [edgeSource, ExistsUnique.choose_eq_iff]
  exact ⟨fun h => ⟨mem_edges_of_isSource h, h⟩, fun ⟨_, h⟩ => h⟩
  -- constructor
  -- · intro h
  --   use mem_edges_of_isSource h
  --   rwa [edgeSource, ExistsUnique.choose_eq_iff]
  -- · intro ⟨_, h⟩

  -- rw [IsEdgeSource, edgeSource]
  -- constructor
  -- · intro ⟨i, hi, hx, he⟩
  --   rw [←he, invOn_edgeI.2 hi]
  --   exact ⟨mapsTo_edgeI hi, hx⟩
  -- · rintro ⟨he, rfl⟩
  --   use flagI G e, mapsTo_flagI he, rfl, invOn_edgeI.1 he

-- lemma invOn_edgeO : Set.InvOn (edgeO G) (flagO G) (edges G) (outFlags G) :=
--   (invOn_flagO (G := G)).symm

-- lemma bijOn_flagO : Set.BijOn (flagO G) (edges G) (outFlags G) :=
--   invOn_flagO.symm.bijOn (mapsTo_flagO (G := G)) (mapsTo_edgeO (G := G))

-- lemma bijOn_edgeO : Set.BijOn (edgeO G) (outFlags G) (edges G) :=
--   invOn_flagO.bijOn (mapsTo_edgeO (G := G)) (mapsTo_flagO (G := G))

-- def edgeTarget (G : Gr) (e : E) : V := target G <| flagO G e

-- lemma isEdgeTarget_iff (e : E) (x : V) : IsEdgeTarget G e x ↔ e ∈ edges G ∧ edgeTarget G e = x := by
--   rw [IsEdgeTarget, edgeTarget]
--   constructor
--   · intro ⟨o, ho, hx, he⟩
--     rw [←he, invOn_edgeO.2 ho]
--     exact ⟨mapsTo_edgeO ho, hx⟩
--   · rintro ⟨he, rfl⟩
--     use flagO G e, mapsTo_flagO he, rfl, invOn_flagO.2 he

noncomputable def edgeTarget {G : Gr} {e : E} (he : e ∈ edges G) : V :=
  Classical.choose (exists_unique_isTarget_of_mem_edges he)

lemma isTarget_iff (e : E) (x : V) : IsTarget G e x ↔ ∃ h : e ∈ edges G, edgeTarget h = x := by
  simp_rw [edgeTarget, ExistsUnique.choose_eq_iff]
  exact ⟨fun h => ⟨mem_edges_of_isTarget h, h⟩, fun ⟨_, h⟩ => h⟩

end GraphLike

open GraphLike

class SimpleGraphLike (V E : outParam Type*) (Gr : Type*) extends GraphLike V E Gr where
  eq_of_isSource_isSource_isTarget_isTarget : ∀ ⦃G e e' x y⦄,
    IsSource G e x → IsSource G e' x → IsTarget G e y → IsTarget G e' y → e = e'
  -- eq_of_source_eq_of_target_eq : ∀ ⦃G e e'⦄, source G (flagI G e) = source G (flagI G e') →
  --   target G (flagO G e) = target G (flagO G e') → e = e'

class IrreflHyperGraphLike (V E : outParam Type*) (Gr : Type*) extends
    HyperGraphLike V E Gr where
  not_isSource_isTarget : ∀ ⦃G e x⦄, ¬ (IsSource G e x ∧ IsTarget G e x)
  -- edgeI_ne_edgeO_of_source_eq_target : ∀ ⦃G i o⦄, source G i = target G o → edgeI G i ≠ edgeO G o

class SymmHyperGraphLike (V E : outParam Type*) (Gr : Type*) extends
    HyperGraphLike V E Gr where
  inv : Gr → E → E -- this is non-canonical outside of `edges G`
  inv_inv_eq : ∀ ⦃G e⦄, inv G (inv G e) = e
  isSource_iff_isTarget_inv : ∀ ⦃G e x⦄, IsSource G e x ↔ IsTarget G (inv G e) x
  -- swapIO : Gr → I → O
  -- swapOI : Gr → O → I
  -- edgeO_swapIO_eq : ∀ ⦃G i⦄, i ∈ inFlags G → edgeO G (swapIO G i) = edgeI G i
  -- edgeI_swapOI_eq : ∀ ⦃G o⦄, o ∈ outFlags G → edgeI G (swapOI G o) = edgeO G o
  -- mapsTo_swapIO : ∀ ⦃G⦄, Set.MapsTo (swapIO G) (inFlags G) (outFlags G)
  -- mapsTo_swapOI : ∀ ⦃G⦄, Set.MapsTo (swapOI G) (outFlags G) (inFlags G)
  -- invOn_swap : ∀ ⦃G⦄, Set.InvOn (swapOI G) (swapIO G) (inFlags G) (outFlags G)

instance : GraphLike V (V × V) (Digraph V) := ofSourceTarget (Gr := Digraph V)
  (verts := fun _ => Set.univ) (edges := fun G => {p : V × V | G.Adj p.1 p.2})
  (src := fun _ => Prod.fst) (tgt := fun _ => Prod.snd)
  (mem_verts_src := fun _ _ _ => trivial) (mem_verts_tgt := fun _ _ _ => trivial)

instance : SimpleGraphLike V (V × V) (Digraph V) where
  eq_of_isSource_isSource_isTarget_isTarget G := by
    intro ⟨x, y⟩ ⟨x', y'⟩ _ _ ⟨_, hx⟩ ⟨_, hx'⟩ ⟨_, hy⟩ ⟨_, hy'⟩
    congr
    · exact hx.trans hx'.symm
    · exact hy.trans hy'.symm
    -- cases
    -- obtain ⟨_, _⟩ := hx

instance : GraphLike V (E × V × V) (Graph V E) := by
  refine ofIsLink Graph.vertexSet (fun G => {p | G.IsLink p.1 p.2.1 p.2.2})
    (fun G e x y => e.2.1 = x ∧ e.2.2 = y ∧ G.IsLink e.1 x y) ?_ ?_ ?_ ?_
  · simp
  · intro G ⟨e, _⟩ x y ⟨_, _, h⟩
    exact h.left_mem
  · intro G ⟨e, _⟩ x y ⟨_, _, h⟩
    exact h.right_mem
  · rintro G ⟨e, z⟩ x x' y y' ⟨rfl, rfl, h⟩ ⟨rfl, rfl, h'⟩
    simp
  --   exact ⟨rfl, h.right_unique h'⟩
  -- · rintro G (e | e) x y h <;> exact G.left_mem_of_isLink h
  -- · rintro G (e | e) x y h <;> exact h.right_mem
  -- · rintro G (e | e) x x' y y' h h'
    -- · simp at h

instance : SymmHyperGraphLike V (E × V × V) (Graph V E) where
  inv G := fun ⟨e, x, y⟩ => ⟨e, y, x⟩
  inv_inv_eq G := by simp
  isSource_iff_isTarget_inv G := by
    rintro ⟨e, x, y⟩ x'
    simp only [IsSource, exists_and_left, ↓existsAndEq, true_and, IsTarget, exists_eq_left',
      and_congr_right_iff]
    rintro rfl
    exact G.isLink_comm

instance : GraphLike V (V × V) (SimpleGraph V) := by
  refine ofIsLink (fun G => Set.univ) (fun G => {p | G.Adj p.1 p.2})
    (fun G e x y => e.1 = x ∧ e.2 = y ∧ G.Adj x y) ?_ ?_ ?_ ?uniq
  case uniq =>
    rintro G ⟨x, y⟩ _ _ _ _ ⟨rfl, rfl, h⟩ ⟨rfl, rfl, h'⟩
    exact ⟨rfl, rfl⟩
  all_goals simp

instance : SymmHyperGraphLike V (V × V) (SimpleGraph V) where
  inv G := fun ⟨x, y⟩ => ⟨y, x⟩
  inv_inv_eq G := by simp
  isSource_iff_isTarget_inv G := by
    intro ⟨x, y⟩ _
    simp only [IsSource, exists_and_left, ↓existsAndEq, true_and, IsTarget, exists_eq_left',
      and_congr_right_iff]
    rintro rfl
    exact G.adj_comm ..

instance : IrreflHyperGraphLike V (V × V) (SimpleGraph V) where
  not_isSource_isTarget G := by
    intro ⟨x, y⟩ _
    simp only [IsSource, exists_and_left, ↓existsAndEq, true_and, IsTarget, exists_eq_left',
      not_and, and_imp]
    rintro rfl h rfl
    exact G.irrefl

-- class HyperGraphLike₂ (V E : outParam Type*) (Gr : Type*) where
--   verts : Gr → Set V
--   edges : Gr → Set E
--   IsSource : Gr → E → V → Prop
--   IsTarget : Gr → E → V → Prop
--   mem_verts_of_isSource : ∀ ⦃G e v⦄, e ∈ edges G → IsSource G e v → v ∈ verts G
--   mem_verts_of_isTarget : ∀ ⦃G e v⦄, e ∈ edges G → IsTarget G e v → v ∈ verts G
--   mem_edges_of_isSource : ∀ ⦃G e v⦄, e ∈ edges G → IsSource G e v → e ∈ edges G
--   mem_edges_of_isTarget : ∀ ⦃G e v⦄, e ∈ edges G → IsTarget G e v → e ∈ edges G

-- namespace HyperGraphLike₂

-- variable [HyperGraphLike₂ V E Gr]

-- def Adj (G : Gr) (x y : V) : Prop := ∃ e ∈ edges G, IsSource G e x ∧ IsTarget G e y

-- def IsLink (G : Gr) (e : E) (x y : V) : Prop := IsSource G e x ∧ IsTarget G e y

-- structure Dart (G : Gr) where
--   s : V
--   t : V
--   e : E
--   isSource : IsSource G e s
--   isTarget : IsTarget G e t

-- end HyperGraphLike₂

-- class GraphLike₂ (V E : outParam Type*) (Gr : Type*) extends HyperGraphLike₂ V E Gr where
--   source : Gr → E → V
--   target : Gr → E → V
--   isSource_iff : ∀ ⦃G e v⦄, e ∈ edges G → (IsSource G e v ↔ v = source G e)
--   isTarget_iff : ∀ ⦃G e v⦄, e ∈ edges G → (IsTarget G e v ↔ v = target G e)
