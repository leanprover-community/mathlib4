/-
Copyright (c) 2026 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
public import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Greedy Coloring
-/

@[expose] public section Dependencies

set_option warn.sorry false
set_option linter.style.longLine false

-- #35619
theorem SimpleGraph.isClique_top {α : Type*} (s : Set α) : (⊤ : SimpleGraph α).IsClique s := sorry
-- #35619
theorem SimpleGraph.isClique_univ_iff {V : Type*} (G : SimpleGraph V) : G.IsClique .univ ↔ G = ⊤ := sorry
-- #36626
theorem IsLowerSet.eqOn_id_of_injOn_of_forall_not_lt {α : Type*} {r : α → α → Prop} [IsWellOrder α r] {s : Set α} (hs : @IsLowerSet α ⟨r⟩ s) {f : α → α} (hf : s.InjOn f) (h : ∀ x ∈ s, ¬r x (f x)) : s.EqOn f id := sorry
-- #36626
theorem IsWellOrder.eq_id_of_injective_of_forall_not_lt {α : Type*} {r : α → α → Prop} [IsWellOrder α r] {f : α → α} (hf : f.Injective) (h : ∀ x, ¬r x (f x)) : f = id := sorry
/-- #38422 -/
@[simps] def SimpleGraph.Coloring.homMap {V α : Type*} {G : SimpleGraph V} (f : G.Coloring α) : G →g G.map f := ⟨f, sorry⟩

end Dependencies

public section

namespace SimpleGraph

open Cardinal Ordinal

variable {V : Type*} (G : SimpleGraph V) (r : V → V → Prop) [IsWellOrder V r]

/-- A greedy coloring of the graph where the vertices are greedily colored in the order specified
by the given well-order. The colors are the vertices of the graph, ordered by the same
well-order. -/
noncomputable def greedyColoring : G.Coloring V :=
  let f v ih :=
    -- The set of possible colors is the complement of the set of colors that are already taken by
    -- neighbors of `v` that were already colored
    let s := {(ih u hu).val | (u : V) (hu : r u v) (_ : G.Adj u v)}ᶜ
    -- This set is not empty since `v` itself is always a possible color
    have : v ∈ s := fun ⟨u, hu, _, heq⟩ ↦ heq ▸ (ih u hu).prop <| hu
    -- Color `v` with the minimum possible color, ordered by the well-order
    ⟨IsWellFounded.wf.min s ⟨v, this⟩, IsWellFounded.wf.not_lt_min s this⟩
  let toFun v :=
    -- Recurse to color each vertex, ordered by the well-order
    IsWellFounded.fix (motive := ({ c // ¬r · c })) r f v |>.val
  { toFun := toFun
    map_rel' {u v} hadj heq := by
      -- As `r` is trichotomous and `u ≠ v` because they are adjacent in the graph, wlog `r u v`
      wlog hr : r u v
      · exact hadj.ne <| Std.Trichotomous.trichotomous u v hr <| this G r hadj.symm heq.symm
      -- Therefore the color of `u` was considered when choosing a color for `v`
      let sv := {toFun u | (u : V) (hu : r u v) (_ : G.Adj u v)}
      have : toFun u ∈ sv := ⟨u, hr, hadj, rfl⟩
      -- Since the color of `v` was chosen to be the minimum of the complement of `sv`,
      -- it can't be in `sv`, so surely the colors of `u` and `v` cannot be the same
      refine absurd this <| heq ▸ ?_
      unfold toFun
      rw [IsWellFounded.fix_eq]
      refine IsWellFounded.wf.min_mem svᶜ ⟨v, fun ⟨w, hw, _, heq'⟩ ↦ absurd hw ?_⟩
      rw [← heq']
      exact IsWellFounded.fix r f w |>.prop }

variable {G} in
/-- Given a coloring of a graph, consider the mapped graph `G.map f` which can be thought of as
taking the original graph `G` and considering every color class (independent set) as a single
vertex. This greedily colors this graph by the given order on colors, which produces a new coloring
of the original graph. -/
noncomputable def Coloring.recolorGreedily {α : Type*} (r : α → α → Prop) [IsWellOrder α r]
    (f : G.Coloring α) : G.Coloring α :=
  G.map f |>.greedyColoring r |>.comp f.homMap

/-- The color assigned to a vertex `v` by greedy coloring is not greater than `v` -/
theorem not_lt_greedyColoring (v : V) : ¬r v (G.greedyColoring r v) := by
  grind [greedyColoring, RelHom.coeFn_mk]

/-- The set of colors that `v` could not use when `G` was greedily colored in the order specified
by the given well-order -/
def greedyColorsBefore (v : V) : Set V :=
  {G.greedyColoring r u | (u) (_ : r u v) (_ : G.Adj u v)}

variable {G r} in
theorem greedyColoring_mem_greedyColorsBefore {u v : V} (hr : r u v) (hadj : G.Adj u v) :
    G.greedyColoring r u ∈ G.greedyColorsBefore r v :=
  ⟨u, hr, hadj, rfl⟩

theorem lt_of_mem_greedyColorsBefore {u v : V} (h : u ∈ G.greedyColorsBefore r v) : r u v := by
  obtain ⟨w, hr, _, rfl⟩ := h
  exact trans_trichotomous_left (G.not_lt_greedyColoring r w) hr

/-- Greedy coloring cannot get stuck since it is always possible for a vertex to be its own color -/
theorem notMem_greedyColorsBefore_self (v : V) : v ∉ G.greedyColorsBefore r v :=
  fun ⟨u, hu, _, heq⟩ ↦ heq ▸ G.not_lt_greedyColoring r u <| hu

theorem greedyColorsBefore_subset_image_neighborSet (v : V) :
    G.greedyColorsBefore r v ⊆ G.greedyColoring r '' G.neighborSet v :=
  fun _u ⟨w, _, hwv, hu⟩ ↦ ⟨w, hwv.symm, hu⟩

/-- Greedy coloring assigns the smallest available color -/
theorem greedyColoring_eq_min (v : V) :
    G.greedyColoring r v = IsWellFounded.wf.min (r := r) (G.greedyColorsBefore r v)ᶜ
      ⟨v, G.notMem_greedyColorsBefore_self r v⟩ := by
  rw [greedyColoring, RelHom.coeFn_mk, IsWellFounded.fix_eq]
  rfl

theorem greedyColoring_notMem_greedyColorsBefore (v : V) :
    G.greedyColoring r v ∉ G.greedyColorsBefore r v := by
  rw [greedyColoring_eq_min, ← Set.mem_compl_iff]
  apply WellFounded.min_mem

variable {G r} in
theorem mem_greedyColorsBefore_of_lt_greedyColoring {u v : V} (h : r u (G.greedyColoring r v)) :
    u ∈ G.greedyColorsBefore r v := by
  rw [greedyColoring_eq_min] at h
  exact WellFounded.mem_of_lt_min_compl h

variable {G r} in
theorem greedyColoring_eq_iff_subset_and_notMem {v c : V} :
    G.greedyColoring r v = c ↔
      {u | r u c} ⊆ G.greedyColorsBefore r v ∧ c ∉ G.greedyColorsBefore r v := by
  refine ⟨(· ▸ ⟨?_, ?_⟩), fun ⟨hsub, hmem⟩ ↦ ?_⟩
  · exact fun _ ↦ mem_greedyColorsBefore_of_lt_greedyColoring
  · exact G.greedyColoring_notMem_greedyColorsBefore r v
  · rw [greedyColoring_eq_min]
    exact WellFounded.min_eq_of_forall_not_lt _ hmem <| Set.compl_subset_compl.mpr hsub

variable {G r} in
theorem greedyColoring_eq_of_greedyColorsBefore_eq {v c : V}
    (h : G.greedyColorsBefore r v = {u | r u c}) : G.greedyColoring r v = c := by
  rw [greedyColoring_eq_iff_subset_and_notMem, h]
  exact ⟨Set.Subset.rfl, irrefl c⟩

variable {G r} in
theorem greedyColoring_eq_self_tfae {v : V} :
    [G.greedyColoring r v = v, G.greedyColorsBefore r v = {u | r u v},
      {u | r u v} ⊆ G.greedyColorsBefore r v].TFAE := by
  tfae_have 1 → 3 := fun h u ↦ by
    nth_rw 1 [← h]
    exact mem_greedyColorsBefore_of_lt_greedyColoring
  tfae_have 2 → 1 := greedyColoring_eq_of_greedyColorsBefore_eq
  tfae_have 3 → 2 := antisymm fun _ ↦ G.lt_of_mem_greedyColorsBefore r
  tfae_finish

theorem isLowerSet_range_greedyColoring : @IsLowerSet V ⟨r⟩ <| Set.range <| G.greedyColoring r := by
  rintro _ u hle ⟨v, rfl⟩
  rcases mem_greedyColorsBefore_of_lt_greedyColoring hle with ⟨u, _, _, rfl⟩
  exact Set.mem_range_self u

theorem mk_greedyColorsBefore_le_coe_degree (v : V) [Fintype <| G.neighborSet v] :
    #(G.greedyColorsBefore r v) ≤ G.degree v := by
  rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_def, ← Set.ncard_eq_toFinset_card',
    Set.cast_ncard <| Set.toFinite _]
  grw [← mk_image_le (f := G.greedyColoring r) (s := G.neighborSet v)]
  exact mk_le_mk_of_subset <| G.greedyColorsBefore_subset_image_neighborSet r v

theorem encard_greedyColorsBefore_le_coe_degree (v : V) [Fintype <| G.neighborSet v] :
    (G.greedyColorsBefore r v).encard ≤ G.degree v := by
  grw [G.greedyColorsBefore_subset_image_neighborSet r v, Set.encard_image_le]
  rw [← card_neighborFinset_eq_degree, neighborFinset_def, Set.encard_eq_coe_toFinset_card]

theorem ncard_greedyColorsBefore_le_degree (v : V) [Fintype <| G.neighborSet v] :
    (G.greedyColorsBefore r v).ncard ≤ G.degree v := by
  grw [← Nat.cast_le (α := ℕ∞), ← G.encard_greedyColorsBefore_le_coe_degree r v]
  apply Set.ncard_le_encard

variable {G r} in
theorem greedyColoring_isClique_tfae {s : Set V} (hs : @IsLowerSet V ⟨r⟩ s) :
    [s.InjOn (G.greedyColoring r), s.EqOn (G.greedyColoring r) id, G.IsClique s].TFAE := by
  tfae_have 2 → 3 := fun h u hu v hv hne ↦ by
    wlog huv : r u v
    · refine this hs h v hv u hu hne.symm ?_ |>.symm
      exact hne.imp_symm <| Std.Trichotomous.trichotomous u v huv
    obtain ⟨u, hr, hadj, rfl⟩ := mem_greedyColorsBefore_of_lt_greedyColoring (h hv ▸ id_def v ▸ huv)
    rwa [h <| hs hr hv]
  tfae_have 3 → 2 := fun h v hv ↦ by
    induction v using IsWellFounded.induction r with | ind v ih
    rw [id_eq, greedyColoring_eq_self_tfae.out 0 2 rfl]
    refine fun u huv ↦ ⟨u, huv, h (hs huv hv) hv (irrefl v <| · ▸ huv), ?_⟩
    rw [ih u huv <| hs huv hv, id_eq]
  tfae_have 1 → 2 :=
    fun h ↦ hs.eqOn_id_of_injOn_of_forall_not_lt h fun v _ ↦ G.not_lt_greedyColoring r v
  tfae_have 2 → 1 := fun h ↦ s.injOn_id.congr h.symm
  tfae_finish

variable {G r} in
theorem greedyColoring_eq_id_tfae :
    [Function.Injective (G.greedyColoring r), ↑(G.greedyColoring r) = id, G = ⊤].TFAE := by
  rw [← Set.eqOn_univ, ← Set.injOn_univ, ← isClique_univ_iff]
  exact greedyColoring_isClique_tfae <| @isLowerSet_univ V ⟨r⟩

@[simp]
theorem greedyColoring_top_eq_id : greedyColoring ⊤ r = .id :=
  RelHom.ext <| congrFun <| greedyColoring_eq_id_tfae.out 2 1 |>.mp rfl

theorem card_typein_greedyColoring_le_mk_greedyColorsBefore (v : V) :
    (typein r <| G.greedyColoring r v).card ≤ #(G.greedyColorsBefore r v) := by
  rw [greedyColoring_eq_min]
  apply card_typein_min_le_mk

theorem typein_greedyColoring_le_coe_degree (v : V) [Fintype <| G.neighborSet v] :
    typein r (G.greedyColoring r v) ≤ G.degree v := by
  grw [← card_le_nat, card_typein_greedyColoring_le_mk_greedyColorsBefore,
    mk_greedyColorsBefore_le_coe_degree]

theorem not_lt_enum_ord_greedyColorsBefore (v : V) (h : G.greedyColorsBefore r v |>.Finite) :
    ¬r (enum r ⟨#(G.greedyColorsBefore r v) |>.ord,
      ord_mk_lt_type r h ⟨v, G.notMem_greedyColorsBefore_self r v⟩⟩) (G.greedyColoring r v) := by
  rw [greedyColoring_eq_min]
  exact not_lt_enum_ord_mk_min_compl r h _

theorem not_lt_enum_degree_greedyColoring (v : V) [Fintype <| G.neighborSet v] :
    ¬r (enum r ⟨G.degree v, by
      rw [Set.mem_Iio, ← card_neighborFinset_eq_degree, ← ord_nat, ← Cardinal.mk_coe_finset]
      exact ord_mk_lt_type r (Finset.finite_toSet _) ⟨v, G.notMem_neighborFinset_self v⟩
    ⟩) (G.greedyColoring r v) := by
  grw [← typein_le_typein, typein_enum, typein_greedyColoring_le_coe_degree]

variable {G} in
/-- A graph is `α`-colorable iff there exists a well-ordering of its vertices such that
greedy coloring uses at most `|α|` colors -/
theorem nonempty_coloring_iff_exists_isWellOrder {α : Type*} :
    Nonempty (G.Coloring α) ↔ ∃ (r : V → V → Prop) (_ : IsWellOrder V r),
      Nonempty (Set.range (G.greedyColoring r) ↪ α) := by
  refine ⟨fun ⟨C⟩ ↦ ?_,
    fun ⟨r, _, ⟨f⟩⟩ ↦ ⟨Embedding.completeGraph f |>.toHom.comp <| G.greedyColoring r |>.attach⟩⟩
  -- Take arbitrary well-orders on `α` and `V`, then order the vertices first by their color,
  -- and then by themselves to break ties (i.e. use the lexicographic order).
  let r := Prod.Lex WellOrderingRel WellOrderingRel |>.onFun fun v ↦ (C v, v)
  have : IsWellOrder V r := Function.Injective.isWellOrder _ fun _ _ h ↦ congr(($h).snd)
  -- For every color `v` assigned in the greedy coloring, let `f v` be the first vertex that was
  -- greedy-colored by the color `v`, with respect to the order `r`.
  let f : Set.range (G.greedyColoring r) → V := (IsWellFounded.wf.min (r := r) _ <| ·.prop)
  -- We claim that `C ∘ f` is injective.
  refine ⟨r, this, C ∘ f, fun u v heq ↦ Subtype.ext ?_⟩
  -- WLOG `r u v` since `r` is trichotomous.
  wlog hr : r u v
  · grind [Std.Trichotomous.trichotomous (r := r)]
  -- Since `f v` got the greedy-color `v`,
  have : G.greedyColoring r (f v) = v := WellFounded.min_mem _ _ v.prop
  -- and `u` precedes `v`, there must exist a `w` before `f v` with color `u` and `G.Adj w (f v)`.
  have ⟨w, hrw, hadj, hw⟩ := mem_greedyColorsBefore_of_lt_greedyColoring <| this ▸ hr
  -- Since `f u` is the first vertex with color `u`, we get `f u ≤ w < f v` (using `r`).
  have hnrw : ¬r w (f u) := WellFounded.not_lt_min _ _ <| by exact hw
  -- Due to the lexicographic order and `C (f u) = C (f v)`, we get `C w = C (f v)`.
  -- But since `G.Adj w (f v)` and `C` is a valid coloring, this is a contradiction.
  exact absurd (by grind) <| C.map_adj hadj

theorem coe_greedyColoringOfEmbedding_le_degree {n : ℕ} (f : V ↪ Fin n) (v : V)
    [Fintype <| G.neighborSet v] :
    (G.coloringOfEmbedding f).recolorGreedily LT.lt v ≤ G.degree v := by
  classical
  grw [← G.degree_map f, ← Nat.cast_le (α := Ordinal),
    ← typein_greedyColoring_le_coe_degree _ LT.lt, typein_lt_fin]
  rfl

/-- A coloring of a graph `G` using at most `G.maxDegree + 1` colors,
constructed by greedy coloring in an arbitrary order -/
noncomputable def coloringMaxDegreeAddOne [Fintype V] [DecidableRel G.Adj] :
    G.Coloring <| Fin <| G.maxDegree + 1 :=
  .castLT (G.coloringOfEmbedding (Fintype.equivFin V).toEmbedding |>.recolorGreedily LT.lt)
    fun v ↦ by
      grw [coe_greedyColoringOfEmbedding_le_degree, degree_le_maxDegree]
      apply Nat.lt_add_one

theorem colorable_maxDegree_add_one [Fintype V] [DecidableRel G.Adj] :
    G.Colorable <| G.maxDegree + 1 :=
  ⟨G.coloringMaxDegreeAddOne⟩

theorem chromaticNumber_le_maxDegree_add_one [Fintype V] [DecidableRel G.Adj] :
    G.chromaticNumber ≤ G.maxDegree + 1 :=
  G.colorable_maxDegree_add_one.chromaticNumber_le

end SimpleGraph
