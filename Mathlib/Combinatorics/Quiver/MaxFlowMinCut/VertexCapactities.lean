import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Combinatorics.Quiver.MaxFlowMinCut.MaxFlowMinCutAlt

open Finset
open scoped BigOperators


structure FlowNetworkVertex (V : Type*) [Fintype V] extends FlowNetwork V where
  vc : V → ℝ
  vc_nonneg : ∀ u, vc u ≥ 0

/-- A ValidVertexFlow is a relaxedFlow that also satisfies both edge and vertex capacity
  constraints defined in a FlowNetworkVertex. -/
def ValidVertexFlow
(V : Type*) [Fintype V] (G : FlowNetworkVertex V) (g : RelaxedFlow G.toSTVertices) : Prop :=
  ValidFlow G.toFlowNetwork g ∧ ∀ u : V, mk_in g.f {u} ≤ G.vc u

/-- just a simple set with two elements to indicate whether a node is an in or an out
   node. I could have used booleans (which already has nice properties like finiteness and norm_num)
   it would be confusing what True and False meant in that case -/
inductive NodeSide | In | Out
  deriving DecidableEq, Repr

-- For some reason, lean did not see that a set of two elements is finite :(
instance : Fintype NodeSide where
  elems := ⟨[NodeSide.In, NodeSide.Out], by decide⟩
  complete := fun x => by cases x <;> decide

-- This is so that things like norm_num work, just like boolens
@[simp] lemma NodeSide.in_ne_out : NodeSide.In ≠ NodeSide.Out := by decide
@[simp] lemma NodeSide.out_ne_in : NodeSide.Out ≠ NodeSide.In := by decide

open NodeSide in
/-- Ordinary flow network derived from vertex capacity network -/
@[simp]
def ExpandedFlowNetworkVertex (V : Type*) [DecidableEq V] [Fintype V] (G : FlowNetworkVertex V) :
    FlowNetwork (V × NodeSide) where
    -- Canonical source: In vertex of the real source
  s := (G.s, In)
  -- Canonical sink: Out veterx of real sink
  t := (G.t, Out)
  -- This would be really ugly if we didn't define in_ne_out
  source_not_sink := by norm_num
  c := fun x y =>
    match x, y with
    | (u, In), (v, Out) =>
        if h : u = v then G.vc u else 0
    | (u, Out), (v, In) =>
        if v = G.s then 0
        else if u = G.t then 0
        else G.c u v
    | _, _ =>
        0
  nonneg_capacity := by
    intro x y
    rcases x with ⟨u, bu⟩
    rcases y with ⟨v, bv⟩
    -- split by each In/Out case
    -- In/In and Out/Out are trivial
    -- In/Out is because vc is nonneg
    -- Out/In because regular edge capacities
    cases bu <;> cases bv
    · grind
    · grind [G.vc_nonneg u]
    · grind [G.nonneg_capacity u v]
    · gcongr

lemma flow_eq_zero_of_cap_zero {V : Type*} [DecidableEq V] [Fintype V]
    (G : FlowNetworkVertex V)
    (g : RelaxedFlow (ExpandedFlowNetworkVertex V G).toSTVertices)
    (hg : ValidFlow (ExpandedFlowNetworkVertex V G) g)
    {a b : V × NodeSide}
    (hc : (ExpandedFlowNetworkVertex V G).c a b = 0) : g.f a b = 0 := by
  have h_le := hg a b
  have h_nonneg := g.nonneg_flow a b
  rw [hc] at h_le
  linarith

open NodeSide in
/-- Flow into an Out vertex is the same has the flow into an In vertex -/
lemma flow_in_out_eq_flow_in_in
    (V : Type*) [DecidableEq V] [Fintype V]
    (G : FlowNetworkVertex V)
    (g : RelaxedFlow (ExpandedFlowNetworkVertex V G).toSTVertices)
    (hg : ValidFlow (ExpandedFlowNetworkVertex V G) g)
    (u : V) :
    g.f (u, In) (u, Out) = ∑ x, g.f (u, In) x := by
  symm
  apply Finset.sum_eq_single (u, Out)
  · intro ⟨v, b⟩ _ hvb
    apply flow_eq_zero_of_cap_zero G g hg
    -- Simplifies the capacity definition and resolves the unmatched sides
    simp [ExpandedFlowNetworkVertex]
    cases b <;> aesop
  · intro h; simp_all only [ExpandedFlowNetworkVertex, dite_eq_ite, mem_univ, not_true_eq_false]

open NodeSide in
/-- Given a flow on the expanded network, recover the corresponding flow on the original
  FlowNetworkVertex by reading off the flow on edges (u, Out) -> (v, In), which correspond
  to the original edges u -> v.

  We have to use ValidFlow on the expanded graph here because otherwise conservation may not hold -/
def ContractedFlow (V : Type*) [DecidableEq V] [Fintype V] (G : FlowNetworkVertex V)
    (g : RelaxedFlow (ExpandedFlowNetworkVertex V G).toSTVertices)
    (hg : ValidFlow (ExpandedFlowNetworkVertex V G) g) :
    RelaxedFlow G.toSTVertices where
  f u v := g.f (u, Out) (v, In)
  nonneg_flow := fun u v => g.nonneg_flow (u, Out) (v, In)
  conservation := by
    intro v vns vnt
    have hIn  := g.conservation (v, NodeSide.In)
      (by simp_all only [ExpandedFlowNetworkVertex, dite_eq_ite, ne_eq, Prod.mk.injEq, and_true,
        not_false_eq_true] )
      (by simp  [ExpandedFlowNetworkVertex, vnt])
    have hOut := g.conservation (v, NodeSide.Out)
      (by simp [ExpandedFlowNetworkVertex, vns])
      (by simp_all only [ExpandedFlowNetworkVertex, dite_eq_ite, ne_eq, Prod.mk.injEq, and_true,
        not_false_eq_true])
    -- zero capacity implies zero flow
    have hzero : ∀ (a b : V × NodeSide),
    (ExpandedFlowNetworkVertex V G).c a b = 0 → g.f a b = 0 := by
      intro a b hc
      linarith [hg a b, g.nonneg_flow a b]
    -- I am not proud of this code, but it works :)
    have hzeroout : ∀ (w : V) (b : NodeSide), (w, b) ≠ (v, In) →
    g.f (w, b) (v, Out) = 0 := by
      aesop
    simp only [mk_out, ExpandedFlowNetworkVertex, dite_eq_ite, subset_univ, sum_sdiff_eq_sub,
      sum_singleton, sum_sub_distrib, mk_in, sub_left_inj] at hIn hOut
    simp only [mk_out, mk_in, Finset.sum_singleton]
    have hzOut : ∀ x : V, g.f (v, Out) (x, Out) = 0 := fun x =>
      hzero (v, Out) (x, Out) (by simp)
    have hzIn : ∀ x : V, g.f (x, In) (v, In) = 0 := fun x =>
      hzero (x, In) (v, In) (by simp)
    have NodeSide_sum_out :
    ∀ x : V, ∑ b : NodeSide, g.f (v, Out) (x, b) = g.f (v, Out) (x, In) := by
      intro x; have : (Finset.univ : Finset NodeSide) = {In, Out} := by decide
      simp only [this, ExpandedFlowNetworkVertex, dite_eq_ite, Finset.sum_pair NodeSide.in_ne_out,
        hzOut, add_zero]
    have NodeSide_sum_in : ∀ x : V, ∑ b : NodeSide, g.f (x, b) (v, In) = g.f (x, Out) (v, In) := by
      intro x; have : (Finset.univ : Finset NodeSide) = {In, Out} := by decide
      simp [this, Finset.sum_pair NodeSide.in_ne_out, hzIn]
    have lhs_collapse : ∑ x : V × NodeSide, g.f (v, Out) x = ∑ x : V, g.f (v, Out) (x, In) := by
      rw [← Finset.univ_product_univ, Finset.sum_product]; simp [NodeSide_sum_out]
    have rhs_collapse : ∑ x : V × NodeSide, g.f x (v, In) = ∑ x : V, g.f (x, Out) (v, In) := by
      rw [← Finset.univ_product_univ, Finset.sum_product]; simp [NodeSide_sum_in]
    have mid : ∑ x : V × NodeSide, g.f (v, Out) x = ∑ x : V × NodeSide, g.f x (v, In) := by
      have hA : ∑ x : V × NodeSide, g.f (v, In) x = g.f (v, In) (v, Out) :=
        (flow_in_out_eq_flow_in_in V G g hg v).symm
      have hB : ∑ x : V × NodeSide, g.f x (v, Out) = g.f (v, In) (v, Out) :=
        Finset.sum_eq_single (f := fun x => g.f x (v, Out)) (v, In)
          (fun p _ hp => by obtain ⟨w, b⟩ := p; exact hzeroout w b hp) (by simp)
      linarith [hIn, hOut, hA, hB]
    have total_eq : ∑ x : V, g.f (v, Out) (x, In) = ∑ x : V, g.f (x, Out) (v, In) := by
      linarith [lhs_collapse, rhs_collapse, mid]
    have split : ∀ (f : V → ℝ), ∑ x : V, f x = f v + ∑ x ∈ Finset.univ \ {v}, f x := fun f => by
      rw [← Finset.sum_sdiff (Finset.subset_univ {v})]; simp
    have s1 : ∑ x : V, g.f (v, Out) (x, In) =
        g.f (v, Out) (v, In) + ∑ x ∈ Finset.univ \ {v}, g.f (v, Out) (x, In) := split _
    have s2 : ∑ x : V, g.f (x, Out) (v, In) =
        g.f (v, Out) (v, In) + ∑ x ∈ Finset.univ \ {v}, g.f (x, Out) (v, In) := split _
    have total_eq' :
        ∑ x ∈ Finset.univ \ {v}, g.f (v, Out) (x, In) =
          ∑ x ∈ Finset.univ \ {v}, g.f (x, Out) (v, In) := by
      linarith [total_eq, s1, s2]
    clear hzOut hzIn NodeSide_sum_out NodeSide_sum_in
      lhs_collapse rhs_collapse mid total_eq split s1 s2
    simp_all only [ExpandedFlowNetworkVertex, dite_eq_ite, ne_eq, Prod.forall, Prod.mk.injEq,
      not_and, subset_univ, sum_sdiff_eq_sub, sum_singleton, sub_left_inj]
  no_edges_in_source := by
    intro u
    apply le_antisymm _ (g.nonneg_flow (u, Out) (G.s, In))
    have key := hg (u, Out) (G.s, In)
    simp only [ExpandedFlowNetworkVertex, dite_eq_ite, ↓reduceIte] at key
    exact key
  no_edges_out_sink := by
    intro u
    apply le_antisymm _ (g.nonneg_flow (G.t, Out) (u, In))
    have key := hg (G.t, Out) (u, In)
    simp only [ExpandedFlowNetworkVertex, dite_eq_ite, ↓reduceIte, ite_self] at key
    exact key


open NodeSide in
theorem FlowInducesValidVertexFlow (V : Type*) [DecidableEq V] [Fintype V] (G : FlowNetworkVertex V)
    (g : RelaxedFlow (ExpandedFlowNetworkVertex V G).toSTVertices)
    (hg : ValidFlow (ExpandedFlowNetworkVertex V G) g) :
    ValidVertexFlow V G (ContractedFlow V G g hg) := by
  constructor
  · intro u v
    have hcg := hg (u, Out) (v, In)
    have h1 := hg (u, Out) (v, In)
    simp only [ContractedFlow, ExpandedFlowNetworkVertex] at *
    split_ifs at h1 <;> try linarith [G.nonneg_capacity u v, g.nonneg_flow (u, Out) (v, In)]
  · intro u
    by_cases h : u = G.s
    · simp_all only [mk_in, ContractedFlow, ExpandedFlowNetworkVertex, dite_eq_ite, sum_singleton,
      subset_univ, sum_sdiff_eq_sub, tsub_le_iff_right]
      have hs0 : ∀ vs : (V × NodeSide), g.f vs (u, In) = 0 := by
          intro vs
          have hcg := hg vs (u, In)
          apply le_antisymm
          · aesop
          · exact g.nonneg_flow vs (u, In)
      have rhs : ∑ x, g.f (x, Out) (G.s, In) = 0 :=
        by simp_all only [ExpandedFlowNetworkVertex, dite_eq_ite, Prod.forall, sum_const_zero]
      rw [rhs]
      linarith [g.nonneg_flow (G.s, Out) (G.s, In), G.vc_nonneg G.s]
    · push Not at h
      simp only [mk_in, ContractedFlow, ExpandedFlowNetworkVertex, dite_eq_ite, sum_singleton,
        subset_univ, sum_sdiff_eq_sub, tsub_le_iff_right]
      have key     := g.conservation (u, In) (by simp [h]) (by simp)
      have hInOut  := hg (u, In) (u, Out)
      simp only [ExpandedFlowNetworkVertex, dite_eq_ite, ↓reduceIte] at hInOut
      -- conservation: mk_out {(u,In)} = mk_in {(u,In)}, unfold to get the sum equation
      have hcons : ∑ x, g.f x (u, In) = ∑ x, g.f (u, In) x := by
        simp only [mk_out, mk_in, Finset.sum_singleton, subset_univ, sum_sdiff_eq_sub] at key
        linarith
      -- flow_in_out_eq_flow_in_in: g.f (u,In) (u,Out) = ∑ x, g.f (u,In) x
      have hfio := flow_in_out_eq_flow_in_in V G g hg u
      have h3 : ∑ x, g.f (x, Out) (u, In) ≤ ∑ x, g.f x (u, In) := by
        rw [← Finset.univ_product_univ, Finset.sum_product]
        apply Finset.sum_le_sum; intro x _
        have : (Finset.univ : Finset NodeSide) = {In, Out} := by decide
        simp only [this, Finset.sum_pair NodeSide.in_ne_out]
        linarith [g.nonneg_flow (x, In) (u, In)]
      -- chain: ∑(x,Out)->(u,In) ≤ ∑ x->(u,In) = ∑ (u,In)->x = (u,In)->(u,Out) ≤ vc u
      linarith [g.nonneg_flow (u, Out) (u, In)]
