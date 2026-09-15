/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.HypergraphLike.Basic

/-!
# Parallel edges in hypergraph-like structures

`HyperGraphLike.Parallel` compares active edges through their complete incidence fibers, preserving
attached vertices, incidence multiplicity, and both source and target roles.
`HyperGraphLike.NoParallelEdge` requires active parallel edges to be equal. This file develops their
general incidence and compatibility API.
-/

@[expose] public section

open Set Function

namespace HyperGraphLike

variable {V I E Gr : Type*} {G : Gr} [HyperGraphLike V I E Gr] {u u' v v' w : V} {i j : I} {e f : E}
  {Gr₂ : Type*} [HyperGraphLike V I E Gr₂]

section Parallel

/-- Two edges are parallel if their incidence fibers admit a bijection preserving the attached
vertex and both source and target roles. Incidence labels are ignored, but multiplicities are
preserved. Both edges must be active, including when their incidence fibers are empty. -/
def Parallel (G : Gr) (e f : E) : Prop :=
  e ∈ E(G) ∧ f ∈ E(G) ∧ ∃ φ : edgeFiber G e ≃ edgeFiber G f,
    (∀ i, toVert G ⟨(φ i : I), edgeFiber_subset_incs (φ i).property⟩ =
      toVert G ⟨(i : I), edgeFiber_subset_incs i.property⟩) ∧
    (∀ i, IsSource G (φ i : I) ↔ IsSource G (i : I)) ∧
    (∀ i, IsTarget G (φ i : I) ↔ IsTarget G (i : I))

lemma parallel_iff [Nonempty V] : Parallel G e f ↔
    e ∈ E(G) ∧ f ∈ E(G) ∧ ∃ φ : edgeFiber G e ≃ edgeFiber G f,
      (∀ i, attach G (φ i : I) = attach G (i : I)) ∧
      (∀ i, IsSource G (φ i : I) ↔ IsSource G (i : I)) ∧
      (∀ i, IsTarget G (φ i : I) ↔ IsTarget G (i : I)) := by
  simp only [Parallel, Subtype.ext_iff, toVert_eq_attach]

@[grind →]
lemma Parallel.left_mem (h : Parallel G e f) : e ∈ E(G) := h.1

@[grind →]
lemma Parallel.right_mem (h : Parallel G e f) : f ∈ E(G) := h.2.1

lemma Parallel.refl (he : e ∈ E(G)) : Parallel G e e :=
  ⟨he, he, Equiv.refl _, fun _ ↦ rfl, fun _ ↦ Iff.rfl, fun _ ↦ Iff.rfl⟩

@[simp]
lemma parallel_self_iff : Parallel G e e ↔ e ∈ E(G) := ⟨Parallel.left_mem, Parallel.refl⟩

@[simp]
lemma not_parallel_of_notMem_edges (he : e ∉ E(G)) : ¬ Parallel G e f := fun h ↦ he h.left_mem

@[simp]
lemma not_parallel_of_notMem_edges_right (hf : f ∉ E(G)) : ¬ Parallel G e f :=
  fun h ↦ hf h.right_mem

@[symm]
lemma Parallel.symm (h : Parallel G e f) : Parallel G f e := by
  obtain ⟨he, hf, φ, hv, hs, ht⟩ := h
  refine ⟨hf, he, φ.symm, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_⟩
  · simpa using (hv (φ.symm i)).symm
  · simpa using (hs (φ.symm i)).symm
  simpa using (ht (φ.symm i)).symm

instance : Std.Symm (Parallel G) where
  symm _ _ := Parallel.symm

lemma Parallel.trans {g : E} (h : Parallel G e f) (h' : Parallel G f g) : Parallel G e g := by
  obtain ⟨he, hf, φ, hv, hs, ht⟩ := h
  obtain ⟨_, hg, ψ, hv', hs', ht'⟩ := h'
  exact ⟨he, hg, φ.trans ψ, fun i ↦ (hv' (φ i)).trans (hv i),
    fun i ↦ (hs' (φ i)).trans (hs i), fun i ↦ (ht' (φ i)).trans (ht i)⟩

instance : IsTrans E (Parallel G) where
  trans _ _ _ := Parallel.trans

lemma Parallel.order_eq (h : Parallel G e f) : order G e = order G f := by
  simpa only [order_eq_encard_edgeFiber] using encard_congr h.2.2.choose

lemma Parallel.incVerts_eq (h : Parallel G e f) : incVerts G e = incVerts G f := by
  suffices ∀ {e f : E}, Parallel G e f → incVerts G e ⊆ incVerts G f from
    (this h).antisymm (this h.symm)
  intro e f hp v hv
  let : Nonempty V := ⟨v⟩
  obtain ⟨_, _, φ, ha, _, _⟩ := parallel_iff.mp hp
  rw [incVerts_eq_image] at hv ⊢
  obtain ⟨i, hi, hiv⟩ := hv
  exact ⟨φ ⟨i, hi⟩, (φ ⟨i, hi⟩).property, (ha ⟨i, hi⟩).trans hiv⟩

lemma Parallel.isLink_iff (h : Parallel G e f) : IsLink G e u v ↔ IsLink G f u v := by
  suffices ∀ {e f : E}, Parallel G e f → IsLink G e u v → IsLink G f u v from ⟨this h, this h.symm⟩
  intro e f hp hl
  let : Nonempty V := ⟨u⟩
  let : Nonempty E := ⟨e⟩
  obtain ⟨_, _, φ, hv, hs, ht⟩ := parallel_iff.mp hp
  obtain ⟨i, j, hij, hi, hj, hie, hje, hiu, hjv⟩ := isLink_iff_exists_incidence.mp hl
  let a : edgeFiber G e := ⟨i, mem_edgeFiber.mpr ⟨hi.mem, hie⟩⟩
  let b : edgeFiber G e := ⟨j, mem_edgeFiber.mpr ⟨hj.mem, hje⟩⟩
  exact isLink_iff_exists_incidence.mpr ⟨φ a, φ b,
    fun heq ↦ hij (congrArg Subtype.val (φ.injective (Subtype.ext heq))),
    (hs a).mpr hi, (ht b).mpr hj,
    (mem_edgeFiber.mp (φ a).property).2, (mem_edgeFiber.mp (φ b).property).2,
    (hv a).trans hiu, (hv b).trans hjv⟩

lemma Parallel.of_compatible (h : Parallel G e f) {H : Gr₂} (hGH : Compatible G H)
    (heH : e ∈ E(H)) (hfH : f ∈ E(H)) (he : edgeFiber G e = edgeFiber H e)
    (hf : edgeFiber G f = edgeFiber H f) : Parallel H e f := by
  obtain ⟨_, _, φ, hv, hs, ht⟩ := h
  let a := (equivOfEq he).symm
  let b := equivOfEq hf
  refine ⟨heH, hfH, a.trans (φ.trans b), fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_⟩
  · apply Subtype.ext
    exact (hGH.toVert_eq (edgeFiber_subset_incs (φ (a i)).property)
      (edgeFiber_subset_incs (b (φ (a i))).property)).symm.trans
      ((congrArg Subtype.val (hv (a i))).trans
        (hGH.toVert_eq (edgeFiber_subset_incs (a i).property)
          (edgeFiber_subset_incs i.property)))
  · exact (hGH.isSource_iff (edgeFiber_subset_incs (φ (a i)).property)
      (edgeFiber_subset_incs (b (φ (a i))).property)).symm.trans
      ((hs (a i)).trans
        (hGH.isSource_iff (edgeFiber_subset_incs (a i).property)
        (edgeFiber_subset_incs i.property)))
  exact (hGH.isTarget_iff (edgeFiber_subset_incs (φ (a i)).property)
    (edgeFiber_subset_incs (b (φ (a i))).property)).symm.trans
    ((ht (a i)).trans
      (hGH.isTarget_iff (edgeFiber_subset_incs (a i).property)
        (edgeFiber_subset_incs i.property)))

lemma Compatible.parallel_congr_of_edgeFiber_eq {H : Gr₂} (h : Compatible G H)
    (heMem : e ∈ E(G) ↔ e ∈ E(H)) (hfMem : f ∈ E(G) ↔ f ∈ E(H))
    (he : edgeFiber G e = edgeFiber H e) (hf : edgeFiber G f = edgeFiber H f) :
    Parallel G e f ↔ Parallel H e f :=
  ⟨fun hp ↦ hp.of_compatible h (heMem.mp hp.left_mem) (hfMem.mp hp.right_mem) he hf,
    fun hp ↦ hp.of_compatible h.symm (heMem.mpr hp.left_mem) (hfMem.mpr hp.right_mem)
      he.symm hf.symm⟩

/-- Two edges of order zero are parallel exactly when both are active. -/
lemma parallel_iff_of_order_eq_zero (he : order G e = 0) (hf : order G f = 0) :
    Parallel G e f ↔ e ∈ E(G) ∧ f ∈ E(G) := by
  refine ⟨fun h ↦ ⟨h.left_mem, h.right_mem⟩, fun ⟨heG, hfG⟩ ↦ ?_⟩
  have he' := incVerts_eq_empty.mp (order_eq_zero.mp he)
  have hf' := incVerts_eq_empty.mp (order_eq_zero.mp hf)
  refine ⟨heG, hfG, equivOfEq (he'.trans hf'.symm), ?_, ?_, ?_⟩ <;>
    exact fun i ↦ (notMem_empty i.val (he' ▸ i.property)).elim

end Parallel

/-- A hypergraph-like object has no parallel edges if active edges with attachment- and
role-preserving bijections between their incidence fibers are equal. -/
class NoParallelEdge (G : Gr) : Prop where
  /-- Active parallel edges are equal. -/
  edge_eq_of_parallel {e f : E} : Parallel G e f → e = f

lemma Parallel.edge_eq [NoParallelEdge G] (h : Parallel G e f) : e = f :=
  NoParallelEdge.edge_eq_of_parallel h

@[simp]
lemma parallel_iff_eq [NoParallelEdge G] : Parallel G e f ↔ e = f ∧ e ∈ E(G) :=
  ⟨fun h ↦ ⟨h.edge_eq, h.left_mem⟩, fun ⟨h, he⟩ ↦ h ▸ Parallel.refl he⟩

/-- Complete retained fibers preserve the absence of parallel edges, including empty fibers. -/
lemma Compatible.noParallelEdge_of_edgeFiber_eq [NoParallelEdge G] {H : Gr₂}
    (h : Compatible G H) (hE : E(H) ⊆ E(G))
    (hF : ∀ e ∈ E(H), edgeFiber H e = edgeFiber G e) : NoParallelEdge H where
  edge_eq_of_parallel hp :=
    (hp.of_compatible h.symm (hE hp.left_mem) (hE hp.right_mem)
      (hF _ hp.left_mem) (hF _ hp.right_mem)).edge_eq

end HyperGraphLike
