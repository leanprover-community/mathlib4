/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.HypergraphLike.Basic
public import Mathlib.Data.Set.Card.Arithmetic

/-!
# Degree and order of graph-like structures

* `HyperGraphLike.edegree` and `HyperGraphLike.eorder` count incidences in `ℕ∞`.
* `HyperGraphLike.degree` and `HyperGraphLike.order` count incidences in `ℕ`, with value zero
  for an infinite incidence fiber.

-/

@[expose] public section

open Set Function

namespace HyperGraphLike

variable {V I E Gr : Type*} {G : Gr} [HyperGraphLike V I E Gr] {u u' v v' w : V} {i j : I} {e f : E}

section HyperGraphLike

instance [Finite I(G)] : Finite (edgeFiber G e) :=
  ((Set.toFinite I(G)).subset edgeFiber_subset_incs).to_subtype

instance [Finite I(G)] : Finite (vertexFiber G v) :=
  ((Set.toFinite I(G)).subset vertexFiber_subset_incs).to_subtype

/-! ### Extended degree and order -/

/-- The number of incidences of an edge, with value `⊤` for an infinite fiber. -/
noncomputable def eorder (G : Gr) (e : E) : ℕ∞ := {i : I(G) | (edgeMap' G i : E) = e}.encard

/-- The number of incidences attached to a vertex, with value `⊤` for an infinite fiber. -/
noncomputable def edegree (G : Gr) (v : V) : ℕ∞ := {i : I(G) | (attach' G i : V) = v}.encard

lemma eorder_eq_encard_edgeFiber (G : Gr) : eorder G e = (edgeFiber G e).encard :=
  (Subtype.val_injective.encard_image _).symm

lemma edegree_eq_encard_vertexFiber (G : Gr) : edegree G v = (vertexFiber G v).encard :=
  (Subtype.val_injective.encard_image _).symm

lemma edegree_eq_zero [Nonempty V] : edegree G v = 0 ↔ ∀ i ∈ I(G), attach G i ≠ v := by
  simp [edegree_eq_encard_vertexFiber, eq_empty_iff_forall_notMem]

lemma edegree_pos [Nonempty V] : 0 < edegree G v ↔ ∃ i ∈ I(G), attach G i = v := by
  simp [edegree_eq_encard_vertexFiber, nonempty_def]

lemma edegree_eq_zero_iff_incEdges_eq_empty : edegree G v = 0 ↔ incEdges G v = ∅ := by
  simp [edegree_eq_encard_vertexFiber, incEdges_eq_empty]

lemma edegree_pos_iff_nonempty_incEdges : 0 < edegree G v ↔ (incEdges G v).Nonempty := by
  simp [edegree_eq_encard_vertexFiber, incEdges_nonempty]

@[simp]
lemma edegree_of_notMem_verts (hv : v ∉ V(G)) : edegree G v = 0 :=
  edegree_eq_zero_iff_incEdges_eq_empty.mpr (incEdges_of_notMem_verts hv)

lemma edegree_attach_pos [Nonempty V] (hi : i ∈ I(G)) : 0 < edegree G (attach G i) :=
  edegree_pos.mpr ⟨i, hi, rfl⟩

@[grind! →]
lemma mem_verts_of_edegree_pos (h : 0 < edegree G v) : v ∈ V(G) :=
  (edegree_pos_iff_nonempty_incEdges.mp h).elim fun _ he ↦ mem_verts_of_mem_incEdges he

lemma edegree_le_encard_incs : edegree G v ≤ I(G).encard :=
  (edegree_eq_encard_vertexFiber G).trans_le (encard_mono vertexFiber_subset_incs)

@[simp]
lemma edegree_lt_top_iff : edegree G v < ⊤ ↔ (vertexFiber G v).Finite := by
  rw [edegree_eq_encard_vertexFiber, encard_lt_top_iff]

@[simp]
lemma edegree_eq_top_iff : edegree G v = ⊤ ↔ (vertexFiber G v).Infinite := by
  rw [edegree_eq_encard_vertexFiber, encard_eq_top_iff]

lemma edegree_lt_top_of_finite (hI : I(G).Finite) : edegree G v < ⊤ :=
  edegree_lt_top_iff.mpr (hI.subset vertexFiber_subset_incs)

lemma attach_surjOn_iff [Nonempty V] :
    SurjOn (attach G) I(G) V(G) ↔ ∀ v ∈ V(G), 0 < edegree G v := by
  simp only [SurjOn, subset_def, mem_image, edegree_pos]

@[simp]
lemma attach_image_incs_of_edegree_pos [Nonempty V] (h : ∀ v ∈ V(G), 0 < edegree G v) :
    attach G '' I(G) = V(G) :=
  (image_subset_iff.mpr fun _ hi ↦ attach_mem_verts hi).antisymm (attach_surjOn_iff.mpr h)

lemma attach_preimage_singleton_injOn [Nonempty V] (h : ∀ v ∈ V(G), edegree G v ≠ 0) :
    InjOn (fun v ↦ attach G ⁻¹' {v}) V(G) := by
  intro v hv w hw hvw
  obtain ⟨i, hi⟩ := encard_ne_zero.mp (edegree_eq_encard_vertexFiber G ▸ h v hv)
  have hi := (mem_vertexFiber.mp hi).2
  exact hi.symm.trans ((congrArg (fun s : Set I ↦ i ∈ s) hvw).mp hi)

lemma eorder_eq_zero : eorder G e = 0 ↔ incVerts G e = ∅ := by
  simp [eorder_eq_encard_edgeFiber, incVerts_eq_empty]

lemma eorder_pos : 0 < eorder G e ↔ (incVerts G e).Nonempty := by
  simp [eorder_eq_encard_edgeFiber, incVerts_nonempty]

@[simp]
lemma eorder_of_notMem_edges (he : e ∉ E(G)) : eorder G e = 0 :=
  eorder_eq_zero.mpr (incVerts_of_notMem_edges he)

lemma eorder_edgeMap_pos [Nonempty E] (hi : i ∈ I(G)) : 0 < eorder G (edgeMap G i) := by
  rw [eorder_eq_encard_edgeFiber, encard_pos]
  exact ⟨i, mem_edgeFiber.mpr ⟨hi, rfl⟩⟩

@[grind! →]
lemma mem_edges_of_eorder_pos (h : 0 < eorder G e) : e ∈ E(G) :=
  (eorder_pos.mp h).elim fun _ hv ↦ mem_edges_of_mem_incVerts hv

lemma eorder_le_encard_incs : eorder G e ≤ I(G).encard :=
  (eorder_eq_encard_edgeFiber G).trans_le (encard_mono edgeFiber_subset_incs)

@[simp]
lemma eorder_lt_top_iff : eorder G e < ⊤ ↔ (edgeFiber G e).Finite := by
  rw [eorder_eq_encard_edgeFiber, encard_lt_top_iff]

@[simp]
lemma eorder_eq_top_iff : eorder G e = ⊤ ↔ (edgeFiber G e).Infinite := by
  rw [eorder_eq_encard_edgeFiber, encard_eq_top_iff]

lemma eorder_lt_top_of_finite (hI : I(G).Finite) : eorder G e < ⊤ :=
  eorder_lt_top_iff.mpr (hI.subset edgeFiber_subset_incs)

/-- Every edge has positive order exactly when `edgeMap` maps the incidences onto the edges. -/
lemma edgeMap_surjOn_iff [Nonempty E] :
    SurjOn (edgeMap G) I(G) E(G) ↔ ∀ e ∈ E(G), 0 < eorder G e := by
  simp only [SurjOn, subset_def, mem_image, eorder_eq_encard_edgeFiber, encard_pos, nonempty_def,
    mem_edgeFiber]

lemma edgeMap_image_incs_of_eorder_pos [Nonempty E] (h : ∀ e ∈ E(G), 0 < eorder G e) :
    edgeMap G '' I(G) = E(G) :=
  (image_subset_iff.mpr fun _ hi ↦ edgeMap_mem_edges hi).antisymm (edgeMap_surjOn_iff.mpr h)

lemma edgeMap_range_of_eorder_pos [Nonempty E] (h : ∀ e ∈ E(G), 0 < eorder G e) :
    range (fun i : I(G) ↦ edgeMap G (i : I)) = E(G) := by
  rw [← edgeMap_image_incs_of_eorder_pos h]
  ext e
  simp only [mem_image, mem_range, Subtype.exists, exists_prop]

lemma edgeMap_preimage_singleton_injOn [Nonempty E] (h : ∀ e ∈ E(G), eorder G e ≠ 0) :
    InjOn (fun e ↦ edgeMap G ⁻¹' {e}) E(G) := by
  intro e he f hf hef
  obtain ⟨i, hi⟩ := encard_ne_zero.mp (eorder_eq_encard_edgeFiber G ▸ h e he)
  have hi := (mem_edgeFiber.mp hi).2
  exact hi.symm.trans ((congrArg (fun s : Set I ↦ i ∈ s) hef).mp hi)

@[grind! .]
lemma IsLink.one_lt_eorder (h : u ~[G; e] v) : 1 < eorder G e := by
  obtain ⟨i, j, hij, _, _, hi, _, hj, _⟩ := isLink_iff.mp h
  exact one_lt_encard_iff.mpr ⟨i, j, hi, hj, hij⟩

/-- A linked edge of order two has precisely the two linked vertices in its support. -/
lemma IsLink.incVerts_eq_of_eorder_eq_two (h : u ~[G; e] v) (ho : eorder G e = 2) :
    incVerts G e = {u, v} := by
  obtain ⟨a, b, hab, hf⟩ := encard_eq_two.mp ho
  have hm (k : I(G)) (hk : (edgeMap' G k : E) = e) : k = a ∨ k = b := by
    simpa using (show k ∈ ({a, b} : Set I(G)) from hf ▸ hk)
  refine subset_antisymm ?_ h.pair_subset_incVerts
  obtain ⟨i, j, hij, _, _, hi, hu, hj, hv⟩ := isLink_iff.mp h
  rintro w ⟨k, hk, rfl⟩
  (obtain rfl | rfl : k = i ∨ k = j := by grind) <;> simp [hu, hv]

lemma IsLink.eq_or_eq_of_isLink_of_eorder_eq_two (h : u ~[G; e] v) (h' : u' ~[G; e] v')
    (ho : eorder G e = 2) : u = u' ∧ v = v' ∨ u = v' ∧ v = u' :=
  pair_eq_pair_iff.mp ((h.incVerts_eq_of_eorder_eq_two ho).symm.trans
    (h'.incVerts_eq_of_eorder_eq_two ho))

@[grind →]
lemma IsLink.right_unique_of_eorder_eq_two (h : u ~[G; e] v) (h' : u ~[G; e] w)
    (ho : eorder G e = 2) : v = w := by
  grind [h.eq_or_eq_of_isLink_of_eorder_eq_two h' ho]

@[grind →]
lemma IsLink.left_unique_of_eorder_eq_two (h : u ~[G; e] w) (h' : v ~[G; e] w)
    (ho : eorder G e = 2) : u = v := by
  grind [h.eq_or_eq_of_isLink_of_eorder_eq_two h' ho]

lemma encard_incVerts_le_eorder : (incVerts G e).encard ≤ eorder G e := encard_image_le _ _

lemma encard_incEdges_le_edegree : (incEdges G v).encard ≤ edegree G v := encard_image_le _ _

lemma edegree_pos_iff_exists_mem_incVerts : 0 < edegree G v ↔ ∃ e, v ∈ incVerts G e := by
  simp only [edegree_pos_iff_nonempty_incEdges, nonempty_def, mem_incEdges]

lemma edegree_eq_zero_iff_forall_notMem_incVerts : edegree G v = 0 ↔ ∀ e, v ∉ incVerts G e := by
  simp only [edegree_eq_zero_iff_incEdges_eq_empty, eq_empty_iff_forall_notMem, mem_incEdges]

lemma edegree_eq_zero_of_incs_eq_empty (hI : I(G) = ∅) : edegree G v = 0 := by
  simpa [hI] using edegree_le_encard_incs (G := G) (v := v)

lemma eorder_eq_zero_of_incs_eq_empty (hI : I(G) = ∅) : eorder G e = 0 := by
  simpa [hI] using eorder_le_encard_incs (G := G) (e := e)

/-! ### Counting incidences in `ℕ∞` -/

/-- Summing degrees over a finite vertex set counts all incidences. This is true without finiteness
assumption but requires importing topology here. -/
lemma sum_edegree (G : Gr) [Fintype V(G)] : ∑ v : V(G), edegree G (v : V) = I(G).encard := by
  simpa only [iUnion_subtype, biUnion_vertexFiber, ← edegree_eq_encard_vertexFiber,
    finsum_eq_sum_of_fintype] using (encard_iUnion_of_finite (ι := V(G))
      ((pairwise_disjoint_vertexFiber G).comp_of_injective Subtype.val_injective)).symm

/-- Summing orders over a finite edge set counts all incidences. This is true without finiteness
assumption but requires importing topology here. -/
lemma sum_eorder (G : Gr) [Fintype E(G)] : ∑ e : E(G), eorder G (e : E) = I(G).encard := by
  simpa only [iUnion_subtype, biUnion_edgeFiber, ← eorder_eq_encard_edgeFiber,
    finsum_eq_sum_of_fintype] using (encard_iUnion_of_finite (ι := E(G))
      ((pairwise_disjoint_edgeFiber G).comp_of_injective Subtype.val_injective)).symm

/-- The degree sum equals the edge order sum when both indexing sets are finite. This is true
without finiteness assumption but requires importing topology here. -/
lemma sum_edegree_eq_sum_eorder (G : Gr) [Fintype V(G)] [Fintype E(G)] :
    ∑ v : V(G), edegree G (v : V) = ∑ e : E(G), eorder G (e : E) :=
  (sum_edegree G).trans (sum_eorder G).symm

/-! ### Natural-number degree and order -/

/-- The number of incidences of an edge, with value zero for an infinite fiber. -/
noncomputable def order (G : Gr) (e : E) : ℕ := (eorder G e).toNat

/-- The number of incidences attached to a vertex, with value zero for an infinite fiber. -/
noncomputable def degree (G : Gr) (v : V) : ℕ := (edegree G v).toNat

@[simp]
lemma toNat_eorder : (eorder G e).toNat = order G e := rfl

@[simp]
lemma toNat_edegree : (edegree G v).toNat = degree G v := rfl

lemma order_eq_ncard_edgeFiber (G : Gr) : order G e = (edgeFiber G e).ncard := by
  rw [order, eorder_eq_encard_edgeFiber, ncard_def]

lemma degree_eq_ncard_vertexFiber (G : Gr) : degree G v = (vertexFiber G v).ncard := by
  rw [degree, edegree_eq_encard_vertexFiber, ncard_def]

@[simp]
lemma natCast_order (he : (edgeFiber G e).Finite := by toFinite_tac) :
    (order G e : ℕ∞) = eorder G e := by
  rw [order_eq_ncard_edgeFiber, eorder_eq_encard_edgeFiber, he.cast_ncard_eq]

@[simp]
lemma natCast_degree (hv : (vertexFiber G v).Finite := by toFinite_tac) :
    (degree G v : ℕ∞) = edegree G v := by
  rw [degree_eq_ncard_vertexFiber, edegree_eq_encard_vertexFiber, hv.cast_ncard_eq]

@[simp]
lemma natCast_order_of_finite [Finite (edgeFiber G e)] : (order G e : ℕ∞) = eorder G e :=
  natCast_order

@[simp]
lemma natCast_degree_of_finite [Finite (vertexFiber G v)] : (degree G v : ℕ∞) = edegree G v :=
  natCast_degree

@[simp]
lemma order_eq_zero_of_infinite (he : (edgeFiber G e).Infinite) : order G e = 0 := by
  rw [order_eq_ncard_edgeFiber, he.ncard]

@[simp]
lemma degree_eq_zero_of_infinite (hv : (vertexFiber G v).Infinite) : degree G v = 0 := by
  rw [degree_eq_ncard_vertexFiber, hv.ncard]

@[grind! →]
lemma finite_vertexFiber_of_degree_pos (h : 0 < degree G v) : (vertexFiber G v).Finite :=
  finite_of_ncard_pos ((degree_eq_ncard_vertexFiber G) ▸ h)

@[grind! →]
lemma finite_edgeFiber_of_order_pos (h : 0 < order G e) : (edgeFiber G e).Finite :=
  finite_of_ncard_pos ((order_eq_ncard_edgeFiber G) ▸ h)

lemma degree_eq_zero [Nonempty V] (hv : (vertexFiber G v).Finite := by toFinite_tac) :
    degree G v = 0 ↔ ∀ i ∈ I(G), attach G i ≠ v := by
  rw [← Nat.cast_eq_zero (R := ℕ∞), natCast_degree hv, edegree_eq_zero]

lemma degree_pos [Nonempty V] (hv : (vertexFiber G v).Finite := by toFinite_tac) :
    0 < degree G v ↔ ∃ i ∈ I(G), attach G i = v := by
  rw [degree_eq_ncard_vertexFiber, ncard_pos hv]
  simp [nonempty_def]

@[simp]
lemma degree_eq_zero_iff_incEdges_eq_empty (hv : (vertexFiber G v).Finite := by toFinite_tac) :
    degree G v = 0 ↔ incEdges G v = ∅ := by
  rw [degree_eq_ncard_vertexFiber, ncard_eq_zero hv, incEdges_eq_empty]

@[simp]
lemma degree_pos_iff_nonempty_incEdges (hv : (vertexFiber G v).Finite := by toFinite_tac) :
    0 < degree G v ↔ (incEdges G v).Nonempty := by
  rw [degree_eq_ncard_vertexFiber, ncard_pos hv, incEdges_nonempty]

@[simp]
lemma degree_of_notMem_verts (hv : v ∉ V(G)) : degree G v = 0 := by
  simp [degree, edegree_of_notMem_verts hv]

lemma degree_attach_pos [Nonempty V] (hi : i ∈ I(G))
    (hv : (vertexFiber G (attach G i)).Finite := by toFinite_tac) : 0 < degree G (attach G i) :=
  (degree_pos hv).mpr ⟨i, hi, rfl⟩

@[grind! →]
lemma mem_verts_of_degree_pos (h : 0 < degree G v) : v ∈ V(G) :=
  ((degree_pos_iff_nonempty_incEdges (finite_vertexFiber_of_degree_pos h)).mp h).elim
    fun _ he ↦ mem_verts_of_mem_incEdges he

lemma degree_le_ncard_incs (hI : I(G).Finite := by toFinite_tac) : degree G v ≤ I(G).ncard := by
  rw [degree_eq_ncard_vertexFiber]
  exact ncard_le_ncard vertexFiber_subset_incs hI

lemma order_eq_zero (he : (edgeFiber G e).Finite := by toFinite_tac) :
    order G e = 0 ↔ incVerts G e = ∅ := by
  rw [order_eq_ncard_edgeFiber, ncard_eq_zero he, incVerts_eq_empty]

lemma order_pos (he : (edgeFiber G e).Finite := by toFinite_tac) :
    0 < order G e ↔ (incVerts G e).Nonempty := by
  rw [order_eq_ncard_edgeFiber, ncard_pos he, incVerts_nonempty]

@[simp]
lemma order_of_notMem_edges (he : e ∉ E(G)) : order G e = 0 := by
  simp [order, eorder_of_notMem_edges he]

lemma order_edgeMap_pos [Nonempty E] (hi : i ∈ I(G))
    (he : (edgeFiber G (edgeMap G i)).Finite := by toFinite_tac) : 0 < order G (edgeMap G i) := by
  rw [order_eq_ncard_edgeFiber, ncard_pos he]
  exact ⟨i, mem_edgeFiber.mpr ⟨hi, rfl⟩⟩

@[grind! →]
lemma mem_edges_of_order_pos (h : 0 < order G e) : e ∈ E(G) :=
  ((order_pos (finite_edgeFiber_of_order_pos h)).mp h).elim
    fun _ hv ↦ mem_edges_of_mem_incVerts hv

lemma order_le_ncard_incs (hI : I(G).Finite := by toFinite_tac) : order G e ≤ I(G).ncard := by
  rw [order_eq_ncard_edgeFiber]
  exact ncard_le_ncard edgeFiber_subset_incs hI

lemma degree_pos_iff_exists_mem_incVerts (hv : (vertexFiber G v).Finite := by toFinite_tac) :
    0 < degree G v ↔ ∃ e, v ∈ incVerts G e := by
  simp only [degree_pos_iff_nonempty_incEdges hv, nonempty_def, mem_incEdges]

lemma degree_eq_zero_iff_forall_notMem_incVerts (hv : (vertexFiber G v).Finite := by toFinite_tac) :
    degree G v = 0 ↔ ∀ e, v ∉ incVerts G e := by
  simp only [degree_eq_zero_iff_incEdges_eq_empty hv, eq_empty_iff_forall_notMem, mem_incEdges]

lemma degree_eq_zero_of_incs_eq_empty (hI : I(G) = ∅) : degree G v = 0 := by
  simp [degree, edegree_eq_zero_of_incs_eq_empty hI]

lemma order_eq_zero_of_incs_eq_empty (hI : I(G) = ∅) : order G e = 0 := by
  simp [order, eorder_eq_zero_of_incs_eq_empty hI]

lemma IsLink.one_lt_order (h : u ~[G; e] v) (he : (edgeFiber G e).Finite := by toFinite_tac) :
    1 < order G e := by
  rw [← Nat.cast_lt (α := ℕ∞), Nat.cast_one, natCast_order he]
  exact h.one_lt_eorder

/-- A linked edge of order two has precisely the two linked vertices in its support. -/
lemma IsLink.incVerts_eq_of_order_eq_two (h : u ~[G; e] v) (ho : order G e = 2) :
    incVerts G e = {u, v} :=
  h.incVerts_eq_of_eorder_eq_two ((ENat.toNat_eq_iff (by decide)).mp ho)

lemma IsLink.eq_or_eq_of_isLink_of_order_eq_two (h : u ~[G; e] v) (h' : u' ~[G; e] v')
    (ho : order G e = 2) : u = u' ∧ v = v' ∨ u = v' ∧ v = u' :=
  h.eq_or_eq_of_isLink_of_eorder_eq_two h' ((ENat.toNat_eq_iff (by decide)).mp ho)

@[grind →]
lemma IsLink.right_unique_of_order_eq_two (h : u ~[G; e] v) (h' : u ~[G; e] w)
    (ho : order G e = 2) : v = w :=
  h.right_unique_of_eorder_eq_two h' ((ENat.toNat_eq_iff (by decide)).mp ho)

@[grind →]
lemma IsLink.left_unique_of_order_eq_two (h : u ~[G; e] w) (h' : v ~[G; e] w) (ho : order G e = 2) :
    u = v :=
  h.left_unique_of_eorder_eq_two h' ((ENat.toNat_eq_iff (by decide)).mp ho)

lemma ncard_incVerts_le_order (he : (edgeFiber G e).Finite := by toFinite_tac) :
    (incVerts G e).ncard ≤ order G e := by
  rw [← Nat.cast_le (α := ℕ∞), natCast_order he]
  exact (ncard_le_encard _).trans encard_incVerts_le_eorder

lemma ncard_incEdges_le_degree (hv : (vertexFiber G v).Finite := by toFinite_tac) :
    (incEdges G v).ncard ≤ degree G v := by
  rw [← Nat.cast_le (α := ℕ∞), natCast_degree hv]
  exact (ncard_le_encard _).trans encard_incEdges_le_edegree

/-! ### Counting incidences in `ℕ` -/

/-- Summing degrees over a finite vertex set counts all incidences, provided there are finitely
many incidences. -/
lemma sum_degree (G : Gr) [Fintype V(G)] (hI : I(G).Finite := by toFinite_tac) :
    ∑ v : V(G), degree G (v : V) = I(G).ncard := by
  simpa only [iUnion_subtype, biUnion_vertexFiber, ← degree_eq_ncard_vertexFiber,
    finsum_eq_sum_of_fintype] using (ncard_iUnion_of_finite (ι := V(G))
      (fun _ ↦ hI.subset vertexFiber_subset_incs)
      ((pairwise_disjoint_vertexFiber G).comp_of_injective Subtype.val_injective)).symm

/-- Summing orders over a finite edge set counts all incidences when the incidence set is finite. -/
lemma sum_order (G : Gr) [Fintype E(G)] (hI : I(G).Finite := by toFinite_tac) :
    ∑ e : E(G), order G (e : E) = I(G).ncard := by
  simpa only [iUnion_subtype, biUnion_edgeFiber, ← order_eq_ncard_edgeFiber,
    finsum_eq_sum_of_fintype] using (ncard_iUnion_of_finite (ι := E(G))
      (fun _ ↦ hI.subset edgeFiber_subset_incs)
      ((pairwise_disjoint_edgeFiber G).comp_of_injective Subtype.val_injective)).symm

/-- The degree sum equals the edge order sum when the vertex, edge, and incidence sets
are finite. -/
lemma sum_degree_eq_sum_order (G : Gr) [Fintype V(G)] [Fintype E(G)]
    (hI : I(G).Finite := by toFinite_tac) :
    ∑ v : V(G), degree G (v : V) = ∑ e : E(G), order G (e : E) :=
  (sum_degree G hI).trans (sum_order G hI).symm

end HyperGraphLike

end HyperGraphLike
