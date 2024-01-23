/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.Order.PFilter
import Mathlib.Combinatorics.AbstractSimplicialComplex.Basic

/-! Documentation here.-/

universe u v

variable {α : Type u} {β : Type v}

variable {K : AbstractSimplicialComplex α} {L : AbstractSimplicialComplex β}

open Finset AbstractSimplicialComplex

variable (K)

/-- Partial order instance on the type of faces of an abstract simplicial complex:
this is the order induced by the inclusion on finsets.-/
instance FacePoset : _root_.PartialOrder K.faces :=
  PartialOrder.lift (fun s => (s.1 : Finset α)) (fun _ _ hst => SetCoe.ext hst)

namespace SimplicialMap

variable [DecidableEq α] [DecidableEq β]
variable {K : AbstractSimplicialComplex α} {L : AbstractSimplicialComplex β}

/-- If `f : K →ₛ L` is a simplicial map, then its face map is an order homomorphism.-/
noncomputable def toOrderHom_faces (f : K →ₛ L) : OrderHom K.faces L.faces where
  toFun := f.face_map
  monotone' s t hst _ := by rw [f.face_vertex, f.face_vertex]
                            exact fun ⟨a, has, hab⟩ ↦ ⟨a, (hst has), hab⟩

end SimplicialMap

/-! Finset `α` is a `LocallyFiniteOrder` and a `LocallyFiniteOrderBot`.-/
--TODO : move this to another file.

namespace Finset

/-- If `s` is a finset of `α`, then the interval `Set.Iic s` in `Finset α` is finite.-/
lemma Iic_finite (s : Finset α) : (Set.Iic s).Finite := by
  rw [← Set.finite_coe_iff]
  apply Finite.of_injective (fun (t : Set.Iic s) => ({a : s | a.1 ∈ t.1} : Set s))
  intro t u htu
  simp only at htu
  revert htu
  rw [← SetCoe.ext_iff, le_antisymm_iff (a := t.1), imp_and]
  constructor
  rw [eq_comm]
  all_goals (intro heq a ha)
  set a' := (⟨a, Set.mem_Iic.mp t.2 ha⟩ : {a : α | a ∈ s})
  swap
  set a' := (⟨a, Set.mem_Iic.mp u.2 ha⟩ : {a : α | a ∈ s})
  all_goals
  rw [Set.ext_iff] at heq
  have : a = a'.1 := by simp only
  erw [this, heq a']
  exact ha

/-- of `s` and `t` are finsets of `α`, then the closed interval `Set.Icc s t` in `Finset α`
is finite.-/
lemma Icc_finite (s t : Finset α) : (Set.Icc s t).Finite :=
  Set.Finite.subset (Iic_finite t) (by rw [Set.subset_def]; simp only [ge_iff_le, gt_iff_lt,
  Set.mem_Icc, Set.mem_Iic, and_imp, imp_self, implies_true, Subtype.forall, forall_const])

/- `LocallyFiniteOrderBot` instance on `Finset α`.-/
noncomputable instance instLocallyFiniteOrderBot [DecidableEq α]:
    LocallyFiniteOrderBot (Finset α) :=
  LocallyFiniteOrderTop.ofIic (Finset α) (fun s => Set.Finite.toFinset (Iic_finite s))
  (fun a s => by simp only [Set.Finite.mem_toFinset, Set.mem_Iic])

/- `LocallyFiniteOrder` instance on `Finset α`.-/
noncomputable instance instLocallyFiniteOrder [DecidableEq α]: LocallyFiniteOrder (Finset α) :=
  LocallyFiniteOrder.ofIcc (Finset α) (fun s t => Set.Finite.toFinset (Icc_finite s t))
  (fun a s t => by simp only [ge_iff_le, gt_iff_lt, Set.Finite.mem_toFinset, Set.mem_Icc])

end Finset

/-! The face poset of an abstract simplicial complex is a `LocallyFiniteOrder` and a
`LocallyFiniteOrderBot`.-/

namespace AbstractSimplicalComplex

/-- If `s` is a finset of `α`, then the intersection of the interval `Set.Iic s` in `Finset α`
and of the set of faces of `K` is finite.-/
lemma FinsetIic_finite (s : Finset α) : {u : K.faces | u ≤ s}.Finite := by
  refine Set.Finite.of_finite_image (f := fun u ↦ u.1) (Set.Finite.subset (Finset.Iic_finite s)
    ?_) (fun _ _ _ _ ↦ by rw [← SetCoe.ext_iff]; simp only [imp_self])
  intro u
  simp only [le_eq_subset, Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_left,
    exists_prop, exists_eq_right_right, Set.mem_Iic, and_imp]
  exact fun h _ ↦ h

/-- If `s` and `t` are finsets of `α`, then the intersection of the interval `Set.Icc s t`
in `Finset α` and of the set of faces of `K` is finite.-/
lemma FinsetIcc_finite (s t : Finset α) : {u : K.faces | s ≤ u ∧ u ≤ t}.Finite :=
  Set.Finite.subset (FinsetIic_finite K t)
    (fun _ ↦ by simp only [le_eq_subset, Set.mem_setOf_eq, and_imp, imp_self, implies_true])

/-- Left-infinite right-closed intervals of the face poset of an abstract simplicial complex
are finite.-/
lemma Iic_finite (s : K.faces) : (Set.Iic s).Finite := by
  rw [← Set.Iic_def]
  exact FinsetIic_finite K s.1

/-- Closed intervals of the face poset of an abstract simplicial complex are finite.-/
lemma Icc_finite (s t : K.faces) : (Set.Icc s t).Finite := by
  rw [← Set.Icc_def]
  exact FinsetIcc_finite K s.1 t.1

/-- `LocallyFiniteOrderBot` instance on the face poset of an abstract simplicial complex.-/
noncomputable instance instLocallyFiniteOrderBot [DecidableEq α] :
    LocallyFiniteOrderBot (K.faces) :=
  LocallyFiniteOrderTop.ofIic K.faces (fun s => Set.Finite.toFinset (Iic_finite K s))
  (fun a s => by simp only [Set.Finite.mem_toFinset, Set.mem_Iic])

/-- `LocallyFiniteOrder` instance on the face poset of an abstract simplicial complex.-/
noncomputable instance instLocallyFiniteOrder : LocallyFiniteOrder (K.faces) :=
  LocallyFiniteOrder.ofFiniteIcc (Icc_finite K)

/-! Finiteness properties of the face poset.-/

variable {K}
-- Probably useless.
/-If `K` is a finite abstract simplicial complex, then the relation `gt` on its face poset is
well-founded.
lemma wf_of_finiteComplex (hfin : FiniteComplex K) :
    WellFounded (fun (s t : K.faces) ↦ t < s) :=
  (@Finite.to_wellFoundedGT K.faces hfin _).wf
-/

/-- If the relation `fun s t ↦ t < s` on the facet poset of `K` is well-founded, then
every face of `K` is contained in a facet.-/
lemma exists_facet_of_wf (hwf : WellFounded (fun (s t : K.faces) ↦ t < s)) (t : K.faces) :
    ∃ (s : K.facets), t.1 ≤ s.1 := by
  have hne : {u : K.faces | t ≤ u}.Nonempty := ⟨t, by simp only [Set.mem_setOf_eq, le_refl]⟩
  set s := WellFounded.min hwf {u : K.faces | t ≤ u} hne
  have hts : t ≤ s := Set.mem_setOf.mp (WellFounded.min_mem hwf {u : K.faces | t ≤ u} hne)
  refine ⟨⟨s, (mem_facets_iff K s.1).mpr ⟨s.2, ?_⟩⟩, hts⟩
  exact fun u huf hsu ↦ eq_of_le_of_not_lt hsu (WellFounded.not_lt_min hwf {u : K.faces | t ≤ u}
    hne (x := ⟨u, huf⟩) (le_trans hts hsu))

open Nat ENat in
/-- If the relation `fun s t ↦ t < s` on the facet poset of `K` is well-founded and the facets
of `K` have the same cardinality, then `K` is pure. -/
lemma pure_of_wf_and_dimension_facets (hwf : WellFounded (fun (s t : K.faces) ↦ t < s))
    (hdim : ∀ s ∈ K.facets, ∀ t ∈ K.facets, Finset.card s = Finset.card t) : Pure K := by
  intro s hsf
  unfold dimension
  simp only [ENat.coe_sub, Nat.cast_one]
  apply le_antisymm
  · simp only [tsub_le_iff_left]
    exact le_trans (le_iSup (fun (s : K.faces) ↦ (s.1.card : ENat)) ⟨s, facets_subset hsf⟩)
      le_add_tsub
  · simp only [tsub_le_iff_right, iSup_le_iff, Subtype.forall]
    intro t htf
    let ⟨u, htu⟩ := exists_facet_of_wf hwf ⟨t, htf⟩
    convert le_of_le_of_eq (WithTop.coe_le_coe.mpr (Finset.card_le_card htu))
      (by rw [hdim u.1 u.2 s hsf])
    rw [← coe_one, ← coe_sub, ← coe_add, ← succ_eq_add_one, ← pred_eq_sub_one,
      succ_pred (face_card_nonzero (facets_subset hsf))]; rfl

-- TODO : move the next two lemmas somewhere else.
/-- If an order ideal has a maximal element, then this element generates the ideal.-/
lemma Order.Ideal.generated_by_maximal_element {α : Type*} [Preorder α] (I : Order.Ideal α)
    {a : α} (ha : a ∈ I ∧ ∀ (b : α), b ∈ I → a ≤ b → b ≤ a) : I = Order.Ideal.principal a := by
  rw [← Order.Ideal.principal_le_iff] at ha
  refine le_antisymm ?_ ha.1
  intro b hbI
  erw [Order.Ideal.mem_principal]
  let ⟨c, hc⟩ := I.directed a (by rw [Order.Ideal.principal_le_iff] at ha; exact ha.1) b hbI
  exact le_trans hc.2.2 (ha.2 c hc.1 hc.2.1)

/-- If an order filter has a minimal element, then this element generates the filter.-/
lemma Order.PFilter.generated_by_minimal_element {α : Type*} [Preorder α] (F : Order.PFilter α)
    {a : α} (ha : a ∈ F ∧ ∀ (b : α), b ∈ F → b ≤ a → a ≤ b) : F = Order.PFilter.principal a := by
  suffices hdual : F.dual = @Order.Ideal.principal αᵒᵈ _ a by
    unfold Order.PFilter.principal
    erw [← hdual]
  apply Order.Ideal.generated_by_maximal_element F.dual
  change a ∈ F.dual ∧ _ at ha
  rw [and_iff_right ha.1]
  exact fun b hbF hab => ha.2 b hbF hab
-- end of stuff to move

/-! Order filters and order ideals of the face poset.-/

/-- Every filter of the face poset of an abstract simplicial complex is principal, generated
by a minimal element.-/
lemma isPrincipal_filter_facePoset [DecidableEq α] (F : Order.PFilter K.faces) :
    ∃ (s : K.faces), F = Order.PFilter.principal s := by
  let ⟨t, ht⟩ := F.nonempty
  have hfin : ({s : K.faces | s ≤ t ∧ s ∈ F}).Finite :=
    Set.finite_coe_iff.mp (Finite.Set.subset (Set.Iic t) (fun s hs ↦ hs.1))
  let ⟨s, hs⟩ := Finset.exists_minimal (Set.Finite.toFinset hfin)
    ⟨t, by simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, le_refl, true_and]; exact ht⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, and_imp, Subtype.forall] at hs
  existsi s
  apply Order.PFilter.generated_by_minimal_element
  rw [and_iff_right hs.1.2]
  intro b hbF hbs
  have hsb := hs.2 b.1 b.2 (le_trans hbs hs.1.1) hbF
  rw [lt_iff_le_not_le] at hsb
  push_neg at hsb
  exact hsb hbs

end AbstractSimplicalComplex
