/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Filter.CountableInter
import Mathlib.Order.Filter.CardinalInter
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Order.Filter.Bases

/-!
# The cocardinal filter

In this file we define `Filter.cocardinal hc`: the filter of sets with cardinality less than
  a regular cardinal `c` that satisfies `Cardinal.aleph0 < c`.
  Such filters are `CardinalInterFilter` with cardinality `c`.

-/

open Set Filter Cardinal

universe u
variable {ι : Type u} {α β : Type u}
variable {c : Cardinal.{u}} {hreg : c.IsRegular}
variable {l : Filter α}

namespace Filter

variable (α) in
/-- The filter defined by all sets that have a complement with at most cardinality `c`. For a union
of `c` sets of `c` elements to have `c` elements, we need that `c` is a regular cardinal. -/
def cocardinal (hreg : c.IsRegular) : Filter α := by
  apply ofCardinalUnion {s | Cardinal.mk s < c} (lt_of_lt_of_le (nat_lt_aleph0 2) hreg.aleph0_le)
  · refine fun s hS hSc ↦ lt_of_le_of_lt (mk_sUnion_le _) <| mul_lt_of_lt hreg.aleph0_le hS ?_
    exact iSup_lt_of_isRegular hreg hS fun i ↦ hSc i i.property
  · exact fun _ hSc _ ht ↦ lt_of_le_of_lt (mk_le_mk_of_subset ht) hSc

@[simp]
theorem mem_cocardinal {s : Set α} :
    s ∈ cocardinal α hreg ↔ Cardinal.mk (sᶜ : Set α) < c := Iff.rfl

@[simp] lemma cocardinal_aleph0_eq_cofinite :
    cocardinal (α := α) isRegular_aleph0 = cofinite := by
  aesop

instance instCardinalInterFilter_cocardinal : CardinalInterFilter (cocardinal (α := α) hreg) c where
  cardinal_sInter_mem S hS hSs := by
    rw [mem_cocardinal, Set.compl_sInter]
    apply lt_of_le_of_lt (mk_sUnion_le _)
    apply mul_lt_of_lt hreg.aleph0_le (lt_of_le_of_lt mk_image_le hS)
    apply iSup_lt_of_isRegular hreg <| lt_of_le_of_lt mk_image_le hS
    intro i
    aesop

@[simp]
theorem eventually_cocardinal {p : α → Prop} :
    (∀ᶠ x in cocardinal α hreg, p x) ↔ #{ x | ¬p x } < c := Iff.rfl

theorem hasBasis_cocardinal : HasBasis (cocardinal α hreg) {s : Set α | #s < c} compl :=
  ⟨fun s =>
    ⟨fun h => ⟨sᶜ, h, (compl_compl s).subset⟩, fun ⟨_t, htf, hts⟩ => by
      have : #↑sᶜ < c := by
        apply lt_of_le_of_lt _ htf
        rw [compl_subset_comm] at hts
        apply Cardinal.mk_le_mk_of_subset hts
      simp_all only [mem_cocardinal] ⟩⟩

theorem frequently_cocardinal {p : α → Prop} :
    (∃ᶠ x in cocardinal α hreg, p x) ↔ c ≤ # { x | p x } := by
  simp only [Filter.Frequently, eventually_cocardinal, not_not,coe_setOf, not_lt]

lemma frequently_cocardinal_mem {s : Set α} :
    (∃ᶠ x in cocardinal α hreg, x ∈ s) ↔ c ≤ #s := frequently_cocardinal

@[simp]
lemma cocardinal_inf_principal_neBot_iff {s : Set α} :
    (cocardinal α hreg ⊓ 𝓟 s).NeBot ↔ c ≤ #s :=
  frequently_mem_iff_neBot.symm.trans frequently_cocardinal

theorem compl_mem_cocardinal_of_card_lt {s : Set α} (hs : #s < c) :
    sᶜ ∈ cocardinal α hreg :=
  mem_cocardinal.2 <| (compl_compl s).symm ▸ hs

theorem _root_.Set.Finite.compl_mem_cocardinal {s : Set α} (hs : s.Finite) :
    sᶜ ∈ cocardinal α hreg :=
  compl_mem_cocardinal_of_card_lt <| lt_of_lt_of_le (Finite.lt_aleph0 hs) (hreg.aleph0_le)

theorem eventually_cocardinal_nmem_of_card_lt  {s : Set α} (hs : #s < c) :
    ∀ᶠ x in cocardinal α hreg, x ∉ s :=
  compl_mem_cocardinal_of_card_lt hs

theorem _root_.Finset.eventually_cocardinal_nmem (s : Finset α) :
    ∀ᶠ x in cocardinal α hreg, x ∉ s :=
  eventually_cocardinal_nmem_of_card_lt <| lt_of_lt_of_le (finset_card_lt_aleph0 s) (hreg.aleph0_le)

theorem eventually_cocardinal_ne (x : α) : ∀ᶠ a in cocardinal α hreg, a ≠ x := by
  simp [Set.finite_singleton x]
  exact hreg.nat_lt 1

/-- The coproduct of the cocardinal filters on two types is the cocardinal filter on their product.
-/
theorem coprod_cocardinal :
    (cocardinal α hreg : Filter α).coprod (cocardinal β hreg : Filter β) = cocardinal (α × β) hreg
    :=
  Filter.coext fun s => by
    simp only [compl_mem_coprod, mem_cofinite, compl_compl, finite_image_fst_and_snd_iff]
    constructor
    · intro ⟨h1, h2⟩
      rw [mem_cocardinal, compl_compl] at *
      have := Cardinal.mul_lt_of_lt hreg.aleph0_le h1 h2
      rw [Cardinal.mul_def] at this
      apply lt_of_le_of_lt ?_ this
      refine mk_le_of_injective (f := fun a => ⟨⟨a.1.fst, ?_⟩, ⟨a.1.snd, ?_⟩⟩) ?_
      · simp only [mem_image, Prod.exists, exists_and_right, exists_eq_right]
        use a.1.snd
        simp only [Prod.mk.eta, Subtype.coe_prop]
      · simp only [mem_image, Prod.exists, exists_eq_right]
        use a.1.fst
        simp only [Prod.mk.eta, Subtype.coe_prop]
      intro x y h
      dsimp only at h
      simp [← Prod.ext_iff] at h
      exact SetCoe.ext h
    · intro h
      constructor
      · rw [mem_cocardinal, compl_compl] at *
        exact lt_of_le_of_lt Cardinal.mk_image_le h
      · rw [mem_cocardinal, compl_compl] at *
        exact lt_of_le_of_lt Cardinal.mk_image_le h

theorem coprodᵢ_cocardinal {α : ι → Type u} [Finite ι] :
    (Filter.coprodᵢ fun i => (cocardinal (α i) hreg : Filter (α i)))
    = cocardinal ((i : ι) → α i) hreg :=
  Filter.coext fun s => by
    simp only [compl_mem_coprodᵢ, mem_cocardinal, compl_compl]
    constructor
    · intro h
      simp at h -- my ideas run out here, the next line is just a thought
      have : #s ≤ #((i : ι) → α i) := by
        refine le_mk_iff_exists_set.mpr ?_
        use s
      apply lt_of_le_of_lt this
      sorry
    · exact fun h i => lt_of_le_of_lt Cardinal.mk_image_le h

theorem disjoint_cocardinal_left : Disjoint (cocardinal α hreg) l ↔ ∃ s ∈ l, #s < c := by
  simp [l.basis_sets.disjoint_iff_right]

theorem disjoint_cocardinal_right : Disjoint l (cocardinal α hreg) ↔ ∃ s ∈ l, #s < c :=
  disjoint_comm.trans disjoint_cocardinal_left

lemma cocardinal_inf_principal_compl_of_card_lt {s : Set α} (hs : #s < c) :
    (cocardinal α hreg) ⊓ 𝓟 sᶜ = cocardinal α hreg := by
  simp only [ge_iff_le, le_principal_iff, compl_mem_cocardinal_of_card_lt hs, inf_of_le_left]

lemma cocardinal_inf_principal_diff_of_card_lt {s t : Set α} (ht : #t < c) :
    (cocardinal α hreg) ⊓ 𝓟 (s \ t) = (cocardinal α hreg) ⊓ 𝓟 s := by
  rw [diff_eq, ← inf_principal, ← inf_assoc, inf_right_comm,
    cocardinal_inf_principal_compl_of_card_lt ht]

theorem Function.Surjective.le_map_cocardinal {f : α → β} (hf : Function.Surjective f) :
    cocardinal β hreg ≤ map f (cocardinal α hreg) := by
  intro U h
  rw [mem_map, mem_cocardinal] at *
  exact lt_of_le_of_lt (mk_preimage_of_subset_range (fun x ↦ f x) Uᶜ fun ⦃a⦄ _ ↦ hf a) h

/-- For an injective function `f`, inverse images of sets with cardinality `< c` have cardinality
`< c`. See also `Function.Injective.comap_cocardinal_eq`. -/
theorem Function.Injective.tendsto_cocardinal {f : α → β} (hf : Function.Injective f) :
    Tendsto f (cocardinal α hreg) (cocardinal β hreg) := by
  intro U h
  rw [mem_map, mem_cocardinal] at *
  exact lt_of_le_of_lt (mk_preimage_of_injective (fun x ↦ f x) Uᶜ hf) h

/-- The filter defined by all sets that have countable complements. -/
abbrev cocountable : Filter α := cocardinal α Cardinal.isRegular_aleph_one

theorem mem_cocountable {s : Set α} :
    s ∈ cocountable ↔ (sᶜ : Set α).Countable := by
  rw [Cardinal.countable_iff_lt_aleph_one, mem_cocardinal]

end Filter
