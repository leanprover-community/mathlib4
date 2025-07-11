/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Order.Interval.Finset.Basic
import Mathlib.Combinatorics.Additive.FreimanHom
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Group.Pointwise.Set.Scalar

/-!
# Sets without arithmetic progressions of length three and Roth numbers

This file defines sets without arithmetic progressions of length three, aka 3AP-free sets, and the
Roth number of a set.

The corresponding notion, sets without geometric progressions of length three, are called 3GP-free
sets.

The Roth number of a finset is the size of its biggest 3AP-free subset. This is a more general
definition than the one often found in mathematical literature, where the `n`-th Roth number is
the size of the biggest 3AP-free subset of `{0, ..., n - 1}`.

## Main declarations

* `ThreeGPFree`: Predicate for a set to be 3GP-free.
* `ThreeAPFree`: Predicate for a set to be 3AP-free.
* `mulRothNumber`: The multiplicative Roth number of a finset.
* `addRothNumber`: The additive Roth number of a finset.
* `rothNumberNat`: The Roth number of a natural, namely `addRothNumber (Finset.range n)`.

## TODO

* Can `threeAPFree_iff_eq_right` be made more general?
* Generalize `ThreeGPFree.image` to Freiman homs

## References

* [Wikipedia, *Salem-Spencer set*](https://en.wikipedia.org/wiki/Salem–Spencer_set)

## Tags

3AP-free, Salem-Spencer, Roth, arithmetic progression, average, three-free
-/

assert_not_exists Field Ideal TwoSidedIdeal

open Finset Function
open scoped Pointwise

variable {F α β : Type*}

section ThreeAPFree

open Set

section Monoid

variable [Monoid α] [Monoid β] (s t : Set α)

/-- A set is **3GP-free** if it does not contain any non-trivial geometric progression of length
three. -/
@[to_additive "A set is **3AP-free** if it does not contain any non-trivial arithmetic progression
of length three.

This is also sometimes called a **non averaging set** or **Salem-Spencer set**."]
def ThreeGPFree : Prop := ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s → a * c = b * b → a = b

/-- Whether a given finset is 3GP-free is decidable. -/
@[to_additive "Whether a given finset is 3AP-free is decidable."]
instance ThreeGPFree.instDecidable [DecidableEq α] {s : Finset α} :
    Decidable (ThreeGPFree (s : Set α)) :=
  decidable_of_iff (∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a * c = b * b → a = b) Iff.rfl

variable {s t}

@[to_additive]
theorem ThreeGPFree.mono (h : t ⊆ s) (hs : ThreeGPFree s) : ThreeGPFree t :=
  fun _ ha _ hb _ hc ↦ hs (h ha) (h hb) (h hc)

@[to_additive (attr := simp)]
theorem threeGPFree_empty : ThreeGPFree (∅ : Set α) := fun _ _ _ ha => ha.elim

@[to_additive]
theorem Set.Subsingleton.threeGPFree (hs : s.Subsingleton) : ThreeGPFree s :=
  fun _ ha _ hb _ _ _ ↦ hs ha hb

@[to_additive (attr := simp)]
theorem threeGPFree_singleton (a : α) : ThreeGPFree ({a} : Set α) :=
  subsingleton_singleton.threeGPFree

@[to_additive ThreeAPFree.prod]
theorem ThreeGPFree.prod {t : Set β} (hs : ThreeGPFree s) (ht : ThreeGPFree t) :
    ThreeGPFree (s ×ˢ t) := fun _ ha _ hb _ hc h ↦
  Prod.ext (hs ha.1 hb.1 hc.1 (Prod.ext_iff.1 h).1) (ht ha.2 hb.2 hc.2 (Prod.ext_iff.1 h).2)

@[to_additive]
theorem threeGPFree_pi {ι : Type*} {α : ι → Type*} [∀ i, Monoid (α i)] {s : ∀ i, Set (α i)}
    (hs : ∀ i, ThreeGPFree (s i)) : ThreeGPFree ((univ : Set ι).pi s) :=
  fun _ ha _ hb _ hc h ↦
  funext fun i => hs i (ha i trivial) (hb i trivial) (hc i trivial) <| congr_fun h i

end Monoid

section CommMonoid
variable [CommMonoid α] [CommMonoid β] {s A : Set α} {t : Set β} {f : α → β}

/-- Geometric progressions of length three are reflected under `2`-Freiman homomorphisms. -/
@[to_additive
"Arithmetic progressions of length three are reflected under `2`-Freiman homomorphisms."]
lemma ThreeGPFree.of_image (hf : IsMulFreimanHom 2 s t f) (hf' : s.InjOn f) (hAs : A ⊆ s)
    (hA : ThreeGPFree (f '' A)) : ThreeGPFree A :=
  fun _ ha _ hb _ hc habc ↦ hf' (hAs ha) (hAs hb) <| hA (mem_image_of_mem _ ha)
    (mem_image_of_mem _ hb) (mem_image_of_mem _ hc) <|
    hf.mul_eq_mul (hAs ha) (hAs hc) (hAs hb) (hAs hb) habc

/-- Geometric progressions of length three are unchanged under `2`-Freiman isomorphisms. -/
@[to_additive
"Arithmetic progressions of length three are unchanged under `2`-Freiman isomorphisms."]
lemma threeGPFree_image (hf : IsMulFreimanIso 2 s t f) (hAs : A ⊆ s) :
    ThreeGPFree (f '' A) ↔ ThreeGPFree A := by
  rw [ThreeGPFree, ThreeGPFree]
  have := (hf.bijOn.injOn.mono hAs).bijOn_image (f := f)
  simp +contextual only
    [((hf.bijOn.injOn.mono hAs).bijOn_image (f := f)).forall,
    hf.mul_eq_mul (hAs _) (hAs _) (hAs _) (hAs _), this.injOn.eq_iff]

@[to_additive] alias ⟨_, ThreeGPFree.image⟩ := threeGPFree_image

/-- Geometric progressions of length three are reflected under `2`-Freiman homomorphisms. -/
@[to_additive
"Arithmetic progressions of length three are reflected under `2`-Freiman homomorphisms."]
lemma IsMulFreimanHom.threeGPFree (hf : IsMulFreimanHom 2 s t f) (hf' : s.InjOn f)
    (ht : ThreeGPFree t) : ThreeGPFree s :=
  (ht.mono hf.mapsTo.image_subset).of_image hf hf' subset_rfl

/-- Geometric progressions of length three are unchanged under `2`-Freiman isomorphisms. -/
@[to_additive
"Arithmetic progressions of length three are unchanged under `2`-Freiman isomorphisms."]
lemma IsMulFreimanIso.threeGPFree_congr (hf : IsMulFreimanIso 2 s t f) :
    ThreeGPFree s ↔ ThreeGPFree t := by
  rw [← threeGPFree_image hf subset_rfl, hf.bijOn.image_eq]

/-- Geometric progressions of length three are preserved under semigroup homomorphisms. -/
@[to_additive
"Arithmetic progressions of length three are preserved under semigroup homomorphisms."]
theorem ThreeGPFree.image' [FunLike F α β] [MulHomClass F α β] (f : F) (hf : (s * s).InjOn f)
    (h : ThreeGPFree s) : ThreeGPFree (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ habc
  rw [h ha hb hc (hf (mul_mem_mul ha hc) (mul_mem_mul hb hb) <| by rwa [map_mul, map_mul])]

end CommMonoid

section CancelCommMonoid

variable [CommMonoid α] [IsCancelMul α] {s : Set α} {a : α}

@[to_additive] lemma ThreeGPFree.eq_right (hs : ThreeGPFree s) :
    ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s → a * c = b * b → b = c := by
  rintro a ha b hb c hc habc
  obtain rfl := hs ha hb hc habc
  simpa using habc.symm

@[to_additive] lemma threeGPFree_insert :
    ThreeGPFree (insert a s) ↔ ThreeGPFree s ∧
      (∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s → a * c = b * b → a = b) ∧
        ∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s → b * c = a * a → b = a := by
  refine ⟨fun hs ↦ ⟨hs.mono (subset_insert _ _),
    fun b hb c hc ↦ hs (Or.inl rfl) (Or.inr hb) (Or.inr hc),
    fun b hb c hc ↦ hs (Or.inr hb) (Or.inl rfl) (Or.inr hc)⟩, ?_⟩
  rintro ⟨hs, ha, ha'⟩ b hb c hc d hd h
  rw [mem_insert_iff] at hb hc hd
  obtain rfl | hb := hb <;> obtain rfl | hc := hc
  · rfl
  all_goals obtain rfl | hd := hd
  · exact (ha' hc hc h.symm).symm
  · exact ha hc hd h
  · exact mul_right_cancel h
  · exact ha' hb hd h
  · obtain rfl := ha hc hb ((mul_comm _ _).trans h)
    exact ha' hb hc h
  · exact hs hb hc hd h

@[to_additive]
theorem ThreeGPFree.smul_set (hs : ThreeGPFree s) : ThreeGPFree (a • s) := by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ h
  exact congr_arg (a • ·) <| hs hb hc hd <| by simpa [mul_mul_mul_comm _ _ a] using h

@[to_additive] lemma threeGPFree_smul_set : ThreeGPFree (a • s) ↔ ThreeGPFree s where
  mp hs b hb c hc d hd h := mul_left_cancel
      (hs (mem_image_of_mem _ hb) (mem_image_of_mem _ hc) (mem_image_of_mem _ hd) <| by
        rw [mul_mul_mul_comm, smul_eq_mul, smul_eq_mul, mul_mul_mul_comm, h])
  mpr := ThreeGPFree.smul_set

end CancelCommMonoid

section OrderedCancelCommMonoid

variable [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α] {s : Set α} {a : α}

@[to_additive]
theorem threeGPFree_insert_of_lt (hs : ∀ i ∈ s, i < a) :
    ThreeGPFree (insert a s) ↔
      ThreeGPFree s ∧ ∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s → a * c = b * b → a = b := by
  refine threeGPFree_insert.trans ?_
  rw [← and_assoc]
  exact and_iff_left fun b hb c hc h => ((mul_lt_mul_of_lt_of_lt (hs _ hb) (hs _ hc)).ne h).elim

end OrderedCancelCommMonoid

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero α] [NoZeroDivisors α] {s : Set α} {a : α}

lemma ThreeGPFree.smul_set₀ (hs : ThreeGPFree s) (ha : a ≠ 0) : ThreeGPFree (a • s) := by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ h
  exact congr_arg (a • ·) <| hs hb hc hd <| by simpa [mul_mul_mul_comm _ _ a, ha] using h

theorem threeGPFree_smul_set₀ (ha : a ≠ 0) : ThreeGPFree (a • s) ↔ ThreeGPFree s :=
  ⟨fun hs b hb c hc d hd h ↦
    mul_left_cancel₀ ha
      (hs (Set.mem_image_of_mem _ hb) (Set.mem_image_of_mem _ hc) (Set.mem_image_of_mem _ hd) <| by
        rw [smul_eq_mul, smul_eq_mul, mul_mul_mul_comm, h, mul_mul_mul_comm]),
    fun hs => hs.smul_set₀ ha⟩

end CancelCommMonoidWithZero

section Nat

theorem threeAPFree_iff_eq_right {s : Set ℕ} :
    ThreeAPFree s ↔ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s → a + c = b + b → a = c := by
  refine forall₄_congr fun a _ha b hb => forall₃_congr fun c hc habc => ⟨?_, ?_⟩
  · rintro rfl
    exact (add_left_cancel habc).symm
  · rintro rfl
    simp_rw [← two_mul] at habc
    exact mul_left_cancel₀ two_ne_zero habc

end Nat
end ThreeAPFree

open Finset

section RothNumber

variable [DecidableEq α]

section Monoid

variable [Monoid α] [DecidableEq β] [Monoid β] (s t : Finset α)

/-- The multiplicative Roth number of a finset is the cardinality of its biggest 3GP-free subset. -/
@[to_additive "The additive Roth number of a finset is the cardinality of its biggest 3AP-free
subset.

The usual Roth number corresponds to `addRothNumber (Finset.range n)`, see `rothNumberNat`."]
def mulRothNumber : Finset α →o ℕ :=
  ⟨fun s ↦ Nat.findGreatest (fun m ↦ ∃ t ⊆ s, #t = m ∧ ThreeGPFree (t : Set α)) #s, by
    rintro t u htu
    refine Nat.findGreatest_mono (fun m => ?_) (card_le_card htu)
    rintro ⟨v, hvt, hv⟩
    exact ⟨v, hvt.trans htu, hv⟩⟩

@[to_additive]
theorem mulRothNumber_le : mulRothNumber s ≤ #s := Nat.findGreatest_le #s

@[to_additive]
theorem mulRothNumber_spec :
    ∃ t ⊆ s, #t = mulRothNumber s ∧ ThreeGPFree (t : Set α) :=
  Nat.findGreatest_spec (P := fun m ↦ ∃ t ⊆ s, #t = m ∧ ThreeGPFree (t : Set α))
    (Nat.zero_le _) ⟨∅, empty_subset _, card_empty, by norm_cast; exact threeGPFree_empty⟩

variable {s t} {n : ℕ}

@[to_additive]
theorem ThreeGPFree.le_mulRothNumber (hs : ThreeGPFree (s : Set α)) (h : s ⊆ t) :
    #s ≤ mulRothNumber t :=
  Nat.le_findGreatest (card_le_card h) ⟨s, h, rfl, hs⟩

@[to_additive]
theorem ThreeGPFree.mulRothNumber_eq (hs : ThreeGPFree (s : Set α)) :
    mulRothNumber s = #s :=
  (mulRothNumber_le _).antisymm <| hs.le_mulRothNumber <| Subset.refl _

@[to_additive (attr := simp)]
theorem mulRothNumber_empty : mulRothNumber (∅ : Finset α) = 0 :=
  Nat.eq_zero_of_le_zero <| (mulRothNumber_le _).trans card_empty.le

@[to_additive (attr := simp)]
theorem mulRothNumber_singleton (a : α) : mulRothNumber ({a} : Finset α) = 1 := by
  refine ThreeGPFree.mulRothNumber_eq ?_
  rw [coe_singleton]
  exact threeGPFree_singleton a

@[to_additive]
theorem mulRothNumber_union_le (s t : Finset α) :
    mulRothNumber (s ∪ t) ≤ mulRothNumber s + mulRothNumber t :=
  let ⟨u, hus, hcard, hu⟩ := mulRothNumber_spec (s ∪ t)
  calc
    mulRothNumber (s ∪ t) = #u := hcard.symm
    _ = #(u ∩ s ∪ u ∩ t) := by rw [← inter_union_distrib_left, inter_eq_left.2 hus]
    _ ≤ #(u ∩ s) + #(u ∩ t) := card_union_le _ _
    _ ≤ mulRothNumber s + mulRothNumber t := _root_.add_le_add
      ((hu.mono inter_subset_left).le_mulRothNumber inter_subset_right)
      ((hu.mono inter_subset_left).le_mulRothNumber inter_subset_right)

@[to_additive]
theorem le_mulRothNumber_product (s : Finset α) (t : Finset β) :
    mulRothNumber s * mulRothNumber t ≤ mulRothNumber (s ×ˢ t) := by
  obtain ⟨u, hus, hucard, hu⟩ := mulRothNumber_spec s
  obtain ⟨v, hvt, hvcard, hv⟩ := mulRothNumber_spec t
  rw [← hucard, ← hvcard, ← card_product]
  refine ThreeGPFree.le_mulRothNumber ?_ (product_subset_product hus hvt)
  rw [coe_product]
  exact hu.prod hv

@[to_additive]
theorem mulRothNumber_lt_of_forall_not_threeGPFree
    (h : ∀ t ∈ powersetCard n s, ¬ThreeGPFree ((t : Finset α) : Set α)) :
    mulRothNumber s < n := by
  obtain ⟨t, hts, hcard, ht⟩ := mulRothNumber_spec s
  rw [← hcard, ← not_le]
  intro hn
  obtain ⟨u, hut, rfl⟩ := exists_subset_card_eq hn
  exact h _ (mem_powersetCard.2 ⟨hut.trans hts, rfl⟩) (ht.mono hut)

end Monoid

section CommMonoid
variable [CommMonoid α] [CommMonoid β] [DecidableEq β] {A : Finset α} {B : Finset β} {f : α → β}

/-- Arithmetic progressions can be pushed forward along bijective 2-Freiman homs. -/
@[to_additive "Arithmetic progressions can be pushed forward along bijective 2-Freiman homs."]
lemma IsMulFreimanHom.mulRothNumber_mono (hf : IsMulFreimanHom 2 A B f) (hf' : Set.BijOn f A B) :
    mulRothNumber B ≤ mulRothNumber A := by
  obtain ⟨s, hsB, hcard, hs⟩ := mulRothNumber_spec B
  have hsA : invFunOn f A '' s ⊆ A :=
    (hf'.surjOn.mapsTo_invFunOn.mono (coe_subset.2 hsB) Subset.rfl).image_subset
  have hfsA : Set.SurjOn f A s := hf'.surjOn.mono Subset.rfl (coe_subset.2 hsB)
  rw [← hcard, ← s.card_image_of_injOn ((invFunOn_injOn_image f _).mono hfsA)]
  refine ThreeGPFree.le_mulRothNumber ?_ (mod_cast hsA)
  rw [coe_image]
  simpa using (hf.subset hsA hfsA.bijOn_subset.mapsTo).threeGPFree (hf'.injOn.mono hsA) hs

/-- Arithmetic progressions are preserved under 2-Freiman isos. -/
@[to_additive "Arithmetic progressions are preserved under 2-Freiman isos."]
lemma IsMulFreimanIso.mulRothNumber_congr (hf : IsMulFreimanIso 2 A B f) :
    mulRothNumber A = mulRothNumber B := by
  refine le_antisymm ?_ (hf.isMulFreimanHom.mulRothNumber_mono hf.bijOn)
  obtain ⟨s, hsA, hcard, hs⟩ := mulRothNumber_spec A
  rw [← coe_subset] at hsA
  have hfs : Set.InjOn f s := hf.bijOn.injOn.mono hsA
  have := (hf.subset hsA hfs.bijOn_image).threeGPFree_congr.1 hs
  rw [← coe_image] at this
  rw [← hcard, ← Finset.card_image_of_injOn hfs]
  refine this.le_mulRothNumber ?_
  rw [← coe_subset, coe_image]
  exact (hf.bijOn.mapsTo.mono hsA Subset.rfl).image_subset

end CommMonoid

section CancelCommMonoid

variable [CancelCommMonoid α] (s : Finset α) (a : α)

@[to_additive (attr := simp)]
theorem mulRothNumber_map_mul_left :
    mulRothNumber (s.map <| mulLeftEmbedding a) = mulRothNumber s := by
  refine le_antisymm ?_ ?_
  · obtain ⟨u, hus, hcard, hu⟩ := mulRothNumber_spec (s.map <| mulLeftEmbedding a)
    rw [subset_map_iff] at hus
    obtain ⟨u, hus, rfl⟩ := hus
    rw [coe_map] at hu
    rw [← hcard, card_map]
    exact (threeGPFree_smul_set.1 hu).le_mulRothNumber hus
  · obtain ⟨u, hus, hcard, hu⟩ := mulRothNumber_spec s
    have h : ThreeGPFree (u.map <| mulLeftEmbedding a : Set α) := by rw [coe_map]; exact hu.smul_set
    convert h.le_mulRothNumber (map_subset_map.2 hus) using 1
    rw [card_map, hcard]

@[to_additive (attr := simp)]
theorem mulRothNumber_map_mul_right :
    mulRothNumber (s.map <| mulRightEmbedding a) = mulRothNumber s := by
  rw [← mulLeftEmbedding_eq_mulRightEmbedding, mulRothNumber_map_mul_left s a]

end CancelCommMonoid

end RothNumber

section rothNumberNat

variable {k n : ℕ}

/-- The Roth number of a natural `N` is the largest integer `m` for which there is a subset of
`range N` of size `m` with no arithmetic progression of length 3.
Trivially, `rothNumberNat N ≤ N`, but Roth's theorem (proved in 1953) shows that
`rothNumberNat N = o(N)` and the construction by Behrend gives a lower bound of the form
`N * exp(-C sqrt(log(N))) ≤ rothNumberNat N`.
A significant refinement of Roth's theorem by Bloom and Sisask announced in 2020 gives
`rothNumberNat N = O(N / (log N)^(1+c))` for an absolute constant `c`. -/
def rothNumberNat : ℕ →o ℕ :=
  ⟨fun n => addRothNumber (range n), addRothNumber.mono.comp range_mono⟩

theorem rothNumberNat_def (n : ℕ) : rothNumberNat n = addRothNumber (range n) :=
  rfl

theorem rothNumberNat_le (N : ℕ) : rothNumberNat N ≤ N :=
  (addRothNumber_le _).trans (card_range _).le

theorem rothNumberNat_spec (n : ℕ) :
    ∃ t ⊆ range n, #t = rothNumberNat n ∧ ThreeAPFree (t : Set ℕ) :=
  addRothNumber_spec _

/-- A verbose specialization of `threeAPFree.le_addRothNumber`, sometimes convenient in
practice. -/
theorem ThreeAPFree.le_rothNumberNat (s : Finset ℕ) (hs : ThreeAPFree (s : Set ℕ))
    (hsn : ∀ x ∈ s, x < n) (hsk : #s = k) : k ≤ rothNumberNat n :=
  hsk.ge.trans <| hs.le_addRothNumber fun x hx => mem_range.2 <| hsn x hx

/-- The Roth number is a subadditive function. Note that by Fekete's lemma this shows that
the limit `rothNumberNat N / N` exists, but Roth's theorem gives the stronger result that this
limit is actually `0`. -/
theorem rothNumberNat_add_le (M N : ℕ) :
    rothNumberNat (M + N) ≤ rothNumberNat M + rothNumberNat N := by
  simp_rw [rothNumberNat_def]
  rw [range_add_eq_union, ← addRothNumber_map_add_left (range N) M]
  exact addRothNumber_union_le _ _

@[simp]
theorem rothNumberNat_zero : rothNumberNat 0 = 0 :=
  rfl

theorem addRothNumber_Ico (a b : ℕ) : addRothNumber (Ico a b) = rothNumberNat (b - a) := by
  obtain h | h := le_total b a
  · rw [Nat.sub_eq_zero_of_le h, Ico_eq_empty_of_le h, rothNumberNat_zero, addRothNumber_empty]
  convert addRothNumber_map_add_left _ a
  rw [range_eq_Ico, map_eq_image]
  convert (image_add_left_Ico 0 (b - a) _).symm
  exact (add_tsub_cancel_of_le h).symm

open Fin.NatCast in -- TODO: should this be refactored to avoid needing the coercion?
lemma Fin.addRothNumber_eq_rothNumberNat (hkn : 2 * k ≤ n) :
    addRothNumber (Iio k : Finset (Fin n.succ)) = rothNumberNat k :=
  IsAddFreimanIso.addRothNumber_congr <| mod_cast isAddFreimanIso_Iio two_ne_zero hkn

open Fin.CommRing in -- TODO: should this be refactored to avoid needing the coercion?
lemma Fin.addRothNumber_le_rothNumberNat (k n : ℕ) (hkn : k ≤ n) :
    addRothNumber (Iio k : Finset (Fin n.succ)) ≤ rothNumberNat k := by
  suffices h : Set.BijOn (Nat.cast : ℕ → Fin n.succ) (range k) (Iio k : Finset (Fin n.succ)) by
    exact (AddMonoidHomClass.isAddFreimanHom (Nat.castRingHom _) h.mapsTo).addRothNumber_mono h
  refine ⟨?_, (CharP.natCast_injOn_Iio _ n.succ).mono (by simp; omega), ?_⟩
  · simpa using fun x ↦ natCast_strictMono hkn
  simp only [Set.SurjOn, coe_Iio, Set.subset_def, Set.mem_Iio, Set.mem_image, lt_iff_val_lt_val,
    val_cast_of_lt, Nat.lt_succ_iff.2 hkn, coe_range]
  exact fun x hx ↦ ⟨x, hx, by simp⟩

end rothNumberNat
