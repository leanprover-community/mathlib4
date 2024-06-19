/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Finset.Slice
import Mathlib.Order.SupClosed

#align_import combinatorics.colex from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# Colexigraphic order

We define the colex order for finite sets, and give a couple of important lemmas and properties
relating to it.

The colex ordering likes to avoid large values: If the biggest element of `t` is bigger than all
elements of `s`, then `s < t`.

In the special case of `ℕ`, it can be thought of as the "binary" ordering. That is, order `s` based
on $∑_{i ∈ s} 2^i$. It's defined here on `Finset α` for any linear order `α`.

In the context of the Kruskal-Katona theorem, we are interested in how colex behaves for sets of a
fixed size. For example, for size 3, the colex order on ℕ starts
`012, 013, 023, 123, 014, 024, 124, 034, 134, 234, ...`

## Main statements

* Colex order properties - linearity, decidability and so on.
* `Finset.Colex.forall_lt_mono`: if `s < t` in colex, and everything in `t` is `< a`, then
  everything in `s` is `< a`. This confirms the idea that an enumeration under colex will exhaust
  all sets using elements `< a` before allowing `a` to be included.
* `Finset.toColex_image_le_toColex_image`: Strictly monotone functions preserve colex.
* `Finset.geomSum_le_geomSum_iff_toColex_le_toColex`: Colex for α = ℕ is the same as binary.
  This also proves binary expansions are unique.

## See also

Related files are:
* `Data.List.Lex`: Lexicographic order on lists.
* `Data.Pi.Lex`: Lexicographic order on `Πₗ i, α i`.
* `Data.PSigma.Order`: Lexicographic order on `Σ' i, α i`.
* `Data.Sigma.Order`: Lexicographic order on `Σ i, α i`.
* `Data.Prod.Lex`: Lexicographic order on `α × β`.

## TODO

* Generalise `Colex.initSeg` so that it applies to `ℕ`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

colex, colexicographic, binary
-/

open Finset Function

#align nat.sum_two_pow_lt Nat.geomSum_lt

variable {α β : Type*}

namespace Finset

/-- Type synonym of `Finset α` equipped with the colexicographic order rather than the inclusion
order. -/
@[ext]
structure Colex (α) :=
  /-- `toColex` is the "identity" function between `Finset α` and `Finset.Colex α`. -/
  toColex ::
  /-- `ofColex` is the "identity" function between `Finset.Colex α` and `Finset α`. -/
  (ofColex : Finset α)

-- TODO: Why can't we export?
--export Colex (toColex)

open Colex

instance : Inhabited (Colex α) := ⟨⟨∅⟩⟩

@[simp] lemma toColex_ofColex (s : Colex α) : toColex (ofColex s) = s := rfl
lemma ofColex_toColex (s : Finset α) : ofColex (toColex s) = s := rfl
lemma toColex_inj {s t : Finset α} : toColex s = toColex t ↔ s = t := by simp
@[simp]
lemma ofColex_inj {s t : Colex α} : ofColex s = ofColex t ↔ s = t := by cases s; cases t; simp
lemma toColex_ne_toColex {s t : Finset α} : toColex s ≠ toColex t ↔ s ≠ t := by simp
lemma ofColex_ne_ofColex {s t : Colex α} : ofColex s ≠ ofColex t ↔ s ≠ t := by simp

lemma toColex_injective : Injective (toColex : Finset α → Colex α) := fun _ _ ↦ toColex_inj.1
lemma ofColex_injective : Injective (ofColex : Colex α → Finset α) := fun _ _ ↦ ofColex_inj.1

namespace Colex
section PartialOrder
variable [PartialOrder α] [PartialOrder β] {f : α → β} {𝒜 𝒜₁ 𝒜₂ : Finset (Finset α)}
  {s t u : Finset α} {a b : α}

instance instLE : LE (Colex α) where
  le s t := ∀ ⦃a⦄, a ∈ ofColex s → a ∉ ofColex t → ∃ b, b ∈ ofColex t ∧ b ∉ ofColex s ∧ a ≤ b

-- TODO: This lemma is weirdly useful given how strange its statement is.
-- Is there a nicer statement? Should this lemma be made public?
private lemma trans_aux (hst : toColex s ≤ toColex t) (htu : toColex t ≤ toColex u)
    (has : a ∈ s) (hat : a ∉ t) : ∃ b, b ∈ u ∧ b ∉ s ∧ a ≤ b := by
  classical
  let s' : Finset α := s.filter fun b ↦ b ∉ t ∧ a ≤ b
  have ⟨b, hb, hbmax⟩ := exists_maximal s' ⟨a, by simp [s', has, hat]⟩
  simp only [s', mem_filter, and_imp] at hb hbmax
  have ⟨c, hct, hcs, hbc⟩ := hst hb.1 hb.2.1
  by_cases hcu : c ∈ u
  · exact ⟨c, hcu, hcs, hb.2.2.trans hbc⟩
  have ⟨d, hdu, hdt, hcd⟩ := htu hct hcu
  have had : a ≤ d := hb.2.2.trans <| hbc.trans hcd
  refine ⟨d, hdu, fun hds ↦ ?_, had⟩
  exact hbmax d hds hdt had <| hbc.trans_lt <| hcd.lt_of_ne <| ne_of_mem_of_not_mem hct hdt

private lemma antisymm_aux (hst : toColex s ≤ toColex t) (hts : toColex t ≤ toColex s) : s ⊆ t := by
  intro a has
  by_contra! hat
  have ⟨_b, hb₁, hb₂, _⟩ := trans_aux hst hts has hat
  exact hb₂ hb₁

instance instPartialOrder : PartialOrder (Colex α) where
  le_refl s a ha ha' := (ha' ha).elim
  le_antisymm s t hst hts := Colex.ext _ _ <| (antisymm_aux hst hts).antisymm (antisymm_aux hts hst)
  le_trans s t u hst htu a has hau := by
    by_cases hat : a ∈ ofColex t
    · have ⟨b, hbu, hbt, hab⟩ := htu hat hau
      by_cases hbs : b ∈ ofColex s
      · have ⟨c, hcu, hcs, hbc⟩ := trans_aux hst htu hbs hbt
        exact ⟨c, hcu, hcs, hab.trans hbc⟩
      · exact ⟨b, hbu, hbs, hab⟩
    · exact trans_aux hst htu has hat

lemma le_def {s t : Colex α} :
    s ≤ t ↔ ∀ ⦃a⦄, a ∈ ofColex s → a ∉ ofColex t → ∃ b, b ∈ ofColex t ∧ b ∉ ofColex s ∧ a ≤ b :=
  Iff.rfl

lemma toColex_le_toColex :
    toColex s ≤ toColex t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t → ∃ b, b ∈ t ∧ b ∉ s ∧ a ≤ b := Iff.rfl

lemma toColex_lt_toColex :
    toColex s < toColex t ↔ s ≠ t ∧ ∀ ⦃a⦄, a ∈ s → a ∉ t → ∃ b, b ∈ t ∧ b ∉ s ∧ a ≤ b := by
  simp [lt_iff_le_and_ne, toColex_le_toColex, and_comm]

/-- If `s ⊆ t`, then `s ≤ t` in the colex order. Note the converse does not hold, as inclusion does
not form a linear order. -/
lemma toColex_mono : Monotone (toColex : Finset α → Colex α) :=
  fun _s _t hst _a has hat ↦ (hat <| hst has).elim

/-- If `s ⊂ t`, then `s < t` in the colex order. Note the converse does not hold, as inclusion does
not form a linear order. -/
lemma toColex_strictMono : StrictMono (toColex : Finset α → Colex α) :=
  toColex_mono.strictMono_of_injective toColex_injective

/-- If `s ⊆ t`, then `s ≤ t` in the colex order. Note the converse does not hold, as inclusion does
not form a linear order. -/
lemma toColex_le_toColex_of_subset (h : s ⊆ t) : toColex s ≤ toColex t := toColex_mono h

/-- If `s ⊂ t`, then `s < t` in the colex order. Note the converse does not hold, as inclusion does
not form a linear order. -/
lemma toColex_lt_toColex_of_ssubset (h : s ⊂ t) : toColex s < toColex t := toColex_strictMono h

instance instOrderBot : OrderBot (Colex α) where
  bot := toColex ∅
  bot_le s a ha := by cases ha

@[simp] lemma toColex_empty : toColex (∅ : Finset α) = ⊥ := rfl
@[simp] lemma ofColex_bot : ofColex (⊥ : Colex α) = ∅ := rfl

/-- If `s ≤ t` in colex, and all elements in `t` are small, then all elements in `s` are small. -/
lemma forall_le_mono (hst : toColex s ≤ toColex t) (ht : ∀ b ∈ t, b ≤ a) : ∀ b ∈ s, b ≤ a := by
  rintro b hb
  by_cases b ∈ t
  · exact ht _ ‹_›
  · obtain ⟨c, hct, -, hbc⟩ := hst hb ‹_›
    exact hbc.trans <| ht _ hct

/-- If `s ≤ t` in colex, and all elements in `t` are small, then all elements in `s` are small. -/
lemma forall_lt_mono (hst : toColex s ≤ toColex t) (ht : ∀ b ∈ t, b < a) : ∀ b ∈ s, b < a := by
  rintro b hb
  by_cases b ∈ t
  · exact ht _ ‹_›
  · obtain ⟨c, hct, -, hbc⟩ := hst hb ‹_›
    exact hbc.trans_lt <| ht _ hct

/-- `s ≤ {a}` in colex iff all elements of `s` are strictly less than `a`, except possibly `a` in
which case `s = {a}`. -/
lemma toColex_le_singleton : toColex s ≤ toColex {a} ↔ ∀ b ∈ s, b ≤ a ∧ (a ∈ s → b = a) := by
  simp only [toColex_le_toColex, mem_singleton, and_assoc, exists_eq_left]
  refine forall₂_congr fun b _ ↦ ?_; obtain rfl | hba := eq_or_ne b a <;> aesop

/-- `s < {a}` in colex iff all elements of `s` are strictly less than `a`. -/
lemma toColex_lt_singleton : toColex s < toColex {a} ↔ ∀ b ∈ s, b < a := by
  rw [lt_iff_le_and_ne, toColex_le_singleton, toColex_ne_toColex]
  refine ⟨fun h b hb ↦ (h.1 _ hb).1.lt_of_ne ?_,
    fun h ↦ ⟨fun b hb ↦ ⟨(h _ hb).le, fun ha ↦ (lt_irrefl _ <| h _ ha).elim⟩, ?_⟩⟩ <;> rintro rfl
  · refine h.2 <| eq_singleton_iff_unique_mem.2 ⟨hb, fun c hc ↦ (h.1 _ hc).2 hb⟩
  · simp at h

/-- `{a} ≤ s` in colex iff `s` contains an element greated than or equal to `a`. -/
lemma singleton_le_toColex : (toColex {a} : Colex α) ≤ toColex s ↔ ∃ x ∈ s, a ≤ x := by
  simp [toColex_le_toColex]; by_cases a ∈ s <;> aesop

/-- Colex is an extension of the base order. -/
lemma singleton_le_singleton : (toColex {a} : Colex α) ≤ toColex {b} ↔ a ≤ b := by
  simp [toColex_le_singleton, eq_comm]

/-- Colex is an extension of the base order. -/
lemma singleton_lt_singleton : (toColex {a} : Colex α) < toColex {b} ↔ a < b := by
  simp [toColex_lt_singleton]

variable [DecidableEq α]

instance instDecidableEq : DecidableEq (Colex α) := fun s t ↦
  decidable_of_iff' (s.ofColex = t.ofColex) <| Colex.ext_iff _ _

instance instDecidableLE [@DecidableRel α (· ≤ ·)] : @DecidableRel (Colex α) (· ≤ ·) := fun s t ↦
  decidable_of_iff'
    (∀ ⦃a⦄, a ∈ ofColex s → a ∉ ofColex t → ∃ b, b ∈ ofColex t ∧ b ∉ ofColex s ∧ a ≤ b) Iff.rfl

instance instDecidableLT [@DecidableRel α (· ≤ ·)] : @DecidableRel (Colex α) (· < ·) :=
  decidableLTOfDecidableLE

lemma le_iff_sdiff_subset_lowerClosure {s t : Colex α} :
    s ≤ t ↔ (ofColex s : Set α) \ ofColex t ⊆ lowerClosure (ofColex t \ ofColex s : Set α) := by
  simp [le_def, Set.subset_def, and_assoc]

/-- The colexigraphic order is insensitive to removing the same elements from both sets. -/
lemma toColex_sdiff_le_toColex_sdiff (hus : u ⊆ s) (hut : u ⊆ t) :
    toColex (s \ u) ≤ toColex (t \ u) ↔ toColex s ≤ toColex t := by
  simp_rw [toColex_le_toColex, ← and_imp, ← and_assoc, ← mem_sdiff,
    sdiff_sdiff_sdiff_cancel_right hus, sdiff_sdiff_sdiff_cancel_right hut]

/-- The colexigraphic order is insensitive to removing the same elements from both sets. -/
lemma toColex_sdiff_lt_toColex_sdiff (hus : u ⊆ s) (hut : u ⊆ t) :
    toColex (s \ u) < toColex (t \ u) ↔ toColex s < toColex t :=
  lt_iff_lt_of_le_iff_le' (toColex_sdiff_le_toColex_sdiff hut hus) <|
    toColex_sdiff_le_toColex_sdiff hus hut

@[simp] lemma toColex_sdiff_le_toColex_sdiff' :
    toColex (s \ t) ≤ toColex (t \ s) ↔ toColex s ≤ toColex t := by
  simpa using toColex_sdiff_le_toColex_sdiff (inter_subset_left s t) (inter_subset_right s t)

@[simp] lemma toColex_sdiff_lt_toColex_sdiff' :
 toColex (s \ t) < toColex (t \ s) ↔ toColex s < toColex t := by
  simpa using toColex_sdiff_lt_toColex_sdiff (inter_subset_left s t) (inter_subset_right s t)

end PartialOrder

variable [LinearOrder α] [LinearOrder β] {f : α → β} {𝒜 𝒜₁ 𝒜₂ : Finset (Finset α)}
  {s t u : Finset α} {a b : α} {r : ℕ}

instance instLinearOrder : LinearOrder (Colex α) where
  le_total s t := by
    classical
    obtain rfl | hts := eq_or_ne t s
    · simp
    have ⟨a, ha, hamax⟩ := exists_max_image _ id (symmDiff_nonempty.2 <| ofColex_ne_ofColex.2 hts)
    simp_rw [mem_symmDiff] at ha hamax
    exact ha.imp (fun ha b hbs hbt ↦ ⟨a, ha.1, ha.2, hamax _ <| Or.inr ⟨hbs, hbt⟩⟩)
      (fun ha b hbt hbs ↦ ⟨a, ha.1, ha.2, hamax _ <| Or.inl ⟨hbt, hbs⟩⟩)
  decidableLE := instDecidableLE
  decidableLT := instDecidableLT

open scoped symmDiff

private lemma max_mem_aux {s t : Colex α} (hst : s ≠ t) : (ofColex s ∆ ofColex t).Nonempty := by
  simpa

lemma toColex_lt_toColex_iff_exists_forall_lt :
    toColex s < toColex t ↔ ∃ a ∈ t, a ∉ s ∧ ∀ b ∈ s, b ∉ t → b < a := by
  rw [← not_le, toColex_le_toColex, not_forall]
  simp only [not_forall, not_exists, not_and, not_le, exists_prop, exists_and_left]

lemma lt_iff_exists_forall_lt {s t : Colex α} :
    s < t ↔ ∃ a ∈ ofColex t, a ∉ ofColex s ∧ ∀ b ∈ ofColex s, b ∉ ofColex t → b < a :=
  toColex_lt_toColex_iff_exists_forall_lt

lemma toColex_le_toColex_iff_max'_mem :
    toColex s ≤ toColex t ↔ ∀ hst : s ≠ t, (s ∆ t).max' (symmDiff_nonempty.2 hst) ∈ t := by
  refine ⟨fun h hst ↦ ?_, fun h a has hat ↦ ?_⟩
  · set m := (s ∆ t).max' (symmDiff_nonempty.2 hst)
    by_contra hmt
    have hms : m ∈ s := by simpa [mem_symmDiff, hmt] using max'_mem _ <| symmDiff_nonempty.2 hst
    have ⟨b, hbt, hbs, hmb⟩ := h hms hmt
    exact lt_irrefl _ <| (max'_lt_iff _ _).1 (hmb.lt_of_ne <| ne_of_mem_of_not_mem hms hbs) _ <|
      mem_symmDiff.2 <| Or.inr ⟨hbt, hbs⟩
  · have hst : s ≠ t := ne_of_mem_of_not_mem' has hat
    refine ⟨_, h hst, ?_, le_max' _ _ <| mem_symmDiff.2 <| Or.inl ⟨has, hat⟩⟩
    simpa [mem_symmDiff, h hst] using max'_mem _ <| symmDiff_nonempty.2 hst

lemma le_iff_max'_mem {s t : Colex α} :
    s ≤ t ↔ ∀ h : s ≠ t, (ofColex s ∆ ofColex t).max' (max_mem_aux h) ∈ ofColex t :=
  toColex_le_toColex_iff_max'_mem.trans
    ⟨fun h hst ↦ h <| ofColex_ne_ofColex.2 hst, fun h hst ↦ h <| ofColex_ne_ofColex.1 hst⟩

lemma toColex_lt_toColex_iff_max'_mem :
    toColex s < toColex t ↔ ∃ hst : s ≠ t, (s ∆ t).max' (symmDiff_nonempty.2 hst) ∈ t := by
  rw [lt_iff_le_and_ne, toColex_le_toColex_iff_max'_mem]; aesop

lemma lt_iff_max'_mem {s t : Colex α} :
    s < t ↔ ∃ h : s ≠ t, (ofColex s ∆ ofColex t).max' (max_mem_aux h) ∈ ofColex t := by
  rw [lt_iff_le_and_ne, le_iff_max'_mem]; aesop

/-- Strictly monotone functions preserve the colex ordering. -/
lemma toColex_image_le_toColex_image (hf : StrictMono f) :
    toColex (s.image f) ≤ toColex (t.image f) ↔ toColex s ≤ toColex t := by
  simp [toColex_le_toColex, hf.le_iff_le, hf.injective.eq_iff]

/-- Strictly monotone functions preserve the colex ordering. -/
lemma toColex_image_lt_toColex_image (hf : StrictMono f) :
    toColex (s.image f) < toColex (t.image f) ↔ toColex s < toColex t :=
  lt_iff_lt_of_le_iff_le <| toColex_image_le_toColex_image hf

lemma toColex_image_ofColex_strictMono (hf : StrictMono f) :
    StrictMono fun s ↦ toColex <| image f <| ofColex s :=
  fun _s _t ↦ (toColex_image_lt_toColex_image hf).2

/-! ### Initial segments -/

/-- `𝒜` is an initial segment of the colexigraphic order on sets of `r`, and that if `t` is below
`s` in colex where `t` has size `r` and `s` is in `𝒜`, then `t` is also in `𝒜`. In effect, `𝒜` is
downwards closed with respect to colex among sets of size `r`. -/
def IsInitSeg (𝒜 : Finset (Finset α)) (r : ℕ) : Prop :=
  (𝒜 : Set (Finset α)).Sized r ∧
    ∀ ⦃s t : Finset α⦄, s ∈ 𝒜 → toColex t < toColex s ∧ t.card = r → t ∈ 𝒜

@[simp] lemma isInitSeg_empty : IsInitSeg (∅ : Finset (Finset α)) r := by simp [IsInitSeg]

/-- Initial segments are nested in some way. In particular, if they're the same size they're equal.
-/
lemma IsInitSeg.total (h₁ : IsInitSeg 𝒜₁ r) (h₂ : IsInitSeg 𝒜₂ r) : 𝒜₁ ⊆ 𝒜₂ ∨ 𝒜₂ ⊆ 𝒜₁ := by
  classical
  simp_rw [← sdiff_eq_empty_iff_subset, ← not_nonempty_iff_eq_empty]
  by_contra! h
  have ⟨⟨s, hs⟩, t, ht⟩ := h
  rw [mem_sdiff] at hs ht
  obtain hst | hst | hts := trichotomous_of (α := Colex α) (· < ·) (toColex s) (toColex t)
  · exact hs.2 <| h₂.2 ht.1 ⟨hst, h₁.1 hs.1⟩
  · simp only [toColex.injEq] at hst
    exact ht.2 <| hst ▸ hs.1
  · exact ht.2 <| h₁.2 hs.1 ⟨hts, h₂.1 ht.1⟩

variable [Fintype α]

/-- The initial segment of the colexicographic order on sets with `s.card` elements and ending at
`s`. -/
def initSeg (s : Finset α) : Finset (Finset α) :=
  univ.filter fun t ↦ s.card = t.card ∧ toColex t ≤ toColex s

@[simp]
lemma mem_initSeg : t ∈ initSeg s ↔ s.card = t.card ∧ toColex t ≤ toColex s := by simp [initSeg]

lemma mem_initSeg_self : s ∈ initSeg s := by simp
@[simp] lemma initSeg_nonempty : (initSeg s).Nonempty := ⟨s, mem_initSeg_self⟩

lemma isInitSeg_initSeg : IsInitSeg (initSeg s) s.card := by
  refine ⟨fun t ht => (mem_initSeg.1 ht).1.symm, fun t₁ t₂ ht₁ ht₂ ↦ mem_initSeg.2 ⟨ht₂.2.symm, ?_⟩⟩
  rw [mem_initSeg] at ht₁
  exact ht₂.1.le.trans ht₁.2

lemma IsInitSeg.exists_initSeg (h𝒜 : IsInitSeg 𝒜 r) (h𝒜₀ : 𝒜.Nonempty) :
    ∃ s : Finset α, s.card = r ∧ 𝒜 = initSeg s := by
  have hs := sup'_mem (ofColex ⁻¹' 𝒜) (LinearOrder.supClosed _) 𝒜 h𝒜₀ toColex
    (fun a ha ↦ by simpa using ha)
  refine ⟨_, h𝒜.1 hs, ?_⟩
  ext t
  rw [mem_initSeg]
  refine ⟨fun p ↦ ?_, ?_⟩
  · rw [h𝒜.1 p, h𝒜.1 hs]
    exact ⟨rfl, le_sup' _ p⟩
  rintro ⟨cards, le⟩
  obtain p | p := le.eq_or_lt
  · rwa [toColex_inj.1 p]
  · exact h𝒜.2 hs ⟨p, cards ▸ h𝒜.1 hs⟩

/-- Being a nonempty initial segment of colex is equivalent to being an `initSeg`. -/
lemma isInitSeg_iff_exists_initSeg :
    IsInitSeg 𝒜 r ∧ 𝒜.Nonempty ↔ ∃ s : Finset α, s.card = r ∧ 𝒜 = initSeg s := by
  refine ⟨fun h𝒜 ↦ h𝒜.1.exists_initSeg h𝒜.2, ?_⟩
  rintro ⟨s, rfl, rfl⟩
  exact ⟨isInitSeg_initSeg, initSeg_nonempty⟩

end Colex

open Colex

/-!
### Colex on `ℕ`

The colexicographic order agrees with the order induced by interpreting a set of naturals as a
`n`-ary expansion.
-/

section Nat
variable {s t : Finset ℕ} {n : ℕ}

lemma geomSum_ofColex_strictMono (hn : 2 ≤ n) : StrictMono fun s ↦ ∑ k ∈ ofColex s, n ^ k := by
  rintro ⟨s⟩ ⟨t⟩ hst
  rw [toColex_lt_toColex_iff_exists_forall_lt] at hst
  obtain ⟨a, hat, has, ha⟩ := hst
  rw [← sum_sdiff_lt_sum_sdiff]
  exact (Nat.geomSum_lt hn <| by simpa).trans_le <| single_le_sum (fun _ _ ↦ by positivity) <|
    mem_sdiff.2 ⟨hat, has⟩

/-- For finsets of naturals of naturals, the colexicographic order is equivalent to the order
induced by the `n`-ary expansion. -/
lemma geomSum_le_geomSum_iff_toColex_le_toColex (hn : 2 ≤ n) :
    ∑ k ∈ s, n ^ k ≤ ∑ k ∈ t, n ^ k ↔ toColex s ≤ toColex t :=
  (geomSum_ofColex_strictMono hn).le_iff_le

/-- For finsets of naturals of naturals, the colexicographic order is equivalent to the order
induced by the `n`-ary expansion. -/
lemma geomSum_lt_geomSum_iff_toColex_lt_toColex (hn : 2 ≤ n) :
    ∑ i ∈ s, n ^ i < ∑ i ∈ t, n ^ i ↔ toColex s < toColex t :=
  (geomSum_ofColex_strictMono hn).lt_iff_lt

-- TODO: Package the above in the `n = 2` case as an order isomorphism `Colex ℕ ≃o ℕ`

end Nat
end Finset
