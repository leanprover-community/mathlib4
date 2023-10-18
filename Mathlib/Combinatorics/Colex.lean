/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov
-/
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Finset.Slice
import Mathlib.Order.SupClosed

#align_import combinatorics.colex from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# Colexigraphic order

We define the colex order for finite sets, and give a couple of important lemmas and properties
relating to it.

The colex ordering likes to avoid large values: If the biggest element of `t` is bigger than all elements of `s`, then `s < t`.

In the special case of `ℕ`, it can be thought of as the "binary" ordering. That is, order `s` based
on `∑_{i ∈ s} 2^i`. It's defined here on `Finset α` for any linear order `α`.

In the context of the Kruskal-Katona theorem, we are interested in how colex behaves for sets of a
fixed size. For example, for size 3, the colex order on ℕ starts
`123, 124, 134, 234, 125, 135, 235, 145, 245, 345, ...`

## Main statements

* Colex order properties - linearity, decidability and so on.
* `Finset.Colex.forall_lt_mono`: if `s < t` in colex, and everything in `t` is `< a`, then
  everything in `s` is `< a`. This confirms the idea that an enumeration under colex will exhaust
  all sets using elements `< a` before allowing `a` to be included.
* `Finse.toColex_image_lt_toColex_image`: Strictly monotone functions preserve colex.
* `Finset.sum_two_pow_le_iff_colex_le`: colex for α = ℕ is the same as binary
  (this also proves binary expansions are unique)

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

open Finset
open scoped BigOperators

/-- If all the elements of a finset `s` of naturals are less than `n`, then the sum of their powers of `2` is less than `2 ^ k`. -/
lemma Nat.sum_two_pow_lt {n : ℕ} {s : Finset ℕ} (hs : ∀ k ∈ s, k < n) :
    ∑ k in s, 2 ^ k < 2 ^ n := by
  calc
    ∑ k in s, 2 ^ k ≤ ∑ k in range n, 2 ^ k := sum_le_sum_of_subset fun k hk ↦ mem_range.2 $ hs _ hk
    _ = 2 ^ n - 1 := by
        simp_rw [←one_add_one_eq_two, ←geom_sum_mul_add 1 n, mul_one, add_tsub_cancel_right]
    _ < 2 ^ n := tsub_lt_self (by positivity) zero_lt_one
#align nat.sum_two_pow_lt Nat.sum_two_pow_lt

variable {α β : Type*}

namespace Finset

/-- Type synonym of `Finset α` equipped with the colexicographic order rather than the inclusion
order. -/
@[ext]
structure Colex (α) := toColex :: (ofColex : Finset α)

-- TODO: Why can't we export?
--export Colex (toColex)

open Colex

/-- `toColex` is the "identity" function between `Finset α` and `Finset.Colex α`. -/
add_decl_doc toColex

/-- `ofColex` is the "identity" function between `Finset.Colex α` and `Finset α`. -/
add_decl_doc ofColex

instance : Inhabited (Colex α) := ⟨⟨∅⟩⟩

@[simp] lemma toColex_ofColex (s : Colex α) : toColex (ofColex s) = s := rfl
lemma ofColex_toColex (s : Finset α) : ofColex (toColex s) = s := rfl
lemma toColex_inj {s t : Finset α} : toColex s = toColex t ↔ s = t := by simp
@[simp] lemma ofColex_inj {s t : Colex α} : ofColex s = ofColex t ↔ s = t := by cases s; cases t; simp
lemma toColex_ne_toColex {s t : Finset α} : toColex s ≠ toColex t ↔ s ≠ t := by simp
lemma ofColex_ne_ofColex {s t : Colex α} : ofColex s ≠ ofColex t ↔ s ≠ t := by simp

namespace Colex
section LT
variable [LT α] {s t u : Finset α}

/-- `s` is less than `t` in the colex ordering if the largest thing that's not in both sets is in t.
In other words, `max (s ∆ t) ∈ t` (if the maximum exists). -/
instance instLT : LT (Colex α) :=
  ⟨fun s t ↦ ∃ a, (∀ ⦃x⦄, a < x → (x ∈ ofColex s ↔ x ∈ ofColex t)) ∧ a ∉ ofColex s ∧ a ∈ ofColex t⟩

/-- We can define (≤) in the obvious way. -/
instance instLE : LE (Colex α) := ⟨fun s t ↦ s = t ∨ s < t⟩

lemma lt_def {s t : Colex α} :
    s < t ↔ ∃ a, (∀ ⦃x⦄, a < x → (x ∈ ofColex s ↔ x ∈ ofColex t)) ∧ a ∉ ofColex s ∧ a ∈ ofColex t :=
  Iff.rfl

lemma le_def {s t : Colex α} :
    s ≤ t ↔ s = t ∨
      ∃ a, (∀ ⦃x⦄, a < x → (x ∈ ofColex s ↔ x ∈ ofColex t)) ∧ a ∉ ofColex s ∧ a ∈ ofColex t :=
  Iff.rfl

lemma toColex_lt_toColex :
    toColex s < toColex t ↔ ∃ k, (∀ ⦃x⦄, k < x → (x ∈ s ↔ x ∈ t)) ∧ k ∉ s ∧ k ∈ t := Iff.rfl

lemma toColex_le_toColex :
    toColex s ≤ toColex t ↔ s = t ∨ ∃ k, (∀ ⦃x⦄, k < x → (x ∈ s ↔ x ∈ t)) ∧ k ∉ s ∧ k ∈ t := by
  simp [le_def]

instance instIsIrrefl : IsIrrefl (Colex α) (· < ·) := ⟨by simp [lt_def]⟩

variable [DecidableEq α]

/-- The colexigraphic order is insensitive to removing elements. -/
lemma toColex_sdiff_lt_toColex_sdiff (hus : u ⊆ s) (hut : u ⊆ t) :
    toColex (s \ u) < toColex (t \ u) ↔ toColex s < toColex t := by
  simp only [toColex_lt_toColex, toColex_lt_toColex, mem_sdiff, not_and, not_not]
  refine exists_congr fun k ↦ ⟨?_, ?_⟩
  · rintro ⟨h, hksu, hkt, hku⟩
    refine ⟨fun x hx ↦ ?_, mt hksu hku, hkt⟩
    specialize h hx
    tauto
  · rintro ⟨h, hks, hkt⟩
    exact ⟨fun x hx ↦ by rw [h hx], fun hks' ↦ (hks hks').elim, hkt, not_mem_mono hus hks⟩

@[simp] lemma toColex_sdiff_lt_toColex_sdiff' :
 toColex (s \ t) < toColex (t \ s) ↔ toColex s < toColex t := by
  simpa using toColex_sdiff_lt_toColex_sdiff (inter_subset_left s t) (inter_subset_right s t)

end LT

section LinearOrder
variable [LinearOrder α] [LinearOrder β] {f : α → β} {𝒜 𝒜₁ 𝒜₂ : Finset (Finset α)}
  {s t u : Finset α} {a b : α} {r : ℕ}

instance : IsStrictTotalOrder (Colex α) (· < ·) where
  irrefl := irrefl_of (· < ·)
  trans s t u := by
    rintro ⟨k₁, k₁z, notinA, inB⟩ ⟨k₂, k₂z, notinB, inC⟩
    obtain h | h := (ne_of_mem_of_not_mem inB notinB).lt_or_lt
    · refine' ⟨k₂, fun x hx ↦ _, by rwa [k₁z h], inC⟩
      rw [←k₂z hx]
      exact k₁z (h.trans hx)
    · refine' ⟨k₁, fun x hx ↦ _, notinA, by rwa [←k₂z h]⟩
      rw [k₁z hx]
      exact k₂z (h.trans hx)
  trichotomous s t := by
    classical
    obtain rfl | hts := eq_or_ne t s
    · simp
    obtain ⟨k, hk, z⟩ := exists_max_image _ id (symmDiff_nonempty.2 $ ofColex_ne_ofColex.2 hts)
    refine' (mem_symmDiff.1 hk).imp (fun hk => ⟨k, fun a ha ↦ _, hk.2, hk.1⟩) fun hk ↦
        Or.inr ⟨k, fun a ha ↦ _, hk.2, hk.1⟩ <;>
      simpa [mem_symmDiff, not_or, iff_iff_implies_and_implies, and_comm, not_imp_not]
        using not_imp_not.2 (z a) ha.not_le

instance instDecidableLT : @DecidableRel (Colex α) (· < ·) := fun s t ↦
  decidable_of_iff'
    (∃ k ∈ ofColex t,
      (∀ x ∈ ofColex s ∪ ofColex t, k < x → (x ∈ ofColex s ↔ x ∈ ofColex t)) ∧ k ∉ ofColex s) $
    exists_congr fun a ↦ by
      simp only [mem_union, exists_prop, or_imp, @and_comm (_ ∈ ofColex t), and_assoc]
      exact and_congr_left' $ forall_congr' $ by tauto

instance instLinearOrder : LinearOrder (Colex α) := linearOrderOfSTO (· < ·)

instance instBot : Bot (Colex α) where
  bot := toColex ∅

@[simp] lemma toColex_empty : toColex (∅ : Finset α) = ⊥ := rfl
@[simp] lemma ofColex_bot : ofColex (⊥ : Colex α) = ∅ := rfl

instance instOrderBot : OrderBot (Colex α) where
  bot_le s := by
    induction' s using Finset.Colex.rec with s
    rw [le_def]
    obtain rfl | hs := s.eq_empty_or_nonempty
    · simp
    refine' Or.inr ⟨max' _ hs, _, by simp, max'_mem _ _⟩
    simp only [max'_lt_iff, ofColex_bot, not_mem_empty, ofColex_toColex, false_iff]
    exact fun x hs hx ↦ lt_irrefl _ $ hs _ hx

/-- The colexigraphic order is insensitive to removing elements. -/
lemma toColex_sdiff_le_toColex_sdiff (hus : u ⊆ s) (hut : u ⊆ t) :
    toColex (s \ u) ≤ toColex (t \ u) ↔ toColex s ≤ toColex t := by
  rw [le_iff_le_iff_lt_iff_lt, toColex_sdiff_lt_toColex_sdiff hut hus]

@[simp] lemma toColex_sdiff_le_toColex_sdiff' :
    toColex (s \ t) ≤ toColex (t \ s) ↔ toColex s ≤ toColex t := by
  rw [le_iff_le_iff_lt_iff_lt, toColex_sdiff_lt_toColex_sdiff']

lemma colex_lt_of_ssubset (h : s ⊂ t) : toColex s < toColex t := by
  rw [←toColex_sdiff_lt_toColex_sdiff', sdiff_eq_empty_iff_subset.2 h.1, toColex_empty,
    bot_lt_iff_ne_bot, ←toColex_empty, toColex_ne_toColex]
  simpa using h.not_subset

/-- If `s ⊆ t`, then `s ≤ t` in the colex order. Note the converse does not hold, as `⊆` is not a
linear order. -/
lemma colex_le_of_subset (h : s ⊆ t) : toColex s ≤ toColex t := by
  rw [←toColex_sdiff_le_toColex_sdiff', sdiff_eq_empty_iff_subset.2 h, toColex_empty]; exact bot_le

instance [Fintype α] : BoundedOrder (Colex α) where
    top := toColex univ
    le_top _x := colex_le_of_subset (subset_univ _)

@[simp] lemma toColex_univ [Fintype α] : toColex (univ : Finset α) = ⊤ := rfl
@[simp] lemma ofColex_top [Fintype α] : ofColex (⊤ : Colex α) = univ := rfl

/-- `s < {a}` in colex iff all elements of `s` are strictly less than `a`. -/
lemma toColex_lt_singleton : toColex s < toColex {a} ↔ ∀ x ∈ s, x < a := by
  simp only [toColex_lt_toColex, mem_singleton, ←and_assoc, exists_eq_right, ←not_le (a := a)]
  refine ⟨fun t x hx hax ↦ ?_, fun h ↦ ⟨fun z hz ↦ ?_, by simpa using h a⟩⟩
  · obtain hax | rfl := hax.lt_or_eq
    · exact hax.ne' $ (t.1 hax).1 hx
    · exact t.2 hx
  · exact ⟨fun i ↦ ((h _ i) hz.le).elim, fun i ↦ (hz.ne' i).elim⟩

/-- `{a} ≤ s` in colex iff `r` contains an element greated than or equal to `a`. -/
lemma singleton_le_toColex : (toColex {a} : Colex α) ≤ toColex s ↔ ∃ x ∈ s, a ≤ x := by
  simp only [←not_lt, toColex_lt_singleton, not_forall, exists_prop]

/-- Colex is an extension of the base order. -/
lemma singleton_lt_singleton : (toColex {a} : Colex α) < toColex {b} ↔ a < b := by
  simp [toColex_lt_singleton]

/-- Colex is an extension of the base order. -/
lemma singleton_le_singleton : (toColex {a} : Colex α) ≤ toColex {b} ↔ a ≤ b := by
  rw [le_iff_le_iff_lt_iff_lt, singleton_lt_singleton]

/-- If `s` is before `t` in colex, and everything in `t` is small, then everything in `s` is small.
-/
lemma forall_lt_mono (h₁ : toColex s ≤ toColex t) (h₂ : ∀ x ∈ t, x < a) : ∀ x ∈ s, x < a := by
  obtain rfl | ⟨k, z, -, hk⟩ := toColex_le_toColex.1 h₁
  · assumption
  · refine' fun x hx => lt_of_not_le fun h ↦ h.not_lt $ h₂ x _
    rwa [←z ((h₂ k hk).trans_le h)]

/-- Strictly monotone functions preserve the colex ordering. -/
lemma toColex_image_lt_toColex_image (hf : StrictMono f) :
    toColex (s.image f) < toColex (t.image f) ↔ toColex s < toColex t := by
  simp only [toColex_lt_toColex, not_exists, mem_image, exists_prop, not_and]
  constructor
  · rintro ⟨k, z, q, k', _, rfl⟩
    exact ⟨k', fun x hx => by simpa [hf.injective.eq_iff] using z (hf hx),
      fun t ↦ q _ t rfl, ‹k' ∈ t›⟩
  rintro ⟨k, z, ka, _⟩
  refine' ⟨f k, fun x hx ↦ _, _, k, ‹k ∈ t›, rfl⟩
  · constructor
    all_goals
      rintro ⟨x', hx', rfl⟩
      refine' ⟨x', _, rfl⟩
      first
      | rwa [←z _]
      | rwa [z _]
      rwa [StrictMono.lt_iff_lt hf] at hx
  · simp only [hf.injective, Function.Injective.eq_iff]
    exact fun x hx ↦ ne_of_mem_of_not_mem hx ka

/-- Strictly monotone functions preserve the colex ordering. -/
lemma toColex_image_le_toColex_image (hf : StrictMono f) :
    toColex (s.image f) ≤ toColex (t.image f) ↔ toColex s ≤ toColex t := by
  rw [le_iff_le_iff_lt_iff_lt, toColex_image_lt_toColex_image hf]

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
  simp_rw [←sdiff_eq_empty_iff_subset, ←not_nonempty_iff_eq_empty]
  by_contra' h
  obtain ⟨⟨s, hs⟩, t, ht⟩ := h
  rw [mem_sdiff] at hs ht
  obtain hst | hst | hts := trichotomous_of (α := Colex α) (· < ·) (toColex s) (toColex t)
  · exact hs.2 $ h₂.2 ht.1 ⟨hst, h₁.1 hs.1⟩
  · simp only [toColex.injEq] at hst
    exact ht.2 $ hst ▸ hs.1
  · exact ht.2 $ h₁.2 hs.1 ⟨hts, h₂.1 ht.1⟩

variable [Fintype α]

/-- Gives all sets up to `s` with the same size as it: this is equivalent to
being an initial segment of colex. -/
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
  refine' ⟨_, h𝒜.1 hs, _⟩
  ext t
  rw [mem_initSeg]
  refine' ⟨fun p ↦ _, _⟩
  · rw [h𝒜.1 p, h𝒜.1 hs]
    exact ⟨rfl, le_sup' _ p⟩
  rintro ⟨cards, le⟩
  obtain p | p := le.eq_or_lt
  · rwa [toColex_inj.1 p]
  · exact h𝒜.2 hs ⟨p, cards ▸ h𝒜.1 hs⟩

/-- Being a nonempty initial segment of colex if equivalent to being an `initSeg`. -/
lemma isInitSeg_iff_exists_initSeg :
    IsInitSeg 𝒜 r ∧ 𝒜.Nonempty ↔ ∃ s : Finset α, s.card = r ∧ 𝒜 = initSeg s := by
  refine ⟨fun h𝒜 ↦ h𝒜.1.exists_initSeg h𝒜.2, ?_⟩
  rintro ⟨s, rfl, rfl⟩
  exact ⟨isInitSeg_initSeg, initSeg_nonempty⟩

end LinearOrder
end Colex

open Colex

/-!
### Colex on `ℕ`

The colexicographic order agrees with the order induced by interpreting a set of naturals as a
binary expansion.
-/

section Nat
variable {s t : Finset ℕ}

/-- For finsets of naturals of naturals, the colexicographic order is equivalent to the order
induced by the binary expansion. -/
lemma sum_two_pow_lt_iff_colex_lt : ∑ i in s, 2 ^ i < ∑ i in t, 2 ^ i ↔ toColex s < toColex t := by
  have z : ∀ s t : Finset ℕ, toColex s < toColex t → ∑ i in s, 2 ^ i < ∑ i in t, 2 ^ i := by
    intro s t
    rw [←toColex_sdiff_lt_toColex_sdiff', toColex_lt_toColex]
    rintro ⟨a, ha, has, hat⟩
    rw [←sdiff_union_inter s t]
    conv_rhs => rw [←sdiff_union_inter t s]
    rw [sum_union (disjoint_sdiff_inter _ _), sum_union (disjoint_sdiff_inter _ _), inter_comm,
      add_lt_add_iff_right]
    apply (@Nat.sum_two_pow_lt a (s \ t) _).trans_le
    · apply single_le_sum (fun _ _ ↦ Nat.zero_le _) hat
    intro x hx
    refine' (ne_of_mem_of_not_mem hx has).lt_or_lt.resolve_right $ fun hax ↦ _
    have := (ha hax).1 hx
    rw [mem_sdiff] at this hx
    exact hx.2 this.1
  refine' ⟨fun h ↦ (lt_trichotomy (toColex s) $ toColex t).resolve_right fun h₁ ↦
    h₁.elim _ (not_lt_of_gt h ∘ z _ _), z s t⟩
  rw [toColex_inj]
  rintro rfl
  exact irrefl _ h

/-- For finsets of naturals of naturals, the colexicographic order is equivalent to the order
induced by the binary expansion. -/
lemma sum_two_pow_le_iff_colex_le : ∑ i in s, 2 ^ i ≤ ∑ i in t, 2 ^ i ↔ toColex s ≤ toColex t := by
  rw [le_iff_le_iff_lt_iff_lt, sum_two_pow_lt_iff_colex_lt]

end Nat
end Finset
