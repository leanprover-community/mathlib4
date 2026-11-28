/-
Copyright (c) 2026 Qiaochu Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiaochu Hu
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.ZMod.Basic

/-!
# Restricted sumsets

This file defines the restricted sumset (restricted product, multiplicatively) of two finsets
and proves a universal lower bound on its size together with the classification of the
exceptional sets attaining a strict drop.

The restricted sumset of `s` and `t` is `s ⊛ t = {a * b | a ∈ s, b ∈ t, a ≠ b}`.
For `s = t` this is the set of products of two distinct elements, the "restricted
product set" of additive combinatorics.  It is NOT obtained by deleting the diagonal
from the full product set `s * t`: an element `a * a` may also arise as `b * c` with
`b ≠ c`, and such elements survive in `s ⊛ s`.

Notation variants in the literature for `s ⊛ s` (all denoting the same object) include `2∧A`
(Girard–Griffiths–Hamidoune), `A \hat{+} A` and `A ⊕ A`; this file uses no dedicated notation
and writes `Finset.restrictedProduct` (`Finset.restrictedSum`, additively).

## Main declarations

* `Finset.restrictedProduct`: the definition `{p ∈ s ×ˢ t | p.1 ≠ p.2}.image (·.1 * ·.2)`.
* `Finset.mem_restrictedProduct`, `Finset.mul_mem_restrictedProduct`: membership API.
* `Finset.card_le_card_restrictedProduct_add_one`: **universal bound.**  In any group,
  `#s ≤ #(s ⊛ s) + 1`; equivalently the size drops by at most one.  No commutativity, ambient
  finiteness or nonemptiness hypotheses: the proof fixes `a ∈ s` and uses that `b ↦ a * b` is
  injective on `s.erase a`.
* `Finset.card_restrictedProduct_lt_iff_coset` (`Finset.card_restrictedSum_lt_iff_coset`,
  additively): **exception classification.**  In a finite commutative group
  with `3 ≤ #s`, the strict drop `#(s ⊛ s) < #s` holds if and only if `s` is a translate of a
  finset `S` containing `1`, closed under multiplication, in which every element satisfies
  `x * x = 1` (an "elementary 2-subgroup coset", called a *2-coset* by
  Girard–Griffiths–Hamidoune).  Combined with the universal bound, whenever the drop happens
  it is exactly one: `#(s ⊛ s) = #s - 1`.

## Literature

The exception classification is due to Girard–Griffiths–Hamidoune, *k-Sums in abelian groups*,
arXiv:1110.1961, published as Combin. Probab. Comput. 21 (2012) 582–596, Lemma 2.2, in
slightly greater generality (the ambient abelian group need not be finite); see [girard2012].
Their notation `2∧A` is our `s ⊛ s` and their `2-coset` is our translate of an
involution-closed subgroup-like finset.  The universal bound as stated here (any group, no
commutativity) is an immediate consequence of the injection argument appearing inside their
proof of Lemma 2.2.

## Tags

restricted sumset, restricted product, sumset, additive combinatorics
-/

@[expose] public section

open scoped Finset

namespace Finset

/-! ### The definition and membership -/

section RestrictedProduct

variable {α : Type*} [DecidableEq α] [Mul α] {s t : Finset α} {a x y : α}

/-- The restricted product `s ⊛ t = {a * b | a ∈ s, b ∈ t, a ≠ b}` of two finsets:
the set of products of pairs with distinct components.  For `s = t` this is the set of
products of two distinct elements of `s` (compared as values, not as occurrences).
Additively this is the *restricted sumset* of the literature. -/
@[to_additive Finset.restrictedSum
  /-- The restricted sum `s ⊛ t = {a + b | a ∈ s, b ∈ t, a ≠ b}` of two finsets: the set
  of sums of pairs with distinct components.  For `s = t` this is the set of sums of two
  distinct elements of `s` (compared as values, not as occurrences); this is the
  *restricted sumset* of additive combinatorics. -/
]
def restrictedProduct (s t : Finset α) : Finset α :=
  ((s ×ˢ t).filter fun p : α × α ↦ p.1 ≠ p.2).image fun p ↦ p.1 * p.2

/-- Membership in the restricted product `s ⊛ t`. -/
@[to_additive Finset.mem_restrictedSum]
theorem mem_restrictedProduct :
    a ∈ s.restrictedProduct t ↔ ∃ x ∈ s, ∃ y ∈ t, x ≠ y ∧ x * y = a := by
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    exact ⟨p.1, hp.1.1, p.2, hp.1.2, hp.2, rfl⟩
  · rintro ⟨x, hx, y, hy, hne, rfl⟩
    exact Finset.mem_image.mpr ⟨(x, y), by
      simp only [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hx, hy⟩, hne⟩, rfl⟩

/-- Products of distinct elements lie in the restricted product. -/
@[to_additive Finset.add_mem_restrictedSum]
theorem mul_mem_restrictedProduct (hx : x ∈ s) (hy : y ∈ t) (hxy : x ≠ y) :
    x * y ∈ s.restrictedProduct t :=
  mem_restrictedProduct.mpr ⟨x, hx, y, hy, hxy, rfl⟩

end RestrictedProduct

/-! ### The universal bound -/

section Group

variable {α : Type*} [Group α] [DecidableEq α] {s : Finset α} {a : α}

/-- **Universal lower bound for restricted products (sharp).**  Every finset `s` of any group
(no commutativity, no ambient finiteness, empty allowed) satisfies `#s ≤ #(s ⊛ s) + 1`, i.e.
the restricted product drops in size by at most one.

The proof fixes `a ∈ s` and observes that `b ↦ a * b` is injective on `s.erase a` with image
inside `s ⊛ s`.  This is the injection argument from the proof of Lemma 2.2 of
Girard–Griffiths–Hamidoune [girard2012].

Sharpness: in finite commutative groups the drop is exactly one precisely for the cosets
classified by `Finset.card_restrictedProduct_lt_iff_coset`; for `#s = 2` the drop is one for
every two-element finset. -/
@[to_additive Finset.card_le_card_restrictedSum_add_one
  /-- **Universal lower bound for restricted sums (sharp).**  Every finset `s` of any additive
  group (no commutativity, no ambient finiteness, empty allowed) satisfies
  `#s ≤ #(s ⊛ s) + 1`, i.e. the restricted sumset drops in size by at most one.

  The proof fixes `a ∈ s` and observes that `b ↦ a + b` is injective on `s.erase a` with
  image inside `s ⊛ s`.  This is the injection argument from the proof of Lemma 2.2 of
  Girard–Griffiths–Hamidoune [girard2012].

  Sharpness: in finite abelian groups the drop is exactly one precisely for the cosets
  classified by `Finset.card_restrictedSum_lt_iff_coset`; for `#s = 2` the drop is one
  for every two-element finset. -/
]
theorem card_le_card_restrictedProduct_add_one (s : Finset α) :
    #s ≤ #(s.restrictedProduct s) + 1 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · obtain ⟨a, ha⟩ := hs
    have hinj : Function.Injective fun b : α ↦ a * b := fun _ _ h ↦ mul_left_cancel h
    have hsub : (s.erase a).image (fun b ↦ a * b) ⊆ s.restrictedProduct s := by
      intro z hz
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨-, hbA⟩ := Finset.mem_erase.mp hb
      exact mul_mem_restrictedProduct ha hbA (Ne.symm (Finset.mem_erase.mp hb).1)
    have h1 : #((s.erase a).image fun b ↦ a * b) = #(s.erase a) :=
      Finset.card_image_of_injective _ hinj
    have h2 : #((s.erase a).image fun b ↦ a * b) ≤ #(s.restrictedProduct s) :=
      Finset.card_le_card hsub
    have h3 : #(s.erase a) = #s - 1 := Finset.card_erase_of_mem ha
    omega

/-- When the strict drop happens, it is exactly one.  This is immediate from
`Finset.card_le_card_restrictedProduct_add_one`. -/
@[to_additive Finset.card_restrictedSum_eq_sub_one]
theorem card_restrictedProduct_eq_sub_one (hlt : #(s.restrictedProduct s) < #s) :
    #(s.restrictedProduct s) = #s - 1 := by
  have := card_le_card_restrictedProduct_add_one s
  omega

end Group

/-! ### Translation invariance and coset computations -/

section CommGroup

variable {G : Type*} [CommGroup G] [DecidableEq G] {s : Finset G}

/-- Translation invariance: simultaneously translating every element of `s` (on the right)
does not change the size of the restricted product.  Used to reduce the classification to the
case `1 ∈ s`. -/
@[to_additive Finset.card_restrictedSum_image_add_right
  /-- Translation invariance: simultaneously translating every element of `s` (on the right)
  does not change the size of the restricted sumset.  Used to reduce the classification to
  the case `0 ∈ s`. -/
]
theorem card_restrictedProduct_image_mul_right (t : G) (s : Finset G) :
    #((s.image fun x ↦ x * t).restrictedProduct (s.image fun x ↦ x * t))
      = #(s.restrictedProduct s) := by
  have key : (s.image fun x ↦ x * t).restrictedProduct (s.image fun x ↦ x * t)
      = (s.restrictedProduct s).image fun z ↦ z * (t * t) := by
    ext z
    constructor
    · intro hz
      obtain ⟨p, hp, q, hq, hne, rfl⟩ := Finset.mem_restrictedProduct.mp hz
      rw [Finset.mem_image] at hp hq
      obtain ⟨x, hx, rfl⟩ := hp
      obtain ⟨y, hy, rfl⟩ := hq
      refine Finset.mem_image.mpr ⟨x * y, ?_, ?_⟩
      · exact mem_restrictedProduct.mpr
          ⟨x, hx, y, hy, fun hxy ↦ hne (by rw [hxy]), rfl⟩
      · simp only [mul_comm, mul_left_comm]
    · intro hz
      rw [Finset.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨x, hx, y, hy, hxy, rfl⟩ := Finset.mem_restrictedProduct.mp hw
      exact mem_restrictedProduct.mpr ⟨x * t, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
        y * t, Finset.mem_image.mpr ⟨y, hy, rfl⟩,
        fun h ↦ hxy (mul_right_cancel h), by simp only [mul_comm, mul_left_comm]⟩
  have hinj : Function.Injective fun z : G ↦ z * (t * t) := fun _ _ h ↦ mul_right_cancel h
  rw [key]
  exact Finset.card_image_of_injective _ hinj

/-- An involution-closed subgroup-like finset `S` (contains `1`, multiplication-closed, every
element satisfies `x * x = 1`) has restricted product exactly `S.erase 1`. -/
@[to_additive Finset.restrictedSum_eq_erase_zero
  /-- A negation-closed subgroup-like finset `S` (contains `0`, addition-closed, every
  element satisfies `x + x = 0`) has restricted sumset exactly `S.erase 0`. -/
]
theorem restrictedProduct_eq_erase_one (S : Finset G) (h1 : (1 : G) ∈ S)
    (hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) (hsq : ∀ x ∈ S, x * x = 1) :
    S.restrictedProduct S = S.erase 1 := by
  ext z
  constructor
  · intro hz
    rcases Finset.mem_restrictedProduct.mp hz with ⟨a, ha, b, hb, hne, rfl⟩
    refine Finset.mem_erase.mpr ⟨?_, hmul a ha b hb⟩
    intro hc
    exact hne (mul_right_cancel (hc.trans (hsq b hb).symm))
  · intro hz
    obtain ⟨hz1, hzS⟩ := Finset.mem_erase.mp hz
    have hmem : (1 : G) * z ∈ S.restrictedProduct S :=
      mul_mem_restrictedProduct h1 hzS (Ne.symm hz1)
    rwa [one_mul] at hmem

/-- The coset computation: the restricted product of a translate `a₀ * S` of an
involution-closed subgroup-like finset is the translate (by `a₀ * a₀`) of `S.erase 1`. -/
@[to_additive Finset.restrictedSum_coset
  /-- The coset computation: the restricted sumset of a translate `a₀ + S` of a
  negation-closed subgroup-like finset is the translate (by `a₀ + a₀`) of `S.erase 0`. -/
]
theorem restrictedProduct_coset {S : Finset G} (h1 : (1 : G) ∈ S)
    (hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) (hsq : ∀ x ∈ S, x * x = 1) (a₀ : G) :
    (S.image fun h ↦ a₀ * h).restrictedProduct (S.image fun h ↦ a₀ * h)
      = (S.erase 1).image fun h ↦ a₀ * a₀ * h := by
  ext z
  constructor
  · intro hz
    rcases Finset.mem_restrictedProduct.mp hz with ⟨p, hp, q, hq, hne, rfl⟩
    rw [Finset.mem_image] at hp hq
    obtain ⟨x, hxS, rfl⟩ := hp
    obtain ⟨y, hyS, rfl⟩ := hq
    have hxy : x ≠ y := fun hc ↦ hne (by rw [hc])
    have hsumS : x * y ∈ S := hmul x hxS y hyS
    have hsum1 : x * y ≠ 1 := fun hc ↦
      hxy (mul_right_cancel (hc.trans (hsq y hyS).symm))
    refine Finset.mem_image.mpr ⟨x * y, Finset.mem_erase.mpr ⟨hsum1, hsumS⟩, ?_⟩
    show a₀ * a₀ * (x * y) = a₀ * x * (a₀ * y)
    simp only [mul_comm, mul_left_comm]
  · intro hz
    rw [Finset.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨hw1, hwS⟩ := Finset.mem_erase.mp hw
    have hne : a₀ * 1 ≠ a₀ * w := fun hc ↦ hw1 (mul_left_cancel hc).symm
    have hmem : a₀ * 1 * (a₀ * w) ∈ (S.image fun h ↦ a₀ * h).restrictedProduct
        (S.image fun h ↦ a₀ * h) :=
      mul_mem_restrictedProduct (Finset.mem_image.mpr ⟨(1 : G), h1, rfl⟩)
        (Finset.mem_image.mpr ⟨w, hwS, rfl⟩) hne
    have heq : a₀ * 1 * (a₀ * w) = a₀ * a₀ * w := by
      simp only [mul_comm, mul_left_comm, mul_one]
    rwa [heq] at hmem

end CommGroup

/-! ### Proof machinery for the classification

These declarations carry out the forward direction of `Finset.card_lt_iff_coset` through the
right stabilizer `mulRightStabilizer s = {g | s.image (· * g) = s}`: under the drop hypothesis
(with `1 ∈ s` and `3 ≤ #s`) the finset `s` equals its right stabilizer, which forces every
element to be an involution.
-/

section Machinery

variable {G : Type*} [CommGroup G] [DecidableEq G] {s : Finset G}

/-- With the drop hypothesis, every restricted product `z` satisfies `z / a ∈ s` for every
`a ∈ s`: the fixed-left-factor injection is forced to be a bijection onto the restricted
product. -/
@[to_additive
  /-- With the drop hypothesis, every restricted sum `z` satisfies `z - a ∈ s` for every
  `a ∈ s`: the fixed-addend injection is forced to be a bijection onto the restricted
  sumset. -/
]
theorem div_mem_of_mem (hlt : #(s.restrictedProduct s) < #s)
    {z : G} (hz : z ∈ s.restrictedProduct s) {a : G} (ha : a ∈ s) : z / a ∈ s := by
  have hcard := card_restrictedProduct_eq_sub_one hlt
  set I := (s.erase a).image fun b ↦ a * b with hIdef
  have hIsub : I ⊆ s.restrictedProduct s := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
    exact mul_mem_restrictedProduct ha (Finset.mem_erase.mp hb).2
      (Ne.symm (Finset.mem_erase.mp hb).1)
  have hIcard : #I = #s - 1 := by
    rw [hIdef, Finset.card_image_of_injective _ (fun _ _ h ↦ mul_left_cancel h),
      Finset.card_erase_of_mem ha]
  have hIeq : I = s.restrictedProduct s :=
    Finset.eq_of_subset_of_card_le hIsub (by rw [hIcard, hcard])
  obtain ⟨b, hb, hsb⟩ := Finset.mem_image.mp (hIeq ▸ hz)
  have hsb' : z / a = b := by rw [← hsb, mul_div_cancel_left]
  rw [hsb']
  exact (Finset.mem_erase.mp hb).2

/-- With `1 ∈ s`, every restricted product lies in `s`. -/
@[to_additive Finset.mem_of_restrictedSum_mem
  /-- With `0 ∈ s`, every restricted sum lies in `s`. -/
]
theorem mem_of_restrictedProduct_mem (h1 : (1 : G) ∈ s)
    (hlt : #(s.restrictedProduct s) < #s)
    {z : G} (hz : z ∈ s.restrictedProduct s) : z ∈ s := by
  have := div_mem_of_mem hlt hz h1
  rwa [div_one] at this

/-- Under the drop hypothesis, `1` is never a restricted product. -/
@[to_additive Finset.zero_notMem_restrictedSum
  /-- Under the drop hypothesis, `0` is never a restricted sum. -/
]
theorem one_notMem_restrictedProduct (h1 : (1 : G) ∈ s)
    (hlt : #(s.restrictedProduct s) < #s) : (1 : G) ∉ s.restrictedProduct s := by
  intro hone
  have hcard := card_restrictedProduct_eq_sub_one hlt
  have hsub : s.erase 1 ⊆ s.restrictedProduct s := by
    intro x hx
    have h1x : (1 : G) * x ∈ s.restrictedProduct s :=
      mul_mem_restrictedProduct h1 (Finset.mem_erase.mp hx).2
        (Ne.symm (Finset.mem_erase.mp hx).1)
    rwa [one_mul] at h1x
  have hAsub : s ⊆ s.restrictedProduct s := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]; exact hone
    · exact hsub (Finset.mem_erase.mpr ⟨hx1, hx⟩)
  have hpos : 0 < #s := Finset.card_pos.mpr ⟨1, h1⟩
  have := Finset.card_le_card hAsub
  omega

/-- Quotient bijection: under the drop hypothesis, division by a restricted product `z` maps
`s` onto itself. -/
@[to_additive /-- Difference bijection: under the drop hypothesis, subtracting a restricted
sum `z` maps `s` onto itself. -/
]
theorem image_div_right_eq (hlt : #(s.restrictedProduct s) < #s)
    {z : G} (hz : z ∈ s.restrictedProduct s) : s.image (fun a ↦ z / a) = s := by
  have hinj : Function.Injective fun a : G ↦ z / a := div_right_injective
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact div_mem_of_mem hlt hz ha
  · rw [Finset.card_image_of_injective _ hinj]

section Stabilizer

variable [Fintype G]

/-- The right stabilizer of `s`, as a finset. -/
@[to_additive /-- The right stabilizer of `s`, as a finset. -/
]
def mulRightStabilizer (s : Finset G) : Finset G :=
  Finset.univ.filter fun g ↦ s.image (fun a ↦ a * g) = s

/-- Membership in the right stabilizer. -/
@[to_additive]
theorem mem_mulRightStabilizer {g : G} :
    g ∈ mulRightStabilizer s ↔ s.image (fun a ↦ a * g) = s := by
  simp [mulRightStabilizer, Finset.mem_filter, Finset.mem_univ]

/-- The identity stabilizes every finset. -/
@[to_additive]
theorem one_mem_mulRightStabilizer (s : Finset G) : (1 : G) ∈ mulRightStabilizer s := by
  rw [mem_mulRightStabilizer]
  have h : s.image (fun a ↦ a * 1) = s.image fun a ↦ a :=
    Finset.image_congr fun a _ ↦ mul_one a
  have h2 : s.image (fun a ↦ a) = s := Finset.image_id
  rw [h, h2]

/-- Quotients of restricted products stabilize `s`. -/
@[to_additive /-- Differences of restricted sums stabilize `s`. -/
]
theorem div_mem_mulRightStabilizer
    (hlt : #(s.restrictedProduct s) < #s)
    {z z' : G} (hz : z ∈ s.restrictedProduct s)
    (hz' : z' ∈ s.restrictedProduct s) : z / z' ∈ mulRightStabilizer s := by
  rw [mem_mulRightStabilizer]
  have hA : s.image (fun a ↦ a * (z / z')) = s.image (fun a ↦ z / (z' / a)) :=
    Finset.image_congr fun a _ ↦ by
      simp only [div_eq_mul_inv, mul_inv, inv_inv, mul_left_comm, mul_comm]
  have hB : s.image (fun a ↦ z / (z' / a))
      = (s.image fun a ↦ z' / a).image fun b ↦ z / b :=
    Finset.image_image.symm
  rw [hA, hB, image_div_right_eq hlt hz', image_div_right_eq hlt hz]

/-- The right stabilizer is closed under pointwise division. -/
@[to_additive]
theorem mulRightStabilizer_div_closed {g₁ g₂ : G} (hg₁ : g₁ ∈ mulRightStabilizer s)
    (hg₂ : g₂ ∈ mulRightStabilizer s) : g₁ / g₂ ∈ mulRightStabilizer s := by
  rw [mem_mulRightStabilizer]
  have hneg : s.image (fun a ↦ a / g₂) = s := by
    have hbij : ∀ x ∈ s, ∃ a ∈ s, a * g₂ = x := by
      intro x hx
      have hmem : x ∈ s.image fun a ↦ a * g₂ := by
        rw [mem_mulRightStabilizer.mp hg₂]; exact hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hmem
      exact ⟨a, ha, rfl⟩
    have hinj : Function.Injective fun a : G ↦ a / g₂ := by
      intro a b h
      simp only [div_eq_mul_inv] at h
      exact mul_right_cancel h
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, hbx⟩ := hbij a ha
      have hax : a / g₂ = b := by rw [← hbx, mul_div_cancel_right]
      rw [hax]; exact hb
    · rw [Finset.card_image_of_injective _ hinj]
  have hA : s.image (fun a ↦ a * (g₁ / g₂)) = s.image fun a ↦ a * g₁ / g₂ :=
    Finset.image_congr fun _ _ ↦ (mul_div_assoc _ _ _).symm
  have hB : s.image (fun a ↦ a * g₁ / g₂)
      = (s.image fun a ↦ a * g₁).image fun b ↦ b / g₂ := by
    rw [Finset.image_image]; rfl
  rw [hA, hB, mem_mulRightStabilizer.mp hg₁, hneg]

/-- The right stabilizer of a finset containing `1` is contained in it. -/
@[to_additive]
theorem mulRightStabilizer_subset (h1 : (1 : G) ∈ s) : mulRightStabilizer s ⊆ s := by
  intro g hg
  have h1g : (1 : G) * g ∈ s.image fun a ↦ a * g :=
    Finset.mem_image.mpr ⟨1, h1, rfl⟩
  rw [mem_mulRightStabilizer.mp hg] at h1g
  simpa using h1g

/-- Under the drop hypothesis (with `1 ∈ s`, `3 ≤ #s`), `s` equals its own right
stabilizer. -/
@[to_additive /-- Under the drop hypothesis (with `0 ∈ s`, `3 ≤ #s`), `s` equals its own
right stabilizer. -/
]
theorem eq_mulRightStabilizer_of_lt (h1 : (1 : G) ∈ s) (h3 : 3 ≤ #s)
    (hlt : #(s.restrictedProduct s) < #s) : s = mulRightStabilizer s := by
  have hcard := card_restrictedProduct_eq_sub_one hlt
  obtain ⟨z₀, hz₀⟩ : (s.restrictedProduct s).Nonempty := by
    have h2 : 0 < #(s.restrictedProduct s) := by omega
    exact Finset.card_pos.mp h2
  have hge : #s - 1 ≤ #(mulRightStabilizer s) := by
    have him : (s.restrictedProduct s).image (fun z ↦ z / z₀) ⊆ mulRightStabilizer s := by
      intro g hg
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hg
      exact div_mem_mulRightStabilizer hlt hz hz₀
    have hinj : Function.Injective fun z : G ↦ z / z₀ := div_left_injective
    have hle := Finset.card_le_card him
    rw [Finset.card_image_of_injective _ hinj] at hle
    omega
  rcases Nat.lt_or_ge #(mulRightStabilizer s) #s with hlt' | hle'
  · exfalso
    obtain ⟨a, ha, hna⟩ : ∃ a ∈ s, a ∉ mulRightStabilizer s := by
      by_contra hc
      push Not at hc
      have hsub : s ⊆ mulRightStabilizer s := fun x hx ↦ hc x hx
      have := Finset.card_le_card hsub
      omega
    have hcos : (mulRightStabilizer s).image (fun h ↦ a * h) ⊆ s := by
      intro x hx
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
      have hmem : a * h ∈ s.image fun b ↦ b * h :=
        Finset.mem_image.mpr ⟨a, ha, rfl⟩
      rwa [mem_mulRightStabilizer.mp hh] at hmem
    have hdisj : Disjoint ((mulRightStabilizer s).image fun h ↦ a * h)
        (mulRightStabilizer s) := by
      rw [Finset.disjoint_left]
      intro x hx hxsym
      obtain ⟨h₂, h₂s, hxh₂⟩ := Finset.mem_image.mp hx
      apply hna
      have hax : a = x / h₂ := by rw [← hxh₂, mul_div_cancel_right]
      rw [hax]
      exact mulRightStabilizer_div_closed hxsym h₂s
    have hcardcos : #((mulRightStabilizer s).image fun h ↦ a * h)
        = #(mulRightStabilizer s) :=
      Finset.card_image_of_injective _ (fun (_ _ : G) h ↦ mul_left_cancel h)
    have hun : (mulRightStabilizer s).image (fun h ↦ a * h) ∪ mulRightStabilizer s ⊆ s := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact hcos h
      · exact mulRightStabilizer_subset h1 h
    have h2 := Finset.card_le_card hun
    rw [Finset.card_union_of_disjoint hdisj, hcardcos] at h2
    omega
  · exact (Finset.eq_of_subset_of_card_le (mulRightStabilizer_subset h1)
      (by omega)).symm

/-- A finset equal to its right stabilizer, with `1` a member and no restricted product equal
to `1`, is pointwise involutive. -/
@[to_additive /-- A finset equal to its right stabilizer, with `0` a member and no restricted
sum equal to `0`, is pointwise 2-torsion. -/
]
theorem sq_eq_one_of_lt (h1 : (1 : G) ∈ s) (hlt : #(s.restrictedProduct s) < #s)
    (heq : s = mulRightStabilizer s) : ∀ x ∈ s, x * x = 1 := by
  intro x hx
  by_contra hxx
  have hinv : x⁻¹ ∈ s := by
    have h0x : (1 : G) / x ∈ mulRightStabilizer s :=
      mulRightStabilizer_div_closed (one_mem_mulRightStabilizer s) (heq ▸ hx)
    rw [heq]
    simpa using h0x
  have hne : x ≠ x⁻¹ := by
    intro h
    apply hxx
    have h2 : x * x = 1 := by
      nth_rewrite 2 [h]
      rw [mul_inv_cancel]
    exact h2
  have h1mem : (1 : G) ∈ s.restrictedProduct s := by
    have := mul_mem_restrictedProduct hx hinv hne
    rwa [mul_inv_cancel] at this
  exact one_notMem_restrictedProduct h1 hlt h1mem

end Stabilizer

end Machinery

/-! ### The exception classification -/

section Classification

variable {G : Type*} [CommGroup G] [DecidableEq G] [Finite G] {s : Finset G}

/-- **Exception classification for restricted products.**  In a finite commutative group, for
a finset `s` with `3 ≤ #s`:

`#(s ⊛ s) < #s` if and only if `s` is a translate `a₀ * S` of a finset `S` containing `1`,
closed under multiplication, in which every element satisfies `x * x = 1` — an
"elementary 2-subgroup coset" (a *2-coset* in the terminology of
Girard–Griffiths–Hamidoune [girard2012], whose Lemma 2.2 this is, stated there for additive
sets in abelian groups not necessarily finite).

Combined with `Finset.card_le_card_restrictedProduct_add_one`, whenever the strict drop
happens it is exactly one: `#(s ⊛ s) = #s - 1`.

The hypothesis `3 ≤ #s` is necessary: for `#s = 2` one always has `#(s ⊛ s) = 1 < 2` but a
two-element finset need not be such a coset (e.g. `{0, 1} ⊆ ZMod 5`). -/
@[to_additive Finset.card_restrictedSum_lt_iff_coset
  /-- **Exception classification for restricted sumsets.**  In a finite abelian group, for
  a finset `s` with `3 ≤ #s`:

  `#(s ⊛ s) < #s` if and only if `s` is a translate `a₀ + S` of a finset `S` containing `0`,
  closed under addition, in which every element satisfies `x + x = 0` — an
  "elementary 2-subgroup coset" (a *2-coset* in the terminology of
  Girard–Griffiths–Hamidoune [girard2012], whose Lemma 2.2 this is, stated there for additive
  sets in abelian groups not necessarily finite).

  Combined with `Finset.card_le_card_restrictedSum_add_one`, whenever the strict drop
  happens it is exactly one: `#(s ⊛ s) = #s - 1`.

  The hypothesis `3 ≤ #s` is necessary: for `#s = 2` one always has `#(s ⊛ s) = 1 < 2` but a
  two-element finset need not be such a coset (e.g. `{0, 1} ⊆ ZMod 5`). -/
]
theorem card_restrictedProduct_lt_iff_coset {s : Finset G} (h3 : 3 ≤ #s) :
    #(s.restrictedProduct s) < #s ↔
      ∃ (a₀ : G) (S : Finset G), (1 : G) ∈ S ∧
        (∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) ∧
        (∀ x ∈ S, x * x = 1) ∧
        s = S.image fun h ↦ a₀ * h := by
  constructor
  · intro hlt
    have : Fintype G := Fintype.ofFinite G
    obtain ⟨a₀, ha₀⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
    set S := s.image fun x ↦ x * a₀⁻¹ with hSdef
    have hcardS : #S = #s :=
      Finset.card_image_of_injective _ (fun (_ _ : G) h ↦ mul_right_cancel h)
    have hltS : #(S.restrictedProduct S) < #S := by
      rw [hcardS, card_restrictedProduct_image_mul_right a₀⁻¹ s]
      exact hlt
    have h1S : (1 : G) ∈ S := Finset.mem_image.mpr ⟨a₀, ha₀, by simp⟩
    have h3S : 3 ≤ #S := by rw [hcardS]; exact h3
    have heqS : S = mulRightStabilizer S :=
      eq_mulRightStabilizer_of_lt h1S h3S hltS
    refine ⟨a₀, S, h1S, ?_, sq_eq_one_of_lt h1S hltS heqS, ?_⟩
    · intro x hx y hy
      have hx' : x ∈ mulRightStabilizer S := heqS ▸ hx
      have hny : y⁻¹ ∈ mulRightStabilizer S := by
        have h0y : (1 : G) / y ∈ mulRightStabilizer S :=
          mulRightStabilizer_div_closed (one_mem_mulRightStabilizer S) (heqS ▸ hy)
        simpa using h0y
      have hxy : x / y⁻¹ = x * y := div_inv_eq_mul x y
      have h1c := mulRightStabilizer_div_closed hx' hny
      rw [hxy] at h1c
      exact heqS ▸ h1c
    · ext a
      constructor
      · intro ha
        refine Finset.mem_image.mpr ⟨a * a₀⁻¹, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
        show a₀ * (a * a₀⁻¹) = a
        rw [mul_comm a₀ (a * a₀⁻¹), mul_assoc, inv_mul_cancel, mul_one]
      · intro hi
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
        simpa using ha
  · rintro ⟨a₀, S, h1S, hmul, hsq, hSeq⟩
    rw [hSeq, restrictedProduct_coset h1S hmul hsq a₀]
    have hcardS : #(S.image fun h ↦ a₀ * h) = #S :=
      Finset.card_image_of_injective _ (fun (_ _ : G) h ↦ mul_left_cancel h)
    have hcarde : #((S.erase 1).image fun h ↦ a₀ * a₀ * h) = #S - 1 := by
      rw [Finset.card_image_of_injective _ (fun (_ _ : G) h ↦ mul_left_cancel h),
        Finset.card_erase_of_mem h1S]
    rw [hSeq] at h3
    omega

/-- Kernel check of the classification on the canonical example: in `ZMod 2 × ZMod 2` the
whole group is an elementary 2-subgroup, so its restricted sumset has size `4 - 1 = 3`,
attaining the universal bound with equality. -/
example : #((Finset.univ : Finset (ZMod 2 × ZMod 2)).restrictedSum
    (Finset.univ : Finset (ZMod 2 × ZMod 2))) = 3 := by
  decide

end Classification

end Finset
