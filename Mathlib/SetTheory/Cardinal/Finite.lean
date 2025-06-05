/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Data.Finite.Prod
import Mathlib.Data.ULift
import Mathlib.Data.ZMod.Defs
import Mathlib.SetTheory.Cardinal.ToNat
import Mathlib.SetTheory.Cardinal.ENat

/-!
# Finite Cardinality Functions

## Main Definitions

* `Nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `Nat.card α = 0`.
* `ENat.card α` is the cardinality of `α` as an  extended natural number.
  If `α` is infinite, `ENat.card α = ⊤`.
* `PartENat.card α` is the cardinality of `α` as an extended natural number
  (using the legacy definition `PartENat := Part ℕ`). If `α` is infinite, `PartENat.card α = ⊤`.
-/

assert_not_exists Field

open Cardinal Function

noncomputable section

variable {α β : Type*}

universe u v

namespace Nat

/-- `Nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `Nat.card α = 0`. -/
protected def card (α : Type*) : ℕ :=
  toNat (mk α)

@[simp]
theorem card_eq_fintype_card [Fintype α] : Nat.card α = Fintype.card α :=
  mk_toNat_eq_card

/-- Because this theorem takes `Fintype α` as a non-instance argument, it can be used in particular
when `Fintype.card` ends up with different instance than the one found by inference -/
theorem _root_.Fintype.card_eq_nat_card {_ : Fintype α} : Fintype.card α = Nat.card α :=
  mk_toNat_eq_card.symm

lemma card_eq_finsetCard (s : Finset α) : Nat.card s = s.card := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe]

lemma card_eq_card_toFinset (s : Set α) [Fintype s] : Nat.card s = s.toFinset.card := by
  simp only [← Nat.card_eq_finsetCard, s.mem_toFinset]

lemma card_eq_card_finite_toFinset {s : Set α} (hs : s.Finite) : Nat.card s = hs.toFinset.card := by
  simp only [← Nat.card_eq_finsetCard, hs.mem_toFinset]

@[simp] theorem card_of_isEmpty [IsEmpty α] : Nat.card α = 0 := by simp [Nat.card]

@[simp] lemma card_eq_zero_of_infinite [Infinite α] : Nat.card α = 0 := mk_toNat_of_infinite

lemma cast_card [Finite α] : (Nat.card α : Cardinal) = Cardinal.mk α := by
  rw [Nat.card, Cardinal.cast_toNat_of_lt_aleph0]
  exact Cardinal.lt_aleph0_of_finite _

lemma _root_.Set.Infinite.card_eq_zero {s : Set α} (hs : s.Infinite) : Nat.card s = 0 :=
  @card_eq_zero_of_infinite _ hs.to_subtype

lemma card_eq_zero : Nat.card α = 0 ↔ IsEmpty α ∨ Infinite α := by
  simp [Nat.card, mk_eq_zero_iff, aleph0_le_mk_iff]

lemma card_ne_zero : Nat.card α ≠ 0 ↔ Nonempty α ∧ Finite α := by simp [card_eq_zero, not_or]

lemma card_pos_iff : 0 < Nat.card α ↔ Nonempty α ∧ Finite α := by
  simp [Nat.card, mk_eq_zero_iff, mk_lt_aleph0_iff]

@[simp] lemma card_pos [Nonempty α] [Finite α] : 0 < Nat.card α := card_pos_iff.2 ⟨‹_›, ‹_›⟩

theorem finite_of_card_ne_zero (h : Nat.card α ≠ 0) : Finite α := (card_ne_zero.1 h).2

theorem card_congr (f : α ≃ β) : Nat.card α = Nat.card β :=
  Cardinal.toNat_congr f

lemma card_le_card_of_injective {α : Type u} {β : Type v} [Finite β] (f : α → β)
    (hf : Injective f) : Nat.card α ≤ Nat.card β := by
  simpa using toNat_le_toNat (lift_mk_le_lift_mk_of_injective hf) (by simp [lt_aleph0_of_finite])

lemma card_le_card_of_surjective {α : Type u} {β : Type v} [Finite α] (f : α → β)
    (hf : Surjective f) : Nat.card β ≤ Nat.card α := by
  have : lift.{u} #β ≤ lift.{v} #α := mk_le_of_surjective (ULift.map_surjective.2 hf)
  simpa using toNat_le_toNat this (by simp [lt_aleph0_of_finite])

theorem card_eq_of_bijective (f : α → β) (hf : Function.Bijective f) : Nat.card α = Nat.card β :=
  card_congr (Equiv.ofBijective f hf)

protected theorem bijective_iff_injective_and_card [Finite β] (f : α → β) :
    Bijective f ↔ Injective f ∧ Nat.card α = Nat.card β := by
  rw [Bijective, and_congr_right_iff]
  intro h
  have := Fintype.ofFinite β
  have := Fintype.ofInjective f h
  revert h
  rw [← and_congr_right_iff, ← Bijective,
    card_eq_fintype_card, card_eq_fintype_card, Fintype.bijective_iff_injective_and_card]

protected theorem bijective_iff_surjective_and_card [Finite α] (f : α → β) :
    Bijective f ↔ Surjective f ∧ Nat.card α = Nat.card β := by
  classical
  rw [_root_.and_comm, Bijective, and_congr_left_iff]
  intro h
  have := Fintype.ofFinite α
  have := Fintype.ofSurjective f h
  revert h
  rw [← and_congr_left_iff, ← Bijective, ← and_comm,
    card_eq_fintype_card, card_eq_fintype_card, Fintype.bijective_iff_surjective_and_card]

theorem _root_.Function.Injective.bijective_of_nat_card_le [Finite β] {f : α → β}
    (inj : Injective f) (hc : Nat.card β ≤ Nat.card α) : Bijective f :=
  (Nat.bijective_iff_injective_and_card f).mpr
    ⟨inj, hc.antisymm (card_le_card_of_injective f inj) |>.symm⟩

theorem _root_.Function.Surjective.bijective_of_nat_card_le [Finite α] {f : α → β}
    (surj : Surjective f) (hc : Nat.card α ≤ Nat.card β) : Bijective f :=
  (Nat.bijective_iff_surjective_and_card f).mpr
    ⟨surj, hc.antisymm (card_le_card_of_surjective f surj)⟩

theorem card_eq_of_equiv_fin {α : Type*} {n : ℕ} (f : α ≃ Fin n) : Nat.card α = n := by
  simpa only [card_eq_fintype_card, Fintype.card_fin] using card_congr f

section Set
open Set
variable {s t : Set α}

lemma card_mono (ht : t.Finite) (h : s ⊆ t) : Nat.card s ≤ Nat.card t :=
  toNat_le_toNat (mk_le_mk_of_subset h) ht.lt_aleph0

lemma card_image_le {f : α → β} (hs : s.Finite) : Nat.card (f '' s) ≤ Nat.card s :=
  have := hs.to_subtype; card_le_card_of_surjective (imageFactorization f s) surjective_onto_image

lemma card_image_of_injOn {f : α → β} (hf : s.InjOn f) : Nat.card (f '' s) = Nat.card s := by
  classical
  obtain hs | hs := s.finite_or_infinite
  · have := hs.fintype
    have := fintypeImage s f
    simp_rw [Nat.card_eq_fintype_card, Set.card_image_of_inj_on hf]
  · have := hs.to_subtype
    have := (hs.image hf).to_subtype
    simp [Nat.card_eq_zero_of_infinite]

lemma card_image_of_injective {f : α → β} (hf : Injective f) (s : Set α) :
    Nat.card (f '' s) = Nat.card s := card_image_of_injOn hf.injOn

lemma card_image_equiv (e : α ≃ β) : Nat.card (e '' s) = Nat.card s :=
    Nat.card_congr (e.image s).symm

lemma card_preimage_of_injOn {f : α → β} {s : Set β} (hf : (f ⁻¹' s).InjOn f) (hsf : s ⊆ range f) :
    Nat.card (f ⁻¹' s) = Nat.card s := by
  rw [← Nat.card_image_of_injOn hf, image_preimage_eq_iff.2 hsf]

lemma card_preimage_of_injective {f : α → β} {s : Set β} (hf : Injective f) (hsf : s ⊆ range f) :
    Nat.card (f ⁻¹' s) = Nat.card s := card_preimage_of_injOn hf.injOn hsf

@[simp] lemma card_univ : Nat.card (univ : Set α) = Nat.card α :=
  card_congr (Equiv.Set.univ α)

lemma card_range_of_injective {f : α → β} (hf : Injective f) :
    Nat.card (range f) = Nat.card α := by
  rw [← Nat.card_preimage_of_injective hf le_rfl]
  simp

end Set

/-- If the cardinality is positive, that means it is a finite type, so there is
an equivalence between `α` and `Fin (Nat.card α)`. See also `Finite.equivFin`. -/
def equivFinOfCardPos {α : Type*} (h : Nat.card α ≠ 0) : α ≃ Fin (Nat.card α) := by
  cases fintypeOrInfinite α
  · simpa only [card_eq_fintype_card] using Fintype.equivFin α
  · simp only [card_eq_zero_of_infinite, ne_eq, not_true_eq_false] at h

theorem card_of_subsingleton (a : α) [Subsingleton α] : Nat.card α = 1 := by
  letI := Fintype.ofSubsingleton a
  rw [card_eq_fintype_card, Fintype.card_ofSubsingleton a]

theorem card_eq_one_iff_unique : Nat.card α = 1 ↔ Subsingleton α ∧ Nonempty α :=
  Cardinal.toNat_eq_one_iff_unique

@[simp]
theorem card_unique [Nonempty α] [Subsingleton α] : Nat.card α = 1 := by
  simp [card_eq_one_iff_unique, *]

theorem card_eq_one_iff_exists : Nat.card α = 1 ↔ ∃ x : α, ∀ y : α, y = x := by
  rw [card_eq_one_iff_unique]
  exact ⟨fun ⟨s, ⟨a⟩⟩ ↦ ⟨a, fun x ↦ s.elim x a⟩, fun ⟨x, h⟩ ↦ ⟨subsingleton_of_forall_eq x h, ⟨x⟩⟩⟩

theorem card_eq_two_iff : Nat.card α = 2 ↔ ∃ x y : α, x ≠ y ∧ {x, y} = @Set.univ α :=
  toNat_eq_ofNat.trans mk_eq_two_iff

theorem card_eq_two_iff' (x : α) : Nat.card α = 2 ↔ ∃! y, y ≠ x :=
  toNat_eq_ofNat.trans (mk_eq_two_iff' x)

@[simp]
theorem card_subtype_true : Nat.card {_a : α // True} = Nat.card α :=
  card_congr <| Equiv.subtypeUnivEquiv fun _ => trivial

@[simp]
theorem card_sum [Finite α] [Finite β] : Nat.card (α ⊕ β) = Nat.card α + Nat.card β := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_sum]

@[simp]
theorem card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α * Nat.card β := by
  simp only [Nat.card, mk_prod, toNat_mul, toNat_lift]

@[simp]
theorem card_ulift (α : Type*) : Nat.card (ULift α) = Nat.card α :=
  card_congr Equiv.ulift

@[simp]
theorem card_plift (α : Type*) : Nat.card (PLift α) = Nat.card α :=
  card_congr Equiv.plift

theorem card_sigma {β : α → Type*} [Fintype α] [∀ a, Finite (β a)] :
    Nat.card (Sigma β) = ∑ a, Nat.card (β a) := by
  letI _ (a : α) : Fintype (β a) := Fintype.ofFinite (β a)
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_sigma]

theorem card_pi {β : α → Type*} [Fintype α] : Nat.card (∀ a, β a) = ∏ a, Nat.card (β a) := by
  simp_rw [Nat.card, mk_pi, prod_eq_of_fintype, toNat_lift, map_prod]

theorem card_fun [Finite α] : Nat.card (α → β) = Nat.card β ^ Nat.card α := by
  haveI := Fintype.ofFinite α
  rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card]

@[simp]
theorem card_zmod (n : ℕ) : Nat.card (ZMod n) = n := by
  cases n
  · exact @Nat.card_eq_zero_of_infinite _ Int.infinite
  · rw [Nat.card_eq_fintype_card, ZMod.card]

end Nat

namespace Set
variable {s : Set α}

lemma card_singleton_prod (a : α) (t : Set β) : Nat.card ({a} ×ˢ t) = Nat.card t := by
  rw [singleton_prod, Nat.card_image_of_injective (Prod.mk_right_injective a)]

lemma card_prod_singleton (s : Set α) (b : β) : Nat.card (s ×ˢ {b}) = Nat.card s := by
  rw [prod_singleton, Nat.card_image_of_injective (Prod.mk_left_injective b)]

theorem natCard_pos (hs : s.Finite) : 0 < Nat.card s ↔ s.Nonempty := by
  simp [pos_iff_ne_zero, Nat.card_eq_zero, hs.to_subtype, nonempty_iff_ne_empty]

protected alias ⟨_, Nonempty.natCard_pos⟩ := natCard_pos

@[simp] lemma natCard_graphOn (s : Set α) (f : α → β) : Nat.card (s.graphOn f) = Nat.card s := by
  rw [← Nat.card_image_of_injOn fst_injOn_graph, image_fst_graphOn]

end Set


namespace ENat

/-- `ENat.card α` is the cardinality of `α` as an extended natural number.
  If `α` is infinite, `ENat.card α = ⊤`. -/
def card (α : Type*) : ℕ∞ :=
  toENat (mk α)

@[simp]
theorem card_eq_coe_fintype_card [Fintype α] : card α = Fintype.card α := by
  simp [card]

@[simp high]
theorem card_eq_top_of_infinite [Infinite α] : card α = ⊤ := by
  simp only [card, toENat_eq_top, aleph0_le_mk]

@[simp] lemma card_eq_top : card α = ⊤ ↔ Infinite α := by simp [card, aleph0_le_mk_iff]

@[simp] theorem card_lt_top_of_finite [Finite α] : card α < ⊤ := by simp [card]

@[simp]
theorem card_sum (α β : Type*) :
    card (α ⊕ β) = card α + card β := by
  simp only [card, mk_sum, map_add, toENat_lift]

theorem card_congr {α β : Type*} (f : α ≃ β) : card α = card β :=
  Cardinal.toENat_congr f

@[simp] lemma card_ulift (α : Type*) : card (ULift α) = card α := card_congr Equiv.ulift

@[simp] lemma card_plift (α : Type*) : card (PLift α) = card α := card_congr Equiv.plift

theorem card_image_of_injOn {α β : Type*} {f : α → β} {s : Set α} (h : Set.InjOn f s) :
    card (f '' s) = card s :=
  card_congr (Equiv.Set.imageOfInjOn f s h).symm

theorem card_image_of_injective {α β : Type*} (f : α → β) (s : Set α)
    (h : Function.Injective f) : card (f '' s) = card s := card_image_of_injOn h.injOn

@[simp]
theorem _root_.Cardinal.natCast_le_toENat_iff {n : ℕ} {c : Cardinal} :
    ↑n ≤ toENat c ↔ ↑n ≤ c := by
  rw [← toENat_nat n, toENat_le_iff_of_le_aleph0 (le_of_lt (nat_lt_aleph0 n))]

theorem _root_.Cardinal.toENat_le_natCast_iff {c : Cardinal} {n : ℕ} :
    toENat c ≤ n ↔ c ≤ n := by simp

@[simp]
theorem _root_.Cardinal.natCast_eq_toENat_iff {n : ℕ} {c : Cardinal} :
    ↑n = toENat c ↔ ↑n = c := by
  rw [le_antisymm_iff, le_antisymm_iff, Cardinal.toENat_le_natCast_iff,
    Cardinal.natCast_le_toENat_iff]

theorem _root_.Cardinal.toENat_eq_natCast_iff {c : Cardinal} {n : ℕ} :
    Cardinal.toENat c = n ↔ c = n := by simp

@[simp]
theorem _root_.Cardinal.natCast_lt_toENat_iff {n : ℕ} {c : Cardinal} :
    ↑n < toENat c ↔ ↑n < c := by
  simp only [← not_le, Cardinal.toENat_le_natCast_iff]

@[simp]
theorem _root_.Cardinal.toENat_lt_natCast_iff {n : ℕ} {c : Cardinal} :
    toENat c < ↑n ↔ c < ↑n := by
  simp only [← not_le, Cardinal.natCast_le_toENat_iff]

theorem card_eq_zero_iff_empty (α : Type*) : card α = 0 ↔ IsEmpty α := by
  rw [← Cardinal.mk_eq_zero_iff]
  simp [card]

theorem card_ne_zero_iff_nonempty (α : Type*) : card α ≠ 0 ↔ Nonempty α := by
  simp [card_eq_zero_iff_empty]

theorem card_le_one_iff_subsingleton (α : Type*) : card α ≤ 1 ↔ Subsingleton α := by
  rw [← le_one_iff_subsingleton]
  simp [card]

lemma card_eq_one_iff_unique {α : Type*} : card α = 1 ↔ Nonempty (Unique α) := by
  rw [unique_iff_subsingleton_and_nonempty α, le_antisymm_iff, one_le_iff_ne_zero]
  exact and_congr (card_le_one_iff_subsingleton α) (card_ne_zero_iff_nonempty α)

theorem one_lt_card_iff_nontrivial (α : Type*) : 1 < card α ↔ Nontrivial α := by
  rw [← Cardinal.one_lt_iff_nontrivial]
  conv_rhs => rw [← Nat.cast_one]
  rw [← natCast_lt_toENat_iff]
  simp only [ENat.card, Nat.cast_one]

@[simp]
theorem card_prod (α β : Type*) : ENat.card (α × β) = .card α * .card β := by
  simp [ENat.card]




lemma infinite_fun_toInfinite {α β : Type*} [Nonempty α] [Infinite β] : Infinite (α → β) :=
  Infinite.of_injective (const α) const_injective

lemma infinite_fun_ofInfinite {α β : Type*} [Infinite α] [Nontrivial β] : Infinite (α → β) := by
  classical
  obtain ⟨b, b', h_b⟩ := nontrivial_iff.1 (by assumption)
  let f := fun y : α ↦ (Set.singleton y).piecewise (const α b) (const α b')
  refine Infinite.of_injective f fun a a' h_a ↦ ?_
  by_contra h_a'
  replace h_a' := Set.notMem_singleton_iff.2 h_a'
  simp only [f, funext_iff] at h_a
  specialize h_a a
  rw [(Set.singleton a).piecewise_eq_of_mem (const α b) (const α b') (Set.mem_singleton a),
    (Set.singleton a').piecewise_eq_of_notMem (const α b) (const α b') h_a',
    const_apply, const_apply] at h_a
  exact h_b h_a

lemma unique_fun_toUnique {α β : Type*} [Nonempty (Unique β)] : Nonempty (Unique (α → β)) := by
  obtain ⟨_, _⟩ := (unique_iff_subsingleton_and_nonempty β).1 (by assumption)
  exact (unique_iff_subsingleton_and_nonempty (α → β)).2 ⟨Pi.instSubsingleton, Pi.instNonempty⟩

instance : NoZeroDivisors ℕ∞ :=
  inferInstanceAs (NoZeroDivisors (WithTop ℕ))

lemma one_lt_mul_iff {x y : ℕ∞} : 1 < x * y ↔ (1 < x ∧ 1 ≤ y) ∨ (1 ≤ x ∧ 1 < y) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases lt_trichotomy x 1 with x_0 | rfl | x_2
    · rw [lt_one_iff_eq_zero.1 x_0, zero_mul] at h
      contradiction
    · rw [one_mul] at h
      exact Or.inr ⟨le_refl 1, h⟩
    · refine Or.inl ⟨x_2, le_of_not_lt fun y_0 ↦ ?_⟩
      rw [lt_one_iff_eq_zero.1 y_0, mul_zero] at h
      contradiction
  · rcases h with h | h
    · rw [mul_comm x y]
      exact one_lt_mul h.2 h.1
    · exact one_lt_mul h.1 h.2

instance : Subsingleton ℕ∞ˣ := by
  refine subsingleton_of_forall_eq 1 fun x ↦ ?_
  rcases lt_trichotomy x 1 with x_0 | x_1 | x_2
  · exact (x.ne_zero (lt_one_iff_eq_zero.1 x_0)).rec
  · exact x_1
  · have x_inv := x.val_inv
    have := (not_iff_not.2 (@one_lt_mul_iff x x.inv)).1 x_inv.symm.not_lt
    rw [← Units.val_lt_val, Units.val_one] at x_2
    simp only [not_or, not_and, not_le, not_lt] at this
    rw [lt_one_iff_eq_zero.1 (this.1 x_2), mul_zero] at x_inv
    contradiction

noncomputable def epow : ℕ∞ → ℕ∞ → ℕ∞
  | x, some y => x ^ y
  | x, ⊤ => if x = 0 then 0 else if x = 1 then 1 else ⊤

@[simp]
lemma epow_coe {x : ℕ∞} {y : ℕ} : x.epow y = x ^ y := rfl

lemma epow_top_def {x : ℕ∞} : x.epow ⊤ = if x = 0 then 0 else if x = 1 then 1 else ⊤ := rfl

@[simp]
lemma zero_epow_top : (0 : ℕ∞).epow ⊤ = 0 := rfl

@[simp]
lemma one_epow {y : ℕ∞} : (1 : ℕ∞).epow y = 1 := by
  induction y with
  | top => rfl
  | coe y => simp

@[simp]
lemma top_epow_top : (⊤ : ℕ∞).epow ⊤ = ⊤ := rfl

lemma epow_top {x : ℕ∞} (h : 1 < x) : x.epow ⊤ = ⊤ := by
  simp only [epow_top_def, (zero_le_one.trans_lt h).ne.symm, ↓reduceIte, h.ne.symm]

lemma epow_top_eq_zero_iff {x : ℕ∞} : x.epow ⊤ = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.symm ▸ zero_epow_top⟩
  rcases lt_trichotomy x 1 with x_0 | rfl | x_2
  · exact lt_one_iff_eq_zero.1 x_0
  · rwa [one_epow] at h
  · rw [epow_top x_2] at h
    contradiction

@[simp]
lemma epow_zero {x : ℕ∞} : x.epow 0 = 1 := by rw [← coe_zero, epow_coe, _root_.pow_zero]

@[simp]
lemma epow_one {x : ℕ∞} : x.epow 1 = x := by rw [← coe_one, epow_coe, _root_.pow_one]

lemma zero_epow_pos {y : ℕ∞} (h : y ≠ 0) : (0 : ℕ∞).epow y = 0 := by
  induction y with
  | top => exact zero_epow_top
  | coe y =>
    rwa [epow_coe, pow_eq_zero_iff', eq_self 0, true_and, ← y.cast_ne_zero (R := ℕ∞)]

lemma top_epow_pos {y : ℕ∞} (h : y ≠ 0) : (⊤ : ℕ∞).epow y = ⊤ := by
  induction y with
  | top => exact top_epow_top
  | coe y =>
    rwa [epow_coe, pow_eq_top_iff, eq_self ⊤, true_and, ← y.cast_ne_zero (R := ℕ∞)]

lemma epow_eq_zero_iff {x y : ℕ∞} : x.epow y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.1.symm ▸ zero_epow_pos h.2⟩
  induction y with
  | top =>
    simp only [ne_eq, top_ne_zero, not_false_eq_true, and_true]
    rcases lt_trichotomy x 1 with x_0 | x_1 | x_2
    · exact lt_one_iff_eq_zero.1 x_0
    · rw [x_1, one_epow] at h
      contradiction
    · rw [epow_top x_2] at h
      contradiction
  | coe y =>
    rw [epow_coe, pow_eq_zero_iff'] at h
    exact ⟨h.1, y.cast_ne_zero.2 h.2⟩

lemma mul_epow {x y z : ℕ∞} : (x * y).epow z = (x.epow z) * (y.epow z) := by
  induction z
  · rcases lt_trichotomy (x * y) 1 with xy_0 | xy_1 | xy_2
    · rw [lt_one_iff_eq_zero] at xy_0
      rw [xy_0, zero_epow_top]
      apply (mul_eq_zero.2 _).symm
      rcases mul_eq_zero.1 xy_0 with h | h <;> rw [h]
      · exact .inl zero_epow_top
      · exact .inr zero_epow_top
    · rw [xy_1, (mul_eq_one.1 xy_1).1, (mul_eq_one.1 xy_1).2, one_epow, one_mul]
    · rw [epow_top xy_2]
      rcases one_lt_mul_iff.1 xy_2 with h | h
      · rw [epow_top h.1, mul_comm]
        refine (mul_top fun y_0 ↦ ?_).symm
        rw [epow_top_eq_zero_iff.1 y_0, mul_zero] at xy_2
        contradiction
      · rw [epow_top h.2]
        refine (mul_top fun x_0 ↦ ?_).symm
        rw [epow_top_eq_zero_iff.1 x_0, zero_mul] at xy_2
        contradiction
  · simp only [epow_coe]
    exact _root_.mul_pow x y _

lemma card_pow {α β : Type*} : ENat.card (α → β) = (ENat.card β).epow (ENat.card α) := by
  classical
  rcases finite_or_infinite α
  · have _ := Fintype.ofFinite α
    rcases finite_or_infinite β
    · have _ := Fintype.ofFinite β
      rw [card_eq_coe_fintype_card (α := α), card_eq_coe_fintype_card (α := β),
        card_eq_coe_fintype_card (α := α → β), epow_coe, ← Nat.cast_pow, Fintype.card_fun]
    · rw [card_eq_top_of_infinite (α := β)]
      rcases isEmpty_or_nonempty α with _ | h
      · simp
      · rw [top_epow_pos ((card_ne_zero_iff_nonempty α).2 h), card_eq_top]
        exact infinite_fun_toInfinite
  · rw [card_eq_top_of_infinite (α := α)]
    rcases lt_trichotomy (ENat.card β) 1 with b_0 | b_1 | b_2
    · rw [lt_one_iff_eq_zero] at b_0
      rw [b_0, zero_epow_top]
      rw [card_eq_zero_iff_empty] at b_0 ⊢
      simp only [isEmpty_pi, b_0, exists_const]
    · rw [b_1, one_epow, card_eq_one_iff_unique]
      rw [card_eq_one_iff_unique] at b_1
      exact unique_fun_toUnique
    · rw [epow_top b_2, card_eq_top]
      rw [one_lt_card_iff_nontrivial β] at b_2
      exact infinite_fun_ofInfinite

end ENat
