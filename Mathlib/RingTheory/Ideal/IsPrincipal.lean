/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.Algebra.Algebra.Operations

/-!
# Principal Ideals
-/

namespace Ideal

variable {R : Type*}

section Semiring

variable [Semiring R]

@[simp]
theorem zero_eq_bot : (0 : Ideal R) = ⊥ :=
  rfl
#align ideal.zero_eq_bot Ideal.zero_eq_bot

theorem mem_span_singleton' {x y : R} : x ∈ span ({y} : Set R) ↔ ∃ a, a * y = x :=
  Submodule.mem_span_singleton
#align ideal.mem_span_singleton' Ideal.mem_span_singleton'

theorem span_singleton_le_iff_mem (I : Ideal R) {x : R} : span {x} ≤ I ↔ x ∈ I :=
  Submodule.span_singleton_le_iff_mem _ _
#align ideal.span_singleton_le_iff_mem Ideal.span_singleton_le_iff_mem

theorem span_singleton_mul_left_unit {a : R} (h2 : IsUnit a) (x : R) :
    span ({a * x} : Set R) = span {x} := by
  apply le_antisymm <;> rw [span_singleton_le_iff_mem, mem_span_singleton']
  exacts [⟨a, rfl⟩, ⟨_, h2.unit.inv_mul_cancel_left x⟩]
#align ideal.span_singleton_mul_left_unit Ideal.span_singleton_mul_left_unit

end Semiring

section CommSemiring

variable [CommSemiring R]

open Submodule Set

@[simp]
theorem one_eq_top : (1 : Ideal R) = ⊤ := by erw [Submodule.one_eq_range, LinearMap.range_id]
#align ideal.one_eq_top Ideal.one_eq_top

theorem span_singleton_ne_top {x : R} (hx : ¬IsUnit x) :
    Ideal.span ({x} : Set R) ≠ ⊤ :=
  (Ideal.ne_top_iff_one _).mpr fun h1 =>
    let ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp h1
    hx ⟨⟨x, y, mul_comm y x ▸ hy, hy⟩, rfl⟩
#align ideal.span_singleton_ne_top Ideal.span_singleton_ne_top

theorem mem_span_singleton_sup {x y : R} {I : Ideal R} :
    x ∈ Ideal.span {y} ⊔ I ↔ ∃ a : R, ∃ b ∈ I, a * y + b = x := by
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨ya, hya, b, hb, rfl⟩
    obtain ⟨a, rfl⟩ := mem_span_singleton'.mp hya
    exact ⟨a, b, hb, rfl⟩
  · rintro ⟨a, b, hb, rfl⟩
    exact ⟨a * y, Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩, b, hb, rfl⟩
#align ideal.mem_span_singleton_sup Ideal.mem_span_singleton_sup

theorem mem_span_singleton {x y : R} : x ∈ span ({y} : Set R) ↔ y ∣ x :=
  mem_span_singleton'.trans <| exists_congr fun _ => by rw [eq_comm, mul_comm]
#align ideal.mem_span_singleton Ideal.mem_span_singleton

theorem mem_span_singleton_self (x : R) : x ∈ span ({x} : Set R) :=
  mem_span_singleton.mpr dvd_rfl
#align ideal.mem_span_singleton_self Ideal.mem_span_singleton_self

theorem span_singleton_le_span_singleton {x y : R} :
    span ({x} : Set R) ≤ span ({y} : Set R) ↔ y ∣ x :=
  span_le.trans <| singleton_subset_iff.trans mem_span_singleton
#align ideal.span_singleton_le_span_singleton Ideal.span_singleton_le_span_singleton

theorem span_singleton_eq_span_singleton {S : Type*} [CommRing S] [IsDomain S] {x y : S} :
    span ({x} : Set S) = span ({y} : Set S) ↔ Associated x y := by
  rw [← dvd_dvd_iff_associated, le_antisymm_iff, and_comm]
  apply and_congr <;> rw [span_singleton_le_span_singleton]
#align ideal.span_singleton_eq_span_singleton Ideal.span_singleton_eq_span_singleton

theorem span_singleton_mul_right_unit {a : R} (h2 : IsUnit a) (x : R) :
    span ({x * a} : Set R) = span {x} := by rw [mul_comm, span_singleton_mul_left_unit h2]
#align ideal.span_singleton_mul_right_unit Ideal.span_singleton_mul_right_unit

@[simp]
theorem span_singleton_eq_top {x} : span ({x} : Set R) = ⊤ ↔ IsUnit x := by
  rw [isUnit_iff_dvd_one, ← span_singleton_le_span_singleton, span_singleton_one, eq_top_iff]
#align ideal.span_singleton_eq_top Ideal.span_singleton_eq_top

theorem span_singleton_prime {p : R} (hp : p ≠ 0) : IsPrime (span ({p} : Set R)) ↔ Prime p := by
  simp [isPrime_iff, Prime, span_singleton_eq_top, hp, mem_span_singleton]
#align ideal.span_singleton_prime Ideal.span_singleton_prime

theorem span_singleton_lt_span_singleton [IsDomain R] {x y : R} :
    span ({x} : Set R) < span ({y} : Set R) ↔ DvdNotUnit y x := by
  rw [lt_iff_le_not_le, span_singleton_le_span_singleton, span_singleton_le_span_singleton,
    dvd_and_not_dvd_iff]
#align ideal.span_singleton_lt_span_singleton Ideal.span_singleton_lt_span_singleton

theorem span_pow_eq_top (s : Set R) (hs : span s = ⊤) (n : ℕ) :
    span ((fun (x : R) => x ^ n) '' s) = ⊤ := by
  rw [eq_top_iff_one]
  cases' n with n
  · obtain rfl | ⟨x, hx⟩ := eq_empty_or_nonempty s
    · rw [Set.image_empty, hs]
      trivial
    · exact subset_span ⟨_, hx, pow_zero _⟩
  rw [eq_top_iff_one, span, Finsupp.mem_span_iff_total] at hs
  rcases hs with ⟨f, hf⟩
  have hf : (f.support.sum fun a => f a * a) = 1 := hf -- Porting note: was `change ... at hf`
  have := sum_pow_mem_span_pow f.support (fun a => f a * a) n
  rw [hf, one_pow] at this
  refine' span_le.mpr _ this
  rintro _ hx
  simp_rw [Set.mem_image] at hx
  rcases hx with ⟨x, _, rfl⟩
  have : span ({(x:R) ^ (n + 1)} : Set R) ≤ span ((fun x : R => x ^ (n + 1)) '' s) := by
    rw [span_le, Set.singleton_subset_iff]
    exact subset_span ⟨x, x.prop, rfl⟩
  refine this ?_
  rw [mul_pow, mem_span_singleton]
  exact ⟨f x ^ (n + 1), mul_comm _ _⟩
#align ideal.span_pow_eq_top Ideal.span_pow_eq_top

theorem span_singleton_mul_span_singleton (r s : R) :
    span {r} * span {s} = (span {r * s} : Ideal R) := by
  unfold span
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]
#align ideal.span_singleton_mul_span_singleton Ideal.span_singleton_mul_span_singleton

theorem span_singleton_pow (s : R) (n : ℕ) : span {s} ^ n = (span {s ^ n} : Ideal R) := by
  induction' n with n ih; · simp [Set.singleton_one]
  simp only [pow_succ, ih, span_singleton_mul_span_singleton]
#align ideal.span_singleton_pow Ideal.span_singleton_pow

end CommSemiring

section Ring

variable [Ring R]

@[simp]
theorem span_singleton_neg (x : R) : (span {-x} : Ideal R) = span {x} := by
  ext
  simp only [mem_span_singleton']
  exact ⟨fun ⟨y, h⟩ => ⟨-y, h ▸ neg_mul_comm y x⟩, fun ⟨y, h⟩ => ⟨-y, h ▸ neg_mul_neg y x⟩⟩
#align ideal.span_singleton_neg Ideal.span_singleton_neg

end Ring

section IsDomain

variable [CommRing R] [IsDomain R]

variable (R) in
/-- The equivalence between `Associates R` and the principal ideals of `R` defined by sending the
class of `x` to the principal ideal generated by `x`. -/
noncomputable def associatesEquivIsPrincipal :
    Associates R ≃ {I : Ideal R // Submodule.IsPrincipal I} := by
  refine Equiv.ofBijective (fun x ↦ ⟨Ideal.span {Quot.out x}, ⟨Quot.out x, rfl⟩⟩)
    ⟨fun  _ _ h ↦ ?_, fun ⟨I, hI⟩ ↦ ?_⟩
  · rw [Subtype.mk_eq_mk, span_singleton_eq_span_singleton] at h
    exact Quotient.out_equiv_out.mp h
  · obtain ⟨x, hx⟩ := hI
    refine ⟨⟦x⟧, ?_⟩
    rw [Subtype.mk_eq_mk, hx, submodule_span_eq, span_singleton_eq_span_singleton]
    exact Associates.mk_quot_out x

@[simp]
theorem associatesEquivIsPrincipal_apply (x : R) :
    associatesEquivIsPrincipal R ⟦x⟧ = Ideal.span {x} := by
  rw [associatesEquivIsPrincipal, Equiv.ofBijective_apply, span_singleton_eq_span_singleton]
  exact Associates.mk_quot_out x

end IsDomain

end Ideal

section

open Ring Set

variable {R : Type*}

theorem Ideal.factors_decreasing [CommSemiring R] [IsDomain R] (b₁ b₂ : R) (h₁ : b₁ ≠ 0)
    (h₂ : ¬IsUnit b₂) :
    span ({b₁ * b₂} : Set R) < span {b₁} :=
  lt_of_le_not_le
    (Ideal.span_le.2 <| singleton_subset_iff.2 <| Ideal.mem_span_singleton.2 ⟨b₂, rfl⟩) fun h =>
    h₂ <| isUnit_of_dvd_one <|
        (mul_dvd_mul_iff_left h₁).1 <| by rwa [mul_one, ← Ideal.span_singleton_le_span_singleton]
#align ideal.factors_decreasing Ideal.factors_decreasing

lemma Ideal.isPrime_of_maximally_disjoint  [CommSemiring R] (I : Ideal R) (S : Submonoid R)
    (disjoint : Disjoint (I : Set R) S)
    (maximally_disjoint : ∀ (J : Ideal R), I < J → ¬ Disjoint (J : Set R) S) :
    I.IsPrime where
  ne_top' := by
    rintro rfl
    have : 1 ∈ (S : Set R) := S.one_mem
    aesop
  mem_or_mem' {x y} hxy := by
    by_contra! rid
    have hx := maximally_disjoint (I ⊔ span {x}) (Submodule.lt_sup_iff_not_mem.mpr rid.1)
    have hy := maximally_disjoint (I ⊔ span {y}) (Submodule.lt_sup_iff_not_mem.mpr rid.2)
    simp only [Set.not_disjoint_iff, mem_inter_iff, SetLike.mem_coe, Submodule.mem_sup,
      mem_span_singleton] at hx hy
    obtain ⟨s₁, ⟨i₁, hi₁, ⟨_, ⟨r₁, rfl⟩, hr₁⟩⟩, hs₁⟩ := hx
    obtain ⟨s₂, ⟨i₂, hi₂, ⟨_, ⟨r₂, rfl⟩, hr₂⟩⟩, hs₂⟩ := hy
    refine disjoint.ne_of_mem
      (I.add_mem (I.mul_mem_left (i₁ + x * r₁) hi₂) <| I.add_mem (I.mul_mem_right (y * r₂) hi₁) <|
        I.mul_mem_right (r₁ * r₂) hxy)
      (S.mul_mem hs₁ hs₂) ?_
    rw [← hr₁, ← hr₂]
    ring

theorem Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top [CommSemiring R] [Nontrivial R] :
    ¬IsField R ↔ ∃ I : Ideal R, ⊥ < I ∧ I < ⊤ := by
  constructor
  · intro h
    obtain ⟨x, nz, nu⟩ := exists_not_isUnit_of_not_isField h
    use Ideal.span {x}
    rw [bot_lt_iff_ne_bot, lt_top_iff_ne_top]
    exact ⟨mt Ideal.span_singleton_eq_bot.mp nz, mt Ideal.span_singleton_eq_top.mp nu⟩
  · rintro ⟨I, bot_lt, lt_top⟩ hf
    obtain ⟨x, mem, ne_zero⟩ := SetLike.exists_of_lt bot_lt
    rw [Submodule.mem_bot] at ne_zero
    obtain ⟨y, hy⟩ := hf.mul_inv_cancel ne_zero
    rw [lt_top_iff_ne_top, Ne, Ideal.eq_top_iff_one, ← hy] at lt_top
    exact lt_top (I.mul_mem_right _ mem)
#align ring.not_is_field_iff_exists_ideal_bot_lt_and_lt_top Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top

theorem Ring.not_isField_iff_exists_prime [CommSemiring R] [Nontrivial R] :
    ¬IsField R ↔ ∃ p : Ideal R, p ≠ ⊥ ∧ p.IsPrime :=
  not_isField_iff_exists_ideal_bot_lt_and_lt_top.trans
    ⟨fun ⟨I, bot_lt, lt_top⟩ =>
      let ⟨p, hp, le_p⟩ := I.exists_le_maximal (lt_top_iff_ne_top.mp lt_top)
      ⟨p, bot_lt_iff_ne_bot.mp (lt_of_lt_of_le bot_lt le_p), hp.isPrime⟩,
      fun ⟨p, ne_bot, Prime⟩ => ⟨p, bot_lt_iff_ne_bot.mpr ne_bot, lt_top_iff_ne_top.mpr Prime.1⟩⟩
#align ring.not_is_field_iff_exists_prime Ring.not_isField_iff_exists_prime

/-- Also see `Ideal.isSimpleOrder` for the forward direction as an instance when `R` is a
division (semi)ring.

This result actually holds for all division semirings, but we lack the predicate to state it. -/
theorem Ring.isField_iff_isSimpleOrder_ideal [CommSemiring R]:
    IsField R ↔ IsSimpleOrder (Ideal R) := by
  cases subsingleton_or_nontrivial R
  · exact
      ⟨fun h => (not_isField_of_subsingleton _ h).elim, fun h =>
        (false_of_nontrivial_of_subsingleton <| Ideal R).elim⟩
  rw [← not_iff_not, Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top, ← not_iff_not]
  push_neg
  simp_rw [lt_top_iff_ne_top, bot_lt_iff_ne_bot, ← or_iff_not_imp_left, not_ne_iff]
  exact ⟨fun h => ⟨h⟩, fun h => h.2⟩
#align ring.is_field_iff_is_simple_order_ideal Ring.isField_iff_isSimpleOrder_ideal

/-- When a ring is not a field, the maximal ideals are nontrivial. -/
theorem Ring.ne_bot_of_isMaximal_of_not_isField [CommSemiring R] [Nontrivial R] {M : Ideal R}
    (max : M.IsMaximal) (not_field : ¬IsField R) : M ≠ ⊥ := by
  rintro h
  rw [h] at max
  rcases max with ⟨⟨_h1, h2⟩⟩
  obtain ⟨I, hIbot, hItop⟩ := not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp not_field
  exact ne_of_lt hItop (h2 I hIbot)
#align ring.ne_bot_of_is_maximal_of_not_is_field Ring.ne_bot_of_isMaximal_of_not_isField

theorem Ideal.bot_lt_of_maximal {R : Type*} [CommSemiring R] [Nontrivial R] (M : Ideal R)
    [hm : M.IsMaximal] (non_field : ¬IsField R) : ⊥ < M := by
  rcases Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.1 non_field with ⟨I, Ibot, Itop⟩
  constructor; · simp
  intro mle
  apply lt_irrefl (⊤ : Ideal R)
  have : M = ⊥ := eq_bot_iff.mpr mle
  rw [← this] at Ibot
  rwa [hm.1.2 I Ibot] at Itop
#align ideal.bot_lt_of_maximal Ideal.bot_lt_of_maximal

theorem exists_max_ideal_of_mem_nonunits {a : R} [CommSemiring R] (h : a ∈ nonunits R) :
    ∃ I : Ideal R, I.IsMaximal ∧ a ∈ I := by
  have : Ideal.span ({a} : Set R) ≠ ⊤ := by
    intro H
    rw [Ideal.span_singleton_eq_top] at H
    contradiction
  rcases Ideal.exists_le_maximal _ this with ⟨I, Imax, H⟩
  use I, Imax
  apply H
  apply Ideal.subset_span
  exact Set.mem_singleton a
#align exists_max_ideal_of_mem_nonunits exists_max_ideal_of_mem_nonunits

end
