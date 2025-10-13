/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Order.BoundedOrder.Basic

/-!
# Associated elements.

In this file we define an equivalence relation `Associated`
saying that two elements of a monoid differ by a multiplication by a unit.
Then we show that the quotient type `Associates` is a monoid
and prove basic properties of this quotient.
-/

assert_not_exists OrderedCommMonoid Multiset Ring

variable {M : Type*}

/-- Two elements of a `Monoid` are `Associated` if one of them is another one
multiplied by a unit on the right. -/
def Associated [Monoid M] (x y : M) : Prop :=
  ∃ u : Mˣ, x * u = y

/-- Notation for two elements of a monoid are associated, i.e.
if one of them is another one multiplied by a unit on the right. -/
local infixl:50 " ~ᵤ " => Associated

namespace Associated

@[refl]
protected theorem refl [Monoid M] (x : M) : x ~ᵤ x :=
  ⟨1, by simp⟩

protected theorem rfl [Monoid M] {x : M} : x ~ᵤ x :=
  .refl x

instance [Monoid M] : IsRefl M Associated :=
  ⟨Associated.refl⟩

@[symm]
protected theorem symm [Monoid M] : ∀ {x y : M}, x ~ᵤ y → y ~ᵤ x
  | x, _, ⟨u, rfl⟩ => ⟨u⁻¹, by rw [mul_assoc, Units.mul_inv, mul_one]⟩

instance [Monoid M] : IsSymm M Associated :=
  ⟨fun _ _ => Associated.symm⟩

protected theorem comm [Monoid M] {x y : M} : x ~ᵤ y ↔ y ~ᵤ x :=
  ⟨Associated.symm, Associated.symm⟩

@[trans]
protected theorem trans [Monoid M] : ∀ {x y z : M}, x ~ᵤ y → y ~ᵤ z → x ~ᵤ z
  | x, _, _, ⟨u, rfl⟩, ⟨v, rfl⟩ => ⟨u * v, by rw [Units.val_mul, mul_assoc]⟩

instance [Monoid M] : IsTrans M Associated :=
  ⟨fun _ _ _ => Associated.trans⟩

/-- The setoid of the relation `x ~ᵤ y` iff there is a unit `u` such that `x * u = y` -/
protected def setoid (M : Type*) [Monoid M] :
    Setoid M where
  r := Associated
  iseqv := ⟨Associated.refl, Associated.symm, Associated.trans⟩

theorem map {M N : Type*} [Monoid M] [Monoid N] {F : Type*} [FunLike F M N] [MonoidHomClass F M N]
    (f : F) {x y : M} (ha : Associated x y) : Associated (f x) (f y) := by
  obtain ⟨u, ha⟩ := ha
  exact ⟨Units.map f u, by rw [← ha, map_mul, Units.coe_map, MonoidHom.coe_coe]⟩

end Associated

attribute [local instance] Associated.setoid

theorem unit_associated_one [Monoid M] {u : Mˣ} : (u : M) ~ᵤ 1 :=
  ⟨u⁻¹, Units.mul_inv u⟩

@[simp]
theorem associated_one_iff_isUnit [Monoid M] {a : M} : (a : M) ~ᵤ 1 ↔ IsUnit a :=
  Iff.intro
    (fun h =>
      let ⟨c, h⟩ := h.symm
      h ▸ ⟨c, (one_mul _).symm⟩)
    fun ⟨c, h⟩ => Associated.symm ⟨c, by simp [h]⟩

@[simp]
theorem associated_zero_iff_eq_zero [MonoidWithZero M] (a : M) : a ~ᵤ 0 ↔ a = 0 :=
  Iff.intro
    (fun h => by
      let ⟨u, h⟩ := h.symm
      simpa using h.symm)
    fun h => h ▸ Associated.refl a

theorem associated_one_of_mul_eq_one [CommMonoid M] {a : M} (b : M) (hab : a * b = 1) : a ~ᵤ 1 :=
  show (Units.mkOfMulEqOne a b hab : M) ~ᵤ 1 from unit_associated_one

theorem associated_one_of_associated_mul_one [CommMonoid M] {a b : M} : a * b ~ᵤ 1 → a ~ᵤ 1
  | ⟨u, h⟩ => associated_one_of_mul_eq_one (b * u) <| by simpa [mul_assoc] using h

theorem associated_mul_unit_left {N : Type*} [Monoid N] (a u : N) (hu : IsUnit u) :
    Associated (a * u) a :=
  let ⟨u', hu⟩ := hu
  ⟨u'⁻¹, hu ▸ Units.mul_inv_cancel_right _ _⟩

theorem associated_unit_mul_left {N : Type*} [CommMonoid N] (a u : N) (hu : IsUnit u) :
    Associated (u * a) a := by
  rw [mul_comm]
  exact associated_mul_unit_left _ _ hu

theorem associated_mul_unit_right {N : Type*} [Monoid N] (a u : N) (hu : IsUnit u) :
    Associated a (a * u) :=
  (associated_mul_unit_left a u hu).symm

theorem associated_unit_mul_right {N : Type*} [CommMonoid N] (a u : N) (hu : IsUnit u) :
    Associated a (u * a) :=
  (associated_unit_mul_left a u hu).symm

theorem associated_mul_isUnit_left_iff {N : Type*} [Monoid N] {a u b : N} (hu : IsUnit u) :
    Associated (a * u) b ↔ Associated a b :=
  ⟨(associated_mul_unit_right _ _ hu).trans, (associated_mul_unit_left _ _ hu).trans⟩

theorem associated_isUnit_mul_left_iff {N : Type*} [CommMonoid N] {u a b : N} (hu : IsUnit u) :
    Associated (u * a) b ↔ Associated a b := by
  rw [mul_comm]
  exact associated_mul_isUnit_left_iff hu

theorem associated_mul_isUnit_right_iff {N : Type*} [Monoid N] {a b u : N} (hu : IsUnit u) :
    Associated a (b * u) ↔ Associated a b :=
  Associated.comm.trans <| (associated_mul_isUnit_left_iff hu).trans Associated.comm

theorem associated_isUnit_mul_right_iff {N : Type*} [CommMonoid N] {a u b : N} (hu : IsUnit u) :
    Associated a (u * b) ↔ Associated a b :=
  Associated.comm.trans <| (associated_isUnit_mul_left_iff hu).trans Associated.comm

@[simp]
theorem associated_mul_unit_left_iff {N : Type*} [Monoid N] {a b : N} {u : Units N} :
    Associated (a * u) b ↔ Associated a b :=
  associated_mul_isUnit_left_iff u.isUnit

@[simp]
theorem associated_unit_mul_left_iff {N : Type*} [CommMonoid N] {a b : N} {u : Units N} :
    Associated (↑u * a) b ↔ Associated a b :=
  associated_isUnit_mul_left_iff u.isUnit

@[simp]
theorem associated_mul_unit_right_iff {N : Type*} [Monoid N] {a b : N} {u : Units N} :
    Associated a (b * u) ↔ Associated a b :=
  associated_mul_isUnit_right_iff u.isUnit

@[simp]
theorem associated_unit_mul_right_iff {N : Type*} [CommMonoid N] {a b : N} {u : Units N} :
    Associated a (↑u * b) ↔ Associated a b :=
  associated_isUnit_mul_right_iff u.isUnit

theorem Associated.mul_left [Monoid M] (a : M) {b c : M} (h : b ~ᵤ c) : a * b ~ᵤ a * c := by
  obtain ⟨d, rfl⟩ := h; exact ⟨d, mul_assoc _ _ _⟩

theorem Associated.mul_right [CommMonoid M] {a b : M} (h : a ~ᵤ b) (c : M) : a * c ~ᵤ b * c := by
  obtain ⟨d, rfl⟩ := h; exact ⟨d, mul_right_comm _ _ _⟩

theorem Associated.mul_mul [CommMonoid M] {a₁ a₂ b₁ b₂ : M}
    (h₁ : a₁ ~ᵤ b₁) (h₂ : a₂ ~ᵤ b₂) : a₁ * a₂ ~ᵤ b₁ * b₂ := (h₁.mul_right _).trans (h₂.mul_left _)

theorem Associated.pow_pow [CommMonoid M] {a b : M} {n : ℕ} (h : a ~ᵤ b) : a ^ n ~ᵤ b ^ n := by
  induction n with
  | zero => simp [Associated.refl]
  | succ n ih => convert h.mul_mul ih <;> rw [pow_succ']

protected theorem Associated.dvd [Monoid M] {a b : M} : a ~ᵤ b → a ∣ b := fun ⟨u, hu⟩ =>
  ⟨u, hu.symm⟩

protected theorem Associated.dvd' [Monoid M] {a b : M} (h : a ~ᵤ b) : b ∣ a :=
  h.symm.dvd

protected theorem Associated.dvd_dvd [Monoid M] {a b : M} (h : a ~ᵤ b) : a ∣ b ∧ b ∣ a :=
  ⟨h.dvd, h.symm.dvd⟩

theorem associated_of_dvd_dvd [CancelMonoidWithZero M] {a b : M} (hab : a ∣ b) (hba : b ∣ a) :
    a ~ᵤ b := by
  rcases hab with ⟨c, rfl⟩
  rcases hba with ⟨d, a_eq⟩
  by_cases ha0 : a = 0
  · simp_all
  have hac0 : a * c ≠ 0 := by
    intro con
    rw [con, zero_mul] at a_eq
    apply ha0 a_eq
  have : a * (c * d) = a * 1 := by rw [← mul_assoc, ← a_eq, mul_one]
  have hcd : c * d = 1 := mul_left_cancel₀ ha0 this
  have : a * c * (d * c) = a * c * 1 := by rw [← mul_assoc, ← a_eq, mul_one]
  have hdc : d * c = 1 := mul_left_cancel₀ hac0 this
  exact ⟨⟨c, d, hcd, hdc⟩, rfl⟩

theorem dvd_dvd_iff_associated [CancelMonoidWithZero M] {a b : M} : a ∣ b ∧ b ∣ a ↔ a ~ᵤ b :=
  ⟨fun ⟨h1, h2⟩ => associated_of_dvd_dvd h1 h2, Associated.dvd_dvd⟩

instance [CancelMonoidWithZero M] [DecidableRel ((· ∣ ·) : M → M → Prop)] :
    DecidableRel ((· ~ᵤ ·) : M → M → Prop) := fun _ _ => decidable_of_iff _ dvd_dvd_iff_associated

theorem Associated.dvd_iff_dvd_left [Monoid M] {a b c : M} (h : a ~ᵤ b) : a ∣ c ↔ b ∣ c :=
  let ⟨_, hu⟩ := h
  hu ▸ Units.mul_right_dvd.symm

theorem Associated.dvd_iff_dvd_right [Monoid M] {a b c : M} (h : b ~ᵤ c) : a ∣ b ↔ a ∣ c :=
  let ⟨_, hu⟩ := h
  hu ▸ Units.dvd_mul_right.symm

theorem Associated.eq_zero_iff [MonoidWithZero M] {a b : M} (h : a ~ᵤ b) : a = 0 ↔ b = 0 := by
  obtain ⟨u, rfl⟩ := h
  rw [← Units.eq_mul_inv_iff_mul_eq, zero_mul]

theorem Associated.ne_zero_iff [MonoidWithZero M] {a b : M} (h : a ~ᵤ b) : a ≠ 0 ↔ b ≠ 0 :=
  not_congr h.eq_zero_iff

protected theorem Associated.prime [CommMonoidWithZero M] {p q : M} (h : p ~ᵤ q) (hp : Prime p) :
    Prime q :=
  ⟨h.ne_zero_iff.1 hp.ne_zero,
    let ⟨u, hu⟩ := h
    ⟨fun ⟨v, hv⟩ => hp.not_unit ⟨v * u⁻¹, by simp [hv, hu.symm]⟩,
      hu ▸ by
        simp only [Units.isUnit, IsUnit.mul_right_dvd]
        intro a b
        exact hp.dvd_or_dvd⟩⟩

theorem prime_mul_iff [CancelCommMonoidWithZero M] {x y : M} :
    Prime (x * y) ↔ (Prime x ∧ IsUnit y) ∨ (IsUnit x ∧ Prime y) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases of_irreducible_mul h.irreducible with hx | hy
    · exact Or.inr ⟨hx, (associated_unit_mul_left y x hx).prime h⟩
    · exact Or.inl ⟨(associated_mul_unit_left x y hy).prime h, hy⟩
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · exact (associated_mul_unit_left x y hy).symm.prime hx
    · exact (associated_unit_mul_right y x hx).prime hy

@[simp]
lemma prime_pow_iff [CancelCommMonoidWithZero M] {p : M} {n : ℕ} :
    Prime (p ^ n) ↔ Prime p ∧ n = 1 := by
  refine ⟨fun hp ↦ ?_, fun ⟨hp, hn⟩ ↦ by simpa [hn]⟩
  suffices n = 1 by simp_all
  rcases n with - | n
  · simp at hp
  · rw [Nat.succ.injEq]
    rw [pow_succ', prime_mul_iff] at hp
    rcases hp with ⟨hp, hpn⟩ | ⟨hp, hpn⟩
    · by_contra contra
      rw [isUnit_pow_iff contra] at hpn
      exact hp.not_unit hpn
    · exfalso
      exact hpn.not_unit (hp.pow n)

theorem Irreducible.dvd_iff [Monoid M] {x y : M} (hx : Irreducible x) :
    y ∣ x ↔ IsUnit y ∨ Associated x y := by
  constructor
  · rintro ⟨z, hz⟩
    obtain (h|h) := hx.isUnit_or_isUnit hz
    · exact Or.inl h
    · rw [hz]
      exact Or.inr (associated_mul_unit_left _ _ h)
  · rintro (hy|h)
    · exact hy.dvd
    · exact h.symm.dvd

theorem Irreducible.associated_of_dvd [Monoid M] {p q : M} (p_irr : Irreducible p)
    (q_irr : Irreducible q) (dvd : p ∣ q) : Associated p q :=
  ((q_irr.dvd_iff.mp dvd).resolve_left p_irr.not_isUnit).symm

theorem Irreducible.dvd_irreducible_iff_associated [Monoid M] {p q : M}
    (pp : Irreducible p) (qp : Irreducible q) : p ∣ q ↔ Associated p q :=
  ⟨Irreducible.associated_of_dvd pp qp, Associated.dvd⟩

theorem Prime.associated_of_dvd [CancelCommMonoidWithZero M] {p q : M} (p_prime : Prime p)
    (q_prime : Prime q) (dvd : p ∣ q) : Associated p q :=
  p_prime.irreducible.associated_of_dvd q_prime.irreducible dvd

theorem Prime.dvd_prime_iff_associated [CancelCommMonoidWithZero M] {p q : M} (pp : Prime p)
    (qp : Prime q) : p ∣ q ↔ Associated p q :=
  pp.irreducible.dvd_irreducible_iff_associated qp.irreducible

theorem Associated.prime_iff [CommMonoidWithZero M] {p q : M} (h : p ~ᵤ q) : Prime p ↔ Prime q :=
  ⟨h.prime, h.symm.prime⟩

protected theorem Associated.isUnit [Monoid M] {a b : M} (h : a ~ᵤ b) : IsUnit a → IsUnit b :=
  let ⟨u, hu⟩ := h
  fun ⟨v, hv⟩ => ⟨v * u, by simp [hv, hu.symm]⟩

theorem Associated.isUnit_iff [Monoid M] {a b : M} (h : a ~ᵤ b) : IsUnit a ↔ IsUnit b :=
  ⟨h.isUnit, h.symm.isUnit⟩

theorem Irreducible.isUnit_iff_not_associated_of_dvd [Monoid M]
    {x y : M} (hx : Irreducible x) (hy : y ∣ x) : IsUnit y ↔ ¬ Associated x y :=
  ⟨fun hy hxy => hx.1 (hxy.symm.isUnit hy), (hx.dvd_iff.mp hy).resolve_right⟩

protected theorem Associated.irreducible [Monoid M] {p q : M} (h : p ~ᵤ q) (hp : Irreducible p) :
    Irreducible q :=
  ⟨mt h.symm.isUnit hp.1,
    let ⟨u, hu⟩ := h
    fun a b hab =>
    have hpab : p = a * (b * (u⁻¹ : Mˣ)) :=
      calc
        p = p * u * (u⁻¹ : Mˣ) := by simp
        _ = _ := by rw [hu]; simp [hab, mul_assoc]
    (hp.isUnit_or_isUnit hpab).elim Or.inl fun ⟨v, hv⟩ => Or.inr ⟨v * u, by simp [hv]⟩⟩

protected theorem Associated.irreducible_iff [Monoid M] {p q : M} (h : p ~ᵤ q) :
    Irreducible p ↔ Irreducible q :=
  ⟨h.irreducible, h.symm.irreducible⟩

theorem Associated.of_mul_left [CancelCommMonoidWithZero M] {a b c d : M} (h : a * b ~ᵤ c * d)
    (h₁ : a ~ᵤ c) (ha : a ≠ 0) : b ~ᵤ d :=
  let ⟨u, hu⟩ := h
  let ⟨v, hv⟩ := Associated.symm h₁
  ⟨u * (v : Mˣ),
    mul_left_cancel₀ ha
      (by
        rw [← hv, mul_assoc c (v : M) d, mul_left_comm c, ← hu]
        simp [hv.symm, mul_comm, mul_left_comm])⟩

theorem Associated.of_mul_right [CancelCommMonoidWithZero M] {a b c d : M} :
    a * b ~ᵤ c * d → b ~ᵤ d → b ≠ 0 → a ~ᵤ c := by
  rw [mul_comm a, mul_comm c]; exact Associated.of_mul_left

theorem Associated.of_pow_associated_of_prime [CancelCommMonoidWithZero M] {p₁ p₂ : M} {k₁ k₂ : ℕ}
    (hp₁ : Prime p₁) (hp₂ : Prime p₂) (hk₁ : 0 < k₁) (h : p₁ ^ k₁ ~ᵤ p₂ ^ k₂) : p₁ ~ᵤ p₂ := by
  have : p₁ ∣ p₂ ^ k₂ := by
    rw [← h.dvd_iff_dvd_right]
    apply dvd_pow_self _ hk₁.ne'
  rw [← hp₁.dvd_prime_iff_associated hp₂]
  exact hp₁.dvd_of_dvd_pow this

theorem Associated.of_pow_associated_of_prime' [CancelCommMonoidWithZero M] {p₁ p₂ : M} {k₁ k₂ : ℕ}
    (hp₁ : Prime p₁) (hp₂ : Prime p₂) (hk₂ : 0 < k₂) (h : p₁ ^ k₁ ~ᵤ p₂ ^ k₂) : p₁ ~ᵤ p₂ :=
  (h.symm.of_pow_associated_of_prime hp₂ hp₁ hk₂).symm

/-- See also `Irreducible.coprime_iff_not_dvd`. -/
lemma Irreducible.isRelPrime_iff_not_dvd [Monoid M] {p n : M} (hp : Irreducible p) :
    IsRelPrime p n ↔ ¬ p ∣ n := by
  refine ⟨fun h contra ↦ hp.not_isUnit (h dvd_rfl contra), fun hpn d hdp hdn ↦ ?_⟩
  contrapose! hpn
  suffices Associated p d from this.dvd.trans hdn
  exact (hp.dvd_iff.mp hdp).resolve_left hpn

lemma Irreducible.dvd_or_isRelPrime [Monoid M] {p n : M} (hp : Irreducible p) :
    p ∣ n ∨ IsRelPrime p n := Classical.or_iff_not_imp_left.mpr hp.isRelPrime_iff_not_dvd.2

section UniqueUnits

variable [Monoid M] [Subsingleton Mˣ]

theorem associated_iff_eq {x y : M} : x ~ᵤ y ↔ x = y := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [units_eq_one c, Units.val_one, mul_one]
  · rintro rfl
    rfl

theorem associated_eq_eq : (Associated : M → M → Prop) = Eq := by
  ext
  rw [associated_iff_eq]

theorem prime_dvd_prime_iff_eq {M : Type*} [CancelCommMonoidWithZero M] [Subsingleton Mˣ] {p q : M}
    (pp : Prime p) (qp : Prime q) : p ∣ q ↔ p = q := by
  rw [pp.dvd_prime_iff_associated qp, ← associated_eq_eq]

end UniqueUnits

section UniqueUnits₀

variable {R : Type*} [CancelCommMonoidWithZero R] [Subsingleton Rˣ] {p₁ p₂ : R} {k₁ k₂ : ℕ}

theorem eq_of_prime_pow_eq (hp₁ : Prime p₁) (hp₂ : Prime p₂) (hk₁ : 0 < k₁)
    (h : p₁ ^ k₁ = p₂ ^ k₂) : p₁ = p₂ := by
  rw [← associated_iff_eq] at h ⊢
  apply h.of_pow_associated_of_prime hp₁ hp₂ hk₁

theorem eq_of_prime_pow_eq' (hp₁ : Prime p₁) (hp₂ : Prime p₂) (hk₁ : 0 < k₂)
    (h : p₁ ^ k₁ = p₂ ^ k₂) : p₁ = p₂ := by
  rw [← associated_iff_eq] at h ⊢
  apply h.of_pow_associated_of_prime' hp₁ hp₂ hk₁

end UniqueUnits₀

/-- The quotient of a monoid by the `Associated` relation. Two elements `x` and `y`
  are associated iff there is a unit `u` such that `x * u = y`. There is a natural
  monoid structure on `Associates M`. -/
abbrev Associates (M : Type*) [Monoid M] : Type _ :=
  Quotient (Associated.setoid M)

namespace Associates

open Associated

/-- The canonical quotient map from a monoid `M` into the `Associates` of `M` -/
protected abbrev mk {M : Type*} [Monoid M] (a : M) : Associates M :=
  ⟦a⟧

instance [Monoid M] : Inhabited (Associates M) :=
  ⟨⟦1⟧⟩

theorem mk_eq_mk_iff_associated [Monoid M] {a b : M} : Associates.mk a = Associates.mk b ↔ a ~ᵤ b :=
  Iff.intro Quotient.exact Quot.sound

theorem quotient_mk_eq_mk [Monoid M] (a : M) : ⟦a⟧ = Associates.mk a :=
  rfl

theorem quot_mk_eq_mk [Monoid M] (a : M) : Quot.mk Setoid.r a = Associates.mk a :=
  rfl

@[simp]
theorem quot_out [Monoid M] (a : Associates M) : Associates.mk (Quot.out a) = a := by
  rw [← quot_mk_eq_mk, Quot.out_eq]

theorem mk_quot_out [Monoid M] (a : M) : Quot.out (Associates.mk a) ~ᵤ a := by
  rw [← Associates.mk_eq_mk_iff_associated, Associates.quot_out]

theorem forall_associated [Monoid M] {p : Associates M → Prop} :
    (∀ a, p a) ↔ ∀ a, p (Associates.mk a) :=
  Iff.intro (fun h _ => h _) fun h a => Quotient.inductionOn a h

theorem mk_surjective [Monoid M] : Function.Surjective (@Associates.mk M _) :=
  forall_associated.2 fun a => ⟨a, rfl⟩

instance [Monoid M] : One (Associates M) :=
  ⟨⟦1⟧⟩

@[simp]
theorem mk_one [Monoid M] : Associates.mk (1 : M) = 1 :=
  rfl

theorem one_eq_mk_one [Monoid M] : (1 : Associates M) = Associates.mk 1 :=
  rfl

@[simp]
theorem mk_eq_one [Monoid M] {a : M} : Associates.mk a = 1 ↔ IsUnit a := by
  rw [← mk_one, mk_eq_mk_iff_associated, associated_one_iff_isUnit]

instance [Monoid M] : Bot (Associates M) :=
  ⟨1⟩

theorem bot_eq_one [Monoid M] : (⊥ : Associates M) = 1 :=
  rfl

theorem exists_rep [Monoid M] (a : Associates M) : ∃ a0 : M, Associates.mk a0 = a :=
  Quot.exists_rep a

instance [Monoid M] [Subsingleton M] :
    Unique (Associates M) where
  default := 1
  uniq := forall_associated.2 fun _ ↦ mk_eq_one.2 <| isUnit_of_subsingleton _

theorem mk_injective [Monoid M] [Subsingleton Mˣ] : Function.Injective (@Associates.mk M _) :=
  fun _ _ h => associated_iff_eq.mp (Associates.mk_eq_mk_iff_associated.mp h)

section CommMonoid

variable [CommMonoid M]

instance instMul : Mul (Associates M) :=
  ⟨Quotient.map₂ (· * ·) fun _ _ h₁ _ _ h₂ ↦ h₁.mul_mul h₂⟩

theorem mk_mul_mk {x y : M} : Associates.mk x * Associates.mk y = Associates.mk (x * y) :=
  rfl

instance instCommMonoid : CommMonoid (Associates M) where
  one := 1
  mul := (· * ·)
  mul_one a' := Quotient.inductionOn a' fun a => show ⟦a * 1⟧ = ⟦a⟧ by simp
  one_mul a' := Quotient.inductionOn a' fun a => show ⟦1 * a⟧ = ⟦a⟧ by simp
  mul_assoc a' b' c' :=
    Quotient.inductionOn₃ a' b' c' fun a b c =>
      show ⟦a * b * c⟧ = ⟦a * (b * c)⟧ by rw [mul_assoc]
  mul_comm a' b' :=
    Quotient.inductionOn₂ a' b' fun a b => show ⟦a * b⟧ = ⟦b * a⟧ by rw [mul_comm]

instance instPreorder : Preorder (Associates M) where
  le := Dvd.dvd
  le_refl := dvd_refl
  le_trans _ _ _ := dvd_trans

/-- `Associates.mk` as a `MonoidHom`. -/
protected def mkMonoidHom : M →* Associates M where
  toFun := Associates.mk
  map_one' := mk_one
  map_mul' _ _ := mk_mul_mk

@[simp]
theorem mkMonoidHom_apply (a : M) : Associates.mkMonoidHom a = Associates.mk a :=
  rfl

theorem associated_map_mk {f : Associates M →* M} (hinv : Function.RightInverse f Associates.mk)
    (a : M) : a ~ᵤ f (Associates.mk a) :=
  Associates.mk_eq_mk_iff_associated.1 (hinv (Associates.mk a)).symm

theorem mk_pow (a : M) (n : ℕ) : Associates.mk (a ^ n) = Associates.mk a ^ n := by
  induction n <;> simp [*, pow_succ, Associates.mk_mul_mk.symm]

theorem dvd_eq_le : ((· ∣ ·) : Associates M → Associates M → Prop) = (· ≤ ·) :=
  rfl

instance uniqueUnits : Unique (Associates M)ˣ where
  uniq := by
    rintro ⟨a, b, hab, hba⟩
    revert hab hba
    exact Quotient.inductionOn₂ a b <| fun a b hab hba ↦ Units.ext <| Quotient.sound <|
      associated_one_of_associated_mul_one <| Quotient.exact hab

@[simp]
theorem coe_unit_eq_one (u : (Associates M)ˣ) : (u : Associates M) = 1 := by
  simp [eq_iff_true_of_subsingleton]

theorem isUnit_iff_eq_one (a : Associates M) : IsUnit a ↔ a = 1 :=
  Iff.intro (fun ⟨_, h⟩ => h ▸ coe_unit_eq_one _) fun h => h.symm ▸ isUnit_one

theorem isUnit_iff_eq_bot {a : Associates M} : IsUnit a ↔ a = ⊥ := by
  rw [Associates.isUnit_iff_eq_one, bot_eq_one]

theorem isUnit_mk {a : M} : IsUnit (Associates.mk a) ↔ IsUnit a :=
  calc
    IsUnit (Associates.mk a) ↔ a ~ᵤ 1 := by
      rw [isUnit_iff_eq_one, one_eq_mk_one, mk_eq_mk_iff_associated]
    _ ↔ IsUnit a := associated_one_iff_isUnit

section Order

theorem mul_mono {a b c d : Associates M} (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
  let ⟨x, hx⟩ := h₁
  let ⟨y, hy⟩ := h₂
  ⟨x * y, by simp [hx, hy, mul_comm, mul_left_comm]⟩

theorem one_le {a : Associates M} : 1 ≤ a :=
  Dvd.intro _ (one_mul a)

theorem le_mul_right {a b : Associates M} : a ≤ a * b :=
  ⟨b, rfl⟩

theorem le_mul_left {a b : Associates M} : a ≤ b * a := by rw [mul_comm]; exact le_mul_right

instance instOrderBot : OrderBot (Associates M) where
  bot := 1
  bot_le _ := one_le

end Order

@[simp]
theorem mk_dvd_mk {a b : M} : Associates.mk a ∣ Associates.mk b ↔ a ∣ b := by
  simp only [dvd_def, mk_surjective.exists, mk_mul_mk, mk_eq_mk_iff_associated,
    Associated.comm (x := b)]
  constructor
  · rintro ⟨x, u, rfl⟩
    exact ⟨_, mul_assoc ..⟩
  · rintro ⟨c, rfl⟩
    use c

theorem dvd_of_mk_le_mk {a b : M} : Associates.mk a ≤ Associates.mk b → a ∣ b :=
  mk_dvd_mk.mp

theorem mk_le_mk_of_dvd {a b : M} : a ∣ b → Associates.mk a ≤ Associates.mk b :=
  mk_dvd_mk.mpr

theorem mk_le_mk_iff_dvd {a b : M} : Associates.mk a ≤ Associates.mk b ↔ a ∣ b := mk_dvd_mk


@[simp]
theorem isPrimal_mk {a : M} : IsPrimal (Associates.mk a) ↔ IsPrimal a := by
  simp_rw [IsPrimal, forall_associated, mk_surjective.exists, mk_mul_mk, mk_dvd_mk]
  constructor <;> intro h b c dvd <;> obtain ⟨a₁, a₂, h₁, h₂, eq⟩ := @h b c dvd
  · obtain ⟨u, rfl⟩ := mk_eq_mk_iff_associated.mp eq.symm
    exact ⟨a₁, a₂ * u, h₁, Units.mul_right_dvd.mpr h₂, mul_assoc _ _ _⟩
  · exact ⟨a₁, a₂, h₁, h₂, congr_arg _ eq⟩


@[simp]
theorem decompositionMonoid_iff : DecompositionMonoid (Associates M) ↔ DecompositionMonoid M := by
  simp_rw [_root_.decompositionMonoid_iff, forall_associated, isPrimal_mk]

instance instDecompositionMonoid [DecompositionMonoid M] : DecompositionMonoid (Associates M) :=
  decompositionMonoid_iff.mpr ‹_›

@[simp]
theorem mk_isRelPrime_iff {a b : M} :
    IsRelPrime (Associates.mk a) (Associates.mk b) ↔ IsRelPrime a b := by
  simp_rw [IsRelPrime, forall_associated, mk_dvd_mk, isUnit_mk]

end CommMonoid

instance [Zero M] [Monoid M] : Zero (Associates M) :=
  ⟨⟦0⟧⟩

instance [Zero M] [Monoid M] : Top (Associates M) :=
  ⟨0⟩

@[simp] theorem mk_zero [Zero M] [Monoid M] : Associates.mk (0 : M) = 0 := rfl

section MonoidWithZero

variable [MonoidWithZero M]

@[simp]
theorem mk_eq_zero {a : M} : Associates.mk a = 0 ↔ a = 0 :=
  ⟨fun h => (associated_zero_iff_eq_zero a).1 <| Quotient.exact h, fun h => h.symm ▸ rfl⟩

@[simp]
theorem quot_out_zero : Quot.out (0 : Associates M) = 0 := by rw [← mk_eq_zero, quot_out]

theorem mk_ne_zero {a : M} : Associates.mk a ≠ 0 ↔ a ≠ 0 :=
  not_congr mk_eq_zero

instance [Nontrivial M] : Nontrivial (Associates M) :=
  ⟨⟨1, 0, mk_ne_zero.2 one_ne_zero⟩⟩

theorem exists_non_zero_rep {a : Associates M} : a ≠ 0 → ∃ a0 : M, a0 ≠ 0 ∧ Associates.mk a0 = a :=
  Quotient.inductionOn a fun b nz => ⟨b, mt (congr_arg Quotient.mk'') nz, rfl⟩

end MonoidWithZero

section CommMonoidWithZero

variable [CommMonoidWithZero M]

instance instCommMonoidWithZero : CommMonoidWithZero (Associates M) where
    zero_mul := forall_associated.2 fun a ↦ by rw [← mk_zero, mk_mul_mk, zero_mul]
    mul_zero := forall_associated.2 fun a ↦ by rw [← mk_zero, mk_mul_mk, mul_zero]

instance instOrderTop : OrderTop (Associates M) where
  top := 0
  le_top := dvd_zero

@[simp] protected theorem le_zero (a : Associates M) : a ≤ 0 := le_top

instance instBoundedOrder : BoundedOrder (Associates M) where

instance [DecidableRel ((· ∣ ·) : M → M → Prop)] :
    DecidableRel ((· ∣ ·) : Associates M → Associates M → Prop) := fun a b =>
  Quotient.recOnSubsingleton₂ a b fun _ _ => decidable_of_iff' _ mk_dvd_mk

theorem Prime.le_or_le {p : Associates M} (hp : Prime p) {a b : Associates M} (h : p ≤ a * b) :
    p ≤ a ∨ p ≤ b :=
  hp.2.2 a b h

@[simp]
theorem prime_mk {p : M} : Prime (Associates.mk p) ↔ Prime p := by
  rw [Prime, _root_.Prime, forall_associated]
  simp only [forall_associated, mk_ne_zero, isUnit_mk, mk_mul_mk, mk_dvd_mk]

@[simp]
theorem irreducible_mk {a : M} : Irreducible (Associates.mk a) ↔ Irreducible a := by
  simp only [irreducible_iff, isUnit_mk, forall_associated, isUnit_mk, mk_mul_mk,
    mk_eq_mk_iff_associated, Associated.comm (x := a)]
  apply Iff.rfl.and
  constructor
  · rintro h x y rfl
    exact h _ _ <| .refl _
  · rintro h x y ⟨u, rfl⟩
    simpa using h (mul_assoc _ _ _)

@[simp]
theorem mk_dvdNotUnit_mk_iff {a b : M} :
    DvdNotUnit (Associates.mk a) (Associates.mk b) ↔ DvdNotUnit a b := by
  simp only [DvdNotUnit, mk_ne_zero, mk_surjective.exists, isUnit_mk, mk_mul_mk,
    mk_eq_mk_iff_associated, Associated.comm (x := b)]
  refine Iff.rfl.and ?_
  constructor
  · rintro ⟨x, hx, u, rfl⟩
    refine ⟨x * u, ?_, mul_assoc ..⟩
    simpa
  · rintro ⟨x, ⟨hx, rfl⟩⟩
    use x

theorem dvdNotUnit_of_lt {a b : Associates M} (hlt : a < b) : DvdNotUnit a b := by
  constructor
  · rintro rfl
    apply not_lt_of_ge _ hlt
    apply dvd_zero
  rcases hlt with ⟨⟨x, rfl⟩, ndvd⟩
  refine ⟨x, ?_, rfl⟩
  contrapose! ndvd
  rcases ndvd with ⟨u, rfl⟩
  simp

theorem irreducible_iff_prime_iff :
    (∀ a : M, Irreducible a ↔ Prime a) ↔ ∀ a : Associates M, Irreducible a ↔ Prime a := by
  simp_rw [forall_associated, irreducible_mk, prime_mk]

end CommMonoidWithZero

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero M]

instance instPartialOrder : PartialOrder (Associates M) where
  le_antisymm := mk_surjective.forall₂.2 fun _a _b hab hba => mk_eq_mk_iff_associated.2 <|
    associated_of_dvd_dvd (dvd_of_mk_le_mk hab) (dvd_of_mk_le_mk hba)

instance instCancelCommMonoidWithZero : CancelCommMonoidWithZero (Associates M) :=
  { (by infer_instance : CommMonoidWithZero (Associates M)) with
    mul_left_cancel_of_ne_zero := by
      rintro ⟨a⟩ ha ⟨b⟩ ⟨c⟩ h
      rcases Quotient.exact' h with ⟨u, hu⟩
      have hu : a * (b * ↑u) = a * c := by rwa [← mul_assoc]
      exact Quotient.sound' ⟨u, mul_left_cancel₀ (mk_ne_zero.1 ha) hu⟩ }

theorem _root_.associates_irreducible_iff_prime [DecompositionMonoid M] {p : Associates M} :
    Irreducible p ↔ Prime p := irreducible_iff_prime

instance : NoZeroDivisors (Associates M) := by infer_instance

theorem le_of_mul_le_mul_left (a b c : Associates M) (ha : a ≠ 0) : a * b ≤ a * c → b ≤ c
  | ⟨d, hd⟩ => ⟨d, mul_left_cancel₀ ha <| by rwa [← mul_assoc]⟩

theorem one_or_eq_of_le_of_prime {p m : Associates M} (hp : Prime p) (hle : m ≤ p) :
    m = 1 ∨ m = p := by
  rcases mk_surjective p with ⟨p, rfl⟩
  rcases mk_surjective m with ⟨m, rfl⟩
  simpa [mk_eq_mk_iff_associated, Associated.comm, -Quotient.eq]
    using (prime_mk.1 hp).irreducible.dvd_iff.mp (mk_le_mk_iff_dvd.1 hle)

theorem dvdNotUnit_iff_lt {a b : Associates M} : DvdNotUnit a b ↔ a < b :=
  dvd_and_not_dvd_iff.symm

theorem le_one_iff {p : Associates M} : p ≤ 1 ↔ p = 1 := by rw [← Associates.bot_eq_one, le_bot_iff]

end CancelCommMonoidWithZero

end Associates

section CommMonoidWithZero

theorem dvdNotUnit_of_dvdNotUnit_associated [CommMonoidWithZero M] [Nontrivial M] {p q r : M}
    (h : DvdNotUnit p q) (h' : Associated q r) : DvdNotUnit p r := by
  obtain ⟨u, rfl⟩ := Associated.symm h'
  obtain ⟨hp, x, hx⟩ := h
  refine ⟨hp, x * ↑u⁻¹, DvdNotUnit.not_unit ⟨u⁻¹.ne_zero, x, hx.left, mul_comm _ _⟩, ?_⟩
  rw [← mul_assoc, ← hx.right, mul_assoc, Units.mul_inv, mul_one]

end CommMonoidWithZero

section CancelCommMonoidWithZero

theorem isUnit_of_associated_mul [CancelCommMonoidWithZero M] {p b : M} (h : Associated (p * b) p)
    (hp : p ≠ 0) : IsUnit b := by
  obtain ⟨a, ha⟩ := h
  refine isUnit_of_mul_eq_one b a ((mul_right_inj' hp).mp ?_)
  rwa [← mul_assoc, mul_one]

theorem DvdNotUnit.not_associated [CancelCommMonoidWithZero M] {p q : M} (h : DvdNotUnit p q) :
    ¬Associated p q := by
  rintro ⟨a, rfl⟩
  obtain ⟨hp, x, hx, hx'⟩ := h
  rcases (mul_right_inj' hp).mp hx' with rfl
  exact hx a.isUnit

theorem dvd_prime_pow [CancelCommMonoidWithZero M] {p q : M} (hp : Prime p) (n : ℕ) :
    q ∣ p ^ n ↔ ∃ i ≤ n, Associated q (p ^ i) := by
  induction n generalizing q with
  | zero =>
    simp [← isUnit_iff_dvd_one, associated_one_iff_isUnit]
  | succ n ih =>
    refine ⟨fun h => ?_, fun ⟨i, hi, hq⟩ => hq.dvd.trans (pow_dvd_pow p hi)⟩
    rw [pow_succ'] at h
    rcases hp.left_dvd_or_dvd_right_of_dvd_mul h with (⟨q, rfl⟩ | hno)
    · rw [mul_dvd_mul_iff_left hp.ne_zero, ih] at h
      rcases h with ⟨i, hi, hq⟩
      refine ⟨i + 1, Nat.succ_le_succ hi, (hq.mul_left p).trans ?_⟩
      rw [pow_succ']
    · obtain ⟨i, hi, hq⟩ := ih.mp hno
      exact ⟨i, hi.trans n.le_succ, hq⟩

end CancelCommMonoidWithZero
