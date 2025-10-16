/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.ENat.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-!
# Basic results un unique factorization monoids

## Main results
* `prime_factors_unique`: the prime factors of an element in a cancellative
  commutative monoid with zero (e.g. an integral domain) are unique up to associates
* `UniqueFactorizationMonoid.factors_unique`: the irreducible factors of an element
  in a unique factorization monoid (e.g. a UFD) are unique up to associates
* `UniqueFactorizationMonoid.iff_exists_prime_factors`: unique factorization exists iff each nonzero
  elements factors into a product of primes
* `UniqueFactorizationMonoid.dvd_of_dvd_mul_left_of_no_prime_factors`: Euclid's lemma:
  if `a ∣ b * c` and `a` and `c` have no common prime factors, `a ∣ b`.
* `UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors`: Euclid's lemma:
  if `a ∣ b * c` and `a` and `b` have no common prime factors, `a ∣ c`.
* `UniqueFactorizationMonoid.exists_reduced_factors`: in a UFM, we can divide out a common factor
  to get relatively prime elements.
-/

assert_not_exists Field

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

namespace WfDvdMonoid

variable [CommMonoidWithZero α]

open Associates Nat

theorem of_wfDvdMonoid_associates (_ : WfDvdMonoid (Associates α)) : WfDvdMonoid α :=
  ⟨(mk_surjective.wellFounded_iff mk_dvdNotUnit_mk_iff.symm).2 wellFounded_dvdNotUnit⟩

variable [WfDvdMonoid α]

instance wfDvdMonoid_associates : WfDvdMonoid (Associates α) :=
  ⟨(mk_surjective.wellFounded_iff mk_dvdNotUnit_mk_iff.symm).1 wellFounded_dvdNotUnit⟩

theorem wellFoundedLT_associates : WellFoundedLT (Associates α) :=
  ⟨Subrelation.wf dvdNotUnit_of_lt wellFounded_dvdNotUnit⟩

end WfDvdMonoid

theorem WfDvdMonoid.of_wellFoundedLT_associates [CancelCommMonoidWithZero α]
    (h : WellFoundedLT (Associates α)) : WfDvdMonoid α :=
  WfDvdMonoid.of_wfDvdMonoid_associates
    ⟨by
      convert h.wf
      ext
      exact Associates.dvdNotUnit_iff_lt⟩

theorem WfDvdMonoid.iff_wellFounded_associates [CancelCommMonoidWithZero α] :
    WfDvdMonoid α ↔ WellFoundedLT (Associates α) :=
  ⟨by apply WfDvdMonoid.wellFoundedLT_associates, WfDvdMonoid.of_wellFoundedLT_associates⟩

instance Associates.ufm [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α] :
    UniqueFactorizationMonoid (Associates α) :=
  { (WfDvdMonoid.wfDvdMonoid_associates : WfDvdMonoid (Associates α)) with
    irreducible_iff_prime := by
      rw [← Associates.irreducible_iff_prime_iff]
      apply UniqueFactorizationMonoid.irreducible_iff_prime }

theorem prime_factors_unique [CancelCommMonoidWithZero α] :
    ∀ {f g : Multiset α},
      (∀ x ∈ f, Prime x) → (∀ x ∈ g, Prime x) → f.prod ~ᵤ g.prod → Multiset.Rel Associated f g := by
  classical
  intro f
  induction f using Multiset.induction_on with
  | empty =>
    intro g _ hg h
    exact Multiset.rel_zero_left.2 <|
      Multiset.eq_zero_of_forall_notMem fun x hx =>
        have : IsUnit g.prod := by simpa [associated_one_iff_isUnit] using h.symm
        (hg x hx).not_unit <|
          isUnit_iff_dvd_one.2 <| (Multiset.dvd_prod hx).trans (isUnit_iff_dvd_one.1 this)
  | cons p f ih =>
    intro g hf hg hfg
    let ⟨b, hbg, hb⟩ :=
      (exists_associated_mem_of_dvd_prod (hf p (by simp)) fun q hq => hg _ hq) <|
        hfg.dvd_iff_dvd_right.1 (show p ∣ (p ::ₘ f).prod by simp)
    haveI := Classical.decEq α
    rw [← Multiset.cons_erase hbg]
    exact
      Multiset.Rel.cons hb
        (ih (fun q hq => hf _ (by simp [hq]))
          (fun {q} (hq : q ∈ g.erase b) => hg q (Multiset.mem_of_mem_erase hq))
          (Associated.of_mul_left
            (by rwa [← Multiset.prod_cons, ← Multiset.prod_cons, Multiset.cons_erase hbg]) hb
            (hf p (by simp)).ne_zero))

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α]

theorem factors_unique {f g : Multiset α} (hf : ∀ x ∈ f, Irreducible x)
    (hg : ∀ x ∈ g, Irreducible x) (h : f.prod ~ᵤ g.prod) : Multiset.Rel Associated f g :=
  prime_factors_unique (fun x hx => UniqueFactorizationMonoid.irreducible_iff_prime.mp (hf x hx))
    (fun x hx => UniqueFactorizationMonoid.irreducible_iff_prime.mp (hg x hx)) h

end UniqueFactorizationMonoid

/-- If an irreducible has a prime factorization,
  then it is an associate of one of its prime factors. -/
theorem prime_factors_irreducible [CommMonoidWithZero α] {a : α} {f : Multiset α}
    (ha : Irreducible a) (pfa : (∀ b ∈ f, Prime b) ∧ f.prod ~ᵤ a) : ∃ p, a ~ᵤ p ∧ f = {p} := by
  haveI := Classical.decEq α
  refine @Multiset.induction_on _
    (fun g => (g.prod ~ᵤ a) → (∀ b ∈ g, Prime b) → ∃ p, a ~ᵤ p ∧ g = {p}) f ?_ ?_ pfa.2 pfa.1
  · intro h; exact (ha.not_isUnit (associated_one_iff_isUnit.1 (Associated.symm h))).elim
  · rintro p s _ ⟨u, hu⟩ hs
    use p
    have hs0 : s = 0 := by
      by_contra hs0
      obtain ⟨q, hq⟩ := Multiset.exists_mem_of_ne_zero hs0
      apply (hs q (by simp [hq])).2.1
      refine (ha.isUnit_or_isUnit (?_ : _ = p * ↑u * (s.erase q).prod * _)).resolve_left ?_
      · rw [mul_right_comm _ _ q, mul_assoc, ← Multiset.prod_cons, Multiset.cons_erase hq, ← hu,
          mul_comm, mul_comm p _, mul_assoc]
        simp
      apply mt isUnit_of_mul_isUnit_left (mt isUnit_of_mul_isUnit_left _)
      apply (hs p (Multiset.mem_cons_self _ _)).2.1
    simp only [mul_one, Multiset.prod_cons, Multiset.prod_zero, hs0] at *
    exact ⟨Associated.symm ⟨u, hu⟩, rfl⟩

theorem irreducible_iff_prime_of_existsUnique_irreducible_factors [CancelCommMonoidWithZero α]
    (eif : ∀ a : α, a ≠ 0 → ∃ f : Multiset α, (∀ b ∈ f, Irreducible b) ∧ f.prod ~ᵤ a)
    (uif :
      ∀ f g : Multiset α,
        (∀ x ∈ f, Irreducible x) →
          (∀ x ∈ g, Irreducible x) → f.prod ~ᵤ g.prod → Multiset.Rel Associated f g)
    (p : α) : Irreducible p ↔ Prime p :=
  letI := Classical.decEq α
  ⟨ fun hpi =>
    ⟨hpi.ne_zero, hpi.1, fun a b ⟨x, hx⟩ =>
      if hab0 : a * b = 0 then
        (eq_zero_or_eq_zero_of_mul_eq_zero hab0).elim (fun ha0 => by simp [ha0]) fun hb0 => by
          simp [hb0]
      else by
        have hx0 : x ≠ 0 := fun hx0 => by simp_all
        have ha0 : a ≠ 0 := left_ne_zero_of_mul hab0
        have hb0 : b ≠ 0 := right_ne_zero_of_mul hab0
        obtain ⟨fx, hfx⟩ := eif x hx0
        obtain ⟨fa, hfa⟩ := eif a ha0
        obtain ⟨fb, hfb⟩ := eif b hb0
        have h : Multiset.Rel Associated (p ::ₘ fx) (fa + fb) := by
          apply uif
          · exact fun i hi => (Multiset.mem_cons.1 hi).elim (fun hip => hip.symm ▸ hpi) (hfx.1 _)
          · exact fun i hi => (Multiset.mem_add.1 hi).elim (hfa.1 _) (hfb.1 _)
          calc
            Multiset.prod (p ::ₘ fx) ~ᵤ a * b := by
              rw [hx, Multiset.prod_cons]; exact hfx.2.mul_left _
            _ ~ᵤ fa.prod * fb.prod := hfa.2.symm.mul_mul hfb.2.symm
            _ = _ := by rw [Multiset.prod_add]
        exact
          let ⟨q, hqf, hq⟩ := Multiset.exists_mem_of_rel_of_mem h (Multiset.mem_cons_self p _)
          (Multiset.mem_add.1 hqf).elim
            (fun hqa =>
              Or.inl <| hq.dvd_iff_dvd_left.2 <| hfa.2.dvd_iff_dvd_right.1 (Multiset.dvd_prod hqa))
            fun hqb =>
            Or.inr <| hq.dvd_iff_dvd_left.2 <| hfb.2.dvd_iff_dvd_right.1 (Multiset.dvd_prod hqb)⟩,
    Prime.irreducible⟩

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero α]
variable [UniqueFactorizationMonoid α]

@[simp]
theorem factors_one : factors (1 : α) = 0 := by
  nontriviality α using factors
  rw [← Multiset.rel_zero_right]
  refine factors_unique irreducible_of_factor (fun x hx => (Multiset.notMem_zero x hx).elim) ?_
  rw [Multiset.prod_zero]
  exact factors_prod one_ne_zero

theorem exists_mem_factors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) :
    p ∣ a → ∃ q ∈ factors a, p ~ᵤ q := fun ⟨b, hb⟩ =>
  have hb0 : b ≠ 0 := fun hb0 => by simp_all
  have : Multiset.Rel Associated (p ::ₘ factors b) (factors a) :=
    factors_unique
      (fun _ hx => (Multiset.mem_cons.1 hx).elim (fun h => h.symm ▸ hp) (irreducible_of_factor _))
      irreducible_of_factor
      (Associated.symm <|
        calc
          Multiset.prod (factors a) ~ᵤ a := factors_prod ha0
          _ = p * b := hb
          _ ~ᵤ Multiset.prod (p ::ₘ factors b) := by
            rw [Multiset.prod_cons]; exact (factors_prod hb0).symm.mul_left _
          )
  Multiset.exists_mem_of_rel_of_mem this (by simp)

theorem exists_mem_factors {x : α} (hx : x ≠ 0) (h : ¬IsUnit x) : ∃ p, p ∈ factors x := by
  obtain ⟨p', hp', hp'x⟩ := WfDvdMonoid.exists_irreducible_factor h hx
  obtain ⟨p, hp, _⟩ := exists_mem_factors_of_dvd hx hp' hp'x
  exact ⟨p, hp⟩

open Classical in
theorem factors_mul {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
    Multiset.Rel Associated (factors (x * y)) (factors x + factors y) := by
  refine
    factors_unique irreducible_of_factor
      (fun a ha =>
        (Multiset.mem_add.mp ha).by_cases (irreducible_of_factor _) (irreducible_of_factor _))
      ((factors_prod (mul_ne_zero hx hy)).trans ?_)
  rw [Multiset.prod_add]
  exact (Associated.mul_mul (factors_prod hx) (factors_prod hy)).symm

theorem factors_pow {x : α} (n : ℕ) :
    Multiset.Rel Associated (factors (x ^ n)) (n • factors x) := by
  match n with
  | 0 => rw [zero_nsmul, pow_zero, factors_one, Multiset.rel_zero_right]
  | n + 1 =>
    by_cases h0 : x = 0
    · simp [h0, zero_pow n.succ_ne_zero, nsmul_zero]
    · rw [pow_succ', succ_nsmul']
      refine Multiset.Rel.trans _ (factors_mul h0 (pow_ne_zero n h0)) ?_
      refine Multiset.Rel.add ?_ <| factors_pow n
      exact Multiset.rel_refl_of_refl_on fun y _ => Associated.refl _

@[simp]
theorem factors_pos (x : α) (hx : x ≠ 0) : 0 < factors x ↔ ¬IsUnit x := by
  constructor
  · intro h hx
    obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero h.ne'
    exact (prime_of_factor _ hp).not_unit (isUnit_of_dvd_unit (dvd_of_mem_factors hp) hx)
  · intro h
    obtain ⟨p, hp⟩ := exists_mem_factors hx h
    exact
      bot_lt_iff_ne_bot.mpr
        (mt Multiset.eq_zero_iff_forall_notMem.mp (not_forall.mpr ⟨p, not_not.mpr hp⟩))

open Multiset in
theorem factors_pow_count_prod [DecidableEq α] {x : α} (hx : x ≠ 0) :
    (∏ p ∈ (factors x).toFinset, p ^ (factors x).count p) ~ᵤ x :=
  calc
  _ = prod (∑ a ∈ toFinset (factors x), count a (factors x) • {a}) := by
    simp only [prod_sum, prod_nsmul, prod_singleton]
  _ = prod (factors x) := by rw [toFinset_sum_count_nsmul_eq (factors x)]
  _ ~ᵤ x := factors_prod hx

theorem factors_rel_of_associated {a b : α} (h : Associated a b) :
    Multiset.Rel Associated (factors a) (factors b) := by
  rcases iff_iff_and_or_not_and_not.mp h.eq_zero_iff with (⟨rfl, rfl⟩ | ⟨ha, hb⟩)
  · simp
  · refine factors_unique irreducible_of_factor irreducible_of_factor ?_
    exact ((factors_prod ha).trans h).trans (factors_prod hb).symm

end UniqueFactorizationMonoid

namespace Associates

attribute [local instance] Associated.setoid

open Multiset UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α]

theorem unique' {p q : Multiset (Associates α)} :
    (∀ a ∈ p, Irreducible a) → (∀ a ∈ q, Irreducible a) → p.prod = q.prod → p = q := by
  apply Multiset.induction_on_multiset_quot p
  apply Multiset.induction_on_multiset_quot q
  intro s t hs ht eq
  refine Multiset.map_mk_eq_map_mk_of_rel (UniqueFactorizationMonoid.factors_unique ?_ ?_ ?_)
  · exact fun a ha => irreducible_mk.1 <| hs _ <| Multiset.mem_map_of_mem _ ha
  · exact fun a ha => irreducible_mk.1 <| ht _ <| Multiset.mem_map_of_mem _ ha
  have eq' : (Quot.mk Setoid.r : α → Associates α) = Associates.mk := funext quot_mk_eq_mk
  rwa [eq', prod_mk, prod_mk, mk_eq_mk_iff_associated] at eq

theorem prod_le_prod_iff_le [Nontrivial α] {p q : Multiset (Associates α)}
    (hp : ∀ a ∈ p, Irreducible a) (hq : ∀ a ∈ q, Irreducible a) : p.prod ≤ q.prod ↔ p ≤ q := by
  refine ⟨?_, prod_le_prod⟩
  rintro ⟨c, eqc⟩
  refine Multiset.le_iff_exists_add.2 ⟨factors c, unique' hq (fun x hx ↦ ?_) ?_⟩
  · obtain h | h := Multiset.mem_add.1 hx
    · exact hp x h
    · exact irreducible_of_factor _ h
  · rw [eqc, Multiset.prod_add]
    congr
    refine associated_iff_eq.mp (factors_prod fun hc => ?_).symm
    refine not_irreducible_zero (hq _ ?_)
    rw [← prod_eq_zero_iff, eqc, hc, mul_zero]

end Associates

section ExistsPrimeFactors

variable [CancelCommMonoidWithZero α]
variable (pf : ∀ a : α, a ≠ 0 → ∃ f : Multiset α, (∀ b ∈ f, Prime b) ∧ f.prod ~ᵤ a)
include pf

theorem WfDvdMonoid.of_exists_prime_factors : WfDvdMonoid α :=
  ⟨by
    classical
      refine RelHomClass.wellFounded
        (RelHom.mk ?_ ?_ : (DvdNotUnit : α → α → Prop) →r ((· < ·) : ℕ∞ → ℕ∞ → Prop)) wellFounded_lt
      · intro a
        by_cases h : a = 0
        · exact ⊤
        exact ↑(Multiset.card (Classical.choose (pf a h)))
      rintro a b ⟨ane0, ⟨c, hc, b_eq⟩⟩
      rw [dif_neg ane0]
      by_cases h : b = 0
      · simp [h, lt_top_iff_ne_top]
      · rw [dif_neg h, Nat.cast_lt]
        have cne0 : c ≠ 0 := by
          refine mt (fun con => ?_) h
          rw [b_eq, con, mul_zero]
        calc
          Multiset.card (Classical.choose (pf a ane0)) <
              _ + Multiset.card (Classical.choose (pf c cne0)) :=
            lt_add_of_pos_right _
              (Multiset.card_pos.mpr fun con => hc (associated_one_iff_isUnit.mp ?_))
          _ = Multiset.card (Classical.choose (pf a ane0) + Classical.choose (pf c cne0)) :=
            (Multiset.card_add _ _).symm
          _ = Multiset.card (Classical.choose (pf b h)) :=
            Multiset.card_eq_card_of_rel
            (prime_factors_unique ?_ (Classical.choose_spec (pf _ h)).1 ?_)
        · convert (Classical.choose_spec (pf c cne0)).2.symm
          rw [con, Multiset.prod_zero]
        · intro x hadd
          rw [Multiset.mem_add] at hadd
          rcases hadd with h | h <;> apply (Classical.choose_spec (pf _ _)).1 _ h <;> assumption
        · rw [Multiset.prod_add]
          trans a * c
          · apply Associated.mul_mul <;> apply (Classical.choose_spec (pf _ _)).2 <;> assumption
          · rw [← b_eq]
            apply (Classical.choose_spec (pf _ _)).2.symm; assumption⟩

theorem irreducible_iff_prime_of_exists_prime_factors {p : α} : Irreducible p ↔ Prime p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  refine ⟨fun h => ?_, Prime.irreducible⟩
  obtain ⟨f, hf⟩ := pf p hp0
  obtain ⟨q, hq, rfl⟩ := prime_factors_irreducible h hf
  rw [hq.prime_iff]
  exact hf.1 q (Multiset.mem_singleton_self _)

theorem UniqueFactorizationMonoid.of_exists_prime_factors : UniqueFactorizationMonoid α :=
  { WfDvdMonoid.of_exists_prime_factors pf with
    irreducible_iff_prime := irreducible_iff_prime_of_exists_prime_factors pf }

end ExistsPrimeFactors

theorem UniqueFactorizationMonoid.iff_exists_prime_factors [CancelCommMonoidWithZero α] :
    UniqueFactorizationMonoid α ↔
      ∀ a : α, a ≠ 0 → ∃ f : Multiset α, (∀ b ∈ f, Prime b) ∧ f.prod ~ᵤ a :=
  ⟨fun h => @UniqueFactorizationMonoid.exists_prime_factors _ _ h,
    UniqueFactorizationMonoid.of_exists_prime_factors⟩

section

variable {β : Type*} [CancelCommMonoidWithZero α] [CancelCommMonoidWithZero β]

theorem MulEquiv.uniqueFactorizationMonoid (e : α ≃* β) (hα : UniqueFactorizationMonoid α) :
    UniqueFactorizationMonoid β := by
  rw [UniqueFactorizationMonoid.iff_exists_prime_factors] at hα ⊢
  intro a ha
  obtain ⟨w, hp, u, h⟩ :=
    hα (e.symm a) fun h =>
      ha <| by
        convert← map_zero e
        simp [← h]
  exact
    ⟨w.map e, fun b hb =>
        let ⟨c, hc, he⟩ := Multiset.mem_map.1 hb
        he ▸ (prime_iff e).2 (hp c hc),
        Units.map e.toMonoidHom u,
      by
        rw [Multiset.prod_hom, toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, ← map_mul e, h,
          apply_symm_apply]⟩

theorem MulEquiv.uniqueFactorizationMonoid_iff (e : α ≃* β) :
    UniqueFactorizationMonoid α ↔ UniqueFactorizationMonoid β :=
  ⟨e.uniqueFactorizationMonoid, e.symm.uniqueFactorizationMonoid⟩

end

namespace UniqueFactorizationMonoid

theorem of_existsUnique_irreducible_factors [CancelCommMonoidWithZero α]
    (eif : ∀ a : α, a ≠ 0 → ∃ f : Multiset α, (∀ b ∈ f, Irreducible b) ∧ f.prod ~ᵤ a)
    (uif :
      ∀ f g : Multiset α,
        (∀ x ∈ f, Irreducible x) →
          (∀ x ∈ g, Irreducible x) → f.prod ~ᵤ g.prod → Multiset.Rel Associated f g) :
    UniqueFactorizationMonoid α :=
  UniqueFactorizationMonoid.of_exists_prime_factors
    (by
      convert eif using 7
      simp_rw [irreducible_iff_prime_of_existsUnique_irreducible_factors eif uif])

variable {R : Type*} [CancelCommMonoidWithZero R] [UniqueFactorizationMonoid R]

theorem isRelPrime_iff_no_prime_factors {a b : R} (ha : a ≠ 0) :
    IsRelPrime a b ↔ ∀ ⦃d⦄, d ∣ a → d ∣ b → ¬Prime d :=
  ⟨fun h _ ha hb ↦ (·.not_unit <| h ha hb), fun h ↦ WfDvdMonoid.isRelPrime_of_no_irreducible_factors
    (ha ·.1) fun _ irr ha hb ↦ h ha hb (UniqueFactorizationMonoid.irreducible_iff_prime.mp irr)⟩

/-- Euclid's lemma: if `a ∣ b * c` and `a` and `c` have no common prime factors, `a ∣ b`.
Compare `IsCoprime.dvd_of_dvd_mul_left`. -/
theorem dvd_of_dvd_mul_left_of_no_prime_factors {a b c : R} (ha : a ≠ 0)
    (h : ∀ ⦃d⦄, d ∣ a → d ∣ c → ¬Prime d) : a ∣ b * c → a ∣ b :=
  ((isRelPrime_iff_no_prime_factors ha).mpr h).dvd_of_dvd_mul_right

/-- Euclid's lemma: if `a ∣ b * c` and `a` and `b` have no common prime factors, `a ∣ c`.
Compare `IsCoprime.dvd_of_dvd_mul_right`. -/
theorem dvd_of_dvd_mul_right_of_no_prime_factors {a b c : R} (ha : a ≠ 0)
    (no_factors : ∀ {d}, d ∣ a → d ∣ b → ¬Prime d) : a ∣ b * c → a ∣ c := by
  simpa [mul_comm b c] using dvd_of_dvd_mul_left_of_no_prime_factors ha @no_factors

/-- If `a ≠ 0, b` are elements of a unique factorization domain, then dividing
out their common factor `c'` gives `a'` and `b'` with no factors in common. -/
theorem exists_reduced_factors :
    ∀ a ≠ (0 : R), ∀ b,
      ∃ a' b' c', IsRelPrime a' b' ∧ c' * a' = a ∧ c' * b' = b := by
  intro a
  refine induction_on_prime a ?_ ?_ ?_
  · intros
    contradiction
  · intro a a_unit _ b
    use a, b, 1
    constructor
    · intro p p_dvd_a _
      exact isUnit_of_dvd_unit p_dvd_a a_unit
    · simp
  · intro a p a_ne_zero p_prime ih_a pa_ne_zero b
    by_cases h : p ∣ b
    · rcases h with ⟨b, rfl⟩
      obtain ⟨a', b', c', no_factor, ha', hb'⟩ := ih_a a_ne_zero b
      refine ⟨a', b', p * c', @no_factor, ?_, ?_⟩
      · rw [mul_assoc, ha']
      · rw [mul_assoc, hb']
    · obtain ⟨a', b', c', coprime, rfl, rfl⟩ := ih_a a_ne_zero b
      refine ⟨p * a', b', c', ?_, mul_left_comm _ _ _, rfl⟩
      intro q q_dvd_pa' q_dvd_b'
      rcases p_prime.left_dvd_or_dvd_right_of_dvd_mul q_dvd_pa' with p_dvd_q | q_dvd_a'
      · have : p ∣ c' * b' := dvd_mul_of_dvd_right (p_dvd_q.trans q_dvd_b') _
        contradiction
      exact coprime q_dvd_a' q_dvd_b'

theorem exists_reduced_factors' (a b : R) (hb : b ≠ 0) :
    ∃ a' b' c', IsRelPrime a' b' ∧ c' * a' = a ∧ c' * b' = b :=
  let ⟨b', a', c', no_factor, hb, ha⟩ := exists_reduced_factors b hb a
  ⟨a', b', c', fun _ hpb hpa => no_factor hpa hpb, ha, hb⟩

end UniqueFactorizationMonoid
