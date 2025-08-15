/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.GroupWithZero.Submonoid.Primal
import Mathlib.Order.WellFounded

/-!
# Unique factorization

## Main Definitions
* `WfDvdMonoid` holds for `Monoid`s for which a strict divisibility relation is
  well-founded.
* `UniqueFactorizationMonoid` holds for `WfDvdMonoid`s where
  `Irreducible` is equivalent to `Prime`
-/

assert_not_exists Field Finsupp Ideal

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

/-- Well-foundedness of the strict version of ∣, which is equivalent to the descending chain
condition on divisibility and to the ascending chain condition on
principal ideals in an integral domain.
-/
abbrev WfDvdMonoid (α : Type*) [CommMonoidWithZero α] : Prop :=
  IsWellFounded α DvdNotUnit

theorem wellFounded_dvdNotUnit {α : Type*} [CommMonoidWithZero α] [h : WfDvdMonoid α] :
    WellFounded (DvdNotUnit (α := α)) :=
  h.wf

namespace WfDvdMonoid

variable [CommMonoidWithZero α]

open Associates Nat

variable [WfDvdMonoid α]

theorem exists_irreducible_factor {a : α} (ha : ¬IsUnit a) (ha0 : a ≠ 0) :
    ∃ i, Irreducible i ∧ i ∣ a :=
  let ⟨b, hs, hr⟩ := wellFounded_dvdNotUnit.has_min { b | b ∣ a ∧ ¬IsUnit b } ⟨a, dvd_rfl, ha⟩
  ⟨b,
    ⟨hs.2, fun c d he =>
      let h := dvd_trans ⟨d, he⟩ hs.1
      or_iff_not_imp_left.2 fun hc =>
        of_not_not fun hd => hr c ⟨h, hc⟩ ⟨ne_zero_of_dvd_ne_zero ha0 h, d, hd, he⟩⟩,
    hs.1⟩

@[elab_as_elim]
theorem induction_on_irreducible {motive : α → Prop} (a : α)
    (zero : motive 0) (unit : ∀ u : α, IsUnit u → motive u)
    (mul : ∀ a i : α, a ≠ 0 → Irreducible i → motive a → motive (i * a)) : motive a :=
  haveI := Classical.dec
  wellFounded_dvdNotUnit.fix
    (fun a ih =>
      if ha0 : a = 0 then ha0.substr zero
      else
        if hau : IsUnit a then unit a hau
        else
          let ⟨i, i_irred, b, hb⟩ := exists_irreducible_factor hau ha0
          let hb0 : b ≠ 0 := ne_zero_of_dvd_ne_zero ha0 ⟨i, mul_comm i b ▸ hb⟩
          hb.symm ▸ mul b i hb0 i_irred <| ih b ⟨hb0, i, i_irred.1, mul_comm i b ▸ hb⟩)
    a

theorem exists_factors (a : α) :
    a ≠ 0 → ∃ f : Multiset α, (∀ b ∈ f, Irreducible b) ∧ Associated f.prod a :=
  induction_on_irreducible a (fun h => (h rfl).elim)
    (fun _ hu _ => ⟨0, fun _ h => False.elim (Multiset.notMem_zero _ h), hu.unit, one_mul _⟩)
    fun a i ha0 hi ih _ =>
    let ⟨s, hs⟩ := ih ha0
    ⟨i ::ₘ s, fun b H => (Multiset.mem_cons.1 H).elim (fun h => h.symm ▸ hi) (hs.1 b), by
      rw [s.prod_cons i]
      exact hs.2.mul_left i⟩

theorem not_unit_iff_exists_factors_eq (a : α) (hn0 : a ≠ 0) :
    ¬IsUnit a ↔ ∃ f : Multiset α, (∀ b ∈ f, Irreducible b) ∧ f.prod = a ∧ f ≠ ∅ :=
  ⟨fun hnu => by
    obtain ⟨f, hi, u, rfl⟩ := exists_factors a hn0
    obtain ⟨b, h⟩ := Multiset.exists_mem_of_ne_zero fun h : f = 0 => hnu <| by simp [h]
    classical
      refine ⟨(f.erase b).cons (b * u), fun a ha => ?_, ?_, Multiset.cons_ne_zero⟩
      · obtain rfl | ha := Multiset.mem_cons.1 ha
        exacts [Associated.irreducible ⟨u, rfl⟩ (hi b h), hi a (Multiset.mem_of_mem_erase ha)]
      · rw [Multiset.prod_cons, mul_comm b, mul_assoc, Multiset.prod_erase h, mul_comm],
    fun ⟨_, hi, he, hne⟩ =>
    let ⟨b, h⟩ := Multiset.exists_mem_of_ne_zero hne
    not_isUnit_of_not_isUnit_dvd (hi b h).not_isUnit <| he ▸ Multiset.dvd_prod h⟩

theorem isRelPrime_of_no_irreducible_factors {x y : α} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : ∀ z : α, Irreducible z → z ∣ x → ¬z ∣ y) : IsRelPrime x y :=
  isRelPrime_of_no_nonunits_factors nonzero fun _z znu znz zx zy ↦
    have ⟨i, h1, h2⟩ := exists_irreducible_factor znu znz
    H i h1 (h2.trans zx) (h2.trans zy)

end WfDvdMonoid

section Prio

-- set_option default_priority 100

-- see Note [default priority]
/--
Unique factorization monoids are defined as `CancelCommMonoidWithZero`s with well-founded
strict divisibility relations, but this is equivalent to more familiar definitions:

Each element (except zero) is uniquely represented as a multiset of irreducible factors.
Uniqueness is only up to associated elements.

Each element (except zero) is non-uniquely represented as a multiset
of prime factors.

To define a UFD using the definition in terms of multisets
of irreducible factors, use the definition `of_existsUnique_irreducible_factors`

To define a UFD using the definition in terms of multisets
of prime factors, use the definition `of_exists_prime_factors`
-/
class UniqueFactorizationMonoid (α : Type*) [CancelCommMonoidWithZero α] : Prop
    extends IsWellFounded α DvdNotUnit where
  protected irreducible_iff_prime : ∀ {a : α}, Irreducible a ↔ Prime a

instance (priority := 100) ufm_of_decomposition_of_wfDvdMonoid
    [CancelCommMonoidWithZero α] [WfDvdMonoid α] [DecompositionMonoid α] :
    UniqueFactorizationMonoid α :=
  { ‹WfDvdMonoid α› with irreducible_iff_prime := irreducible_iff_prime }

end Prio

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α]

theorem exists_prime_factors (a : α) :
    a ≠ 0 → ∃ f : Multiset α, (∀ b ∈ f, Prime b) ∧ f.prod ~ᵤ a := by
  simp_rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  apply WfDvdMonoid.exists_factors a

lemma exists_prime_iff :
    (∃ (p : α), Prime p) ↔ ∃ (x : α), x ≠ 0 ∧ ¬ IsUnit x := by
  refine ⟨fun ⟨p, hp⟩ ↦ ⟨p, hp.ne_zero, hp.not_unit⟩, fun ⟨x, hx₀, hxu⟩ ↦ ?_⟩
  obtain ⟨f, hf, -⟩ := WfDvdMonoid.exists_irreducible_factor hxu hx₀
  exact ⟨f, UniqueFactorizationMonoid.irreducible_iff_prime.mp hf⟩

@[elab_as_elim]
theorem induction_on_prime {P : α → Prop} (a : α) (h₁ : P 0) (h₂ : ∀ x : α, IsUnit x → P x)
    (h₃ : ∀ a p : α, a ≠ 0 → Prime p → P a → P (p * a)) : P a := by
  simp_rw [← UniqueFactorizationMonoid.irreducible_iff_prime] at h₃
  exact WfDvdMonoid.induction_on_irreducible a h₁ h₂ h₃

instance : DecompositionMonoid α where
  primal a := by
    obtain rfl | ha := eq_or_ne a 0; · exact isPrimal_zero
    obtain ⟨f, hf, u, rfl⟩ := exists_prime_factors a ha
    exact ((Submonoid.isPrimal α).multiset_prod_mem f (hf · ·|>.isPrimal)).mul u.isUnit.isPrimal

end UniqueFactorizationMonoid

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero α]
variable [UniqueFactorizationMonoid α]

open Classical in
/-- Noncomputably determines the multiset of prime factors. -/
noncomputable def factors (a : α) : Multiset α :=
  if h : a = 0 then 0 else Classical.choose (UniqueFactorizationMonoid.exists_prime_factors a h)

theorem factors_prod {a : α} (ane0 : a ≠ 0) : Associated (factors a).prod a := by
  rw [factors, dif_neg ane0]
  exact (Classical.choose_spec (exists_prime_factors a ane0)).2

@[simp]
theorem factors_zero : factors (0 : α) = 0 := by simp [factors]

theorem ne_zero_of_mem_factors {p a : α} (h : p ∈ factors a) : a ≠ 0 := by
  rintro rfl
  simp at h

theorem dvd_of_mem_factors {p a : α} (h : p ∈ factors a) : p ∣ a :=
  dvd_trans (Multiset.dvd_prod h) (Associated.dvd (factors_prod (ne_zero_of_mem_factors h)))

theorem prime_of_factor {a : α} (x : α) (hx : x ∈ factors a) : Prime x := by
  have ane0 := ne_zero_of_mem_factors hx
  rw [factors, dif_neg ane0] at hx
  exact (Classical.choose_spec (UniqueFactorizationMonoid.exists_prime_factors a ane0)).1 x hx

theorem irreducible_of_factor {a : α} : ∀ x : α, x ∈ factors a → Irreducible x := fun x h =>
  (prime_of_factor x h).irreducible

end UniqueFactorizationMonoid
