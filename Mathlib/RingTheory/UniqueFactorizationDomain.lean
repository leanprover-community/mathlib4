/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Nat.Factors
import Mathlib.RingTheory.Noetherian
import Mathlib.RingTheory.Multiplicity

#align_import ring_theory.unique_factorization_domain from "leanprover-community/mathlib"@"570e9f4877079b3a923135b3027ac3be8695ab8c"

/-!

# Unique factorization

## Main Definitions
* `WfDvdMonoid` holds for `Monoid`s for which a strict divisibility relation is
  well-founded.
* `UniqueFactorizationMonoid` holds for `WfDvdMonoid`s where
  `Irreducible` is equivalent to `Prime`

## To do
* set up the complete lattice structure on `FactorSet`.

-/


variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

/-- Well-foundedness of the strict version of |, which is equivalent to the descending chain
condition on divisibility and to the ascending chain condition on
principal ideals in an integral domain.
  -/
class WfDvdMonoid (α : Type*) [CommMonoidWithZero α] : Prop where
  wellFounded_dvdNotUnit : WellFounded (@DvdNotUnit α _)
#align wf_dvd_monoid WfDvdMonoid

export WfDvdMonoid (wellFounded_dvdNotUnit)

-- see Note [lower instance priority]
instance (priority := 100) IsNoetherianRing.wfDvdMonoid [CommRing α] [IsDomain α]
    [IsNoetherianRing α] : WfDvdMonoid α :=
  ⟨by
    convert InvImage.wf (fun a => Ideal.span ({a} : Set α)) (wellFounded_submodule_gt _ _)
    ext
    exact Ideal.span_singleton_lt_span_singleton.symm⟩
#align is_noetherian_ring.wf_dvd_monoid IsNoetherianRing.wfDvdMonoid

namespace WfDvdMonoid

variable [CommMonoidWithZero α]

open Associates Nat

theorem of_wfDvdMonoid_associates (_ : WfDvdMonoid (Associates α)) : WfDvdMonoid α :=
  ⟨(mk_surjective.wellFounded_iff mk_dvdNotUnit_mk_iff.symm).2 wellFounded_dvdNotUnit⟩
#align wf_dvd_monoid.of_wf_dvd_monoid_associates WfDvdMonoid.of_wfDvdMonoid_associates

variable [WfDvdMonoid α]

instance wfDvdMonoid_associates : WfDvdMonoid (Associates α) :=
  ⟨(mk_surjective.wellFounded_iff mk_dvdNotUnit_mk_iff.symm).1 wellFounded_dvdNotUnit⟩
#align wf_dvd_monoid.wf_dvd_monoid_associates WfDvdMonoid.wfDvdMonoid_associates

theorem wellFounded_associates : WellFounded ((· < ·) : Associates α → Associates α → Prop) :=
  Subrelation.wf dvdNotUnit_of_lt wellFounded_dvdNotUnit
#align wf_dvd_monoid.well_founded_associates WfDvdMonoid.wellFounded_associates

-- Porting note: elab_as_elim can only be global and cannot be changed on an imported decl
-- attribute [local elab_as_elim] WellFounded.fix

theorem exists_irreducible_factor {a : α} (ha : ¬IsUnit a) (ha0 : a ≠ 0) :
    ∃ i, Irreducible i ∧ i ∣ a :=
  let ⟨b, hs, hr⟩ := wellFounded_dvdNotUnit.has_min { b | b ∣ a ∧ ¬IsUnit b } ⟨a, dvd_rfl, ha⟩
  ⟨b,
    ⟨hs.2, fun c d he =>
      let h := dvd_trans ⟨d, he⟩ hs.1
      or_iff_not_imp_left.2 fun hc =>
        of_not_not fun hd => hr c ⟨h, hc⟩ ⟨ne_zero_of_dvd_ne_zero ha0 h, d, hd, he⟩⟩,
    hs.1⟩
#align wf_dvd_monoid.exists_irreducible_factor WfDvdMonoid.exists_irreducible_factor

@[elab_as_elim]
theorem induction_on_irreducible {P : α → Prop} (a : α) (h0 : P 0) (hu : ∀ u : α, IsUnit u → P u)
    (hi : ∀ a i : α, a ≠ 0 → Irreducible i → P a → P (i * a)) : P a :=
  haveI := Classical.dec
  wellFounded_dvdNotUnit.fix
    (fun a ih =>
      if ha0 : a = 0 then ha0.substr h0
      else
        if hau : IsUnit a then hu a hau
        else
          let ⟨i, hii, b, hb⟩ := exists_irreducible_factor hau ha0
          let hb0 : b ≠ 0 := ne_zero_of_dvd_ne_zero ha0 ⟨i, mul_comm i b ▸ hb⟩
          hb.symm ▸ hi b i hb0 hii <| ih b ⟨hb0, i, hii.1, mul_comm i b ▸ hb⟩)
    a
#align wf_dvd_monoid.induction_on_irreducible WfDvdMonoid.induction_on_irreducible

theorem exists_factors (a : α) :
    a ≠ 0 → ∃ f : Multiset α, (∀ b ∈ f, Irreducible b) ∧ Associated f.prod a :=
  induction_on_irreducible a (fun h => (h rfl).elim)
    (fun u hu _ => ⟨0, fun _ h => False.elim (Multiset.not_mem_zero _ h), hu.unit, one_mul _⟩)
    fun a i ha0 hi ih _ =>
    let ⟨s, hs⟩ := ih ha0
    ⟨i ::ₘ s, fun b H => (Multiset.mem_cons.1 H).elim (fun h => h.symm ▸ hi) (hs.1 b), by
      rw [s.prod_cons i]
      exact hs.2.mul_left i⟩
#align wf_dvd_monoid.exists_factors WfDvdMonoid.exists_factors

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
    fun ⟨f, hi, he, hne⟩ =>
    let ⟨b, h⟩ := Multiset.exists_mem_of_ne_zero hne
    not_isUnit_of_not_isUnit_dvd (hi b h).not_unit <| he ▸ Multiset.dvd_prod h⟩
#align wf_dvd_monoid.not_unit_iff_exists_factors_eq WfDvdMonoid.not_unit_iff_exists_factors_eq

theorem isRelPrime_of_no_irreducible_factors {x y : α} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : ∀ z : α, Irreducible z → z ∣ x → ¬z ∣ y) : IsRelPrime x y :=
  isRelPrime_of_no_nonunits_factors nonzero fun _z znu znz zx zy ↦
    have ⟨i, h1, h2⟩ := exists_irreducible_factor znu znz
    H i h1 (h2.trans zx) (h2.trans zy)

end WfDvdMonoid

theorem WfDvdMonoid.of_wellFounded_associates [CancelCommMonoidWithZero α]
    (h : WellFounded ((· < ·) : Associates α → Associates α → Prop)) : WfDvdMonoid α :=
  WfDvdMonoid.of_wfDvdMonoid_associates
    ⟨by
      convert h
      ext
      exact Associates.dvdNotUnit_iff_lt⟩
#align wf_dvd_monoid.of_well_founded_associates WfDvdMonoid.of_wellFounded_associates

theorem WfDvdMonoid.iff_wellFounded_associates [CancelCommMonoidWithZero α] :
    WfDvdMonoid α ↔ WellFounded ((· < ·) : Associates α → Associates α → Prop) :=
  ⟨by apply WfDvdMonoid.wellFounded_associates, WfDvdMonoid.of_wellFounded_associates⟩
#align wf_dvd_monoid.iff_well_founded_associates WfDvdMonoid.iff_wellFounded_associates

theorem WfDvdMonoid.max_power_factor' [CommMonoidWithZero α] [WfDvdMonoid α] {a₀ x : α}
    (h : a₀ ≠ 0) (hx : ¬IsUnit x) : ∃ (n : ℕ) (a : α), ¬x ∣ a ∧ a₀ = x ^ n * a := by
  obtain ⟨a, ⟨n, rfl⟩, hm⟩ := wellFounded_dvdNotUnit.has_min
    {a | ∃ n, x ^ n * a = a₀} ⟨a₀, 0, by rw [pow_zero, one_mul]⟩
  refine ⟨n, a, ?_, rfl⟩; rintro ⟨d, rfl⟩
  exact hm d ⟨n + 1, by rw [pow_succ, mul_assoc]⟩
    ⟨(right_ne_zero_of_mul <| right_ne_zero_of_mul h), x, hx, mul_comm _ _⟩

theorem WfDvdMonoid.max_power_factor [CommMonoidWithZero α] [WfDvdMonoid α] {a₀ x : α}
    (h : a₀ ≠ 0) (hx : Irreducible x) : ∃ (n : ℕ) (a : α), ¬x ∣ a ∧ a₀ = x ^ n * a :=
  max_power_factor' h hx.not_unit

theorem multiplicity.finite_of_not_isUnit [CancelCommMonoidWithZero α] [WfDvdMonoid α]
    {a b : α} (ha : ¬IsUnit a) (hb : b ≠ 0) : multiplicity.Finite a b := by
  obtain ⟨n, c, ndvd, rfl⟩ := WfDvdMonoid.max_power_factor' hb ha
  exact ⟨n, by rwa [pow_succ, mul_dvd_mul_iff_left (left_ne_zero_of_mul hb)]⟩

section Prio

-- set_option default_priority 100

-- see Note [default priority]
/-- unique factorization monoids.

These are defined as `CancelCommMonoidWithZero`s with well-founded strict divisibility
relations, but this is equivalent to more familiar definitions:

Each element (except zero) is uniquely represented as a multiset of irreducible factors.
Uniqueness is only up to associated elements.

Each element (except zero) is non-uniquely represented as a multiset
of prime factors.

To define a UFD using the definition in terms of multisets
of irreducible factors, use the definition `of_exists_unique_irreducible_factors`

To define a UFD using the definition in terms of multisets
of prime factors, use the definition `of_exists_prime_factors`

-/
class UniqueFactorizationMonoid (α : Type*) [CancelCommMonoidWithZero α] extends WfDvdMonoid α :
  Prop where
  protected irreducible_iff_prime : ∀ {a : α}, Irreducible a ↔ Prime a
#align unique_factorization_monoid UniqueFactorizationMonoid

/-- Can't be an instance because it would cause a loop `ufm → WfDvdMonoid → ufm → ...`. -/
theorem ufm_of_decomposition_of_wfDvdMonoid [CancelCommMonoidWithZero α] [WfDvdMonoid α]
    [DecompositionMonoid α] : UniqueFactorizationMonoid α :=
  { ‹WfDvdMonoid α› with irreducible_iff_prime := irreducible_iff_prime }
#align ufm_of_gcd_of_wf_dvd_monoid ufm_of_decomposition_of_wfDvdMonoid
@[deprecated] alias ufm_of_gcd_of_wfDvdMonoid := ufm_of_decomposition_of_wfDvdMonoid

instance Associates.ufm [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α] :
    UniqueFactorizationMonoid (Associates α) :=
  { (WfDvdMonoid.wfDvdMonoid_associates : WfDvdMonoid (Associates α)) with
    irreducible_iff_prime := by
      rw [← Associates.irreducible_iff_prime_iff]
      apply UniqueFactorizationMonoid.irreducible_iff_prime }
#align associates.ufm Associates.ufm

end Prio

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α]

theorem exists_prime_factors (a : α) :
    a ≠ 0 → ∃ f : Multiset α, (∀ b ∈ f, Prime b) ∧ f.prod ~ᵤ a := by
  simp_rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  apply WfDvdMonoid.exists_factors a
#align unique_factorization_monoid.exists_prime_factors UniqueFactorizationMonoid.exists_prime_factors

instance : DecompositionMonoid α where
  primal a := by
    obtain rfl | ha := eq_or_ne a 0; · exact isPrimal_zero
    obtain ⟨f, hf, u, rfl⟩ := exists_prime_factors a ha
    exact ((Submonoid.isPrimal α).multiset_prod_mem f (hf · ·|>.isPrimal)).mul u.isUnit.isPrimal

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
#align unique_factorization_monoid.induction_on_prime UniqueFactorizationMonoid.induction_on_prime

end UniqueFactorizationMonoid

theorem prime_factors_unique [CancelCommMonoidWithZero α] :
    ∀ {f g : Multiset α},
      (∀ x ∈ f, Prime x) → (∀ x ∈ g, Prime x) → f.prod ~ᵤ g.prod → Multiset.Rel Associated f g := by
  classical
  intro f
  induction' f using Multiset.induction_on with p f ih
  · intros g _ hg h
    exact Multiset.rel_zero_left.2 <|
      Multiset.eq_zero_of_forall_not_mem fun x hx =>
        have : IsUnit g.prod := by simpa [associated_one_iff_isUnit] using h.symm
        (hg x hx).not_unit <|
          isUnit_iff_dvd_one.2 <| (Multiset.dvd_prod hx).trans (isUnit_iff_dvd_one.1 this)
  · intros g hf hg hfg
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
#align prime_factors_unique prime_factors_unique

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α]

theorem factors_unique {f g : Multiset α} (hf : ∀ x ∈ f, Irreducible x)
    (hg : ∀ x ∈ g, Irreducible x) (h : f.prod ~ᵤ g.prod) : Multiset.Rel Associated f g :=
  prime_factors_unique (fun x hx => UniqueFactorizationMonoid.irreducible_iff_prime.mp (hf x hx))
    (fun x hx => UniqueFactorizationMonoid.irreducible_iff_prime.mp (hg x hx)) h
#align unique_factorization_monoid.factors_unique UniqueFactorizationMonoid.factors_unique

end UniqueFactorizationMonoid

/-- If an irreducible has a prime factorization,
  then it is an associate of one of its prime factors. -/
theorem prime_factors_irreducible [CancelCommMonoidWithZero α] {a : α} {f : Multiset α}
    (ha : Irreducible a) (pfa : (∀ b ∈ f, Prime b) ∧ f.prod ~ᵤ a) : ∃ p, a ~ᵤ p ∧ f = {p} := by
  haveI := Classical.decEq α
  refine @Multiset.induction_on _
    (fun g => (g.prod ~ᵤ a) → (∀ b ∈ g, Prime b) → ∃ p, a ~ᵤ p ∧ g = {p}) f ?_ ?_ pfa.2 pfa.1
  · intro h; exact (ha.not_unit (associated_one_iff_isUnit.1 (Associated.symm h))).elim
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
#align prime_factors_irreducible prime_factors_irreducible

section ExistsPrimeFactors

variable [CancelCommMonoidWithZero α]
variable (pf : ∀ a : α, a ≠ 0 → ∃ f : Multiset α, (∀ b ∈ f, Prime b) ∧ f.prod ~ᵤ a)

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
      · rw [dif_neg h]
        erw [WithTop.coe_lt_coe]
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
          cases' hadd with h h <;> apply (Classical.choose_spec (pf _ _)).1 _ h <;> assumption
        · rw [Multiset.prod_add]
          trans a * c
          · apply Associated.mul_mul <;> apply (Classical.choose_spec (pf _ _)).2 <;> assumption
          · rw [← b_eq]
            apply (Classical.choose_spec (pf _ _)).2.symm; assumption⟩
#align wf_dvd_monoid.of_exists_prime_factors WfDvdMonoid.of_exists_prime_factors

theorem irreducible_iff_prime_of_exists_prime_factors {p : α} : Irreducible p ↔ Prime p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  refine ⟨fun h => ?_, Prime.irreducible⟩
  obtain ⟨f, hf⟩ := pf p hp0
  obtain ⟨q, hq, rfl⟩ := prime_factors_irreducible h hf
  rw [hq.prime_iff]
  exact hf.1 q (Multiset.mem_singleton_self _)
#align irreducible_iff_prime_of_exists_prime_factors irreducible_iff_prime_of_exists_prime_factors

theorem UniqueFactorizationMonoid.of_exists_prime_factors : UniqueFactorizationMonoid α :=
  { WfDvdMonoid.of_exists_prime_factors pf with
    irreducible_iff_prime := irreducible_iff_prime_of_exists_prime_factors pf }
#align unique_factorization_monoid.of_exists_prime_factors UniqueFactorizationMonoid.of_exists_prime_factors

end ExistsPrimeFactors

theorem UniqueFactorizationMonoid.iff_exists_prime_factors [CancelCommMonoidWithZero α] :
    UniqueFactorizationMonoid α ↔
      ∀ a : α, a ≠ 0 → ∃ f : Multiset α, (∀ b ∈ f, Prime b) ∧ f.prod ~ᵤ a :=
  ⟨fun h => @UniqueFactorizationMonoid.exists_prime_factors _ _ h,
    UniqueFactorizationMonoid.of_exists_prime_factors⟩
#align unique_factorization_monoid.iff_exists_prime_factors UniqueFactorizationMonoid.iff_exists_prime_factors

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
        he ▸ e.prime_iff.1 (hp c hc),
        Units.map e.toMonoidHom u,
      by
        erw [Multiset.prod_hom, ← e.map_mul, h]
        simp⟩
#align mul_equiv.unique_factorization_monoid MulEquiv.uniqueFactorizationMonoid

theorem MulEquiv.uniqueFactorizationMonoid_iff (e : α ≃* β) :
    UniqueFactorizationMonoid α ↔ UniqueFactorizationMonoid β :=
  ⟨e.uniqueFactorizationMonoid, e.symm.uniqueFactorizationMonoid⟩
#align mul_equiv.unique_factorization_monoid_iff MulEquiv.uniqueFactorizationMonoid_iff

end

theorem irreducible_iff_prime_of_exists_unique_irreducible_factors [CancelCommMonoidWithZero α]
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
        cases' eif x hx0 with fx hfx
        cases' eif a ha0 with fa hfa
        cases' eif b hb0 with fb hfb
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
#align irreducible_iff_prime_of_exists_unique_irreducible_factors irreducible_iff_prime_of_exists_unique_irreducible_factors

theorem UniqueFactorizationMonoid.of_exists_unique_irreducible_factors [CancelCommMonoidWithZero α]
    (eif : ∀ a : α, a ≠ 0 → ∃ f : Multiset α, (∀ b ∈ f, Irreducible b) ∧ f.prod ~ᵤ a)
    (uif :
      ∀ f g : Multiset α,
        (∀ x ∈ f, Irreducible x) →
          (∀ x ∈ g, Irreducible x) → f.prod ~ᵤ g.prod → Multiset.Rel Associated f g) :
    UniqueFactorizationMonoid α :=
  UniqueFactorizationMonoid.of_exists_prime_factors
    (by
      convert eif using 7
      simp_rw [irreducible_iff_prime_of_exists_unique_irreducible_factors eif uif])
#align unique_factorization_monoid.of_exists_unique_irreducible_factors UniqueFactorizationMonoid.of_exists_unique_irreducible_factors

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero α]
variable [UniqueFactorizationMonoid α]

open Classical in
/-- Noncomputably determines the multiset of prime factors. -/
noncomputable def factors (a : α) : Multiset α :=
  if h : a = 0 then 0 else Classical.choose (UniqueFactorizationMonoid.exists_prime_factors a h)
#align unique_factorization_monoid.factors UniqueFactorizationMonoid.factors

theorem factors_prod {a : α} (ane0 : a ≠ 0) : Associated (factors a).prod a := by
  rw [factors, dif_neg ane0]
  exact (Classical.choose_spec (exists_prime_factors a ane0)).2
#align unique_factorization_monoid.factors_prod UniqueFactorizationMonoid.factors_prod

@[simp]
theorem factors_zero : factors (0 : α) = 0 := by simp [factors]
#align unique_factorization_monoid.factors_zero UniqueFactorizationMonoid.factors_zero

theorem ne_zero_of_mem_factors {p a : α} (h : p ∈ factors a) : a ≠ 0 := by
  rintro rfl
  simp at h
#align unique_factorization_monoid.ne_zero_of_mem_factors UniqueFactorizationMonoid.ne_zero_of_mem_factors

theorem dvd_of_mem_factors {p a : α} (h : p ∈ factors a) : p ∣ a :=
  dvd_trans (Multiset.dvd_prod h) (Associated.dvd (factors_prod (ne_zero_of_mem_factors h)))
#align unique_factorization_monoid.dvd_of_mem_factors UniqueFactorizationMonoid.dvd_of_mem_factors

theorem prime_of_factor {a : α} (x : α) (hx : x ∈ factors a) : Prime x := by
  have ane0 := ne_zero_of_mem_factors hx
  rw [factors, dif_neg ane0] at hx
  exact (Classical.choose_spec (UniqueFactorizationMonoid.exists_prime_factors a ane0)).1 x hx
#align unique_factorization_monoid.prime_of_factor UniqueFactorizationMonoid.prime_of_factor

theorem irreducible_of_factor {a : α} : ∀ x : α, x ∈ factors a → Irreducible x := fun x h =>
  (prime_of_factor x h).irreducible
#align unique_factorization_monoid.irreducible_of_factor UniqueFactorizationMonoid.irreducible_of_factor

@[simp]
theorem factors_one : factors (1 : α) = 0 := by
  nontriviality α using factors
  rw [← Multiset.rel_zero_right]
  refine factors_unique irreducible_of_factor (fun x hx => (Multiset.not_mem_zero x hx).elim) ?_
  rw [Multiset.prod_zero]
  exact factors_prod one_ne_zero
#align unique_factorization_monoid.factors_one UniqueFactorizationMonoid.factors_one

theorem exists_mem_factors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) :
    p ∣ a → ∃ q ∈ factors a, p ~ᵤ q := fun ⟨b, hb⟩ =>
  have hb0 : b ≠ 0 := fun hb0 => by simp_all
  have : Multiset.Rel Associated (p ::ₘ factors b) (factors a) :=
    factors_unique
      (fun x hx => (Multiset.mem_cons.1 hx).elim (fun h => h.symm ▸ hp) (irreducible_of_factor _))
      irreducible_of_factor
      (Associated.symm <|
        calc
          Multiset.prod (factors a) ~ᵤ a := factors_prod ha0
          _ = p * b := hb
          _ ~ᵤ Multiset.prod (p ::ₘ factors b) := by
            rw [Multiset.prod_cons]; exact (factors_prod hb0).symm.mul_left _
          )
  Multiset.exists_mem_of_rel_of_mem this (by simp)
#align unique_factorization_monoid.exists_mem_factors_of_dvd UniqueFactorizationMonoid.exists_mem_factors_of_dvd

theorem exists_mem_factors {x : α} (hx : x ≠ 0) (h : ¬IsUnit x) : ∃ p, p ∈ factors x := by
  obtain ⟨p', hp', hp'x⟩ := WfDvdMonoid.exists_irreducible_factor h hx
  obtain ⟨p, hp, _⟩ := exists_mem_factors_of_dvd hx hp' hp'x
  exact ⟨p, hp⟩
#align unique_factorization_monoid.exists_mem_factors UniqueFactorizationMonoid.exists_mem_factors

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
#align unique_factorization_monoid.factors_mul UniqueFactorizationMonoid.factors_mul

theorem factors_pow {x : α} (n : ℕ) :
    Multiset.Rel Associated (factors (x ^ n)) (n • factors x) := by
  match n with
  | 0 => rw [zero_smul, pow_zero, factors_one, Multiset.rel_zero_right]
  | n+1 =>
    by_cases h0 : x = 0
    · simp [h0, zero_pow n.succ_ne_zero, smul_zero]
    · rw [pow_succ', succ_nsmul']
      refine Multiset.Rel.trans _ (factors_mul h0 (pow_ne_zero n h0)) ?_
      refine Multiset.Rel.add ?_ <| factors_pow n
      exact Multiset.rel_refl_of_refl_on fun y _ => Associated.refl _
#align unique_factorization_monoid.factors_pow UniqueFactorizationMonoid.factors_pow

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
        (mt Multiset.eq_zero_iff_forall_not_mem.mp (not_forall.mpr ⟨p, not_not.mpr hp⟩))
#align unique_factorization_monoid.factors_pos UniqueFactorizationMonoid.factors_pos

open Multiset in
theorem factors_pow_count_prod [DecidableEq α] {x : α} (hx : x ≠ 0) :
    (∏ p ∈ (factors x).toFinset, p ^ (factors x).count p) ~ᵤ x :=
  calc
  _ = prod (∑ a ∈ toFinset (factors x), count a (factors x) • {a}) := by
    simp only [prod_sum, prod_nsmul, prod_singleton]
  _ = prod (factors x) := by rw [toFinset_sum_count_nsmul_eq (factors x)]
  _ ~ᵤ x := factors_prod hx

end UniqueFactorizationMonoid

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero α] [NormalizationMonoid α]
variable [UniqueFactorizationMonoid α]

/-- Noncomputably determines the multiset of prime factors. -/
noncomputable def normalizedFactors (a : α) : Multiset α :=
  Multiset.map normalize <| factors a
#align unique_factorization_monoid.normalized_factors UniqueFactorizationMonoid.normalizedFactors

/-- An arbitrary choice of factors of `x : M` is exactly the (unique) normalized set of factors,
if `M` has a trivial group of units. -/
@[simp]
theorem factors_eq_normalizedFactors {M : Type*} [CancelCommMonoidWithZero M]
    [UniqueFactorizationMonoid M] [Unique Mˣ] (x : M) : factors x = normalizedFactors x := by
  unfold normalizedFactors
  convert (Multiset.map_id (factors x)).symm
  ext p
  exact normalize_eq p
#align unique_factorization_monoid.factors_eq_normalized_factors UniqueFactorizationMonoid.factors_eq_normalizedFactors

theorem normalizedFactors_prod {a : α} (ane0 : a ≠ 0) :
    Associated (normalizedFactors a).prod a := by
  rw [normalizedFactors, factors, dif_neg ane0]
  refine Associated.trans ?_ (Classical.choose_spec (exists_prime_factors a ane0)).2
  rw [← Associates.mk_eq_mk_iff_associated, ← Associates.prod_mk, ← Associates.prod_mk,
    Multiset.map_map]
  congr 2
  ext
  rw [Function.comp_apply, Associates.mk_normalize]
#align unique_factorization_monoid.normalized_factors_prod UniqueFactorizationMonoid.normalizedFactors_prod

theorem prime_of_normalized_factor {a : α} : ∀ x : α, x ∈ normalizedFactors a → Prime x := by
  rw [normalizedFactors, factors]
  split_ifs with ane0; · simp
  intro x hx; rcases Multiset.mem_map.1 hx with ⟨y, ⟨hy, rfl⟩⟩
  rw [(normalize_associated _).prime_iff]
  exact (Classical.choose_spec (UniqueFactorizationMonoid.exists_prime_factors a ane0)).1 y hy
#align unique_factorization_monoid.prime_of_normalized_factor UniqueFactorizationMonoid.prime_of_normalized_factor

theorem irreducible_of_normalized_factor {a : α} :
    ∀ x : α, x ∈ normalizedFactors a → Irreducible x := fun x h =>
  (prime_of_normalized_factor x h).irreducible
#align unique_factorization_monoid.irreducible_of_normalized_factor UniqueFactorizationMonoid.irreducible_of_normalized_factor

theorem normalize_normalized_factor {a : α} :
    ∀ x : α, x ∈ normalizedFactors a → normalize x = x := by
  rw [normalizedFactors, factors]
  split_ifs with h; · simp
  intro x hx
  obtain ⟨y, _, rfl⟩ := Multiset.mem_map.1 hx
  apply normalize_idem
#align unique_factorization_monoid.normalize_normalized_factor UniqueFactorizationMonoid.normalize_normalized_factor

theorem normalizedFactors_irreducible {a : α} (ha : Irreducible a) :
    normalizedFactors a = {normalize a} := by
  obtain ⟨p, a_assoc, hp⟩ :=
    prime_factors_irreducible ha ⟨prime_of_normalized_factor, normalizedFactors_prod ha.ne_zero⟩
  have p_mem : p ∈ normalizedFactors a := by
    rw [hp]
    exact Multiset.mem_singleton_self _
  convert hp
  rwa [← normalize_normalized_factor p p_mem, normalize_eq_normalize_iff, dvd_dvd_iff_associated]
#align unique_factorization_monoid.normalized_factors_irreducible UniqueFactorizationMonoid.normalizedFactors_irreducible

theorem normalizedFactors_eq_of_dvd (a : α) :
    ∀ᵉ (p ∈ normalizedFactors a) (q ∈ normalizedFactors a), p ∣ q → p = q := by
  intro p hp q hq hdvd
  convert normalize_eq_normalize hdvd
          ((prime_of_normalized_factor _ hp).irreducible.dvd_symm
            (prime_of_normalized_factor _ hq).irreducible hdvd) <;>
    apply (normalize_normalized_factor _ ‹_›).symm
#align unique_factorization_monoid.normalized_factors_eq_of_dvd UniqueFactorizationMonoid.normalizedFactors_eq_of_dvd

theorem exists_mem_normalizedFactors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) :
    p ∣ a → ∃ q ∈ normalizedFactors a, p ~ᵤ q := fun ⟨b, hb⟩ =>
  have hb0 : b ≠ 0 := fun hb0 => by simp_all
  have : Multiset.Rel Associated (p ::ₘ normalizedFactors b) (normalizedFactors a) :=
    factors_unique
      (fun x hx =>
        (Multiset.mem_cons.1 hx).elim (fun h => h.symm ▸ hp) (irreducible_of_normalized_factor _))
      irreducible_of_normalized_factor
      (Associated.symm <|
        calc
          Multiset.prod (normalizedFactors a) ~ᵤ a := normalizedFactors_prod ha0
          _ = p * b := hb
          _ ~ᵤ Multiset.prod (p ::ₘ normalizedFactors b) := by
            rw [Multiset.prod_cons]
            exact (normalizedFactors_prod hb0).symm.mul_left _
          )
  Multiset.exists_mem_of_rel_of_mem this (by simp)
#align unique_factorization_monoid.exists_mem_normalized_factors_of_dvd UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd

theorem exists_mem_normalizedFactors {x : α} (hx : x ≠ 0) (h : ¬IsUnit x) :
    ∃ p, p ∈ normalizedFactors x := by
  obtain ⟨p', hp', hp'x⟩ := WfDvdMonoid.exists_irreducible_factor h hx
  obtain ⟨p, hp, _⟩ := exists_mem_normalizedFactors_of_dvd hx hp' hp'x
  exact ⟨p, hp⟩
#align unique_factorization_monoid.exists_mem_normalized_factors UniqueFactorizationMonoid.exists_mem_normalizedFactors

@[simp]
theorem normalizedFactors_zero : normalizedFactors (0 : α) = 0 := by
  simp [normalizedFactors, factors]
#align unique_factorization_monoid.normalized_factors_zero UniqueFactorizationMonoid.normalizedFactors_zero

@[simp]
theorem normalizedFactors_one : normalizedFactors (1 : α) = 0 := by
  cases' subsingleton_or_nontrivial α with h h
  · dsimp [normalizedFactors, factors]
    simp [Subsingleton.elim (1:α) 0]
  · rw [← Multiset.rel_zero_right]
    apply factors_unique irreducible_of_normalized_factor
    · intro x hx
      exfalso
      apply Multiset.not_mem_zero x hx
    · apply normalizedFactors_prod one_ne_zero
#align unique_factorization_monoid.normalized_factors_one UniqueFactorizationMonoid.normalizedFactors_one

@[simp]
theorem normalizedFactors_mul {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
    normalizedFactors (x * y) = normalizedFactors x + normalizedFactors y := by
  have h : (normalize : α → α) = Associates.out ∘ Associates.mk := by
    ext
    rw [Function.comp_apply, Associates.out_mk]
  rw [← Multiset.map_id' (normalizedFactors (x * y)), ← Multiset.map_id' (normalizedFactors x), ←
    Multiset.map_id' (normalizedFactors y), ← Multiset.map_congr rfl normalize_normalized_factor, ←
    Multiset.map_congr rfl normalize_normalized_factor, ←
    Multiset.map_congr rfl normalize_normalized_factor, ← Multiset.map_add, h, ←
    Multiset.map_map Associates.out, eq_comm, ← Multiset.map_map Associates.out]
  refine congr rfl ?_
  apply Multiset.map_mk_eq_map_mk_of_rel
  apply factors_unique
  · intro x hx
    rcases Multiset.mem_add.1 hx with (hx | hx) <;> exact irreducible_of_normalized_factor x hx
  · exact irreducible_of_normalized_factor
  · rw [Multiset.prod_add]
    exact
      ((normalizedFactors_prod hx).mul_mul (normalizedFactors_prod hy)).trans
        (normalizedFactors_prod (mul_ne_zero hx hy)).symm
#align unique_factorization_monoid.normalized_factors_mul UniqueFactorizationMonoid.normalizedFactors_mul

@[simp]
theorem normalizedFactors_pow {x : α} (n : ℕ) :
    normalizedFactors (x ^ n) = n • normalizedFactors x := by
  induction' n with n ih
  · simp
  by_cases h0 : x = 0
  · simp [h0, zero_pow n.succ_ne_zero, smul_zero]
  rw [pow_succ', succ_nsmul', normalizedFactors_mul h0 (pow_ne_zero _ h0), ih]
#align unique_factorization_monoid.normalized_factors_pow UniqueFactorizationMonoid.normalizedFactors_pow

theorem _root_.Irreducible.normalizedFactors_pow {p : α} (hp : Irreducible p) (k : ℕ) :
    normalizedFactors (p ^ k) = Multiset.replicate k (normalize p) := by
  rw [UniqueFactorizationMonoid.normalizedFactors_pow, normalizedFactors_irreducible hp,
    Multiset.nsmul_singleton]
#align irreducible.normalized_factors_pow Irreducible.normalizedFactors_pow

theorem normalizedFactors_prod_eq (s : Multiset α) (hs : ∀ a ∈ s, Irreducible a) :
    normalizedFactors s.prod = s.map normalize := by
  induction' s using Multiset.induction with a s ih
  · rw [Multiset.prod_zero, normalizedFactors_one, Multiset.map_zero]
  · have ia := hs a (Multiset.mem_cons_self a _)
    have ib := fun b h => hs b (Multiset.mem_cons_of_mem h)
    obtain rfl | ⟨b, hb⟩ := s.empty_or_exists_mem
    · rw [Multiset.cons_zero, Multiset.prod_singleton, Multiset.map_singleton,
        normalizedFactors_irreducible ia]
    haveI := nontrivial_of_ne b 0 (ib b hb).ne_zero
    rw [Multiset.prod_cons, Multiset.map_cons,
      normalizedFactors_mul ia.ne_zero (Multiset.prod_ne_zero fun h => (ib 0 h).ne_zero rfl),
      normalizedFactors_irreducible ia, ih ib, Multiset.singleton_add]
#align unique_factorization_monoid.normalized_factors_prod_eq UniqueFactorizationMonoid.normalizedFactors_prod_eq

theorem dvd_iff_normalizedFactors_le_normalizedFactors {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
    x ∣ y ↔ normalizedFactors x ≤ normalizedFactors y := by
  constructor
  · rintro ⟨c, rfl⟩
    simp [hx, right_ne_zero_of_mul hy]
  · rw [← (normalizedFactors_prod hx).dvd_iff_dvd_left, ←
      (normalizedFactors_prod hy).dvd_iff_dvd_right]
    apply Multiset.prod_dvd_prod_of_le
#align unique_factorization_monoid.dvd_iff_normalized_factors_le_normalized_factors UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors

theorem associated_iff_normalizedFactors_eq_normalizedFactors {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
    x ~ᵤ y ↔ normalizedFactors x = normalizedFactors y := by
  refine
    ⟨fun h => ?_, fun h =>
      (normalizedFactors_prod hx).symm.trans (_root_.trans (by rw [h]) (normalizedFactors_prod hy))⟩
  apply le_antisymm <;> rw [← dvd_iff_normalizedFactors_le_normalizedFactors]
  all_goals simp [*, h.dvd, h.symm.dvd]
#align unique_factorization_monoid.associated_iff_normalized_factors_eq_normalized_factors UniqueFactorizationMonoid.associated_iff_normalizedFactors_eq_normalizedFactors

theorem normalizedFactors_of_irreducible_pow {p : α} (hp : Irreducible p) (k : ℕ) :
    normalizedFactors (p ^ k) = Multiset.replicate k (normalize p) := by
  rw [normalizedFactors_pow, normalizedFactors_irreducible hp, Multiset.nsmul_singleton]
#align unique_factorization_monoid.normalized_factors_of_irreducible_pow UniqueFactorizationMonoid.normalizedFactors_of_irreducible_pow

theorem zero_not_mem_normalizedFactors (x : α) : (0 : α) ∉ normalizedFactors x := fun h =>
  Prime.ne_zero (prime_of_normalized_factor _ h) rfl
#align unique_factorization_monoid.zero_not_mem_normalized_factors UniqueFactorizationMonoid.zero_not_mem_normalizedFactors

theorem dvd_of_mem_normalizedFactors {a p : α} (H : p ∈ normalizedFactors a) : p ∣ a := by
  by_cases hcases : a = 0
  · rw [hcases]
    exact dvd_zero p
  · exact dvd_trans (Multiset.dvd_prod H) (Associated.dvd (normalizedFactors_prod hcases))
#align unique_factorization_monoid.dvd_of_mem_normalized_factors UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors

theorem mem_normalizedFactors_iff [Unique αˣ] {p x : α} (hx : x ≠ 0) :
    p ∈ normalizedFactors x ↔ Prime p ∧ p ∣ x := by
  constructor
  · intro h
    exact ⟨prime_of_normalized_factor p h, dvd_of_mem_normalizedFactors h⟩
  · rintro ⟨hprime, hdvd⟩
    obtain ⟨q, hqmem, hqeq⟩ := exists_mem_normalizedFactors_of_dvd hx hprime.irreducible hdvd
    rw [associated_iff_eq] at hqeq
    exact hqeq ▸ hqmem

theorem exists_associated_prime_pow_of_unique_normalized_factor {p r : α}
    (h : ∀ {m}, m ∈ normalizedFactors r → m = p) (hr : r ≠ 0) : ∃ i : ℕ, Associated (p ^ i) r := by
  use Multiset.card.toFun (normalizedFactors r)
  have := UniqueFactorizationMonoid.normalizedFactors_prod hr
  rwa [Multiset.eq_replicate_of_mem fun b => h, Multiset.prod_replicate] at this
#align unique_factorization_monoid.exists_associated_prime_pow_of_unique_normalized_factor UniqueFactorizationMonoid.exists_associated_prime_pow_of_unique_normalized_factor

theorem normalizedFactors_prod_of_prime [Nontrivial α] [Unique αˣ] {m : Multiset α}
    (h : ∀ p ∈ m, Prime p) : normalizedFactors m.prod = m := by
  simpa only [← Multiset.rel_eq, ← associated_eq_eq] using
    prime_factors_unique prime_of_normalized_factor h
      (normalizedFactors_prod (m.prod_ne_zero_of_prime h))
#align unique_factorization_monoid.normalized_factors_prod_of_prime UniqueFactorizationMonoid.normalizedFactors_prod_of_prime

theorem mem_normalizedFactors_eq_of_associated {a b c : α} (ha : a ∈ normalizedFactors c)
    (hb : b ∈ normalizedFactors c) (h : Associated a b) : a = b := by
  rw [← normalize_normalized_factor a ha, ← normalize_normalized_factor b hb,
    normalize_eq_normalize_iff]
  exact Associated.dvd_dvd h
#align unique_factorization_monoid.mem_normalized_factors_eq_of_associated UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated

@[simp]
theorem normalizedFactors_pos (x : α) (hx : x ≠ 0) : 0 < normalizedFactors x ↔ ¬IsUnit x := by
  constructor
  · intro h hx
    obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero h.ne'
    exact
      (prime_of_normalized_factor _ hp).not_unit
        (isUnit_of_dvd_unit (dvd_of_mem_normalizedFactors hp) hx)
  · intro h
    obtain ⟨p, hp⟩ := exists_mem_normalizedFactors hx h
    exact
      bot_lt_iff_ne_bot.mpr
        (mt Multiset.eq_zero_iff_forall_not_mem.mp (not_forall.mpr ⟨p, not_not.mpr hp⟩))
#align unique_factorization_monoid.normalized_factors_pos UniqueFactorizationMonoid.normalizedFactors_pos

theorem dvdNotUnit_iff_normalizedFactors_lt_normalizedFactors {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
    DvdNotUnit x y ↔ normalizedFactors x < normalizedFactors y := by
  constructor
  · rintro ⟨_, c, hc, rfl⟩
    simp only [hx, right_ne_zero_of_mul hy, normalizedFactors_mul, Ne, not_false_iff,
      lt_add_iff_pos_right, normalizedFactors_pos, hc]
  · intro h
    exact
      dvdNotUnit_of_dvd_of_not_dvd
        ((dvd_iff_normalizedFactors_le_normalizedFactors hx hy).mpr h.le)
        (mt (dvd_iff_normalizedFactors_le_normalizedFactors hy hx).mp h.not_le)
#align unique_factorization_monoid.dvd_not_unit_iff_normalized_factors_lt_normalized_factors UniqueFactorizationMonoid.dvdNotUnit_iff_normalizedFactors_lt_normalizedFactors

theorem normalizedFactors_multiset_prod (s : Multiset α) (hs : 0 ∉ s) :
    normalizedFactors (s.prod) = (s.map normalizedFactors).sum := by
  cases subsingleton_or_nontrivial α
  · obtain rfl : s = 0 := by
      apply Multiset.eq_zero_of_forall_not_mem
      intro _
      convert hs
    simp
  induction s using Multiset.induction with
  | empty => simp
  | cons _ _ IH =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, normalizedFactors_mul, IH]
    · exact fun h ↦ hs (Multiset.mem_cons_of_mem h)
    · exact fun h ↦ hs (h ▸ Multiset.mem_cons_self _ _)
    · apply Multiset.prod_ne_zero
      exact fun h ↦ hs (Multiset.mem_cons_of_mem h)

end UniqueFactorizationMonoid

namespace UniqueFactorizationMonoid

open scoped Classical

open Multiset Associates

variable [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α]

/-- Noncomputably defines a `normalizationMonoid` structure on a `UniqueFactorizationMonoid`. -/
protected noncomputable def normalizationMonoid : NormalizationMonoid α :=
  normalizationMonoidOfMonoidHomRightInverse
    { toFun := fun a : Associates α =>
        if a = 0 then 0
        else
          ((normalizedFactors a).map
              (Classical.choose mk_surjective.hasRightInverse : Associates α → α)).prod
      map_one' := by nontriviality α; simp
      map_mul' := fun x y => by
        by_cases hx : x = 0
        · simp [hx]
        by_cases hy : y = 0
        · simp [hy]
        simp [hx, hy] }
    (by
      intro x
      dsimp
      by_cases hx : x = 0
      · simp [hx]
      have h : Associates.mkMonoidHom ∘ Classical.choose mk_surjective.hasRightInverse =
          (id : Associates α → Associates α) := by
        ext x
        rw [Function.comp_apply, mkMonoidHom_apply,
          Classical.choose_spec mk_surjective.hasRightInverse x]
        rfl
      rw [if_neg hx, ← mkMonoidHom_apply, MonoidHom.map_multiset_prod, map_map, h, map_id, ←
        associated_iff_eq]
      apply normalizedFactors_prod hx)
#align unique_factorization_monoid.normalization_monoid UniqueFactorizationMonoid.normalizationMonoid

end UniqueFactorizationMonoid

namespace UniqueFactorizationMonoid

variable {R : Type*} [CancelCommMonoidWithZero R] [UniqueFactorizationMonoid R]

theorem isRelPrime_iff_no_prime_factors {a b : R} (ha : a ≠ 0) :
    IsRelPrime a b ↔ ∀ ⦃d⦄, d ∣ a → d ∣ b → ¬Prime d :=
  ⟨fun h _ ha hb ↦ (·.not_unit <| h ha hb), fun h ↦ WfDvdMonoid.isRelPrime_of_no_irreducible_factors
    (ha ·.1) fun _ irr ha hb ↦ h ha hb (UniqueFactorizationMonoid.irreducible_iff_prime.mp irr)⟩
#align unique_factorization_monoid.no_factors_of_no_prime_factors UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors

/-- Euclid's lemma: if `a ∣ b * c` and `a` and `c` have no common prime factors, `a ∣ b`.
Compare `IsCoprime.dvd_of_dvd_mul_left`. -/
theorem dvd_of_dvd_mul_left_of_no_prime_factors {a b c : R} (ha : a ≠ 0)
    (h : ∀ ⦃d⦄, d ∣ a → d ∣ c → ¬Prime d) : a ∣ b * c → a ∣ b :=
  ((isRelPrime_iff_no_prime_factors ha).mpr h).dvd_of_dvd_mul_right
#align unique_factorization_monoid.dvd_of_dvd_mul_left_of_no_prime_factors UniqueFactorizationMonoid.dvd_of_dvd_mul_left_of_no_prime_factors

/-- Euclid's lemma: if `a ∣ b * c` and `a` and `b` have no common prime factors, `a ∣ c`.
Compare `IsCoprime.dvd_of_dvd_mul_right`. -/
theorem dvd_of_dvd_mul_right_of_no_prime_factors {a b c : R} (ha : a ≠ 0)
    (no_factors : ∀ {d}, d ∣ a → d ∣ b → ¬Prime d) : a ∣ b * c → a ∣ c := by
  simpa [mul_comm b c] using dvd_of_dvd_mul_left_of_no_prime_factors ha @no_factors
#align unique_factorization_monoid.dvd_of_dvd_mul_right_of_no_prime_factors UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors

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
      cases' p_prime.left_dvd_or_dvd_right_of_dvd_mul q_dvd_pa' with p_dvd_q q_dvd_a'
      · have : p ∣ c' * b' := dvd_mul_of_dvd_right (p_dvd_q.trans q_dvd_b') _
        contradiction
      exact coprime q_dvd_a' q_dvd_b'
#align unique_factorization_monoid.exists_reduced_factors UniqueFactorizationMonoid.exists_reduced_factors

theorem exists_reduced_factors' (a b : R) (hb : b ≠ 0) :
    ∃ a' b' c', IsRelPrime a' b' ∧ c' * a' = a ∧ c' * b' = b :=
  let ⟨b', a', c', no_factor, hb, ha⟩ := exists_reduced_factors b hb a
  ⟨a', b', c', fun _ hpb hpa => no_factor hpa hpb, ha, hb⟩
#align unique_factorization_monoid.exists_reduced_factors' UniqueFactorizationMonoid.exists_reduced_factors'

theorem pow_right_injective {a : R} (ha0 : a ≠ 0) (ha1 : ¬IsUnit a) :
    Function.Injective (a ^ · : ℕ → R) := by
  letI := Classical.decEq R
  intro i j hij
  letI : Nontrivial R := ⟨⟨a, 0, ha0⟩⟩
  letI : NormalizationMonoid R := UniqueFactorizationMonoid.normalizationMonoid
  obtain ⟨p', hp', dvd'⟩ := WfDvdMonoid.exists_irreducible_factor ha1 ha0
  obtain ⟨p, mem, _⟩ := exists_mem_normalizedFactors_of_dvd ha0 hp' dvd'
  have := congr_arg (fun x => Multiset.count p (normalizedFactors x)) hij
  simp only [normalizedFactors_pow, Multiset.count_nsmul] at this
  exact mul_right_cancel₀ (Multiset.count_ne_zero.mpr mem) this
#align unique_factorization_monoid.pow_right_injective UniqueFactorizationMonoid.pow_right_injective

theorem pow_eq_pow_iff {a : R} (ha0 : a ≠ 0) (ha1 : ¬IsUnit a) {i j : ℕ} : a ^ i = a ^ j ↔ i = j :=
  (pow_right_injective ha0 ha1).eq_iff
#align unique_factorization_monoid.pow_eq_pow_iff UniqueFactorizationMonoid.pow_eq_pow_iff

section multiplicity

variable [NormalizationMonoid R]
variable [DecidableRel (Dvd.dvd : R → R → Prop)]

open multiplicity Multiset

theorem le_multiplicity_iff_replicate_le_normalizedFactors {a b : R} {n : ℕ} (ha : Irreducible a)
    (hb : b ≠ 0) :
    ↑n ≤ multiplicity a b ↔ replicate n (normalize a) ≤ normalizedFactors b := by
  rw [← pow_dvd_iff_le_multiplicity]
  revert b
  induction' n with n ih; · simp
  intro b hb
  constructor
  · rintro ⟨c, rfl⟩
    rw [Ne, pow_succ', mul_assoc, mul_eq_zero, not_or] at hb
    rw [pow_succ', mul_assoc, normalizedFactors_mul hb.1 hb.2, replicate_succ,
      normalizedFactors_irreducible ha, singleton_add, cons_le_cons_iff, ← ih hb.2]
    apply Dvd.intro _ rfl
  · rw [Multiset.le_iff_exists_add]
    rintro ⟨u, hu⟩
    rw [← (normalizedFactors_prod hb).dvd_iff_dvd_right, hu, prod_add, prod_replicate]
    exact (Associated.pow_pow <| associated_normalize a).dvd.trans (Dvd.intro u.prod rfl)
#align unique_factorization_monoid.le_multiplicity_iff_replicate_le_normalized_factors UniqueFactorizationMonoid.le_multiplicity_iff_replicate_le_normalizedFactors

/-- The multiplicity of an irreducible factor of a nonzero element is exactly the number of times
the normalized factor occurs in the `normalizedFactors`.

See also `count_normalizedFactors_eq` which expands the definition of `multiplicity`
to produce a specification for `count (normalizedFactors _) _`..
-/
theorem multiplicity_eq_count_normalizedFactors [DecidableEq R] {a b : R} (ha : Irreducible a)
    (hb : b ≠ 0) : multiplicity a b = (normalizedFactors b).count (normalize a) := by
  apply le_antisymm
  · apply PartENat.le_of_lt_add_one
    rw [← Nat.cast_one, ← Nat.cast_add, lt_iff_not_ge, ge_iff_le,
      le_multiplicity_iff_replicate_le_normalizedFactors ha hb, ← le_count_iff_replicate_le]
    simp
  rw [le_multiplicity_iff_replicate_le_normalizedFactors ha hb, ← le_count_iff_replicate_le]
#align unique_factorization_monoid.multiplicity_eq_count_normalized_factors UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors


/-- The number of times an irreducible factor `p` appears in `normalizedFactors x` is defined by
the number of times it divides `x`.

See also `multiplicity_eq_count_normalizedFactors` if `n` is given by `multiplicity p x`.
-/
theorem count_normalizedFactors_eq [DecidableEq R] {p x : R} (hp : Irreducible p)
    (hnorm : normalize p = p) {n : ℕ} (hle : p ^ n ∣ x) (hlt : ¬p ^ (n + 1) ∣ x) :
    (normalizedFactors x).count p = n := by
  letI : DecidableRel ((· ∣ ·) : R → R → Prop) := fun _ _ => Classical.propDecidable _
  by_cases hx0 : x = 0
  · simp [hx0] at hlt
  rw [← PartENat.natCast_inj]
  convert (multiplicity_eq_count_normalizedFactors hp hx0).symm
  · exact hnorm.symm
  exact (multiplicity.eq_coe_iff.mpr ⟨hle, hlt⟩).symm
#align unique_factorization_monoid.count_normalized_factors_eq UniqueFactorizationMonoid.count_normalizedFactors_eq

/-- The number of times an irreducible factor `p` appears in `normalizedFactors x` is defined by
the number of times it divides `x`. This is a slightly more general version of
`UniqueFactorizationMonoid.count_normalizedFactors_eq` that allows `p = 0`.

See also `multiplicity_eq_count_normalizedFactors` if `n` is given by `multiplicity p x`.
-/
theorem count_normalizedFactors_eq' [DecidableEq R] {p x : R} (hp : p = 0 ∨ Irreducible p)
    (hnorm : normalize p = p) {n : ℕ} (hle : p ^ n ∣ x) (hlt : ¬p ^ (n + 1) ∣ x) :
    (normalizedFactors x).count p = n := by
  rcases hp with (rfl | hp)
  · cases n
    · exact count_eq_zero.2 (zero_not_mem_normalizedFactors _)
    · rw [zero_pow (Nat.succ_ne_zero _)] at hle hlt
      exact absurd hle hlt
  · exact count_normalizedFactors_eq hp hnorm hle hlt
#align unique_factorization_monoid.count_normalized_factors_eq' UniqueFactorizationMonoid.count_normalizedFactors_eq'

/-- Deprecated. Use `WfDvdMonoid.max_power_factor` instead. -/
@[deprecated WfDvdMonoid.max_power_factor]
theorem max_power_factor {a₀ x : R} (h : a₀ ≠ 0) (hx : Irreducible x) :
    ∃ n : ℕ, ∃ a : R, ¬x ∣ a ∧ a₀ = x ^ n * a := WfDvdMonoid.max_power_factor h hx
#align unique_factorization_monoid.max_power_factor UniqueFactorizationMonoid.max_power_factor

end multiplicity

section Multiplicative

variable [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α]
variable {β : Type*} [CancelCommMonoidWithZero β]

theorem prime_pow_coprime_prod_of_coprime_insert [DecidableEq α] {s : Finset α} (i : α → ℕ) (p : α)
    (hps : p ∉ s) (is_prime : ∀ q ∈ insert p s, Prime q)
    (is_coprime : ∀ᵉ (q ∈ insert p s) (q' ∈ insert p s), q ∣ q' → q = q') :
    IsRelPrime (p ^ i p) (∏ p' ∈ s, p' ^ i p') := by
  have hp := is_prime _ (Finset.mem_insert_self _ _)
  refine (isRelPrime_iff_no_prime_factors <| pow_ne_zero _ hp.ne_zero).mpr ?_
  intro d hdp hdprod hd
  apply hps
  replace hdp := hd.dvd_of_dvd_pow hdp
  obtain ⟨q, q_mem', hdq⟩ := hd.exists_mem_multiset_dvd hdprod
  obtain ⟨q, q_mem, rfl⟩ := Multiset.mem_map.mp q_mem'
  replace hdq := hd.dvd_of_dvd_pow hdq
  have : p ∣ q := dvd_trans (hd.irreducible.dvd_symm hp.irreducible hdp) hdq
  convert q_mem
  rw [Finset.mem_val,
    is_coprime _ (Finset.mem_insert_self p s) _ (Finset.mem_insert_of_mem q_mem) this]
#align unique_factorization_monoid.prime_pow_coprime_prod_of_coprime_insert UniqueFactorizationMonoid.prime_pow_coprime_prod_of_coprime_insert

/-- If `P` holds for units and powers of primes,
and `P x ∧ P y` for coprime `x, y` implies `P (x * y)`,
then `P` holds on a product of powers of distinct primes. -/
-- @[elab_as_elim] Porting note: commented out
theorem induction_on_prime_power {P : α → Prop} (s : Finset α) (i : α → ℕ)
    (is_prime : ∀ p ∈ s, Prime p) (is_coprime : ∀ᵉ (p ∈ s) (q ∈ s), p ∣ q → p = q)
    (h1 : ∀ {x}, IsUnit x → P x) (hpr : ∀ {p} (i : ℕ), Prime p → P (p ^ i))
    (hcp : ∀ {x y}, IsRelPrime x y → P x → P y → P (x * y)) :
    P (∏ p ∈ s, p ^ i p) := by
  letI := Classical.decEq α
  induction' s using Finset.induction_on with p f' hpf' ih
  · simpa using h1 isUnit_one
  rw [Finset.prod_insert hpf']
  exact
    hcp (prime_pow_coprime_prod_of_coprime_insert i p hpf' is_prime is_coprime)
      (hpr (i p) (is_prime _ (Finset.mem_insert_self _ _)))
      (ih (fun q hq => is_prime _ (Finset.mem_insert_of_mem hq)) fun q hq q' hq' =>
        is_coprime _ (Finset.mem_insert_of_mem hq) _ (Finset.mem_insert_of_mem hq'))
#align unique_factorization_monoid.induction_on_prime_power UniqueFactorizationMonoid.induction_on_prime_power

/-- If `P` holds for `0`, units and powers of primes,
and `P x ∧ P y` for coprime `x, y` implies `P (x * y)`,
then `P` holds on all `a : α`. -/
@[elab_as_elim]
theorem induction_on_coprime {P : α → Prop} (a : α) (h0 : P 0) (h1 : ∀ {x}, IsUnit x → P x)
    (hpr : ∀ {p} (i : ℕ), Prime p → P (p ^ i))
    (hcp : ∀ {x y}, IsRelPrime x y → P x → P y → P (x * y)) : P a := by
  letI := Classical.decEq α
  have P_of_associated : ∀ {x y}, Associated x y → P x → P y := by
    rintro x y ⟨u, rfl⟩ hx
    exact hcp (fun p _ hpx => isUnit_of_dvd_unit hpx u.isUnit) hx (h1 u.isUnit)
  by_cases ha0 : a = 0
  · rwa [ha0]
  haveI : Nontrivial α := ⟨⟨_, _, ha0⟩⟩
  letI : NormalizationMonoid α := UniqueFactorizationMonoid.normalizationMonoid
  refine P_of_associated (normalizedFactors_prod ha0) ?_
  rw [← (normalizedFactors a).map_id, Finset.prod_multiset_map_count]
  refine induction_on_prime_power _ _ ?_ ?_ @h1 @hpr @hcp <;> simp only [Multiset.mem_toFinset]
  · apply prime_of_normalized_factor
  · apply normalizedFactors_eq_of_dvd
#align unique_factorization_monoid.induction_on_coprime UniqueFactorizationMonoid.induction_on_coprime

/-- If `f` maps `p ^ i` to `(f p) ^ i` for primes `p`, and `f`
is multiplicative on coprime elements, then `f` is multiplicative on all products of primes. -/
-- @[elab_as_elim] Porting note: commented out
theorem multiplicative_prime_power {f : α → β} (s : Finset α) (i j : α → ℕ)
    (is_prime : ∀ p ∈ s, Prime p) (is_coprime : ∀ᵉ (p ∈ s) (q ∈ s), p ∣ q → p = q)
    (h1 : ∀ {x y}, IsUnit y → f (x * y) = f x * f y)
    (hpr : ∀ {p} (i : ℕ), Prime p → f (p ^ i) = f p ^ i)
    (hcp : ∀ {x y}, IsRelPrime x y → f (x * y) = f x * f y) :
    f (∏ p ∈ s, p ^ (i p + j p)) = f (∏ p ∈ s, p ^ i p) * f (∏ p ∈ s, p ^ j p) := by
  letI := Classical.decEq α
  induction' s using Finset.induction_on with p s hps ih
  · simpa using h1 isUnit_one
  have hpr_p := is_prime _ (Finset.mem_insert_self _ _)
  have hpr_s : ∀ p ∈ s, Prime p := fun p hp => is_prime _ (Finset.mem_insert_of_mem hp)
  have hcp_p := fun i => prime_pow_coprime_prod_of_coprime_insert i p hps is_prime is_coprime
  have hcp_s : ∀ᵉ (p ∈ s) (q ∈ s), p ∣ q → p = q := fun p hp q hq =>
    is_coprime p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_of_mem hq)
  rw [Finset.prod_insert hps, Finset.prod_insert hps, Finset.prod_insert hps, hcp (hcp_p _),
    hpr _ hpr_p, hcp (hcp_p _), hpr _ hpr_p, hcp (hcp_p (fun p => i p + j p)), hpr _ hpr_p,
    ih hpr_s hcp_s, pow_add, mul_assoc, mul_left_comm (f p ^ j p), mul_assoc]
#align unique_factorization_monoid.multiplicative_prime_power UniqueFactorizationMonoid.multiplicative_prime_power

/-- If `f` maps `p ^ i` to `(f p) ^ i` for primes `p`, and `f`
is multiplicative on coprime elements, then `f` is multiplicative everywhere. -/
theorem multiplicative_of_coprime (f : α → β) (a b : α) (h0 : f 0 = 0)
    (h1 : ∀ {x y}, IsUnit y → f (x * y) = f x * f y)
    (hpr : ∀ {p} (i : ℕ), Prime p → f (p ^ i) = f p ^ i)
    (hcp : ∀ {x y}, IsRelPrime x y → f (x * y) = f x * f y) :
    f (a * b) = f a * f b := by
  letI := Classical.decEq α
  by_cases ha0 : a = 0
  · rw [ha0, zero_mul, h0, zero_mul]
  by_cases hb0 : b = 0
  · rw [hb0, mul_zero, h0, mul_zero]
  by_cases hf1 : f 1 = 0
  · calc
      f (a * b) = f (a * b * 1) := by rw [mul_one]
      _ = 0 := by simp only [h1 isUnit_one, hf1, mul_zero]
      _ = f a * f (b * 1) := by simp only [h1 isUnit_one, hf1, mul_zero]
      _ = f a * f b := by rw [mul_one]
  haveI : Nontrivial α := ⟨⟨_, _, ha0⟩⟩
  letI : NormalizationMonoid α := UniqueFactorizationMonoid.normalizationMonoid
  suffices
      f (∏ p ∈ (normalizedFactors a).toFinset ∪ (normalizedFactors b).toFinset,
        p ^ ((normalizedFactors a).count p + (normalizedFactors b).count p)) =
      f (∏ p ∈ (normalizedFactors a).toFinset ∪ (normalizedFactors b).toFinset,
        p ^ (normalizedFactors a).count p) *
      f (∏ p ∈ (normalizedFactors a).toFinset ∪ (normalizedFactors b).toFinset,
        p ^ (normalizedFactors b).count p) by
    obtain ⟨ua, a_eq⟩ := normalizedFactors_prod ha0
    obtain ⟨ub, b_eq⟩ := normalizedFactors_prod hb0
    rw [← a_eq, ← b_eq, mul_right_comm (Multiset.prod (normalizedFactors a)) ua
        (Multiset.prod (normalizedFactors b) * ub), h1 ua.isUnit, h1 ub.isUnit, h1 ua.isUnit, ←
      mul_assoc, h1 ub.isUnit, mul_right_comm _ (f ua), ← mul_assoc]
    congr
    rw [← (normalizedFactors a).map_id, ← (normalizedFactors b).map_id,
      Finset.prod_multiset_map_count, Finset.prod_multiset_map_count,
      Finset.prod_subset (Finset.subset_union_left (s₂:=(normalizedFactors b).toFinset)),
      Finset.prod_subset (Finset.subset_union_right (s₂:=(normalizedFactors b).toFinset)), ←
      Finset.prod_mul_distrib]
    · simp_rw [id, ← pow_add, this]
    all_goals simp only [Multiset.mem_toFinset]
    · intro p _ hpb
      simp [hpb]
    · intro p _ hpa
      simp [hpa]
  refine multiplicative_prime_power _ _ _ ?_ ?_ @h1 @hpr @hcp
  all_goals simp only [Multiset.mem_toFinset, Finset.mem_union]
  · rintro p (hpa | hpb) <;> apply prime_of_normalized_factor <;> assumption
  · rintro p (hp | hp) q (hq | hq) hdvd <;>
      rw [← normalize_normalized_factor _ hp, ← normalize_normalized_factor _ hq] <;>
      exact
        normalize_eq_normalize hdvd
          ((prime_of_normalized_factor _ hp).irreducible.dvd_symm
            (prime_of_normalized_factor _ hq).irreducible hdvd)
#align unique_factorization_monoid.multiplicative_of_coprime UniqueFactorizationMonoid.multiplicative_of_coprime

end Multiplicative

end UniqueFactorizationMonoid

namespace Associates

open UniqueFactorizationMonoid Associated Multiset

variable [CancelCommMonoidWithZero α]

/-- `FactorSet α` representation elements of unique factorization domain as multisets.
`Multiset α` produced by `normalizedFactors` are only unique up to associated elements, while the
multisets in `FactorSet α` are unique by equality and restricted to irreducible elements. This
gives us a representation of each element as a unique multisets (or the added ⊤ for 0), which has a
complete lattice structure. Infimum is the greatest common divisor and supremum is the least common
multiple.
-/
abbrev FactorSet.{u} (α : Type u) [CancelCommMonoidWithZero α] : Type u :=
  WithTop (Multiset { a : Associates α // Irreducible a })
#align associates.factor_set Associates.FactorSet

attribute [local instance] Associated.setoid

theorem FactorSet.coe_add {a b : Multiset { a : Associates α // Irreducible a }} :
    (↑(a + b) : FactorSet α) = a + b := by norm_cast
#align associates.factor_set.coe_add Associates.FactorSet.coe_add

theorem FactorSet.sup_add_inf_eq_add [DecidableEq (Associates α)] :
    ∀ a b : FactorSet α, a ⊔ b + a ⊓ b = a + b
  | ⊤, b => show ⊤ ⊔ b + ⊤ ⊓ b = ⊤ + b by simp
  | a, ⊤ => show a ⊔ ⊤ + a ⊓ ⊤ = a + ⊤ by simp
  | WithTop.some a, WithTop.some b =>
    show (a : FactorSet α) ⊔ b + (a : FactorSet α) ⊓ b = a + b by
      rw [← WithTop.coe_sup, ← WithTop.coe_inf, ← WithTop.coe_add, ← WithTop.coe_add,
        WithTop.coe_eq_coe]
      exact Multiset.union_add_inter _ _
#align associates.factor_set.sup_add_inf_eq_add Associates.FactorSet.sup_add_inf_eq_add

/-- Evaluates the product of a `FactorSet` to be the product of the corresponding multiset,
  or `0` if there is none. -/
def FactorSet.prod : FactorSet α → Associates α
  | ⊤ => 0
  | WithTop.some s => (s.map (↑)).prod
#align associates.factor_set.prod Associates.FactorSet.prod

@[simp]
theorem prod_top : (⊤ : FactorSet α).prod = 0 :=
  rfl
#align associates.prod_top Associates.prod_top

@[simp]
theorem prod_coe {s : Multiset { a : Associates α // Irreducible a }} :
    FactorSet.prod (s : FactorSet α) = (s.map (↑)).prod :=
  rfl
#align associates.prod_coe Associates.prod_coe

@[simp]
theorem prod_add : ∀ a b : FactorSet α, (a + b).prod = a.prod * b.prod
  | ⊤, b => show (⊤ + b).prod = (⊤ : FactorSet α).prod * b.prod by simp
  | a, ⊤ => show (a + ⊤).prod = a.prod * (⊤ : FactorSet α).prod by simp
  | WithTop.some a, WithTop.some b => by
    rw [← FactorSet.coe_add, prod_coe, prod_coe, prod_coe, Multiset.map_add, Multiset.prod_add]
#align associates.prod_add Associates.prod_add

@[gcongr]
theorem prod_mono : ∀ {a b : FactorSet α}, a ≤ b → a.prod ≤ b.prod
  | ⊤, b, h => by
    have : b = ⊤ := top_unique h
    rw [this, prod_top]
  | a, ⊤, _ => show a.prod ≤ (⊤ : FactorSet α).prod by simp
  | WithTop.some a, WithTop.some b, h =>
    prod_le_prod <| Multiset.map_le_map <| WithTop.coe_le_coe.1 <| h
#align associates.prod_mono Associates.prod_mono

theorem FactorSet.prod_eq_zero_iff [Nontrivial α] (p : FactorSet α) : p.prod = 0 ↔ p = ⊤ := by
  unfold FactorSet at p
  induction p  -- TODO: `induction_eliminator` doesn't work with `abbrev`
  · simp only [iff_self_iff, eq_self_iff_true, Associates.prod_top]
  · rw [prod_coe, Multiset.prod_eq_zero_iff, Multiset.mem_map, eq_false WithTop.coe_ne_top,
      iff_false_iff, not_exists]
    exact fun a => not_and_of_not_right _ a.prop.ne_zero
#align associates.factor_set.prod_eq_zero_iff Associates.FactorSet.prod_eq_zero_iff

section count

variable [DecidableEq (Associates α)]

/-- `bcount p s` is the multiplicity of `p` in the FactorSet `s` (with bundled `p`)-/
def bcount (p : { a : Associates α // Irreducible a }) :
    FactorSet α → ℕ
  | ⊤ => 0
  | WithTop.some s => s.count p
#align associates.bcount Associates.bcount

variable [∀ p : Associates α, Decidable (Irreducible p)] {p : Associates α}

/-- `count p s` is the multiplicity of the irreducible `p` in the FactorSet `s`.

If `p` is not irreducible, `count p s` is defined to be `0`. -/
def count (p : Associates α) : FactorSet α → ℕ :=
  if hp : Irreducible p then bcount ⟨p, hp⟩ else 0
#align associates.count Associates.count

@[simp]
theorem count_some (hp : Irreducible p) (s : Multiset _) :
    count p (WithTop.some s) = s.count ⟨p, hp⟩ := by
  simp only [count, dif_pos hp, bcount]
#align associates.count_some Associates.count_some

@[simp]
theorem count_zero (hp : Irreducible p) : count p (0 : FactorSet α) = 0 := by
  simp only [count, dif_pos hp, bcount, Multiset.count_zero]
#align associates.count_zero Associates.count_zero

theorem count_reducible (hp : ¬Irreducible p) : count p = 0 := dif_neg hp
#align associates.count_reducible Associates.count_reducible

end count

section Mem

/-- membership in a FactorSet (bundled version) -/
def BfactorSetMem : { a : Associates α // Irreducible a } → FactorSet α → Prop
  | _, ⊤ => True
  | p, some l => p ∈ l
#align associates.bfactor_set_mem Associates.BfactorSetMem

/-- `FactorSetMem p s` is the predicate that the irreducible `p` is a member of
`s : FactorSet α`.

If `p` is not irreducible, `p` is not a member of any `FactorSet`. -/
def FactorSetMem (p : Associates α) (s : FactorSet α) : Prop :=
  letI : Decidable (Irreducible p) := Classical.dec _
  if hp : Irreducible p then BfactorSetMem ⟨p, hp⟩ s else False
#align associates.factor_set_mem Associates.FactorSetMem

instance : Membership (Associates α) (FactorSet α) :=
  ⟨FactorSetMem⟩

@[simp]
theorem factorSetMem_eq_mem (p : Associates α) (s : FactorSet α) : FactorSetMem p s = (p ∈ s) :=
  rfl
#align associates.factor_set_mem_eq_mem Associates.factorSetMem_eq_mem

theorem mem_factorSet_top {p : Associates α} {hp : Irreducible p} : p ∈ (⊤ : FactorSet α) := by
  dsimp only [Membership.mem]; dsimp only [FactorSetMem]; split_ifs; exact trivial
#align associates.mem_factor_set_top Associates.mem_factorSet_top

theorem mem_factorSet_some {p : Associates α} {hp : Irreducible p}
    {l : Multiset { a : Associates α // Irreducible a }} :
    p ∈ (l : FactorSet α) ↔ Subtype.mk p hp ∈ l := by
  dsimp only [Membership.mem]; dsimp only [FactorSetMem]; split_ifs; rfl
#align associates.mem_factor_set_some Associates.mem_factorSet_some

theorem reducible_not_mem_factorSet {p : Associates α} (hp : ¬Irreducible p) (s : FactorSet α) :
    ¬p ∈ s := fun h ↦ by
  rwa [← factorSetMem_eq_mem, FactorSetMem, dif_neg hp] at h
#align associates.reducible_not_mem_factor_set Associates.reducible_not_mem_factorSet

theorem irreducible_of_mem_factorSet {p : Associates α} {s : FactorSet α} (h : p ∈ s) :
    Irreducible p :=
  by_contra fun hp ↦ reducible_not_mem_factorSet hp s h

end Mem

variable [UniqueFactorizationMonoid α]

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
#align associates.unique' Associates.unique'

theorem FactorSet.unique [Nontrivial α] {p q : FactorSet α} (h : p.prod = q.prod) : p = q := by
  -- TODO: `induction_eliminator` doesn't work with `abbrev`
  unfold FactorSet at p q
  induction p <;> induction q
  · rfl
  · rw [eq_comm, ← FactorSet.prod_eq_zero_iff, ← h, Associates.prod_top]
  · rw [← FactorSet.prod_eq_zero_iff, h, Associates.prod_top]
  · congr 1
    rw [← Multiset.map_eq_map Subtype.coe_injective]
    apply unique' _ _ h <;>
      · intro a ha
        obtain ⟨⟨a', irred⟩, -, rfl⟩ := Multiset.mem_map.mp ha
        rwa [Subtype.coe_mk]
#align associates.factor_set.unique Associates.FactorSet.unique

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
#align associates.prod_le_prod_iff_le Associates.prod_le_prod_iff_le

/-- This returns the multiset of irreducible factors as a `FactorSet`,
  a multiset of irreducible associates `WithTop`. -/
noncomputable def factors' (a : α) : Multiset { a : Associates α // Irreducible a } :=
  (factors a).pmap (fun a ha => ⟨Associates.mk a, irreducible_mk.2 ha⟩) irreducible_of_factor
#align associates.factors' Associates.factors'

@[simp]
theorem map_subtype_coe_factors' {a : α} :
    (factors' a).map (↑) = (factors a).map Associates.mk := by
  simp [factors', Multiset.map_pmap, Multiset.pmap_eq_map]
#align associates.map_subtype_coe_factors' Associates.map_subtype_coe_factors'

theorem factors'_cong {a b : α} (h : a ~ᵤ b) : factors' a = factors' b := by
  obtain rfl | hb := eq_or_ne b 0
  · rw [associated_zero_iff_eq_zero] at h
    rw [h]
  have ha : a ≠ 0 := by
    contrapose! hb with ha
    rw [← associated_zero_iff_eq_zero, ← ha]
    exact h.symm
  rw [← Multiset.map_eq_map Subtype.coe_injective, map_subtype_coe_factors',
    map_subtype_coe_factors', ← rel_associated_iff_map_eq_map]
  exact
    factors_unique irreducible_of_factor irreducible_of_factor
      ((factors_prod ha).trans <| h.trans <| (factors_prod hb).symm)
#align associates.factors'_cong Associates.factors'_cong

/-- This returns the multiset of irreducible factors of an associate as a `FactorSet`,
  a multiset of irreducible associates `WithTop`. -/
noncomputable def factors (a : Associates α) : FactorSet α := by
  classical refine if h : a = 0 then ⊤ else Quotient.hrecOn a (fun x _ => factors' x) ?_ h
  intro a b hab
  apply Function.hfunext
  · have : a ~ᵤ 0 ↔ b ~ᵤ 0 := Iff.intro (fun ha0 => hab.symm.trans ha0) fun hb0 => hab.trans hb0
    simp only [associated_zero_iff_eq_zero] at this
    simp only [quotient_mk_eq_mk, this, mk_eq_zero]
  exact fun ha hb _ => heq_of_eq <| congr_arg some <| factors'_cong hab
#align associates.factors Associates.factors

@[simp]
theorem factors_zero : (0 : Associates α).factors = ⊤ :=
  dif_pos rfl
#align associates.factors_0 Associates.factors_zero

@[deprecated] alias factors_0 := factors_zero -- 2024-03-16

@[simp]
theorem factors_mk (a : α) (h : a ≠ 0) : (Associates.mk a).factors = factors' a := by
  classical
    apply dif_neg
    apply mt mk_eq_zero.1 h
#align associates.factors_mk Associates.factors_mk

@[simp]
theorem factors_prod (a : Associates α) : a.factors.prod = a := by
  rcases Associates.mk_surjective a with ⟨a, rfl⟩
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · simp [ha, prod_mk, mk_eq_mk_iff_associated, UniqueFactorizationMonoid.factors_prod,
      -Quotient.eq]
#align associates.factors_prod Associates.factors_prod

@[simp]
theorem prod_factors [Nontrivial α] (s : FactorSet α) : s.prod.factors = s :=
  FactorSet.unique <| factors_prod _
#align associates.prod_factors Associates.prod_factors

@[nontriviality]
theorem factors_subsingleton [Subsingleton α] {a : Associates α} : a.factors = ⊤ := by
  have : Subsingleton (Associates α) := inferInstance
  convert factors_zero
#align associates.factors_subsingleton Associates.factors_subsingleton

theorem factors_eq_top_iff_zero {a : Associates α} : a.factors = ⊤ ↔ a = 0 := by
  nontriviality α
  exact ⟨fun h ↦ by rwa [← factors_prod a, FactorSet.prod_eq_zero_iff], fun h ↦ h ▸ factors_zero⟩
#align associates.factors_eq_none_iff_zero Associates.factors_eq_top_iff_zero

@[deprecated] alias factors_eq_none_iff_zero := factors_eq_top_iff_zero

theorem factors_eq_some_iff_ne_zero {a : Associates α} :
    (∃ s : Multiset { p : Associates α // Irreducible p }, a.factors = s) ↔ a ≠ 0 := by
  simp_rw [@eq_comm _ a.factors, ← WithTop.ne_top_iff_exists]
  exact factors_eq_top_iff_zero.not
#align associates.factors_eq_some_iff_ne_zero Associates.factors_eq_some_iff_ne_zero

theorem eq_of_factors_eq_factors {a b : Associates α} (h : a.factors = b.factors) : a = b := by
  have : a.factors.prod = b.factors.prod := by rw [h]
  rwa [factors_prod, factors_prod] at this
#align associates.eq_of_factors_eq_factors Associates.eq_of_factors_eq_factors

theorem eq_of_prod_eq_prod [Nontrivial α] {a b : FactorSet α} (h : a.prod = b.prod) : a = b := by
  have : a.prod.factors = b.prod.factors := by rw [h]
  rwa [prod_factors, prod_factors] at this
#align associates.eq_of_prod_eq_prod Associates.eq_of_prod_eq_prod

@[simp]
theorem factors_mul (a b : Associates α) : (a * b).factors = a.factors + b.factors := by
  nontriviality α
  refine eq_of_prod_eq_prod <| eq_of_factors_eq_factors ?_
  rw [prod_add, factors_prod, factors_prod, factors_prod]
#align associates.factors_mul Associates.factors_mul

@[gcongr]
theorem factors_mono : ∀ {a b : Associates α}, a ≤ b → a.factors ≤ b.factors
  | s, t, ⟨d, eq⟩ => by rw [eq, factors_mul]; exact le_add_of_nonneg_right bot_le
#align associates.factors_mono Associates.factors_mono

@[simp]
theorem factors_le {a b : Associates α} : a.factors ≤ b.factors ↔ a ≤ b := by
  refine ⟨fun h ↦ ?_, factors_mono⟩
  have : a.factors.prod ≤ b.factors.prod := prod_mono h
  rwa [factors_prod, factors_prod] at this
#align associates.factors_le Associates.factors_le

section count

variable [DecidableEq (Associates α)] [∀ p : Associates α, Decidable (Irreducible p)]

theorem eq_factors_of_eq_counts {a b : Associates α} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p : Associates α, Irreducible p → p.count a.factors = p.count b.factors) :
    a.factors = b.factors := by
  obtain ⟨sa, h_sa⟩ := factors_eq_some_iff_ne_zero.mpr ha
  obtain ⟨sb, h_sb⟩ := factors_eq_some_iff_ne_zero.mpr hb
  rw [h_sa, h_sb] at h ⊢
  rw [WithTop.coe_eq_coe]
  have h_count : ∀ (p : Associates α) (hp : Irreducible p),
      sa.count ⟨p, hp⟩ = sb.count ⟨p, hp⟩ := by
    intro p hp
    rw [← count_some, ← count_some, h p hp]
  apply Multiset.toFinsupp.injective
  ext ⟨p, hp⟩
  rw [Multiset.toFinsupp_apply, Multiset.toFinsupp_apply, h_count p hp]
#align associates.eq_factors_of_eq_counts Associates.eq_factors_of_eq_counts

theorem eq_of_eq_counts {a b : Associates α} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p : Associates α, Irreducible p → p.count a.factors = p.count b.factors) : a = b :=
  eq_of_factors_eq_factors (eq_factors_of_eq_counts ha hb h)
#align associates.eq_of_eq_counts Associates.eq_of_eq_counts

theorem count_le_count_of_factors_le {a b p : Associates α} (hb : b ≠ 0) (hp : Irreducible p)
    (h : a.factors ≤ b.factors) : p.count a.factors ≤ p.count b.factors := by
  by_cases ha : a = 0
  · simp_all
  obtain ⟨sa, h_sa⟩ := factors_eq_some_iff_ne_zero.mpr ha
  obtain ⟨sb, h_sb⟩ := factors_eq_some_iff_ne_zero.mpr hb
  rw [h_sa, h_sb] at h ⊢
  rw [count_some hp, count_some hp]; rw [WithTop.coe_le_coe] at h
  exact Multiset.count_le_of_le _ h
#align associates.count_le_count_of_factors_le Associates.count_le_count_of_factors_le

theorem count_le_count_of_le {a b p : Associates α} (hb : b ≠ 0) (hp : Irreducible p) (h : a ≤ b) :
    p.count a.factors ≤ p.count b.factors :=
  count_le_count_of_factors_le hb hp <| factors_mono h
#align associates.count_le_count_of_le Associates.count_le_count_of_le

end count

theorem prod_le [Nontrivial α] {a b : FactorSet α} : a.prod ≤ b.prod ↔ a ≤ b := by
  refine ⟨fun h ↦ ?_, prod_mono⟩
  have : a.prod.factors ≤ b.prod.factors := factors_mono h
  rwa [prod_factors, prod_factors] at this
#align associates.prod_le Associates.prod_le

open Classical in
noncomputable instance : Sup (Associates α) :=
  ⟨fun a b => (a.factors ⊔ b.factors).prod⟩

open Classical in
noncomputable instance : Inf (Associates α) :=
  ⟨fun a b => (a.factors ⊓ b.factors).prod⟩

open Classical in
noncomputable instance : Lattice (Associates α) :=
  { Associates.instPartialOrder with
    sup := (· ⊔ ·)
    inf := (· ⊓ ·)
    sup_le := fun _ _ c hac hbc =>
      factors_prod c ▸ prod_mono (sup_le (factors_mono hac) (factors_mono hbc))
    le_sup_left := fun a _ => le_trans (le_of_eq (factors_prod a).symm) <| prod_mono <| le_sup_left
    le_sup_right := fun _ b =>
      le_trans (le_of_eq (factors_prod b).symm) <| prod_mono <| le_sup_right
    le_inf := fun a _ _ hac hbc =>
      factors_prod a ▸ prod_mono (le_inf (factors_mono hac) (factors_mono hbc))
    inf_le_left := fun a _ => le_trans (prod_mono inf_le_left) (le_of_eq (factors_prod a))
    inf_le_right := fun _ b => le_trans (prod_mono inf_le_right) (le_of_eq (factors_prod b)) }

open Classical in
theorem sup_mul_inf (a b : Associates α) : (a ⊔ b) * (a ⊓ b) = a * b :=
  show (a.factors ⊔ b.factors).prod * (a.factors ⊓ b.factors).prod = a * b by
    nontriviality α
    refine eq_of_factors_eq_factors ?_
    rw [← prod_add, prod_factors, factors_mul, FactorSet.sup_add_inf_eq_add]
#align associates.sup_mul_inf Associates.sup_mul_inf

theorem dvd_of_mem_factors {a p : Associates α} (hm : p ∈ factors a) :
    p ∣ a := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact dvd_zero p
  obtain ⟨a0, nza, ha'⟩ := exists_non_zero_rep ha0
  rw [← Associates.factors_prod a]
  rw [← ha', factors_mk a0 nza] at hm ⊢
  rw [prod_coe]
  apply Multiset.dvd_prod; apply Multiset.mem_map.mpr
  exact ⟨⟨p, irreducible_of_mem_factorSet hm⟩, mem_factorSet_some.mp hm, rfl⟩
#align associates.dvd_of_mem_factors Associates.dvd_of_mem_factors

theorem dvd_of_mem_factors' {a : α} {p : Associates α} {hp : Irreducible p} {hz : a ≠ 0}
    (h_mem : Subtype.mk p hp ∈ factors' a) : p ∣ Associates.mk a := by
  haveI := Classical.decEq (Associates α)
  apply dvd_of_mem_factors
  rw [factors_mk _ hz]
  apply mem_factorSet_some.2 h_mem
#align associates.dvd_of_mem_factors' Associates.dvd_of_mem_factors'

theorem mem_factors'_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) (hd : p ∣ a) :
    Subtype.mk (Associates.mk p) (irreducible_mk.2 hp) ∈ factors' a := by
  obtain ⟨q, hq, hpq⟩ := exists_mem_factors_of_dvd ha0 hp hd
  apply Multiset.mem_pmap.mpr; use q; use hq
  exact Subtype.eq (Eq.symm (mk_eq_mk_iff_associated.mpr hpq))
#align associates.mem_factors'_of_dvd Associates.mem_factors'_of_dvd

theorem mem_factors'_iff_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) :
    Subtype.mk (Associates.mk p) (irreducible_mk.2 hp) ∈ factors' a ↔ p ∣ a := by
  constructor
  · rw [← mk_dvd_mk]
    apply dvd_of_mem_factors'
    apply ha0
  · apply mem_factors'_of_dvd ha0 hp
#align associates.mem_factors'_iff_dvd Associates.mem_factors'_iff_dvd

theorem mem_factors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) (hd : p ∣ a) :
    Associates.mk p ∈ factors (Associates.mk a) := by
  rw [factors_mk _ ha0]
  exact mem_factorSet_some.mpr (mem_factors'_of_dvd ha0 hp hd)
#align associates.mem_factors_of_dvd Associates.mem_factors_of_dvd

theorem mem_factors_iff_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) :
    Associates.mk p ∈ factors (Associates.mk a) ↔ p ∣ a := by
  constructor
  · rw [← mk_dvd_mk]
    apply dvd_of_mem_factors
  · apply mem_factors_of_dvd ha0 hp
#align associates.mem_factors_iff_dvd Associates.mem_factors_iff_dvd

open Classical in
theorem exists_prime_dvd_of_not_inf_one {a b : α} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Associates.mk a ⊓ Associates.mk b ≠ 1) : ∃ p : α, Prime p ∧ p ∣ a ∧ p ∣ b := by
  have hz : factors (Associates.mk a) ⊓ factors (Associates.mk b) ≠ 0 := by
    contrapose! h with hf
    change (factors (Associates.mk a) ⊓ factors (Associates.mk b)).prod = 1
    rw [hf]
    exact Multiset.prod_zero
  rw [factors_mk a ha, factors_mk b hb, ← WithTop.coe_inf] at hz
  obtain ⟨⟨p0, p0_irr⟩, p0_mem⟩ := Multiset.exists_mem_of_ne_zero ((mt WithTop.coe_eq_coe.mpr) hz)
  rw [Multiset.inf_eq_inter] at p0_mem
  obtain ⟨p, rfl⟩ : ∃ p, Associates.mk p = p0 := Quot.exists_rep p0
  refine ⟨p, ?_, ?_, ?_⟩
  · rw [← UniqueFactorizationMonoid.irreducible_iff_prime, ← irreducible_mk]
    exact p0_irr
  · apply dvd_of_mk_le_mk
    apply dvd_of_mem_factors' (Multiset.mem_inter.mp p0_mem).left
    apply ha
  · apply dvd_of_mk_le_mk
    apply dvd_of_mem_factors' (Multiset.mem_inter.mp p0_mem).right
    apply hb
#align associates.exists_prime_dvd_of_not_inf_one Associates.exists_prime_dvd_of_not_inf_one

theorem coprime_iff_inf_one {a b : α} (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    Associates.mk a ⊓ Associates.mk b = 1 ↔ ∀ {d : α}, d ∣ a → d ∣ b → ¬Prime d := by
  constructor
  · intro hg p ha hb hp
    refine (Associates.prime_mk.mpr hp).not_unit (isUnit_of_dvd_one ?_)
    rw [← hg]
    exact le_inf (mk_le_mk_of_dvd ha) (mk_le_mk_of_dvd hb)
  · contrapose
    intro hg hc
    obtain ⟨p, hp, hpa, hpb⟩ := exists_prime_dvd_of_not_inf_one ha0 hb0 hg
    exact hc hpa hpb hp
#align associates.coprime_iff_inf_one Associates.coprime_iff_inf_one

theorem factors_self [Nontrivial α] {p : Associates α} (hp : Irreducible p) :
    p.factors = WithTop.some {⟨p, hp⟩} :=
  eq_of_prod_eq_prod
    (by rw [factors_prod, FactorSet.prod]; dsimp; rw [prod_singleton])
#align associates.factors_self Associates.factors_self

theorem factors_prime_pow [Nontrivial α] {p : Associates α} (hp : Irreducible p) (k : ℕ) :
    factors (p ^ k) = WithTop.some (Multiset.replicate k ⟨p, hp⟩) :=
  eq_of_prod_eq_prod
    (by
      rw [Associates.factors_prod, FactorSet.prod]
      dsimp; rw [Multiset.map_replicate, Multiset.prod_replicate, Subtype.coe_mk])
#align associates.factors_prime_pow Associates.factors_prime_pow

theorem prime_pow_le_iff_le_bcount [DecidableEq (Associates α)] {m p : Associates α}
    (h₁ : m ≠ 0) (h₂ : Irreducible p) {k : ℕ} : p ^ k ≤ m ↔ k ≤ bcount ⟨p, h₂⟩ m.factors := by
  rcases Associates.exists_non_zero_rep h₁ with ⟨m, hm, rfl⟩
  have := nontrivial_of_ne _ _ hm
  rw [bcount, factors_mk, Multiset.le_count_iff_replicate_le, ← factors_le, factors_prime_pow,
    factors_mk, WithTop.coe_le_coe] <;> assumption

section count

variable [DecidableEq (Associates α)] [∀ p : Associates α, Decidable (Irreducible p)]

theorem prime_pow_dvd_iff_le {m p : Associates α} (h₁ : m ≠ 0) (h₂ : Irreducible p) {k : ℕ} :
    p ^ k ≤ m ↔ k ≤ count p m.factors := by
  rw [count, dif_pos h₂, prime_pow_le_iff_le_bcount h₁]
#align associates.prime_pow_dvd_iff_le Associates.prime_pow_dvd_iff_le

theorem le_of_count_ne_zero {m p : Associates α} (h0 : m ≠ 0) (hp : Irreducible p) :
    count p m.factors ≠ 0 → p ≤ m := by
  nontriviality α
  rw [← pos_iff_ne_zero]
  intro h
  rw [← pow_one p]
  apply (prime_pow_dvd_iff_le h0 hp).2
  simpa only
#align associates.le_of_count_ne_zero Associates.le_of_count_ne_zero

theorem count_ne_zero_iff_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) :
    (Associates.mk p).count (Associates.mk a).factors ≠ 0 ↔ p ∣ a := by
  nontriviality α
  rw [← Associates.mk_le_mk_iff_dvd]
  refine
    ⟨fun h =>
      Associates.le_of_count_ne_zero (Associates.mk_ne_zero.mpr ha0)
        (Associates.irreducible_mk.mpr hp) h,
      fun h => ?_⟩
  rw [← pow_one (Associates.mk p),
    Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr ha0)
      (Associates.irreducible_mk.mpr hp)] at h
  exact (zero_lt_one.trans_le h).ne'
#align associates.count_ne_zero_iff_dvd Associates.count_ne_zero_iff_dvd

theorem count_self [Nontrivial α] [DecidableEq (Associates α)] {p : Associates α}
    (hp : Irreducible p) : p.count p.factors = 1 := by
  simp [factors_self hp, Associates.count_some hp]
#align associates.count_self Associates.count_self

theorem count_eq_zero_of_ne [DecidableEq (Associates α)] {p q : Associates α} (hp : Irreducible p)
    (hq : Irreducible q) (h : p ≠ q) : p.count q.factors = 0 :=
  not_ne_iff.mp fun h' ↦ h <| associated_iff_eq.mp <| hp.associated_of_dvd hq <|
    le_of_count_ne_zero hq.ne_zero hp h'
#align associates.count_eq_zero_of_ne Associates.count_eq_zero_of_ne

theorem count_mul [DecidableEq (Associates α)] {a : Associates α} (ha : a ≠ 0) {b : Associates α}
    (hb : b ≠ 0) {p : Associates α} (hp : Irreducible p) :
    count p (factors (a * b)) = count p a.factors + count p b.factors := by
  obtain ⟨a0, nza, rfl⟩ := exists_non_zero_rep ha
  obtain ⟨b0, nzb, rfl⟩ := exists_non_zero_rep hb
  rw [factors_mul, factors_mk a0 nza, factors_mk b0 nzb, ← FactorSet.coe_add, count_some hp,
    Multiset.count_add, count_some hp, count_some hp]
#align associates.count_mul Associates.count_mul

theorem count_of_coprime [DecidableEq (Associates α)] {a : Associates α} (ha : a ≠ 0)
    {b : Associates α} (hb : b ≠ 0) (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) {p : Associates α}
    (hp : Irreducible p) : count p a.factors = 0 ∨ count p b.factors = 0 := by
  rw [or_iff_not_imp_left, ← Ne]
  intro hca
  contrapose! hab with hcb
  exact ⟨p, le_of_count_ne_zero ha hp hca, le_of_count_ne_zero hb hp hcb,
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hp⟩
#align associates.count_of_coprime Associates.count_of_coprime

theorem count_mul_of_coprime [DecidableEq (Associates α)] {a : Associates α} {b : Associates α}
    (hb : b ≠ 0) {p : Associates α} (hp : Irreducible p) (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) :
    count p a.factors = 0 ∨ count p a.factors = count p (a * b).factors := by
  by_cases ha : a = 0
  · simp [ha]
  cases' count_of_coprime ha hb hab hp with hz hb0; · tauto
  apply Or.intro_right
  rw [count_mul ha hb hp, hb0, add_zero]
#align associates.count_mul_of_coprime Associates.count_mul_of_coprime

theorem count_mul_of_coprime' [DecidableEq (Associates α)] {a b : Associates α} {p : Associates α}
    (hp : Irreducible p) (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) :
    count p (a * b).factors = count p a.factors ∨ count p (a * b).factors = count p b.factors := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [count_mul ha hb hp]
  cases' count_of_coprime ha hb hab hp with ha0 hb0
  · apply Or.intro_right
    rw [ha0, zero_add]
  · apply Or.intro_left
    rw [hb0, add_zero]
#align associates.count_mul_of_coprime' Associates.count_mul_of_coprime'

theorem dvd_count_of_dvd_count_mul [DecidableEq (Associates α)] {a b : Associates α} (hb : b ≠ 0)
    {p : Associates α} (hp : Irreducible p) (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) {k : ℕ}
    (habk : k ∣ count p (a * b).factors) : k ∣ count p a.factors := by
  by_cases ha : a = 0
  · simpa [*] using habk
  cases' count_of_coprime ha hb hab hp with hz h
  · rw [hz]
    exact dvd_zero k
  · rw [count_mul ha hb hp, h] at habk
    exact habk
#align associates.dvd_count_of_dvd_count_mul Associates.dvd_count_of_dvd_count_mul

@[simp]
theorem factors_one [Nontrivial α] : factors (1 : Associates α) = 0 := by
  apply eq_of_prod_eq_prod
  rw [Associates.factors_prod]
  exact Multiset.prod_zero
#align associates.factors_one Associates.factors_one

@[simp]
theorem pow_factors [Nontrivial α] {a : Associates α} {k : ℕ} :
    (a ^ k).factors = k • a.factors := by
  induction' k with n h
  · rw [zero_nsmul, pow_zero]
    exact factors_one
  · rw [pow_succ, succ_nsmul, factors_mul, h]
#align associates.pow_factors Associates.pow_factors

theorem count_pow [Nontrivial α] [DecidableEq (Associates α)] {a : Associates α} (ha : a ≠ 0)
    {p : Associates α} (hp : Irreducible p) (k : ℕ) :
    count p (a ^ k).factors = k * count p a.factors := by
  induction' k with n h
  · rw [pow_zero, factors_one, zero_mul, count_zero hp]
  · rw [pow_succ', count_mul ha (pow_ne_zero _ ha) hp, h]
    ring
#align associates.count_pow Associates.count_pow

theorem dvd_count_pow [Nontrivial α] [DecidableEq (Associates α)] {a : Associates α} (ha : a ≠ 0)
    {p : Associates α} (hp : Irreducible p) (k : ℕ) : k ∣ count p (a ^ k).factors := by
  rw [count_pow ha hp]
  apply dvd_mul_right
#align associates.dvd_count_pow Associates.dvd_count_pow

theorem is_pow_of_dvd_count [DecidableEq (Associates α)] {a : Associates α}
    (ha : a ≠ 0) {k : ℕ} (hk : ∀ p : Associates α, Irreducible p → k ∣ count p a.factors) :
    ∃ b : Associates α, a = b ^ k := by
  nontriviality α
  obtain ⟨a0, hz, rfl⟩ := exists_non_zero_rep ha
  rw [factors_mk a0 hz] at hk
  have hk' : ∀ p, p ∈ factors' a0 → k ∣ (factors' a0).count p := by
    rintro p -
    have pp : p = ⟨p.val, p.2⟩ := by simp only [Subtype.coe_eta]
    rw [pp, ← count_some p.2]
    exact hk p.val p.2
  obtain ⟨u, hu⟩ := Multiset.exists_smul_of_dvd_count _ hk'
  use FactorSet.prod (u : FactorSet α)
  apply eq_of_factors_eq_factors
  rw [pow_factors, prod_factors, factors_mk a0 hz, hu]
  exact WithBot.coe_nsmul u k
#align associates.is_pow_of_dvd_count Associates.is_pow_of_dvd_count

/-- The only divisors of prime powers are prime powers. See `eq_pow_find_of_dvd_irreducible_pow`
for an explicit expression as a p-power (without using `count`). -/
theorem eq_pow_count_factors_of_dvd_pow [DecidableEq (Associates α)] {p a : Associates α}
    (hp : Irreducible p) {n : ℕ} (h : a ∣ p ^ n) : a = p ^ p.count a.factors := by
  nontriviality α
  have hph := pow_ne_zero n hp.ne_zero
  have ha := ne_zero_of_dvd_ne_zero hph h
  apply eq_of_eq_counts ha (pow_ne_zero _ hp.ne_zero)
  have eq_zero_of_ne : ∀ q : Associates α, Irreducible q → q ≠ p → _ = 0 := fun q hq h' =>
    Nat.eq_zero_of_le_zero <| by
      convert count_le_count_of_le hph hq h
      symm
      rw [count_pow hp.ne_zero hq, count_eq_zero_of_ne hq hp h', mul_zero]
  intro q hq
  rw [count_pow hp.ne_zero hq]
  by_cases h : q = p
  · rw [h, count_self hp, mul_one]
  · rw [count_eq_zero_of_ne hq hp h, mul_zero, eq_zero_of_ne q hq h]
#align associates.eq_pow_count_factors_of_dvd_pow Associates.eq_pow_count_factors_of_dvd_pow

theorem count_factors_eq_find_of_dvd_pow [DecidableEq (Associates α)] {a p : Associates α}
    (hp : Irreducible p) [∀ n : ℕ, Decidable (a ∣ p ^ n)] {n : ℕ} (h : a ∣ p ^ n) :
    @Nat.find (fun n => a ∣ p ^ n) _ ⟨n, h⟩ = p.count a.factors := by
  apply le_antisymm
  · refine Nat.find_le ⟨1, ?_⟩
    rw [mul_one]
    symm
    exact eq_pow_count_factors_of_dvd_pow hp h
  · have hph := pow_ne_zero (@Nat.find (fun n => a ∣ p ^ n) _ ⟨n, h⟩) hp.ne_zero
    cases' subsingleton_or_nontrivial α with hα hα
    · simp [eq_iff_true_of_subsingleton] at hph
    convert count_le_count_of_le hph hp (@Nat.find_spec (fun n => a ∣ p ^ n) _ ⟨n, h⟩)
    rw [count_pow hp.ne_zero hp, count_self hp, mul_one]
#align associates.count_factors_eq_find_of_dvd_pow Associates.count_factors_eq_find_of_dvd_pow

end count

theorem eq_pow_of_mul_eq_pow {a b c : Associates α} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) {k : ℕ} (h : a * b = c ^ k) :
    ∃ d : Associates α, a = d ^ k := by
  classical
  nontriviality α
  by_cases hk0 : k = 0
  · use 1
    rw [hk0, pow_zero] at h ⊢
    apply (mul_eq_one_iff.1 h).1
  · refine is_pow_of_dvd_count ha fun p hp ↦ ?_
    apply dvd_count_of_dvd_count_mul hb hp hab
    rw [h]
    apply dvd_count_pow _ hp
    rintro rfl
    rw [zero_pow hk0] at h
    cases mul_eq_zero.mp h <;> contradiction
#align associates.eq_pow_of_mul_eq_pow Associates.eq_pow_of_mul_eq_pow

/-- The only divisors of prime powers are prime powers. -/
theorem eq_pow_find_of_dvd_irreducible_pow {a p : Associates α} (hp : Irreducible p)
    [∀ n : ℕ, Decidable (a ∣ p ^ n)] {n : ℕ} (h : a ∣ p ^ n) :
    a = p ^ @Nat.find (fun n => a ∣ p ^ n) _ ⟨n, h⟩ := by
  classical rw [count_factors_eq_find_of_dvd_pow hp, ← eq_pow_count_factors_of_dvd_pow hp h]
  exact h
#align associates.eq_pow_find_of_dvd_irreducible_pow Associates.eq_pow_find_of_dvd_irreducible_pow

end Associates

section

open Associates UniqueFactorizationMonoid

/-- `toGCDMonoid` constructs a GCD monoid out of a unique factorization domain. -/
noncomputable def UniqueFactorizationMonoid.toGCDMonoid (α : Type*) [CancelCommMonoidWithZero α]
    [UniqueFactorizationMonoid α] : GCDMonoid α where
  gcd a b := Quot.out (Associates.mk a ⊓ Associates.mk b : Associates α)
  lcm a b := Quot.out (Associates.mk a ⊔ Associates.mk b : Associates α)
  gcd_dvd_left a b := by
    rw [← mk_dvd_mk, Associates.quot_out, congr_fun₂ dvd_eq_le]
    exact inf_le_left
  gcd_dvd_right a b := by
    rw [← mk_dvd_mk, Associates.quot_out, congr_fun₂ dvd_eq_le]
    exact inf_le_right
  dvd_gcd {a b c} hac hab := by
    rw [← mk_dvd_mk, Associates.quot_out, congr_fun₂ dvd_eq_le, le_inf_iff,
      mk_le_mk_iff_dvd, mk_le_mk_iff_dvd]
    exact ⟨hac, hab⟩
  lcm_zero_left a := by simp
  lcm_zero_right a := by simp
  gcd_mul_lcm a b := by
    rw [← mk_eq_mk_iff_associated, ← Associates.mk_mul_mk, ← associated_iff_eq, Associates.quot_out,
      Associates.quot_out, mul_comm, sup_mul_inf, Associates.mk_mul_mk]
#align unique_factorization_monoid.to_gcd_monoid UniqueFactorizationMonoid.toGCDMonoid

/-- `toNormalizedGCDMonoid` constructs a GCD monoid out of a normalization on a
  unique factorization domain. -/
noncomputable def UniqueFactorizationMonoid.toNormalizedGCDMonoid (α : Type*)
    [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α] [NormalizationMonoid α] :
    NormalizedGCDMonoid α :=
  { ‹NormalizationMonoid α› with
    gcd := fun a b => (Associates.mk a ⊓ Associates.mk b).out
    lcm := fun a b => (Associates.mk a ⊔ Associates.mk b).out
    gcd_dvd_left := fun a b => (out_dvd_iff a (Associates.mk a ⊓ Associates.mk b)).2 <| inf_le_left
    gcd_dvd_right := fun a b =>
      (out_dvd_iff b (Associates.mk a ⊓ Associates.mk b)).2 <| inf_le_right
    dvd_gcd := fun {a} {b} {c} hac hab =>
      show a ∣ (Associates.mk c ⊓ Associates.mk b).out by
        rw [dvd_out_iff, le_inf_iff, mk_le_mk_iff_dvd, mk_le_mk_iff_dvd]
        exact ⟨hac, hab⟩
    lcm_zero_left := fun a => show (⊤ ⊔ Associates.mk a).out = 0 by simp
    lcm_zero_right := fun a => show (Associates.mk a ⊔ ⊤).out = 0 by simp
    gcd_mul_lcm := fun a b => by
      rw [← out_mul, mul_comm, sup_mul_inf, mk_mul_mk, out_mk]
      exact normalize_associated (a * b)
    normalize_gcd := fun a b => by apply normalize_out _
    normalize_lcm := fun a b => by apply normalize_out _ }
#align unique_factorization_monoid.to_normalized_gcd_monoid UniqueFactorizationMonoid.toNormalizedGCDMonoid

instance (α) [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α] :
    Nonempty (NormalizedGCDMonoid α) := by
  letI := UniqueFactorizationMonoid.normalizationMonoid (α := α)
  classical exact ⟨UniqueFactorizationMonoid.toNormalizedGCDMonoid α⟩

end

namespace UniqueFactorizationMonoid

/-- If `y` is a nonzero element of a unique factorization monoid with finitely
many units (e.g. `ℤ`, `Ideal (ring_of_integers K)`), it has finitely many divisors. -/
noncomputable def fintypeSubtypeDvd {M : Type*} [CancelCommMonoidWithZero M]
    [UniqueFactorizationMonoid M] [Fintype Mˣ] (y : M) (hy : y ≠ 0) : Fintype { x // x ∣ y } := by
  haveI : Nontrivial M := ⟨⟨y, 0, hy⟩⟩
  haveI : NormalizationMonoid M := UniqueFactorizationMonoid.normalizationMonoid
  haveI := Classical.decEq M
  haveI := Classical.decEq (Associates M)
  -- We'll show `λ (u : Mˣ) (f ⊆ factors y) → u * Π f` is injective
  -- and has image exactly the divisors of `y`.
  refine
    Fintype.ofFinset
      (((normalizedFactors y).powerset.toFinset ×ˢ (Finset.univ : Finset Mˣ)).image fun s =>
        (s.snd : M) * s.fst.prod)
      fun x => ?_
  simp only [exists_prop, Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true_iff,
    Multiset.mem_toFinset, Multiset.mem_powerset, exists_eq_right, Multiset.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    show (s.snd : M) * s.fst.prod ∣ y
    rw [(unit_associated_one.mul_right s.fst.prod).dvd_iff_dvd_left, one_mul,
      ← (normalizedFactors_prod hy).dvd_iff_dvd_right]
    exact Multiset.prod_dvd_prod_of_le hs
  · rintro (h : x ∣ y)
    have hx : x ≠ 0 := by
      refine mt (fun hx => ?_) hy
      rwa [hx, zero_dvd_iff] at h
    obtain ⟨u, hu⟩ := normalizedFactors_prod hx
    refine ⟨⟨normalizedFactors x, u⟩, ?_, (mul_comm _ _).trans hu⟩
    exact (dvd_iff_normalizedFactors_le_normalizedFactors hx hy).mp h
#align unique_factorization_monoid.fintype_subtype_dvd UniqueFactorizationMonoid.fintypeSubtypeDvd

end UniqueFactorizationMonoid

section Finsupp

variable [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α]
variable [NormalizationMonoid α] [DecidableEq α]

open UniqueFactorizationMonoid

/-- This returns the multiset of irreducible factors as a `Finsupp`. -/
noncomputable def factorization (n : α) : α →₀ ℕ :=
  Multiset.toFinsupp (normalizedFactors n)
#align factorization factorization

theorem factorization_eq_count {n p : α} :
    factorization n p = Multiset.count p (normalizedFactors n) := by simp [factorization]
#align factorization_eq_count factorization_eq_count

@[simp]
theorem factorization_zero : factorization (0 : α) = 0 := by simp [factorization]
#align factorization_zero factorization_zero

@[simp]
theorem factorization_one : factorization (1 : α) = 0 := by simp [factorization]
#align factorization_one factorization_one

/-- The support of `factorization n` is exactly the Finset of normalized factors -/
@[simp]
theorem support_factorization {n : α} :
    (factorization n).support = (normalizedFactors n).toFinset := by
  simp [factorization, Multiset.toFinsupp_support]
#align support_factorization support_factorization

/-- For nonzero `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
@[simp]
theorem factorization_mul {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
    factorization (a * b) = factorization a + factorization b := by
  simp [factorization, normalizedFactors_mul ha hb]
#align factorization_mul factorization_mul

/-- For any `p`, the power of `p` in `x^n` is `n` times the power in `x` -/
theorem factorization_pow {x : α} {n : ℕ} : factorization (x ^ n) = n • factorization x := by
  ext
  simp [factorization]
#align factorization_pow factorization_pow

theorem associated_of_factorization_eq (a b : α) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : factorization a = factorization b) : Associated a b := by
  simp_rw [factorization, AddEquiv.apply_eq_iff_eq] at h
  rwa [associated_iff_normalizedFactors_eq_normalizedFactors ha hb]
#align associated_of_factorization_eq associated_of_factorization_eq

end Finsupp

open UniqueFactorizationMonoid in
/-- Every non-zero prime ideal in a unique factorization domain contains a prime element. -/
theorem Ideal.IsPrime.exists_mem_prime_of_ne_bot {R : Type*} [CommSemiring R] [IsDomain R]
    [UniqueFactorizationMonoid R] {I : Ideal R} (hI₂ : I.IsPrime) (hI : I ≠ ⊥) :
    ∃ x ∈ I, Prime x := by
  classical
  obtain ⟨a : R, ha₁ : a ∈ I, ha₂ : a ≠ 0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  replace ha₁ : (factors a).prod ∈ I := by
    obtain ⟨u : Rˣ, hu : (factors a).prod * u = a⟩ := factors_prod ha₂
    rwa [← hu, mul_unit_mem_iff_mem _ u.isUnit] at ha₁
  obtain ⟨p : R, hp₁ : p ∈ factors a, hp₂ : p ∈ I⟩ :=
    (hI₂.multiset_prod_mem_iff_exists_mem <| factors a).1 ha₁
  exact ⟨p, hp₂, prime_of_factor p hp₁⟩

namespace Nat

instance instWfDvdMonoid : WfDvdMonoid ℕ where
  wellFounded_dvdNotUnit := by
    refine RelHomClass.wellFounded
      (⟨fun x : ℕ => if x = 0 then (⊤ : ℕ∞) else x, ?_⟩ : DvdNotUnit →r (· < ·)) wellFounded_lt
    intro a b h
    cases' a with a
    · exfalso
      revert h
      simp [DvdNotUnit]
    cases b
    · simpa [succ_ne_zero] using WithTop.coe_lt_top (a + 1)
    cases' dvd_and_not_dvd_iff.2 h with h1 h2
    simp only [succ_ne_zero, cast_lt, if_false]
    refine lt_of_le_of_ne (Nat.le_of_dvd (Nat.succ_pos _) h1) fun con => h2 ?_
    rw [con]

instance instUniqueFactorizationMonoid : UniqueFactorizationMonoid ℕ where
  irreducible_iff_prime := Nat.irreducible_iff_prime

open UniqueFactorizationMonoid

lemma factors_eq : ∀ n : ℕ, normalizedFactors n = n.factors
  | 0 => by simp
  | n + 1 => by
    rw [← Multiset.rel_eq, ← associated_eq_eq]
    apply UniqueFactorizationMonoid.factors_unique irreducible_of_normalized_factor _
    · rw [Multiset.prod_coe, Nat.prod_factors n.succ_ne_zero]
      exact normalizedFactors_prod n.succ_ne_zero
    · intro x hx
      rw [Nat.irreducible_iff_prime, ← Nat.prime_iff]
      exact Nat.prime_of_mem_factors hx
#align nat.factors_eq Nat.factors_eq

lemma factors_multiset_prod_of_irreducible {s : Multiset ℕ} (h : ∀ x : ℕ, x ∈ s → Irreducible x) :
    normalizedFactors s.prod = s := by
  rw [← Multiset.rel_eq, ← associated_eq_eq]
  apply UniqueFactorizationMonoid.factors_unique irreducible_of_normalized_factor h
    (normalizedFactors_prod _)
  rw [Ne, Multiset.prod_eq_zero_iff]
  exact fun con ↦ not_irreducible_zero (h 0 con)
#align nat.factors_multiset_prod_of_irreducible Nat.factors_multiset_prod_of_irreducible

lemma _root_.induction_on_primes {P : ℕ → Prop} (h₀ : P 0) (h₁ : P 1)
    (h : ∀ p a : ℕ, p.Prime → P a → P (p * a)) (n : ℕ) : P n := by
  apply UniqueFactorizationMonoid.induction_on_prime
  · exact h₀
  · intro n h
    rw [Nat.isUnit_iff.1 h]
    exact h₁
  · exact fun a p _ hp ↦ h p a hp.nat_prime
#align induction_on_primes induction_on_primes

end Nat
