/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
import Mathlib.Data.Finsupp.Multiset
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Tactic.Ring

/-!
# Set of factors

## Main definitions
* `Associates.FactorSet`: multiset of factors of an element, unique up to propositional equality.
* `Associates.factors`: determine the `FactorSet` for a given element.

## TODO
* set up the complete lattice structure on `FactorSet`.

-/

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

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

attribute [local instance] Associated.setoid

theorem FactorSet.coe_add {a b : Multiset { a : Associates α // Irreducible a }} :
    (↑(a + b) : FactorSet α) = a + b := by norm_cast

theorem FactorSet.sup_add_inf_eq_add [DecidableEq (Associates α)] :
    ∀ a b : FactorSet α, a ⊔ b + a ⊓ b = a + b
  | ⊤, b => show ⊤ ⊔ b + ⊤ ⊓ b = ⊤ + b by simp
  | a, ⊤ => show a ⊔ ⊤ + a ⊓ ⊤ = a + ⊤ by simp
  | WithTop.some a, WithTop.some b =>
    show (a : FactorSet α) ⊔ b + (a : FactorSet α) ⊓ b = a + b by
      rw [← WithTop.coe_sup, ← WithTop.coe_inf, ← WithTop.coe_add, ← WithTop.coe_add,
        WithTop.coe_eq_coe]
      exact Multiset.union_add_inter _ _

/-- Evaluates the product of a `FactorSet` to be the product of the corresponding multiset,
  or `0` if there is none. -/
def FactorSet.prod : FactorSet α → Associates α
  | ⊤ => 0
  | WithTop.some s => (s.map (↑)).prod

@[simp]
theorem prod_top : (⊤ : FactorSet α).prod = 0 :=
  rfl

@[simp]
theorem prod_coe {s : Multiset { a : Associates α // Irreducible a }} :
    FactorSet.prod (s : FactorSet α) = (s.map (↑)).prod :=
  rfl

@[simp]
theorem prod_add : ∀ a b : FactorSet α, (a + b).prod = a.prod * b.prod
  | ⊤, b => show (⊤ + b).prod = (⊤ : FactorSet α).prod * b.prod by simp
  | a, ⊤ => show (a + ⊤).prod = a.prod * (⊤ : FactorSet α).prod by simp
  | WithTop.some a, WithTop.some b => by
    rw [← FactorSet.coe_add, prod_coe, prod_coe, prod_coe, Multiset.map_add, Multiset.prod_add]

@[gcongr]
theorem prod_mono : ∀ {a b : FactorSet α}, a ≤ b → a.prod ≤ b.prod
  | ⊤, b, h => by
    have : b = ⊤ := top_unique h
    rw [this, prod_top]
  | a, ⊤, _ => show a.prod ≤ (⊤ : FactorSet α).prod by simp
  | WithTop.some _, WithTop.some _, h =>
    prod_le_prod <| Multiset.map_le_map <| WithTop.coe_le_coe.1 <| h

theorem FactorSet.prod_eq_zero_iff [Nontrivial α] (p : FactorSet α) : p.prod = 0 ↔ p = ⊤ := by
  unfold FactorSet at p
  induction p  -- TODO: `induction_eliminator` doesn't work with `abbrev`
  · simp only [Associates.prod_top]
  · rw [prod_coe, Multiset.prod_eq_zero_iff, Multiset.mem_map, eq_false WithTop.coe_ne_top,
      iff_false, not_exists]
    exact fun a => not_and_of_not_right _ a.prop.ne_zero

section count

variable [DecidableEq (Associates α)]

/-- `bcount p s` is the multiplicity of `p` in the FactorSet `s` (with bundled `p`). -/
def bcount (p : { a : Associates α // Irreducible a }) :
    FactorSet α → ℕ
  | ⊤ => 0
  | WithTop.some s => s.count p

variable [∀ p : Associates α, Decidable (Irreducible p)] {p : Associates α}

/-- `count p s` is the multiplicity of the irreducible `p` in the FactorSet `s`.

If `p` is not irreducible, `count p s` is defined to be `0`. -/
def count (p : Associates α) : FactorSet α → ℕ :=
  if hp : Irreducible p then bcount ⟨p, hp⟩ else 0

@[simp]
theorem count_some (hp : Irreducible p) (s : Multiset _) :
    count p (WithTop.some s) = s.count ⟨p, hp⟩ := by
  simp only [count, dif_pos hp, bcount]

@[simp]
theorem count_zero (hp : Irreducible p) : count p (0 : FactorSet α) = 0 := by
  simp only [count, dif_pos hp, bcount, Multiset.count_zero]

theorem count_reducible (hp : ¬Irreducible p) : count p = 0 := dif_neg hp

end count

section Mem

/-- membership in a FactorSet (bundled version) -/
def BfactorSetMem : { a : Associates α // Irreducible a } → FactorSet α → Prop
  | _, ⊤ => True
  | p, some l => p ∈ l

/-- `FactorSetMem p s` is the predicate that the irreducible `p` is a member of
`s : FactorSet α`.

If `p` is not irreducible, `p` is not a member of any `FactorSet`. -/
def FactorSetMem (s : FactorSet α) (p : Associates α) : Prop :=
  letI : Decidable (Irreducible p) := Classical.dec _
  if hp : Irreducible p then BfactorSetMem ⟨p, hp⟩ s else False

instance : Membership (Associates α) (FactorSet α) :=
  ⟨FactorSetMem⟩

@[simp]
theorem factorSetMem_eq_mem (p : Associates α) (s : FactorSet α) : FactorSetMem s p = (p ∈ s) :=
  rfl

theorem mem_factorSet_top {p : Associates α} {hp : Irreducible p} : p ∈ (⊤ : FactorSet α) := by
  dsimp only [Membership.mem]; dsimp only [FactorSetMem]; split_ifs; exact trivial

theorem mem_factorSet_some {p : Associates α} {hp : Irreducible p}
    {l : Multiset { a : Associates α // Irreducible a }} :
    p ∈ (l : FactorSet α) ↔ Subtype.mk p hp ∈ l := by
  dsimp only [Membership.mem]; dsimp only [FactorSetMem]; split_ifs; rfl

theorem reducible_notMem_factorSet {p : Associates α} (hp : ¬Irreducible p) (s : FactorSet α) :
    p ∉ s := fun h ↦ by
  rwa [← factorSetMem_eq_mem, FactorSetMem, dif_neg hp] at h

@[deprecated (since := "2025-05-23")]
alias reducible_not_mem_factorSet := reducible_notMem_factorSet

theorem irreducible_of_mem_factorSet {p : Associates α} {s : FactorSet α} (h : p ∈ s) :
    Irreducible p :=
  by_contra fun hp ↦ reducible_notMem_factorSet hp s h

end Mem

variable [UniqueFactorizationMonoid α]

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

/-- This returns the multiset of irreducible factors as a `FactorSet`,
  a multiset of irreducible associates `WithTop`. -/
noncomputable def factors' (a : α) : Multiset { a : Associates α // Irreducible a } :=
  (factors a).pmap (fun a ha => ⟨Associates.mk a, irreducible_mk.2 ha⟩) irreducible_of_factor

@[simp]
theorem map_subtype_coe_factors' {a : α} :
    (factors' a).map (↑) = (factors a).map Associates.mk := by
  simp [factors', Multiset.map_pmap, Multiset.pmap_eq_map]

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

@[simp]
theorem factors_zero : (0 : Associates α).factors = ⊤ :=
  dif_pos rfl


@[simp]
theorem factors_mk (a : α) (h : a ≠ 0) : (Associates.mk a).factors = factors' a := by
  classical
    apply dif_neg
    apply mt mk_eq_zero.1 h

@[simp]
theorem factors_prod (a : Associates α) : a.factors.prod = a := by
  rcases Associates.mk_surjective a with ⟨a, rfl⟩
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · simp [ha, prod_mk, mk_eq_mk_iff_associated, UniqueFactorizationMonoid.factors_prod,
      -Quotient.eq]

@[simp]
theorem prod_factors [Nontrivial α] (s : FactorSet α) : s.prod.factors = s :=
  FactorSet.unique <| factors_prod _

@[nontriviality]
theorem factors_subsingleton [Subsingleton α] {a : Associates α} : a.factors = ⊤ := by
  have : Subsingleton (Associates α) := inferInstance
  convert factors_zero

theorem factors_eq_top_iff_zero {a : Associates α} : a.factors = ⊤ ↔ a = 0 := by
  nontriviality α
  exact ⟨fun h ↦ by rwa [← factors_prod a, FactorSet.prod_eq_zero_iff], fun h ↦ h ▸ factors_zero⟩

theorem factors_eq_some_iff_ne_zero {a : Associates α} :
    (∃ s : Multiset { p : Associates α // Irreducible p }, a.factors = s) ↔ a ≠ 0 := by
  simp_rw [@eq_comm _ a.factors, ← WithTop.ne_top_iff_exists]
  exact factors_eq_top_iff_zero.not

theorem eq_of_factors_eq_factors {a b : Associates α} (h : a.factors = b.factors) : a = b := by
  have : a.factors.prod = b.factors.prod := by rw [h]
  rwa [factors_prod, factors_prod] at this

@[deprecated (since := "2025-10-06")] alias eq_of_prod_eq_prod := FactorSet.unique

@[simp]
theorem factors_mul (a b : Associates α) : (a * b).factors = a.factors + b.factors := by
  nontriviality α
  refine FactorSet.unique <| eq_of_factors_eq_factors ?_
  rw [prod_add, factors_prod, factors_prod, factors_prod]

@[gcongr]
theorem factors_mono : ∀ {a b : Associates α}, a ≤ b → a.factors ≤ b.factors
  | s, t, ⟨d, eq⟩ => by rw [eq, factors_mul]; exact le_add_of_nonneg_right bot_le

@[simp]
theorem factors_le {a b : Associates α} : a.factors ≤ b.factors ↔ a ≤ b := by
  refine ⟨fun h ↦ ?_, factors_mono⟩
  have : a.factors.prod ≤ b.factors.prod := prod_mono h
  rwa [factors_prod, factors_prod] at this

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

theorem eq_of_eq_counts {a b : Associates α} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p : Associates α, Irreducible p → p.count a.factors = p.count b.factors) : a = b :=
  eq_of_factors_eq_factors (eq_factors_of_eq_counts ha hb h)

theorem count_le_count_of_factors_le {a b p : Associates α} (hb : b ≠ 0) (hp : Irreducible p)
    (h : a.factors ≤ b.factors) : p.count a.factors ≤ p.count b.factors := by
  by_cases ha : a = 0
  · simp_all
  obtain ⟨sa, h_sa⟩ := factors_eq_some_iff_ne_zero.mpr ha
  obtain ⟨sb, h_sb⟩ := factors_eq_some_iff_ne_zero.mpr hb
  rw [h_sa, h_sb] at h ⊢
  rw [count_some hp, count_some hp]; rw [WithTop.coe_le_coe] at h
  exact Multiset.count_le_of_le _ h

theorem count_le_count_of_le {a b p : Associates α} (hb : b ≠ 0) (hp : Irreducible p) (h : a ≤ b) :
    p.count a.factors ≤ p.count b.factors :=
  count_le_count_of_factors_le hb hp <| factors_mono h

end count

theorem prod_le [Nontrivial α] {a b : FactorSet α} : a.prod ≤ b.prod ↔ a ≤ b := by
  refine ⟨fun h ↦ ?_, prod_mono⟩
  have : a.prod.factors ≤ b.prod.factors := factors_mono h
  rwa [prod_factors, prod_factors] at this

open Classical in
noncomputable instance : Max (Associates α) :=
  ⟨fun a b => (a.factors ⊔ b.factors).prod⟩

open Classical in
noncomputable instance : Min (Associates α) :=
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

theorem dvd_of_mem_factors' {a : α} {p : Associates α} {hp : Irreducible p} {hz : a ≠ 0}
    (h_mem : Subtype.mk p hp ∈ factors' a) : p ∣ Associates.mk a := by
  haveI := Classical.decEq (Associates α)
  apply dvd_of_mem_factors
  rw [factors_mk _ hz]
  apply mem_factorSet_some.2 h_mem

theorem mem_factors'_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) (hd : p ∣ a) :
    Subtype.mk (Associates.mk p) (irreducible_mk.2 hp) ∈ factors' a := by
  obtain ⟨q, hq, hpq⟩ := exists_mem_factors_of_dvd ha0 hp hd
  apply Multiset.mem_pmap.mpr; use q; use hq
  exact Subtype.ext (Eq.symm (mk_eq_mk_iff_associated.mpr hpq))

theorem mem_factors'_iff_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) :
    Subtype.mk (Associates.mk p) (irreducible_mk.2 hp) ∈ factors' a ↔ p ∣ a := by
  constructor
  · rw [← mk_dvd_mk]
    apply dvd_of_mem_factors'
    apply ha0
  · apply mem_factors'_of_dvd ha0 hp

theorem mem_factors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) (hd : p ∣ a) :
    Associates.mk p ∈ factors (Associates.mk a) := by
  rw [factors_mk _ ha0]
  exact mem_factorSet_some.mpr (mem_factors'_of_dvd ha0 hp hd)

theorem mem_factors_iff_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) :
    Associates.mk p ∈ factors (Associates.mk a) ↔ p ∣ a := by
  constructor
  · rw [← mk_dvd_mk]
    apply dvd_of_mem_factors
  · apply mem_factors_of_dvd ha0 hp

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

theorem factors_self [Nontrivial α] {p : Associates α} (hp : Irreducible p) :
    p.factors = WithTop.some {⟨p, hp⟩} :=
  FactorSet.unique
    (by rw [factors_prod, FactorSet.prod.eq_def]; dsimp; rw [prod_singleton])

theorem factors_prime_pow [Nontrivial α] {p : Associates α} (hp : Irreducible p) (k : ℕ) :
    factors (p ^ k) = WithTop.some (Multiset.replicate k ⟨p, hp⟩) :=
  FactorSet.unique
    (by
      rw [Associates.factors_prod, FactorSet.prod.eq_def]
      dsimp; rw [Multiset.map_replicate, Multiset.prod_replicate, Subtype.coe_mk])

theorem prime_pow_le_iff_le_bcount [DecidableEq (Associates α)] {m p : Associates α}
    (h₁ : m ≠ 0) (h₂ : Irreducible p) {k : ℕ} : p ^ k ≤ m ↔ k ≤ bcount ⟨p, h₂⟩ m.factors := by
  rcases Associates.exists_non_zero_rep h₁ with ⟨m, hm, rfl⟩
  have := nontrivial_of_ne _ _ hm
  rw [bcount.eq_def, factors_mk, Multiset.le_count_iff_replicate_le, ← factors_le,
    factors_prime_pow, factors_mk, WithTop.coe_le_coe] <;> assumption

@[simp]
theorem factors_one [Nontrivial α] : factors (1 : Associates α) = 0 := by
  apply FactorSet.unique
  rw [Associates.factors_prod]
  exact Multiset.prod_zero

@[simp]
theorem pow_factors [Nontrivial α] {a : Associates α} {k : ℕ} :
    (a ^ k).factors = k • a.factors := by
  induction k with
  | zero => rw [zero_nsmul, pow_zero]; exact factors_one
  | succ n h => rw [pow_succ, succ_nsmul, factors_mul, h]

section count

variable [DecidableEq (Associates α)] [∀ p : Associates α, Decidable (Irreducible p)]

theorem prime_pow_dvd_iff_le {m p : Associates α} (h₁ : m ≠ 0) (h₂ : Irreducible p) {k : ℕ} :
    p ^ k ≤ m ↔ k ≤ count p m.factors := by
  rw [count, dif_pos h₂, prime_pow_le_iff_le_bcount h₁]

theorem le_of_count_ne_zero {m p : Associates α} (h0 : m ≠ 0) (hp : Irreducible p) :
    count p m.factors ≠ 0 → p ≤ m := by
  nontriviality α
  rw [← pos_iff_ne_zero]
  intro h
  rw [← pow_one p]
  apply (prime_pow_dvd_iff_le h0 hp).2
  simpa only

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

theorem count_self [Nontrivial α] {p : Associates α}
    (hp : Irreducible p) : p.count p.factors = 1 := by
  simp [factors_self hp, Associates.count_some hp]

theorem count_eq_zero_of_ne {p q : Associates α} (hp : Irreducible p)
    (hq : Irreducible q) (h : p ≠ q) : p.count q.factors = 0 :=
  not_ne_iff.mp fun h' ↦ h <| associated_iff_eq.mp <| hp.associated_of_dvd hq <|
    le_of_count_ne_zero hq.ne_zero hp h'

theorem count_mul {a : Associates α} (ha : a ≠ 0) {b : Associates α}
    (hb : b ≠ 0) {p : Associates α} (hp : Irreducible p) :
    count p (factors (a * b)) = count p a.factors + count p b.factors := by
  obtain ⟨a0, nza, rfl⟩ := exists_non_zero_rep ha
  obtain ⟨b0, nzb, rfl⟩ := exists_non_zero_rep hb
  rw [factors_mul, factors_mk a0 nza, factors_mk b0 nzb, ← FactorSet.coe_add, count_some hp,
    Multiset.count_add, count_some hp, count_some hp]

theorem count_of_coprime {a : Associates α} (ha : a ≠ 0)
    {b : Associates α} (hb : b ≠ 0) (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) {p : Associates α}
    (hp : Irreducible p) : count p a.factors = 0 ∨ count p b.factors = 0 := by
  rw [or_iff_not_imp_left, ← Ne]
  intro hca
  contrapose! hab with hcb
  exact ⟨p, le_of_count_ne_zero ha hp hca, le_of_count_ne_zero hb hp hcb,
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hp⟩

theorem count_mul_of_coprime {a : Associates α} {b : Associates α}
    (hb : b ≠ 0) {p : Associates α} (hp : Irreducible p) (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) :
    count p a.factors = 0 ∨ count p a.factors = count p (a * b).factors := by
  by_cases ha : a = 0
  · simp [ha]
  rcases count_of_coprime ha hb hab hp with hz | hb0; · tauto
  apply Or.intro_right
  rw [count_mul ha hb hp, hb0, add_zero]

theorem count_mul_of_coprime' {a b : Associates α} {p : Associates α}
    (hp : Irreducible p) (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) :
    count p (a * b).factors = count p a.factors ∨ count p (a * b).factors = count p b.factors := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [count_mul ha hb hp]
  rcases count_of_coprime ha hb hab hp with ha0 | hb0
  · apply Or.intro_right
    rw [ha0, zero_add]
  · apply Or.intro_left
    rw [hb0, add_zero]

theorem dvd_count_of_dvd_count_mul {a b : Associates α} (hb : b ≠ 0)
    {p : Associates α} (hp : Irreducible p) (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) {k : ℕ}
    (habk : k ∣ count p (a * b).factors) : k ∣ count p a.factors := by
  by_cases ha : a = 0
  · simpa [*] using habk
  rcases count_of_coprime ha hb hab hp with hz | h
  · rw [hz]
    exact dvd_zero k
  · rw [count_mul ha hb hp, h] at habk
    exact habk

theorem count_pow [Nontrivial α] {a : Associates α} (ha : a ≠ 0)
    {p : Associates α} (hp : Irreducible p) (k : ℕ) :
    count p (a ^ k).factors = k * count p a.factors := by
  induction k with
  | zero => rw [pow_zero, factors_one, zero_mul, count_zero hp]
  | succ n h => rw [pow_succ', count_mul ha (pow_ne_zero _ ha) hp, h]; ring

theorem dvd_count_pow [Nontrivial α] {a : Associates α} (ha : a ≠ 0)
    {p : Associates α} (hp : Irreducible p) (k : ℕ) : k ∣ count p (a ^ k).factors := by
  rw [count_pow ha hp]
  apply dvd_mul_right

theorem is_pow_of_dvd_count {a : Associates α}
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

/-- The only divisors of prime powers are prime powers. See `eq_pow_find_of_dvd_irreducible_pow`
for an explicit expression as a p-power (without using `count`). -/
theorem eq_pow_count_factors_of_dvd_pow {p a : Associates α}
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

theorem count_factors_eq_find_of_dvd_pow {a p : Associates α}
    (hp : Irreducible p) [∀ n : ℕ, Decidable (a ∣ p ^ n)] {n : ℕ} (h : a ∣ p ^ n) :
    @Nat.find (fun n => a ∣ p ^ n) _ ⟨n, h⟩ = p.count a.factors := by
  apply le_antisymm
  · refine Nat.find_le ⟨1, ?_⟩
    rw [mul_one]
    symm
    exact eq_pow_count_factors_of_dvd_pow hp h
  · have hph := pow_ne_zero (@Nat.find (fun n => a ∣ p ^ n) _ ⟨n, h⟩) hp.ne_zero
    rcases subsingleton_or_nontrivial α with hα | hα
    · simp [eq_iff_true_of_subsingleton] at hph
    convert count_le_count_of_le hph hp (@Nat.find_spec (fun n => a ∣ p ^ n) _ ⟨n, h⟩)
    rw [count_pow hp.ne_zero hp, count_self hp, mul_one]

end count

theorem eq_pow_of_mul_eq_pow {a b c : Associates α} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) {k : ℕ} (h : a * b = c ^ k) :
    ∃ d : Associates α, a = d ^ k := by
  classical
  nontriviality α
  by_cases hk0 : k = 0
  · use 1
    rw [hk0, pow_zero] at h ⊢
    apply (mul_eq_one.1 h).1
  · refine is_pow_of_dvd_count ha fun p hp ↦ ?_
    apply dvd_count_of_dvd_count_mul hb hp hab
    rw [h]
    apply dvd_count_pow _ hp
    rintro rfl
    rw [zero_pow hk0] at h
    cases mul_eq_zero.mp h <;> contradiction

/-- The only divisors of prime powers are prime powers. -/
theorem eq_pow_find_of_dvd_irreducible_pow {a p : Associates α} (hp : Irreducible p)
    [∀ n : ℕ, Decidable (a ∣ p ^ n)] {n : ℕ} (h : a ∣ p ^ n) :
    a = p ^ @Nat.find (fun n => a ∣ p ^ n) _ ⟨n, h⟩ := by
  classical rw [count_factors_eq_find_of_dvd_pow hp, ← eq_pow_count_factors_of_dvd_pow hp h]
  exact h

end Associates
