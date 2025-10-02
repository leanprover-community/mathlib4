/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Data.Multiset.OrderedMonoid
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Unique factorization and normalization

## Main definitions
* `UniqueFactorizationMonoid.normalizedFactors`: choose a multiset of prime factors that are unique
  by normalizing them.
* `UniqueFactorizationMonoid.normalizationMonoid`: choose a way of normalizing the elements of a UFM
-/

assert_not_exists Field

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero α] [NormalizationMonoid α]
variable [UniqueFactorizationMonoid α]

/-- Noncomputably determines the multiset of prime factors. -/
noncomputable def normalizedFactors (a : α) : Multiset α :=
  Multiset.map normalize <| factors a

/-- An arbitrary choice of factors of `x : M` is exactly the (unique) normalized set of factors,
if `M` has a trivial group of units. -/
@[simp]
theorem factors_eq_normalizedFactors {M : Type*} [CancelCommMonoidWithZero M]
    [UniqueFactorizationMonoid M] [Subsingleton Mˣ] (x : M) : factors x = normalizedFactors x := by
  unfold normalizedFactors
  convert (Multiset.map_id (factors x)).symm
  ext p
  exact normalize_eq p

theorem prod_normalizedFactors {a : α} (ane0 : a ≠ 0) :
    Associated (normalizedFactors a).prod a := by
  rw [normalizedFactors, factors, dif_neg ane0]
  refine Associated.trans ?_ (Classical.choose_spec (exists_prime_factors a ane0)).2
  rw [← Associates.mk_eq_mk_iff_associated, ← Associates.prod_mk, ← Associates.prod_mk,
    Multiset.map_map]
  congr 2
  ext
  rw [Function.comp_apply, Associates.mk_normalize]

theorem prod_normalizedFactors_eq {a : α} (ane0 : a ≠ 0) :
    (normalizedFactors a).prod = normalize a := by
  trans normalize (normalizedFactors a).prod
  · rw [normalizedFactors, ← map_multiset_prod, normalize_idem]
  · exact normalize_eq_normalize_iff.mpr (dvd_dvd_iff_associated.mpr (prod_normalizedFactors ane0))

theorem prime_of_normalized_factor {a : α} : ∀ x : α, x ∈ normalizedFactors a → Prime x := by
  rw [normalizedFactors, factors]
  split_ifs with ane0; · simp
  intro x hx; rcases Multiset.mem_map.1 hx with ⟨y, ⟨hy, rfl⟩⟩
  rw [(normalize_associated _).prime_iff]
  exact (Classical.choose_spec (UniqueFactorizationMonoid.exists_prime_factors a ane0)).1 y hy

theorem irreducible_of_normalized_factor {a : α} :
    ∀ x : α, x ∈ normalizedFactors a → Irreducible x := fun x h =>
  (prime_of_normalized_factor x h).irreducible

theorem normalize_normalized_factor {a : α} :
    ∀ x : α, x ∈ normalizedFactors a → normalize x = x := by
  rw [normalizedFactors, factors]
  split_ifs with h; · simp
  intro x hx
  obtain ⟨y, _, rfl⟩ := Multiset.mem_map.1 hx
  apply normalize_idem

theorem normalizedFactors_irreducible {a : α} (ha : Irreducible a) :
    normalizedFactors a = {normalize a} := by
  obtain ⟨p, a_assoc, hp⟩ :=
    prime_factors_irreducible ha ⟨prime_of_normalized_factor, prod_normalizedFactors ha.ne_zero⟩
  have p_mem : p ∈ normalizedFactors a := by
    rw [hp]
    exact Multiset.mem_singleton_self _
  convert hp
  rwa [← normalize_normalized_factor p p_mem, normalize_eq_normalize_iff, dvd_dvd_iff_associated]

theorem normalizedFactors_eq_of_dvd (a : α) :
    ∀ᵉ (p ∈ normalizedFactors a) (q ∈ normalizedFactors a), p ∣ q → p = q := by
  intro p hp q hq hdvd
  convert normalize_eq_normalize hdvd
          ((prime_of_normalized_factor _ hp).irreducible.dvd_symm
            (prime_of_normalized_factor _ hq).irreducible hdvd) <;>
    apply (normalize_normalized_factor _ ‹_›).symm

theorem exists_mem_normalizedFactors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) :
    p ∣ a → ∃ q ∈ normalizedFactors a, p ~ᵤ q := fun ⟨b, hb⟩ =>
  have hb0 : b ≠ 0 := fun hb0 => by simp_all
  have : Multiset.Rel Associated (p ::ₘ normalizedFactors b) (normalizedFactors a) :=
    factors_unique
      (fun _ hx =>
        (Multiset.mem_cons.1 hx).elim (fun h => h.symm ▸ hp) (irreducible_of_normalized_factor _))
      irreducible_of_normalized_factor
      (Associated.symm <|
        calc
          Multiset.prod (normalizedFactors a) ~ᵤ a := prod_normalizedFactors ha0
          _ = p * b := hb
          _ ~ᵤ Multiset.prod (p ::ₘ normalizedFactors b) := by
            rw [Multiset.prod_cons]
            exact (prod_normalizedFactors hb0).symm.mul_left _
          )
  Multiset.exists_mem_of_rel_of_mem this (by simp)

theorem exists_mem_normalizedFactors {x : α} (hx : x ≠ 0) (h : ¬IsUnit x) :
    ∃ p, p ∈ normalizedFactors x := by
  obtain ⟨p', hp', hp'x⟩ := WfDvdMonoid.exists_irreducible_factor h hx
  obtain ⟨p, hp, _⟩ := exists_mem_normalizedFactors_of_dvd hx hp' hp'x
  exact ⟨p, hp⟩

@[simp]
theorem normalizedFactors_zero : normalizedFactors (0 : α) = 0 := by
  simp [normalizedFactors, factors]

@[simp]
theorem normalizedFactors_one : normalizedFactors (1 : α) = 0 := by
  rcases subsingleton_or_nontrivial α with h | h
  · dsimp [normalizedFactors, factors]
    simp [Subsingleton.elim (1 : α) 0]
  · rw [← Multiset.rel_zero_right]
    apply factors_unique irreducible_of_normalized_factor
    · intro x hx
      exfalso
      apply Multiset.notMem_zero x hx
    · apply prod_normalizedFactors one_ne_zero

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
      ((prod_normalizedFactors hx).mul_mul (prod_normalizedFactors hy)).trans
        (prod_normalizedFactors (mul_ne_zero hx hy)).symm

@[simp]
theorem normalizedFactors_pow {x : α} (n : ℕ) :
    normalizedFactors (x ^ n) = n • normalizedFactors x := by
  induction n with
  | zero => simp [zero_nsmul]
  | succ n ih =>
    by_cases h0 : x = 0
    · simp [h0, zero_pow n.succ_ne_zero, nsmul_zero]
    rw [pow_succ', succ_nsmul', normalizedFactors_mul h0 (pow_ne_zero _ h0), ih]

theorem _root_.Irreducible.normalizedFactors_pow {p : α} (hp : Irreducible p) (k : ℕ) :
    normalizedFactors (p ^ k) = Multiset.replicate k (normalize p) := by
  rw [UniqueFactorizationMonoid.normalizedFactors_pow, normalizedFactors_irreducible hp,
    Multiset.nsmul_singleton]

theorem normalizedFactors_prod_eq (s : Multiset α) (hs : ∀ a ∈ s, Irreducible a) :
    normalizedFactors s.prod = s.map normalize := by
  induction s using Multiset.induction with
  | empty => rw [Multiset.prod_zero, normalizedFactors_one, Multiset.map_zero]
  | cons a s ih =>
    have ia := hs a (Multiset.mem_cons_self a _)
    have ib := fun b h => hs b (Multiset.mem_cons_of_mem h)
    obtain rfl | ⟨b, hb⟩ := s.empty_or_exists_mem
    · rw [Multiset.cons_zero, Multiset.prod_singleton, Multiset.map_singleton,
        normalizedFactors_irreducible ia]
    haveI := nontrivial_of_ne b 0 (ib b hb).ne_zero
    rw [Multiset.prod_cons, Multiset.map_cons,
      normalizedFactors_mul ia.ne_zero (Multiset.prod_ne_zero fun h => (ib 0 h).ne_zero rfl),
      normalizedFactors_irreducible ia, ih ib, Multiset.singleton_add]

theorem dvd_iff_normalizedFactors_le_normalizedFactors {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
    x ∣ y ↔ normalizedFactors x ≤ normalizedFactors y := by
  constructor
  · rintro ⟨c, rfl⟩
    simp [hx, right_ne_zero_of_mul hy]
  · rw [← (prod_normalizedFactors hx).dvd_iff_dvd_left, ←
      (prod_normalizedFactors hy).dvd_iff_dvd_right]
    apply Multiset.prod_dvd_prod_of_le

theorem _root_.Associated.normalizedFactors_eq {a b : α} (h : Associated a b) :
    normalizedFactors a = normalizedFactors b := by
  unfold normalizedFactors
  have h' : ⇑(normalize (α := α)) = Associates.out ∘ Associates.mk := funext Associates.out_mk
  rw [h', ← Multiset.map_map, ← Multiset.map_map,
    Associates.rel_associated_iff_map_eq_map.mp (factors_rel_of_associated h)]

theorem associated_iff_normalizedFactors_eq_normalizedFactors {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
    x ~ᵤ y ↔ normalizedFactors x = normalizedFactors y :=
  ⟨Associated.normalizedFactors_eq, fun h =>
    (prod_normalizedFactors hx).symm.trans (_root_.trans (by rw [h]) (prod_normalizedFactors hy))⟩

theorem normalizedFactors_of_irreducible_pow {p : α} (hp : Irreducible p) (k : ℕ) :
    normalizedFactors (p ^ k) = Multiset.replicate k (normalize p) := by
  rw [normalizedFactors_pow, normalizedFactors_irreducible hp, Multiset.nsmul_singleton]

theorem zero_notMem_normalizedFactors (x : α) : (0 : α) ∉ normalizedFactors x := fun h =>
  Prime.ne_zero (prime_of_normalized_factor _ h) rfl

theorem ne_zero_of_mem_normalizedFactors {x a : α} (hx : x ∈ normalizedFactors a) : x ≠ 0 :=
  ne_of_mem_of_not_mem hx <| zero_notMem_normalizedFactors a

@[deprecated (since := "2025-05-23")]
alias zero_not_mem_normalizedFactors := zero_notMem_normalizedFactors

theorem dvd_of_mem_normalizedFactors {a p : α} (H : p ∈ normalizedFactors a) : p ∣ a := by
  by_cases hcases : a = 0
  · rw [hcases]
    exact dvd_zero p
  · exact dvd_trans (Multiset.dvd_prod H) (Associated.dvd (prod_normalizedFactors hcases))
@[deprecated (since := "2025-08-26")]
alias dvd_of_normalized_factor := dvd_of_mem_normalizedFactors

theorem mem_normalizedFactors_iff [Subsingleton αˣ] {p x : α} (hx : x ≠ 0) :
    p ∈ normalizedFactors x ↔ Prime p ∧ p ∣ x := by
  constructor
  · intro h
    exact ⟨prime_of_normalized_factor p h, dvd_of_mem_normalizedFactors h⟩
  · rintro ⟨hprime, hdvd⟩
    obtain ⟨q, hqmem, hqeq⟩ := exists_mem_normalizedFactors_of_dvd hx hprime.irreducible hdvd
    rw [associated_iff_eq] at hqeq
    exact hqeq ▸ hqmem

theorem mem_normalizedFactors_iff' {p x : α} (h : x ≠ 0) :
    p ∈ normalizedFactors x ↔ Irreducible p ∧ normalize p = p ∧ p ∣ x := by
  refine ⟨fun h ↦ ⟨irreducible_of_normalized_factor p h, normalize_normalized_factor p h,
    dvd_of_mem_normalizedFactors h⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ?_⟩
  obtain ⟨y, hy₁, hy₂⟩ := exists_mem_factors_of_dvd h h₁ h₃
  exact Multiset.mem_map.mpr ⟨y, hy₁, by
    rwa [← h₂, normalize_eq_normalize_iff_associated, Associated.comm]⟩

/-- Relatively prime elements have disjoint prime factors (as multisets). -/
theorem disjoint_normalizedFactors {a b : α} (hc : IsRelPrime a b) :
    Disjoint (normalizedFactors a) (normalizedFactors b) := by
  rw [Multiset.disjoint_left]
  intro x hxa hxb
  have x_dvd_a := dvd_of_mem_normalizedFactors hxa
  have x_dvd_b := dvd_of_mem_normalizedFactors hxb
  exact (prime_of_normalized_factor x hxa).not_unit (hc x_dvd_a x_dvd_b)

theorem exists_associated_prime_pow_of_unique_normalized_factor {p r : α}
    (h : ∀ {m}, m ∈ normalizedFactors r → m = p) (hr : r ≠ 0) : ∃ i : ℕ, Associated (p ^ i) r := by
  use (normalizedFactors r).card
  have := UniqueFactorizationMonoid.prod_normalizedFactors hr
  rwa [Multiset.eq_replicate_of_mem fun b => h, Multiset.prod_replicate] at this

theorem normalizedFactors_prod_of_prime [Subsingleton αˣ] {m : Multiset α}
    (h : ∀ p ∈ m, Prime p) : normalizedFactors m.prod = m := by
  cases subsingleton_or_nontrivial α
  · obtain rfl : m = 0 := by
      refine Multiset.eq_zero_of_forall_notMem fun x hx ↦ ?_
      simpa [Subsingleton.elim x 0] using h x hx
    simp
  · simpa only [← Multiset.rel_eq, ← associated_eq_eq] using
      prime_factors_unique prime_of_normalized_factor h
        (prod_normalizedFactors (m.prod_ne_zero_of_prime h))

theorem mem_normalizedFactors_eq_of_associated {a b c : α} (ha : a ∈ normalizedFactors c)
    (hb : b ∈ normalizedFactors c) (h : Associated a b) : a = b := by
  rw [← normalize_normalized_factor a ha, ← normalize_normalized_factor b hb,
    normalize_eq_normalize_iff]
  exact Associated.dvd_dvd h

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
        (mt Multiset.eq_zero_iff_forall_notMem.mp (not_forall.mpr ⟨p, not_not.mpr hp⟩))

/--
The multiset of normalized factors of `x` is nil if and only if `x` is a unit.
The converse is true without the nonzero assumption, see `normalizedFactors_of_isUnit`.
-/
theorem normalizedFactors_eq_zero_iff {x : α} (hx : x ≠ 0) :
    normalizedFactors x = 0 ↔ IsUnit x := by
  rw [← not_iff_not, ← normalizedFactors_pos _ hx, pos_iff_ne_zero]

/--
If `x` is a unit, then the multiset of normalized factors of `x` is nil.
The converse is true with a nonzero assumption, see `normalizedFactors_eq_zero_iff`.
-/
theorem normalizedFactors_of_isUnit {x : α} (hx : IsUnit x) :
    normalizedFactors x = 0 := by
  obtain rfl | hx₀ := eq_or_ne x 0
  · simp
  rwa [normalizedFactors_eq_zero_iff hx₀]

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
        (mt (dvd_iff_normalizedFactors_le_normalizedFactors hy hx).mp h.not_ge)

theorem normalizedFactors_multiset_prod (s : Multiset α) (hs : 0 ∉ s) :
    normalizedFactors (s.prod) = (s.map normalizedFactors).sum := by
  cases subsingleton_or_nontrivial α
  · obtain rfl : s = 0 := by
      apply Multiset.eq_zero_of_forall_notMem
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

variable {β : Type*} [CancelCommMonoidWithZero β] [NormalizationMonoid β]
  [UniqueFactorizationMonoid β] {F : Type*} [EquivLike F α β] [MulEquivClass F α β] {f : F}

/--
If the monoid equiv `f : α ≃* β` commutes with `normalize` then, for `a : α`, it yields a
bijection between the `normalizedFactors` of `a` and of `f a`.
-/
def normalizedFactorsEquiv (he : ∀ x, normalize (f x) = f (normalize x)) (a : α) :
    {x // x ∈ normalizedFactors a} ≃ {y // y ∈ normalizedFactors (f a)} :=
  Equiv.subtypeEquiv f fun x ↦ by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · simp [mem_normalizedFactors_iff' ha,
        mem_normalizedFactors_iff' (EmbeddingLike.map_ne_zero_iff.mpr ha), map_dvd_iff_dvd_symm,
        MulEquiv.irreducible_iff, he]

@[simp]
theorem normalizedFactorsEquiv_apply (he : ∀ x, normalize (f x) = f (normalize x))
    {a p : α} (hp : p ∈ normalizedFactors a) :
    normalizedFactorsEquiv he a ⟨p, hp⟩ = f p := rfl

@[simp]
theorem normalizedFactorsEquiv_symm_apply (he : ∀ x, normalize (f x) = f (normalize x))
    {a : α} {q : β} (hq : q ∈ normalizedFactors (f a)) :
    (normalizedFactorsEquiv he a).symm ⟨q, hq⟩ = (MulEquivClass.toMulEquiv f).symm q := rfl

end UniqueFactorizationMonoid

namespace UniqueFactorizationMonoid

open Multiset Associates

variable [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α]

open scoped Classical in
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
      apply prod_normalizedFactors hx)

end UniqueFactorizationMonoid
