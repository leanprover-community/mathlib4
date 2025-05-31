/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Finset.Max

/-!
# Archimedean classes of linearly ordered group.

This file defines archimedean classes of a given linearly ordered group.

## Main definitions

* `archimedeanClass` are classes of elements in a ordered additive commutative group
  that are archimedean equivelent. Two elements `a` and `b` are archimedean equivalent when there
  exists two positive integers `m` and `n` such that `|a| ≤ m • |b|` and `|b| ≤ n • |a|`.
* `mulArchimedeanClass` is the multiplicative version of `archimedeanClass`.
  Two elements `a` and `b` are mul-archimedean equivalent when there
  exists two positive integers `m` and `n` such that `|a|ₘ ≤ |b|ₘ ^ m` and `|b|ₘ ≤ |a|ₘ ^ n`.
* `archimedeanClass.orderHom` and `mulArchimedeanClass.orderHom` are `OrderHom` over
  archimedean classes lifted from ordered group homomorphisms.

## Main statements
* `archimedeanClass.archimedean_of_mk_eq_mk` / `mulArchimedeanClass.mulArchimedean_of_mk_eq_mk`:
  an ordered commutative group is (mul-)archimedean if
  all non-identity elements belong to the same (mul-)archimedeanClass.

-/

variable {M: Type*}
variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M]

variable (M) in
/-- Two elements are mul-archimedean equivalent iff there exists two positive integers
`m` and `n` such that `|a|ₘ ≤ |b|ₘ ^ m` and `|b|ₘ ≤ |a|ₘ ^ n`. -/
@[to_additive archimedeanEquiv "Two elements are archimedean equivalent iff there exists
two positive integers `m` and `n` such that `|a| ≤ m • |b|` and `|b| ≤ n • |a|`."]
def mulArchimedeanEquiv : Setoid M where
  r (a b) := (∃ m, m ≠ 0 ∧ |a|ₘ ≤ |b|ₘ ^ m) ∧ (∃ n, n ≠ 0 ∧ |b|ₘ ≤ |a|ₘ ^ n)
  iseqv := {
    refl (a) := ⟨⟨1, by simp, by simp⟩, ⟨1, by simp, by simp⟩⟩
    symm (h) := h.symm
    trans := by
      intro a b c ⟨⟨m, hm0, hm⟩, ⟨n, hn0, hn⟩⟩ ⟨⟨m', hm0', hm'⟩, ⟨n', hn0', hn'⟩⟩
      refine ⟨⟨m' * m, by simp [hm0, hm0'], ?_⟩, ⟨n * n', by simp [hn0, hn0'], ?_⟩⟩
      · refine le_trans hm ?_
        rw [pow_mul]
        exact pow_le_pow_left' hm' m
      · refine le_trans hn' ?_
        rw [pow_mul]
        exact pow_le_pow_left' hn n'
  }

variable (M) in
/-- `mulArchimedeanClass` is the quotient of `M` over `mulArchimedeanEquiv M`. -/
@[to_additive archimedeanClass "`archimedeanClass` is the quotient of `M`
over `archimedeanEquiv M`."]
def mulArchimedeanClass := Quotient (mulArchimedeanEquiv M)

namespace mulArchimedeanClass

/-- The archimedean class of a given element. -/
@[to_additive "The archimedean class of a given element."]
def mk (a : M) : mulArchimedeanClass M := Quotient.mk'' a

variable (M) in
@[to_additive]
theorem mk_surjective : Function.Surjective <| mk (M := M) := Quotient.mk''_surjective

variable (M) in
@[to_additive (attr := simp)]
theorem range_mk : Set.range (mk (M := M)) = Set.univ := Set.range_eq_univ.mpr (mk_surjective M)

/-- Choose a representative element from a given archimedean class. -/
@[to_additive "Choose a representative element from a given archimedean class."]
noncomputable
def out (A : mulArchimedeanClass M) : M := Quotient.out A

@[to_additive (attr := simp)]
theorem out_eq (A : mulArchimedeanClass M) : mk A.out = A := Quotient.out_eq' A

@[to_additive]
theorem eq {a b : M} :
    mk a = mk b ↔ (∃ m, m ≠ 0 ∧ |a|ₘ ≤ |b|ₘ ^ m) ∧ (∃ n, n ≠ 0 ∧ |b|ₘ ≤ |a|ₘ ^ n) := Quotient.eq''

@[to_additive]
theorem mk_out (a : M) :
    (∃ m, m ≠ 0 ∧ |(mk a).out|ₘ ≤ |a|ₘ ^ m) ∧ (∃ n, n ≠ 0 ∧ |a|ₘ ≤ |(mk a).out|ₘ ^ n) :=
  eq.mp (by simp)

@[to_additive (attr := simp)]
theorem mk_inv (a : M) : mk a⁻¹ = mk a :=
  eq.mpr ⟨⟨1, by simp, by simp⟩, ⟨1, by simp, by simp⟩⟩

@[to_additive]
theorem mk_div_comm (a b : M) : mk (a / b) = mk (b / a) := by
  rw [← mk_inv, inv_div]

@[to_additive (attr := simp)]
theorem mk_mabs (a : M) : mk |a|ₘ = mk a :=
  eq.mpr ⟨⟨1, by simp, by simp⟩, ⟨1, by simp, by simp⟩⟩

variable (M) in
/-- Following the definition of archimedean classes, the identity element is always
in its own class. We denote it as the zero class. -/
@[to_additive "Following the definition of archimedean classes, the identity element is always
in its own class. We denote it as the zero class."]
instance instZero : Zero (mulArchimedeanClass M) := ⟨mk 1⟩

variable (M) in
@[to_additive (attr := simp)]
theorem mk_one : mk (1 : M) = 0 := rfl

@[to_additive (attr := simp)]
theorem mk_eq_zero_iff {a : M} : mk a = 0 ↔ a = 1 := by
  constructor
  · intro h
    rw [← mk_one, eq] at h
    obtain ⟨⟨_, _, hm⟩, _⟩ := h
    simpa using hm
  · intro h
    rw [h, mk_one]

variable (M) in
@[to_additive (attr := simp)]
theorem zero_out : (0 : mulArchimedeanClass M).out = 1 := by
  rw [← mk_eq_zero_iff, out_eq]

variable (M) in
@[to_additive]
instance instNontrivial [Nontrivial M]: Nontrivial (mulArchimedeanClass M) where
  exists_pair_ne := by
    obtain ⟨x, hx⟩ := exists_ne (1 : M)
    exact ⟨mk x, 0, mk_eq_zero_iff.ne.mpr hx⟩

variable (M) in
/-- We equip archimedean classes with linear order using the absolute value of their
representatives. By convention, elements with smaller absolute value are in *larger* classes.
Ordering backwards this way simplifies formalization of theorems such as
Hahn embedding theorem. -/
@[to_additive "We equip archimedean classes with linear order using the absolute value of their
representatives. By convention, elements with smaller absolute value are in *larger* classes.
Ordering backwards this way simplifies formalization of theorems such as
Hahn embedding theorem."]
noncomputable
instance instLinearOrder : LinearOrder (mulArchimedeanClass M) :=
  LinearOrder.lift' (OrderDual.toDual |·.out|ₘ) (by
    intro A B
    simp only [EmbeddingLike.apply_eq_iff_eq]
    intro h
    simpa using congr_arg mk h
  )

@[to_additive]
theorem le (A B : mulArchimedeanClass M) : A ≤ B ↔ |B.out|ₘ ≤ |A.out|ₘ := by rfl

@[to_additive]
theorem lt (A B : mulArchimedeanClass M) : A < B ↔ |B.out|ₘ < |A.out|ₘ := by rfl

/-- The zero class is the largest class -/
@[to_additive le_zero "The zero class is the largest class"]
theorem le_zero (A : mulArchimedeanClass M) : A ≤ 0 := by
  rw [le]
  simp

@[to_additive]
theorem ne_zero_of_lt {A B : mulArchimedeanClass M} (h : A < B) : A ≠ 0 :=
  lt_of_lt_of_le h (le_zero _) |>.ne

variable (M) in
@[to_additive]
noncomputable
instance instOrderTop : OrderTop (mulArchimedeanClass M) where
  top := 0
  le_top := le_zero

@[to_additive]
theorem mk_lt_mk {a b : M} : mk a < mk b ↔ ∀ n, |b|ₘ ^ n < |a|ₘ := by
  obtain ⟨⟨m, hm0, hm⟩, ⟨n, hn0, hn⟩⟩ := mk_out a
  obtain ⟨⟨m', hm0', hm'⟩, ⟨n', hn0', hn'⟩⟩ := mk_out b
  constructor
  · intro h k
    by_cases hk0 : k = 0
    · rw [hk0]
      simp only [pow_zero, one_lt_mabs]
      contrapose! h
      rw [h]
      simpa using le_zero (mk b)
    · have hne : ¬ mk a = mk b := ne_of_lt h
      rw [eq] at hne
      simp only [not_and, not_exists, not_le, forall_exists_index] at hne
      by_contra!
      obtain hne' := hne k ⟨hk0, this⟩ (m * n') (by simp [hn0', hm0])
      rw [lt] at h
      contrapose! hne'
      refine le_of_lt (lt_of_le_of_lt hn' ?_)
      rw [pow_mul, (pow_left_strictMono hn0').lt_iff_lt]
      exact lt_of_lt_of_le h hm
  · intro h
    rw [lt, ← (pow_left_strictMono hn0).lt_iff_lt]
    rw [← (pow_left_strictMono hn0).le_iff_le] at hm'
    apply lt_of_le_of_lt hm'
    rw [← pow_mul]
    exact lt_of_lt_of_le (h (m' * n)) hn

variable (M) in
@[to_additive]
theorem mk_antitoneOn : AntitoneOn mk (Set.Ici (1 : M)) := by
  intro a ha b hb hab
  contrapose! hab
  rw [mk_lt_mk] at hab
  obtain h := hab 1
  rw [mabs_eq_self.mpr ha, mabs_eq_self.mpr hb] at h
  simpa using h

variable (M) in
@[to_additive]
theorem mk_monotoneOn : MonotoneOn mk (Set.Iic (1 : M)) := by
  intro a ha b hb hab
  contrapose! hab
  rw [mk_lt_mk] at hab
  obtain h := hab 1
  rw [mabs_eq_inv_self.mpr ha, mabs_eq_inv_self.mpr hb] at h
  simpa using h

@[to_additive]
theorem mk_le_mk_self_mul_of_mk_eq {a b : M} (hab : mk a = mk b) : mk a ≤ mk (a * b) := by
  by_contra! h
  obtain h1 := mk_lt_mk.mp h 2
  obtain h2 := mk_lt_mk.mp (hab ▸ h) 2
  rw [pow_two] at h1 h2
  obtain h1 := lt_of_lt_of_le h1 (mabs_mul _ _)
  obtain h2 := lt_of_lt_of_le h2 (mabs_mul _ _)
  simp only [mul_lt_mul_iff_left, mul_lt_mul_iff_right] at h1 h2
  have := h1.trans h2
  simp at this

@[to_additive]
theorem mk_eq_mk_self_mul_of_mk_lt {a b : M} (h : mk a < mk b) : mk a = mk (a * b) := by
  rw [mk_lt_mk] at h
  refine eq.mpr ⟨⟨2, by simp, ?_⟩, ⟨2, by simp, ?_⟩⟩
  · apply (mabs_mul' _ b).trans
    rw [mul_comm b a, pow_two, mul_le_mul_iff_right]
    apply le_of_mul_le_mul_left' (a := |b|ₘ)
    rw [mul_comm a b]
    refine le_trans ?_ (mabs_mul' a b)
    obtain h := (h 2).le
    rw [pow_two] at h
    exact h
  · apply (mabs_mul _ _).trans
    rw [pow_two, mul_le_mul_iff_left]
    simpa using (h 1).le

/-- The product over a set of an elements in distinct classes is in the lowest class. -/
@[to_additive "The sum over a set of an elements in distinct classes is in the lowest class."]
theorem mk_prod {ι : Type*} [LinearOrder ι] {s : Finset ι} (hnonempty : s.Nonempty)
    {a : ι → M}  :
    StrictMonoOn (mk ∘ a) s → mk (∏ i ∈ s, (a i)) = mk (a (s.min' hnonempty)) := by
  induction hnonempty using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons i s hi hs ih =>
    intro hmono
    obtain ih := ih (hmono.mono (by simp))
    rw [Finset.prod_cons]
    have hminmem : s.min' hs ∈ (Finset.cons i s hi) :=
      Finset.mem_cons_of_mem (by apply Finset.min'_mem)
    have hne : mk (a i) ≠ mk (a (s.min' hs)) := by
      by_contra!
      obtain eq := hmono.injOn (by simp) hminmem this
      rw [eq] at hi
      exact hi (Finset.min'_mem _ hs)
    rw [← ih] at hne
    obtain hlt|hlt := lt_or_gt_of_ne hne
    · rw [← mk_eq_mk_self_mul_of_mk_lt hlt]
      congr
      apply le_antisymm (Finset.le_min' _ _ _ ?_) (Finset.min'_le _ _ (by simp))
      intro y hy
      obtain rfl|hmem := Finset.mem_cons.mp hy
      · rfl
      · refine (lt_of_lt_of_le ?_ (Finset.min'_le _ _ hmem)).le
        apply (hmono.lt_iff_lt (by simp) hminmem).mp
        rw [ih] at hlt
        exact hlt
    · rw [mul_comm, ← mk_eq_mk_self_mul_of_mk_lt hlt, ih]
      congr 2
      refine le_antisymm (Finset.le_min' _ _ _ ?_) (Finset.min'_le _ _ hminmem)
      intro y hy
      obtain rfl|hmem := Finset.mem_cons.mp hy
      · apply ((hmono.lt_iff_lt hminmem (by simp)).mp ?_).le
        rw [ih] at hlt
        exact hlt
      · exact Finset.min'_le _ _ hmem

@[to_additive]
theorem min_le_mk_mul (a b : M) : min (mk a) (mk b) ≤ mk (a * b) := by
  obtain hab|hab|hab := lt_trichotomy (mk a) (mk b)
  · rw [inf_le_iff]
    exact Or.inl (mk_eq_mk_self_mul_of_mk_lt hab).le
  · rw [← hab]
    simpa using mk_le_mk_self_mul_of_mk_eq hab
  · rw [inf_le_iff]
    right
    rw [mul_comm]
    exact (mk_eq_mk_self_mul_of_mk_lt hab).le

@[to_additive]
theorem lt_of_mk_lt_mk_of_one_le {a b : M} (h : mk a < mk b) (hpos : 1 ≤ a) : b < a := by
  obtain h := (mk_lt_mk).mp h 1
  rw [pow_one, mabs_lt, mabs_eq_self.mpr hpos] at h
  exact h.2

@[to_additive]
theorem lt_of_mk_lt_mk_of_le_one {a b : M} (h : mk a < mk b) (hneg : a ≤ 1) : a < b := by
  obtain h := (mk_lt_mk).mp h 1
  rw [pow_one, mabs_lt, mabs_eq_inv_self.mpr hneg, inv_inv] at h
  exact h.1

@[to_additive]
theorem one_lt_of_one_lt_of_mk_lt {a b : M} (ha : 1 < a) (hab : mk a < mk (b / a)) :
    1 < b := by
  suffices a⁻¹ < b / a by
    simpa using this
  apply lt_of_mk_lt_mk_of_le_one
  · simpa using hab
  · simpa using ha.le

@[to_additive archimedean_of_mk_eq_mk]
theorem mulArchimedean_of_mk_eq_mk (h : ∀ (a b : M), a ≠ 1 → b ≠ 1 → mk a = mk b) :
    MulArchimedean M where
  arch := by
    intro x y hy
    by_cases hx : x ≤ 1
    · use 0
      simpa using hx
    · have hx : 1 < x := lt_of_not_ge hx
      have hxy : mk x = mk y := h x y hx.ne.symm hy.ne.symm
      obtain ⟨⟨m, _, hm⟩, _⟩ := (mulArchimedeanClass.eq).mp hxy
      rw [mabs_eq_self.mpr hx.le, mabs_eq_self.mpr hy.le] at hm
      exact ⟨m, hm⟩

section Hom

variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]
variable {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N]

/-- An ordered group homomorphism can be lifted to an OrderHom
over archimedean classes. -/
@[to_additive "An ordered group homomorphism can be lifted to an OrderHom
over archimedean classes."]
noncomputable
def orderHom (f : F) : mulArchimedeanClass M →o mulArchimedeanClass N where
  toFun := fun a ↦ mk (f a.out)
  monotone' := by
    intro a b h
    contrapose! h
    rw [mk_lt_mk] at h
    rw [← out_eq a, ← out_eq b, mk_lt_mk]
    intro n
    obtain h := h n
    contrapose! h
    obtain h := OrderHomClass.monotone f h
    rw [map_pow, map_mabs, map_mabs] at h
    exact h

@[to_additive]
theorem orderHom_apply (f : F) (A : mulArchimedeanClass M) : (orderHom f) A = mk (f A.out) := rfl

@[to_additive]
theorem map_mk (f : F) (a : M) : mk (f a) = (orderHom f) (mk a) := by
  rw [orderHom_apply]
  apply eq.mpr
  have heq : mk a = mk (mk a).out := by
    rw [out_eq]
  obtain ⟨⟨m, hm0, hm⟩, ⟨n, hn0, hn⟩⟩ := eq.mp heq
  refine ⟨⟨m, hm0, ?_⟩, ⟨n, hn0, ?_⟩⟩
  all_goals
    rw [← map_mabs, ← map_mabs, ← map_pow]
    apply OrderHomClass.monotone
    try exact hm
    try exact hn

@[to_additive]
theorem map_mk_eq (f : F) {a b : M} (h : mk a = mk b) : mk (f a) = mk (f b) := by
  rw [map_mk, map_mk, h]

@[to_additive]
theorem map_mk_le (f : F) {a b : M} (h : mk a ≤ mk b) : mk (f a) ≤ mk (f b) := by
  rw [map_mk, map_mk]
  apply OrderHomClass.monotone
  exact h

@[to_additive]
theorem orderHom_injective {f : F} (h : Function.Injective f) :
    Function.Injective (orderHom f) := by
  intro a b
  nth_rw 2 [← out_eq a]
  nth_rw 2 [← out_eq b]
  rw [orderHom_apply, orderHom_apply, eq, eq]
  simp_rw [← map_mabs, ← map_pow]
  intro h
  obtain ⟨⟨m, hm0, hm⟩, ⟨n, hn0, hn⟩⟩ := h
  refine ⟨⟨m, hm0, ?_⟩, ⟨n, hn0, ?_⟩⟩
  · contrapose! hm
    apply lt_of_le_of_ne
    · apply OrderHomClass.monotone f hm.le
    · contrapose! hm
      exact (h hm).symm.le
  · contrapose! hn
    apply lt_of_le_of_ne
    · apply OrderHomClass.monotone f hn.le
    · contrapose! hn
      exact (h hn).symm.le

@[to_additive (attr := simp)]
theorem orderHom_zero (f : F) :
    (orderHom f) (0 : mulArchimedeanClass M) = (0 : mulArchimedeanClass N) := by
  rw [← mk_one, ← mk_one, ← map_mk]
  simp

end Hom

end mulArchimedeanClass
