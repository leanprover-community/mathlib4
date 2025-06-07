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

* `ArchimedeanClass` are classes of elements in a ordered additive commutative group
  that are archimedean equivelent. Two elements `a` and `b` are archimedean equivalent when there
  exists two natural numbers `m` and `n` such that `|a| ≤ m • |b|` and `|b| ≤ n • |a|`.
* `MulArchimedeanClass` is the multiplicative version of `ArchimedeanClass`.
  Two elements `a` and `b` are mul-archimedean equivalent when there
  exists two natural numbers `m` and `n` such that `|a|ₘ ≤ |b|ₘ ^ m` and `|b|ₘ ≤ |a|ₘ ^ n`.
* `ArchimedeanClass.orderHom` and `MulArchimedeanClass.orderHom` are `OrderHom` over
  archimedean classes lifted from ordered group homomorphisms.

## Main statements

The following theorems state that an ordered commutative group is (mul-)archimedean if and only if
all non-identity elements belong to the same (`Mul`-)`ArchimedeanClass`:
* `ArchimedeanClass.archimedean_of_mk_eq_mk` / `MulArchimedeanClass.mulArchimedean_of_mk_eq_mk`
* `ArchimedeanClass.mk_eq_mk_of_archimedean` / `MulArchimedeanClass.mk_eq_mk_of_mulArchimedean`

-/

variable {M: Type*}
variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable (M) in
/-- Two elements are mul-archimedean equivalent iff there exists two natural numbers
`m` and `n` such that `|a|ₘ ≤ |b|ₘ ^ m` and `|b|ₘ ≤ |a|ₘ ^ n`. -/
@[to_additive archimedeanEquiv "Two elements are archimedean equivalent iff there exists
two natural numbers `m` and `n` such that `|a| ≤ m • |b|` and `|b| ≤ n • |a|`."]
def mulArchimedeanEquiv : Setoid M where
  r a b := (∃ m, |a|ₘ ≤ |b|ₘ ^ m) ∧ (∃ n, |b|ₘ ≤ |a|ₘ ^ n)
  iseqv.refl _ := ⟨⟨1, by simp⟩, ⟨1, by simp⟩⟩
  iseqv.symm := And.symm
  iseqv.trans {a b c} := by
    intro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ ⟨⟨m', hm'⟩, ⟨n', hn'⟩⟩
    refine ⟨⟨m' * m, hm.trans ?_⟩, ⟨n * n', hn'.trans ?_⟩⟩
    · rw [pow_mul]
      exact pow_le_pow_left' hm' m
    · rw [pow_mul]
      exact pow_le_pow_left' hn n'

variable (M) in
/-- `MulArchimedeanClass` is the quotient of `M` over `mulArchimedeanEquiv M`. -/
@[to_additive ArchimedeanClass "`ArchimedeanClass` is the quotient of `M`
over `archimedeanEquiv M`."]
def MulArchimedeanClass := Quotient (mulArchimedeanEquiv M)

namespace MulArchimedeanClass

/-- The archimedean class of a given element. -/
@[to_additive "The archimedean class of a given element."]
def mk (a : M) : MulArchimedeanClass M := Quotient.mk'' a

variable (M) in
@[to_additive]
theorem mk_surjective : Function.Surjective <| mk (M := M) := Quotient.mk''_surjective

variable (M) in
@[to_additive (attr := simp)]
theorem range_mk : Set.range (mk (M := M)) = Set.univ := Set.range_eq_univ.mpr (mk_surjective M)

/-- Choose a representative element from a given archimedean class. -/
@[to_additive "Choose a representative element from a given archimedean class."]
noncomputable
def out (A : MulArchimedeanClass M) : M := Quotient.out A

@[to_additive (attr := simp)]
theorem out_eq (A : MulArchimedeanClass M) : mk A.out = A := Quotient.out_eq' A

@[to_additive]
theorem eq {a b : M} :
    mk a = mk b ↔ (∃ m, |a|ₘ ≤ |b|ₘ ^ m) ∧ (∃ n, |b|ₘ ≤ |a|ₘ ^ n) := Quotient.eq''

@[to_additive]
theorem mk_out (a : M) :
    (∃ m, |(mk a).out|ₘ ≤ |a|ₘ ^ m) ∧ (∃ n, |a|ₘ ≤ |(mk a).out|ₘ ^ n) :=
  eq.mp (by simp)

@[to_additive (attr := simp)]
theorem mk_inv (a : M) : mk a⁻¹ = mk a :=
  eq.mpr ⟨⟨1, by simp⟩, ⟨1, by simp⟩⟩

@[to_additive]
theorem mk_div_comm (a b : M) : mk (a / b) = mk (b / a) := by
  rw [← mk_inv, inv_div]

@[to_additive (attr := simp)]
theorem mk_mabs (a : M) : mk |a|ₘ = mk a :=
  eq.mpr ⟨⟨1, by simp⟩, ⟨1, by simp⟩⟩

@[to_additive (attr := simp)]
theorem mk_eq_mk_one_iff {a : M} : mk a = mk 1 ↔ a = 1 := by
  constructor
  · intro h
    obtain ⟨⟨_, hm⟩, _⟩ := eq.mp h
    simpa using hm
  · intro h
    rw [h]

variable (M) in
@[to_additive (attr := simp)]
theorem mk_one_out : (mk 1 : MulArchimedeanClass M).out = 1 := by
  rw [← mk_eq_mk_one_iff, out_eq]

variable (M) in
/-- We equip archimedean classes with linear order using the absolute value of their
representatives. By convention, elements with smaller absolute value are in *larger* classes.
Ordering backwards this way simplifies formalization of theorems such as
the Hahn embedding theorem.

While the order is defined using `MulArchimedean.out`, it is equivalently characterized by
`MulArchimedean.mk_le_mk` and `MulArchimedean.mk_lt_mk`, which are recommended to use to
avoid using `MulArchimedean.out`. -/
@[to_additive "We equip archimedean classes with linear order using the absolute value of their
representatives. By convention, elements with smaller absolute value are in *larger* classes.
Ordering backwards this way simplifies formalization of theorems such as
the Hahn embedding theorem.

While the order is defined using `Archimedean.out`, it is equivalently characterized by
`Archimedean.mk_le_mk` and `Archimedean.mk_lt_mk`, which are recommended to use to
avoid using `Archimedean.out`."]
noncomputable
instance instLinearOrder : LinearOrder (MulArchimedeanClass M) :=
  LinearOrder.lift' (OrderDual.toDual |·.out|ₘ) fun A B ↦ by
    simp only [EmbeddingLike.apply_eq_iff_eq]
    intro h
    simpa using congr_arg mk h

@[to_additive]
theorem le (A B : MulArchimedeanClass M) : A ≤ B ↔ |B.out|ₘ ≤ |A.out|ₘ := by rfl

@[to_additive]
theorem lt (A B : MulArchimedeanClass M) : A < B ↔ |B.out|ₘ < |A.out|ₘ := by rfl

@[to_additive]
theorem le_mk_one (A : MulArchimedeanClass M) : A ≤ mk 1 := by
  rw [le]
  simp

@[to_additive]
theorem mk_lt_mk : mk a < mk b ↔ ∀ n, |b|ₘ ^ n < |a|ₘ := by
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := mk_out a
  obtain ⟨⟨m', hm'⟩, ⟨n', hn'⟩⟩ := mk_out b
  constructor
  · intro h k
    have hne : ¬ mk a = mk b := ne_of_lt h
    rw [eq] at hne
    simp only [not_and, not_exists, not_le, forall_exists_index] at hne
    by_contra!
    obtain hne' := hne k this (m * n')
    rw [lt] at h
    contrapose! hne'
    refine hn'.trans ?_
    rw [pow_mul]
    exact pow_le_pow_left' (lt_of_lt_of_le h hm).le n'
  · intro h
    rw [lt]
    apply (pow_left_mono n).reflect_lt
    apply lt_of_le_of_lt (pow_le_pow_left' hm' n)
    rw [← pow_mul]
    exact lt_of_lt_of_le (h (m' * n)) hn

@[to_additive]
theorem mk_le_mk : mk a ≤ mk b ↔ ∃ n, |b|ₘ ≤ |a|ₘ ^ n := by
  simpa using mk_lt_mk.not

variable (M) in
/-- 1 is in its own class, which is also the largest class. -/
@[to_additive "0 is in its own class, which is also the largest class."]
noncomputable
instance instOrderTop : OrderTop (MulArchimedeanClass M) where
  top := mk 1
  le_top := le_mk_one

variable (M) in
@[to_additive]
theorem top_eq : (⊤ : MulArchimedeanClass M) = mk 1 := rfl

variable (M) in
@[to_additive (attr := simp)]
theorem top_out : (⊤ : MulArchimedeanClass M).out = 1 := mk_one_out M

@[to_additive (attr := simp)]
theorem mk_eq_top_iff : mk a = ⊤ ↔ a = 1 := mk_eq_mk_one_iff

variable (M) in
@[to_additive]
instance [Nontrivial M] : Nontrivial (MulArchimedeanClass M) where
  exists_pair_ne := by
    obtain ⟨x, hx⟩ := exists_ne (1 : M)
    exact ⟨mk x, ⊤, mk_eq_top_iff.ne.mpr hx⟩

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
theorem min_le_mk_mul (a b : M) : min (mk a) (mk b) ≤ mk (a * b) := by
  by_contra! h
  rw [lt_min_iff] at h
  have h1 := (mk_lt_mk.mp h.1 2).trans_le (mabs_mul _ _)
  have h2 := (mk_lt_mk.mp h.2 2).trans_le (mabs_mul _ _)
  simp only [mul_lt_mul_iff_left, mul_lt_mul_iff_right, pow_two] at h1 h2
  exact h1.not_lt h2

@[to_additive]
theorem mk_left_le_mk_mul (hab : mk a ≤ mk b) : mk a ≤ mk (a * b) := by
  simpa [hab] using min_le_mk_mul (a := a) (b := b)

@[to_additive]
theorem mk_right_le_mk_mul (hba : mk b ≤ mk a) : mk b ≤ mk (a * b) := by
  simpa [hba] using min_le_mk_mul (a := a) (b := b)

@[to_additive]
theorem mk_left_eq_mk_mul (h : mk a < mk b) : mk a = mk (a * b) := by
  refine le_antisymm (mk_left_le_mk_mul h.le) (mk_le_mk.mpr ⟨2, ?_⟩)
  rw [mk_lt_mk] at h
  apply (mabs_mul' _ b).trans
  rw [mul_comm b a, pow_two, mul_le_mul_iff_right]
  apply le_of_mul_le_mul_left' (a := |b|ₘ)
  rw [mul_comm a b]
  exact (pow_two |b|ₘ ▸ (h 2).le).trans (mabs_mul' a b)

@[to_additive]
theorem mk_right_eq_mk_mul (h : mk b < mk a) : mk b = mk (a * b) :=
  mul_comm a b ▸ mk_left_eq_mk_mul h

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
    · rw [← mk_left_eq_mk_mul hlt]
      congr
      apply le_antisymm (Finset.le_min' _ _ _ ?_) (Finset.min'_le _ _ (by simp))
      intro y hy
      obtain rfl|hmem := Finset.mem_cons.mp hy
      · rfl
      · refine (lt_of_lt_of_le ?_ (Finset.min'_le _ _ hmem)).le
        apply (hmono.lt_iff_lt (by simp) hminmem).mp
        rw [ih] at hlt
        exact hlt
    · rw [mul_comm, ← mk_left_eq_mk_mul hlt, ih]
      congr 2
      refine le_antisymm (Finset.le_min' _ _ _ ?_) (Finset.min'_le _ _ hminmem)
      intro y hy
      obtain rfl|hmem := Finset.mem_cons.mp hy
      · apply ((hmono.lt_iff_lt hminmem (by simp)).mp ?_).le
        rw [ih] at hlt
        exact hlt
      · exact Finset.min'_le _ _ hmem

@[to_additive]
theorem lt_of_mk_lt_mk_of_one_le (h : mk a < mk b) (hpos : 1 ≤ a) : b < a := by
  obtain h := (mk_lt_mk).mp h 1
  rw [pow_one, mabs_lt, mabs_eq_self.mpr hpos] at h
  exact h.2

@[to_additive]
theorem lt_of_mk_lt_mk_of_le_one (h : mk a < mk b) (hneg : a ≤ 1) : a < b := by
  obtain h := (mk_lt_mk).mp h 1
  rw [pow_one, mabs_lt, mabs_eq_inv_self.mpr hneg, inv_inv] at h
  exact h.1

@[to_additive]
theorem one_lt_of_one_lt_of_mk_lt (ha : 1 < a) (hab : mk a < mk (b / a)) :
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
      obtain ⟨⟨m, hm⟩, _⟩ := (MulArchimedeanClass.eq).mp hxy
      rw [mabs_eq_self.mpr hx.le, mabs_eq_self.mpr hy.le] at hm
      exact ⟨m, hm⟩

@[to_additive mk_eq_mk_of_archimedean]
theorem mk_eq_mk_of_mulArchimedean [MulArchimedean M] (ha : a ≠ 1) (hb : b ≠ 1) :
    mk a = mk b := by
  obtain hm := MulArchimedean.arch |a|ₘ (show 1 < |b|ₘ by simpa using hb)
  obtain hn := MulArchimedean.arch |b|ₘ (show 1 < |a|ₘ by simpa using ha)
  exact eq.mpr ⟨hm, hn⟩

section Hom

variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]
variable {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N]

/-- An ordered group homomorphism can be lifted to an OrderHom
over archimedean classes. -/
@[to_additive "An ordered group homomorphism can be lifted to an OrderHom
over archimedean classes."]
noncomputable
def orderHom (f : F) : MulArchimedeanClass M →o MulArchimedeanClass N where
  toFun := Quotient.map f (fun a b h ↦ by
    obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := h
    refine ⟨⟨m, ?_⟩, ⟨n, ?_⟩⟩ <;> rw [← map_mabs, ← map_mabs, ← map_pow]
    · exact OrderHomClass.monotone f hm
    · exact OrderHomClass.monotone f hn
  )
  monotone' a b h := by
    rw [← out_eq a, ← out_eq b] at h ⊢
    show mk (f a.out) ≤ mk (f b.out)
    rw [mk_le_mk] at h ⊢
    obtain ⟨n, hn⟩ := h
    simp_rw [← map_mabs, ← map_pow]
    exact ⟨n, OrderHomClass.monotone f hn⟩

@[to_additive]
theorem map_mk (f : F) (a : M) : mk (f a) = orderHom f (mk a) := rfl

@[to_additive]
theorem map_mk_eq (f : F) (h : mk a = mk b) : mk (f a) = mk (f b) := by
  rw [map_mk, map_mk, h]

@[to_additive]
theorem map_mk_le (f : F) (h : mk a ≤ mk b) : mk (f a) ≤ mk (f b) := by
  rw [map_mk, map_mk]
  exact OrderHomClass.monotone _ h

@[to_additive]
theorem orderHom_injective {f : F} (h : Function.Injective f) :
    Function.Injective (orderHom f) := by
  intro a b
  rw [← out_eq a, ← out_eq b, ← map_mk, ← map_mk, eq, eq]
  simp_rw [← map_mabs, ← map_pow]
  obtain hmono := (OrderHomClass.monotone f).strictMono_of_injective h
  intro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
  exact ⟨⟨m, hmono.le_iff_le.mp hm⟩, ⟨n, hmono.le_iff_le.mp hn⟩⟩

@[to_additive (attr := simp)]
theorem orderHom_top (f : F) : orderHom f ⊤ = ⊤ := by
  rw [top_eq, top_eq, ← map_mk]
  simp

end Hom

end MulArchimedeanClass
