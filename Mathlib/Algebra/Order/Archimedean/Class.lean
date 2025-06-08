/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Order.Antisymmetrization

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

## Implementation notes

Archimedean classes are equiped with a linear order, where elements with smaller absolute value
are placed in a *higher* classes by convention. In other words, if `b` is infinitesimal relative to
`a`, `b` is in a higher class than `a`. Ordering backwards this way simplifies formalization of
theorems such as the Hahn embedding theorem.

To naturally derive this order, we first define it on the underlying group via the type
synonym (`Mul`-)`ArchimedeanOrder`, and define (`Mul`-)`ArchimedeanClass` as `Antisymmetrization` of
the order.

-/

section Pre

variable {M: Type*}

variable (M) in
/-- Type synonym to equip a ordered group with a new `Preorder` defined by the infinitesimal order
of elements. `a` is said less than `b` if `b` is infinitesimal comparing to `a`, or more precisely,
`∀ n, |b|ₘ ^ n < |a|ₘ`. If `a` and `b` are neither infinitesimal to each other, they are equivalent
in this order. -/
@[to_additive ArchimedeanOrder
"Type synonym to equip a ordered group with a new `Preorder` defined by the infinitesimal order
of elements. `a` is said less than `b` if `b` is infinitesimal comparing to `a`, or more precisely,
`∀ n, n • |b| < |a|`. If `a` and `b` are neither infinitesimal to each other, they are equivalent
in this order."]
def MulArchimedeanOrder := M

namespace MulArchimedeanOrder

/-- Create a `MulArchimedeanOrder` element from the underlying type. -/
@[to_additive "Create a `ArchimedeanOrder` element from the underlying type."]
def of (a : M) : MulArchimedeanOrder M := a

/-- Retrieve the underlying value from a `MulArchimedeanOrder` element. -/
@[to_additive "Retrieve the underlying value from a `ArchimedeanOrder` element."]
def val (a : MulArchimedeanOrder M) : M := a

@[to_additive (attr := simp)]
theorem of_val (a : MulArchimedeanOrder M) : of (val a) = a := rfl

@[to_additive (attr := simp)]
theorem val_of (a : M) : val (of a) = a := rfl

variable [Group M] [Lattice M]

variable (M) in
@[to_additive]
instance instLE : LE (MulArchimedeanOrder M) where
  le a b := ∃ n, |b.val|ₘ ≤ |a.val|ₘ ^ n

variable (M) in
@[to_additive]
instance instLT : LT (MulArchimedeanOrder M) where
  lt a b := ∀ n, |b.val|ₘ ^ n < |a.val|ₘ

@[to_additive]
theorem le {a b : MulArchimedeanOrder M} :
  a ≤ b ↔ ∃ n, |b.val|ₘ ≤ |a.val|ₘ ^ n := by rfl

@[to_additive]
theorem lt {a b : MulArchimedeanOrder M} :
  a < b ↔ ∀ n, |b.val|ₘ ^ n < |a.val|ₘ := by rfl

variable {M: Type*}
variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable (M) in
@[to_additive]
instance instPreorder : Preorder (MulArchimedeanOrder M) where
  le_refl a := ⟨1, by simp⟩
  le_trans a b c := by
    intro ⟨m, hm⟩ ⟨n, hn⟩
    use m * n
    rw [pow_mul]
    exact hn.trans (pow_le_pow_left' hm n)
  lt_iff_le_not_le a b := by
    rw [lt, le, le]
    suffices (∀ (n : ℕ), |b.val|ₘ ^ n < |a.val|ₘ) → ∃ n, |b.val|ₘ ≤ |a.val|ₘ ^ n by
      simpa using this
    intro h
    obtain h := (h 1).le
    exact ⟨1, by simpa using h⟩

variable (M) in
@[to_additive]
instance instIsTotal : IsTotal (MulArchimedeanOrder M) (· ≤ ·) where
  total := by
    simp_rw [le]
    by_contra!
    obtain ⟨a, b, hab, hba⟩ := this
    exact (lt_self_iff_false _).mp <| (pow_one |a.val|ₘ ▸ hab 1).trans (pow_one |b.val|ₘ ▸ hba 1)

variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]
variable {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N]

/-- An ordered group homomorphism can be made to an
`orderHom` between their `MulArchimedeanOrder`. -/
@[to_additive "An ordered group homomorphism can be made to an
`orderHom` between their `ArchimedeanOrder`."]
noncomputable
def orderHom (f : F) : MulArchimedeanOrder M →o MulArchimedeanOrder N where
  toFun a := of (f a.val)
  monotone' a b h := by
    rw [le] at h ⊢
    obtain ⟨n, hn⟩ := h
    simp_rw [val_of, ← map_mabs, ← map_pow]
    exact ⟨n, OrderHomClass.monotone f hn⟩

end MulArchimedeanOrder

end Pre

variable {M: Type*}
variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable (M) in
/-- `MulArchimedeanClass` is the antisymmetrization of `MulArchimedeanOrder`. -/
@[to_additive ArchimedeanClass
"`ArchimedeanClass` is the antisymmetrization of `ArchimedeanOrder`."]
def MulArchimedeanClass := Antisymmetrization (MulArchimedeanOrder M) (· ≤ ·)


namespace MulArchimedeanClass

/-- The archimedean class of a given element. -/
@[to_additive "The archimedean class of a given element."]
def mk (a : M) : MulArchimedeanClass M := toAntisymmetrization _ (MulArchimedeanOrder.of a)

/-- An induction principle for `MulArchimedeanClass`. -/
@[to_additive (attr := elab_as_elim) "An induction principle for `ArchimedeanClass`"]
theorem ind {motive : MulArchimedeanClass M → Prop} (mk : ∀ a, motive (.mk a)) : ∀ x, motive x :=
  Antisymmetrization.ind _ mk

variable (M) in
@[to_additive]
theorem mk_surjective : Function.Surjective <| mk (M := M) := Quotient.mk_surjective

variable (M) in
@[to_additive (attr := simp)]
theorem range_mk : Set.range (mk (M := M)) = Set.univ := Set.range_eq_univ.mpr (mk_surjective M)

@[to_additive]
theorem eq {a b : M} : mk a = mk b ↔ (∃ m, |b|ₘ ≤ |a|ₘ ^ m) ∧ (∃ n, |a|ₘ ≤ |b|ₘ ^ n) := by
  unfold mk toAntisymmetrization
  rw [Quotient.eq]
  rfl

/-- Choose a representative element from a given archimedean class. -/
@[to_additive "Choose a representative element from a given archimedean class."]
noncomputable
def out (A : MulArchimedeanClass M) : M := (Quotient.out A).val

@[to_additive (attr := simp)]
theorem out_eq (A : MulArchimedeanClass M) : mk A.out = A := Quotient.out_eq' A

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
    obtain ⟨_, ⟨_, hm⟩⟩ := eq.mp h
    simpa using hm
  · intro h
    rw [h]

variable (M) in
@[to_additive (attr := simp)]
theorem mk_one_out : (mk 1 : MulArchimedeanClass M).out = 1 := by
  rw [← mk_eq_mk_one_iff, out_eq]

variable (M) in
@[to_additive]
noncomputable
instance instLinearOrder : LinearOrder (MulArchimedeanClass M) := by
  classical
  exact instLinearOrderAntisymmetrizationLeOfDecidableLEOfDecidableLTOfIsTotal

@[to_additive]
theorem mk_le_mk : mk a ≤ mk b ↔ ∃ n, |b|ₘ ≤ |a|ₘ ^ n := by rfl

@[to_additive]
theorem mk_lt_mk : mk a < mk b ↔ ∀ n, |b|ₘ ^ n < |a|ₘ := by simpa using mk_le_mk.not

@[to_additive]
theorem le_mk_one (A : MulArchimedeanClass M) : A ≤ mk 1 := by
  induction A using ind with | mk a
  rw [mk_le_mk]
  exact ⟨1, by simp⟩

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
  arch x y hy := by
    by_cases hx : x ≤ 1
    · use 0
      simpa using hx
    · have hx : 1 < x := lt_of_not_ge hx
      have hxy : mk x = mk y := h x y hx.ne.symm hy.ne.symm
      obtain ⟨_, ⟨m, hm⟩⟩ := (MulArchimedeanClass.eq).mp hxy
      rw [mabs_eq_self.mpr hx.le, mabs_eq_self.mpr hy.le] at hm
      exact ⟨m, hm⟩

@[to_additive mk_eq_mk_of_archimedean]
theorem mk_eq_mk_of_mulArchimedean [MulArchimedean M] (ha : a ≠ 1) (hb : b ≠ 1) :
    mk a = mk b := by
  obtain hm := MulArchimedean.arch |b|ₘ (show 1 < |a|ₘ by simpa using ha)
  obtain hn := MulArchimedean.arch |a|ₘ (show 1 < |b|ₘ by simpa using hb)
  exact eq.mpr ⟨hm, hn⟩

section Hom

variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]
variable {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N]

/-- An ordered group homomorphism can be lifted to an `OrderHom`
over archimedean classes. -/
@[to_additive "An ordered group homomorphism can be lifted to an `OrderHom`
over archimedean classes."]
noncomputable
def orderHom (f : F) : MulArchimedeanClass M →o MulArchimedeanClass N :=
  (MulArchimedeanOrder.orderHom f).antisymmetrization

@[to_additive (attr := simp)]
theorem orderHom_mk (f : F) (a : M) : orderHom f (mk a) = mk (f a) := rfl

@[to_additive]
theorem map_mk_eq (f : F) (h : mk a = mk b) : mk (f a) = mk (f b) := by
  rw [← orderHom_mk, ← orderHom_mk, h]

@[to_additive]
theorem map_mk_le (f : F) (h : mk a ≤ mk b) : mk (f a) ≤ mk (f b) := by
  rw [← orderHom_mk, ← orderHom_mk]
  exact OrderHomClass.monotone _ h

@[to_additive]
theorem orderHom_injective {f : F} (h : Function.Injective f) :
    Function.Injective (orderHom f) := by
  intro a b
  induction a using ind with | mk a
  induction b using ind with | mk b
  simp_rw [orderHom_mk, eq, ← map_mabs, ← map_pow]
  obtain hmono := (OrderHomClass.monotone f).strictMono_of_injective h
  intro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
  exact ⟨⟨m, hmono.le_iff_le.mp hm⟩, ⟨n, hmono.le_iff_le.mp hn⟩⟩

@[to_additive (attr := simp)]
theorem orderHom_top (f : F) : orderHom f ⊤ = ⊤ := by
  rw [top_eq, top_eq]
  simp

end Hom

end MulArchimedeanClass
