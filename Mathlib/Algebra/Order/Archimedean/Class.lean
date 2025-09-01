/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Data.Finset.Max
import Mathlib.Order.Antisymmetrization
import Mathlib.Order.Hom.WithTopBot
import Mathlib.Order.UpperLower.CompleteLattice
import Mathlib.Order.UpperLower.Principal

/-!
# Archimedean classes of a linearly ordered group

This file defines archimedean classes of a given linearly ordered group. Archimedean classes
measure to what extent the group fails to be Archimedean. For additive group, elements `a` and `b`
in the same class are "equivalent" in the sense that there exist two natural numbers
`m` and `n` such that `|a| ≤ m • |b|` and `|b| ≤ n • |a|`. An element `a` in a higher class than `b`
is "infinitesimal" to `b` in the sense that `n • |a| < |b|` for all natural number `n`.

## Main definitions

* `ArchimedeanClass` is the archimedean class for additive linearly ordered group.
* `MulArchimedeanClass` is the archimedean class for multiplicative linearly ordered group.
* `ArchimedeanClass.orderHom` and `MulArchimedeanClass.orderHom` are `OrderHom` over
  archimedean classes lifted from ordered group homomorphisms.
* `ArchimedeanClass.ballAddSubgroup` and `MulArchimedeanClass.ballSubgroup` are subgroups
  formed by an open interval of archimedean classes
* `ArchimedeanClass.closedBallAddSubgroup` and `MulArchimedeanClass.closedBallSubgroup` are
  subgroups formed by a closed interval of archimedean classes.

## Main statements

The following theorems state that an ordered commutative group is (mul-)archimedean if and only if
all non-identity elements belong to the same (`Mul`-)`ArchimedeanClass`:
* `ArchimedeanClass.archimedean_of_mk_eq_mk` / `MulArchimedeanClass.mulArchimedean_of_mk_eq_mk`
* `ArchimedeanClass.mk_eq_mk_of_archimedean` / `MulArchimedeanClass.mk_eq_mk_of_mulArchimedean`

## Implementation notes

Archimedean classes are equipped with a linear order, where elements with smaller absolute value
are placed in a *higher* classes by convention. Ordering backwards this way simplifies
formalization of theorems such as the Hahn embedding theorem.

To naturally derive this order, we first define it on the underlying group via the type
synonym (`Mul`-)`ArchimedeanOrder`, and define (`Mul`-)`ArchimedeanClass` as `Antisymmetrization` of
the order.

-/

section ArchimedeanOrder
variable {M : Type*}

variable (M) in
/-- Type synonym to equip a ordered group with a new `Preorder` defined by the infinitesimal order
of elements. `a` is said less than `b` if `b` is infinitesimal comparing to `a`, or more precisely,
`∀ n, |b|ₘ ^ n < |a|ₘ`. If `a` and `b` are neither infinitesimal to each other, they are equivalent
in this order. -/
@[to_additive ArchimedeanOrder
/-- Type synonym to equip a ordered group with a new `Preorder` defined by the infinitesimal order
of elements. `a` is said less than `b` if `b` is infinitesimal comparing to `a`, or more precisely,
`∀ n, n • |b| < |a|`. If `a` and `b` are neither infinitesimal to each other, they are equivalent
in this order. -/]
def MulArchimedeanOrder := M

namespace MulArchimedeanOrder

/-- Create a `MulArchimedeanOrder` element from the underlying type. -/
@[to_additive /-- Create a `ArchimedeanOrder` element from the underlying type. -/]
def of : M ≃ MulArchimedeanOrder M := Equiv.refl _

/-- Retrieve the underlying value from a `MulArchimedeanOrder` element. -/
@[to_additive /-- Retrieve the underlying value from a `ArchimedeanOrder` element. -/]
def val : MulArchimedeanOrder M ≃ M := Equiv.refl _

@[to_additive (attr := simp)]
theorem of_symm_eq : (of (M := M)).symm = val := rfl

@[to_additive (attr := simp)]
theorem val_symm_eq : (val (M := M)).symm = of := rfl

@[to_additive (attr := simp)]
theorem of_val (a : MulArchimedeanOrder M) : of (val a) = a := rfl

@[to_additive (attr := simp)]
theorem val_of (a : M) : val (of a) = a := rfl

variable [Group M] [Lattice M]

@[to_additive]
instance : LE (MulArchimedeanOrder M) where
  le a b := ∃ n, |b.val|ₘ ≤ |a.val|ₘ ^ n

@[to_additive]
instance : LT (MulArchimedeanOrder M) where
  lt a b := ∀ n, |b.val|ₘ ^ n < |a.val|ₘ

@[to_additive]
theorem le_def {a b : MulArchimedeanOrder M} : a ≤ b ↔ ∃ n, |b.val|ₘ ≤ |a.val|ₘ ^ n := .rfl

@[to_additive]
theorem lt_def {a b : MulArchimedeanOrder M} : a < b ↔ ∀ n, |b.val|ₘ ^ n < |a.val|ₘ := .rfl

variable {M : Type*}
variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

@[to_additive]
instance : Preorder (MulArchimedeanOrder M) where
  le_refl a := ⟨1, by simp⟩
  le_trans a b c := by
    intro ⟨m, hm⟩ ⟨n, hn⟩
    use m * n
    rw [pow_mul]
    exact hn.trans (pow_le_pow_left' hm n)
  lt_iff_le_not_ge a b := by
    rw [lt_def, le_def, le_def]
    suffices (∀ (n : ℕ), |b.val|ₘ ^ n < |a.val|ₘ) → ∃ n, |b.val|ₘ ≤ |a.val|ₘ ^ n by
      simpa using this
    intro h
    obtain h := (h 1).le
    exact ⟨1, by simpa using h⟩

@[to_additive]
instance : IsTotal (MulArchimedeanOrder M) (· ≤ ·) where
  total a b := by
    obtain hab | hab := le_total |a.val|ₘ |b.val|ₘ
    · exact .inr ⟨1, by simpa using hab⟩
    · exact .inl ⟨1, by simpa using hab⟩

variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]

/-- An `OrderMonoidHom` can be made to an `OrderHom` between their `MulArchimedeanOrder`. -/
@[to_additive /-- An `OrderAddMonoidHom` can be made to an `OrderHom` between their
`ArchimedeanOrder`. -/]
noncomputable
def orderHom (f : M →*o N) : MulArchimedeanOrder M →o MulArchimedeanOrder N where
  toFun a := of (f a.val)
  monotone' := by
    rintro a b ⟨n, hn⟩
    simp_rw [le_def, val_of, ← map_mabs, ← map_pow]
    exact ⟨n, OrderHomClass.monotone f hn⟩

end MulArchimedeanOrder

end ArchimedeanOrder

variable {M : Type*}
variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable (M) in
/-- `MulArchimedeanClass M` is the quotient of the group `M` by multiplicative archimedean
equivalence, where two elements `a` and `b` are in the same class iff
`(∃ m : ℕ, |b|ₘ ≤ |a|ₘ ^ m) ∧ (∃ n : ℕ, |a|ₘ ≤ |b|ₘ ^ n)`. -/
@[to_additive ArchimedeanClass
/-- `ArchimedeanClass M` is the quotient of the additive group `M` by additive archimedean
equivalence, where two elements `a` and `b` are in the same class iff
`(∃ m : ℕ, |b| ≤ m • |a|) ∧ (∃ n : ℕ, |a| ≤ n • |b|)`. -/]
def MulArchimedeanClass := Antisymmetrization (MulArchimedeanOrder M) (· ≤ ·)

namespace MulArchimedeanClass

/-- The archimedean class of a given element. -/
@[to_additive /-- The archimedean class of a given element. -/]
def mk (a : M) : MulArchimedeanClass M := toAntisymmetrization _ (MulArchimedeanOrder.of a)

/-- An induction principle for `MulArchimedeanClass`. -/
@[to_additive (attr := elab_as_elim, induction_eliminator)
/-- An induction principle for `ArchimedeanClass` -/]
theorem ind {motive : MulArchimedeanClass M → Prop} (mk : ∀ a, motive (.mk a)) : ∀ x, motive x :=
  Antisymmetrization.ind _ mk

@[to_additive]
theorem «forall» {p : MulArchimedeanClass M → Prop} : (∀ A, p A) ↔ ∀ a, p (mk a) := Quotient.forall

variable (M) in
@[to_additive]
theorem mk_surjective : Function.Surjective <| mk (M := M) := Quotient.mk_surjective

variable (M) in
@[to_additive (attr := simp)]
theorem range_mk : Set.range (mk (M := M)) = Set.univ := Set.range_eq_univ.mpr (mk_surjective M)

@[to_additive]
theorem mk_eq_mk {a b : M} : mk a = mk b ↔ (∃ m, |b|ₘ ≤ |a|ₘ ^ m) ∧ (∃ n, |a|ₘ ≤ |b|ₘ ^ n) := by
  unfold mk toAntisymmetrization
  rw [Quotient.eq]
  rfl

/-- Lift a `M → α` function to `MulArchimedeanClass M → α`. -/
@[to_additive /-- Lift a `M → α` function to `ArchimedeanClass M → α`. -/]
def lift {α : Type*} (f : M → α) (h : ∀ a b, mk a = mk b → f a = f b) :
    MulArchimedeanClass M → α :=
  Quotient.lift f fun _ _ h' ↦ h _ _ <| mk_eq_mk.mpr h'

@[to_additive (attr := simp)]
theorem lift_mk {α : Type*} (f : M → α) (h : ∀ a b, mk a = mk b → f a = f b)
    (a : M) : lift f h (mk a) = f a := by
  unfold lift
  exact Quotient.lift_mk f (fun _ _ h' ↦ h _ _ <| mk_eq_mk.mpr h') a

/-- Lift a `M → M → α` function to `MulArchimedeanClass M → MulArchimedeanClass M → α`. -/
@[to_additive /-- Lift a `M → M → α` function to `ArchimedeanClass M → ArchimedeanClass M → α`. -/]
def lift₂ {α : Type*} (f : M → M → α)
    (h : ∀ a₁ b₁ a₂ b₂, mk a₁ = mk b₁ → mk a₂ = mk b₂ → f a₁ a₂ = f b₁ b₂) :
    MulArchimedeanClass M → MulArchimedeanClass M → α :=
  Quotient.lift₂ f fun _ _ _ _ h₁ h₂ ↦ h _ _ _ _ (mk_eq_mk.mpr h₁) (mk_eq_mk.mpr h₂)

@[to_additive (attr := simp)]
theorem lift₂_mk {α : Type*} (f : M → M → α)
    (h : ∀ a₁ b₁ a₂ b₂, mk a₁ = mk b₁ → mk a₂ = mk b₂ → f a₁ a₂ = f b₁ b₂)
    (a b : M) : lift₂ f h (mk a) (mk b) = f a b := by
  unfold lift₂
  exact Quotient.lift₂_mk f (fun _ _ _ _ h₁ h₂ ↦ h _ _ _ _ (mk_eq_mk.mpr h₁) (mk_eq_mk.mpr h₂)) a b

/-- Choose a representative element from a given archimedean class. -/
@[to_additive /-- Choose a representative element from a given archimedean class. -/]
noncomputable
def out (A : MulArchimedeanClass M) : M := (Quotient.out A).val

@[to_additive (attr := simp)]
theorem mk_out (A : MulArchimedeanClass M) : mk A.out = A := Quotient.out_eq' A

@[to_additive (attr := simp)]
theorem mk_inv (a : M) : mk a⁻¹ = mk a :=
  mk_eq_mk.mpr ⟨⟨1, by simp⟩, ⟨1, by simp⟩⟩

@[to_additive]
theorem mk_div_comm (a b : M) : mk (a / b) = mk (b / a) := by
  rw [← mk_inv, inv_div]

@[to_additive (attr := simp)]
theorem mk_mabs (a : M) : mk |a|ₘ = mk a :=
  mk_eq_mk.mpr ⟨⟨1, by simp⟩, ⟨1, by simp⟩⟩

@[to_additive]
noncomputable
instance : LinearOrder (MulArchimedeanClass M) := by
  classical
  unfold MulArchimedeanClass
  infer_instance

@[to_additive]
theorem mk_le_mk : mk a ≤ mk b ↔ ∃ n, |b|ₘ ≤ |a|ₘ ^ n := .rfl

@[to_additive]
theorem mk_lt_mk : mk a < mk b ↔ ∀ n, |b|ₘ ^ n < |a|ₘ := .rfl

/-- 1 is in its own class (see `MulArchimedeanClass.mk_eq_top_iff`),
which is also the largest class. -/
@[to_additive /-- 0 is in its own class (see `ArchimedeanClass.mk_eq_top_iff`),
which is also the largest class. -/]
instance : OrderTop (MulArchimedeanClass M) where
  top := mk 1
  le_top A := by
    induction A using ind with | mk a
    rw [mk_le_mk]
    exact ⟨1, by simp⟩

variable (M) in
@[to_additive (attr := simp)]
theorem mk_one : mk 1 = (⊤ : MulArchimedeanClass M) := rfl

@[to_additive (attr := simp)]
theorem mk_eq_top_iff : mk a = ⊤ ↔ a = 1 where
  mp := by simp [← mk_one, mk_eq_mk]
  mpr := by simp_all

@[to_additive (attr := simp)]
theorem top_eq_mk_iff : ⊤ = mk a ↔ a = 1 := by
  rw [eq_comm, mk_eq_top_iff]

variable (M) in
@[to_additive (attr := simp)]
theorem out_top : (⊤ : MulArchimedeanClass M).out = 1 := by
  rw [← mk_eq_top_iff, mk_out]

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
  exact h1.not_gt h2

@[to_additive]
theorem mk_left_le_mk_mul (hab : mk a ≤ mk b) : mk a ≤ mk (a * b) := by
  simpa [hab] using min_le_mk_mul (a := a) (b := b)

@[to_additive]
theorem mk_right_le_mk_mul (hba : mk b ≤ mk a) : mk b ≤ mk (a * b) := by
  simpa [hba] using min_le_mk_mul (a := a) (b := b)

@[to_additive]
theorem mk_mul_eq_mk_left (h : mk a < mk b) : mk (a * b) = mk a := by
  refine le_antisymm (mk_le_mk.mpr ⟨2, ?_⟩) (mk_left_le_mk_mul h.le)
  rw [mk_lt_mk] at h
  apply (mabs_mul' _ b).trans
  rw [mul_comm b a, pow_two, mul_le_mul_iff_right]
  apply le_of_mul_le_mul_left' (a := |b|ₘ)
  rw [mul_comm a b]
  exact (pow_two |b|ₘ ▸ (h 2).le).trans (mabs_mul' a b)

@[to_additive]
theorem mk_mul_eq_mk_right (h : mk b < mk a) : mk (a * b) = mk b :=
  mul_comm a b ▸ mk_mul_eq_mk_left h

/-- The product over a set of an elements in distinct classes is in the lowest class. -/
@[to_additive /-- The sum over a set of an elements in distinct classes is in the lowest class. -/]
theorem mk_prod {ι : Type*} [LinearOrder ι] {s : Finset ι} (hnonempty : s.Nonempty)
    {a : ι → M} :
    StrictMonoOn (mk ∘ a) s → mk (∏ i ∈ s, (a i)) = mk (a (s.min' hnonempty)) := by
  induction hnonempty using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons i s hi hs ih =>
    intro hmono
    obtain ih := ih (hmono.mono (by simp))
    rw [Finset.prod_cons]
    have hminmem : s.min' hs ∈ (Finset.cons i s hi) :=
      Finset.mem_cons_of_mem (Finset.min'_mem _ _)
    have hne : mk (a i) ≠ mk (a (s.min' hs)) := by
      by_contra!
      obtain eq := hmono.injOn (by simp) hminmem this
      rw [eq] at hi
      exact hi (Finset.min'_mem _ hs)
    rw [← ih] at hne
    obtain hlt|hlt := lt_or_gt_of_ne hne
    · rw [mk_mul_eq_mk_left hlt]
      congr
      apply le_antisymm (Finset.le_min' _ _ _ ?_) (Finset.min'_le _ _ (by simp))
      intro y hy
      obtain rfl | hmem := Finset.mem_cons.mp hy
      · rfl
      · refine (lt_of_lt_of_le ?_ (Finset.min'_le _ _ hmem)).le
        apply (hmono.lt_iff_lt (by simp) hminmem).mp
        rw [ih] at hlt
        exact hlt
    · rw [mul_comm, mk_mul_eq_mk_left hlt, ih]
      congr 2
      refine le_antisymm (Finset.le_min' _ _ _ ?_) (Finset.min'_le _ _ hminmem)
      intro y hy
      obtain rfl | hmem := Finset.mem_cons.mp hy
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
theorem mulArchimedean_of_mk_eq_mk (h : ∀ a ≠ (1 : M), ∀ b ≠ 1, mk a = mk b) :
    MulArchimedean M where
  arch x y hy := by
    by_cases hx : x ≤ 1
    · use 0
      simpa using hx
    · have hx : 1 < x := lt_of_not_ge hx
      have hxy : mk x = mk y := h x hx.ne.symm y hy.ne.symm
      obtain ⟨_, ⟨m, hm⟩⟩ := (mk_eq_mk).mp hxy
      rw [mabs_eq_self.mpr hx.le, mabs_eq_self.mpr hy.le] at hm
      exact ⟨m, hm⟩

@[to_additive mk_eq_mk_of_archimedean]
theorem mk_eq_mk_of_mulArchimedean [MulArchimedean M] (ha : a ≠ 1) (hb : b ≠ 1) :
    mk a = mk b := by
  obtain hm := MulArchimedean.arch |b|ₘ (show 1 < |a|ₘ by simpa using ha)
  obtain hn := MulArchimedean.arch |a|ₘ (show 1 < |b|ₘ by simpa using hb)
  exact mk_eq_mk.mpr ⟨hm, hn⟩

section Hom
variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]

/-- An `OrderMonoidHom` can be lifted to an `OrderHom` over archimedean classes. -/
@[to_additive
/-- An `OrderAddMonoidHom` can be lifted to an `OrderHom` over archimedean classes. -/]
noncomputable
def orderHom (f : M →*o N) : MulArchimedeanClass M →o MulArchimedeanClass N :=
  (MulArchimedeanOrder.orderHom f).antisymmetrization

@[to_additive (attr := simp)]
theorem orderHom_mk (f : M →*o N) (a : M) : orderHom f (mk a) = mk (f a) := rfl

@[to_additive]
theorem map_mk_eq (f : M →*o N) (h : mk a = mk b) : mk (f a) = mk (f b) := by
  rw [← orderHom_mk, ← orderHom_mk, h]

@[to_additive]
theorem map_mk_le (f : M →*o N) (h : mk a ≤ mk b) : mk (f a) ≤ mk (f b) := by
  rw [← orderHom_mk, ← orderHom_mk]
  exact OrderHomClass.monotone _ h

@[to_additive]
theorem orderHom_injective {f : M →*o N} (h : Function.Injective f) :
    Function.Injective (orderHom f) := by
  intro a b
  induction a using ind with | mk a
  induction b using ind with | mk b
  simp_rw [orderHom_mk, mk_eq_mk, ← map_mabs, ← map_pow]
  obtain hmono := (OrderHomClass.monotone f).strictMono_of_injective h
  intro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
  exact ⟨⟨m, hmono.le_iff_le.mp hm⟩, ⟨n, hmono.le_iff_le.mp hn⟩⟩

@[to_additive (attr := simp)]
theorem orderHom_top (f : M →*o N) : orderHom f ⊤ = ⊤ := by
  rw [← mk_one, ← mk_one, orderHom_mk, map_one]

end Hom

section LiftHom

variable {α : Type*} [PartialOrder α]

/-- Lift a function `M → α` that's monotone along archimedean classes to a
monotone function `MulArchimedeanClass M →o α`. -/
@[to_additive /-- Lift a function `M → α` that's monotone along archimedean classes to a
monotone function `ArchimedeanClass M →o α`. -/]
noncomputable
def liftOrderHom (f : M → α) (h : ∀ a b, mk a ≤ mk b → f a ≤ f b) :
    MulArchimedeanClass M →o α where
  toFun := lift f fun a b heq ↦ le_antisymm (h a b heq.le) (h b a heq.ge)
  monotone' A B hle := by
    induction A using ind with | mk a
    induction B using ind with | mk b
    simpa using h a b (mk_le_mk.mp hle)

@[to_additive (attr := simp)]
theorem liftOrderHom_mk (f : M → α) (h : ∀ a b, mk a ≤ mk b → f a ≤ f b) (a : M) :
    liftOrderHom f h (mk a) = f a :=
  lift_mk f (fun a b heq ↦ le_antisymm (h a b heq.le) (h b a heq.ge)) a

end LiftHom

/-- Given a `UpperSet` of `MulArchimedeanClass`,
all group elements belonging to these classes form a subsemigroup.
This is not yet a subgroup because it doesn't contain the identity if `s = ⊤`. -/
@[to_additive /-- Given a `UpperSet` of `ArchimedeanClass`,
all group elements belonging to these classes form a subsemigroup.
This is not yet a subgroup because it doesn't contain the identity if `s = ⊤`. -/]
def subsemigroup (s : UpperSet (MulArchimedeanClass M)) : Subsemigroup M where
  carrier := mk ⁻¹' s
  mul_mem' {a b} ha hb := by
    rw [Set.mem_preimage] at ha hb ⊢
    obtain h | h := min_le_iff.mp (min_le_mk_mul a b)
    · exact s.upper h ha
    · exact s.upper h hb

/-- Make `MulArchimedeanClass.subsemigroup` a subgroup by assigning
s = ⊤ with a junk value ⊥. -/
@[to_additive /-- Make `ArchimedeanClass.subsemigroup` a subgroup by assigning
s = ⊤ with a junk value ⊥. -/]
noncomputable
def subgroup (s : UpperSet (MulArchimedeanClass M)) : Subgroup M :=
  open Classical in
  if hs : s = ⊤ then
    ⊥
  else {
    subsemigroup s with
    one_mem' := by
      rw [subsemigroup, Set.mem_preimage]
      obtain ⟨u, hu⟩ := UpperSet.coe_nonempty.mpr hs
      simpa using s.upper (by simp) hu
    inv_mem' := by simp [subsemigroup]
  }

variable {s : UpperSet (MulArchimedeanClass M)}

@[to_additive]
theorem subsemigroup_eq_subgroup_of_ne_top (hs : s ≠ ⊤) :
    subsemigroup s = (subgroup s : Set M)  := by
  simp [subgroup, hs]

variable (M) in
@[to_additive (attr := simp)]
theorem subgroup_eq_bot : subgroup (M := M) ⊤ = ⊥ := by
  simp [subgroup]

@[to_additive (attr := simp)]
theorem mem_subgroup_iff (hs : s ≠ ⊤) : a ∈ subgroup s ↔ mk a ∈ s := by
  simp [subgroup, subsemigroup, hs]

@[to_additive]
theorem subgroup_strictAntiOn : StrictAntiOn (subgroup (M := M)) (Set.Iio ⊤) := by
  intro s hs t ht hst
  rw [← SetLike.coe_ssubset_coe]
  rw [← subsemigroup_eq_subgroup_of_ne_top (Set.mem_Iio.mp hs).ne_top]
  rw [← subsemigroup_eq_subgroup_of_ne_top (Set.mem_Iio.mp ht).ne_top]
  refine Set.ssubset_iff_subset_ne.mpr ⟨by simpa [subsemigroup] using hst.le, ?_⟩
  contrapose! hst with heq
  apply le_of_eq
  simpa [mk_surjective, subsemigroup] using heq

@[to_additive]
theorem subgroup_antitone : Antitone (subgroup (M := M)) := by
  intro s t hst
  obtain rfl | hs := eq_or_ne s ⊤
  · rw [eq_top_iff.mpr hst]
  obtain rfl | ht := eq_or_ne t ⊤
  · simp
  rwa [subgroup_strictAntiOn.le_iff_ge ht.lt_top hs.lt_top]

/-- An open ball defined by `MulArchimedeanClass.subgroup` of `UpperSet.Ioi c`.
For `c = ⊤`, we assign the junk value `⊥`. -/
@[to_additive /--An open ball defined by `ArchimedeanClass.addSubgroup` of `UpperSet.Ioi c`.
For `c = ⊤`, we assign the junk value `⊥`. -/]
noncomputable
abbrev ballSubgroup (c : MulArchimedeanClass M) := subgroup (UpperSet.Ioi c)

/-- A closed ball defined by `MulArchimedeanClass.subgroup` of `UpperSet.Ici c`. -/
@[to_additive /-- A closed ball defined by `ArchimedeanClass.addSubgroup` of `UpperSet.Ici c`. -/]
noncomputable
abbrev closedBallSubgroup (c : MulArchimedeanClass M) := subgroup (UpperSet.Ici c)

@[to_additive]
theorem mem_ballSubgroup_iff {a : M} {c : MulArchimedeanClass M} (hA : c ≠ ⊤) :
    a ∈ ballSubgroup c ↔ c < mk a := by
  simp [hA]

@[to_additive]
theorem mem_closedBallSubgroup_iff {a : M} {c : MulArchimedeanClass M} :
    a ∈ closedBallSubgroup c ↔ c ≤ mk a := by
  simp

variable (M) in
@[to_additive (attr := simp)]
theorem ballSubgroup_top : ballSubgroup (M := M) ⊤ = ⊥ := by
  convert subgroup_eq_bot M
  simp

variable (M) in
@[to_additive (attr := simp)]
theorem closedBallSubgroup_top : closedBallSubgroup (M := M) ⊤ = ⊥ := by
  ext
  simp

@[to_additive]
theorem ballSubgroup_antitone : Antitone (ballSubgroup (M := M)) := by
  intro _ _ h
  exact subgroup_antitone <| (UpperSet.Ioi_strictMono _).monotone h

end MulArchimedeanClass

variable (M) in
/-- `FiniteMulArchimedeanClass M` is the quotient of the non-one elements of the group `M` by
multiplicative archimedean equivalence, where two elements `a` and `b` are in the same class iff
`(∃ m : ℕ, |b|ₘ ≤ |a|ₘ ^ m) ∧ (∃ n : ℕ, |a|ₘ ≤ |b|ₘ ^ n)`.

It is defined as the subtype of non-top elements of `MulArchimedeanClass M`
(`⊤ : MulArchimedeanClass M` is the archimedean class of `1`).

This is useful since the family of non-top archimedean classes is linearly independent. -/
@[to_additive FiniteArchimedeanClass
/-- `FiniteArchimedeanClass M` is the quotient of the non-zero elements of the additive group `M` by
additive archimedean equivalence, where two elements `a` and `b` are in the same class iff
`(∃ m : ℕ, |b| ≤ m • |a|) ∧ (∃ n : ℕ, |a| ≤ n • |b|)`.

It is defined as the subtype of non-top elements of `ArchimedeanClass M`
(`⊤ : ArchimedeanClass M` is the archimedean class of `0`).

This is useful since the family of non-top archimedean classes is linearly independent. -/]
abbrev FiniteMulArchimedeanClass := {A : MulArchimedeanClass M // A ≠ ⊤}

namespace FiniteMulArchimedeanClass

/-- Create a `FiniteMulArchimedeanClass` from a non-one element. -/
@[to_additive /-- Create a `FiniteArchimedeanClass` from a non-zero element. -/]
def mk (a : M) (h : a ≠ 1) : FiniteMulArchimedeanClass M :=
  ⟨MulArchimedeanClass.mk a, MulArchimedeanClass.mk_eq_top_iff.not.mpr h⟩

@[to_additive (attr := simp)]
theorem val_mk {a : M} (h : a ≠ 1) : (mk a h).val = MulArchimedeanClass.mk a := rfl

@[to_additive]
theorem mk_le_mk {a : M} (ha : a ≠ 1) {b : M} (hb : b ≠ 1) :
    mk a ha ≤ mk b hb ↔ MulArchimedeanClass.mk a ≤ MulArchimedeanClass.mk b := .rfl

@[to_additive]
theorem mk_lt_mk {a : M} (ha : a ≠ 1) {b : M} (hb : b ≠ 1) :
    mk a ha < mk b hb ↔ MulArchimedeanClass.mk a < MulArchimedeanClass.mk b := .rfl

/-- An induction principle for `FiniteMulArchimedeanClass`. -/
@[to_additive (attr := elab_as_elim) /--An induction principle for `FiniteArchimedeanClass`. -/]
theorem ind {motive : FiniteMulArchimedeanClass M → Prop}
    (mk : ∀ a, (ha : a ≠ 1) → motive (.mk a ha)) : ∀ x, motive x := by
  simpa [FiniteMulArchimedeanClass, MulArchimedeanClass.forall]

@[to_additive]
instance [MulArchimedean M] : Subsingleton (FiniteMulArchimedeanClass M) where
  allEq A B := by
    induction A using ind with | mk a ha
    induction B using ind with | mk b hb
    simpa [mk] using MulArchimedeanClass.mk_eq_mk_of_mulArchimedean ha hb

@[to_additive]
instance [Nontrivial M] : Nonempty (FiniteMulArchimedeanClass M) := by
  obtain ⟨x, hx⟩ := exists_ne (1 : M)
  exact ⟨mk x hx, by simpa using hx⟩

/-- Lift a `f : {a : M // a ≠ 1} → α` function to `FiniteMulArchimedeanClass M → α`. -/
@[to_additive /-- Lift a `f : {a : M // a ≠ 0} → α` function to `FiniteArchimedeanClass M → α`. -/]
def lift {α : Type*} (f : {a : M // a ≠ 1} → α)
    (h : ∀ (a b : {a : M // a ≠ 1}), mk a.val a.prop = mk b.val b.prop → f a = f b) :
    FiniteMulArchimedeanClass M → α := fun ⟨A, hA⟩ ↦ by
  refine (MulArchimedeanClass.lift
    (fun b ↦ if h : b = 1 then ⊤ else WithTop.some (f ⟨b, h⟩)) (fun a b h' ↦ ?_) A).untop ?_
  · simp only
    split_ifs with ha hb hb
    · rfl
    · exact (hb (MulArchimedeanClass.mk_eq_top_iff.mp (ha ▸ h').symm)).elim
    · exact (ha (MulArchimedeanClass.mk_eq_top_iff.mp (by apply hb ▸ h'))).elim
    · rw [h ⟨a, ha⟩ ⟨b, hb⟩ (by simpa [mk] using h')]
  · induction A using MulArchimedeanClass.ind with | mk a
    simpa using MulArchimedeanClass.mk_eq_top_iff.not.mp hA

@[to_additive (attr := simp)]
theorem lift_mk {α : Type*} (f : {a : M // a ≠ 1} → α)
    (h : ∀ (a b : {a : M // a ≠ 1}), mk a.val a.prop = mk b.val b.prop → f a = f b)
    {a : M} (ha : a ≠ 1) :
    lift f h (mk a ha) = f ⟨a, ha⟩ := by simp [lift, mk, ha]

/-- Lift a function `{a : M // a ≠ 1} → α` that's monotone along archimedean classes to a
monotone function `FiniteMulArchimedeanClass M →o α`. -/
@[to_additive /-- Lift a function `{a : M // a ≠ 1} → α` that's monotone along archimedean
classes to a monotone function `FiniteArchimedeanClass M₁ →o α`. -/]
noncomputable
def liftOrderHom {α : Type*} [PartialOrder α]
    (f : {a : M // a ≠ 1} → α)
    (h : ∀ (a b : {a : M // a ≠ 1}), mk a.val a.prop ≤ mk b.val b.prop → f a ≤ f b) :
    FiniteMulArchimedeanClass M →o α where
  toFun := lift f fun a b heq ↦ le_antisymm (h a b heq.le) (h b a heq.ge)
  monotone' A B hAB := by
    induction A using ind with | mk a ha
    induction B using ind with | mk b hb
    simpa using h ⟨a, ha⟩ ⟨b, hb⟩ hAB

@[to_additive (attr := simp)]
theorem liftOrderHom_mk {α : Type*} [PartialOrder α]
    (f : {a : M // a ≠ 1} → α)
    (h : ∀ (a b : {a : M // a ≠ 1}), mk a.val a.prop ≤ mk b.val b.prop → f a ≤ f b)
    {a : M} (ha : a ≠ 1) : liftOrderHom f h (mk a ha) = f ⟨a, ha⟩ :=
  lift_mk f (fun a b heq ↦ le_antisymm (h a b heq.le) (h b a heq.ge)) ha

variable (M) in
/-- Adding top to the type of finite classes yields the type of all classes. -/
@[to_additive /-- Adding top to the type of finite classes yields the type of all classes. -/]
noncomputable
def withTopOrderIso : WithTop (FiniteMulArchimedeanClass M) ≃o MulArchimedeanClass M :=
  WithTop.subtypeOrderIso

@[to_additive (attr := simp)]
theorem withTopOrderIso_apply_coe (A : FiniteMulArchimedeanClass M) :
    withTopOrderIso M (A : WithTop (FiniteMulArchimedeanClass M)) = A.val :=
  WithTop.subtypeOrderIso_apply_coe A

@[to_additive]
theorem withTopOrderIso_symm_apply {a : M} (h : a ≠ 1) :
    (withTopOrderIso M).symm (MulArchimedeanClass.mk a) = mk a h := by
  unfold mk withTopOrderIso
  convert WithTop.subtypeOrderIso_symm_apply (MulArchimedeanClass.mk_eq_top_iff.ne.mpr h)

end FiniteMulArchimedeanClass
