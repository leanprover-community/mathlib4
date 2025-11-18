/-
Copyright (c) 2018 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Basic properties of holors

Holors are indexed collections of tensor coefficients. Confusingly,
they are often called tensors in physics and in the neural network
community.

A holor is simply a multidimensional array of values. The size of a
holor is specified by a `List ℕ`, whose length is called the dimension
of the holor.

The tensor product of `x₁ : Holor α ds₁` and `x₂ : Holor α ds₂` is the
holor given by `(x₁ ⊗ x₂) (i₁ ++ i₂) = x₁ i₁ * x₂ i₂`. A holor is "of
rank at most 1" if it is a tensor product of one-dimensional holors.
The CP rank of a holor `x` is the smallest N such that `x` is the sum
of N holors of rank at most 1.

Based on the tensor library found in <https://www.isa-afp.org/entries/Deep_Learning.html>

## References

* <https://en.wikipedia.org/wiki/Tensor_rank_decomposition>
-/


universe u

open List

/-- `HolorIndex ds` is the type of valid index tuples used to identify an entry of a holor
of dimensions `ds`. -/
def HolorIndex (ds : List ℕ) : Type :=
  { is : List ℕ // Forall₂ (· < ·) is ds }

namespace HolorIndex

variable {ds₁ ds₂ ds₃ : List ℕ}

/-- Take the first elements of a `HolorIndex`. -/
def take : ∀ {ds₁ : List ℕ}, HolorIndex (ds₁ ++ ds₂) → HolorIndex ds₁
  | ds, is => ⟨List.take (length ds) is.1, forall₂_take_append is.1 ds ds₂ is.2⟩

/-- Drop the first elements of a `HolorIndex`. -/
def drop : ∀ {ds₁ : List ℕ}, HolorIndex (ds₁ ++ ds₂) → HolorIndex ds₂
  | ds, is => ⟨List.drop (length ds) is.1, forall₂_drop_append is.1 ds ds₂ is.2⟩

theorem cast_type (is : List ℕ) (eq : ds₁ = ds₂) (h : Forall₂ (· < ·) is ds₁) :
    (cast (congr_arg HolorIndex eq) ⟨is, h⟩).val = is := by subst eq; rfl

/-- Right associator for `HolorIndex` -/
def assocRight : HolorIndex (ds₁ ++ ds₂ ++ ds₃) → HolorIndex (ds₁ ++ (ds₂ ++ ds₃)) :=
  cast (congr_arg HolorIndex (append_assoc ds₁ ds₂ ds₃))

/-- Left associator for `HolorIndex` -/
def assocLeft : HolorIndex (ds₁ ++ (ds₂ ++ ds₃)) → HolorIndex (ds₁ ++ ds₂ ++ ds₃) :=
  cast (congr_arg HolorIndex (append_assoc ds₁ ds₂ ds₃).symm)

theorem take_take : ∀ t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.take = t.take.take
  | ⟨is, h⟩ =>
    Subtype.ext <| by
      simp [assocRight, take, cast_type, List.take_take, Nat.le_add_right]

theorem drop_take : ∀ t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.drop.take = t.take.drop
  | ⟨is, h⟩ => Subtype.ext (by simp [assocRight, take, drop, cast_type, List.drop_take])

theorem drop_drop : ∀ t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.drop.drop = t.drop
  | ⟨is, h⟩ => Subtype.ext (by simp [assocRight, drop, cast_type, List.drop_drop])

end HolorIndex

/-- Holor (indexed collections of tensor coefficients) -/
def Holor (α : Type u) (ds : List ℕ) :=
  HolorIndex ds → α

namespace Holor

variable {α : Type} {d : ℕ} {ds : List ℕ} {ds₁ : List ℕ} {ds₂ : List ℕ} {ds₃ : List ℕ}

instance [Inhabited α] : Inhabited (Holor α ds) :=
  ⟨fun _ => default⟩

instance [Zero α] : Zero (Holor α ds) :=
  ⟨fun _ => 0⟩

instance [Add α] : Add (Holor α ds) :=
  ⟨fun x y t => x t + y t⟩

instance [Neg α] : Neg (Holor α ds) :=
  ⟨fun a t => -a t⟩

instance [AddSemigroup α] : AddSemigroup (Holor α ds) := Pi.addSemigroup

instance [AddCommSemigroup α] : AddCommSemigroup (Holor α ds) := Pi.addCommSemigroup

instance [AddMonoid α] : AddMonoid (Holor α ds) := Pi.addMonoid

instance [AddCommMonoid α] : AddCommMonoid (Holor α ds) := Pi.addCommMonoid

instance [AddGroup α] : AddGroup (Holor α ds) := Pi.addGroup

instance [AddCommGroup α] : AddCommGroup (Holor α ds) := Pi.addCommGroup

-- scalar product
instance [Mul α] : SMul α (Holor α ds) :=
  ⟨fun a x => fun t => a * x t⟩

instance [Semiring α] : Module α (Holor α ds) := Pi.module _ _ _

/-- The tensor product of two holors. -/
def mul [Mul α] (x : Holor α ds₁) (y : Holor α ds₂) : Holor α (ds₁ ++ ds₂) := fun t =>
  x t.take * y t.drop

local infixl:70 " ⊗ " => mul

theorem cast_type (eq : ds₁ = ds₂) (a : Holor α ds₁) :
    cast (congr_arg (Holor α) eq) a = fun t => a (cast (congr_arg HolorIndex eq.symm) t) := by
  subst eq; rfl

/-- Right associator for `Holor` -/
def assocRight : Holor α (ds₁ ++ ds₂ ++ ds₃) → Holor α (ds₁ ++ (ds₂ ++ ds₃)) :=
  cast (congr_arg (Holor α) (append_assoc ds₁ ds₂ ds₃))

/-- Left associator for `Holor` -/
def assocLeft : Holor α (ds₁ ++ (ds₂ ++ ds₃)) → Holor α (ds₁ ++ ds₂ ++ ds₃) :=
  cast (congr_arg (Holor α) (append_assoc ds₁ ds₂ ds₃).symm)

theorem mul_assoc0 [Semigroup α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₃) :
    x ⊗ y ⊗ z = (x ⊗ (y ⊗ z)).assocLeft :=
  funext fun t : HolorIndex (ds₁ ++ ds₂ ++ ds₃) => by
    rw [assocLeft]
    unfold mul
    rw [mul_assoc, ← HolorIndex.take_take, ← HolorIndex.drop_take, ← HolorIndex.drop_drop,
      cast_type]
    · rfl
    rw [append_assoc]

theorem mul_assoc [Semigroup α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₃) :
    mul (mul x y) z ≍ mul x (mul y z) := by simp [cast_heq, mul_assoc0, assocLeft]

theorem mul_left_distrib [Distrib α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₂) :
    x ⊗ (y + z) = x ⊗ y + x ⊗ z := funext fun t => left_distrib (x t.take) (y t.drop) (z t.drop)

theorem mul_right_distrib [Distrib α] (x : Holor α ds₁) (y : Holor α ds₁) (z : Holor α ds₂) :
    (x + y) ⊗ z = x ⊗ z + y ⊗ z := funext fun t => add_mul (x t.take) (y t.take) (z t.drop)

@[simp]
nonrec theorem zero_mul {α : Type} [MulZeroClass α] (x : Holor α ds₂) : (0 : Holor α ds₁) ⊗ x = 0 :=
  funext fun t => zero_mul (x (HolorIndex.drop t))

@[simp]
nonrec theorem mul_zero {α : Type} [MulZeroClass α] (x : Holor α ds₁) : x ⊗ (0 : Holor α ds₂) = 0 :=
  funext fun t => mul_zero (x (HolorIndex.take t))

theorem mul_scalar_mul [Mul α] (x : Holor α []) (y : Holor α ds) :
    x ⊗ y = x ⟨[], Forall₂.nil⟩ • y := by
  simp +unfoldPartialApp [mul, SMul.smul, HolorIndex.take, HolorIndex.drop,
    HSMul.hSMul]

-- holor slices
/-- A slice is a subholor consisting of all entries with initial index i. -/
def slice (x : Holor α (d :: ds)) (i : ℕ) (h : i < d) : Holor α ds := fun is : HolorIndex ds =>
  x ⟨i :: is.1, Forall₂.cons h is.2⟩

/-- The 1-dimensional "unit" holor with 1 in the `j`th position. -/
def unitVec [Monoid α] [AddMonoid α] (d : ℕ) (j : ℕ) : Holor α [d] := fun ti =>
  if ti.1 = [j] then 1 else 0

theorem holor_index_cons_decomp (p : HolorIndex (d :: ds) → Prop) :
    ∀ t : HolorIndex (d :: ds),
      (∀ i is, ∀ h : t.1 = i :: is, p ⟨i :: is, by rw [← h]; exact t.2⟩) → p t
  | ⟨[], hforall₂⟩, _ => absurd (forall₂_nil_left_iff.1 hforall₂) (cons_ne_nil d ds)
  | ⟨i :: is, _⟩, hp => hp i is rfl

/-- Two holors are equal if all their slices are equal. -/
theorem slice_eq (x : Holor α (d :: ds)) (y : Holor α (d :: ds)) (h : slice x = slice y) : x = y :=
  funext fun t : HolorIndex (d :: ds) =>
    holor_index_cons_decomp (fun t => x t = y t) t fun i is hiis =>
      have hiisdds : Forall₂ (· < ·) (i :: is) (d :: ds) := by rw [← hiis]; exact t.2
      have hid : i < d := (forall₂_cons.1 hiisdds).1
      have hisds : Forall₂ (· < ·) is ds := (forall₂_cons.1 hiisdds).2
      calc
        x ⟨i :: is, _⟩ = slice x i hid ⟨is, hisds⟩ := congr_arg x (Subtype.ext rfl)
        _ = slice y i hid ⟨is, hisds⟩ := by rw [h]
        _ = y ⟨i :: is, _⟩ := congr_arg y (Subtype.ext rfl)

theorem slice_unitVec_mul [Semiring α] {i : ℕ} {j : ℕ} (hid : i < d) (x : Holor α ds) :
    slice (unitVec d j ⊗ x) i hid = if i = j then x else 0 :=
  funext fun t : HolorIndex ds =>
    if h : i = j then by simp [slice, mul, HolorIndex.take, unitVec, HolorIndex.drop, h]
    else by simp [slice, mul, HolorIndex.take, unitVec, HolorIndex.drop, h]; rfl

theorem slice_add [Add α] (i : ℕ) (hid : i < d) (x : Holor α (d :: ds)) (y : Holor α (d :: ds)) :
    slice x i hid + slice y i hid = slice (x + y) i hid :=
  funext fun t => by simp [slice, (· + ·), Add.add]

theorem slice_zero [Zero α] (i : ℕ) (hid : i < d) : slice (0 : Holor α (d :: ds)) i hid = 0 :=
  rfl

theorem slice_sum [AddCommMonoid α] {β : Type} (i : ℕ) (hid : i < d) (s : Finset β)
    (f : β → Holor α (d :: ds)) : (∑ x ∈ s, slice (f x) i hid) = slice (∑ x ∈ s, f x) i hid := by
  letI := Classical.decEq β
  refine Finset.induction_on s ?_ ?_
  · simp [slice_zero]
  · intro _ _ h_not_in ih
    rw [Finset.sum_insert h_not_in, ih, slice_add, Finset.sum_insert h_not_in]

/-- The original holor can be recovered from its slices by multiplying with unit vectors and
summing up. -/
@[simp]
theorem sum_unitVec_mul_slice [Semiring α] (x : Holor α (d :: ds)) :
    (∑ i ∈ (Finset.range d).attach,
        unitVec d i ⊗ slice x i (Nat.succ_le_of_lt (Finset.mem_range.1 i.prop))) =
      x := by
  apply slice_eq _ _ _
  ext i hid
  rw [← slice_sum]
  simp only [slice_unitVec_mul hid]
  rw [Finset.sum_eq_single (Subtype.mk i <| Finset.mem_range.2 hid)]
  · simp
  · intro (b : { x // x ∈ Finset.range d }) (_ : b ∈ (Finset.range d).attach) (hbi : b ≠ ⟨i, _⟩)
    have hbi' : i ≠ b := by simpa only [Ne, Subtype.ext_iff, Subtype.coe_mk] using hbi.symm
    simp [hbi']
  · intro (hid' : Subtype.mk i _ ∉ Finset.attach (Finset.range d))
    exfalso
    exact absurd (Finset.mem_attach _ _) hid'

-- CP rank
/-- `CPRankMax1 x` means `x` has CP rank at most 1, that is,
  it is the tensor product of 1-dimensional holors. -/
inductive CPRankMax1 [Mul α] : ∀ {ds}, Holor α ds → Prop
  | nil (x : Holor α []) : CPRankMax1 x
  | cons {d} {ds} (x : Holor α [d]) (y : Holor α ds) : CPRankMax1 y → CPRankMax1 (x ⊗ y)

/-- `CPRankMax N x` means `x` has CP rank at most `N`, that is,
  it can be written as the sum of N holors of rank at most 1. -/
inductive CPRankMax [Mul α] [AddMonoid α] : ℕ → ∀ {ds}, Holor α ds → Prop
  | zero {ds} : CPRankMax 0 (0 : Holor α ds)
  | succ (n) {ds} (x : Holor α ds) (y : Holor α ds) :
    CPRankMax1 x → CPRankMax n y → CPRankMax (n + 1) (x + y)

theorem cprankMax_nil [Mul α] [AddMonoid α] (x : Holor α nil) : CPRankMax 1 x := by
  have h := CPRankMax.succ 0 x 0 (CPRankMax1.nil x) CPRankMax.zero
  rwa [add_zero x, zero_add] at h

theorem cprankMax_1 [Mul α] [AddMonoid α] {x : Holor α ds} (h : CPRankMax1 x) :
    CPRankMax 1 x := by
  have h' := CPRankMax.succ 0 x 0 h CPRankMax.zero
  rwa [zero_add, add_zero] at h'

theorem cprankMax_add [Mul α] [AddMonoid α] :
    ∀ {m : ℕ} {n : ℕ} {x : Holor α ds} {y : Holor α ds},
      CPRankMax m x → CPRankMax n y → CPRankMax (m + n) (x + y)
  | 0, n, x, y, hx, hy => by
    match hx with
    | CPRankMax.zero => simp only [zero_add, hy]
  | m + 1, n, _, y, CPRankMax.succ _ x₁ x₂ hx₁ hx₂, hy => by
    suffices CPRankMax (m + n + 1) (x₁ + (x₂ + y)) by
      simpa only [add_comm, add_assoc, add_left_comm] using this
    apply CPRankMax.succ
    · assumption
    · exact cprankMax_add hx₂ hy

theorem cprankMax_mul [NonUnitalNonAssocSemiring α] :
    ∀ (n : ℕ) (x : Holor α [d]) (y : Holor α ds), CPRankMax n y → CPRankMax n (x ⊗ y)
  | 0, x, _, CPRankMax.zero => by simp [mul_zero x, CPRankMax.zero]
  | n + 1, x, _, CPRankMax.succ _ y₁ y₂ hy₁ hy₂ => by
    rw [mul_left_distrib]
    rw [Nat.add_comm]
    apply cprankMax_add
    · exact cprankMax_1 (CPRankMax1.cons _ _ hy₁)
    · exact cprankMax_mul _ x y₂ hy₂

theorem cprankMax_sum [NonUnitalNonAssocSemiring α] {β} {n : ℕ} (s : Finset β)
    (f : β → Holor α ds) : (∀ x ∈ s, CPRankMax n (f x)) → CPRankMax (s.card * n) (∑ x ∈ s, f x) :=
  letI := Classical.decEq β
  Finset.induction_on s (by simp [CPRankMax.zero])
    (by
      intro x s (h_x_notin_s : x ∉ s) ih h_cprank
      simp only [Finset.sum_insert h_x_notin_s, Finset.card_insert_of_notMem h_x_notin_s]
      rw [Nat.right_distrib]
      simp only [Nat.one_mul, Nat.add_comm]
      have ih' : CPRankMax (Finset.card s * n) (∑ x ∈ s, f x) := by
        apply ih
        intro (x : β) (h_x_in_s : x ∈ s)
        simp only [h_cprank, Finset.mem_insert_of_mem, h_x_in_s]
      exact cprankMax_add (h_cprank x (Finset.mem_insert_self x s)) ih')

theorem cprankMax_upper_bound [Semiring α] : ∀ {ds}, ∀ x : Holor α ds, CPRankMax ds.prod x
  | [], x => cprankMax_nil x
  | d :: ds, x => by
    have h_summands :
      ∀ i : { x // x ∈ Finset.range d },
        CPRankMax ds.prod (unitVec d i.1 ⊗ slice x i.1 (mem_range.1 i.2)) :=
      fun i => cprankMax_mul _ _ _ (cprankMax_upper_bound (slice x i.1 (mem_range.1 i.2)))
    have h_dds_prod : (List.cons d ds).prod = Finset.card (Finset.range d) * prod ds := by
      simp [Finset.card_range]
    have :
      CPRankMax (Finset.card (Finset.attach (Finset.range d)) * prod ds)
        (∑ i ∈ Finset.attach (Finset.range d),
          unitVec d i.val ⊗ slice x i.val (mem_range.1 i.2)) :=
      cprankMax_sum (Finset.range d).attach _ fun i _ => h_summands i
    have h_cprankMax_sum :
      CPRankMax (Finset.card (Finset.range d) * prod ds)
        (∑ i ∈ Finset.attach (Finset.range d),
          unitVec d i.val ⊗ slice x i.val (mem_range.1 i.2)) := by rwa [Finset.card_attach] at this
    rw [← sum_unitVec_mul_slice x]
    rw [h_dds_prod]
    exact h_cprankMax_sum

/-- The CP rank of a holor `x`: the smallest N such that
  `x` can be written as the sum of N holors of rank at most 1. -/
noncomputable def cprank [Ring α] (x : Holor α ds) : Nat :=
  @Nat.find (fun n => CPRankMax n x) (Classical.decPred _) ⟨ds.prod, cprankMax_upper_bound x⟩

theorem cprank_upper_bound [Ring α] : ∀ {ds}, ∀ x : Holor α ds, cprank x ≤ ds.prod :=
  fun {ds} x =>
  letI := Classical.decPred fun n : ℕ => CPRankMax n x
  Nat.find_min' ⟨ds.prod, show (fun n => CPRankMax n x) ds.prod from cprankMax_upper_bound x⟩
    (cprankMax_upper_bound x)

end Holor
