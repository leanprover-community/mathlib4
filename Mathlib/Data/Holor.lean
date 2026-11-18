/-
Copyright (c) 2018 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Nat.Find

/-!
# Basic properties of holors

Holors are indexed collections of tensor coefficients. Confusingly,
they are often called tensors in physics and in the neural network
community.

A holor is simply a multidimensional array of values. The size of a
holor is specified by a `List ℕ`, whose length is called the dimension
of the holor.

The tensor product of `x₁ : Holor ds₁ α` and `x₂ : Holor ds₂ α` is the
holor given by `(x₁ ⊗ x₂) (i₁ ++ i₂) = x₁ i₁ * x₂ i₂`. A holor is "of
rank at most 1" if it is a tensor product of one-dimensional holors.
The CP rank of a holor `x` is the smallest N such that `x` is the sum
of N holors of rank at most 1.

Based on the tensor library found in <https://www.isa-afp.org/entries/Deep_Learning.html>

## References

* <https://en.wikipedia.org/wiki/Tensor_rank_decomposition>
-/

@[expose] public section


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
    (cast congr(HolorIndex $eq) ⟨is, h⟩).val = is := by subst eq; rfl

/-- Right associator for `HolorIndex` -/
def assocRight : HolorIndex (ds₁ ++ ds₂ ++ ds₃) → HolorIndex (ds₁ ++ (ds₂ ++ ds₃)) :=
  cast congr(HolorIndex $(append_assoc ds₁ ds₂ ds₃))

/-- Left associator for `HolorIndex` -/
def assocLeft : HolorIndex (ds₁ ++ (ds₂ ++ ds₃)) → HolorIndex (ds₁ ++ ds₂ ++ ds₃) :=
  cast congr(HolorIndex $((append_assoc ds₁ ds₂ ds₃).symm))

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
def Holor (ds : List ℕ) (α : Type u) :=
  HolorIndex ds → α

namespace Holor

variable {α : Type} {d : ℕ} {ds : List ℕ} {ds₁ : List ℕ} {ds₂ : List ℕ} {ds₃ : List ℕ}

instance [Inhabited α] : Inhabited (Holor ds α) :=
  ⟨fun _ => default⟩

instance [Zero α] : Zero (Holor ds α) :=
  ⟨fun _ => 0⟩

instance [Add α] : Add (Holor ds α) :=
  ⟨fun x y t => x t + y t⟩

instance [Neg α] : Neg (Holor ds α) :=
  ⟨fun a t => -a t⟩

instance [AddSemigroup α] : AddSemigroup (Holor ds α) :=
  inferInstanceAs <| AddSemigroup (HolorIndex ds → α)

instance [AddCommSemigroup α] : AddCommSemigroup (Holor ds α) :=
  inferInstanceAs <| AddCommSemigroup (HolorIndex ds → α)

instance [AddMonoid α] : AddMonoid (Holor ds α) :=
  inferInstanceAs <| AddMonoid (HolorIndex ds → α)

instance [AddCommMonoid α] : AddCommMonoid (Holor ds α) :=
  inferInstanceAs <| AddCommMonoid (HolorIndex ds → α)

instance [AddGroup α] : AddGroup (Holor ds α) :=
  inferInstanceAs <| AddGroup (HolorIndex ds → α)

instance [AddCommGroup α] : AddCommGroup (Holor ds α) :=
  inferInstanceAs <| AddCommGroup (HolorIndex ds → α)

-- scalar product
instance [Mul α] : SMul α (Holor ds α) :=
  ⟨fun a x => fun t => a * x t⟩

instance [Semiring α] : Module α (Holor ds α) :=
  inferInstanceAs <| Module α (HolorIndex ds → α)

instance : Functor (Holor ds) where
  map f x t := f (x t)

instance : LawfulFunctor (Holor ds) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

instance : Applicative (Holor ds) where
  pure a _ := a
  seq f x t := f t (x () t)

instance : LawfulApplicative (Holor ds) where
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := rfl
  map_pure _ _ := rfl
  seq_pure _ _ := rfl
  seq_assoc _ _ _ := rfl

/-- The tensor product of two holors. -/
def mul [Mul α] (x : Holor ds₁ α) (y : Holor ds₂ α) : Holor (ds₁ ++ ds₂) α := fun t =>
  x t.take * y t.drop

local infixl:70 " ⊗ " => mul

theorem cast_type (eq : ds₁ = ds₂) (a : Holor ds₁ α) :
    cast congr(Holor $eq α) a = fun t => a (cast congr(HolorIndex $eq.symm) t) := by
  subst eq; rfl

/-- Right associator for `Holor` -/
def assocRight : Holor (ds₁ ++ ds₂ ++ ds₃) α → Holor (ds₁ ++ (ds₂ ++ ds₃)) α :=
  cast congr(Holor $( append_assoc ds₁ ds₂ ds₃) α)

/-- Left associator for `Holor` -/
def assocLeft : Holor (ds₁ ++ (ds₂ ++ ds₃)) α → Holor (ds₁ ++ ds₂ ++ ds₃) α :=
  cast congr(Holor $((append_assoc ds₁ ds₂ ds₃).symm) α)

set_option backward.isDefEq.respectTransparency false in
theorem mul_assoc0 [Semigroup α] (x : Holor ds₁ α) (y : Holor ds₂ α) (z : Holor ds₃ α) :
    x ⊗ y ⊗ z = (x ⊗ (y ⊗ z)).assocLeft :=
  funext fun t : HolorIndex (ds₁ ++ ds₂ ++ ds₃) => by
    rw [assocLeft]
    unfold mul
    rw [mul_assoc, ← HolorIndex.take_take, ← HolorIndex.drop_take, ← HolorIndex.drop_drop,
      cast_type]
    · rfl
    rw [append_assoc]

theorem mul_assoc [Semigroup α] (x : Holor ds₁ α) (y : Holor ds₂ α) (z : Holor ds₃ α) :
    mul (mul x y) z ≍ mul x (mul y z) := by simp [cast_heq, mul_assoc0, assocLeft]

theorem mul_left_distrib [Distrib α] (x : Holor ds₁ α) (y : Holor ds₂ α) (z : Holor ds₂ α) :
    x ⊗ (y + z) = x ⊗ y + x ⊗ z := funext fun t => left_distrib (x t.take) (y t.drop) (z t.drop)

theorem mul_right_distrib [Distrib α] (x : Holor ds₁ α) (y : Holor ds₁ α) (z : Holor ds₂ α) :
    (x + y) ⊗ z = x ⊗ z + y ⊗ z := funext fun t => add_mul (x t.take) (y t.take) (z t.drop)

@[simp]
nonrec theorem zero_mul {α : Type} [MulZeroClass α] (x : Holor ds₂ α) : (0 : Holor ds₁ α) ⊗ x = 0 :=
  funext fun t => zero_mul (x (HolorIndex.drop t))

@[simp]
nonrec theorem mul_zero {α : Type} [MulZeroClass α] (x : Holor ds₁ α) : x ⊗ (0 : Holor ds₂ α) = 0 :=
  funext fun t => mul_zero (x (HolorIndex.take t))

set_option backward.isDefEq.respectTransparency false in
theorem mul_scalar_mul [Mul α] (x : Holor [] α) (y : Holor ds α) :
    x ⊗ y = x ⟨[], Forall₂.nil⟩ • y := by
  simp +unfoldPartialApp [mul, SMul.smul, HolorIndex.take, HolorIndex.drop,
    HSMul.hSMul]

-- holor slices
/-- A slice is a subholor consisting of all entries with initial index i. -/
def slice (x : Holor (d :: ds) α) (i : ℕ) (h : i < d) : Holor ds α := fun is : HolorIndex ds =>
  x ⟨i :: is.1, Forall₂.cons h is.2⟩

/-- The 1-dimensional "unit" holor with 1 in the `j`th position. -/
def unitVec [Monoid α] [AddMonoid α] (d : ℕ) (j : ℕ) : Holor [d] α := fun ti =>
  if ti.1 = [j] then 1 else 0

theorem holor_index_cons_decomp (p : HolorIndex (d :: ds) → Prop) :
    ∀ t : HolorIndex (d :: ds),
      (∀ i is, ∀ h : t.1 = i :: is, p ⟨i :: is, by rw [← h]; exact t.2⟩) → p t
  | ⟨[], hforall₂⟩, _ => absurd (forall₂_nil_left_iff.1 hforall₂) (cons_ne_nil d ds)
  | ⟨i :: is, _⟩, hp => hp i is rfl

/-- Two holors are equal if all their slices are equal. -/
theorem slice_eq (x : Holor (d :: ds) α) (y : Holor (d :: ds) α) (h : slice x = slice y) : x = y :=
  funext fun t : HolorIndex (d :: ds) =>
    holor_index_cons_decomp (fun t => x t = y t) t fun i is hiis =>
      have hiisdds : Forall₂ (· < ·) (i :: is) (d :: ds) := by rw [← hiis]; exact t.2
      have hid : i < d := (forall₂_cons.1 hiisdds).1
      have hisds : Forall₂ (· < ·) is ds := (forall₂_cons.1 hiisdds).2
      calc
        x ⟨i :: is, _⟩ = slice x i hid ⟨is, hisds⟩ := congr(x $(Subtype.ext rfl))
        _ = slice y i hid ⟨is, hisds⟩ := by rw [h]
        _ = y ⟨i :: is, _⟩ := congr(y $(Subtype.ext rfl))

set_option backward.isDefEq.respectTransparency false in
theorem slice_unitVec_mul [Semiring α] {i : ℕ} {j : ℕ} (hid : i < d) (x : Holor ds α) :
    slice (unitVec d j ⊗ x) i hid = if i = j then x else 0 :=
  funext fun t : HolorIndex ds =>
    if h : i = j then by simp [slice, mul, HolorIndex.take, unitVec, HolorIndex.drop, h]
    else by simp [slice, mul, HolorIndex.take, unitVec, HolorIndex.drop, h]; rfl

theorem slice_add [Add α] (i : ℕ) (hid : i < d) (x : Holor (d :: ds) α) (y : Holor (d :: ds) α) :
    slice x i hid + slice y i hid = slice (x + y) i hid :=
  funext fun t => by simp [slice, (· + ·), Add.add]

theorem slice_zero [Zero α] (i : ℕ) (hid : i < d) : slice (0 : Holor (d :: ds) α) i hid = 0 :=
  rfl

theorem slice_sum [AddCommMonoid α] {β : Type} (i : ℕ) (hid : i < d) (s : Finset β)
    (f : β → Holor (d :: ds) α) : (∑ x ∈ s, slice (f x) i hid) = slice (∑ x ∈ s, f x) i hid := by
  let := Classical.decEq β
  refine Finset.induction_on s ?_ ?_
  · simp [slice_zero]
  · intro _ _ h_not_in ih
    rw [Finset.sum_insert h_not_in, ih, slice_add, Finset.sum_insert h_not_in]

/-- The original holor can be recovered from its slices by multiplying with unit vectors and
summing up. -/
@[simp]
theorem sum_unitVec_mul_slice [Semiring α] (x : Holor (d :: ds) α) :
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
inductive CPRankMax1 [Mul α] : ∀ {ds}, Holor ds α → Prop
  | nil (x : Holor [] α) : CPRankMax1 x
  | cons {d : ℕ} {ds : List ℕ} (x : Holor [d] α) (y : Holor ds α) :
    CPRankMax1 y → CPRankMax1 (x ⊗ y)

/-- `CPRankMax N x` means `x` has CP rank at most `N`, that is,
  it can be written as the sum of N holors of rank at most 1. -/
inductive CPRankMax [Mul α] [AddMonoid α] : ℕ → ∀ {ds}, Holor ds α → Prop
  | zero {ds : List ℕ} : CPRankMax 0 (0 : Holor ds α)
  | succ (n : ℕ) {ds : List ℕ} (x : Holor ds α) (y : Holor ds α) :
    CPRankMax1 x → CPRankMax n y → CPRankMax (n + 1) (x + y)

theorem cprankMax_nil [Mul α] [AddMonoid α] (x : Holor nil α) : CPRankMax 1 x := by
  have h := CPRankMax.succ 0 x 0 (CPRankMax1.nil x) CPRankMax.zero
  rwa [add_zero x, zero_add] at h

theorem cprankMax_1 [Mul α] [AddMonoid α] {x : Holor ds α} (h : CPRankMax1 x) :
    CPRankMax 1 x := by
  have h' := CPRankMax.succ 0 x 0 h CPRankMax.zero
  rwa [zero_add, add_zero] at h'

theorem cprankMax_add [Mul α] [AddMonoid α] :
    ∀ {m : ℕ} {n : ℕ} {x : Holor ds α} {y : Holor ds α},
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
    ∀ (n : ℕ) (x : Holor [d] α) (y : Holor ds α), CPRankMax n y → CPRankMax n (x ⊗ y)
  | 0, x, _, CPRankMax.zero => by simp [mul_zero x, CPRankMax.zero]
  | n + 1, x, _, CPRankMax.succ _ y₁ y₂ hy₁ hy₂ => by
    rw [mul_left_distrib]
    rw [Nat.add_comm]
    apply cprankMax_add
    · exact cprankMax_1 (CPRankMax1.cons _ _ hy₁)
    · exact cprankMax_mul _ x y₂ hy₂

theorem cprankMax_sum [NonUnitalNonAssocSemiring α] {β} {n : ℕ} (s : Finset β)
    (f : β → Holor ds α) : (∀ x ∈ s, CPRankMax n (f x)) → CPRankMax (s.card * n) (∑ x ∈ s, f x) :=
  letI := Classical.decEq β
  Finset.induction_on s (by simp [CPRankMax.zero])
    (by
      intro x s (h_x_notin_s : x ∉ s) ih h_cprank
      simp only [Finset.sum_insert h_x_notin_s, Finset.card_insert_of_notMem h_x_notin_s]
      rw [Nat.right_distrib]
      simp only [Nat.one_mul, Nat.add_comm]
      have ih' : CPRankMax (Finset.card s * n) (∑ x ∈ s, f x) := by grind
      exact cprankMax_add (h_cprank x (Finset.mem_insert_self x s)) ih')

theorem cprankMax_upper_bound [Semiring α] : ∀ {ds}, ∀ x : Holor ds α, CPRankMax ds.prod x
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
noncomputable def cprank [Ring α] (x : Holor ds α) : Nat :=
  @Nat.find (fun n => CPRankMax n x) (Classical.decPred _) ⟨ds.prod, cprankMax_upper_bound x⟩

theorem cprank_upper_bound [Ring α] : ∀ {ds}, ∀ x : Holor ds α, cprank x ≤ ds.prod :=
  fun {ds} x =>
  letI := Classical.decPred fun n : ℕ => CPRankMax n x
  Nat.find_min' ⟨ds.prod, show (fun n => CPRankMax n x) ds.prod from cprankMax_upper_bound x⟩
    (cprankMax_upper_bound x)

end Holor
