/-
Copyright (c) 2018 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.BigOperators.Basic

#align_import data.holor from "leanprover-community/mathlib"@"509de852e1de55e1efa8eacfa11df0823f26f226"

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
open BigOperators

/-- `HolorIndex ds` is the type of valid index tuples used to identify an entry of a holor
of dimensions `ds`. -/
def HolorIndex (ds : List ℕ) : Type :=
  { is : List ℕ // Forall₂ (· < ·) is ds }
#align holor_index HolorIndex

namespace HolorIndex

variable {ds₁ ds₂ ds₃ : List ℕ}

def take : ∀ {ds₁ : List ℕ}, HolorIndex (ds₁ ++ ds₂) → HolorIndex ds₁
  | ds, is => ⟨List.take (length ds) is.1, forall₂_take_append is.1 ds ds₂ is.2⟩
#align holor_index.take HolorIndex.take

def drop : ∀ {ds₁ : List ℕ}, HolorIndex (ds₁ ++ ds₂) → HolorIndex ds₂
  | ds, is => ⟨List.drop (length ds) is.1, forall₂_drop_append is.1 ds ds₂ is.2⟩
#align holor_index.drop HolorIndex.drop

theorem cast_type (is : List ℕ) (eq : ds₁ = ds₂) (h : Forall₂ (· < ·) is ds₁) :
    (cast (congr_arg HolorIndex eq) ⟨is, h⟩).val = is := by subst eq; rfl
                                                            -- ⊢ ↑(cast (_ : HolorIndex ds₁ = HolorIndex ds₁) { val := is, property := h }) = …
                                                                      -- 🎉 no goals
#align holor_index.cast_type HolorIndex.cast_type

def assocRight : HolorIndex (ds₁ ++ ds₂ ++ ds₃) → HolorIndex (ds₁ ++ (ds₂ ++ ds₃)) :=
  cast (congr_arg HolorIndex (append_assoc ds₁ ds₂ ds₃))
#align holor_index.assoc_right HolorIndex.assocRight

def assocLeft : HolorIndex (ds₁ ++ (ds₂ ++ ds₃)) → HolorIndex (ds₁ ++ ds₂ ++ ds₃) :=
  cast (congr_arg HolorIndex (append_assoc ds₁ ds₂ ds₃).symm)
#align holor_index.assoc_left HolorIndex.assocLeft

theorem take_take : ∀ t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.take = t.take.take
  | ⟨is, h⟩ =>
    Subtype.eq <| by
      simp [assocRight, take, cast_type, List.take_take, Nat.le_add_right, min_eq_left]
      -- 🎉 no goals
#align holor_index.take_take HolorIndex.take_take

theorem drop_take : ∀ t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.drop.take = t.take.drop
  | ⟨is, h⟩ => Subtype.eq (by simp [assocRight, take, drop, cast_type, List.drop_take])
                              -- 🎉 no goals
#align holor_index.drop_take HolorIndex.drop_take

theorem drop_drop : ∀ t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.drop.drop = t.drop
  | ⟨is, h⟩ => Subtype.eq (by simp [add_comm, assocRight, drop, cast_type, List.drop_drop])
                              -- 🎉 no goals
#align holor_index.drop_drop HolorIndex.drop_drop

end HolorIndex

/-- Holor (indexed collections of tensor coefficients) -/
def Holor (α : Type u) (ds : List ℕ) :=
  HolorIndex ds → α
#align holor Holor

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
-- Porting note: Previous code was:
-- by
-- refine_struct { add := (· + ·).. } <;> pi_instance_derive_field
--
-- `refine_struct` has not been ported yet.

instance [AddCommSemigroup α] : AddCommSemigroup (Holor α ds) := Pi.addCommSemigroup
-- Porting note: Previous code was:
-- by
-- refine_struct { add := (· + ·).. } <;> pi_instance_derive_field
--
-- `refine_struct` has not been ported yet.

instance [AddMonoid α] : AddMonoid (Holor α ds) := Pi.addMonoid
-- Porting note: Previous code was:
-- by
-- refine_struct
--     { zero := (0 : Holor α ds)
--       add := (· + ·)
--       nsmul := fun n x i => n • x i } <;>
--   pi_instance_derive_field
--
-- `refine_struct` has not been ported yet.

instance [AddCommMonoid α] : AddCommMonoid (Holor α ds) := Pi.addCommMonoid
-- Porting note: Previous code was:
-- by
-- refine_struct
--     { zero := (0 : Holor α ds)
--       add := (· + ·)
--       nsmul := AddMonoid.nsmul } <;>
--   pi_instance_derive_field
--
-- `refine_struct` has not been ported yet.

instance [AddGroup α] : AddGroup (Holor α ds) := Pi.addGroup
-- Porting note: Previous code was:
-- by
-- refine_struct
--     { zero := (0 : Holor α ds)
--       add := (· + ·)
--       nsmul := AddMonoid.nsmul
--       zsmul := fun n x i => n • x i } <;>
--   pi_instance_derive_field
--
-- `refine_struct` has not been ported yet.

instance [AddCommGroup α] : AddCommGroup (Holor α ds) := Pi.addCommGroup
-- Porting note: Previous code was:
-- by
-- refine_struct
--     { zero := (0 : Holor α ds)
--       add := (· + ·)
--       nsmul := AddMonoid.nsmul
--       zsmul := SubNegMonoid.zsmul } <;>
--   pi_instance_derive_field
--
-- `refine_struct` has not been ported yet.

-- scalar product
instance [Mul α] : SMul α (Holor α ds) :=
  ⟨fun a x => fun t => a * x t⟩

instance [Semiring α] : Module α (Holor α ds) := Pi.module _ _ _

/-- The tensor product of two holors. -/
def mul [Mul α] (x : Holor α ds₁) (y : Holor α ds₂) : Holor α (ds₁ ++ ds₂) := fun t =>
  x t.take * y t.drop
#align holor.mul Holor.mul

local infixl:70 " ⊗ " => mul

theorem cast_type (eq : ds₁ = ds₂) (a : Holor α ds₁) :
    cast (congr_arg (Holor α) eq) a = fun t => a (cast (congr_arg HolorIndex eq.symm) t) := by
  subst eq; rfl
  -- ⊢ cast (_ : Holor α ds₁ = Holor α ds₁) a = fun t => a (cast (_ : HolorIndex ds …
            -- 🎉 no goals
#align holor.cast_type Holor.cast_type

def assocRight : Holor α (ds₁ ++ ds₂ ++ ds₃) → Holor α (ds₁ ++ (ds₂ ++ ds₃)) :=
  cast (congr_arg (Holor α) (append_assoc ds₁ ds₂ ds₃))
#align holor.assoc_right Holor.assocRight

def assocLeft : Holor α (ds₁ ++ (ds₂ ++ ds₃)) → Holor α (ds₁ ++ ds₂ ++ ds₃) :=
  cast (congr_arg (Holor α) (append_assoc ds₁ ds₂ ds₃).symm)
#align holor.assoc_left Holor.assocLeft

theorem mul_assoc0 [Semigroup α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₃) :
    x ⊗ y ⊗ z = (x ⊗ (y ⊗ z)).assocLeft :=
  funext fun t : HolorIndex (ds₁ ++ ds₂ ++ ds₃) => by
    rw [assocLeft]
    -- ⊢ (x ⊗ y ⊗ z) t = cast (_ : Holor α (ds₁ ++ (ds₂ ++ ds₃)) = Holor α (ds₁ ++ ds …
    unfold mul
    -- ⊢ x (HolorIndex.take (HolorIndex.take t)) * y (HolorIndex.drop (HolorIndex.tak …
    rw [mul_assoc, ←HolorIndex.take_take, ←HolorIndex.drop_take, ←HolorIndex.drop_drop, cast_type]
    -- ⊢ x (HolorIndex.take (HolorIndex.assocRight t)) * (y (HolorIndex.take (HolorIn …
    rfl
    -- ⊢ ds₁ ++ (ds₂ ++ ds₃) = ds₁ ++ ds₂ ++ ds₃
    rw [append_assoc]
    -- 🎉 no goals
#align holor.mul_assoc0 Holor.mul_assoc0

theorem mul_assoc [Semigroup α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₃) :
    HEq (mul (mul x y) z) (mul x (mul y z)) := by simp [cast_heq, mul_assoc0, assocLeft]
                                                  -- 🎉 no goals
#align holor.mul_assoc Holor.mul_assoc

theorem mul_left_distrib [Distrib α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₂) :
    x ⊗ (y + z) = x ⊗ y + x ⊗ z := funext fun t => left_distrib (x t.take) (y t.drop) (z t.drop)
#align holor.mul_left_distrib Holor.mul_left_distrib

theorem mul_right_distrib [Distrib α] (x : Holor α ds₁) (y : Holor α ds₁) (z : Holor α ds₂) :
    (x + y) ⊗ z = x ⊗ z + y ⊗ z := funext fun t => add_mul (x t.take) (y t.take) (z t.drop)
#align holor.mul_right_distrib Holor.mul_right_distrib

@[simp]
nonrec theorem zero_mul {α : Type} [Ring α] (x : Holor α ds₂) : (0 : Holor α ds₁) ⊗ x = 0 :=
  funext fun t => zero_mul (x (HolorIndex.drop t))
#align holor.zero_mul Holor.zero_mul

@[simp]
nonrec theorem mul_zero {α : Type} [Ring α] (x : Holor α ds₁) : x ⊗ (0 : Holor α ds₂) = 0 :=
  funext fun t => mul_zero (x (HolorIndex.take t))
#align holor.mul_zero Holor.mul_zero

theorem mul_scalar_mul [Monoid α] (x : Holor α []) (y : Holor α ds) :
    x ⊗ y = x ⟨[], Forall₂.nil⟩ • y := by
      simp [mul, SMul.smul, HolorIndex.take, HolorIndex.drop, HSMul.hSMul]
      -- 🎉 no goals
#align holor.mul_scalar_mul Holor.mul_scalar_mul

-- holor slices
/-- A slice is a subholor consisting of all entries with initial index i. -/
def slice (x : Holor α (d :: ds)) (i : ℕ) (h : i < d) : Holor α ds := fun is : HolorIndex ds =>
  x ⟨i :: is.1, Forall₂.cons h is.2⟩
#align holor.slice Holor.slice

/-- The 1-dimensional "unit" holor with 1 in the `j`th position. -/
def unitVec [Monoid α] [AddMonoid α] (d : ℕ) (j : ℕ) : Holor α [d] := fun ti =>
  if ti.1 = [j] then 1 else 0
#align holor.unit_vec Holor.unitVec

theorem holor_index_cons_decomp (p : HolorIndex (d :: ds) → Prop) :
    ∀ t : HolorIndex (d :: ds),
      (∀ i is, ∀ h : t.1 = i :: is, p ⟨i :: is, by rw [← h]; exact t.2⟩) → p t
                                                   -- ⊢ Forall₂ (fun x x_1 => x < x_1) (↑t) (d :: ds)
                                                             -- 🎉 no goals
  | ⟨[], hforall₂⟩, _ => absurd (forall₂_nil_left_iff.1 hforall₂) (cons_ne_nil d ds)
  | ⟨i :: is, _⟩, hp => hp i is rfl
#align holor.holor_index_cons_decomp Holor.holor_index_cons_decomp

/-- Two holors are equal if all their slices are equal. -/
theorem slice_eq (x : Holor α (d :: ds)) (y : Holor α (d :: ds)) (h : slice x = slice y) : x = y :=
  funext fun t : HolorIndex (d :: ds) =>
    holor_index_cons_decomp (fun t => x t = y t) t fun i is hiis =>
      have hiisdds : Forall₂ (· < ·) (i :: is) (d :: ds) := by rw [← hiis]; exact t.2
                                                               -- ⊢ Forall₂ (fun x x_1 => x < x_1) (↑t) (d :: ds)
                                                                            -- 🎉 no goals
      have hid : i < d := (forall₂_cons.1 hiisdds).1
      have hisds : Forall₂ (· < ·) is ds := (forall₂_cons.1 hiisdds).2
      calc
        x ⟨i :: is, _⟩ = slice x i hid ⟨is, hisds⟩ := congr_arg (fun t => x t) (Subtype.eq rfl)
        _ = slice y i hid ⟨is, hisds⟩ := by rw [h]
                                            -- 🎉 no goals
        _ = y ⟨i :: is, _⟩ := congr_arg (fun t => y t) (Subtype.eq rfl)
#align holor.slice_eq Holor.slice_eq

theorem slice_unitVec_mul [Ring α] {i : ℕ} {j : ℕ} (hid : i < d) (x : Holor α ds) :
    slice (unitVec d j ⊗ x) i hid = if i = j then x else 0 :=
  funext fun t : HolorIndex ds =>
    if h : i = j then by simp [slice, mul, HolorIndex.take, unitVec, HolorIndex.drop, h]
                         -- 🎉 no goals
    else by simp [slice, mul, HolorIndex.take, unitVec, HolorIndex.drop, h]; rfl
            -- ⊢ 0 = OfNat.ofNat 0 t
                                                                             -- 🎉 no goals
#align holor.slice_unit_vec_mul Holor.slice_unitVec_mul

theorem slice_add [Add α] (i : ℕ) (hid : i < d) (x : Holor α (d :: ds)) (y : Holor α (d :: ds)) :
    slice x i hid + slice y i hid = slice (x + y) i hid :=
  funext fun t => by simp [slice, (· + ·), Add.add]
                     -- 🎉 no goals
#align holor.slice_add Holor.slice_add

theorem slice_zero [Zero α] (i : ℕ) (hid : i < d) : slice (0 : Holor α (d :: ds)) i hid = 0 :=
  rfl
#align holor.slice_zero Holor.slice_zero

theorem slice_sum [AddCommMonoid α] {β : Type} (i : ℕ) (hid : i < d) (s : Finset β)
    (f : β → Holor α (d :: ds)) : (∑ x in s, slice (f x) i hid) = slice (∑ x in s, f x) i hid := by
  letI := Classical.decEq β
  -- ⊢ ∑ x in s, slice (f x) i hid = slice (∑ x in s, f x) i hid
  refine' Finset.induction_on s _ _
  -- ⊢ ∑ x in ∅, slice (f x) i hid = slice (∑ x in ∅, f x) i hid
  · simp [slice_zero]
    -- 🎉 no goals
  · intro _ _ h_not_in ih
    -- ⊢ ∑ x in insert a✝ s✝, slice (f x) i hid = slice (∑ x in insert a✝ s✝, f x) i  …
    rw [Finset.sum_insert h_not_in, ih, slice_add, Finset.sum_insert h_not_in]
    -- 🎉 no goals
#align holor.slice_sum Holor.slice_sum

/-- The original holor can be recovered from its slices by multiplying with unit vectors and
summing up. -/
@[simp]
theorem sum_unitVec_mul_slice [Ring α] (x : Holor α (d :: ds)) :
    (∑ i in (Finset.range d).attach,
        unitVec d i ⊗ slice x i (Nat.succ_le_of_lt (Finset.mem_range.1 i.prop))) =
      x := by
  apply slice_eq _ _ _
  -- ⊢ slice (∑ i in Finset.attach (Finset.range d), unitVec d ↑i ⊗ slice x ↑i (_ : …
  ext i hid
  -- ⊢ slice (∑ i in Finset.attach (Finset.range d), unitVec d ↑i ⊗ slice x ↑i (_ : …
  rw [← slice_sum]
  -- ⊢ ∑ x_1 in Finset.attach (Finset.range d), slice (unitVec d ↑x_1 ⊗ slice x ↑x_ …
  simp only [slice_unitVec_mul hid]
  -- ⊢ (∑ x_1 in Finset.attach (Finset.range d), if i = ↑x_1 then slice x ↑x_1 (_ : …
  rw [Finset.sum_eq_single (Subtype.mk i <| Finset.mem_range.2 hid)]
  · simp
    -- 🎉 no goals
  · intro (b : { x // x ∈ Finset.range d }) (_ : b ∈ (Finset.range d).attach) (hbi : b ≠ ⟨i, _⟩)
    -- ⊢ (if i = ↑b then slice x ↑b (_ : Nat.succ ↑b ≤ d) else 0) = 0
    have hbi' : i ≠ b := by simpa only [Ne.def, Subtype.ext_iff, Subtype.coe_mk] using hbi.symm
    -- ⊢ (if i = ↑b then slice x ↑b (_ : Nat.succ ↑b ≤ d) else 0) = 0
    simp [hbi']
    -- 🎉 no goals
  · intro (hid' : Subtype.mk i _ ∉ Finset.attach (Finset.range d))
    -- ⊢ (if i = ↑{ val := i, property := (_ : i ∈ Finset.range d) } then slice x ↑{  …
    exfalso
    -- ⊢ False
    exact absurd (Finset.mem_attach _ _) hid'
    -- 🎉 no goals
#align holor.sum_unit_vec_mul_slice Holor.sum_unitVec_mul_slice

-- CP rank
/-- `CPRankMax1 x` means `x` has CP rank at most 1, that is,
  it is the tensor product of 1-dimensional holors. -/
inductive CPRankMax1 [Mul α] : ∀ {ds}, Holor α ds → Prop
  | nil (x : Holor α []) : CPRankMax1 x
  | cons {d} {ds} (x : Holor α [d]) (y : Holor α ds) : CPRankMax1 y → CPRankMax1 (x ⊗ y)
#align holor.cprank_max1 Holor.CPRankMax1

/-- `CPRankMax N x` means `x` has CP rank at most `N`, that is,
  it can be written as the sum of N holors of rank at most 1. -/
inductive CPRankMax [Mul α] [AddMonoid α] : ℕ → ∀ {ds}, Holor α ds → Prop
  | zero {ds} : CPRankMax 0 (0 : Holor α ds)
  | succ (n) {ds} (x : Holor α ds) (y : Holor α ds) :
    CPRankMax1 x → CPRankMax n y → CPRankMax (n + 1) (x + y)
#align holor.cprank_max Holor.CPRankMax

theorem cprankMax_nil [Monoid α] [AddMonoid α] (x : Holor α nil) : CPRankMax 1 x := by
  have h := CPRankMax.succ 0 x 0 (CPRankMax1.nil x) CPRankMax.zero
  -- ⊢ CPRankMax 1 x
  rwa [add_zero x, zero_add] at h
  -- 🎉 no goals
#align holor.cprank_max_nil Holor.cprankMax_nil

theorem cprankMax_1 [Monoid α] [AddMonoid α] {x : Holor α ds} (h : CPRankMax1 x) :
  CPRankMax 1 x := by
  have h' := CPRankMax.succ 0 x 0 h CPRankMax.zero
  -- ⊢ CPRankMax 1 x
  rwa [zero_add, add_zero] at h'
  -- 🎉 no goals
#align holor.cprank_max_1 Holor.cprankMax_1

theorem cprankMax_add [Monoid α] [AddMonoid α] :
    ∀ {m : ℕ} {n : ℕ} {x : Holor α ds} {y : Holor α ds},
      CPRankMax m x → CPRankMax n y → CPRankMax (m + n) (x + y)
  | 0, n, x, y, hx, hy => by
    match hx with
    | CPRankMax.zero => simp only [zero_add, hy]
  | m + 1, n, _, y, CPRankMax.succ _ x₁ x₂ hx₁ hx₂, hy => by
    simp only [add_comm, add_assoc]
    -- ⊢ CPRankMax (n + (m + 1)) (x₁ + (x₂ + y))
    apply CPRankMax.succ
    -- ⊢ CPRankMax1 x₁
    · assumption
      -- 🎉 no goals
    · -- Porting note: Single line is added.
      simp only [Nat.add_eq, add_zero, add_comm n m]
      -- ⊢ CPRankMax (m + n) (x₂ + y)
      exact cprankMax_add hx₂ hy
      -- 🎉 no goals
#align holor.cprank_max_add Holor.cprankMax_add

theorem cprankMax_mul [Ring α] :
    ∀ (n : ℕ) (x : Holor α [d]) (y : Holor α ds), CPRankMax n y → CPRankMax n (x ⊗ y)
  | 0, x, _, CPRankMax.zero => by simp [mul_zero x, CPRankMax.zero]
                                  -- 🎉 no goals
  | n + 1, x, _, CPRankMax.succ _ y₁ y₂ hy₁ hy₂ => by
    rw [mul_left_distrib]
    -- ⊢ CPRankMax (n + 1) (x ⊗ y₁ + x ⊗ y₂)
    rw [Nat.add_comm]
    -- ⊢ CPRankMax (1 + n) (x ⊗ y₁ + x ⊗ y₂)
    apply cprankMax_add
    -- ⊢ CPRankMax 1 (x ⊗ y₁)
    · exact cprankMax_1 (CPRankMax1.cons _ _ hy₁)
      -- 🎉 no goals
    · exact cprankMax_mul _ x y₂ hy₂
      -- 🎉 no goals
#align holor.cprank_max_mul Holor.cprankMax_mul

theorem cprankMax_sum [Ring α] {β} {n : ℕ} (s : Finset β) (f : β → Holor α ds) :
    (∀ x ∈ s, CPRankMax n (f x)) → CPRankMax (s.card * n) (∑ x in s, f x) :=
  letI := Classical.decEq β
  Finset.induction_on s (by simp [CPRankMax.zero])
                            -- 🎉 no goals
    (by
      intro x s(h_x_notin_s : x ∉ s)ih h_cprank
      -- ⊢ CPRankMax (Finset.card (insert x s) * n) (∑ x in insert x s, f x)
      simp only [Finset.sum_insert h_x_notin_s, Finset.card_insert_of_not_mem h_x_notin_s]
      -- ⊢ CPRankMax ((Finset.card s + 1) * n) (f x + ∑ x in s, f x)
      rw [Nat.right_distrib]
      -- ⊢ CPRankMax (Finset.card s * n + 1 * n) (f x + ∑ x in s, f x)
      simp only [Nat.one_mul, Nat.add_comm]
      -- ⊢ CPRankMax (n + Finset.card s * n) (f x + ∑ x in s, f x)
      have ih' : CPRankMax (Finset.card s * n) (∑ x in s, f x) := by
        apply ih
        intro (x : β) (h_x_in_s : x ∈ s)
        simp only [h_cprank, Finset.mem_insert_of_mem, h_x_in_s]
      exact cprankMax_add (h_cprank x (Finset.mem_insert_self x s)) ih')
      -- 🎉 no goals
#align holor.cprank_max_sum Holor.cprankMax_sum

theorem cprankMax_upper_bound [Ring α] : ∀ {ds}, ∀ x : Holor α ds, CPRankMax ds.prod x
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
        (∑ i in Finset.attach (Finset.range d),
          unitVec d i.val ⊗ slice x i.val (mem_range.1 i.2)) :=
      cprankMax_sum (Finset.range d).attach _ fun i _ => h_summands i
    have h_cprankMax_sum :
      CPRankMax (Finset.card (Finset.range d) * prod ds)
        (∑ i in Finset.attach (Finset.range d),
          unitVec d i.val ⊗ slice x i.val (mem_range.1 i.2)) := by rwa [Finset.card_attach] at this
    rw [← sum_unitVec_mul_slice x]
    -- ⊢ CPRankMax (prod (d :: ds)) (∑ i in Finset.attach (Finset.range d), unitVec d …
    rw [h_dds_prod]
    -- ⊢ CPRankMax (Finset.card (Finset.range d) * prod ds) (∑ i in Finset.attach (Fi …
    exact h_cprankMax_sum
    -- 🎉 no goals
#align holor.cprank_max_upper_bound Holor.cprankMax_upper_bound

/-- The CP rank of a holor `x`: the smallest N such that
  `x` can be written as the sum of N holors of rank at most 1. -/
noncomputable def cprank [Ring α] (x : Holor α ds) : Nat :=
  @Nat.find (fun n => CPRankMax n x) (Classical.decPred _) ⟨ds.prod, cprankMax_upper_bound x⟩
#align holor.cprank Holor.cprank

theorem cprank_upper_bound [Ring α] : ∀ {ds}, ∀ x : Holor α ds, cprank x ≤ ds.prod :=
  fun {ds} x =>
  letI := Classical.decPred fun n : ℕ => CPRankMax n x
  Nat.find_min' ⟨ds.prod, show (fun n => CPRankMax n x) ds.prod from cprankMax_upper_bound x⟩
    (cprankMax_upper_bound x)
#align holor.cprank_upper_bound Holor.cprank_upper_bound

end Holor
