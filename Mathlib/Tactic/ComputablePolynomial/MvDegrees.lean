/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ring

/-!
# Exponent vectors for computable multivariate polynomials

`MvDegrees nvars` is an exponent vector for a monomial in `nvars` variables: an array of
per-variable exponents together with its cached total degree. This file gives the `AddCommMonoid`
structure (pointwise addition) and the `List`/`Array` folding lemmas the rest of the computable
multivariate polynomial library (`MvSparsePoly`) is built on.

## Provenance

Based on the univariate `SparsePoly`, started by Mario Carneiro at the Hausdorff Institute,
June 2024, with design notes and an original Lean prototype by James Davenport
(https://github.com/JamesHDavenport/Dagstuhl23401, `verify-irred/VerifyIrred`).
-/

@[expose] public section

/-- An exponent vector for a monomial in `nvars` variables: an array of length `nvars` giving each
variable's exponent, together with its (cached) total degree. -/
@[ext] structure MvDegrees (nvars : ℕ) where
  /-- The per-variable exponents, one entry per variable. -/
  degrees : Array ℕ
  /-- The exponent array has exactly `nvars` entries. -/
  correct: degrees.size = nvars
  /-- The cached total degree (the sum of all exponents). -/
  totalDegree : ℕ
  /-- The cached `totalDegree` equals the sum of the exponents. -/
  totalDegree_eq : totalDegree = degrees.foldl (· + ·) 0

/-- Pull the accumulator out of a pure `List.foldl` add loop. -/
lemma list_foldl_add_acc (l : List ℕ) (acc : ℕ) :
    l.foldl (· + ·) acc = acc + l.foldl (· + ·) 0 := by
  induction l generalizing acc with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih (acc + x), ih (0 + x)]; omega

/-- Summing a pointwise list addition splits over the two summands. -/
lemma list_zipWith_foldl_add (la lb : List ℕ) (h : la.length = lb.length) :
    (List.zipWith (· + ·) la lb).foldl (· + ·) 0 =
    la.foldl (· + ·) 0 + lb.foldl (· + ·) 0 := by
  induction la generalizing lb with
  | nil => cases lb with
    | nil => rfl
    | cons y ys => simp at h
  | cons x xs ih =>
    cases lb with
    | nil => simp at h
    | cons y ys =>
      simp only [List.zipWith, List.foldl_cons, List.length_cons, Nat.succ.injEq] at h ⊢
      rw [list_foldl_add_acc (List.zipWith (· + ·) xs ys) (0 + (x + y)), ih ys h,
        list_foldl_add_acc xs (0 + x), list_foldl_add_acc ys (0 + y)]
      omega

/-- Array version of `list_zipWith_foldl_add`. -/
lemma array_zipWith_foldl_add (a b : Array ℕ) (h : a.size = b.size) :
    (Array.zipWith (· + ·) a b).foldl (· + ·) 0 =
    a.foldl (· + ·) 0 + b.foldl (· + ·) 0 := by
  simp only [← Array.foldl_toList, Array.toList_zipWith]
  exact list_zipWith_foldl_add a.toList b.toList h

/-- Folding a list of zeros gives `0`. -/
lemma list_replicate_zero_foldl (n : ℕ) :
    (List.replicate n 0).foldl (· + ·) 0 = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change (0 :: List.replicate k 0).foldl (· + ·) 0 = 0
    rw [List.foldl_cons, list_foldl_add_acc (List.replicate k 0) (0 + 0)]
    omega

/-- Array version of `list_replicate_zero_foldl`. -/
lemma array_replicate_zero_foldl (n : ℕ) :
    ((List.replicate n 0).toArray).foldl (· + ·) 0 = 0 := by
  simp only [← Array.foldl_toList]
  exact list_replicate_zero_foldl n

/-- Scalar multiplication distributes over a `List.foldl` sum. -/
lemma list_map_mul_foldl (l : List ℕ) (n : ℕ) :
    (l.map (· * n)).foldl (· + ·) 0 = l.foldl (· + ·) 0 * n := by
  induction l with
  | nil => grind
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [list_foldl_add_acc (xs.map (· * n)) (0 + x * n), list_foldl_add_acc xs (0 + x), ih,
      Nat.add_mul]
    grind

/-- Array version of `list_map_mul_foldl`. -/
lemma array_map_mul_foldl (a : Array ℕ) (n : ℕ) :
    (a.map (· * n)).foldl (· + ·) 0 = a.foldl (· + ·) 0 * n := by
  simp only [← Array.foldl_toList, Array.toList_map]
  exact list_map_mul_foldl a.toList n

/-- Arrays are equal if their underlying lists are equal. -/
lemma array_eq_of_toList_eq {α} {a b : Array α} (h : a.toList = b.toList) : a = b := by
  cases a; cases b; simp_all

/-- Associativity of pointwise list addition. -/
lemma list_zipWith_add_assoc (a b c : List ℕ) :
  List.zipWith (· + ·) (List.zipWith (· + ·) a b) c =
  List.zipWith (· + ·) a (List.zipWith (· + ·) b c) := by
  induction a generalizing b c with
  | nil => rfl
  | cons x xs ih =>
    cases b with
    | nil => rfl
    | cons y ys =>
      cases c with
      | nil => rfl
      | cons z zs => simp only [List.zipWith]; rw [ih]; grind

/-- Commutativity of pointwise list addition. -/
lemma list_zipWith_add_comm (a b : List ℕ) :
  List.zipWith (· + ·) a b = List.zipWith (· + ·) b a := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih =>
    cases b with
    | nil => rfl
    | cons y ys => simp only [List.zipWith]; rw [ih]; grind

/-- Left identity for pointwise list addition. -/
lemma list_zipWith_zero_add (a : List ℕ) :
  List.zipWith (· + ·) (List.replicate a.length 0) a = a := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    change List.zipWith (· + ·) (0 :: List.replicate xs.length 0) (x :: xs) = x :: xs
    simp only [List.zipWith]; rw [ih]; grind

/-- Right identity for pointwise list addition. -/
lemma list_zipWith_add_zero (a : List ℕ) :
  List.zipWith (· + ·) a (List.replicate a.length 0) = a := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    change List.zipWith (· + ·) (x :: xs) (0 :: List.replicate xs.length 0) = x :: xs
    simp only [List.zipWith]; rw [ih]; grind

lemma list_zipWith_add_right_cancel {la lb lc : List ℕ}
    (h1 : la.length = lc.length) (h2 : lb.length = lc.length)
    (h : List.zipWith (· + ·) la lc = List.zipWith (· + ·) lb lc) : la = lb := by
  induction la generalizing lb lc with
  | nil =>
    cases lc with
    | nil => cases lb with | nil => rfl | cons => simp at h2
    | cons => simp at h1
  | cons a as ih =>
    cases lc with
    | nil => simp at h1
    | cons c cs =>
      cases lb with
      | nil => simp at h2
      | cons b bs =>
        simp only [List.zipWith_cons_cons, List.cons.injEq] at h
        simp only [List.length_cons, Nat.succ.injEq] at h1 h2
        obtain ⟨hab, htail⟩ := h
        rw [show a = b by omega, ih h1 h2 htail]

/-- `map (· * 0)` produces a list of zeros. -/
lemma list_map_zero (a : List ℕ) :
  a.map (· * 0) = List.replicate a.length 0 := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    change (x * 0) :: (xs.map (· * 0)) = 0 :: List.replicate xs.length 0
    rw [ih]; rfl

/-- `nsmul` successor step for pointwise list scalar multiplication. -/
lemma list_nsmul_succ (a : List ℕ) (n : ℕ) :
  a.map (· * (n + 1)) = List.zipWith (· + ·) a (a.map (· * n)) := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp only [List.map, List.zipWith]; rw [ih]; grind

/-- The size of any `MvDegrees` array is exactly `nvars`. -/
@[simp]
lemma MvDegrees.size_eq {nvars : ℕ} (x : MvDegrees nvars) : x.degrees.size = nvars :=
  x.correct

/-- Array version of `list_zipWith_add_assoc`. -/
lemma array_zipWith_add_assoc (a b c : Array ℕ) :
    Array.zipWith (· + ·) (Array.zipWith (· + ·) a b) c =
    Array.zipWith (· + ·) a (Array.zipWith (· + ·) b c) := by
  apply array_eq_of_toList_eq
  simp only [Array.toList_zipWith]
  exact list_zipWith_add_assoc a.toList b.toList c.toList

/-- Array version of `list_zipWith_zero_add`. -/
lemma array_zipWith_zero_add (a : Array ℕ) (nvars : ℕ) (h : a.size = nvars) :
    Array.zipWith (· + ·) (List.replicate nvars 0).toArray a = a := by
  apply array_eq_of_toList_eq
  simp only [Array.toList_zipWith]
  rw [show nvars = a.toList.length from h.symm]
  exact list_zipWith_zero_add a.toList

/-- Array version of `list_zipWith_add_zero`. -/
lemma array_zipWith_add_zero (a : Array ℕ) (nvars : ℕ) (h : a.size = nvars) :
    Array.zipWith (· + ·) a (List.replicate nvars 0).toArray = a := by
  apply array_eq_of_toList_eq
  simp only [Array.toList_zipWith]
  rw [show nvars = a.toList.length from h.symm]
  exact list_zipWith_add_zero a.toList

/-- Array version of `list_zipWith_add_comm`. -/
lemma array_zipWith_add_comm (a b : Array ℕ) :
    Array.zipWith (· + ·) a b = Array.zipWith (· + ·) b a := by
  apply array_eq_of_toList_eq
  simp only [Array.toList_zipWith]
  exact list_zipWith_add_comm a.toList b.toList

/-- Array version of `list_map_zero`. -/
lemma array_map_zero (a : Array ℕ) (nvars : ℕ) (h : a.size = nvars) :
    a.map (· * 0) = (List.replicate nvars 0).toArray := by
  apply array_eq_of_toList_eq
  simp only [Array.toList_map]
  rw [show nvars = a.toList.length from h.symm]
  exact list_map_zero a.toList

/-- `nsmul` successor step for pointwise array scalar multiplication. -/
lemma array_nsmul_succ (a : Array ℕ) (n : ℕ) :
    a.map (· * (n + 1)) = Array.zipWith (· + ·) (a.map (· * n)) a := by
  apply array_eq_of_toList_eq
  simp only [Array.toList_map, Array.toList_zipWith]
  ext i j
  grind

variable {nvars : ℕ}

instance : AddCommMonoid (MvDegrees nvars) where
  add a b := {
    degrees := Array.zipWith (· + ·) a.degrees b.degrees
    correct := by simp [a.correct, b.correct]
    totalDegree := a.totalDegree + b.totalDegree
    totalDegree_eq := by
      rw [a.totalDegree_eq, b.totalDegree_eq]
      have h_size : a.degrees.size = b.degrees.size := by rw [a.correct, b.correct]
      grind [array_zipWith_foldl_add]
  }
  zero := {
    degrees := (List.replicate nvars 0).toArray
    correct := by simp
    totalDegree := 0
    totalDegree_eq := (array_replicate_zero_foldl nvars).symm
  }
  nsmul n a := {
    degrees := Array.map (· * n) a.degrees
    correct := by simp [a.correct]
    totalDegree := a.totalDegree * n
    totalDegree_eq := by rw [a.totalDegree_eq]; exact (array_map_mul_foldl a.degrees n).symm
  }
  add_assoc a b c := by
    apply MvDegrees.ext
    · change Array.zipWith (· + ·) (Array.zipWith (· + ·) a.degrees b.degrees) c.degrees =
             Array.zipWith (· + ·) a.degrees (Array.zipWith (· + ·) b.degrees c.degrees)
      exact array_zipWith_add_assoc a.degrees b.degrees c.degrees
    · change (a.totalDegree + b.totalDegree) + c.totalDegree =
             a.totalDegree + (b.totalDegree + c.totalDegree)
      omega
  zero_add a := by
    apply MvDegrees.ext
    · change Array.zipWith (· + ·) (List.replicate nvars 0).toArray a.degrees = a.degrees
      exact array_zipWith_zero_add a.degrees nvars a.correct
    · change 0 + a.totalDegree = a.totalDegree
      omega
  add_zero a := by
    apply MvDegrees.ext
    · change Array.zipWith (· + ·) a.degrees (List.replicate nvars 0).toArray = a.degrees
      exact array_zipWith_add_zero a.degrees nvars a.correct
    · change a.totalDegree + 0 = a.totalDegree
      omega
  add_comm a b := by
    apply MvDegrees.ext
    · change Array.zipWith (· + ·) a.degrees b.degrees = Array.zipWith (· + ·) b.degrees a.degrees
      exact array_zipWith_add_comm a.degrees b.degrees
    · change a.totalDegree + b.totalDegree = b.totalDegree + a.totalDegree
      omega
  nsmul_zero a := by
    apply MvDegrees.ext
    · change a.degrees.map (· * 0) = (List.replicate nvars 0).toArray
      exact array_map_zero a.degrees nvars a.correct
    · change a.totalDegree * 0 = 0
      omega
  nsmul_succ n a := by
    apply MvDegrees.ext
    · change a.degrees.map (· * (n + 1)) = Array.zipWith (· + ·) (a.degrees.map (· * n)) a.degrees
      exact array_nsmul_succ a.degrees n
    · change a.totalDegree * (n + 1) = a.totalDegree * n + a.totalDegree
      grind
