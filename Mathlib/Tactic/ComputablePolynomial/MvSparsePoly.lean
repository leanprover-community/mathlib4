/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.List.Sort
public import Mathlib.Data.DFinsupp.WellFounded
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ring

/-! # Computable multivariate polynomials (`MvSparsePoly`)

This file provides `MvSparsePoly`, a computational, sparse, distributed representation of
multivariate polynomials over a commutative ring `R` with `DecidableEq R`. The number of
variables `nvars` is fixed, and a polynomial is stored as a list of `(exponent-vector,
coefficient)` pairs (with non-zero coefficients), mirroring Mathlib's `MvPolynomial`. This
representation serves as the backend for the `mv_decide`/`mv_compute` reflection tactic.

## Implementation notes

`DecidableEq R` is required so that zero coefficients can be recognised and dropped, keeping the
term list canonical.

J. Davenport notes that Lean permits the trivial ring (in which `0 = 1`); supporting it here costs
extra case analysis, and one may wish to rethink whether to allow it.

## Provenance

Based on the univariate `SparsePoly`, started by Mario Carneiro at the Hausdorff Institute,
June 2024, with design notes and an original Lean prototype by James Davenport
(https://github.com/JamesHDavenport/Dagstuhl23401, `verify-irred/VerifyIrred`).
-/

set_option linter.style.longFile 1600

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

/-- A monomial ordering on `MvDegrees nvars`: a linear order compatible with the monoid structure
(`0` is the least element, addition is monotone) and well-founded, so it can serve as an admissible
term order for the sparse polynomial arithmetic. -/
@[ext] class WOrdering (nvars : ℕ) extends LinearOrder (MvDegrees nvars) where
  zero_le {x : MvDegrees nvars} : 0 ≤ x
  add_le_add {x y z : MvDegrees nvars} : x ≤ y → x + z ≤ y + z
  wf : WellFounded (fun (a b : MvDegrees nvars) => a < b)

/-- Pure-list functional definition of lexicographic order. -/
def listLex : List ℕ → List ℕ → Bool
| [], _ => true
| _, [] => true
| (x::xs), (y::ys) =>
  if x < y then true
  else if y < x then false
  else listLex xs ys

/-- Lexicographic order on lists is total. -/
lemma list_lex_total (l1 l2 : List ℕ) : listLex l1 l2 = true ∨ listLex l2 l1 = true := by
  induction l1 generalizing l2 with
  | nil => simp [listLex]
  | cons x xs ih =>
    cases l2 with
    | nil => simp [listLex]
    | cons y ys =>
      unfold listLex
      rcases Nat.lt_trichotomy x y with hlt | heq | hgt
      · simp [hlt, show ¬(y < x) by omega]
      · subst heq; simp; grind
      · simp [show ¬(x < y) by omega, hgt]

/-- The per-step state machine for the lexicographic `forIn` loop. -/
def lexStep (p : ℕ × ℕ) (_acc : Bool) : ForInStep Bool :=
  if p.1 < p.2 then ForInStep.done true
  else if p.1 > p.2 then ForInStep.done false
  else ForInStep.yield true

/-- Bridge the array `forIn` loop to the list one. -/
lemma array_forIn_eq_list_forIn (a b : Array ℕ) :
    Id.run (ForIn.forIn (a.zip b) true lexStep) =
    Id.run (ForIn.forIn (a.toList.zip b.toList) true lexStep) := by
  grind [Array.toList_zip]

/-- The executable implementation of `lexorder`, kept as the compiled engine. -/
def lexorderImpl (a b : MvDegrees nvars) : Bool := Id.run do
  for ai in a.degrees, bi in b.degrees do
     if ai < bi then return true
     else if ai > bi then return false
  return true

/-- Lexicographic comparison of `MvDegrees`, evaluated via `listLex` but run via
`lexorderImpl`. -/
@[implemented_by lexorderImpl]
def lexorder (a b : MvDegrees nvars) : Bool :=
  listLex a.degrees.toList b.degrees.toList

/-- Antisymmetry of lexicographic order on lists. -/
lemma list_lex_antisymm {l1 l2 : List ℕ} (hlen : l1.length = l2.length)
    (h1 : listLex l1 l2 = true) (h2 : listLex l2 l1 = true) : l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp_all
  | cons x xs ih =>
    cases l2 with
    | nil => simp at hlen
    | cons y ys =>
      unfold listLex at h1 h2
      split_ifs at h1 h2 <;> try omega
      obtain rfl : x = y := by omega
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [ih hlen h1 h2]

/-- `lexorder` agrees with `listLex` on the underlying lists. -/
lemma lexorder_eq_list_lex (a b : MvDegrees nvars) :
    lexorder a b = listLex a.degrees.toList b.degrees.toList := rfl

/-- Transitivity of lexicographic order on lists. -/
lemma list_lex_trans {l1 l2 l3 : List ℕ} (h12 : l1.length = l2.length) (h23 : l2.length = l3.length)
    (h1 : listLex l1 l2 = true) (h2 : listLex l2 l3 = true) : listLex l1 l3 = true := by
  induction l1 generalizing l2 l3 with
  | nil => rfl
  | cons x xs ih =>
    cases l2 with | nil => simp at h12 | cons y ys =>
    cases l3 with | nil => simp at h23 | cons z zs =>
      unfold listLex at h1 h2 ⊢
      split_ifs at h1 h2 ⊢ <;> try omega
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h12 h23
      exact ih h12 h23 h1 h2

/-- The zero list is lexicographically below any list of the same length. -/
lemma list_lex_zero_le (l : List ℕ) : listLex (List.replicate l.length 0) l = true := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    change listLex (0 :: List.replicate xs.length 0) (x :: xs) = true
    unfold listLex
    split_ifs <;> try omega
    grind

/-- Lexicographic order is preserved by pointwise addition of a common list. -/
lemma list_lex_add_le_add (la lb lc : List ℕ) (h1 : la.length = lb.length)
    (h2 : lb.length = lc.length) (hab : listLex la lb = true) :
    listLex (List.zipWith (· + ·) la lc) (List.zipWith (· + ·) lb lc) = true := by
  induction la generalizing lb lc with
  | nil => rfl
  | cons x xs ih =>
    cases lb with | nil => simp at h1 | cons y ys =>
    cases lc with | nil => simp at h2 | cons z zs =>
      unfold listLex at hab ⊢
      simp only [List.zipWith]
      split_ifs at hab ⊢ <;> try omega
      simp at h1 h2
      grind

/-- Totality of `lexorder`. -/
theorem lexorder_total (a b : MvDegrees nvars) : lexorder a b = true ∨ lexorder b a = true :=
  list_lex_total a.degrees.toList b.degrees.toList

/-- Antisymmetry of `lexorder`. -/
lemma lexorder_antisymm (a b : MvDegrees nvars) (hab : lexorder a b = true)
    (hba : lexorder b a = true) : a = b := by
  have h1 : a.degrees.toList.length = b.degrees.toList.length := by aesop
  have hlist := list_lex_antisymm h1 hab hba
  apply MvDegrees.ext
  · exact array_eq_of_toList_eq hlist
  · rw [a.totalDegree_eq, b.totalDegree_eq, array_eq_of_toList_eq hlist]

/-- The strict lexicographic order is witnessed by the first differing coordinate. -/
lemma list_lex_strict_first_diff : ∀ {l1 l2 : List ℕ}, l1.length = l2.length →
    listLex l1 l2 = true → ¬ (listLex l2 l1 = true) →
    ∃ n, n < l1.length ∧ (∀ m, m < n → l1[m]! = l2[m]!) ∧ l1[n]! < l2[n]! := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 hlen h1 h2
    cases l2 with
    | nil => exact absurd rfl h2
    | cons y ys => simp at hlen
  | cons x xs ih =>
    intro l2 hlen h1 h2
    cases l2 with
    | nil => simp at hlen
    | cons y ys =>
      have hlen' : xs.length = ys.length := by simpa using hlen
      simp only [listLex] at h1 h2
      rcases lt_trichotomy x y with hxy | hxy | hxy
      · exact ⟨0, by simp, fun m hm => absurd hm (by omega), by simpa using hxy⟩
      · subst hxy
        simp only [lt_self_iff_false, if_false] at h1 h2
        obtain ⟨n, hn, heq, hlt⟩ := ih hlen' h1 h2
        refine ⟨n + 1, by simpa using hn, fun m hm => ?_, by simpa using hlt⟩
        cases m with
        | zero => rfl
        | succ k => simpa using heq k (by omega)
      · exfalso
        rw [if_neg (asymm hxy), if_pos hxy] at h1
        exact absurd h1 (by simp)

/-- Bridge `toList[k]!` to the bounded array access. -/
private lemma mvDegrees_getElem!_toList (d : MvDegrees nvars) (k : ℕ) (hk : k < nvars) :
    d.degrees.toList[k]! = d.degrees[k]'(by rw [d.correct]; exact hk) := by
  rw [getElem!_pos d.degrees.toList k (by rw [Array.length_toList, d.correct]; exact hk)]
  exact (Array.getElem_toList ..).symm

/-- Well-foundedness of the lexicographic monomial order, via `Pi.Lex.wellFounded` on
`Fin nvars → ℕ` (a finite index ordering each well-founded `ℕ`). -/
lemma mvDegrees_lex_wf :
    WellFounded (fun a b : MvDegrees nvars => lexorder a b = true ∧ ¬ (lexorder b a = true)) := by
  let f : MvDegrees nvars → (Fin nvars → ℕ) :=
    fun d k => d.degrees[(k : ℕ)]'(by rw [d.correct]; exact k.2)
  have hpi := Pi.Lex.wellFounded (α := fun _ : Fin nvars => ℕ) (· < ·)
    (fun _ => wellFounded_lt)
  refine Subrelation.wf ?_ (InvImage.wf f hpi)
  intro a b hab
  obtain ⟨hab1, hab2⟩ := hab
  change listLex a.degrees.toList b.degrees.toList = true at hab1
  change ¬ (listLex b.degrees.toList a.degrees.toList = true) at hab2
  have hlen : a.degrees.toList.length = b.degrees.toList.length := by
    rw [Array.length_toList, Array.length_toList, a.correct, b.correct]
  obtain ⟨n, hn, heq, hlt⟩ := list_lex_strict_first_diff hlen hab1 hab2
  have hn' : n < nvars := by rwa [Array.length_toList, a.correct] at hn
  refine ⟨⟨n, hn'⟩, fun j hj => ?_, ?_⟩
  · have hjn : (j : ℕ) < n := hj
    have hh := heq (j : ℕ) hjn
    rwa [mvDegrees_getElem!_toList a (j : ℕ) (lt_trans hjn hn'),
      mvDegrees_getElem!_toList b (j : ℕ) (lt_trans hjn hn')] at hh
  · have hh := hlt
    rwa [mvDegrees_getElem!_toList a n hn', mvDegrees_getElem!_toList b n hn'] at hh

instance : WOrdering nvars where
  le a b := lexorder a b
  le_refl a := or_self_iff.1 (lexorder_total _ _)

  le_trans a b c hab hbc := by
    change listLex a.degrees.toList b.degrees.toList = true at hab
    change listLex b.degrees.toList c.degrees.toList = true at hbc
    change listLex a.degrees.toList c.degrees.toList = true
    have h1 : a.degrees.toList.length = b.degrees.toList.length := by aesop
    have h2 : b.degrees.toList.length = c.degrees.toList.length := by aesop
    exact list_lex_trans h1 h2 hab hbc

  le_antisymm a b hab hba := by
    have h1 : a.degrees.toList.length = b.degrees.toList.length := by aesop
    change listLex a.degrees.toList b.degrees.toList = true at hab
    change listLex b.degrees.toList a.degrees.toList = true at hba
    have hlist := list_lex_antisymm h1 hab hba
    apply MvDegrees.ext
    · exact array_eq_of_toList_eq hlist
    · rw [a.totalDegree_eq, b.totalDegree_eq, array_eq_of_toList_eq hlist]
  min a b := if lexorder a b = true then a else b
  max a b := if lexorder a b = true then b else a
  compare a b :=
    if lexorder a b = true ∧ ¬(lexorder b a = true) then .lt
    else if lexorder a b = true then .eq
    else .gt

  le_total := lexorder_total
  toDecidableLE := fun a b => inferInstanceAs (Decidable (lexorder a b = true))
  compare_eq_compareOfLessAndEq a b := by
    have h_anti := lexorder_antisymm a b
    dsimp [compare, compareOfLessAndEq]
    split_ifs
    · rfl
    · subst ‹a = b›
      have h_refl : lexorder a a = true := by rcases lexorder_total a a with h | h <;> exact h
      grind
    · have heq := h_anti ‹lexorder a b = true› (by tauto)
      contradiction
    · subst ‹a = b›
      have h_refl : lexorder a a = true := by rcases lexorder_total a a with h | h <;> exact h
      contradiction
    · rfl
  zero_le {a} := by
    change listLex (List.replicate nvars 0) (a : MvDegrees nvars).degrees.toList = true
    have h : nvars = (a : MvDegrees nvars).degrees.toList.length := by aesop
    grind [list_lex_zero_le (a : MvDegrees nvars).degrees.toList]
  add_le_add {a b c} hab := by
    change listLex a.degrees.toList b.degrees.toList = true at hab
    change listLex (Array.zipWith (· + ·) a.degrees c.degrees).toList
      (Array.zipWith (· + ·) b.degrees c.degrees).toList = true
    simp only [Array.toList_zipWith]
    have h1 : a.degrees.toList.length = b.degrees.toList.length := by aesop
    have h2 : b.degrees.toList.length = c.degrees.toList.length := by aesop
    exact list_lex_add_le_add a.degrees.toList b.degrees.toList c.degrees.toList h1 h2 hab
  wf := mvDegrees_lex_wf

/-- A computable sparse multivariate polynomial over `R` in `nvars` variables: the list of its
`(exponent-vector, coefficient)` terms, kept strictly decreasing in the monomial order and with all
coefficients non-zero, giving a canonical normal form. -/
@[ext] structure MvSparsePoly (R : Type) [CommRing R] (nvars : ℕ)
    [WOrdering nvars] : Type where
  /-- The list of `(exponent-vector, coefficient)` terms making up the polynomial. -/
  terms : List (MvDegrees nvars × R)
  /-- The terms are strictly decreasing in the monomial order (so degrees are distinct). -/
  sorted : terms.Pairwise (·.1 > ·.1)
  /-- Every stored coefficient is non-zero. -/
  nonzero : ∀ x ∈ terms, x.2 ≠ 0

namespace MvSparsePoly

open MvPolynomial

variable {R : Type} [CommRing R] [DecidableEq R]

/-- Build a polynomial from a sorted term list, dropping zero coefficients. -/
def ofSortedList
    (terms : List (MvDegrees nvars × R)) (sorted : terms.Pairwise (·.1 > ·.1)) :
    MvSparsePoly R nvars where
  terms := terms.filter (·.2 ≠ 0)
  sorted := sorted.sublist List.filter_sublist
  nonzero := by simp [List.mem_filter]

instance : Zero (MvSparsePoly R nvars) where
  zero := { terms := [], sorted := .nil, nonzero := nofun }

/-- The constant polynomial. `ofSortedList` handles `r = 0` (where `0` is the zero of the
`MvDegrees` monoid). -/
def C (r : R) : MvSparsePoly R nvars := ofSortedList [(0, r)] (by simp)

instance : One (MvSparsePoly R nvars) where
  one := C 1

/-- All exponents in a term list are strictly below `a`. -/
def degLt (a : MvDegrees nvars) (l : List (MvDegrees nvars × R)) : Prop :=
  ∀ x ∈ l, x.1 < a

/-- The `Finsupp` underlying an `MvDegrees`, bridging to Mathlib's `MvPolynomial`. -/
noncomputable def MvDegrees.toFinsupp (deg : MvDegrees nvars) : Fin nvars →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun i => deg.degrees[i]'(by simp [deg.correct, i.2])) (by simp)

/-- Interpret a raw term list as an honest `MvPolynomial`, by summing the monomials
`monomial (toFinsupp i) a` over the terms. This is the noncomputable semantics against which the
computable operations are proved correct. -/
noncomputable def toPolyCore : List (MvDegrees nvars × R) → MvPolynomial (Fin nvars) R
  | [] => 0
  | (i, a) :: x => monomial (MvDegrees.toFinsupp i) a + toPolyCore x

/-- Interpret an `MvSparsePoly` as the corresponding Mathlib `MvPolynomial`, via `toPolyCore` on its
term list. -/
noncomputable def toPoly (x : MvSparsePoly R nvars) : MvPolynomial (Fin nvars) R :=
  toPolyCore x.terms

/-- Add two sorted term lists by a single merge pass: at each step keep the larger-degree head,
and on equal degrees add the coefficients (dropping the term if the sum is zero). Preserves the
strictly-decreasing sortedness. -/
def addCore : List (MvDegrees nvars × R) → List (MvDegrees nvars × R) → List (MvDegrees nvars × R)
  | [], yy => yy
  | xx, [] => xx
  | xx@((i, a) :: x), yy@((j, b) :: y) =>
    if i < j then
      (j, b) :: addCore xx y
    else if j < i then
      (i, a) :: addCore x yy
    else
      ( fun c => if c=0 then addCore x y else (i, c) :: addCore x y) (a+b)
    termination_by xx yy => xx.length + yy.length

/-- `addCore` preserves the `degLt` bound. -/
theorem addCore_degLt {n : MvDegrees nvars} : ∀ {x y : List (MvDegrees nvars × R)},
    degLt n x → degLt n y → degLt n (addCore x y) := by
  intro x y hx hy
  unfold addCore
  split
  · exact hy
  · exact hx
  · next i a x' j b y' =>
    let ⟨hi, hx'⟩ := List.forall_mem_cons.1 hx
    let ⟨hj, hy'⟩ := List.forall_mem_cons.1 hy
    split
    · next ij =>
      unfold degLt
      intro x hx_mem
      cases hx_mem with
      | head => exact hj
      | tail h => exact addCore_degLt hx hy' x (by aesop)
    split
    · next ji =>
      unfold degLt
      intro x hx_mem
      cases hx_mem with
      | head => exact hi
      | tail h => exact addCore_degLt hx' hy x (by aesop)
    · next h_not_ij h_not_ji =>
      dsimp only
      split
      · exact addCore_degLt hx' hy'
      · unfold degLt
        intro x hx_mem
        cases hx_mem with
        | head => exact hi
        | tail h => exact addCore_degLt hx' hy' x (by aesop)
termination_by x y => x.length + y.length

theorem addCore_sorted : ∀ {x y : List (MvDegrees nvars × R)},
    x.Pairwise (·.1 > ·.1) → y.Pairwise (·.1 > ·.1) →
    (addCore x y).Pairwise (·.1 > ·.1) := by
  intro x y hx hy
  unfold addCore
  split
  · exact hy
  · exact hx
  · next i a x j b y =>
    let .cons hi hx' := hx
    let .cons hj hy' := hy
    split
    · next ij =>
      constructor
      · apply addCore_degLt
        · intro
          | _, .head _ => exact ij
          | p, .tail _ hp => exact (hi _ hp).trans ij
        · exact hj
      · exact addCore_sorted hx hy'
    split
    · next ji =>
      constructor
      · apply addCore_degLt
        · exact hi
        · intro
          | _, .head _ => exact ji
          | p, .tail _ hp => exact (hj _ hp).trans ji
      · exact addCore_sorted hx' hy
    · have eq_ij : i = j := by
        rcases lt_trichotomy i j with hlt | heq | hgt
        · contradiction
        · exact heq
        · contradiction
      subst eq_ij
      dsimp only
      split
      · exact addCore_sorted hx' hy'
      · exact .cons (addCore_degLt hi hj) (addCore_sorted hx' hy')
termination_by x y => x.length + y.length

instance : Add (MvSparsePoly R nvars) where
  add x y := ofSortedList (addCore x.terms y.terms) (addCore_sorted x.sorted y.sorted)

/-- Merge adjacent equal-degree terms, summing coefficients. -/
def dedupList : List (MvDegrees nvars × R) → List (MvDegrees nvars × R)
  | (i, a) :: (j, b) :: x =>
    if i = j then
      dedupList ((i, a + b) :: x)
    else
      (i, a) :: dedupList ((j, b) :: x)
  | x => x

omit [DecidableEq R] in
lemma dedupList_bound : ∀ (terms : List (MvDegrees nvars × R)) (k : MvDegrees nvars),
    (∀ p ∈ terms, k ≥ p.1) → ∀ p ∈ dedupList terms, k ≥ p.1
  | [], k, h => by
    simp [dedupList]
  | [(i, a)], k, h => by
    intro x hx
    rw [show dedupList [(i, a)] = [(i, a)] by unfold dedupList; rfl] at hx
    exact h x hx
  | (i, a) :: (j, b) :: x, k, h => by
    unfold dedupList
    split
    · next heq =>
      apply dedupList_bound ((i, a + b) :: x) k
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp_in_x
      · exact h (i, a) (by simp)
      · exact h p (by simp [hp_in_x])
    · next hneq =>
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp_in_dedup
      · exact h (i, a) (by simp)
      · apply dedupList_bound ((j, b) :: x) k _ p hp_in_dedup
        intro p' hp'
        exact h p' (by simp [hp'])
termination_by terms => terms.length

omit [DecidableEq R] in
lemma dedupList_sorted_aux : ∀ (terms : List (MvDegrees nvars × R)),
    terms.Pairwise (fun p1 p2 => p2.1 ≤ p1.1) →
    (dedupList terms).Pairwise (fun p1 p2 => p2.1 < p1.1)
  | [] => fun _ => by unfold dedupList; constructor
  | [(i, a)] => fun _ => by
    rw [show dedupList [(i, a)] = [(i, a)] by unfold dedupList; rfl]
    constructor <;> grind
  | (i, a) :: (j, b) :: x => fun h => by
    unfold dedupList
    split
    · next heq =>
      have h_next : ((i, a + b) :: x).Pairwise (fun p1 p2 => p2.1 ≤ p1.1) := by
        simp only [List.pairwise_cons] at h ⊢
        rcases h with ⟨hi, hj_x⟩
        exact ⟨fun p hp => hi p (List.mem_cons_of_mem _ hp), by grind⟩
      exact dedupList_sorted_aux ((i, a + b) :: x) h_next
    · next hneq =>
      have ih := dedupList_sorted_aux ((j, b) :: x) h.of_cons
      simp only [List.pairwise_cons] at h ⊢
      rcases h with ⟨hi, hj_x⟩
      refine ⟨fun p hp => ?_, ih⟩
      have hj_bound : ∀ p' ∈ ((j, b) :: x), p'.1 ≤ j := by
        intro p' hp'
        simp only [List.mem_cons] at hp'
        rcases hp' with rfl | hp_x
        · exact le_rfl
        · exact hj_x.1 p' hp_x
      have hp_le_j : p.1 ≤ j := dedupList_bound ((j, b) :: x) j hj_bound p hp
      have j_lt_i : j < i := lt_of_le_of_ne (hi (j, b) List.mem_cons_self) (Ne.symm hneq)
      exact lt_of_le_of_lt hp_le_j j_lt_i
termination_by terms => terms.length

omit [DecidableEq R] in
theorem dedupList_sorted (terms : List (MvDegrees nvars × R))
  (sorted : terms.Pairwise (·.1 ≥ ·.1)) :
  (dedupList terms).Pairwise (·.1 > ·.1) := dedupList_sorted_aux terms sorted

/-- Sort an arbitrary term list and merge duplicate degrees into a canonical polynomial. -/
def ofList (terms : List (MvDegrees nvars × R)) : MvSparsePoly R nvars :=
  let terms' := terms.mergeSort (fun a b => decide (b.1 ≤ a.1))
  have hSorted : terms'.Pairwise (·.1 ≥ ·.1) := by
    apply List.Pairwise.imp (R := fun a b => decide (b.1 ≤ a.1) = true)
    · intro a b h
      change b.1 ≤ a.1
      exact of_decide_eq_true h
    · apply List.pairwise_mergeSort
      · exact fun a b c hab hbc =>
          decide_eq_true (le_trans (of_decide_eq_true hbc) (of_decide_eq_true hab))
      · intro a b
        rcases le_total b.1 a.1 with h1 | h2
        · simp only [decide_eq_true h1, Bool.true_or]
        · simp only [decide_eq_true h2, Bool.or_true]
  ofSortedList (dedupList terms') (dedupList_sorted terms' hSorted)

/-- Summing a list of zeros with exactly one entry set to `1` gives `1`. -/
lemma list_set_one_zero_foldl : ∀ (n : ℕ) (i : ℕ) (_h : i < n),
    ((List.replicate n 0).set i 1).foldl (· + ·) 0 = 1
  | 0, i, h => by omega
  | n + 1, 0, h => by
    change (1 :: List.replicate n 0).foldl (· + ·) 0 = 1
    rw [List.foldl_cons, list_foldl_add_acc (List.replicate n 0) (0 + 1),
      list_replicate_zero_foldl n]
  | n + 1, i + 1, h => by
    change (0 :: (List.replicate n 0).set i 1).foldl (· + ·) 0 = 1
    rw [List.foldl_cons]
    change ((List.replicate n 0).set i 1).foldl (· + ·) 0 = 1
    exact list_set_one_zero_foldl n i (by omega)


/-- The exponent vector of the single variable `v`: exponent `1` in position `v` and `0` elsewhere
(total degree `1`). -/
def singleDegree (v : Fin nvars) : MvDegrees nvars := {
  degrees := ((List.replicate nvars 0).set v.val 1).toArray
  correct := by simp
  totalDegree := 1
  totalDegree_eq := by
    symm
    simp only [← Array.foldl_toList]
    change ((List.replicate nvars 0).set v.val 1).foldl (· + ·) 0 = 1
    exact list_set_one_zero_foldl nvars v.val v.isLt
}

/-- The polynomial consisting of the single variable `v`. -/
def X (v : Fin nvars) : MvSparsePoly R nvars :=
  ofSortedList [(singleDegree v, 1)] (List.pairwise_singleton _ _)

/-- Exponent addition is right-cancellative (proved on the underlying arrays). -/
lemma mvDegrees_add_right_cancel {a b c : MvDegrees nvars} (h : a + c = b + c) : a = b := by
  have hd : a.degrees = b.degrees := by
    apply array_eq_of_toList_eq
    apply list_zipWith_add_right_cancel (lc := c.degrees.toList)
    · simp [a.correct, c.correct]
    · simp [b.correct, c.correct]
    · show List.zipWith (· + ·) a.degrees.toList c.degrees.toList
        = List.zipWith (· + ·) b.degrees.toList c.degrees.toList
      rw [← Array.toList_zipWith, ← Array.toList_zipWith]
      change (a + c).degrees.toList = (b + c).degrees.toList
      rw [h]
  obtain ⟨ad, hac, at_, hae⟩ := a
  obtain ⟨bd, hbc, bt, hbe⟩ := b
  subst hd
  simp only [MvDegrees.mk.injEq, true_and]
  rw [hae, hbe]

/-- Addition by a fixed exponent is strictly monotone in the monomial order. -/
lemma mvDegrees_add_lt_add_left {i j₁ j₂ : MvDegrees nvars} (h : j₂ < j₁) : i + j₂ < i + j₁ := by
  rw [add_comm i j₂, add_comm i j₁]
  refine lt_of_le_of_ne (WOrdering.add_le_add (le_of_lt h)) ?_
  intro he
  exact (ne_of_lt h) (mvDegrees_add_right_cancel he)

omit [DecidableEq R] in
lemma monomialMul_sorted (i : MvDegrees nvars) (a : R) (y : MvSparsePoly R nvars) :
    (y.terms.map (fun t => (i + t.1, a * t.2))).Pairwise (·.1 > ·.1) :=
  List.Pairwise.map _ (fun _ _ hpq => mvDegrees_add_lt_add_left hpq) y.sorted

/-- `monomialMul i a y = (a · Xⁱ) * y`, computed directly (no re-sort, since the result is
already sorted). The building block of the fast Johnson/Monagan–Pearce multiplication. -/
def monomialMul (i : MvDegrees nvars) (a : R) (y : MvSparsePoly R nvars) : MvSparsePoly R nvars :=
  ofSortedList (y.terms.map (fun t => (i + t.1, a * t.2))) (monomialMul_sorted i a y)

/-- Fuel-recursive worker for `balancedSum`: split the list in half and recurse, summing the two
halves. -/
def balancedSumGo : ℕ → List (MvSparsePoly R nvars) → MvSparsePoly R nvars
  | _, [] => 0
  | _, [p] => p
  | 0, l => l.foldl (· + ·) 0
  | fuel + 1, l => balancedSumGo fuel (l.take (l.length / 2)) +
    balancedSumGo fuel (l.drop (l.length / 2))

/-- Sum a list of polynomials by a balanced (divide-and-conquer) merge tree, so building an
`n`-term result costs `O(n log #summands)` merges instead of the `O(n · #summands)` of a left
fold. -/
def balancedSum (l : List (MvSparsePoly R nvars)) : MvSparsePoly R nvars :=
  balancedSumGo l.length l

/-- Fast multiplication by a **balanced merge** (mergesort tree): multiply `y` by each term of `x`
(each product `monomialMul tᵢ y` is already sorted), then merge the `#x` sorted rows pairwise in a
balanced tree. Same result as the reference `mulCore` (each polynomial has a unique sorted normal
form), but `O(#x · #y · log #x)` *time* instead of generating all `#x·#y` products and sorting
them.

Relation to Davenport's notes (Ch. 2, "What are polynomials?"): he notes the sorted approach is
`O(mn log m)`, and that "naïve construction of all the terms followed by sorting would take `O(mn)`
space ... we can do better with heapsort [Joh74]". This `balancedSum` achieves the *time* bound but
NOT the space bound — it still materialises all `#x` rows (so peak `O(#x·#y)`). A true Johnson heap
of size `#x` would stream the output in `O(#x)` working space. For multiplication the rows have
equal size `#y`, so the balanced merge is efficient (unlike the division case — see the note on
`normalForm`); the only thing a real heap would buy here is peak memory, so we keep the simpler,
verifiable merge. -/
def mulFast (x y : MvSparsePoly R nvars) : MvSparsePoly R nvars :=
  balancedSum (x.terms.map (fun t => monomialMul t.1 t.2 y))

/-- Runtime-only **packed** multiplication — the Davenport / Monagan–Pearce exponent-packing trick.

`mulFast` represents each monomial as an `Array ℕ`, so every one of the `#x·#y` partial products
allocates a fresh boxed-`Nat` array and every merge comparison walks an array. When the product's
exponents are small enough that each variable fits in a `b`-bit field with `nvars·b ≤ 64`, we
instead encode a whole monomial as a single `UInt64` (variable `0` in the most-significant field).
Then:

* the monomial order is plain `UInt64` comparison (`lexorder` is lex with var `0` most significant),
* monomial multiplication `i + j` is a single `UInt64` add (fields can't carry, since each field sum
  `≤ 2·maxDeg < 2^b`).

So the whole `#x·#y` inner loop runs on unboxed machine words; we merge/dedup in packed space and
only unpack the `≤ #product` survivors back to `MvDegrees`. When the exponents don't fit in 64 bits
(or `nvars = 0`) we fall back to `mulFast`. This is the *time*-constant-factor win Davenport's notes
point at (Ch. 2, exponent encoding); same result as `mulCore` (wired via `@[implemented_by]`), and
cross-checked against `mulFast`/`mulCore` by `#guard`. -/
def mulPacked (x y : MvSparsePoly R nvars) : MvSparsePoly R nvars :=
  if nvars = 0 then mulFast x y else
  Id.run do
    let mut maxDeg : ℕ := 0
    for t in x.terms do
      for e in t.1.degrees do
        if e > maxDeg then maxDeg := e
    for t in y.terms do
      for e in t.1.degrees do
        if e > maxDeg then maxDeg := e
    let fieldBound : ℕ := 2 * maxDeg + 1
    let b : ℕ := Nat.log2 fieldBound + 1
    if nvars * b > 64 then
      return mulFast x y
    let bb : UInt64 := b.toUInt64
    let mask : UInt64 := (1 <<< bb) - 1
    let pack : MvDegrees nvars → UInt64 := fun d => Id.run do
      let mut k : UInt64 := 0
      for e in d.degrees do
        k := (k <<< bb) ||| (e.toUInt64 &&& mask)
      return k
    let unpack : UInt64 → MvDegrees nvars := fun k =>
      let degs : Array ℕ := Array.ofFn (n := nvars) (fun j : Fin nvars =>
        ((k >>> (((nvars - 1 - j.val) * b).toUInt64)) &&& mask).toNat)
      { degrees := degs, correct := by simp [degs], totalDegree := degs.foldl (· + ·) 0,
        totalDegree_eq := rfl }
    let yk : Array (UInt64 × R) := (y.terms.map (fun t => (pack t.1, t.2))).toArray
    let mut prods : Array (UInt64 × R) := Array.mkEmpty (x.terms.length * yk.size)
    for t in x.terms do
      let xkey := pack t.1
      let xc := t.2
      for p in yk do
        prods := prods.push (xkey + p.1, xc * p.2)
    let sorted := prods.qsort (fun a c => decide (c.1 < a.1))
    let mut merged : Array (UInt64 × R) := Array.mkEmpty sorted.size
    for p in sorted do
      match merged.back? with
      | some q => if q.1 == p.1 then merged := merged.set! (merged.size - 1) (p.1, q.2 + p.2)
                  else merged := merged.push p
      | none => merged := merged.push p
    let mut out : List (MvDegrees nvars × R) := []
    for p in merged do
      if p.2 ≠ 0 then out := (unpack p.1, p.2) :: out
    return ofList out

/-- Reference multiplication: generate every product term, then sort/dedup/filter via `ofList`.
The proofs use this; compiled code uses the equivalent `mulPacked` via `@[implemented_by]`. -/
@[implemented_by mulPacked]
def mulCore (x y : MvSparsePoly R nvars) : MvSparsePoly R nvars :=
  ofList do
    let (i, a) ← x.terms
    let (j, b) ← y.terms
    return (i + j, a * b)

instance : Mul (MvSparsePoly R nvars) where
  mul := mulCore

instance : Neg (MvSparsePoly R nvars) where
  neg x := C (-1) * x

/-- Native computational negation, negating every coefficient. -/
def negCore (x : List (MvDegrees nvars × R)) : List (MvDegrees nvars × R) :=
  x.map (fun p => (p.1, -p.2))

omit [DecidableEq R] in
lemma negCore_sorted {x : List (MvDegrees nvars × R)} (h : x.Pairwise (·.1 > ·.1)) :
    (negCore x).Pairwise (·.1 > ·.1) := by
  induction x with
  | nil => exact List.Pairwise.nil
  | cons head tail ih =>
    simp only [negCore, List.map_cons, List.pairwise_cons] at h ⊢
    refine ⟨fun p hp => ?_, ih h.2⟩
    rcases List.mem_map.1 hp with ⟨p', hp', heq⟩
    subst heq
    exact h.1 p' hp'

/-- Negating non-zero elements keeps them non-zero. -/
lemma negCore_filter (x : List (MvDegrees nvars × R)) (hx : ∀ p ∈ x, p.2 ≠ 0) :
    (negCore x).filter (·.2 ≠ 0) = negCore x := by
  apply List.filter_eq_self.mpr
  intro p hp
  rcases List.mem_map.1 hp with ⟨p', hp', heq⟩
  subst heq
  have h_not_zero := hx p' hp'
  grind
/-- Adding a polynomial to its negation cancels to the empty list. -/
lemma addCore_negCore (x : List (MvDegrees nvars × R)) :
    addCore x (negCore x) = [] := by
  induction x with
  | nil => simp [addCore, negCore]
  | cons head tail ih =>
    rcases head with ⟨i, a⟩
    unfold addCore
    have h_not_lt : ¬(i < i) := lt_irrefl i
    simp only [negCore]
    have h_zero : a + -a = 0 := add_neg_cancel a
    aesop

instance : Neg (MvSparsePoly R nvars) where
  neg p := ofSortedList (negCore p.terms) (negCore_sorted p.sorted)

lemma addCore_nil_left (x : List (MvDegrees nvars × R)) : addCore [] x = x := by
  cases x <;> simp [addCore]

lemma addCore_nil_right (x : List (MvDegrees nvars × R)) : addCore x [] = x := by
  cases x <;> simp [addCore]

/-- `addCore` is commutative. -/
lemma addCore_comm : ∀ (x y : List (MvDegrees nvars × R)),
    addCore x y = addCore y x
  | [], yy => by cases yy <;> simp [addCore]
  | (i, a) :: x, [] => by simp [addCore]
  | (i, a) :: x, (j, b) :: y => by
    unfold addCore
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have h_not_ji : ¬(j < i) := fun h => lt_irrefl i (lt_trans hlt h)
      simp only [hlt, h_not_ji, ite_true, ite_false]
      rw [addCore_comm ((i, a) :: x) y]
    · subst heq
      have h_not_lt : ¬(i < i) := lt_irrefl i
      simp only [h_not_lt, ite_false, add_comm a b, addCore_comm x y]
    · have h_not_ij : ¬(i < j) := fun h => lt_irrefl j (lt_trans hgt h)
      simp only [hgt, h_not_ij, ite_true, ite_false]
      rw [addCore_comm x ((j, b) :: y)]
termination_by x y => x.length + y.length

/-- The `ofSortedList` filter does not change an already-valid polynomial. -/
lemma filter_nonzero_eq_self (p : MvSparsePoly R nvars) :
    p.terms.filter (·.2 ≠ 0) = p.terms := by
  apply List.filter_eq_self.mpr
  intro x hx
  exact decide_eq_true (p.nonzero x hx)

lemma poly_zero_add (p : MvSparsePoly R nvars) : 0 + p = p := by
  apply MvSparsePoly.ext
  change (addCore [] p.terms).filter (·.2 ≠ 0) = p.terms
  rw [addCore_nil_left]
  exact filter_nonzero_eq_self p

lemma poly_add_zero (p : MvSparsePoly R nvars) : p + 0 = p := by
  apply MvSparsePoly.ext
  change (addCore p.terms []).filter (·.2 ≠ 0) = p.terms
  rw [addCore_nil_right]
  exact filter_nonzero_eq_self p

lemma poly_add_comm (p q : MvSparsePoly R nvars) : p + q = q + p := by
  apply MvSparsePoly.ext
  change (addCore p.terms q.terms).filter (·.2 ≠ 0) =
    (addCore q.terms p.terms).filter (·.2 ≠ 0)
  rw [addCore_comm]

lemma poly_add_left_neg (p : MvSparsePoly R nvars) : -p + p = 0 := by
  apply MvSparsePoly.ext
  change (addCore ((negCore p.terms).filter (·.2 ≠ 0)) p.terms).filter (·.2 ≠ 0) = []
  rw [negCore_filter p.terms p.nonzero, addCore_comm (negCore p.terms) p.terms,
    addCore_negCore p.terms]
  rfl

/-- `ofList` of the empty list is the zero polynomial. -/
lemma ofList_nil : ofList (R := R) (nvars := nvars) [] = 0 := by
  apply MvSparsePoly.ext
  simp [ofList]
  simp [ofSortedList, dedupList]
  rfl

lemma poly_zero_mul (p : MvSparsePoly R nvars) : 0 * p = 0 := by
  change ofList [] = 0
  exact ofList_nil

lemma poly_mul_zero (p : MvSparsePoly R nvars) : p * 0 = 0 := by
  change ofList (p.terms.flatMap (fun _ => [])) = 0
  have h_bind : p.terms.flatMap
    (fun _ => ([] : List (MvDegrees nvars × R))) = [] := by
    induction p.terms with
    | nil => rfl
    | cons head tail ih => exact ih
  rw [h_bind]
  exact ofList_nil

/-! ### The Mathlib `Finsupp` bridge, identity and injectivity -/

open MvPolynomial

/-- `MvDegrees.toFinsupp` is injective. -/
lemma toFinsupp_inj {i j : MvDegrees nvars} :
    MvDegrees.toFinsupp i = MvDegrees.toFinsupp j ↔ i = j := by
  constructor
  · intro h
    have h_arr : i.degrees = j.degrees := by
      apply Array.ext
      · exact i.correct.trans j.correct.symm
      · intro v hv1 hv2
        have hv_fin : v < nvars := by aesop
        exact Finsupp.ext_iff.mp h ⟨v, hv_fin⟩
    have h_tot : i.totalDegree = j.totalDegree := by
      rw [i.totalDegree_eq, j.totalDegree_eq, h_arr]
    cases i
    cases j
    simp_all
  · intro h
    rw [h]

/-- `MvDegrees.toFinsupp` is additive. -/
lemma toFinsupp_add (i j : MvDegrees nvars) :
    MvDegrees.toFinsupp (i + j) =
    MvDegrees.toFinsupp i + MvDegrees.toFinsupp j := by
  ext v
  rw [Finsupp.add_apply]
  unfold MvDegrees.toFinsupp
  simp only [Finsupp.onFinset_apply]
  dsimp only [HAdd.hAdd, Add.add]
  simp

/-- `MvDegrees.toFinsupp` sends `0` to `0`. -/
lemma toFinsupp_zero :
    MvDegrees.toFinsupp (0 : MvDegrees nvars) = 0 := by
  ext v
  rw [Finsupp.zero_apply]
  unfold MvDegrees.toFinsupp
  simp only [Finsupp.onFinset_apply]
  have h_zero_def : (0 : MvDegrees nvars).degrees =
    (List.replicate nvars 0).toArray := rfl
  simp only [h_zero_def]
  grind

/-- `toPoly` of a constant polynomial is the constant `MvPolynomial`. -/
theorem toPoly_C (r : R) : toPoly (C r : MvSparsePoly R nvars) =
    MvPolynomial.C r := by
  unfold C toPoly ofSortedList
  dsimp only
  by_cases hr : r = 0
  · subst hr
    unfold toPolyCore
    grind
  · have h_filter : ([(0, r)] : List (MvDegrees nvars × R)).filter (·.2 ≠ 0) = [(0, r)] := by
      simp [hr]
    rw [h_filter]
    change MvPolynomial.monomial (MvDegrees.toFinsupp 0) r +
      toPolyCore [] = MvPolynomial.C r
    unfold toPolyCore
    rw [add_zero]
    have h_zero : MvDegrees.toFinsupp (0 : MvDegrees nvars) = 0 := toFinsupp_zero
    aesop

/-- `toPoly` of `1` is `1`. -/
lemma toPoly_one : toPoly (1 : MvSparsePoly R nvars) = 1 := by
  change toPoly (C 1 : MvSparsePoly R nvars) = 1
  rw [toPoly_C]
  exact map_one (MvPolynomial.C)

omit [DecidableEq R] in
/-- The coefficient at `n` of a polynomial with all degrees `< n` is zero. -/
theorem coeff_toPolyCore_of_degLt {n : MvDegrees nvars}
     (xs : List (MvDegrees nvars × R)) (h : degLt n xs) :
    MvPolynomial.coeff (MvDegrees.toFinsupp n) (toPolyCore xs) = 0 := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨i, a⟩
    dsimp only [toPolyCore]
    rw [MvPolynomial.coeff_add]
    have h_deg : i < n := h (i, a) List.mem_cons_self
    have h_finsupp_ne : MvDegrees.toFinsupp i ≠ MvDegrees.toFinsupp n :=
      fun h_eq => ne_of_lt h_deg (toFinsupp_inj.mp h_eq)
    rw [MvPolynomial.coeff_monomial, if_neg h_finsupp_ne,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), zero_add]

omit [DecidableEq R] in
/-- The coefficient of the head term at its own exponent `i` is its coefficient. -/
theorem coeff_toPolyCore_head {i : MvDegrees nvars} {a : R}
  (xs : List (MvDegrees nvars × R)) (h : degLt i xs) :
    MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore ((i, a) :: xs)) = a := by
  dsimp only [toPolyCore]
  simp only [MvPolynomial.coeff_add]
  rw [MvPolynomial.coeff_monomial, if_pos rfl, coeff_toPolyCore_of_degLt xs h, add_zero]

omit [CommRing R] [DecidableEq R] in
/-- Extract `degLt` from `Pairwise` sortedness. -/
lemma degLt_of_sorted_cons {i : MvDegrees nvars} {a : R}
  {xs : List (MvDegrees nvars × R)}
    (h : ((i, a) :: xs).Pairwise (·.1 > ·.1)) : degLt i xs :=
  fun x hx => (List.pairwise_cons.1 h).1 x hx

omit [DecidableEq R] in
/-- `toPolyCore` is injective on sorted term lists. -/
theorem toPolyCore_injective_of_sorted : ∀ (l1 l2 : List (MvDegrees nvars × R)),
    l1.Pairwise (·.1 > ·.1) → l2.Pairwise (·.1 > ·.1) →
    (∀ x ∈ l1, x.2 ≠ 0) → (∀ x ∈ l2, x.2 ≠ 0) →
    toPolyCore l1 = toPolyCore l2 → l1 = l2
  | [], [], _, _, _, _, _ => rfl
  | [], (j, b) :: ys, _, s2, _, nz2, heq => by
    have h_coeff : MvPolynomial.coeff (MvDegrees.toFinsupp j) (toPolyCore []) =
                   MvPolynomial.coeff (MvDegrees.toFinsupp j)
                   (toPolyCore ((j, b) :: ys)) := by
                    rw [heq]
    change 0 = _ at h_coeff
    rw [coeff_toPolyCore_head ys (degLt_of_sorted_cons s2)] at h_coeff
    have hb_nz := nz2 (j, b) List.mem_cons_self
    exact False.elim (hb_nz h_coeff.symm)
  | (i, a) :: xs, [], s1, _, nz1, _, heq => by
    have h_coeff : MvPolynomial.coeff (MvDegrees.toFinsupp i)
                   (toPolyCore ((i, a) :: xs)) =
                   MvPolynomial.coeff (MvDegrees.toFinsupp i)
                   (toPolyCore []) := by rw [heq]
    change _ = 0 at h_coeff
    rw [coeff_toPolyCore_head xs (degLt_of_sorted_cons s1)] at h_coeff
    have ha_nz := nz1 (i, a) List.mem_cons_self
    exact False.elim (ha_nz h_coeff)
  | (i, a) :: xs, (j, b) :: ys, s1, s2, nz1, nz2, heq => by
    have h_deg_x : degLt i xs := degLt_of_sorted_cons s1
    have h_deg_y : degLt j ys := degLt_of_sorted_cons s2
    obtain hij | rfl | hji := lt_trichotomy i j
    · have h_coeff : MvPolynomial.coeff (MvDegrees.toFinsupp j)
                     (toPolyCore ((i, a) :: xs)) =
                     MvPolynomial.coeff (MvDegrees.toFinsupp j) (toPolyCore ((j, b) :: ys)) := by
                     rw [heq]
      rw [coeff_toPolyCore_head ys h_deg_y] at h_coeff
      have h_xs_j : degLt j xs := fun e he => lt_trans (h_deg_x e he) hij
      have h_lhs : MvPolynomial.coeff (MvDegrees.toFinsupp j) (toPolyCore ((i, a) :: xs)) = 0 := by
        dsimp only [toPolyCore]
        simp only [MvPolynomial.coeff_add]
        have h_finsupp_ne : MvDegrees.toFinsupp i ≠ MvDegrees.toFinsupp j :=
          fun h_eq => (ne_of_lt hij) (toFinsupp_inj.mp h_eq)
        rw [MvPolynomial.coeff_monomial, if_neg h_finsupp_ne,
          coeff_toPolyCore_of_degLt xs h_xs_j, zero_add]
      rw [h_lhs] at h_coeff
      have hb_nz := nz2 (j, b) List.mem_cons_self
      exact False.elim (hb_nz h_coeff.symm)
    · have h_coeff : MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore ((i, a) :: xs)) =
                     MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore ((i, b) :: ys)) := by
                     rw [heq]
      rw [coeff_toPolyCore_head xs h_deg_x, coeff_toPolyCore_head ys h_deg_y] at h_coeff
      subst h_coeff
      dsimp only [toPolyCore] at heq
      have heq_xs_ys : toPolyCore xs = toPolyCore ys := add_left_cancel heq
      have s1_xs : xs.Pairwise (·.1 > ·.1) := (List.pairwise_cons.1 s1).2
      have s2_ys : ys.Pairwise (·.1 > ·.1) := (List.pairwise_cons.1 s2).2
      have nz1_xs : ∀ x ∈ xs, x.2 ≠ 0 := fun e he => nz1 e (List.mem_cons_of_mem _ he)
      have nz2_ys : ∀ x ∈ ys, x.2 ≠ 0 := fun e he => nz2 e (List.mem_cons_of_mem _ he)
      rw [toPolyCore_injective_of_sorted xs ys s1_xs s2_ys nz1_xs nz2_ys heq_xs_ys]
    · have h_coeff : MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore ((i, a) :: xs)) =
                     MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore ((j, b) :: ys)) := by
                     rw [heq]
      rw [coeff_toPolyCore_head xs h_deg_x] at h_coeff
      have h_ys_i : degLt i ys := fun e he => lt_trans (h_deg_y e he) hji
      have h_rhs : MvPolynomial.coeff (MvDegrees.toFinsupp i) (toPolyCore ((j, b) :: ys)) = 0 := by
        dsimp only [toPolyCore]
        simp only [MvPolynomial.coeff_add]
        have h_finsupp_ne : MvDegrees.toFinsupp j ≠ MvDegrees.toFinsupp i :=
          fun h_eq => (ne_of_lt hji) (toFinsupp_inj.mp h_eq)
        rw [MvPolynomial.coeff_monomial, if_neg h_finsupp_ne,
          coeff_toPolyCore_of_degLt ys h_ys_i, zero_add]
      rw [h_rhs] at h_coeff
      have ha_nz := nz1 (i, a) List.mem_cons_self
      exact False.elim (ha_nz h_coeff)

omit [DecidableEq R] in
lemma toPoly_injective : Function.Injective (toPoly (R := R) (nvars := nvars)) := by
  intro x y h
  ext1
  exact toPolyCore_injective_of_sorted x.terms y.terms x.sorted y.sorted x.nonzero y.nonzero h

/-- Filtering out zero coefficients does not change the `MvPolynomial`. -/
theorem toPolyCore_filter_nonzero (l : List (MvDegrees nvars × R)) :
    toPolyCore (l.filter (·.2 ≠ 0)) = toPolyCore l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨i, a⟩
    simp only [List.filter_cons]
    split
    · next h_nonzero => unfold toPolyCore; rw [ih]
    · next h_zero =>
      have ha0 : a = 0 := by aesop
      unfold toPolyCore
      rw [ha0, map_zero, zero_add]
      aesop

/-- `addCore` mirrors `MvPolynomial` addition. -/
theorem toPolyCore_addCore : ∀ (x y : List (MvDegrees nvars × R)),
    toPolyCore (addCore x y) = toPolyCore x + toPolyCore y
  | [], yy => by simp [addCore, toPolyCore]
  | (i, a) :: x, [] => by simp [addCore, toPolyCore]
  | (i, a) :: x, (j, b) :: y => by
    simp only [addCore]
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have h_not_ji : ¬(j < i) := fun h_contra => lt_irrefl i (lt_trans hlt h_contra)
      simp only [hlt, ↓reduceIte]
      dsimp only [toPolyCore]
      rw [toPolyCore_addCore]
      simp only [toPolyCore]
      ring
    · subst heq
      simp only [lt_self_iff_false, ↓reduceIte]
      split
      · next hab =>
          dsimp only [toPolyCore]
          rw [toPolyCore_addCore]
          have h_rearrange : (MvPolynomial.monomial (MvDegrees.toFinsupp i) a + toPolyCore x) +
                             (MvPolynomial.monomial (MvDegrees.toFinsupp i) b + toPolyCore y) =
                             (MvPolynomial.monomial (MvDegrees.toFinsupp i) a +
                              MvPolynomial.monomial (MvDegrees.toFinsupp i) b) +
                             (toPolyCore x + toPolyCore y) := by ring
          rw [h_rearrange, ← map_add, hab, map_zero, zero_add]
      · next hab =>
          dsimp only [toPolyCore]
          rw [toPolyCore_addCore, map_add]
          ring
    · have h_not_ij : ¬(i < j) := fun h_contra => lt_irrefl j (lt_trans hgt h_contra)
      simp only [h_not_ij, ↓reduceIte, hgt]
      dsimp only [toPolyCore]
      rw [toPolyCore_addCore]
      simp only [toPolyCore]
      ring
termination_by x y => x.length + y.length

lemma toPoly_add (a b : MvSparsePoly R nvars) : toPoly (a + b) = toPoly a + toPoly b := by
  unfold toPoly
  change toPolyCore ((addCore a.terms b.terms).filter (·.2 ≠ 0)) =
         toPolyCore a.terms + toPolyCore b.terms
  rw [toPolyCore_filter_nonzero]
  exact toPolyCore_addCore a.terms b.terms

omit [DecidableEq R] in
theorem toPolyCore_perm {l1 l2 : List (MvDegrees nvars × R)} (h : l1.Perm l2) :
    toPolyCore l1 = toPolyCore l2 := by
  induction h with
  | nil => rfl
  | cons x _ ih => dsimp [toPolyCore]; rw [ih]
  | swap x y l => dsimp [toPolyCore]; ring
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

omit [DecidableEq R] in
/-- `mergeSort` is a permutation, so it preserves the polynomial. -/
theorem toPolyCore_mergeSort (l : List (MvDegrees nvars × R))
  (r : (MvDegrees nvars × R) → (MvDegrees nvars × R) → Bool) :
    toPolyCore (l.mergeSort r) = toPolyCore l :=
  toPolyCore_perm (l.mergeSort_perm r)

omit [DecidableEq R] in
theorem toPolyCore_dedupList : ∀ (l : List (MvDegrees nvars × R)),
    toPolyCore (dedupList l) = toPolyCore l
  | [] => by simp [dedupList, toPolyCore]
  | [x] => by simp [dedupList, toPolyCore]
  | (i, a) :: (j, b) :: xs => by
      unfold dedupList
      split
      · next heq =>
        subst heq
        rw [toPolyCore_dedupList ((i, a + b) :: xs)]
        dsimp [toPolyCore]
        rw [map_add]
        ring
      · next hneq =>
        dsimp [toPolyCore]
        rw [toPolyCore_dedupList ((j, b) :: xs)]
        simp only [toPolyCore]

/-- The master bridge: `toPoly (ofList l) = toPolyCore l`. -/
theorem toPoly_ofList (l : List (MvDegrees nvars × R)) :
    toPoly (ofList l) = toPolyCore l := by
  unfold toPoly ofList ofSortedList
  dsimp only
  rw [toPolyCore_filter_nonzero, toPolyCore_dedupList, toPolyCore_mergeSort]

omit [DecidableEq R] in
/-- Multiplying a term list by a single monomial `(i, a)`. -/
theorem toPolyCore_monomial_mul (l : List (MvDegrees nvars × R)) (i : MvDegrees nvars) (a : R) :
    toPolyCore (l.map fun ⟨j, b⟩ => (i + j, a * b)) =
    (MvPolynomial.monomial (MvDegrees.toFinsupp i) a) * toPolyCore l := by
  induction l with
  | nil => simp [toPolyCore]
  | cons hd tl ih =>
    rcases hd with ⟨j, b⟩
    dsimp [toPolyCore]
    rw [mul_add, ← ih]
    congr 1
    rw [MvPolynomial.monomial_mul, toFinsupp_add, mul_comm a b, add_comm]

theorem toPolyCore_ofList_terms (l : List (MvDegrees nvars × R)) :
    toPolyCore (ofList l).terms = toPolyCore l := by
  unfold ofList ofSortedList
  dsimp
  rw [toPolyCore_filter_nonzero, toPolyCore_dedupList, toPolyCore_mergeSort]

omit [DecidableEq R] in
/-- `toPolyCore` distributes over list append. -/
theorem toPolyCore_append (l1 l2 : List (MvDegrees nvars × R)) :
    toPolyCore (l1 ++ l2) = toPolyCore l1 + toPolyCore l2 := by
  induction l1 with
  | nil => simp [toPolyCore]
  | cons hd tl ih =>
    dsimp [toPolyCore]
    rw [ih, add_assoc]

omit [DecidableEq R] in
/-- `flatMap` form of `toPolyCore_monomial_mul`. -/
theorem toPolyCore_monomial_mul_flatMap (l : List (MvDegrees nvars × R))
      (i : MvDegrees nvars) (a : R) :
    toPolyCore (l.flatMap fun x => [(i + x.1, a * x.2)]) =
    (MvPolynomial.monomial (MvDegrees.toFinsupp i) a) * toPolyCore l := by
  induction l with
  | nil => simp [toPolyCore, List.flatMap]
  | cons hd tl ih =>
    change (MvPolynomial.monomial (MvDegrees.toFinsupp (i + hd.1))) (a * hd.2) +
           toPolyCore (tl.flatMap fun x => [(i + x.1, a * x.2)]) = _
    rw [ih]
    erw [mul_add]
    congr 1
    rw [MvPolynomial.monomial_mul, toFinsupp_add, mul_comm a hd.2, add_comm]

omit [DecidableEq R] in
/-- The product of two term lists, expanded via `flatMap`, computes the polynomial product. -/
theorem toPolyCore_mul_flatMap (l1 l2 : List (MvDegrees nvars × R)) :
    toPolyCore (l1.flatMap fun x => l2.flatMap fun y => [(x.1 + y.1, x.2 * y.2)]) =
    toPolyCore l1 * toPolyCore l2 := by
  induction l1 with
  | nil => simp [toPolyCore, List.flatMap]
  | cons hd tl ih =>
    change toPolyCore ((l2.flatMap fun y => [(hd.1 + y.1, hd.2 * y.2)]) ++
                       (tl.flatMap fun x => l2.flatMap fun y => [(x.1 + y.1, x.2 * y.2)])) = _
    rw [toPolyCore_append, toPolyCore_monomial_mul_flatMap, ih]
    dsimp [toPolyCore]
    rw [add_mul]

lemma toPoly_mul (a b : MvSparsePoly R nvars) :
    toPoly (a * b) = toPoly a * toPoly b := by
  unfold toPoly
  dsimp [HMul.hMul, Mul.mul, mulCore]
  rw [toPolyCore_ofList_terms]
  exact toPolyCore_mul_flatMap a.terms b.terms

instance : CommRing (MvSparsePoly R nvars) where
  add := (·+·)
  zero := 0
  zero_add := poly_zero_add
  add_zero := poly_add_zero
  add_comm := poly_add_comm
  neg := (-·)
  neg_add_cancel := poly_add_left_neg
  mul := (·*·)
  one := 1
  zero_mul := poly_zero_mul
  mul_zero := poly_mul_zero
  nsmul := nsmulRec
  zsmul := zsmulRec
  nsmul_zero := by intros; rfl
  nsmul_succ := by intros; rfl
  zsmul_zero' := by intros; rfl
  zsmul_succ' := by intros; rfl
  natCast n := nsmulRec n 1
  natCast_zero := rfl
  natCast_succ := by intros; rfl
  zsmul_neg' := by intros; rfl
  add_assoc a b c := toPoly_injective (by simp only [toPoly_add, add_assoc])
  mul_assoc a b c := toPoly_injective (by simp only [toPoly_mul, mul_assoc])
  mul_comm a b := toPoly_injective (by simp only [toPoly_mul, mul_comm])
  left_distrib a b c := toPoly_injective (by simp only [toPoly_add, toPoly_mul, left_distrib])
  right_distrib a b c := toPoly_injective (by simp only [toPoly_add, toPoly_mul, right_distrib])
  one_mul a := toPoly_injective (by simp only [toPoly_mul, toPoly_one, one_mul])
  mul_one a := toPoly_injective (by simp only [toPoly_mul, toPoly_one, mul_one])

omit [DecidableEq R] in
lemma toPoly_zero : toPoly (0 : MvSparsePoly R nvars) = 0 := rfl

/-- The constant-polynomial inclusion `R → MvSparsePoly R nvars` as a ring homomorphism. -/
def CHom : R →+* MvSparsePoly R nvars where
  toFun := C
  map_zero' := by
    apply toPoly_injective
    simp only [toPoly_C, toPoly_zero, map_zero]
  map_one' := by
    apply toPoly_injective
    simp only [toPoly_C, toPoly_one, map_one]
  map_add' := by
    intro x y
    apply toPoly_injective
    simp only [toPoly_add, toPoly_C, map_add]
  map_mul' := by
    intro x y
    apply toPoly_injective
    simp only [toPoly_mul, toPoly_C, map_mul]

instance : Algebra R (MvSparsePoly R nvars) where
  smul r p := C r * p
  algebraMap := CHom
  commutes' r p := mul_comm (C r) p
  smul_def' _ _ := rfl


lemma toFinsupp_singleDegree (v : Fin nvars) :
    MvDegrees.toFinsupp (singleDegree v) = Finsupp.single v 1 := by
  ext i
  rw [Finsupp.single_apply]
  unfold MvDegrees.toFinsupp singleDegree
  simp only [Finsupp.onFinset_apply]
  rw [Fin.getElem_fin, ← Array.getElem_toList]
  simp only [List.getElem_set, List.getElem_replicate]
  by_cases h : v = i
  · subst h; simp
  · rw [if_neg h]
    split
    · rename_i hc
      exact absurd (Fin.ext (show (v : ℕ) = (i : ℕ) by omega)) h
    · rfl

@[simp]
theorem toPoly_X (v : Fin nvars) :
    (X v : MvSparsePoly R nvars).toPoly = MvPolynomial.X v := by
  unfold X toPoly ofSortedList
  dsimp only
  rw [toPolyCore_filter_nonzero]
  simp only [toPolyCore, add_zero]
  rw [toFinsupp_singleDegree]
  rfl

instance : DecidableEq (MvSparsePoly R nvars) := fun a b =>
  decidable_of_iff' (a.terms = b.terms) (MvSparsePoly.ext_iff ..)

end MvSparsePoly
