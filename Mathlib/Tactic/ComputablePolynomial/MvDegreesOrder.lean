/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
module

public import Mathlib.Tactic.ComputablePolynomial.MvDegrees
public import Mathlib.Data.DFinsupp.WellFounded

/-!
# The lexicographic monomial order on `MvDegrees`

`WOrdering nvars` packages an admissible monomial order on `MvDegrees nvars`: a linear order that
is well-founded, has `0` least, and is compatible with addition. The instance provided is the
lexicographic order, implemented by a kernel-friendly list comparison (`listLex`) and proved
well-founded via `Pi.Lex.wellFounded`.
-/

@[expose] public section

variable {nvars : ℕ}

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
