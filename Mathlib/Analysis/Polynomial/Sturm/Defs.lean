/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Basic.Sign.Basic
public import Mathlib.Topology.Algebra.Polynomial

/-!
Definitions supporting Sturm's theorem over `Polynomial ℝ`.

This module defines the zero-skipping sign-variation count `Sturm.sturmVar`
of a chain of real polynomials at a point, and the predicate
`Sturm.IsSturmChain` capturing the sign axioms that the root-counting
argument uses. Nothing here refers to any `HexRealRoots` executable type; the
definitions are stated directly over `Polynomial ℝ`.

The zero-skipping convention: the variation count of a sign pattern such as
`(+, 0, −)` is `1`. Concretely we drop the zero evaluations and count the
adjacent pairs of opposite sign among what remains.
-/

public section

open Filter Topology

namespace Sturm

/-- Count the sign changes of a real list: the number of adjacent pairs
whose product is negative. Callers first drop the zero entries (see
`Sturm.signVariations`), so on a zero-free list this is exactly the number
of adjacent opposite-sign pairs. -/
@[expose]
noncomputable def countSignChanges : List ℝ → ℕ
  | a :: b :: rest => (if a * b < 0 then 1 else 0) + countSignChanges (b :: rest)
  | _ => 0

@[simp] theorem countSignChanges_nil : countSignChanges [] = 0 := rfl

@[simp] theorem countSignChanges_singleton (a : ℝ) : countSignChanges [a] = 0 := rfl

theorem countSignChanges_cons_cons (a b : ℝ) (rest : List ℝ) :
    countSignChanges (a :: b :: rest) =
      (if a * b < 0 then 1 else 0) + countSignChanges (b :: rest) := rfl

/-- Zero-skipping sign variations of a real list: drop the zeros, then count
the adjacent opposite-sign pairs. This is the variation count that both the
pointwise chain evaluations and the leading-coefficient signs at `±∞` feed
into. -/
@[expose]
noncomputable def signVariations (l : List ℝ) : ℕ :=
  countSignChanges (l.filter (fun v => decide (v ≠ 0)))

@[simp] theorem signVariations_nil : signVariations [] = 0 := rfl

/-- Prepending a zero entry does not change the sign variations. -/
theorem signVariations_cons_zero (l : List ℝ) :
    signVariations (0 :: l) = signVariations l := by
  simp [signVariations]

/-- Prepending a nonzero entry `a` to a list whose first surviving entry has
the same sign as `a` (or which becomes empty after dropping zeros) is
governed by `countSignChanges`; this unfolding lemma exposes the recursion to
downstream local-sign arguments. -/
theorem signVariations_cons_ne (a : ℝ) (l : List ℝ) (ha : a ≠ 0) :
    signVariations (a :: l) =
      countSignChanges (a :: l.filter (fun v => decide (v ≠ 0))) := by
  simp [signVariations, ha]

/-- Zero-skipping sign variations of the chain `chain` evaluated at `x`:
the sign variations of the list of evaluations `chain.map (·.eval x)`. -/
@[expose]
noncomputable def sturmVar (chain : List (Polynomial ℝ)) (x : ℝ) : ℕ :=
  signVariations (chain.map (Polynomial.eval x))

@[simp] theorem sturmVar_nil (x : ℝ) : sturmVar [] x = 0 := rfl

/-- A chain element that vanishes at `x` contributes no variation at `x`:
`sturmVar` ignores it. -/
theorem sturmVar_cons_zero {q : Polynomial ℝ} {x : ℝ} (h : q.eval x = 0)
    (chain : List (Polynomial ℝ)) :
    sturmVar (q :: chain) x = sturmVar chain x := by
  simp [sturmVar, List.map_cons, signVariations, h]

/-- Two real lists whose entries have pointwise equal signs have equal
`countSignChanges`: the sign-change count reads only the signs of the entries. -/
theorem countSignChanges_congr {l₁ l₂ : List ℝ}
    (h : List.Forall₂ (fun u v => SignType.sign u = SignType.sign v) l₁ l₂) :
    countSignChanges l₁ = countSignChanges l₂ := by
  induction h with
  | nil => rfl
  | @cons a b l₁' l₂' hab htail ih =>
    cases htail with
    | nil => rfl
    | @cons c d l₁'' l₂'' hcd _ =>
      rw [countSignChanges_cons_cons, countSignChanges_cons_cons]
      have hiff : (a * c < 0) ↔ (b * d < 0) := by
        rw [← sign_eq_neg_one_iff, ← sign_eq_neg_one_iff, sign_mul, sign_mul, hab, hcd]
      by_cases hc : a * c < 0
      · rw [ite_eq_left hc, ite_eq_left (hiff.mp hc), ih]
      · rw [ite_eq_right hc, ite_eq_right (fun h => hc (hiff.mpr h)), ih]

/-- Dropping the zero entries commutes with a pointwise sign-equal
correspondence: the filtered lists remain pointwise sign-equal. -/
theorem filter_ne_zero_congr {l₁ l₂ : List ℝ}
    (h : List.Forall₂ (fun u v => SignType.sign u = SignType.sign v) l₁ l₂) :
    List.Forall₂ (fun u v => SignType.sign u = SignType.sign v)
      (l₁.filter (fun v => decide (v ≠ 0))) (l₂.filter (fun v => decide (v ≠ 0))) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons a b l₁' l₂' hab htail ih =>
    have hzero : (a = 0) ↔ (b = 0) := by
      rw [← sign_eq_zero_iff (a := a), ← sign_eq_zero_iff (a := b), hab]
    by_cases ha : a = 0
    · have hb : b = 0 := hzero.mp ha
      have e1 : (a :: l₁').filter (fun v => decide (v ≠ 0))
          = l₁'.filter (fun v => decide (v ≠ 0)) := by rw [List.filter_cons]; simp [ha]
      have e2 : (b :: l₂').filter (fun v => decide (v ≠ 0))
          = l₂'.filter (fun v => decide (v ≠ 0)) := by rw [List.filter_cons]; simp [hb]
      rw [e1, e2]; exact ih
    · have hb : b ≠ 0 := fun h => ha (hzero.mpr h)
      have e1 : (a :: l₁').filter (fun v => decide (v ≠ 0))
          = a :: l₁'.filter (fun v => decide (v ≠ 0)) := by rw [List.filter_cons]; simp [ha]
      have e2 : (b :: l₂').filter (fun v => decide (v ≠ 0))
          = b :: l₂'.filter (fun v => decide (v ≠ 0)) := by rw [List.filter_cons]; simp [hb]
      rw [e1, e2]; exact List.Forall₂.cons hab ih

/-- `signVariations` reads only the signs of the entries: two real lists whose
entries are pointwise sign-equal have equal sign variations. -/
theorem signVariations_congr {l₁ l₂ : List ℝ}
    (h : List.Forall₂ (fun u v => SignType.sign u = SignType.sign v) l₁ l₂) :
    signVariations l₁ = signVariations l₂ :=
  countSignChanges_congr (filter_ne_zero_congr h)

/-- The sign of the first surviving (nonzero) entry of a real list, as an
`Option SignType`: `none` when every entry is zero. This is the piece of local
state that governs how prepending a nonzero entry changes `signVariations`. -/
@[expose]
noncomputable def firstSign (l : List ℝ) : Option SignType :=
  (l.filter (fun v => decide (v ≠ 0))).head?.map (fun a => SignType.sign a)

@[simp] theorem firstSign_nil : firstSign [] = none := rfl

theorem firstSign_cons_zero {a : ℝ} (l : List ℝ) (ha : a = 0) :
    firstSign (a :: l) = firstSign l := by
  unfold firstSign; rw [List.filter_cons_of_neg (by simp [ha])]

theorem firstSign_cons_ne {a : ℝ} (l : List ℝ) (ha : a ≠ 0) :
    firstSign (a :: l) = some (SignType.sign a) := by
  unfold firstSign
  rw [List.filter_cons_of_pos (by simp [ha]), List.head?_cons, Option.map_some]

private theorem sign_mul_eq_neg_one {a b : ℝ} :
    (SignType.sign a * SignType.sign b = -1) ↔ a * b < 0 := by
  rw [← sign_mul, sign_eq_neg_one_iff]

/-- Prepending a nonzero entry `a` adds one variation exactly when its sign is
opposite the sign of the next surviving entry. -/
theorem signVariations_cons_pos {a : ℝ} (l : List ℝ) (ha : a ≠ 0) :
    signVariations (a :: l) =
      (firstSign l).elim 0
        (fun t => if SignType.sign a * t = -1 then 1 else 0) + signVariations l := by
  induction l with
  | nil => rw [signVariations_cons_ne a [] ha]; simp [firstSign]
  | cons b l' ih =>
    by_cases hb : b = 0
    · subst hb
      rw [firstSign_cons_zero l' rfl, signVariations_cons_zero l',
        signVariations_cons_ne a (0 :: l') ha, List.filter_cons_of_neg (by simp),
        ← signVariations_cons_ne a l' ha]
      exact ih
    · rw [firstSign_cons_ne l' hb, signVariations_cons_ne a (b :: l') ha,
        List.filter_cons_of_pos (by simp [hb]), countSignChanges_cons_cons,
        ← signVariations_cons_ne b l' hb]
      simp only [Option.elim_some]
      congr 1
      by_cases hlt : a * b < 0
      · rw [ite_eq_left hlt, ite_eq_left (sign_mul_eq_neg_one.mpr hlt)]
      · rw [ite_eq_right hlt, ite_eq_right (fun h => hlt (sign_mul_eq_neg_one.mp h))]

/-- A local sign-pattern relation between two real lists: they agree entry by
entry except that a nonzero entry flanked by two opposite-sign neighbours may
collapse to `0`. Such a collapse is variation-neutral, so `signVariations` and
the leading sign are preserved (`SVRel.signVariations_eq`). -/
inductive SVRel : List ℝ → List ℝ → Prop
  | nil : SVRel [] []
  | same {x y : ℝ} {l m : List ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
      (hs : SignType.sign x = SignType.sign y) (h : SVRel l m) :
      SVRel (x :: l) (y :: m)
  | collapse {x X x' : ℝ} {l m : List ℝ} {y y' : ℝ}
      (hx : x ≠ 0) (hX : X ≠ 0) (hy' : y' ≠ 0)
      (hsx : SignType.sign x = SignType.sign x')
      (hsy : SignType.sign y = SignType.sign y')
      (hopp : SignType.sign x * SignType.sign y = -1)
      (h : SVRel (y :: l) (y' :: m)) :
      SVRel (x :: X :: y :: l) (x' :: 0 :: y' :: m)

private theorem svrel_flank_arith (u v w : SignType) (huw : u * w = -1) (hv : v ≠ 0) :
    (if u * v = -1 then (1 : ℕ) else 0) + (if v * w = -1 then 1 else 0) = 1 := by
  revert huw hv; revert u v w; decide

/-- The core combinatorial fact: an `SVRel`-related pair of lists has equal
sign variations and equal leading sign. -/
theorem SVRel.signVariations_eq {L M : List ℝ} (h : SVRel L M) :
    signVariations L = signVariations M ∧ firstSign L = firstSign M := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | @same x y l m hx hy hs h ih =>
    refine ⟨?_, ?_⟩
    · rw [signVariations_cons_pos l hx, signVariations_cons_pos m hy, ih.1, ih.2, hs]
    · rw [firstSign_cons_ne l hx, firstSign_cons_ne m hy, hs]
  | @collapse x X x' l m y y' hx hX hy' hsx hsy hopp h ih =>
    have hy : y ≠ 0 := by
      intro hy0; rw [hy0, sign_zero, mul_zero] at hopp; exact absurd hopp (by decide)
    have hx' : x' ≠ 0 := by
      intro hx0; rw [hx0, sign_zero] at hsx; exact hx (sign_eq_zero_iff.mp hsx)
    refine ⟨?_, ?_⟩
    · -- signVariations L
      rw [signVariations_cons_pos (X :: y :: l) hx,
        firstSign_cons_ne (y :: l) hX, signVariations_cons_pos (y :: l) hX,
        firstSign_cons_ne l hy]
      rw [signVariations_cons_pos (0 :: y' :: m) hx',
        firstSign_cons_zero (y' :: m) rfl, firstSign_cons_ne m hy',
        signVariations_cons_zero]
      simp only [Option.elim_some]
      rw [← add_assoc, ih.1]
      congr 1
      rw [← hsx, ← hsy, ite_eq_left hopp]
      exact svrel_flank_arith _ _ _ hopp (fun h => hX (sign_eq_zero_iff.mp h))
    · rw [firstSign_cons_ne (X :: y :: l) hx, firstSign_cons_ne (0 :: y' :: m) hx', hsx]

/-- A generalised Sturm chain for `p`: the sign axioms that the counting
argument actually uses, packaged as explicit fields. The chain is stored as
a plain `List (Polynomial ℝ)` and elements are addressed by index through
`getElem?`, so no length lower bound is baked in (a nonzero constant `p` has
the one-element chain `[p]`).

The fields are:

* `nonempty` / `head` — the chain is nonempty and its head is `p`;
* `root_flank` — at every real root `r` of `p` there is a second element
  `q` (`chain[1] = q`), nonzero at `r`, with `p * q` negative on a punctured
  left neighbourhood of `r` and positive on a punctured right neighbourhood.
  Phrasing the second element existentially forbids the degenerate witness in
  which `p` has a root but the chain has no derivative-like second entry;
* `nonzero_mem` — no chain element is the zero polynomial, so each element
  has finitely many zeros and the counting theorem's telescope over the
  chain's zeros is finite;
* `consec_coprime` — consecutive elements never vanish at a common point;
* `interior_alternates` — when an interior element (one with both neighbours
  present) vanishes at a point, both neighbours are nonzero there and have
  opposite signs, so the local pattern is `(±, 0, ∓)`;
* `last_no_root` — the last element has no real zero. -/
structure IsSturmChain (p : Polynomial ℝ) (chain : List (Polynomial ℝ)) : Prop where
  /-- The chain is nonempty. -/
  nonempty : chain ≠ []
  /-- The head of the chain is `p`. -/
  head : chain.head? = some p
  /-- At every real root `r` of `p`, the chain has a second element `q`,
  nonzero at `r`, with `p * q` negative just left of `r` and positive just
  right of `r`. -/
  root_flank : ∀ r : ℝ, p.IsRoot r → ∃ q : Polynomial ℝ, chain[1]? = some q ∧
    q.eval r ≠ 0 ∧
    (∀ᶠ x in 𝓝[<] r, (p * q).eval x < 0) ∧
    (∀ᶠ x in 𝓝[>] r, 0 < (p * q).eval x)
  /-- No chain element is the zero polynomial. -/
  nonzero_mem : ∀ q ∈ chain, q ≠ 0
  /-- Consecutive elements have no common real zero. -/
  consec_coprime : ∀ (i : ℕ) (x : ℝ) (a b : Polynomial ℝ),
    chain[i]? = some a → chain[i + 1]? = some b → a.eval x = 0 → b.eval x ≠ 0
  /-- Whenever the interior element `b = chain[i+1]` vanishes at `x`, its two
  neighbours `a = chain[i]` and `c = chain[i+2]` are nonzero there and have
  opposite signs. -/
  interior_alternates : ∀ (i : ℕ) (x : ℝ) (a b c : Polynomial ℝ),
    chain[i]? = some a → chain[i + 1]? = some b → chain[i + 2]? = some c →
    b.eval x = 0 → a.eval x ≠ 0 ∧ c.eval x ≠ 0 ∧ a.eval x * c.eval x < 0
  /-- The last element of the chain has no real zero. -/
  last_no_root : ∀ q : Polynomial ℝ, chain.getLast? = some q → ∀ x : ℝ, q.eval x ≠ 0

end Sturm
