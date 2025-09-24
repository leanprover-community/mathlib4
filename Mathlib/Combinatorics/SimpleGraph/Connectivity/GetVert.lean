/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Walks

/-!

# The `n`-th vertex of a walk and related definitions

## Main definitions

* `p.getVert n` the `n`th vertex of a walk `p`. If `n` is greater than or equal to `p.length`,
  the result is the walk's endpoint.
* `p.snd` the second vertex of a walk, or the only vertex in a nil walk.
* `p.penultimate` the penultimate vertex of a walk, or the only vertex in a nil walk.
* `p.drop n` the walk formed by removing the first `n` darts from `p`.
* `p.take n` the walk formed by taking the first `n` darts of `p`.
* `p.tail` the walk formed by removing the first dart from `p`.
* `p.dropLast` the walk formed by removing the last dart from `p`.

-/

universe u
namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}
namespace Walk

/-- Get the `n`th vertex from a walk, where `n` is generally expected to be
between `0` and `p.length`, inclusive.
If `n` is greater than or equal to `p.length`, the result is the walk's endpoint. -/
def getVert {u v : V} : G.Walk u v → ℕ → V
  | nil, _ => u
  | cons _ _, 0 => u
  | cons _ q, n + 1 => q.getVert n

@[simp]
theorem getVert_zero {u v} (w : G.Walk u v) : w.getVert 0 = u := by cases w <;> rfl

@[simp]
theorem getVert_nil (u : V) {i : ℕ} : (@nil _ G u).getVert i = u := rfl

theorem getVert_of_length_le {u v} (w : G.Walk u v) {i : ℕ} (hi : w.length ≤ i) :
    w.getVert i = v := by
  induction w generalizing i with
  | nil => rfl
  | cons _ _ ih =>
    cases i
    · cases hi
    · exact ih (Nat.succ_le_succ_iff.1 hi)

@[simp]
theorem getVert_length {u v} (w : G.Walk u v) : w.getVert w.length = v :=
  w.getVert_of_length_le rfl.le

theorem adj_getVert_succ {u v} (w : G.Walk u v) {i : ℕ} (hi : i < w.length) :
    G.Adj (w.getVert i) (w.getVert (i + 1)) := by
  induction w generalizing i with
  | nil => cases hi
  | cons hxy _ ih =>
    cases i
    · simp [getVert, hxy]
    · exact ih (Nat.succ_lt_succ_iff.1 hi)

@[simp]
lemma getVert_cons_succ {u v w n} (p : G.Walk v w) (h : G.Adj u v) :
    (p.cons h).getVert (n + 1) = p.getVert n := rfl

lemma getVert_cons {u v w n} (p : G.Walk v w) (h : G.Adj u v) (hn : n ≠ 0) :
    (p.cons h).getVert n = p.getVert (n - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  rw [getVert_cons_succ, Nat.add_sub_cancel]

theorem getVert_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) (i : ℕ) :
    (p.append q).getVert i = if i < p.length then p.getVert i else q.getVert (i - p.length) := by
  induction p generalizing i with
  | nil => simp
  | cons h p ih => cases i <;> simp [getVert, ih, Nat.succ_lt_succ_iff]

theorem getVert_reverse {u v : V} (p : G.Walk u v) (i : ℕ) :
    p.reverse.getVert i = p.getVert (p.length - i) := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [reverse_cons, getVert_append, length_reverse, ih, length_cons]
    split_ifs
    next hi =>
      rw [Nat.succ_sub hi.le]
      simp [getVert]
    next hi =>
      obtain rfl | hi' := eq_or_gt_of_not_lt hi
      · simp
      · rw [Nat.eq_add_of_sub_eq (Nat.sub_pos_of_lt hi') rfl, Nat.sub_eq_zero_of_le hi']
        simp [getVert]

@[simp]
theorem getVert_mem_support {u v : V} (p : G.Walk u v) (i : ℕ) : p.getVert i ∈ p.support := by
  induction p generalizing i with
  | nil => simp
  | cons _ _ hind =>
    cases i
    · simp
    · simp [hind]

lemma getVert_eq_support_getElem {u v : V} {n : ℕ} (p : G.Walk u v) (h : n ≤ p.length) :
    p.getVert n = p.support[n]'(p.length_support ▸ Nat.lt_add_one_of_le h) := by
  cases p with
  | nil => simp
  | cons => cases n with
    | zero => simp
    | succ n =>
      simp_rw [support_cons, getVert_cons _ _ n.zero_ne_add_one.symm, List.getElem_cons]
      exact getVert_eq_support_getElem _ (Nat.sub_le_of_le_add h)

lemma getVert_eq_support_getElem? {u v : V} {n : ℕ} (p : G.Walk u v) (h : n ≤ p.length) :
    some (p.getVert n) = p.support[n]? := by
  rw [getVert_eq_support_getElem p h, ← List.getElem?_eq_getElem]

@[deprecated (since := "2025-06-10")]
alias getVert_eq_support_get? := getVert_eq_support_getElem?

theorem nodup_tail_support_reverse {u : V} {p : G.Walk u u} :
    p.reverse.support.tail.Nodup ↔ p.support.tail.Nodup := by
  rw [Walk.support_reverse]
  refine List.nodup_tail_reverse p.support ?h
  rw [← getVert_eq_support_getElem? _ (by cutsat), List.getLast?_eq_getElem?,
    ← getVert_eq_support_getElem? _ (by rw [Walk.length_support]; cutsat)]
  aesop

/-- The walk obtained by removing the first `n` darts of a walk. -/
def drop {u v : V} (p : G.Walk u v) (n : ℕ) : G.Walk (p.getVert n) v :=
  match p, n with
  | .nil, _ => .nil
  | p, 0 => p.copy (getVert_zero p).symm rfl
  | .cons _ q, (n + 1) => q.drop n

variable {u v w : V}

@[simp]
lemma drop_length (p : G.Walk u v) (n : ℕ) : (p.drop n).length = p.length - n := by
  induction p generalizing n with
  | nil => simp [drop]
  | cons => cases n <;> simp_all [drop]

@[simp]
lemma drop_getVert (p : G.Walk u v) (n m : ℕ) : (p.drop n).getVert m = p.getVert (n + m) := by
  induction p generalizing n with
  | nil => simp [drop]
  | cons => cases n <;> simp_all [drop, Nat.add_right_comm]

/-- The second vertex of a walk, or the only vertex in a nil walk. -/
abbrev snd (p : G.Walk u v) : V := p.getVert 1

@[simp] lemma adj_snd {p : G.Walk v w} (hp : ¬ p.Nil) :
    G.Adj v p.snd := by
  simpa using adj_getVert_succ p (by simpa [not_nil_iff_lt_length] using hp : 0 < p.length)

lemma snd_cons {u v w} (q : G.Walk v w) (hadj : G.Adj u v) :
    (q.cons hadj).snd = v := by simp

/-- The walk obtained by taking the first `n` darts of a walk. -/
def take {u v : V} (p : G.Walk u v) (n : ℕ) : G.Walk u (p.getVert n) :=
  match p, n with
  | .nil, _ => .nil
  | p, 0 => nil.copy rfl (getVert_zero p).symm
  | .cons h q, (n + 1) => .cons h (q.take n)

@[simp]
lemma take_length (p : G.Walk u v) (n : ℕ) : (p.take n).length = n ⊓ p.length := by
  induction p generalizing n with
  | nil => simp [take]
  | cons => cases n <;> simp_all [take]

@[simp]
lemma take_getVert (p : G.Walk u v) (n m : ℕ) : (p.take n).getVert m = p.getVert (n ⊓ m) := by
  induction p generalizing n m with
  | nil => simp [take]
  | cons => cases n <;> cases m <;> simp_all [take]

lemma take_support_eq_support_take_succ {u v} (p : G.Walk u v) (n : ℕ) :
    (p.take n).support = p.support.take (n + 1) := by
  induction p generalizing n with
  | nil => simp [take]
  | cons => cases n <;> simp_all [take]

/-- The penultimate vertex of a walk, or the only vertex in a nil walk. -/
abbrev penultimate (p : G.Walk u v) : V := p.getVert (p.length - 1)

@[simp]
lemma penultimate_nil : (@nil _ G v).penultimate = v := rfl

@[simp]
lemma penultimate_cons_nil (h : G.Adj u v) : (cons h nil).penultimate = u := rfl

@[simp]
lemma penultimate_cons_cons {w'} (h : G.Adj u v) (h₂ : G.Adj v w) (p : G.Walk w w') :
    (cons h (cons h₂ p)).penultimate = (cons h₂ p).penultimate := rfl

lemma penultimate_cons_of_not_nil (h : G.Adj u v) (p : G.Walk v w) (hp : ¬ p.Nil) :
    (cons h p).penultimate = p.penultimate :=
  p.notNilRec (by simp) hp h

@[simp]
lemma penultimate_concat {t u v} (p : G.Walk u v) (h : G.Adj v t) :
    (p.concat h).penultimate = v := by simp [penultimate, concat_eq_append, getVert_append]

@[simp]
lemma adj_penultimate {p : G.Walk v w} (hp : ¬ p.Nil) :
    G.Adj p.penultimate w := by
  conv => rhs; rw [← getVert_length p]
  rw [nil_iff_length_eq] at hp
  convert adj_getVert_succ _ _ <;> omega

@[simp]
lemma snd_reverse (p : G.Walk u v) : p.reverse.snd = p.penultimate := by
  simpa using getVert_reverse p 1

@[simp]
lemma penultimate_reverse (p : G.Walk u v) : p.reverse.penultimate = p.snd := by
  cases p <;> simp [snd, penultimate, getVert_append]

/-- The walk obtained by removing the first dart of a walk. A nil walk stays nil. -/
def tail (p : G.Walk u v) : G.Walk (p.snd) v := p.drop 1

lemma drop_zero {u v} (p : G.Walk u v) :
    p.drop 0 = p.copy (getVert_zero p).symm rfl := by
  cases p <;> simp [Walk.drop]

lemma drop_support_eq_support_drop_min {u v} (p : G.Walk u v) (n : ℕ) :
    (p.drop n).support = p.support.drop (n ⊓ p.length) := by
  induction p generalizing n with
  | nil => simp [drop]
  | cons => cases n <;> simp_all [drop]

/-- The walk obtained by removing the last dart of a walk. A nil walk stays nil. -/
def dropLast (p : G.Walk u v) : G.Walk u p.penultimate := p.take (p.length - 1)

@[simp]
lemma tail_nil : (@nil _ G v).tail = .nil := rfl

@[simp]
lemma tail_cons_nil (h : G.Adj u v) : (Walk.cons h .nil).tail = .nil := rfl

@[simp]
lemma tail_cons (h : G.Adj u v) (p : G.Walk v w) :
    (p.cons h).tail = p.copy (getVert_zero p).symm rfl := by
  match p with
  | .nil => rfl
  | .cons h q => rfl

@[deprecated (since := "2025-08-19")] alias tail_cons_eq := tail_cons

@[simp]
lemma dropLast_nil : (@nil _ G v).dropLast = nil := rfl

@[simp]
lemma dropLast_cons_nil (h : G.Adj u v) : (cons h nil).dropLast = nil := rfl

@[simp]
lemma dropLast_cons_cons {w'} (h : G.Adj u v) (h₂ : G.Adj v w) (p : G.Walk w w') :
    (cons h (cons h₂ p)).dropLast = cons h (cons h₂ p).dropLast := rfl

lemma dropLast_cons_of_not_nil (h : G.Adj u v) (p : G.Walk v w) (hp : ¬ p.Nil) :
    (cons h p).dropLast = cons h (p.dropLast.copy rfl (penultimate_cons_of_not_nil _ _ hp).symm) :=
  p.notNilRec (by simp) hp h

@[simp]
lemma dropLast_concat {t u v} (p : G.Walk u v) (h : G.Adj v t) :
    (p.concat h).dropLast = p.copy rfl (by simp) := by
  induction p
  · rfl
  · simp_rw [concat_cons]
    rw [dropLast_cons_of_not_nil]
    · simp [*]
    · simp [concat, nil_iff_length_eq]

/-- The first dart of a walk. -/
@[simps]
def firstDart (p : G.Walk v w) (hp : ¬ p.Nil) : G.Dart where
  fst := v
  snd := p.snd
  adj := p.adj_snd hp

/-- The last dart of a walk. -/
@[simps]
def lastDart (p : G.Walk v w) (hp : ¬ p.Nil) : G.Dart where
  fst := p.penultimate
  snd := w
  adj := p.adj_penultimate hp

lemma edge_firstDart (p : G.Walk v w) (hp : ¬ p.Nil) :
    (p.firstDart hp).edge = s(v, p.snd) := rfl

lemma edge_lastDart (p : G.Walk v w) (hp : ¬ p.Nil) :
    (p.lastDart hp).edge = s(p.penultimate, w) := rfl

lemma cons_tail_eq (p : G.Walk u v) (hp : ¬ p.Nil) :
    cons (p.adj_snd hp) p.tail = p := by
  cases p with
  | nil => simp at hp
  | cons h q =>
    simp only [getVert_cons_succ, tail_cons, cons_copy, copy_rfl_rfl]

@[simp]
lemma concat_dropLast (p : G.Walk u v) (hp : G.Adj p.penultimate v) :
    p.dropLast.concat hp = p := by
  induction p with
  | nil => simp at hp
  | cons hadj p hind =>
    cases p with
    | nil => rfl
    | _ => simp [hind]

@[simp] lemma cons_support_tail (p : G.Walk u v) (hp : ¬p.Nil) :
    u :: p.tail.support = p.support := by
  rw [← support_cons (p.adj_snd hp), cons_tail_eq _ hp]

@[simp] lemma length_tail_add_one {p : G.Walk u v} (hp : ¬ p.Nil) :
    p.tail.length + 1 = p.length := by
  rw [← length_cons (p.adj_snd hp), cons_tail_eq _ hp]

protected lemma Nil.tail {p : G.Walk v w} (hp : p.Nil) : p.tail.Nil := by cases p <;> aesop

lemma not_nil_of_tail_not_nil {p : G.Walk v w} (hp : ¬ p.tail.Nil) : ¬ p.Nil := mt Nil.tail hp

@[simp] lemma support_tail (p : G.Walk u u) (hp : ¬ p.Nil) :
    p.tail.support = p.support.tail := by
  rw [← cons_support_tail p hp, List.tail_cons]

lemma support_tail_of_not_nil (p : G.Walk u v) (hnp : ¬p.Nil) :
    p.tail.support = p.support.tail := by
  match p with
  | .nil => simp only [nil_nil, not_true_eq_false] at hnp
  | .cons h q =>
    simp only [tail_cons, getVert_cons_succ, support_copy, support_cons, List.tail_cons]

@[simp] lemma getVert_copy {u v w x : V} (p : G.Walk u v) (i : ℕ) (h : u = w) (h' : v = x) :
    (p.copy h h').getVert i = p.getVert i := by
  subst_vars
  rfl

@[simp] lemma getVert_tail {u v n} (p : G.Walk u v) :
    p.tail.getVert n = p.getVert (n + 1) := by
  match p with
  | .nil => rfl
  | .cons h q =>
    simp only [getVert_cons_succ, tail_cons]
    exact getVert_copy q n (getVert_zero q).symm rfl

lemma ext_getVert_le_length {u v} {p q : G.Walk u v} (hl : p.length = q.length)
    (h : ∀ k ≤ p.length, p.getVert k = q.getVert k) :
    p = q := by
  suffices ∀ k : ℕ, p.support[k]? = q.support[k]? by
    exact ext_support <| List.ext_getElem?_iff.mpr this
  intro k
  cases le_or_gt k p.length with
  | inl hk =>
    rw [← getVert_eq_support_getElem? p hk, ← getVert_eq_support_getElem? q (hl ▸ hk)]
    exact congrArg some (h k hk)
  | inr hk =>
    replace hk : p.length + 1 ≤ k := hk
    have ht : q.length + 1 ≤ k := hl ▸ hk
    rw [← length_support, ← List.getElem?_eq_none_iff] at hk ht
    rw [hk, ht]

lemma ext_getVert {u v} {p q : G.Walk u v} (h : ∀ k, p.getVert k = q.getVert k) :
    p = q := by
  wlog hpq : p.length ≤ q.length generalizing p q
  · exact (this (fun k ↦ (h k).symm) (le_of_not_ge hpq)).symm
  have : q.length ≤ p.length := by
    by_contra!
    exact (q.adj_getVert_succ this).ne (by simp [← h, getVert_of_length_le])
  exact ext_getVert_le_length (hpq.antisymm this) fun k _ ↦ h k

theorem isSubwalk_iff_support_isInfix {v w v' w' : V} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'} :
    p₁.IsSubwalk p₂ ↔ p₁.support <:+: p₂.support := by
  refine ⟨fun ⟨ru, rv, h⟩ ↦ ?_, fun ⟨s, t, h⟩ ↦ ?_⟩
  · grind [support_append, support_append_eq_support_dropLast_append]
  · have : (s.length + p₁.length) ≤ p₂.length := by grind [_=_ length_support]
    have h₁ : p₂.getVert s.length = v := by
      simp [p₂.getVert_eq_support_getElem (by cutsat : s.length ≤ p₂.length), ← h, List.getElem_zero]
    have h₂ : p₂.getVert (s.length + p₁.length) = w := by
      simp [p₂.getVert_eq_support_getElem (by omega), ← h,
        ← p₁.getVert_eq_support_getElem (Nat.le_refl _)]
    refine ⟨p₂.take s.length |>.copy rfl h₁, p₂.drop (s.length + p₁.length) |>.copy h₂ rfl, ?_⟩
    apply ext_support
    simp only [← h, support_append, support_copy, take_support_eq_support_take_succ,
      List.take_append, drop_support_eq_support_drop_min, List.tail_drop]
    rw [Nat.min_eq_left (by grind [length_support]), List.drop_append, List.drop_append,
      List.drop_eq_nil_of_le (by cutsat), List.drop_eq_nil_of_le (by grind [length_support]),
      p₁.support_eq_cons]
    simp +arith

lemma isSubwalk_antisymm {u v} {p₁ p₂ : G.Walk u v} (h₁ : p₁.IsSubwalk p₂) (h₂ : p₂.IsSubwalk p₁) :
    p₁ = p₂ := by
  rw [isSubwalk_iff_support_isInfix] at h₁ h₂
  exact ext_support <| List.infix_antisymm h₁ h₂

end Walk

end SimpleGraph
