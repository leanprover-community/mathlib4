/-
Copyright (c) 2026 Ezequiel Souza dos Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezequiel Souza dos Santos
-/
module

public import Mathlib.Geometry.Group.Grigorchuk.Superpolynomial

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List

/-!
# Intermediate growth of the Grigorchuk group

The Grigorchuk group has subexponential growth, and therefore intermediate growth.
The argument follows Grigorchuk's original papers: restriction to the eight subtrees
of level 3 contracts word lengths by a factor of `5/6`, up to an additive constant.
Iterating the resulting bound on the exponential growth rate forces that rate to be `1`.
Combined with superpolynomial growth, this yields intermediate growth.

## Main definitions

* `Grigorchuk.restrictSt`: restriction of an element of `st (n + 1)` to a child subtree.
* `Grigorchuk.chi`: the eight sections of an element of `st 3`.

## Main results

* `Grigorchuk.chi_wordLength_sum_le`: the sum of the eight section lengths is at most
  `(5/6) ℓ(h) + 8`.
* `Grigorchuk.hasSubexponentialGrowth`: `G` has subexponential growth.
* `Grigorchuk.hasIntermediateGrowth`: `G` has intermediate growth.

## References

The construction and growth estimates follow
Grigorchuk, *On the Milnor problem of group growth*, Soviet Math. Dokl. 28 (1983),
and Grigorchuk, *Degrees of growth of finitely generated groups and the theory of
invariant means*, Izv. Akad. Nauk SSSR Ser. Mat. 48 (1984).
The cancellation estimate is arranged as in Grigorchuk–Pak,
*Groups of intermediate growth: an introduction*.

## Tags

Grigorchuk group, intermediate growth, subexponential growth, geometric group theory
-/

set_option linter.style.longFile 1700

@[expose] public section

open InfiniteBinaryTree InfiniteBinaryTree.TreeAut Function Set
open scoped BigOperators Growth

namespace Grigorchuk

/-! ### Stabilizers and restriction at deeper levels -/

lemma mem_stabilizerLevel_of_le {m n : ℕ} (hmn : n ≤ m) {f : TreeAut}
    (hf : f ∈ stabilizerLevel m) : f ∈ stabilizerLevel n := by
  intro v hv
  exact apply_eq_of_mem_stabilizerLevel hf (hv ▸ hmn)

lemma st_anti {m n : ℕ} (hmn : n ≤ m) : st m ≤ st n := by
  intro g hg
  exact mem_stabilizerLevel_of_le hmn hg

lemma mem_st_of_le {m n : ℕ} (hmn : n ≤ m) {g : G} (hg : g ∈ st m) : g ∈ st n :=
  st_anti hmn hg

lemma restrict_mem_stabilizerLevel {n : ℕ} {f : TreeAut}
    (hf : f ∈ stabilizerLevel (n + 1)) (i : Fin 2) :
    restrict f i ∈ stabilizerLevel n := by
  intro v hv
  have hfix : f (i :: v) = i :: v := hf (i :: v) (by simp [hv])
  simpa [TreeAut.restrict_apply] using congrArg List.tail hfix

/-- An element of `st n` viewed as an element of the larger stabilizer `st 1`. -/
noncomputable def asSt1 {n : ℕ} (hn : 1 ≤ n) (h : st n) : st 1 :=
  ⟨h.1, mem_st_of_le hn h.2⟩

lemma restrict_mem_G_st_succ {n : ℕ} (h : st (n + 1)) (i : Fin 2) :
    restrict (h : TreeAut) i ∈ G :=
  restrict_mem_G (asSt1 (Nat.le_add_left 1 n) h) i

/-- Restriction of an element of `st (n + 1)` to the subtree of the child `i`. -/
noncomputable def restrictSt {n : ℕ} (h : st (n + 1)) (i : Fin 2) : st n :=
  ⟨⟨restrict (h : TreeAut) i, restrict_mem_G_st_succ h i⟩,
    restrict_mem_stabilizerLevel h.property i⟩

lemma apply_cons_st {n : ℕ} (h : st (n + 1)) (i : Fin 2) (w : InfiniteBinaryTree) :
    (h : TreeAut) (i :: w) = i :: restrict (h : TreeAut) i w :=
  apply_cons_of_mem_stabilizerLevel_one
    (mem_stabilizerLevel_of_le (Nat.le_add_left 1 n) h.property) i w

/-- The eight sections of an element of `st 3`. -/
noncomputable def chi (h : st 3) (i j k : Fin 2) : G :=
  restrictSt (restrictSt (restrictSt h i) j) k

lemma chi_apply (h : st 3) (i j k : Fin 2) (w : InfiniteBinaryTree) :
    (h : TreeAut) (i :: j :: k :: w) = i :: j :: k :: (chi h i j k : TreeAut) w := by
  rw [apply_cons_st h i]
  change i :: (restrictSt h i : TreeAut) (j :: k :: w) = _
  rw [apply_cons_st (restrictSt h i) j]
  change i :: j :: (restrictSt (restrictSt h i) j : TreeAut) (k :: w) = _
  rw [apply_cons_st (restrictSt (restrictSt h i) j) k]
  rfl

lemma chi_injective {h₁ h₂ : st 3}
    (heq : ∀ i j k : Fin 2, chi h₁ i j k = chi h₂ i j k) : h₁ = h₂ := by
  apply Subtype.ext
  apply Subtype.ext
  apply TreeAut.ext
  intro v
  match v with
  | [] => simp [map_root]
  | [i] =>
    have h1 : (h₁ : TreeAut) ∈ stabilizerLevel 1 :=
      mem_stabilizerLevel_of_le (by decide : (1 : ℕ) ≤ 3) h₁.property
    have h2 : (h₂ : TreeAut) ∈ stabilizerLevel 1 :=
      mem_stabilizerLevel_of_le (by decide : (1 : ℕ) ≤ 3) h₂.property
    exact (h1 [i] (by simp)).trans (h2 [i] (by simp)).symm
  | [i, j] =>
    have h1 : (h₁ : TreeAut) ∈ stabilizerLevel 2 :=
      mem_stabilizerLevel_of_le (by decide : (2 : ℕ) ≤ 3) h₁.property
    have h2 : (h₂ : TreeAut) ∈ stabilizerLevel 2 :=
      mem_stabilizerLevel_of_le (by decide : (2 : ℕ) ≤ 3) h₂.property
    exact (h1 [i, j] (by simp)).trans (h2 [i, j] (by simp)).symm
  | [i, j, k] =>
    exact (h₁.property [i, j, k] (by simp)).trans (h₂.property [i, j, k] (by simp)).symm
  | i :: j :: k :: w =>
    rw [chi_apply, chi_apply, heq]

/-! ### Reduced words in `{a,b,c,d}` -/

/-- Letters `0,1,2,3` stand for the generators `a,b,c,d`. -/
def gen (i : Fin 4) : G := generator i

lemma gen_mul_self (i : Fin 4) : gen i * gen i = 1 := by
  fin_cases i <;> apply Subtype.ext
  · exact a_mul_self
  · exact b_mul_self
  · exact c_mul_self
  · exact d_mul_self

lemma gen_inv (i : Fin 4) : (gen i)⁻¹ = gen i :=
  inv_eq_of_mul_eq_one_right (gen_mul_self i)

lemma gen_wordLength_le (i : Fin 4) : gens.wordLength (gen i) ≤ 1 := by
  have : gens.wordProd [(i, true)] = gen i := by
    simp [gen, gens, generator, Group.Generators.wordProd_singleton]
  exact this ▸ gens.wordLength_wordProd_le [(i, true)]

lemma b_mul_d_eq_c : (b * d : TreeAut) = c := by
  rw [← bc_eq_d, ← mul_assoc, b_mul_self, one_mul]

lemma c_mul_b_eq_d : (c * b : TreeAut) = d := by
  calc
    c * b = (c * b) * (c * c) := by rw [c_mul_self, mul_one]
    _ = c * (b * c) * c := by simp only [mul_assoc]
    _ = c * d * c := by rw [bc_eq_d]
    _ = (c * d) * c := by rw [mul_assoc]
    _ = b * c := by rw [cd_eq_b]
    _ = d := bc_eq_d

lemma d_mul_c_eq_b : (d * c : TreeAut) = b := by
  rw [← bc_eq_d, mul_assoc, c_mul_self, mul_one]

lemma gen_mul_wordLength_le (i j : Fin 4) (h : (i = 0) ↔ (j = 0)) :
    gens.wordLength (gen i * gen j) ≤ 1 := by
  have hone : gens.wordLength (1 : G) ≤ 1 := by simp
  by_cases hi : i = 0
  · have hj : j = 0 := h.mp hi
    simp [hi, hj, gen_mul_self]
  · have hj : j ≠ 0 := fun hj ↦ hi (h.mpr hj)
    fin_cases i
    · exact (hi rfl).elim
    · fin_cases j
      · exact (hj rfl).elim
      · simp [gen_mul_self]
      · convert gen_wordLength_le (3 : Fin 4)
        exact Subtype.ext bc_eq_d
      · convert gen_wordLength_le (2 : Fin 4)
        exact Subtype.ext b_mul_d_eq_c
    · fin_cases j
      · exact (hj rfl).elim
      · convert gen_wordLength_le (3 : Fin 4)
        exact Subtype.ext c_mul_b_eq_d
      · simp [gen_mul_self]
      · convert gen_wordLength_le (1 : Fin 4)
        exact Subtype.ext cd_eq_b
    · fin_cases j
      · exact (hj rfl).elim
      · convert gen_wordLength_le (2 : Fin 4)
        exact Subtype.ext db_eq_c
      · convert gen_wordLength_le (1 : Fin 4)
        exact Subtype.ext d_mul_c_eq_b
      · simp [gen_mul_self]

/-- The product in `G` of a word in the letters `a,b,c,d`. -/
def ofLetters (w : List (Fin 4)) : G := (w.map gen).prod

lemma ofLetters_nil : ofLetters [] = 1 := by simp [ofLetters]

lemma ofLetters_cons (i : Fin 4) (w : List (Fin 4)) :
    ofLetters (i :: w) = gen i * ofLetters w := by
  simp [ofLetters]

lemma ofLetters_append (u v : List (Fin 4)) :
    ofLetters (u ++ v) = ofLetters u * ofLetters v := by
  simp [ofLetters]

lemma gens_val_inv (i : Fin 4) : (gens.val i)⁻¹ = gens.val i :=
  gen_inv i

lemma wordProd_eq_ofLetters (l : List (Fin 4 × Bool)) :
    gens.wordProd l = ofLetters (l.map Prod.fst) := by
  induction l with
  | nil => simp [ofLetters]
  | cons p l ih =>
    rcases p with ⟨i, b⟩
    have hcond : cond b (gens.val i) (gens.val i)⁻¹ = gen i := by
      cases b
      · change (gens.val i)⁻¹ = gen i
        simpa [gens, generator, gen] using gen_inv i
      · simp [gens, generator, gen]
    rw [Group.Generators.wordProd_cons, ih, List.map_cons, ofLetters_cons, hcond]

lemma ofLetters_wordLength_le (w : List (Fin 4)) :
    gens.wordLength (ofLetters w) ≤ w.length := by
  have h : gens.wordProd (w.map fun i ↦ (i, true)) = ofLetters w := by
    rw [wordProd_eq_ofLetters, List.map_map]
    simp [Function.comp_def]
  exact h ▸ (gens.wordLength_wordProd_le _).trans_eq (by simp)

/-- A word is reduced if it alternates between `a` and `{b,c,d}`. -/
def IsReduced (w : List (Fin 4)) : Prop :=
  w.IsChain fun x y ↦ (x = 0) ≠ (y = 0)

lemma ofLetters_take_drop (w : List (Fin 4)) (n : ℕ) (hn : n + 1 < w.length) :
    ofLetters w = ofLetters (w.take n) * gen w[n] * gen w[n + 1] *
      ofLetters (w.drop (n + 2)) := by
  have hdrop : w.drop n = w[n] :: w.drop (n + 1) :=
    List.drop_eq_getElem_cons (Nat.lt_of_succ_lt hn)
  have hdrop2 : w.drop (n + 1) = w[n + 1] :: w.drop (n + 2) :=
    List.drop_eq_getElem_cons hn
  calc
    ofLetters w = ofLetters (w.take n ++ w.drop n) := by rw [List.take_append_drop]
    _ = ofLetters (w.take n) * ofLetters (w.drop n) := ofLetters_append _ _
    _ = ofLetters (w.take n) * ofLetters (w[n] :: w[n + 1] :: w.drop (n + 2)) := by
        rw [hdrop, hdrop2]
    _ = ofLetters (w.take n) * (gen w[n] * (gen w[n + 1] * ofLetters (w.drop (n + 2)))) := by
        rw [ofLetters_cons, ofLetters_cons]
    _ = ofLetters (w.take n) * gen w[n] * gen w[n + 1] * ofLetters (w.drop (n + 2)) := by
        simp [mul_assoc]

lemma geodesic_isReduced (l : List (Fin 4 × Bool)) (hl : gens.IsGeodesic l) :
    IsReduced (l.map Prod.fst) := by
  by_contra h
  obtain ⟨n, hn, hR⟩ := List.exists_not_getElem_of_not_isChain h
  set w := l.map Prod.fst
  have hlen : w.length = l.length := by simp [w]
  have hprod : gens.wordProd l = ofLetters w := wordProd_eq_ofLetters l
  have hdecomp := ofLetters_take_drop w n (by simpa [w, hlen] using hn)
  have hiff : (w[n] = 0) ↔ (w[n + 1] = 0) := by
    have : ¬ ((w[n] = 0) ≠ (w[n + 1] = 0)) := by
      simpa [w, List.getElem_map] using hR
    exact eq_iff_iff.mp (not_ne_iff.mp this)
  have hℓ : gens.wordLength (gen w[n] * gen w[n + 1]) ≤ 1 :=
    gen_mul_wordLength_le _ _ hiff
  have htake : gens.wordLength (ofLetters (w.take n)) ≤ n :=
    (ofLetters_wordLength_le _).trans (by simp [List.length_take])
  have hdrop : gens.wordLength (ofLetters (w.drop (n + 2))) ≤ w.length - (n + 2) :=
    (ofLetters_wordLength_le _).trans (by simp [List.length_drop])
  have hshort : gens.wordLength (ofLetters w) ≤ w.length - 1 := by
    calc
      gens.wordLength (ofLetters w)
          = gens.wordLength
              (ofLetters (w.take n) * (gen w[n] * gen w[n + 1] *
                ofLetters (w.drop (n + 2)))) := by
            rw [hdecomp]; simp [mul_assoc]
      _ ≤ gens.wordLength (ofLetters (w.take n)) +
            gens.wordLength (gen w[n] * gen w[n + 1] *
              ofLetters (w.drop (n + 2))) :=
          gens.wordLength_mul_le _ _
      _ ≤ gens.wordLength (ofLetters (w.take n)) +
            (gens.wordLength (gen w[n] * gen w[n + 1]) +
              gens.wordLength (ofLetters (w.drop (n + 2)))) :=
          Nat.add_le_add_left (gens.wordLength_mul_le _ _) _
      _ ≤ n + (1 + (w.length - (n + 2))) :=
          Nat.add_le_add htake (Nat.add_le_add hℓ hdrop)
      _ = w.length - 1 := by omega
  have hgeo : gens.wordLength (ofLetters w) = w.length :=
    (congrArg gens.wordLength hprod).symm.trans (hl.trans hlen.symm)
  omega

lemma count_sum (w : List (Fin 4)) :
    w.count 0 + w.count 1 + w.count 2 + w.count 3 = w.length := by
  induction w with
  | nil => simp
  | cons i t ih =>
    fin_cases i <;> simp <;> omega

lemma bcd_count (w : List (Fin 4)) (hr : IsReduced w) :
    w.count 1 + w.count 2 + w.count 3 =
      if w.head?.any (· ≠ 0) then (w.length + 1) / 2 else w.length / 2 := by
  induction w with
  | nil => simp
  | cons x t ih =>
    cases t with
    | nil =>
      fin_cases x <;> simp
    | cons y s =>
      have hr' : IsReduced (y :: s) := (List.isChain_cons_cons.mp hr).2
      have hxy : (x = 0) ≠ (y = 0) := (List.isChain_cons_cons.mp hr).1
      have ih' := ih hr'
      by_cases hx : x = 0
      · have hy : y ≠ 0 := fun hy ↦ hxy (by simp [hx, hy])
        have hhead : (y :: s).head?.any (· ≠ 0) = true := by simp [hy]
        have hcnt : (x :: y :: s).count 1 + (x :: y :: s).count 2 + (x :: y :: s).count 3 =
            (y :: s).count 1 + (y :: s).count 2 + (y :: s).count 3 := by
          simp [List.count_cons, hx]
        have hheadx : (x :: y :: s).head?.any (· ≠ 0) = false := by simp [hx]
        rw [hcnt, ih', hhead, hheadx]
        simp [List.length_cons]
      · have hy : y = 0 := by
          by_contra hy
          exact hxy (by simp [hx, hy])
        have hhead : (y :: s).head?.any (· ≠ 0) = false := by simp [hy]
        have hcnt : (x :: y :: s).count 1 + (x :: y :: s).count 2 + (x :: y :: s).count 3 =
            1 + ((y :: s).count 1 + (y :: s).count 2 + (y :: s).count 3) := by
          fin_cases x
          · exact (hx rfl).elim
          · simp [hy]; omega
          · simp [hy]; omega
          · simp [hy]; omega
        have hheadx : (x :: y :: s).head?.any (· ≠ 0) = true := by simp [hx]
        rw [hcnt, ih', hhead, hheadx]
        simp [List.length_cons]
        omega

lemma bcd_count_ge (w : List (Fin 4)) (hr : IsReduced w) :
    (w.length - 1) / 2 ≤ w.count 1 + w.count 2 + w.count 3 := by
  have := bcd_count w hr
  split_ifs at this <;> omega

lemma max_bcd_ge (w : List (Fin 4)) :
    (w.count 1 + w.count 2 + w.count 3) / 3 ≤ w.count 1 ⊔ w.count 2 ⊔ w.count 3 := by
  have : w.count 1 + w.count 2 + w.count 3 ≤
      3 * (w.count 1 ⊔ w.count 2 ⊔ w.count 3) := by
    have h1 : w.count 1 ≤ w.count 1 ⊔ w.count 2 ⊔ w.count 3 :=
      le_sup_of_le_left le_sup_left
    have h2 : w.count 2 ≤ w.count 1 ⊔ w.count 2 ⊔ w.count 3 :=
      le_sup_of_le_left le_sup_right
    have h3 : w.count 3 ≤ w.count 1 ⊔ w.count 2 ⊔ w.count 3 := le_sup_right
    omega
  exact Nat.div_le_of_le_mul this

/-! ### Section rewriting -/

/-- Image of a letter on the two sections, given the current swap bit. -/
def push (σ : Fin 2) (i : Fin 4) : Fin 2 × List (Fin 4) × List (Fin 4) :=
  if i = 0 then
    (σ + 1, [], [])
  else if i = 1 then
    (σ, if σ = 0 then ([0], [2]) else ([2], [0]))
  else if i = 2 then
    (σ, if σ = 0 then ([0], [3]) else ([3], [0]))
  else
    (σ, if σ = 0 then ([], [1]) else ([1], []))

/-- Recursive first-level section words, tracking the current swap bit `σ`. -/
def sectionWordsAux (σ : Fin 2) : List (Fin 4) → List (Fin 4) × List (Fin 4)
  | [] => ([], [])
  | i :: t =>
    let p := push σ i
    let q := sectionWordsAux p.1 t
    (p.2.1 ++ q.1, p.2.2 ++ q.2)

/-- The two first-level (unreduced) section words of a word in `a,b,c,d`. -/
def sectionWords (w : List (Fin 4)) : List (Fin 4) × List (Fin 4) :=
  sectionWordsAux 0 w

lemma sectionWordsAux_length (σ : Fin 2) :
    ∀ w : List (Fin 4),
      (sectionWordsAux σ w).1.length + (sectionWordsAux σ w).2.length =
        2 * w.count 1 + 2 * w.count 2 + w.count 3
  | [] => by simp [sectionWordsAux]
  | i :: t => by
    have ih := sectionWordsAux_length (push σ i).1 t
    fin_cases i <;> fin_cases σ <;> simp [sectionWordsAux, push] at ih ⊢ <;> omega

lemma sectionWords_length (w : List (Fin 4)) :
    (sectionWords w).1.length + (sectionWords w).2.length =
      2 * w.count 1 + 2 * w.count 2 + w.count 3 :=
  sectionWordsAux_length 0 w

lemma sectionWords_length_le_of_reduced (w : List (Fin 4)) (hr : IsReduced w) :
    (sectionWords w).1.length + (sectionWords w).2.length ≤
      w.length + 1 - w.count 3 := by
  have hlen := sectionWords_length w
  have hbcd : w.count 1 + w.count 2 + w.count 3 ≤ (w.length + 1) / 2 := by
    rw [bcd_count w hr]
    split_ifs <;> omega
  have : 2 * (w.count 1 + w.count 2 + w.count 3) ≤ w.length + 1 :=
    (Nat.mul_le_mul_left 2 hbcd).trans (by omega)
  omega

/-! ### Wreath decomposition of words -/

lemma ofLetters_singleton (i : Fin 4) : ofLetters [i] = gen i := by
  simp [ofLetters_cons, ofLetters_nil]

/-- Current leftover `a` while reading a word from the left. -/
def swapBit (σ : Fin 2) : TreeAut := if σ = 0 then 1 else a

lemma swapBit_zero : swapBit 0 = 1 := rfl

lemma swapBit_one : swapBit 1 = a := rfl

lemma swapBit_mul_self (σ : Fin 2) : swapBit σ * swapBit σ = 1 := by
  fin_cases σ
  · simp [swapBit]
  · simp [swapBit]

lemma coe_gen_zero : (gen 0 : TreeAut) = a := rfl
lemma coe_gen_one : (gen 1 : TreeAut) = b := rfl
lemma coe_gen_two : (gen 2 : TreeAut) = c := rfl
lemma coe_gen_three : (gen 3 : TreeAut) = d := rfl

/-- The swap bit remaining after rewriting a word through the wreath product. -/
def finalSigma (σ : Fin 2) : List (Fin 4) → Fin 2
  | [] => σ
  | i :: t => finalSigma (push σ i).1 t

set_option linter.flexible false in
lemma push_wreath (σ : Fin 2) (i : Fin 4) :
    swapBit σ * (gen i : TreeAut) * swapBit (push σ i).1 =
      phi (ofLetters (push σ i).2.1 : TreeAut) (ofLetters (push σ i).2.2 : TreeAut) := by
  fin_cases i <;> fin_cases σ
  · simp [push, swapBit, ofLetters_nil, phi_one, coe_gen_zero]
  · simp [push, swapBit, ofLetters_nil, phi_one, coe_gen_zero]
  · simp [push, swapBit, ofLetters_singleton, coe_gen_one, coe_gen_zero, coe_gen_two]
    exact b_eq_phi
  · simp [push, swapBit, ofLetters_singleton, coe_gen_one, coe_gen_zero, coe_gen_two]
    exact a_mul_b_mul_a_eq_phi
  · simp [push, swapBit, ofLetters_singleton, coe_gen_two, coe_gen_zero, coe_gen_three]
    exact c_eq_phi
  · simp [push, swapBit, ofLetters_singleton, coe_gen_two, coe_gen_zero, coe_gen_three]
    exact a_mul_c_mul_a_eq_phi
  · simp [push, swapBit, ofLetters_singleton, ofLetters_nil, coe_gen_three, coe_gen_one]
    exact d_eq_phi
  · simp [push, swapBit, ofLetters_singleton, ofLetters_nil, coe_gen_three, coe_gen_one]
    exact a_mul_d_mul_a_eq_phi

lemma coe_ofLetters_mul (u v : List (Fin 4)) :
    (ofLetters (u ++ v) : TreeAut) = (ofLetters u : TreeAut) * (ofLetters v : TreeAut) := by
  simp [ofLetters_append, Subgroup.coe_mul]

lemma sectionWordsAux_wreath (σ : Fin 2) :
    ∀ w : List (Fin 4),
      swapBit σ * (ofLetters w : TreeAut) =
        phi (ofLetters (sectionWordsAux σ w).1 : TreeAut)
            (ofLetters (sectionWordsAux σ w).2 : TreeAut) *
        swapBit (finalSigma σ w)
  | [] => by
    simp [sectionWordsAux, finalSigma, ofLetters_nil, phi_one]
  | i :: t => by
    have ih := sectionWordsAux_wreath (push σ i).1 t
    have hpush := push_wreath σ i
    have hA := swapBit_mul_self (push σ i).1
    calc
      swapBit σ * (ofLetters (i :: t) : TreeAut)
          = swapBit σ * ((gen i : TreeAut) * (ofLetters t : TreeAut)) := by
            simp [ofLetters_cons, Subgroup.coe_mul]
      _ = swapBit σ * (gen i : TreeAut) * (ofLetters t : TreeAut) := by
            simp [mul_assoc]
      _ = swapBit σ * (gen i : TreeAut) *
            (swapBit (push σ i).1 * swapBit (push σ i).1) * (ofLetters t : TreeAut) := by
            simp [hA]
      _ = (swapBit σ * (gen i : TreeAut) * swapBit (push σ i).1) *
            (swapBit (push σ i).1 * (ofLetters t : TreeAut)) := by
            simp [mul_assoc]
      _ = phi (ofLetters (push σ i).2.1 : TreeAut) (ofLetters (push σ i).2.2 : TreeAut) *
            (phi (ofLetters (sectionWordsAux (push σ i).1 t).1 : TreeAut)
              (ofLetters (sectionWordsAux (push σ i).1 t).2 : TreeAut) *
              swapBit (finalSigma (push σ i).1 t)) := by
            rw [hpush, ih]
      _ = phi (ofLetters ((push σ i).2.1 ++ (sectionWordsAux (push σ i).1 t).1) : TreeAut)
            (ofLetters ((push σ i).2.2 ++ (sectionWordsAux (push σ i).1 t).2) : TreeAut) *
          swapBit (finalSigma σ (i :: t)) := by
            simp [phi_mul, coe_ofLetters_mul, finalSigma, mul_assoc]

lemma ofLetters_eq_phi (w : List (Fin 4)) (hw : ofLetters w ∈ st 1) :
    (ofLetters w : TreeAut) =
      phi (ofLetters (sectionWords w).1 : TreeAut)
        (ofLetters (sectionWords w).2 : TreeAut) := by
  have h := sectionWordsAux_wreath 0 w
  simp only [swapBit_zero, one_mul] at h
  have hσ : finalSigma 0 w = 0 := by
    by_contra hσ
    have h1 : finalSigma 0 w = 1 := by
      rcases fin2_eq_zero_or_one (finalSigma 0 w) with h0 | h1
      · exact (hσ h0).elim
      · exact h1
    have hact : activity (ofLetters w : TreeAut) [] = 1 := by
      have hact := congrArg (fun f : TreeAut ↦ activity f []) h
      rw [h1, swapBit_one] at hact
      calc
        activity (ofLetters w : TreeAut) []
            = activity
                (phi (ofLetters (sectionWordsAux 0 w).1 : TreeAut)
                    (ofLetters (sectionWordsAux 0 w).2 : TreeAut) *
                  a) [] := hact
        _ = activity (phi (ofLetters (sectionWordsAux 0 w).1 : TreeAut)
                (ofLetters (sectionWordsAux 0 w).2 : TreeAut)) [] +
              activity a [] := activity_mul _ _
        _ = activity (phi (ofLetters (sectionWordsAux 0 w).1 : TreeAut)
                (ofLetters (sectionWordsAux 0 w).2 : TreeAut)) root +
              activity a [] := by rw [activity_nil]
        _ = 0 + 1 := by rw [activity_phi, activity_a]
        _ = 1 := zero_add _
    have hz : activity (ofLetters w : TreeAut) [] = 0 :=
      (activity_eq_zero_iff_mem_stabilizerLevel_one).mpr (Subgroup.mem_subgroupOf.mp hw)
    exact Fin.zero_ne_one (hz.symm.trans hact)
  rw [hσ, swapBit_zero, mul_one] at h
  simpa [sectionWords] using h

lemma restrict_ofLetters (w : List (Fin 4)) (hw : ofLetters w ∈ st 1) (i : Fin 2) :
    restrict (ofLetters w : TreeAut) i =
      (ofLetters (if i = 0 then (sectionWords w).1 else (sectionWords w).2) : TreeAut) := by
  have h := ofLetters_eq_phi w hw
  rcases fin2_eq_zero_or_one i with hi | hi
  · simp [hi, h, restrict_phi_zero]
  · simp [hi, h, restrict_phi_one]

/-! ### Letter counts through three rewriting levels -/

lemma sectionWordsAux_count (σ : Fin 2) :
    ∀ w : List (Fin 4),
      ((sectionWordsAux σ w).1.count 1 + (sectionWordsAux σ w).2.count 1 = w.count 3) ∧
      ((sectionWordsAux σ w).1.count 2 + (sectionWordsAux σ w).2.count 2 = w.count 1) ∧
      ((sectionWordsAux σ w).1.count 3 + (sectionWordsAux σ w).2.count 3 = w.count 2)
  | [] => by simp [sectionWordsAux]
  | i :: t => by
    have ih := sectionWordsAux_count (push σ i).1 t
    fin_cases i <;> fin_cases σ <;> simp [sectionWordsAux, push] at ih ⊢ <;>
      omega

lemma sectionWords_count (w : List (Fin 4)) :
    (sectionWords w).1.count 1 + (sectionWords w).2.count 1 = w.count 3 ∧
    (sectionWords w).1.count 2 + (sectionWords w).2.count 2 = w.count 1 ∧
    (sectionWords w).1.count 3 + (sectionWords w).2.count 3 = w.count 2 :=
  sectionWordsAux_count 0 w

/-- Total length of the four second-level (unreduced) section words. -/
def lengthTwo (w : List (Fin 4)) : ℕ :=
  let p := sectionWords w
  (sectionWords p.1).1.length + (sectionWords p.1).2.length +
    (sectionWords p.2).1.length + (sectionWords p.2).2.length

lemma lengthTwo_eq (w : List (Fin 4)) :
    lengthTwo w = 2 * w.count 3 + 2 * w.count 1 + w.count 2 := by
  simp only [lengthTwo]
  have h1 := sectionWords_length (sectionWords w).1
  have h2 := sectionWords_length (sectionWords w).2
  have ⟨hb, hc, hd⟩ := sectionWords_count w
  omega

/-- Total length of the eight third-level (unreduced) section words. -/
def lengthThree (w : List (Fin 4)) : ℕ :=
  let p := sectionWords w
  lengthTwo p.1 + lengthTwo p.2

lemma lengthThree_eq (w : List (Fin 4)) :
    lengthThree w = w.count 1 + 2 * w.count 2 + 2 * w.count 3 := by
  simp only [lengthThree]
  rw [lengthTwo_eq, lengthTwo_eq]
  have ⟨hb, hc, hd⟩ := sectionWords_count w
  omega

lemma lengthTwo_le_of_reduced (w : List (Fin 4)) (hr : IsReduced w) :
    lengthTwo w ≤ w.length + 3 - w.count 2 := by
  have hbcd : 2 * (w.count 1 + w.count 2 + w.count 3) ≤ w.length + 1 := by
    have : w.count 1 + w.count 2 + w.count 3 ≤ (w.length + 1) / 2 := by
      rw [bcd_count w hr]
      split_ifs <;> omega
    exact (Nat.mul_le_mul_left 2 this).trans (by omega)
  rw [lengthTwo_eq]
  omega

lemma lengthThree_le_of_reduced (w : List (Fin 4)) (hr : IsReduced w) :
    lengthThree w ≤ w.length + 7 - w.count 1 := by
  have hbcd : 2 * (w.count 1 + w.count 2 + w.count 3) ≤ w.length + 1 := by
    have : w.count 1 + w.count 2 + w.count 3 ≤ (w.length + 1) / 2 := by
      rw [bcd_count w hr]
      split_ifs <;> omega
    exact (Nat.mul_le_mul_left 2 this).trans (by omega)
  rw [lengthThree_eq]
  omega

/-! ### Sections of group elements -/

lemma psi_wordLength_sum_le (h : st 1) :
    gens.wordLength (psi h).1 + gens.wordLength (psi h).2 ≤
      gens.wordLength (h : G) + 1 := by
  obtain ⟨l, hlgeo, hl⟩ := gens.exists_isGeodesic (h : G)
  have hr : IsReduced (l.map Prod.fst) := geodesic_isReduced l hlgeo
  set w := l.map Prod.fst
  have hlen : w.length = l.length := by simp [w]
  have hprod : ofLetters w = (h : G) := by
    simpa [w, wordProd_eq_ofLetters] using hl
  have hw : ofLetters w ∈ st 1 := by simp [hprod, h.property]
  have hψ : psi h = (⟨restrict (h : TreeAut) 0, restrict_mem_G h 0⟩,
      ⟨restrict (h : TreeAut) 1, restrict_mem_G h 1⟩) := rfl
  have hr0 : restrict (h : TreeAut) 0 =
      (ofLetters (sectionWords w).1 : TreeAut) := by
    simpa [hprod] using restrict_ofLetters w hw 0
  have hr1 : restrict (h : TreeAut) 1 =
      (ofLetters (sectionWords w).2 : TreeAut) := by
    simpa [hprod] using restrict_ofLetters w hw 1
  have h0 : (psi h).1 = ofLetters (sectionWords w).1 := by
    apply Subtype.ext
    simpa [hψ] using hr0
  have h1 : (psi h).2 = ofLetters (sectionWords w).2 := by
    apply Subtype.ext
    simpa [hψ] using hr1
  have hsum := sectionWords_length_le_of_reduced w hr
  have hle0 : gens.wordLength (psi h).1 ≤ (sectionWords w).1.length := by
    simpa [h0] using ofLetters_wordLength_le (sectionWords w).1
  have hle1 : gens.wordLength (psi h).2 ≤ (sectionWords w).2.length := by
    simpa [h1] using ofLetters_wordLength_le (sectionWords w).2
  have hgeo : gens.wordLength (h : G) = w.length :=
    (congrArg gens.wordLength hl).symm.trans (hlgeo.trans hlen.symm)
  omega

lemma restrictSt_wordLength_sum_le {n : ℕ} (h : st (n + 1))
    (h1 : (h : G) ∈ st 1) :
    gens.wordLength (restrictSt h 0 : G) + gens.wordLength (restrictSt h 1 : G) ≤
      gens.wordLength (h : G) + 1 := by
  let h' : st 1 := ⟨h.1, h1⟩
  have h0 : (restrictSt h 0 : G) = (psi h').1 := by
    apply Subtype.ext
    rfl
  have h1' : (restrictSt h 1 : G) = (psi h').2 := by
    apply Subtype.ext
    rfl
  simpa [h0, h1'] using psi_wordLength_sum_le h'

/-- The unreduced third-level section word in the subtree indexed by `i,j,k`. -/
def sectionWord3 (w : List (Fin 4)) (i j k : Fin 2) : List (Fin 4) :=
  let p := sectionWords w
  let u := if i = 0 then p.1 else p.2
  let q := sectionWords u
  let v := if j = 0 then q.1 else q.2
  let r := sectionWords v
  if k = 0 then r.1 else r.2

lemma chi_eq_ofLetters (h : st 3) (w : List (Fin 4))
    (hw : ofLetters w = (h : G)) (i j k : Fin 2) :
    chi h i j k = ofLetters (sectionWord3 w i j k) := by
  have hst1 : ofLetters w ∈ st 1 := by
    simpa [hw] using mem_st_of_le (by decide : (1 : ℕ) ≤ 3) h.property
  have hst2 : ofLetters w ∈ st 2 := by
    simpa [hw] using mem_st_of_le (by decide : (2 : ℕ) ≤ 3) h.property
  have ri : restrict (h : TreeAut) i =
      (ofLetters (if i = 0 then (sectionWords w).1 else (sectionWords w).2) : TreeAut) := by
    simpa [hw] using restrict_ofLetters w hst1 i
  set u := if i = 0 then (sectionWords w).1 else (sectionWords w).2
  have huG : ofLetters u ∈ st 1 :=
    (Subgroup.mem_subgroupOf).mpr (by
      have : restrict (h : TreeAut) i ∈ stabilizerLevel 1 :=
        restrict_mem_stabilizerLevel
          (mem_stabilizerLevel_of_le (by decide : (2 : ℕ) ≤ 3) h.property) i
      rwa [← ri])
  have rj : restrict (restrict (h : TreeAut) i) j =
      (ofLetters (if j = 0 then (sectionWords u).1 else (sectionWords u).2) : TreeAut) := by
    simpa [ri] using restrict_ofLetters u huG j
  set v := if j = 0 then (sectionWords u).1 else (sectionWords u).2
  have hvG : ofLetters v ∈ st 1 :=
    (Subgroup.mem_subgroupOf).mpr (by
      have : restrict (restrict (h : TreeAut) i) j ∈ stabilizerLevel 1 :=
        restrict_mem_stabilizerLevel (restrict_mem_stabilizerLevel h.property i) j
      rwa [← rj])
  have rk : restrict (restrict (restrict (h : TreeAut) i) j) k =
      (ofLetters (if k = 0 then (sectionWords v).1 else (sectionWords v).2) : TreeAut) := by
    simpa [rj] using restrict_ofLetters v hvG k
  apply Subtype.ext
  simpa [chi, restrictSt, sectionWord3, u, v] using rk

lemma sum_fin2 (f : Fin 2 → ℕ) : ∑ i : Fin 2, f i = f 0 + f 1 := by
  rw [Finset.univ_fin2, Finset.sum_insert (by decide), Finset.sum_singleton]

lemma sum_sectionWord3_length (w : List (Fin 4)) (i : Fin 2) :
    ∑ j : Fin 2, ∑ k : Fin 2, (sectionWord3 w i j k).length =
      lengthTwo (if i = 0 then (sectionWords w).1 else (sectionWords w).2) := by
  rcases fin2_eq_zero_or_one i with hi | hi <;>
    simp [hi, sectionWord3, lengthTwo, sum_fin2] <;> ring

lemma lengthThree_eq_sum (w : List (Fin 4)) :
    ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, (sectionWord3 w i j k).length = lengthThree w := by
  rw [sum_fin2, lengthThree, sum_sectionWord3_length, sum_sectionWord3_length]
  simp

lemma chi_wordLength_le_lengthThree (h : st 3) (w : List (Fin 4))
    (hw : ofLetters w = (h : G)) :
    ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, gens.wordLength (chi h i j k) ≤
      lengthThree w := by
  have bound (i j k : Fin 2) :
      gens.wordLength (chi h i j k) ≤ (sectionWord3 w i j k).length := by
    rw [chi_eq_ofLetters h w hw i j k]
    exact ofLetters_wordLength_le _
  have hsum :
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, gens.wordLength (chi h i j k) ≤
        ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, (sectionWord3 w i j k).length :=
    Finset.sum_le_sum fun _ _ ↦ Finset.sum_le_sum fun _ _ ↦
      Finset.sum_le_sum fun _ _ ↦ bound _ _ _
  rwa [lengthThree_eq_sum] at hsum

lemma sum_chi_subtree_le (h : st 3) (i : Fin 2) :
    ∑ j : Fin 2, ∑ k : Fin 2, gens.wordLength (chi h i j k) ≤
      gens.wordLength (restrictSt h i : G) + 3 := by
  have hs := restrictSt_wordLength_sum_le (restrictSt h i)
    (mem_st_of_le (by decide : (1 : ℕ) ≤ 2) (restrictSt h i).property)
  have h0 := restrictSt_wordLength_sum_le (restrictSt (restrictSt h i) 0)
    (restrictSt (restrictSt h i) 0).property
  have h1 := restrictSt_wordLength_sum_le (restrictSt (restrictSt h i) 1)
    (restrictSt (restrictSt h i) 1).property
  simp only [chi, sum_fin2] at hs h0 h1 ⊢
  omega

lemma restrictSt_wordLength_le_section (h : st 3) (w : List (Fin 4))
    (hw : ofLetters w = (h : G)) (i : Fin 2) :
    gens.wordLength (restrictSt h i : G) ≤
      (if i = 0 then (sectionWords w).1 else (sectionWords w).2).length := by
  have hst1 : ofLetters w ∈ st 1 :=
    mem_st_of_le (by decide : (1 : ℕ) ≤ 3) (by simp [hw, h.property])
  have ri := restrict_ofLetters w hst1 i
  apply le_of_eq_of_le (congrArg gens.wordLength (Subtype.ext ?_))
    (ofLetters_wordLength_le _)
  simpa [restrictSt, hw] using ri

lemma chi_wordLength_sum_le_aux (h : st 3) (w : List (Fin 4))
    (hw : ofLetters w = (h : G)) (hr : IsReduced w) :
    ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, gens.wordLength (chi h i j k) ≤
      w.length + 7 - (w.count 1 ⊔ w.count 2 ⊔ w.count 3) := by
  have h3 := (chi_wordLength_le_lengthThree h w hw).trans (lengthThree_le_of_reduced w hr)
  have h1 : ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, gens.wordLength (chi h i j k) ≤
      (sectionWords w).1.length + (sectionWords w).2.length + 6 := by
    have s0 := sum_chi_subtree_le h 0
    have s1 := sum_chi_subtree_le h 1
    have b0 := restrictSt_wordLength_le_section h w hw 0
    have b1 := restrictSt_wordLength_le_section h w hw 1
    simp [sum_fin2] at s0 s1 b0 b1 ⊢
    omega
  have hL1 := sectionWords_length_le_of_reduced w hr
  have h2 : ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, gens.wordLength (chi h i j k) ≤
      lengthTwo w + 4 := by
    have hle (i j : Fin 2) :
        gens.wordLength (chi h i j 0) + gens.wordLength (chi h i j 1) ≤
          gens.wordLength (restrictSt (restrictSt h i) j : G) + 1 := by
      simpa [chi] using
        restrictSt_wordLength_sum_le (restrictSt (restrictSt h i) j)
          (restrictSt (restrictSt h i) j).property
    have hexp :
        ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, gens.wordLength (chi h i j k) =
          ∑ i : Fin 2, ∑ j : Fin 2,
            (gens.wordLength (chi h i j 0) + gens.wordLength (chi h i j 1)) := by
      simp [sum_fin2]
    rw [hexp]
    have hsum :
        ∑ i : Fin 2, ∑ j : Fin 2,
            (gens.wordLength (chi h i j 0) + gens.wordLength (chi h i j 1)) ≤
          ∑ i : Fin 2, ∑ j : Fin 2,
            (gens.wordLength (restrictSt (restrictSt h i) j : G) + 1) :=
      Finset.sum_le_sum fun _ _ ↦ Finset.sum_le_sum fun _ _ ↦ hle _ _
    have bound (i j : Fin 2) :
        gens.wordLength (restrictSt (restrictSt h i) j : G) ≤
          (let u := if i = 0 then (sectionWords w).1 else (sectionWords w).2
            if j = 0 then (sectionWords u).1 else (sectionWords u).2).length := by
      set u := if i = 0 then (sectionWords w).1 else (sectionWords w).2
      set v := if j = 0 then (sectionWords u).1 else (sectionWords u).2
      have hst1 : ofLetters w ∈ st 1 :=
        mem_st_of_le (by decide : (1 : ℕ) ≤ 3) (by simp [hw, h.property])
      have ri : restrict (h : TreeAut) i = (ofLetters u : TreeAut) := by
        simpa [hw, u] using restrict_ofLetters w hst1 i
      have huG : ofLetters u ∈ st 1 :=
        (Subgroup.mem_subgroupOf).mpr (by
          have : restrict (h : TreeAut) i ∈ stabilizerLevel 1 :=
            restrict_mem_stabilizerLevel
              (mem_stabilizerLevel_of_le (by decide : (2 : ℕ) ≤ 3) h.property) i
          rwa [← ri])
      have rj : restrict (restrict (h : TreeAut) i) j = (ofLetters v : TreeAut) := by
        simpa [ri, v] using restrict_ofLetters u huG j
      apply le_of_eq_of_le (congrArg gens.wordLength (Subtype.ext ?_))
        (ofLetters_wordLength_le v)
      simpa [restrictSt] using rj
    have hL :
        ∑ i : Fin 2, ∑ j : Fin 2, gens.wordLength (restrictSt (restrictSt h i) j : G) ≤
          lengthTwo w := by
      have b00 := bound 0 0
      have b01 := bound 0 1
      have b10 := bound 1 0
      have b11 := bound 1 1
      simp [sum_fin2, lengthTwo] at b00 b01 b10 b11 ⊢
      omega
    simp [sum_fin2] at hsum hL ⊢
    omega
  have hL2 := lengthTwo_le_of_reduced w hr
  have hcnt1 : w.count 1 ≤ w.length := List.countP_le_length
  have hcnt2 : w.count 2 ≤ w.length := List.countP_le_length
  have hcnt3 : w.count 3 ≤ w.length := List.countP_le_length
  have hb : ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, gens.wordLength (chi h i j k) ≤
      w.length + 7 - w.count 1 := h3
  have hd : ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, gens.wordLength (chi h i j k) ≤
      w.length + 7 - w.count 3 := by
    have : (sectionWords w).1.length + (sectionWords w).2.length + 6 ≤
        w.length + 7 - w.count 3 := by omega
    exact h1.trans this
  have hc : ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, gens.wordLength (chi h i j k) ≤
      w.length + 7 - w.count 2 := by
    have : lengthTwo w + 4 ≤ w.length + 7 - w.count 2 := by omega
    exact h2.trans this
  cases Nat.le_total (w.count 1 ⊔ w.count 2) (w.count 3) with
  | inl h =>
    have : w.count 1 ⊔ w.count 2 ⊔ w.count 3 = w.count 3 := sup_eq_right.mpr h
    rwa [this]
  | inr h =>
    cases Nat.le_total (w.count 1) (w.count 2) with
    | inl h12 =>
      have hmax : w.count 1 ⊔ w.count 2 = w.count 2 := sup_eq_right.mpr h12
      have : w.count 1 ⊔ w.count 2 ⊔ w.count 3 = w.count 2 := by
        rw [hmax]
        exact sup_eq_left.mpr (h.trans_eq hmax)
      rwa [this]
    | inr h12 =>
      have hmax : w.count 1 ⊔ w.count 2 = w.count 1 := sup_eq_left.mpr h12
      have : w.count 1 ⊔ w.count 2 ⊔ w.count 3 = w.count 1 := by
        rw [hmax]
        exact sup_eq_left.mpr (h.trans_eq hmax)
      rwa [this]

/-- The sum of the eight section lengths is at most `(5/6) ℓ(h) + 8`. -/
lemma chi_wordLength_sum_le (h : st 3) :
    ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, gens.wordLength (chi h i j k) ≤
      (5 * gens.wordLength (h : G) + 48) / 6 := by
  obtain ⟨l, hlgeo, hl⟩ := gens.exists_isGeodesic (h : G)
  have hr : IsReduced (l.map Prod.fst) := geodesic_isReduced l hlgeo
  set w := l.map Prod.fst
  have hlen : w.length = l.length := by simp [w]
  have hprod : ofLetters w = (h : G) := by
    simpa [w, wordProd_eq_ofLetters] using hl
  have hgeo : gens.wordLength (h : G) = w.length :=
    (congrArg gens.wordLength hl).symm.trans (hlgeo.trans hlen.symm)
  have hsum := chi_wordLength_sum_le_aux h w hprod hr
  have hmax : (w.length - 1) / 6 ≤ w.count 1 ⊔ w.count 2 ⊔ w.count 3 := by
    have : ((w.length - 1) / 2) / 3 = (w.length - 1) / 6 :=
      Nat.div_div_eq_div_mul (w.length - 1) 2 3
    rw [← this]
    exact (Nat.div_le_div_right (bcd_count_ge w hr)).trans (max_bcd_ge w)
  have hc1 : w.count 1 ≤ w.length := List.countP_le_length
  have hc2 : w.count 2 ≤ w.length := List.countP_le_length
  have hc3 : w.count 3 ≤ w.length := List.countP_le_length
  have hM : w.count 1 ⊔ w.count 2 ⊔ w.count 3 ≤ w.length := by omega
  omega

/-! ### Finite index of `st 3` and growth covering -/

instance (n : ℕ) : Finite (G ⧸ st n) :=
  Finite.of_injective _ (stQuotEmbed_injective n)

instance : (st 3).FiniteIndex :=
  Subgroup.finiteIndex_of_finite_quotient

lemma st3_index_le : (st 3).index ≤ 128 := by
  simpa using st_index_le 3

/-- A finite right transversal for `st 3` in `G`. -/
noncomputable def st3Transversal : Set G :=
  Classical.choose ((st 3).exists_isComplement_right (1 : G))

lemma st3_isComplement : Subgroup.IsComplement (st 3) st3Transversal :=
  (Classical.choose_spec ((st 3).exists_isComplement_right (1 : G))).1

lemma finite_st3Transversal : st3Transversal.Finite :=
  st3_isComplement.finite_right

/-- The representative of the right coset `(st 3) g` in `st3Transversal`. -/
noncomputable def st3Rep (g : G) : G := (st3_isComplement.equiv g).2

lemma st3Rep_mem (g : G) : st3Rep g ∈ st3Transversal :=
  (st3_isComplement.equiv g).2.property

lemma mul_inv_st3Rep_mem (g : G) : g * (st3Rep g)⁻¹ ∈ st 3 := by
  have h := (st3_isComplement.equiv g).1.property
  rw [st3Rep, ← Subgroup.IsComplement.equiv_fst_eq_mul_inv]
  exact h

/-- The maximal word length of an element of `st3Transversal`. -/
noncomputable def st3Bound : ℕ := sSup (gens.wordLength '' st3Transversal)

lemma le_st3Bound {g : G} (hg : g ∈ st3Transversal) :
    gens.wordLength g ≤ st3Bound :=
  le_csSup ((finite_st3Transversal.image _).bddAbove) ⟨g, hg, rfl⟩

lemma ncard_st3_inter_wordBall (n : ℕ) :
    gens.growth n ≤
      (st 3).index * ((st 3).carrier ∩ gens.wordBall (n + st3Bound)).ncard := by
  let σ (g : G) : G := g * (st3Rep g)⁻¹
  have hσ (g : G) : σ g ∈ st 3 := mul_inv_st3Rep_mem g
  have hσlen (g : G) (hg : g ∈ gens.wordBall n) :
      σ g ∈ gens.wordBall (n + st3Bound) := by
    have : gens.wordLength (σ g) ≤ gens.wordLength g + gens.wordLength (st3Rep g) := by
      simpa [σ, gens.wordLength_inv] using gens.wordLength_mul_le g (st3Rep g)⁻¹
    exact this.trans (Nat.add_le_add hg (le_st3Bound (st3Rep_mem g)))
  have hcover : gens.wordBall n ⊆
      (fun p : G × G ↦ p.1 * p.2) ''
        (((st 3).carrier ∩ gens.wordBall (n + st3Bound)) ×ˢ st3Transversal) := by
    intro g hg
    refine ⟨(σ g, st3Rep g), ?_, ?_⟩
    · exact ⟨⟨hσ g, hσlen g hg⟩, st3Rep_mem g⟩
    · simp [σ]
  have hfin : (((st 3).carrier ∩ gens.wordBall (n + st3Bound)) ×ˢ st3Transversal).Finite :=
    ((gens.finite_wordBall (n + st3Bound)).subset inter_subset_right).prod finite_st3Transversal
  have := ncard_le_ncard hcover (hfin.image _)
  have hmul : (((st 3).carrier ∩ gens.wordBall (n + st3Bound)) ×ˢ st3Transversal).ncard =
      ((st 3).carrier ∩ gens.wordBall (n + st3Bound)).ncard * st3Transversal.ncard :=
    ncard_prod
  have hR : st3Transversal.ncard = (st 3).index := st3_isComplement.ncard_right
  have himage := ncard_image_le (hs := hfin) (f := fun p : G × G ↦ p.1 * p.2)
  calc
    gens.growth n = (gens.wordBall n).ncard := rfl
    _ ≤ ((fun p : G × G ↦ p.1 * p.2) ''
          (((st 3).carrier ∩ gens.wordBall (n + st3Bound)) ×ˢ st3Transversal)).ncard :=
        this
    _ ≤ (((st 3).carrier ∩ gens.wordBall (n + st3Bound)) ×ˢ st3Transversal).ncard :=
        himage
    _ = (st 3).index * ((st 3).carrier ∩ gens.wordBall (n + st3Bound)).ncard := by
        rw [hmul, hR, mul_comm]

/-! ### Crude exponential bound and bootstrap -/

lemma ncard_lists_length_eq (k : Nat) :
    ({l : List (Fin 4 × Bool) | l.length = k}).ncard = 8 ^ k := by
  let e : {l : List (Fin 4 × Bool) | l.length = k} ≃ (Fin k → Fin 4 × Bool) :=
    { toFun := fun l i => l.val[i.val]'(l.property.symm ▸ i.isLt)
      invFun := fun f => ⟨List.ofFn f, by simp⟩
      left_inv := fun l => by
        apply Subtype.ext
        apply List.ext_getElem
        · simpa using l.property.symm
        · intro i h1 h2
          simp
      right_inv := fun f => by
        funext i
        simp }
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fun, Nat.card_prod]
  simp [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_bool]

lemma growth_le_mul_eight_pow (n : Nat) : gens.growth n ≤ (n + 1) * 8 ^ n := by
  have hfin : {l : List (Fin 4 × Bool) | l.length ≤ n}.Finite :=
    List.finite_length_le _ n
  rw [gens.growth_eq_ncard, gens.wordBall_eq_image]
  refine (ncard_image_le hfin).trans ?_
  have hunion :
      {l : List (Fin 4 × Bool) | l.length ≤ n} =
        ⋃ k ∈ Finset.range (n + 1), {l | l.length = k} := by
    ext l
    simp [Finset.mem_range]
  rw [hunion]
  refine (Finset.set_ncard_biUnion_le _ _).trans ?_
  refine (Finset.sum_le_sum fun k _ => (ncard_lists_length_eq k).le).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (8 ^ n) ?_).trans_eq ?_
  · intro k hk
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 8)
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  · simp [Finset.card_range]
lemma sum_div_two_pow_le (N t : Nat) :
    ∑ i ∈ Finset.range t, N / 2 ^ (i + 1) ≤ N := by
  induction t generalizing N with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ']
    have hdiv (i : Nat) : N / 2 ^ (i + 2) = N / 2 / 2 ^ (i + 1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
    have : ∑ i ∈ Finset.range t, N / 2 ^ (i + 1 + 1) =
        ∑ i ∈ Finset.range t, N / 2 / 2 ^ (i + 1) :=
      Finset.sum_congr rfl fun i _ => hdiv i
    rw [this]
    have := ih (N / 2)
    omega

lemma pow_add_one_le_two_mul_pow {k n : Nat} (hn : 2 * k ≤ n) :
    (n + 1) ^ k ≤ 2 * n ^ k := by
  cases k with
  | zero => simp
  | succ k =>
    have hbin : (n + 1) ^ (k + 1) =
        ∑ i ∈ Finset.range (k + 2), n ^ (k + 1 - i) * (k + 1).choose i := by
      simpa [Nat.add_comm n 1] using add_pow (1 : Nat) n (k + 1)
    have hterm (i : Nat) (hi : i ∈ Finset.range (k + 2)) :
        n ^ (k + 1 - i) * (k + 1).choose i ≤ n ^ (k + 1) / 2 ^ i := by
      have hch : (k + 1).choose i ≤ (k + 1) ^ i := Nat.choose_le_pow _ _
      have hi' : i ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hmul : n ^ (k + 1 - i) * (k + 1).choose i * 2 ^ i ≤ n ^ (k + 1) := by
        have hpow : (k + 1) ^ i * 2 ^ i ≤ n ^ i := by
          rw [← mul_pow]
          exact Nat.pow_le_pow_left (by omega) _
        calc
          n ^ (k + 1 - i) * (k + 1).choose i * 2 ^ i
              ≤ n ^ (k + 1 - i) * (k + 1) ^ i * 2 ^ i :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hch)
          _ = n ^ (k + 1 - i) * ((k + 1) ^ i * 2 ^ i) := by ring
          _ ≤ n ^ (k + 1 - i) * n ^ i := Nat.mul_le_mul_left _ hpow
          _ = n ^ (k + 1) := by rw [← pow_add]; congr 1; omega
      exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos i)).2 hmul
    rw [hbin, Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, tsub_zero, mul_one]
    have hrest :
        ∑ i ∈ Finset.range (k + 1),
            n ^ (k + 1 - (i + 1)) * (k + 1).choose (i + 1) ≤ n ^ (k + 1) := by
      have : ∑ i ∈ Finset.range (k + 1),
          n ^ (k + 1 - (i + 1)) * (k + 1).choose (i + 1) ≤
          ∑ i ∈ Finset.range (k + 1), n ^ (k + 1) / 2 ^ (i + 1) :=
        Finset.sum_le_sum fun i hi =>
          hterm (i + 1) (by simp [Finset.mem_range] at hi ⊢; omega)
      exact this.trans (sum_div_two_pow_le _ _)
    omega

lemma two_mul_sq_le_pow (D : Nat) : D * (2 * D + 5) ≤ 2 ^ (2 * D + 4) := by
  have hD : D ≤ 2 ^ D := Nat.lt_two_pow_self.le
  have hsq : D * D ≤ 2 ^ (2 * D) :=
    calc
      D * D ≤ 2 ^ D * 2 ^ D := Nat.mul_le_mul hD hD
      _ = 2 ^ (2 * D) := by rw [← pow_add, two_mul]
  have h2sq : 2 * D ^ 2 ≤ 2 ^ (2 * D + 1) := by
    calc
      2 * D ^ 2 = 2 * (D * D) := by ring
      _ ≤ 2 * 2 ^ (2 * D) := Nat.mul_le_mul_left _ hsq
      _ = 2 ^ (2 * D + 1) := by rw [pow_succ']
  have h5 : 5 * D ≤ 2 ^ (2 * D + 3) := by
    have : 5 * D ≤ 8 * 2 ^ D :=
      (Nat.mul_le_mul_left 5 hD).trans (Nat.mul_le_mul_right _ (by decide : 5 ≤ 8))
    have : 8 * 2 ^ D = 2 ^ (D + 3) := by
      rw [show (8 : Nat) = 2 ^ 3 from rfl, ← pow_add, Nat.add_comm]
    have : 2 ^ (D + 3) ≤ 2 ^ (2 * D + 3) :=
      Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega)
    omega
  have : D * (2 * D + 5) = 2 * D ^ 2 + 5 * D := by ring
  rw [this]
  have : 2 ^ (2 * D + 1) + 2 ^ (2 * D + 3) ≤ 2 ^ (2 * D + 4) := by
    have : 2 ^ (2 * D + 3) = 4 * 2 ^ (2 * D + 1) := by
      rw [pow_add]; ring
    rw [this]
    have : 2 ^ (2 * D + 1) + 4 * 2 ^ (2 * D + 1) = 5 * 2 ^ (2 * D + 1) := by ring
    rw [this]
    have : 5 * 2 ^ (2 * D + 1) ≤ 8 * 2 ^ (2 * D + 1) :=
      Nat.mul_le_mul_right _ (by decide)
    have : 8 * 2 ^ (2 * D + 1) = 2 ^ (2 * D + 4) := by
      rw [show (8 : Nat) = 2 ^ 3 from rfl, ← pow_add]
      congr 1
      ring
    omega
  omega

lemma exists_pow_le_two_pow (D : Nat) :
    ∃ n₀, ∀ n ≥ n₀, (n + 1) ^ D ≤ 2 ^ n := by
  let n₀ := 2 ^ (2 * D + 4)
  have hn₀D : 2 * D ≤ n₀ :=
    (Nat.lt_two_pow_self.le : 2 * D ≤ 2 ^ (2 * D)).trans
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_add_right _ 4))
  refine ⟨n₀, ?_⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    have hle : n₀ + 1 ≤ 2 ^ (2 * D + 5) := by
      have : 1 ≤ n₀ := Nat.one_le_two_pow
      have : n₀ + 1 ≤ 2 * n₀ := by omega
      have : 2 * n₀ = 2 ^ (2 * D + 5) := by rw [pow_succ']
      omega
    have hpow := Nat.pow_le_pow_left hle D
    rw [← pow_mul] at hpow
    rw [Nat.mul_comm (2 * D + 5)] at hpow
    exact hpow.trans (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (two_mul_sq_le_pow D))
  | succ n hn ih =>
    have hratio : (n + 2) ^ D ≤ 2 * (n + 1) ^ D :=
      pow_add_one_le_two_mul_pow (by omega)
    calc
      (n + 2) ^ D ≤ 2 * (n + 1) ^ D := hratio
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (n + 1) := by rw [pow_succ']

lemma exists_pow_le_two_pow_div (D Q : Nat) (hQ : 0 < Q) :
    ∃ n₀, ∀ n ≥ n₀, (n + 1) ^ D ≤ 2 ^ (n / Q + 1) := by
  obtain ⟨n₀, hn₀⟩ := exists_pow_le_two_pow (D * Q)
  refine ⟨n₀, fun n hn => ?_⟩
  have hpow : ((n + 1) ^ D) ^ Q ≤ 2 ^ n := by
    rw [← pow_mul]
    exact hn₀ n hn
  refine (Nat.pow_le_pow_iff_left hQ.ne').1 (hpow.trans ?_)
  have hle : n ≤ (n / Q + 1) * Q := by
    have : n ≤ Q * (n / Q + 1) :=
      calc
        n = Q * (n / Q) + n % Q := (Nat.div_add_mod n Q).symm
        _ ≤ Q * (n / Q) + (Q - 1) :=
            Nat.add_le_add_left (Nat.le_pred_of_lt (Nat.mod_lt n hQ)) _
        _ ≤ Q * (n / Q) + Q := Nat.add_le_add_left (Nat.sub_le _ _) _
        _ = Q * (n / Q + 1) := by rw [Nat.mul_add, Nat.mul_one]
    rwa [Nat.mul_comm] at this
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hle

lemma prod_pow_eq_pow_sum {ι : Type*} (s : Finset ι) (b : Nat) (f : ι → Nat) :
    ∏ i ∈ s, b ^ f i = b ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, pow_add]

lemma sum_div_le_div_sum {ι : Type*} {q : Nat} (hq : 0 < q) (s : Finset ι) (f : ι → Nat) :
    ∑ i ∈ s, f i / q ≤ (∑ i ∈ s, f i) / q := by
  have hdecomp : ∑ i ∈ s, f i = q * ∑ i ∈ s, f i / q + ∑ i ∈ s, f i % q := by
    conv_lhs => rw [Finset.sum_congr rfl fun i _ => (Nat.div_add_mod (f i) q).symm]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hdecomp, Nat.mul_add_div hq]
  exact Nat.le_add_right _ _

lemma mul_div_le_div_mul (a b c : Nat) (hc : 0 < c) : a * (b / c) ≤ a * b / c := by
  have hb : b = c * (b / c) + b % c := (Nat.div_add_mod b c).symm
  have : a * b = c * (a * (b / c)) + a * (b % c) := by
    conv_lhs => rw [hb]
    ring
  rw [this, Nat.mul_add_div hc]
  exact Nat.le_add_right _ _

/-- Indices of the eight subtrees of level 3. -/
abbrev SecIdx : Type := Fin 2 × Fin 2 × Fin 2

/-- The eight sections of an element of `st 3`, indexed by `SecIdx`. -/
noncomputable def chiSec (h : st 3) : SecIdx → G := fun x => chi h x.1 x.2.1 x.2.2

lemma chiSec_injective {h₁ h₂ : st 3} (heq : chiSec h₁ = chiSec h₂) : h₁ = h₂ := by
  apply chi_injective
  intro i j k
  exact congr_fun heq ⟨i, j, k⟩

lemma sum_secIdx (f : SecIdx → Nat) :
    ∑ x : SecIdx, f x = ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, f (i, j, k) := by
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.univ_product_univ, Finset.sum_product]

lemma sum_chiSec (h : st 3) :
    ∑ x : SecIdx, gens.wordLength (chiSec h x) =
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, gens.wordLength (chi h i j k) :=
  sum_secIdx _

lemma ncard_pi_wordBall (t : SecIdx → Nat) :
    (Set.pi (Set.univ : Set SecIdx) fun x => gens.wordBall (t x)).ncard =
      ∏ x : SecIdx, gens.growth (t x) := by
  let e := Equiv.Set.univPi fun x : SecIdx => gens.wordBall (t x)
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_pi]
  refine Finset.prod_congr rfl fun x _ => ?_
  simp [Nat.card_coe_set_eq, gens.growth_eq_ncard]

lemma ncard_st3_inter_le_of_bound (M C D p q A : Nat) (hq : 0 < q)
    (hf : ∀ m, gens.growth m ≤ C * (m + 1) ^ D * 2 ^ ((p * m + A) / q)) :
    let α := (5 * M + 48) / 6
    ((st 3).carrier ∩ gens.wordBall M).ncard ≤
      (α + 1) ^ 8 * C ^ 8 * (α + 1) ^ (8 * D) * 2 ^ ((p * α + 8 * A) / q) := by
  classical
  intro α
  let S := (st 3).carrier ∩ gens.wordBall M
  let f : G → (SecIdx → G) := fun g =>
    if hg : g ∈ st 3 then chiSec ⟨g, hg⟩ else fun _ => 1
  have hfS (g : G) (hg : g ∈ S) : f g = chiSec ⟨g, hg.1⟩ := by
    have mem : g ∈ st 3 := hg.1
    change (if hg' : g ∈ st 3 then chiSec ⟨g, hg'⟩ else fun _ => 1) =
      chiSec ⟨g, hg.1⟩
    simp [mem]
  have hinj : InjOn f S := by
    intro g₁ hg₁ g₂ hg₂ heq
    exact Subtype.ext_iff.mp (chiSec_injective (by
      calc
        chiSec ⟨g₁, hg₁.1⟩ = f g₁ := (hfS g₁ hg₁).symm
        _ = f g₂ := heq
        _ = chiSec ⟨g₂, hg₂.1⟩ := hfS g₂ hg₂))
  have himg : f '' S ⊆ {p : SecIdx → G | ∑ x, gens.wordLength (p x) ≤ α} := by
    intro p hp
    obtain ⟨g, hgS, rfl⟩ := hp
    change ∑ x, gens.wordLength (f g x) ≤ α
    rw [hfS g hgS, sum_chiSec]
    have hsum := chi_wordLength_sum_le ⟨g, hgS.1⟩
    have hlen : gens.wordLength g ≤ M := hgS.2
    have : (5 * gens.wordLength g + 48) / 6 ≤ α :=
      Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_left 5 hlen) 48)
    exact hsum.trans this
  have hfinS : S.Finite := (gens.finite_wordBall M).subset inter_subset_right
  let T := SecIdx → Fin (α + 1)
  let U (t : T) : Set (SecIdx → G) :=
    if ∑ x, (t x : Nat) ≤ α then Set.pi Set.univ fun x => gens.wordBall (t x) else ∅
  have hcover : {p : SecIdx → G | ∑ x, gens.wordLength (p x) ≤ α} ⊆ ⋃ t : T, U t := by
    intro p hp
    have hxi (x : SecIdx) : gens.wordLength (p x) ≤ α :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)).trans hp
    let t : T := fun x => ⟨gens.wordLength (p x), Nat.lt_succ_of_le (hxi x)⟩
    refine mem_iUnion.mpr ⟨t, ?_⟩
    have hsumt : ∑ x, (t x : Nat) ≤ α := hp
    simp only [U, hsumt, ↓reduceIte, Set.mem_pi, Set.mem_univ]
    intro x _
    exact gens.mem_wordBall.mpr (Nat.le_refl _)
  have hfinU : (⋃ t : T, U t).Finite := by
    refine Set.finite_iUnion fun t => ?_
    by_cases hsum : ∑ x, (t x : Nat) ≤ α
    · simp only [U, hsum, ↓reduceIte]
      exact Set.Finite.pi fun _ => gens.finite_wordBall _
    · simp [U, hsum]
  have hle1 : S.ncard ≤ {p : SecIdx → G | ∑ x, gens.wordLength (p x) ≤ α}.ncard := by
    rw [← hinj.ncard_image]
    exact ncard_le_ncard himg (hfinU.subset hcover)
  have hle2 : {p : SecIdx → G | ∑ x, gens.wordLength (p x) ≤ α}.ncard ≤
      ∑ t : T, (U t).ncard :=
    (ncard_le_ncard hcover hfinU).trans (ncard_iUnion_le_of_fintype U)
  have hcard8 : (Finset.univ : Finset SecIdx).card = 8 := by
    simp [Fintype.card_prod, Fintype.card_fin]
  have hUt (t : T) :
      (U t).ncard ≤ C ^ 8 * (α + 1) ^ (8 * D) * 2 ^ ((p * α + 8 * A) / q) := by
    by_cases hsum : ∑ x, (t x : Nat) ≤ α
    · have hU : U t = Set.pi Set.univ fun x => gens.wordBall (t x) := by
        simp [U, hsum]
      rw [hU, ncard_pi_wordBall]
      have hprod : ∏ x : SecIdx, gens.growth (t x) ≤
          ∏ x : SecIdx, C * ((t x : Nat) + 1) ^ D * 2 ^ ((p * (t x : Nat) + A) / q) :=
        Finset.prod_le_prod fun x _ => hf (t x)
      refine hprod.trans ?_
      have hsplit :
          ∏ x : SecIdx, C * ((t x : Nat) + 1) ^ D * 2 ^ ((p * (t x : Nat) + A) / q) =
            C ^ 8 *
              (∏ x : SecIdx, ((t x : Nat) + 1) ^ D) *
                (∏ x : SecIdx, 2 ^ ((p * (t x : Nat) + A) / q)) := by
        simp_rw [mul_assoc]
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, hcard8]
      rw [hsplit]
      have ha : ∏ x : SecIdx, ((t x : Nat) + 1) ^ D ≤ (α + 1) ^ (8 * D) := by
        have hx (x : SecIdx) : (t x : Nat) + 1 ≤ α + 1 :=
          Nat.succ_le_succ (Nat.le_of_lt_succ (t x).isLt)
        have : ∏ x : SecIdx, ((t x : Nat) + 1) ^ D ≤ ∏ _x : SecIdx, (α + 1) ^ D :=
          Finset.prod_le_prod fun x _ => Nat.pow_le_pow_left (hx x) _
        refine this.trans_eq ?_
        rw [Finset.prod_const, hcard8, ← pow_mul, Nat.mul_comm D]
      have hb : ∏ x : SecIdx, 2 ^ ((p * (t x : Nat) + A) / q) ≤
          2 ^ ((p * α + 8 * A) / q) := by
        rw [prod_pow_eq_pow_sum]
        refine Nat.pow_le_pow_right (by decide : 1 ≤ 2) ?_
        have hdiv := sum_div_le_div_sum hq Finset.univ
          (fun x : SecIdx => p * (t x : Nat) + A)
        refine hdiv.trans (Nat.div_le_div_right ?_)
        have hsumeq : ∑ x : SecIdx, (p * (t x : Nat) + A) =
            p * ∑ x : SecIdx, (t x : Nat) + 8 * A := by
          simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, hcard8]
        rw [hsumeq]
        exact Nat.add_le_add (Nat.mul_le_mul_left p hsum) le_rfl
      exact Nat.mul_le_mul (Nat.mul_le_mul le_rfl ha) hb
    · simp [U, hsum]
  have hT : (Finset.univ : Finset T).card = (α + 1) ^ 8 := by
    simp [T, Fintype.card_prod, Fintype.card_fin]
  have hle3 : ∑ t : T, (U t).ncard ≤
      (α + 1) ^ 8 * C ^ 8 * (α + 1) ^ (8 * D) * 2 ^ ((p * α + 8 * A) / q) := by
    have hsum := Finset.sum_le_card_nsmul (s := Finset.univ) (f := fun t => (U t).ncard)
      (C ^ 8 * (α + 1) ^ (8 * D) * 2 ^ ((p * α + 8 * A) / q)) (fun t _ => hUt t)
    have hmul : (Finset.univ : Finset T).card •
        (C ^ 8 * (α + 1) ^ (8 * D) * 2 ^ ((p * α + 8 * A) / q)) =
        (α + 1) ^ 8 * C ^ 8 * (α + 1) ^ (8 * D) * 2 ^ ((p * α + 8 * A) / q) := by
      simp [hT, mul_assoc]
    exact hsum.trans_eq hmul
  exact hle1.trans (hle2.trans hle3)

lemma growth_iter_bound (t : Nat) :
    ∃ C D A : Nat, ∀ n,
      gens.growth n ≤ C * (n + 1) ^ D * 2 ^ ((3 * 5 ^ t * n + A) / 6 ^ t) := by
  induction t with
  | zero =>
    refine ⟨1, 1, 0, fun n => ?_⟩
    have h := growth_le_mul_eight_pow n
    have h8 : (8 : Nat) ^ n = 2 ^ (3 * n) := by
      rw [show (8 : Nat) = 2 ^ 3 from rfl, ← pow_mul]
    simpa [h8] using h
  | succ t ih =>
    obtain ⟨C, D, A, hf⟩ := ih
    let C' := (st 3).index * C ^ 8 * (5 * st3Bound + 49) ^ (8 * D + 8)
    let D' := 8 * D + 8
    let A' := 3 * 5 ^ (t + 1) * st3Bound + 144 * 5 ^ t + 48 * A
    refine ⟨C', D', A', fun n => ?_⟩
    have hq : 0 < 6 ^ t := Nat.pow_pos (by decide : 0 < 6)
    have hst := ncard_st3_inter_le_of_bound (n + st3Bound) C D (3 * 5 ^ t) (6 ^ t) A hq hf
    have hcov := ncard_st3_inter_wordBall n
    let α := (5 * (n + st3Bound) + 48) / 6
    have hα1 : α + 1 ≤ (5 * st3Bound + 49) * (n + 1) := by
      have hα : α ≤ 5 * (n + st3Bound) + 48 := Nat.div_le_self _ _
      have hlin : α + 1 ≤ 5 * n + 5 * st3Bound + 49 := by
        have : 5 * (n + st3Bound) + 48 = 5 * n + 5 * st3Bound + 48 := by ring
        omega
      have hmul : 5 * n + 5 * st3Bound + 49 ≤ (5 * st3Bound + 49) * (n + 1) := by
        have : 5 * n ≤ (5 * st3Bound + 49) * n :=
          Nat.mul_le_mul_right n (by omega)
        have : (5 * st3Bound + 49) * (n + 1) =
            (5 * st3Bound + 49) * n + (5 * st3Bound + 49) := by ring
        omega
      exact hlin.trans hmul
    have hpoly : (α + 1) ^ (8 * D + 8) ≤
        (5 * st3Bound + 49) ^ (8 * D + 8) * (n + 1) ^ (8 * D + 8) := by
      have := Nat.pow_le_pow_left hα1 (8 * D + 8)
      rwa [mul_pow] at this
    have hα6 : 6 * α ≤ 5 * (n + st3Bound) + 48 := Nat.mul_div_le _ _
    have hexp : (3 * 5 ^ t * α + 8 * A) / 6 ^ t ≤
        (3 * 5 ^ (t + 1) * n + A') / 6 ^ (t + 1) := by
      have hmul : 6 * (3 * 5 ^ t * α + 8 * A) ≤ 3 * 5 ^ (t + 1) * n + A' := by
        have : 6 * (3 * 5 ^ t * α) ≤ 3 * 5 ^ t * (5 * (n + st3Bound) + 48) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            Nat.mul_le_mul_left (3 * 5 ^ t) hα6
        have : 3 * 5 ^ t * (5 * (n + st3Bound) + 48) =
            3 * 5 ^ (t + 1) * n + 3 * 5 ^ (t + 1) * st3Bound + 144 * 5 ^ t := by
          rw [pow_succ]
          ring
        omega
      have : (3 * 5 ^ t * α + 8 * A) / 6 ^ t =
          6 * (3 * 5 ^ t * α + 8 * A) / 6 ^ (t + 1) := by
        have h6 : (3 * 5 ^ t * α + 8 * A) / 6 ^ t =
            6 * (3 * 5 ^ t * α + 8 * A) / (6 * 6 ^ t) :=
          (Nat.mul_div_mul_left _ _ (by decide : 0 < 6)).symm
        rwa [← pow_succ'] at h6
      rw [this]
      exact Nat.div_le_div_right hmul
    have hmain : gens.growth n ≤
        (st 3).index * (α + 1) ^ 8 * C ^ 8 * (α + 1) ^ (8 * D) *
          2 ^ ((3 * 5 ^ t * α + 8 * A) / 6 ^ t) := by
      refine hcov.trans ?_
      have := Nat.mul_le_mul_left (st 3).index hst
      simpa [α, mul_assoc] using this
    have hmain' : gens.growth n ≤
        (st 3).index * C ^ 8 * (α + 1) ^ (8 * D + 8) *
          2 ^ ((3 * 5 ^ (t + 1) * n + A') / 6 ^ (t + 1)) := by
      refine hmain.trans ?_
      have : (α + 1) ^ 8 * (α + 1) ^ (8 * D) = (α + 1) ^ (8 * D + 8) := by
        rw [← pow_add, Nat.add_comm 8]
      have hre : (st 3).index * (α + 1) ^ 8 * C ^ 8 * (α + 1) ^ (8 * D) =
          (st 3).index * C ^ 8 * ((α + 1) ^ 8 * (α + 1) ^ (8 * D)) := by ring
      rw [hre, this]
      exact Nat.mul_le_mul le_rfl (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hexp)
    refine hmain'.trans ?_
    have : (st 3).index * C ^ 8 * (α + 1) ^ (8 * D + 8) ≤ C' * (n + 1) ^ D' := by
      have := Nat.mul_le_mul_left ((st 3).index * C ^ 8) hpoly
      simpa [C', D', mul_assoc] using this
    exact Nat.mul_le_mul this le_rfl

lemma six_mul_five_pow_lt (k : Nat) :
    6 * (k + 1) * 5 ^ (10 * (k + 1)) < 6 ^ (10 * (k + 1)) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h1 : (k + 2) * 5 ^ 10 ≤ 2 * (k + 1) * 5 ^ 10 :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : 2 * (k + 1) * 5 ^ 10 < (k + 1) * 6 ^ 10 := by
      have : 2 * (k + 1) * 5 ^ 10 = (k + 1) * (2 * 5 ^ 10) := by ring
      rw [this]
      exact Nat.mul_lt_mul_of_pos_left (by decide) (Nat.succ_pos _)
    have h12 : (k + 2) * 5 ^ 10 < (k + 1) * 6 ^ 10 := h1.trans_lt h2
    have h3 : 6 * ((k + 2) * 5 ^ 10) < 6 * ((k + 1) * 6 ^ 10) :=
      Nat.mul_lt_mul_of_pos_left h12 (by decide : 0 < 6)
    have h3' : 6 * (k + 2) * 5 ^ 10 < 6 * (k + 1) * 6 ^ 10 := by
      convert h3 using 1 <;> ring
    have h5pos : 0 < 5 ^ (10 * (k + 1)) := Nat.pow_pos (by decide : 0 < 5)
    have h6pos : 0 < 6 ^ 10 := Nat.pow_pos (by decide : 0 < 6)
    calc
      6 * (k + 2) * 5 ^ (10 * (k + 2))
          = 6 * (k + 2) * (5 ^ 10 * 5 ^ (10 * (k + 1))) := by
            rw [show 10 * (k + 2) = 10 + 10 * (k + 1) from by ring, pow_add]
      _ = 6 * (k + 2) * 5 ^ 10 * 5 ^ (10 * (k + 1)) := by ring
      _ < 6 * (k + 1) * 6 ^ 10 * 5 ^ (10 * (k + 1)) :=
          Nat.mul_lt_mul_of_pos_right h3' h5pos
      _ = 6 ^ 10 * (6 * (k + 1) * 5 ^ (10 * (k + 1))) := by ring
      _ < 6 ^ 10 * 6 ^ (10 * (k + 1)) :=
          Nat.mul_lt_mul_of_pos_left ih h6pos
      _ = 6 ^ (10 * (k + 2)) := by
            rw [← pow_add]; congr 1; ring

theorem hasSubexponentialGrowth {ι : Type*} [Finite ι] (P : Group.Generators G ι) :
    P.HasSubexponentialGrowth := by
  refine Function.HasSubexponentialGrowth.of_growthEquivalent
    (P.growth_growthEquivalent gens).symm ?_
  intro k
  cases k with
  | zero => exact ⟨0, fun n _ => Nat.one_le_two_pow⟩
  | succ k =>
    let t := 10 * (k + 1)
    obtain ⟨C, D, A, hf⟩ := growth_iter_bound t
    have ht : 6 * (k + 1) * 5 ^ t < 6 ^ t := six_mul_five_pow_lt k
    have hq : 0 < 6 ^ t := Nat.pow_pos (by decide : 0 < 6)
    let q := 6 ^ t
    obtain ⟨n₁, hn₁⟩ := exists_pow_le_two_pow_div (D * (k + 1)) 4 (by decide)
    obtain ⟨m₀, hm₀⟩ := exists_const_le_two_pow (C ^ (k + 1) * 2 ^ (A * (k + 1)))
    refine ⟨max n₁ (max (4 * (m₀ + 1)) (2 * q)), fun n hn => ?_⟩
    have hn4 : 4 * (m₀ + 1) ≤ n :=
      le_trans (le_max_left _ _) (le_trans (le_max_right n₁ _) hn)
    have _hn2q : 2 * q ≤ n :=
      le_trans (le_max_right (4 * (m₀ + 1)) _) (le_trans (le_max_right n₁ _) hn)
    have hg := hf n
    have hpow := Nat.pow_le_pow_left hg (k + 1)
    have hsplit :
        (C * (n + 1) ^ D * 2 ^ ((3 * 5 ^ t * n + A) / q)) ^ (k + 1) =
          C ^ (k + 1) * (n + 1) ^ (D * (k + 1)) *
            2 ^ (((3 * 5 ^ t * n + A) / q) * (k + 1)) := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    rw [hsplit] at hpow
    have hexp0 : (3 * 5 ^ t * n + A) / q ≤ (3 * 5 ^ t * n) / q + A := by
      have : 3 * 5 ^ t * n + A ≤ 3 * 5 ^ t * n + A * q :=
        Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hq) _
      have hdiv : (3 * 5 ^ t * n + A) / q ≤ (3 * 5 ^ t * n + A * q) / q :=
        Nat.div_le_div_right this
      have : (3 * 5 ^ t * n + A * q) / q = (3 * 5 ^ t * n) / q + A :=
        Nat.add_mul_div_right _ _ hq
      rwa [this] at hdiv
    have hexpk : ((3 * 5 ^ t * n + A) / q) * (k + 1) ≤
        (3 * 5 ^ t * n) / q * (k + 1) + A * (k + 1) := by
      have := Nat.mul_le_mul_right (k + 1) hexp0
      have hdistrib : ((3 * 5 ^ t * n) / q + A) * (k + 1) =
          (3 * 5 ^ t * n) / q * (k + 1) + A * (k + 1) := by ring
      rwa [hdistrib] at this
    have hhalf : (3 * 5 ^ t * n) / q * (k + 1) ≤ n / 2 := by
      have hcomm : (3 * 5 ^ t * n) / q * (k + 1) =
          (k + 1) * ((3 * 5 ^ t * n) / q) := Nat.mul_comm _ _
      rw [hcomm]
      have hle : (k + 1) * ((3 * 5 ^ t * n) / q) ≤
          3 * (k + 1) * 5 ^ t * n / q := by
        have := mul_div_le_div_mul (k + 1) (3 * 5 ^ t * n) q hq
        have hrw : (k + 1) * (3 * 5 ^ t * n) = 3 * (k + 1) * 5 ^ t * n := by ring
        rwa [hrw] at this
      refine hle.trans ?_
      set a := 3 * (k + 1) * 5 ^ t
      have ha : 2 * a < q := by
        have : 2 * a = 6 * (k + 1) * 5 ^ t := by simp [a]; ring
        rwa [this]
      have h2a1 : 2 * a + 1 ≤ q := Nat.succ_le_of_lt ha
      have hpred : a * n ≤ q * (n / 2) + (q - 1) := by
        have hn : n = 2 * (n / 2) + n % 2 := (Nat.div_add_mod n 2).symm
        have h1 : a * n ≤ (2 * a + 1) * (n / 2) + 2 * a := by
          have hmod : n % 2 ≤ 1 :=
            Nat.lt_succ_iff.mp (Nat.mod_lt n (by decide : 0 < 2))
          calc
            a * n = a * (2 * (n / 2) + n % 2) := by conv_lhs => rw [hn]
            _ = 2 * a * (n / 2) + a * (n % 2) := by ring
            _ ≤ 2 * a * (n / 2) + a :=
                Nat.add_le_add_left
                  ((Nat.mul_le_mul_left a hmod).trans_eq (Nat.mul_one a)) _
            _ ≤ 2 * a * (n / 2) + (n / 2) + 2 * a := by omega
            _ = (2 * a + 1) * (n / 2) + 2 * a := by ring
        have h2 : (2 * a + 1) * (n / 2) + 2 * a ≤ q * (n / 2) + (q - 1) :=
          Nat.add_le_add (Nat.mul_le_mul_right _ h2a1) (Nat.le_sub_one_of_lt ha)
        exact h1.trans h2
      exact (Nat.div_le_iff_le_mul_add_pred hq).2 hpred
    have hexp : ((3 * 5 ^ t * n + A) / q) * (k + 1) ≤ n / 2 + A * (k + 1) :=
      hexpk.trans (Nat.add_le_add_right hhalf _)
    have hpoly : (n + 1) ^ (D * (k + 1)) ≤ 2 ^ (n / 4 + 1) :=
      hn₁ n (le_trans (le_max_left _ _) hn)
    have hconst : C ^ (k + 1) * 2 ^ (A * (k + 1)) ≤ 2 ^ (n / 4 - 1) := by
      have : m₀ ≤ n / 4 - 1 := by
        have : (m₀ + 1) * 4 ≤ n := by rwa [Nat.mul_comm]
        have : m₀ + 1 ≤ n / 4 := (Nat.le_div_iff_mul_le (by decide : 0 < 4)).2 this
        omega
      exact hm₀ (n / 4 - 1) this
    refine hpow.trans ?_
    have hexp2 : 2 ^ (((3 * 5 ^ t * n + A) / q) * (k + 1)) ≤
        2 ^ (n / 2 + A * (k + 1)) :=
      Nat.pow_le_pow_right (by decide : 1 ≤ 2) hexp
    have : C ^ (k + 1) * (n + 1) ^ (D * (k + 1)) *
        2 ^ (((3 * 5 ^ t * n + A) / q) * (k + 1)) ≤
          C ^ (k + 1) * 2 ^ (n / 4 + 1) * 2 ^ (n / 2 + A * (k + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul le_rfl hpoly) hexp2
    refine this.trans ?_
    have : C ^ (k + 1) * 2 ^ (n / 4 + 1) * 2 ^ (n / 2 + A * (k + 1)) =
        (C ^ (k + 1) * 2 ^ (A * (k + 1))) * 2 ^ (n / 4 + 1 + n / 2) := by
      simp [pow_add, mul_assoc, mul_left_comm, mul_comm]
    rw [this]
    have : (C ^ (k + 1) * 2 ^ (A * (k + 1))) * 2 ^ (n / 4 + 1 + n / 2) ≤
        2 ^ (n / 4 - 1) * 2 ^ (n / 4 + 1 + n / 2) :=
      Nat.mul_le_mul_right _ hconst
    refine this.trans ?_
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by
      have : 1 ≤ n / 4 := by
        have : 4 ≤ n := le_trans (Nat.le_mul_of_pos_right 4 (Nat.succ_pos _)) hn4
        omega
      omega)

theorem hasIntermediateGrowth {ι : Type*} [Finite ι] (P : Group.Generators G ι) :
    P.HasIntermediateGrowth :=
  ⟨hasSuperpolynomialGrowth P, hasSubexponentialGrowth P⟩

end Grigorchuk
