/-
Copyright (c) 2024 Shogo Saito. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shogo Saito. Adapted for mathlib by Hunter Monroe
-/
import Mathlib.Computability.Halting
import Mathlib.Data.Fin.VecNotation

/-!
# Arithmetization of Partial Recursive Functions

As a step toward proving Gödel's incompleteness theorems, this file
arithmetizes facts about partial recursive functions.

## Main result

- `exists_code`: Arithmetized proof that a universal partial recursive
  exists (to be added shortly)

## Tags

Gödel, partial recursive function
-/

open Vector Part

namespace Nat

variable {m n : ℕ}

/-- Returns 1 if m and n are equal and 0 otherwise -/
def isEqNat (n m : ℕ) : ℕ := if n = m then 1 else 0

/-- Returns 1 if n is less than m and 0 otherwise -/
def isLtNat (n m : ℕ) : ℕ := if n < m then 1 else 0

/-- Returns 1 if n is less than or equal to m and 0 otherwise -/
def isLeNat (n m : ℕ) : ℕ := if n ≤ m then 1 else 0

/-- Returns 1 if m is divisible by n and 0 otherwise -/
def isDvdNat (n m : ℕ) : ℕ := if n ∣ m then 1 else 0

@[simp] lemma isEqNat_pos_iff : 0 < isEqNat n m ↔ n = m := by
  by_cases n = m <;> simp [*, isEqNat]

@[simp] lemma isLtNat_pos_iff : 0 < isLtNat n m ↔ n < m := by
  by_cases n < m <;> simp [*, isLtNat]

@[simp] lemma isLeNat_pos_iff : 0 < isLeNat n m ↔ n ≤ m := by
  by_cases n ≤ m <;> simp [*, isLeNat]

@[simp] lemma isDvdNat_pos_iff : 0 < isDvdNat n m ↔ n ∣ m := by
  by_cases n ∣ m <;> simp [*, isDvdNat]

/-- Returns 1 if n is equal to 0 and 0 otherwise -/
def inv (n : ℕ) : ℕ := isEqNat n 0

/-- Returns 1 if n is positive and 0 otherwise -/
def pos (n : ℕ) : ℕ := isLtNat 0 n

@[simp] lemma inv_zero : inv 0 = 1 := rfl

@[simp] lemma inv_iff_ne_zero : inv n = 0 ↔ 0 < n := by simp [inv, isEqNat, zero_lt_iff]

@[simp] lemma inv_ne_zero (h : n ≠ 0) : inv n = 0 := by simp [inv, isEqNat, h]

@[simp] lemma pos_zero : pos 0 = 0 := rfl

@[simp] lemma pos_ne_zero (h : n ≠ 0) : pos n = 1 := by simp [pos, isLtNat, h]

/-- Returns 1 if m and n are both positive and 0 otherwise -/
def and (n m : ℕ) : ℕ := isLtNat 0 (n * m)

/-- Returns 1 if either m or n is positive and 0 otherwise -/
def or (n m : ℕ) : ℕ := isLtNat 0 (n + m)

lemma and_eq (n m : ℕ) : and n m = if 0 < n ∧ 0 < m then 1 else 0 := by simp [and, isLtNat]

lemma and_eq_one (n m : ℕ) : and n m = 1 ↔ 0 < n ∧ 0 < m := by
  simp [and_eq, imp_false, Nat.pos_iff_ne_zero]

lemma or_eq (n m : ℕ) : or n m = if 0 < n ∨ 0 < m then 1 else 0 := by simp [or, isLtNat]

@[simp] lemma and_pos_iff (n m : ℕ) : 0 < and n m ↔ 0 < n ∧ 0 < m := by
  by_cases 0 < n ∧ 0 < m <;> simp [*, and_eq]

@[simp] lemma or_pos_iff (n m : ℕ) : 0 < or n m ↔ 0 < n ∨ 0 < m := by
  by_cases 0 < n ∨ 0 < m <;> simp [*, or_eq]

@[simp] lemma inv_pos_iff (n : ℕ) : 0 < inv n ↔ ¬0 < n := by simp [inv]

@[simp] lemma pos_pos_iff (n : ℕ) : 0 < pos n ↔ 0 < n := by simp [pos]

/-- Bounded universal (for all) quantifier -/
def ball (n : ℕ) (p : ℕ → ℕ) : ℕ := n.rec 1 (fun n ih => (p n).pos.and ih)

@[simp] lemma ball_pos_iff {p : ℕ → ℕ} {n : ℕ} : 0 < ball n p ↔ ∀ m < n, 0 < p m := by
  induction n with
  | zero => simp [ball]
  | succ n ih =>
    simp only [ball, and_pos_iff, pos_pos_iff, Nat.lt_succ_iff] at *
    rw [ih]
    constructor
    · rintro ⟨hn, hp⟩ m hm
      rcases lt_or_eq_of_le hm with (hm | rfl)
      · exact hp _ hm
      · exact hn
    · intro h
      exact ⟨h n (Nat.le_refl n), fun m hm => h m (le_of_lt hm)⟩

@[simp] lemma ball_eq_zero_iff {p : ℕ → ℕ} {n : ℕ} : ball n p = 0 ↔ ∃ m < n, p m = 0 := by
  simpa [-ball_pos_iff] using ball_pos_iff.not

lemma ball_pos_iff_eq_one {p : ℕ → ℕ} {n : ℕ} : ball n p = 1 ↔ 0 < ball n p := by
  cases n with
  | zero => simp [ball]
  | succ n => simp [ball, and_eq_one]

/-- Arithmetized partial recursive function -/
inductive PartArith : ∀ {n}, (Vector ℕ n →. ℕ) → Prop
  | zero {n} : @PartArith n (fun _ => 0)
  | one {n} : @PartArith n (fun _ => 1)
  | add {n} (i j : Fin n) : @PartArith n (fun v => v.get i + v.get j : Vector ℕ n → ℕ)
  | mul {n} (i j : Fin n) : @PartArith n (fun v => v.get i * v.get j : Vector ℕ n → ℕ)
  | proj {n} (i : Fin n) : @PartArith n (fun v => v.get i : Vector ℕ n → ℕ)
  | equal {n} (i j : Fin n) : @PartArith n (fun v => isEqNat (v.get i) (v.get j) : Vector ℕ n → ℕ)
  | lt {n} (i j : Fin n) : @PartArith n (fun v => isLtNat (v.get i) (v.get j) : Vector ℕ n → ℕ)
  | comp {m n f} (g : Fin n → Vector ℕ m →. ℕ) :
    PartArith f → (∀ i, PartArith (g i)) → PartArith fun v => (mOfFn fun i => g i v) >>= f
  | rfind {n} {f : Vector ℕ (n + 1) → ℕ} :
    PartArith (n := n + 1) f → PartArith (fun v => rfind fun n => some (f (n ::ᵥ v) = 0))

/-- f is a partial recursive function -/
def Arith (f : Vector ℕ n → ℕ) := PartArith (n := n) f

end Nat

namespace Matrix
open Fin
section
universe u
variable {n : ℕ} {α β : Type u}

/-- notation `:>` is short for vecCons, which prepends an entry to a vector -/
infixr:70 " :> " => vecCons

lemma comp_vecCons (f : α → β) (a : α) (s : Fin n → α) : (fun x => f $ (a :> s) x) = f a :> f ∘ s :=
  funext (fun i => cases (by simp) (by simp) i)

lemma comp_vecCons' (f : α → β) (a : α) (s : Fin n → α) :
    (fun x => f $ (a :> s) x) = f a :> fun i => f (s i) :=
  comp_vecCons f a s

end

end Matrix

namespace Nat.PartArith

open Primrec

variable {n : ℕ}

lemma to_partrec' {n} {f : Vector ℕ n →. ℕ} (hf : PartArith f) : Partrec' f := by
  induction hf with
  | zero => exact Partrec'.of_part (Partrec.const' 0)
  | one  => exact Partrec'.of_part (Partrec.const' 1)
  | add i j =>
    exact (Partrec'.of_part ((Primrec.nat_add.comp
      (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const i))
      (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const j))).to_comp.partrec))
  | mul i j =>
    exact (Partrec'.of_part ((Primrec.nat_mul.comp
      (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const i))
      (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const j))).to_comp.partrec))
  | proj i =>
    exact Partrec'.of_part
      (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const i)).to_comp.partrec
  | @equal n i j =>
    have : Primrec (fun (v : Vector ℕ n) => if v.get i = v.get j then 1 else 0) :=
      Primrec.ite
        (Primrec.eq.comp
          (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const i))
          (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const j)))
        (_root_.Primrec.const 1)
        (_root_.Primrec.const 0)
    exact Partrec'.of_part this.to_comp.partrec
  | @lt n i j =>
    have : Primrec (fun (v : Vector ℕ n) => if v.get i < v.get j then 1 else 0) :=
      Primrec.ite
        (Primrec.nat_lt.comp
          (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const i))
          (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const j)))
        (_root_.Primrec.const 1)
        (_root_.Primrec.const 0)
    exact Partrec'.of_part this.to_comp.partrec
  | comp g _ _ hf hg => exact Partrec'.comp g hf hg
  | rfind _ hf => exact Partrec'.rfind hf

lemma of_eq {n} {f g : Vector ℕ n →. ℕ} (hf : PartArith f) (H : ∀ i, f i = g i) : PartArith g :=
  (funext H : f = g) ▸ hf

lemma bind (f : Vector ℕ n → ℕ →. ℕ) (hf : @PartArith (n + 1) fun v => f v.tail v.head) {g}
    (hg : @PartArith n g) : @PartArith n fun v => (g v).bind (f v) :=
  (hf.comp (g :> fun i v => v.get i)
  (fun i => by cases i using Fin.cases <;> simp [*]; exact proj _)).of_eq (by
    intro v; simp only [coe_some, bind_eq_bind]
    rcases Part.eq_none_or_eq_some (g v) with (hgv | ⟨x, hgv⟩)
    · simp [hgv, mOfFn]
    · simp [hgv, Matrix.comp_vecCons']
      have : mOfFn (fun i => (g :> fun j v => Part.some $ v.get j) i v) =
          pure (Vector.ofFn (x :> fun j => v.get j)) := by
        rw [← Vector.mOfFn_pure]; apply congr_arg
        funext i; cases i using Fin.cases <;> simp [hgv]
      simp [this])

lemma map (f : Vector ℕ n → ℕ → ℕ) (hf : @Arith (n + 1) fun v => f v.tail v.head) {g}
    (hg : @PartArith n g) : @PartArith n fun v => (g v).map (f v) :=
  (bind (Part.some $ f · ·) (hf.of_eq <| by simp) hg).of_eq <| by
  intro v; rcases Part.eq_none_or_eq_some (g v) with (_ | ⟨x, _⟩) <;> simp [*]

lemma comp₁ (f : ℕ →. ℕ) (hf : @PartArith 1 fun v => f (v.get 0)) {n g} (hg : @Arith n g) :
    @PartArith n fun v => f (g v) :=
  (hf.comp _ fun _ => hg).of_eq (by simp)

lemma comp₂ (f : ℕ → ℕ →. ℕ) (hf : @PartArith 2 fun v => f (v.get 0) (v.get 1)) {n g h}
    (hg : @Arith n g) (hh : @Arith n h) : @PartArith n fun v => f (g v) (h v) :=
  (hf.comp ![g, h] (fun i => i.cases hg (fun i => by simpa using hh))).of_eq
    (by intro i
        have : (fun j => (![↑g, h] : Fin 2 → Vector ℕ n →. ℕ) j i) =
            (fun j => pure (![g i, h i] j)) := by
          funext j; cases j using Fin.cases <;> simp [Fin.eq_zero]
        simp only [get_zero, bind_eq_bind]; simp [this] )

lemma rfind' {n} {f : ℕ → Vector ℕ n → ℕ} (h : Arith (n := n + 1) (fun v => f v.head v.tail)) :
    PartArith (fun v => Nat.rfind fun n => Part.some (f n v = 0)) := rfind h

lemma rfind'₁ {n} (i : Fin n) {f : ℕ → ℕ → ℕ} (h : Arith (n := 2)
    (fun v => f (v.get 0) (v.get 1))) : PartArith (fun v => Nat.rfind fun n =>
    Part.some (f n (v.get i) = 0)) :=
  (rfind h).comp₁ (fun m => Nat.rfind fun n => Part.some (f n m = 0)) (proj i)

end Nat.PartArith

namespace Nat.Arith

variable {n : ℕ}

lemma of_eq {n} {f g : Vector ℕ n → ℕ} (hf : Arith f) (H : ∀ i, f i = g i) : Arith g :=
  (funext H : f = g) ▸ hf

lemma zero {n} : @Arith n (fun _ => 0 : Vector ℕ n → ℕ) := Nat.PartArith.zero

lemma one {n} : @Arith n (fun _ => 1 : Vector ℕ n → ℕ) := Nat.PartArith.one

lemma add {n} (i j : Fin n) : @Arith n (fun v => v.get i + v.get j) := Nat.PartArith.add i j

lemma mul {n} (i j : Fin n) : @Arith n (fun v => v.get i * v.get j) := Nat.PartArith.mul i j

lemma proj {n} (i : Fin n) : @Arith n (fun v => v.get i) := Nat.PartArith.proj i

lemma head {n} : @Arith (n + 1) (fun v => v.head) := (Nat.PartArith.proj 0).of_eq <| by simp

lemma equal {n} (i j : Fin n) : @Arith n (fun v => isEqNat (v.get i) (v.get j)) :=
  Nat.PartArith.equal i j

lemma lt {n} (i j : Fin n) : @Arith n (fun v => isLtNat (v.get i) (v.get j)) := Nat.PartArith.lt i j

lemma comp {m n f} (g : Fin n → Vector ℕ m → ℕ) (hf : Arith f) (hg : ∀ i, Arith (g i)) :
    Arith fun v => f (Vector.ofFn fun i => g i v) :=
  (Nat.PartArith.comp (fun i => g i : Fin n → Vector ℕ m →. ℕ) hf hg).of_eq <| by simp

/-- The ith component of f v of is a partial recursive function -/
def Vec {n m} (f : Vector ℕ n → Vector ℕ m) : Prop := ∀ i, Arith fun v => (f v).get i

protected lemma nil {n} : @Vec n 0 (fun _ => nil) := fun i => i.elim0

protected lemma cons {n m f g} (hf : @Arith n f) (hg : @Vec n m g) :
    Vec (fun v => f v ::ᵥ g v) := fun i => Fin.cases (by simp [*]) (fun i => by simp [hg i]) i

lemma tail {n f} (hf : @Arith n f) : @Arith n.succ fun v => f v.tail :=
  (hf.comp _ fun i => @proj _ i.succ).of_eq fun v => by
    rw [← ofFn_get v.tail]; congr; funext i; simp

lemma comp' {n m f g} (hf : @Arith m f) (hg : @Vec n m g) : Arith fun v => f (g v) :=
  (hf.comp _ hg).of_eq fun v => by simp

lemma comp₁ (f : ℕ → ℕ) (hf : @Arith 1 fun v => f (v.get 0)) {n g} (hg : @Arith n g) :
    @Arith n fun v => f (g v) :=
  (hf.comp _ fun _ => hg).of_eq (by simp)

lemma comp₂ (f : ℕ → ℕ → ℕ) (hf : @Arith 2 fun v => f (v.get 0) (v.get 1)) {n g h}
    (hg : @Arith n g) (hh : @Arith n h) : @Arith n fun v => f (g v) (h v) :=
  (hf.comp ![g, h] (fun i => i.cases hg (fun i => by simpa using hh))).of_eq
    (by intro i; simp [Matrix.comp_vecCons'])

lemma succ {n} (i : Fin n) : Arith (fun v => v.get i + 1) := (add 0 1).comp₂ _ (proj i) one

lemma const {n} : ∀ m, @Arith n fun _ => m
  | 0     => zero
  | m + 1 => (succ 0).comp₁ _ (const m)

lemma inv {n} (i : Fin n) : Arith (fun v => inv (v.get i)) := (equal 0 1).comp₂ _ (proj i) zero

lemma pos {n} (i : Fin n) : Arith (fun v => pos (v.get i)) := (lt 0 1).comp₂ _ zero (proj i)

lemma and {n} (i j : Fin n) : Arith (fun v => and (v.get i) (v.get j)) :=
  (lt 0 1).comp₂ _ zero (mul i j)

lemma or {n} (i j : Fin n) : Arith (fun v => or (v.get i) (v.get j)) :=
  (lt 0 1).comp₂ _ zero (add i j)

lemma le {n} (i j : Fin n) : @Arith n (fun v => isLeNat (v.get i) (v.get j)) :=
  ((or 0 1).comp₂ _ (lt i j) (equal i j)).of_eq <| by simp [Nat.or_eq, Nat.le_iff_lt_or_eq, isLeNat]

lemma if_pos {n} {f g h : Vector ℕ n → ℕ} (hf : Arith f) (hg : Arith g) (hh : Arith h) :
    Arith (fun v => if 0 < f v then g v else h v) := by
  have : Arith (fun v => (f v).pos * (g v) + (f v).inv * (h v)) :=
    (add 0 1).comp₂ _
      ((mul 0 1).comp₂ _ ((pos 0).comp₁ _ hf) hg)
      ((mul 0 1).comp₂ _ ((inv 0).comp₁ _ hf) hh)
  exact this.of_eq <| by
    intro i; by_cases hf : f i = 0 <;> simp [hf, zero_lt_iff]

lemma to_Arith {f : Vector ℕ n → ℕ} (h : Arith f) : @PartArith n (fun x => f x) := h

end Nat.Arith

namespace Nat.PartArith

lemma rfindPos {n} {f : Vector ℕ (n + 1) → ℕ} (h : Arith f) :
    PartArith (fun v => Nat.rfind fun n => Part.some (0 < f (n ::ᵥ v))) :=
  (PartArith.rfind ((Arith.inv 0).comp₁ _ ((Arith.lt 0 1).comp₂ _ zero h))).of_eq <| by simp

lemma rfindPos₁ {n} (i : Fin n) {f : ℕ → ℕ → ℕ} (h : Arith (n := 2)
    (fun v => f (v.get 0) (v.get 1))) : PartArith (fun v => Nat.rfind fun n =>
    Part.some (0 < f n (v.get i))) :=
  (rfindPos h).comp₁ (fun m => Nat.rfind fun n => Part.some (0 < f n m)) (proj i)

lemma inv_fun {n} (i : Fin n) (f : ℕ → ℕ) (hf : Arith (n := 1) (fun v => f (v.get 0))) :
    PartArith (fun v => Nat.rfind (fun x => Part.some (f x ≤ v.get i ∧ v.get i < f (x + 1)))) := by
  let F : ℕ → ℕ → ℕ := fun x y => (isLeNat (f x) y).and (isLtNat y (f (x + 1)))
  have := rfindPos₁ i (f := F) <| (Arith.and 0 1).comp₂ _
      ((Arith.le 0 1).comp₂ _ (hf.comp₁ _ (proj 0)) (proj 1))
      ((Arith.lt 0 1).comp₂ _ (proj 1) (hf.comp₁ _ $ (Arith.succ 0).comp₁ _ $ proj 0))
  exact this.of_eq <| by intro v; simp

lemma implicit_fun {n} (i : Fin n) (f : Vector ℕ n → ℕ → ℕ) (hf : Arith (n := n + 1)
    (fun v => f v.tail v.head)) : PartArith (fun v => Nat.rfind (fun x => Part.some
    (f v x ≤ v.get i ∧ v.get i < f v (x + 1)))) := by
  let F : Vector ℕ (n + 1) → ℕ :=
    fun v => (isLeNat (f v.tail v.head) (v.get i.succ)).and (isLtNat (v.get i.succ)
    (f v.tail (v.head + 1)))
  have : Arith F :=
    (Arith.and 0 1).comp₂ _
      ((Arith.le 0 1).comp₂ _ hf (proj i.succ))
      ((Arith.lt 0 1).comp₂ _ (proj i.succ)
        (Arith.comp' hf (Arith.cons
          ((Arith.add 0 1).comp₂ _ Arith.head one) (fun i => Arith.tail (proj i)))))
  have := rfindPos this
  exact this.of_eq <| by { intro v; simp }

end Nat.PartArith
