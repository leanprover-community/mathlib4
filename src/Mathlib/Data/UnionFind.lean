/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Tactic.Basic
import Mathlib.Data.Array.Basic

structure UFModel (n) where
  parent : Fin n → Fin n
  rank : Nat → Nat
  rank_lt : ∀ i, (parent i).1 ≠ i → rank i < rank (parent i)

namespace UFModel

def empty : UFModel 0 where
  parent i := i.elim0
  rank i := 0
  rank_lt i := i.elim0

def push {n} (m : UFModel n) (k) (le : n ≤ k) : UFModel k where
  parent i :=
    if h : i < n then
      let ⟨a, h'⟩ := m.parent ⟨i, h⟩
      ⟨a, lt_of_lt_of_le h' le⟩
    else i
  rank i := if h : i < n then m.rank i else 0
  rank_lt i := by
    simp; split <;> rename_i h
    · simp [(m.parent ⟨i, h⟩).2, h]; exact m.rank_lt _
    · intro.

def setParent {n} (m : UFModel n) (x y : Fin n) (h : m.rank x < m.rank y) : UFModel n where
  parent i := if x.1 = i then y else m.parent i
  rank := m.rank
  rank_lt i := by
    simp; split <;> rename_i h'
    · rw [← h']; exact fun _ => h
    · exact m.rank_lt i

def setParentBump {n} (m : UFModel n) (x y : Fin n)
  (ne : x.1 ≠ y) (H : m.rank x ≤ m.rank y) (hroot : (m.parent y).1 = y) : UFModel n where
  parent i := if x.1 = i then y else m.parent i
  rank i := if y.1 = i ∧ m.rank x = m.rank y then m.rank y + 1 else m.rank i
  rank_lt i := by
    simp; split <;>
      (rename_i h₁; simp [h₁]; split <;> rename_i h₂ <;>
        (intro h; simp [h] at h₂ <;> simp [h₁, h₂, h]))
    · simp [← h₁]; split <;> rename_i h₃
      · rw [h₃]; apply Nat.lt_succ_self
      · exact lt_of_le_of_ne H h₃
    · have := Fin.eq_of_val_eq h₂.1; subst this
      simp [hroot] at h
    · have := m.rank_lt i h
      split <;> rename_i h₃
      · rw [h₃.1]; exact Nat.lt_succ_of_lt this
      · exact this

end UFModel

structure UFNode (α : Type _) where
  parent : Nat
  value : α
  rank : Nat

inductive UFModel.Agrees (arr : Array α) (f : α → β) : ∀ {n}, (Fin n → β) → Prop
| mk : Agrees arr f fun i => f (arr.get i)

namespace UFModel.Agrees

theorem mk' {arr : Array α} {f : α → β} {n} {g : Fin n → β}
  (e : n = arr.size)
  (H : ∀ i h₁ h₂, f (arr.get ⟨i, h₁⟩) = g ⟨i, h₂⟩) :
  Agrees arr f g := by
    cases e
    have : (fun i => f (arr.get i)) = g := by funext ⟨i, h⟩; apply H
    cases this; constructor

theorem size_eq {arr : Array α} {m : Fin n → β} (H : Agrees arr f m) :
  n = arr.size := by cases H; rfl

theorem get_eq {arr : Array α} {n} {m : Fin n → β} (H : Agrees arr f m) :
  ∀ i h₁ h₂, f (arr.get ⟨i, h₁⟩) = m ⟨i, h₂⟩ := by
  cases H; exact fun i h _ => rfl

theorem get_eq' {arr : Array α} {m : Fin arr.size → β} (H : Agrees arr f m)
  (i) : f (arr.get i) = m i := H.get_eq ..

theorem empty {f : α → β} {g : Fin 0 → β} : Agrees #[] f g := mk' rfl λ.

theorem push {arr : Array α} {n} {m : Fin n → β} (H : Agrees arr f m)
  (k) (hk : k = n + 1) (x) (m' : Fin k → β)
  (hm₁ : ∀ (i : Fin k) (h : i < n), m' i = m ⟨i, h⟩)
  (hm₂ : ∀ (h : n < k), f x = m' ⟨n, h⟩) : Agrees (arr.push x) f m' := by
  cases H
  have : k = (arr.push x).size := by simp [hk]
  refine mk' this fun i h₁ h₂ => ?_
  simp [Array.get_push]; split <;> (rename_i h; simp at hm₁ ⊢)
  · exact (hm₁ ⟨i, h₂⟩ _).symm
  · simp at h₁
    cases le_antisymm (le_of_not_lt h) (Nat.le_of_lt_succ h₁); apply hm₂

theorem set {arr : Array α} {n} {m : Fin n → β} (H : Agrees arr f m)
  {i : Fin arr.size} {x} {m' : Fin n → β}
  (hm₁ : ∀ (j : Fin n) (h : j.1 ≠ i), m' j = m j)
  (hm₂ : ∀ (h : i < n), f x = m' ⟨i, h⟩) : Agrees (arr.set i x) f m' := by
  cases H
  refine mk' (by simp) fun j hj₁ hj₂ => ?_
  have := arr.get?_set i j x
  rw [Array.get?_eq_get _ _ hj₁, Array.get?_eq_get _ _ hj₂] at this
  revert this; split <;> (rename_i h; simp; intro h'; rw [h'])
  · cases h; apply hm₂
  · rw [hm₁]; exact Ne.symm h

end UFModel.Agrees

def UFModel.Models (arr : Array (UFNode α)) {n} (m : UFModel n) :=
  UFModel.Agrees arr (·.parent) (fun i => m.parent i) ∧
  UFModel.Agrees arr (·.rank) (fun i : Fin n => m.rank i)

namespace UFModel.Models

theorem size_eq {arr : Array (UFNode α)} {n} {m : UFModel n} (H : m.Models arr) :
  n = arr.size := H.1.size_eq

theorem parent_eq {arr : Array (UFNode α)} {n} {m : UFModel n} (H : m.Models arr)
  (i h₁ h₂) : (arr.get ⟨i, h₁⟩).parent = m.parent ⟨i, h₂⟩ := H.1.get_eq ..

theorem parent_eq' {arr : Array (UFNode α)} {m : UFModel arr.size} (H : m.Models arr)
  (i) : (arr.get i).parent = m.parent i := H.parent_eq ..

theorem rank_eq {arr : Array (UFNode α)} {n} {m : UFModel n} (H : m.Models arr)
  (i) : (arr.get i).rank = m.rank i := H.2.get_eq _ _ (by rw [H.size_eq]; exact i.2)

theorem empty : UFModel.empty.Models (α := α) #[] := ⟨Agrees.empty, Agrees.empty⟩

theorem push {arr : Array (UFNode α)} {n} {m : UFModel n} (H : m.Models arr)
  (k) (hk : k = n + 1) (x) :
  (m.push k (hk ▸ Nat.le_add_right ..)).Models (arr.push ⟨n, x, 0⟩) := by
  apply H.imp <;>
  · intro H
    refine H.push _ hk _ _ (fun i h => ?_) (fun h => ?_) <;>
    simp [UFModel.push, h, lt_irrefl]

theorem setParent {arr : Array (UFNode α)} {n} {m : UFModel n} (hm : m.Models arr)
  (i j H hi x) (hp : x.parent = j.1) (hrk : x.rank = (arr.get ⟨i.1, hi⟩).rank) :
  (m.setParent i j H).Models (arr.set ⟨i.1, hi⟩ x) :=
  ⟨hm.1.set
      (fun k h => by simp [UFModel.setParent, h.symm])
      (fun h => by simp [UFModel.setParent, hp]),
    hm.2.set (fun _ _ => rfl) (fun _ => hrk.trans $ hm.2.get_eq ..)⟩

end UFModel.Models

structure UnionFind (α) where
  arr : Array (UFNode α)
  model : ∃ (n : _) (m : UFModel n), m.Models arr

namespace UnionFind

def size (self : UnionFind α) := self.arr.size

theorem model' (self : UnionFind α) : ∃ (m : UFModel self.arr.size), m.Models self.arr := by
  let ⟨n, m, hm⟩ := self.model; cases hm.size_eq; exact ⟨m, hm⟩

def empty : UnionFind α where
  arr := #[]
  model := ⟨_, _, UFModel.Models.empty⟩

def mkEmpty (c : Nat) : UnionFind α where
  arr := Array.mkEmpty c
  model := ⟨_, _, UFModel.Models.empty⟩

def rank (self : UnionFind α) (i : Nat) : Nat :=
  if h : i < self.size then (self.arr.get ⟨i, h⟩).rank else 0

def rankMaxAux (self : UnionFind α) : ∀ (i : Nat),
  {k : Nat // ∀ j < i, ∀ h, (self.arr.get ⟨j, h⟩).rank ≤ k}
| 0 => ⟨0, λ.⟩
| i+1 => by
  let ⟨k, H⟩ := rankMaxAux self i
  refine ⟨max k (if h : _ then (self.arr.get ⟨i, h⟩).rank else 0), fun j hj h => ?_⟩
  match j, lt_or_eq_of_le (Nat.le_of_lt_succ hj) with
  | j, Or.inl hj => exact le_trans (H _ hj h) (le_max_left _ _)
  | _, Or.inr rfl => simp [h, le_max_right]

def rankMax (self : UnionFind α) := (rankMaxAux self self.size).1 + 1

theorem lt_rankMax' (self : UnionFind α) (i : Fin self.size) :
  (self.arr.get i).rank < self.rankMax :=
  Nat.lt_succ_iff.2 $ (rankMaxAux self self.size).2 _ i.2 _

theorem lt_rankMax (self : UnionFind α) (i : Nat) : self.rank i < self.rankMax := by
  simp [rank]; split; {apply lt_rankMax'}; apply Nat.succ_pos

theorem rank_eq (self : UnionFind α) {n} {m : UFModel n} (H : m.Models self.arr)
  {i} (h : i < self.size) : self.rank i = m.rank i := by
  simp [rank, h, H.rank_eq]

theorem rank_lt (self : UnionFind α) {i} : (self.arr.get i).parent ≠ i →
  self.rank i < self.rank (self.arr.get i).parent := by
  let ⟨m, hm⟩ := self.model'
  simp [hm.parent_eq', hm.rank_eq, rank, size, i.2, (m.parent i).2]
  exact m.rank_lt i

theorem parent_lt (self : UnionFind α) (i) : (self.arr.get i).parent < self.size := by
  let ⟨m, hm⟩ := self.model'
  simp [hm.parent_eq', size, (m.parent i).2]

def push (self : UnionFind α) (x : α) : UnionFind α where
  arr := self.arr.push ⟨self.arr.size, x, 0⟩
  model := let ⟨m, hm⟩ := self.model'; ⟨_, _, hm.push _ rfl _⟩

def findAux (self : UnionFind α) (x : Fin self.size) :
  (s : Array (UFNode α)) ×' (root : Fin s.size) ×'
    ∃ n, ∃ (m : UFModel n) (m' : UFModel n),
      m.Models self.arr ∧ m'.Models s ∧ m'.rank = m.rank ∧
      (∃ hr, (m'.parent ⟨root, hr⟩).1 = root) ∧
      m.rank x ≤ m.rank root := by
  let y := (self.arr.get x).parent
  refine if h : y = x then ⟨self.arr, x, ?a⟩ else
    have := Nat.sub_lt_sub_left (self.lt_rankMax x) (self.rank_lt h)
    let ⟨arr₁, root, H⟩ := self.findAux ⟨y, self.parent_lt x⟩
    have hx := ?hx
    let arr₂ := arr₁.set ⟨x, hx⟩ {arr₁.get ⟨x, hx⟩ with parent := root}
    ⟨arr₂, ⟨root, by simp [root.2]⟩, ?b⟩
  -- start proof
  case a =>
    let ⟨m, hm⟩ := self.model'
    exact ⟨_, m, m, hm, hm, rfl, ⟨x.2, by rwa [← hm.parent_eq']⟩, le_refl _⟩
  all_goals let ⟨n, m, m', hm, hm', e, ⟨_, hr⟩, le⟩ := H
  case hx => exact hm'.size_eq ▸ hm.size_eq.symm ▸ x.2
  case b =>
    let x' : Fin n := ⟨x, hm.size_eq ▸ x.2⟩
    let root : Fin n := ⟨root, hm'.size_eq.symm ▸ root.2⟩
    have hy : (UFModel.parent m x').1 = y := by rw [← hm.parent_eq x x.2 x'.2]; rfl
    have := m.rank_lt x'; rw [hy] at this
    have := lt_of_lt_of_le (this h) le
    refine ⟨n, m, _, hm,
      hm'.setParent x' root (by rw [e]; exact this) hx _ rfl rfl, e,
      ⟨root.2, ?_⟩, le_of_lt this⟩
    have := show x.1 ≠ root from mt (congrArg _) (ne_of_lt this)
    simp [UFModel.setParent, this, hr]
termination_by _ α self x => self.rankMax - self.rank x

def find (self : UnionFind α) (x : Fin self.size) :
  (s : UnionFind α) × (root : Fin s.size) ×'
    s.size = self.size ∧ (s.arr.get root).parent = root :=
  let ⟨s, root, H⟩ := self.findAux x
  have : _ ∧ s.size = self.size ∧ (s.get root).parent = root :=
    let ⟨n, _, m', hm, hm', _, ⟨_, hr⟩, _⟩ := H
    ⟨⟨n, m', hm'⟩, hm'.size_eq.symm.trans hm.size_eq, by rwa [hm'.parent_eq]⟩
  ⟨⟨s, this.1⟩, root, this.2⟩

def link (self : UnionFind α) (x y : Fin self.size)
  (yroot : (self.arr.get y).parent = y) : UnionFind α := by
  refine if ne : x.1 = y then self else
    let nx := self.arr.get x
    let ny := self.arr.get y
    if h : ny.rank < nx.rank then
      ⟨self.arr.set y {ny with parent := x}, ?a⟩
    else
      let arr₁ := self.arr.set x {nx with parent := y}
      let arr₂ := if e : nx.rank = ny.rank then
        arr₁.set ⟨y, by simp; exact y.2⟩ {ny with rank := ny.rank + 1}
      else arr₁
      ⟨arr₂, ?b⟩
  -- start proof
  case a =>
    let ⟨m, hm⟩ := self.model'
    simp [hm.rank_eq] at h
    exact ⟨_, _, hm.setParent y x h _ _ rfl rfl⟩
  case b =>
    let ⟨m, hm⟩ := self.model'; let n := self.size
    simp [hm.rank_eq] at h; simp [hm.parent_eq'] at yroot
    refine ⟨_, m.setParentBump x y ne h yroot, ?_⟩
    let parent (i : Fin n) := (if x.1 = i then y else m.parent i).1
    have : UFModel.Agrees arr₁ (·.parent) parent :=
      hm.1.set (fun i h => by simp; rw [if_neg h.symm]) (fun h => by simp)
    have H1 : UFModel.Agrees arr₂ (·.parent) parent := by
      simp; split
      · exact this.set (fun i h => by simp [h.symm]) (fun h => by simp [ne, hm.parent_eq'])
      · exact this
    have : UFModel.Agrees arr₁ (·.rank) (fun i : Fin n => m.rank i) :=
      hm.2.set (fun i h => by simp) (fun h => by simp [hm.rank_eq])
    let rank (i : Fin n) := if y.1 = i ∧ m.rank x = m.rank y then m.rank y + 1 else m.rank i
    have H2 : UFModel.Agrees arr₂ (·.rank) rank := by
      simp; split <;> (rename_i xy; simp [hm.rank_eq] at xy; simp [xy])
      · exact this.set (fun i h => by rw [if_neg h.symm]) (fun h => by simp [hm.rank_eq])
      · exact this
    exact ⟨H1, H2⟩

def union (self : UnionFind α) (x y : Fin self.size) : UnionFind α :=
  let ⟨self₁, rx, e, _⟩ := self.find x
  let ⟨self₂, ry, e, hry⟩ := self₁.find ⟨y, by rw [e]; exact y.2⟩
  self₂.link ⟨rx, by rw [e]; exact rx.2⟩ ry hry
