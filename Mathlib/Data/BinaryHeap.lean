import Mathlib.Init.WF
import Mathlib.Data.Fin.Basic

/-- A max-heap data structure. -/
structure BinaryHeap (α) (lt : α → α → Bool) where
  arr : Array α

namespace BinaryHeap

/-- Core operation for binary heaps, expressed directly on arrays.
Given an array which is a max-heap, push item `i` down to restore the max-heap property. -/
def heapifyDown (lt : α → α → Bool) (a : Array α) (i : Fin a.size) :
  {a' : Array α // a'.size = a.size} :=
  let left := 2 * i.1 + 1
  let right := left + 1
  have left_le : i ≤ left := Nat.le_trans
    (by rw [Nat.succ_mul, Nat.one_mul]; exact Nat.le_add_left i i)
    (Nat.le_add_right ..)
  have right_le : i ≤ right := Nat.le_trans left_le (Nat.le_add_right ..)
  have i_le : i ≤ i := Nat.le_refl _
  have j : {j : Fin a.size // i ≤ j} := if h : left < a.size then
    if lt (a.get i) (a.get ⟨left, h⟩) then ⟨⟨left, h⟩, left_le⟩ else ⟨i, i_le⟩ else ⟨i, i_le⟩
  have j := if h : right < a.size then
    if lt (a.get j) (a.get ⟨right, h⟩) then ⟨⟨right, h⟩, right_le⟩ else j else j
  if h : i.1 = j then ⟨a, rfl⟩ else
    let a' := a.swap i j
    let j' := ⟨j, by rw [a.size_swap i j]; exact j.1.2⟩
    have : (skipLeft Fin.upRel).1 ⟨a'.size, j'⟩ ⟨a.size, i⟩ := by
      have H {n} (h : n = a.size) (j' : Fin n) (e' : i.1 < j'.1) :
        (skipLeft Fin.upRel).1 ⟨n, j'⟩ ⟨a.size, i⟩ := by
        subst n; exact PSigma.Lex.right _ e'
      exact H (a.size_swap i j) _ (lt_of_le_of_ne j.2 h)
    let ⟨a₂, h₂⟩ := heapifyDown lt a' j'
    ⟨a₂, h₂.trans (a.size_swap i j)⟩
termination_by invImage (fun ⟨_, _, a, i⟩ => (⟨a.size, i⟩ : (n : ℕ) ×' Fin n)) $ skipLeft Fin.upRel
decreasing_by assumption

@[simp] theorem size_heapifyDown (lt : α → α → Bool) (a : Array α) (i : Fin a.size) :
  (heapifyDown lt a i).1.size = a.size := (heapifyDown lt a i).2

/-- Core operation for binary heaps, expressed directly on arrays.
Construct a heap from an unsorted array, by heapifying all the elements. -/
def mkHeap (lt : α → α → Bool) (a : Array α) : {a' : Array α // a'.size = a.size} :=
  let rec loop : (i : Nat) → (a : Array α) → i ≤ a.size → {a' : Array α // a'.size = a.size}
  | 0, a, _ => ⟨a, rfl⟩
  | i+1, a, h =>
    let h := Nat.lt_of_succ_le h
    let a' := heapifyDown lt a ⟨i, h⟩
    let ⟨a₂, h₂⟩ := loop i a' ((heapifyDown ..).2.symm ▸ le_of_lt h)
    ⟨a₂, h₂.trans a'.2⟩
  loop (a.size / 2) a (Nat.div_le_self ..)

@[simp] theorem size_mkHeap (lt : α → α → Bool) (a : Array α) (i : Fin a.size) :
  (mkHeap lt a).1.size = a.size := (mkHeap lt a).2

/-- Core operation for binary heaps, expressed directly on arrays.
Given an array which is a max-heap, push item `i` up to restore the max-heap property. -/
def heapifyUp (lt : α → α → Bool) (a : Array α) (i : Fin a.size) :
  {a' : Array α // a'.size = a.size} :=
if i0 : i.1 = 0 then ⟨a, rfl⟩ else
  have : (i.1 - 1) / 2 < i := lt_of_le_of_lt (Nat.div_le_self ..) $
    Nat.sub_lt (Nat.pos_iff_ne_zero.2 i0) Nat.one_pos
  let j := ⟨(i.1 - 1) / 2, lt_trans this i.2⟩
  if lt (a.get j) (a.get i) then
    let a' := a.swap i j
    let ⟨a₂, h₂⟩ := heapifyUp lt a' ⟨j.1, by rw [a.size_swap i j]; exact j.2⟩
    ⟨a₂, h₂.trans (a.size_swap i j)⟩
  else ⟨a, rfl⟩
termination_by measure (·.2.2.2)
decreasing_by assumption

@[simp] theorem size_heapifyUp (lt : α → α → Bool) (a : Array α) (i : Fin a.size) :
  (heapifyUp lt a i).1.size = a.size := (heapifyUp lt a i).2

/-- `O(1)`. Build a new empty heap. -/
@[inline] def empty (lt) : BinaryHeap α lt := ⟨#[]⟩

instance (lt) : Inhabited (BinaryHeap α lt) := ⟨empty _⟩

/-- `O(1)`. Get the number of elements in a `BinaryHeap`. -/
@[inline] def size {lt} (self : BinaryHeap α lt) : Nat := self.1.size

/-- `O(log n)`. Insert an element into a `BinaryHeap`, preserving the max-heap property. -/
def insert {lt} (self : BinaryHeap α lt) (x : α) : BinaryHeap α lt where
  arr := let n := self.size;
    heapifyUp lt (self.1.push x) ⟨n, by rw [Array.size_push]; apply Nat.lt_succ_self⟩

@[simp] theorem size_insert {lt} (self : BinaryHeap α lt) (x : α) :
  (self.insert x).size = self.size + 1 := by
  simp [insert, size, size_heapifyUp]

/-- `O(1)`. Get the maximum element in a `BinaryHeap`. -/
def max {lt} (self : BinaryHeap α lt) : Option α := self.1.get? 0

/-- Auxiliary for `popMax`. -/
def popMaxAux {lt} (self : BinaryHeap α lt) : {a' : BinaryHeap α lt // a'.size = self.size - 1} :=
  match e: self.1.size with
  | 0 => ⟨self, by simp [size, e]⟩
  | n+1 =>
    have h0 := by rw [e]; apply Nat.succ_pos
    have hn := by rw [e]; apply Nat.lt_succ_self
    if hn0 : 0 < n then
      let a := self.1.swap ⟨0, h0⟩ ⟨n, hn⟩ |>.pop
      ⟨⟨heapifyDown lt a ⟨0, by rwa [Array.size_pop, Array.size_swap, e, Nat.add_sub_cancel]⟩⟩,
        by simp [size]⟩
    else
      ⟨⟨self.1.pop⟩, by simp [size]⟩

/-- `O(log n)`. Remove the maximum element from a `BinaryHeap`.
Call `max` first to actually retrieve the maximum element. -/
@[inline] def popMax {lt} (self : BinaryHeap α lt) : BinaryHeap α lt := self.popMaxAux

@[simp] theorem size_popMax {lt} (self : BinaryHeap α lt) :
  self.popMax.size = self.size - 1 := self.popMaxAux.2

/-- `O(log n)`. Return and remove the maximum element from a `BinaryHeap`. -/
def extractMax {lt} (self : BinaryHeap α lt) : Option α × BinaryHeap α lt :=
  (self.max, self.popMax)

end BinaryHeap

/-- `O(n)`. Convert an unsorted array to a `BinaryHeap`. -/
@[inline] def Array.toBinaryHeap (lt : α → α → Bool) (a : Array α) : BinaryHeap α lt where
  arr := BinaryHeap.mkHeap lt a

/-- `O(n log n)`. Sort an array using a `BinaryHeap`. -/
@[inline] def Array.heapSort (a : Array α) (lt : α → α → Bool) : Array α :=
  let gt y x := lt x y
  let rec loop (a : BinaryHeap α gt) (out : Array α) : Array α :=
    match e: a.max with
    | none => out
    | some x =>
      have : a.popMax.size < a.size := by
        simp; refine Nat.sub_lt (Decidable.of_not_not fun h: ¬ 0 < a.1.size => ?_) Nat.zero_lt_one
        simp [BinaryHeap.max, Array.get?, h] at e
      loop a.popMax (out.push x)
  loop (a.toBinaryHeap gt) #[]
termination_by measure (·.2.2.1.size)
decreasing_by assumption
