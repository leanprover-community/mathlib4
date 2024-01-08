import Mathlib.Data.List.Range

set_option autoImplicit true

@[simp] theorem List.finRange_get_cast {n : Nat} {i : Fin k} {h : k = (List.finRange n).length} :
    (List.finRange n).get (Fin.cast h i) = Fin.cast (by simp [h]) i := by
  ext
  cases i
  simp

structure Perm (n : Nat) where
  map : List (Fin n)
  inv : List (Fin n)
  map_length : map.length = n := by simp
  inv_length : inv.length = n := by simp
  map_inv : ∀ i j : Fin n,
    inv.get (Fin.cast inv_length.symm i) = j ↔ map.get (Fin.cast map_length.symm j) = i

attribute [simp] Perm.map_length Perm.inv_length Perm.map_inv

namespace Perm

def id (n : Nat) : Perm n where
  map := List.finRange n
  inv := List.finRange n
  map_inv i j := by constructor <;> (rintro rfl; ext; simp)

def mul (p q : Perm n) : Perm n where
  map := p.map.map fun i => q.map.get (Fin.cast q.map_length.symm i)
  inv := q.inv.map fun i => p.inv.get (Fin.cast p.inv_length.symm i)
  map_inv i j := by simp_rw [List.get_map, Fin.coe_cast, map_inv p, ← map_inv q]; rw [eq_comm]; rfl

def symm (p : Perm n) : Perm n where
  map := p.inv
  inv := p.map
  map_inv := by simp

def toFun (p : Perm n) (i : Nat) : Nat :=
  match p.map.get? i with
  | some j => j
  | none => i

instance : CoeFun (Perm n) (fun _ => Nat → Nat) := ⟨toFun⟩

def pred (p : Perm (n + 1)) (w : p 0 = 0) : Perm n where
  map := p.map.tail.map fun i => Fin.pred i sorry
  inv := p.inv.tail.map fun i => Fin.pred i sorry
  map_inv := sorry

end Perm

-- https://www.math.toronto.edu/~drorbn/Talks/CUMC-0807/NCGE.pdf
structure SchreierSimsData (n : Nat) where
  data : List (List (Option (Perm n)))
  data_length : data.length = n
  col_length : ∀ i, (data.get i).length = n - i
  spec : ∀ i j p, p ∈ (data.get i).get j → ∀ k < i, p k = k ∧ p i = j

namespace SchreierSimsData

def insert_aux (d : SchreierSimsData n) (p : Perm n) (k : Nat) : List Nat × Option (SchreierSimsData n) :=
  if h : n ≤ k then
    ([], none)
  else
    match (d.data.getD k []).getD (p k - k) none with
    | some q =>
      have : n - (k + 1) < n - k := by omega
      match insert_aux d (Perm.mul p (Perm.symm q)) (k + 1) with
      | ⟨r, d?⟩ => (p k :: r, d?)
    | none =>
    ([], some sorry)
termination_by insert_aux => n - k


def insert (d : SchreierSimsData n) (p : Perm n) : List (Fin n) × Option (SchreierSimsData n) := sorry
