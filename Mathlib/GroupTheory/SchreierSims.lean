import Mathlib.Data.List.Range
import Mathlib.Data.Vector

set_option autoImplicit true

def Vector.finRange (n : Nat) : Vector (Fin n) n := ⟨List.finRange n, by simp⟩
@[simp] theorem Vector.finRange_get : (finRange n).get i = i := sorry
@[simp] theorem Vector.get_map (v : Vector α n) : (v.map f).get i = f (v.get i) := sorry

def Vector.set (v : Vector α n) (i : Fin n) (a : α) : Vector α n :=
  ⟨v.1.set i a, sorry⟩

structure Perm (n : Nat) where
  map : Vector (Fin n) n
  inv : Vector (Fin n) n
  map_inv : ∀ i j : Fin n, inv.get i = j ↔ map.get j = i

attribute [simp] Perm.map_inv

namespace Perm

instance : ToString (Perm n) := ⟨fun p => toString p.map.toList⟩

def id (n : Nat) : Perm n where
  map := Vector.finRange n
  inv := Vector.finRange n
  map_inv i j := by constructor <;> (rintro rfl; ext; simp)

def mul (p q : Perm n) : Perm n where
  map := p.map.map q.map.get
  inv := q.inv.map p.inv.get
  map_inv i j := by simp only [Vector.get_map, map_inv]; rw [eq_comm]; simp

def symm (p : Perm n) : Perm n where
  map := p.inv
  inv := p.map
  map_inv := by simp

def toFun (p : Perm n) (i : Nat) : Nat :=
  if h : i < n then
    p.map.get ⟨i, h⟩
  else
    i

instance : CoeFun (Perm n) (fun _ => Nat → Nat) := ⟨toFun⟩

def succ (p : Perm n) : Perm (n + 1) where
  map := .cons 0 (p.map.map Fin.succ)
  inv := .cons 0 (p.inv.map Fin.succ)
  map_inv := sorry

def pred (p : Perm (n + 1)) (w : p 0 = 0) : Perm n where
  map := p.map.tail.map fun i => Fin.pred i sorry
  inv := p.inv.tail.map fun i => Fin.pred i sorry
  map_inv := sorry

end Perm

-- https://www.math.toronto.edu/~drorbn/Talks/CUMC-0807/NCGE.pdf

inductive SchreierSimsData : Nat → Type
| nil : SchreierSimsData 0
| cons : (data : Vector (Option (Perm (n + 1))) (n + 1)) →
    (∀ i p, p ∈ data.get i → p 0 = i) →
    SchreierSimsData n → SchreierSimsData (n + 1)

namespace SchreierSimsData

def mk : (n : Nat) → SchreierSimsData n
  | 0 => .nil
  | (n + 1) => .cons (.cons (some (.id _)) (.replicate n none)) sorry (mk n)

def size : SchreierSimsData n → Nat
  | .nil => 1
  | .cons qs _ d => (qs.toList.countP Option.isSome) * d.size

/--
Feed a permutation into a Schreier-Sims table.

Returns a list of natural numbers (TODO upgrade these to `Fin`?) `r`
and an optional pair `t? : Option (Perm n × SchreierSimsData n)`.

If the permutation `p` could be expressed as a product of entries already in the table,
then we will have `t? = none`,
and the numbers `r` indicate (how?) to write `p` as a product of the entries.
Otherwise, there will be exactly one more entry in `t?` than the original `d`,
and the numbers `r` indicate how to write `p` as a product of the new entries.
-/
def insert? (d : SchreierSimsData n) (p : Perm n) : List Nat × Option (Perm n × SchreierSimsData n) :=
  match d with
  | .nil => ([], none)
  | .cons qs w d =>
    let i := p.map.get 0
    match qs.get i with
    | some q =>
      let p' := Perm.mul p (Perm.symm q)
      let p'' := p'.pred sorry
      match d.insert? p'' with
      | (r, none) => (i :: r, none)
      | (r, some (z, d')) => (i :: r, some (z.succ, .cons qs w d'))
    | none => ([i], some (p, .cons (qs.set i p) sorry d))

def insert (d : SchreierSimsData n) (p : Perm n) : SchreierSimsData n :=
  match (d.insert? p).2 with
  | none => d
  | some (_, d) => d

def lookup (d : SchreierSimsData n) (p : Perm n) : Option (List Nat) :=
  match d.insert? p with
  | (r, none) => some r
  | _ =>  none

def contains (d : SchreierSimsData n) (p : Perm n) : Bool := (d.lookup p).isSome

/--
Return all "off-diagonal" entries in a Schreier-Sims table.
-/
def entries (d : SchreierSimsData n) : List (Perm n) := match d with
  | .nil => []
  | .cons qs _ d => (qs.toList.tail.filterMap id) ++ (d.entries.map Perm.succ)

-- We can remove `partial` here: if `insert?` returns a new table, it has exactly one more entry.
partial def insertSaturating (d : SchreierSimsData n) (p : Perm n) : SchreierSimsData n :=
  match (d.insert? p).2 with
  | none => d
  | some (r, d) =>
    let n := d.entries.map (Perm.mul · r) ++ d.entries.map (Perm.mul r ·)
    n.foldl (fun d q => d.insertSaturating q) d

end SchreierSimsData


def purple := [17, 26, 35, 3, 4, 5, 6, 7, 8, 2, 10, 11, 12, 13, 14, 15, 16, 44, 1, 19, 20, 21, 22,
  23, 24, 25, 43, 0, 28, 29, 30, 31, 32, 33, 34, 42, 36, 37, 38, 39, 40, 41, 9, 18, 27, 51, 48, 45,
  52, 49, 46, 53, 50, 47]
def white := [0, 1, 2, 3, 4, 5, 15, 24, 33, 9, 10, 8, 14, 23, 32, 38, 16, 17, 18, 19, 7, 13, 22, 31,
  37, 25, 26, 27, 28, 6, 12, 21, 30, 36, 34, 35, 11, 20, 29, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
  49, 50, 51, 52, 53]
def green := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
  24, 25, 26, 30, 31, 32, 33, 34, 35, 47, 46, 45, 38, 41, 44, 37, 40, 43, 36, 39, 42, 29, 28, 27,
  48, 49, 50, 51, 52, 53]
def blue := [2, 5, 8, 1, 4, 7, 0, 3, 6, 53, 52, 51, 9, 10, 11, 12, 13, 14, 18, 19, 20, 21, 22, 23,
  24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
  48, 49, 50, 17, 16, 15]
def red := [12, 1, 2, 21, 4, 5, 30, 7, 8, 11, 20, 29, 36, 13, 14, 15, 16, 17, 10, 19, 28, 39, 22,
  23, 24, 25, 26, 9, 18, 27, 42, 31, 32, 33, 34, 35, 45, 37, 38, 48, 40, 41, 51, 43, 44, 0, 46, 47,
  3, 49, 50, 6, 52, 53]
def yellow := [0, 1, 47, 3, 4, 50, 6, 7, 53, 9, 10, 11, 12, 13, 2, 17, 26, 35, 18, 19, 20, 21, 22,
  5, 16, 25, 34, 27, 28, 29, 30, 31, 8, 15, 24, 33, 36, 37, 14, 39, 40, 23, 42, 43, 32, 45, 46, 38,
  48, 49, 41, 51, 52, 44]

def liftFin (x : List Nat) (w : ∀ i ∈ x, i < n) : List (Fin n) :=
  x.attach.map fun p => ⟨p.1, w _ p.2⟩

macro "Perm.elab " n:term:max U:term : term =>
  `(({ map := ⟨liftFin $U (by decide), by decide⟩
       inv := ⟨liftFin ((List.range $n).map fun i => List.findIdx (· == i) $U) (by decide), by decide⟩
       map_inv := by decide } : Perm $n))

def Purple := Perm.elab 54 purple
def White := Perm.elab 54 white
def Green := Perm.elab 54 green
def Blue := Perm.elab 54 blue
def Red := Perm.elab 54 red
def Yellow := Perm.elab 54 yellow

def rubiks0 := SchreierSimsData.mk 54
def rubiks1 := rubiks0 |>.insertSaturating Purple
def rubiks2 := rubiks1 |>.insertSaturating Green
def rubiks3 := rubiks2 |>.insertSaturating Yellow
def rubiks4 := rubiks3 |>.insertSaturating White
def rubiks5 := rubiks4 |>.insertSaturating Blue
def rubiks6 := rubiks5 |>.insertSaturating Red

-- We need to get rid of `partial` above before we can actually prove anything.
-- example : rubiks1.entries.length = 3 := rfl

#eval rubiks6.size -- 43252003274489856000

def z := [1, 0] ++ (List.range 52).map (· + 2)
def Z : Perm 54 where
  map := ⟨z.map fun i => ⟨i, sorry⟩, by decide⟩
  inv := ⟨(List.range 54).map fun i => ⟨z.findIdx (· == i), sorry⟩, sorry⟩
  map_inv := sorry

#eval rubiks6.contains Z -- false

def p : Perm 54 := [White, Yellow, Purple, Purple, Green, Red, Yellow, Purple, Blue, Red, White, White, Yellow, Red, Blue].foldl Perm.mul (Perm.id 54)

#eval p -- [27, 26, 6, 48, 4, 5, 44, 43, 32, 42, 18, 47, 35, 46, 38, 33, 16, 11, 24, 19, 7, 13, 22, 28, 39, 25, 21, 0, 10, 17, 2, 1, 15, 14, 31, 30, 53, 52, 8, 3, 40, 37, 9, 34, 29, 51, 41, 36, 23, 49, 20, 45, 50, 12]
#eval rubiks6.lookup p -- some [27, 42, 4, 47, 0, 29, 9, 11, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 1, 0, 0, 1, 0, 0, 5, 2, 11, 7, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

#eval rubiks1.entries.length -- 3
#eval rubiks2.entries.length -- 66
#eval rubiks3.entries.length -- 153
#eval rubiks4.entries.length -- 216
#eval rubiks5.entries.length -- 239
#eval rubiks6.entries.length -- 239
