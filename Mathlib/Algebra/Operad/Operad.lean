/-
Copyright (c) 2024 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Algebra.Operad.Basic
import Mathlib.Algebra.Operad.Perm

/-! Defines `Operad` and `SymmOperad`. An `Operad` is a ℕ-graded set of operations that are
  closed under composition, with an identity, that obey the "natural" commutative and associative
  constraints - the ones satisfied by composition of arbitrary multi-argument functions.

  A `SymmOperad` is an `Operad` equipped with a `MulAction` by `Perm (Fin n)` for all n, that
  rearrange the arguments in the natural way.
-/

section Operad

/-- An `Operad` is a ℕ-graded set of operations that are closed under composition and
  with an identity. The composition operation has to be appropriately associative and
  commutative:
  - Composing a into b and then into c is assocative as to the order of composition.
  - Composing a and b into two different arguments of c is commutative as to which is
    composed in first.

  Operads are sometimes defined instead with "superposition" as the basic operation, where
  all n arguments are composed at once instead of just one. This is an equivalent structure,
  as superposition can be built from progressively composing each in and using identity in
  the other arguments. This notion of superposition is rather unwieldly in Lean, since
  the *type* of the result is the sum of the arities of all the arguments, and associativity
  laws require statements about partial sums of lists of arities. Also note this kind of
  superposition is distinct from `Superposable`, which combines the inputs, instead of adding
  the arities.
  -/
class Operad (A) extends MultiComposable A, OneGradedOne A where
  /- The identity element 'one' doesn't change under left composition. -/
  id_left (a : Sigma A) : 1 ∘[0] a = a
  /- The identity element 'one' doesn't change under right composition. -/
  id_right (a : Sigma A) (p : Fin a.fst) : a ∘[p] 1 = a
  /- Composing f3 into f2 and then into f1 is associative. -/
  assoc (a b c : Sigma A) (p1 : Fin a.fst) (p2 : Fin b.fst) :
    a ∘[p1] (b ∘[p2] c) = (a ∘[p1] b) ∘[ p1.hAdd p2 ] c
  /- Composing argument into two different holes is a right-commutative operation. This statement
   assumes that p1 is less than p2; this is necessary because the indices get shifted over. -/
  comm {a : Sigma A} (b c : Sigma A) {p1 p2 : Fin a.fst} (hp : p1.val < p2.val) :
    let p1' : Fin (a.fst + c.fst - 1) := ⟨p1, by omega⟩;
    let p2' : Fin (a.fst + b.fst - 1) := ⟨p2 + b.fst - 1, by omega⟩;
    (a ∘[p1] b) ∘[ p2' ] c = (a ∘[p2] c) ∘[ p1' ] b

variable {A} [Operad A]

@[simp]
theorem id_composeAt (a : Sigma A) : 1 ∘[0] a = a :=
  Operad.id_left a

@[simp]
theorem composeAt_id (a : Sigma A) (p : Fin a.fst) : a ∘[p] 1 = a :=
  Operad.id_right a p

/-- Composition in an `Operad` is associative, as long as they go into each other's slots. -/
theorem composeAt_assoc (a b c : Sigma A) (p1 : Fin a.fst) (p2 : Fin b.fst) :
    a ∘[p1] (b ∘[p2] c) = (a ∘[p1] b) ∘[ p1.hAdd p2 ] c :=
  Operad.assoc a b c p1 p2

/- Alias for `composeAt_assoc` where the arities are separate parameters. -/
theorem composeAt_assoc_Fin {i j k : ℕ} (a : A i) (b : A j) (c : A k) (p1 : Fin i) (p2 : Fin j) :
    ⟨i,a⟩ ∘[p1] (⟨j,b⟩ ∘[p2] ⟨k,c⟩) = (⟨i,a⟩ ∘[p1] ⟨j,b⟩) ∘[ p1.hAdd p2 ] ⟨k,c⟩ :=
  Operad.assoc ⟨i,a⟩ ⟨j,b⟩ ⟨k,c⟩ p1 p2

/-- Composition on the right in an `Operad` commutes, as long as the two elements go into
 different slots. This version takes the two "left" slots and computes the other two. -/
theorem composeAt_comm_swap (a b c : Sigma A) {p1 p2 : Fin a.fst} (hp : p1.val < p2.val) :
    let p1' : Fin (a.fst + c.fst - 1) := ⟨p1, by omega⟩;
    let p2' : Fin (a.fst + b.fst - 1) := ⟨p2 + b.fst - 1, by omega⟩;
    (a ∘[p1] b) ∘[ p2' ] c = (a ∘[p2] c) ∘[ p1' ] b :=
  Operad.comm b c hp

/-- Like `composeAt_comm`, but with all four slot numbers as separate parameters. -/
theorem composeAt_comm_four (a b c : Sigma A) {p1 p2 : Fin a.fst}
  {p3 : Fin (a.fst + c.fst - 1)} {p4 : Fin (a.fst + b.fst - 1)}
  (hp12 : p1.val < p2) (hp31 : p3.val = p1) (hp42 : p4.val = p2 + b.fst - 1) :
    (a ∘[p1] b) ∘[ p4 ] c = (a ∘[p2] c) ∘[ p3 ] b := by
  convert Operad.comm b c hp12

/- Alias for `composeAt_comm_four` where the arities are separate parameters. -/
theorem composeAt_comm_Fin {i j k : ℕ} (a : A i) (b : A j) (c : A k) {p1 p2 : Fin i}
  {p3 : Fin (i + k - 1)} {p4 : Fin (i + j - 1)}
  (hp12 : p1.val < p2) (hp31 : p3.val = p1) (hp42 : p4.val = p2 + j - 1) :
    (⟨i,a⟩ ∘[p1] ⟨j,b⟩) ∘[ p4 ] ⟨k,c⟩ = (⟨i,a⟩ ∘[p2] ⟨k,c⟩) ∘[ p3 ] ⟨j,b⟩ :=
  composeAt_comm_four ⟨i,a⟩ ⟨j,b⟩ ⟨k,c⟩ hp12 hp31 hp42

/-- Composition on the right in an `Operad` commutes, as long as the two elements go into
 different slots. This version rewrites from the LHS to the RHS. -/
theorem composeAt_comm (a b c : Sigma A) {p1 : Fin a.fst} {p2 : Fin (a.fst + b.fst - 1)}
    (hp : p1 + b.fst < p2 + 1) :
    (a ∘[p1] b) ∘[p2] c = (a ∘[⟨p2 + 1 - b.fst, by omega⟩] c) ∘[@Fin.mk (_-1) p1 (by omega)] b := by
  apply composeAt_comm_four a b c <;> dsimp <;> omega

end Operad

section SymmOperad

open Equiv

/-- A symmetric operad is an `Operad` that admits a permutation operation on arguments, with
 appropriate action on resulting compositions. -/
class SymmOperad (A) extends Operad A, SigmaMulAction (Perm <| Fin ·) A where
  /- Permutations on the left side of function composition permute where it gets composed. -/
  perm_left {n m : ℕ} (s : Perm (Fin n)) (k : Fin n) (hm : 0 < m) (x : A n) (y : A m) :
    s • x ∘⟨k⟩ y = PermFinPadAt s hm (s.symm k) • (x ∘⟨s.symm k⟩ y)
  /- Permutations on the right side of function composition extend to a
    permutation of the whole object. -/
  perm_right {n m : ℕ} (s : Perm (Fin m)) (k : Fin n) (x : A n) (y : A m) :
    x ∘⟨k⟩ s • y = PermFinPadTo s n k • (x ∘⟨k⟩ y)

variable {A} [SymmOperad A]

--Need this as a hint to find the SMul instance
instance : ∀ (i : ℕ), MulAction (Perm (Fin i)) (A i) :=
  SigmaMulAction.act_at

open MultiComposable

/- Alias of `SymmOperad.perm_left` -/
theorem SymmOperad.smul_compose {n m : ℕ} (s : Perm (Fin n)) (k : Fin n)
    (hm : 0 < m) (x : A n) (y : A m) :
    s • x ∘⟨k⟩ y = PermFinPadAt s hm (s.symm k) • (x ∘⟨s.symm k⟩ y) :=
  SymmOperad.perm_left s k hm x y

/- Alias of `SymmOperad.perm_right` -/
theorem SymmOperad.compose_smul {n m : ℕ} (s : Perm (Fin m)) (k : Fin n) (x : A n) (y : A m) :
    x ∘⟨k⟩ s • y = PermFinPadTo s n k • (x ∘⟨k⟩ y):=
  SymmOperad.perm_right s k x y

end SymmOperad
