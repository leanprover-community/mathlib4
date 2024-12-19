import Mathlib.Algebra.Operad.Basic
import Mathlib.Algebra.Operad.Perm

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
  assoc (a : Sigma A) (b : Sigma A) (c : Sigma A) (p1 : Fin a.fst) (p2 : Fin b.fst) :
    a ∘[p1] (b ∘[p2] c) = (a ∘[p1] b) ∘[ p1.hAdd p2 ] c
  /- Composing argument into two different holes is a right-commutative operation. This statement
   assumes that p1 is less than p2; this is necessary because the indices get shifted over. -/
  comm {a : Sigma A} (b c : Sigma A) {p1 p2 : Fin a.fst} (hp : p1.val < p2.val) :
    let p1' : Fin (a.fst + c.fst - 1) := ⟨p1.val, by omega⟩;
    let p2' : Fin (a.fst + b.fst - 1) := ⟨p2 + b.fst - 1, by omega⟩;
    (a ∘[p1] b) ∘[ p2' ] c = (a ∘[p2] c) ∘[ p1' ] b

variable {A} [Operad A]

@[simp]
theorem Operad.id_composeAt (a : Sigma A) : 1 ∘[0] a = a :=
  Operad.id_left a

@[simp]
theorem Operad.composeAt_id (a : Sigma A) (p : Fin a.fst) : a ∘[p] 1 = a :=
  Operad.id_right a p

theorem Operad.composeAt_assoc (a : Sigma A) (p : Fin a.fst) : a ∘[p] 1 = a :=
  Operad.id_right a p

end Operad

section SymmOperad

open Equiv in
/-- A symmetric operad is an `Operad` that admits a permutation operation on arguments, with
 appropriate action on resulting compositions. -/
class SymmOperad (A) extends Operad A, SigmaMulAction (Perm <| Fin ·) A where
  /- Permutations on the left side of function composition permute where it gets composed. -/
  perm_left {n m : ℕ} (s : Perm (Fin n)) (k : Fin n) (hm : 0 < m) (x : A n) (y : A m) :
    compose (s •σ[ toSigmaMulAction ] x) k y =
      (PermFinPadAt s hm k) •σ[ toSigmaMulAction ] (compose x (s.symm k) y)
  /- Permutations on the right side of function composition extend to a
    permutation of the whole object. -/
  perm_right {n m : ℕ} (s : Perm (Fin m)) (k : Fin n) (x : A n) (y : A m) :
    compose x k (s •σ[ toSigmaMulAction ] y) = (PermFinPadTo s n k) • (compose x k y)

end SymmOperad
