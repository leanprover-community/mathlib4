import Mathlib.Algebra.Operad.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.GroupTheory.Perm.Basic

section Operad

/-- An operad is a set of operations that are closed under composition and have an identity.
  The composition operation has to be associative and commutative in the proper sense:
  - Composing a into b and then into c is assocative as to the order of composition.
  - Composing a and b into two different arguments of c is commutative as to which is
    composed in first.

  Operads are sometimes defined instead with "superposition" as the basic operation, where
  all n arguments are composed at once instead of just one. This is an equivalent structure,
  as superposition can be built from progressively composing each in and using identity in
  the other arguments. This notion of superposition is rather unwieldly in Lean, since
  the *type* of the result is the sum of the arities of all the arguments, and associativity
  laws require statements about partial sums of lists of arities.
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

end Operad

section SymmOperad

open Equiv

def PermFinPadLeftRight {n : ℕ} (p : Perm (Fin n)) (m k : ℕ) : (Perm (Fin (m + n + k))) :=
  Perm.extendDomain p (p := fun x ↦ m ≤ x ∧ x < m + n) ⟨
    fun x ↦ ⟨(Fin.natAdd m x).castAdd k, by simp [Fin.natAdd, Fin.addNat]⟩,
    fun x ↦ ⟨(Fin.castLT x.1 (show x < n + m by omega)).subNat m (by simp [x.2.1]),
      Nat.sub_lt_left_of_lt_add x.2.1 x.2.2⟩,
    fun x ↦ by simp,
    fun x ↦ by
      ext
      simp only [Fin.coe_subNat, Fin.coe_castLT, Fin.natAdd_mk, Fin.castAdd_mk]
      omega
    ⟩

/- permfindPadTo is equal to permfinPadLeftRight, but with a different expression type. It
  starts the permutation Sm at location k out of n, and creates a length of (n-m+1). -/
def PermFinPadTo {m : ℕ} (p : Perm (Fin m)) (n : ℕ) (k : Fin n) : Perm (Fin (n+m-1)) :=
  have h : (k + m + (n - (k + 1))) = n + m - 1 := by
    omega
  h ▸ PermFinPadLeftRight p k (n-(k+1))

/-- A symmetric operad is an `Operad` that admits a permutation operation on arguments, with
 appropriate action on resulting compositions. -/
class SymmOperad (A) extends Operad A, SigmaMulAction (Perm <| Fin ·) A where
  /- Permutations on the left side of function composition permute where it gets composed. -/
  perm_left {n m : ℕ} (s : Perm (Fin n)) (k : Fin n) (x : A n) (y : A m) :
    compose (s •σ[ toSigmaMulAction ] x) k y = compose x (s k) y
  /- Permutations on the right side of function composition extend to a
    permutation of the whole object. -/
  perm_right {n m : ℕ} (s : Perm (Fin m)) (k : Fin n) (x : A n) (y : A m) :
    compose x k (s •σ[ toSigmaMulAction ] y) = (PermFinPadTo s n k) • (compose x k y)

end SymmOperad
