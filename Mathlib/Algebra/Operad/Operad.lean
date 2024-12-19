import Mathlib.Algebra.Operad.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Card

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

/-- Extend a permutation on Fin n to a permutation on Fim (m+n+k), by acting as the identity
 on the first m and last k elements. -/
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

/-- PermfindPadTo is morally equivalent to PermfinPadLeftRight, but with a different type. It
  starts the permutation Sm at location k out of n, and creates a perm of length (n+m-1). -/
def PermFinPadTo {m : ℕ} (p : Perm (Fin m)) (n : ℕ) (k : Fin n) : Perm (Fin (n+m-1)) :=
  have h : (k + m + (n - (k + 1))) = n + m - 1 := by
    omega
  h ▸ PermFinPadLeftRight p k (n-(k+1))

def PermFinPadAt_core {m n : ℕ} (p : Perm (Fin m)) (hn : 0 < n) (k : Fin m) (x : Fin (m+n-1)) :
    Fin (m+n-1) :=
  if h : k.1 ≤ x.1 ∧ x.1 ≤ k + n - 1 then
    ⟨p k + x - k.1, by omega⟩
  else (
    let x' := if h₂ : x < k.1 then p ⟨x.1, h₂.trans k.2⟩ else p ⟨x.1 - (n-1), by omega⟩;
    if h₃ : x' < p k then ⟨x', by omega⟩ else ⟨x'+n-1, by omega⟩
  )

-- set_option maxHeartbeats 400000 in
theorem PermFinPadAt_core.LeftInverse {m n : ℕ} (p : Perm (Fin m)) (hn : 0 < n) (k : Fin m) :
    Function.LeftInverse (PermFinPadAt_core p.symm hn (p k)) (PermFinPadAt_core p hn k) := by
  intro x
  rw [PermFinPadAt_core]
  split
  · suffices (k:ℕ) ≤ ↑x ∧ (x:ℕ) ≤ ↑k + n - 1 by
      suffices h : (PermFinPadAt_core p hn k x : ℕ) = (p k) + x - k ∧ (k:ℕ) ≤ x by
        ext
        simp only [symm_apply_apply]
        omega
      simp [PermFinPadAt_core, this]
    rename_i h₁
    rcases h₁ with ⟨h₁,h₂⟩
    by_contra h₃
    rw [PermFinPadAt_core, dif_neg h₃] at h₁ h₂
    rw [Decidable.not_and_iff_or_not_not] at h₃
    push_neg at h₃
    have h₄ : p ⟨x - (n-1), proof_3 hn k x⟩ ≠ p k := by
      simpa using Fin.ne_of_val_ne (show x - (n-1) ≠ k by omega)
    rcases h₃ with h₃|h₃
    · simp only [dif_pos h₃] at h₁ h₂
      split at h₁
      <;> rename_i h₄
      <;> simp only [h₄, ↓reduceDIte] at h₂
      · dsimp at h₁
        omega
      · refine (?_:¬_) (show (p ⟨↑x, proof_2 k x (of_eq_true (eq_true h₃))⟩) = p k by omega)
        simpa [Fin.ext_iff] using Nat.ne_of_lt h₃
    · simp [show ¬(x:ℕ) < k by omega] at h₁ h₂
      split at h₁
      <;> rename_i h₄
      <;> simp only [h₄, ↓reduceDIte] at h₂
      <;> simp only [Fin.val_fin_le] at h₁
      <;> omega
  · rename_i h₁
    rw [Decidable.not_and_iff_or_not_not] at h₁
    push_neg at h₁
    rcases h₁ with h₁|h₁
    · simp only [dif_pos h₁, symm_apply_apply]
      by_cases h₂ : (k:ℕ) ≤ x
      · simp [PermFinPadAt_core, h₂, Nat.not_lt.mpr h₂]
        have h₃ : ¬(x:ℕ) ≤ ↑k + n - 1 := by
          by_contra! h₃
          simp only [PermFinPadAt_core, h₂, Nat.not_lt.mpr h₂, h₃, true_and, ↓reduceDIte] at h₁
          omega
        simp only [PermFinPadAt_core, h₂, Nat.not_lt.mpr h₂, h₃, and_false, ↓reduceDIte] at h₁
        simp only [h₃, ↓reduceDIte, and_false]
        split at h₁
        · rename_i h₄
          simp only [h₄, ↓reduceDIte, Fin.eta, symm_apply_apply]
          split
          · exfalso
            rename_i h₅
            simp only [Fin.lt_def] at h₅
            omega
          · ext
            dsimp
            omega
        · absurd h₁
          dsimp
          omega
      · simp [PermFinPadAt_core, h₂, Nat.gt_of_not_le h₂]
        split
        · simpa using fun h ↦ (h₂ h).elim
        · rename_i h₃
          simp only [PermFinPadAt_core, h₂, Nat.gt_of_not_le h₂, h₃, false_and, ↓reduceDIte] at h₁
          omega
    · simp only [dif_neg (show ¬(PermFinPadAt_core p hn k x : ℕ) < p k by omega), symm_apply_apply]
      by_cases h₂ : (k:ℕ) ≤ x
      · simp only [PermFinPadAt_core, h₂, true_and, dif_neg (Nat.not_lt.mpr h₂)]
        have h₃ : ¬(x:ℕ) ≤ ↑k + n - 1 := by
          by_contra! h₃
          simp only [PermFinPadAt_core, h₂, Nat.not_lt.mpr h₂, h₃, true_and, ↓reduceDIte] at h₁
          omega
        simp only [PermFinPadAt_core, h₂, Nat.not_lt.mpr h₂, h₃, and_false, ↓reduceDIte] at h₁
        simp only [dif_neg h₃]
        split at h₁
        · absurd h₁
          dsimp
          omega
        · rename_i h₄
          simp only [dif_neg h₄]
          generalize_proofs pf1 pf2
          have h₆ : (⟨↑(p ⟨↑x - (n - 1), pf1⟩) + n - 1 - (n - 1), pf2⟩ : Fin m) =
              p ⟨↑x - (n - 1), pf1⟩ := by
            ext
            dsimp
            omega
          split
          · exfalso
            rename_i h₅
            simp only [h₆, symm_apply_apply, Fin.lt_def] at h₅
            omega
          · rename_i h₅
            simp only [h₆, symm_apply_apply, Fin.ext_iff]
            omega
      · simp only [PermFinPadAt_core, h₂, false_and, ↓reduceDIte, Nat.gt_of_not_le h₂]
        split
        · rename_i h₃
          simp only [h₂, false_and]
          simp only [PermFinPadAt_core, h₂, false_and, ↓reduceDIte, Nat.gt_of_not_le h₂, h₃] at h₁
          omega
        · rename_i h₃
          simp only [PermFinPadAt_core, h₂, Nat.gt_of_not_le h₂, h₃, false_and, ↓reduceDIte] at h₁
          dsimp
          generalize_proofs pf1 pf2 pf3 pf4
          have h₄ : (⟨(p ⟨↑x, pf1⟩) + n - 1 - (n - 1), pf2⟩ : Fin m) = p ⟨↑x, pf1⟩ := by
            ext
            dsimp
            omega
          simpa [h₄] using fun h ↦ (h₂ h).elim

/-- PermfindPadAt takes the permutation in Sm and "expands" location k out of m, into a block
 of n indices that get permuted together, and creates a perm of length (m+n-1).-/
@[irreducible]
def PermFinPadAt {n m : ℕ} (p : Perm (Fin m)) (hn : 0 < n) (k : Fin m) : Perm (Fin (m+n-1)) :=
  ⟨PermFinPadAt_core p hn k, PermFinPadAt_core p.symm hn (p k),
    PermFinPadAt_core.LeftInverse p hn k,
  by
    apply Function.LeftInverse.rightInverse_of_card_le (PermFinPadAt_core.LeftInverse p hn k)
    simp only [Fintype.card_fin, le_refl]⟩

/-- A symmetric operad is an `Operad` that admits a permutation operation on arguments, with
 appropriate action on resulting compositions. -/
class SymmOperad (A) extends Operad A, SigmaMulAction (Perm <| Fin ·) A where
  /- Permutations on the left side of function composition permute where it gets composed. -/
  perm_left {n m : ℕ} (s : Perm (Fin n)) (k : Fin n) (hm : 0 < m) (x : A n) (y : A m) :
    compose (s •σ[ toSigmaMulAction ] x) k y =
      (PermFinPadAt s hm k) •σ[ toSigmaMulAction ] (compose x (s k) y)
  /- Permutations on the right side of function composition extend to a
    permutation of the whole object. -/
  perm_right {n m : ℕ} (s : Perm (Fin m)) (k : Fin n) (x : A n) (y : A m) :
    compose x k (s •σ[ toSigmaMulAction ] y) = (PermFinPadTo s n k) • (compose x k y)

end SymmOperad
