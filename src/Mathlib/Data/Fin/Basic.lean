import Mathlib.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Basic

instance : Subsingleton (Fin 0) where
  allEq := fun.

instance : Subsingleton (Fin 1) where
  allEq := fun ⟨0, _⟩ ⟨0, _⟩ => rfl

/-- If you actually have an element of `Fin n`, then the `n` is always positive -/
lemma Fin.size_positive : ∀ (x : Fin n), 0 < n
| ⟨x, h⟩ =>
  match Nat.eq_or_lt_of_le (Nat.zero_le x) with
  | Or.inl h_eq => h_eq ▸ h
  | Or.inr h_lt => Nat.lt_trans h_lt h

lemma Fin.ext {a b : Fin n} : a.val = b.val → a = b := by
  cases a; cases b; intro h; cases h; rfl

lemma Fin.ext_iff {a b : Fin n} : a = b ↔ a.val = b.val :=
  ⟨congrArg _, ext⟩

lemma Fin.size_positive' [Nonempty (Fin n)] : 0 < n :=
  ‹Nonempty (Fin n)›.elim fun i => Fin.size_positive i

lemma zero_lt_of_lt {a : Nat} : ∀ {x : Nat}, x < a -> 0 < a
| 0, h   => h
| x+1, h => Nat.lt_trans (Nat.zero_lt_succ x) h

lemma Fin.val_eq_of_lt {n a : Nat} (h : a < n) : (Fin.ofNat' a (zero_lt_of_lt h)).val = a := by
  simp only [Fin.ofNat', Nat.mod_eq_of_lt h]

@[simp] lemma Fin.one_val : (1 : Fin (n + 2)).val = 1 := by
  simp only [OfNat.ofNat, Fin.ofNat]
  rw [Nat.mod_eq_of_lt]
  exact Nat.succ_lt_succ (Nat.zero_lt_succ _)

lemma Fin.modn_def : ∀ (a : Fin n) (m : Nat),
  a % m = Fin.mk ((a.val % m) % n) (Nat.mod_lt (a.val % m) (a.size_positive))
| ⟨a, pa⟩, m => rfl

lemma Fin.mod_def : ∀ (a m : Fin n),
  a % m = Fin.mk ((a.val % m.val) % n) (Nat.mod_lt (a.val % m.val) (a.size_positive))
| ⟨a, pa⟩, ⟨m, pm⟩ => rfl

lemma Fin.add_def : ∀ (a b : Fin n),
  a + b = (Fin.mk ((a.val + b.val) % n) (Nat.mod_lt _ (a.size_positive)))
| ⟨a, pa⟩, ⟨b, pb⟩ => rfl

lemma Fin.mul_def : ∀ (a b : Fin n),
  a * b = (Fin.mk ((a.val * b.val) % n) (Nat.mod_lt _ (a.size_positive)))
| ⟨a, pa⟩, ⟨b, pb⟩ => rfl

lemma Fin.sub_def : ∀ (a b : Fin n),
  a - b = (Fin.mk ((a + (n - b)) % n) (Nat.mod_lt _ (a.size_positive)))
| ⟨a, pa⟩, ⟨b, pb⟩ => rfl

@[simp] lemma Fin.mod_eq (a : Fin n) : a % n = a := by
  apply Fin.eq_of_val_eq
  simp only [Fin.modn_def, Nat.mod_mod]
  exact Nat.mod_eq_of_lt a.isLt

@[simp] lemma Fin.mod_eq_val (a : Fin n) : a.val % n = a.val := by
  simp only [Fin.modn_def, Nat.mod_mod]
  exact Nat.mod_eq_of_lt a.isLt

theorem Fin.mod_eq_of_lt {a b : Fin n} (h : a < b) : a % b = a := by
  apply Fin.eq_of_val_eq
  simp only [Fin.mod_def]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt a.isLt]

/- The basic structures on `Fin` are predicated on `Fin n` being nonempty.
The Nonempty bound is there so that we can implement `Zero` in a way that satisfies
the requirements of the relevant typeclasses (for example, AddMonoid). If we were to
use `Fin n+1` for the `Zero` implementation, we would be shutting out some irreducible
definitions (notably USize.size) that are known to be inhabited, but not defined in terms
of `Nat.succ`. Since there's a blanket implementation of `∀ n, Inhabited (Fin n+1)` in
the prelude, this hopefully won't be a significant impediment. -/
section

variable {n : Nat} [Nonempty (Fin n)]

instance : OfNat (Fin n) a where
  ofNat := Fin.ofNat' a Fin.size_positive'

@[simp] lemma Fin.ofNat'_zero : (Fin.ofNat' 0 h : Fin n) = 0 := rfl
@[simp] lemma Fin.ofNat'_one : (Fin.ofNat' 1 h : Fin n) = 1 := rfl

lemma Fin.ofNat'_succ : (Fin.ofNat' i.succ Fin.size_positive' : Fin n) = (Fin.ofNat' i Fin.size_positive' : Fin n) + 1 := by
  revert n; exact fun
    | n + 2, h => ext (by simp [Fin.ofNat', Fin.add_def])
    | 1, h => Subsingleton.allEq _ _
    | 0, h => Subsingleton.allEq _ _

instance : AddCommSemigroup (Fin n) where
  add_assoc _ _ _ := by
    apply Fin.eq_of_val_eq
    simp only [Fin.add_def, Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]
  add_comm _ _ := by
    apply Fin.eq_of_val_eq
    simp only [Fin.add_def, Nat.add_comm]

instance : CommSemigroup (Fin n) where
  mul_assoc a b c := by
    apply Fin.eq_of_val_eq
    simp only [Fin.mul_def]
    generalize lhs : ((a.val * b.val) % n * c.val) % n = l
    generalize rhs : a.val * (b.val * c.val % n) % n = r
    rw [← Nat.mod_eq_of_lt c.isLt, (Nat.mul_mod (a.val * b.val) c.val n).symm] at lhs
    rw [← Nat.mod_eq_of_lt a.isLt, (Nat.mul_mod a.val (b.val * c.val) n).symm,
        ← Nat.mul_assoc] at rhs
    rw [← lhs, ← rhs]
  mul_comm (a b : Fin n) : a * b = b * a := by
    apply Fin.eq_of_val_eq; simp only [Fin.mul_def, Nat.mul_comm]

@[simp] lemma Fin.zero_def : (0 : Fin n).val = (0 : Nat) :=
  show (Fin.ofNat' 0 Fin.size_positive').val = (0 : Nat) by simp only [Fin.ofNat', Nat.zero_mod]

theorem Fin.mod_lt : ∀ (i : Fin n) {m : Fin n}, (0 : Fin n) < m → (i % m) < m
| ⟨a, aLt⟩, ⟨m, mLt⟩, hp =>  by
    have zero_lt : (0 : Nat) < m := Fin.zero_def ▸ hp
    have a_mod_lt : a % m < m := Nat.mod_lt _ zero_lt
    simp only [Fin.mod_def, LT.lt]
    rw [(Nat.mod_eq_of_lt (Nat.lt_trans a_mod_lt mLt) : a % m % n = a % m)]
    exact Nat.mod_lt _ zero_lt

/- Aux lemma that makes nsmul_succ' easier -/
protected lemma Fin.nsmuls_eq (x : Nat) : ∀ (a : Fin n),
  ((Fin.ofNat' x Fin.size_positive') * a) = Fin.ofNat' (x * a.val) Fin.size_positive'
| ⟨a, isLt⟩ => by
  apply Fin.eq_of_val_eq
  simp only [Fin.ofNat', Fin.mul_def]
  generalize hy : x * a % n = y
  rw [← Nat.mod_eq_of_lt isLt, ← Nat.mul_mod, hy]

@[simp] lemma Fin.one_def : (1 : Fin n).val = (1 % n : Nat) :=
  show (Fin.ofNat' 1 Fin.size_positive').val = 1 % n by simp [Fin.ofNat']

def Fin.addOverflows? (a b : Fin n) : Bool := n <= a.val + b.val

def Fin.mulOverflows? (a b : Fin n) : Bool := n <= a.val * b.val

def Fin.subUnderflows? (a b : Fin n) : Bool := a.val < b.val

def Fin.overflowingAdd (a b : Fin n) : (Bool × Fin n) := (n <= a.val + b.val, a + b)

def Fin.overflowingMul (a b : Fin n) : (Bool × Fin n) := (n <= a.val * b.val, a * b)

def Fin.underflowingSub (a b : Fin n) : (Bool × Fin n) := (a.val < b.val, a - b)

def Fin.checkedAdd (a b : Fin n) : Option (Fin n) :=
  match Fin.overflowingAdd a b with
  | (true, _) => none
  | (false, sum) => some (sum)

def Fin.checkedMul (a b : Fin n) : Option (Fin n) :=
  match Fin.overflowingMul a b with
  | (true, _) => none
  | (false, prod) => some (prod)

def Fin.checkedSub (a b : Fin n) : Option (Fin n) :=
  match Fin.underflowingSub a b with
  | (true, _) => none
  | (false, diff) => some (diff)

lemma Fin.checked_add_spec (a b : Fin n) :
  (Fin.checkedAdd a b).isSome = true ↔ a.val + b.val < n := by
  by_cases n <= a.val + b.val <;>
    simp_all [checkedAdd, Option.isSome, overflowingAdd, decide_eq_true, decide_eq_false]

lemma Fin.checked_mul_spec (a b : Fin n) :
  (Fin.checkedMul a b).isSome = true ↔ a.val * b.val < n := by
  simp only [checkedMul, overflowingMul, Option.isSome]
  refine Iff.intro ?mp ?mpr <;> intro h
  case mp =>
    by_cases hx : n <= a.val * b.val
    case pos => simp only [(decide_eq_true_iff (n <= a.val * b.val)).mpr hx] at h
    case neg => exact Nat.lt_of_not_le hx
  case mpr => simp only [decide_eq_false (Nat.not_le_of_lt h : ¬n <= a.val * b.val)]

lemma Fin.checked_sub_spec (a b : Fin n) :
  (Fin.checkedSub a b).isSome = true ↔ b.val <= a.val := by
  simp only [checkedSub, underflowingSub, Option.isSome]
  refine Iff.intro ?mp ?mpr <;> intro h
  case mp =>
    by_cases hx : a.val < b.val
    case pos => simp only [(decide_eq_true_iff (a.val < b.val)).mpr hx] at h
    case neg => exact Nat.le_of_not_lt hx
  case mpr => simp only [decide_eq_false (Nat.not_lt_of_le h : ¬a.val < b.val)]

instance : AddCommMonoid (Fin n) where
  __ := inferInstanceAs (AddCommSemigroup (Fin n))

  add_zero (a : Fin n) : a + 0 = a := by
    apply Fin.eq_of_val_eq
    simp only [Fin.add_def, Fin.zero_def, Nat.add_zero]
    exact Nat.mod_eq_of_lt a.isLt
  zero_add (a : Fin n) : 0 + a = a := by
    apply Fin.eq_of_val_eq
    simp only [Fin.add_def, Fin.zero_def, Nat.zero_add]
    exact Nat.mod_eq_of_lt a.isLt

  nsmul := fun x a => (Fin.ofNat' x a.size_positive) * a
  nsmul_zero' := fun _ => by
    apply Fin.eq_of_val_eq
    simp [Fin.mul_def, Fin.ofNat', Fin.zero_def, Nat.zero_mul, Nat.zero_mod]
  nsmul_succ' := fun x a => by
    simp only [Fin.nsmuls_eq]
    simp [Fin.ofNat', Fin.add_def]
    exact congrArg (fun x => x % n) (Nat.add_comm (x * a.val) (a.val) ▸ Nat.succ_mul x a.val)

instance : AddMonoidWithOne (Fin n) where
  __ := inferInstanceAs (AddCommMonoid (Fin n))
  natCast n := Fin.ofNat' n Fin.size_positive'
  natCast_zero := rfl
  natCast_succ _ := Fin.ofNat'_succ

private theorem Fin.mul_one (a : Fin n) : a * 1 = a := by
  apply Fin.eq_of_val_eq
  simp only [Fin.mul_def, Fin.one_def]
  cases n with
  | zero => exact (False.elim a.elim0)
  | succ n =>
    match Nat.lt_or_eq_of_le (Nat.mod_le 1 n.succ) with
    | Or.inl h_lt =>
      have h_eq : 1 % n.succ = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h_lt)
      have hnz : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ (Nat.le_of_mod_lt h_lt))
      have haz : a.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ (hnz ▸ a.isLt))
      rw [h_eq, haz]
      simp only [Nat.zero_mul, Nat.zero_mod]
    | Or.inr h_eq => simp only [h_eq, Nat.mul_one, Nat.mod_eq_of_lt (a.isLt)]

instance : MonoidWithZero (Fin n) where
  __ := inferInstanceAs (CommSemigroup (Fin n))
  mul_one := Fin.mul_one
  one_mul _ := by rw [mul_comm, Fin.mul_one]
  npow_zero' _ := rfl
  npow_succ' _ _ := rfl
  zero_mul x := by
    apply Fin.eq_of_val_eq
    simp only [Fin.mul_def, Fin.zero_def, Nat.zero_mul, Nat.zero_mod]
  mul_zero x := by
    apply Fin.eq_of_val_eq
    simp only [Fin.mul_def, Fin.zero_def, Nat.mul_zero, Nat.zero_mod]

private theorem Fin.mul_add (a b c : Fin n) : a * (b + c) = a * b + a * c := by
    apply Fin.eq_of_val_eq
    simp [Fin.mul_def, Fin.add_def]
    generalize lhs : a.val * ((b.val + c.val) % n) % n = l
    rw [(Nat.mod_eq_of_lt a.isLt).symm, ← Nat.mul_mod] at lhs
    rw [← lhs, left_distrib]

instance : CommSemiring (Fin n) where
  __ := inferInstanceAs (MonoidWithZero (Fin n))
  __ := inferInstanceAs (CommSemigroup (Fin n))
  __ := inferInstanceAs (AddCommMonoid (Fin n))
  __ := inferInstanceAs (AddMonoidWithOne (Fin n))
  left_distrib := Fin.mul_add
  right_distrib a b c := (by rw [mul_comm, Fin.mul_add, mul_comm c, mul_comm c])

instance : Neg (Fin n) where
  neg a := ⟨(n - a) % n, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) a.isLt)⟩

lemma Fin.neg_def : (-a : Fin n) = ⟨(n - a) % n, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) a.isLt)⟩ := rfl

protected def Fin.ofInt'' : Int → Fin n
  | Int.ofNat a => Fin.ofNat' a Fin.size_positive'
  | Int.negSucc a => -(Fin.ofNat' a.succ Fin.size_positive')

private theorem Fin.sub_eq_add_neg : ∀ (a b : Fin n), a - b = a + -b := by
  simp [Fin.add_def, Fin.sub_def, Neg.neg]

private theorem Fin.add_left_neg (a : Fin n) : -a + a = 0 := by
    rw [add_comm, ← Fin.sub_eq_add_neg]
    apply Fin.eq_of_val_eq
    simp [Fin.sub_def, (Nat.add_sub_cancel' (Nat.le_of_lt a.isLt)), Nat.mod_self]

def Fin.ofInt' : ℤ → Fin n
  | (i : ℕ) => i
  | (Int.negSucc i) => -↑(i + 1 : ℕ)

instance : AddGroupWithOne (Fin n) where
  __ := inferInstanceAs (AddMonoidWithOne (Fin n))
  gsmul_zero' := by simp [gsmul_rec, nsmul_rec]
  gsmul_succ' := by simp [gsmul_rec, nsmul_rec, -Int.ofNat_eq_cast]
  gsmul_neg' := by simp [gsmul_rec, nsmul_rec, -Int.ofNat_eq_cast]
  sub_eq_add_neg := Fin.sub_eq_add_neg
  add_left_neg := Fin.add_left_neg
  intCast := Fin.ofInt'
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl

instance : CommRing (Fin n) where
  __ := inferInstanceAs (AddGroupWithOne (Fin n))
  __ := inferInstanceAs (CommSemiring (Fin n))

lemma Fin.gt_wf : WellFounded (fun a b : Fin n => b < a) :=
  Subrelation.wf (@fun a i h => ⟨h, i.2⟩) (invImage (fun i => i.1) (Nat.upRel n)).wf

/-- A well-ordered relation for "upwards" induction on `Fin n`. -/
def Fin.upRel (n : ℕ) : WellFoundedRelation (Fin n) := ⟨_, gt_wf⟩

lemma Fin.le_refl (f : Fin n) : f ≤ f := Nat.le_refl _
lemma Fin.le_trans (a b c : Fin n) : a ≤ b → b ≤ c → a ≤ c := Nat.le_trans
lemma Fin.lt_iff_le_not_le (a b : Fin n) : a < b ↔ a ≤ b ∧ ¬b ≤ a := Nat.lt_iff_le_not_le
lemma Fin.le_antisymm (a b : Fin n) : a ≤ b → b ≤ a → a = b := by
  intro h1 h2
  apply Fin.eq_of_val_eq
  exact Nat.le_antisymm h1 h2

lemma Fin.le_total (a b : Fin n) : a ≤ b ∨ b ≤ a := Nat.le_total _ _

instance : LinearOrder (Fin n) where
  le_refl := Fin.le_refl
  le_trans := Fin.le_trans
  lt_iff_le_not_le := Fin.lt_iff_le_not_le
  le_antisymm := Fin.le_antisymm
  le_total := Fin.le_total
  decidable_le := inferInstance

end
