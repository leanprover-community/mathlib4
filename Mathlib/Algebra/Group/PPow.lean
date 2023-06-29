import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Data.PNat.Basic

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- See issue #2220

variable {M : Type _}

instance Semigroup.instPow [Semigroup M] : Pow M ℕ+ where
  pow x n := Semigroup.ppow n n.pos x

instance AddSemigroup.instSMul [AddSemigroup M] : SMul ℕ+ M where
  smul n x := AddSemigroup.psmul n n.pos x

attribute [to_additive existing AddSemigroup.instSMul] Semigroup.instPow

section Semigroup

variable [Semigroup M]

@[to_additive (attr := simp) one_psmul]
lemma ppow_one (x : M) : x ^ (1 : ℕ+) = x := Semigroup.ppow_one x

@[to_additive succ_psmul']
lemma ppow_succ' (x : M) (n : ℕ+) : x ^ (n + 1) = x * x ^ n :=
  n.recOn (Semigroup.ppow_succ x 0) fun k _ => Semigroup.ppow_succ x k

@[to_additive succ_psmul]
lemma ppow_succ (x : M) (n : ℕ+) : x ^ (n + 1) = x ^ n * x :=
  n.recOn (by simp [ppow_succ']) fun k hk => by rw [ppow_succ' x k, ppow_succ', hk, mul_assoc]

@[to_additive add_psmul]
lemma ppow_add (x : M) (n m : ℕ+) : x ^ (n + m) = x ^ n * x ^ m :=
  m.recOn (by simp [ppow_succ, add_comm]) fun k hk => by
    rw [←add_assoc, ppow_succ, ppow_succ, hk, mul_assoc]

@[to_additive mul_comm_psmul]
lemma ppow_mul_comm (x : M) (n m : ℕ+) : x ^ n * x ^ m = x ^ m * x ^ n := by
  simp only [←ppow_add, add_comm]

@[to_additive mul_comm_psmul']
lemma ppow_mul_comm' (x : M) (n : ℕ+) : x ^ n * x = x * x ^ n := by
  simpa only [ppow_one] using ppow_mul_comm x n 1

@[to_additive mul_psmul]
lemma ppow_mul (x : M) (n m : ℕ+) : x ^ (n * m) = (x ^ n) ^ m :=
  m.recOn (by simp) fun k hk => by simp [mul_add, ppow_add, hk]

@[to_additive]
lemma Commute.ppow_left {x y : M} (h : Commute x y) (n : ℕ+) : Commute (x ^ n) y :=
  n.recOn ((ppow_one x).symm ▸ h) fun k hk => ppow_succ x k ▸ hk.mul_left h

@[to_additive]
lemma Commute.ppow_right {x y : M} (h : Commute x y) (n : ℕ+) : Commute x (y ^ n) :=
  (h.symm.ppow_left n).symm

@[to_additive Commute.psmul_add]
lemma Commute.mul_ppow {x y : M} (h : Commute x y) (n : ℕ+) : (x * y) ^ n = x ^ n * y ^ n :=
  n.recOn (by simp) fun k hk => by
    simp only [ppow_succ, hk, mul_assoc]
    rw [←mul_assoc x, ←mul_assoc (y ^ k)]
    congr 2
    exact (h.symm.ppow_left k).eq

end Semigroup

section CommSemigroup

variable [CommSemigroup M]

@[to_additive psmul_add]
lemma mul_ppow (x y : M) (n : ℕ+) : (x * y) ^ n = x ^ n * y ^ n :=
  (Commute.all x y).mul_ppow n

variable (M)

@[to_additive (attr := simps)]
def ppowMulHom (n : ℕ+) : M →ₙ* M where
  toFun x := x ^ n
  map_mul' := mul_ppow (n := n)

end CommSemigroup

-- not marked as `simp` because in a monoid we probably prefer powers with type `ℕ`
@[to_additive (attr := norm_cast)]
lemma npow_val_eq_ppow [Monoid M] (x : M) (n : ℕ+) : x ^ (n : ℕ) = x ^ n :=
  n.recOn (by simp [pow_one]) fun k hk => by simp [pow_succ, ppow_succ', hk]

@[to_additive]
lemma map_ppow {F M N : Type _} [Semigroup M] [Semigroup N] [MulHomClass F M N]
    (f : F) (x : M) (n : ℕ+) : f (x ^ n) = f x ^ n :=
  n.recOn (by simp) fun k hk => by simp [ppow_succ, hk]
