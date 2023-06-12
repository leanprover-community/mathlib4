import Mathlib.Data.Bitvec.Lemmas
import Mathlib.Data.ZMod.Basic

namespace Bitvec

instance (n : ℕ) : NeZero (2 ^ n) := ⟨Nat.pos_iff_ne_zero.1 <| pow_pos (by norm_num) _⟩

@[simp]
theorem two_pow_eq_zero_zmod (n : ℕ) : (2 ^ n : ZMod (2 ^ n)) = 0 := by
    rw [← Nat.cast_two (R := ZMod (2 ^ n)), ← Nat.cast_pow, ZMod.nat_cast_self]

def toZMod {n : Nat} (x : Bitvec n) : ZMod (2 ^ n) :=
  x.toNat

theorem toZMod_val {n : ℕ} (v : Bitvec n) : (toZMod v).val = v.toNat := by
  rw [toZMod, ZMod.val_nat_cast, Nat.mod_eq_of_lt]
  apply toNat_lt

def ofZMod {n : ℕ} (x : ZMod (2 ^ n)) : Bitvec n :=
  Bitvec.ofNat _ x.val

theorem toZMod_ofZMod {n} (i : ZMod <| 2 ^ n) : (ofZMod i).toZMod = i :=
  ZMod.val_injective _ (by simp [toZMod_val, ofZMod, Bitvec.toNat_ofNat,
    Nat.mod_eq_of_lt (ZMod.val_lt i)])

theorem ofZMod_toZMod {n} (v : Bitvec n) : ofZMod (toZMod v) = v := by
  dsimp [ofZMod]
  rw [toZMod_val, ofNat_toNat]

@[simp]
theorem toZMod_natCast {n : ℕ} (x : ℕ) : (↑x : Bitvec n).toZMod = x := by
  show (Bitvec.ofNat n x).toZMod = x
  simp [toZMod, toNat_ofNat]
#print Bitvec.neg
@[simp]
theorem toZMod_intCast {n : ℕ} (x : ℤ) : (↑x : Bitvec n).toZMod = x := by
  show (Bitvec.ofInt n x).toZMod = x
  cases x
  . simp [Bitvec.ofInt, toZMod, toNat_ofNat]
  . simp [Bitvec.ofInt]


@[simp]
theorem toZMod_add {n : ℕ} (x y : Bitvec n) : (x + y).toZMod = (x.toZMod + y.toZMod) := by
  apply ZMod.val_injective
  rw [toZMod_val, ZMod.val_add, toNat_add, toZMod_val, toZMod_val]

@[simp]
theorem ofZMod_add {n : ℕ} (x y : ZMod (2 ^n)) :
    Bitvec.ofZMod (x + y) = Bitvec.ofZMod x + Bitvec.ofZMod y := by
  rw [← toZMod_ofZMod x, ← toZMod_ofZMod y, ← toZMod_add, toZMod_ofZMod, toZMod_ofZMod,
    ofZMod_toZMod]

@[simp]
theorem toZMod_zero : ∀ {n : Nat}, (0 : Bitvec n).toZMod = 0 :=
  by simp [toZMod]

@[simp]
theorem ofZMod_zero : Bitvec.ofZMod (0 : ZMod (2^n)) = 0 := by
  rw [← toZMod_zero, ofZMod_toZMod]

@[simp]
theorem toZMod_one : ∀ {n : Nat}, (1 : Bitvec n).toZMod = 1 := by
  simp [toZMod, toNat_one]

@[simp]
theorem ofZMod_one : Bitvec.ofZMod (1 : ZMod (2^n)) = 1 := by
  rw [← toZMod_one, ofZMod_toZMod]

private theorem toInt_sub_aux : ∀ {x y : List Bool} (_hx : List.length x = List.length y),
    (↑(((x.mapAccumr₂
      (fun a b c => (Bitvec.carry (!a) b c, Bitvec.xor3 a b c)) y false).snd).foldl addLsb 0) : ℤ)
    - 2 ^ x.length * cond (x.mapAccumr₂
      (fun a b c => (Bitvec.carry (!a) b c, Bitvec.xor3 a b c)) y false).fst 1 0 =
    x.foldl addLsb 0 + -y.foldl addLsb 0
| [], [], _ => rfl
|  a::x, b::y, h => by
  simp only [List.length_cons, Nat.succ.injEq] at h
  rw [foldl_addLsb_cons_zero, foldl_addLsb_cons_zero, Nat.cast_add,
    Nat.cast_add, neg_add, add_add_add_comm, ← toInt_sub_aux h, List.mapAccumr₂,
    foldl_addLsb_eq_add_foldl_addLsb_zero, foldl_addLsb_cons_zero]
  simp only [List.length_cons, List.length_mapAccumr₂, h, min_self, pow_succ, mul_zero, addLsb,
    zero_add, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  cases a <;>
  cases b <;>
  cases (x.mapAccumr₂ (fun a b c => (Bitvec.carry (!a) b c, Bitvec.xor3 a b c)) y false).fst <;>
  simp [Bitvec.carry, Bitvec.xor3] <;>
  ring

theorem toZMod_sbb {n : ℕ} (x y : Bitvec n) : (x.sbb y false).2.toZMod = x.toZMod - y.toZMod := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  simp [Bitvec.toNat, toZMod, bitsToNat, Vector.toList, sbb, Vector.mapAccumr₂]
  have := congr_arg ((↑) : ℤ → ZMod (2^n)) (toInt_sub_aux (hx.trans hy.symm))
  simpa [hx, sub_eq_add_neg] using this

theorem toZMod_sub {n : ℕ} (x y : Bitvec n) : (x - y).toZMod = x.toZMod - y.toZMod :=
  toZMod_sbb x y

instance : SMul ℕ (Bitvec n) := ⟨nsmulRec⟩

private theorem toInt_neg_aux : ∀ (x : List Bool),
    (((x.mapAccumr (fun a c => (a || c, xor a c)) false).snd.foldl addLsb (0 : ℕ) : ℕ)
      - 2 ^ x.length * cond (x.mapAccumr (fun a c => (a || c, xor a c)) false).fst 1 0 : ℤ) =
      -(x.foldl addLsb 0)
  | [] => rfl
  | a::x => by
    rw [List.mapAccumr, foldl_addLsb_cons_zero, foldl_addLsb_cons_zero, Nat.cast_add,
      Nat.cast_add, neg_add, ← toInt_neg_aux x]
    cases a <;> cases (x.mapAccumr (fun b c => (b || c, xor b c)) false).fst <;>
    simp [pow_succ, two_mul, sub_eq_add_neg] <;> ring

theorem toZMod_neg {n : ℕ} (x : Bitvec n) : (-x).toZMod = -x.toZMod := by
  show x.neg.toZMod = -x.toZMod
  rcases x with ⟨x, hx⟩
  simp only [Bitvec.neg, Bitvec.toNat, bitsToNat, Vector.toList, Vector.mapAccumr, toZMod]
  have := congr_arg ((↑) : ℤ → ZMod (2^n)) (toInt_neg_aux x)
  subst n
  simpa [sub_eq_add_neg] using this

theorem nsmul_def {n : ℕ} (x : Bitvec n) (y : ℕ) : y • x = nsmulRec y x := rfl

@[simp]
theorem toZMod_nsmul {n : ℕ} (x : Bitvec n) : ∀ (y : ℕ), (y • x).toZMod = y • x.toZMod
  | 0 => by simp [zero_nsmul, nsmul_def, nsmulRec]
  | y+1 => by
    rw [nsmul_def, nsmulRec, toZMod_add, ← nsmul_def, toZMod_nsmul _ y]
    simp [add_mul, add_comm]

instance : SMul ℤ (Bitvec n) := ⟨zsmulRec⟩

theorem zsmul_def {n : ℕ} (x : Bitvec n) (y : ℤ) : y • x = zsmulRec y x := rfl

@[simp]
theorem toZMod_zsmul {n : ℕ} (x : Bitvec n) (y : ℤ) : (y • x).toZMod = y • x.toZMod := by
  induction y with
  | ofNat y => simp [zsmul_def, zsmulRec, ← nsmul_def]
  | negSucc y => simp [zsmul_def, zsmulRec, ← nsmul_def, toZMod_neg, add_mul]

instance : AddCommGroup (Bitvec n) :=
  Function.Injective.addCommGroup toZMod
    (Function.injective_iff_hasLeftInverse.2 ⟨_, ofZMod_toZMod⟩)
    toZMod_zero toZMod_add toZMod_neg toZMod_sub toZMod_nsmul toZMod_zsmul

theorem toZMod_mul_aux {n : ℕ} :
    ∀ (x : List Bool) (s y : Bitvec n),
    (List.foldl (fun r b ↦ bif b then r + r + y else r + r) s x).toZMod  =
      (2 ^ x.length * s.toZMod + x.foldl addLsb 0 * y.toZMod)
| [], s, y => by simp
| a::x, s, y => by
  rw [List.foldl_cons, toZMod_mul_aux x, foldl_addLsb_cons_zero, List.length_cons, pow_succ]
  cases a <;> simp <;> ring

theorem toZMod_mul {n : ℕ} (x y : Bitvec n) : (x * y).toZMod = (x.toZMod * y.toZMod) := by
  refine (toZMod_mul_aux x.toList 0 y).trans ?_
  simp [toZMod, Bitvec.toNat, bitsToNat]

instance : Pow (Bitvec n) ℕ := ⟨fun x n => npowRec n x⟩

theorem npow_def {n : ℕ} (x : Bitvec n) (y : ℕ) : x ^ y = npowRec y x := rfl

@[simp]
theorem toZMod_npow : ∀ (x : Bitvec n) (y : ℕ), (x ^ y).toZMod = x.toZMod ^ y
  | _, 0 => by simp [npow_def, npowRec]
  | x, y+1 => by
    rw [npow_def, npowRec, toZMod_mul, ← npow_def, toZMod_npow x y]
    simp [pow_succ, mul_comm]

instance : CommRing (Bitvec n) :=
  Function.Injective.commRing toZMod
    (Function.injective_iff_hasLeftInverse.2 ⟨_, ofZMod_toZMod⟩)
    toZMod_zero toZMod_one toZMod_add toZMod_mul toZMod_neg toZMod_sub
      toZMod_nsmul toZMod_zsmul toZMod_npow toZMod_natCast toZMod_intCast

end Bitvec
