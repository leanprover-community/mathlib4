import Mathlib.Data.Bitvec.ConstantLemmas
import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas
import Mathlib.Data.Bitvec.Tactic
import Mathlib.Data.Vector.MapLemmas
import Mathlib.Data.Vector.Snoc

namespace Vector
  variable (xs : Vector α n)


  @[simp]
  theorem mapAccumr₂_replicate_left :
      mapAccumr₂ f (Vector.replicate n b) = mapAccumr (f b) := by
    clear *-f
    funext xs s
    induction xs using Vector.revInductionOn generalizing s
    case nil => rfl
    case snoc xs x ih =>
      rw[replicate_succ_to_snoc]
      simp[ih]

  @[simp]
  theorem mapAccumr₂_replicate_right :
      mapAccumr₂ f xs (Vector.replicate n b) = mapAccumr (fun x => f x b) xs := by
    funext s
    induction xs using Vector.revInductionOn generalizing s
    case nil => rfl
    case snoc xs x ih =>
      rw[replicate_succ_to_snoc]
      simp[ih]
end Vector


namespace Bool
  @[simp]
  theorem xor3_false_left : Bool.xor3 false x y = xor x y := by
    simp only [Bool.xor3, xor_false_left]

  @[simp]
  theorem xor3_false_middle : Bool.xor3 x false y = xor x y := by
    simp only [Bool.xor3, xor_false_right]

  @[simp]
  theorem xor3_false_right : Bool.xor3 x y false = xor x y := by
    simp only [Bool.xor3, xor_false_right]
end Bool


namespace Bitvec
open Bitvec (sub add xor neg)


variable (x : Bitvec n)

@[simp]
theorem add_zero_left : 0 + x = x := by
  aesop_bitvec

@[simp]
theorem add_zero_right : add x 0 = x := by
  aesop_bitvec

@[simp]
theorem add_comm : add x y = add y x := by
  aesop_bitvec

-- @[simp]
-- theorem add_neg_y : add x (neg y) = sub x y := by
--   aesop_bitvec (options := {terminal := false})


-- @[simp]
-- theorem zero_sub_x_eq_neg_x : sub 0 x = neg x := by
--   aesop_bitvec

@[simp]
theorem neg_neg_x : neg (neg x) = x := by
  aesop_bitvec


theorem add_eq_or_of_and_eq_zero {n : ℕ} {x y : Bitvec n} (hxy : x &&& y = 0) :
    x + y = x ||| y := by
  simp[(· + ·), Add.add, (· ||| ·), OrOp.or, Bitvec.or]
  simp[add, adc]
  induction x, y using Vector.revInductionOn₂
  next => rfl
  next xs ys x y ih =>
    simp [(· &&& ·), AndOp.and, Bitvec.and] at hxy
    rw [Bitvec.zero_unfold_snoc] at hxy
    rcases (Vector.snoc.inj hxy) with ⟨head, tail⟩
    specialize ih tail
    have head : (x = false) ∨ (y = false) := by
      revert head; simp
    cases head <;> simp_all [Bool.carry]

end Bitvec
