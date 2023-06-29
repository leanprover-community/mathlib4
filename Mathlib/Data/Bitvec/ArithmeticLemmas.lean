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
  theorem xor3_false_left : Bitvec.xor3 false x y = xor x y := by
    simp only [Bitvec.xor3, xor_false_left]

  @[simp]
  theorem xor3_false_middle : Bitvec.xor3 x false y = xor x y := by
    simp only [Bitvec.xor3, xor_false_right]

  @[simp]
  theorem xor3_false_right : Bitvec.xor3 x y false = xor x y := by
    simp only [Bitvec.xor3, xor_false_right]
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



theorem add_eq_or_of_and_eq_zero_aux₁ : ∀ {x y : List Bool} (_ : x.length = y.length),
    x.zipWith (. && .) y = List.replicate x.length false →
    (x.mapAccumr₂ (fun a b c => (Bitvec.carry a b c, Bitvec.xor3 a b c)) y false).fst = false
  | [], [], _ => fun _ => rfl
  | a::x, b::y, h => fun h' => by
    simp only [List.zipWith, Bool.forall_bool, List.replicate, Nat.add_eq, add_zero,
      List.cons.injEq, Bool.and_eq_false_eq_eq_false_or_eq_false] at h'
    have := add_eq_or_of_and_eq_zero_aux₁ (Nat.succ.inj h) h'.2
    unfold Bitvec.carry at this
    rcases h'.1 with rfl | rfl <;>
    simp [List.mapAccumr₂, Bitvec.carry, this]

theorem add_eq_or_of_and_eq_zero_aux₂ : ∀ {x y : List Bool} (_ : x.length = y.length),
    x.zipWith (. && .) y = List.replicate x.length false →
    (x.mapAccumr₂ (fun a b c => (Bitvec.carry a b c, Bitvec.xor3 a b c)) y false).snd =
    x.zipWith (. || .) y
  | [], [], _ => fun _ => rfl
  | a::x, b::y, h => fun h' => by
    dsimp [List.mapAccumr₂]
    simp only [List.zipWith, Bool.forall_bool, List.replicate, Nat.add_eq, add_zero,
      List.cons.injEq, Bool.and_eq_false_eq_eq_false_or_eq_false] at h'
    rw [add_eq_or_of_and_eq_zero_aux₁ (Nat.succ.inj h) h'.2,
      add_eq_or_of_and_eq_zero_aux₂ (Nat.succ.inj h) h'.2]
    rcases h'.1 with rfl | rfl <;>
    simp [List.mapAccumr₂, Bitvec.carry, Bitvec.xor3]

theorem add_eq_or_of_and_eq_zero {n : ℕ} {x y : Bitvec n} (hxy : x.and y = 0) : x + y = x.or y :=
  Subtype.ext (add_eq_or_of_and_eq_zero_aux₂ (x.2.trans y.2.symm)
    (by convert congr_arg Vector.toList hxy;
        simp[OfNat.ofNat, Zero.zero, Bitvec.zero, Vector.toList, Vector.replicate]))

end Bitvec
