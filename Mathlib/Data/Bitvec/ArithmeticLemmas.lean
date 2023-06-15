import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas
import Mathlib.Data.Bitvec.Tactic
import Mathlib.Data.Bitvec.ConstantLemmas


namespace Vector
  variable (xs : Vector α n)

  protected def mapAccumr_mapAccumr_fold.g (f₁ : β₂ → σ₁ → σ₁ × β₁) (f₂ : α → σ₂ → σ₂ × β₂) :=
    fun (x : α) ((s₁, s₂) : σ₁ × σ₂) =>
      let r₂ := f₂ x s₂
      let r₁ := f₁ r₂.snd s₁
      ((r₁.fst, r₂.fst), r₁.snd)

  /-- We can fold nested `mapAccumr`s into a single `mapAccumr` -/
  @[simp]
  theorem mapAccumr_mapAccumr_fold (f₁ : β₂ → σ₁ → σ₁ × β₁) (f₂ : α → σ₂ → σ₂ × β₂)
                              : (mapAccumr f₁ (mapAccumr f₂ xs s₂).snd s₁) = (
                                  (mapAccumr (mapAccumr_mapAccumr_fold.g f₁ f₂) xs (s₁, s₂)).fst.fst,
                                  (mapAccumr (mapAccumr_mapAccumr_fold.g f₁ f₂) xs (s₁, s₂)).snd
                                ) := by
    induction xs using Vector.revInductionOn generalizing s₁ s₂
    case nil =>
      simp
    case snoc xs x ih =>
      simp[ih]
      constructor <;> rfl

  /-
    TODO:
    * write all variations of `mapAccumr_mapAccumr` with `₂`/`₃`
    * write `foldl` in terms of `mapAccumr`?
  -/

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

section Unfold
  open Bitvec (carry)

  variable (x y c b : Bool) (xs ys : Bitvec n)

  @[simp]
  theorem sbb_cons : sbb (x ::ᵥ xs) (y ::ᵥ ys) b = (carry (!x) y (sbb xs ys b).fst,
    Bitvec.xor3 x y ((sbb xs ys b)).fst ::ᵥ ((sbb xs ys b)).snd) :=
      rfl

  @[simp]
  theorem sbb_snoc : sbb (xs.snoc x) (ys.snoc y) b
                      = ((sbb xs ys (carry (!x) y b)).fst,
                          Vector.snoc (sbb xs ys (carry (!x) y b)).snd (Bitvec.xor3 x y b)) := by
      simp[sbb]
end Unfold

variable (x y : Bitvec n)

theorem zero_sub_x_eq_neg_x : sub 0 x = neg x := by
  clear *-x
  simp[sub, neg]
  suffices ∀ xs x, sbb 0 xs x = Vector.mapAccumr (fun y c ↦ (y || c, _root_.xor y c)) xs x
    by rw[this x false]
  clear x
  intro xs
  induction xs using Vector.revInductionOn
  case nil =>
    intro; rfl
  case snoc n xs x ih =>
    simp[zero_unfold_snoc, Bitvec.carry, ih]

theorem neg_neg_x : neg (neg x) = x := by
  clear y;
  simp[neg]




-- theorem add_impl_with_bitwise : x.add y =

-- @[simp]
-- theorem sub_eq_xor : x.sub y = x.xor y := by
--   ext i
--   simp
--   simp[sub, sbb, Bitvec.xor]
--   induction x, y using Vector.inductionOn₂
--   case x.nil =>
--     exact Fin.elim0 i
--   case x.cons x y xs ys ih =>
--     simp[Bitvec.xor3]
--     cases i using Fin.cases
--     . simp
--       rw[←Bool.xor_assoc]
--       suffices
--           (Vector.mapAccumr₂ (fun x y c ↦ (Bitvec.carry (!x) y c, _root_.xor x (_root_.xor y c))) xs ys false).fst = false
--       from by simp[this]






#eval false ::ᵥ (1 : Bitvec 3)

end Bitvec
