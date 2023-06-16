import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas
import Mathlib.Data.Bitvec.Tactic
import Mathlib.Data.Bitvec.ConstantLemmas


namespace Vector
  variable (xs : Vector α n)

  protected abbrev mapAccumr_mapAccumr_fold.g (f₁ : β₂ → σ₁ → σ₁ × β₁) (f₂ : α → σ₂ → σ₂ × β₂) :=
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
      rfl
    case snoc xs x ih =>
      simp[ih]

  /-- If nested `mapAccumr` with the same function `f` were folded into one, and `f`
      satisfies a specific property with how it handles its state, then we can simplify
      the expression to only use a single element of the state `σ`, instead of a pair of states
   -/
  @[simp]
  theorem mapAccumr_fold_g_same (f : α → σ → σ × α) (h : ∀ x s, (f (f x s).snd s).fst = (f x s).fst)
                              : mapAccumr (mapAccumr_mapAccumr_fold.g f f) xs (s, s) = (
                                  let m := mapAccumr (fun x s => f (f x s).2 s) xs s
                                  ((m.1, m.1), m.2)
                                ) := by
    simp only
    induction xs using Vector.revInductionOn generalizing s
    case nil => rfl
    case snoc xs x ih => simp[h, ih]


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

variable (x : Bitvec n)

theorem add_zero_left : add 0 x = x := by
  simp[add, adc, Bitvec.carry, Bitvec.xor3]
  induction x using Vector.revInductionOn
  case nil =>
    rfl
  case snoc n xs x ih =>
    simp[ih]

theorem add_zero_right : add x 0 = x := by
  simp[add, adc, Bitvec.carry, Bitvec.xor3]
  induction x using Vector.revInductionOn
  case nil =>
    rfl
  case snoc n xs x ih =>
    simp[ih]


@[simp]
theorem zero_sub_x_eq_neg_x : sub 0 x = neg x := by
  simp[sub, neg, sbb]
  congr
  funext y c
  cases y <;> cases c <;> rfl

@[simp]
theorem neg_neg_x : neg (neg x) = x := by
  simp[neg]
  suffices ∀ b, (Vector.mapAccumr (fun x s ↦ (_root_.xor x s || s, x)) x b).snd = x
  from this false
  induction x using Vector.revInductionOn
  case nil =>
    intro; rfl
  case snoc xs x ih =>
    simp[ih]


end Bitvec
