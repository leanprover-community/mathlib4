import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas
import Mathlib.Data.Bitvec.Tactic
import Mathlib.Data.Bitvec.ConstantLemmas
import Mathlib.Data.Vector.MapNorm

namespace Vector
  variable (xs : Vector α n)

  /-!
  ## Fold nested instances of mapAccumrₓ
  -/
  section Fold
    /-- If nested `mapAccumr` with the same function `f` were folded into one, and `f`
        satisfies a specific property with how it handles its state, then we can simplify
        the expression to only use a single element of the state `σ`, instead of a pair of states
     -/
    @[simp]
    theorem mapAccumr_fold_g_same (f : α → σ → σ × α) (h : ∀ x s, (f (f x s).snd s).fst = (f x s).fst)
                                : mapAccumr (mapAccumr_mapAccumr.g f f) xs (s, s) = (
                                    let m := mapAccumr (fun x s => f (f x s).snd s) xs s
                                    ((m.fst, m.fst), m.snd)
                                  ) := by
      simp only
      induction xs using Vector.revInductionOn generalizing s
      case nil => rfl
      case snoc xs x ih => simp[h, ih]



    -- theorem mapAccumr₂_mapAccumr₂_left_left (f₁ : γ → α → σ₁ → σ₁ × γ) (f₂ : α → β → σ₂ → σ₂ × γ) :
    --     (mapAccumr₂ f₁ (mapAccumr₂ f₂ xs ys c₂).snd xs c₁)
    --     =
    --       let m := mapAccumr₂ (fun x y (c₁, c₂) =>
    --                   let r₂ := f₂ x y s₂
    --                   let r₁ := f₁ r₂.snd x s₁
    --                   ((r₁.fst, r₂.fst), r₁.snd)
    --                 )
    --               xs ys (c₁, c₂);
    --       (m.fst.fst, m.snd) := by
    --   induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂
    --   case nil =>
    --     rfl
    --   case snoc xs ys x y ih =>
    --     simp_all
    --     constructor
    --     . simp[ih];
    --     . simp

  end Fold




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
  ### Congruences
  -/
  section Congr


  @[simp, aesop 90%]
  theorem mapAccumr_congr_fun_snd (h : f = g) :
      (Vector.mapAccumr f xs c).snd = (Vector.mapAccumr g xs c).snd := by
    congr

  @[simp, aesop 90%]
  theorem mapAccumr₂_congr_fun_snd (h : f = g) :
      (Vector.mapAccumr₂ f xs ys c).snd = (Vector.mapAccumr₂ g xs ys c).snd := by
    congr

  @[simp, aesop 90%]
  theorem mapAccumr₂_congr_fun_symm_snd (h : ∀ x y, f x y = g y x) :
      (Vector.mapAccumr₂ f xs ys c).snd = (Vector.mapAccumr₂ g ys xs c).snd := by
    induction xs, ys using Vector.revInductionOn₂ generalizing c <;> simp[*]

  @[simp, aesop 90%]
  theorem mapAccumr_map_congr_fun (f : α → σ → σ × α) (h : ∀ xs c, (f xs c).snd = g xs) :
      (mapAccumr f xs c).snd = map g xs := by
    induction xs using revInductionOn generalizing c <;> simp[*]

  @[simp, aesop 90%]
  theorem mapAccumr_map_congr_fun' (f : α → σ → σ × α) (c : σ) (h : ∀ xs, (f xs c) = (c, g xs)) :
      (mapAccumr f xs c).snd = map g xs := by
    induction xs using revInductionOn generalizing c <;> simp[*]

  end Congr

  /-!
  ### When is a mapAccumr a no-op
  -/
  section Noop

  /-- Wrap a bitvec into a trivial `mapAccumr` -/
  protected theorem mapAccumr_wrap (f : α → σ → σ × α) (c : σ) :
      xs = (mapAccumr (fun x c => ((f x c).fst, x)) xs c).snd := by
    induction xs using Vector.revInductionOn generalizing c
    case nil =>
      rfl
    case snoc xs x ih =>
      simp[←ih]

  /--
    If `f` simply returns the input bit, for every possible state, then `mapAccumr f _` is a no-op
  -/
  @[simp, aesop safe]
  theorem mapAccumr_nop (f : α → σ → σ × α) (h : ∀ x c, (f x c).snd = x) :
      (Vector.mapAccumr f x c).snd = x := by
    conv => {
      rhs; rw[Vector.mapAccumr_wrap x f c]
    }
    congr
    funext x c
    specialize h x c
    revert h
    cases (f x c)
    simp

  /--
    If `f` returns the input bit, and a constant state `c`, when given `c` as the initial state,
    then `mapAccumr f c` is a no-op
  -/
  @[simp, aesop safe]
  theorem mapAccumr_nop' (f : α → σ → σ × α) (h : ∀ x, f x c = (c, x)) :
      (Vector.mapAccumr f x c).snd = x := by
    conv => {
      rhs; rw[Vector.mapAccumr_wrap x f c]
    }
    induction x using Vector.revInductionOn
    case nil => rfl
    case snoc xs x ih =>
      simp[h, ih]

  end Noop


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


variable (x : Bitvec n)


@[simp]
theorem add_zero_left : add 0 x = x := by
  aesop_bitvec

@[simp]
theorem add_zero_right : add x 0 = x := by
  aesop_bitvec

@[simp]
theorem add_comm : add x y = add y x := by
  aesop_bitvec

-- theorem add_neg_y : add x (neg y) = sub x y := by
--   aesop_bitvec


@[simp]
theorem zero_sub_x_eq_neg_x : sub 0 x = neg x := by
  aesop_bitvec

@[simp]
theorem neg_neg_x : neg (neg x) = x := by
  aesop_bitvec


end Bitvec
