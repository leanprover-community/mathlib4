import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas
import Mathlib.Data.Bitvec.Tactic
import Mathlib.Data.Bitvec.ConstantLemmas
import Mathlib.Data.Vector.MapNorm
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

-- @[simp]
-- theorem add_comm : add x y = add y x := by
--   aesop_bitvec

-- theorem add_neg_y : add x (neg y) = sub x y := by
--   aesop_bitvec


-- @[simp]
-- theorem zero_sub_x_eq_neg_x : sub 0 x = neg x := by
--   aesop_bitvec

@[simp]
theorem neg_neg_x : neg (neg x) = x := by
  aesop_bitvec



  section Mul

    #check List.map

    def corec : (n : Nat) → (f : σ → σ × Bool) → (s : σ) → Bitvec n
      | 0,   _, _ => Vector.nil
      | n+1, f, s => Vector.snoc (corec n f ((f s).1)) ((f s).2)


    structure BitvecStateMachine where
      σ : Type u
      f : σ → σ × Bool
      s : σ


    structure MulState (σ₁ σ₂ : Type _) where
      initial_state1 : σ₁
      cur_state1 : σ₁
      cur_state2 : σ₂
      carry_states : List σ₁
      carry : Nat

    /--
      An alternative definition of `Bitvec` multiplication, when the two arguments can be described
      in terms of `corec`
    -/
    protected abbrev mul' (xs ys : BitvecStateMachine) : Bitvec n :=
      corec n (fun (s : MulState xs.σ ys.σ) =>
        let ⟨next_state1, _⟩ := xs.f s.cur_state1
        let ⟨next_state2, y⟩ := ys.f s.cur_state2
        let carry_states := if y then
          s.initial_state1 :: s.carry_states
        else
          s.carry_states

        /- Iterate all carry states, storing -/
        let (carry_states, carry) :=
          carry_states.map xs.f
          |>.unzip

        let carry := s.carry + (carry.map Bool.toNat).sum

        let out := (carry % 2) == 1
        let carry := carry / 2

        ({
          initial_state1 := s.initial_state1,
          cur_state1 := next_state1,
          cur_state2 := next_state2,
          carry_states,
          carry
        }, out)
      ) ⟨xs.s, xs.s, ys.s, [], 0⟩

  end Mul


end Bitvec
