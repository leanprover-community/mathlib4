/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.FieldTheory.Perfect

#align_import field_theory.perfect_closure from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# The perfect closure of a field
-/

universe u v

open Function

section

variable (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- `PerfectClosure K p` is the quotient by this relation. -/
@[mk_iff]
inductive PerfectClosure.R : ℕ × K → ℕ × K → Prop
  | intro : ∀ n x, PerfectClosure.R (n, x) (n + 1, frobenius K p x)
#align perfect_closure.r PerfectClosure.R

/-- The perfect closure is the smallest extension that makes frobenius surjective. -/
def PerfectClosure : Type u :=
  Quot (PerfectClosure.R K p)
#align perfect_closure PerfectClosure

end

namespace PerfectClosure

variable (K : Type u)

section Ring

variable [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Constructor for `PerfectClosure`. -/
def mk (x : ℕ × K) : PerfectClosure K p :=
  Quot.mk (R K p) x
#align perfect_closure.mk PerfectClosure.mk

@[simp] theorem mk_succ_pow (m : ℕ) (x : K) : mk K p ⟨m + 1, x ^ p⟩ = mk K p ⟨m, x⟩ :=
  Eq.symm $ Quot.sound (R.intro m x)

@[simp]
theorem quot_mk_eq_mk (x : ℕ × K) : (Quot.mk (R K p) x : PerfectClosure K p) = mk K p x :=
  rfl
#align perfect_closure.quot_mk_eq_mk PerfectClosure.quot_mk_eq_mk

variable {K p}

/-- Lift a function `ℕ × K → L` to a function on `PerfectClosure K p`. -/
-- Porting note: removed `@[elab_as_elim]` for "unexpected eliminator resulting type L"
def liftOn {L : Type*} (x : PerfectClosure K p) (f : ℕ × K → L)
    (hf : ∀ x y, R K p x y → f x = f y) : L :=
  Quot.liftOn x f hf
#align perfect_closure.lift_on PerfectClosure.liftOn

@[simp]
theorem liftOn_mk {L : Sort _} (f : ℕ × K → L) (hf : ∀ x y, R K p x y → f x = f y) (x : ℕ × K) :
    (mk K p x).liftOn f hf = f x :=
  rfl
#align perfect_closure.lift_on_mk PerfectClosure.liftOn_mk

@[elab_as_elim]
theorem induction_on (x : PerfectClosure K p) {q : PerfectClosure K p → Prop}
    (h : ∀ x, q (mk K p x)) : q x :=
  Quot.inductionOn x h
#align perfect_closure.induction_on PerfectClosure.induction_on

variable (K p)

private theorem mul_aux_left (x1 x2 y : ℕ × K) (H : R K p x1 x2) :
    mk K p (x1.1 + y.1, (frobenius K p)^[y.1] x1.2 * (frobenius K p)^[x1.1] y.2) =
      mk K p (x2.1 + y.1, (frobenius K p)^[y.1] x2.2 * (frobenius K p)^[x2.1] y.2) :=
  match x1, x2, H with
  | _, _, R.intro n x =>
    Quot.sound <| by
      rw [← iterate_succ_apply, iterate_succ_apply', iterate_succ_apply', ← frobenius_mul,
        Nat.succ_add]
      apply R.intro
      -- 🎉 no goals

private theorem mul_aux_right (x y1 y2 : ℕ × K) (H : R K p y1 y2) :
    mk K p (x.1 + y1.1, (frobenius K p)^[y1.1] x.2 * (frobenius K p)^[x.1] y1.2) =
      mk K p (x.1 + y2.1, (frobenius K p)^[y2.1] x.2 * (frobenius K p)^[x.1] y2.2) :=
  match y1, y2, H with
  | _, _, R.intro n y =>
    Quot.sound <| by
      rw [← iterate_succ_apply, iterate_succ_apply', iterate_succ_apply', ← frobenius_mul]
      -- ⊢ R K p (x.fst + (n, y).fst, (↑(frobenius K p))^[(n, y).fst] x.snd * (↑(froben …
      apply R.intro
      -- 🎉 no goals

instance : Mul (PerfectClosure K p) :=
  ⟨Quot.lift
      (fun x : ℕ × K =>
        Quot.lift
          (fun y : ℕ × K =>
            mk K p (x.1 + y.1, (frobenius K p)^[y.1] x.2 * (frobenius K p)^[x.1] y.2))
          (mul_aux_right K p x))
      fun x1 x2 (H : R K p x1 x2) =>
      funext fun e => Quot.inductionOn e fun y => mul_aux_left K p x1 x2 y H⟩

@[simp]
theorem mk_mul_mk (x y : ℕ × K) :
    mk K p x * mk K p y =
      mk K p (x.1 + y.1, (frobenius K p)^[y.1] x.2 * (frobenius K p)^[x.1] y.2) :=
  rfl
#align perfect_closure.mk_mul_mk PerfectClosure.mk_mul_mk

instance : CommMonoid (PerfectClosure K p) :=
  { (inferInstance : Mul (PerfectClosure K p)) with
    mul_assoc := fun e f g =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ =>
          Quot.inductionOn g fun ⟨s, z⟩ => by
            simp only [quot_mk_eq_mk, mk_mul_mk] -- Porting note: added this line
            -- ⊢ mk K p (m + n + s, (↑(frobenius K p))^[s] ((↑(frobenius K p))^[n] x * (↑(fro …
            apply congr_arg (Quot.mk _)
            -- ⊢ (m + n + s, (↑(frobenius K p))^[s] ((↑(frobenius K p))^[n] x * (↑(frobenius  …
            simp only [add_assoc, mul_assoc, iterate_map_mul, ← iterate_add_apply,
              add_comm, add_left_comm]
    one := mk K p (0, 1)
    one_mul := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ =>
        congr_arg (Quot.mk _) <| by
          simp only [RingHom.iterate_map_one, iterate_zero_apply, one_mul, zero_add]
          -- 🎉 no goals
    mul_one := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ =>
        congr_arg (Quot.mk _) <| by
          simp only [RingHom.iterate_map_one, iterate_zero_apply, mul_one, add_zero]
          -- 🎉 no goals
    mul_comm := fun e f =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ =>
          congr_arg (Quot.mk _) <| by simp only [add_comm, mul_comm] }
                                      -- 🎉 no goals

theorem one_def : (1 : PerfectClosure K p) = mk K p (0, 1) :=
  rfl
#align perfect_closure.one_def PerfectClosure.one_def

instance : Inhabited (PerfectClosure K p) :=
  ⟨1⟩

private theorem add_aux_left (x1 x2 y : ℕ × K) (H : R K p x1 x2) :
    mk K p (x1.1 + y.1, (frobenius K p)^[y.1] x1.2 + (frobenius K p)^[x1.1] y.2) =
      mk K p (x2.1 + y.1, (frobenius K p)^[y.1] x2.2 + (frobenius K p)^[x2.1] y.2) :=
  match x1, x2, H with
  | _, _, R.intro n x =>
    Quot.sound <| by
      rw [← iterate_succ_apply, iterate_succ_apply', iterate_succ_apply', ← frobenius_add,
        Nat.succ_add]
      apply R.intro
      -- 🎉 no goals

private theorem add_aux_right (x y1 y2 : ℕ × K) (H : R K p y1 y2) :
    mk K p (x.1 + y1.1, (frobenius K p)^[y1.1] x.2 + (frobenius K p)^[x.1] y1.2) =
      mk K p (x.1 + y2.1, (frobenius K p)^[y2.1] x.2 + (frobenius K p)^[x.1] y2.2) :=
  match y1, y2, H with
  | _, _, R.intro n y =>
    Quot.sound <| by
      rw [← iterate_succ_apply, iterate_succ_apply', iterate_succ_apply', ← frobenius_add]
      -- ⊢ R K p (x.fst + (n, y).fst, (↑(frobenius K p))^[(n, y).fst] x.snd + (↑(froben …
      apply R.intro
      -- 🎉 no goals

instance : Add (PerfectClosure K p) :=
  ⟨Quot.lift
      (fun x : ℕ × K =>
        Quot.lift
          (fun y : ℕ × K =>
            mk K p (x.1 + y.1, (frobenius K p)^[y.1] x.2 + (frobenius K p)^[x.1] y.2))
          (add_aux_right K p x))
      fun x1 x2 (H : R K p x1 x2) =>
      funext fun e => Quot.inductionOn e fun y => add_aux_left K p x1 x2 y H⟩

@[simp]
theorem mk_add_mk (x y : ℕ × K) :
    mk K p x + mk K p y =
      mk K p (x.1 + y.1, (frobenius K p)^[y.1] x.2 + (frobenius K p)^[x.1] y.2) :=
  rfl
#align perfect_closure.mk_add_mk PerfectClosure.mk_add_mk

instance : Neg (PerfectClosure K p) :=
  ⟨Quot.lift (fun x : ℕ × K => mk K p (x.1, -x.2)) fun x y (H : R K p x y) =>
      match x, y, H with
      | _, _, R.intro n x => Quot.sound <| by rw [← frobenius_neg]; apply R.intro⟩
                                              -- ⊢ R K p ((n, x).fst, -(n, x).snd) ((n + 1, ↑(frobenius K p) x).fst, ↑(frobeniu …
                                                                    -- 🎉 no goals

@[simp]
theorem neg_mk (x : ℕ × K) : -mk K p x = mk K p (x.1, -x.2) :=
  rfl
#align perfect_closure.neg_mk PerfectClosure.neg_mk

instance : Zero (PerfectClosure K p) :=
  ⟨mk K p (0, 0)⟩

theorem zero_def : (0 : PerfectClosure K p) = mk K p (0, 0) :=
  rfl
#align perfect_closure.zero_def PerfectClosure.zero_def

@[simp]
theorem mk_zero_zero : mk K p (0, 0) = 0 :=
  rfl
#align perfect_closure.mk_zero_zero PerfectClosure.mk_zero_zero

-- Porting note: improved proof structure
theorem mk_zero (n : ℕ) : mk K p (n, 0) = 0 := by
  induction' n with n ih
  -- ⊢ mk K p (Nat.zero, 0) = 0
  · rfl
    -- 🎉 no goals
  rw [← ih]
  -- ⊢ mk K p (Nat.succ n, 0) = mk K p (n, 0)
  symm
  -- ⊢ mk K p (n, 0) = mk K p (Nat.succ n, 0)
  apply Quot.sound
  -- ⊢ R K p (n, 0) (Nat.succ n, 0)
  have := R.intro (p := p) n (0 : K)
  -- ⊢ R K p (n, 0) (Nat.succ n, 0)
  rwa [frobenius_zero K p] at this
  -- 🎉 no goals
#align perfect_closure.mk_zero PerfectClosure.mk_zero

-- Porting note: improved proof structure
theorem R.sound (m n : ℕ) (x y : K) (H : (frobenius K p)^[m] x = y) :
    mk K p (n, x) = mk K p (m + n, y) := by
  subst H
  -- ⊢ mk K p (n, x) = mk K p (m + n, (↑(frobenius K p))^[m] x)
  induction' m with m ih
  -- ⊢ mk K p (n, x) = mk K p (Nat.zero + n, (↑(frobenius K p))^[Nat.zero] x)
  · simp only [Nat.zero_eq, zero_add, iterate_zero_apply]
    -- 🎉 no goals
  rw [ih, Nat.succ_add, iterate_succ']
  -- ⊢ mk K p (m + n, (↑(frobenius K p))^[m] x) = mk K p (Nat.succ (m + n), (↑(frob …
  apply Quot.sound
  -- ⊢ R K p (m + n, (↑(frobenius K p))^[m] x) (Nat.succ (m + n), (↑(frobenius K p) …
  apply R.intro
  -- 🎉 no goals
#align perfect_closure.r.sound PerfectClosure.R.sound

instance PerfectClosure.addCommGroup : AddCommGroup (PerfectClosure K p) :=
  { (inferInstance : Add (PerfectClosure K p)),
    (inferInstance : Neg (PerfectClosure K p)) with
    add_assoc := fun e f g =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ =>
          Quot.inductionOn g fun ⟨s, z⟩ => by
            simp only [quot_mk_eq_mk, mk_add_mk] -- Porting note: added this line
            -- ⊢ mk K p (m + n + s, (↑(frobenius K p))^[s] ((↑(frobenius K p))^[n] x + (↑(fro …
            apply congr_arg (Quot.mk _)
            -- ⊢ (m + n + s, (↑(frobenius K p))^[s] ((↑(frobenius K p))^[n] x + (↑(frobenius  …
            simp only [iterate_map_add, ← iterate_add_apply, add_assoc, add_comm s _]
            -- 🎉 no goals
    zero := 0
    zero_add := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ =>
        congr_arg (Quot.mk _) <| by
          simp only [RingHom.iterate_map_zero, iterate_zero_apply, zero_add]
          -- 🎉 no goals
    add_zero := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ =>
        congr_arg (Quot.mk _) <| by
          simp only [RingHom.iterate_map_zero, iterate_zero_apply, add_zero]
          -- 🎉 no goals
    sub_eq_add_neg := fun a b => rfl
    add_left_neg := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ => by
        simp only [quot_mk_eq_mk, neg_mk, mk_add_mk, RingHom.iterate_map_neg, add_left_neg, mk_zero]
        -- 🎉 no goals
    add_comm := fun e f =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ => congr_arg (Quot.mk _) <| by simp only [add_comm] }
                                                                     -- 🎉 no goals

instance PerfectClosure.commRing : CommRing (PerfectClosure K p) :=
  { PerfectClosure.addCommGroup K p, AddMonoidWithOne.unary,
    (inferInstance : CommMonoid (PerfectClosure K p)) with
    -- Porting note: added `zero_mul`, `mul_zero`
    zero_mul := fun a => by
      refine Quot.inductionOn a fun ⟨m, x⟩ => ?_
      -- ⊢ 0 * Quot.mk (R K p) (m, x) = 0
      rw [zero_def, quot_mk_eq_mk, mk_mul_mk]
      -- ⊢ mk K p ((0, 0).fst + (m, x).fst, (↑(frobenius K p))^[(m, x).fst] (0, 0).snd  …
      simp only [zero_add, iterate_zero, id_eq, RingHom.iterate_map_zero, zero_mul, mk_zero]
      -- 🎉 no goals
    mul_zero := fun a => by
      refine Quot.inductionOn a fun ⟨m, x⟩ => ?_
      -- ⊢ Quot.mk (R K p) (m, x) * 0 = 0
      rw [zero_def, quot_mk_eq_mk, mk_mul_mk]
      -- ⊢ mk K p ((m, x).fst + (0, 0).fst, (↑(frobenius K p))^[(0, 0).fst] (m, x).snd  …
      simp only [zero_add, iterate_zero, id_eq, RingHom.iterate_map_zero, mul_zero, mk_zero]
            -- ⊢ mk K p (m + (n + s), (↑(frobenius K p))^[n + s] x * (↑(frobenius K p))^[m] ( …
      -- 🎉 no goals
            -- ⊢ mk K p (m + (n + s), (↑(frobenius K p))^[n + s] x * (↑(frobenius K p))^[m] ( …
    left_distrib := fun e f g =>
            -- ⊢ (↑(frobenius K p))^[m] ((↑(frobenius K p))^[n + s] x * (↑(frobenius K p))^[m …
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ =>
          Quot.inductionOn g fun ⟨s, z⟩ => by
            simp only [quot_mk_eq_mk, mk_add_mk, mk_mul_mk] -- Porting note: added this line
            simp only [add_assoc, add_comm, add_left_comm]
            apply R.sound
            simp only [iterate_map_mul, iterate_map_add, ← iterate_add_apply,
            -- ⊢ mk K p (m + n + s, (↑(frobenius K p))^[s] ((↑(frobenius K p))^[n] x + (↑(fro …
              mul_add, add_comm, add_left_comm]
            -- ⊢ mk K p (s + (m + n), (↑(frobenius K p))^[s] ((↑(frobenius K p))^[n] x + (↑(f …
    right_distrib := fun e f g =>
            -- ⊢ (↑(frobenius K p))^[s] ((↑(frobenius K p))^[s] ((↑(frobenius K p))^[n] x + ( …
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ =>
          Quot.inductionOn g fun ⟨s, z⟩ => by
            simp only [quot_mk_eq_mk, mk_add_mk, mk_mul_mk] -- Porting note: added this line
            simp only [add_assoc, add_comm _ s, add_left_comm _ s]
            apply R.sound
            simp only [iterate_map_mul, iterate_map_add, ← iterate_add_apply,
              add_mul, add_comm, add_left_comm] }

theorem eq_iff' (x y : ℕ × K) :
    mk K p x = mk K p y ↔ ∃ z, (frobenius K p)^[y.1 + z] x.2 = (frobenius K p)^[x.1 + z] y.2 := by
  constructor
  -- ⊢ mk K p x = mk K p y → ∃ z, (↑(frobenius K p))^[y.fst + z] x.snd = (↑(frobeni …
  · intro H
    -- ⊢ ∃ z, (↑(frobenius K p))^[y.fst + z] x.snd = (↑(frobenius K p))^[x.fst + z] y …
    replace H := Quot.exact _ H
    -- ⊢ ∃ z, (↑(frobenius K p))^[y.fst + z] x.snd = (↑(frobenius K p))^[x.fst + z] y …
    induction H
    case rel x y H => cases' H with n x; exact ⟨0, rfl⟩
    -- 🎉 no goals
    case refl H => exact ⟨0, rfl⟩
    -- ⊢ ∃ z, (↑(frobenius K p))^[x✝.fst + z] y✝.snd = (↑(frobenius K p))^[y✝.fst + z …
    -- 🎉 no goals
    case symm x y H ih => cases' ih with w ih; exact ⟨w, ih.symm⟩
    -- ⊢ ∃ z, (↑(frobenius K p))^[z✝.fst + z] x✝.snd = (↑(frobenius K p))^[x✝.fst + z …
    -- 🎉 no goals
    case trans x y z H1 H2 ih1 ih2 =>
      cases' ih1 with z1 ih1
      cases' ih2 with z2 ih2
      exists z2 + (y.1 + z1)
      rw [← add_assoc, iterate_add_apply, ih1]
      rw [← iterate_add_apply, add_comm, iterate_add_apply, ih2]
      rw [← iterate_add_apply]
      simp only [add_comm, add_left_comm]
  intro H
  -- ⊢ mk K p x = mk K p y
  cases' x with m x
  -- ⊢ mk K p (m, x) = mk K p y
  cases' y with n y
  -- ⊢ mk K p (m, x) = mk K p (n, y)
  cases' H with z H; dsimp only at H
  -- ⊢ mk K p (m, x) = mk K p (n, y)
                     -- ⊢ mk K p (m, x) = mk K p (n, y)
  rw [R.sound K p (n + z) m x _ rfl, R.sound K p (m + z) n y _ rfl, H]
  -- ⊢ mk K p (n + z + m, (↑(frobenius K p))^[m + z] y) = mk K p (m + z + n, (↑(fro …
  rw [add_assoc, add_comm, add_comm z]
  -- 🎉 no goals
#align perfect_closure.eq_iff' PerfectClosure.eq_iff'

theorem nat_cast (n x : ℕ) : (x : PerfectClosure K p) = mk K p (n, x) := by
  induction' n with n ih
  -- ⊢ ↑x = mk K p (Nat.zero, ↑x)
  · induction' x with x ih
    -- ⊢ ↑Nat.zero = mk K p (Nat.zero, ↑Nat.zero)
    · simp
      -- 🎉 no goals
    rw [Nat.cast_succ, Nat.cast_succ, ih]
    -- ⊢ mk K p (Nat.zero, ↑x) + 1 = mk K p (Nat.zero, ↑x + 1)
    rfl
    -- 🎉 no goals
  rw [ih]; apply Quot.sound
  -- ⊢ mk K p (n, ↑x) = mk K p (Nat.succ n, ↑x)
           -- ⊢ R K p (n, ↑x) (Nat.succ n, ↑x)
  -- Porting note: was `conv`
  suffices R K p (n, (x : K)) (Nat.succ n, frobenius K p (x : K)) by
    rwa [frobenius_nat_cast K p x] at this
  apply R.intro
  -- 🎉 no goals
#align perfect_closure.nat_cast PerfectClosure.nat_cast

theorem int_cast (x : ℤ) : (x : PerfectClosure K p) = mk K p (0, x) := by
  induction x <;> simp only [Int.ofNat_eq_coe, Int.cast_ofNat, Int.cast_negSucc, nat_cast K p 0]
  -- ⊢ ↑(Int.ofNat a✝) = mk K p (0, ↑(Int.ofNat a✝))
                  -- 🎉 no goals
                  -- ⊢ -mk K p (0, ↑(a✝ + 1)) = mk K p (0, -↑(a✝ + 1))
  rfl
  -- 🎉 no goals
#align perfect_closure.int_cast PerfectClosure.int_cast

theorem nat_cast_eq_iff (x y : ℕ) : (x : PerfectClosure K p) = y ↔ (x : K) = y := by
  constructor <;> intro H
  -- ⊢ ↑x = ↑y → ↑x = ↑y
                  -- ⊢ ↑x = ↑y
                  -- ⊢ ↑x = ↑y
  · rw [nat_cast K p 0, nat_cast K p 0, eq_iff'] at H
    -- ⊢ ↑x = ↑y
    cases' H with z H
    -- ⊢ ↑x = ↑y
    simpa only [zero_add, iterate_fixed (frobenius_nat_cast K p _)] using H
    -- 🎉 no goals
  rw [nat_cast K p 0, nat_cast K p 0, H]
  -- 🎉 no goals
#align perfect_closure.nat_cast_eq_iff PerfectClosure.nat_cast_eq_iff

instance : CharP (PerfectClosure K p) p := by
  constructor; intro x; rw [← CharP.cast_eq_zero_iff K]
  -- ⊢ ∀ (x : ℕ), ↑x = 0 ↔ p ∣ x
               -- ⊢ ↑x = 0 ↔ p ∣ x
                        -- ⊢ ↑x = 0 ↔ ↑x = 0
  rw [← Nat.cast_zero, nat_cast_eq_iff, Nat.cast_zero]
  -- 🎉 no goals

theorem frobenius_mk (x : ℕ × K) :
    (frobenius (PerfectClosure K p) p : PerfectClosure K p → PerfectClosure K p) (mk K p x) =
      mk _ _ (x.1, x.2 ^ p) := by
  simp only [frobenius_def]
  -- ⊢ mk K p x ^ p = mk K p (x.fst, x.snd ^ p)
  cases' x with n x
  -- ⊢ mk K p (n, x) ^ p = mk K p ((n, x).fst, (n, x).snd ^ p)
  dsimp only
  -- ⊢ mk K p (n, x) ^ p = mk K p (n, x ^ p)
  suffices ∀ p' : ℕ, mk K p (n, x) ^ p' = mk K p (n, x ^ p') by apply this
  -- ⊢ ∀ (p' : ℕ), mk K p (n, x) ^ p' = mk K p (n, x ^ p')
  intro p
  -- ⊢ mk K p✝ (n, x) ^ p = mk K p✝ (n, x ^ p)
  induction' p with p ih
  -- ⊢ mk K p (n, x) ^ Nat.zero = mk K p (n, x ^ Nat.zero)
  case zero => apply R.sound; rw [(frobenius _ _).iterate_map_one, pow_zero]
  -- ⊢ mk K p✝ (n, x) ^ Nat.succ p = mk K p✝ (n, x ^ Nat.succ p)
  -- 🎉 no goals
  case succ =>
    rw [pow_succ, ih]
    symm
    apply R.sound
    simp only [pow_succ, iterate_map_mul]
#align perfect_closure.frobenius_mk PerfectClosure.frobenius_mk

/-- Embedding of `K` into `PerfectClosure K p` -/
def of : K →+* PerfectClosure K p where
  toFun x := mk _ _ (0, x)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
#align perfect_closure.of PerfectClosure.of

theorem of_apply (x : K) : of K p x = mk _ _ (0, x) :=
  rfl
#align perfect_closure.of_apply PerfectClosure.of_apply

end Ring

theorem eq_iff [CommRing K] [IsReduced K] (p : ℕ) [Fact p.Prime] [CharP K p] (x y : ℕ × K) :
    Quot.mk (R K p) x = Quot.mk (R K p) y ↔ (frobenius K p)^[y.1] x.2 = (frobenius K p)^[x.1] y.2 :=
  (eq_iff' K p x y).trans
    ⟨fun ⟨z, H⟩ => (frobenius_inj K p).iterate z <| by simpa only [add_comm, iterate_add] using H,
                                                       -- 🎉 no goals
      fun H => ⟨0, H⟩⟩
#align perfect_closure.eq_iff PerfectClosure.eq_iff

section Field

variable [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

instance : Inv (PerfectClosure K p) :=
  ⟨Quot.lift (fun x : ℕ × K => Quot.mk (R K p) (x.1, x.2⁻¹)) fun x y (H : R K p x y) =>
      match x, y, H with
      | _, _, R.intro n x =>
        Quot.sound <| by
          simp only [frobenius_def]
          -- ⊢ R K p (n, x⁻¹) (n + 1, (x ^ p)⁻¹)
          rw [← inv_pow]
          -- ⊢ R K p (n, x⁻¹) (n + 1, x⁻¹ ^ p)
          apply R.intro⟩
          -- 🎉 no goals

-- Porting note: added
@[simp]
theorem mk_inv (x : ℕ × K) : (mk K p x)⁻¹ = mk K p (x.1, x.2⁻¹) :=
  rfl

-- Porting note: added to avoid "unknown free variable" error
instance : DivisionRing (PerfectClosure K p) :=
  { (inferInstance : Inv (PerfectClosure K p)) with
    exists_pair_ne := ⟨0, 1, fun H => zero_ne_one ((eq_iff _ _ _ _).1 H)⟩
    mul_inv_cancel := fun e =>
      induction_on e fun ⟨m, x⟩ H => by
        -- Porting note: restructured
        have := mt (eq_iff _ _ _ _).2 H
        -- ⊢ mk K p (m, x) * (mk K p (m, x))⁻¹ = 1
        rw [mk_inv, mk_mul_mk]
        -- ⊢ mk K p ((m, x).fst + ((m, x).fst, (m, x).snd⁻¹).fst, (↑(frobenius K p))^[((m …
        refine (eq_iff K p _ _).2 ?_
        -- ⊢ (↑(frobenius K p))^[(0, 1).fst] ((m, x).fst + ((m, x).fst, (m, x).snd⁻¹).fst …
        simp only [(frobenius _ _).iterate_map_one, (frobenius K p).iterate_map_zero,
            iterate_zero_apply, ← iterate_map_mul] at this ⊢
        rw [mul_inv_cancel this, (frobenius _ _).iterate_map_one]
        -- 🎉 no goals
    inv_zero := congr_arg (Quot.mk (R K p)) (by rw [inv_zero]) }
                                                -- 🎉 no goals

instance : Field (PerfectClosure K p) :=
  { (inferInstance : DivisionRing (PerfectClosure K p)),
    (inferInstance : CommRing (PerfectClosure K p)) with }

instance : PerfectRing (PerfectClosure K p) p where
  bijective_frobenius := by
    let f : PerfectClosure K p → PerfectClosure K p := fun e ↦
      liftOn e (fun x => mk K p (x.1 + 1, x.2)) fun x y H =>
      match x, y, H with
      | _, _, R.intro n x => Quot.sound (R.intro _ _)
    have hl : LeftInverse f (frobenius (PerfectClosure K p) p) := fun e ↦
      induction_on e fun ⟨n, x⟩ => by
        simp only [liftOn_mk, frobenius_mk]
        exact (Quot.sound <| R.intro _ _).symm
    have hr : RightInverse f (frobenius (PerfectClosure K p) p) := fun e ↦
      induction_on e fun ⟨n, x⟩ => by
        simp only [liftOn_mk, frobenius_mk]
        exact (Quot.sound <| R.intro _ _).symm
    exact bijective_iff_has_inverse.mpr ⟨f, hl, hr⟩
    -- 🎉 no goals

@[simp]
theorem iterate_frobenius_mk (n : ℕ) (x : K) :
    (frobenius (PerfectClosure K p) p)^[n] (mk K p ⟨n, x⟩) = of K p x := by
  induction' n with n ih; rfl
  -- ⊢ (↑(frobenius (PerfectClosure K p) p))^[Nat.zero] (mk K p (Nat.zero, x)) = ↑( …
                          -- ⊢ (↑(frobenius (PerfectClosure K p) p))^[Nat.succ n] (mk K p (Nat.succ n, x))  …
  rw [iterate_succ_apply, ← ih, frobenius_mk, mk_succ_pow]
  -- 🎉 no goals

/-- Given a field `K` of characteristic `p` and a perfect ring `L` of the same characteristic,
any homomorphism `K →+* L` can be lifted to `PerfectClosure K p`. -/
noncomputable def lift (L : Type v) [CommSemiring L] [CharP L p] [PerfectRing L p] :
    (K →+* L) ≃ (PerfectClosure K p →+* L) where
  toFun f :=
    { toFun := by
        refine' fun e => liftOn e (fun x => (frobeniusEquiv L p).symm^[x.1] (f x.2)) _
        -- ⊢ ∀ (x y : ℕ × K), R K p x y → (fun x => (↑(RingEquiv.symm (frobeniusEquiv L p …
        rintro - - ⟨n, x⟩
        -- ⊢ (fun x => (↑(RingEquiv.symm (frobeniusEquiv L p)))^[x.fst] (↑f x.snd)) (n, x …
        simp [f.map_frobenius]
        -- 🎉 no goals
      map_one' := f.map_one
      map_zero' := f.map_zero
      map_mul' := by
        rintro ⟨n, x⟩ ⟨m, y⟩
        -- ⊢ OneHom.toFun { toFun := fun e => liftOn e (fun x => (↑(RingEquiv.symm (frobe …
        simp only [quot_mk_eq_mk, liftOn_mk, f.map_iterate_frobenius, mk_mul_mk, map_mul,
          iterate_map_mul]
        have := LeftInverse.iterate (frobeniusEquiv_symm_apply_frobenius L p)
        -- ⊢ (↑(RingEquiv.symm (frobeniusEquiv L p)))^[n + m] ((↑(frobenius L p))^[m] (↑f …
        rw [iterate_add_apply, this _ _, add_comm, iterate_add_apply, this _ _]
        -- 🎉 no goals
      map_add' := by
        rintro ⟨n, x⟩ ⟨m, y⟩
        -- ⊢ OneHom.toFun (↑{ toOneHom := { toFun := fun e => liftOn e (fun x => (↑(RingE …
        simp only [quot_mk_eq_mk, liftOn_mk, f.map_iterate_frobenius, mk_add_mk, map_add,
          iterate_map_add]
        have := LeftInverse.iterate (frobeniusEquiv_symm_apply_frobenius L p)
        -- ⊢ (↑(RingEquiv.symm (frobeniusEquiv L p)))^[n + m] ((↑(frobenius L p))^[m] (↑f …
        rw [iterate_add_apply, this _ _, add_comm n, iterate_add_apply, this _ _] }
        -- 🎉 no goals
  invFun f := f.comp (of K p)
  left_inv f := by ext x; rfl
                   -- ⊢ ↑((fun f => RingHom.comp f (of K p)) ((fun f => { toMonoidHom := { toOneHom  …
                          -- 🎉 no goals
  right_inv f := by
    ext ⟨n, x⟩
    -- ⊢ ↑((fun f => { toMonoidHom := { toOneHom := { toFun := fun e => liftOn e (fun …
    simp only [quot_mk_eq_mk, RingHom.comp_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      liftOn_mk]
    apply (injective_frobenius L p).iterate n
    -- ⊢ (↑(frobenius L p))^[n] ((↑(RingEquiv.symm (frobeniusEquiv L p)))^[n] (↑f (↑( …
    rw [← f.map_iterate_frobenius, iterate_frobenius_mk,
      RightInverse.iterate (frobenius_apply_frobeniusEquiv_symm L p) n]
#align perfect_closure.lift PerfectClosure.lift

end Field

end PerfectClosure
