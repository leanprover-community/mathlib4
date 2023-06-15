import Mathlib.Data.Bitvec.Tactic

-- A lot of this should probably go to a differet file here and not Mathlib
inductive Refinement {α : Type u} : Option α → Option α → Prop
  | bothSome {x y : α } : x = y → Refinement (some x) (some y)
  | noneAny {x? : Option α} : Refinement none x?

namespace Refinement

theorem Refinement.refl {α: Type u} : ∀ x : Option α, Refinement x x := by
  intro x ; cases x
  apply Refinement.noneAny
  apply Refinement.bothSome; rfl

theorem Refinement.trans {α : Type u} : ∀ x y z : Option α, Refinement x y → Refinement y z → Refinement x z := by
  intro x y z h₁ h₂
  cases h₁ <;> cases h₂ <;> try { apply Refinement.noneAny } ; try {apply Refinement.bothSome; assumption}
  rename_i x y hxy y h
  rw [hxy, h]; apply Refinement.refl

instance {α : Type u} [DecidableEq α] : DecidableRel (@Refinement α) := by
  intro x y
  cases x <;> cases y
  { apply isTrue; exact Refinement.noneAny}
  { apply isTrue; exact Refinement.noneAny }
  { apply isFalse; intro h; cases h }
  { rename_i val val'
    cases (decEq val val')
    { apply isFalse; intro h; cases h; contradiction }
    { apply isTrue; apply Refinement.bothSome; assumption }
  }

end Refinement

infix:50 " ⊑ " => Refinement

@[simp, aesop safe]
theorem refine_some_some (h : x = y) : some x ⊑ some y :=
  Refinement.bothSome h

open Bitvec

variable (a b A B x y z : Bitvec w)


-- def statement12 :  some (Bitvec.sub x y) ⊑
--     some (Bitvec.xor x y)
--     := by aesop_bitvec

-- def statement13 :  some (Bitvec.sub ((-1 : Bitvec w)) x) ⊑
--     some (Bitvec.xor x ((-1 : Bitvec w)))
--     := by aesop_bitvec


-- def statement15 :  some (Bitvec.sub (Bitvec.sub x y) x) ⊑
--     some (Bitvec.sub 0 y)
--     := sorry

-- def statement16 :  some
--       (Bitvec.sub (Bitvec.or A B)
--         (Bitvec.xor A B)) ⊑
--     some (Bitvec.and A B)
--     := sorry

def statement17 :  some
      (Bitvec.and (Bitvec.xor x ((-1 : Bitvec w)))
        (Bitvec.xor y ((-1 : Bitvec w)))) ⊑
    some (Bitvec.xor (Bitvec.or x y) ((-1 : Bitvec w)))
    := by aesop_bitvec

def statement18 :  some
      (Bitvec.and (Bitvec.or A B)
        (Bitvec.xor (Bitvec.and A B) ((-1 : Bitvec w)))) ⊑
    some (Bitvec.xor A B)
    := by aesop_bitvec

def statement19 :  some
      (Bitvec.and (Bitvec.xor (Bitvec.and A B) ((-1 : Bitvec w)))
        (Bitvec.or A B)) ⊑
    some (Bitvec.xor A B)
    := by aesop_bitvec

def statement20 :  some (Bitvec.and (Bitvec.xor A B) A) ⊑
    some (Bitvec.and A (Bitvec.xor B ((-1 : Bitvec w))))
    := by aesop_bitvec

def statement21 :  some
      (Bitvec.and (Bitvec.or (Bitvec.xor A ((-1 : Bitvec w))) B)
        A) ⊑
    some (Bitvec.and A B)
    := by aesop_bitvec

def statement22 :  some
      (Bitvec.and (Bitvec.xor A B)
        (Bitvec.xor (Bitvec.xor B (Bitvec.ofInt w C)) A)) ⊑
    some
      (Bitvec.and (Bitvec.xor A B)
        (Bitvec.xor (Bitvec.ofInt w C) ((-1 : Bitvec w))))
    := by aesop_bitvec

def statement23 :  some
      (Bitvec.and (Bitvec.or A B)
        (Bitvec.xor (Bitvec.xor A ((-1 : Bitvec w))) B)) ⊑
    some (Bitvec.and A B)
    := by aesop_bitvec

def statement24 :  some
      (Bitvec.or (Bitvec.and (Bitvec.xor A ((-1 : Bitvec w))) B)
        A) ⊑
    some (Bitvec.or A B)
    := by aesop_bitvec

def statement25 :  some
      (Bitvec.or (Bitvec.and A B)
        (Bitvec.xor A ((-1 : Bitvec w)))) ⊑
    some (Bitvec.or (Bitvec.xor A ((-1 : Bitvec w))) B)
    := by aesop_bitvec

def statement26 :  some
      (Bitvec.or (Bitvec.and A (Bitvec.xor B ((-1 : Bitvec w))))
        (Bitvec.xor A B)) ⊑
    some (Bitvec.xor A B)
    := by aesop_bitvec

def statement27 :  some
      (Bitvec.or (Bitvec.and A (Bitvec.xor (Bitvec.ofInt w D) ((-1 : Bitvec w))))
        (Bitvec.and (Bitvec.xor A ((-1 : Bitvec w))) (Bitvec.ofInt w D))) ⊑
    some (Bitvec.xor A (Bitvec.ofInt w D))
    := by aesop_bitvec

def statement28 :  some
      (Bitvec.or (Bitvec.xor A B)
        (Bitvec.xor (Bitvec.xor B (Bitvec.ofInt w C)) A)) ⊑
    some (Bitvec.or (Bitvec.xor A B) (Bitvec.ofInt w C))
    := by aesop_bitvec

def statement29 :  some
      (Bitvec.or (Bitvec.and (Bitvec.or B (Bitvec.ofInt w C)) A)
        B) ⊑
    some (Bitvec.or B (Bitvec.and A (Bitvec.ofInt w C)))
    := by aesop_bitvec

def statement30 :  some
      (Bitvec.or (Bitvec.xor A ((-1 : Bitvec w)))
        (Bitvec.xor B ((-1 : Bitvec w)))) ⊑
    some (Bitvec.xor (Bitvec.and A B) ((-1 : Bitvec w)))
    := by aesop_bitvec

def statement31 :  some (Bitvec.or (Bitvec.ofInt w op0) (Bitvec.xor (Bitvec.ofInt w op0) B)) ⊑
    some (Bitvec.or (Bitvec.ofInt w op0) B)
    := by aesop_bitvec

def statement32 :  some
      (Bitvec.or A
        (Bitvec.xor (Bitvec.xor A ((-1 : Bitvec w))) B)) ⊑
    some (Bitvec.or A (Bitvec.xor B ((-1 : Bitvec w))))
    := by aesop_bitvec

def statement33 :  some
      (Bitvec.or (Bitvec.and A B)
        (Bitvec.xor A B)) ⊑
    some (Bitvec.or A B)
    := by aesop_bitvec

def statement34 :  some
      (Bitvec.or A
        (Bitvec.xor (Bitvec.or A B) ((-1 : Bitvec w)))) ⊑
    some (Bitvec.or A (Bitvec.xor B ((-1 : Bitvec w))))
    := by aesop_bitvec

def statement35 :  some
      (Bitvec.or A
        (Bitvec.xor (Bitvec.xor A B) ((-1 : Bitvec w)))) ⊑
    some (Bitvec.or A (Bitvec.xor B ((-1 : Bitvec w))))
    := by aesop_bitvec

def statement36 :  some
      (Bitvec.or (Bitvec.and A B)
        (Bitvec.xor (Bitvec.xor A ((-1 : Bitvec w))) B)) ⊑
    some (Bitvec.xor (Bitvec.xor A ((-1 : Bitvec w))) B)
    := by aesop_bitvec

def statement37 :  some (Bitvec.or (Bitvec.or A (Bitvec.ofInt w C1)) (Bitvec.ofInt w op1)) ⊑
    some (Bitvec.or (Bitvec.or A (Bitvec.ofInt w op1)) (Bitvec.ofInt w C1))
    := by aesop_bitvec

def statement38 :  some
      (Bitvec.xor (Bitvec.and (Bitvec.xor (Bitvec.ofInt w nx) ((-1 : Bitvec w))) y)
        ((-1 : Bitvec w))) ⊑
    some (Bitvec.or (Bitvec.ofInt w nx) (Bitvec.xor y ((-1 : Bitvec w))))
    := by aesop_bitvec

def statement39 :  some
      (Bitvec.xor (Bitvec.or (Bitvec.xor (Bitvec.ofInt w nx) ((-1 : Bitvec w))) y)
        ((-1 : Bitvec w))) ⊑
    some (Bitvec.and (Bitvec.ofInt w nx) (Bitvec.xor y ((-1 : Bitvec w))))
    := sorry

def statement40 :  some (Bitvec.xor (Bitvec.and x y) ((-1 : Bitvec w))) ⊑
    some
      (Bitvec.or (Bitvec.xor x ((-1 : Bitvec w)))
        (Bitvec.xor y ((-1 : Bitvec w))))
    := sorry

def statement41 :  some (Bitvec.xor (Bitvec.or x y) ((-1 : Bitvec w))) ⊑
    some
      (Bitvec.and (Bitvec.xor x ((-1 : Bitvec w)))
        (Bitvec.xor y ((-1 : Bitvec w))))
    := sorry

def statement42 :  some (Bitvec.xor (Bitvec.or A (Bitvec.ofInt w op1)) (Bitvec.ofInt w op1)) ⊑
    some (Bitvec.and A (Bitvec.xor (Bitvec.ofInt w op1) ((-1 : Bitvec w))))
    := sorry

def statement43 :  some (Bitvec.xor (Bitvec.and A (Bitvec.ofInt w op1)) (Bitvec.ofInt w op1)) ⊑
    some (Bitvec.and (Bitvec.xor A ((-1 : Bitvec w))) (Bitvec.ofInt w op1))
    := sorry

def statement44 :  some
      (Bitvec.xor (Bitvec.and A B)
        (Bitvec.or A B)) ⊑
    some (Bitvec.xor A B)
    := sorry

def statement45 :  some
      (Bitvec.xor (Bitvec.or A (Bitvec.xor B ((-1 : Bitvec w))))
        (Bitvec.or (Bitvec.xor A ((-1 : Bitvec w))) B)) ⊑
    some (Bitvec.xor A B)
    := sorry

def statement46 :  some
      (Bitvec.xor (Bitvec.and A (Bitvec.xor B ((-1 : Bitvec w))))
        (Bitvec.and (Bitvec.xor A ((-1 : Bitvec w))) B)) ⊑
    some (Bitvec.xor A B)
    := sorry

def statement47 :  some
      (Bitvec.xor (Bitvec.xor A (Bitvec.ofInt w c))
        (Bitvec.or A B)) ⊑
    some
      (Bitvec.xor (Bitvec.and (Bitvec.xor A ((-1 : Bitvec w))) B)
        (Bitvec.ofInt w c))
    := sorry

def statement48 :  some
      (Bitvec.xor (Bitvec.and A B)
        (Bitvec.xor A B)) ⊑
    some (Bitvec.or A B)
    := sorry

def statement49 :  some
      (Bitvec.xor (Bitvec.and A (Bitvec.xor B ((-1 : Bitvec w))))
        (Bitvec.xor A ((-1 : Bitvec w)))) ⊑
    some (Bitvec.xor (Bitvec.and A B) ((-1 : Bitvec w)))
    := sorry
