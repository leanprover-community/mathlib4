/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Algebra.Jordan.Basic
import Mathlib.Algebra.Module.Basic

#align_import algebra.symmetrized from "leanprover-community/mathlib"@"933547832736be61a5de6576e22db351c6c2fbfd"

/-!
# Symmetrized algebra

A commutative multiplication on a real or complex space can be constructed from any multiplication
by "symmetrization" i.e
$$
a \circ b = \frac{1}{2}(ab + ba)
$$

We provide the symmetrized version of a type `α` as `SymAlg α`, with notation `αˢʸᵐ`.

## Implementation notes

The approach taken here is inspired by `Mathlib/Algebra/Opposites.lean`. We use Oxford Spellings
(IETF en-GB-oxendict).

## References

* [Hanche-Olsen and Størmer, Jordan Operator Algebras][hancheolsenstormer1984]
-/


open Function

/-- The symmetrized algebra has the same underlying space as the original algebra.
-/
def SymAlg (α : Type*) : Type _ :=
  α
#align sym_alg SymAlg

-- mathport name: «expr ˢʸᵐ»
postfix:max "ˢʸᵐ" => SymAlg

namespace SymAlg

variable {α : Type*}

/-- The element of `SymAlg α` that represents `a : α`. -/
@[match_pattern]
-- Porting note: removed @[pp_nodot]
def sym : α ≃ αˢʸᵐ :=
  Equiv.refl _
#align sym_alg.sym SymAlg.sym

/-- The element of `α` represented by `x : αˢʸᵐ`. -/
-- Porting note: removed @[pp_nodot]
def unsym : αˢʸᵐ ≃ α :=
  Equiv.refl _
#align sym_alg.unsym SymAlg.unsym

@[simp]
theorem unsym_sym (a : α) : unsym (sym a) = a :=
  rfl
#align sym_alg.unsym_sym SymAlg.unsym_sym

@[simp]
theorem sym_unsym (a : α) : sym (unsym a) = a :=
  rfl
#align sym_alg.sym_unsym SymAlg.sym_unsym

@[simp]
theorem sym_comp_unsym : (sym : α → αˢʸᵐ) ∘ unsym = id :=
  rfl
#align sym_alg.sym_comp_unsym SymAlg.sym_comp_unsym

@[simp]
theorem unsym_comp_sym : (unsym : αˢʸᵐ → α) ∘ sym = id :=
  rfl
#align sym_alg.unsym_comp_sym SymAlg.unsym_comp_sym

@[simp]
theorem sym_symm : (@sym α).symm = unsym :=
  rfl
#align sym_alg.sym_symm SymAlg.sym_symm

@[simp]
theorem unsym_symm : (@unsym α).symm = sym :=
  rfl
#align sym_alg.unsym_symm SymAlg.unsym_symm

theorem sym_bijective : Bijective (sym : α → αˢʸᵐ) :=
  sym.bijective
#align sym_alg.sym_bijective SymAlg.sym_bijective

theorem unsym_bijective : Bijective (unsym : αˢʸᵐ → α) :=
  unsym.symm.bijective
#align sym_alg.unsym_bijective SymAlg.unsym_bijective

theorem sym_injective : Injective (sym : α → αˢʸᵐ) :=
  sym.injective
#align sym_alg.sym_injective SymAlg.sym_injective

theorem sym_surjective : Surjective (sym : α → αˢʸᵐ) :=
  sym.surjective
#align sym_alg.sym_surjective SymAlg.sym_surjective

theorem unsym_injective : Injective (unsym : αˢʸᵐ → α) :=
  unsym.injective
#align sym_alg.unsym_injective SymAlg.unsym_injective

theorem unsym_surjective : Surjective (unsym : αˢʸᵐ → α) :=
  unsym.surjective
#align sym_alg.unsym_surjective SymAlg.unsym_surjective

-- Porting note: @[simp] can prove this
theorem sym_inj {a b : α} : sym a = sym b ↔ a = b :=
  sym_injective.eq_iff
#align sym_alg.sym_inj SymAlg.sym_inj

-- Porting note: @[simp] can prove this
theorem unsym_inj {a b : αˢʸᵐ} : unsym a = unsym b ↔ a = b :=
  unsym_injective.eq_iff
#align sym_alg.unsym_inj SymAlg.unsym_inj

instance [Nontrivial α] : Nontrivial αˢʸᵐ :=
  sym_injective.nontrivial

instance [Inhabited α] : Inhabited αˢʸᵐ :=
  ⟨sym default⟩

instance [Subsingleton α] : Subsingleton αˢʸᵐ :=
  unsym_injective.subsingleton

instance [Unique α] : Unique αˢʸᵐ :=
  Unique.mk' _

instance [IsEmpty α] : IsEmpty αˢʸᵐ :=
  Function.isEmpty unsym

@[to_additive]
instance [One α] : One αˢʸᵐ where one := sym 1

instance [Add α] : Add αˢʸᵐ where add a b := sym (unsym a + unsym b)

instance [Sub α] : Sub αˢʸᵐ where sub a b := sym (unsym a - unsym b)

instance [Neg α] : Neg αˢʸᵐ where neg a := sym (-unsym a)

-- Introduce the symmetrized multiplication
instance [Add α] [Mul α] [One α] [OfNat α 2] [Invertible (2 : α)] : Mul αˢʸᵐ where
  mul a b := sym (⅟ 2 * (unsym a * unsym b + unsym b * unsym a))

@[to_additive existing]
instance [Inv α] : Inv αˢʸᵐ where inv a := sym <| (unsym a)⁻¹

instance (R : Type*) [SMul R α] : SMul R αˢʸᵐ where smul r a := sym (r • unsym a)

@[to_additive (attr := simp)]
theorem sym_one [One α] : sym (1 : α) = 1 :=
  rfl
#align sym_alg.sym_one SymAlg.sym_one
#align sym_alg.sym_zero SymAlg.sym_zero

@[to_additive (attr := simp)]
theorem unsym_one [One α] : unsym (1 : αˢʸᵐ) = 1 :=
  rfl
#align sym_alg.unsym_one SymAlg.unsym_one
#align sym_alg.unsym_zero SymAlg.unsym_zero

@[simp]
theorem sym_add [Add α] (a b : α) : sym (a + b) = sym a + sym b :=
  rfl
#align sym_alg.sym_add SymAlg.sym_add

@[simp]
theorem unsym_add [Add α] (a b : αˢʸᵐ) : unsym (a + b) = unsym a + unsym b :=
  rfl
#align sym_alg.unsym_add SymAlg.unsym_add

@[simp]
theorem sym_sub [Sub α] (a b : α) : sym (a - b) = sym a - sym b :=
  rfl
#align sym_alg.sym_sub SymAlg.sym_sub

@[simp]
theorem unsym_sub [Sub α] (a b : αˢʸᵐ) : unsym (a - b) = unsym a - unsym b :=
  rfl
#align sym_alg.unsym_sub SymAlg.unsym_sub

@[simp]
theorem sym_neg [Neg α] (a : α) : sym (-a) = -sym a :=
  rfl
#align sym_alg.sym_neg SymAlg.sym_neg

@[simp]
theorem unsym_neg [Neg α] (a : αˢʸᵐ) : unsym (-a) = -unsym a :=
  rfl
#align sym_alg.unsym_neg SymAlg.unsym_neg

theorem mul_def [Add α] [Mul α] [One α] [OfNat α 2] [Invertible (2 : α)] (a b : αˢʸᵐ) :
    a * b = sym (⅟ 2 * (unsym a * unsym b + unsym b * unsym a)) := by rfl
                                                                      -- 🎉 no goals
#align sym_alg.mul_def SymAlg.mul_def

theorem unsym_mul [Mul α] [Add α] [One α] [OfNat α 2] [Invertible (2 : α)] (a b : αˢʸᵐ) :
    unsym (a * b) = ⅟ 2 * (unsym a * unsym b + unsym b * unsym a) := by rfl
                                                                        -- 🎉 no goals
#align sym_alg.unsym_mul SymAlg.unsym_mul

theorem sym_mul_sym [Mul α] [Add α] [One α] [OfNat α 2] [Invertible (2 : α)] (a b : α) :
    sym a * sym b = sym (⅟ 2 * (a * b + b * a)) :=
  rfl
#align sym_alg.sym_mul_sym SymAlg.sym_mul_sym

set_option linter.existingAttributeWarning false in
@[simp, to_additive existing]
theorem sym_inv [Inv α] (a : α) : sym a⁻¹ = (sym a)⁻¹ :=
  rfl
#align sym_alg.sym_inv SymAlg.sym_inv

set_option linter.existingAttributeWarning false in
@[simp, to_additive existing]
theorem unsym_inv [Inv α] (a : αˢʸᵐ) : unsym a⁻¹ = (unsym a)⁻¹ :=
  rfl
#align sym_alg.unsym_inv SymAlg.unsym_inv

@[simp]
theorem sym_smul {R : Type*} [SMul R α] (c : R) (a : α) : sym (c • a) = c • sym a :=
  rfl
#align sym_alg.sym_smul SymAlg.sym_smul

@[simp]
theorem unsym_smul {R : Type*} [SMul R α] (c : R) (a : αˢʸᵐ) : unsym (c • a) = c • unsym a :=
  rfl
#align sym_alg.unsym_smul SymAlg.unsym_smul

@[to_additive (attr := simp)]
theorem unsym_eq_one_iff [One α] (a : αˢʸᵐ) : unsym a = 1 ↔ a = 1 :=
  unsym_injective.eq_iff' rfl
#align sym_alg.unsym_eq_one_iff SymAlg.unsym_eq_one_iff
#align sym_alg.unsym_eq_zero_iff SymAlg.unsym_eq_zero_iff

@[to_additive (attr := simp)]
theorem sym_eq_one_iff [One α] (a : α) : sym a = 1 ↔ a = 1 :=
  sym_injective.eq_iff' rfl
#align sym_alg.sym_eq_one_iff SymAlg.sym_eq_one_iff
#align sym_alg.sym_eq_zero_iff SymAlg.sym_eq_zero_iff

@[to_additive]
theorem unsym_ne_one_iff [One α] (a : αˢʸᵐ) : unsym a ≠ (1 : α) ↔ a ≠ (1 : αˢʸᵐ) :=
  not_congr <| unsym_eq_one_iff a
#align sym_alg.unsym_ne_one_iff SymAlg.unsym_ne_one_iff
#align sym_alg.unsym_ne_zero_iff SymAlg.unsym_ne_zero_iff

@[to_additive]
theorem sym_ne_one_iff [One α] (a : α) : sym a ≠ (1 : αˢʸᵐ) ↔ a ≠ (1 : α) :=
  not_congr <| sym_eq_one_iff a
#align sym_alg.sym_ne_one_iff SymAlg.sym_ne_one_iff
#align sym_alg.sym_ne_zero_iff SymAlg.sym_ne_zero_iff

instance addCommSemigroup [AddCommSemigroup α] : AddCommSemigroup αˢʸᵐ :=
  unsym_injective.addCommSemigroup _ unsym_add

instance addMonoid [AddMonoid α] : AddMonoid αˢʸᵐ :=
  unsym_injective.addMonoid _ unsym_zero unsym_add fun _ _ => rfl

instance addGroup [AddGroup α] : AddGroup αˢʸᵐ :=
  unsym_injective.addGroup _ unsym_zero unsym_add unsym_neg unsym_sub (fun _ _ => rfl) fun _ _ =>
    rfl

instance addCommMonoid [AddCommMonoid α] : AddCommMonoid αˢʸᵐ :=
  { SymAlg.addCommSemigroup, SymAlg.addMonoid with }

instance addCommGroup [AddCommGroup α] : AddCommGroup αˢʸᵐ :=
  { SymAlg.addCommMonoid, SymAlg.addGroup with }

instance {R : Type*} [Semiring R] [AddCommMonoid α] [Module R α] : Module R αˢʸᵐ :=
  Function.Injective.module R ⟨⟨unsym, unsym_zero⟩, unsym_add⟩ unsym_injective unsym_smul

instance [Mul α] [AddMonoidWithOne α] [Invertible (2 : α)] (a : α) [Invertible a] :
    Invertible (sym a) where
  invOf := sym (⅟ a)
  invOf_mul_self := by
    rw [sym_mul_sym, mul_invOf_self, invOf_mul_self, one_add_one_eq_two, invOf_mul_self, sym_one]
    -- 🎉 no goals
  mul_invOf_self := by
    rw [sym_mul_sym, mul_invOf_self, invOf_mul_self, one_add_one_eq_two, invOf_mul_self, sym_one]
    -- 🎉 no goals

@[simp]
theorem invOf_sym [Mul α] [AddMonoidWithOne α] [Invertible (2 : α)] (a : α) [Invertible a] :
    ⅟ (sym a) = sym (⅟ a) :=
  rfl
#align sym_alg.inv_of_sym SymAlg.invOf_sym

instance nonAssocSemiring [Semiring α] [Invertible (2 : α)] : NonAssocSemiring αˢʸᵐ :=
  { SymAlg.addCommMonoid with
    one := 1
    mul := (· * ·)
    zero := 0
    zero_mul := fun _ => by
      rw [mul_def, unsym_zero, zero_mul, mul_zero, add_zero,
        mul_zero, sym_zero]
    mul_zero := fun _ => by
      rw [mul_def, unsym_zero, zero_mul, mul_zero, add_zero,
        mul_zero, sym_zero]
    mul_one := fun _ => by
      rw [mul_def, unsym_one, mul_one, one_mul, ← two_mul, invOf_mul_self_assoc, sym_unsym]
      -- 🎉 no goals
    one_mul := fun _ => by
      -- 🎉 no goals
      rw [mul_def, unsym_one, mul_one, one_mul, ← two_mul, invOf_mul_self_assoc, sym_unsym]
    left_distrib := fun a b c => by
      -- ⊢ ↑sym (⅟2 * (↑unsym a * (↑unsym b + ↑unsym c) + (↑unsym b * ↑unsym a + ↑unsym …
      -- Porting note: rewrote previous proof which used `match` in a way that seems unsupported.
      -- ⊢ ↑unsym a * (↑unsym b + ↑unsym c) + (↑unsym b * ↑unsym a + ↑unsym c * ↑unsym  …
      rw [mul_def, mul_def, mul_def, ← sym_add, ← mul_add, unsym_add, add_mul]
      -- ⊢ ↑unsym a * ↑unsym b + ↑unsym a * ↑unsym c + (↑unsym b * ↑unsym a + ↑unsym c  …
      congr 2
      -- 🎉 no goals
      -- 🎉 no goals
      rw [mul_add]
      abel
    right_distrib := fun a b c => by
      -- ⊢ ↑sym (⅟2 * (↑unsym a * ↑unsym c + ↑unsym b * ↑unsym c + ↑unsym c * (↑unsym a …
      -- Porting note: rewrote previous proof which used `match` in a way that seems unsupported.
      -- ⊢ ↑unsym a * ↑unsym c + ↑unsym b * ↑unsym c + ↑unsym c * (↑unsym a + ↑unsym b) …
      rw [mul_def, mul_def, mul_def, ← sym_add, ← mul_add, unsym_add, add_mul]
      -- ⊢ ↑unsym a * ↑unsym c + ↑unsym b * ↑unsym c + (↑unsym c * ↑unsym a + ↑unsym c  …
      congr 2
      -- 🎉 no goals
      -- 🎉 no goals
      rw [mul_add]
      abel }

/-- The symmetrization of a real (unital, associative) algebra is a non-associative ring. -/
instance [Ring α] [Invertible (2 : α)] : NonAssocRing αˢʸᵐ :=
  { SymAlg.nonAssocSemiring, SymAlg.addCommGroup with }

/-! The squaring operation coincides for both multiplications -/


theorem unsym_mul_self [Semiring α] [Invertible (2 : α)] (a : αˢʸᵐ) :
    unsym (a * a) = unsym a * unsym a := by rw [mul_def, unsym_sym, ← two_mul, invOf_mul_self_assoc]
                                            -- 🎉 no goals
#align sym_alg.unsym_mul_self SymAlg.unsym_mul_self

theorem sym_mul_self [Semiring α] [Invertible (2 : α)] (a : α) : sym (a * a) = sym a * sym a := by
  rw [sym_mul_sym, ← two_mul, invOf_mul_self_assoc]
  -- 🎉 no goals
#align sym_alg.sym_mul_self SymAlg.sym_mul_self

theorem mul_comm [Mul α] [AddCommSemigroup α] [One α] [OfNat α 2] [Invertible (2 : α)]
    (a b : αˢʸᵐ) :
    a * b = b * a := by rw [mul_def, mul_def, add_comm]
                        -- 🎉 no goals
#align sym_alg.mul_comm SymAlg.mul_comm

instance [Ring α] [Invertible (2 : α)] : IsCommJordan αˢʸᵐ where
  mul_comm := SymAlg.mul_comm
  lmul_comm_rmul_rmul a b := by
    have commute_half_left := fun a : α => by
      -- Porting note: mathlib3 used `bit0_left`
      have := (Commute.one_left a).add_left (Commute.one_left a)
      rw [one_add_one_eq_two] at this
      exact this.invOf_left.eq

    -- Porting note: introduced `calc` block to make more robust
    calc a * b * (a * a)
      _ = sym (⅟2 * ⅟2 * (unsym a * unsym b * unsym (a * a) +
          unsym b * unsym a * unsym (a * a) +
          unsym (a * a) * unsym a * unsym b +
          unsym (a * a) * unsym b * unsym a)) := ?_
      _ = sym (⅟ 2 * (unsym a *
          unsym (sym (⅟ 2 * (unsym b * unsym (a * a) + unsym (a * a) * unsym b))) +
          unsym (sym (⅟ 2 * (unsym b * unsym (a * a) + unsym (a * a) * unsym b))) * unsym a)) := ?_
      _ = a * (b * (a * a)) := ?_

    -- Rearrange LHS
    · rw [mul_def, mul_def a b, unsym_sym, ← mul_assoc, ← commute_half_left (unsym (a * a)),
        mul_assoc, mul_assoc, ← mul_add, ← mul_assoc, add_mul, mul_add (unsym (a * a)),
        ← add_assoc, ← mul_assoc, ← mul_assoc]

    · rw [unsym_sym, sym_inj, ← mul_assoc, ← commute_half_left (unsym a), mul_assoc (⅟ 2) (unsym a),
        mul_assoc (⅟ 2) _ (unsym a), ← mul_add, ← mul_assoc]
      conv_rhs => rw [mul_add (unsym a)]
      -- ⊢ ⅟2 * ⅟2 * (↑unsym a * ↑unsym b * ↑unsym (a * a) + ↑unsym b * ↑unsym a * ↑uns …
      rw [add_mul, ← add_assoc, ← mul_assoc, ← mul_assoc]
      -- ⊢ ⅟2 * ⅟2 * (↑unsym a * ↑unsym b * ↑unsym (a * a) + ↑unsym b * ↑unsym a * ↑uns …
      rw [unsym_mul_self]
      -- ⊢ ⅟2 * ⅟2 * (↑unsym a * ↑unsym b * (↑unsym a * ↑unsym a) + ↑unsym b * ↑unsym a …
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← sub_eq_zero, ← mul_sub]
      -- ⊢ ⅟2 * ⅟2 * (↑unsym a * ↑unsym b * ↑unsym a * ↑unsym a + ↑unsym b * ↑unsym a * …
      convert mul_zero (⅟ (2 : α) * ⅟ (2 : α))
      -- ⊢ ↑unsym a * ↑unsym b * ↑unsym a * ↑unsym a + ↑unsym b * ↑unsym a * ↑unsym a * …
      rw [add_sub_add_right_eq_sub, add_assoc, add_assoc, add_sub_add_left_eq_sub, add_comm,
        add_sub_add_right_eq_sub, sub_eq_zero]

    -- Rearrange RHS
    · rw [← mul_def, ← mul_def]
      -- 🎉 no goals

end SymAlg
