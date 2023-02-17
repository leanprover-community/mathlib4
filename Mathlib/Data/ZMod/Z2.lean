import Mathlib.Algebra.Hom.Equiv.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

inductive AddZ2 : Type
| zero : AddZ2
| a : AddZ2
deriving DecidableEq

@[to_additive]
inductive MulZ2 : Type
| one : MulZ2
| a : MulZ2
deriving DecidableEq

namespace MulZ2

-- should not be necessary, if to_additive knew a↦a
attribute [to_additive?] instDecidableEqMulZ2 a

@[to_additive]
instance : Fintype MulZ2 := ⟨{one, a}, fun x ↦ by cases x <;> simp⟩

@[to_additive (attr := simp)] lemma card_eq : Fintype.card MulZ2 = 2 := rfl

@[to_additive] def elim {α : Sort _} (x y : α) : MulZ2 → α
| one => x
| a => y

@[to_additive] protected def mul : MulZ2 → MulZ2 → MulZ2
| one, x => x
| a, one => a
| a, a => one

@[to_additive] instance : CommGroup MulZ2 :=
{ mul := MulZ2.mul,
  mul_assoc := by decide,
  mul_comm := by decide,
  one := one,
  one_mul := fun x ↦ rfl,
  mul_one := by decide,
  inv := fun x ↦ x,
  div := MulZ2.mul,
  div_eq_mul_inv := fun x y ↦ rfl,
  mul_left_inv := by decide }

@[to_additive (attr := simp)] lemma one_eq_1 : one = 1 := rfl

@[to_additive (attr := simp)] protected lemma «forall» {p : MulZ2 → Prop} : (∀ x, p x) ↔ p one ∧ p a :=
⟨fun h ↦ ⟨h one, h a⟩, fun h x ↦ MulZ2.recOn x h.1 h.2⟩

@[to_additive (attr := simp)] protected lemma «exists» {p : MulZ2 → Prop} : (∃ x, p x) ↔ p one ∨ p a :=
⟨fun ⟨x, hx⟩ ↦ MulZ2.recOn x Or.inl Or.inr hx, fun h ↦ h.elim (fun h ↦ ⟨_, h⟩) (fun h ↦ ⟨_, h⟩)⟩

@[to_additive (attr := simp)] lemma mul_self : ∀ x : MulZ2, x * x = 1 := by decide

@[to_additive (attr := simp)] lemma elim_one {α} (x y : α) : elim x y 1 = x := rfl
@[to_additive (attr := simp)] lemma elim_a {α} (x y : α) : elim x y a = y := rfl

lemma a_ne_one : a ≠ 1 := by decide
lemma one_ne_a : 1 ≠ a := by decide
lemma ne_one_iff : ∀ {x}, x ≠ 1 ↔ x = a := by decide
lemma one_ne_iff : ∀ {x}, 1 ≠ x ↔ x = a := by decide

lemma hom_ext {M F : Type _} [One M] [OneHomClass F MulZ2 M] {f g : F} (h : f a = g a) :
  f = g := FunLike.ext _ _ $ by simp [h]

def lift {M : Type _} [MulOneClass M] : {x : M // x * x = 1} ≃ (MulZ2 →* M) :=
{ toFun := fun x ↦ ⟨⟨elim 1 x.1, rfl⟩, by simpa using x.2.symm⟩,
  invFun := fun f ↦ ⟨f a, by rw [← map_mul, mul_self, map_one]⟩,
  left_inv := fun x ↦ Subtype.ext rfl,
  right_inv := fun f ↦ hom_ext rfl }

end MulZ2
