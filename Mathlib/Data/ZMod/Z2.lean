import Mathlib.Algebra.Hom.Equiv.Basic
import Mathlib.Data.Fintype.Basic

@[derive decidable_eq, to_additive]
inductive mul_z2 : Type
| one : mul_z2
| a : mul_z2

namespace mul_z2

instance : fintype mul_z2 := ⟨{one, a}, λ x, by cases x; simp⟩

@[simp] lemma card_eq : fintype.card mul_z2 = 2 := rfl

def elim {α : Sort*} (x y : α) : mul_z2 → α := λ z, mul_z2.rec_on z x y

protected def mul : mul_z2 → mul_z2 → mul_z2
| one x := x
| a one := a
| a a := one

instance : comm_group mul_z2 :=
{ mul := mul_z2.mul,
  mul_assoc := dec_trivial,
  mul_comm := dec_trivial,
  one := one,
  one_mul := λ x, rfl,
  mul_one := dec_trivial,
  inv := λ x, x,
  div := mul_z2.mul,
  div_eq_mul_inv := λ x y, rfl,
  mul_left_inv := dec_trivial }

@[simp] protected lemma «forall» {p : mul_z2 → Prop} : (∀ x, p x) ↔ p 1 ∧ p a :=
⟨λ h, ⟨h 1, h a⟩, λ h x, mul_z2.rec_on x h.1 h.2⟩

@[simp] protected lemma «exists» {p : mul_z2 → Prop} : (∃ x, p x) ↔ p 1 ∨ p a :=
⟨λ ⟨x, hx⟩, mul_z2.rec_on x or.inl or.inr hx, λ h, h.elim (λ h, ⟨_, h⟩) (λ h, ⟨_, h⟩)⟩

@[simp] lemma mul_self : ∀ x : mul_z2, x * x = 1 := dec_trivial

@[simp] lemma elim_one {α} (x y : α) : elim x y 1 = x := rfl
@[simp] lemma elim_a {α} (x y : α) : elim x y a = y := rfl

lemma a_ne_one : a ≠ 1.
lemma one_ne_a : 1 ≠ a.
lemma ne_one_iff : ∀ {x}, x ≠ 1 ↔ x = a := dec_trivial
lemma one_ne_iff : ∀ {x}, 1 ≠ x ↔ x = a := dec_trivial

lemma hom_ext {M F : Type*} [has_one M] [one_hom_class F mul_z2 M] {f g : F} (h : f a = g a) :
  f = g :=
fun_like.ext _ _ $ by simp [h]

def lift {M : Type*} [mul_one_class M] : {x : M // x * x = 1} ≃ (mul_z2 →* M) :=
{ to_fun := λ x, ⟨elim 1 x, rfl, by simpa using x.2.symm⟩,
  inv_fun := λ f, ⟨f a, by rw [← map_mul, mul_self, map_one]⟩,
  left_inv := λ x, subtype.ext rfl,
  right_inv := λ f, hom_ext rfl }

end mul_z2
