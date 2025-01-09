import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.LinearAlgebra.LinearPMap.Basic

class PFunLike (F : Type*) (α : outParam Type*) (γ : outParam Type*) (β : outParam Type*)
  [SetLike γ α] where
domain : F → γ
coe : Π (f : F), (domain f) → β
coe_injective : Π (f g : F), domain f = domain g →
  (∀ (x : domain f) (y : domain g), (x : α) = (y : α) → coe f x = coe g y) → f = g

attribute [coe] PFunLike.coe

namespace PFunLike

instance {F α γ β : Type*} [SetLike γ α] [PFunLike F α γ β] :
  CoeFun F (fun f ↦ domain f → β) := ⟨coe⟩

lemma ext {F α β γ : Type*} [SetLike γ α] [PFunLike F α γ β] {f g : F} (h : domain f = domain g)
    (h' : ∀ ⦃x : domain f⦄ ⦃y : domain g⦄, (x : α) = y → f x = g y) : f = g :=
  coe_injective f g h h'

end PFunLike

class PMapZeroClass (F : Type*) (M γ N : outParam Type*) [SetLike γ M] [Zero M] [Zero N]
    [ZeroMemClass γ M] extends PFunLike F M γ N where
  pmap_zero : ∀ (f : F), f 0 = 0

class PMapAddClass (F : Type*) (α γ β : outParam Type*)
    [SetLike γ α] [Add α] [Add β] [AddMemClass γ α]
    extends PFunLike F α γ β where
  pmap_add : ∀ (f : F) (x y : domain f), f (x + y) = f x + f y

class PMapAddZeroClass (F : Type*) (M γ N : outParam Type*) [SetLike γ M]
    [AddZeroClass M] [AddZeroClass N] [AddMemClass γ M] [ZeroMemClass γ M]
    extends PMapAddClass F M γ N, PMapZeroClass F M γ N

theorem pmap_neg (G H F γ : Type*) [AddGroup G] [SubtractionMonoid H] [SetLike γ G]
    [AddSubgroupClass γ G] []

class PMapSMulClass (F : Type*) (M X γ : outParam Type*) [SetLike γ X] [SMul M X]
    (Y : outParam Type*) [SMul M Y] [SMulMemClass γ M X] extends PFunLike F X γ Y where
  pmap_smul : ∀ (f : F) (x : domain f) (c : M), f (c • x) = c • (f x)

class LinearPMapClass (F : Type*) (δ α γ β : outParam Type*) [Semiring δ] [AddCommMonoid α]
    [AddCommMonoid β] [Module δ α] [Module δ β]
    [SetLike γ α] [SMulMemClass γ δ α] [AddMemClass γ α]
    extends PMapSMulClass F δ α γ β, PMapAddClass F α γ β

instance (priority := 900) SMulMemClass.SMulWithZero (R M α : Type*) [Zero R] [Zero M]
    [SMulWithZero R M] [SetLike α M] [SMulMemClass α R M] [ZeroMemClass α M] (a : α) :
    SMulWithZero R a where
  smul_zero r := by ext1; simp
  zero_smul m := by ext1; simp

instance (priority := 100) LinearPMapClass.toPMapAddZeroClass (F δ α γ β : Type*)
    [Semiring δ] [AddCommMonoid α] [AddCommMonoid β] [Module δ α] [Module δ β]
    [SetLike γ α] [SMulMemClass γ δ α] [AddMemClass γ α] [ZeroMemClass γ α]
    [LinearPMapClass F δ α γ β] :
    PMapAddZeroClass F α γ β where
  pmap_zero f := by
    rw [← zero_smul δ 0, PMapSMulClass.pmap_smul, zero_smul]

/-

theorem pmap_zero {F δ α γ β : Type*} [Zero α] [Zero β] [Zero δ] [SMulWithZero δ α]
    [SetLike γ α] [Add α] [SMul δ α] [SMulMemClass γ δ α] [AddMemClass γ α] [Add β] [SMul δ β]
    [LinearPMapClass F δ α γ β] (f : F) [ZeroMemClass γ α] : f 0 = 0 := by
  rw [← zero_smul δ (0 : PFunLike.domain f)]

variable {R E F : Type*} [Ring R] [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F]

instance : LinearPMapClass (E →ₗ.[R] F) R E (Submodule R E) F where
  domain f := f.domain
  coe f := f.toFun
  coe_injective _ _ hd h := LinearPMap.ext hd h
  pmap_smul f x c := f.toFun.map_smul c x
  pmap_add f x y := f.toFun.map_add x y

lemma test (f : E →ₗ.[R] F) (x y : f.domain) : f (x + y) = f x + f y :=
  LinearPMapClass.pmap_add f x y

export pmul_hom_class (pmap_mul)

structure pmul_hom (α β : Type*) [has_mul α] [has_mul β] :=
(domain : subsemigroup α)
(to_mul_hom : domain →ₙ* β)

infixr ` →.ₙ* `:25 := pmul_hom

namespace pmul_hom

instance (α β : Type*) [has_mul α] [has_mul β] :
  pmul_hom_class (pmul_hom α β) α (subsemigroup α) β :=
{ domain := pmul_hom.domain,
  coe := λ f, f.to_mul_hom,
  coe_injective := λ f g h h',
  begin
    rcases f with ⟨f_dom, f⟩,
    rcases g with ⟨g_dom, g⟩,
    obtain rfl : f_dom = g_dom := h,
    obtain rfl : f = g := mul_hom.ext (λ x, h' _ _ rfl),
    refl,
  end,
  pmap_mul := λ f, map_mul f.to_mul_hom }

-- this would be our standard `ext` lemma
@[ext]
lemma ext {α β : Type*} [has_mul α] [has_mul β] {f g : α →.ₙ* β} (h : domain f = domain g)
  (h' : ∀ ⦃x : domain f⦄ ⦃y : domain g⦄, (x : α) = (y : α) → f x = g y) : f = g :=
PFunLike.coe_injective f g h h'

-- see? it works!
example {α β : Type*} [has_mul α] [has_mul β] (f : α →.ₙ* β) (x y : domain f) :
  f (x * y) = f x * f y :=
pmap_mul f x y

-- this instance seems dangerous: all of a sudden `α →ₙ* β` would have *two* `has_coe_to_fun`
-- instances, one coercing to `α → β` from the `fun_like` instance and another coercing to
-- `λ f, domain f → β` from the `PFunLike` instance, but maybe this isn't so much of a problem.
-- even if it is a problem, perhaps we can just solve it by lowering the priority on this one?
instance dangerous {α β : Type*} [has_mul α] [has_mul β] :
  pmul_hom_class (mul_hom α β) α (subsemigroup α) β  :=
{ domain := λ f, ⊤,
  coe := λ f x, match x with ⟨x, _⟩ := f x end,
  coe_injective := λ f g _ h, mul_hom.ext (λ x, h ⟨x, true.intro⟩ ⟨x, true.intro⟩ rfl),
  pmap_mul := λ f,
  begin
    simp_rw [SetLike.forall],
    rintros x _ y _,
    exact map_mul f x y,
  end }

end pmul_hom
-/
