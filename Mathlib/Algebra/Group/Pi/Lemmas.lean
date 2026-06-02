/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Data.Set.Piecewise
public import Mathlib.Logic.Pairwise

/-!
# Extra lemmas about products of monoids and groups

This file proves lemmas about the instances defined in `Algebra.Group.Pi.Basic` that require more
imports.
-/

@[expose] public section

assert_not_exists AddMonoidWithOne MonoidWithZero

universe u v w

variable {ι α : Type*}
variable {I : Type u}
variable {f : I → Type v} {M N : ι → Type*}

variable (i : I)

@[to_additive (attr := simp)]
theorem Set.range_one {α β : Type*} [One β] [Nonempty α] : Set.range (1 : α → β) = {1} :=
  range_const

@[to_additive]
theorem Set.preimage_one {α β : Type*} [One β] (s : Set β) [Decidable ((1 : β) ∈ s)] :
    (1 : α → β) ⁻¹' s = if (1 : β) ∈ s then Set.univ else ∅ :=
  Set.preimage_const 1 s

namespace Pi

@[to_additive]
instance instIsMulTorsionFree [∀ i, Monoid (M i)] [∀ i, IsMulTorsionFree (M i)] :
    IsMulTorsionFree (∀ i, M i) where
  pow_left_injective n hn a b hab := by ext i; exact pow_left_injective hn <| congr_fun hab i

variable {α β : Type*} [Preorder α] [Preorder β]

@[to_additive] lemma one_mono [One β] : Monotone (1 : α → β) := monotone_const
@[to_additive] lemma one_anti [One β] : Antitone (1 : α → β) := antitone_const

end Pi

namespace MulHom

@[to_additive]
theorem coe_mul {M N} {_ : Mul M} {_ : CommSemigroup N} (f g : M →ₙ* N) : (f * g : M → N) =
    fun x => f x * g x := rfl

end MulHom

section MulHom

variable [(i : I) → Mul (f i)]

/-- A family of MulHom's `f a : γ →ₙ* β a` defines a MulHom `MulHom.pi f : γ →ₙ* Π a, β a`
given by `MulHom.pi f x b = f b x`. -/
@[to_additive (attr := simps)
  /-- A family of AddHom's `f a : γ → β a` defines an AddHom `AddHom.pi f : γ → Π a, β a` given by
  `AddHom.pi f x b = f b x`. -/]
def MulHom.pi {γ : Type w} [Mul γ] (g : ∀ i, γ →ₙ* f i) : γ →ₙ* ∀ i, f i where
  toFun x i := g i x
  map_mul' x y := funext fun i => (g i).map_mul x y

@[deprecated (since := "2026-05-29")] alias Pi.addHom := AddHom.pi
@[to_additive existing (attr := deprecated MulHom.pi (since := "2026-05-29"))] alias
  Pi.mulHom := MulHom.pi

@[deprecated (since := "2026-05-29")] alias Pi.addHom_apply := AddHom.pi_apply
@[to_additive existing (attr := deprecated MulHom.pi_apply (since := "2026-05-29"))] alias
  Pi.mulHom_apply := MulHom.pi_apply

@[to_additive]
theorem MulHom.pi_injective {γ : Type w} [Nonempty I] [Mul γ] (g : ∀ i, γ →ₙ* f i)
    (hg : ∀ i, Function.Injective (g i)) : Function.Injective (MulHom.pi g) := fun _ _ h =>
  let ⟨i⟩ := ‹Nonempty I›
  hg i ((funext_iff.mp h :) i)

@[deprecated (since := "2026-05-29")] alias AddHom.injective_pi := AddHom.pi_injective
@[to_additive existing (attr := deprecated MulHom.pi_injective (since := "2026-05-29"))] alias
  MulHom.injective_pi := MulHom.pi_injective

@[deprecated (since := "2026-05-29")] alias Pi.addHom_injective := AddHom.injective_pi
@[to_additive existing (attr := deprecated MulHom.pi_injective (since := "2026-05-29"))] alias
  Pi.mulHom_injective := MulHom.pi_injective

variable (f)

/-- Evaluation of functions into an indexed collection of semigroups at a point is a semigroup
homomorphism.
This is `Function.eval i` as a `MulHom`. -/
@[to_additive (attr := simps)
  /-- Evaluation of functions into an indexed collection of additive semigroups at a point is an
  additive semigroup homomorphism. This is `Function.eval i` as an `AddHom`. -/]
def Pi.evalMulHom (i : I) : (∀ i, f i) →ₙ* f i where
  toFun g := g i
  map_mul' _ _ := Pi.mul_apply _ _ i

/-- A family of MulHom's `f i : M i →ₙ* N i` defines a MulHom
`MulHom.piMap f : (Π i, M i) →ₙ* (Π i, N i)`
given by `MulHom.piMap f x i = f i x`. This is `Pi.map` for `MulHom`s. -/
@[to_additive (attr := simps!)
  /-- A family of AddHom's `f i : M i →ₙ+ N i` defines an AddHom
  `AddHom.piMap f : (Π i, M i) →ₙ+ (Π i, N i)`
  given by `AddHom.piMap f x i = f i x`. This is `Pi.map` for `AddHom`s. -/]
def MulHom.piMap [∀ i, Mul (M i)] [∀ i, Mul (N i)] (g : ∀ i, M i →ₙ* N i) :
    (∀ i, M i) →ₙ* (∀ i, N i) :=
  .pi fun i ↦ (g i).comp (Pi.evalMulHom M i)

/-- `Function.const` as a `MulHom`. -/
@[to_additive (attr := simps) /-- `Function.const` as an `AddHom`. -/]
def Pi.constMulHom (α β : Type*) [Mul β] :
    β →ₙ* α → β where
  toFun := Function.const α
  map_mul' _ _ := rfl

/-- Coercion of a `MulHom` into a function is itself a `MulHom`.

See also `MulHom.eval`. -/
@[to_additive (attr := simps) /-- Coercion of an `AddHom` into a function is itself an `AddHom`.

See also `AddHom.eval`. -/]
def MulHom.coeFn (α β : Type*) [Mul α] [CommSemigroup β] :
    (α →ₙ* β) →ₙ* α → β where
  toFun g := g
  map_mul' _ _ := rfl

/-- Semigroup homomorphism between the function spaces `I → α` and `I → β`, induced by a semigroup
homomorphism `f` between `α` and `β`. -/
@[to_additive (attr := simps) /-- Additive semigroup homomorphism between the function spaces
  `I → α` and `I → β`, induced by an additive semigroup homomorphism `f` between `α` and `β` -/]
protected def MulHom.compLeft {α β : Type*} [Mul α] [Mul β] (f : α →ₙ* β) (I : Type*) :
    (I → α) →ₙ* I → β where
  toFun h := f ∘ h
  map_mul' _ _ := by ext; simp

end MulHom

section MonoidHom

variable [(i : I) → MulOneClass (f i)]

/-- A family of monoid homomorphisms `f a : γ →* β a` defines a monoid homomorphism
`Pi.monoidHom f : γ →* Π a, β a` given by `Pi.monoidHom f x b = f b x`. -/
@[to_additive (attr := simps)
  /-- A family of additive monoid homomorphisms `f a : γ →+ β a` defines a monoid homomorphism
  `Pi.addMonoidHom f : γ →+ Π a, β a` given by `Pi.addMonoidHom f x b = f b x`. -/]
def MonoidHom.pi {γ : Type w} [MulOneClass γ] (g : ∀ i, γ →* f i) :
    γ →* ∀ i, f i :=
  { MulHom.pi fun i => (g i).toMulHom with
    toFun := fun x i => g i x
    map_one' := funext fun i => (g i).map_one }

@[deprecated (since := "2026-05-29")] alias Pi.addMonoidHom := AddMonoidHom.pi
@[to_additive existing (attr := deprecated MonoidHom.pi (since := "2026-05-29"))] alias
  Pi.monoidHom := MonoidHom.pi

@[deprecated (since := "2026-05-29")] alias Pi.addMonoidHom_apply := AddMonoidHom.pi_apply
@[to_additive existing (attr := deprecated MonoidHom.pi_apply (since := "2026-05-29"))] alias
  Pi.monoidHom_apply := MonoidHom.pi_apply

@[to_additive]
theorem MonoidHom.pi_injective {γ : Type w} [Nonempty I] [MulOneClass γ]
    (g : ∀ i, γ →* f i) (hg : ∀ i, Function.Injective (g i)) :
    Function.Injective (MonoidHom.pi g) :=
  MulHom.pi_injective (fun i => (g i).toMulHom) hg

@[deprecated (since := "2026-05-29")] alias AddMonoidHom.injective_pi := AddMonoidHom.pi_injective
@[to_additive existing (attr := deprecated MonoidHom.pi_injective (since := "2026-05-29"))] alias
  MonoidHom.injective_pi := MonoidHom.pi_injective

@[deprecated (since := "2026-05-29")] alias Pi.addMonoidHom_injective := AddMonoidHom.pi_injective
@[to_additive existing (attr := deprecated MonoidHom.pi_injective (since := "2026-05-29"))] alias
  Pi.monoidHom_injective := MonoidHom.pi_injective

variable (f)

/-- Evaluation of functions into an indexed collection of monoids at a point is a monoid
homomorphism.
This is `Function.eval i` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- Evaluation of functions into an indexed collection of additive
monoids at a point is an additive monoid homomorphism. This is `Function.eval i` as an
`AddMonoidHom`. -/]
def Pi.evalMonoidHom (i : I) : (∀ i, f i) →* f i where
  toFun g := g i
  map_one' := Pi.one_apply i
  map_mul' _ _ := Pi.mul_apply _ _ i

@[simp, norm_cast]
lemma Pi.coe_evalMonoidHom (i : I) : ⇑(evalMonoidHom f i) = Function.eval i := rfl

/-- A family of monoid homomorphisms `f i : M i →* N i` defines a monoid homomorphism
`MonoidHom.piMap f : (Π i, M i) →* (Π i, N i)`
given by `MonoidHom.piMap f x i = f i x`. This is `Pi.map` for `MonoidHom`s. -/
@[to_additive (attr := simps!)
  /-- A family of additive monoid homomorphisms `f i : M i →+ N i` defines an additive monoid
  homomorphism  `AddMonoidHom.piMap f : (Π i, M i) →+ (Π i, N i)`
  given by `AddMonoidHom.piMap f x i = f i x`. This is `Pi.map` for `AddMonoidHom`s. -/]
def MonoidHom.piMap [∀ i, MulOneClass (M i)] [∀ i, MulOneClass (N i)] (g : ∀ i, M i →* N i) :
    (∀ i, M i) →* (∀ i, N i) :=
  .pi fun i ↦ (g i).comp (Pi.evalMonoidHom M i)

/-- `Function.const` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `Function.const` as an `AddMonoidHom`. -/]
def Pi.constMonoidHom (α β : Type*) [MulOneClass β] : β →* α → β where
  toFun := Function.const α
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Coercion of a `MonoidHom` into a function is itself a `MonoidHom`.

See also `MonoidHom.eval`. -/
@[to_additive (attr := simps) /-- Coercion of an `AddMonoidHom` into a function is itself
an `AddMonoidHom`.

See also `AddMonoidHom.eval`. -/]
def MonoidHom.coeFn (α β : Type*) [MulOneClass α] [CommMonoid β] : (α →* β) →* α → β where
  toFun g := g
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Monoid homomorphism between the function spaces `I → α` and `I → β`, induced by a monoid
homomorphism `f` between `α` and `β`. -/
@[to_additive (attr := simps)
  /-- Additive monoid homomorphism between the function spaces `I → α` and `I → β`, induced by an
  additive monoid homomorphism `f` between `α` and `β` -/]
protected def MonoidHom.compLeft {α β : Type*} [MulOneClass α] [MulOneClass β] (f : α →* β)
    (I : Type*) : (I → α) →* I → β where
  toFun h := f ∘ h
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

end MonoidHom

section Single

variable [DecidableEq I]

open Pi

variable (f) in
/-- The one-preserving homomorphism including a single value
into a dependent family of values, as functions supported at a point.

This is the `OneHom` version of `Pi.mulSingle`. -/
@[to_additive
  /-- The zero-preserving homomorphism including a single value into a dependent family of values,
  as functions supported at a point.

  This is the `ZeroHom` version of `Pi.single`. -/]
nonrec def OneHom.mulSingle [∀ i, One <| f i] (i : I) : OneHom (f i) (∀ i, f i) where
  toFun := mulSingle i
  map_one' := mulSingle_one i

@[to_additive (attr := simp)]
theorem OneHom.mulSingle_apply [∀ i, One <| f i] (i : I) (x : f i) :
    mulSingle f i x = Pi.mulSingle i x := rfl

@[to_additive (attr := simp, norm_cast)]
theorem OneHom.coe_mulSingle [∀ i, One <| f i] (i : I) :
    mulSingle f i = Pi.mulSingle (M := f) i := rfl

variable (f) in
/-- The monoid homomorphism including a single monoid into a dependent family of additive monoids,
as functions supported at a point.

This is the `MonoidHom` version of `Pi.mulSingle`. -/
@[to_additive
  /-- The additive monoid homomorphism including a single additive monoid into a dependent family
  of additive monoids, as functions supported at a point.

  This is the `AddMonoidHom` version of `Pi.single`. -/]
def MonoidHom.mulSingle [∀ i, MulOneClass <| f i] (i : I) : f i →* ∀ i, f i :=
  { OneHom.mulSingle f i with map_mul' := mulSingle_op₂ (fun _ => (· * ·)) (fun _ => one_mul _) _ }

@[to_additive (attr := simp)]
theorem MonoidHom.mulSingle_apply [∀ i, MulOneClass <| f i] (i : I) (x : f i) :
    mulSingle f i x = Pi.mulSingle i x :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem MonoidHom.coe_mulSingle [∀ i, MulOneClass <| f i] (i : I) :
    mulSingle f i = Pi.mulSingle (M := f) i := rfl

@[to_additive]
theorem Pi.mulSingle_sup [∀ i, SemilatticeSup (f i)] [∀ i, One (f i)] (i : I) (x y : f i) :
    Pi.mulSingle i (x ⊔ y) = Pi.mulSingle i x ⊔ Pi.mulSingle i y :=
  Function.update_sup _ _ _ _

@[to_additive]
theorem Pi.mulSingle_inf [∀ i, SemilatticeInf (f i)] [∀ i, One (f i)] (i : I) (x y : f i) :
    Pi.mulSingle i (x ⊓ y) = Pi.mulSingle i x ⊓ Pi.mulSingle i y :=
  Function.update_inf _ _ _ _

@[to_additive]
theorem Pi.mulSingle_mul [∀ i, MulOneClass <| f i] (i : I) (x y : f i) :
    mulSingle i (x * y) = mulSingle i x * mulSingle i y :=
  (MonoidHom.mulSingle f i).map_mul x y

@[to_additive]
theorem Pi.mulSingle_inv [∀ i, Group <| f i] (i : I) (x : f i) :
    mulSingle i x⁻¹ = (mulSingle i x)⁻¹ :=
  (MonoidHom.mulSingle f i).map_inv x

@[to_additive]
theorem Pi.mulSingle_div [∀ i, Group <| f i] (i : I) (x y : f i) :
    mulSingle i (x / y) = mulSingle i x / mulSingle i y :=
  (MonoidHom.mulSingle f i).map_div x y

@[to_additive]
theorem Pi.mulSingle_pow [∀ i, Monoid (f i)] (i : I) (x : f i) (n : ℕ) :
    mulSingle i (x ^ n) = mulSingle i x ^ n :=
  (MonoidHom.mulSingle f i).map_pow x n

@[to_additive]
theorem Pi.mulSingle_zpow [∀ i, Group (f i)] (i : I) (x : f i) (n : ℤ) :
    mulSingle i (x ^ n) = mulSingle i x ^ n :=
  (MonoidHom.mulSingle f i).map_zpow x n

/-- The injection into a pi group at different indices commutes.

For injections of commuting elements at the same index, see `Commute.map` -/
@[to_additive
  /-- The injection into an additive pi group at different indices commutes.

  For injections of commuting elements at the same index, see `AddCommute.map` -/]
theorem Pi.mulSingle_commute [∀ i, MulOneClass <| f i] :
    Pairwise fun i j => ∀ (x : f i) (y : f j), Commute (mulSingle i x) (mulSingle j y) := by
  intro i j hij x y; ext k
  by_cases i = k <;> simp_all

/-- The injection into a pi group with the same values commutes. -/
@[to_additive /-- The injection into an additive pi group with the same values commutes. -/]
theorem Pi.mulSingle_apply_commute [∀ i, MulOneClass <| f i] (x : ∀ i, f i) (i j : I) :
    Commute (mulSingle i (x i)) (mulSingle j (x j)) := by
  obtain rfl | hij := Decidable.eq_or_ne i j
  · rfl
  · exact Pi.mulSingle_commute hij _ _

@[to_additive]
theorem Pi.update_eq_div_mul_mulSingle [∀ i, Group <| f i] (g : ∀ i : I, f i) (x : f i) :
    Function.update g i x = g / mulSingle i (g i) * mulSingle i x := by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [h, eqComm]

@[to_additive]
theorem Pi.mulSingle_mul_mulSingle_eq_mulSingle_mul_mulSingle {M : Type*} [CommMonoid M]
    {k l m n : I} {u v : M} (hu : u ≠ 1) (hv : v ≠ 1) :
    (mulSingle k u : I → M) * mulSingle l v = mulSingle m u * mulSingle n v ↔
      k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u * v = 1 ∧ k = l ∧ m = n := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hk := congr_fun h k
    have hl := congr_fun h l
    have hm := congr_fun h m
    have hn := congr_fun h n
    grind [mul_one, one_mul, mul_apply]
  · aesop (add simp [mulSingle_apply])

end Single

section
variable [∀ i, Mul <| f i]

@[to_additive]
theorem SemiconjBy.pi {x y z : ∀ i, f i} (h : ∀ i, SemiconjBy (x i) (y i) (z i)) :
    SemiconjBy x y z :=
  funext h

@[to_additive]
theorem Pi.semiconjBy_iff {x y z : ∀ i, f i} :
    SemiconjBy x y z ↔ ∀ i, SemiconjBy (x i) (y i) (z i) := funext_iff

@[to_additive]
theorem Commute.pi {x y : ∀ i, f i} (h : ∀ i, Commute (x i) (y i)) : Commute x y := SemiconjBy.pi h

@[to_additive]
theorem Pi.commute_iff {x y : ∀ i, f i} : Commute x y ↔ ∀ i, Commute (x i) (y i) := semiconjBy_iff

end

namespace Function

@[to_additive (attr := simp)]
theorem update_one [∀ i, One (f i)] [DecidableEq I] (i : I) : update (1 : ∀ i, f i) i 1 = 1 :=
  update_eq_self i (1 : (a : I) → f a)

@[to_additive]
theorem update_mul [∀ i, Mul (f i)] [DecidableEq I] (f₁ f₂ : ∀ i, f i) (i : I) (x₁ : f i)
    (x₂ : f i) : update (f₁ * f₂) i (x₁ * x₂) = update f₁ i x₁ * update f₂ i x₂ :=
  funext fun j => (apply_update₂ (fun _ => (· * ·)) f₁ f₂ i x₁ x₂ j).symm

@[to_additive]
theorem update_inv [∀ i, Inv (f i)] [DecidableEq I] (f₁ : ∀ i, f i) (i : I) (x₁ : f i) :
    update f₁⁻¹ i x₁⁻¹ = (update f₁ i x₁)⁻¹ :=
  funext fun j => (apply_update (fun _ => Inv.inv) f₁ i x₁ j).symm

@[to_additive]
theorem update_div [∀ i, Div (f i)] [DecidableEq I] (f₁ f₂ : ∀ i, f i) (i : I) (x₁ : f i)
    (x₂ : f i) : update (f₁ / f₂) i (x₁ / x₂) = update f₁ i x₁ / update f₂ i x₂ :=
  funext fun j => (apply_update₂ (fun _ => (· / ·)) f₁ f₂ i x₁ x₂ j).symm

variable [One α] [Nonempty ι] {a : α}

@[to_additive (attr := simp)]
theorem const_eq_one : const ι a = 1 ↔ a = 1 :=
  @const_inj _ _ _ _ 1

@[to_additive]
theorem const_ne_one : const ι a ≠ 1 ↔ a ≠ 1 :=
  Iff.not const_eq_one

end Function

section Piecewise

@[to_additive]
theorem Set.piecewise_mul [∀ i, Mul (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)]
    (f₁ f₂ g₁ g₂ : ∀ i, f i) :
    s.piecewise (f₁ * f₂) (g₁ * g₂) = s.piecewise f₁ g₁ * s.piecewise f₂ g₂ :=
  s.piecewise_op₂ f₁ _ _ _ fun _ => (· * ·)

@[to_additive]
theorem Set.piecewise_inv [∀ i, Inv (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)] (f₁ g₁ : ∀ i, f i) :
    s.piecewise f₁⁻¹ g₁⁻¹ = (s.piecewise f₁ g₁)⁻¹ :=
  s.piecewise_op f₁ g₁ fun _ x => x⁻¹

@[to_additive]
theorem Set.piecewise_div [∀ i, Div (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)]
    (f₁ f₂ g₁ g₂ : ∀ i, f i) :
    s.piecewise (f₁ / f₂) (g₁ / g₂) = s.piecewise f₁ g₁ / s.piecewise f₂ g₂ :=
  s.piecewise_op₂ f₁ _ _ _ fun _ => (· / ·)

end Piecewise

section Extend

variable {η : Type v} (R : Type w) (s : ι → η)

/-- `Function.extend s f 1` as a bundled hom. -/
@[to_additive (attr := simps) Function.ExtendByZero.hom
/-- `Function.extend s f 0` as a bundled hom. -/]
noncomputable def Function.ExtendByOne.hom [MulOneClass R] :
    (ι → R) →* η → R where
  toFun f := Function.extend s f 1
  map_one' := Function.extend_one s
  map_mul' f g := by simpa using Function.extend_mul s f g 1 1

end Extend

namespace Pi

variable [DecidableEq I] [∀ i, Preorder (f i)] [∀ i, One (f i)]

@[to_additive]
theorem mulSingle_mono : Monotone (Pi.mulSingle i : f i → ∀ i, f i) :=
  Function.update_mono

@[to_additive]
theorem mulSingle_strictMono : StrictMono (Pi.mulSingle i : f i → ∀ i, f i) :=
  Function.update_strictMono

@[to_additive]
lemma mulSingle_comp_equiv {m n : Type*} [DecidableEq n] [DecidableEq m] [One α] (σ : n ≃ m)
    (i : m) (x : α) : Pi.mulSingle i x ∘ σ = Pi.mulSingle (σ.symm i) x := by
  ext x
  aesop (add simp Pi.mulSingle_apply)

end Pi

namespace Sigma

variable {α : Type*} {β : α → Type*} {γ : ∀ a, β a → Type*}

@[to_additive (attr := simp)]
theorem curry_one [∀ a b, One (γ a b)] : Sigma.curry (1 : (i : Σ a, β a) → γ i.1 i.2) = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem uncurry_one [∀ a b, One (γ a b)] : Sigma.uncurry (1 : ∀ a b, γ a b) = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem curry_mul [∀ a b, Mul (γ a b)] (x y : (i : Σ a, β a) → γ i.1 i.2) :
    Sigma.curry (x * y) = Sigma.curry x * Sigma.curry y :=
  rfl

@[to_additive (attr := simp)]
theorem uncurry_mul [∀ a b, Mul (γ a b)] (x y : ∀ a b, γ a b) :
    Sigma.uncurry (x * y) = Sigma.uncurry x * Sigma.uncurry y :=
  rfl

@[to_additive (attr := simp)]
theorem curry_inv [∀ a b, Inv (γ a b)] (x : (i : Σ a, β a) → γ i.1 i.2) :
    Sigma.curry (x⁻¹) = (Sigma.curry x)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
theorem uncurry_inv [∀ a b, Inv (γ a b)] (x : ∀ a b, γ a b) :
    Sigma.uncurry (x⁻¹) = (Sigma.uncurry x)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
theorem curry_mulSingle [DecidableEq α] [∀ a, DecidableEq (β a)] [∀ a b, One (γ a b)]
    (i : Σ a, β a) (x : γ i.1 i.2) :
    Sigma.curry (Pi.mulSingle i x) = Pi.mulSingle i.1 (Pi.mulSingle i.2 x) := by
  simp only [Pi.mulSingle, Sigma.curry_update, Sigma.curry_one, Pi.one_apply]

@[to_additive (attr := simp)]
theorem uncurry_mulSingle_mulSingle [DecidableEq α] [∀ a, DecidableEq (β a)] [∀ a b, One (γ a b)]
    (a : α) (b : β a) (x : γ a b) :
    Sigma.uncurry (Pi.mulSingle a (Pi.mulSingle b x)) = Pi.mulSingle (Sigma.mk a b) x := by
  rw [← curry_mulSingle ⟨a, b⟩, uncurry_curry]

end Sigma
