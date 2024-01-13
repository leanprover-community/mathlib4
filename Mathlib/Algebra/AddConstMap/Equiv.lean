/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.AddConstMap.Basic
/-!
# Equivalences conjugating `(· + a)` to `(· + b)`

In this file we define `AddConstEquiv G H a b` (notation: `G ≃+c[a, b] H`)
to be the type of equivalences such that `∀ x, f (x + a) = f x + b`.

We also define the corresponding typeclass and prove some basic properties.
-/

open Function

/-- An equivalence between `G` and `H` conjugating `(· + a)` to `(· + b)`. -/
structure AddConstEquiv (G H : Type*) [Add G] [Add H] (a : G) (b : H)
  extends G ≃ H, G →+c[a, b] H

@[inherit_doc]
notation:25 G " ≃+c[" a ", " b "] " H => AddConstEquiv G H a b

/-- A typeclass saying that `F` is a type of bundled equivalences `G ≃ H`
semiconjugating `(· + a)` to `(· + b)`. -/
class AddConstEquivClass (F : Type*) (G H : outParam (Type*)) [Add G] [Add H]
    (a : outParam G) (b : outParam H) extends EquivLike F G H where
  /-- A map of `AddConstEquivClass` class semiconjugates shift by `a` to the shift by `b`:
  `∀ x, f (x + a) = f x + b`. -/
  map_add_const (f : F) (x : G) : f (x + a) = f x + b

instance (priority := 100) {F : Type*} {G H : outParam Type*} [Add G] [Add H]
    {a : outParam G} {b : outParam H} [h : AddConstEquivClass F G H a b] :
    AddConstMapClass F G H a b where
  toFunLike := inferInstance
  __ := h

instance {G H : Type*} [Add G] [Add H] {a : G} {b : H} :
    AddConstEquivClass (G ≃+c[a, b] H) G H a b where
  coe f := f.toEquiv
  inv f := f.toEquiv.symm
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' | ⟨_, _⟩, ⟨_, _⟩, h, _ => by congr; exact FunLike.ext' h
  map_add_const f x := f.map_add_const' x

namespace AddConstEquiv

variable {G H K : Type*} [Add G] [Add H] [Add K] {a : G} {b : H} {c : K}

@[ext] lemma ext {e₁ e₂ : G ≃+c[a, b] H} (h : ∀ x, e₁ x = e₂ x) : e₁ = e₂ := FunLike.ext _ _ h

lemma toEquiv_injective : Injective (toEquiv : (G ≃+c[a, b] H) → G ≃ H) :=
  Injective.of_comp <| show Injective (FunLike.coe ∘ _) from FunLike.coe_injective

@[simp]
lemma toEquiv_eq_iff {e₁ e₂ : G ≃+c[a, b] H} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  toEquiv_injective.eq_iff

@[simp] lemma coe_toEquiv (e : G ≃+c[a, b] H) : ⇑e.toEquiv = e := rfl

/-- Inverse map of an `AddConstEquiv`, as an `AddConstEquiv`. -/
@[pp_dot]
def symm (e : G ≃+c[a, b] H) : H ≃+c[b, a] G where
  toEquiv := e.toEquiv.symm
  map_add_const' := (AddConstMapClass.semiconj e).inverse_left e.left_inv e.right_inv

/-- A custom projection for `simps`. -/
def Simps.symm_apply (e : G ≃+c[a, b] H) : H → G := e.symm

initialize_simps_projections AddConstEquiv (toFun → apply, invFun → symm_apply, +toEquiv)

@[simp] lemma symm_symm (e : G ≃+c[a, b] H) : e.symm.symm = e := rfl

/-- The identity map as an `AddConstEquiv`. -/
@[simps! toEquiv apply]
def refl (a : G) : G ≃+c[a, a] G where
  toEquiv := .refl G
  map_add_const' _ := rfl

@[simp] lemma symm_refl (a : G) : (refl a).symm = refl a := rfl

/-- Composition of `AddConstEquiv`s, as an `AddConstEquiv`. -/
@[simps! (config := { simpRhs := true }) toEquiv apply, pp_dot]
def trans (e₁ : G ≃+c[a, b] H) (e₂ : H ≃+c[b, c] K) : G ≃+c[a, c] K where
  toEquiv := e₁.toEquiv.trans e₂.toEquiv
  map_add_const' := (AddConstMapClass.semiconj e₁).comp_left (AddConstMapClass.semiconj e₂)

@[simp] lemma trans_refl (e : G ≃+c[a, b] H) : e.trans (.refl b) = e := rfl
@[simp] lemma refl_trans (e : G ≃+c[a, b] H) : (refl a).trans e = e := rfl

@[simp]
lemma self_trans_symm (e : G ≃+c[a, b] H) : e.trans e.symm = .refl a :=
  toEquiv_injective e.toEquiv.self_trans_symm

@[simp]
lemma symm_trans_self (e : G ≃+c[a, b] H) : e.symm.trans e = .refl b :=
  toEquiv_injective e.toEquiv.symm_trans_self

end AddConstEquiv
