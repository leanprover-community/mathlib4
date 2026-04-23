/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.AddConstMap.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive

/-!
# Equivalences conjugating `(· + a)` to `(· + b)`

In this file we define `AddConstEquiv G H a b` (notation: `G ≃+c[a, b] H`)
to be the type of equivalences such that `∀ x, f (x + a) = f x + b`.

We also define the corresponding typeclass and prove some basic properties.
-/

@[expose] public section

assert_not_exists Finset

open Function
open scoped AddConstMap

/-- An equivalence between `G` and `H` conjugating `(· + a)` to `(· + b)`,
denoted as `G ≃+c[a, b] H`. -/
structure AddConstEquiv (G H : Type*) [Add G] [Add H] (a : G) (b : H)
  extends G ≃ H, G →+c[a, b] H

/-- Interpret an `AddConstEquiv` as an `Equiv`. -/
add_decl_doc AddConstEquiv.toEquiv

/-- Interpret an `AddConstEquiv` as an `AddConstMap`. -/
add_decl_doc AddConstEquiv.toAddConstMap

@[inherit_doc]
scoped[AddConstMap] notation:25 G " ≃+c[" a ", " b "] " H => AddConstEquiv G H a b

namespace AddConstEquiv

variable {G H K : Type*} [Add G] [Add H] [Add K] {a : G} {b : H} {c : K}

lemma toEquiv_injective : Injective (toEquiv : (G ≃+c[a, b] H) → G ≃ H)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

instance {G H : Type*} [Add G] [Add H] {a : G} {b : H} :
    EquivLike (G ≃+c[a, b] H) G H where
  coe f := f.toEquiv
  inv f := f.toEquiv.symm
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' _ _ h _ := toEquiv_injective <| DFunLike.ext' h

instance {G H : Type*} [Add G] [Add H] {a : G} {b : H} :
    AddConstMapClass (G ≃+c[a, b] H) G H a b where
  map_add_const f x := f.map_add_const' x

@[ext] lemma ext {e₁ e₂ : G ≃+c[a, b] H} (h : ∀ x, e₁ x = e₂ x) : e₁ = e₂ := DFunLike.ext _ _ h

@[simp]
lemma toEquiv_inj {e₁ e₂ : G ≃+c[a, b] H} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  toEquiv_injective.eq_iff

@[simp] lemma coe_toEquiv (e : G ≃+c[a, b] H) : ⇑e.toEquiv = e := rfl

/-- Inverse map of an `AddConstEquiv`, as an `AddConstEquiv`. -/
def symm (e : G ≃+c[a, b] H) : H ≃+c[b, a] G where
  toEquiv := e.toEquiv.symm
  map_add_const' := (AddConstMapClass.semiconj e).inverse_left e.left_inv e.right_inv

/-- A custom projection for `simps`. -/
def Simps.symm_apply (e : G ≃+c[a, b] H) : H → G := e.symm

initialize_simps_projections AddConstEquiv (toFun → apply, invFun → symm_apply)

@[simp] lemma symm_symm (e : G ≃+c[a, b] H) : e.symm.symm = e := rfl

/-- The identity map as an `AddConstEquiv`. -/
@[simps! toEquiv apply]
def refl (a : G) : G ≃+c[a, a] G where
  toEquiv := .refl G
  map_add_const' _ := rfl

@[simp] lemma symm_refl (a : G) : (refl a).symm = refl a := rfl

/-- Composition of `AddConstEquiv`s, as an `AddConstEquiv`. -/
@[simps! +simpRhs toEquiv apply]
def trans (e₁ : G ≃+c[a, b] H) (e₂ : H ≃+c[b, c] K) : G ≃+c[a, c] K where
  toEquiv := e₁.toEquiv.trans e₂.toEquiv
  map_add_const' := (AddConstMapClass.semiconj e₁).trans (AddConstMapClass.semiconj e₂)

@[simp] lemma trans_refl (e : G ≃+c[a, b] H) : e.trans (.refl b) = e := rfl
@[simp] lemma refl_trans (e : G ≃+c[a, b] H) : (refl a).trans e = e := rfl

@[simp]
lemma self_trans_symm (e : G ≃+c[a, b] H) : e.trans e.symm = .refl a :=
  toEquiv_injective e.toEquiv.self_trans_symm

@[simp]
lemma symm_trans_self (e : G ≃+c[a, b] H) : e.symm.trans e = .refl b :=
  toEquiv_injective e.toEquiv.symm_trans_self

@[simp]
lemma coe_symm_toEquiv (e : G ≃+c[a, b] H) : ⇑e.toEquiv.symm = e.symm := rfl

@[simp]
lemma toEquiv_symm (e : G ≃+c[a, b] H) : e.symm.toEquiv = e.toEquiv.symm := rfl

@[simp]
lemma toEquiv_trans (e₁ : G ≃+c[a, b] H) (e₂ : H ≃+c[b, c] K) :
    (e₁.trans e₂).toEquiv = e₁.toEquiv.trans e₂.toEquiv := rfl

instance instOne : One (G ≃+c[a, a] G) := ⟨.refl _⟩
instance instMul : Mul (G ≃+c[a, a] G) := ⟨fun f g ↦ g.trans f⟩
instance instInv : Inv (G ≃+c[a, a] G) := ⟨.symm⟩
instance instDiv : Div (G ≃+c[a, a] G) := ⟨fun f g ↦ f * g⁻¹⟩

instance instPowNat : Pow (G ≃+c[a, a] G) ℕ where
  pow e n := ⟨e^n, (e.toAddConstMap^n).map_add_const'⟩

instance instPowInt : Pow (G ≃+c[a, a] G) ℤ where
  pow e n := ⟨e^n,
    match n with
    | .ofNat n => (e^n).map_add_const'
    | .negSucc n => (e.symm^(n + 1)).map_add_const'⟩

instance instGroup : Group (G ≃+c[a, a] G) :=
  toEquiv_injective.group _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    fun _ _ ↦ rfl

/-- Projection from `G ≃+c[a, a] G` to permutations `G ≃ G`, as a monoid homomorphism. -/
@[simps! apply]
def toPerm : (G ≃+c[a, a] G) →* Equiv.Perm G :=
  .mk' toEquiv fun _ _ ↦ rfl

/-- Projection from `G ≃+c[a, a] G` to `G →+c[a, a] G`, as a monoid homomorphism. -/
@[simps! apply]
def toAddConstMapHom : (G ≃+c[a, a] G) →* (G →+c[a, a] G) where
  toFun := toAddConstMap
  map_mul' _ _ := rfl
  map_one' := rfl

/-- Group equivalence between `G ≃+c[a, a] G` and the units of `G →+c[a, a] G`. -/
@[simps!]
def equivUnits : (G ≃+c[a, a] G) ≃* (G →+c[a, a] G)ˣ where
  toFun := toAddConstMapHom.toHomUnits
  invFun u :=
    { toEquiv := Equiv.Perm.equivUnitsEnd.symm <| Units.map AddConstMap.toEnd u
      map_add_const' := u.1.2 }
  map_mul' _ _ := rfl

end AddConstEquiv
