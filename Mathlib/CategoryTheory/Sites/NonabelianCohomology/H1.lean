/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.GroupCat.Basic

/-! The cohomology of a sheaf of groups in degree 1

In this file, we shall define the cohomology in degree 1 of a sheaf
of groups (TODO).

Currently, given a presheaf of groups `G : Cᵒᵖ ⥤ GroupCat` and a family
of objects `U : I → C`, we define 1-cochains/1-cocycles with values
in `G` over `U`. (This definition neither requires the assumption that `G`
is a sheaf, nor that `U` covers the terminal object.)

## TODO

* show that if `1 ⟶ G₁ ⟶ G₂ ⟶ G₃ ⟶ 1` is a short exact sequence of sheaves
of groups, and `x₃` is a global section of `G₃` which can be locally lifted
to a section of `G₂`, there is an associated canonical cohomology class of `G₁`
which is trivial iff `x₃` can be lifted to a global section of `G₂`.
(This should hold more generally if `G₂` is a sheaf of sets on which `G₁` acts
freely, and `G₃` is the quotient sheaf.)
* deduce a similar result for abelian sheaves
* when the notion of quasi-coherent sheaves on schemes is defined, show that
if `0 ⟶ Q ⟶ M ⟶ N ⟶ 0` is an exact sequence of abelian sheaves over a scheme `X`
and `Q` is the underlying sheaf of a quasi-coherent sheaf, then `M(U) ⟶ N(U)`
is surjective for any affine open `U`.
* take the colimit of `Cohomology₁ G U` over all covering families `U` (for
a Grothendieck topology)

-/

universe w' w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace PresheafOfGroups

variable (G : Cᵒᵖ ⥤ GroupCat.{w}) {X : C} {I : Type w'} (U : I → C)

/-- A zero cochain consist of a family of sections. -/
def Cochain₀ := ∀ (i : I), G.obj (Opposite.op (U i))

instance : Group (Cochain₀ G U) := by
  dsimp [Cochain₀]
  infer_instance

namespace Cochain₀

@[simp]
lemma one_apply (i : I) : (1 : Cochain₀ G U) i = 1 := rfl

@[simp]
lemma inv_apply (γ : Cochain₀ G U) (i : I) : γ⁻¹ i = (γ i) ⁻¹ := rfl

@[simp]
lemma mul_apply (γ₁ γ₂ : Cochain₀ G U) (i : I) : (γ₁ * γ₂) i = γ₁ i * γ₂ i := rfl

end Cochain₀

/-- A 1-cochain of a presheaf of groups `G : Cᵒᵖ ⥤ GroupCat` on a family `U : I → C` of objects
consists of the data of an element in `G.obj (Opposite.op T)` whenever we have elements
`i` and `j` in `I` and maps `a : T ⟶ U i` and `b : T ⟶ U j`, and it must satisfy a compatibility
with respect to precomposition. (When the binary product of `U i` and `U j` exists, this
data for all `T`, `a` and `b` corresponds to the data of a section of `G` on this product.) -/
@[ext]
structure Cochain₁ where
  /-- the data involved in a 1-cochain -/
  ev (i j : I) ⦃T : C⦄ (a : T ⟶ U i) (b : T ⟶ U j) : G.obj (Opposite.op T)
  ev_precomp (i j : I) ⦃T T' : C⦄ (φ : T ⟶ T') (a : T' ⟶ U i) (b : T' ⟶ U j) :
    G.map φ.op (ev i j a b) = ev i j (φ ≫ a) (φ ≫ b) := by aesop

namespace Cochain₁

attribute [simp] Cochain₁.ev_precomp

instance : One (Cochain₁ G U) where
  one := { ev := fun _ _ _ _ _ => 1 }

@[simp]
lemma one_ev (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j) :
    (1 : Cochain₁ G U).ev i j a b = 1 := rfl

variable {G U}

instance : Mul (Cochain₁ G U) where
  mul γ₁ γ₂ := { ev := fun i j T a b => γ₁.ev i j a b * γ₂.ev i j a b }

@[simp]
lemma mul_ev (γ₁ γ₂ : Cochain₁ G U) (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j) :
    (γ₁ * γ₂).ev i j a b = γ₁.ev i j a b * γ₂.ev i j a b := rfl

instance : Inv (Cochain₁ G U) where
  inv γ := { ev := fun i j T a b => (γ.ev i j a b) ⁻¹}

@[simp]
lemma inv_ev (γ : Cochain₁ G U) (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j) :
    (γ ⁻¹).ev i j a b = (γ.ev i j a b) ⁻¹ := rfl

instance : Group (Cochain₁ G U) where
  mul_assoc _ _ _ := by ext; apply mul_assoc
  one_mul _ := by ext; apply one_mul
  mul_one _ := by ext; apply mul_one
  mul_left_inv _ := by ext; apply mul_left_inv

end Cochain₁

/-- A 1-cocycle is a 1-cochain which satisfies a cocycle condition. -/
structure Cocycle₁ extends Cochain₁ G U where
  ev_trans (i j k : I) ⦃T : C⦄ (a : T ⟶ U i) (b : T ⟶ U j) (c : T ⟶ U k) :
      ev i j a b * ev j k b c = ev i k a c := by aesop

namespace Cocycle₁

instance : One (Cocycle₁ G U) where
  one := Cocycle₁.mk 1

@[simp]
lemma one_toCochain₁ : (1 : Cocycle₁ G U).toCochain₁ = 1 := rfl

@[simp]
lemma ev_refl (γ : Cocycle₁ G U) (i : I) ⦃T : C⦄ (a : T ⟶ U i) :
    γ.ev i i a a = 1 := by
  simpa using γ.ev_trans i i i a a a

lemma ev_symm (γ : Cocycle₁ G U) (i j : I) ⦃T : C⦄ (a : T ⟶ U i) (b : T ⟶ U j) :
    γ.ev i j a b = (γ.ev j i b a) ⁻¹ := by
  rw [← mul_left_inj (γ.ev j i b a), γ.ev_trans i j i a b a,
    ev_refl, mul_left_inv]

end Cocycle₁

variable {G U}

/-- The assertion that two cochains in `Cochain₁ G U` are cohomologous via
an explicit zero-cochain. -/
def CohomologyRelation₁ (γ₁ γ₂ : Cochain₁ G U) (α : Cochain₀ G U) : Prop :=
  ∀ (i j : I) ⦃T : C⦄ (a : T ⟶ U i) (b : T ⟶ U j),
    G.map a.op (α i) * γ₁.ev i j a b = γ₂.ev i j a b * G.map b.op (α j)

namespace CohomologyRelation₁

lemma refl (γ : Cochain₁ G U) : CohomologyRelation₁ γ γ 1 := fun _ _ _ _ _ => by simp

lemma symm {γ₁ γ₂ : Cochain₁ G U} {α : Cochain₀ G U} (h : CohomologyRelation₁ γ₁ γ₂ α) :
    CohomologyRelation₁ γ₂ γ₁ α⁻¹ := fun i j T a b => by
  rw [← mul_left_inj (G.map b.op (α j)), mul_assoc, ← h i j a b,
    mul_assoc, Cochain₀.inv_apply, map_inv, inv_mul_cancel_left,
    Cochain₀.inv_apply, map_inv, mul_left_inv, mul_one]

lemma trans {γ₁ γ₂ γ₃ : Cochain₁ G U} {α β : Cochain₀ G U}
    (h₁₂ : CohomologyRelation₁ γ₁ γ₂ α) (h₂₃ : CohomologyRelation₁ γ₂ γ₃ β) :
    CohomologyRelation₁ γ₁ γ₃ (β * α) := fun i j T a b => by
  dsimp
  rw [map_mul, map_mul, mul_assoc, h₁₂ i j a b, ← mul_assoc,
    h₂₃ i j a b, mul_assoc]

end CohomologyRelation₁

namespace Cocycle₁

/-- The cohomology (equivalence) relation on 1-cocycles. -/
def IsCohomologous (γ₁ γ₂ : Cocycle₁ G U) : Prop :=
  ∃ (α : Cochain₀ G U), CohomologyRelation₁ γ₁.toCochain₁ γ₂.toCochain₁ α

variable (G U)

lemma equivalence_isCohomologous :
    _root_.Equivalence (IsCohomologous (G := G) (U := U)) where
  refl γ := ⟨_, CohomologyRelation₁.refl γ.toCochain₁⟩
  symm := by
    rintro γ₁ γ₂ ⟨α, h⟩
    exact ⟨_, h.symm⟩
  trans := by
    rintro γ₁ γ₂ γ₂ ⟨α, h⟩ ⟨β, h'⟩
    exact ⟨_, h.trans h'⟩

end Cocycle₁

variable (G U) in
/-- The cohomology in degree 1 of a presheaf of groups
`G : Cᵒᵖ ⥤ GroupCat` on a family of objects `U : I → C`. -/
def Cohomology₁ := Quot (Cocycle₁.IsCohomologous (G := G) (U := U))

/-- The cohomology class of a 1-cocycle. -/
def Cocycle₁.class (γ : Cocycle₁ G U) : Cohomology₁ G U := Quot.mk _ γ

instance : One (Cohomology₁ G U) where
  one := Cocycle₁.class 1

lemma Cocycle₁.class_eq_iff (γ₁ γ₂ : Cocycle₁ G U) :
    γ₁.class = γ₂.class ↔ γ₁.IsCohomologous γ₂ :=
  (equivalence_isCohomologous _ _ ).quot_mk_eq_iff _ _

lemma Cocycle₁.IsCohomologous.class_eq {γ₁ γ₂ : Cocycle₁ G U} (h : γ₁.IsCohomologous γ₂) :
    γ₁.class = γ₂.class :=
  Quot.sound h

end PresheafOfGroups

end CategoryTheory
