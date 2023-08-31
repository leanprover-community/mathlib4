/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.GroupTheory.SpecificGroups.Coprod
import Mathlib.GroupTheory.FreeGroup

open Monoid Coprod Multiplicative

notation "C∞ " => Multiplicative ℤ

-- @[reducible]
-- def HNNExtension.TypeFamilyAux (G : Type u) [Group G] :
--     Bool → Σ G : Type u, Group G
--   | true => ⟨FreeGroup PUnit, inferInstance⟩
--   | false => ⟨G, inferInstance⟩

-- variable {G : Type u} [Group G]

-- @[reducible]
-- def HNNExtension.TypeFamily (G : Type u) [Group G] (b : Bool) : Type u :=
--   (HNNExtension.TypeFamilyAux G b).1

-- instance (b : Bool) : Group (HNNExtension.TypeFamily G b) :=
--   (HNNExtension.TypeFamilyAux G b).2

def HNNExtension.con (G : Type*) [Group G] (A B : Subgroup G) (φ : A ≃* B) : Con (G ∗ C∞) :=
  conGen (fun x y => ∃ (a : A),
    x = inr (ofAdd 1) * inl (a : G) ∧
    y = inl (φ a : G) * inr (ofAdd 1))

def HNNExtension  (G : Type*) [Group G] (A B : Subgroup G) (φ : A ≃* B) : Type _ :=
  (HNNExtension.con G A B φ).Quotient

variable {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B} {H : Type*} [Group H]

instance : Group (HNNExtension G A B φ) := by
  delta HNNExtension; infer_instance

namespace HNNExtension

def of : G →* HNNExtension G A B φ :=
  (HNNExtension.con G A B φ).mk'.comp inl

def t : HNNExtension G A B φ :=
  (HNNExtension.con G A B φ).mk'.comp inr (ofAdd 1)

def lift (f : G →* H) (x : H) (hx : ∀ a : A, x * f ↑a = f (φ a : G) * x) :
    HNNExtension G A B φ →* H :=
  Con.lift _ (Coprod.lift f (zpowersHom H x)) (Con.conGen_le <| by
    rintro _ _ ⟨a, rfl, rfl⟩
    simp [hx])

@[simp]
theorem lift_t (f : G →* H) (x : H) (hx : ∀ a : A, x * f ↑a = f (φ a : G) * x) :
    lift f x hx t = x := by
  delta HNNExtension; simp [lift, t]

@[simp]
theorem lift_of (f : G →* H) (x : H) (hx : ∀ a : A, x * f ↑a = f (φ a : G) * x) (g : G) :
    lift f x hx (of g) = f g := by
  delta HNNExtension; simp [lift, of]

@[ext]
theorem hom_ext {f g : HNNExtension G A B φ →* H}
    (hg : f.comp of  = g.comp of) (ht : f t = g t) : f = g :=
  (MonoidHom.cancel_right Con.mk'_surjective).mp <|
    Coprod.ext_hom _ _ hg (MonoidHom.ext_mint ht)

end HNNExtension
