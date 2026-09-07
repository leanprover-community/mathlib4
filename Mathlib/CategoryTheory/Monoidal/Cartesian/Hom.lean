/-
Copyright (c) 2024 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
Note: I was getting some error when I tried to submit a PR. Claude asked me to add
that copyright section above - I am not sure if I am supposed to or not.

In this file we shall define ring structure on `Hom A A` for an abelian
group object `A`.

In general for any monoidal object `H`, the morphisms `X ⟶ H` for any `X`
has an additon defined on it. If we consider two morphisms `f g : G ⟶ H`
which are monoidal morphisms, then `f + g` will also be a monoidal
morphisms.

Further the type of all monoial morphisms `Hom A A` for a commutative
monoidal object is a semiring, and when the object is a group object,
it is ring.
-/

@[expose] public section

section RingStructure
open CategoryTheory MonoidalCategory Mon MonObj CartesianMonoidalCategory

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable {G G₁ H : C} [MonObj G] [MonObj G₁] [MonObj H] [IsCommMonObj H]

namespace IsMonHom

abbrev add (f g : G ⟶ H) [IsMonHom f] [IsMonHom g] : G ⟶ H := (lift f g) ≫ μ[H]

-- I am not sure what is the right name for this
set_option linter.unusedSectionVars false
lemma one_comp_lift (f g : G ⟶ G₁) [IsMonHom f] [IsMonHom g]
    : (η[G] ≫ (lift f g)) = (lift η[G₁] η[G₁]) := by
  ext
  · simp [IsMonHom.one_hom f]
  · simp [IsMonHom.one_hom g]

lemma leftUnitor_inv_comp_one : (λ_ (𝟙_ C)).inv ≫ (η[H] ⊗ₘ η[H]) = lift η[H] η[H]
    := by
  ext <;> simp only [mon_tauto] <;> simp

instance add_IsMonHom {f g : G ⟶ H} [IsMonHom f] [IsMonHom g]
    : IsMonHom (IsMonHom.add f g) where
  one_hom := by
    rw [reassoc_of% one_comp_lift f g]
    simp_rw [← reassoc_of% leftUnitor_inv_comp_one, mon_tauto]

  mul_hom := by
    have : μ[G] ≫ lift f g = lift (μ[G] ≫ f) (μ[G] ≫ g) := by
      ext <;> simp
    rw [← Category.assoc, this, IsMonHom.mul_hom]
    have this₀ : lift ((f ⊗ₘ f) ≫ μ) ((g ⊗ₘ g) ≫ μ)
        = lift (f ⊗ₘ f) (g ⊗ₘ g) ≫ (μ ⊗ₘ μ) := by
      ext <;> simp
    have this₀₀ : ((lift f g) ⊗ₘ (lift f g)) ≫ (μ ⊗ₘ μ)
        = (lift f g ≫ μ ⊗ₘ lift f g ≫ μ) := by
      ext <;> simp
    have big_this : (α_ H H (H ⊗ H)).hom ≫ (H ◁ (α_ H H H).inv) ≫
        (H ◁ μ ▷ H) ≫ (H ◁ μ) ≫ μ = (μ ⊗ₘ μ) ≫ μ := by
      simp only [mon_tauto]
    have this₁ : (H ◁ ((β_ H H).hom ≫ μ) ▷ H) = (H ◁ μ[H] ▷ H) := by
      rw [IsCommMonObj.mul_comm]
    have THIS : lift (f ⊗ₘ f) (g ⊗ₘ g) ≫
        ((α_ H H (H ⊗ H)).hom ≫ (H ◁ (α_ H H H).inv) ≫
        ((H ◁ μ[H] ▷ H)))
        = ((lift f g) ⊗ₘ (lift f g)) ≫
        (α_ H H (H ⊗ H)).hom ≫ (H ◁ (α_ H H H).inv) ≫
        (H ◁ ((β_ H H).hom ≫ μ) ▷ H) := by
      ext
      · simp only [Category.assoc, whiskerLeft_fst, associator_hom_fst,
        lift_fst_assoc, tensorHom_fst, IsCommMonObj.mul_comm, tensorHom_fst_assoc, lift_fst]
      · simp only [Category.assoc, whiskerLeft_snd, whiskerLeft_snd_assoc, whiskerRight_fst,
        IsCommMonObj.mul_comm]
        have : lift (f ⊗ₘ f) (g ⊗ₘ g) ≫ (α_ H H (H ⊗ H)).hom ≫
            snd H (H ⊗ H ⊗ H) ≫ (α_ H H H).inv ≫ fst (H ⊗ H) H ≫ μ
            = (lift (f ⊗ₘ f) (g ⊗ₘ g) ≫ (α_ H H (H ⊗ H)).hom ≫
            snd H (H ⊗ H ⊗ H) ≫ (α_ H H H).inv ≫ fst (H ⊗ H) H) ≫ μ
            := by simp
        rw [this]
        have : lift (f ⊗ₘ f) (g ⊗ₘ g) ≫
            (α_ H H (H ⊗ H)).hom ≫ snd H (H ⊗ H ⊗ H) ≫ (α_ H H H).inv ≫ fst (H ⊗ H) H
            = (lift f g ⊗ₘ lift f g) ≫ (α_ H H (H ⊗ H)).hom ≫
            snd H (H ⊗ H ⊗ H) ≫ (α_ H H H).inv ≫ fst (H ⊗ H) H ≫ (β_ H H).hom := by
          ext <;> simp
        simp [this]
      · simp
    rw [← this₀₀]
    have : ((lift f g ⊗ₘ lift f g) ≫ (μ ⊗ₘ μ)) ≫ μ
        = ((lift f g ⊗ₘ lift f g) ≫ ((μ ⊗ₘ μ)) ≫ μ) := by simp
    simp_rw [this, ← big_this, ← this₁, ← reassoc_of% THIS, mon_tauto,
    IsMonHom.mul_hom, ← reassoc_of% this₀]


/-
If `G` and `H` are monoidal object in a Cartesian Monoidal Category, where `H` has a
commutative monoidal structure, the monoidal homomorphisms between them have a natural
addition.

We use the additive notation here for two reasons:
1. Multiplication of functions usually means compositon
2. The additive structure will later be part of a ring strucutre.

I will submit the rest of the ring structure separately.
-/
instance {G₀ H₀ : Mon C} [IsCommMonObj H₀.X] : Add (Hom G₀ H₀) where
  add f g := {
    hom := IsMonHom.add f.hom g.hom
    isMonHom_hom := by infer_instance
  }

end IsMonHom
end RingStructure
