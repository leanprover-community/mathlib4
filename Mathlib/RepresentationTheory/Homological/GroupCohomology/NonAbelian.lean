/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
import Mathlib.CategoryTheory.Action.Limits
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Category.Pointed.Exact
import Mathlib.CategoryTheory.Category.Pointed.Forgetful
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Non-abelian group cohomology

Let `G` be a group acting on another (not necessarily abelian) group `A`, in this file we define
`H⁰(G, A)` and `H¹(G, A)`, and prove some basic properties about it.

## Main Results

## Reference

-/

universe u

open CategoryTheory

namespace groupCohomology

namespace NonAbelian

section basic

abbrev NonAbelianRep (G : Type u) [Monoid G] := Action AddGrp.{u} G

variable (G : Type u) [Monoid G]

instance : CoeSort (NonAbelianRep G) (Type u) := ⟨fun V ↦ V.V⟩

instance (A : NonAbelianRep G) : DistribMulAction G A  where
  smul_zero _ :=  map_zero _
  smul_add := by
    intro a x y
    apply map_add


instance (A B : NonAbelianRep G) : Coe (A ⟶ B) (A →+[G] B) := sorry

end basic

section H0

variable (G : Type u) [Monoid G]

def H0 (A : Type*) [AddGroup A] [DistribMulAction G A] : AddSubgroup A where
  carrier := setOf fun v => ∀ g : G, g • v = v
  add_mem' := by simp +contextual
  zero_mem' := by simp
  neg_mem' := by simp +contextual

variable {G}

def H0.map {A B : Type*} [AddGroup A] [AddGroup B] [DistribMulAction G A] [DistribMulAction G B]
    (f : A →+[G] B) : H0 G A →+ H0 G B := sorry

variable (G) in
theorem H0.map_id (A : Type*) [AddGroup A] [DistribMulAction G A] :
    H0.map (.id _) = .id (H0 G A) := sorry

theorem H0.map_comp {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    (f : A →+[G] B) (g : B →+[G] C) : H0.map (g.comp f) = (H0.map g).comp (H0.map f) := sorry

theorem H0.map_injective_of_injective {A B : Type*} [AddGroup A] [AddGroup B] [DistribMulAction G A]
    [DistribMulAction G B] (f : A →+[G] B) (hf : Function.Injective f) :
    Function.Injective (H0.map f) := sorry

-- def H0Functor : (NonAbelianRep G) ⥤ AddGrp := sorry

end H0

section H1

variable (G : Type u) [Monoid G] (A : Type*) [AddGroup A] [DistribMulAction G A]

def Z1 := { f : G → A // ∀ g h : G, f (g * h) = f g + g • f h}

namespace Z1

instance zero : Zero (Z1 G A) := ⟨⟨0, fun g h => by simp⟩⟩
instance inhabited : Inhabited (Z1 G A) := ⟨0⟩

instance coeFun : CoeFun (Z1 G A) (fun _ ↦ G → A) := ⟨fun f ↦ f.val⟩

variable {G} {A} in
def cohomologous (f g : Z1 G A) : Prop :=
  ∃ a : A, ∀ h : G, g h = - a + f h + (h • a)

instance setoid : Setoid (Z1 G A) where
  r := cohomologous
  iseqv := {
    refl := fun f ↦ ⟨0, fun h ↦ by simp⟩,
    symm := fun ⟨a, ha⟩ ↦ ⟨-a, fun h ↦ by simp [← add_assoc, ha h]⟩,
    trans := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨a + b, fun h ↦ by simp [← add_assoc, ha h, hb h]⟩
  }

end Z1

def H1 := Quotient (Z1.setoid G A)

instance : Zero (H1 G A) := ⟨⟦0⟧⟩
instance : Inhabited (H1 G A) := ⟨0⟩

variable {G}

def H1.map {A B : Type*} [AddGroup A] [AddGroup B] [DistribMulAction G A]
    [DistribMulAction G B] (f : A →+[G] B) : H1 G A → H1 G B :=
  Quotient.map (fun z : Z1 G A => ⟨f ∘ z, fun g h => by simp [z.prop, map_smul]⟩)
    (fun z1 z2 ⟨a, ha⟩ => ⟨f a, fun h => by simp [ha, map_smul]⟩)

variable (G) in
theorem H1.map_id (A : Type*) [AddGroup A] [DistribMulAction G A] :
    H1.map (.id _) = 𝟙 (H1 G A) :=
  sorry

theorem H1.map_zero {A B : Type*} [AddGroup A] [AddGroup B] [DistribMulAction G A]
    [DistribMulAction G B] (f : A →+[G] B) : H1.map f 0 = 0 := sorry

theorem H1.map_comp {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    (f : A →+[G] B) (g : B →+[G] C) : H1.map (g.comp f) = (H1.map g).comp (H1.map f) := sorry

-- def H1Functor : NonAbelianRep G ⥤ Pointed := sorry

end H1

section connectHom₀₁

variable {G : Type u} [Group G] {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    {f : A →+[G] B} {g : B →+[G] C} (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g)

noncomputable def δ₀₁_aux (b : B) (c : H0 G C) (hb : g b = c) : Z1 G A := ⟨fun s ↦
    (Equiv.ofInjective f hf).symm
      ⟨-b + s • b, ((hfg _).mp (by simp [hb, c.prop s]))⟩,
    fun g h ↦ hf (by simp [Equiv.apply_ofInjective_symm, mul_smul, ← add_assoc])⟩

theorem δ₀₁_aux_well_defined (b b' : B) (c : H0 G C) (hb : g b = c) (hb' : g b' = c) :
    Z1.cohomologous (δ₀₁_aux hf hfg b c hb) (δ₀₁_aux hf hfg b' c hb') := sorry

noncomputable def δ₀₁ : H0 G C → H1 G A := fun x ↦
    ⟦δ₀₁_aux hf hfg (Classical.choose (hg x)) x (Classical.choose_spec (hg x))⟧

def δ₀₁_zero : δ₀₁ hf hg hfg 0 = 0 := sorry

theorem exact₁ : Function.Exact (H0.map f) (H0.map g) := sorry

theorem exact₂ : Function.Exact (H0.map g) (δ₀₁ hf hg hfg) := sorry

theorem exact₃ : Function.Exact (δ₀₁ hf hg hfg) (H1.map f) := sorry

theorem exact₄ : Function.Exact (H1.map f) (H1.map g) := sorry

-- Add the natural equivalence between δ₀₁ and the original map

end connectHom₀₁


section compatibility

variable {G : Type u} [Group G] {k : Type u} [CommRing k] (A : Rep k G)

-- Why can't this be found automatically?
instance : MulAction G A := Action.instMulAction A

-- should be moved
instance : DistribMulAction G A where
  smul_zero _ := map_zero _
  smul_add _ := map_add _

def H0Iso (A : Rep k G) : groupCohomology.H0 A ≃+ H0 G A := sorry

def H1Iso (A : Rep k G) : groupCohomology.H1 A ≃ H1 G A := sorry

theorem H1Iso_zero : H1Iso A 0 = 0 := sorry

end compatibility

section connectHom₁₂

end connectHom₁₂

end NonAbelian

end groupCohomology
