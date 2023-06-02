/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno

! This file was ported from Lean 3 source module category_theory.bicategory.coherence_tactic
! leanprover-community/mathlib commit 3d7987cda72abc473c7cdbbb075170e9ac620042
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Bicategory.Coherence

/-!
# A `coherence` tactic for bicategories, and `⊗≫` (composition up to associators)

We provide a `coherence` tactic,
which proves that any two 2-morphisms (with the same source and target)
in a bicategory which are built out of associators and unitors
are equal.

We also provide `f ⊗≫ g`, the `bicategoricalComp` operation,
which automatically inserts associators and unitors as needed
to make the target of `f` match the source of `g`.

This file mainly deals with the type class setup for the coherence tactic. The actual front end
tactic is given in `CategoryTheory.Monoidal.Coherence` at the same time as the coherence
tactic for monoidal categories.
-/


noncomputable section

universe w v u

open CategoryTheory

open CategoryTheory.FreeBicategory

open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B] {a b c d e : B}

namespace CategoryTheory.Bicategory

/-- A typeclass carrying a choice of lift of a 1-morphism from `B` to `FreeBicategory B`. -/
class LiftHom {a b : B} (f : a ⟶ b) where
  lift : of.obj a ⟶ of.obj b
#align category_theory.bicategory.lift_hom CategoryTheory.Bicategory.LiftHom

instance liftHomId : LiftHom (𝟙 a) where lift := 𝟙 (of.obj a)
#align category_theory.bicategory.lift_hom_id CategoryTheory.Bicategory.liftHomId

instance liftHomComp (f : a ⟶ b) (g : b ⟶ c) [LiftHom f] [LiftHom g] : LiftHom (f ≫ g)
    where lift := LiftHom.lift f ≫ LiftHom.lift g
#align category_theory.bicategory.lift_hom_comp CategoryTheory.Bicategory.liftHomComp

instance (priority := 100) liftHomOf (f : a ⟶ b) : LiftHom f where lift := of.map f
#align category_theory.bicategory.lift_hom_of CategoryTheory.Bicategory.liftHomOf

/-- A typeclass carrying a choice of lift of a 2-morphism from `B` to `FreeBicategory B`. -/
class LiftHom₂ {f g : a ⟶ b} [LiftHom f] [LiftHom g] (η : f ⟶ g) where
  lift : LiftHom.lift f ⟶ LiftHom.lift g
#align category_theory.bicategory.lift_hom₂ CategoryTheory.Bicategory.LiftHom₂

instance liftHom₂Id (f : a ⟶ b) [LiftHom f] : LiftHom₂ (𝟙 f) where lift := 𝟙 _
#align category_theory.bicategory.lift_hom₂_id CategoryTheory.Bicategory.liftHom₂Id

instance liftHom₂LeftUnitorHom (f : a ⟶ b) [LiftHom f] : LiftHom₂ (λ_ f).hom
    where lift := (λ_ (LiftHom.lift f)).hom
#align category_theory.bicategory.lift_hom₂_left_unitor_hom CategoryTheory.Bicategory.liftHom₂LeftUnitorHom

instance liftHom₂LeftUnitorInv (f : a ⟶ b) [LiftHom f] : LiftHom₂ (λ_ f).inv
    where lift := (λ_ (LiftHom.lift f)).inv
#align category_theory.bicategory.lift_hom₂_left_unitor_inv CategoryTheory.Bicategory.liftHom₂LeftUnitorInv

instance liftHom₂RightUnitorHom (f : a ⟶ b) [LiftHom f] : LiftHom₂ (ρ_ f).hom
    where lift := (ρ_ (LiftHom.lift f)).hom
#align category_theory.bicategory.lift_hom₂_right_unitor_hom CategoryTheory.Bicategory.liftHom₂RightUnitorHom

instance liftHom₂RightUnitorInv (f : a ⟶ b) [LiftHom f] : LiftHom₂ (ρ_ f).inv
    where lift := (ρ_ (LiftHom.lift f)).inv
#align category_theory.bicategory.lift_hom₂_right_unitor_inv CategoryTheory.Bicategory.liftHom₂RightUnitorInv

instance liftHom₂AssociatorHom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) [LiftHom f] [LiftHom g]
    [LiftHom h] : LiftHom₂ (α_ f g h).hom
    where lift := (α_ (LiftHom.lift f) (LiftHom.lift g) (LiftHom.lift h)).hom
#align category_theory.bicategory.lift_hom₂_associator_hom CategoryTheory.Bicategory.liftHom₂AssociatorHom

instance liftHom₂AssociatorInv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) [LiftHom f] [LiftHom g]
    [LiftHom h] : LiftHom₂ (α_ f g h).inv
    where lift := (α_ (LiftHom.lift f) (LiftHom.lift g) (LiftHom.lift h)).inv
#align category_theory.bicategory.lift_hom₂_associator_inv CategoryTheory.Bicategory.liftHom₂AssociatorInv

instance liftHom₂Comp {f g h : a ⟶ b} [LiftHom f] [LiftHom g] [LiftHom h] (η : f ⟶ g) (θ : g ⟶ h)
    [LiftHom₂ η] [LiftHom₂ θ] : LiftHom₂ (η ≫ θ) where lift := LiftHom₂.lift η ≫ LiftHom₂.lift θ
#align category_theory.bicategory.lift_hom₂_comp CategoryTheory.Bicategory.liftHom₂Comp

instance liftHom₂WhiskerLeft (f : a ⟶ b) [LiftHom f] {g h : b ⟶ c} (η : g ⟶ h) [LiftHom g]
    [LiftHom h] [LiftHom₂ η] : LiftHom₂ (f ◁ η) where lift := LiftHom.lift f ◁ LiftHom₂.lift η
#align category_theory.bicategory.lift_hom₂_whisker_left CategoryTheory.Bicategory.liftHom₂WhiskerLeft

instance liftHom₂WhiskerRight {f g : a ⟶ b} (η : f ⟶ g) [LiftHom f] [LiftHom g] [LiftHom₂ η]
    {h : b ⟶ c} [LiftHom h] : LiftHom₂ (η ▷ h) where lift := LiftHom₂.lift η ▷ LiftHom.lift h
#align category_theory.bicategory.lift_hom₂_whisker_right CategoryTheory.Bicategory.liftHom₂WhiskerRight

/-- A typeclass carrying a choice of bicategorical structural isomorphism between two objects.
Used by the `⊗≫` bicategorical composition operator, and the `coherence` tactic.
-/
class BicategoricalCoherence (f g : a ⟶ b) [LiftHom f] [LiftHom g] where
  hom' : f ⟶ g
  [isIso : IsIso hom']
#align category_theory.bicategory.bicategorical_coherence CategoryTheory.Bicategory.BicategoricalCoherence


namespace BicategoricalCoherence

attribute [instance] isIso

-- porting note: the field `BicategoricalCoherence.hom'` was named `hom` in mathlib3, but in Lean4
-- `f` and `g` are not explicit parameters, so that we have to redefine `hom` as follows
@[reducible]
def hom (f g : a ⟶ b) [LiftHom f] [LiftHom g] [BicategoricalCoherence f g] : f ⟶ g := hom'

@[simps]
instance refl (f : a ⟶ b) [LiftHom f] : BicategoricalCoherence f f :=
  ⟨𝟙 _⟩
#align category_theory.bicategory.bicategorical_coherence.refl CategoryTheory.Bicategory.BicategoricalCoherence.refl

@[simps]
instance whiskerLeft (f : a ⟶ b) (g h : b ⟶ c) [LiftHom f] [LiftHom g] [LiftHom h]
    [BicategoricalCoherence g h] : BicategoricalCoherence (f ≫ g) (f ≫ h) :=
  ⟨f ◁ BicategoricalCoherence.hom g h⟩
#align category_theory.bicategory.bicategorical_coherence.whisker_left CategoryTheory.Bicategory.BicategoricalCoherence.whiskerLeft

@[simps]
instance whiskerRight (f g : a ⟶ b) (h : b ⟶ c) [LiftHom f] [LiftHom g] [LiftHom h]
    [BicategoricalCoherence f g] : BicategoricalCoherence (f ≫ h) (g ≫ h) :=
  ⟨BicategoricalCoherence.hom f g ▷ h⟩
#align category_theory.bicategory.bicategorical_coherence.whisker_right CategoryTheory.Bicategory.BicategoricalCoherence.whiskerRight

@[simps]
instance tensorRight (f : a ⟶ b) (g : b ⟶ b) [LiftHom f] [LiftHom g]
    [BicategoricalCoherence (𝟙 b) g] : BicategoricalCoherence f (f ≫ g) :=
  ⟨(ρ_ f).inv ≫ f ◁ BicategoricalCoherence.hom (𝟙 b) g⟩
#align category_theory.bicategory.bicategorical_coherence.tensor_right CategoryTheory.Bicategory.BicategoricalCoherence.tensorRight

@[simps]
instance tensorRight' (f : a ⟶ b) (g : b ⟶ b) [LiftHom f] [LiftHom g]
    [BicategoricalCoherence g (𝟙 b)] : BicategoricalCoherence (f ≫ g) f :=
  ⟨f ◁ BicategoricalCoherence.hom g (𝟙 b) ≫ (ρ_ f).hom⟩
#align category_theory.bicategory.bicategorical_coherence.tensor_right' CategoryTheory.Bicategory.BicategoricalCoherence.tensorRight'

@[simps]
instance left (f g : a ⟶ b) [LiftHom f] [LiftHom g] [BicategoricalCoherence f g] :
    BicategoricalCoherence (𝟙 a ≫ f) g :=
  ⟨(λ_ f).hom ≫ BicategoricalCoherence.hom f g⟩
#align category_theory.bicategory.bicategorical_coherence.left CategoryTheory.Bicategory.BicategoricalCoherence.left

@[simps]
instance left' (f g : a ⟶ b) [LiftHom f] [LiftHom g] [BicategoricalCoherence f g] :
    BicategoricalCoherence f (𝟙 a ≫ g) :=
  ⟨BicategoricalCoherence.hom f g ≫ (λ_ g).inv⟩
#align category_theory.bicategory.bicategorical_coherence.left' CategoryTheory.Bicategory.BicategoricalCoherence.left'

@[simps]
instance right (f g : a ⟶ b) [LiftHom f] [LiftHom g] [BicategoricalCoherence f g] :
    BicategoricalCoherence (f ≫ 𝟙 b) g :=
  ⟨(ρ_ f).hom ≫ BicategoricalCoherence.hom f g⟩
#align category_theory.bicategory.bicategorical_coherence.right CategoryTheory.Bicategory.BicategoricalCoherence.right

@[simps]
instance right' (f g : a ⟶ b) [LiftHom f] [LiftHom g] [BicategoricalCoherence f g] :
    BicategoricalCoherence f (g ≫ 𝟙 b) :=
  ⟨BicategoricalCoherence.hom f g ≫ (ρ_ g).inv⟩
#align category_theory.bicategory.bicategorical_coherence.right' CategoryTheory.Bicategory.BicategoricalCoherence.right'

@[simps]
instance assoc (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : a ⟶ d) [LiftHom f] [LiftHom g] [LiftHom h]
    [LiftHom i] [BicategoricalCoherence (f ≫ g ≫ h) i] :
    BicategoricalCoherence ((f ≫ g) ≫ h) i :=
  ⟨(α_ f g h).hom ≫ BicategoricalCoherence.hom (f ≫ g ≫ h) i⟩
#align category_theory.bicategory.bicategorical_coherence.assoc CategoryTheory.Bicategory.BicategoricalCoherence.assoc

@[simps]
instance assoc' (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : a ⟶ d) [LiftHom f] [LiftHom g] [LiftHom h]
    [LiftHom i] [BicategoricalCoherence i (f ≫ g ≫ h)] :
    BicategoricalCoherence i ((f ≫ g) ≫ h) :=
  ⟨BicategoricalCoherence.hom i (f ≫ g ≫ h) ≫ (α_ f g h).inv⟩
#align category_theory.bicategory.bicategorical_coherence.assoc' CategoryTheory.Bicategory.BicategoricalCoherence.assoc'

end BicategoricalCoherence

/-- Construct an isomorphism between two objects in a bicategorical category
out of unitors and associators. -/
def bicategoricalIso (f g : a ⟶ b) [LiftHom f] [LiftHom g] [BicategoricalCoherence f g] : f ≅ g :=
  asIso (BicategoricalCoherence.hom f g)
#align category_theory.bicategory.bicategorical_iso CategoryTheory.Bicategory.bicategoricalIso

/-- Compose two morphisms in a bicategorical category,
inserting unitors and associators between as necessary. -/
def bicategoricalComp {f g h i : a ⟶ b} [LiftHom g] [LiftHom h] [BicategoricalCoherence g h]
    (η : f ⟶ g) (θ : h ⟶ i) : f ⟶ i :=
  η ≫ BicategoricalCoherence.hom g h ≫ θ
#align category_theory.bicategory.bicategorical_comp CategoryTheory.Bicategory.bicategoricalComp

-- mathport name: bicategorical_comp
scoped[CategoryTheory.Bicategory] infixr:80 " ⊗≫ " =>
  CategoryTheory.Bicategory.bicategoricalComp

-- type as \ot \gg
/-- Compose two isomorphisms in a bicategorical category,
inserting unitors and associators between as necessary. -/
def bicategoricalIsoComp {f g h i : a ⟶ b} [LiftHom g] [LiftHom h] [BicategoricalCoherence g h]
    (η : f ≅ g) (θ : h ≅ i) : f ≅ i :=
  η ≪≫ asIso (BicategoricalCoherence.hom g h) ≪≫ θ
#align category_theory.bicategory.bicategorical_iso_comp CategoryTheory.Bicategory.bicategoricalIsoComp

-- mathport name: bicategorical_iso_comp
scoped[CategoryTheory.Bicategory] infixr:80 " ≪⊗≫ " =>
  CategoryTheory.Bicategory.bicategoricalIsoComp

-- type as \ot \gg
example {f' : a ⟶ d} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {h' : a ⟶ d} (η : f' ⟶ f ≫ g ≫ h)
    (θ : (f ≫ g) ≫ h ⟶ h') : f' ⟶ h' :=
    η ⊗≫ θ

-- To automatically insert unitors/associators at the beginning or end,
-- you can use `η ⊗≫ 𝟙 _`
example {f' : a ⟶ d} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} (η : f' ⟶ (f ≫ g) ≫ h) :
    f' ⟶ f ≫ g ≫ h :=
  η ⊗≫ 𝟙 _

@[simp]
theorem bicategoricalComp_refl {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) : η ⊗≫ θ = η ≫ θ := by
  dsimp [bicategoricalComp]; simp
#align category_theory.bicategory.bicategorical_comp_refl CategoryTheory.Bicategory.bicategoricalComp_refl

end CategoryTheory.Bicategory

open CategoryTheory.Bicategory

namespace Tactic

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34:
  unsupported: setup_tactic_parser -/
/- ./././Mathport/Syntax/Translate/Expr.lean:330:4: warning: unsupported (TODO): `[tacs] -/
-- failed to format: unknown constant 'term.pseudo.antiquot'
/-- Coherence tactic for bicategories. -/ unsafe
  def
    bicategorical_coherence
    : tactic Unit
    :=
      focus1
        do
          let o ← get_options
            set_options <| o `class.instance_max_depth 128
            try sorry
            let q( $ ( lhs ) = $ ( rhs ) ) ← target
            to_expr
                `
                  `(
                    ( FreeBicategory.lift ( Prefunctor.id _ ) ) . zipWith
                        ( LiftHom₂.lift $ ( lhs ) )
                      =
                      ( FreeBicategory.lift ( Prefunctor.id _ ) ) . zipWith
                        ( LiftHom₂.lift $ ( rhs ) )
                    )
              >>=
              tactic.change
            congr
#align tactic.bicategorical_coherence tactic.bicategorical_coherence

namespace Bicategory

/- ./././Mathport/Syntax/Translate/Expr.lean:330:4: warning: unsupported (TODO): `[tacs] -/
/-- Simp lemmas for rewriting a 2-morphism into a normal form. -/
unsafe def whisker_simps : tactic Unit :=
  sorry
#align tactic.bicategory.whisker_simps tactic.bicategory.whisker_simps

namespace Coherence

-- We have unused typeclass arguments here.
-- They are intentional, to ensure that `simp only [assoc_liftHom₂]` only left associates
-- bicategorical structural morphisms.
/-- Auxiliary simp lemma for the `coherence` tactic:
this move brackets to the left in order to expose a maximal prefix
built out of unitors and associators.
-/
@[nolint unusedArguments]
theorem assoc_liftHom₂ {f g h i : a ⟶ b} [LiftHom f] [LiftHom g] [LiftHom h] (η : f ⟶ g) (θ : g ⟶ h)
    (ι : h ⟶ i) [LiftHom₂ η] [LiftHom₂ θ] : η ≫ θ ≫ ι = (η ≫ θ) ≫ ι :=
  (Category.assoc _ _ _).symm
#align tactic.bicategory.coherence.assoc_lift_hom₂ Tactic.Bicategory.Coherence.assoc_liftHom₂

end Coherence

end Bicategory

end Tactic
