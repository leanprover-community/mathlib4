/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Set.Subsingleton
import Mathlib.Order.Category.FinPartOrd
import Mathlib.Order.Category.LinOrd

/-!
# Nonempty finite linear orders

This defines `NonemptyFinLinOrd`, the category of nonempty finite linear
orders with monotone maps. This is the index category for simplicial objects.

Note: `NonemptyFinLinOrd` is *not* a subcategory of `FinBddDistLat` because its morphisms do not
preserve `⊥` and `⊤`.
-/

universe u v

open CategoryTheory CategoryTheory.Limits

/-- The category of nonempty finite linear orders. -/
structure NonemptyFinLinOrd extends LinOrd where
  [nonempty : Nonempty carrier]
  [fintype : Fintype carrier]

attribute [instance] NonemptyFinLinOrd.nonempty NonemptyFinLinOrd.fintype

namespace NonemptyFinLinOrd

instance : CoeSort NonemptyFinLinOrd (Type _) where
  coe X := X.carrier

instance : LargeCategory NonemptyFinLinOrd :=
  inferInstanceAs (Category (InducedCategory _ NonemptyFinLinOrd.toLinOrd))

instance : ConcreteCategory NonemptyFinLinOrd (· →o ·) :=
  InducedCategory.concreteCategory NonemptyFinLinOrd.toLinOrd

instance (X : NonemptyFinLinOrd) : BoundedOrder X :=
    Fintype.toBoundedOrder X

/-- Construct a bundled `NonemptyFinLinOrd` from the underlying type and typeclass. -/
abbrev of (α : Type*) [Nonempty α] [Fintype α] [LinearOrder α] : NonemptyFinLinOrd where
  carrier := α

theorem coe_of (α : Type*) [Nonempty α] [Fintype α] [LinearOrder α] : ↥(of α) = α :=
  rfl

/-- Typecheck a `OrderHom` as a morphism in `NonemptyFinLinOrd`. -/
abbrev ofHom {X Y : Type u} [Nonempty X] [LinearOrder X] [Fintype X]
    [Nonempty Y] [LinearOrder Y] [Fintype Y] (f : X →o Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := NonemptyFinLinOrd) f

@[simp]
lemma hom_hom_id {X : NonemptyFinLinOrd} : (𝟙 X : X ⟶ X).hom.hom = OrderHom.id := rfl

@[deprecated (since := "2025-07-05")] alias hom_id := hom_hom_id

/- Provided for rewriting. -/
lemma id_apply (X : NonemptyFinLinOrd) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
lemma hom_hom_comp {X Y Z : NonemptyFinLinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom.hom = g.hom.hom.comp f.hom.hom := rfl

@[deprecated (since := "2025-07-05")] alias hom_comp := hom_hom_comp

/- Provided for rewriting. -/
lemma comp_apply {X Y Z : NonemptyFinLinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
lemma hom_ext {X Y : NonemptyFinLinOrd} {f g : X ⟶ Y} (hf : f.hom.hom = g.hom.hom) : f = g :=
  InducedCategory.hom_ext (ConcreteCategory.ext hf)

@[simp]
lemma hom_hom_ofHom {X Y : Type u} [Nonempty X] [LinearOrder X] [Fintype X] [Nonempty Y]
    [LinearOrder Y] [Fintype Y] (f : X →o Y) :
  (ofHom f).hom.hom = f := rfl

@[deprecated (since := "2025-07-05")] alias hom_ofHom := hom_hom_ofHom

@[simp]
lemma ofHom_hom {X Y : NonemptyFinLinOrd} (f : X ⟶ Y) :
    ofHom f.hom.hom = f := rfl

instance : Inhabited NonemptyFinLinOrd :=
  ⟨of PUnit⟩

instance hasForgetToLinOrd : HasForget₂ NonemptyFinLinOrd LinOrd :=
  InducedCategory.hasForget₂ _

instance hasForgetToFinPartOrd : HasForget₂ NonemptyFinLinOrd FinPartOrd where
  forget₂.obj X := .of X
  forget₂.map f := FinPartOrd.ofHom f.hom.hom

/-- Constructs an equivalence between nonempty finite linear orders from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : NonemptyFinLinOrd.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
def dual : NonemptyFinLinOrd ⥤ NonemptyFinLinOrd where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.hom.dual

/-- The equivalence between `NonemptyFinLinOrd` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : NonemptyFinLinOrd ≌ NonemptyFinLinOrd where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

theorem mono_iff_injective {A B : NonemptyFinLinOrd.{u}} (f : A ⟶ B) :
    Mono f ↔ Function.Injective f := by
  refine ⟨?_, ConcreteCategory.mono_of_injective f⟩
  intro _ a₁ a₂ h
  let X := of (ULift (Fin 1))
  let g₁ : X ⟶ A := ofHom ⟨fun _ => a₁, fun _ _ _ => by rfl⟩
  let g₂ : X ⟶ A := ofHom ⟨fun _ => a₂, fun _ _ _ => by rfl⟩
  change g₁ (ULift.up (0 : Fin 1)) = g₂ (ULift.up (0 : Fin 1))
  have eq : g₁ ≫ f = g₂ ≫ f := by
    ext
    exact h
  rw [cancel_mono] at eq
  rw [eq]

theorem epi_iff_surjective {A B : NonemptyFinLinOrd.{u}} (f : A ⟶ B) :
    Epi f ↔ Function.Surjective f := by
  constructor
  · intro
    dsimp only [Function.Surjective]
    by_contra! hf'
    rcases hf' with ⟨m, hm⟩
    let Y := of (ULift (Fin 2))
    let p₁ : B ⟶ Y := ofHom
      ⟨fun b => if b < m then ULift.up 0 else ULift.up 1, fun x₁ x₂ h => by
        simp only
        split_ifs with h₁ h₂ h₂
        any_goals apply Fin.zero_le
        · exfalso
          exact h₁ (lt_of_le_of_lt h h₂)
        · rfl⟩
    let p₂ : B ⟶ Y := ofHom
      ⟨fun b => if b ≤ m then ULift.up 0 else ULift.up 1, fun x₁ x₂ h => by
        simp only
        split_ifs with h₁ h₂ h₂
        any_goals apply Fin.zero_le
        · exfalso
          exact h₁ (h.trans h₂)
        · rfl⟩
    have h : p₁ m = p₂ m := by
      congr
      rw [← cancel_epi f]
      ext a : 3
      simp only [p₁, p₂, hom_hom_comp, OrderHom.comp_coe, Function.comp_apply, hom_hom_ofHom]
      change ite _ _ _ = ite _ _ _
      split_ifs with h₁ h₂ h₂
      any_goals rfl
      · exfalso
        exact h₂ (le_of_lt h₁)
      · exfalso
        exact hm a (eq_of_le_of_not_lt h₂ h₁)
    simp [Y, p₁, p₂, ConcreteCategory.hom_ofHom] at h
  · intro h
    exact ConcreteCategory.epi_of_surjective f h

instance : SplitEpiCategory NonemptyFinLinOrd.{u} :=
  ⟨fun {X Y} f hf => by
    have H : ∀ y : Y, Nonempty (f ⁻¹' {y}) := by
      rw [epi_iff_surjective] at hf
      intro y
      exact Nonempty.intro ⟨(hf y).choose, (hf y).choose_spec⟩
    let φ : Y → X := fun y => (H y).some.1
    have hφ : ∀ y : Y, f (φ y) = y := fun y => (H y).some.2
    refine IsSplitEpi.mk' ⟨ofHom ⟨φ, ?_⟩, ?_⟩
    swap
    · ext b
      apply hφ
    · intro a b
      contrapose
      intro h
      simp only [not_le] at h ⊢
      suffices b ≤ a by
        apply lt_of_le_of_ne this
        rintro rfl
        exfalso
        simp at h
      have H : f (φ b) ≤ f (φ a) := f.hom.hom.monotone (le_of_lt h)
      simpa only [hφ] using H⟩

instance : HasStrongEpiMonoFactorisations NonemptyFinLinOrd.{u} :=
  ⟨fun {X Y} f => by
    let I := of (Set.image f ⊤)
    let e : X ⟶ I := ofHom ⟨fun x => ⟨f x, ⟨x, by tauto⟩⟩, fun x₁ x₂ h => f.hom.hom.monotone h⟩
    let m : I ⟶ Y := ofHom ⟨fun y => y.1, by tauto⟩
    haveI : Epi e := by
      rw [epi_iff_surjective]
      rintro ⟨_, y, h, rfl⟩
      exact ⟨y, rfl⟩
    haveI : StrongEpi e := strongEpi_of_epi e
    haveI : Mono m := ConcreteCategory.mono_of_injective _ (fun x y h => Subtype.ext h)
    exact ⟨⟨I, m, e, rfl⟩⟩⟩

end NonemptyFinLinOrd

theorem nonemptyFinLinOrd_dual_comp_forget_to_linOrd :
    NonemptyFinLinOrd.dual ⋙ forget₂ NonemptyFinLinOrd LinOrd =
      forget₂ NonemptyFinLinOrd LinOrd ⋙ LinOrd.dual :=
  rfl

/-- The forgetful functor `NonemptyFinLinOrd ⥤ FinPartOrd` and `OrderDual` commute. -/
def nonemptyFinLinOrdDualCompForgetToFinPartOrd :
    NonemptyFinLinOrd.dual ⋙ forget₂ NonemptyFinLinOrd FinPartOrd ≅
      forget₂ NonemptyFinLinOrd FinPartOrd ⋙ FinPartOrd.dual where
  hom.app X := FinPartOrd.ofHom OrderHom.id
  inv.app X := FinPartOrd.ofHom OrderHom.id

/-- The generating arrow `i ⟶ i+1` in the category `Fin n` -/
def Fin.hom_succ {n} (i : Fin n) : i.castSucc ⟶ i.succ := homOfLE (Fin.castSucc_le_succ i)
