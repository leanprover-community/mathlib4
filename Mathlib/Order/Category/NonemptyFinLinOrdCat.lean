/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Set.Finite
import Mathlib.Order.Category.FinPartOrd
import Mathlib.Order.Category.LinOrdCat
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

#align_import order.category.NonemptyFinLinOrd from "leanprover-community/mathlib"@"fa4a805d16a9cd9c96e0f8edeb57dc5a07af1a19"

/-!
# Nonempty finite linear orders

This defines `NonemptyFinLinOrdCat`, the category of nonempty finite linear
orders with monotone maps. This is the index category for simplicial objects.

Note: `NonemptyFinLinOrd` is *not* a subcategory of `FinBddDistLat` because its morphisms do not
preserve `⊥` and `⊤`.
-/


universe u v

open CategoryTheory CategoryTheory.Limits

/-- A typeclass for nonempty finite linear orders. -/
class NonemptyFinLinOrd (α : Type*) extends Fintype α, LinearOrder α where
  Nonempty : Nonempty α := by infer_instance
#align nonempty_fin_lin_ord NonemptyFinLinOrd

attribute [instance] NonemptyFinLinOrd.Nonempty

instance (priority := 100) NonemptyFinLinOrd.toBoundedOrder (α : Type*) [NonemptyFinLinOrd α] :
    BoundedOrder α :=
  Fintype.toBoundedOrder α
#align nonempty_fin_lin_ord.to_bounded_order NonemptyFinLinOrd.toBoundedOrder

instance PUnit.nonemptyFinLinOrd : NonemptyFinLinOrd PUnit where
#align punit.nonempty_fin_lin_ord PUnit.nonemptyFinLinOrd

instance Fin.nonemptyFinLinOrd (n : ℕ) : NonemptyFinLinOrd (Fin (n + 1)) where
#align fin.nonempty_fin_lin_ord Fin.nonemptyFinLinOrd

instance ULift.nonemptyFinLinOrd (α : Type u) [NonemptyFinLinOrd α] :
    NonemptyFinLinOrd (ULift.{v} α) :=
  { LinearOrder.lift' Equiv.ulift (Equiv.injective _) with }
#align ulift.nonempty_fin_lin_ord ULift.nonemptyFinLinOrd

instance (α : Type*) [NonemptyFinLinOrd α] : NonemptyFinLinOrd αᵒᵈ :=
  { OrderDual.fintype α with }

/-- The category of nonempty finite linear orders. -/
def NonemptyFinLinOrdCat :=
  Bundled NonemptyFinLinOrd
set_option linter.uppercaseLean3 false in
#align NonemptyFinLinOrd NonemptyFinLinOrdCat

namespace NonemptyFinLinOrdCat

instance : BundledHom.ParentProjection @NonemptyFinLinOrd.toLinearOrder :=
  ⟨⟩

deriving instance LargeCategory for NonemptyFinLinOrdCat

-- Porting note: probably see https://github.com/leanprover-community/mathlib4/issues/5020
instance : ConcreteCategory NonemptyFinLinOrdCat :=
  BundledHom.concreteCategory _

instance : CoeSort NonemptyFinLinOrdCat (Type*) :=
  Bundled.coeSort

/-- Construct a bundled `NonemptyFinLinOrdCat` from the underlying type and typeclass. -/
def of (α : Type*) [NonemptyFinLinOrd α] : NonemptyFinLinOrdCat :=
  Bundled.of α
set_option linter.uppercaseLean3 false in
#align NonemptyFinLinOrd.of NonemptyFinLinOrdCat.of

@[simp]
theorem coe_of (α : Type*) [NonemptyFinLinOrd α] : ↥(of α) = α :=
  rfl
set_option linter.uppercaseLean3 false in
#align NonemptyFinLinOrd.coe_of NonemptyFinLinOrdCat.coe_of

instance : Inhabited NonemptyFinLinOrdCat :=
  ⟨of PUnit⟩

instance (α : NonemptyFinLinOrdCat) : NonemptyFinLinOrd α :=
  α.str

instance hasForgetToLinOrd : HasForget₂ NonemptyFinLinOrdCat LinOrdCat :=
  BundledHom.forget₂ _ _
set_option linter.uppercaseLean3 false in
#align NonemptyFinLinOrd.has_forget_to_LinOrd NonemptyFinLinOrdCat.hasForgetToLinOrd

instance hasForgetToFinPartOrd : HasForget₂ NonemptyFinLinOrdCat FinPartOrd
    where forget₂ :=
    { obj := fun X => FinPartOrd.of X
      map := @fun X Y => id }
set_option linter.uppercaseLean3 false in
#align NonemptyFinLinOrd.has_forget_to_FinPartOrd NonemptyFinLinOrdCat.hasForgetToFinPartOrd

/-- Constructs an equivalence between nonempty finite linear orders from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : NonemptyFinLinOrdCat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : OrderHom _ _)
  inv := (e.symm : OrderHom _ _)
  hom_inv_id := by
    ext x
    -- ⊢ ↑(↑e ≫ ↑(OrderIso.symm e)) x = ↑(𝟙 α) x
    exact e.symm_apply_apply x
    -- 🎉 no goals
  inv_hom_id := by
    ext x
    -- ⊢ ↑(↑(OrderIso.symm e) ≫ ↑e) x = ↑(𝟙 β) x
    exact e.apply_symm_apply x
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align NonemptyFinLinOrd.iso.mk NonemptyFinLinOrdCat.Iso.mk

/-- `OrderDual` as a functor. -/
@[simps]
def dual : NonemptyFinLinOrdCat ⥤ NonemptyFinLinOrdCat where
  obj X := of Xᵒᵈ
  map := OrderHom.dual
set_option linter.uppercaseLean3 false in
#align NonemptyFinLinOrd.dual NonemptyFinLinOrdCat.dual

/-- The equivalence between `NonemptyFinLinOrdCat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : NonemptyFinLinOrdCat ≌ NonemptyFinLinOrdCat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
set_option linter.uppercaseLean3 false in
#align NonemptyFinLinOrd.dual_equiv NonemptyFinLinOrdCat.dualEquiv

-- porting note: this instance was not necessary in mathlib
instance {A B : NonemptyFinLinOrdCat.{u}} : OrderHomClass (A ⟶ B) A B where
  coe f := ⇑(show OrderHom A B from f)
  coe_injective' _ _ h := by
    ext x
    -- ⊢ ↑x✝¹ x = ↑x✝ x
    exact congr_fun h x
    -- 🎉 no goals
  map_rel f _ _ h := f.monotone h

theorem mono_iff_injective {A B : NonemptyFinLinOrdCat.{u}} (f : A ⟶ B) :
    Mono f ↔ Function.Injective f := by
  refine' ⟨_, ConcreteCategory.mono_of_injective f⟩
  -- ⊢ Mono f → Function.Injective ↑f
  intro
  -- ⊢ Function.Injective ↑f
  intro a₁ a₂ h
  -- ⊢ a₁ = a₂
  let X := NonemptyFinLinOrdCat.of (ULift (Fin 1))
  -- ⊢ a₁ = a₂
  let g₁ : X ⟶ A := ⟨fun _ => a₁, fun _ _ _ => by rfl⟩
  -- ⊢ a₁ = a₂
  let g₂ : X ⟶ A := ⟨fun _ => a₂, fun _ _ _ => by rfl⟩
  -- ⊢ a₁ = a₂
  change g₁ (ULift.up (0 : Fin 1)) = g₂ (ULift.up (0 : Fin 1))
  -- ⊢ ↑g₁ { down := 0 } = ↑g₂ { down := 0 }
  have eq : g₁ ≫ f = g₂ ≫ f := by
    ext
    exact h
  rw [cancel_mono] at eq
  -- ⊢ ↑g₁ { down := 0 } = ↑g₂ { down := 0 }
  rw [eq]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align NonemptyFinLinOrd.mono_iff_injective NonemptyFinLinOrdCat.mono_iff_injective

-- porting note: added to ease the following proof
lemma forget_map_apply {A B : NonemptyFinLinOrdCat.{u}} (f : A ⟶ B) (a : A) :
  (forget NonemptyFinLinOrdCat).map f a = (f : OrderHom A B).toFun a := rfl

theorem epi_iff_surjective {A B : NonemptyFinLinOrdCat.{u}} (f : A ⟶ B) :
    Epi f ↔ Function.Surjective f := by
  constructor
  -- ⊢ Epi f → Function.Surjective ↑f
  · intro
    -- ⊢ Function.Surjective ↑f
    dsimp only [Function.Surjective]
    -- ⊢ ∀ (b : ↑B), ∃ a, ↑f a = b
    by_contra' hf'
    -- ⊢ False
    rcases hf' with ⟨m, hm⟩
    -- ⊢ False
    let Y := NonemptyFinLinOrdCat.of (ULift (Fin 2))
    -- ⊢ False
    let p₁ : B ⟶ Y :=
      ⟨fun b => if b < m then ULift.up 0 else ULift.up 1, fun x₁ x₂ h => by
        simp only
        split_ifs with h₁ h₂ h₂
        any_goals apply Fin.zero_le
        · exfalso
          exact h₁ (lt_of_le_of_lt h h₂)
        · rfl⟩
    let p₂ : B ⟶ Y :=
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
      ext a
      simp only [coe_of, comp_apply]
      change ite _ _ _ = ite _ _ _
      split_ifs with h₁ h₂ h₂
      any_goals rfl
      · exfalso
        exact h₂ (le_of_lt h₁)
      · exfalso
        exact hm a (eq_of_le_of_not_lt h₂ h₁)
    simp [FunLike.coe] at h
    -- 🎉 no goals
  · intro h
    -- ⊢ Epi f
    exact ConcreteCategory.epi_of_surjective f h
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align NonemptyFinLinOrd.epi_iff_surjective NonemptyFinLinOrdCat.epi_iff_surjective

instance : SplitEpiCategory NonemptyFinLinOrdCat.{u} :=
  ⟨fun {X Y} f hf => by
    have H : ∀ y : Y, Nonempty (f ⁻¹' {y}) := by
      rw [epi_iff_surjective] at hf
      intro y
      exact Nonempty.intro ⟨(hf y).choose, (hf y).choose_spec⟩
    let φ : Y → X := fun y => (H y).some.1
    -- ⊢ IsSplitEpi f
    have hφ : ∀ y : Y, f (φ y) = y := fun y => (H y).some.2
    -- ⊢ IsSplitEpi f
    refine' IsSplitEpi.mk' ⟨⟨φ, _⟩, _⟩
    -- ⊢ Monotone φ
    swap
    -- ⊢ { toFun := φ, monotone' := ?refine'_1 } ≫ f = 𝟙 Y
    · ext b
      -- ⊢ ↑({ toFun := φ, monotone' := ?refine'_1 } ≫ f) b = ↑(𝟙 Y) b
      apply hφ
      -- 🎉 no goals
    · intro a b
      -- ⊢ a ≤ b → φ a ≤ φ b
      contrapose
      -- ⊢ ¬φ a ≤ φ b → ¬a ≤ b
      intro h
      -- ⊢ ¬a ≤ b
      simp only [not_le] at h ⊢
      -- ⊢ b < a
      suffices b ≤ a by
        apply lt_of_le_of_ne this
        rintro rfl
        exfalso
        simp at h
      have H : f (φ b) ≤ f (φ a) := f.monotone (le_of_lt h)
      -- ⊢ b ≤ a
      simpa only [hφ] using H⟩
      -- 🎉 no goals

instance : HasStrongEpiMonoFactorisations NonemptyFinLinOrdCat.{u} :=
  ⟨fun {X Y} f => by
    letI : NonemptyFinLinOrd (Set.image f ⊤) := ⟨by infer_instance⟩
    -- ⊢ Nonempty (StrongEpiMonoFactorisation f)
    let I := NonemptyFinLinOrdCat.of (Set.image f ⊤)
    -- ⊢ Nonempty (StrongEpiMonoFactorisation f)
    let e : X ⟶ I := ⟨fun x => ⟨f x, ⟨x, by tauto⟩⟩, fun x₁ x₂ h => f.monotone h⟩
    -- ⊢ Nonempty (StrongEpiMonoFactorisation f)
    let m : I ⟶ Y := ⟨fun y => y.1, by tauto⟩
    -- ⊢ Nonempty (StrongEpiMonoFactorisation f)
    haveI : Epi e := by
      rw [epi_iff_surjective]
      rintro ⟨_, y, h, rfl⟩
      exact ⟨y, rfl⟩
    haveI : StrongEpi e := strongEpi_of_epi e
    -- ⊢ Nonempty (StrongEpiMonoFactorisation f)
    haveI : Mono m := ConcreteCategory.mono_of_injective _ (fun x y h => Subtype.ext h)
    -- ⊢ Nonempty (StrongEpiMonoFactorisation f)
    exact ⟨⟨I, m, e, rfl⟩⟩⟩
    -- 🎉 no goals

end NonemptyFinLinOrdCat

theorem nonemptyFinLinOrdCat_dual_comp_forget_to_linOrdCat :
    NonemptyFinLinOrdCat.dual ⋙ forget₂ NonemptyFinLinOrdCat LinOrdCat =
      forget₂ NonemptyFinLinOrdCat LinOrdCat ⋙ LinOrdCat.dual :=
  rfl
set_option linter.uppercaseLean3 false in
#align NonemptyFinLinOrd_dual_comp_forget_to_LinOrd nonemptyFinLinOrdCat_dual_comp_forget_to_linOrdCat

/-- The forgetful functor `NonemptyFinLinOrd ⥤ FinPartOrd` and `order_dual` commute. -/
def nonemptyFinLinOrdDualCompForgetToFinPartOrd :
    NonemptyFinLinOrdCat.dual ⋙ forget₂ NonemptyFinLinOrdCat FinPartOrd ≅
      forget₂ NonemptyFinLinOrdCat FinPartOrd ⋙ FinPartOrd.dual
    where
  hom := { app := fun X => OrderHom.id }
  inv := { app := fun X => OrderHom.id }
set_option linter.uppercaseLean3 false in
#align NonemptyFinLinOrd_dual_comp_forget_to_FinPartOrd nonemptyFinLinOrdDualCompForgetToFinPartOrd
