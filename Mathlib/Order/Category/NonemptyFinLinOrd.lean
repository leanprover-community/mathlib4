/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module order.category.NonemptyFinLinOrd
! leanprover-community/mathlib commit e8ac6315bcfcbaf2d19a046719c3b553206dac75
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Order
import Mathbin.Data.Set.Finite
import Mathbin.Order.Category.LinOrd
import Mathbin.CategoryTheory.Limits.Shapes.Images
import Mathbin.CategoryTheory.Limits.Shapes.RegularMono

/-!
# Nonempty finite linear orders

This defines `NonemptyFinLinOrd`, the category of nonempty finite linear orders with monotone maps.
This is the index category for simplicial objects.
-/


universe u v

open CategoryTheory CategoryTheory.Limits

/-- A typeclass for nonempty finite linear orders. -/
class NonemptyFinLinOrd (α : Type _) extends Fintype α, LinearOrder α where
  Nonempty : Nonempty α := by infer_instance
#align nonempty_fin_lin_ord NonemptyFinLinOrd

attribute [instance] NonemptyFinLinOrd.nonempty

instance (priority := 100) NonemptyFinLinOrd.toBoundedOrder (α : Type _) [NonemptyFinLinOrd α] :
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

instance (α : Type _) [NonemptyFinLinOrd α] : NonemptyFinLinOrd αᵒᵈ :=
  { OrderDual.fintype α with }

/-- The category of nonempty finite linear orders. -/
def NonemptyFinLinOrdCat :=
  Bundled NonemptyFinLinOrd
#align NonemptyFinLinOrd NonemptyFinLinOrdCat

namespace NonemptyFinLinOrdCat

instance : BundledHom.ParentProjection @NonemptyFinLinOrd.toLinearOrder :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for NonemptyFinLinOrdCat

instance : CoeSort NonemptyFinLinOrdCat (Type _) :=
  Bundled.hasCoeToSort

/-- Construct a bundled `NonemptyFinLinOrd` from the underlying type and typeclass. -/
def of (α : Type _) [NonemptyFinLinOrd α] : NonemptyFinLinOrdCat :=
  Bundled.of α
#align NonemptyFinLinOrd.of NonemptyFinLinOrdCat.of

@[simp]
theorem coe_of (α : Type _) [NonemptyFinLinOrd α] : ↥(of α) = α :=
  rfl
#align NonemptyFinLinOrd.coe_of NonemptyFinLinOrdCat.coe_of

instance : Inhabited NonemptyFinLinOrdCat :=
  ⟨of PUnit⟩

instance (α : NonemptyFinLinOrdCat) : NonemptyFinLinOrd α :=
  α.str

instance hasForgetToLinOrd : HasForget₂ NonemptyFinLinOrdCat LinOrd :=
  BundledHom.forget₂ _ _
#align NonemptyFinLinOrd.has_forget_to_LinOrd NonemptyFinLinOrdCat.hasForgetToLinOrd

/-- Constructs an equivalence between nonempty finite linear orders from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : NonemptyFinLinOrdCat.{u}} (e : α ≃o β) : α ≅ β
    where
  hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply x
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply x
#align NonemptyFinLinOrd.iso.mk NonemptyFinLinOrdCat.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : NonemptyFinLinOrdCat ⥤ NonemptyFinLinOrdCat
    where
  obj X := of Xᵒᵈ
  map X Y := OrderHom.dual
#align NonemptyFinLinOrd.dual NonemptyFinLinOrdCat.dual

/-- The equivalence between `FinPartOrd` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : NonemptyFinLinOrdCat ≌ NonemptyFinLinOrdCat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align NonemptyFinLinOrd.dual_equiv NonemptyFinLinOrdCat.dualEquiv

theorem mono_iff_injective {A B : NonemptyFinLinOrdCat.{u}} (f : A ⟶ B) :
    Mono f ↔ Function.Injective f :=
  by
  refine' ⟨_, concrete_category.mono_of_injective f⟩
  intro
  intro a₁ a₂ h
  let X : NonemptyFinLinOrdCat.{u} := ⟨ULift (Fin 1)⟩
  let g₁ : X ⟶ A := ⟨fun x => a₁, fun x₁ x₂ h => by rfl⟩
  let g₂ : X ⟶ A := ⟨fun x => a₂, fun x₁ x₂ h => by rfl⟩
  change g₁ (ULift.up (0 : Fin 1)) = g₂ (ULift.up (0 : Fin 1))
  have eq : g₁ ≫ f = g₂ ≫ f := by
    ext x
    exact h
  rw [cancel_mono] at eq
  rw [Eq]
#align NonemptyFinLinOrd.mono_iff_injective NonemptyFinLinOrdCat.mono_iff_injective

theorem epi_iff_surjective {A B : NonemptyFinLinOrdCat.{u}} (f : A ⟶ B) :
    Epi f ↔ Function.Surjective f := by
  constructor
  · intro
    by_contra' hf'
    rcases hf' with ⟨m, hm⟩
    let Y : NonemptyFinLinOrdCat.{u} := ⟨ULift (Fin 2)⟩
    let p₁ : B ⟶ Y :=
      ⟨fun b => if b < m then ULift.up 0 else ULift.up 1, fun x₁ x₂ h =>
        by
        simp only
        split_ifs with h₁ h₂ h₂
        any_goals apply Fin.zero_le
        · exfalso
          exact h₁ (lt_of_le_of_lt h h₂)
        · rfl⟩
    let p₂ : B ⟶ Y :=
      ⟨fun b => if b ≤ m then ULift.up 0 else ULift.up 1, fun x₁ x₂ h =>
        by
        simp only
        split_ifs with h₁ h₂ h₂
        any_goals apply Fin.zero_le
        · exfalso
          exact h₁ (h.trans h₂)
        · rfl⟩
    have h : p₁ m = p₂ m := by
      congr
      rw [← cancel_epi f]
      ext a : 2
      simp only [comp_apply, OrderHom.coe_fun_mk]
      split_ifs with h₁ h₂ h₂
      any_goals rfl
      · exfalso
        exact h₂ (le_of_lt h₁)
      · exfalso
        exact hm a (eq_of_le_of_not_lt h₂ h₁)
    simpa only [OrderHom.coe_fun_mk, lt_self_iff_false, if_false, le_refl, if_true, ULift.up_inj,
      Fin.one_eq_zero_iff, Nat.succ_succ_ne_one] using h
  · intro h
    exact concrete_category.epi_of_surjective f h
#align NonemptyFinLinOrd.epi_iff_surjective NonemptyFinLinOrdCat.epi_iff_surjective

instance : SplitEpiCategory NonemptyFinLinOrdCat.{u} :=
  ⟨fun X Y f hf =>
    by
    have H : ∀ y : Y, Nonempty (f ⁻¹' {y}) :=
      by
      rw [epi_iff_surjective] at hf
      intro y
      exact Nonempty.intro ⟨(hf y).some, (hf y).choose_spec⟩
    let φ : Y → X := fun y => (H y).some.1
    have hφ : ∀ y : Y, f (φ y) = y := fun y => (H y).some.2
    refine' is_split_epi.mk' ⟨⟨φ, _⟩, _⟩
    swap
    · ext b
      apply hφ
    · intro a b
      contrapose
      intro h
      simp only [not_le] at h⊢
      suffices b ≤ a by
        apply lt_of_le_of_ne this
        intro h'
        exfalso
        simpa only [h', lt_self_iff_false] using h
      simpa only [hφ] using f.monotone (le_of_lt h)⟩

instance : HasStrongEpiMonoFactorisations NonemptyFinLinOrdCat.{u} :=
  ⟨fun X Y f => by
    let I : NonemptyFinLinOrdCat.{u} := ⟨Set.image (coeFn f) ⊤, ⟨⟩⟩
    let e : X ⟶ I := ⟨fun x => ⟨f x, ⟨x, by tidy⟩⟩, fun x₁ x₂ h => f.monotone h⟩
    let m : I ⟶ Y := ⟨fun y => y, by tidy⟩
    haveI : epi e := by
      rw [epi_iff_surjective]
      tidy
    haveI : strong_epi e := strong_epi_of_epi e
    haveI : mono m := concrete_category.mono_of_injective _ (by tidy)
    exact
      Nonempty.intro
        { i
          m
          e }⟩

end NonemptyFinLinOrdCat

theorem nonemptyFinLinOrdCat_dual_comp_forget_to_linOrd :
    NonemptyFinLinOrdCat.dual ⋙ forget₂ NonemptyFinLinOrdCat LinOrd =
      forget₂ NonemptyFinLinOrdCat LinOrd ⋙ LinOrd.dual :=
  rfl
#align NonemptyFinLinOrd_dual_comp_forget_to_LinOrd nonemptyFinLinOrdCat_dual_comp_forget_to_linOrd

