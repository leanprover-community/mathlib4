/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.Data.Subtype
import Mathlib.Data.Sum.Basic
import Mathlib.Init.Data.Sigma.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Conjugate

#align_import logic.equiv.basic from "leanprover-community/mathlib"@"cd391184c85986113f8c00844cfe6dda1d34be3d"

/-!
# Equivalence between types

In this file we continue the work on equivalences begun in `Logic/Equiv/Defs.lean`, defining

* canonical isomorphisms between various types: e.g.,

  - `Equiv.sumEquivSigmaBool` is the canonical equivalence between the sum of two types `α ⊕ β`
    and the sigma-type `Σ b : Bool, cond b α β`;

  - `Equiv.prodSumDistrib : α × (β ⊕ γ) ≃ (α × β) ⊕ (α × γ)` shows that type product and type sum
    satisfy the distributive law up to a canonical equivalence;

* operations on equivalences: e.g.,

  - `Equiv.prodCongr ea eb : α₁ × β₁ ≃ α₂ × β₂`: combine two equivalences `ea : α₁ ≃ α₂` and
    `eb : β₁ ≃ β₂` using `Prod.map`.

  More definitions of this kind can be found in other files.
  E.g., `Data/Equiv/TransferInstance.lean` does it for many algebraic type classes like
  `Group`, `Module`, etc.

## Tags

equivalence, congruence, bijective map
-/

set_option autoImplicit true

open Function

namespace Equiv

/-- `PProd α β` is equivalent to `α × β` -/
@[simps apply symm_apply]
def pprodEquivProd : PProd α β ≃ α × β where
  toFun x := (x.1, x.2)
  invFun x := ⟨x.1, x.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
#align equiv.pprod_equiv_prod Equiv.pprodEquivProd
#align equiv.pprod_equiv_prod_apply Equiv.pprodEquivProd_apply
#align equiv.pprod_equiv_prod_symm_apply Equiv.pprodEquivProd_symm_apply

/-- Product of two equivalences, in terms of `PProd`. If `α ≃ β` and `γ ≃ δ`, then
`PProd α γ ≃ PProd β δ`. -/
-- porting note: in Lean 3 this had `@[congr]`
@[simps apply]
def pprodCongr (e₁ : α ≃ β) (e₂ : γ ≃ δ) : PProd α γ ≃ PProd β δ where
  toFun x := ⟨e₁ x.1, e₂ x.2⟩
  invFun x := ⟨e₁.symm x.1, e₂.symm x.2⟩
  left_inv := fun ⟨x, y⟩ => by simp
                               -- 🎉 no goals
  right_inv := fun ⟨x, y⟩ => by simp
                                -- 🎉 no goals
#align equiv.pprod_congr Equiv.pprodCongr
#align equiv.pprod_congr_apply Equiv.pprodCongr_apply

/-- Combine two equivalences using `PProd` in the domain and `Prod` in the codomain. -/
@[simps! apply symm_apply]
def pprodProd (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) :
    PProd α₁ β₁ ≃ α₂ × β₂ :=
  (ea.pprodCongr eb).trans pprodEquivProd
#align equiv.pprod_prod Equiv.pprodProd
#align equiv.pprod_prod_apply Equiv.pprodProd_apply
#align equiv.pprod_prod_symm_apply Equiv.pprodProd_symm_apply

/-- Combine two equivalences using `PProd` in the codomain and `Prod` in the domain. -/
@[simps! apply symm_apply]
def prodPProd (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) :
    α₁ × β₁ ≃ PProd α₂ β₂ :=
  (ea.symm.pprodProd eb.symm).symm
#align equiv.prod_pprod Equiv.prodPProd
#align equiv.prod_pprod_symm_apply Equiv.prodPProd_symm_apply
#align equiv.prod_pprod_apply Equiv.prodPProd_apply

/-- `PProd α β` is equivalent to `PLift α × PLift β` -/
@[simps! apply symm_apply]
def pprodEquivProdPLift : PProd α β ≃ PLift α × PLift β :=
  Equiv.plift.symm.pprodProd Equiv.plift.symm
#align equiv.pprod_equiv_prod_plift Equiv.pprodEquivProdPLift
#align equiv.pprod_equiv_prod_plift_symm_apply Equiv.pprodEquivProdPLift_symm_apply
#align equiv.pprod_equiv_prod_plift_apply Equiv.pprodEquivProdPLift_apply

/-- Product of two equivalences. If `α₁ ≃ α₂` and `β₁ ≃ β₂`, then `α₁ × β₁ ≃ α₂ × β₂`. This is
`Prod.map` as an equivalence. -/
-- porting note: in Lean 3 there was also a @[congr] tag
@[simps (config := .asFn) apply]
def prodCongr (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂ :=
  ⟨Prod.map e₁ e₂, Prod.map e₁.symm e₂.symm, fun ⟨a, b⟩ => by simp, fun ⟨a, b⟩ => by simp⟩
                                                              -- 🎉 no goals
                                                                                     -- 🎉 no goals
#align equiv.prod_congr Equiv.prodCongr
#align equiv.prod_congr_apply Equiv.prodCongr_apply

@[simp]
theorem prodCongr_symm (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (prodCongr e₁ e₂).symm = prodCongr e₁.symm e₂.symm :=
  rfl
#align equiv.prod_congr_symm Equiv.prodCongr_symm

/-- Type product is commutative up to an equivalence: `α × β ≃ β × α`. This is `Prod.swap` as an
equivalence.-/
def prodComm (α β) : α × β ≃ β × α :=
  ⟨Prod.swap, Prod.swap, Prod.swap_swap, Prod.swap_swap⟩
#align equiv.prod_comm Equiv.prodComm

@[simp]
theorem coe_prodComm (α β) : (⇑(prodComm α β) : α × β → β × α) = Prod.swap :=
  rfl
#align equiv.coe_prod_comm Equiv.coe_prodComm

@[simp]
theorem prodComm_apply (x : α × β) : prodComm α β x = x.swap :=
  rfl
#align equiv.prod_comm_apply Equiv.prodComm_apply

@[simp]
theorem prodComm_symm (α β) : (prodComm α β).symm = prodComm β α :=
  rfl
#align equiv.prod_comm_symm Equiv.prodComm_symm

/-- Type product is associative up to an equivalence. -/
@[simps]
def prodAssoc (α β γ) : (α × β) × γ ≃ α × β × γ :=
  ⟨fun p => (p.1.1, p.1.2, p.2), fun p => ((p.1, p.2.1), p.2.2), fun ⟨⟨_, _⟩, _⟩ => rfl,
    fun ⟨_, ⟨_, _⟩⟩ => rfl⟩
#align equiv.prod_assoc Equiv.prodAssoc
#align equiv.prod_assoc_symm_apply Equiv.prodAssoc_symm_apply
#align equiv.prod_assoc_apply Equiv.prodAssoc_apply

/-- Four-way commutativity of `prod`. The name matches `mul_mul_mul_comm`. -/
@[simps apply]
def prodProdProdComm (α β γ δ : Type*) : (α × β) × γ × δ ≃ (α × γ) × β × δ where
  toFun abcd := ((abcd.1.1, abcd.2.1), (abcd.1.2, abcd.2.2))
  invFun acbd := ((acbd.1.1, acbd.2.1), (acbd.1.2, acbd.2.2))
  left_inv := fun ⟨⟨_a, _b⟩, ⟨_c, _d⟩⟩ => rfl
  right_inv := fun ⟨⟨_a, _c⟩, ⟨_b, _d⟩⟩ => rfl
#align equiv.prod_prod_prod_comm Equiv.prodProdProdComm

@[simp]
theorem prodProdProdComm_symm (α β γ δ : Type*) :
    (prodProdProdComm α β γ δ).symm = prodProdProdComm α γ β δ :=
  rfl
#align equiv.prod_prod_prod_comm_symm Equiv.prodProdProdComm_symm

/-- `γ`-valued functions on `α × β` are equivalent to functions `α → β → γ`. -/
@[simps (config := { fullyApplied := false })]
def curry (α β γ) : (α × β → γ) ≃ (α → β → γ) where
  toFun := Function.curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry
#align equiv.curry Equiv.curry
#align equiv.curry_symm_apply Equiv.curry_symm_apply
#align equiv.curry_apply Equiv.curry_apply

section

/-- `PUnit` is a right identity for type product up to an equivalence. -/
@[simps]
def prodPUnit (α) : α × PUnit ≃ α :=
  ⟨fun p => p.1, fun a => (a, PUnit.unit), fun ⟨_, PUnit.unit⟩ => rfl, fun _ => rfl⟩
#align equiv.prod_punit Equiv.prodPUnit
#align equiv.prod_punit_apply Equiv.prodPUnit_apply
#align equiv.prod_punit_symm_apply Equiv.prodPUnit_symm_apply

/-- `PUnit` is a left identity for type product up to an equivalence. -/
@[simps!]
def punitProd (α) : PUnit × α ≃ α :=
  calc
    PUnit × α ≃ α × PUnit := prodComm _ _
    _ ≃ α := prodPUnit _
#align equiv.punit_prod Equiv.punitProd
#align equiv.punit_prod_symm_apply Equiv.punitProd_symm_apply
#align equiv.punit_prod_apply Equiv.punitProd_apply

/-- `PUnit` is a right identity for dependent type product up to an equivalence. -/
@[simps]
def sigmaPUnit (α) : (_ : α) × PUnit ≃ α :=
  ⟨fun p => p.1, fun a => ⟨a, PUnit.unit⟩, fun ⟨_, PUnit.unit⟩ => rfl, fun _ => rfl⟩

/-- Any `Unique` type is a right identity for type product up to equivalence. -/
def prodUnique (α β) [Unique β] : α × β ≃ α :=
  ((Equiv.refl α).prodCongr <| equivPUnit.{_,1} β).trans <| prodPUnit α
#align equiv.prod_unique Equiv.prodUnique

@[simp]
theorem coe_prodUnique [Unique β] : (⇑(prodUnique α β) : α × β → α) = Prod.fst :=
  rfl
#align equiv.coe_prod_unique Equiv.coe_prodUnique

theorem prodUnique_apply [Unique β] (x : α × β) : prodUnique α β x = x.1 :=
  rfl
#align equiv.prod_unique_apply Equiv.prodUnique_apply

@[simp]
theorem prodUnique_symm_apply [Unique β] (x : α) :
    (prodUnique α β).symm x = (x, default) :=
  rfl
#align equiv.prod_unique_symm_apply Equiv.prodUnique_symm_apply

/-- Any `Unique` type is a left identity for type product up to equivalence. -/
def uniqueProd (α β) [Unique β] : β × α ≃ α :=
  ((equivPUnit.{_,1} β).prodCongr <| Equiv.refl α).trans <| punitProd α
#align equiv.unique_prod Equiv.uniqueProd

@[simp]
theorem coe_uniqueProd [Unique β] : (⇑(uniqueProd α β) : β × α → α) = Prod.snd :=
  rfl
#align equiv.coe_unique_prod Equiv.coe_uniqueProd

theorem uniqueProd_apply [Unique β] (x : β × α) : uniqueProd α β x = x.2 :=
  rfl
#align equiv.unique_prod_apply Equiv.uniqueProd_apply

@[simp]
theorem uniqueProd_symm_apply [Unique β] (x : α) :
    (uniqueProd α β).symm x = (default, x) :=
  rfl
#align equiv.unique_prod_symm_apply Equiv.uniqueProd_symm_apply

/-- Any family of `Unique` types is a right identity for dependent type product up to
equivalence. -/
def sigmaUnique (α) (β : α → Type*) [∀ a, Unique (β a)] : (a : α) × (β a) ≃ α :=
  (Equiv.sigmaCongrRight fun a ↦ equivPUnit.{_,1} (β a)).trans <| sigmaPUnit α

@[simp]
theorem coe_sigmaUnique {β : α → Type*} [∀ a, Unique (β a)] :
    (⇑(sigmaUnique α β) : (a : α) × (β a) → α) = Sigma.fst :=
  rfl

theorem sigmaUnique_apply {β : α → Type*} [∀ a, Unique (β a)] (x : (a : α) × β a) :
    sigmaUnique α β x = x.1 :=
  rfl

@[simp]
theorem sigmaUnique_symm_apply {β : α → Type*} [∀ a, Unique (β a)] (x : α) :
    (sigmaUnique α β).symm x = ⟨x, default⟩ :=
  rfl

/-- `Empty` type is a right absorbing element for type product up to an equivalence. -/
def prodEmpty (α) : α × Empty ≃ Empty :=
  equivEmpty _
#align equiv.prod_empty Equiv.prodEmpty

/-- `Empty` type is a left absorbing element for type product up to an equivalence. -/
def emptyProd (α) : Empty × α ≃ Empty :=
  equivEmpty _
#align equiv.empty_prod Equiv.emptyProd

/-- `PEmpty` type is a right absorbing element for type product up to an equivalence. -/
def prodPEmpty (α) : α × PEmpty ≃ PEmpty :=
  equivPEmpty _
#align equiv.prod_pempty Equiv.prodPEmpty

/-- `PEmpty` type is a left absorbing element for type product up to an equivalence. -/
def pemptyProd (α) : PEmpty × α ≃ PEmpty :=
  equivPEmpty _
#align equiv.pempty_prod Equiv.pemptyProd

end

section

open Sum

/-- `PSum` is equivalent to `Sum`. -/
def psumEquivSum (α β) : PSum α β ≃ Sum α β where
  toFun s := PSum.casesOn s inl inr
  invFun := Sum.elim PSum.inl PSum.inr
  left_inv s := by cases s <;> rfl
                   -- ⊢ Sum.elim PSum.inl PSum.inr ((fun s => PSum.casesOn s inl inr) (PSum.inl val✝ …
                               -- 🎉 no goals
                               -- 🎉 no goals
  right_inv s := by cases s <;> rfl
                    -- ⊢ (fun s => PSum.casesOn s inl inr) (Sum.elim PSum.inl PSum.inr (inl val✝)) =  …
                                -- 🎉 no goals
                                -- 🎉 no goals
#align equiv.psum_equiv_sum Equiv.psumEquivSum

/-- If `α ≃ α'` and `β ≃ β'`, then `α ⊕ β ≃ α' ⊕ β'`. This is `Sum.map` as an equivalence. -/
@[simps apply]
def sumCongr (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : Sum α₁ β₁ ≃ Sum α₂ β₂ :=
  ⟨Sum.map ea eb, Sum.map ea.symm eb.symm, fun x => by simp, fun x => by simp⟩
                                                       -- 🎉 no goals
                                                                         -- 🎉 no goals
#align equiv.sum_congr Equiv.sumCongr
#align equiv.sum_congr_apply Equiv.sumCongr_apply

/-- If `α ≃ α'` and `β ≃ β'`, then `PSum α β ≃ PSum α' β'`. -/
def psumCongr (e₁ : α ≃ β) (e₂ : γ ≃ δ) : PSum α γ ≃ PSum β δ where
  toFun x := PSum.casesOn x (PSum.inl ∘ e₁) (PSum.inr ∘ e₂)
  invFun x := PSum.casesOn x (PSum.inl ∘ e₁.symm) (PSum.inr ∘ e₂.symm)
  left_inv := by rintro (x | x) <;> simp
                 -- ⊢ (fun x => PSum.casesOn x (PSum.inl ∘ ↑e₁.symm) (PSum.inr ∘ ↑e₂.symm)) ((fun  …
                                    -- 🎉 no goals
                                    -- 🎉 no goals
  right_inv := by rintro (x | x) <;> simp
                  -- ⊢ (fun x => PSum.casesOn x (PSum.inl ∘ ↑e₁) (PSum.inr ∘ ↑e₂)) ((fun x => PSum. …
                                     -- 🎉 no goals
                                     -- 🎉 no goals
#align equiv.psum_congr Equiv.psumCongr

/-- Combine two `Equiv`s using `PSum` in the domain and `Sum` in the codomain. -/
def psumSum (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) :
    PSum α₁ β₁ ≃ Sum α₂ β₂ :=
  (ea.psumCongr eb).trans (psumEquivSum _ _)
#align equiv.psum_sum Equiv.psumSum

/-- Combine two `Equiv`s using `Sum` in the domain and `PSum` in the codomain. -/
def sumPSum (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) :
    Sum α₁ β₁ ≃ PSum α₂ β₂ :=
  (ea.symm.psumSum eb.symm).symm
#align equiv.sum_psum Equiv.sumPSum

@[simp]
theorem sumCongr_trans (e : α₁ ≃ β₁) (f : α₂ ≃ β₂) (g : β₁ ≃ γ₁) (h : β₂ ≃ γ₂) :
    (Equiv.sumCongr e f).trans (Equiv.sumCongr g h) = Equiv.sumCongr (e.trans g) (f.trans h) := by
  ext i
  -- ⊢ ↑((sumCongr e f).trans (sumCongr g h)) i = ↑(sumCongr (e.trans g) (f.trans h …
  cases i <;> rfl
  -- ⊢ ↑((sumCongr e f).trans (sumCongr g h)) (inl val✝) = ↑(sumCongr (e.trans g) ( …
              -- 🎉 no goals
              -- 🎉 no goals
#align equiv.sum_congr_trans Equiv.sumCongr_trans

@[simp]
theorem sumCongr_symm (e : α ≃ β) (f : γ ≃ δ) :
    (Equiv.sumCongr e f).symm = Equiv.sumCongr e.symm f.symm :=
  rfl
#align equiv.sum_congr_symm Equiv.sumCongr_symm

@[simp]
theorem sumCongr_refl : Equiv.sumCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (Sum α β) := by
  ext i
  -- ⊢ ↑(sumCongr (Equiv.refl α) (Equiv.refl β)) i = ↑(Equiv.refl (α ⊕ β)) i
  cases i <;> rfl
  -- ⊢ ↑(sumCongr (Equiv.refl α) (Equiv.refl β)) (inl val✝) = ↑(Equiv.refl (α ⊕ β)) …
              -- 🎉 no goals
              -- 🎉 no goals
#align equiv.sum_congr_refl Equiv.sumCongr_refl

/-- A subtype of a sum is equivalent to a sum of subtypes. -/
def subtypeSum {p : α ⊕ β → Prop} : {c // p c} ≃ {a // p (Sum.inl a)} ⊕ {b // p (Sum.inr b)} where
  toFun c := match h : c.1 with
    | Sum.inl a => Sum.inl ⟨a, h ▸ c.2⟩
    | Sum.inr b => Sum.inr ⟨b, h ▸ c.2⟩
  invFun c := match c with
    | Sum.inl a => ⟨Sum.inl a, a.2⟩
    | Sum.inr b => ⟨Sum.inr b, b.2⟩
  left_inv := by rintro ⟨a | b, h⟩ <;> rfl
                                       -- 🎉 no goals
                                       -- 🎉 no goals
  right_inv := by rintro (a | b) <;> rfl
                                     -- 🎉 no goals
                                     -- 🎉 no goals

namespace Perm

/-- Combine a permutation of `α` and of `β` into a permutation of `α ⊕ β`. -/
@[reducible]
def sumCongr (ea : Equiv.Perm α) (eb : Equiv.Perm β) : Equiv.Perm (Sum α β) :=
  Equiv.sumCongr ea eb
#align equiv.perm.sum_congr Equiv.Perm.sumCongr

@[simp]
theorem sumCongr_apply (ea : Equiv.Perm α) (eb : Equiv.Perm β) (x : Sum α β) :
    sumCongr ea eb x = Sum.map (⇑ea) (⇑eb) x :=
  Equiv.sumCongr_apply ea eb x
#align equiv.perm.sum_congr_apply Equiv.Perm.sumCongr_apply

-- porting note: it seems the general theorem about `Equiv` is now applied, so there's no need
-- to have this version also have `@[simp]`. Similarly for below.
theorem sumCongr_trans (e : Equiv.Perm α) (f : Equiv.Perm β) (g : Equiv.Perm α)
    (h : Equiv.Perm β) : (sumCongr e f).trans (sumCongr g h) = sumCongr (e.trans g) (f.trans h) :=
  Equiv.sumCongr_trans e f g h
#align equiv.perm.sum_congr_trans Equiv.Perm.sumCongr_trans

theorem sumCongr_symm (e : Equiv.Perm α) (f : Equiv.Perm β) :
    (sumCongr e f).symm = sumCongr e.symm f.symm :=
  Equiv.sumCongr_symm e f
#align equiv.perm.sum_congr_symm Equiv.Perm.sumCongr_symm

theorem sumCongr_refl : sumCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (Sum α β) :=
  Equiv.sumCongr_refl
#align equiv.perm.sum_congr_refl Equiv.Perm.sumCongr_refl

end Perm

/-- `Bool` is equivalent the sum of two `PUnit`s. -/
def boolEquivPUnitSumPUnit : Bool ≃ Sum PUnit.{u + 1} PUnit.{v + 1} :=
  ⟨fun b => cond b (inr PUnit.unit) (inl PUnit.unit), Sum.elim (fun _ => false) fun _ => true,
    fun b => by cases b <;> rfl, fun s => by rcases s with (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> rfl⟩
                -- ⊢ Sum.elim (fun x => false) (fun x => true) ((fun b => bif b then inr PUnit.un …
                            -- 🎉 no goals
                            -- 🎉 no goals
                                             -- ⊢ (fun b => bif b then inr PUnit.unit else inl PUnit.unit) (Sum.elim (fun x => …
                                                                             -- 🎉 no goals
                                                                             -- 🎉 no goals
#align equiv.bool_equiv_punit_sum_punit Equiv.boolEquivPUnitSumPUnit

/-- Sum of types is commutative up to an equivalence. This is `Sum.swap` as an equivalence. -/
@[simps (config := { fullyApplied := false }) apply]
def sumComm (α β) : Sum α β ≃ Sum β α :=
  ⟨Sum.swap, Sum.swap, Sum.swap_swap, Sum.swap_swap⟩
#align equiv.sum_comm Equiv.sumComm
#align equiv.sum_comm_apply Equiv.sumComm_apply

@[simp]
theorem sumComm_symm (α β) : (sumComm α β).symm = sumComm β α :=
  rfl
#align equiv.sum_comm_symm Equiv.sumComm_symm

/-- Sum of types is associative up to an equivalence. -/
def sumAssoc (α β γ) : Sum (Sum α β) γ ≃ Sum α (Sum β γ) :=
  ⟨Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr),
    Sum.elim (Sum.inl ∘ Sum.inl) <| Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr,
      by rintro (⟨_ | _⟩ | _) <;> rfl, by
                                  -- 🎉 no goals
                                  -- 🎉 no goals
                                  -- 🎉 no goals
    rintro (_ | ⟨_ | _⟩) <;> rfl⟩
                             -- 🎉 no goals
                             -- 🎉 no goals
                             -- 🎉 no goals
#align equiv.sum_assoc Equiv.sumAssoc

@[simp]
theorem sumAssoc_apply_inl_inl (a) : sumAssoc α β γ (inl (inl a)) = inl a :=
  rfl
#align equiv.sum_assoc_apply_inl_inl Equiv.sumAssoc_apply_inl_inl

@[simp]
theorem sumAssoc_apply_inl_inr (b) : sumAssoc α β γ (inl (inr b)) = inr (inl b) :=
  rfl
#align equiv.sum_assoc_apply_inl_inr Equiv.sumAssoc_apply_inl_inr

@[simp]
theorem sumAssoc_apply_inr (c) : sumAssoc α β γ (inr c) = inr (inr c) :=
  rfl
#align equiv.sum_assoc_apply_inr Equiv.sumAssoc_apply_inr

@[simp]
theorem sumAssoc_symm_apply_inl {α β γ} (a) : (sumAssoc α β γ).symm (inl a) = inl (inl a) :=
  rfl
#align equiv.sum_assoc_symm_apply_inl Equiv.sumAssoc_symm_apply_inl

@[simp]
theorem sumAssoc_symm_apply_inr_inl {α β γ} (b) :
    (sumAssoc α β γ).symm (inr (inl b)) = inl (inr b) :=
  rfl
#align equiv.sum_assoc_symm_apply_inr_inl Equiv.sumAssoc_symm_apply_inr_inl

@[simp]
theorem sumAssoc_symm_apply_inr_inr {α β γ} (c) : (sumAssoc α β γ).symm (inr (inr c)) = inr c :=
  rfl
#align equiv.sum_assoc_symm_apply_inr_inr Equiv.sumAssoc_symm_apply_inr_inr

/-- Sum with `IsEmpty` is equivalent to the original type. -/
@[simps symm_apply]
def sumEmpty (α β) [IsEmpty β] : Sum α β ≃ α where
  toFun := Sum.elim id isEmptyElim
  invFun := inl
  left_inv s := by
    rcases s with (_ | x)
    -- ⊢ inl (Sum.elim id (fun a => isEmptyElim a) (inl val✝)) = inl val✝
    · rfl
      -- 🎉 no goals
    · exact isEmptyElim x
      -- 🎉 no goals
  right_inv _ := rfl
#align equiv.sum_empty Equiv.sumEmpty
#align equiv.sum_empty_symm_apply Equiv.sumEmpty_symm_apply

@[simp]
theorem sumEmpty_apply_inl [IsEmpty β] (a : α) : sumEmpty α β (Sum.inl a) = a :=
  rfl
#align equiv.sum_empty_apply_inl Equiv.sumEmpty_apply_inl

/-- The sum of `IsEmpty` with any type is equivalent to that type. -/
@[simps! symm_apply]
def emptySum (α β) [IsEmpty α] : Sum α β ≃ β :=
  (sumComm _ _).trans <| sumEmpty _ _
#align equiv.empty_sum Equiv.emptySum
#align equiv.empty_sum_symm_apply Equiv.emptySum_symm_apply

@[simp]
theorem emptySum_apply_inr [IsEmpty α] (b : β) : emptySum α β (Sum.inr b) = b :=
  rfl
#align equiv.empty_sum_apply_inr Equiv.emptySum_apply_inr

/-- `Option α` is equivalent to `α ⊕ PUnit` -/
def optionEquivSumPUnit (α) : Option α ≃ Sum α PUnit :=
  ⟨fun o => o.elim (inr PUnit.unit) inl, fun s => s.elim some fun _ => none,
    fun o => by cases o <;> rfl,
                -- ⊢ (fun s => Sum.elim some (fun x => none) s) ((fun o => Option.elim o (inr PUn …
                            -- 🎉 no goals
                            -- 🎉 no goals
    fun s => by rcases s with (_ | ⟨⟨⟩⟩) <;> rfl⟩
                -- ⊢ (fun o => Option.elim o (inr PUnit.unit) inl) ((fun s => Sum.elim some (fun  …
                                             -- 🎉 no goals
                                             -- 🎉 no goals
#align equiv.option_equiv_sum_punit Equiv.optionEquivSumPUnit

@[simp]
theorem optionEquivSumPUnit_none : optionEquivSumPUnit α none = Sum.inr PUnit.unit :=
  rfl
#align equiv.option_equiv_sum_punit_none Equiv.optionEquivSumPUnit_none

@[simp]
theorem optionEquivSumPUnit_some (a) : optionEquivSumPUnit α (some a) = Sum.inl a :=
  rfl
#align equiv.option_equiv_sum_punit_some Equiv.optionEquivSumPUnit_some

@[simp]
theorem optionEquivSumPUnit_coe (a : α) : optionEquivSumPUnit α a = Sum.inl a :=
  rfl
#align equiv.option_equiv_sum_punit_coe Equiv.optionEquivSumPUnit_coe

@[simp]
theorem optionEquivSumPUnit_symm_inl (a) : (optionEquivSumPUnit α).symm (Sum.inl a) = a :=
  rfl
#align equiv.option_equiv_sum_punit_symm_inl Equiv.optionEquivSumPUnit_symm_inl

@[simp]
theorem optionEquivSumPUnit_symm_inr (a) : (optionEquivSumPUnit α).symm (Sum.inr a) = none :=
  rfl
#align equiv.option_equiv_sum_punit_symm_inr Equiv.optionEquivSumPUnit_symm_inr

/-- The set of `x : Option α` such that `isSome x` is equivalent to `α`. -/
@[simps]
def optionIsSomeEquiv (α) : { x : Option α // x.isSome } ≃ α where
  toFun o := Option.get _ o.2
  invFun x := ⟨some x, rfl⟩
  left_inv _ := Subtype.eq <| Option.some_get _
  right_inv _ := Option.get_some _ _
#align equiv.option_is_some_equiv Equiv.optionIsSomeEquiv
#align equiv.option_is_some_equiv_apply Equiv.optionIsSomeEquiv_apply
#align equiv.option_is_some_equiv_symm_apply_coe Equiv.optionIsSomeEquiv_symm_apply_coe

/-- The product over `Option α` of `β a` is the binary product of the
product over `α` of `β (some α)` and `β none` -/
@[simps]
def piOptionEquivProd {β : Option α → Type*} :
    (∀ a : Option α, β a) ≃ β none × ∀ a : α, β (some a) where
  toFun f := (f none, fun a => f (some a))
  invFun x a := Option.casesOn a x.fst x.snd
  left_inv f := funext fun a => by cases a <;> rfl
                                   -- ⊢ (fun x a => Option.casesOn a x.fst x.snd) ((fun f => (f none, fun a => f (so …
                                               -- 🎉 no goals
                                               -- 🎉 no goals
  right_inv x := by simp
                    -- 🎉 no goals
#align equiv.pi_option_equiv_prod Equiv.piOptionEquivProd
#align equiv.pi_option_equiv_prod_symm_apply Equiv.piOptionEquivProd_symm_apply
#align equiv.pi_option_equiv_prod_apply Equiv.piOptionEquivProd_apply

/-- `α ⊕ β` is equivalent to a `Sigma`-type over `Bool`. Note that this definition assumes `α` and
`β` to be types from the same universe, so it cannot be used directly to transfer theorems about
sigma types to theorems about sum types. In many cases one can use `ULift` to work around this
difficulty. -/
def sumEquivSigmaBool (α β : Type u) : Sum α β ≃ Σ b : Bool, cond b α β :=
  ⟨fun s => s.elim (fun x => ⟨true, x⟩) fun x => ⟨false, x⟩, fun s =>
    match s with
    | ⟨true, a⟩ => inl a
    | ⟨false, b⟩ => inr b,
    fun s => by cases s <;> rfl, fun s => by rcases s with ⟨_ | _, _⟩ <;> rfl⟩
                            -- 🎉 no goals
                            -- 🎉 no goals
                                                                          -- 🎉 no goals
                                                                          -- 🎉 no goals
#align equiv.sum_equiv_sigma_bool Equiv.sumEquivSigmaBool

-- See also `Equiv.sigmaPreimageEquiv`.
/-- `sigmaFiberEquiv f` for `f : α → β` is the natural equivalence between
the type of all fibres of `f` and the total space `α`. -/
@[simps]
def sigmaFiberEquiv {α β : Type*} (f : α → β) : (Σ y : β, { x // f x = y }) ≃ α :=
  ⟨fun x => ↑x.2, fun x => ⟨f x, x, rfl⟩, fun ⟨_, _, rfl⟩ => rfl, fun _ => rfl⟩
#align equiv.sigma_fiber_equiv Equiv.sigmaFiberEquiv
#align equiv.sigma_fiber_equiv_apply Equiv.sigmaFiberEquiv_apply
#align equiv.sigma_fiber_equiv_symm_apply_fst Equiv.sigmaFiberEquiv_symm_apply_fst
#align equiv.sigma_fiber_equiv_symm_apply_snd_coe Equiv.sigmaFiberEquiv_symm_apply_snd_coe

end

section sumCompl

/-- For any predicate `p` on `α`,
the sum of the two subtypes `{a // p a}` and its complement `{a // ¬ p a}`
is naturally equivalent to `α`.

See `subtypeOrEquiv` for sum types over subtypes `{x // p x}` and `{x // q x}`
that are not necessarily `IsCompl p q`.  -/
def sumCompl {α : Type*} (p : α → Prop) [DecidablePred p] :
    Sum { a // p a } { a // ¬p a } ≃ α where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun a := if h : p a then Sum.inl ⟨a, h⟩ else Sum.inr ⟨a, h⟩
  left_inv := by
    rintro (⟨x, hx⟩ | ⟨x, hx⟩) <;> dsimp
    -- ⊢ (fun a => if h : p a then Sum.inl { val := a, property := h } else Sum.inr { …
                                   -- ⊢ (if h : p x then Sum.inl { val := x, property := h } else Sum.inr { val := x …
                                   -- ⊢ (if h : p x then Sum.inl { val := x, property := h } else Sum.inr { val := x …
    · rw [dif_pos]
      -- 🎉 no goals
    · rw [dif_neg]
      -- 🎉 no goals
  right_inv a := by
    dsimp
    -- ⊢ Sum.elim Subtype.val Subtype.val (if h : p a then Sum.inl { val := a, proper …
    split_ifs <;> rfl
    -- ⊢ Sum.elim Subtype.val Subtype.val (Sum.inl { val := a, property := h✝ }) = a
                  -- 🎉 no goals
                  -- 🎉 no goals
#align equiv.sum_compl Equiv.sumCompl

@[simp]
theorem sumCompl_apply_inl (p : α → Prop) [DecidablePred p] (x : { a // p a }) :
    sumCompl p (Sum.inl x) = x :=
  rfl
#align equiv.sum_compl_apply_inl Equiv.sumCompl_apply_inl

@[simp]
theorem sumCompl_apply_inr (p : α → Prop) [DecidablePred p] (x : { a // ¬p a }) :
    sumCompl p (Sum.inr x) = x :=
  rfl
#align equiv.sum_compl_apply_inr Equiv.sumCompl_apply_inr

@[simp]
theorem sumCompl_apply_symm_of_pos (p : α → Prop) [DecidablePred p] (a : α) (h : p a) :
    (sumCompl p).symm a = Sum.inl ⟨a, h⟩ :=
  dif_pos h
#align equiv.sum_compl_apply_symm_of_pos Equiv.sumCompl_apply_symm_of_pos

@[simp]
theorem sumCompl_apply_symm_of_neg (p : α → Prop) [DecidablePred p] (a : α) (h : ¬p a) :
    (sumCompl p).symm a = Sum.inr ⟨a, h⟩ :=
  dif_neg h
#align equiv.sum_compl_apply_symm_of_neg Equiv.sumCompl_apply_symm_of_neg

/-- Combines an `Equiv` between two subtypes with an `Equiv` between their complements to form a
  permutation. -/
def subtypeCongr {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (e : { x // p x } ≃ { x // q x }) (f : { x // ¬p x } ≃ { x // ¬q x }) : Perm α :=
  (sumCompl p).symm.trans ((sumCongr e f).trans (sumCompl q))
#align equiv.subtype_congr Equiv.subtypeCongr

variable {p : ε → Prop} [DecidablePred p]

variable (ep ep' : Perm { a // p a }) (en en' : Perm { a // ¬p a })

/-- Combining permutations on `ε` that permute only inside or outside the subtype
split induced by `p : ε → Prop` constructs a permutation on `ε`. -/
def Perm.subtypeCongr : Equiv.Perm ε :=
  permCongr (sumCompl p) (sumCongr ep en)
#align equiv.perm.subtype_congr Equiv.Perm.subtypeCongr

theorem Perm.subtypeCongr.apply (a : ε) : ep.subtypeCongr en a =
    if h : p a then (ep ⟨a, h⟩ : ε) else en ⟨a, h⟩ := by
  by_cases h : p a <;> simp [Perm.subtypeCongr, h]
  -- ⊢ ↑(subtypeCongr ep en) a = if h : p a then ↑(↑ep { val := a, property := h }) …
                       -- 🎉 no goals
                       -- 🎉 no goals
#align equiv.perm.subtype_congr.apply Equiv.Perm.subtypeCongr.apply

@[simp]
theorem Perm.subtypeCongr.left_apply {a : ε} (h : p a) : ep.subtypeCongr en a = ep ⟨a, h⟩ := by
  simp [Perm.subtypeCongr.apply, h]
  -- 🎉 no goals
#align equiv.perm.subtype_congr.left_apply Equiv.Perm.subtypeCongr.left_apply

@[simp]
theorem Perm.subtypeCongr.left_apply_subtype (a : { a // p a }) : ep.subtypeCongr en a = ep a :=
    Perm.subtypeCongr.left_apply ep en a.property
#align equiv.perm.subtype_congr.left_apply_subtype Equiv.Perm.subtypeCongr.left_apply_subtype

@[simp]
theorem Perm.subtypeCongr.right_apply {a : ε} (h : ¬p a) : ep.subtypeCongr en a = en ⟨a, h⟩ := by
  simp [Perm.subtypeCongr.apply, h]
  -- 🎉 no goals
#align equiv.perm.subtype_congr.right_apply Equiv.Perm.subtypeCongr.right_apply

@[simp]
theorem Perm.subtypeCongr.right_apply_subtype (a : { a // ¬p a }) : ep.subtypeCongr en a = en a :=
  Perm.subtypeCongr.right_apply ep en a.property
#align equiv.perm.subtype_congr.right_apply_subtype Equiv.Perm.subtypeCongr.right_apply_subtype

@[simp]
theorem Perm.subtypeCongr.refl :
    Perm.subtypeCongr (Equiv.refl { a // p a }) (Equiv.refl { a // ¬p a }) = Equiv.refl ε := by
  ext x
  -- ⊢ ↑(subtypeCongr (Equiv.refl { a // p a }) (Equiv.refl { a // ¬p a })) x = ↑(E …
  by_cases h:p x <;> simp [h]
  -- ⊢ ↑(subtypeCongr (Equiv.refl { a // p a }) (Equiv.refl { a // ¬p a })) x = ↑(E …
                     -- 🎉 no goals
                     -- 🎉 no goals
#align equiv.perm.subtype_congr.refl Equiv.Perm.subtypeCongr.refl

@[simp]
theorem Perm.subtypeCongr.symm : (ep.subtypeCongr en).symm = Perm.subtypeCongr ep.symm en.symm := by
  ext x
  -- ⊢ ↑(subtypeCongr ep en).symm x = ↑(subtypeCongr ep.symm en.symm) x
  by_cases h:p x
  -- ⊢ ↑(subtypeCongr ep en).symm x = ↑(subtypeCongr ep.symm en.symm) x
  · have : p (ep.symm ⟨x, h⟩) := Subtype.property _
    -- ⊢ ↑(subtypeCongr ep en).symm x = ↑(subtypeCongr ep.symm en.symm) x
    simp [Perm.subtypeCongr.apply, h, symm_apply_eq, this]
    -- 🎉 no goals
  · have : ¬p (en.symm ⟨x, h⟩) := Subtype.property (en.symm _)
    -- ⊢ ↑(subtypeCongr ep en).symm x = ↑(subtypeCongr ep.symm en.symm) x
    simp [Perm.subtypeCongr.apply, h, symm_apply_eq, this]
    -- 🎉 no goals
#align equiv.perm.subtype_congr.symm Equiv.Perm.subtypeCongr.symm

@[simp]
theorem Perm.subtypeCongr.trans :
    (ep.subtypeCongr en).trans (ep'.subtypeCongr en')
    = Perm.subtypeCongr (ep.trans ep') (en.trans en') := by
  ext x
  -- ⊢ ↑((subtypeCongr ep en).trans (subtypeCongr ep' en')) x = ↑(subtypeCongr (ep. …
  by_cases h:p x
  -- ⊢ ↑((subtypeCongr ep en).trans (subtypeCongr ep' en')) x = ↑(subtypeCongr (ep. …
  · have : p (ep ⟨x, h⟩) := Subtype.property _
    -- ⊢ ↑((subtypeCongr ep en).trans (subtypeCongr ep' en')) x = ↑(subtypeCongr (ep. …
    simp [Perm.subtypeCongr.apply, h, this]
    -- 🎉 no goals
  · have : ¬p (en ⟨x, h⟩) := Subtype.property (en _)
    -- ⊢ ↑((subtypeCongr ep en).trans (subtypeCongr ep' en')) x = ↑(subtypeCongr (ep. …
    simp [Perm.subtypeCongr.apply, h, symm_apply_eq, this]
    -- 🎉 no goals
#align equiv.perm.subtype_congr.trans Equiv.Perm.subtypeCongr.trans

end sumCompl

section subtypePreimage

variable (p : α → Prop) [DecidablePred p] (x₀ : { a // p a } → β)

/-- For a fixed function `x₀ : {a // p a} → β` defined on a subtype of `α`,
the subtype of functions `x : α → β` that agree with `x₀` on the subtype `{a // p a}`
is naturally equivalent to the type of functions `{a // ¬ p a} → β`. -/
@[simps]
def subtypePreimage : { x : α → β // x ∘ Subtype.val = x₀ } ≃ ({ a // ¬p a } → β) where
  toFun (x : { x : α → β // x ∘ Subtype.val = x₀ }) a := (x : α → β) a
  invFun x := ⟨fun a => if h : p a then x₀ ⟨a, h⟩ else x ⟨a, h⟩, funext fun ⟨a, h⟩ => dif_pos h⟩
  left_inv := fun ⟨x, hx⟩ =>
    Subtype.val_injective <|
      funext fun a => by
        dsimp only
        -- ⊢ (if h : p a then x₀ { val := a, property := h } else x a) = x a
        split_ifs
        -- ⊢ x₀ { val := a, property := h✝ } = x a
        · rw [← hx]; rfl
          -- ⊢ (x ∘ Subtype.val) { val := a, property := h✝ } = x a
                     -- 🎉 no goals
        · rfl
          -- 🎉 no goals
  right_inv x :=
    funext fun ⟨a, h⟩ =>
      show dite (p a) _ _ = _ by
        dsimp only
        -- ⊢ (if h : p a then x₀ { val := a, property := h } else x { val := a, property  …
        rw [dif_neg h]
        -- 🎉 no goals
#align equiv.subtype_preimage Equiv.subtypePreimage
#align equiv.subtype_preimage_symm_apply_coe Equiv.subtypePreimage_symm_apply_coe
#align equiv.subtype_preimage_apply Equiv.subtypePreimage_apply

theorem subtypePreimage_symm_apply_coe_pos (x : { a // ¬p a } → β) (a : α) (h : p a) :
    ((subtypePreimage p x₀).symm x : α → β) a = x₀ ⟨a, h⟩ :=
  dif_pos h
#align equiv.subtype_preimage_symm_apply_coe_pos Equiv.subtypePreimage_symm_apply_coe_pos

theorem subtypePreimage_symm_apply_coe_neg (x : { a // ¬p a } → β) (a : α) (h : ¬p a) :
    ((subtypePreimage p x₀).symm x : α → β) a = x ⟨a, h⟩ :=
  dif_neg h
#align equiv.subtype_preimage_symm_apply_coe_neg Equiv.subtypePreimage_symm_apply_coe_neg

end subtypePreimage

section

/-- A family of equivalences `∀ a, β₁ a ≃ β₂ a` generates an equivalence between `∀ a, β₁ a` and
`∀ a, β₂ a`. -/
def piCongrRight {β₁ β₂ : α → Sort*} (F : ∀ a, β₁ a ≃ β₂ a) : (∀ a, β₁ a) ≃ (∀ a, β₂ a) :=
  ⟨fun H a => F a (H a), fun H a => (F a).symm (H a), fun H => funext <| by simp,
                                                                            -- 🎉 no goals
    fun H => funext <| by simp⟩
                          -- 🎉 no goals
#align equiv.Pi_congr_right Equiv.piCongrRight

/-- Given `φ : α → β → Sort*`, we have an equivalence between `∀ a b, φ a b` and `∀ b a, φ a b`.
This is `Function.swap` as an `Equiv`. -/
@[simps apply]
def piComm (φ : α → β → Sort*) : (∀ a b, φ a b) ≃ ∀ b a, φ a b :=
  ⟨swap, swap, fun _ => rfl, fun _ => rfl⟩
#align equiv.Pi_comm Equiv.piComm
#align equiv.Pi_comm_apply Equiv.piComm_apply

@[simp]
theorem piComm_symm {φ : α → β → Sort*} : (piComm φ).symm = (piComm <| swap φ) :=
  rfl
#align equiv.Pi_comm_symm Equiv.piComm_symm

/-- Dependent `curry` equivalence: the type of dependent functions on `Σ i, β i` is equivalent
to the type of dependent functions of two arguments (i.e., functions to the space of functions).

This is `Sigma.curry` and `Sigma.uncurry` together as an equiv. -/
def piCurry {β : α → Sort _} (γ : ∀ a, β a → Sort _) :
    (∀ x : Σ i, β i, γ x.1 x.2) ≃ ∀ a b, γ a b where
  toFun := Sigma.curry
  invFun := Sigma.uncurry
  left_inv := Sigma.uncurry_curry
  right_inv := Sigma.curry_uncurry
#align equiv.Pi_curry Equiv.piCurry

end

section prodCongr

variable (e : α₁ → β₁ ≃ β₂)

/-- A family of equivalences `∀ (a : α₁), β₁ ≃ β₂` generates an equivalence
between `β₁ × α₁` and `β₂ × α₁`. -/
def prodCongrLeft : β₁ × α₁ ≃ β₂ × α₁ where
  toFun ab := ⟨e ab.2 ab.1, ab.2⟩
  invFun ab := ⟨(e ab.2).symm ab.1, ab.2⟩
  left_inv := by
    rintro ⟨a, b⟩
    -- ⊢ (fun ab => (↑(e ab.snd).symm ab.fst, ab.snd)) ((fun ab => (↑(e ab.snd) ab.fs …
    simp
    -- 🎉 no goals
  right_inv := by
    rintro ⟨a, b⟩
    -- ⊢ (fun ab => (↑(e ab.snd) ab.fst, ab.snd)) ((fun ab => (↑(e ab.snd).symm ab.fs …
    simp
    -- 🎉 no goals
#align equiv.prod_congr_left Equiv.prodCongrLeft

@[simp]
theorem prodCongrLeft_apply (b : β₁) (a : α₁) : prodCongrLeft e (b, a) = (e a b, a) :=
  rfl
#align equiv.prod_congr_left_apply Equiv.prodCongrLeft_apply

theorem prodCongr_refl_right (e : β₁ ≃ β₂) :
    prodCongr e (Equiv.refl α₁) = prodCongrLeft fun _ => e := by
  ext ⟨a, b⟩ : 1
  -- ⊢ ↑(prodCongr e (Equiv.refl α₁)) (a, b) = ↑(prodCongrLeft fun x => e) (a, b)
  simp
  -- 🎉 no goals
#align equiv.prod_congr_refl_right Equiv.prodCongr_refl_right

/-- A family of equivalences `∀ (a : α₁), β₁ ≃ β₂` generates an equivalence
between `α₁ × β₁` and `α₁ × β₂`. -/
def prodCongrRight : α₁ × β₁ ≃ α₁ × β₂ where
  toFun ab := ⟨ab.1, e ab.1 ab.2⟩
  invFun ab := ⟨ab.1, (e ab.1).symm ab.2⟩
  left_inv := by
    rintro ⟨a, b⟩
    -- ⊢ (fun ab => (ab.fst, ↑(e ab.fst).symm ab.snd)) ((fun ab => (ab.fst, ↑(e ab.fs …
    simp
    -- 🎉 no goals
  right_inv := by
    rintro ⟨a, b⟩
    -- ⊢ (fun ab => (ab.fst, ↑(e ab.fst) ab.snd)) ((fun ab => (ab.fst, ↑(e ab.fst).sy …
    simp
    -- 🎉 no goals
#align equiv.prod_congr_right Equiv.prodCongrRight

@[simp]
theorem prodCongrRight_apply (a : α₁) (b : β₁) : prodCongrRight e (a, b) = (a, e a b) :=
  rfl
#align equiv.prod_congr_right_apply Equiv.prodCongrRight_apply

theorem prodCongr_refl_left (e : β₁ ≃ β₂) :
    prodCongr (Equiv.refl α₁) e = prodCongrRight fun _ => e := by
  ext ⟨a, b⟩ : 1
  -- ⊢ ↑(prodCongr (Equiv.refl α₁) e) (a, b) = ↑(prodCongrRight fun x => e) (a, b)
  simp
  -- 🎉 no goals
#align equiv.prod_congr_refl_left Equiv.prodCongr_refl_left

@[simp]
theorem prodCongrLeft_trans_prodComm :
    (prodCongrLeft e).trans (prodComm _ _) = (prodComm _ _).trans (prodCongrRight e) := by
  ext ⟨a, b⟩ : 1
  -- ⊢ ↑((prodCongrLeft e).trans (prodComm β₂ α₁)) (a, b) = ↑((prodComm β₁ α₁).tran …
  simp
  -- 🎉 no goals
#align equiv.prod_congr_left_trans_prod_comm Equiv.prodCongrLeft_trans_prodComm

@[simp]
theorem prodCongrRight_trans_prodComm :
    (prodCongrRight e).trans (prodComm _ _) = (prodComm _ _).trans (prodCongrLeft e) := by
  ext ⟨a, b⟩ : 1
  -- ⊢ ↑((prodCongrRight e).trans (prodComm α₁ β₂)) (a, b) = ↑((prodComm α₁ β₁).tra …
  simp
  -- 🎉 no goals
#align equiv.prod_congr_right_trans_prod_comm Equiv.prodCongrRight_trans_prodComm

theorem sigmaCongrRight_sigmaEquivProd :
    (sigmaCongrRight e).trans (sigmaEquivProd α₁ β₂)
    = (sigmaEquivProd α₁ β₁).trans (prodCongrRight e) := by
  ext ⟨a, b⟩ : 1
  -- ⊢ ↑((sigmaCongrRight e).trans (sigmaEquivProd α₁ β₂)) { fst := a, snd := b } = …
  simp
  -- 🎉 no goals
#align equiv.sigma_congr_right_sigma_equiv_prod Equiv.sigmaCongrRight_sigmaEquivProd

theorem sigmaEquivProd_sigmaCongrRight :
    (sigmaEquivProd α₁ β₁).symm.trans (sigmaCongrRight e)
    = (prodCongrRight e).trans (sigmaEquivProd α₁ β₂).symm := by
  ext ⟨a, b⟩ : 1
  -- ⊢ ↑((sigmaEquivProd α₁ β₁).symm.trans (sigmaCongrRight e)) (a, b) = ↑((prodCon …
  simp only [trans_apply, sigmaCongrRight_apply, prodCongrRight_apply]
  -- ⊢ { fst := (↑(sigmaEquivProd α₁ β₁).symm (a, b)).fst, snd := ↑(e (↑(sigmaEquiv …
  rfl
  -- 🎉 no goals
#align equiv.sigma_equiv_prod_sigma_congr_right Equiv.sigmaEquivProd_sigmaCongrRight

-- See also `Equiv.ofPreimageEquiv`.
/-- A family of equivalences between fibers gives an equivalence between domains. -/
@[simps!]
def ofFiberEquiv {f : α → γ} {g : β → γ} (e : ∀ c, { a // f a = c } ≃ { b // g b = c }) : α ≃ β :=
  (sigmaFiberEquiv f).symm.trans <| (Equiv.sigmaCongrRight e).trans (sigmaFiberEquiv g)
#align equiv.of_fiber_equiv Equiv.ofFiberEquiv
#align equiv.of_fiber_equiv_apply Equiv.ofFiberEquiv_apply
#align equiv.of_fiber_equiv_symm_apply Equiv.ofFiberEquiv_symm_apply

theorem ofFiberEquiv_map {α β γ} {f : α → γ} {g : β → γ}
    (e : ∀ c, { a // f a = c } ≃ { b // g b = c }) (a : α) : g (ofFiberEquiv e a) = f a :=
  (_ : { b // g b = _ }).property
#align equiv.of_fiber_equiv_map Equiv.ofFiberEquiv_map

/-- A variation on `Equiv.prodCongr` where the equivalence in the second component can depend
  on the first component. A typical example is a shear mapping, explaining the name of this
  declaration. -/
@[simps (config := { fullyApplied := false })]
def prodShear (e₁ : α₁ ≃ α₂) (e₂ : α₁ → β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂ where
  toFun := fun x : α₁ × β₁ => (e₁ x.1, e₂ x.1 x.2)
  invFun := fun y : α₂ × β₂ => (e₁.symm y.1, (e₂ <| e₁.symm y.1).symm y.2)
  left_inv := by
    rintro ⟨x₁, y₁⟩
    -- ⊢ (fun y => (↑e₁.symm y.fst, ↑(e₂ (↑e₁.symm y.fst)).symm y.snd)) ((fun x => (↑ …
    simp only [symm_apply_apply]
    -- 🎉 no goals
  right_inv := by
    rintro ⟨x₁, y₁⟩
    -- ⊢ (fun x => (↑e₁ x.fst, ↑(e₂ x.fst) x.snd)) ((fun y => (↑e₁.symm y.fst, ↑(e₂ ( …
    simp only [apply_symm_apply]
    -- 🎉 no goals
#align equiv.prod_shear Equiv.prodShear
#align equiv.prod_shear_apply Equiv.prodShear_apply
#align equiv.prod_shear_symm_apply Equiv.prodShear_symm_apply

end prodCongr

namespace Perm

variable [DecidableEq α₁] (a : α₁) (e : Perm β₁)

/-- `prodExtendRight a e` extends `e : Perm β` to `Perm (α × β)` by sending `(a, b)` to
`(a, e b)` and keeping the other `(a', b)` fixed. -/
def prodExtendRight : Perm (α₁ × β₁) where
  toFun ab := if ab.fst = a then (a, e ab.snd) else ab
  invFun ab := if ab.fst = a then (a, e.symm ab.snd) else ab
  left_inv := by
    rintro ⟨k', x⟩
    -- ⊢ (fun ab => if ab.fst = a then (a, ↑e.symm ab.snd) else ab) ((fun ab => if ab …
    dsimp only
    -- ⊢ (if (if k' = a then (a, ↑e x) else (k', x)).fst = a then (a, ↑e.symm (if k'  …
    split_ifs with h₁ h₂
    · simp [h₁]
      -- 🎉 no goals
    · simp at h₂
      -- 🎉 no goals
    · simp
      -- 🎉 no goals
  right_inv := by
    rintro ⟨k', x⟩
    -- ⊢ (fun ab => if ab.fst = a then (a, ↑e ab.snd) else ab) ((fun ab => if ab.fst  …
    dsimp only
    -- ⊢ (if (if k' = a then (a, ↑e.symm x) else (k', x)).fst = a then (a, ↑e (if k'  …
    split_ifs with h₁ h₂
    · simp [h₁]
      -- 🎉 no goals
    · simp at h₂
      -- 🎉 no goals
    · simp
      -- 🎉 no goals
#align equiv.perm.prod_extend_right Equiv.Perm.prodExtendRight

@[simp]
theorem prodExtendRight_apply_eq (b : β₁) : prodExtendRight a e (a, b) = (a, e b) :=
  if_pos rfl
#align equiv.perm.prod_extend_right_apply_eq Equiv.Perm.prodExtendRight_apply_eq

theorem prodExtendRight_apply_ne {a a' : α₁} (h : a' ≠ a) (b : β₁) :
    prodExtendRight a e (a', b) = (a', b) :=
  if_neg h
#align equiv.perm.prod_extend_right_apply_ne Equiv.Perm.prodExtendRight_apply_ne

theorem eq_of_prodExtendRight_ne {e : Perm β₁} {a a' : α₁} {b : β₁}
    (h : prodExtendRight a e (a', b) ≠ (a', b)) : a' = a := by
  contrapose! h
  -- ⊢ ↑(prodExtendRight a e) (a', b) = (a', b)
  exact prodExtendRight_apply_ne _ h _
  -- 🎉 no goals
#align equiv.perm.eq_of_prod_extend_right_ne Equiv.Perm.eq_of_prodExtendRight_ne

@[simp]
theorem fst_prodExtendRight (ab : α₁ × β₁) : (prodExtendRight a e ab).fst = ab.fst := by
  rw [prodExtendRight]
  -- ⊢ (↑{ toFun := fun ab => if ab.fst = a then (a, ↑e ab.snd) else ab, invFun :=  …
  dsimp
  -- ⊢ (if ab.fst = a then (a, ↑e ab.snd) else ab).fst = ab.fst
  split_ifs with h
  -- ⊢ (a, ↑e ab.snd).fst = ab.fst
  · rw [h]
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
#align equiv.perm.fst_prod_extend_right Equiv.Perm.fst_prodExtendRight

end Perm

section

/-- The type of functions to a product `α × β` is equivalent to the type of pairs of functions
`γ → α` and `γ → β`. -/
def arrowProdEquivProdArrow (α β γ : Type*) : (γ → α × β) ≃ (γ → α) × (γ → β) where
  toFun := fun f => (fun c => (f c).1, fun c => (f c).2)
  invFun := fun p c => (p.1 c, p.2 c)
  left_inv := fun f => funext fun c => Prod.mk.eta
  right_inv := fun p => by cases p; rfl
                           -- ⊢ (fun f => (fun c => (f c).fst, fun c => (f c).snd)) ((fun p c => (Prod.fst p …
                                    -- 🎉 no goals
#align equiv.arrow_prod_equiv_prod_arrow Equiv.arrowProdEquivProdArrow

open Sum

/-- The type of functions on a sum type `α ⊕ β` is equivalent to the type of pairs of functions
on `α` and on `β`. -/
def sumArrowEquivProdArrow (α β γ : Type*) : (Sum α β → γ) ≃ (α → γ) × (β → γ) :=
  ⟨fun f => (f ∘ inl, f ∘ inr), fun p => Sum.elim p.1 p.2, fun f => by ext ⟨⟩ <;> rfl, fun p => by
                                                                       -- ⊢ (fun p => Sum.elim p.fst p.snd) ((fun f => (f ∘ inl, f ∘ inr)) f) (inl val✝) …
                                                                                  -- 🎉 no goals
                                                                                  -- 🎉 no goals
    cases p
    -- ⊢ (fun f => (f ∘ inl, f ∘ inr)) ((fun p => Sum.elim p.fst p.snd) (fst✝, snd✝)) …
    rfl⟩
    -- 🎉 no goals
#align equiv.sum_arrow_equiv_prod_arrow Equiv.sumArrowEquivProdArrow

@[simp]
theorem sumArrowEquivProdArrow_apply_fst (f : Sum α β → γ) (a : α) :
    (sumArrowEquivProdArrow α β γ f).1 a = f (inl a) :=
  rfl
#align equiv.sum_arrow_equiv_prod_arrow_apply_fst Equiv.sumArrowEquivProdArrow_apply_fst

@[simp]
theorem sumArrowEquivProdArrow_apply_snd (f : Sum α β → γ) (b : β) :
    (sumArrowEquivProdArrow α β γ f).2 b = f (inr b) :=
  rfl
#align equiv.sum_arrow_equiv_prod_arrow_apply_snd Equiv.sumArrowEquivProdArrow_apply_snd

@[simp]
theorem sumArrowEquivProdArrow_symm_apply_inl (f : α → γ) (g : β → γ) (a : α) :
    ((sumArrowEquivProdArrow α β γ).symm (f, g)) (inl a) = f a :=
  rfl
#align equiv.sum_arrow_equiv_prod_arrow_symm_apply_inl Equiv.sumArrowEquivProdArrow_symm_apply_inl

@[simp]
theorem sumArrowEquivProdArrow_symm_apply_inr (f : α → γ) (g : β → γ) (b : β) :
    ((sumArrowEquivProdArrow α β γ).symm (f, g)) (inr b) = g b :=
  rfl
#align equiv.sum_arrow_equiv_prod_arrow_symm_apply_inr Equiv.sumArrowEquivProdArrow_symm_apply_inr

/-- Type product is right distributive with respect to type sum up to an equivalence. -/
def sumProdDistrib (α β γ) : Sum α β × γ ≃ Sum (α × γ) (β × γ) :=
  ⟨fun p => p.1.map (fun x => (x, p.2)) fun x => (x, p.2),
    fun s => s.elim (Prod.map inl id) (Prod.map inr id), by
      rintro ⟨_ | _, _⟩ <;> rfl, by rintro (⟨_, _⟩ | ⟨_, _⟩) <;> rfl⟩
      -- ⊢ (fun s => Sum.elim (Prod.map inl id) (Prod.map inr id) s) ((fun p => Sum.map …
                            -- 🎉 no goals
                            -- 🎉 no goals
                                    -- ⊢ (fun p => Sum.map (fun x => (x, p.snd)) (fun x => (x, p.snd)) p.fst) ((fun s …
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
#align equiv.sum_prod_distrib Equiv.sumProdDistrib

@[simp]
theorem sumProdDistrib_apply_left (a : α) (c : γ) :
    sumProdDistrib α β γ (Sum.inl a, c) = Sum.inl (a, c) :=
  rfl
#align equiv.sum_prod_distrib_apply_left Equiv.sumProdDistrib_apply_left

@[simp]
theorem sumProdDistrib_apply_right (b : β) (c : γ) :
    sumProdDistrib α β γ (Sum.inr b, c) = Sum.inr (b, c) :=
  rfl
#align equiv.sum_prod_distrib_apply_right Equiv.sumProdDistrib_apply_right

@[simp]
theorem sumProdDistrib_symm_apply_left (a : α × γ) :
    (sumProdDistrib α β γ).symm (inl a) = (inl a.1, a.2) :=
  rfl
#align equiv.sum_prod_distrib_symm_apply_left Equiv.sumProdDistrib_symm_apply_left

@[simp]
theorem sumProdDistrib_symm_apply_right (b : β × γ) :
    (sumProdDistrib α β γ).symm (inr b) = (inr b.1, b.2) :=
  rfl
#align equiv.sum_prod_distrib_symm_apply_right Equiv.sumProdDistrib_symm_apply_right

/-- Type product is left distributive with respect to type sum up to an equivalence. -/
def prodSumDistrib (α β γ) : α × Sum β γ ≃ Sum (α × β) (α × γ) :=
  calc
    α × Sum β γ ≃ Sum β γ × α := prodComm _ _
    _ ≃ Sum (β × α) (γ × α) := sumProdDistrib _ _ _
    _ ≃ Sum (α × β) (α × γ) := sumCongr (prodComm _ _) (prodComm _ _)
#align equiv.prod_sum_distrib Equiv.prodSumDistrib

@[simp]
theorem prodSumDistrib_apply_left (a : α) (b : β) :
    prodSumDistrib α β γ (a, Sum.inl b) = Sum.inl (a, b) :=
  rfl
#align equiv.prod_sum_distrib_apply_left Equiv.prodSumDistrib_apply_left

@[simp]
theorem prodSumDistrib_apply_right (a : α) (c : γ) :
    prodSumDistrib α β γ (a, Sum.inr c) = Sum.inr (a, c) :=
  rfl
#align equiv.prod_sum_distrib_apply_right Equiv.prodSumDistrib_apply_right

@[simp]
theorem prodSumDistrib_symm_apply_left (a : α × β) :
    (prodSumDistrib α β γ).symm (inl a) = (a.1, inl a.2) :=
  rfl
#align equiv.prod_sum_distrib_symm_apply_left Equiv.prodSumDistrib_symm_apply_left

@[simp]
theorem prodSumDistrib_symm_apply_right (a : α × γ) :
    (prodSumDistrib α β γ).symm (inr a) = (a.1, inr a.2) :=
  rfl
#align equiv.prod_sum_distrib_symm_apply_right Equiv.prodSumDistrib_symm_apply_right

/-- An indexed sum of disjoint sums of types is equivalent to the sum of the indexed sums. -/
@[simps]
def sigmaSumDistrib (α β : ι → Type*) :
    (Σ i, Sum (α i) (β i)) ≃ Sum (Σ i, α i) (Σ i, β i) :=
  ⟨fun p => p.2.map (Sigma.mk p.1) (Sigma.mk p.1),
    Sum.elim (Sigma.map id fun _ => Sum.inl) (Sigma.map id fun _ => Sum.inr), fun p => by
    rcases p with ⟨i, a | b⟩ <;> rfl, fun p => by rcases p with (⟨i, a⟩ | ⟨i, b⟩) <;> rfl⟩
    -- ⊢ Sum.elim (Sigma.map id fun x => inl) (Sigma.map id fun x => inr) ((fun p =>  …
                                 -- 🎉 no goals
                                 -- 🎉 no goals
                                                  -- ⊢ (fun p => Sum.map (Sigma.mk p.fst) (Sigma.mk p.fst) p.snd) (Sum.elim (Sigma. …
                                                                                      -- 🎉 no goals
                                                                                      -- 🎉 no goals
#align equiv.sigma_sum_distrib Equiv.sigmaSumDistrib
#align equiv.sigma_sum_distrib_apply Equiv.sigmaSumDistrib_apply
#align equiv.sigma_sum_distrib_symm_apply Equiv.sigmaSumDistrib_symm_apply

/-- The product of an indexed sum of types (formally, a `Sigma`-type `Σ i, α i`) by a type `β` is
equivalent to the sum of products `Σ i, (α i × β)`. -/
def sigmaProdDistrib (α : ι → Type*) (β : Type*) : (Σ i, α i) × β ≃ Σ i, α i × β :=
  ⟨fun p => ⟨p.1.1, (p.1.2, p.2)⟩, fun p => (⟨p.1, p.2.1⟩, p.2.2), fun p => by
    rcases p with ⟨⟨_, _⟩, _⟩
    -- ⊢ (fun p => ({ fst := p.fst, snd := p.snd.fst }, p.snd.snd)) ((fun p => { fst  …
    rfl, fun p => by
    -- 🎉 no goals
    rcases p with ⟨_, ⟨_, _⟩⟩
    -- ⊢ (fun p => { fst := p.fst.fst, snd := (p.fst.snd, p.snd) }) ((fun p => ({ fst …
    rfl⟩
    -- 🎉 no goals
#align equiv.sigma_prod_distrib Equiv.sigmaProdDistrib

/-- An equivalence that separates out the 0th fiber of `(Σ (n : ℕ), f n)`. -/
def sigmaNatSucc (f : ℕ → Type u) : (Σ n, f n) ≃ Sum (f 0) (Σ n, f (n + 1)) :=
  ⟨fun x =>
    @Sigma.casesOn ℕ f (fun _ => Sum (f 0) (Σn, f (n + 1))) x fun n =>
      @Nat.casesOn (fun i => f i → Sum (f 0) (Σn : ℕ, f (n + 1))) n (fun x : f 0 => Sum.inl x)
        fun (n : ℕ) (x : f n.succ) => Sum.inr ⟨n, x⟩,
    Sum.elim (Sigma.mk 0) (Sigma.map Nat.succ fun _ => id), by rintro ⟨n | n, x⟩ <;> rfl, by
                                                               -- ⊢ Sum.elim (Sigma.mk 0) (Sigma.map Nat.succ fun x => id) ((fun x => Sigma.case …
                                                                                     -- 🎉 no goals
                                                                                     -- 🎉 no goals
    rintro (x | ⟨n, x⟩) <;> rfl⟩
    -- ⊢ (fun x => Sigma.casesOn x fun n => Nat.casesOn (motive := fun i => f i → f 0 …
                            -- 🎉 no goals
                            -- 🎉 no goals
#align equiv.sigma_nat_succ Equiv.sigmaNatSucc

/-- The product `Bool × α` is equivalent to `α ⊕ α`. -/
@[simps]
def boolProdEquivSum (α) : Bool × α ≃ Sum α α where
  toFun p := cond p.1 (inr p.2) (inl p.2)
  invFun := Sum.elim (Prod.mk false) (Prod.mk true)
  left_inv := by rintro ⟨_ | _, _⟩ <;> rfl
                 -- ⊢ Sum.elim (Prod.mk false) (Prod.mk true) ((fun p => bif p.fst then inr p.snd  …
                                       -- 🎉 no goals
                                       -- 🎉 no goals
  right_inv := by rintro (_ | _) <;> rfl
                  -- ⊢ (fun p => bif p.fst then inr p.snd else inl p.snd) (Sum.elim (Prod.mk false) …
                                     -- 🎉 no goals
                                     -- 🎉 no goals
#align equiv.bool_prod_equiv_sum Equiv.boolProdEquivSum
#align equiv.bool_prod_equiv_sum_apply Equiv.boolProdEquivSum_apply
#align equiv.bool_prod_equiv_sum_symm_apply Equiv.boolProdEquivSum_symm_apply

/-- The function type `Bool → α` is equivalent to `α × α`. -/
@[simps]
def boolArrowEquivProd (α) : (Bool → α) ≃ α × α where
  toFun f := (f true, f false)
  invFun p b := cond b p.1 p.2
  left_inv _ := funext <| Bool.forall_bool.2 ⟨rfl, rfl⟩
  right_inv := fun _ => rfl
#align equiv.bool_arrow_equiv_prod Equiv.boolArrowEquivProd
#align equiv.bool_arrow_equiv_prod_apply Equiv.boolArrowEquivProd_apply
#align equiv.bool_arrow_equiv_prod_symm_apply Equiv.boolArrowEquivProd_symm_apply

end

section

open Sum Nat

/-- The set of natural numbers is equivalent to `ℕ ⊕ PUnit`. -/
def natEquivNatSumPUnit : ℕ ≃ Sum ℕ PUnit where
  toFun n := Nat.casesOn n (inr PUnit.unit) inl
  invFun := Sum.elim Nat.succ fun _ => 0
  left_inv n := by cases n <;> rfl
                   -- ⊢ Sum.elim succ (fun x => 0) ((fun n => Nat.casesOn n (inr PUnit.unit) inl) ze …
                               -- 🎉 no goals
                               -- 🎉 no goals
  right_inv := by rintro (_ | _) <;> rfl
                  -- ⊢ (fun n => Nat.casesOn n (inr PUnit.unit) inl) (Sum.elim succ (fun x => 0) (i …
                                     -- 🎉 no goals
                                     -- 🎉 no goals
#align equiv.nat_equiv_nat_sum_punit Equiv.natEquivNatSumPUnit

/-- `ℕ ⊕ PUnit` is equivalent to `ℕ`. -/
def natSumPUnitEquivNat : Sum ℕ PUnit ≃ ℕ :=
  natEquivNatSumPUnit.symm
#align equiv.nat_sum_punit_equiv_nat Equiv.natSumPUnitEquivNat

/-- The type of integer numbers is equivalent to `ℕ ⊕ ℕ`. -/
def intEquivNatSumNat : ℤ ≃ Sum ℕ ℕ where
  toFun z := Int.casesOn z inl inr
  invFun := Sum.elim Int.ofNat Int.negSucc
  left_inv := by rintro (m | n) <;> rfl
                 -- ⊢ Sum.elim Int.ofNat Int.negSucc ((fun z => Int.casesOn z inl inr) (Int.ofNat  …
                                    -- 🎉 no goals
                                    -- 🎉 no goals
  right_inv := by rintro (m | n) <;> rfl
                  -- ⊢ (fun z => Int.casesOn z inl inr) (Sum.elim Int.ofNat Int.negSucc (inl m)) =  …
                                     -- 🎉 no goals
                                     -- 🎉 no goals
#align equiv.int_equiv_nat_sum_nat Equiv.intEquivNatSumNat

end

/-- An equivalence between `α` and `β` generates an equivalence between `List α` and `List β`. -/
def listEquivOfEquiv (e : α ≃ β) : List α ≃ List β where
  toFun := List.map e
  invFun := List.map e.symm
  left_inv l := by rw [List.map_map, e.symm_comp_self, List.map_id]
                   -- 🎉 no goals
  right_inv l := by rw [List.map_map, e.self_comp_symm, List.map_id]
                    -- 🎉 no goals
#align equiv.list_equiv_of_equiv Equiv.listEquivOfEquiv

/-- If `α` is equivalent to `β`, then `Unique α` is equivalent to `Unique β`. -/
def uniqueCongr (e : α ≃ β) : Unique α ≃ Unique β where
  toFun h := @Equiv.unique _ _ h e.symm
  invFun h := @Equiv.unique _ _ h e
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align equiv.unique_congr Equiv.uniqueCongr

/-- If `α` is equivalent to `β`, then `IsEmpty α` is equivalent to `IsEmpty β`. -/
theorem isEmpty_congr (e : α ≃ β) : IsEmpty α ↔ IsEmpty β :=
  ⟨fun h => @Function.isEmpty _ _ h e.symm, fun h => @Function.isEmpty _ _ h e⟩
#align equiv.is_empty_congr Equiv.isEmpty_congr

protected theorem isEmpty (e : α ≃ β) [IsEmpty β] : IsEmpty α :=
  e.isEmpty_congr.mpr ‹_›
#align equiv.is_empty Equiv.isEmpty

section

open Subtype

/-- If `α` is equivalent to `β` and the predicates `p : α → Prop` and `q : β → Prop` are equivalent
at corresponding points, then `{a // p a}` is equivalent to `{b // q b}`.
For the statement where `α = β`, that is, `e : perm α`, see `Perm.subtypePerm`. -/
def subtypeEquiv {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : ∀ a, p a ↔ q (e a)) :
    { a : α // p a } ≃ { b : β // q b } where
  toFun a := ⟨e a, (h _).mp a.property⟩
  invFun b := ⟨e.symm b, (h _).mpr ((e.apply_symm_apply b).symm ▸ b.property)⟩
  left_inv a := Subtype.ext <| by simp
                                  -- 🎉 no goals
  right_inv b := Subtype.ext <| by simp
                                   -- 🎉 no goals
#align equiv.subtype_equiv Equiv.subtypeEquiv

@[simp]
theorem subtypeEquiv_refl {p : α → Prop} (h : ∀ a, p a ↔ p (Equiv.refl _ a) := fun a => Iff.rfl) :
    (Equiv.refl α).subtypeEquiv h = Equiv.refl { a : α // p a } := by
  ext
  -- ⊢ ↑(↑(subtypeEquiv (Equiv.refl α) h) x✝) = ↑(↑(Equiv.refl { a // p a }) x✝)
  rfl
  -- 🎉 no goals
#align equiv.subtype_equiv_refl Equiv.subtypeEquiv_refl

@[simp]
theorem subtypeEquiv_symm {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : ∀ a : α, p a ↔ q (e a)) :
    (e.subtypeEquiv h).symm =
      e.symm.subtypeEquiv fun a => by
        convert (h <| e.symm a).symm
        -- ⊢ a = ↑e (↑e.symm a)
        exact (e.apply_symm_apply a).symm :=
        -- 🎉 no goals
  rfl
#align equiv.subtype_equiv_symm Equiv.subtypeEquiv_symm

@[simp]
theorem subtypeEquiv_trans {p : α → Prop} {q : β → Prop} {r : γ → Prop} (e : α ≃ β) (f : β ≃ γ)
    (h : ∀ a : α, p a ↔ q (e a)) (h' : ∀ b : β, q b ↔ r (f b)) :
    (e.subtypeEquiv h).trans (f.subtypeEquiv h')
    = (e.trans f).subtypeEquiv fun a => (h a).trans (h' <| e a) :=
  rfl
#align equiv.subtype_equiv_trans Equiv.subtypeEquiv_trans

@[simp]
theorem subtypeEquiv_apply {p : α → Prop} {q : β → Prop}
    (e : α ≃ β) (h : ∀ a : α, p a ↔ q (e a)) (x : { x // p x }) :
    e.subtypeEquiv h x = ⟨e x, (h _).1 x.2⟩ :=
  rfl
#align equiv.subtype_equiv_apply Equiv.subtypeEquiv_apply

/-- If two predicates `p` and `q` are pointwise equivalent, then `{x // p x}` is equivalent to
`{x // q x}`. -/
@[simps!]
def subtypeEquivRight {p q : α → Prop} (e : ∀ x, p x ↔ q x) : { x // p x } ≃ { x // q x } :=
  subtypeEquiv (Equiv.refl _) e
#align equiv.subtype_equiv_right Equiv.subtypeEquivRight
#align equiv.subtype_equiv_right_apply_coe Equiv.subtypeEquivRight_apply_coe
#align equiv.subtype_equiv_right_symm_apply_coe Equiv.subtypeEquivRight_symm_apply_coe

/-- If `α ≃ β`, then for any predicate `p : β → Prop` the subtype `{a // p (e a)}` is equivalent
to the subtype `{b // p b}`. -/
def subtypeEquivOfSubtype {p : β → Prop} (e : α ≃ β) : { a : α // p (e a) } ≃ { b : β // p b } :=
  subtypeEquiv e <| by simp
                       -- 🎉 no goals
#align equiv.subtype_equiv_of_subtype Equiv.subtypeEquivOfSubtype

/-- If `α ≃ β`, then for any predicate `p : α → Prop` the subtype `{a // p a}` is equivalent
to the subtype `{b // p (e.symm b)}`. This version is used by `equiv_rw`. -/
def subtypeEquivOfSubtype' {p : α → Prop} (e : α ≃ β) :
    { a : α // p a } ≃ { b : β // p (e.symm b) } :=
  e.symm.subtypeEquivOfSubtype.symm
#align equiv.subtype_equiv_of_subtype' Equiv.subtypeEquivOfSubtype'

/-- If two predicates are equal, then the corresponding subtypes are equivalent. -/
def subtypeEquivProp {p q : α → Prop} (h : p = q) : Subtype p ≃ Subtype q :=
  subtypeEquiv (Equiv.refl α) fun _ => h ▸ Iff.rfl
#align equiv.subtype_equiv_prop Equiv.subtypeEquivProp

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. This
version allows the “inner” predicate to depend on `h : p a`. -/
@[simps]
def subtypeSubtypeEquivSubtypeExists (p : α → Prop) (q : Subtype p → Prop) :
    Subtype q ≃ { a : α // ∃ h : p a, q ⟨a, h⟩ } :=
  ⟨fun a =>
    ⟨a.1, a.1.2, by
      rcases a with ⟨⟨a, hap⟩, haq⟩
      -- ⊢ q { val := ↑↑{ val := { val := a, property := hap }, property := haq }, prop …
      exact haq⟩,
      -- 🎉 no goals
    fun a => ⟨⟨a, a.2.fst⟩, a.2.snd⟩, fun ⟨⟨a, ha⟩, h⟩ => rfl, fun ⟨a, h₁, h₂⟩ => rfl⟩
#align equiv.subtype_subtype_equiv_subtype_exists Equiv.subtypeSubtypeEquivSubtypeExists
#align equiv.subtype_subtype_equiv_subtype_exists_symm_apply_coe_coe Equiv.subtypeSubtypeEquivSubtypeExists_symm_apply_coe_coe
#align equiv.subtype_subtype_equiv_subtype_exists_apply_coe Equiv.subtypeSubtypeEquivSubtypeExists_apply_coe

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. -/
@[simps!]
def subtypeSubtypeEquivSubtypeInter {α : Type u} (p q : α → Prop) :
    { x : Subtype p // q x.1 } ≃ Subtype fun x => p x ∧ q x :=
  (subtypeSubtypeEquivSubtypeExists p _).trans <|
    subtypeEquivRight fun x => @exists_prop (q x) (p x)
#align equiv.subtype_subtype_equiv_subtype_inter Equiv.subtypeSubtypeEquivSubtypeInter
#align equiv.subtype_subtype_equiv_subtype_inter_apply_coe Equiv.subtypeSubtypeEquivSubtypeInter_apply_coe
#align equiv.subtype_subtype_equiv_subtype_inter_symm_apply_coe_coe Equiv.subtypeSubtypeEquivSubtypeInter_symm_apply_coe_coe

/-- If the outer subtype has more restrictive predicate than the inner one,
then we can drop the latter. -/
@[simps!]
def subtypeSubtypeEquivSubtype {p q : α → Prop} (h : ∀ {x}, q x → p x) :
    { x : Subtype p // q x.1 } ≃ Subtype q :=
  (subtypeSubtypeEquivSubtypeInter p _).trans <| subtypeEquivRight fun _ => and_iff_right_of_imp h
#align equiv.subtype_subtype_equiv_subtype Equiv.subtypeSubtypeEquivSubtype
#align equiv.subtype_subtype_equiv_subtype_apply_coe Equiv.subtypeSubtypeEquivSubtype_apply_coe
#align equiv.subtype_subtype_equiv_subtype_symm_apply_coe_coe Equiv.subtypeSubtypeEquivSubtype_symm_apply_coe_coe

/-- If a proposition holds for all elements, then the subtype is
equivalent to the original type. -/
@[simps apply symm_apply]
def subtypeUnivEquiv {p : α → Prop} (h : ∀ x, p x) : Subtype p ≃ α :=
  ⟨fun x => x, fun x => ⟨x, h x⟩, fun _ => Subtype.eq rfl, fun _ => rfl⟩
#align equiv.subtype_univ_equiv Equiv.subtypeUnivEquiv
#align equiv.subtype_univ_equiv_apply Equiv.subtypeUnivEquiv_apply
#align equiv.subtype_univ_equiv_symm_apply Equiv.subtypeUnivEquiv_symm_apply

/-- A subtype of a sigma-type is a sigma-type over a subtype. -/
def subtypeSigmaEquiv (p : α → Type v) (q : α → Prop) : { y : Sigma p // q y.1 } ≃ Σ x :
    Subtype q, p x.1 :=
  ⟨fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, fun _ => rfl,
    fun _ => rfl⟩
#align equiv.subtype_sigma_equiv Equiv.subtypeSigmaEquiv

/-- A sigma type over a subtype is equivalent to the sigma set over the original type,
if the fiber is empty outside of the subset -/
def sigmaSubtypeEquivOfSubset (p : α → Type v) (q : α → Prop) (h : ∀ x, p x → q x) :
    (Σ x : Subtype q, p x) ≃ Σ x : α, p x :=
  (subtypeSigmaEquiv p q).symm.trans <| subtypeUnivEquiv fun x => h x.1 x.2
#align equiv.sigma_subtype_equiv_of_subset Equiv.sigmaSubtypeEquivOfSubset

/-- If a predicate `p : β → Prop` is true on the range of a map `f : α → β`, then
`Σ y : {y // p y}, {x // f x = y}` is equivalent to `α`. -/
def sigmaSubtypeFiberEquiv {α β : Type*} (f : α → β) (p : β → Prop) (h : ∀ x, p (f x)) :
    (Σ y : Subtype p, { x : α // f x = y }) ≃ α :=
  calc
    _ ≃ Σy : β, { x : α // f x = y } := sigmaSubtypeEquivOfSubset _ p fun _ ⟨x, h'⟩ => h' ▸ h x
    _ ≃ α := sigmaFiberEquiv f
#align equiv.sigma_subtype_fiber_equiv Equiv.sigmaSubtypeFiberEquiv

/-- If for each `x` we have `p x ↔ q (f x)`, then `Σ y : {y // q y}, f ⁻¹' {y}` is equivalent
to `{x // p x}`. -/
def sigmaSubtypeFiberEquivSubtype {α β : Type*} (f : α → β) {p : α → Prop} {q : β → Prop}
    (h : ∀ x, p x ↔ q (f x)) : (Σ y : Subtype q, { x : α // f x = y }) ≃ Subtype p :=
  calc
    (Σy : Subtype q, { x : α // f x = y }) ≃ Σy :
        Subtype q, { x : Subtype p // Subtype.mk (f x) ((h x).1 x.2) = y } := by {
          apply sigmaCongrRight
          intro y
          apply Equiv.symm
          refine' (subtypeSubtypeEquivSubtypeExists _ _).trans (subtypeEquivRight _)
          intro x
          exact ⟨fun ⟨hp, h'⟩ => congr_arg Subtype.val h', fun h' => ⟨(h x).2 (h'.symm ▸ y.2),
            Subtype.eq h'⟩⟩ }
    _ ≃ Subtype p := sigmaFiberEquiv fun x : Subtype p => (⟨f x, (h x).1 x.property⟩ : Subtype q)
#align equiv.sigma_subtype_fiber_equiv_subtype Equiv.sigmaSubtypeFiberEquivSubtype

/-- A sigma type over an `Option` is equivalent to the sigma set over the original type,
if the fiber is empty at none. -/
def sigmaOptionEquivOfSome (p : Option α → Type v) (h : p none → False) :
    (Σ x : Option α, p x) ≃ Σ x : α, p (some x) :=
  haveI h' : ∀ x, p x → x.isSome := by
    intro x
    -- ⊢ p x → Option.isSome x = true
    cases x
    -- ⊢ p none → Option.isSome none = true
    · intro n
      -- ⊢ Option.isSome none = true
      exfalso
      -- ⊢ False
      exact h n
      -- 🎉 no goals
    · intro _
      -- ⊢ Option.isSome (some val✝) = true
      exact rfl
      -- 🎉 no goals
  (sigmaSubtypeEquivOfSubset _ _ h').symm.trans (sigmaCongrLeft' (optionIsSomeEquiv α))
#align equiv.sigma_option_equiv_of_some Equiv.sigmaOptionEquivOfSome

/-- The `Pi`-type `∀ i, π i` is equivalent to the type of sections `f : ι → Σ i, π i` of the
`Sigma` type such that for all `i` we have `(f i).fst = i`. -/
def piEquivSubtypeSigma (ι) (π : ι → Type*) :
    (∀ i, π i) ≃ { f : ι → Σ i, π i // ∀ i, (f i).1 = i } where
  toFun := fun f => ⟨fun i => ⟨i, f i⟩, fun i => rfl⟩
  invFun := fun f i => by rw [← f.2 i]; exact (f.1 i).2
                          -- ⊢ π (↑f i).fst
                                        -- 🎉 no goals
  left_inv := fun f => funext fun i => rfl
  right_inv := fun ⟨f, hf⟩ =>
    Subtype.eq <| funext fun i =>
      Sigma.eq (hf i).symm <| eq_of_heq <| rec_heq_of_heq _ <| by simp
                                                                  -- 🎉 no goals
#align equiv.pi_equiv_subtype_sigma Equiv.piEquivSubtypeSigma

/-- The type of functions `f : ∀ a, β a` such that for all `a` we have `p a (f a)` is equivalent
to the type of functions `∀ a, {b : β a // p a b}`. -/
def subtypePiEquivPi {β : α → Sort v} {p : ∀ a, β a → Prop} :
    { f : ∀ a, β a // ∀ a, p a (f a) } ≃ ∀ a, { b : β a // p a b } where
  toFun := fun f a => ⟨f.1 a, f.2 a⟩
  invFun := fun f => ⟨fun a => (f a).1, fun a => (f a).2⟩
  left_inv := by
    rintro ⟨f, h⟩
    -- ⊢ (fun f => { val := fun a => ↑(f a), property := (_ : ∀ (a : α), p a ↑(f a))  …
    rfl
    -- 🎉 no goals
  right_inv := by
    rintro f
    -- ⊢ (fun f a => { val := ↑f a, property := (_ : p a (↑f a)) }) ((fun f => { val  …
    funext a
    -- ⊢ (fun f a => { val := ↑f a, property := (_ : p a (↑f a)) }) ((fun f => { val  …
    exact Subtype.ext_val rfl
    -- 🎉 no goals
#align equiv.subtype_pi_equiv_pi Equiv.subtypePiEquivPi

/-- A subtype of a product defined by componentwise conditions
is equivalent to a product of subtypes. -/
def subtypeProdEquivProd {p : α → Prop} {q : β → Prop} :
    { c : α × β // p c.1 ∧ q c.2 } ≃ { a // p a } × { b // q b } where
  toFun := fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩
  invFun := fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩
  left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
#align equiv.subtype_prod_equiv_prod Equiv.subtypeProdEquivProd

/-- A subtype of a `Prod` is equivalent to a sigma type whose fibers are subtypes. -/
def subtypeProdEquivSigmaSubtype (p : α → β → Prop) :
    { x : α × β // p x.1 x.2 } ≃ Σa, { b : β // p a b } where
  toFun x := ⟨x.1.1, x.1.2, x.property⟩
  invFun x := ⟨⟨x.1, x.2⟩, x.2.property⟩
  left_inv x := by ext <;> rfl
                   -- ⊢ (↑((fun x => { val := (x.fst, ↑x.snd), property := (_ : p x.fst ↑x.snd) }) ( …
                           -- 🎉 no goals
                           -- 🎉 no goals
  right_inv := fun ⟨a, b, pab⟩ => rfl
#align equiv.subtype_prod_equiv_sigma_subtype Equiv.subtypeProdEquivSigmaSubtype

/-- The type `∀ (i : α), β i` can be split as a product by separating the indices in `α`
depending on whether they satisfy a predicate `p` or not. -/
@[simps]
def piEquivPiSubtypeProd {α : Type*} (p : α → Prop) (β : α → Type*) [DecidablePred p] :
    (∀ i : α, β i) ≃ (∀ i : { x // p x }, β i) × ∀ i : { x // ¬p x }, β i where
  toFun f := (fun x => f x, fun x => f x)
  invFun f x := if h : p x then f.1 ⟨x, h⟩ else f.2 ⟨x, h⟩
  right_inv := by
    rintro ⟨f, g⟩
    -- ⊢ (fun f => (fun x => f ↑x, fun x => f ↑x)) ((fun f x => if h : p x then Prod. …
    ext1 <;>
    -- ⊢ ((fun f => (fun x => f ↑x, fun x => f ↑x)) ((fun f x => if h : p x then Prod …
      · ext y
        -- ⊢ Prod.fst ((fun f => (fun x => f ↑x, fun x => f ↑x)) ((fun f x => if h : p x  …
        -- ⊢ Prod.snd ((fun f => (fun x => f ↑x, fun x => f ↑x)) ((fun f x => if h : p x  …
    -- ⊢ (fun f x => if h : p x then Prod.fst f { val := x, property := h } else Prod …
        -- ⊢ Prod.fst ((fun f => (fun x => f ↑x, fun x => f ↑x)) ((fun f x => if h : p x  …
    -- ⊢ (fun f x => if h : p x then Prod.fst f { val := x, property := h } else Prod …
        rcases y with ⟨val, property⟩
        -- 🎉 no goals
        -- 🎉 no goals
        -- 🎉 no goals
        -- ⊢ Prod.snd ((fun f => (fun x => f ↑x, fun x => f ↑x)) ((fun f x => if h : p x  …
        simp only [property, dif_pos, dif_neg, not_false_iff, Subtype.coe_mk]
        -- 🎉 no goals
  left_inv f := by
    ext x
    by_cases h:p x <;>
      · simp only [h, dif_neg, dif_pos, not_false_iff]
#align equiv.pi_equiv_pi_subtype_prod Equiv.piEquivPiSubtypeProd
#align equiv.pi_equiv_pi_subtype_prod_symm_apply Equiv.piEquivPiSubtypeProd_symm_apply
#align equiv.pi_equiv_pi_subtype_prod_apply Equiv.piEquivPiSubtypeProd_apply

/-- A product of types can be split as the binary product of one of the types and the product
  of all the remaining types. -/
@[simps]
def piSplitAt {α : Type*} [DecidableEq α] (i : α) (β : α → Type*) :
    (∀ j, β j) ≃ β i × ∀ j : { j // j ≠ i }, β j where
  toFun f := ⟨f i, fun j => f j⟩
  invFun f j := if h : j = i then h.symm.rec f.1 else f.2 ⟨j, h⟩
  right_inv f := by
    ext x
    -- ⊢ ((fun f => (f i, fun j => f ↑j)) ((fun f j => if h : j = i then (_ : i = j)  …
    exacts [dif_pos rfl, (dif_neg x.2).trans (by cases x; rfl)]
    -- 🎉 no goals
    -- ⊢ (fun f j => if h : j = i then (_ : i = j) ▸ f.fst else Prod.snd f { val := j …
  left_inv f := by
    -- ⊢ (if h : x = i then (_ : i = x) ▸ f i else f x) = f x
    ext x
    -- ⊢ (_ : i = x) ▸ f i = f x
    dsimp only
      -- ⊢ (_ : x = x) ▸ f x = f x
               -- 🎉 no goals
    split_ifs with h
      -- 🎉 no goals
    · subst h; rfl
    · rfl
#align equiv.pi_split_at Equiv.piSplitAt
#align equiv.pi_split_at_apply Equiv.piSplitAt_apply
#align equiv.pi_split_at_symm_apply Equiv.piSplitAt_symm_apply

/-- A product of copies of a type can be split as the binary product of one copy and the product
  of all the remaining copies. -/
@[simps!]
def funSplitAt {α : Type*} [DecidableEq α] (i : α) (β : Type*) :
    (α → β) ≃ β × ({ j // j ≠ i } → β) :=
  piSplitAt i _
#align equiv.fun_split_at Equiv.funSplitAt
#align equiv.fun_split_at_symm_apply Equiv.funSplitAt_symm_apply
#align equiv.fun_split_at_apply Equiv.funSplitAt_apply

end

section subtypeEquivCodomain

variable [DecidableEq X] {x : X}

/-- The type of all functions `X → Y` with prescribed values for all `x' ≠ x`
is equivalent to the codomain `Y`. -/
def subtypeEquivCodomain (f : { x' // x' ≠ x } → Y) :
    { g : X → Y // g ∘ (↑) = f } ≃ Y :=
  (subtypePreimage _ f).trans <|
    @funUnique { x' // ¬x' ≠ x } _ <|
      show Unique { x' // ¬x' ≠ x } from
        @Equiv.unique _ _
          (show Unique { x' // x' = x } from {
            default := ⟨x, rfl⟩, uniq := fun ⟨_, h⟩ => Subtype.val_injective h })
          (subtypeEquivRight fun _ => not_not)
#align equiv.subtype_equiv_codomain Equiv.subtypeEquivCodomain

@[simp]
theorem coe_subtypeEquivCodomain (f : { x' // x' ≠ x } → Y) :
    (subtypeEquivCodomain f : _ → Y) =
      fun g : { g : X → Y // g ∘ (↑) = f } => (g : X → Y) x :=
  rfl
#align equiv.coe_subtype_equiv_codomain Equiv.coe_subtypeEquivCodomain

@[simp]
theorem subtypeEquivCodomain_apply (f : { x' // x' ≠ x } → Y) (g) :
    subtypeEquivCodomain f g = (g : X → Y) x :=
  rfl
#align equiv.subtype_equiv_codomain_apply Equiv.subtypeEquivCodomain_apply

theorem coe_subtypeEquivCodomain_symm (f : { x' // x' ≠ x } → Y) :
    ((subtypeEquivCodomain f).symm : Y → _) = fun y =>
      ⟨fun x' => if h : x' ≠ x then f ⟨x', h⟩ else y, by
        funext x'
        -- ⊢ ((fun x' => if h : x' ≠ x then f { val := x', property := h } else y) ∘ Subt …
        simp only [ne_eq, dite_not, comp_apply, Subtype.coe_eta, dite_eq_ite, ite_eq_right_iff]
        -- ⊢ ↑x' = x → y = f x'
        intro w
        -- ⊢ y = f x'
        exfalso
        -- ⊢ False
        exact x'.property w⟩ :=
        -- 🎉 no goals
  rfl
#align equiv.coe_subtype_equiv_codomain_symm Equiv.coe_subtypeEquivCodomain_symm

@[simp]
theorem subtypeEquivCodomain_symm_apply (f : { x' // x' ≠ x } → Y) (y : Y) (x' : X) :
    ((subtypeEquivCodomain f).symm y : X → Y) x' = if h : x' ≠ x then f ⟨x', h⟩ else y :=
  rfl
#align equiv.subtype_equiv_codomain_symm_apply Equiv.subtypeEquivCodomain_symm_apply

theorem subtypeEquivCodomain_symm_apply_eq (f : { x' // x' ≠ x } → Y) (y : Y) :
    ((subtypeEquivCodomain f).symm y : X → Y) x = y :=
  dif_neg (not_not.mpr rfl)
#align equiv.subtype_equiv_codomain_symm_apply_eq Equiv.subtypeEquivCodomain_symm_apply_eq

theorem subtypeEquivCodomain_symm_apply_ne
    (f : { x' // x' ≠ x } → Y) (y : Y) (x' : X) (h : x' ≠ x) :
    ((subtypeEquivCodomain f).symm y : X → Y) x' = f ⟨x', h⟩ :=
  dif_pos h
#align equiv.subtype_equiv_codomain_symm_apply_ne Equiv.subtypeEquivCodomain_symm_apply_ne

end subtypeEquivCodomain

/-- If `f` is a bijective function, then its domain is equivalent to its codomain. -/
@[simps apply]
noncomputable def ofBijective (f : α → β) (hf : Bijective f) : α ≃ β where
  toFun := f
  invFun := Function.surjInv hf.surjective
  left_inv := Function.leftInverse_surjInv hf
  right_inv := Function.rightInverse_surjInv _
#align equiv.of_bijective Equiv.ofBijective
#align equiv.of_bijective_apply Equiv.ofBijective_apply

theorem ofBijective_apply_symm_apply (f : α → β) (hf : Bijective f) (x : β) :
    f ((ofBijective f hf).symm x) = x :=
  (ofBijective f hf).apply_symm_apply x
#align equiv.of_bijective_apply_symm_apply Equiv.ofBijective_apply_symm_apply

@[simp]
theorem ofBijective_symm_apply_apply (f : α → β) (hf : Bijective f) (x : α) :
    (ofBijective f hf).symm (f x) = x :=
  (ofBijective f hf).symm_apply_apply x
#align equiv.of_bijective_symm_apply_apply Equiv.ofBijective_symm_apply_apply

instance : CanLift (α → β) (α ≃ β) (↑) Bijective where prf f hf := ⟨ofBijective f hf, rfl⟩

section

variable {α' β' : Type*} (e : Perm α') {p : β' → Prop} [DecidablePred p] (f : α' ≃ Subtype p)

/-- Extend the domain of `e : Equiv.Perm α` to one that is over `β` via `f : α → Subtype p`,
where `p : β → Prop`, permuting only the `b : β` that satisfy `p b`.
This can be used to extend the domain across a function `f : α → β`,
keeping everything outside of `Set.range f` fixed. For this use-case `Equiv` given by `f` can
be constructed by `Equiv.of_leftInverse'` or `Equiv.of_leftInverse` when there is a known
inverse, or `Equiv.ofInjective` in the general case.
-/
def Perm.extendDomain : Perm β' :=
  (permCongr f e).subtypeCongr (Equiv.refl _)
#align equiv.perm.extend_domain Equiv.Perm.extendDomain

@[simp]
theorem Perm.extendDomain_apply_image (a : α') : e.extendDomain f (f a) = f (e a) := by
  simp [Perm.extendDomain]
  -- 🎉 no goals
#align equiv.perm.extend_domain_apply_image Equiv.Perm.extendDomain_apply_image

theorem Perm.extendDomain_apply_subtype {b : β'} (h : p b) :
    e.extendDomain f b = f (e (f.symm ⟨b, h⟩)) := by
  simp [Perm.extendDomain, h]
  -- 🎉 no goals
#align equiv.perm.extend_domain_apply_subtype Equiv.Perm.extendDomain_apply_subtype

theorem Perm.extendDomain_apply_not_subtype {b : β'} (h : ¬p b) : e.extendDomain f b = b := by
  simp [Perm.extendDomain, h]
  -- 🎉 no goals
#align equiv.perm.extend_domain_apply_not_subtype Equiv.Perm.extendDomain_apply_not_subtype

@[simp]
theorem Perm.extendDomain_refl : Perm.extendDomain (Equiv.refl _) f = Equiv.refl _ := by
  simp [Perm.extendDomain]
  -- 🎉 no goals
#align equiv.perm.extend_domain_refl Equiv.Perm.extendDomain_refl

@[simp]
theorem Perm.extendDomain_symm : (e.extendDomain f).symm = Perm.extendDomain e.symm f :=
  rfl
#align equiv.perm.extend_domain_symm Equiv.Perm.extendDomain_symm

theorem Perm.extendDomain_trans (e e' : Perm α') :
    (e.extendDomain f).trans (e'.extendDomain f) = Perm.extendDomain (e.trans e') f := by
  simp [Perm.extendDomain, permCongr_trans]
  -- 🎉 no goals
#align equiv.perm.extend_domain_trans Equiv.Perm.extendDomain_trans

end

/-- Subtype of the quotient is equivalent to the quotient of the subtype. Let `α` be a setoid with
equivalence relation `~`. Let `p₂` be a predicate on the quotient type `α/~`, and `p₁` be the lift
of this predicate to `α`: `p₁ a ↔ p₂ ⟦a⟧`. Let `~₂` be the restriction of `~` to `{x // p₁ x}`.
Then `{x // p₂ x}` is equivalent to the quotient of `{x // p₁ x}` by `~₂`. -/
def subtypeQuotientEquivQuotientSubtype (p₁ : α → Prop) [s₁ : Setoid α] [s₂ : Setoid (Subtype p₁)]
    (p₂ : Quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧)
    (h : ∀ x y : Subtype p₁, @Setoid.r _ s₂ x y ↔ (x : α) ≈ y) :
    { x // p₂ x } ≃ Quotient s₂ where
  toFun a :=
    Quotient.hrecOn a.1 (fun a h => ⟦⟨a, (hp₂ _).2 h⟩⟧)
      (fun a b hab => hfunext (by rw [Quotient.sound hab]) fun h₁ h₂ _ =>
                                  -- 🎉 no goals
        heq_of_eq (Quotient.sound ((h _ _).2 hab)))
      a.2
  invFun a :=
    Quotient.liftOn a (fun a => (⟨⟦a.1⟧, (hp₂ _).1 a.2⟩ : { x // p₂ x })) fun a b hab =>
      Subtype.ext_val (Quotient.sound ((h _ _).1 hab))
  left_inv := by exact fun ⟨a, ha⟩ => Quotient.inductionOn a (fun b hb => rfl) ha
                 -- 🎉 no goals
  right_inv a := Quotient.inductionOn a fun ⟨a, ha⟩ => rfl
#align equiv.subtype_quotient_equiv_quotient_subtype Equiv.subtypeQuotientEquivQuotientSubtype

@[simp]
theorem subtypeQuotientEquivQuotientSubtype_mk (p₁ : α → Prop)
    [s₁ : Setoid α] [s₂ : Setoid (Subtype p₁)] (p₂ : Quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧)
    (h : ∀ x y : Subtype p₁, @Setoid.r _ s₂ x y ↔ (x : α) ≈ y)
    (x hx) : subtypeQuotientEquivQuotientSubtype p₁ p₂ hp₂ h ⟨⟦x⟧, hx⟩ = ⟦⟨x, (hp₂ _).2 hx⟩⟧ :=
  rfl
#align equiv.subtype_quotient_equiv_quotient_subtype_mk Equiv.subtypeQuotientEquivQuotientSubtype_mk

@[simp]
theorem subtypeQuotientEquivQuotientSubtype_symm_mk (p₁ : α → Prop)
    [s₁ : Setoid α] [s₂ : Setoid (Subtype p₁)] (p₂ : Quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧)
    (h : ∀ x y : Subtype p₁, @Setoid.r _ s₂ x y ↔ (x : α) ≈ y) (x) :
    (subtypeQuotientEquivQuotientSubtype p₁ p₂ hp₂ h).symm ⟦x⟧ = ⟨⟦x⟧, (hp₂ _).1 x.property⟩ :=
  rfl
#align equiv.subtype_quotient_equiv_quotient_subtype_symm_mk Equiv.subtypeQuotientEquivQuotientSubtype_symm_mk

section Swap

variable [DecidableEq α]

/-- A helper function for `Equiv.swap`. -/
def swapCore (a b r : α) : α :=
  if r = a then b else if r = b then a else r
#align equiv.swap_core Equiv.swapCore

theorem swapCore_self (r a : α) : swapCore a a r = r := by
  unfold swapCore
  -- ⊢ (if r = a then a else if r = a then a else r) = r
  split_ifs <;> simp [*]
  -- ⊢ a = r
                -- 🎉 no goals
                -- 🎉 no goals
#align equiv.swap_core_self Equiv.swapCore_self

theorem swapCore_swapCore (r a b : α) : swapCore a b (swapCore a b r) = r := by
  unfold swapCore
  -- ⊢ (if (if r = a then b else if r = b then a else r) = a then b else if (if r = …
  -- Porting note: cc missing.
  -- `casesm` would work here, with `casesm _ = _, ¬ _ = _`,
  -- if it would just continue past failures on hypotheses matching the pattern
  split_ifs with h₁ h₂ h₃ h₄ h₅
  · subst h₁; exact h₂
    -- ⊢ b = r
              -- 🎉 no goals
  · subst h₁; rfl
    -- ⊢ r = r
              -- 🎉 no goals
  · cases h₃ rfl
    -- 🎉 no goals
  · exact h₄.symm
    -- 🎉 no goals
  · cases h₅ rfl
    -- 🎉 no goals
  · cases h₅ rfl
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
#align equiv.swap_core_swap_core Equiv.swapCore_swapCore

theorem swapCore_comm (r a b : α) : swapCore a b r = swapCore b a r := by
  unfold swapCore
  -- ⊢ (if r = a then b else if r = b then a else r) = if r = b then a else if r =  …
  -- Porting note: whatever solution works for `swapCore_swapCore` will work here too.
  split_ifs with h₁ h₂ h₃ <;> try simp
                              -- ⊢ b = a
                              -- 🎉 no goals
                              -- 🎉 no goals
                              -- 🎉 no goals
  · cases h₁; cases h₂; rfl
    -- ⊢ b = r
              -- ⊢ r = r
                        -- 🎉 no goals
#align equiv.swap_core_comm Equiv.swapCore_comm

/-- `swap a b` is the permutation that swaps `a` and `b` and
  leaves other values as is. -/
def swap (a b : α) : Perm α :=
  ⟨swapCore a b, swapCore a b, fun r => swapCore_swapCore r a b,
    fun r => swapCore_swapCore r a b⟩
#align equiv.swap Equiv.swap

@[simp]
theorem swap_self (a : α) : swap a a = Equiv.refl _ :=
  ext fun r => swapCore_self r a
#align equiv.swap_self Equiv.swap_self

theorem swap_comm (a b : α) : swap a b = swap b a :=
  ext fun r => swapCore_comm r _ _
#align equiv.swap_comm Equiv.swap_comm

theorem swap_apply_def (a b x : α) : swap a b x = if x = a then b else if x = b then a else x :=
  rfl
#align equiv.swap_apply_def Equiv.swap_apply_def

@[simp]
theorem swap_apply_left (a b : α) : swap a b a = b :=
  if_pos rfl
#align equiv.swap_apply_left Equiv.swap_apply_left

@[simp]
theorem swap_apply_right (a b : α) : swap a b b = a := by
  by_cases h:b = a <;> simp [swap_apply_def, h]
  -- ⊢ ↑(swap a b) b = a
                       -- 🎉 no goals
                       -- 🎉 no goals
#align equiv.swap_apply_right Equiv.swap_apply_right

theorem swap_apply_of_ne_of_ne {a b x : α} : x ≠ a → x ≠ b → swap a b x = x := by
  simp (config := { contextual := true }) [swap_apply_def]
  -- 🎉 no goals
#align equiv.swap_apply_of_ne_of_ne Equiv.swap_apply_of_ne_of_ne

@[simp]
theorem swap_swap (a b : α) : (swap a b).trans (swap a b) = Equiv.refl _ :=
  ext fun _ => swapCore_swapCore _ _ _
#align equiv.swap_swap Equiv.swap_swap

@[simp]
theorem symm_swap (a b : α) : (swap a b).symm = swap a b :=
  rfl
#align equiv.symm_swap Equiv.symm_swap

@[simp]
theorem swap_eq_refl_iff {x y : α} : swap x y = Equiv.refl _ ↔ x = y := by
  refine' ⟨fun h => (Equiv.refl _).injective _, fun h => h ▸ swap_self _⟩
  -- ⊢ ↑(Equiv.refl α) x = ↑(Equiv.refl α) y
  rw [← h, swap_apply_left, h, refl_apply]
  -- 🎉 no goals
#align equiv.swap_eq_refl_iff Equiv.swap_eq_refl_iff

theorem swap_comp_apply {a b x : α} (π : Perm α) :
    π.trans (swap a b) x = if π x = a then b else if π x = b then a else π x := by
  cases π
  -- ⊢ ↑({ toFun := toFun✝, invFun := invFun✝, left_inv := left_inv✝, right_inv :=  …
  rfl
  -- 🎉 no goals
#align equiv.swap_comp_apply Equiv.swap_comp_apply

theorem swap_eq_update (i j : α) : (Equiv.swap i j : α → α) = update (update id j i) i j :=
  funext fun x => by rw [update_apply _ i j, update_apply _ j i, Equiv.swap_apply_def, id.def]
                     -- 🎉 no goals
#align equiv.swap_eq_update Equiv.swap_eq_update

theorem comp_swap_eq_update (i j : α) (f : α → β) :
    f ∘ Equiv.swap i j = update (update f j (f i)) i (f j) := by
  rw [swap_eq_update, comp_update, comp_update, comp.right_id]
  -- 🎉 no goals
#align equiv.comp_swap_eq_update Equiv.comp_swap_eq_update

@[simp]
theorem symm_trans_swap_trans [DecidableEq β] (a b : α) (e : α ≃ β) :
    (e.symm.trans (swap a b)).trans e = swap (e a) (e b) :=
  Equiv.ext fun x => by
    have : ∀ a, e.symm x = a ↔ x = e a := fun a => by
      rw [@eq_comm _ (e.symm x)]
      constructor <;> intros <;> simp_all
    simp [trans_apply, swap_apply_def, this]
    -- ⊢ ↑e (if x = ↑e a then b else if x = ↑e b then a else ↑e.symm x) = if x = ↑e a …
    split_ifs <;> simp
                  -- 🎉 no goals
                  -- 🎉 no goals
                  -- 🎉 no goals
#align equiv.symm_trans_swap_trans Equiv.symm_trans_swap_trans

@[simp]
theorem trans_swap_trans_symm [DecidableEq β] (a b : β) (e : α ≃ β) :
    (e.trans (swap a b)).trans e.symm = swap (e.symm a) (e.symm b) :=
  symm_trans_swap_trans a b e.symm
#align equiv.trans_swap_trans_symm Equiv.trans_swap_trans_symm

@[simp]
theorem swap_apply_self (i j a : α) : swap i j (swap i j a) = a := by
  rw [← Equiv.trans_apply, Equiv.swap_swap, Equiv.refl_apply]
  -- 🎉 no goals
#align equiv.swap_apply_self Equiv.swap_apply_self

/-- A function is invariant to a swap if it is equal at both elements -/
theorem apply_swap_eq_self {v : α → β} {i j : α} (hv : v i = v j) (k : α) :
    v (swap i j k) = v k := by
  by_cases hi : k = i
  -- ⊢ v (↑(swap i j) k) = v k
  · rw [hi, swap_apply_left, hv]
    -- 🎉 no goals

  by_cases hj : k = j
  -- ⊢ v (↑(swap i j) k) = v k
  · rw [hj, swap_apply_right, hv]
    -- 🎉 no goals

  rw [swap_apply_of_ne_of_ne hi hj]
  -- 🎉 no goals
#align equiv.apply_swap_eq_self Equiv.apply_swap_eq_self

theorem swap_apply_eq_iff {x y z w : α} : swap x y z = w ↔ z = swap x y w := by
  rw [apply_eq_iff_eq_symm_apply, symm_swap]
  -- 🎉 no goals
#align equiv.swap_apply_eq_iff Equiv.swap_apply_eq_iff

theorem swap_apply_ne_self_iff {a b x : α} : swap a b x ≠ x ↔ a ≠ b ∧ (x = a ∨ x = b) := by
  by_cases hab : a = b
  -- ⊢ ↑(swap a b) x ≠ x ↔ a ≠ b ∧ (x = a ∨ x = b)
  · simp [hab]
    -- 🎉 no goals

  by_cases hax : x = a
  -- ⊢ ↑(swap a b) x ≠ x ↔ a ≠ b ∧ (x = a ∨ x = b)
  · simp [hax, eq_comm]
    -- 🎉 no goals

  by_cases hbx : x = b
  -- ⊢ ↑(swap a b) x ≠ x ↔ a ≠ b ∧ (x = a ∨ x = b)
  · simp [hbx]
    -- 🎉 no goals

  simp [hab, hax, hbx, swap_apply_of_ne_of_ne]
  -- 🎉 no goals
#align equiv.swap_apply_ne_self_iff Equiv.swap_apply_ne_self_iff

namespace Perm

@[simp]
theorem sumCongr_swap_refl {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : α) :
    Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.refl β) = Equiv.swap (Sum.inl i) (Sum.inl j) := by
  ext x
  -- ⊢ ↑(sumCongr (swap i j) (Equiv.refl β)) x = ↑(swap (Sum.inl i) (Sum.inl j)) x
  cases x
  -- ⊢ ↑(sumCongr (swap i j) (Equiv.refl β)) (Sum.inl val✝) = ↑(swap (Sum.inl i) (S …
  · simp only [Equiv.sumCongr_apply, Sum.map, coe_refl, comp.right_id, Sum.elim_inl, comp_apply,
      swap_apply_def, Sum.inl.injEq]
    split_ifs <;> rfl
                  -- 🎉 no goals
                  -- 🎉 no goals
                  -- 🎉 no goals
  · simp [Sum.map, swap_apply_of_ne_of_ne]
    -- 🎉 no goals
#align equiv.perm.sum_congr_swap_refl Equiv.Perm.sumCongr_swap_refl

@[simp]
theorem sumCongr_refl_swap {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : β) :
    Equiv.Perm.sumCongr (Equiv.refl α) (Equiv.swap i j) = Equiv.swap (Sum.inr i) (Sum.inr j) := by
  ext x
  -- ⊢ ↑(sumCongr (Equiv.refl α) (swap i j)) x = ↑(swap (Sum.inr i) (Sum.inr j)) x
  cases x
  -- ⊢ ↑(sumCongr (Equiv.refl α) (swap i j)) (Sum.inl val✝) = ↑(swap (Sum.inr i) (S …
  · simp [Sum.map, swap_apply_of_ne_of_ne]
    -- 🎉 no goals

  · simp only [Equiv.sumCongr_apply, Sum.map, coe_refl, comp.right_id, Sum.elim_inr, comp_apply,
      swap_apply_def, Sum.inr.injEq]
    split_ifs <;> rfl
                  -- 🎉 no goals
                  -- 🎉 no goals
                  -- 🎉 no goals
#align equiv.perm.sum_congr_refl_swap Equiv.Perm.sumCongr_refl_swap

end Perm

/-- Augment an equivalence with a prescribed mapping `f a = b` -/
def setValue (f : α ≃ β) (a : α) (b : β) : α ≃ β :=
  (swap a (f.symm b)).trans f
#align equiv.set_value Equiv.setValue

@[simp]
theorem setValue_eq (f : α ≃ β) (a : α) (b : β) : setValue f a b a = b := by
  simp [setValue, swap_apply_left]
  -- 🎉 no goals
#align equiv.set_value_eq Equiv.setValue_eq

end Swap

end Equiv

namespace Function.Involutive

/-- Convert an involutive function `f` to a permutation with `toFun = invFun = f`. -/
def toPerm (f : α → α) (h : Involutive f) : Equiv.Perm α :=
  ⟨f, f, h.leftInverse, h.rightInverse⟩
#align function.involutive.to_perm Function.Involutive.toPerm

@[simp]
theorem coe_toPerm {f : α → α} (h : Involutive f) : (h.toPerm f : α → α) = f :=
  rfl
#align function.involutive.coe_to_perm Function.Involutive.coe_toPerm

@[simp]
theorem toPerm_symm {f : α → α} (h : Involutive f) : (h.toPerm f).symm = h.toPerm f :=
  rfl
#align function.involutive.to_perm_symm Function.Involutive.toPerm_symm

theorem toPerm_involutive {f : α → α} (h : Involutive f) : Involutive (h.toPerm f) :=
  h
#align function.involutive.to_perm_involutive Function.Involutive.toPerm_involutive

end Function.Involutive

theorem PLift.eq_up_iff_down_eq {x : PLift α} {y : α} : x = PLift.up y ↔ x.down = y :=
  Equiv.plift.eq_symm_apply
#align plift.eq_up_iff_down_eq PLift.eq_up_iff_down_eq

theorem Function.Injective.map_swap [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (x y z : α) :
    f (Equiv.swap x y z) = Equiv.swap (f x) (f y) (f z) := by
  conv_rhs => rw [Equiv.swap_apply_def]
  -- ⊢ f (↑(Equiv.swap x y) z) = if f z = f x then f y else if f z = f y then f x e …
  split_ifs with h₁ h₂
  · rw [hf h₁, Equiv.swap_apply_left]
    -- 🎉 no goals
  · rw [hf h₂, Equiv.swap_apply_right]
    -- 🎉 no goals
  · rw [Equiv.swap_apply_of_ne_of_ne (mt (congr_arg f) h₁) (mt (congr_arg f) h₂)]
    -- 🎉 no goals
#align function.injective.map_swap Function.Injective.map_swap

namespace Equiv

section

variable (P : α → Sort w) (e : α ≃ β)

/-- Transport dependent functions through an equivalence of the base space.
-/
@[simps]
def piCongrLeft' (P : α → Sort*) (e : α ≃ β) : (∀ a, P a) ≃ ∀ b, P (e.symm b) where
  toFun f x := f (e.symm x)
  invFun f x := (e.symm_apply_apply x).ndrec (f (e x))
  left_inv f := funext fun x =>
    (by rintro _ rfl; rfl : ∀ {y} (h : y = x), h.ndrec (f y) = f x) (e.symm_apply_apply x)
        -- ⊢ (_ : y✝ = y✝) ▸ f y✝ = f y✝
                      -- 🎉 no goals
  right_inv f := funext fun x =>
    (by rintro _ rfl; rfl : ∀ {y} (h : y = x), (congr_arg e.symm h).ndrec (f y) = f x)
        -- ⊢ (_ : ↑e.symm y✝ = ↑e.symm y✝) ▸ f y✝ = f y✝
                      -- 🎉 no goals
      (e.apply_symm_apply x)
#align equiv.Pi_congr_left' Equiv.piCongrLeft'
#align equiv.Pi_congr_left'_apply Equiv.piCongrLeft'_apply
#align equiv.Pi_congr_left'_symm_apply Equiv.piCongrLeft'_symm_apply

end

section

variable (P : β → Sort w) (e : α ≃ β)

/-- Transporting dependent functions through an equivalence of the base,
expressed as a "simplification".
-/
def piCongrLeft : (∀ a, P (e a)) ≃ ∀ b, P b :=
  (piCongrLeft' P e.symm).symm
#align equiv.Pi_congr_left Equiv.piCongrLeft

end

section

variable {W : α → Sort w} {Z : β → Sort z} (h₁ : α ≃ β) (h₂ : ∀ a : α, W a ≃ Z (h₁ a))

/-- Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibers.
-/
def piCongr : (∀ a, W a) ≃ ∀ b, Z b :=
  (Equiv.piCongrRight h₂).trans (Equiv.piCongrLeft _ h₁)
#align equiv.Pi_congr Equiv.piCongr

@[simp]
theorem coe_piCongr_symm : ((h₁.piCongr h₂).symm :
    (∀ b, Z b) → ∀ a, W a) = fun f a => (h₂ a).symm (f (h₁ a)) :=
  rfl
#align equiv.coe_Pi_congr_symm Equiv.coe_piCongr_symm

theorem piCongr_symm_apply (f : ∀ b, Z b) :
    (h₁.piCongr h₂).symm f = fun a => (h₂ a).symm (f (h₁ a)) :=
  rfl
#align equiv.Pi_congr_symm_apply Equiv.piCongr_symm_apply

@[simp]
theorem piCongr_apply_apply (f : ∀ a, W a) (a : α) : h₁.piCongr h₂ f (h₁ a) = h₂ a (f a) := by
  change Eq.ndrec _ _ = _
  -- ⊢ (_ : ↑h₁.symm.symm (↑h₁.symm (↑h₁ a)) = ↑h₁ a) ▸ ↑(piCongrRight h₂) f (↑h₁.s …
  generalize_proofs hZa
  -- ⊢ hZa ▸ ↑(piCongrRight h₂) f (↑h₁.symm (↑h₁ a)) = ↑(h₂ a) (f a)
  revert hZa
  -- ⊢ ∀ (hZa : ↑h₁.symm.symm (↑h₁.symm (↑h₁ a)) = ↑h₁ a), hZa ▸ ↑(piCongrRight h₂) …
  rw [h₁.symm_apply_apply a]
  -- ⊢ ∀ (hZa : ↑h₁.symm.symm a = ↑h₁ a), hZa ▸ ↑(piCongrRight h₂) f a = ↑(h₂ a) (f …
  simp; rfl
  -- ⊢ ↑(piCongrRight h₂) f a = ↑(h₂ a) (f a)
        -- 🎉 no goals
#align equiv.Pi_congr_apply_apply Equiv.piCongr_apply_apply

end

section

variable {W : α → Sort w} {Z : β → Sort z} (h₁ : α ≃ β) (h₂ : ∀ b : β, W (h₁.symm b) ≃ Z b)

/-- Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibres.
-/
def piCongr' : (∀ a, W a) ≃ ∀ b, Z b :=
  (piCongr h₁.symm fun b => (h₂ b).symm).symm
#align equiv.Pi_congr' Equiv.piCongr'

@[simp]
theorem coe_piCongr' :
    (h₁.piCongr' h₂ : (∀ a, W a) → ∀ b, Z b) = fun f b => h₂ b <| f <| h₁.symm b :=
  rfl
#align equiv.coe_Pi_congr' Equiv.coe_piCongr'

theorem piCongr'_apply (f : ∀ a, W a) : h₁.piCongr' h₂ f = fun b => h₂ b <| f <| h₁.symm b :=
  rfl
#align equiv.Pi_congr'_apply Equiv.piCongr'_apply

@[simp]
theorem piCongr'_symm_apply_symm_apply (f : ∀ b, Z b) (b : β) :
    (h₁.piCongr' h₂).symm f (h₁.symm b) = (h₂ b).symm (f b) := by
  change Eq.ndrec _ _ = _
  -- ⊢ (_ : ↑h₁.symm.symm.symm (↑h₁.symm.symm (↑h₁.symm b)) = ↑h₁.symm b) ▸ ↑(piCon …
  generalize_proofs hWb
  -- ⊢ hWb ▸ ↑(piCongrRight fun b => (h₂ b).symm) f (↑h₁.symm.symm (↑h₁.symm b)) =  …
  revert hWb
  -- ⊢ ∀ (hWb : ↑h₁.symm.symm.symm (↑h₁.symm.symm (↑h₁.symm b)) = ↑h₁.symm b), hWb  …
  generalize hb : h₁ (h₁.symm b) = b'
  -- ⊢ ∀ (hWb : ↑h₁.symm.symm.symm b' = ↑h₁.symm b), hWb ▸ ↑(piCongrRight fun b =>  …
  rw [h₁.apply_symm_apply b] at hb
  -- ⊢ ∀ (hWb : ↑h₁.symm.symm.symm b' = ↑h₁.symm b), hWb ▸ ↑(piCongrRight fun b =>  …
  subst hb
  -- ⊢ ∀ (hWb : ↑h₁.symm.symm.symm b = ↑h₁.symm b), hWb ▸ ↑(piCongrRight fun b => ( …
  simp; rfl
  -- ⊢ ↑(piCongrRight fun b => (h₂ b).symm) f b = ↑(h₂ b).symm (f b)
        -- 🎉 no goals
#align equiv.Pi_congr'_symm_apply_symm_apply Equiv.piCongr'_symm_apply_symm_apply

end

section BinaryOp

variable (e : α₁ ≃ β₁) (f : α₁ → α₁ → α₁)

theorem semiconj_conj (f : α₁ → α₁) : Semiconj e f (e.conj f) := fun x => by simp
                                                                             -- 🎉 no goals
#align equiv.semiconj_conj Equiv.semiconj_conj

theorem semiconj₂_conj : Semiconj₂ e f (e.arrowCongr e.conj f) := fun x y => by simp [arrowCongr]
                                                                                -- 🎉 no goals
#align equiv.semiconj₂_conj Equiv.semiconj₂_conj

instance [IsAssociative α₁ f] : IsAssociative β₁ (e.arrowCongr (e.arrowCongr e) f) :=
  (e.semiconj₂_conj f).isAssociative_right e.surjective

instance [IsIdempotent α₁ f] : IsIdempotent β₁ (e.arrowCongr (e.arrowCongr e) f) :=
  (e.semiconj₂_conj f).isIdempotent_right e.surjective

instance [IsLeftCancel α₁ f] : IsLeftCancel β₁ (e.arrowCongr (e.arrowCongr e) f) :=
  ⟨e.surjective.forall₃.2 fun x y z => by simpa using @IsLeftCancel.left_cancel _ f _ x y z⟩
                                          -- 🎉 no goals

instance [IsRightCancel α₁ f] : IsRightCancel β₁ (e.arrowCongr (e.arrowCongr e) f) :=
  ⟨e.surjective.forall₃.2 fun x y z => by simpa using @IsRightCancel.right_cancel _ f _ x y z⟩
                                          -- 🎉 no goals

end BinaryOp

end Equiv

theorem Function.Injective.swap_apply
    [DecidableEq α] [DecidableEq β] {f : α → β} (hf : Function.Injective f) (x y z : α) :
    Equiv.swap (f x) (f y) (f z) = f (Equiv.swap x y z) := by
  by_cases hx:z = x
  -- ⊢ ↑(Equiv.swap (f x) (f y)) (f z) = f (↑(Equiv.swap x y) z)
  · simp [hx]
    -- 🎉 no goals

  by_cases hy:z = y
  -- ⊢ ↑(Equiv.swap (f x) (f y)) (f z) = f (↑(Equiv.swap x y) z)
  · simp [hy]
    -- 🎉 no goals

  rw [Equiv.swap_apply_of_ne_of_ne hx hy, Equiv.swap_apply_of_ne_of_ne (hf.ne hx) (hf.ne hy)]
  -- 🎉 no goals
#align function.injective.swap_apply Function.Injective.swap_apply

theorem Function.Injective.swap_comp
    [DecidableEq α] [DecidableEq β] {f : α → β} (hf : Function.Injective f) (x y : α) :
    Equiv.swap (f x) (f y) ∘ f = f ∘ Equiv.swap x y :=
  funext fun _ => hf.swap_apply _ _ _
#align function.injective.swap_comp Function.Injective.swap_comp

/-- If `α` is a subsingleton, then it is equivalent to `α × α`. -/
def subsingletonProdSelfEquiv [Subsingleton α] : α × α ≃ α where
  toFun p := p.1
  invFun a := (a, a)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align subsingleton_prod_self_equiv subsingletonProdSelfEquiv

/-- To give an equivalence between two subsingleton types, it is sufficient to give any two
    functions between them. -/
def equivOfSubsingletonOfSubsingleton [Subsingleton α] [Subsingleton β] (f : α → β) (g : β → α) :
    α ≃ β where
  toFun := f
  invFun := g
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align equiv_of_subsingleton_of_subsingleton equivOfSubsingletonOfSubsingleton

/-- A nonempty subsingleton type is (noncomputably) equivalent to `PUnit`. -/
noncomputable def Equiv.punitOfNonemptyOfSubsingleton [h : Nonempty α] [Subsingleton α] :
    α ≃ PUnit :=
  equivOfSubsingletonOfSubsingleton (fun _ => PUnit.unit) fun _ => h.some
#align equiv.punit_of_nonempty_of_subsingleton Equiv.punitOfNonemptyOfSubsingleton

/-- `Unique (Unique α)` is equivalent to `Unique α`. -/
def uniqueUniqueEquiv : Unique (Unique α) ≃ Unique α :=
  equivOfSubsingletonOfSubsingleton (fun h => h.default) fun h =>
    { default := h, uniq := fun _ => Subsingleton.elim _ _ }
#align unique_unique_equiv uniqueUniqueEquiv

/-- If `Unique β`, then `Unique α` is equivalent to `α ≃ β`. -/
def uniqueEquivEquivUnique (α : Sort u) (β : Sort v) [Unique β] : Unique α ≃ (α ≃ β) :=
  equivOfSubsingletonOfSubsingleton (fun _ => Equiv.equivOfUnique _ _) Equiv.unique

namespace Function

theorem update_comp_equiv [DecidableEq α'] [DecidableEq α] (f : α → β)
    (g : α' ≃ α) (a : α) (v : β) :
    update f a v ∘ g = update (f ∘ g) (g.symm a) v := by
  rw [← update_comp_eq_of_injective _ g.injective, g.apply_symm_apply]
  -- 🎉 no goals
#align function.update_comp_equiv Function.update_comp_equiv

theorem update_apply_equiv_apply [DecidableEq α'] [DecidableEq α] (f : α → β)
    (g : α' ≃ α) (a : α) (v : β) (a' : α') : update f a v (g a') = update (f ∘ g) (g.symm a) v a' :=
  congr_fun (update_comp_equiv f g a v) a'
#align function.update_apply_equiv_apply Function.update_apply_equiv_apply

-- porting note: EmbeddingLike.apply_eq_iff_eq broken here too
theorem piCongrLeft'_update [DecidableEq α] [DecidableEq β] (P : α → Sort*) (e : α ≃ β)
    (f : ∀ a, P a) (b : β) (x : P (e.symm b)) :
    e.piCongrLeft' P (update f (e.symm b) x) = update (e.piCongrLeft' P f) b x := by
  ext b'
  -- ⊢ ↑(Equiv.piCongrLeft' P e) (update f (↑e.symm b) x) b' = update (↑(Equiv.piCo …
  rcases eq_or_ne b' b with (rfl | h)
  -- ⊢ ↑(Equiv.piCongrLeft' P e) (update f (↑e.symm b') x) b' = update (↑(Equiv.piC …
  · simp
    -- 🎉 no goals
  · simp only [Equiv.piCongrLeft'_apply, ne_eq, h, not_false_iff, update_noteq]
    -- ⊢ update f (↑e.symm b) x (↑e.symm b') = f (↑e.symm b')
    rw [update_noteq _]
    -- ⊢ ↑e.symm b' ≠ ↑e.symm b
    rw [ne_eq]
    -- ⊢ ¬↑e.symm b' = ↑e.symm b
    intro h'
    -- ⊢ False
    /- an example of something that should work, or also putting `EmbeddingLike.apply_eq_iff_eq`
      in the `simp` should too:
    have := (EmbeddingLike.apply_eq_iff_eq e).mp h' -/
    cases e.symm.injective h' |> h
    -- 🎉 no goals
#align function.Pi_congr_left'_update Function.piCongrLeft'_update

theorem piCongrLeft'_symm_update [DecidableEq α] [DecidableEq β] (P : α → Sort*) (e : α ≃ β)
    (f : ∀ b, P (e.symm b)) (b : β) (x : P (e.symm b)) :
    (e.piCongrLeft' P).symm (update f b x) = update ((e.piCongrLeft' P).symm f) (e.symm b) x := by
  simp [(e.piCongrLeft' P).symm_apply_eq, piCongrLeft'_update]
  -- 🎉 no goals
#align function.Pi_congr_left'_symm_update Function.piCongrLeft'_symm_update

end Function
