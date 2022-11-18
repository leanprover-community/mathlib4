/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.Data.Subtype
import Mathlib.Data.Sum.Basic
import Mathlib.Logic.Function.Conjugate

-- **TODO** remove these later
set_option autoImplicit false

/-!
# Equivalence between types

In this file we continue the work on equivalences begun in `logic/equiv/defs.lean`, defining

* canonical isomorphisms between various types: e.g.,

  - `equiv.sum_equiv_sigma_bool` is the canonical equivalence between the sum of two types `α ⊕ β`
    and the sigma-type `Σ b : bool, cond b α β`;

  - `equiv.prod_sum_distrib : α × (β ⊕ γ) ≃ (α × β) ⊕ (α × γ)` shows that type product and type sum
    satisfy the distributive law up to a canonical equivalence;

* operations on equivalences: e.g.,

  - `equiv.prod_congr ea eb : α₁ × β₁ ≃ α₂ × β₂`: combine two equivalences `ea : α₁ ≃ α₂` and
    `eb : β₁ ≃ β₂` using `prod.map`.

  More definitions of this kind can be found in other files. E.g., `data/equiv/transfer_instance`
  does it for many algebraic type classes like `group`, `module`, etc.

## Tags

equivalence, congruence, bijective map
-/


open Function

universe u v w z

variable {α : Sort u} {β : Sort v} {γ : Sort w}

namespace Equiv

/-- `pprod α β` is equivalent to `α × β` -/
@[simps apply symmApply]
def pprodEquivProd {α β : Type _} : PProd α β ≃ α × β where
  toFun x := (x.1, x.2)
  invFun x := ⟨x.1, x.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
#align equiv.pprod_equiv_prod Equiv.pprodEquivProd

/-- Product of two equivalences, in terms of `pprod`. If `α ≃ β` and `γ ≃ δ`, then
`pprod α γ ≃ pprod β δ`. -/
-- porting note: in Lean 3 this had @[congr]`
@[simps apply]
def pprodCongr {δ : Sort z} (e₁ : α ≃ β) (e₂ : γ ≃ δ) : PProd α γ ≃ PProd β δ where
  toFun x := ⟨e₁ x.1, e₂ x.2⟩
  invFun x := ⟨e₁.symm x.1, e₂.symm x.2⟩
  left_inv := fun ⟨x, y⟩ => by simp
  right_inv := fun ⟨x, y⟩ => by simp
#align equiv.pprod_congr Equiv.pprodCongr

/-- Combine two equivalences using `pprod` in the domain and `prod` in the codomain. -/
@[simps apply symmApply]
def pprodProd {α₁ β₁ : Sort _} {α₂ β₂ : Type _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : PProd α₁ β₁ ≃ α₂ × β₂ :=
  (ea.pprodCongr eb).trans pprodEquivProd
#align equiv.pprod_prod Equiv.pprodProd

/-- Combine two equivalences using `pprod` in the codomain and `prod` in the domain. -/
@[simps apply symmApply]
def prodPProd {α₁ β₁ : Type _} {α₂ β₂ : Sort _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : α₁ × β₁ ≃ PProd α₂ β₂ :=
  (ea.symm.pprodProd eb.symm).symm
#align equiv.prod_pprod Equiv.prodPprod

/-- `pprod α β` is equivalent to `plift α × plift β` -/
@[simps apply symmApply]
def pprodEquivProdPlift {α β : Sort _} : PProd α β ≃ PLift α × PLift β :=
  Equiv.plift.symm.pprodProd Equiv.plift.symm
#align equiv.pprod_equiv_prod_plift Equiv.pprodEquivProdPlift

/-- Product of two equivalences. If `α₁ ≃ α₂` and `β₁ ≃ β₂`, then `α₁ × β₁ ≃ α₂ × β₂`. This is
`prod.map` as an equivalence. -/
-- porting note: in Lean 3 there was also a @[congr] tag
@[simps apply]
def prodCongr {α₁ β₁ α₂ β₂ : Type _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂ :=
  ⟨Prod.map e₁ e₂, Prod.map e₁.symm e₂.symm, fun ⟨a, b⟩ => by simp, fun ⟨a, b⟩ => by simp⟩
#align equiv.prod_congr Equiv.prodCongr

@[simp]
theorem prod_congr_symm {α₁ β₁ α₂ β₂ : Type _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (prodCongr e₁ e₂).symm = prodCongr e₁.symm e₂.symm :=
  rfl
#align equiv.prod_congr_symm Equiv.prod_congr_symm

/-- Type product is commutative up to an equivalence: `α × β ≃ β × α`. This is `prod.swap` as an
equivalence.-/
def prodComm (α β : Type _) : α × β ≃ β × α :=
  ⟨Prod.swap, Prod.swap, Prod.swap_swap, Prod.swap_swap⟩
#align equiv.prod_comm Equiv.prodComm

@[simp]
theorem coe_prod_comm (α β : Type _) : (⇑(prodComm α β) : α × β → β × α) = Prod.swap :=
  rfl
#align equiv.coe_prod_comm Equiv.coe_prod_comm

@[simp]
theorem prod_comm_apply {α β : Type _} (x : α × β) : prodComm α β x = x.swap :=
  rfl
#align equiv.prod_comm_apply Equiv.prod_comm_apply

@[simp]
theorem prod_comm_symm (α β) : (prodComm α β).symm = prodComm β α :=
  rfl
#align equiv.prod_comm_symm Equiv.prod_comm_symm

/-- Type product is associative up to an equivalence. -/
@[simps]
def prodAssoc (α β γ : Sort _) : (α × β) × γ ≃ α × β × γ :=
  ⟨fun p => (p.1.1, p.1.2, p.2), fun p => ((p.1, p.2.1), p.2.2), fun ⟨⟨_, _⟩, _⟩ => rfl,
    fun ⟨_, ⟨_, _⟩⟩ => rfl⟩
#align equiv.prod_assoc Equiv.prodAssoc

/-- Functions on `α × β` are equivalent to functions `α → β → γ`. -/
@[simps (config := { fullyApplied := false })]
def curry (α β γ : Type _) : (α × β → γ) ≃ (α → β → γ) where
  toFun := Function.curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry
#align equiv.curry Equiv.curry

section

/-- `punit` is a right identity for type product up to an equivalence. -/
@[simps]
def prodPUnit (α : Type _) : α × PUnit.{u + 1} ≃ α :=
  ⟨fun p => p.1, fun a => (a, PUnit.unit), fun ⟨_, PUnit.unit⟩ => rfl, fun _ => rfl⟩
#align equiv.prod_punit Equiv.prodPunit

/-- `punit` is a left identity for type product up to an equivalence. -/
@[simps]
def pUnitProd (α : Type _) : PUnit.{u + 1} × α ≃ α :=
  calc
    PUnit × α ≃ α × PUnit := prodComm _ _
    _ ≃ α := prodPUnit _

#align equiv.punit_prod Equiv.punitProd

/-- Any `unique` type is a right identity for type product up to equivalence. -/
def prodUnique (α : Type u) (β : Type v) [Unique β] : α × β ≃ α :=
  ((Equiv.refl α).prodCongr <| equivPUnit.{v+1,v+1} β).trans <| prodPUnit α
#align equiv.prod_unique Equiv.prodUnique

@[simp]
theorem coe_prod_unique {α β : Type _} [Unique β] : (⇑(prodUnique α β) : α × β → α)  = Prod.fst :=
  rfl
#align equiv.coe_prod_unique Equiv.coe_prod_unique

theorem prod_unique_apply {α β : Type _} [Unique β] (x : α × β) : prodUnique α β x = x.1 :=
  rfl
#align equiv.prod_unique_apply Equiv.prod_unique_apply

@[simp]
theorem prod_unique_symm_apply {α β : Type _} [Unique β] (x : α) : (prodUnique α β).symm x = (x, default) :=
  rfl
#align equiv.prod_unique_symm_apply Equiv.prod_unique_symm_apply

/-- Any `unique` type is a left identity for type product up to equivalence. -/
def uniqueProd (α β : Type _) [Unique β] : β × α ≃ α :=
  ((equivPUnit.{v+1,v+1} β).prodCongr <| Equiv.refl α).trans <| pUnitProd α
#align equiv.unique_prod Equiv.uniqueProd

@[simp]
theorem coe_unique_prod {α β : Type _} [Unique β] : (⇑(uniqueProd α β) : β × α → α) = Prod.snd :=
  rfl
#align equiv.coe_unique_prod Equiv.coe_unique_prod

theorem unique_prod_apply {α β : Type _} [Unique β] (x : β × α) : uniqueProd α β x = x.2 :=
  rfl
#align equiv.unique_prod_apply Equiv.unique_prod_apply

@[simp]
theorem unique_prod_symm_apply {α β : Type _} [Unique β] (x : α) :
    (uniqueProd α β).symm x = (default, x) :=
  rfl
#align equiv.unique_prod_symm_apply Equiv.unique_prod_symm_apply

/-- `empty` type is a right absorbing element for type product up to an equivalence. -/
def prodEmpty (α : Type _) : α × Empty ≃ Empty :=
  equivEmpty _
#align equiv.prod_empty Equiv.prodEmpty

/-- `empty` type is a left absorbing element for type product up to an equivalence. -/
def emptyProd (α : Type _) : Empty × α ≃ Empty :=
  equivEmpty _
#align equiv.empty_prod Equiv.emptyProd

/-- `pempty` type is a right absorbing element for type product up to an equivalence. -/
def prodPempty (α : Type _) : α × PEmpty ≃ PEmpty :=
  equivPEmpty _
#align equiv.prod_pempty Equiv.prodPempty

/-- `pempty` type is a left absorbing element for type product up to an equivalence. -/
def pemptyProd (α : Type _) : PEmpty × α ≃ PEmpty :=
  equivPEmpty _
#align equiv.pempty_prod Equiv.pemptyProd

end

section

open Sum

/-- `psum` is equivalent to `sum`. -/
def psumEquivSum (α β : Type _) : PSum α β ≃ Sum α β where
  toFun s := PSum.casesOn s inl inr
  invFun := Sum.elim PSum.inl PSum.inr
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl
#align equiv.psum_equiv_sum Equiv.psumEquivSum

/-- If `α ≃ α'` and `β ≃ β'`, then `α ⊕ β ≃ α' ⊕ β'`. This is `sum.map` as an equivalence. -/
@[simps apply]
def sumCongr {α₁ β₁ α₂ β₂ : Type _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : Sum α₁ β₁ ≃ Sum α₂ β₂ :=
  ⟨Sum.map ea eb, Sum.map ea.symm eb.symm, fun x => by simp, fun x => by simp⟩
#align equiv.sum_congr Equiv.sumCongr

/-- If `α ≃ α'` and `β ≃ β'`, then `psum α β ≃ psum α' β'`. -/
def psumCongr {δ : Sort z} (e₁ : α ≃ β) (e₂ : γ ≃ δ) : PSum α γ ≃ PSum β δ where
  toFun x := PSum.casesOn x (PSum.inl ∘ e₁) (PSum.inr ∘ e₂)
  invFun x := PSum.casesOn x (PSum.inl ∘ e₁.symm) (PSum.inr ∘ e₂.symm)
  left_inv := by rintro (x | x) <;> simp
  right_inv := by rintro (x | x) <;> simp
#align equiv.psum_congr Equiv.psumCongr

/-- Combine two `equiv`s using `psum` in the domain and `sum` in the codomain. -/
def psumSum {α₁ β₁ : Sort _} {α₂ β₂ : Type _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : PSum α₁ β₁ ≃ Sum α₂ β₂ :=
  (ea.psumCongr eb).trans (psumEquivSum _ _)
#align equiv.psum_sum Equiv.psumSum

/-- Combine two `equiv`s using `sum` in the domain and `psum` in the codomain. -/
def sumPsum {α₁ β₁ : Type _} {α₂ β₂ : Sort _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : Sum α₁ β₁ ≃ PSum α₂ β₂ :=
  (ea.symm.psumSum eb.symm).symm
#align equiv.sum_psum Equiv.sumPsum

@[simp]
theorem sum_congr_trans {α₁ α₂ β₁ β₂ γ₁ γ₂ : Sort _} (e : α₁ ≃ β₁) (f : α₂ ≃ β₂) (g : β₁ ≃ γ₁) (h : β₂ ≃ γ₂) :
    (Equiv.sumCongr e f).trans (Equiv.sumCongr g h) = Equiv.sumCongr (e.trans g) (f.trans h) := by
  ext i
  cases i <;> rfl
#align equiv.sum_congr_trans Equiv.sum_congr_trans

@[simp]
theorem sum_congr_symm {α β γ δ : Sort _} (e : α ≃ β) (f : γ ≃ δ) :
    (Equiv.sumCongr e f).symm = Equiv.sumCongr e.symm f.symm :=
  rfl
#align equiv.sum_congr_symm Equiv.sum_congr_symm

@[simp]
theorem sum_congr_refl {α β : Sort _} : Equiv.sumCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (Sum α β) := by
  ext i
  cases i <;> rfl
#align equiv.sum_congr_refl Equiv.sum_congr_refl

namespace Perm

/-- Combine a permutation of `α` and of `β` into a permutation of `α ⊕ β`. -/
@[reducible]
def sumCongr {α β : Type _} (ea : Equiv.Perm α) (eb : Equiv.Perm β) : Equiv.Perm (Sum α β) :=
  Equiv.sumCongr ea eb
#align equiv.perm.sum_congr Equiv.Perm.sumCongr

@[simp]
theorem sum_congr_apply {α β : Type _} (ea : Equiv.Perm α) (eb : Equiv.Perm β) (x : Sum α β) :
    sumCongr ea eb x = Sum.map (⇑ea) (⇑eb) x :=
  Equiv.sumCongr_apply ea eb x
#align equiv.perm.sum_congr_apply Equiv.Perm.sum_congr_apply

@[simp]
theorem sum_congr_trans {α β : Sort _} (e : Equiv.Perm α) (f : Equiv.Perm β) (g : Equiv.Perm α) (h : Equiv.Perm β) :
    (sumCongr e f).trans (sumCongr g h) = sumCongr (e.trans g) (f.trans h) :=
  Equiv.sum_congr_trans e f g h
#align equiv.perm.sum_congr_trans Equiv.Perm.sum_congr_trans

@[simp]
theorem sum_congr_symm {α β : Sort _} (e : Equiv.Perm α) (f : Equiv.Perm β) :
    (sumCongr e f).symm = sumCongr e.symm f.symm :=
  Equiv.sum_congr_symm e f
#align equiv.perm.sum_congr_symm Equiv.Perm.sum_congr_symm

@[simp]
theorem sum_congr_refl {α β : Sort _} : sumCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (Sum α β) :=
  Equiv.sum_congr_refl
#align equiv.perm.sum_congr_refl Equiv.Perm.sum_congr_refl

end Perm

/-- `bool` is equivalent the sum of two `punit`s. -/
def boolEquivPunitSumPunit : Bool ≃ Sum PUnit.{u + 1} PUnit.{v + 1} :=
  ⟨fun b => cond b (inr PUnit.unit) (inl PUnit.unit), Sum.elim (fun _ => false) fun _ => true, fun b => by
    cases b <;> rfl, fun s => by rcases s with (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> rfl⟩
#align equiv.bool_equiv_punit_sum_punit Equiv.boolEquivPunitSumPunit

/-- Sum of types is commutative up to an equivalence. This is `sum.swap` as an equivalence. -/
@[simps (config := { fullyApplied := false }) apply]
def sumComm (α β : Type _) : Sum α β ≃ Sum β α :=
  ⟨Sum.swap, Sum.swap, Sum.swap_swap, Sum.swap_swap⟩
#align equiv.sum_comm Equiv.sumComm

@[simp]
theorem sum_comm_symm (α β) : (sumComm α β).symm = sumComm β α :=
  rfl
#align equiv.sum_comm_symm Equiv.sum_comm_symm

/-- Sum of types is associative up to an equivalence. -/
def sumAssoc (α β γ : Type _) : Sum (Sum α β) γ ≃ Sum α (Sum β γ) :=
  ⟨Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr),
    Sum.elim (Sum.inl ∘ Sum.inl) <| Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr, by rintro (⟨_ | _⟩ | _) <;> rfl, by
    rintro (_ | ⟨_ | _⟩) <;> rfl⟩
#align equiv.sum_assoc Equiv.sumAssoc

@[simp]
theorem sum_assoc_apply_inl_inl {α β γ} (a) : sumAssoc α β γ (inl (inl a)) = inl a :=
  rfl
#align equiv.sum_assoc_apply_inl_inl Equiv.sum_assoc_apply_inl_inl

@[simp]
theorem sum_assoc_apply_inl_inr {α β γ} (b) : sumAssoc α β γ (inl (inr b)) = inr (inl b) :=
  rfl
#align equiv.sum_assoc_apply_inl_inr Equiv.sum_assoc_apply_inl_inr

@[simp]
theorem sum_assoc_apply_inr {α β γ} (c) : sumAssoc α β γ (inr c) = inr (inr c) :=
  rfl
#align equiv.sum_assoc_apply_inr Equiv.sum_assoc_apply_inr

@[simp]
theorem sum_assoc_symm_apply_inl {α β γ} (a) : (sumAssoc α β γ).symm (inl a) = inl (inl a) :=
  rfl
#align equiv.sum_assoc_symm_apply_inl Equiv.sum_assoc_symm_apply_inl

@[simp]
theorem sum_assoc_symm_apply_inr_inl {α β γ} (b) : (sumAssoc α β γ).symm (inr (inl b)) = inl (inr b) :=
  rfl
#align equiv.sum_assoc_symm_apply_inr_inl Equiv.sum_assoc_symm_apply_inr_inl

@[simp]
theorem sum_assoc_symm_apply_inr_inr {α β γ} (c) : (sumAssoc α β γ).symm (inr (inr c)) = inr c :=
  rfl
#align equiv.sum_assoc_symm_apply_inr_inr Equiv.sum_assoc_symm_apply_inr_inr

/-- Sum with `empty` is equivalent to the original type. -/
@[simps symmApply]
def sumEmpty (α β : Type _) [IsEmpty β] : Sum α β ≃ α :=
  ⟨Sum.elim id isEmptyElim, inl, fun s => by
    rcases s with (_ | x)
    rfl
    exact isEmptyElim x, fun a => rfl⟩
#align equiv.sum_empty Equiv.sumEmpty

@[simp]
theorem sum_empty_apply_inl {α β : Type _} [IsEmpty β] (a : α) : sumEmpty α β (Sum.inl a) = a :=
  rfl
#align equiv.sum_empty_apply_inl Equiv.sum_empty_apply_inl

/-- The sum of `empty` with any `Sort*` is equivalent to the right summand. -/
@[simps symmApply]
def emptySum (α β : Type _) [IsEmpty α] : Sum α β ≃ β :=
  (sumComm _ _).trans <| sumEmpty _ _
#align equiv.empty_sum Equiv.emptySum

@[simp]
theorem empty_sum_apply_inr {α β : Type _} [IsEmpty α] (b : β) : emptySum α β (Sum.inr b) = b :=
  rfl
#align equiv.empty_sum_apply_inr Equiv.empty_sum_apply_inr

/-- `option α` is equivalent to `α ⊕ punit` -/
def optionEquivSumPunit (α : Type _) : Option α ≃ Sum α PUnit.{u + 1} :=
  ⟨fun o => o.elim (inr PUnit.unit) inl, fun s => s.elim some fun _ => none, fun o => by cases o <;> rfl, fun s => by
    rcases s with (_ | ⟨⟨⟩⟩) <;> rfl⟩
#align equiv.option_equiv_sum_punit Equiv.optionEquivSumPunit

@[simp]
theorem option_equiv_sum_punit_none {α} : optionEquivSumPunit α none = Sum.inr PUnit.unit :=
  rfl
#align equiv.option_equiv_sum_punit_none Equiv.option_equiv_sum_punit_none
#exit

@[simp]
theorem option_equiv_sum_punit_some {α} (a) : optionEquivSumPunit α (some a) = Sum.inl a :=
  rfl
#align equiv.option_equiv_sum_punit_some Equiv.option_equiv_sum_punit_some

@[simp]
theorem option_equiv_sum_punit_coe {α} (a : α) : optionEquivSumPunit α a = Sum.inl a :=
  rfl
#align equiv.option_equiv_sum_punit_coe Equiv.option_equiv_sum_punit_coe

@[simp]
theorem option_equiv_sum_punit_symm_inl {α} (a) : (optionEquivSumPunit α).symm (Sum.inl a) = a :=
  rfl
#align equiv.option_equiv_sum_punit_symm_inl Equiv.option_equiv_sum_punit_symm_inl

@[simp]
theorem option_equiv_sum_punit_symm_inr {α} (a) : (optionEquivSumPunit α).symm (Sum.inr a) = none :=
  rfl
#align equiv.option_equiv_sum_punit_symm_inr Equiv.option_equiv_sum_punit_symm_inr

/-- The set of `x : option α` such that `is_some x` is equivalent to `α`. -/
@[simps]
def optionIsSomeEquiv (α : Type _) : { x : Option α // x.isSome } ≃ α where
  toFun o := Option.get o.2
  invFun x := ⟨some x, by decide⟩
  left_inv o := Subtype.eq <| Option.some_get _
  right_inv x := Option.get_some _ _
#align equiv.option_is_some_equiv Equiv.optionIsSomeEquiv

/-- The product over `option α` of `β a` is the binary product of the
product over `α` of `β (some α)` and `β none` -/
@[simps]
def piOptionEquivProd {α : Type _} {β : Option α → Type _} : (∀ a : Option α, β a) ≃ β none × ∀ a : α, β (some a) where
  toFun f := (f none, fun a => f (some a))
  invFun x a := Option.casesOn a x.fst x.snd
  left_inv f := funext fun a => by cases a <;> rfl
  right_inv x := by simp
#align equiv.pi_option_equiv_prod Equiv.piOptionEquivProd

/-- `α ⊕ β` is equivalent to a `sigma`-type over `bool`. Note that this definition assumes `α` and
`β` to be types from the same universe, so it cannot by used directly to transfer theorems about
sigma types to theorems about sum types. In many cases one can use `ulift` to work around this
difficulty. -/
def sumEquivSigmaBool (α β : Type u) : Sum α β ≃ Σb : Bool, cond b α β :=
  ⟨fun s => s.elim (fun x => ⟨true, x⟩) fun x => ⟨false, x⟩, fun s =>
    match s with
    | ⟨tt, a⟩ => inl a
    | ⟨ff, b⟩ => inr b,
    fun s => by cases s <;> rfl, fun s => by rcases s with ⟨_ | _, _⟩ <;> rfl⟩
#align equiv.sum_equiv_sigma_bool Equiv.sumEquivSigmaBool

-- See also `equiv.sigma_preimage_equiv`.
/-- `sigma_fiber_equiv f` for `f : α → β` is the natural equivalence between
the type of all fibres of `f` and the total space `α`. -/
@[simps]
def sigmaFiberEquiv {α β : Type _} (f : α → β) : (Σy : β, { x // f x = y }) ≃ α :=
  ⟨fun x => ↑x.2, fun x => ⟨f x, x, rfl⟩, fun ⟨y, x, rfl⟩ => rfl, fun x => rfl⟩
#align equiv.sigma_fiber_equiv Equiv.sigmaFiberEquiv

end

section SumCompl

/-- For any predicate `p` on `α`,
the sum of the two subtypes `{a // p a}` and its complement `{a // ¬ p a}`
is naturally equivalent to `α`.

See `subtype_or_equiv` for sum types over subtypes `{x // p x}` and `{x // q x}`
that are not necessarily `is_compl p q`.  -/
def sumCompl {α : Type _} (p : α → Prop) [DecidablePred p] : Sum { a // p a } { a // ¬p a } ≃ α where
  toFun := Sum.elim coe coe
  invFun a := if h : p a then Sum.inl ⟨a, h⟩ else Sum.inr ⟨a, h⟩
  left_inv := by rintro (⟨x, hx⟩ | ⟨x, hx⟩) <;> dsimp <;> [rw [dif_pos], rw [dif_neg]]
  right_inv a := by
    dsimp
    split_ifs <;> rfl
#align equiv.sum_compl Equiv.sumCompl

@[simp]
theorem sum_compl_apply_inl {α : Type _} (p : α → Prop) [DecidablePred p] (x : { a // p a }) :
    sumCompl p (Sum.inl x) = x :=
  rfl
#align equiv.sum_compl_apply_inl Equiv.sum_compl_apply_inl

@[simp]
theorem sum_compl_apply_inr {α : Type _} (p : α → Prop) [DecidablePred p] (x : { a // ¬p a }) :
    sumCompl p (Sum.inr x) = x :=
  rfl
#align equiv.sum_compl_apply_inr Equiv.sum_compl_apply_inr

@[simp]
theorem sum_compl_apply_symm_of_pos {α : Type _} (p : α → Prop) [DecidablePred p] (a : α) (h : p a) :
    (sumCompl p).symm a = Sum.inl ⟨a, h⟩ :=
  dif_pos h
#align equiv.sum_compl_apply_symm_of_pos Equiv.sum_compl_apply_symm_of_pos

@[simp]
theorem sum_compl_apply_symm_of_neg {α : Type _} (p : α → Prop) [DecidablePred p] (a : α) (h : ¬p a) :
    (sumCompl p).symm a = Sum.inr ⟨a, h⟩ :=
  dif_neg h
#align equiv.sum_compl_apply_symm_of_neg Equiv.sum_compl_apply_symm_of_neg

/-- Combines an `equiv` between two subtypes with an `equiv` between their complements to form a
  permutation. -/
def subtypeCongr {α : Type _} {p q : α → Prop} [DecidablePred p] [DecidablePred q] (e : { x // p x } ≃ { x // q x })
    (f : { x // ¬p x } ≃ { x // ¬q x }) : Perm α :=
  (sumCompl p).symm.trans ((sumCongr e f).trans (sumCompl q))
#align equiv.subtype_congr Equiv.subtypeCongr

open Equiv

variable {ε : Type _} {p : ε → Prop} [DecidablePred p]

variable (ep ep' : Perm { a // p a }) (en en' : Perm { a // ¬p a })

/-- Combining permutations on `ε` that permute only inside or outside the subtype
split induced by `p : ε → Prop` constructs a permutation on `ε`. -/
def Perm.subtypeCongr : Equiv.Perm ε :=
  permCongr (sumCompl p) (sumCongr ep en)
#align equiv.perm.subtype_congr Equiv.Perm.subtypeCongr

theorem Perm.subtypeCongr.apply (a : ε) : ep.subtypeCongr en a = if h : p a then ep ⟨a, h⟩ else en ⟨a, h⟩ := by
  by_cases h:p a <;> simp [perm.subtype_congr, h]
#align equiv.perm.subtype_congr.apply Equiv.Perm.subtypeCongr.apply

@[simp]
theorem Perm.subtypeCongr.left_apply {a : ε} (h : p a) : ep.subtypeCongr en a = ep ⟨a, h⟩ := by
  simp [perm.subtype_congr.apply, h]
#align equiv.perm.subtype_congr.left_apply Equiv.Perm.subtypeCongr.left_apply

@[simp]
theorem Perm.subtypeCongr.left_apply_subtype (a : { a // p a }) : ep.subtypeCongr en a = ep a := by
  convert perm.subtype_congr.left_apply _ _ a.property
  simp
#align equiv.perm.subtype_congr.left_apply_subtype Equiv.Perm.subtypeCongr.left_apply_subtype

@[simp]
theorem Perm.subtypeCongr.right_apply {a : ε} (h : ¬p a) : ep.subtypeCongr en a = en ⟨a, h⟩ := by
  simp [perm.subtype_congr.apply, h]
#align equiv.perm.subtype_congr.right_apply Equiv.Perm.subtypeCongr.right_apply

@[simp]
theorem Perm.subtypeCongr.right_apply_subtype (a : { a // ¬p a }) : ep.subtypeCongr en a = en a := by
  convert perm.subtype_congr.right_apply _ _ a.property
  simp
#align equiv.perm.subtype_congr.right_apply_subtype Equiv.Perm.subtypeCongr.right_apply_subtype

@[simp]
theorem Perm.subtypeCongr.refl :
    Perm.subtypeCongr (Equiv.refl { a // p a }) (Equiv.refl { a // ¬p a }) = Equiv.refl ε := by
  ext x
  by_cases h:p x <;> simp [h]
#align equiv.perm.subtype_congr.refl Equiv.Perm.subtypeCongr.refl

@[simp]
theorem Perm.subtypeCongr.symm : (ep.subtypeCongr en).symm = Perm.subtypeCongr ep.symm en.symm := by
  ext x
  by_cases h:p x
  · have : p (ep.symm ⟨x, h⟩) := Subtype.property _
    simp [perm.subtype_congr.apply, h, symm_apply_eq, this]

  · have : ¬p (en.symm ⟨x, h⟩) := Subtype.property (en.symm _)
    simp [perm.subtype_congr.apply, h, symm_apply_eq, this]

#align equiv.perm.subtype_congr.symm Equiv.Perm.subtypeCongr.symm

@[simp]
theorem Perm.subtypeCongr.trans :
    (ep.subtypeCongr en).trans (ep'.subtypeCongr en') = Perm.subtypeCongr (ep.trans ep') (en.trans en') := by
  ext x
  by_cases h:p x
  · have : p (ep ⟨x, h⟩) := Subtype.property _
    simp [perm.subtype_congr.apply, h, this]

  · have : ¬p (en ⟨x, h⟩) := Subtype.property (en _)
    simp [perm.subtype_congr.apply, h, symm_apply_eq, this]

#align equiv.perm.subtype_congr.trans Equiv.Perm.subtypeCongr.trans

end SumCompl

section SubtypePreimage

variable (p : α → Prop) [DecidablePred p] (x₀ : { a // p a } → β)

/-- For a fixed function `x₀ : {a // p a} → β` defined on a subtype of `α`,
the subtype of functions `x : α → β` that agree with `x₀` on the subtype `{a // p a}`
is naturally equivalent to the type of functions `{a // ¬ p a} → β`. -/
@[simps]
def subtypePreimage : { x : α → β // x ∘ coe = x₀ } ≃ ({ a // ¬p a } → β) where
  toFun (x : { x : α → β // x ∘ coe = x₀ }) a := (x : α → β) a
  invFun x := ⟨fun a => if h : p a then x₀ ⟨a, h⟩ else x ⟨a, h⟩, funext fun ⟨a, h⟩ => dif_pos h⟩
  left_inv := fun ⟨x, hx⟩ =>
    Subtype.val_injective <|
      funext fun a => by
        dsimp
        split_ifs <;> [rw [← hx], skip] <;> rfl
  right_inv x :=
    funext fun ⟨a, h⟩ =>
      show dite (p a) _ _ = _ by
        dsimp
        rw [dif_neg h]
#align equiv.subtype_preimage Equiv.subtypePreimage

theorem subtype_preimage_symm_apply_coe_pos (x : { a // ¬p a } → β) (a : α) (h : p a) :
    ((subtypePreimage p x₀).symm x : α → β) a = x₀ ⟨a, h⟩ :=
  dif_pos h
#align equiv.subtype_preimage_symm_apply_coe_pos Equiv.subtype_preimage_symm_apply_coe_pos

theorem subtype_preimage_symm_apply_coe_neg (x : { a // ¬p a } → β) (a : α) (h : ¬p a) :
    ((subtypePreimage p x₀).symm x : α → β) a = x ⟨a, h⟩ :=
  dif_neg h
#align equiv.subtype_preimage_symm_apply_coe_neg Equiv.subtype_preimage_symm_apply_coe_neg

end SubtypePreimage

section

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Π a, β₁ a` and
`Π a, β₂ a`. -/
def piCongrRight {α} {β₁ β₂ : α → Sort _} (F : ∀ a, β₁ a ≃ β₂ a) : (∀ a, β₁ a) ≃ ∀ a, β₂ a :=
  ⟨fun H a => F a (H a), fun H a => (F a).symm (H a), fun H => funext <| by simp, fun H => funext <| by simp⟩
#align equiv.Pi_congr_right Equiv.piCongrRight

/-- Given `φ : α → β → Sort*`, we have an equivalence between `Π a b, φ a b` and `Π b a, φ a b`.
This is `function.swap` as an `equiv`. -/
@[simps apply]
def piComm {α β} (φ : α → β → Sort _) : (∀ a b, φ a b) ≃ ∀ b a, φ a b :=
  ⟨swap, swap, fun x => rfl, fun y => rfl⟩
#align equiv.Pi_comm Equiv.piComm

@[simp]
theorem Pi_comm_symm {α β} {φ : α → β → Sort _} : (piComm φ).symm = (Pi_comm <| swap φ) :=
  rfl
#align equiv.Pi_comm_symm Equiv.Pi_comm_symm

/-- Dependent `curry` equivalence: the type of dependent functions on `Σ i, β i` is equivalent
to the type of dependent functions of two arguments (i.e., functions to the space of functions).

This is `sigma.curry` and `sigma.uncurry` together as an equiv. -/
def piCurry {α} {β : α → Sort _} (γ : ∀ a, β a → Sort _) : (∀ x : Σi, β i, γ x.1 x.2) ≃ ∀ a b, γ a b where
  toFun := Sigma.curry
  invFun := Sigma.uncurry
  left_inv := Sigma.uncurry_curry
  right_inv := Sigma.curry_uncurry
#align equiv.Pi_curry Equiv.piCurry

end

section ProdCongr

variable {α₁ β₁ β₂ : Type _} (e : α₁ → β₁ ≃ β₂)

/-- A family of equivalences `Π (a : α₁), β₁ ≃ β₂` generates an equivalence
between `β₁ × α₁` and `β₂ × α₁`. -/
def prodCongrLeft : β₁ × α₁ ≃ β₂ × α₁ where
  toFun ab := ⟨e ab.2 ab.1, ab.2⟩
  invFun ab := ⟨(e ab.2).symm ab.1, ab.2⟩
  left_inv := by
    rintro ⟨a, b⟩
    simp
  right_inv := by
    rintro ⟨a, b⟩
    simp
#align equiv.prod_congr_left Equiv.prodCongrLeft

@[simp]
theorem prod_congr_left_apply (b : β₁) (a : α₁) : prodCongrLeft e (b, a) = (e a b, a) :=
  rfl
#align equiv.prod_congr_left_apply Equiv.prod_congr_left_apply

theorem prod_congr_refl_right (e : β₁ ≃ β₂) : prodCongr e (Equiv.refl α₁) = prodCongrLeft fun _ => e := by
  ext ⟨a, b⟩ : 1
  simp
#align equiv.prod_congr_refl_right Equiv.prod_congr_refl_right

/-- A family of equivalences `Π (a : α₁), β₁ ≃ β₂` generates an equivalence
between `α₁ × β₁` and `α₁ × β₂`. -/
def prodCongrRight : α₁ × β₁ ≃ α₁ × β₂ where
  toFun ab := ⟨ab.1, e ab.1 ab.2⟩
  invFun ab := ⟨ab.1, (e ab.1).symm ab.2⟩
  left_inv := by
    rintro ⟨a, b⟩
    simp
  right_inv := by
    rintro ⟨a, b⟩
    simp
#align equiv.prod_congr_right Equiv.prodCongrRight

@[simp]
theorem prod_congr_right_apply (a : α₁) (b : β₁) : prodCongrRight e (a, b) = (a, e a b) :=
  rfl
#align equiv.prod_congr_right_apply Equiv.prod_congr_right_apply

theorem prod_congr_refl_left (e : β₁ ≃ β₂) : prodCongr (Equiv.refl α₁) e = prodCongrRight fun _ => e := by
  ext ⟨a, b⟩ : 1
  simp
#align equiv.prod_congr_refl_left Equiv.prod_congr_refl_left

@[simp]
theorem prod_congr_left_trans_prod_comm :
    (prodCongrLeft e).trans (prodComm _ _) = (prodComm _ _).trans (prodCongrRight e) := by
  ext ⟨a, b⟩ : 1
  simp
#align equiv.prod_congr_left_trans_prod_comm Equiv.prod_congr_left_trans_prod_comm

@[simp]
theorem prod_congr_right_trans_prod_comm :
    (prodCongrRight e).trans (prodComm _ _) = (prodComm _ _).trans (prodCongrLeft e) := by
  ext ⟨a, b⟩ : 1
  simp
#align equiv.prod_congr_right_trans_prod_comm Equiv.prod_congr_right_trans_prod_comm

theorem sigma_congr_right_sigma_equiv_prod :
    (sigmaCongrRight e).trans (sigmaEquivProd α₁ β₂) = (sigmaEquivProd α₁ β₁).trans (prodCongrRight e) := by
  ext ⟨a, b⟩ : 1
  simp
#align equiv.sigma_congr_right_sigma_equiv_prod Equiv.sigma_congr_right_sigma_equiv_prod

theorem sigma_equiv_prod_sigma_congr_right :
    (sigmaEquivProd α₁ β₁).symm.trans (sigmaCongrRight e) = (prodCongrRight e).trans (sigmaEquivProd α₁ β₂).symm := by
  ext ⟨a, b⟩ : 1
  simp
#align equiv.sigma_equiv_prod_sigma_congr_right Equiv.sigma_equiv_prod_sigma_congr_right

-- See also `equiv.of_preimage_equiv`.
/-- A family of equivalences between fibers gives an equivalence between domains. -/
@[simps]
def ofFiberEquiv {α β γ : Type _} {f : α → γ} {g : β → γ} (e : ∀ c, { a // f a = c } ≃ { b // g b = c }) : α ≃ β :=
  (sigmaFiberEquiv f).symm.trans <| (Equiv.sigmaCongrRight e).trans (sigmaFiberEquiv g)
#align equiv.of_fiber_equiv Equiv.ofFiberEquiv

theorem of_fiber_equiv_map {α β γ} {f : α → γ} {g : β → γ} (e : ∀ c, { a // f a = c } ≃ { b // g b = c }) (a : α) :
    g (ofFiberEquiv e a) = f a :=
  (_ : { b // g b = _ }).Prop
#align equiv.of_fiber_equiv_map Equiv.of_fiber_equiv_map

/-- A variation on `equiv.prod_congr` where the equivalence in the second component can depend
  on the first component. A typical example is a shear mapping, explaining the name of this
  declaration. -/
@[simps (config := { fullyApplied := false })]
def prodShear {α₁ β₁ α₂ β₂ : Type _} (e₁ : α₁ ≃ α₂) (e₂ : α₁ → β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂ where
  toFun := fun x : α₁ × β₁ => (e₁ x.1, e₂ x.1 x.2)
  invFun := fun y : α₂ × β₂ => (e₁.symm y.1, (e₂ <| e₁.symm y.1).symm y.2)
  left_inv := by
    rintro ⟨x₁, y₁⟩
    simp only [symm_apply_apply]
  right_inv := by
    rintro ⟨x₁, y₁⟩
    simp only [apply_symm_apply]
#align equiv.prod_shear Equiv.prodShear

end ProdCongr

namespace Perm

variable {α₁ β₁ β₂ : Type _} [DecidableEq α₁] (a : α₁) (e : Perm β₁)

/-- `prod_extend_right a e` extends `e : perm β` to `perm (α × β)` by sending `(a, b)` to
`(a, e b)` and keeping the other `(a', b)` fixed. -/
def prodExtendRight : Perm (α₁ × β₁) where
  toFun ab := if ab.fst = a then (a, e ab.snd) else ab
  invFun ab := if ab.fst = a then (a, e.symm ab.snd) else ab
  left_inv := by
    rintro ⟨k', x⟩
    dsimp only
    split_ifs with h <;> simp [h]
  right_inv := by
    rintro ⟨k', x⟩
    dsimp only
    split_ifs with h <;> simp [h]
#align equiv.perm.prod_extend_right Equiv.Perm.prodExtendRight

@[simp]
theorem prod_extend_right_apply_eq (b : β₁) : prodExtendRight a e (a, b) = (a, e b) :=
  if_pos rfl
#align equiv.perm.prod_extend_right_apply_eq Equiv.Perm.prod_extend_right_apply_eq

theorem prod_extend_right_apply_ne {a a' : α₁} (h : a' ≠ a) (b : β₁) : prodExtendRight a e (a', b) = (a', b) :=
  if_neg h
#align equiv.perm.prod_extend_right_apply_ne Equiv.Perm.prod_extend_right_apply_ne

theorem eq_of_prod_extend_right_ne {e : Perm β₁} {a a' : α₁} {b : β₁} (h : prodExtendRight a e (a', b) ≠ (a', b)) :
    a' = a := by
  contrapose! h
  exact prod_extend_right_apply_ne _ h _
#align equiv.perm.eq_of_prod_extend_right_ne Equiv.Perm.eq_of_prod_extend_right_ne

@[simp]
theorem fst_prod_extend_right (ab : α₁ × β₁) : (prodExtendRight a e ab).fst = ab.fst := by
  rw [prod_extend_right, coe_fn_mk]
  split_ifs with h
  · rw [h]

  · rfl

#align equiv.perm.fst_prod_extend_right Equiv.Perm.fst_prod_extend_right

end Perm

section

/-- The type of functions to a product `α × β` is equivalent to the type of pairs of functions
`γ → α` and `γ → β`. -/
def arrowProdEquivProdArrow (α β γ : Type _) : (γ → α × β) ≃ (γ → α) × (γ → β) :=
  ⟨fun f => (fun c => (f c).1, fun c => (f c).2), fun p c => (p.1 c, p.2 c), fun f => funext fun c => Prod.mk.eta,
    fun p => by
    cases p
    rfl⟩
#align equiv.arrow_prod_equiv_prod_arrow Equiv.arrowProdEquivProdArrow

open Sum

/-- The type of functions on a sum type `α ⊕ β` is equivalent to the type of pairs of functions
on `α` and on `β`. -/
def sumArrowEquivProdArrow (α β γ : Type _) : (Sum α β → γ) ≃ (α → γ) × (β → γ) :=
  ⟨fun f => (f ∘ inl, f ∘ inr), fun p => Sum.elim p.1 p.2, fun f => by ext ⟨⟩ <;> rfl, fun p => by
    cases p
    rfl⟩
#align equiv.sum_arrow_equiv_prod_arrow Equiv.sumArrowEquivProdArrow

@[simp]
theorem sum_arrow_equiv_prod_arrow_apply_fst {α β γ} (f : Sum α β → γ) (a : α) :
    (sumArrowEquivProdArrow α β γ f).1 a = f (inl a) :=
  rfl
#align equiv.sum_arrow_equiv_prod_arrow_apply_fst Equiv.sum_arrow_equiv_prod_arrow_apply_fst

@[simp]
theorem sum_arrow_equiv_prod_arrow_apply_snd {α β γ} (f : Sum α β → γ) (b : β) :
    (sumArrowEquivProdArrow α β γ f).2 b = f (inr b) :=
  rfl
#align equiv.sum_arrow_equiv_prod_arrow_apply_snd Equiv.sum_arrow_equiv_prod_arrow_apply_snd

@[simp]
theorem sum_arrow_equiv_prod_arrow_symm_apply_inl {α β γ} (f : α → γ) (g : β → γ) (a : α) :
    ((sumArrowEquivProdArrow α β γ).symm (f, g)) (inl a) = f a :=
  rfl
#align equiv.sum_arrow_equiv_prod_arrow_symm_apply_inl Equiv.sum_arrow_equiv_prod_arrow_symm_apply_inl

@[simp]
theorem sum_arrow_equiv_prod_arrow_symm_apply_inr {α β γ} (f : α → γ) (g : β → γ) (b : β) :
    ((sumArrowEquivProdArrow α β γ).symm (f, g)) (inr b) = g b :=
  rfl
#align equiv.sum_arrow_equiv_prod_arrow_symm_apply_inr Equiv.sum_arrow_equiv_prod_arrow_symm_apply_inr

/-- Type product is right distributive with respect to type sum up to an equivalence. -/
def sumProdDistrib (α β γ : Sort _) : Sum α β × γ ≃ Sum (α × γ) (β × γ) :=
  ⟨fun p => p.1.map (fun x => (x, p.2)) fun x => (x, p.2), fun s => s.elim (Prod.map inl id) (Prod.map inr id), by
    rintro ⟨_ | _, _⟩ <;> rfl, by rintro (⟨_, _⟩ | ⟨_, _⟩) <;> rfl⟩
#align equiv.sum_prod_distrib Equiv.sumProdDistrib

@[simp]
theorem sum_prod_distrib_apply_left {α β γ} (a : α) (c : γ) : sumProdDistrib α β γ (Sum.inl a, c) = Sum.inl (a, c) :=
  rfl
#align equiv.sum_prod_distrib_apply_left Equiv.sum_prod_distrib_apply_left

@[simp]
theorem sum_prod_distrib_apply_right {α β γ} (b : β) (c : γ) : sumProdDistrib α β γ (Sum.inr b, c) = Sum.inr (b, c) :=
  rfl
#align equiv.sum_prod_distrib_apply_right Equiv.sum_prod_distrib_apply_right

@[simp]
theorem sum_prod_distrib_symm_apply_left {α β γ} (a : α × γ) : (sumProdDistrib α β γ).symm (inl a) = (inl a.1, a.2) :=
  rfl
#align equiv.sum_prod_distrib_symm_apply_left Equiv.sum_prod_distrib_symm_apply_left

@[simp]
theorem sum_prod_distrib_symm_apply_right {α β γ} (b : β × γ) : (sumProdDistrib α β γ).symm (inr b) = (inr b.1, b.2) :=
  rfl
#align equiv.sum_prod_distrib_symm_apply_right Equiv.sum_prod_distrib_symm_apply_right

/-- Type product is left distributive with respect to type sum up to an equivalence. -/
def prodSumDistrib (α β γ : Sort _) : α × Sum β γ ≃ Sum (α × β) (α × γ) :=
  calc
    α × Sum β γ ≃ Sum β γ × α := prodComm _ _
    _ ≃ Sum (β × α) (γ × α) := sumProdDistrib _ _ _
    _ ≃ Sum (α × β) (α × γ) := sumCongr (prodComm _ _) (prodComm _ _)

#align equiv.prod_sum_distrib Equiv.prodSumDistrib

@[simp]
theorem prod_sum_distrib_apply_left {α β γ} (a : α) (b : β) : prodSumDistrib α β γ (a, Sum.inl b) = Sum.inl (a, b) :=
  rfl
#align equiv.prod_sum_distrib_apply_left Equiv.prod_sum_distrib_apply_left

@[simp]
theorem prod_sum_distrib_apply_right {α β γ} (a : α) (c : γ) : prodSumDistrib α β γ (a, Sum.inr c) = Sum.inr (a, c) :=
  rfl
#align equiv.prod_sum_distrib_apply_right Equiv.prod_sum_distrib_apply_right

@[simp]
theorem prod_sum_distrib_symm_apply_left {α β γ} (a : α × β) : (prodSumDistrib α β γ).symm (inl a) = (a.1, inl a.2) :=
  rfl
#align equiv.prod_sum_distrib_symm_apply_left Equiv.prod_sum_distrib_symm_apply_left

@[simp]
theorem prod_sum_distrib_symm_apply_right {α β γ} (a : α × γ) : (prodSumDistrib α β γ).symm (inr a) = (a.1, inr a.2) :=
  rfl
#align equiv.prod_sum_distrib_symm_apply_right Equiv.prod_sum_distrib_symm_apply_right

/-- An indexed sum of disjoint sums of types is equivalent to the sum of the indexed sums. -/
@[simps]
def sigmaSumDistrib {ι : Type _} (α β : ι → Type _) : (Σi, Sum (α i) (β i)) ≃ Sum (Σi, α i) (Σi, β i) :=
  ⟨fun p => p.2.map (Sigma.mk p.1) (Sigma.mk p.1),
    Sum.elim (Sigma.map id fun _ => Sum.inl) (Sigma.map id fun _ => Sum.inr), fun p => by
    rcases p with ⟨i, a | b⟩ <;> rfl, fun p => by rcases p with (⟨i, a⟩ | ⟨i, b⟩) <;> rfl⟩
#align equiv.sigma_sum_distrib Equiv.sigmaSumDistrib

/-- The product of an indexed sum of types (formally, a `sigma`-type `Σ i, α i`) by a type `β` is
equivalent to the sum of products `Σ i, (α i × β)`. -/
def sigmaProdDistrib {ι : Type _} (α : ι → Type _) (β : Type _) : (Σi, α i) × β ≃ Σi, α i × β :=
  ⟨fun p => ⟨p.1.1, (p.1.2, p.2)⟩, fun p => (⟨p.1, p.2.1⟩, p.2.2), fun p => by
    rcases p with ⟨⟨_, _⟩, _⟩
    rfl, fun p => by
    rcases p with ⟨_, ⟨_, _⟩⟩
    rfl⟩
#align equiv.sigma_prod_distrib Equiv.sigmaProdDistrib

/-- An equivalence that separates out the 0th fiber of `(Σ (n : ℕ), f n)`. -/
def sigmaNatSucc (f : ℕ → Type u) : (Σn, f n) ≃ Sum (f 0) (Σn, f (n + 1)) :=
  ⟨fun x =>
    @Sigma.casesOn ℕ f (fun _ => Sum (f 0) (Σn, f (n + 1))) x fun n =>
      @Nat.casesOn (fun i => f i → Sum (f 0) (Σn : ℕ, f (n + 1))) n (fun x : f 0 => Sum.inl x)
        fun (n : ℕ) (x : f n.succ) => Sum.inr ⟨n, x⟩,
    Sum.elim (Sigma.mk 0) (Sigma.map Nat.succ fun _ => id), by rintro ⟨n | n, x⟩ <;> rfl, by
    rintro (x | ⟨n, x⟩) <;> rfl⟩
#align equiv.sigma_nat_succ Equiv.sigmaNatSucc

/-- The product `bool × α` is equivalent to `α ⊕ α`. -/
@[simps]
def boolProdEquivSum (α : Type u) : Bool × α ≃ Sum α α where
  toFun p := cond p.1 (inr p.2) (inl p.2)
  invFun := Sum.elim (Prod.mk false) (Prod.mk true)
  left_inv := by rintro ⟨_ | _, _⟩ <;> rfl
  right_inv := by rintro (_ | _) <;> rfl
#align equiv.bool_prod_equiv_sum Equiv.boolProdEquivSum

/-- The function type `bool → α` is equivalent to `α × α`. -/
@[simps]
def boolArrowEquivProd (α : Type u) : (Bool → α) ≃ α × α where
  toFun f := (f true, f false)
  invFun p b := cond b p.1 p.2
  left_inv f := funext <| Bool.forall_bool.2 ⟨rfl, rfl⟩
  right_inv := fun ⟨x, y⟩ => rfl
#align equiv.bool_arrow_equiv_prod Equiv.boolArrowEquivProd

end

section

open Sum Nat

/-- The set of natural numbers is equivalent to `ℕ ⊕ punit`. -/
def natEquivNatSumPunit : ℕ ≃ Sum ℕ PUnit.{u + 1} where
  toFun n := Nat.casesOn n (inr PUnit.unit) inl
  invFun := Sum.elim Nat.succ fun _ => 0
  left_inv n := by cases n <;> rfl
  right_inv := by rintro (_ | _ | _) <;> rfl
#align equiv.nat_equiv_nat_sum_punit Equiv.natEquivNatSumPunit

/-- `ℕ ⊕ punit` is equivalent to `ℕ`. -/
def natSumPunitEquivNat : Sum ℕ PUnit.{u + 1} ≃ ℕ :=
  natEquivNatSumPunit.symm
#align equiv.nat_sum_punit_equiv_nat Equiv.natSumPunitEquivNat

/-- The type of integer numbers is equivalent to `ℕ ⊕ ℕ`. -/
def intEquivNatSumNat : ℤ ≃ Sum ℕ ℕ where
  toFun z := Int.casesOn z inl inr
  invFun := Sum.elim coe Int.negSucc
  left_inv := by rintro (m | n) <;> rfl
  right_inv := by rintro (m | n) <;> rfl
#align equiv.int_equiv_nat_sum_nat Equiv.intEquivNatSumNat

end

/-- An equivalence between `α` and `β` generates an equivalence between `list α` and `list β`. -/
def listEquivOfEquiv {α β : Type _} (e : α ≃ β) : List α ≃ List β where
  toFun := List.map e
  invFun := List.map e.symm
  left_inv l := by rw [List.map_map, e.symm_comp_self, List.map_id]
  right_inv l := by rw [List.map_map, e.self_comp_symm, List.map_id]
#align equiv.list_equiv_of_equiv Equiv.listEquivOfEquiv

/-- If `α` is equivalent to `β`, then `unique α` is equivalent to `unique β`. -/
def uniqueCongr (e : α ≃ β) : Unique α ≃ Unique β where
  toFun h := @Equiv.unique _ _ h e.symm
  invFun h := @Equiv.unique _ _ h e
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align equiv.unique_congr Equiv.uniqueCongr

/-- If `α` is equivalent to `β`, then `is_empty α` is equivalent to `is_empty β`. -/
theorem is_empty_congr (e : α ≃ β) : IsEmpty α ↔ IsEmpty β :=
  ⟨fun h => @function.isEmpty _ _ h e.symm, fun h => @function.isEmpty _ _ h e⟩
#align equiv.is_empty_congr Equiv.is_empty_congr

protected theorem is_empty (e : α ≃ β) [IsEmpty β] : IsEmpty α :=
  e.is_empty_congr.mpr ‹_›
#align equiv.is_empty Equiv.is_empty

section

open Subtype

/-- If `α` is equivalent to `β` and the predicates `p : α → Prop` and `q : β → Prop` are equivalent
at corresponding points, then `{a // p a}` is equivalent to `{b // q b}`.
For the statement where `α = β`, that is, `e : perm α`, see `perm.subtype_perm`. -/
def subtypeEquiv {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : ∀ a, p a ↔ q (e a)) :
    { a : α // p a } ≃ { b : β // q b } where
  toFun a := ⟨e a, (h _).mp a.Prop⟩
  invFun b := ⟨e.symm b, (h _).mpr ((e.apply_symm_apply b).symm ▸ b.Prop)⟩
  left_inv a := Subtype.ext <| by simp
  right_inv b := Subtype.ext <| by simp
#align equiv.subtype_equiv Equiv.subtypeEquiv

@[simp]
theorem subtype_equiv_refl {p : α → Prop} (h : ∀ a, p a ↔ p (Equiv.refl _ a) := fun a => Iff.rfl) :
    (Equiv.refl α).subtypeEquiv h = Equiv.refl { a : α // p a } := by
  ext
  rfl
#align equiv.subtype_equiv_refl Equiv.subtype_equiv_refl

@[simp]
theorem subtype_equiv_symm {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : ∀ a : α, p a ↔ q (e a)) :
    (e.subtypeEquiv h).symm =
      e.symm.subtypeEquiv fun a => by
        convert (h <| e.symm a).symm
        exact (e.apply_symm_apply a).symm :=
  rfl
#align equiv.subtype_equiv_symm Equiv.subtype_equiv_symm

@[simp]
theorem subtype_equiv_trans {p : α → Prop} {q : β → Prop} {r : γ → Prop} (e : α ≃ β) (f : β ≃ γ)
    (h : ∀ a : α, p a ↔ q (e a)) (h' : ∀ b : β, q b ↔ r (f b)) :
    (e.subtypeEquiv h).trans (f.subtypeEquiv h') = (e.trans f).subtypeEquiv fun a => (h a).trans (h' <| e a) :=
  rfl
#align equiv.subtype_equiv_trans Equiv.subtype_equiv_trans

@[simp]
theorem subtype_equiv_apply {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : ∀ a : α, p a ↔ q (e a)) (x : { x // p x }) :
    e.subtypeEquiv h x = ⟨e x, (h _).1 x.2⟩ :=
  rfl
#align equiv.subtype_equiv_apply Equiv.subtype_equiv_apply

/-- If two predicates `p` and `q` are pointwise equivalent, then `{x // p x}` is equivalent to
`{x // q x}`. -/
@[simps]
def subtypeEquivRight {p q : α → Prop} (e : ∀ x, p x ↔ q x) : { x // p x } ≃ { x // q x } :=
  subtypeEquiv (Equiv.refl _) e
#align equiv.subtype_equiv_right Equiv.subtypeEquivRight

/-- If `α ≃ β`, then for any predicate `p : β → Prop` the subtype `{a // p (e a)}` is equivalent
to the subtype `{b // p b}`. -/
def subtypeEquivOfSubtype {p : β → Prop} (e : α ≃ β) : { a : α // p (e a) } ≃ { b : β // p b } :=
  subtypeEquiv e <| by simp
#align equiv.subtype_equiv_of_subtype Equiv.subtypeEquivOfSubtype

/-- If `α ≃ β`, then for any predicate `p : α → Prop` the subtype `{a // p a}` is equivalent
to the subtype `{b // p (e.symm b)}`. This version is used by `equiv_rw`. -/
def subtypeEquivOfSubtype' {p : α → Prop} (e : α ≃ β) : { a : α // p a } ≃ { b : β // p (e.symm b) } :=
  e.symm.subtypeEquivOfSubtype.symm
#align equiv.subtype_equiv_of_subtype' Equiv.subtypeEquivOfSubtype'

/-- If two predicates are equal, then the corresponding subtypes are equivalent. -/
def subtypeEquivProp {α : Type _} {p q : α → Prop} (h : p = q) : Subtype p ≃ Subtype q :=
  subtypeEquiv (Equiv.refl α) fun a => h ▸ Iff.rfl
#align equiv.subtype_equiv_prop Equiv.subtypeEquivProp

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. This
version allows the “inner” predicate to depend on `h : p a`. -/
@[simps]
def subtypeSubtypeEquivSubtypeExists {α : Type u} (p : α → Prop) (q : Subtype p → Prop) :
    Subtype q ≃ { a : α // ∃ h : p a, q ⟨a, h⟩ } :=
  ⟨fun a =>
    ⟨a, a.1.2, by
      rcases a with ⟨⟨a, hap⟩, haq⟩
      exact haq⟩,
    fun a => ⟨⟨a, a.2.fst⟩, a.2.snd⟩, fun ⟨⟨a, ha⟩, h⟩ => rfl, fun ⟨a, h₁, h₂⟩ => rfl⟩
#align equiv.subtype_subtype_equiv_subtype_exists Equiv.subtypeSubtypeEquivSubtypeExists

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. -/
@[simps]
def subtypeSubtypeEquivSubtypeInter {α : Type u} (p q : α → Prop) :
    { x : Subtype p // q x.1 } ≃ Subtype fun x => p x ∧ q x :=
  (subtypeSubtypeEquivSubtypeExists p _).trans <| subtype_equiv_right fun x => exists_prop
#align equiv.subtype_subtype_equiv_subtype_inter Equiv.subtypeSubtypeEquivSubtypeInter

/-- If the outer subtype has more restrictive predicate than the inner one,
then we can drop the latter. -/
@[simps]
def subtypeSubtypeEquivSubtype {α : Type u} {p q : α → Prop} (h : ∀ {x}, q x → p x) :
    { x : Subtype p // q x.1 } ≃ Subtype q :=
  (subtypeSubtypeEquivSubtypeInter p _).trans <| subtype_equiv_right fun x => and_iff_right_of_imp h
#align equiv.subtype_subtype_equiv_subtype Equiv.subtypeSubtypeEquivSubtype

/-- If a proposition holds for all elements, then the subtype is
equivalent to the original type. -/
@[simps apply symmApply]
def subtypeUnivEquiv {α : Type u} {p : α → Prop} (h : ∀ x, p x) : Subtype p ≃ α :=
  ⟨fun x => x, fun x => ⟨x, h x⟩, fun x => Subtype.eq rfl, fun x => rfl⟩
#align equiv.subtype_univ_equiv Equiv.subtypeUnivEquiv

/-- A subtype of a sigma-type is a sigma-type over a subtype. -/
def subtypeSigmaEquiv {α : Type u} (p : α → Type v) (q : α → Prop) : { y : Sigma p // q y.1 } ≃ Σx : Subtype q, p x.1 :=
  ⟨fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, fun ⟨⟨x, h⟩, y⟩ => rfl, fun ⟨⟨x, y⟩, h⟩ => rfl⟩
#align equiv.subtype_sigma_equiv Equiv.subtypeSigmaEquiv

/-- A sigma type over a subtype is equivalent to the sigma set over the original type,
if the fiber is empty outside of the subset -/
def sigmaSubtypeEquivOfSubset {α : Type u} (p : α → Type v) (q : α → Prop) (h : ∀ x, p x → q x) :
    (Σx : Subtype q, p x) ≃ Σx : α, p x :=
  (subtypeSigmaEquiv p q).symm.trans <| subtype_univ_equiv fun x => h x.1 x.2
#align equiv.sigma_subtype_equiv_of_subset Equiv.sigmaSubtypeEquivOfSubset

/-- If a predicate `p : β → Prop` is true on the range of a map `f : α → β`, then
`Σ y : {y // p y}, {x // f x = y}` is equivalent to `α`. -/
def sigmaSubtypeFiberEquiv {α : Type u} {β : Type v} (f : α → β) (p : β → Prop) (h : ∀ x, p (f x)) :
    (Σy : Subtype p, { x : α // f x = y }) ≃ α :=
  calc
    _ ≃ Σy : β, { x : α // f x = y } := sigmaSubtypeEquivOfSubset _ p fun y ⟨x, h'⟩ => h' ▸ h x
    _ ≃ α := sigmaFiberEquiv f

#align equiv.sigma_subtype_fiber_equiv Equiv.sigmaSubtypeFiberEquiv

/-- If for each `x` we have `p x ↔ q (f x)`, then `Σ y : {y // q y}, f ⁻¹' {y}` is equivalent
to `{x // p x}`. -/
def sigmaSubtypeFiberEquivSubtype {α : Type u} {β : Type v} (f : α → β) {p : α → Prop} {q : β → Prop}
    (h : ∀ x, p x ↔ q (f x)) : (Σy : Subtype q, { x : α // f x = y }) ≃ Subtype p :=
  calc
    (Σy : Subtype q, { x : α // f x = y }) ≃ Σy : Subtype q, { x : Subtype p // Subtype.mk (f x) ((h x).1 x.2) = y } :=
      by
      apply sigma_congr_right
      intro y
      symm
      refine' (subtype_subtype_equiv_subtype_exists _ _).trans (subtype_equiv_right _)
      intro x
      exact ⟨fun ⟨hp, h'⟩ => congr_arg Subtype.val h', fun h' => ⟨(h x).2 (h'.symm ▸ y.2), Subtype.eq h'⟩⟩
    _ ≃ Subtype p := sigmaFiberEquiv fun x : Subtype p => (⟨f x, (h x).1 x.property⟩ : Subtype q)

#align equiv.sigma_subtype_fiber_equiv_subtype Equiv.sigmaSubtypeFiberEquivSubtype

/-- A sigma type over an `option` is equivalent to the sigma set over the original type,
if the fiber is empty at none. -/
def sigmaOptionEquivOfSome {α : Type u} (p : Option α → Type v) (h : p none → False) :
    (Σx : Option α, p x) ≃ Σx : α, p (some x) :=
  haveI h' : ∀ x, p x → x.isSome := by
    intro x
    cases x
    · intro n
      exfalso
      exact h n

    · intro s
      exact rfl

  (sigma_subtype_equiv_of_subset _ _ h').symm.trans (sigma_congr_left' (option_is_some_equiv α))
#align equiv.sigma_option_equiv_of_some Equiv.sigmaOptionEquivOfSome

/-- The `pi`-type `Π i, π i` is equivalent to the type of sections `f : ι → Σ i, π i` of the
`sigma` type such that for all `i` we have `(f i).fst = i`. -/
def piEquivSubtypeSigma (ι : Type _) (π : ι → Type _) : (∀ i, π i) ≃ { f : ι → Σi, π i // ∀ i, (f i).1 = i } :=
  ⟨fun f => ⟨fun i => ⟨i, f i⟩, fun i => rfl⟩, fun f i => by
    rw [← f.2 i]
    exact (f.1 i).2, fun f => funext fun i => rfl, fun ⟨f, hf⟩ =>
    Subtype.eq <|
      funext fun i => Sigma.eq (hf i).symm <| eq_of_heq <| rec_heq_of_heq _ <| rec_heq_of_heq _ <| HEq.refl _⟩
#align equiv.pi_equiv_subtype_sigma Equiv.piEquivSubtypeSigma

/-- The set of functions `f : Π a, β a` such that for all `a` we have `p a (f a)` is equivalent
to the set of functions `Π a, {b : β a // p a b}`. -/
def subtypePiEquivPi {α : Sort u} {β : α → Sort v} {p : ∀ a, β a → Prop} :
    { f : ∀ a, β a // ∀ a, p a (f a) } ≃ ∀ a, { b : β a // p a b } :=
  ⟨fun f a => ⟨f.1 a, f.2 a⟩, fun f => ⟨fun a => (f a).1, fun a => (f a).2⟩, by
    rintro ⟨f, h⟩
    rfl, by
    rintro f
    funext a
    exact Subtype.ext_val rfl⟩
#align equiv.subtype_pi_equiv_pi Equiv.subtypePiEquivPi

/-- A subtype of a product defined by componentwise conditions
is equivalent to a product of subtypes. -/
def subtypeProdEquivProd {α : Type u} {β : Type v} {p : α → Prop} {q : β → Prop} :
    { c : α × β // p c.1 ∧ q c.2 } ≃ { a // p a } × { b // q b } :=
  ⟨fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩, fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩, fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl,
    fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl⟩
#align equiv.subtype_prod_equiv_prod Equiv.subtypeProdEquivProd

/-- A subtype of a `prod` is equivalent to a sigma type whose fibers are subtypes. -/
def subtypeProdEquivSigmaSubtype {α β : Type _} (p : α → β → Prop) :
    { x : α × β // p x.1 x.2 } ≃ Σa, { b : β // p a b } where
  toFun x := ⟨x.1.1, x.1.2, x.Prop⟩
  invFun x := ⟨⟨x.1, x.2⟩, x.2.Prop⟩
  left_inv x := by ext <;> rfl
  right_inv := fun ⟨a, b, pab⟩ => rfl
#align equiv.subtype_prod_equiv_sigma_subtype Equiv.subtypeProdEquivSigmaSubtype

/-- The type `Π (i : α), β i` can be split as a product by separating the indices in `α`
depending on whether they satisfy a predicate `p` or not. -/
@[simps]
def piEquivPiSubtypeProd {α : Type _} (p : α → Prop) (β : α → Type _) [DecidablePred p] :
    (∀ i : α, β i) ≃ (∀ i : { x // p x }, β i) × ∀ i : { x // ¬p x }, β i where
  toFun f := (fun x => f x, fun x => f x)
  invFun f x := if h : p x then f.1 ⟨x, h⟩ else f.2 ⟨x, h⟩
  right_inv := by
    rintro ⟨f, g⟩
    ext1 <;>
      · ext y
        rcases y with ⟨⟩
        simp only [y_property, dif_pos, dif_neg, not_false_iff, Subtype.coe_mk]
        rfl

  left_inv f := by
    ext x
    by_cases h:p x <;>
      · simp only [h, dif_neg, dif_pos, not_false_iff]
        rfl

#align equiv.pi_equiv_pi_subtype_prod Equiv.piEquivPiSubtypeProd

/-- A product of types can be split as the binary product of one of the types and the product
  of all the remaining types. -/
@[simps]
def piSplitAt {α : Type _} [DecidableEq α] (i : α) (β : α → Type _) : (∀ j, β j) ≃ β i × ∀ j : { j // j ≠ i }, β j where
  toFun f := ⟨f i, fun j => f j⟩
  invFun f j := if h : j = i then h.symm.rec f.1 else f.2 ⟨j, h⟩
  right_inv f := by
    ext
    exacts[dif_pos rfl, (dif_neg x.2).trans (by cases x <;> rfl)]
  left_inv f := by
    ext
    dsimp only
    split_ifs
    · subst h

    · rfl

#align equiv.pi_split_at Equiv.piSplitAt

/-- A product of copies of a type can be split as the binary product of one copy and the product
  of all the remaining copies. -/
@[simps]
def funSplitAt {α : Type _} [DecidableEq α] (i : α) (β : Type _) : (α → β) ≃ β × ({ j // j ≠ i } → β) :=
  piSplitAt i _
#align equiv.fun_split_at Equiv.funSplitAt

end

section SubtypeEquivCodomain

variable {X : Type _} {Y : Type _} [DecidableEq X] {x : X}

/-- The type of all functions `X → Y` with prescribed values for all `x' ≠ x`
is equivalent to the codomain `Y`. -/
def subtypeEquivCodomain (f : { x' // x' ≠ x } → Y) : { g : X → Y // g ∘ coe = f } ≃ Y :=
  (subtypePreimage _ f).trans <|
    @funUnique { x' // ¬x' ≠ x } _ <|
      show Unique { x' // ¬x' ≠ x } from
        @Equiv.unique _ _
          (show Unique { x' // x' = x } from { default := ⟨x, rfl⟩, uniq := fun ⟨x', h⟩ => Subtype.val_injective h })
          (subtype_equiv_right fun a => not_not)
#align equiv.subtype_equiv_codomain Equiv.subtypeEquivCodomain

@[simp]
theorem coe_subtype_equiv_codomain (f : { x' // x' ≠ x } → Y) :
    (subtypeEquivCodomain f : { g : X → Y // g ∘ coe = f } → Y) = fun g => (g : X → Y) x :=
  rfl
#align equiv.coe_subtype_equiv_codomain Equiv.coe_subtype_equiv_codomain

@[simp]
theorem subtype_equiv_codomain_apply (f : { x' // x' ≠ x } → Y) (g : { g : X → Y // g ∘ coe = f }) :
    subtypeEquivCodomain f g = (g : X → Y) x :=
  rfl
#align equiv.subtype_equiv_codomain_apply Equiv.subtype_equiv_codomain_apply

theorem coe_subtype_equiv_codomain_symm (f : { x' // x' ≠ x } → Y) :
    ((subtypeEquivCodomain f).symm : Y → { g : X → Y // g ∘ coe = f }) = fun y =>
      ⟨fun x' => if h : x' ≠ x then f ⟨x', h⟩ else y, by
        funext x'
        dsimp
        erw [dif_pos x'.2, Subtype.coe_eta]⟩ :=
  rfl
#align equiv.coe_subtype_equiv_codomain_symm Equiv.coe_subtype_equiv_codomain_symm

@[simp]
theorem subtype_equiv_codomain_symm_apply (f : { x' // x' ≠ x } → Y) (y : Y) (x' : X) :
    ((subtypeEquivCodomain f).symm y : X → Y) x' = if h : x' ≠ x then f ⟨x', h⟩ else y :=
  rfl
#align equiv.subtype_equiv_codomain_symm_apply Equiv.subtype_equiv_codomain_symm_apply

@[simp]
theorem subtype_equiv_codomain_symm_apply_eq (f : { x' // x' ≠ x } → Y) (y : Y) :
    ((subtypeEquivCodomain f).symm y : X → Y) x = y :=
  dif_neg (not_not.mpr rfl)
#align equiv.subtype_equiv_codomain_symm_apply_eq Equiv.subtype_equiv_codomain_symm_apply_eq

theorem subtype_equiv_codomain_symm_apply_ne (f : { x' // x' ≠ x } → Y) (y : Y) (x' : X) (h : x' ≠ x) :
    ((subtypeEquivCodomain f).symm y : X → Y) x' = f ⟨x', h⟩ :=
  dif_pos h
#align equiv.subtype_equiv_codomain_symm_apply_ne Equiv.subtype_equiv_codomain_symm_apply_ne

end SubtypeEquivCodomain

/-- If `f` is a bijective function, then its domain is equivalent to its codomain. -/
@[simps apply]
noncomputable def ofBijective (f : α → β) (hf : Bijective f) : α ≃ β where
  toFun := f
  invFun := Function.surjInv hf.Surjective
  left_inv := Function.left_inverse_surj_inv hf
  right_inv := Function.right_inverse_surj_inv _
#align equiv.of_bijective Equiv.ofBijective

theorem of_bijective_apply_symm_apply (f : α → β) (hf : Bijective f) (x : β) : f ((ofBijective f hf).symm x) = x :=
  (ofBijective f hf).apply_symm_apply x
#align equiv.of_bijective_apply_symm_apply Equiv.of_bijective_apply_symm_apply

@[simp]
theorem of_bijective_symm_apply_apply (f : α → β) (hf : Bijective f) (x : α) : (ofBijective f hf).symm (f x) = x :=
  (ofBijective f hf).symm_apply_apply x
#align equiv.of_bijective_symm_apply_apply Equiv.of_bijective_symm_apply_apply

instance : CanLift (α → β) (α ≃ β) coeFn Bijective where prf f hf := ⟨ofBijective f hf, rfl⟩

section

variable {α' β' : Type _} (e : Perm α') {p : β' → Prop} [DecidablePred p] (f : α' ≃ Subtype p)

/-- Extend the domain of `e : equiv.perm α` to one that is over `β` via `f : α → subtype p`,
where `p : β → Prop`, permuting only the `b : β` that satisfy `p b`.
This can be used to extend the domain across a function `f : α → β`,
keeping everything outside of `set.range f` fixed. For this use-case `equiv` given by `f` can
be constructed by `equiv.of_left_inverse'` or `equiv.of_left_inverse` when there is a known
inverse, or `equiv.of_injective` in the general case.`.
-/
def Perm.extendDomain : Perm β' :=
  (permCongr f e).subtypeCongr (Equiv.refl _)
#align equiv.perm.extend_domain Equiv.Perm.extendDomain

@[simp]
theorem Perm.extend_domain_apply_image (a : α') : e.extendDomain f (f a) = f (e a) := by simp [perm.extend_domain]
#align equiv.perm.extend_domain_apply_image Equiv.Perm.extend_domain_apply_image

theorem Perm.extend_domain_apply_subtype {b : β'} (h : p b) : e.extendDomain f b = f (e (f.symm ⟨b, h⟩)) := by
  simp [perm.extend_domain, h]
#align equiv.perm.extend_domain_apply_subtype Equiv.Perm.extend_domain_apply_subtype

theorem Perm.extend_domain_apply_not_subtype {b : β'} (h : ¬p b) : e.extendDomain f b = b := by
  simp [perm.extend_domain, h]
#align equiv.perm.extend_domain_apply_not_subtype Equiv.Perm.extend_domain_apply_not_subtype

@[simp]
theorem Perm.extend_domain_refl : Perm.extendDomain (Equiv.refl _) f = Equiv.refl _ := by simp [perm.extend_domain]
#align equiv.perm.extend_domain_refl Equiv.Perm.extend_domain_refl

@[simp]
theorem Perm.extend_domain_symm : (e.extendDomain f).symm = Perm.extendDomain e.symm f :=
  rfl
#align equiv.perm.extend_domain_symm Equiv.Perm.extend_domain_symm

theorem Perm.extend_domain_trans (e e' : Perm α') :
    (e.extendDomain f).trans (e'.extendDomain f) = Perm.extendDomain (e.trans e') f := by
  simp [perm.extend_domain, perm_congr_trans]
#align equiv.perm.extend_domain_trans Equiv.Perm.extend_domain_trans

end

/-- Subtype of the quotient is equivalent to the quotient of the subtype. Let `α` be a setoid with
equivalence relation `~`. Let `p₂` be a predicate on the quotient type `α/~`, and `p₁` be the lift
of this predicate to `α`: `p₁ a ↔ p₂ ⟦a⟧`. Let `~₂` be the restriction of `~` to `{x // p₁ x}`.
Then `{x // p₂ x}` is equivalent to the quotient of `{x // p₁ x}` by `~₂`. -/
def subtypeQuotientEquivQuotientSubtype (p₁ : α → Prop) [s₁ : Setoid α] [s₂ : Setoid (Subtype p₁)]
    (p₂ : Quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧) (h : ∀ x y : Subtype p₁, @Setoid.r _ s₂ x y ↔ (x : α) ≈ y) :
    { x // p₂ x } ≃ Quotient s₂ where
  toFun a :=
    Quotient.hrecOn a.1 (fun a h => ⟦⟨a, (hp₂ _).2 h⟩⟧)
      (fun a b hab => hfunext (by rw [Quotient.sound hab]) fun h₁ h₂ _ => heq_of_eq (Quotient.sound ((h _ _).2 hab)))
      a.2
  invFun a :=
    Quotient.liftOn a (fun a => (⟨⟦a.1⟧, (hp₂ _).1 a.2⟩ : { x // p₂ x })) fun a b hab =>
      Subtype.ext_val (Quotient.sound ((h _ _).1 hab))
  left_inv := fun ⟨a, ha⟩ => Quotient.induction_on a (fun a ha => rfl) ha
  right_inv a := Quotient.induction_on a fun ⟨a, ha⟩ => rfl
#align equiv.subtype_quotient_equiv_quotient_subtype Equiv.subtypeQuotientEquivQuotientSubtype

@[simp]
theorem subtype_quotient_equiv_quotient_subtype_mk (p₁ : α → Prop) [s₁ : Setoid α] [s₂ : Setoid (Subtype p₁)]
    (p₂ : Quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧) (h : ∀ x y : Subtype p₁, @Setoid.r _ s₂ x y ↔ (x : α) ≈ y)
    (x hx) : subtypeQuotientEquivQuotientSubtype p₁ p₂ hp₂ h ⟨⟦x⟧, hx⟩ = ⟦⟨x, (hp₂ _).2 hx⟩⟧ :=
  rfl
#align equiv.subtype_quotient_equiv_quotient_subtype_mk Equiv.subtype_quotient_equiv_quotient_subtype_mk

@[simp]
theorem subtype_quotient_equiv_quotient_subtype_symm_mk (p₁ : α → Prop) [s₁ : Setoid α] [s₂ : Setoid (Subtype p₁)]
    (p₂ : Quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧) (h : ∀ x y : Subtype p₁, @Setoid.r _ s₂ x y ↔ (x : α) ≈ y)
    (x) : (subtypeQuotientEquivQuotientSubtype p₁ p₂ hp₂ h).symm ⟦x⟧ = ⟨⟦x⟧, (hp₂ _).1 x.Prop⟩ :=
  rfl
#align equiv.subtype_quotient_equiv_quotient_subtype_symm_mk Equiv.subtype_quotient_equiv_quotient_subtype_symm_mk

section Swap

variable [DecidableEq α]

/-- A helper function for `equiv.swap`. -/
def swapCore (a b r : α) : α :=
  if r = a then b else if r = b then a else r
#align equiv.swap_core Equiv.swapCore

theorem swap_core_self (r a : α) : swapCore a a r = r := by
  unfold swap_core
  split_ifs <;> cc
#align equiv.swap_core_self Equiv.swap_core_self

theorem swap_core_swap_core (r a b : α) : swapCore a b (swapCore a b r) = r := by
  unfold swap_core
  split_ifs <;> cc
#align equiv.swap_core_swap_core Equiv.swap_core_swap_core

theorem swap_core_comm (r a b : α) : swapCore a b r = swapCore b a r := by
  unfold swap_core
  split_ifs <;> cc
#align equiv.swap_core_comm Equiv.swap_core_comm

/-- `swap a b` is the permutation that swaps `a` and `b` and
  leaves other values as is. -/
def swap (a b : α) : Perm α :=
  ⟨swapCore a b, swapCore a b, fun r => swap_core_swap_core r a b, fun r => swap_core_swap_core r a b⟩
#align equiv.swap Equiv.swap

@[simp]
theorem swap_self (a : α) : swap a a = Equiv.refl _ :=
  ext fun r => swap_core_self r a
#align equiv.swap_self Equiv.swap_self

theorem swap_comm (a b : α) : swap a b = swap b a :=
  ext fun r => swap_core_comm r _ _
#align equiv.swap_comm Equiv.swap_comm

theorem swap_apply_def (a b x : α) : swap a b x = if x = a then b else if x = b then a else x :=
  rfl
#align equiv.swap_apply_def Equiv.swap_apply_def

@[simp]
theorem swap_apply_left (a b : α) : swap a b a = b :=
  if_pos rfl
#align equiv.swap_apply_left Equiv.swap_apply_left

@[simp]
theorem swap_apply_right (a b : α) : swap a b b = a := by by_cases h:b = a <;> simp [swap_apply_def, h]
#align equiv.swap_apply_right Equiv.swap_apply_right

theorem swap_apply_of_ne_of_ne {a b x : α} : x ≠ a → x ≠ b → swap a b x = x := by
  simp (config := { contextual := true }) [swap_apply_def]
#align equiv.swap_apply_of_ne_of_ne Equiv.swap_apply_of_ne_of_ne

@[simp]
theorem swap_swap (a b : α) : (swap a b).trans (swap a b) = Equiv.refl _ :=
  ext fun x => swap_core_swap_core _ _ _
#align equiv.swap_swap Equiv.swap_swap

@[simp]
theorem symm_swap (a b : α) : (swap a b).symm = swap a b :=
  rfl
#align equiv.symm_swap Equiv.symm_swap

@[simp]
theorem swap_eq_refl_iff {x y : α} : swap x y = Equiv.refl _ ↔ x = y := by
  refine' ⟨fun h => (Equiv.refl _).Injective _, fun h => h ▸ swap_self _⟩
  rw [← h, swap_apply_left, h, refl_apply]
#align equiv.swap_eq_refl_iff Equiv.swap_eq_refl_iff

theorem swap_comp_apply {a b x : α} (π : Perm α) :
    π.trans (swap a b) x = if π x = a then b else if π x = b then a else π x := by
  cases π
  rfl
#align equiv.swap_comp_apply Equiv.swap_comp_apply

theorem swap_eq_update (i j : α) : (Equiv.swap i j : α → α) = update (update id j i) i j :=
  funext fun x => by rw [update_apply _ i j, update_apply _ j i, Equiv.swap_apply_def, id.def]
#align equiv.swap_eq_update Equiv.swap_eq_update

theorem comp_swap_eq_update (i j : α) (f : α → β) : f ∘ Equiv.swap i j = update (update f j (f i)) i (f j) := by
  rw [swap_eq_update, comp_update, comp_update, comp.right_id]
#align equiv.comp_swap_eq_update Equiv.comp_swap_eq_update

@[simp]
theorem symm_trans_swap_trans [DecidableEq β] (a b : α) (e : α ≃ β) :
    (e.symm.trans (swap a b)).trans e = swap (e a) (e b) :=
  Equiv.ext fun x => by
    have : ∀ a, e.symm x = a ↔ x = e a := fun a => by
      rw [@eq_comm _ (e.symm x)]
      constructor <;> intros <;> simp_all
    simp [swap_apply_def, this]
    split_ifs <;> simp
#align equiv.symm_trans_swap_trans Equiv.symm_trans_swap_trans

@[simp]
theorem trans_swap_trans_symm [DecidableEq β] (a b : β) (e : α ≃ β) :
    (e.trans (swap a b)).trans e.symm = swap (e.symm a) (e.symm b) :=
  symm_trans_swap_trans a b e.symm
#align equiv.trans_swap_trans_symm Equiv.trans_swap_trans_symm

@[simp]
theorem swap_apply_self (i j a : α) : swap i j (swap i j a) = a := by
  rw [← Equiv.trans_apply, Equiv.swap_swap, Equiv.refl_apply]
#align equiv.swap_apply_self Equiv.swap_apply_self

/-- A function is invariant to a swap if it is equal at both elements -/
theorem apply_swap_eq_self {v : α → β} {i j : α} (hv : v i = v j) (k : α) : v (swap i j k) = v k := by
  by_cases hi:k = i
  · rw [hi, swap_apply_left, hv]

  by_cases hj:k = j
  · rw [hj, swap_apply_right, hv]

  rw [swap_apply_of_ne_of_ne hi hj]
#align equiv.apply_swap_eq_self Equiv.apply_swap_eq_self

theorem swap_apply_eq_iff {x y z w : α} : swap x y z = w ↔ z = swap x y w := by
  rw [apply_eq_iff_eq_symm_apply, symm_swap]
#align equiv.swap_apply_eq_iff Equiv.swap_apply_eq_iff

theorem swap_apply_ne_self_iff {a b x : α} : swap a b x ≠ x ↔ a ≠ b ∧ (x = a ∨ x = b) := by
  by_cases hab:a = b
  · simp [hab]

  by_cases hax:x = a
  · simp [hax, eq_comm]

  by_cases hbx:x = b
  · simp [hbx]

  simp [hab, hax, hbx, swap_apply_of_ne_of_ne]
#align equiv.swap_apply_ne_self_iff Equiv.swap_apply_ne_self_iff

namespace Perm

@[simp]
theorem sum_congr_swap_refl {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : α) :
    Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.refl β) = Equiv.swap (Sum.inl i) (Sum.inl j) := by
  ext x
  cases x
  · simp [Sum.map, swap_apply_def]
    split_ifs <;> rfl

  · simp [Sum.map, swap_apply_of_ne_of_ne]

#align equiv.perm.sum_congr_swap_refl Equiv.Perm.sum_congr_swap_refl

@[simp]
theorem sum_congr_refl_swap {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : β) :
    Equiv.Perm.sumCongr (Equiv.refl α) (Equiv.swap i j) = Equiv.swap (Sum.inr i) (Sum.inr j) := by
  ext x
  cases x
  · simp [Sum.map, swap_apply_of_ne_of_ne]

  · simp [Sum.map, swap_apply_def]
    split_ifs <;> rfl

#align equiv.perm.sum_congr_refl_swap Equiv.Perm.sum_congr_refl_swap

end Perm

/-- Augment an equivalence with a prescribed mapping `f a = b` -/
def setValue (f : α ≃ β) (a : α) (b : β) : α ≃ β :=
  (swap a (f.symm b)).trans f
#align equiv.set_value Equiv.setValue

@[simp]
theorem set_value_eq (f : α ≃ β) (a : α) (b : β) : setValue f a b a = b := by
  dsimp [set_value]
  simp [swap_apply_left]
#align equiv.set_value_eq Equiv.set_value_eq

end Swap

end Equiv

namespace Function.Involutive

/-- Convert an involutive function `f` to a permutation with `to_fun = inv_fun = f`. -/
def toPerm (f : α → α) (h : Involutive f) : Equiv.Perm α :=
  ⟨f, f, h.LeftInverse, h.RightInverse⟩
#align function.involutive.to_perm Function.Involutive.toPerm

@[simp]
theorem coe_to_perm {f : α → α} (h : Involutive f) : (h.toPerm f : α → α) = f :=
  rfl
#align function.involutive.coe_to_perm Function.Involutive.coe_to_perm

@[simp]
theorem to_perm_symm {f : α → α} (h : Involutive f) : (h.toPerm f).symm = h.toPerm f :=
  rfl
#align function.involutive.to_perm_symm Function.Involutive.to_perm_symm

theorem to_perm_involutive {f : α → α} (h : Involutive f) : Involutive (h.toPerm f) :=
  h
#align function.involutive.to_perm_involutive Function.Involutive.to_perm_involutive

end Function.Involutive

theorem PLift.eq_up_iff_down_eq {x : PLift α} {y : α} : x = PLift.up y ↔ x.down = y :=
  Equiv.plift.eq_symm_apply
#align plift.eq_up_iff_down_eq PLift.eq_up_iff_down_eq

theorem Function.Injective.map_swap {α β : Type _} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (x y z : α) : f (Equiv.swap x y z) = Equiv.swap (f x) (f y) (f z) := by
  conv_rhs => rw [Equiv.swap_apply_def]
  split_ifs with h₁ h₂
  · rw [hf h₁, Equiv.swap_apply_left]

  · rw [hf h₂, Equiv.swap_apply_right]

  · rw [Equiv.swap_apply_of_ne_of_ne (mt (congr_arg f) h₁) (mt (congr_arg f) h₂)]

#align function.injective.map_swap Function.Injective.map_swap

namespace Equiv

section

variable (P : α → Sort w) (e : α ≃ β)

/-- Transport dependent functions through an equivalence of the base space.
-/
@[simps]
def piCongrLeft' : (∀ a, P a) ≃ ∀ b, P (e.symm b) where
  toFun f x := f (e.symm x)
  invFun f x := by
    rw [← e.symm_apply_apply x]
    exact f (e x)
  left_inv f :=
    funext fun x =>
      eq_of_heq
        ((eq_rec_heq _ _).trans
          (by
            dsimp
            rw [e.symm_apply_apply]))
  right_inv f := funext fun x => eq_of_heq ((eq_rec_heq _ _).trans (by rw [e.apply_symm_apply]))
#align equiv.Pi_congr_left' Equiv.piCongrLeft'

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
theorem coe_Pi_congr_symm : ((h₁.piCongr h₂).symm : (∀ b, Z b) → ∀ a, W a) = fun f a => (h₂ a).symm (f (h₁ a)) :=
  rfl
#align equiv.coe_Pi_congr_symm Equiv.coe_Pi_congr_symm

theorem Pi_congr_symm_apply (f : ∀ b, Z b) : (h₁.piCongr h₂).symm f = fun a => (h₂ a).symm (f (h₁ a)) :=
  rfl
#align equiv.Pi_congr_symm_apply Equiv.Pi_congr_symm_apply

@[simp]
theorem Pi_congr_apply_apply (f : ∀ a, W a) (a : α) : h₁.piCongr h₂ f (h₁ a) = h₂ a (f a) := by
  change cast _ ((h₂ (h₁.symm (h₁ a))) (f (h₁.symm (h₁ a)))) = (h₂ a) (f a)
  generalize_proofs hZa
  revert hZa
  rw [h₁.symm_apply_apply a]
  simp
#align equiv.Pi_congr_apply_apply Equiv.Pi_congr_apply_apply

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
theorem coe_Pi_congr' : (h₁.piCongr' h₂ : (∀ a, W a) → ∀ b, Z b) = fun f b => h₂ b <| f <| h₁.symm b :=
  rfl
#align equiv.coe_Pi_congr' Equiv.coe_Pi_congr'

theorem Pi_congr'_apply (f : ∀ a, W a) : h₁.piCongr' h₂ f = fun b => h₂ b <| f <| h₁.symm b :=
  rfl
#align equiv.Pi_congr'_apply Equiv.Pi_congr'_apply

@[simp]
theorem Pi_congr'_symm_apply_symm_apply (f : ∀ b, Z b) (b : β) :
    (h₁.piCongr' h₂).symm f (h₁.symm b) = (h₂ b).symm (f b) := by
  change cast _ ((h₂ (h₁ (h₁.symm b))).symm (f (h₁ (h₁.symm b)))) = (h₂ b).symm (f b)
  generalize_proofs hWb
  revert hWb
  generalize hb : h₁ (h₁.symm b) = b'
  rw [h₁.apply_symm_apply b] at hb
  subst hb
  simp
#align equiv.Pi_congr'_symm_apply_symm_apply Equiv.Pi_congr'_symm_apply_symm_apply

end

section BinaryOp

variable {α₁ β₁ : Type _} (e : α₁ ≃ β₁) (f : α₁ → α₁ → α₁)

theorem semiconj_conj (f : α₁ → α₁) : Semiconj e f (e.conj f) := fun x => by simp
#align equiv.semiconj_conj Equiv.semiconj_conj

theorem semiconj₂_conj : Semiconj₂ e f (e.arrowCongr e.conj f) := fun x y => by simp
#align equiv.semiconj₂_conj Equiv.semiconj₂_conj

instance [IsAssociative α₁ f] : IsAssociative β₁ (e.arrowCongr (e.arrowCongr e) f) :=
  (e.semiconj₂_conj f).is_associative_right e.Surjective

instance [IsIdempotent α₁ f] : IsIdempotent β₁ (e.arrowCongr (e.arrowCongr e) f) :=
  (e.semiconj₂_conj f).is_idempotent_right e.Surjective

instance [IsLeftCancel α₁ f] : IsLeftCancel β₁ (e.arrowCongr (e.arrowCongr e) f) :=
  ⟨e.Surjective.forall₃.2 fun x y z => by simpa using @IsLeftCancel.left_cancel _ f _ x y z⟩

instance [IsRightCancel α₁ f] : IsRightCancel β₁ (e.arrowCongr (e.arrowCongr e) f) :=
  ⟨e.Surjective.forall₃.2 fun x y z => by simpa using @IsRightCancel.right_cancel _ f _ x y z⟩

end BinaryOp

end Equiv

theorem Function.Injective.swap_apply [DecidableEq α] [DecidableEq β] {f : α → β} (hf : Function.Injective f)
    (x y z : α) : Equiv.swap (f x) (f y) (f z) = f (Equiv.swap x y z) := by
  by_cases hx:z = x
  · simp [hx]

  by_cases hy:z = y
  · simp [hy]

  rw [Equiv.swap_apply_of_ne_of_ne hx hy, Equiv.swap_apply_of_ne_of_ne (hf.ne hx) (hf.ne hy)]
#align function.injective.swap_apply Function.Injective.swap_apply

theorem Function.Injective.swap_comp [DecidableEq α] [DecidableEq β] {f : α → β} (hf : Function.Injective f) (x y : α) :
    Equiv.swap (f x) (f y) ∘ f = f ∘ Equiv.swap x y :=
  funext fun z => hf.swap_apply _ _ _
#align function.injective.swap_comp Function.Injective.swap_comp

/-- If `α` is a subsingleton, then it is equivalent to `α × α`. -/
def subsingletonProdSelfEquiv {α : Type _} [Subsingleton α] : α × α ≃ α where
  toFun p := p.1
  invFun a := (a, a)
  left_inv p := Subsingleton.elim _ _
  right_inv p := Subsingleton.elim _ _
#align subsingleton_prod_self_equiv subsingletonProdSelfEquiv

/-- To give an equivalence between two subsingleton types, it is sufficient to give any two
    functions between them. -/
def equivOfSubsingletonOfSubsingleton [Subsingleton α] [Subsingleton β] (f : α → β) (g : β → α) : α ≃ β where
  toFun := f
  invFun := g
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align equiv_of_subsingleton_of_subsingleton equivOfSubsingletonOfSubsingleton

/-- A nonempty subsingleton type is (noncomputably) equivalent to `punit`. -/
noncomputable def Equiv.punitOfNonemptyOfSubsingleton {α : Sort _} [h : Nonempty α] [Subsingleton α] : α ≃ PUnit.{v} :=
  equivOfSubsingletonOfSubsingleton (fun _ => PUnit.unit) fun _ => h.some
#align equiv.punit_of_nonempty_of_subsingleton Equiv.punitOfNonemptyOfSubsingleton

/-- `unique (unique α)` is equivalent to `unique α`. -/
def uniqueUniqueEquiv : Unique (Unique α) ≃ Unique α :=
  equivOfSubsingletonOfSubsingleton (fun h => h.default) fun h =>
    { default := h, uniq := fun _ => Subsingleton.elim _ _ }
#align unique_unique_equiv uniqueUniqueEquiv

namespace Function

theorem update_comp_equiv {α β α' : Sort _} [DecidableEq α'] [DecidableEq α] (f : α → β) (g : α' ≃ α) (a : α) (v : β) :
    update f a v ∘ g = update (f ∘ g) (g.symm a) v := by
  rw [← update_comp_eq_of_injective _ g.injective, g.apply_symm_apply]
#align function.update_comp_equiv Function.update_comp_equiv

theorem update_apply_equiv_apply {α β α' : Sort _} [DecidableEq α'] [DecidableEq α] (f : α → β) (g : α' ≃ α) (a : α)
    (v : β) (a' : α') : update f a v (g a') = update (f ∘ g) (g.symm a) v a' :=
  congr_fun (update_comp_equiv f g a v) a'
#align function.update_apply_equiv_apply Function.update_apply_equiv_apply

theorem Pi_congr_left'_update [DecidableEq α] [DecidableEq β] (P : α → Sort _) (e : α ≃ β) (f : ∀ a, P a) (b : β)
    (x : P (e.symm b)) : e.piCongrLeft' P (update f (e.symm b) x) = update (e.piCongrLeft' P f) b x := by
  ext b'
  rcases eq_or_ne b' b with (rfl | h)
  · simp

  · simp [h]

#align function.Pi_congr_left'_update Function.Pi_congr_left'_update

theorem Pi_congr_left'_symm_update [DecidableEq α] [DecidableEq β] (P : α → Sort _) (e : α ≃ β) (f : ∀ b, P (e.symm b))
    (b : β) (x : P (e.symm b)) :
    (e.piCongrLeft' P).symm (update f b x) = update ((e.piCongrLeft' P).symm f) (e.symm b) x := by
  simp [(e.Pi_congr_left' P).symm_apply_eq, Pi_congr_left'_update]
#align function.Pi_congr_left'_symm_update Function.Pi_congr_left'_symm_update

end Function
