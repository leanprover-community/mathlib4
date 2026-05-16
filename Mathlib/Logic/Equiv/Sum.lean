/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Data.Option.Defs
public import Mathlib.Data.Sigma.Basic
public import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Coe
import Mathlib.Tactic.SplitIfs

/-!
# Equivalence between sum types

In this file we continue the work on equivalences begun in `Mathlib/Logic/Equiv/Defs.lean`, defining

* canonical isomorphisms between various types: e.g.,

  - `Equiv.sumEquivSigmaBool` is the canonical equivalence between the sum of two types `α ⊕ β`
    and the sigma-type `Σ b, bif b then β else α`;

  - `Equiv.prodSumDistrib : α × (β ⊕ γ) ≃ (α × β) ⊕ (α × γ)` shows that type product and type sum
    satisfy the distributive law up to a canonical equivalence;

More definitions of this kind can be found in other files.
E.g., `Mathlib/Algebra/Group/TransferInstance.lean` does it for `Group`,
`Mathlib/Algebra/Module/TransferInstance.lean` does it for `Module`, and similar files exist for
other algebraic type classes.

## Tags

equivalence, congruence, bijective map
-/

@[expose] public section

universe u v w z

open Function

-- Unless required to be `Type*`, all variables in this file are `Sort*`
variable {α α₁ α₂ β β₁ β₂ γ δ : Sort*}

namespace Equiv

section

open Sum

/-- `PSum` is equivalent to `Sum`. -/
def psumEquivSum (α β) : α ⊕' β ≃ α ⊕ β where
  toFun s := PSum.casesOn s inl inr
  invFun := Sum.elim PSum.inl PSum.inr
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl

/-- If `α ≃ α'` and `β ≃ β'`, then `α ⊕ β ≃ α' ⊕ β'`. This is `Sum.map` as an equivalence. -/
@[simps (attr := grind =) apply]
def sumCongr {α₁ α₂ β₁ β₂} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂ :=
  ⟨Sum.map ea eb, Sum.map ea.symm eb.symm, fun x => by simp, fun x => by simp⟩

@[simp, grind =]
theorem sumCongr_trans {α₁ α₂ β₁ β₂ γ₁ γ₂} (e : α₁ ≃ β₁) (f : α₂ ≃ β₂) (g : β₁ ≃ γ₁) (h : β₂ ≃ γ₂) :
    (Equiv.sumCongr e f).trans (Equiv.sumCongr g h) = Equiv.sumCongr (e.trans g) (f.trans h) := by
  ext i
  cases i <;> rfl

@[simp]
theorem sumCongr_symm {α β γ δ} (e : α ≃ β) (f : γ ≃ δ) :
    (Equiv.sumCongr e f).symm = Equiv.sumCongr e.symm f.symm :=
  rfl

@[simp]
theorem sumCongr_refl {α β} :
    Equiv.sumCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α ⊕ β) := by
  ext i
  cases i <;> rfl

/-- If `α ≃ α'` and `β ≃ β'`, then `α ⊕' β ≃ α' ⊕' β'`. -/
def psumCongr (e₁ : α ≃ β) (e₂ : γ ≃ δ) : α ⊕' γ ≃ β ⊕' δ where
  toFun x := PSum.casesOn x (PSum.inl ∘ e₁) (PSum.inr ∘ e₂)
  invFun x := PSum.casesOn x (PSum.inl ∘ e₁.symm) (PSum.inr ∘ e₂.symm)
  left_inv := by rintro (x | x) <;> simp
  right_inv := by rintro (x | x) <;> simp

/-- Combine two `Equiv`s using `PSum` in the domain and `Sum` in the codomain. -/
def psumSum {α₂ β₂} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) :
    α₁ ⊕' β₁ ≃ α₂ ⊕ β₂ :=
  (ea.psumCongr eb).trans (psumEquivSum _ _)

/-- Combine two `Equiv`s using `Sum` in the domain and `PSum` in the codomain. -/
def sumPSum {α₁ β₁} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) :
    α₁ ⊕ β₁ ≃ α₂ ⊕' β₂ :=
  (ea.symm.psumSum eb.symm).symm

/-- A subtype of a sum is equivalent to a sum of subtypes. -/
def subtypeSum {α β} {p : α ⊕ β → Prop} :
    {c // p c} ≃ {a // p (Sum.inl a)} ⊕ {b // p (Sum.inr b)} where
  toFun
    | ⟨.inl a, h⟩ => .inl ⟨a, h⟩
    | ⟨.inr b, h⟩ => .inr ⟨b, h⟩
  invFun
    | .inl a => ⟨.inl a, a.2⟩
    | .inr b => ⟨.inr b, b.2⟩
  left_inv := by rintro ⟨a | b, h⟩ <;> rfl
  right_inv := by rintro (a | b) <;> rfl

namespace Perm

/-- Combine a permutation of `α` and of `β` into a permutation of `α ⊕ β`. -/
abbrev sumCongr {α β} (ea : Equiv.Perm α) (eb : Equiv.Perm β) : Equiv.Perm (α ⊕ β) :=
  Equiv.sumCongr ea eb

@[simp]
theorem sumCongr_apply {α β} (ea : Equiv.Perm α) (eb : Equiv.Perm β) (x : α ⊕ β) :
    sumCongr ea eb x = Sum.map (⇑ea) (⇑eb) x := rfl

theorem sumCongr_trans {α β} (e : Equiv.Perm α) (f : Equiv.Perm β) (g : Equiv.Perm α)
    (h : Equiv.Perm β) : (sumCongr e f).trans (sumCongr g h) = sumCongr (e.trans g) (f.trans h) :=
  Equiv.sumCongr_trans e f g h

theorem sumCongr_symm {α β} (e : Equiv.Perm α) (f : Equiv.Perm β) :
    (sumCongr e f).symm = sumCongr e.symm f.symm :=
  Equiv.sumCongr_symm e f

theorem sumCongr_refl {α β} : sumCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α ⊕ β) :=
  Equiv.sumCongr_refl

end Perm

/-- `Bool` is equivalent the sum of two `PUnit`s. -/
def boolEquivPUnitSumPUnit : Bool ≃ PUnit.{u + 1} ⊕ PUnit.{v + 1} :=
  ⟨fun b => b.casesOn (inl PUnit.unit) (inr PUnit.unit), Sum.elim (fun _ => false) fun _ => true,
    fun b => by cases b <;> rfl, fun s => by rcases s with (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> rfl⟩

/-- Sum of types is commutative up to an equivalence. This is `Sum.swap` as an equivalence. -/
@[simps -fullyApplied apply]
def sumComm (α β) : α ⊕ β ≃ β ⊕ α :=
  ⟨Sum.swap, Sum.swap, Sum.swap_swap, Sum.swap_swap⟩

@[simp]
theorem sumComm_symm (α β) : (sumComm α β).symm = sumComm β α :=
  rfl

/-- Sum of types is associative up to an equivalence. -/
def sumAssoc (α β γ) : (α ⊕ β) ⊕ γ ≃ α ⊕ (β ⊕ γ) :=
  ⟨Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr),
    Sum.elim (Sum.inl ∘ Sum.inl) <| Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr,
      by rintro (⟨_ | _⟩ | _) <;> rfl, by
    rintro (_ | ⟨_ | _⟩) <;> rfl⟩

@[simp]
theorem sumAssoc_apply_inl_inl {α β γ} (a) : sumAssoc α β γ (inl (inl a)) = inl a :=
  rfl

@[simp]
theorem sumAssoc_apply_inl_inr {α β γ} (b) : sumAssoc α β γ (inl (inr b)) = inr (inl b) :=
  rfl

@[simp]
theorem sumAssoc_apply_inr {α β γ} (c) : sumAssoc α β γ (inr c) = inr (inr c) :=
  rfl

@[simp]
theorem sumAssoc_symm_apply_inl {α β γ} (a) : (sumAssoc α β γ).symm (inl a) = inl (inl a) :=
  rfl

@[simp]
theorem sumAssoc_symm_apply_inr_inl {α β γ} (b) :
    (sumAssoc α β γ).symm (inr (inl b)) = inl (inr b) :=
  rfl

@[simp]
theorem sumAssoc_symm_apply_inr_inr {α β γ} (c) : (sumAssoc α β γ).symm (inr (inr c)) = inr c :=
  rfl

/-- Four-way commutativity of `sum`. The name matches `add_add_add_comm`. -/
@[simps apply]
def sumSumSumComm (α β γ δ) : (α ⊕ β) ⊕ γ ⊕ δ ≃ (α ⊕ γ) ⊕ β ⊕ δ where
  toFun :=
    (sumAssoc (α ⊕ γ) β δ) ∘ (Sum.map (sumAssoc α γ β).symm (@id δ))
      ∘ (Sum.map (Sum.map (@id α) (sumComm β γ)) (@id δ))
      ∘ (Sum.map (sumAssoc α β γ) (@id δ))
      ∘ (sumAssoc (α ⊕ β) γ δ).symm
  invFun :=
    (sumAssoc (α ⊕ β) γ δ) ∘ (Sum.map (sumAssoc α β γ).symm (@id δ))
      ∘ (Sum.map (Sum.map (@id α) (sumComm β γ).symm) (@id δ))
      ∘ (Sum.map (sumAssoc α γ β) (@id δ))
      ∘ (sumAssoc (α ⊕ γ) β δ).symm
  left_inv x := by rcases x with ((a | b) | (c | d)) <;> simp
  right_inv x := by rcases x with ((a | c) | (b | d)) <;> simp

@[simp]
theorem sumSumSumComm_symm (α β γ δ) : (sumSumSumComm α β γ δ).symm = sumSumSumComm α γ β δ :=
  rfl

/-- Sum with `IsEmpty` is equivalent to the original type. -/
@[simps symm_apply]
def sumEmpty (α β) [IsEmpty β] : α ⊕ β ≃ α where
  toFun := Sum.elim id isEmptyElim
  invFun := inl
  left_inv s := by
    rcases s with (_ | x)
    · rfl
    · exact isEmptyElim x

@[simp]
theorem sumEmpty_apply_inl {α β} [IsEmpty β] (a : α) : sumEmpty α β (Sum.inl a) = a :=
  rfl

/-- The sum of `IsEmpty` with any type is equivalent to that type. -/
@[simps! symm_apply]
def emptySum (α β) [IsEmpty α] : α ⊕ β ≃ β :=
  (sumComm _ _).trans <| sumEmpty _ _

@[simp]
theorem emptySum_apply_inr {α β} [IsEmpty α] (b : β) : emptySum α β (Sum.inr b) = b :=
  rfl

/-- `α ⊕ β` is equivalent to a `Sigma`-type over `Bool`. Note that this definition assumes `α` and
`β` to be types from the same universe, so it cannot be used directly to transfer theorems about
sigma types to theorems about sum types. In many cases one can use `ULift` to work around this
difficulty. -/
def sumEquivSigmaBool (α β) : α ⊕ β ≃ Σ b, bif b then β else α :=
  ⟨fun s => s.elim (fun x => ⟨false, x⟩) fun x => ⟨true, x⟩, fun s =>
    match s with
    | ⟨false, a⟩ => inl a
    | ⟨true, b⟩ => inr b,
    fun s => by cases s <;> rfl, fun s => by rcases s with ⟨_ | _, _⟩ <;> rfl⟩

-- See also `Equiv.sigmaPreimageEquiv`.
/-- `sigmaFiberEquiv f` for `f : α → β` is the natural equivalence between
the type of all fibres of `f` and the total space `α`. -/
@[simps]
def sigmaFiberEquiv {α β : Type*} (f : α → β) : (Σ y : β, { x // f x = y }) ≃ α :=
  ⟨fun x => ↑x.2, fun x => ⟨f x, x, rfl⟩, fun ⟨_, _, rfl⟩ => rfl, fun _ => rfl⟩

/-- Inhabited types are equivalent to `Option β` for some `β` by identifying `default` with `none`.
-/
def sigmaEquivOptionOfInhabited (α : Type u) [Inhabited α] [DecidableEq α] :
    Σ β : Type u, α ≃ Option β where
  fst := {a // a ≠ default}
  snd.toFun a := if h : a = default then none else some ⟨a, h⟩
  snd.invFun := Option.elim' default (↑)
  snd.left_inv a := by dsimp only; split_ifs <;> simp [*]
  snd.right_inv
    | none => by simp
    | some ⟨_, ha⟩ => dif_neg ha

end

section sumCompl

/-- For any predicate `p` on `α`,
the sum of the two subtypes `{a // p a}` and its complement `{a // ¬ p a}`
is naturally equivalent to `α`.

See `subtypeOrEquiv` for sum types over subtypes `{x // p x}` and `{x // q x}`
that are not necessarily `IsCompl p q`. See also `Equiv.Set.sumCompl` for a version on sets. -/
def sumCompl {α : Type*} (p : α → Prop) [DecidablePred p] :
    { a // p a } ⊕ { a // ¬p a } ≃ α where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun a := if h : p a then Sum.inl ⟨a, h⟩ else Sum.inr ⟨a, h⟩
  left_inv := by
    rintro (⟨x, hx⟩ | ⟨x, hx⟩) <;> dsimp
    · rw [dif_pos]
    · rw [dif_neg]
  right_inv a := by
    dsimp
    split_ifs <;> rfl

@[simp]
theorem sumCompl_apply_inl {α} {p : α → Prop} [DecidablePred p] (x : { a // p a }) :
    sumCompl p (Sum.inl x) = x :=
  rfl

@[simp]
theorem sumCompl_apply_inr {α} {p : α → Prop} [DecidablePred p] (x : { a // ¬p a }) :
    sumCompl p (Sum.inr x) = x :=
  rfl

@[simp]
theorem sumCompl_symm_apply_of_pos {α} {p : α → Prop} [DecidablePred p] {a : α} (h : p a) :
    (sumCompl p).symm a = Sum.inl ⟨a, h⟩ :=
  dif_pos h

@[simp]
theorem sumCompl_symm_apply_of_neg {α} {p : α → Prop} [DecidablePred p] {a : α} (h : ¬p a) :
    (sumCompl p).symm a = Sum.inr ⟨a, h⟩ :=
  dif_neg h

@[deprecated (since := "2025-10-28")]
alias sumCompl_apply_symm_of_pos := sumCompl_symm_apply_of_pos
@[deprecated (since := "2025-10-28")]
alias sumCompl_apply_symm_of_neg := sumCompl_symm_apply_of_neg

@[simp]
theorem sumCompl_symm_apply_pos {α} {p : α → Prop} [DecidablePred p] (x : {x // p x}) :
    (sumCompl p).symm x = Sum.inl x :=
  sumCompl_symm_apply_of_pos x.2

@[simp]
theorem sumCompl_symm_apply_neg {α} {p : α → Prop} [DecidablePred p] (x : {x // ¬ p x}) :
    (sumCompl p).symm x = Sum.inr x :=
  sumCompl_symm_apply_of_neg x.2

end sumCompl

section

open Sum

/-- Type product is left distributive with respect to type sum up to an equivalence. -/
def prodSumDistrib (α β γ) : α × (β ⊕ γ) ≃ (α × β) ⊕ (α × γ) :=
  calc
    α × (β ⊕ γ) ≃ (β ⊕ γ) × α := prodComm _ _
    _ ≃ (β × α) ⊕ (γ × α) := sumProdDistrib _ _ _
    _ ≃ (α × β) ⊕ (α × γ) := sumCongr (prodComm _ _) (prodComm _ _)

@[simp]
theorem prodSumDistrib_apply_left {α β γ} (a : α) (b : β) :
    prodSumDistrib α β γ (a, Sum.inl b) = Sum.inl (a, b) :=
  rfl

@[simp]
theorem prodSumDistrib_apply_right {α β γ} (a : α) (c : γ) :
    prodSumDistrib α β γ (a, Sum.inr c) = Sum.inr (a, c) :=
  rfl

@[simp]
theorem prodSumDistrib_symm_apply_left {α β γ} (a : α × β) :
    (prodSumDistrib α β γ).symm (inl a) = (a.1, inl a.2) :=
  rfl

@[simp]
theorem prodSumDistrib_symm_apply_right {α β γ} (a : α × γ) :
    (prodSumDistrib α β γ).symm (inr a) = (a.1, inr a.2) :=
  rfl

/-- An indexed sum of disjoint sums of types is equivalent to the sum of the indexed sums. Compare
with `Equiv.sumSigmaDistrib` which is indexed by sums. -/
@[simps]
def sigmaSumDistrib {ι} (α β : ι → Type*) :
    (Σ i, α i ⊕ β i) ≃ (Σ i, α i) ⊕ (Σ i, β i) :=
  ⟨fun p => p.2.map (Sigma.mk p.1) (Sigma.mk p.1),
    Sum.elim (Sigma.map id fun _ => Sum.inl) (Sigma.map id fun _ => Sum.inr), fun p => by
    rcases p with ⟨i, a | b⟩ <;> rfl, fun p => by rcases p with (⟨i, a⟩ | ⟨i, b⟩) <;> rfl⟩

/-- A type indexed by disjoint sums of types is equivalent to the sum of the sums. Compare with
`Equiv.sigmaSumDistrib` which has the sums as the output type. -/
@[simps]
def sumSigmaDistrib {α β} (t : α ⊕ β → Type*) :
    (Σ i, t i) ≃ (Σ i, t (.inl i)) ⊕ (Σ i, t (.inr i)) :=
  ⟨(match · with
    | .mk (.inl x) y => .inl ⟨x, y⟩
    | .mk (.inr x) y => .inr ⟨x, y⟩),
  Sum.elim (fun a ↦ ⟨.inl a.1, a.2⟩) (fun b ↦ ⟨.inr b.1, b.2⟩),
  by rintro ⟨x|x,y⟩ <;> simp,
  by rintro (⟨x,y⟩|⟨x,y⟩) <;> simp⟩

end

end Equiv
