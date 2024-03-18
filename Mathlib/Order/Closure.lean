/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Yaël Dillies
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Data.SetLike.Basic
import Mathlib.Order.GaloisConnection
import Mathlib.Order.Hom.Basic

#align_import order.closure from "leanprover-community/mathlib"@"f252872231e87a5db80d9938fc05530e70f23a94"

/-!
# Closure operators between preorders

We define (bundled) closure operators on a preorder as monotone (increasing), extensive
(inflationary) and idempotent functions.
We define closed elements for the operator as elements which are fixed by it.

Lower adjoints to a function between preorders `u : β → α` allow to generalise closure operators to
situations where the closure operator we are dealing with naturally decomposes as `u ∘ l` where `l`
is a worthy function to have on its own. Typical examples include
`l : Set G → Subgroup G := Subgroup.closure`, `u : Subgroup G → Set G := (↑)`, where `G` is a group.
This shows there is a close connection between closure operators, lower adjoints and Galois
connections/insertions: every Galois connection induces a lower adjoint which itself induces a
closure operator by composition (see `GaloisConnection.lowerAdjoint` and
`LowerAdjoint.closureOperator`), and every closure operator on a partial order induces a Galois
insertion from the set of closed elements to the underlying type (see `ClosureOperator.gi`).

## Main definitions

* `ClosureOperator`: A closure operator is a monotone function `f : α → α` such that
  `∀ x, x ≤ f x` and `∀ x, f (f x) = f x`.
* `LowerAdjoint`: A lower adjoint to `u : β → α` is a function `l : α → β` such that `l` and `u`
  form a Galois connection.

## Implementation details

Although `LowerAdjoint` is technically a generalisation of `ClosureOperator` (by defining
`toFun := id`), it is desirable to have both as otherwise `id`s would be carried all over the
place when using concrete closure operators such as `ConvexHull`.

`LowerAdjoint` really is a semibundled `structure` version of `GaloisConnection`.

## References

* https://en.wikipedia.org/wiki/Closure_operator#Closure_operators_on_partially_ordered_sets
-/

open Set

/-! ### Closure operator -/


variable (α : Type*) {ι : Sort*} {κ : ι → Sort*}

/-- A closure operator on the preorder `α` is a monotone function which is extensive (every `x`
is less than its closure) and idempotent. -/
structure ClosureOperator [Preorder α] extends α →o α where
  /-- An element is less than or equal its closure -/
  le_closure' : ∀ x, x ≤ toFun x
  /-- Closures are idempotent -/
  idempotent' : ∀ x, toFun (toFun x) = toFun x
  /-- Predicate for an element to be closed.

  By default, this is defined as `c.IsClosed x := (c x = x)` (see `isClosed_iff`).
  We allow an override to fix definitional equalities. -/
  IsClosed (x : α) : Prop := toFun x = x
  isClosed_iff {x : α} : IsClosed x ↔ toFun x = x := by aesop
#align closure_operator ClosureOperator

namespace ClosureOperator

instance [Preorder α] : FunLike (ClosureOperator α) α α where
  coe c := c.1
  coe_injective' := by rintro ⟨⟩ ⟨⟩ h; obtain rfl := DFunLike.ext' h; congr with x; simp_all

instance [Preorder α] : OrderHomClass (ClosureOperator α) α α where
  map_rel f _ _ h := f.mono h

initialize_simps_projections ClosureOperator (toFun → apply, IsClosed → isClosed)

section PartialOrder

variable [PartialOrder α]

/-- The identity function as a closure operator. -/
@[simps!]
def id : ClosureOperator α where
  toOrderHom := OrderHom.id
  le_closure' _ := le_rfl
  idempotent' _ := rfl
  IsClosed _ := True
#align closure_operator.id ClosureOperator.id
#align closure_operator.id_apply ClosureOperator.id_apply
#align closure_operator.closed ClosureOperator.IsClosed
#align closure_operator.mem_closed_iff ClosureOperator.isClosed_iff

instance : Inhabited (ClosureOperator α) :=
  ⟨id α⟩

variable {α} [PartialOrder α] (c : ClosureOperator α)

@[ext]
theorem ext : ∀ c₁ c₂ : ClosureOperator α, (c₁ : α → α) = (c₂ : α → α) → c₁ = c₂ :=
  DFunLike.coe_injective
#align closure_operator.ext ClosureOperator.ext

/-- Constructor for a closure operator using the weaker idempotency axiom: `f (f x) ≤ f x`. -/
@[simps]
def mk' (f : α → α) (hf₁ : Monotone f) (hf₂ : ∀ x, x ≤ f x) (hf₃ : ∀ x, f (f x) ≤ f x) :
    ClosureOperator α where
  toFun := f
  monotone' := hf₁
  le_closure' := hf₂
  idempotent' x := (hf₃ x).antisymm (hf₁ (hf₂ x))
#align closure_operator.mk' ClosureOperator.mk'
#align closure_operator.mk'_apply ClosureOperator.mk'_apply

/-- Convenience constructor for a closure operator using the weaker minimality axiom:
`x ≤ f y → f x ≤ f y`, which is sometimes easier to prove in practice. -/
@[simps]
def mk₂ (f : α → α) (hf : ∀ x, x ≤ f x) (hmin : ∀ ⦃x y⦄, x ≤ f y → f x ≤ f y) : ClosureOperator α
    where
  toFun := f
  monotone' _ y hxy := hmin (hxy.trans (hf y))
  le_closure' := hf
  idempotent' _ := (hmin le_rfl).antisymm (hf _)
#align closure_operator.mk₂ ClosureOperator.mk₂
#align closure_operator.mk₂_apply ClosureOperator.mk₂_apply

/-- Construct a closure operator from an inflationary function `f` and a "closedness" predicate `p`
witnessing minimality of `f x` among closed elements greater than `x`. -/
@[simps!]
def ofPred (f : α → α) (p : α → Prop) (hf : ∀ x, x ≤ f x) (hfp : ∀ x, p (f x))
    (hmin : ∀ ⦃x y⦄, x ≤ y → p y → f x ≤ y) : ClosureOperator α where
  __ := mk₂ f hf fun _ y hxy => hmin hxy (hfp y)
  IsClosed := p
  isClosed_iff := ⟨fun hx ↦ (hmin le_rfl hx).antisymm <| hf _, fun hx ↦ hx ▸ hfp _⟩
#align closure_operator.mk₃ ClosureOperator.ofPred
#align closure_operator.mk₃_apply ClosureOperator.ofPred_apply
#align closure_operator.mem_mk₃_closed ClosureOperator.ofPred_isClosed

#noalign closure_operator.closure_mem_ofPred
#noalign closure_operator.closure_le_ofPred_iff

@[mono]
theorem monotone : Monotone c :=
  c.monotone'
#align closure_operator.monotone ClosureOperator.monotone

/-- Every element is less than its closure. This property is sometimes referred to as extensivity or
inflationarity. -/
theorem le_closure (x : α) : x ≤ c x :=
  c.le_closure' x
#align closure_operator.le_closure ClosureOperator.le_closure

@[simp]
theorem idempotent (x : α) : c (c x) = c x :=
  c.idempotent' x
#align closure_operator.idempotent ClosureOperator.idempotent

@[simp] lemma isClosed_closure (x : α) : c.IsClosed (c x) := c.isClosed_iff.2 <| c.idempotent x
#align closure_operator.closure_is_closed ClosureOperator.isClosed_closure

/-- The type of elements closed under a closure operator. -/
abbrev Closeds := {x // c.IsClosed x}

/-- Send an element to a closed element (by taking the closure). -/
def toCloseds (x : α) : c.Closeds := ⟨c x, c.isClosed_closure x⟩
#align closure_operator.to_closed ClosureOperator.toCloseds

variable {c} {x y : α}

theorem IsClosed.closure_eq : c.IsClosed x → c x = x := c.isClosed_iff.1
#align closure_operator.closure_eq_self_of_mem_closed ClosureOperator.IsClosed.closure_eq

theorem isClosed_iff_closure_le : c.IsClosed x ↔ c x ≤ x :=
  ⟨fun h ↦ h.closure_eq.le, fun h ↦ c.isClosed_iff.2 <| h.antisymm <| c.le_closure x⟩
#align closure_operator.mem_closed_iff_closure_le ClosureOperator.isClosed_iff_closure_le

/-- The set of closed elements for `c` is exactly its range. -/
theorem setOf_isClosed_eq_range_closure : {x | c.IsClosed x} = Set.range c := by
  ext x; exact ⟨fun hx ↦ ⟨x, hx.closure_eq⟩, by rintro ⟨y, rfl⟩; exact c.isClosed_closure _⟩
#align closure_operator.closed_eq_range_close ClosureOperator.setOf_isClosed_eq_range_closure

theorem le_closure_iff : x ≤ c y ↔ c x ≤ c y :=
  ⟨fun h ↦ c.idempotent y ▸ c.monotone h, (c.le_closure x).trans⟩
#align closure_operator.le_closure_iff ClosureOperator.le_closure_iff

@[simp]
theorem IsClosed.closure_le_iff (hy : c.IsClosed y) : c x ≤ y ↔ x ≤ y := by
  rw [← hy.closure_eq, ← le_closure_iff]
#align closure_operator.closure_le_closed_iff_le ClosureOperator.IsClosed.closure_le_iff

lemma closure_min (hxy : x ≤ y) (hy : c.IsClosed y) : c x ≤ y := hy.closure_le_iff.2 hxy

/-- A closure operator is equal to the closure operator obtained by feeding `c.closed` into the
`ofPred` constructor. -/
theorem eq_ofPred_closed (c : ClosureOperator α) :
    c = ofPred c c.IsClosed c.le_closure c.isClosed_closure fun x y ↦ closure_min := by
  ext
  rfl
#align closure_operator.eq_mk₃_closed ClosureOperator.eq_ofPred_closed

end PartialOrder

variable {α}

section OrderTop

variable [PartialOrder α] [OrderTop α] (c : ClosureOperator α)

@[simp]
theorem closure_top : c ⊤ = ⊤ :=
  le_top.antisymm (c.le_closure _)
#align closure_operator.closure_top ClosureOperator.closure_top

@[simp] lemma isClosed_top : c.IsClosed ⊤ := c.isClosed_iff.2 c.closure_top
#align closure_operator.top_mem_closed ClosureOperator.isClosed_top

end OrderTop

theorem closure_inf_le [SemilatticeInf α] (c : ClosureOperator α) (x y : α) :
    c (x ⊓ y) ≤ c x ⊓ c y :=
  c.monotone.map_inf_le _ _
#align closure_operator.closure_inf_le ClosureOperator.closure_inf_le

section SemilatticeSup

variable [SemilatticeSup α] (c : ClosureOperator α)

theorem closure_sup_closure_le (x y : α) : c x ⊔ c y ≤ c (x ⊔ y) :=
  c.monotone.le_map_sup _ _
#align closure_operator.closure_sup_closure_le ClosureOperator.closure_sup_closure_le

theorem closure_sup_closure_left (x y : α) : c (c x ⊔ y) = c (x ⊔ y) :=
  (le_closure_iff.1
        (sup_le (c.monotone le_sup_left) (le_sup_right.trans (c.le_closure _)))).antisymm
    (c.monotone (sup_le_sup_right (c.le_closure _) _))
#align closure_operator.closure_sup_closure_left ClosureOperator.closure_sup_closure_left

theorem closure_sup_closure_right (x y : α) : c (x ⊔ c y) = c (x ⊔ y) := by
  rw [sup_comm, closure_sup_closure_left, sup_comm (a := x)]
#align closure_operator.closure_sup_closure_right ClosureOperator.closure_sup_closure_right

theorem closure_sup_closure (x y : α) : c (c x ⊔ c y) = c (x ⊔ y) := by
  rw [closure_sup_closure_left, closure_sup_closure_right]
#align closure_operator.closure_sup_closure ClosureOperator.closure_sup_closure

end SemilatticeSup

section CompleteLattice

variable [CompleteLattice α] (c : ClosureOperator α) {p : α → Prop}

/-- Define a closure operator from a predicate that's preserved under infima. -/
@[simps!]
def ofCompletePred (p : α → Prop) (hsinf : ∀ s, (∀ a ∈ s, p a) → p (sInf s)) : ClosureOperator α :=
  ofPred (fun a ↦ ⨅ b : {b // a ≤ b ∧ p b}, b) p
    (fun a ↦ by set_option tactic.skipAssignedInstances false in simp [forall_swap])
    (fun a ↦ hsinf _ <| forall_mem_range.2 fun b ↦ b.2.2)
    (fun a b hab hb ↦ iInf_le_of_le ⟨b, hab, hb⟩ le_rfl)

@[simp]
theorem closure_iSup_closure (f : ι → α) : c (⨆ i, c (f i)) = c (⨆ i, f i) :=
  le_antisymm (le_closure_iff.1 <| iSup_le fun i => c.monotone <| le_iSup f i) <|
    c.monotone <| iSup_mono fun _ => c.le_closure _
#align closure_operator.closure_supr_closure ClosureOperator.closure_iSup_closure

@[simp]
theorem closure_iSup₂_closure (f : ∀ i, κ i → α) :
    c (⨆ (i) (j), c (f i j)) = c (⨆ (i) (j), f i j) :=
  le_antisymm (le_closure_iff.1 <| iSup₂_le fun i j => c.monotone <| le_iSup₂ i j) <|
    c.monotone <| iSup₂_mono fun _ _ => c.le_closure _
#align closure_operator.closure_supr₂_closure ClosureOperator.closure_iSup₂_closure

end CompleteLattice

end ClosureOperator

/-! ### Lower adjoint -/


variable {α} {β : Type*}

/-- A lower adjoint of `u` on the preorder `α` is a function `l` such that `l` and `u` form a Galois
connection. It allows us to define closure operators whose output does not match the input. In
practice, `u` is often `(↑) : β → α`. -/
structure LowerAdjoint [Preorder α] [Preorder β] (u : β → α) where
  /-- The underlying function -/
  toFun : α → β
  /-- The underlying function is a lower adjoint. -/
  gc' : GaloisConnection toFun u
#align lower_adjoint LowerAdjoint

namespace LowerAdjoint

variable (α)

/-- The identity function as a lower adjoint to itself. -/
@[simps]
protected def id [Preorder α] : LowerAdjoint (id : α → α) where
  toFun x := x
  gc' := GaloisConnection.id
#align lower_adjoint.id LowerAdjoint.id
#align lower_adjoint.id_to_fun LowerAdjoint.id_toFun

variable {α}

instance [Preorder α] : Inhabited (LowerAdjoint (id : α → α)) :=
  ⟨LowerAdjoint.id α⟩

section Preorder

variable [Preorder α] [Preorder β] {u : β → α} (l : LowerAdjoint u)

instance : CoeFun (LowerAdjoint u) fun _ => α → β where coe := toFun

theorem gc : GaloisConnection l u :=
  l.gc'
#align lower_adjoint.gc LowerAdjoint.gc

@[ext]
theorem ext : ∀ l₁ l₂ : LowerAdjoint u, (l₁ : α → β) = (l₂ : α → β) → l₁ = l₂
  | ⟨l₁, _⟩, ⟨l₂, _⟩, h => by
    congr
#align lower_adjoint.ext LowerAdjoint.ext

@[mono]
theorem monotone : Monotone (u ∘ l) :=
  l.gc.monotone_u.comp l.gc.monotone_l
#align lower_adjoint.monotone LowerAdjoint.monotone

/-- Every element is less than its closure. This property is sometimes referred to as extensivity or
inflationarity. -/
theorem le_closure (x : α) : x ≤ u (l x) :=
  l.gc.le_u_l _
#align lower_adjoint.le_closure LowerAdjoint.le_closure

end Preorder

section PartialOrder

variable [PartialOrder α] [Preorder β] {u : β → α} (l : LowerAdjoint u)

/-- Every lower adjoint induces a closure operator given by the composition. This is the partial
order version of the statement that every adjunction induces a monad. -/
@[simps]
def closureOperator : ClosureOperator α where
  toFun x := u (l x)
  monotone' := l.monotone
  le_closure' := l.le_closure
  idempotent' x := l.gc.u_l_u_eq_u (l x)
#align lower_adjoint.closure_operator LowerAdjoint.closureOperator
#align lower_adjoint.closure_operator_apply LowerAdjoint.closureOperator_apply

theorem idempotent (x : α) : u (l (u (l x))) = u (l x) :=
  l.closureOperator.idempotent _
#align lower_adjoint.idempotent LowerAdjoint.idempotent

theorem le_closure_iff (x y : α) : x ≤ u (l y) ↔ u (l x) ≤ u (l y) :=
  l.closureOperator.le_closure_iff
#align lower_adjoint.le_closure_iff LowerAdjoint.le_closure_iff

end PartialOrder

section Preorder

variable [Preorder α] [Preorder β] {u : β → α} (l : LowerAdjoint u)

/-- An element `x` is closed for `l : LowerAdjoint u` if it is a fixed point: `u (l x) = x` -/
def closed : Set α := {x | u (l x) = x}
#align lower_adjoint.closed LowerAdjoint.closed

theorem mem_closed_iff (x : α) : x ∈ l.closed ↔ u (l x) = x :=
  Iff.rfl
#align lower_adjoint.mem_closed_iff LowerAdjoint.mem_closed_iff

theorem closure_eq_self_of_mem_closed {x : α} (h : x ∈ l.closed) : u (l x) = x :=
  h
#align lower_adjoint.closure_eq_self_of_mem_closed LowerAdjoint.closure_eq_self_of_mem_closed

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β] {u : β → α} (l : LowerAdjoint u)

theorem mem_closed_iff_closure_le (x : α) : x ∈ l.closed ↔ u (l x) ≤ x :=
  l.closureOperator.isClosed_iff_closure_le
#align lower_adjoint.mem_closed_iff_closure_le LowerAdjoint.mem_closed_iff_closure_le

@[simp, nolint simpNF] -- Porting note: lemma does prove itself, seems to be a linter error
theorem closure_is_closed (x : α) : u (l x) ∈ l.closed :=
  l.idempotent x
#align lower_adjoint.closure_is_closed LowerAdjoint.closure_is_closed

/-- The set of closed elements for `l` is the range of `u ∘ l`. -/
theorem closed_eq_range_close : l.closed = Set.range (u ∘ l) :=
  l.closureOperator.setOf_isClosed_eq_range_closure
#align lower_adjoint.closed_eq_range_close LowerAdjoint.closed_eq_range_close

/-- Send an `x` to an element of the set of closed elements (by taking the closure). -/
def toClosed (x : α) : l.closed :=
  ⟨u (l x), l.closure_is_closed x⟩
#align lower_adjoint.to_closed LowerAdjoint.toClosed

@[simp]
theorem closure_le_closed_iff_le (x : α) {y : α} (hy : l.closed y) : u (l x) ≤ y ↔ x ≤ y :=
  (show l.closureOperator.IsClosed y from hy).closure_le_iff
#align lower_adjoint.closure_le_closed_iff_le LowerAdjoint.closure_le_closed_iff_le

end PartialOrder

theorem closure_top [PartialOrder α] [OrderTop α] [Preorder β] {u : β → α} (l : LowerAdjoint u) :
    u (l ⊤) = ⊤ :=
  l.closureOperator.closure_top
#align lower_adjoint.closure_top LowerAdjoint.closure_top

theorem closure_inf_le [SemilatticeInf α] [Preorder β] {u : β → α} (l : LowerAdjoint u) (x y : α) :
    u (l (x ⊓ y)) ≤ u (l x) ⊓ u (l y) :=
  l.closureOperator.closure_inf_le x y
#align lower_adjoint.closure_inf_le LowerAdjoint.closure_inf_le

section SemilatticeSup

variable [SemilatticeSup α] [Preorder β] {u : β → α} (l : LowerAdjoint u)

theorem closure_sup_closure_le (x y : α) : u (l x) ⊔ u (l y) ≤ u (l (x ⊔ y)) :=
  l.closureOperator.closure_sup_closure_le x y
#align lower_adjoint.closure_sup_closure_le LowerAdjoint.closure_sup_closure_le

theorem closure_sup_closure_left (x y : α) : u (l (u (l x) ⊔ y)) = u (l (x ⊔ y)) :=
  l.closureOperator.closure_sup_closure_left x y
#align lower_adjoint.closure_sup_closure_left LowerAdjoint.closure_sup_closure_left

theorem closure_sup_closure_right (x y : α) : u (l (x ⊔ u (l y))) = u (l (x ⊔ y)) :=
  l.closureOperator.closure_sup_closure_right x y
#align lower_adjoint.closure_sup_closure_right LowerAdjoint.closure_sup_closure_right

theorem closure_sup_closure (x y : α) : u (l (u (l x) ⊔ u (l y))) = u (l (x ⊔ y)) :=
  l.closureOperator.closure_sup_closure x y
#align lower_adjoint.closure_sup_closure LowerAdjoint.closure_sup_closure

end SemilatticeSup

section CompleteLattice

variable [CompleteLattice α] [Preorder β] {u : β → α} (l : LowerAdjoint u)

theorem closure_iSup_closure (f : ι → α) : u (l (⨆ i, u (l (f i)))) = u (l (⨆ i, f i)) :=
  l.closureOperator.closure_iSup_closure _
#align lower_adjoint.closure_supr_closure LowerAdjoint.closure_iSup_closure

theorem closure_iSup₂_closure (f : ∀ i, κ i → α) :
    u (l <| ⨆ (i) (j), u (l <| f i j)) = u (l <| ⨆ (i) (j), f i j) :=
  l.closureOperator.closure_iSup₂_closure _
#align lower_adjoint.closure_supr₂_closure LowerAdjoint.closure_iSup₂_closure

end CompleteLattice

-- Lemmas for `LowerAdjoint ((↑) : α → Set β)`, where `SetLike α β`
section CoeToSet

variable [SetLike α β] (l : LowerAdjoint ((↑) : α → Set β))

theorem subset_closure (s : Set β) : s ⊆ l s :=
  l.le_closure s
#align lower_adjoint.subset_closure LowerAdjoint.subset_closure

theorem not_mem_of_not_mem_closure {s : Set β} {P : β} (hP : P ∉ l s) : P ∉ s := fun h =>
  hP (subset_closure _ s h)
#align lower_adjoint.not_mem_of_not_mem_closure LowerAdjoint.not_mem_of_not_mem_closure

theorem le_iff_subset (s : Set β) (S : α) : l s ≤ S ↔ s ⊆ S :=
  l.gc s S
#align lower_adjoint.le_iff_subset LowerAdjoint.le_iff_subset

theorem mem_iff (s : Set β) (x : β) : x ∈ l s ↔ ∀ S : α, s ⊆ S → x ∈ S := by
  simp_rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← l.le_iff_subset]
  exact ⟨fun h S => h.trans, fun h => h _ le_rfl⟩
#align lower_adjoint.mem_iff LowerAdjoint.mem_iff

theorem eq_of_le {s : Set β} {S : α} (h₁ : s ⊆ S) (h₂ : S ≤ l s) : l s = S :=
  ((l.le_iff_subset _ _).2 h₁).antisymm h₂
#align lower_adjoint.eq_of_le LowerAdjoint.eq_of_le

theorem closure_union_closure_subset (x y : α) : (l x : Set β) ∪ l y ⊆ l (x ∪ y) :=
  l.closure_sup_closure_le x y
#align lower_adjoint.closure_union_closure_subset LowerAdjoint.closure_union_closure_subset

@[simp]
theorem closure_union_closure_left (x y : α) : l (l x ∪ y) = l (x ∪ y) :=
  SetLike.coe_injective (l.closure_sup_closure_left x y)
#align lower_adjoint.closure_union_closure_left LowerAdjoint.closure_union_closure_left

@[simp]
theorem closure_union_closure_right (x y : α) : l (x ∪ l y) = l (x ∪ y) :=
  SetLike.coe_injective (l.closure_sup_closure_right x y)
#align lower_adjoint.closure_union_closure_right LowerAdjoint.closure_union_closure_right

theorem closure_union_closure (x y : α) : l (l x ∪ l y) = l (x ∪ y) := by
  rw [closure_union_closure_right, closure_union_closure_left]
#align lower_adjoint.closure_union_closure LowerAdjoint.closure_union_closure

@[simp]
theorem closure_iUnion_closure (f : ι → α) : l (⋃ i, l (f i)) = l (⋃ i, f i) :=
  SetLike.coe_injective <| l.closure_iSup_closure _
#align lower_adjoint.closure_Union_closure LowerAdjoint.closure_iUnion_closure

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem closure_iUnion₂_closure (f : ∀ i, κ i → α) :
    l (⋃ (i) (j), l (f i j)) = l (⋃ (i) (j), f i j) :=
  SetLike.coe_injective <| l.closure_iSup₂_closure _
#align lower_adjoint.closure_Union₂_closure LowerAdjoint.closure_iUnion₂_closure

end CoeToSet

end LowerAdjoint

/-! ### Translations between `GaloisConnection`, `LowerAdjoint`, `ClosureOperator` -/

/-- Every Galois connection induces a lower adjoint. -/
@[simps]
def GaloisConnection.lowerAdjoint [Preorder α] [Preorder β] {l : α → β} {u : β → α}
    (gc : GaloisConnection l u) : LowerAdjoint u
    where
  toFun := l
  gc' := gc
#align galois_connection.lower_adjoint GaloisConnection.lowerAdjoint
#align galois_connection.lower_adjoint_to_fun GaloisConnection.lowerAdjoint_toFun

/-- Every Galois connection induces a closure operator given by the composition. This is the partial
order version of the statement that every adjunction induces a monad. -/
@[simps!]
def GaloisConnection.closureOperator [PartialOrder α] [Preorder β] {l : α → β} {u : β → α}
    (gc : GaloisConnection l u) : ClosureOperator α :=
  gc.lowerAdjoint.closureOperator
#align galois_connection.closure_operator GaloisConnection.closureOperator
#align galois_connection.closure_operator_apply GaloisConnection.closureOperator_apply

/-- The set of closed elements has a Galois insertion to the underlying type. -/
def ClosureOperator.gi [PartialOrder α] (c : ClosureOperator α) :
    GaloisInsertion c.toCloseds (↑) where
  choice x hx := ⟨x, isClosed_iff_closure_le.2 hx⟩
  gc _ y := y.2.closure_le_iff
  le_l_u _ := c.le_closure _
  choice_eq x hx := le_antisymm (c.le_closure x) hx
#align closure_operator.gi ClosureOperator.gi

/-- The Galois insertion associated to a closure operator can be used to reconstruct the closure
operator.
Note that the inverse in the opposite direction does not hold in general. -/
@[simp]
theorem closureOperator_gi_self [PartialOrder α] (c : ClosureOperator α) :
    c.gi.gc.closureOperator = c := by
  ext x
  rfl
#align closure_operator_gi_self closureOperator_gi_self
