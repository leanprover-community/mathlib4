/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn

! This file was ported from Lean 3 source module set_theory.cardinal.basic
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.BigOperators
import Mathbin.Data.Finsupp.Defs
import Mathbin.Data.Nat.PartEnat
import Mathbin.Data.Set.Countable
import Mathbin.Logic.Small.Basic
import Mathbin.Order.ConditionallyCompleteLattice.Basic
import Mathbin.Order.SuccPred.Basic
import Mathbin.SetTheory.Cardinal.SchroederBernstein
import Mathbin.Tactic.Positivity

/-!
# Cardinal Numbers

We define cardinal numbers as a quotient of types under the equivalence relation of equinumerity.

## Main definitions

* `cardinal` the type of cardinal numbers (in a given universe).
* `cardinal.mk α` or `#α` is the cardinality of `α`. The notation `#` lives in the locale
  `cardinal`.
* Addition `c₁ + c₂` is defined by `cardinal.add_def α β : #α + #β = #(α ⊕ β)`.
* Multiplication `c₁ * c₂` is defined by `cardinal.mul_def : #α * #β = #(α × β)`.
* The order `c₁ ≤ c₂` is defined by `cardinal.le_def α β : #α ≤ #β ↔ nonempty (α ↪ β)`.
* Exponentiation `c₁ ^ c₂` is defined by `cardinal.power_def α β : #α ^ #β = #(β → α)`.
* `cardinal.aleph_0` or `ℵ₀` is the cardinality of `ℕ`. This definition is universe polymorphic:
  `cardinal.aleph_0.{u} : cardinal.{u}` (contrast with `ℕ : Type`, which lives in a specific
  universe). In some cases the universe level has to be given explicitly.
* `cardinal.sum` is the sum of an indexed family of cardinals, i.e. the cardinality of the
  corresponding sigma type.
* `cardinal.prod` is the product of an indexed family of cardinals, i.e. the cardinality of the
  corresponding pi type.
* `cardinal.powerlt a b` or `a ^< b` is defined as the supremum of `a ^ c` for `c < b`.

## Main instances

* Cardinals form a `canonically_ordered_comm_semiring` with the aforementioned sum and product.
* Cardinals form a `succ_order`. Use `order.succ c` for the smallest cardinal greater than `c`.
* The less than relation on cardinals forms a well-order.
* Cardinals form a `conditionally_complete_linear_order_bot`. Bounded sets for cardinals in universe
  `u` are precisely the sets indexed by some type in universe `u`, see
  `cardinal.bdd_above_iff_small`. One can use `Sup` for the cardinal supremum, and `Inf` for the
  minimum of a set of cardinals.

## Main Statements

* Cantor's theorem: `cardinal.cantor c : c < 2 ^ c`.
* König's theorem: `cardinal.sum_lt_prod`

## Implementation notes

* There is a type of cardinal numbers in every universe level:
  `cardinal.{u} : Type (u + 1)` is the quotient of types in `Type u`.
  The operation `cardinal.lift` lifts cardinal numbers to a higher level.
* Cardinal arithmetic specifically for infinite cardinals (like `κ * κ = κ`) is in the file
  `set_theory/cardinal_ordinal.lean`.
* There is an instance `has_pow cardinal`, but this will only fire if Lean already knows that both
  the base and the exponent live in the same universe. As a workaround, you can add
  ```
    local infixr (name := cardinal.pow) ^ := @has_pow.pow cardinal cardinal cardinal.has_pow
  ```
  to a file. This notation will work even if Lean doesn't know yet that the base and the exponent
  live in the same universe (but no exponents in other types can be used).

## References

* <https://en.wikipedia.org/wiki/Cardinal_number>

## Tags

cardinal number, cardinal arithmetic, cardinal exponentiation, aleph,
Cantor's theorem, König's theorem, Konig's theorem
-/


open Function Set Order

open BigOperators Classical

noncomputable section

universe u v w

variable {α β : Type u}

/-- The equivalence relation on types given by equivalence (bijective correspondence) of types.
  Quotienting by this equivalence relation gives the cardinal numbers.
-/
instance Cardinal.isEquivalent : Setoid (Type u)
    where
  R α β := Nonempty (α ≃ β)
  iseqv := ⟨fun α => ⟨Equiv.refl α⟩, fun α β ⟨e⟩ => ⟨e.symm⟩, fun α β γ ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩⟩
#align cardinal.is_equivalent Cardinal.isEquivalent

/-- `cardinal.{u}` is the type of cardinal numbers in `Type u`,
  defined as the quotient of `Type u` by existence of an equivalence
  (a bijection with explicit inverse). -/
def Cardinal : Type (u + 1) :=
  Quotient Cardinal.isEquivalent
#align cardinal Cardinal

namespace Cardinal

/-- The cardinal number of a type -/
def mk : Type u → Cardinal :=
  Quotient.mk'
#align cardinal.mk Cardinal.mk

-- mathport name: cardinal.mk
scoped prefix:0 "#" => Cardinal.mk

instance canLiftCardinalType : CanLift Cardinal.{u} (Type u) mk fun _ => True :=
  ⟨fun c _ => Quot.inductionOn c fun α => ⟨α, rfl⟩⟩
#align cardinal.can_lift_cardinal_Type Cardinal.canLiftCardinalType

@[elab_as_elim]
theorem induction_on {p : Cardinal → Prop} (c : Cardinal) (h : ∀ α, p (#α)) : p c :=
  Quotient.inductionOn c h
#align cardinal.induction_on Cardinal.induction_on

@[elab_as_elim]
theorem induction_on₂ {p : Cardinal → Cardinal → Prop} (c₁ : Cardinal) (c₂ : Cardinal)
    (h : ∀ α β, p (#α) (#β)) : p c₁ c₂ :=
  Quotient.induction_on₂ c₁ c₂ h
#align cardinal.induction_on₂ Cardinal.induction_on₂

@[elab_as_elim]
theorem induction_on₃ {p : Cardinal → Cardinal → Cardinal → Prop} (c₁ : Cardinal) (c₂ : Cardinal)
    (c₃ : Cardinal) (h : ∀ α β γ, p (#α) (#β) (#γ)) : p c₁ c₂ c₃ :=
  Quotient.induction_on₃ c₁ c₂ c₃ h
#align cardinal.induction_on₃ Cardinal.induction_on₃

protected theorem eq : (#α) = (#β) ↔ Nonempty (α ≃ β) :=
  Quotient.eq'
#align cardinal.eq Cardinal.eq

@[simp]
theorem mk'_def (α : Type u) : @Eq Cardinal ⟦α⟧ (#α) :=
  rfl
#align cardinal.mk_def Cardinal.mk'_def

@[simp]
theorem mk_out (c : Cardinal) : (#c.out) = c :=
  Quotient.out_eq _
#align cardinal.mk_out Cardinal.mk_out

/-- The representative of the cardinal of a type is equivalent ot the original type. -/
def outMkEquiv {α : Type v} : (#α).out ≃ α :=
  Nonempty.some <| Cardinal.eq.mp (by simp)
#align cardinal.out_mk_equiv Cardinal.outMkEquiv

theorem mk_congr (e : α ≃ β) : (#α) = (#β) :=
  Quot.sound ⟨e⟩
#align cardinal.mk_congr Cardinal.mk_congr

alias mk_congr ← _root_.equiv.cardinal_eq
#align equiv.cardinal_eq Equiv.cardinal_eq

/-- Lift a function between `Type*`s to a function between `cardinal`s. -/
def map (f : Type u → Type v) (hf : ∀ α β, α ≃ β → f α ≃ f β) : Cardinal.{u} → Cardinal.{v} :=
  Quotient.map f fun α β ⟨e⟩ => ⟨hf α β e⟩
#align cardinal.map Cardinal.map

@[simp]
theorem map_mk (f : Type u → Type v) (hf : ∀ α β, α ≃ β → f α ≃ f β) (α : Type u) :
    map f hf (#α) = (#f α) :=
  rfl
#align cardinal.map_mk Cardinal.map_mk

/-- Lift a binary operation `Type* → Type* → Type*` to a binary operation on `cardinal`s. -/
def map₂ (f : Type u → Type v → Type w) (hf : ∀ α β γ δ, α ≃ β → γ ≃ δ → f α γ ≃ f β δ) :
    Cardinal.{u} → Cardinal.{v} → Cardinal.{w} :=
  Quotient.map₂ f fun α β ⟨e₁⟩ γ δ ⟨e₂⟩ => ⟨hf α β γ δ e₁ e₂⟩
#align cardinal.map₂ Cardinal.map₂

/-- The universe lift operation on cardinals. You can specify the universes explicitly with
  `lift.{u v} : cardinal.{v} → cardinal.{max v u}` -/
def lift (c : Cardinal.{v}) : Cardinal.{max v u} :=
  map ULift (fun α β e => Equiv.ulift.trans <| e.trans Equiv.ulift.symm) c
#align cardinal.lift Cardinal.lift

@[simp]
theorem mk_uLift (α) : (#ULift.{v, u} α) = lift.{v} (#α) :=
  rfl
#align cardinal.mk_ulift Cardinal.mk_uLift

/-- `lift.{(max u v) u}` equals `lift.{v u}`. Using `set_option pp.universes true` will make it much
    easier to understand what's happening when using this lemma. -/
@[simp]
theorem lift_umax : lift.{max u v, u} = lift.{v, u} :=
  funext fun a => induction_on a fun α => (Equiv.ulift.trans Equiv.ulift.symm).cardinal_eq
#align cardinal.lift_umax Cardinal.lift_umax

/-- `lift.{(max v u) u}` equals `lift.{v u}`. Using `set_option pp.universes true` will make it much
    easier to understand what's happening when using this lemma. -/
@[simp]
theorem lift_umax' : lift.{max v u, u} = lift.{v, u} :=
  lift_umax
#align cardinal.lift_umax' Cardinal.lift_umax'

/-- A cardinal lifted to a lower or equal universe equals itself. -/
@[simp]
theorem lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a :=
  induction_on a fun α => mk_congr Equiv.ulift
#align cardinal.lift_id' Cardinal.lift_id'

/-- A cardinal lifted to the same universe equals itself. -/
@[simp]
theorem lift_id (a : Cardinal) : lift.{u, u} a = a :=
  lift_id'.{u, u} a
#align cardinal.lift_id Cardinal.lift_id

/-- A cardinal lifted to the zero universe equals itself. -/
@[simp]
theorem lift_uzero (a : Cardinal.{u}) : lift.{0} a = a :=
  lift_id'.{0, u} a
#align cardinal.lift_uzero Cardinal.lift_uzero

@[simp]
theorem lift_lift (a : Cardinal) : lift.{w} (lift.{v} a) = lift.{max v w} a :=
  induction_on a fun α => (Equiv.ulift.trans <| Equiv.ulift.trans Equiv.ulift.symm).cardinal_eq
#align cardinal.lift_lift Cardinal.lift_lift

/-- We define the order on cardinal numbers by `#α ≤ #β` if and only if
  there exists an embedding (injective function) from α to β. -/
instance : LE Cardinal.{u} :=
  ⟨fun q₁ q₂ =>
    Quotient.liftOn₂ q₁ q₂ (fun α β => Nonempty <| α ↪ β) fun α β γ δ ⟨e₁⟩ ⟨e₂⟩ =>
      propext ⟨fun ⟨e⟩ => ⟨e.congr e₁ e₂⟩, fun ⟨e⟩ => ⟨e.congr e₁.symm e₂.symm⟩⟩⟩

instance : PartialOrder Cardinal.{u} where
  le := (· ≤ ·)
  le_refl := by rintro ⟨α⟩ <;> exact ⟨embedding.refl _⟩
  le_trans := by rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨e₁⟩ ⟨e₂⟩ <;> exact ⟨e₁.trans e₂⟩
  le_antisymm := by
    rintro ⟨α⟩ ⟨β⟩ ⟨e₁⟩ ⟨e₂⟩
    exact Quotient.sound (e₁.antisymm e₂)

theorem le_def (α β : Type u) : (#α) ≤ (#β) ↔ Nonempty (α ↪ β) :=
  Iff.rfl
#align cardinal.le_def Cardinal.le_def

theorem mk_le_of_injective {α β : Type u} {f : α → β} (hf : Injective f) : (#α) ≤ (#β) :=
  ⟨⟨f, hf⟩⟩
#align cardinal.mk_le_of_injective Cardinal.mk_le_of_injective

theorem Function.Embedding.cardinal_le {α β : Type u} (f : α ↪ β) : (#α) ≤ (#β) :=
  ⟨f⟩
#align function.embedding.cardinal_le Function.Embedding.cardinal_le

theorem mk_le_of_surjective {α β : Type u} {f : α → β} (hf : Surjective f) : (#β) ≤ (#α) :=
  ⟨Embedding.ofSurjective f hf⟩
#align cardinal.mk_le_of_surjective Cardinal.mk_le_of_surjective

theorem le_mk_iff_exists_set {c : Cardinal} {α : Type u} : c ≤ (#α) ↔ ∃ p : Set α, (#p) = c :=
  ⟨induction_on c fun β ⟨⟨f, hf⟩⟩ => ⟨Set.range f, (Equiv.ofInjective f hf).cardinal_eq.symm⟩,
    fun ⟨p, e⟩ => e ▸ ⟨⟨Subtype.val, fun a b => Subtype.eq⟩⟩⟩
#align cardinal.le_mk_iff_exists_set Cardinal.le_mk_iff_exists_set

theorem mk_subtype_le {α : Type u} (p : α → Prop) : (#Subtype p) ≤ (#α) :=
  ⟨Embedding.subtype p⟩
#align cardinal.mk_subtype_le Cardinal.mk_subtype_le

theorem mk_set_le (s : Set α) : (#s) ≤ (#α) :=
  mk_subtype_le s
#align cardinal.mk_set_le Cardinal.mk_set_le

theorem out_embedding {c c' : Cardinal} : c ≤ c' ↔ Nonempty (c.out ↪ c'.out) :=
  by
  trans _
  rw [← Quotient.out_eq c, ← Quotient.out_eq c']
  rfl
#align cardinal.out_embedding Cardinal.out_embedding

theorem lift_mk_le {α : Type u} {β : Type v} :
    lift.{max v w} (#α) ≤ lift.{max u w} (#β) ↔ Nonempty (α ↪ β) :=
  ⟨fun ⟨f⟩ => ⟨Embedding.congr Equiv.ulift Equiv.ulift f⟩, fun ⟨f⟩ =>
    ⟨Embedding.congr Equiv.ulift.symm Equiv.ulift.symm f⟩⟩
#align cardinal.lift_mk_le Cardinal.lift_mk_le

/-- A variant of `cardinal.lift_mk_le` with specialized universes.
Because Lean often can not realize it should use this specialization itself,
we provide this statement separately so you don't have to solve the specialization problem either.
-/
theorem lift_mk_le' {α : Type u} {β : Type v} : lift.{v} (#α) ≤ lift.{u} (#β) ↔ Nonempty (α ↪ β) :=
  lift_mk_le.{u, v, 0}
#align cardinal.lift_mk_le' Cardinal.lift_mk_le'

theorem lift_mk_eq {α : Type u} {β : Type v} :
    lift.{max v w} (#α) = lift.{max u w} (#β) ↔ Nonempty (α ≃ β) :=
  Quotient.eq'.trans
    ⟨fun ⟨f⟩ => ⟨Equiv.ulift.symm.trans <| f.trans Equiv.ulift⟩, fun ⟨f⟩ =>
      ⟨Equiv.ulift.trans <| f.trans Equiv.ulift.symm⟩⟩
#align cardinal.lift_mk_eq Cardinal.lift_mk_eq

/-- A variant of `cardinal.lift_mk_eq` with specialized universes.
Because Lean often can not realize it should use this specialization itself,
we provide this statement separately so you don't have to solve the specialization problem either.
-/
theorem lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} (#α) = lift.{u} (#β) ↔ Nonempty (α ≃ β) :=
  lift_mk_eq.{u, v, 0}
#align cardinal.lift_mk_eq' Cardinal.lift_mk_eq'

@[simp]
theorem lift_le {a b : Cardinal} : lift a ≤ lift b ↔ a ≤ b :=
  induction_on₂ a b fun α β => by
    rw [← lift_umax]
    exact lift_mk_le
#align cardinal.lift_le Cardinal.lift_le

/-- `cardinal.lift` as an `order_embedding`. -/
@[simps (config := { fullyApplied := false })]
def liftOrderEmbedding : Cardinal.{v} ↪o Cardinal.{max v u} :=
  OrderEmbedding.ofMapLeIff lift fun _ _ => lift_le
#align cardinal.lift_order_embedding Cardinal.liftOrderEmbedding

theorem lift_injective : Injective lift.{u, v} :=
  liftOrderEmbedding.Injective
#align cardinal.lift_injective Cardinal.lift_injective

@[simp]
theorem lift_inj {a b : Cardinal} : lift a = lift b ↔ a = b :=
  lift_injective.eq_iff
#align cardinal.lift_inj Cardinal.lift_inj

@[simp]
theorem lift_lt {a b : Cardinal} : lift a < lift b ↔ a < b :=
  liftOrderEmbedding.lt_iff_lt
#align cardinal.lift_lt Cardinal.lift_lt

theorem lift_strictMono : StrictMono lift := fun a b => lift_lt.2
#align cardinal.lift_strict_mono Cardinal.lift_strictMono

theorem lift_monotone : Monotone lift :=
  lift_strictMono.Monotone
#align cardinal.lift_monotone Cardinal.lift_monotone

instance : Zero Cardinal.{u} :=
  ⟨#PEmpty⟩

instance : Inhabited Cardinal.{u} :=
  ⟨0⟩

theorem mk_eq_zero (α : Type u) [IsEmpty α] : (#α) = 0 :=
  (Equiv.equivPEmpty α).cardinal_eq
#align cardinal.mk_eq_zero Cardinal.mk_eq_zero

@[simp]
theorem lift_zero : lift 0 = 0 :=
  mk_congr (Equiv.equivPEmpty _)
#align cardinal.lift_zero Cardinal.lift_zero

@[simp]
theorem lift_eq_zero {a : Cardinal.{v}} : lift.{u} a = 0 ↔ a = 0 :=
  lift_injective.eq_iff' lift_zero
#align cardinal.lift_eq_zero Cardinal.lift_eq_zero

theorem mk_eq_zero_iff {α : Type u} : (#α) = 0 ↔ IsEmpty α :=
  ⟨fun e =>
    let ⟨h⟩ := Quotient.exact e
    h.isEmpty,
    @mk_eq_zero α⟩
#align cardinal.mk_eq_zero_iff Cardinal.mk_eq_zero_iff

theorem mk_ne_zero_iff {α : Type u} : (#α) ≠ 0 ↔ Nonempty α :=
  (not_iff_not.2 mk_eq_zero_iff).trans not_isEmpty_iff
#align cardinal.mk_ne_zero_iff Cardinal.mk_ne_zero_iff

@[simp]
theorem mk_ne_zero (α : Type u) [Nonempty α] : (#α) ≠ 0 :=
  mk_ne_zero_iff.2 ‹_›
#align cardinal.mk_ne_zero Cardinal.mk_ne_zero

instance : One Cardinal.{u} :=
  ⟨#PUnit⟩

instance : Nontrivial Cardinal.{u} :=
  ⟨⟨1, 0, mk_ne_zero _⟩⟩

theorem mk_eq_one (α : Type u) [Unique α] : (#α) = 1 :=
  (Equiv.equivPUnit α).cardinal_eq
#align cardinal.mk_eq_one Cardinal.mk_eq_one

theorem le_one_iff_subsingleton {α : Type u} : (#α) ≤ 1 ↔ Subsingleton α :=
  ⟨fun ⟨f⟩ => ⟨fun a b => f.Injective (Subsingleton.elim _ _)⟩, fun ⟨h⟩ =>
    ⟨⟨fun a => PUnit.unit, fun a b _ => h _ _⟩⟩⟩
#align cardinal.le_one_iff_subsingleton Cardinal.le_one_iff_subsingleton

@[simp]
theorem mk_le_one_iff_set_subsingleton {s : Set α} : (#s) ≤ 1 ↔ s.Subsingleton :=
  le_one_iff_subsingleton.trans s.subsingleton_coe
#align cardinal.mk_le_one_iff_set_subsingleton Cardinal.mk_le_one_iff_set_subsingleton

alias mk_le_one_iff_set_subsingleton ↔ _ _root_.set.subsingleton.cardinal_mk_le_one
#align set.subsingleton.cardinal_mk_le_one Set.Subsingleton.cardinal_mk_le_one

instance : Add Cardinal.{u} :=
  ⟨map₂ Sum fun α β γ δ => Equiv.sumCongr⟩

theorem add_def (α β : Type u) : (#α) + (#β) = (#Sum α β) :=
  rfl
#align cardinal.add_def Cardinal.add_def

instance : NatCast Cardinal.{u} :=
  ⟨Nat.unaryCast⟩

@[simp]
theorem mk_sum (α : Type u) (β : Type v) : (#Sum α β) = lift.{v, u} (#α) + lift.{u, v} (#β) :=
  mk_congr (Equiv.ulift.symm.sumCongr Equiv.ulift.symm)
#align cardinal.mk_sum Cardinal.mk_sum

@[simp]
theorem mk_option {α : Type u} : (#Option α) = (#α) + 1 :=
  (Equiv.optionEquivSumPUnit α).cardinal_eq
#align cardinal.mk_option Cardinal.mk_option

@[simp]
theorem mk_pSum (α : Type u) (β : Type v) : (#PSum α β) = lift.{v} (#α) + lift.{u} (#β) :=
  (mk_congr (Equiv.psumEquivSum α β)).trans (mk_sum α β)
#align cardinal.mk_psum Cardinal.mk_pSum

@[simp]
theorem mk_fintype (α : Type u) [Fintype α] : (#α) = Fintype.card α :=
  by
  refine' Fintype.induction_empty_option _ _ _ α
  · intro α β h e hα
    letI := Fintype.ofEquiv β e.symm
    rwa [mk_congr e, Fintype.card_congr e] at hα
  · rfl
  · intro α h hα
    simp [hα]
    rfl
#align cardinal.mk_fintype Cardinal.mk_fintype

instance : Mul Cardinal.{u} :=
  ⟨map₂ Prod fun α β γ δ => Equiv.prodCongr⟩

theorem mul_def (α β : Type u) : (#α) * (#β) = (#α × β) :=
  rfl
#align cardinal.mul_def Cardinal.mul_def

@[simp]
theorem mk_prod (α : Type u) (β : Type v) : (#α × β) = lift.{v, u} (#α) * lift.{u, v} (#β) :=
  mk_congr (Equiv.ulift.symm.prodCongr Equiv.ulift.symm)
#align cardinal.mk_prod Cardinal.mk_prod

private theorem mul_comm' (a b : Cardinal.{u}) : a * b = b * a :=
  induction_on₂ a b fun α β => mk_congr <| Equiv.prodComm α β
#align cardinal.mul_comm' cardinal.mul_comm'

/-- The cardinal exponential. `#α ^ #β` is the cardinal of `β → α`. -/
instance : Pow Cardinal.{u} Cardinal.{u} :=
  ⟨map₂ (fun α β => β → α) fun α β γ δ e₁ e₂ => e₂.arrowCongr e₁⟩

-- mathport name: cardinal.pow
local infixr:0 "^" => @Pow.pow Cardinal Cardinal Cardinal.hasPow

-- mathport name: cardinal.pow.nat
local infixr:80 " ^ℕ " => @Pow.pow Cardinal ℕ Monoid.Pow

theorem power_def (α β) : ((#α)^#β) = (#β → α) :=
  rfl
#align cardinal.power_def Cardinal.power_def

theorem mk_arrow (α : Type u) (β : Type v) : (#α → β) = (lift.{u} (#β)^lift.{v} (#α)) :=
  mk_congr (Equiv.ulift.symm.arrowCongr Equiv.ulift.symm)
#align cardinal.mk_arrow Cardinal.mk_arrow

@[simp]
theorem lift_power (a b) : lift (a^b) = (lift a^lift b) :=
  induction_on₂ a b fun α β =>
    mk_congr <| Equiv.ulift.trans (Equiv.ulift.arrowCongr Equiv.ulift).symm
#align cardinal.lift_power Cardinal.lift_power

@[simp]
theorem power_zero {a : Cardinal} : (a^0) = 1 :=
  induction_on a fun α => mk_congr <| Equiv.pemptyArrowEquivPUnit α
#align cardinal.power_zero Cardinal.power_zero

@[simp]
theorem power_one {a : Cardinal} : (a^1) = a :=
  induction_on a fun α => mk_congr <| Equiv.punitArrowEquiv α
#align cardinal.power_one Cardinal.power_one

theorem power_add {a b c : Cardinal} : (a^b + c) = (a^b) * (a^c) :=
  induction_on₃ a b c fun α β γ => mk_congr <| Equiv.sumArrowEquivProdArrow β γ α
#align cardinal.power_add Cardinal.power_add

instance : CommSemiring Cardinal.{u} where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  zero_add a := induction_on a fun α => mk_congr <| Equiv.emptySum PEmpty α
  add_zero a := induction_on a fun α => mk_congr <| Equiv.sumEmpty α PEmpty
  add_assoc a b c := induction_on₃ a b c fun α β γ => mk_congr <| Equiv.sumAssoc α β γ
  add_comm a b := induction_on₂ a b fun α β => mk_congr <| Equiv.sumComm α β
  zero_mul a := induction_on a fun α => mk_congr <| Equiv.pemptyProd α
  mul_zero a := induction_on a fun α => mk_congr <| Equiv.prodPEmpty α
  one_mul a := induction_on a fun α => mk_congr <| Equiv.punitProd α
  mul_one a := induction_on a fun α => mk_congr <| Equiv.prodPUnit α
  mul_assoc a b c := induction_on₃ a b c fun α β γ => mk_congr <| Equiv.prodAssoc α β γ
  mul_comm := mul_comm'
  left_distrib a b c := induction_on₃ a b c fun α β γ => mk_congr <| Equiv.prodSumDistrib α β γ
  right_distrib a b c := induction_on₃ a b c fun α β γ => mk_congr <| Equiv.sumProdDistrib α β γ
  npow n c := c^n
  npow_zero := @power_zero
  npow_succ n c := show (c^n + 1) = c * (c^n) by rw [power_add, power_one, mul_comm']

theorem power_bit0 (a b : Cardinal) : (a^bit0 b) = (a^b) * (a^b) :=
  power_add
#align cardinal.power_bit0 Cardinal.power_bit0

theorem power_bit1 (a b : Cardinal) : (a^bit1 b) = (a^b) * (a^b) * a := by
  rw [bit1, ← power_bit0, power_add, power_one]
#align cardinal.power_bit1 Cardinal.power_bit1

@[simp]
theorem one_power {a : Cardinal} : (1^a) = 1 :=
  induction_on a fun α => (Equiv.arrowPUnitEquivPUnit α).cardinal_eq
#align cardinal.one_power Cardinal.one_power

@[simp]
theorem mk_bool : (#Bool) = 2 := by simp
#align cardinal.mk_bool Cardinal.mk_bool

@[simp]
theorem mk_Prop : (#Prop) = 2 := by simp
#align cardinal.mk_Prop Cardinal.mk_Prop

@[simp]
theorem zero_power {a : Cardinal} : a ≠ 0 → (0^a) = 0 :=
  induction_on a fun α heq =>
    mk_eq_zero_iff.2 <|
      isEmpty_pi.2 <|
        let ⟨a⟩ := mk_ne_zero_iff.1 HEq
        ⟨a, PEmpty.isEmpty⟩
#align cardinal.zero_power Cardinal.zero_power

theorem power_ne_zero {a : Cardinal} (b) : a ≠ 0 → (a^b) ≠ 0 :=
  induction_on₂ a b fun α β h =>
    let ⟨a⟩ := mk_ne_zero_iff.1 h
    mk_ne_zero_iff.2 ⟨fun _ => a⟩
#align cardinal.power_ne_zero Cardinal.power_ne_zero

theorem mul_power {a b c : Cardinal} : (a * b^c) = (a^c) * (b^c) :=
  induction_on₃ a b c fun α β γ => mk_congr <| Equiv.arrowProdEquivProdArrow α β γ
#align cardinal.mul_power Cardinal.mul_power

theorem power_mul {a b c : Cardinal} : (a^b * c) = ((a^b)^c) :=
  by
  rw [mul_comm b c]
  exact induction_on₃ a b c fun α β γ => mk_congr <| Equiv.curry γ β α
#align cardinal.power_mul Cardinal.power_mul

@[simp]
theorem pow_cast_right (a : Cardinal.{u}) (n : ℕ) : (a^(↑n : Cardinal.{u})) = a ^ℕ n :=
  rfl
#align cardinal.pow_cast_right Cardinal.pow_cast_right

@[simp]
theorem lift_one : lift 1 = 1 :=
  mk_congr <| Equiv.ulift.trans Equiv.punitEquivPUnit
#align cardinal.lift_one Cardinal.lift_one

@[simp]
theorem lift_add (a b) : lift (a + b) = lift a + lift b :=
  induction_on₂ a b fun α β =>
    mk_congr <| Equiv.ulift.trans (Equiv.sumCongr Equiv.ulift Equiv.ulift).symm
#align cardinal.lift_add Cardinal.lift_add

@[simp]
theorem lift_mul (a b) : lift (a * b) = lift a * lift b :=
  induction_on₂ a b fun α β =>
    mk_congr <| Equiv.ulift.trans (Equiv.prodCongr Equiv.ulift Equiv.ulift).symm
#align cardinal.lift_mul Cardinal.lift_mul

@[simp]
theorem lift_bit0 (a : Cardinal) : lift (bit0 a) = bit0 (lift a) :=
  lift_add a a
#align cardinal.lift_bit0 Cardinal.lift_bit0

@[simp]
theorem lift_bit1 (a : Cardinal) : lift (bit1 a) = bit1 (lift a) := by simp [bit1]
#align cardinal.lift_bit1 Cardinal.lift_bit1

theorem lift_two : lift.{u, v} 2 = 2 := by simp
#align cardinal.lift_two Cardinal.lift_two

@[simp]
theorem mk_set {α : Type u} : (#Set α) = (2^#α) := by simp [Set, mk_arrow]
#align cardinal.mk_set Cardinal.mk_set

/-- A variant of `cardinal.mk_set` expressed in terms of a `set` instead of a `Type`. -/
@[simp]
theorem mk_powerset {α : Type u} (s : Set α) : (#↥(𝒫 s)) = (2^#↥s) :=
  (mk_congr (Equiv.Set.powerset s)).trans mk_set
#align cardinal.mk_powerset Cardinal.mk_powerset

theorem lift_two_power (a) : lift (2^a) = (2^lift a) := by simp
#align cardinal.lift_two_power Cardinal.lift_two_power

section OrderProperties

open Sum

protected theorem zero_le : ∀ a : Cardinal, 0 ≤ a := by rintro ⟨α⟩ <;> exact ⟨embedding.of_is_empty⟩
#align cardinal.zero_le Cardinal.zero_le

private theorem add_le_add' : ∀ {a b c d : Cardinal}, a ≤ b → c ≤ d → a + c ≤ b + d := by
  rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨δ⟩ ⟨e₁⟩ ⟨e₂⟩ <;> exact ⟨e₁.sum_map e₂⟩
#align cardinal.add_le_add' cardinal.add_le_add'

instance add_covariantClass : CovariantClass Cardinal Cardinal (· + ·) (· ≤ ·) :=
  ⟨fun a b c => add_le_add' le_rfl⟩
#align cardinal.add_covariant_class Cardinal.add_covariantClass

instance add_swap_covariantClass : CovariantClass Cardinal Cardinal (swap (· + ·)) (· ≤ ·) :=
  ⟨fun a b c h => add_le_add' h le_rfl⟩
#align cardinal.add_swap_covariant_class Cardinal.add_swap_covariantClass

instance : CanonicallyOrderedCommSemiring Cardinal.{u} :=
  { Cardinal.commSemiring,
    Cardinal.partialOrder with
    bot := 0
    bot_le := Cardinal.zero_le
    add_le_add_left := fun a b => add_le_add_left
    exists_add_of_le := fun a b =>
      induction_on₂ a b fun α β ⟨⟨f, hf⟩⟩ =>
        have : Sum α (range fᶜ : Set β) ≃ β :=
          (Equiv.sumCongr (Equiv.ofInjective f hf) (Equiv.refl _)).trans <|
            Equiv.Set.sumCompl (range f)
        ⟨#↥(range fᶜ), mk_congr this.symm⟩
    le_self_add := fun a b => (add_zero a).ge.trans <| add_le_add_left (Cardinal.zero_le _) _
    eq_zero_or_eq_zero_of_mul_eq_zero := fun a b =>
      induction_on₂ a b fun α β => by simpa only [mul_def, mk_eq_zero_iff, isEmpty_prod] using id }

theorem zero_power_le (c : Cardinal.{u}) : ((0 : Cardinal.{u})^c) ≤ 1 :=
  by
  by_cases h : c = 0
  rw [h, power_zero]
  rw [zero_power h]
  apply zero_le
#align cardinal.zero_power_le Cardinal.zero_power_le

theorem power_le_power_left : ∀ {a b c : Cardinal}, a ≠ 0 → b ≤ c → (a^b) ≤ (a^c) := by
  rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ hα ⟨e⟩ <;>
    exact
      let ⟨a⟩ := mk_ne_zero_iff.1 hα
      ⟨@embedding.arrow_congr_left _ _ _ ⟨a⟩ e⟩
#align cardinal.power_le_power_left Cardinal.power_le_power_left

theorem self_le_power (a : Cardinal) {b : Cardinal} (hb : 1 ≤ b) : a ≤ (a^b) :=
  by
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact zero_le _
  · convert power_le_power_left ha hb
    exact power_one.symm
#align cardinal.self_le_power Cardinal.self_le_power

/-- **Cantor's theorem** -/
theorem cantor (a : Cardinal.{u}) : a < (2^a) :=
  by
  induction' a using Cardinal.induction_on with α
  rw [← mk_set]
  refine' ⟨⟨⟨singleton, fun a b => singleton_eq_singleton_iff.1⟩⟩, _⟩
  rintro ⟨⟨f, hf⟩⟩
  exact cantor_injective f hf
#align cardinal.cantor Cardinal.cantor

instance : NoMaxOrder Cardinal.{u} :=
  { Cardinal.partialOrder with exists_gt := fun a => ⟨_, cantor a⟩ }

instance : CanonicallyLinearOrderedAddMonoid Cardinal.{u} :=
  { (inferInstance : CanonicallyOrderedAddMonoid Cardinal),
    Cardinal.partialOrder with
    le_total := by
      rintro ⟨α⟩ ⟨β⟩
      apply embedding.total
    decidableLe := Classical.decRel _ }

-- short-circuit type class inference
instance : DistribLattice Cardinal.{u} := by infer_instance

theorem one_lt_iff_nontrivial {α : Type u} : 1 < (#α) ↔ Nontrivial α := by
  rw [← not_le, le_one_iff_subsingleton, ← not_nontrivial_iff_subsingleton, Classical.not_not]
#align cardinal.one_lt_iff_nontrivial Cardinal.one_lt_iff_nontrivial

theorem power_le_max_power_one {a b c : Cardinal} (h : b ≤ c) : (a^b) ≤ max (a^c) 1 :=
  by
  by_cases ha : a = 0
  simp [ha, zero_power_le]
  exact (power_le_power_left ha h).trans (le_max_left _ _)
#align cardinal.power_le_max_power_one Cardinal.power_le_max_power_one

theorem power_le_power_right {a b c : Cardinal} : a ≤ b → (a^c) ≤ (b^c) :=
  induction_on₃ a b c fun α β γ ⟨e⟩ => ⟨Embedding.arrowCongrRight e⟩
#align cardinal.power_le_power_right Cardinal.power_le_power_right

theorem power_pos {a : Cardinal} (b) (ha : 0 < a) : 0 < (a^b) :=
  (power_ne_zero _ ha.ne').bot_lt
#align cardinal.power_pos Cardinal.power_pos

end OrderProperties

protected theorem lt_wf : @WellFounded Cardinal.{u} (· < ·) :=
  ⟨fun a =>
    by_contradiction fun h => by
      let ι := { c : Cardinal // ¬Acc (· < ·) c }
      let f : ι → Cardinal := Subtype.val
      haveI hι : Nonempty ι := ⟨⟨_, h⟩⟩
      obtain ⟨⟨c : Cardinal, hc : ¬Acc (· < ·) c⟩, ⟨h_1 : ∀ j, (f ⟨c, hc⟩).out ↪ (f j).out⟩⟩ :=
        embedding.min_injective fun i => (f i).out
      apply hc (Acc.intro _ fun j h' => by_contradiction fun hj => h'.2 _)
      have : (#_) ≤ (#_) := ⟨h_1 ⟨j, hj⟩⟩
      simpa only [f, mk_out] using this⟩
#align cardinal.lt_wf Cardinal.lt_wf

instance : WellFoundedRelation Cardinal.{u} :=
  ⟨(· < ·), Cardinal.lt_wf⟩

instance : WellFoundedLT Cardinal.{u} :=
  ⟨Cardinal.lt_wf⟩

instance wo : @IsWellOrder Cardinal.{u} (· < ·) where
#align cardinal.wo Cardinal.wo

instance : ConditionallyCompleteLinearOrderBot Cardinal :=
  IsWellOrder.conditionallyCompleteLinearOrderBot _

@[simp]
theorem infₛ_empty : infₛ (∅ : Set Cardinal.{u}) = 0 :=
  dif_neg not_nonempty_empty
#align cardinal.Inf_empty Cardinal.infₛ_empty

/-- Note that the successor of `c` is not the same as `c + 1` except in the case of finite `c`. -/
instance : SuccOrder Cardinal :=
  SuccOrder.ofSuccLeIff (fun c => infₛ { c' | c < c' }) fun a b =>
    ⟨lt_of_lt_of_le <| cinfₛ_mem <| exists_gt a, cinfₛ_le'⟩

theorem succ_def (c : Cardinal) : succ c = infₛ { c' | c < c' } :=
  rfl
#align cardinal.succ_def Cardinal.succ_def

theorem add_one_le_succ (c : Cardinal.{u}) : c + 1 ≤ succ c :=
  by
  refine' (le_cinfₛ_iff'' (exists_gt c)).2 fun b hlt => _
  rcases b, c with ⟨⟨β⟩, ⟨γ⟩⟩
  cases' le_of_lt hlt with f
  have : ¬surjective f := fun hn => (not_le_of_lt hlt) (mk_le_of_surjective hn)
  simp only [surjective, not_forall] at this
  rcases this with ⟨b, hb⟩
  calc
    (#γ) + 1 = (#Option γ) := mk_option.symm
    _ ≤ (#β) := (f.option_elim b hb).cardinal_le
    
#align cardinal.add_one_le_succ Cardinal.add_one_le_succ

theorem succ_pos : ∀ c : Cardinal, 0 < succ c :=
  bot_lt_succ
#align cardinal.succ_pos Cardinal.succ_pos

theorem succ_ne_zero (c : Cardinal) : succ c ≠ 0 :=
  (succ_pos _).ne'
#align cardinal.succ_ne_zero Cardinal.succ_ne_zero

/-- The indexed sum of cardinals is the cardinality of the
  indexed disjoint union, i.e. sigma type. -/
def sum {ι} (f : ι → Cardinal) : Cardinal :=
  mk (Σi, (f i).out)
#align cardinal.sum Cardinal.sum

theorem le_sum {ι} (f : ι → Cardinal) (i) : f i ≤ sum f := by
  rw [← Quotient.out_eq (f i)] <;>
    exact ⟨⟨fun a => ⟨i, a⟩, fun a b h => eq_of_hEq <| by injection h⟩⟩
#align cardinal.le_sum Cardinal.le_sum

@[simp]
theorem mk_sigma {ι} (f : ι → Type _) : (#Σi, f i) = sum fun i => #f i :=
  mk_congr <| Equiv.sigmaCongrRight fun i => outMkEquiv.symm
#align cardinal.mk_sigma Cardinal.mk_sigma

@[simp]
theorem sum_const (ι : Type u) (a : Cardinal.{v}) :
    (sum fun i : ι => a) = lift.{v} (#ι) * lift.{u} a :=
  induction_on a fun α =>
    mk_congr <|
      calc
        (Σi : ι, Quotient.out (#α)) ≃ ι × Quotient.out (#α) := Equiv.sigmaEquivProd _ _
        _ ≃ ULift ι × ULift α := Equiv.ulift.symm.prodCongr (outMkEquiv.trans Equiv.ulift.symm)
        
#align cardinal.sum_const Cardinal.sum_const

theorem sum_const' (ι : Type u) (a : Cardinal.{u}) : (sum fun _ : ι => a) = (#ι) * a := by simp
#align cardinal.sum_const' Cardinal.sum_const'

@[simp]
theorem sum_add_distrib {ι} (f g : ι → Cardinal) : sum (f + g) = sum f + sum g := by
  simpa only [mk_sigma, mk_sum, mk_out, lift_id] using
    mk_congr (Equiv.sigmaSumDistrib (Quotient.out ∘ f) (Quotient.out ∘ g))
#align cardinal.sum_add_distrib Cardinal.sum_add_distrib

@[simp]
theorem sum_add_distrib' {ι} (f g : ι → Cardinal) :
    (Cardinal.sum fun i => f i + g i) = sum f + sum g :=
  sum_add_distrib f g
#align cardinal.sum_add_distrib' Cardinal.sum_add_distrib'

@[simp]
theorem lift_sum {ι : Type u} (f : ι → Cardinal.{v}) :
    Cardinal.lift.{w} (Cardinal.sum f) = Cardinal.sum fun i => Cardinal.lift.{w} (f i) :=
  Equiv.cardinal_eq <|
    Equiv.ulift.trans <|
      Equiv.sigmaCongrRight fun a =>
        Nonempty.some <| by rw [← lift_mk_eq, mk_out, mk_out, lift_lift]
#align cardinal.lift_sum Cardinal.lift_sum

theorem sum_le_sum {ι} (f g : ι → Cardinal) (H : ∀ i, f i ≤ g i) : sum f ≤ sum g :=
  ⟨(Embedding.refl _).sigma_map fun i =>
      Classical.choice <| by have := H i <;> rwa [← Quot.out_eq (f i), ← Quot.out_eq (g i)] at this⟩
#align cardinal.sum_le_sum Cardinal.sum_le_sum

theorem mk_le_mk_mul_of_mk_preimage_le {c : Cardinal} (f : α → β) (hf : ∀ b : β, (#f ⁻¹' {b}) ≤ c) :
    (#α) ≤ (#β) * c := by
  simpa only [← mk_congr (@Equiv.sigmaFiberEquiv α β f), mk_sigma, ← sum_const'] using
    sum_le_sum _ _ hf
#align cardinal.mk_le_mk_mul_of_mk_preimage_le Cardinal.mk_le_mk_mul_of_mk_preimage_le

theorem lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le {α : Type u} {β : Type v} {c : Cardinal}
    (f : α → β) (hf : ∀ b : β, lift.{v} (#f ⁻¹' {b}) ≤ c) : lift.{v} (#α) ≤ lift.{u} (#β) * c :=
  (mk_le_mk_mul_of_mk_preimage_le fun x : ULift.{v} α => ULift.up.{u} (f x.1)) <|
    ULift.forall.2 fun b =>
      (mk_congr <|
            (Equiv.ulift.image _).trans
              (Equiv.trans
                (by
                  rw [Equiv.image_eq_preimage]
                  simp [Set.preimage])
                Equiv.ulift.symm)).trans_le
        (hf b)
#align cardinal.lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le Cardinal.lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le

/-- The range of an indexed cardinal function, whose outputs live in a higher universe than the
    inputs, is always bounded above. -/
theorem bddAbove_range {ι : Type u} (f : ι → Cardinal.{max u v}) : BddAbove (Set.range f) :=
  ⟨_, by
    rintro a ⟨i, rfl⟩
    exact le_sum f i⟩
#align cardinal.bdd_above_range Cardinal.bddAbove_range

instance (a : Cardinal.{u}) : Small.{u} (Set.Iic a) :=
  by
  rw [← mk_out a]
  apply @small_of_surjective (Set a.out) (Iic (#a.out)) _ fun x => ⟨#x, mk_set_le x⟩
  rintro ⟨x, hx⟩
  simpa using le_mk_iff_exists_set.1 hx

instance (a : Cardinal.{u}) : Small.{u} (Set.Iio a) :=
  small_subset Iio_subset_Iic_self

/-- A set of cardinals is bounded above iff it's small, i.e. it corresponds to an usual ZFC set. -/
theorem bddAbove_iff_small {s : Set Cardinal.{u}} : BddAbove s ↔ Small.{u} s :=
  ⟨fun ⟨a, ha⟩ => @small_subset _ (Iic a) s (fun x h => ha h) _,
    by
    rintro ⟨ι, ⟨e⟩⟩
    suffices (range fun x : ι => (e.symm x).1) = s
      by
      rw [← this]
      apply bddAbove_range.{u, u}
    ext x
    refine' ⟨_, fun hx => ⟨e ⟨x, hx⟩, _⟩⟩
    · rintro ⟨a, rfl⟩
      exact (e.symm a).Prop
    · simp_rw [Subtype.val_eq_coe, Equiv.symm_apply_apply]
      rfl⟩
#align cardinal.bdd_above_iff_small Cardinal.bddAbove_iff_small

theorem bddAbove_of_small (s : Set Cardinal.{u}) [h : Small.{u} s] : BddAbove s :=
  bddAbove_iff_small.2 h
#align cardinal.bdd_above_of_small Cardinal.bddAbove_of_small

theorem bddAbove_image (f : Cardinal.{u} → Cardinal.{max u v}) {s : Set Cardinal.{u}}
    (hs : BddAbove s) : BddAbove (f '' s) :=
  by
  rw [bdd_above_iff_small] at hs⊢
  exact small_lift _
#align cardinal.bdd_above_image Cardinal.bddAbove_image

theorem bddAbove_range_comp {ι : Type u} {f : ι → Cardinal.{v}} (hf : BddAbove (range f))
    (g : Cardinal.{v} → Cardinal.{max v w}) : BddAbove (range (g ∘ f)) :=
  by
  rw [range_comp]
  exact bdd_above_image g hf
#align cardinal.bdd_above_range_comp Cardinal.bddAbove_range_comp

theorem supᵢ_le_sum {ι} (f : ι → Cardinal) : supᵢ f ≤ sum f :=
  csupᵢ_le' <| le_sum _
#align cardinal.supr_le_sum Cardinal.supᵢ_le_sum

theorem sum_le_supᵢ_lift {ι : Type u} (f : ι → Cardinal.{max u v}) : sum f ≤ (#ι).lift * supᵢ f :=
  by
  rw [← (supᵢ f).lift_id, ← lift_umax, lift_umax.{max u v, u}, ← sum_const]
  exact sum_le_sum _ _ (le_csupᵢ <| bddAbove_range.{u, v} f)
#align cardinal.sum_le_supr_lift Cardinal.sum_le_supᵢ_lift

theorem sum_le_supᵢ {ι : Type u} (f : ι → Cardinal.{u}) : sum f ≤ (#ι) * supᵢ f :=
  by
  rw [← lift_id (#ι)]
  exact sum_le_supr_lift f
#align cardinal.sum_le_supr Cardinal.sum_le_supᵢ

theorem sum_nat_eq_add_sum_succ (f : ℕ → Cardinal.{u}) :
    Cardinal.sum f = f 0 + Cardinal.sum fun i => f (i + 1) :=
  by
  refine' (Equiv.sigmaNatSucc fun i => Quotient.out (f i)).cardinal_eq.trans _
  simp only [mk_sum, mk_out, lift_id, mk_sigma]
#align cardinal.sum_nat_eq_add_sum_succ Cardinal.sum_nat_eq_add_sum_succ

/-- A variant of `csupr_of_empty` but with `0` on the RHS for convenience -/
@[simp]
protected theorem supᵢ_of_empty {ι} (f : ι → Cardinal) [IsEmpty ι] : supᵢ f = 0 :=
  csupᵢ_of_empty f
#align cardinal.supr_of_empty Cardinal.supᵢ_of_empty

@[simp]
theorem lift_mk_shrink (α : Type u) [Small.{v} α] :
    Cardinal.lift.{max u w} (#Shrink.{v} α) = Cardinal.lift.{max v w} (#α) :=
  lift_mk_eq.2 ⟨(equivShrink α).symm⟩
#align cardinal.lift_mk_shrink Cardinal.lift_mk_shrink

@[simp]
theorem lift_mk_shrink' (α : Type u) [Small.{v} α] :
    Cardinal.lift.{u} (#Shrink.{v} α) = Cardinal.lift.{v} (#α) :=
  lift_mk_shrink.{u, v, 0} α
#align cardinal.lift_mk_shrink' Cardinal.lift_mk_shrink'

@[simp]
theorem lift_mk_shrink'' (α : Type max u v) [Small.{v} α] :
    Cardinal.lift.{u} (#Shrink.{v} α) = (#α) := by
  rw [← lift_umax', lift_mk_shrink.{max u v, v, 0} α, ← lift_umax, lift_id]
#align cardinal.lift_mk_shrink'' Cardinal.lift_mk_shrink''

/-- The indexed product of cardinals is the cardinality of the Pi type
  (dependent product). -/
def prod {ι : Type u} (f : ι → Cardinal) : Cardinal :=
  #∀ i, (f i).out
#align cardinal.prod Cardinal.prod

@[simp]
theorem mk_pi {ι : Type u} (α : ι → Type v) : (#∀ i, α i) = prod fun i => #α i :=
  mk_congr <| Equiv.piCongrRight fun i => outMkEquiv.symm
#align cardinal.mk_pi Cardinal.mk_pi

@[simp]
theorem prod_const (ι : Type u) (a : Cardinal.{v}) :
    (prod fun i : ι => a) = (lift.{u} a^lift.{v} (#ι)) :=
  induction_on a fun α =>
    mk_congr <| Equiv.piCongr Equiv.ulift.symm fun i => outMkEquiv.trans Equiv.ulift.symm
#align cardinal.prod_const Cardinal.prod_const

theorem prod_const' (ι : Type u) (a : Cardinal.{u}) : (prod fun _ : ι => a) = (a^#ι) :=
  induction_on a fun α => (mk_pi _).symm
#align cardinal.prod_const' Cardinal.prod_const'

theorem prod_le_prod {ι} (f g : ι → Cardinal) (H : ∀ i, f i ≤ g i) : prod f ≤ prod g :=
  ⟨Embedding.piCongrRight fun i =>
      Classical.choice <| by have := H i <;> rwa [← mk_out (f i), ← mk_out (g i)] at this⟩
#align cardinal.prod_le_prod Cardinal.prod_le_prod

@[simp]
theorem prod_eq_zero {ι} (f : ι → Cardinal.{u}) : prod f = 0 ↔ ∃ i, f i = 0 :=
  by
  lift f to ι → Type u using fun _ => trivial
  simp only [mk_eq_zero_iff, ← mk_pi, isEmpty_pi]
#align cardinal.prod_eq_zero Cardinal.prod_eq_zero

theorem prod_ne_zero {ι} (f : ι → Cardinal) : prod f ≠ 0 ↔ ∀ i, f i ≠ 0 := by simp [prod_eq_zero]
#align cardinal.prod_ne_zero Cardinal.prod_ne_zero

@[simp]
theorem lift_prod {ι : Type u} (c : ι → Cardinal.{v}) :
    lift.{w} (prod c) = prod fun i => lift.{w} (c i) :=
  by
  lift c to ι → Type v using fun _ => trivial
  simp only [← mk_pi, ← mk_ulift]
  exact mk_congr (equiv.ulift.trans <| Equiv.piCongrRight fun i => equiv.ulift.symm)
#align cardinal.lift_prod Cardinal.lift_prod

theorem prod_eq_of_fintype {α : Type u} [Fintype α] (f : α → Cardinal.{v}) :
    prod f = Cardinal.lift.{u} (∏ i, f i) := by
  revert f
  refine' Fintype.induction_empty_option _ _ _ α
  · intro α β hβ e h f
    letI := Fintype.ofEquiv β e.symm
    rw [← e.prod_comp f, ← h]
    exact mk_congr (e.Pi_congr_left _).symm
  · intro f
    rw [Fintype.univ_pempty, Finset.prod_empty, lift_one, Cardinal.prod, mk_eq_one]
  · intro α hα h f
    rw [Cardinal.prod, mk_congr Equiv.piOptionEquivProd, mk_prod, lift_umax', mk_out, ←
      Cardinal.prod, lift_prod, Fintype.prod_option, lift_mul, ← h fun a => f (some a)]
    simp only [lift_id]
#align cardinal.prod_eq_of_fintype Cardinal.prod_eq_of_fintype

@[simp]
theorem lift_infₛ (s : Set Cardinal) : lift (infₛ s) = infₛ (lift '' s) :=
  by
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · simp
  · exact lift_monotone.map_Inf hs
#align cardinal.lift_Inf Cardinal.lift_infₛ

@[simp]
theorem lift_infᵢ {ι} (f : ι → Cardinal) : lift (infᵢ f) = ⨅ i, lift (f i) :=
  by
  unfold infᵢ
  convert lift_Inf (range f)
  rw [range_comp]
#align cardinal.lift_infi Cardinal.lift_infᵢ

theorem lift_down {a : Cardinal.{u}} {b : Cardinal.{max u v}} : b ≤ lift a → ∃ a', lift a' = b :=
  induction_on₂ a b fun α β => by
    rw [← lift_id (#β), ← lift_umax, ← lift_umax.{u, v}, lift_mk_le] <;>
      exact fun ⟨f⟩ =>
        ⟨#Set.range f,
          Eq.symm <|
            lift_mk_eq.2
              ⟨embedding.equiv_of_surjective (Embedding.codRestrict _ f Set.mem_range_self)
                  fun ⟨a, ⟨b, e⟩⟩ => ⟨b, Subtype.eq e⟩⟩⟩
#align cardinal.lift_down Cardinal.lift_down

theorem le_lift_iff {a : Cardinal.{u}} {b : Cardinal.{max u v}} :
    b ≤ lift a ↔ ∃ a', lift a' = b ∧ a' ≤ a :=
  ⟨fun h =>
    let ⟨a', e⟩ := lift_down h
    ⟨a', e, lift_le.1 <| e.symm ▸ h⟩,
    fun ⟨a', e, h⟩ => e ▸ lift_le.2 h⟩
#align cardinal.le_lift_iff Cardinal.le_lift_iff

theorem lt_lift_iff {a : Cardinal.{u}} {b : Cardinal.{max u v}} :
    b < lift a ↔ ∃ a', lift a' = b ∧ a' < a :=
  ⟨fun h =>
    let ⟨a', e⟩ := lift_down h.le
    ⟨a', e, lift_lt.1 <| e.symm ▸ h⟩,
    fun ⟨a', e, h⟩ => e ▸ lift_lt.2 h⟩
#align cardinal.lt_lift_iff Cardinal.lt_lift_iff

@[simp]
theorem lift_succ (a) : lift (succ a) = succ (lift a) :=
  le_antisymm
    (le_of_not_gt fun h => by
      rcases lt_lift_iff.1 h with ⟨b, e, h⟩
      rw [lt_succ_iff, ← lift_le, e] at h
      exact h.not_lt (lt_succ _))
    (succ_le_of_lt <| lift_lt.2 <| lt_succ a)
#align cardinal.lift_succ Cardinal.lift_succ

@[simp]
theorem lift_umax_eq {a : Cardinal.{u}} {b : Cardinal.{v}} :
    lift.{max v w} a = lift.{max u w} b ↔ lift.{v} a = lift.{u} b := by
  rw [← lift_lift, ← lift_lift, lift_inj]
#align cardinal.lift_umax_eq Cardinal.lift_umax_eq

@[simp]
theorem lift_min {a b : Cardinal} : lift (min a b) = min (lift a) (lift b) :=
  lift_monotone.map_min
#align cardinal.lift_min Cardinal.lift_min

@[simp]
theorem lift_max {a b : Cardinal} : lift (max a b) = max (lift a) (lift b) :=
  lift_monotone.map_max
#align cardinal.lift_max Cardinal.lift_max

/-- The lift of a supremum is the supremum of the lifts. -/
theorem lift_supₛ {s : Set Cardinal} (hs : BddAbove s) : lift.{u} (supₛ s) = supₛ (lift.{u} '' s) :=
  by
  apply ((le_csupₛ_iff' (bdd_above_image _ hs)).2 fun c hc => _).antisymm (csupₛ_le' _)
  · by_contra h
    obtain ⟨d, rfl⟩ := Cardinal.lift_down (not_le.1 h).le
    simp_rw [lift_le] at h hc
    rw [csupₛ_le_iff' hs] at h
    exact h fun a ha => lift_le.1 <| hc (mem_image_of_mem _ ha)
  · rintro i ⟨j, hj, rfl⟩
    exact lift_le.2 (le_csupₛ hs hj)
#align cardinal.lift_Sup Cardinal.lift_supₛ

/-- The lift of a supremum is the supremum of the lifts. -/
theorem lift_supᵢ {ι : Type v} {f : ι → Cardinal.{w}} (hf : BddAbove (range f)) :
    lift.{u} (supᵢ f) = ⨆ i, lift.{u} (f i) := by rw [supᵢ, supᵢ, lift_Sup hf, ← range_comp]
#align cardinal.lift_supr Cardinal.lift_supᵢ

/-- To prove that the lift of a supremum is bounded by some cardinal `t`,
it suffices to show that the lift of each cardinal is bounded by `t`. -/
theorem lift_supᵢ_le {ι : Type v} {f : ι → Cardinal.{w}} {t : Cardinal} (hf : BddAbove (range f))
    (w : ∀ i, lift.{u} (f i) ≤ t) : lift.{u} (supᵢ f) ≤ t :=
  by
  rw [lift_supr hf]
  exact csupᵢ_le' w
#align cardinal.lift_supr_le Cardinal.lift_supᵢ_le

@[simp]
theorem lift_supᵢ_le_iff {ι : Type v} {f : ι → Cardinal.{w}} (hf : BddAbove (range f))
    {t : Cardinal} : lift.{u} (supᵢ f) ≤ t ↔ ∀ i, lift.{u} (f i) ≤ t :=
  by
  rw [lift_supr hf]
  exact csupᵢ_le_iff' (bdd_above_range_comp hf _)
#align cardinal.lift_supr_le_iff Cardinal.lift_supᵢ_le_iff

universe v' w'

/-- To prove an inequality between the lifts to a common universe of two different supremums,
it suffices to show that the lift of each cardinal from the smaller supremum
if bounded by the lift of some cardinal from the larger supremum.
-/
theorem lift_supᵢ_le_lift_supᵢ {ι : Type v} {ι' : Type v'} {f : ι → Cardinal.{w}}
    {f' : ι' → Cardinal.{w'}} (hf : BddAbove (range f)) (hf' : BddAbove (range f')) {g : ι → ι'}
    (h : ∀ i, lift.{w'} (f i) ≤ lift.{w} (f' (g i))) : lift.{w'} (supᵢ f) ≤ lift.{w} (supᵢ f') :=
  by
  rw [lift_supr hf, lift_supr hf']
  exact csupᵢ_mono' (bdd_above_range_comp hf' _) fun i => ⟨_, h i⟩
#align cardinal.lift_supr_le_lift_supr Cardinal.lift_supᵢ_le_lift_supᵢ

/-- A variant of `lift_supr_le_lift_supr` with universes specialized via `w = v` and `w' = v'`.
This is sometimes necessary to avoid universe unification issues. -/
theorem lift_supᵢ_le_lift_supr' {ι : Type v} {ι' : Type v'} {f : ι → Cardinal.{v}}
    {f' : ι' → Cardinal.{v'}} (hf : BddAbove (range f)) (hf' : BddAbove (range f')) (g : ι → ι')
    (h : ∀ i, lift.{v'} (f i) ≤ lift.{v} (f' (g i))) : lift.{v'} (supᵢ f) ≤ lift.{v} (supᵢ f') :=
  lift_supᵢ_le_lift_supᵢ hf hf' h
#align cardinal.lift_supr_le_lift_supr' Cardinal.lift_supᵢ_le_lift_supr'

/-- `ℵ₀` is the smallest infinite cardinal. -/
def aleph0 : Cardinal.{u} :=
  lift (#ℕ)
#align cardinal.aleph_0 Cardinal.aleph0

-- mathport name: cardinal.aleph_0
scoped notation "ℵ₀" => Cardinal.aleph0

theorem mk_nat : (#ℕ) = ℵ₀ :=
  (lift_id _).symm
#align cardinal.mk_nat Cardinal.mk_nat

theorem aleph0_ne_zero : ℵ₀ ≠ 0 :=
  mk_ne_zero _
#align cardinal.aleph_0_ne_zero Cardinal.aleph0_ne_zero

theorem aleph0_pos : 0 < ℵ₀ :=
  pos_iff_ne_zero.2 aleph0_ne_zero
#align cardinal.aleph_0_pos Cardinal.aleph0_pos

@[simp]
theorem lift_aleph0 : lift ℵ₀ = ℵ₀ :=
  lift_lift _
#align cardinal.lift_aleph_0 Cardinal.lift_aleph0

@[simp]
theorem aleph0_le_lift {c : Cardinal.{u}} : ℵ₀ ≤ lift.{v} c ↔ ℵ₀ ≤ c := by
  rw [← lift_aleph_0, lift_le]
#align cardinal.aleph_0_le_lift Cardinal.aleph0_le_lift

@[simp]
theorem lift_le_aleph0 {c : Cardinal.{u}} : lift.{v} c ≤ ℵ₀ ↔ c ≤ ℵ₀ := by
  rw [← lift_aleph_0, lift_le]
#align cardinal.lift_le_aleph_0 Cardinal.lift_le_aleph0

/-! ### Properties about the cast from `ℕ` -/


@[simp]
theorem mk_fin (n : ℕ) : (#Fin n) = n := by simp
#align cardinal.mk_fin Cardinal.mk_fin

@[simp]
theorem lift_nat_cast (n : ℕ) : lift.{u} (n : Cardinal.{v}) = n := by induction n <;> simp [*]
#align cardinal.lift_nat_cast Cardinal.lift_nat_cast

@[simp]
theorem lift_eq_nat_iff {a : Cardinal.{u}} {n : ℕ} : lift.{v} a = n ↔ a = n :=
  lift_injective.eq_iff' (lift_nat_cast n)
#align cardinal.lift_eq_nat_iff Cardinal.lift_eq_nat_iff

@[simp]
theorem nat_eq_lift_iff {n : ℕ} {a : Cardinal.{u}} :
    (n : Cardinal) = lift.{v} a ↔ (n : Cardinal) = a := by rw [← lift_nat_cast.{v} n, lift_inj]
#align cardinal.nat_eq_lift_iff Cardinal.nat_eq_lift_iff

theorem lift_mk_fin (n : ℕ) : lift (#Fin n) = n := by simp
#align cardinal.lift_mk_fin Cardinal.lift_mk_fin

theorem mk_coe_finset {α : Type u} {s : Finset α} : (#s) = ↑(Finset.card s) := by simp
#align cardinal.mk_coe_finset Cardinal.mk_coe_finset

theorem mk_finset_of_fintype [Fintype α] : (#Finset α) = 2 ^ℕ Fintype.card α := by simp
#align cardinal.mk_finset_of_fintype Cardinal.mk_finset_of_fintype

@[simp]
theorem mk_finsupp_lift_of_fintype (α : Type u) (β : Type v) [Fintype α] [Zero β] :
    (#α →₀ β) = lift.{u} (#β) ^ℕ Fintype.card α := by
  simpa using (@Finsupp.equivFunOnFinite α β _ _).cardinal_eq
#align cardinal.mk_finsupp_lift_of_fintype Cardinal.mk_finsupp_lift_of_fintype

theorem mk_finsupp_of_fintype (α β : Type u) [Fintype α] [Zero β] :
    (#α →₀ β) = (#β) ^ℕ Fintype.card α := by simp
#align cardinal.mk_finsupp_of_fintype Cardinal.mk_finsupp_of_fintype

theorem card_le_of_finset {α} (s : Finset α) : (s.card : Cardinal) ≤ (#α) :=
  @mk_coe_finset _ s ▸ mk_set_le _
#align cardinal.card_le_of_finset Cardinal.card_le_of_finset

@[simp, norm_cast]
theorem nat_cast_pow {m n : ℕ} : (↑(pow m n) : Cardinal) = (m^n) := by
  induction n <;> simp [pow_succ', power_add, *]
#align cardinal.nat_cast_pow Cardinal.nat_cast_pow

@[simp, norm_cast]
theorem nat_cast_le {m n : ℕ} : (m : Cardinal) ≤ n ↔ m ≤ n := by
  rw [← lift_mk_fin, ← lift_mk_fin, lift_le, le_def, Function.Embedding.nonempty_iff_card_le,
    Fintype.card_fin, Fintype.card_fin]
#align cardinal.nat_cast_le Cardinal.nat_cast_le

@[simp, norm_cast]
theorem nat_cast_lt {m n : ℕ} : (m : Cardinal) < n ↔ m < n := by simp [lt_iff_le_not_le, ← not_le]
#align cardinal.nat_cast_lt Cardinal.nat_cast_lt

instance : CharZero Cardinal :=
  ⟨StrictMono.injective fun m n => nat_cast_lt.2⟩

theorem nat_cast_inj {m n : ℕ} : (m : Cardinal) = n ↔ m = n :=
  Nat.cast_inj
#align cardinal.nat_cast_inj Cardinal.nat_cast_inj

theorem nat_cast_injective : Injective (coe : ℕ → Cardinal) :=
  Nat.cast_injective
#align cardinal.nat_cast_injective Cardinal.nat_cast_injective

@[simp, norm_cast]
theorem nat_succ (n : ℕ) : (n.succ : Cardinal) = succ n :=
  (add_one_le_succ _).antisymm (succ_le_of_lt <| nat_cast_lt.2 <| Nat.lt_succ_self _)
#align cardinal.nat_succ Cardinal.nat_succ

@[simp]
theorem succ_zero : succ (0 : Cardinal) = 1 := by norm_cast
#align cardinal.succ_zero Cardinal.succ_zero

theorem card_le_of {α : Type u} {n : ℕ} (H : ∀ s : Finset α, s.card ≤ n) : (#α) ≤ n :=
  by
  refine' le_of_lt_succ (lt_of_not_ge fun hn => _)
  rw [← Cardinal.nat_succ, ← lift_mk_fin n.succ] at hn
  cases' hn with f
  refine' (H <| finset.univ.map f).not_lt _
  rw [Finset.card_map, ← Fintype.card, Fintype.card_ulift, Fintype.card_fin]
  exact n.lt_succ_self
#align cardinal.card_le_of Cardinal.card_le_of

theorem cantor' (a) {b : Cardinal} (hb : 1 < b) : a < (b^a) :=
  by
  rw [← succ_le_iff, (by norm_cast : succ (1 : Cardinal) = 2)] at hb
  exact (cantor a).trans_le (power_le_power_right hb)
#align cardinal.cantor' Cardinal.cantor'

theorem one_le_iff_pos {c : Cardinal} : 1 ≤ c ↔ 0 < c := by rw [← succ_zero, succ_le_iff]
#align cardinal.one_le_iff_pos Cardinal.one_le_iff_pos

theorem one_le_iff_ne_zero {c : Cardinal} : 1 ≤ c ↔ c ≠ 0 := by rw [one_le_iff_pos, pos_iff_ne_zero]
#align cardinal.one_le_iff_ne_zero Cardinal.one_le_iff_ne_zero

theorem nat_lt_aleph0 (n : ℕ) : (n : Cardinal.{u}) < ℵ₀ :=
  succ_le_iff.1
    (by
      rw [← nat_succ, ← lift_mk_fin, aleph_0, lift_mk_le.{0, 0, u}]
      exact ⟨⟨coe, fun a b => Fin.ext⟩⟩)
#align cardinal.nat_lt_aleph_0 Cardinal.nat_lt_aleph0

@[simp]
theorem one_lt_aleph0 : 1 < ℵ₀ := by simpa using nat_lt_aleph_0 1
#align cardinal.one_lt_aleph_0 Cardinal.one_lt_aleph0

theorem one_le_aleph0 : 1 ≤ ℵ₀ :=
  one_lt_aleph0.le
#align cardinal.one_le_aleph_0 Cardinal.one_le_aleph0

theorem lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ ∃ n : ℕ, c = n :=
  ⟨fun h => by
    rcases lt_lift_iff.1 h with ⟨c, rfl, h'⟩
    rcases le_mk_iff_exists_set.1 h'.1 with ⟨S, rfl⟩
    suffices S.finite by
      lift S to Finset ℕ using this
      simp
    contrapose! h'
    haveI := infinite.to_subtype h'
    exact ⟨Infinite.natEmbedding S⟩, fun ⟨n, e⟩ => e.symm ▸ nat_lt_aleph0 _⟩
#align cardinal.lt_aleph_0 Cardinal.lt_aleph0

theorem aleph0_le {c : Cardinal} : ℵ₀ ≤ c ↔ ∀ n : ℕ, ↑n ≤ c :=
  ⟨fun h n => (nat_lt_aleph0 _).le.trans h, fun h =>
    le_of_not_lt fun hn => by
      rcases lt_aleph_0.1 hn with ⟨n, rfl⟩
      exact (Nat.lt_succ_self _).not_le (nat_cast_le.1 (h (n + 1)))⟩
#align cardinal.aleph_0_le Cardinal.aleph0_le

@[simp]
theorem range_nat_cast : range (coe : ℕ → Cardinal) = Iio ℵ₀ :=
  ext fun x => by simp only [mem_Iio, mem_range, eq_comm, lt_aleph_0]
#align cardinal.range_nat_cast Cardinal.range_nat_cast

theorem mk_eq_nat_iff {α : Type u} {n : ℕ} : (#α) = n ↔ Nonempty (α ≃ Fin n) := by
  rw [← lift_mk_fin, ← lift_uzero (#α), lift_mk_eq']
#align cardinal.mk_eq_nat_iff Cardinal.mk_eq_nat_iff

theorem lt_aleph0_iff_finite {α : Type u} : (#α) < ℵ₀ ↔ Finite α := by
  simp only [lt_aleph_0, mk_eq_nat_iff, finite_iff_exists_equiv_fin]
#align cardinal.lt_aleph_0_iff_finite Cardinal.lt_aleph0_iff_finite

theorem lt_aleph0_iff_fintype {α : Type u} : (#α) < ℵ₀ ↔ Nonempty (Fintype α) :=
  lt_aleph0_iff_finite.trans (finite_iff_nonempty_fintype _)
#align cardinal.lt_aleph_0_iff_fintype Cardinal.lt_aleph0_iff_fintype

theorem lt_aleph0_of_finite (α : Type u) [Finite α] : (#α) < ℵ₀ :=
  lt_aleph0_iff_finite.2 ‹_›
#align cardinal.lt_aleph_0_of_finite Cardinal.lt_aleph0_of_finite

@[simp]
theorem lt_aleph0_iff_set_finite {S : Set α} : (#S) < ℵ₀ ↔ S.Finite :=
  lt_aleph0_iff_finite.trans finite_coe_iff
#align cardinal.lt_aleph_0_iff_set_finite Cardinal.lt_aleph0_iff_set_finite

alias lt_aleph_0_iff_set_finite ↔ _ _root_.set.finite.lt_aleph_0
#align set.finite.lt_aleph_0 Set.Finite.lt_aleph0

@[simp]
theorem lt_aleph0_iff_subtype_finite {p : α → Prop} : (#{ x // p x }) < ℵ₀ ↔ { x | p x }.Finite :=
  lt_aleph0_iff_set_finite
#align cardinal.lt_aleph_0_iff_subtype_finite Cardinal.lt_aleph0_iff_subtype_finite

theorem mk_le_aleph0_iff : (#α) ≤ ℵ₀ ↔ Countable α := by
  rw [countable_iff_nonempty_embedding, aleph_0, ← lift_uzero (#α), lift_mk_le']
#align cardinal.mk_le_aleph_0_iff Cardinal.mk_le_aleph0_iff

@[simp]
theorem mk_le_aleph0 [Countable α] : (#α) ≤ ℵ₀ :=
  mk_le_aleph0_iff.mpr ‹_›
#align cardinal.mk_le_aleph_0 Cardinal.mk_le_aleph0

@[simp]
theorem le_aleph0_iff_set_countable {s : Set α} : (#s) ≤ ℵ₀ ↔ s.Countable := by
  rw [mk_le_aleph_0_iff, countable_coe_iff]
#align cardinal.le_aleph_0_iff_set_countable Cardinal.le_aleph0_iff_set_countable

alias le_aleph_0_iff_set_countable ↔ _ _root_.set.countable.le_aleph_0
#align set.countable.le_aleph_0 Set.Countable.le_aleph0

@[simp]
theorem le_aleph0_iff_subtype_countable {p : α → Prop} :
    (#{ x // p x }) ≤ ℵ₀ ↔ { x | p x }.Countable :=
  le_aleph0_iff_set_countable
#align cardinal.le_aleph_0_iff_subtype_countable Cardinal.le_aleph0_iff_subtype_countable

instance canLiftCardinalNat : CanLift Cardinal ℕ coe fun x => x < ℵ₀ :=
  ⟨fun x hx =>
    let ⟨n, hn⟩ := lt_aleph0.mp hx
    ⟨n, hn.symm⟩⟩
#align cardinal.can_lift_cardinal_nat Cardinal.canLiftCardinalNat

theorem add_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a + b < ℵ₀ :=
  match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [← Nat.cast_add] <;> apply nat_lt_aleph_0
#align cardinal.add_lt_aleph_0 Cardinal.add_lt_aleph0

theorem add_lt_aleph0_iff {a b : Cardinal} : a + b < ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀ :=
  ⟨fun h => ⟨(self_le_add_right _ _).trans_lt h, (self_le_add_left _ _).trans_lt h⟩, fun ⟨h1, h2⟩ =>
    add_lt_aleph0 h1 h2⟩
#align cardinal.add_lt_aleph_0_iff Cardinal.add_lt_aleph0_iff

theorem aleph0_le_add_iff {a b : Cardinal} : ℵ₀ ≤ a + b ↔ ℵ₀ ≤ a ∨ ℵ₀ ≤ b := by
  simp only [← not_lt, add_lt_aleph_0_iff, not_and_or]
#align cardinal.aleph_0_le_add_iff Cardinal.aleph0_le_add_iff

/-- See also `cardinal.nsmul_lt_aleph_0_iff_of_ne_zero` if you already have `n ≠ 0`. -/
theorem nsmul_lt_aleph0_iff {n : ℕ} {a : Cardinal} : n • a < ℵ₀ ↔ n = 0 ∨ a < ℵ₀ :=
  by
  cases n
  · simpa using nat_lt_aleph_0 0
  simp only [Nat.succ_ne_zero, false_or_iff]
  induction' n with n ih
  · simp
  rw [succ_nsmul, add_lt_aleph_0_iff, ih, and_self_iff]
#align cardinal.nsmul_lt_aleph_0_iff Cardinal.nsmul_lt_aleph0_iff

/-- See also `cardinal.nsmul_lt_aleph_0_iff` for a hypothesis-free version. -/
theorem nsmul_lt_aleph0_iff_of_ne_zero {n : ℕ} {a : Cardinal} (h : n ≠ 0) : n • a < ℵ₀ ↔ a < ℵ₀ :=
  nsmul_lt_aleph0_iff.trans <| or_iff_right h
#align cardinal.nsmul_lt_aleph_0_iff_of_ne_zero Cardinal.nsmul_lt_aleph0_iff_of_ne_zero

theorem mul_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a * b < ℵ₀ :=
  match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [← Nat.cast_mul] <;> apply nat_lt_aleph_0
#align cardinal.mul_lt_aleph_0 Cardinal.mul_lt_aleph0

theorem mul_lt_aleph0_iff {a b : Cardinal} : a * b < ℵ₀ ↔ a = 0 ∨ b = 0 ∨ a < ℵ₀ ∧ b < ℵ₀ :=
  by
  refine' ⟨fun h => _, _⟩
  · by_cases ha : a = 0
    · exact Or.inl ha
    right
    by_cases hb : b = 0
    · exact Or.inl hb
    right
    rw [← Ne, ← one_le_iff_ne_zero] at ha hb
    constructor
    · rw [← mul_one a]
      refine' (mul_le_mul' le_rfl hb).trans_lt h
    · rw [← one_mul b]
      refine' (mul_le_mul' ha le_rfl).trans_lt h
  rintro (rfl | rfl | ⟨ha, hb⟩) <;> simp only [*, mul_lt_aleph_0, aleph_0_pos, zero_mul, mul_zero]
#align cardinal.mul_lt_aleph_0_iff Cardinal.mul_lt_aleph0_iff

/-- See also `cardinal.aleph_0_le_mul_iff`. -/
theorem aleph0_le_mul_iff {a b : Cardinal} : ℵ₀ ≤ a * b ↔ a ≠ 0 ∧ b ≠ 0 ∧ (ℵ₀ ≤ a ∨ ℵ₀ ≤ b) :=
  by
  let h := (@mul_lt_aleph0_iff a b).Not
  rwa [not_lt, not_or, not_or, not_and_or, not_lt, not_lt] at h
#align cardinal.aleph_0_le_mul_iff Cardinal.aleph0_le_mul_iff

/-- See also `cardinal.aleph_0_le_mul_iff'`. -/
theorem aleph0_le_mul_iff' {a b : Cardinal.{u}} : ℵ₀ ≤ a * b ↔ a ≠ 0 ∧ ℵ₀ ≤ b ∨ ℵ₀ ≤ a ∧ b ≠ 0 :=
  by
  have : ∀ {a : Cardinal.{u}}, ℵ₀ ≤ a → a ≠ 0 := fun a => ne_bot_of_le_ne_bot aleph_0_ne_zero
  simp only [aleph_0_le_mul_iff, and_or_left, and_iff_right_of_imp this, @and_left_comm (a ≠ 0)]
  simp only [and_comm, or_comm]
#align cardinal.aleph_0_le_mul_iff' Cardinal.aleph0_le_mul_iff'

theorem mul_lt_aleph0_iff_of_ne_zero {a b : Cardinal} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b < ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀ := by simp [mul_lt_aleph_0_iff, ha, hb]
#align cardinal.mul_lt_aleph_0_iff_of_ne_zero Cardinal.mul_lt_aleph0_iff_of_ne_zero

theorem power_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : (a^b) < ℵ₀ :=
  match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [← nat_cast_pow] <;> apply nat_lt_aleph_0
#align cardinal.power_lt_aleph_0 Cardinal.power_lt_aleph0

theorem eq_one_iff_unique {α : Type _} : (#α) = 1 ↔ Subsingleton α ∧ Nonempty α :=
  calc
    (#α) = 1 ↔ (#α) ≤ 1 ∧ 1 ≤ (#α) := le_antisymm_iff
    _ ↔ Subsingleton α ∧ Nonempty α :=
      le_one_iff_subsingleton.And (one_le_iff_ne_zero.trans mk_ne_zero_iff)
    
#align cardinal.eq_one_iff_unique Cardinal.eq_one_iff_unique

theorem infinite_iff {α : Type u} : Infinite α ↔ ℵ₀ ≤ (#α) := by
  rw [← not_lt, lt_aleph_0_iff_finite, not_finite_iff_infinite]
#align cardinal.infinite_iff Cardinal.infinite_iff

@[simp]
theorem aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ ≤ (#α) :=
  infinite_iff.1 ‹_›
#align cardinal.aleph_0_le_mk Cardinal.aleph0_le_mk

@[simp]
theorem mk_eq_aleph0 (α : Type _) [Countable α] [Infinite α] : (#α) = ℵ₀ :=
  mk_le_aleph0.antisymm <| aleph0_le_mk _
#align cardinal.mk_eq_aleph_0 Cardinal.mk_eq_aleph0

theorem denumerable_iff {α : Type u} : Nonempty (Denumerable α) ↔ (#α) = ℵ₀ :=
  ⟨fun ⟨h⟩ => mk_congr ((@Denumerable.eqv α h).trans Equiv.ulift.symm), fun h =>
    by
    cases' Quotient.exact h with f
    exact ⟨Denumerable.mk' <| f.trans Equiv.ulift⟩⟩
#align cardinal.denumerable_iff Cardinal.denumerable_iff

@[simp]
theorem mk_denumerable (α : Type u) [Denumerable α] : (#α) = ℵ₀ :=
  denumerable_iff.1 ⟨‹_›⟩
#align cardinal.mk_denumerable Cardinal.mk_denumerable

@[simp]
theorem aleph0_add_aleph0 : ℵ₀ + ℵ₀ = ℵ₀ :=
  mk_denumerable _
#align cardinal.aleph_0_add_aleph_0 Cardinal.aleph0_add_aleph0

theorem aleph0_mul_aleph0 : ℵ₀ * ℵ₀ = ℵ₀ :=
  mk_denumerable _
#align cardinal.aleph_0_mul_aleph_0 Cardinal.aleph0_mul_aleph0

@[simp]
theorem nat_mul_aleph0 {n : ℕ} (hn : n ≠ 0) : ↑n * ℵ₀ = ℵ₀ :=
  le_antisymm (lift_mk_fin n ▸ mk_le_aleph0) <|
    le_mul_of_one_le_left (zero_le _) <| by
      rwa [← Nat.cast_one, nat_cast_le, Nat.one_le_iff_ne_zero]
#align cardinal.nat_mul_aleph_0 Cardinal.nat_mul_aleph0

@[simp]
theorem aleph0_mul_nat {n : ℕ} (hn : n ≠ 0) : ℵ₀ * n = ℵ₀ := by rw [mul_comm, nat_mul_aleph_0 hn]
#align cardinal.aleph_0_mul_nat Cardinal.aleph0_mul_nat

@[simp]
theorem add_le_aleph0 {c₁ c₂ : Cardinal} : c₁ + c₂ ≤ ℵ₀ ↔ c₁ ≤ ℵ₀ ∧ c₂ ≤ ℵ₀ :=
  ⟨fun h => ⟨le_self_add.trans h, le_add_self.trans h⟩, fun h =>
    aleph0_add_aleph0 ▸ add_le_add h.1 h.2⟩
#align cardinal.add_le_aleph_0 Cardinal.add_le_aleph0

@[simp]
theorem aleph0_add_nat (n : ℕ) : ℵ₀ + n = ℵ₀ :=
  (add_le_aleph0.2 ⟨le_rfl, (nat_lt_aleph0 n).le⟩).antisymm le_self_add
#align cardinal.aleph_0_add_nat Cardinal.aleph0_add_nat

@[simp]
theorem nat_add_aleph0 (n : ℕ) : ↑n + ℵ₀ = ℵ₀ := by rw [add_comm, aleph_0_add_nat]
#align cardinal.nat_add_aleph_0 Cardinal.nat_add_aleph0

/-- This function sends finite cardinals to the corresponding natural, and infinite cardinals
  to 0. -/
def toNat : ZeroHom Cardinal ℕ :=
  ⟨fun c => if h : c < aleph0.{v} then Classical.choose (lt_aleph0.1 h) else 0,
    by
    have h : 0 < ℵ₀ := nat_lt_aleph_0 0
    rw [dif_pos h, ← Cardinal.nat_cast_inj, ← Classical.choose_spec (lt_aleph_0.1 h),
      Nat.cast_zero]⟩
#align cardinal.to_nat Cardinal.toNat

theorem toNat_apply_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) :
    c.toNat = Classical.choose (lt_aleph0.1 h) :=
  dif_pos h
#align cardinal.to_nat_apply_of_lt_aleph_0 Cardinal.toNat_apply_of_lt_aleph0

theorem toNat_apply_of_aleph0_le {c : Cardinal} (h : ℵ₀ ≤ c) : c.toNat = 0 :=
  dif_neg h.not_lt
#align cardinal.to_nat_apply_of_aleph_0_le Cardinal.toNat_apply_of_aleph0_le

theorem cast_toNat_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : ↑c.toNat = c := by
  rw [to_nat_apply_of_lt_aleph_0 h, ← Classical.choose_spec (lt_aleph_0.1 h)]
#align cardinal.cast_to_nat_of_lt_aleph_0 Cardinal.cast_toNat_of_lt_aleph0

theorem cast_toNat_of_aleph0_le {c : Cardinal} (h : ℵ₀ ≤ c) : ↑c.toNat = (0 : Cardinal) := by
  rw [to_nat_apply_of_aleph_0_le h, Nat.cast_zero]
#align cardinal.cast_to_nat_of_aleph_0_le Cardinal.cast_toNat_of_aleph0_le

theorem toNat_le_iff_le_of_lt_aleph0 {c d : Cardinal} (hc : c < ℵ₀) (hd : d < ℵ₀) :
    c.toNat ≤ d.toNat ↔ c ≤ d := by
  rw [← nat_cast_le, cast_to_nat_of_lt_aleph_0 hc, cast_to_nat_of_lt_aleph_0 hd]
#align cardinal.to_nat_le_iff_le_of_lt_aleph_0 Cardinal.toNat_le_iff_le_of_lt_aleph0

theorem toNat_lt_iff_lt_of_lt_aleph0 {c d : Cardinal} (hc : c < ℵ₀) (hd : d < ℵ₀) :
    c.toNat < d.toNat ↔ c < d := by
  rw [← nat_cast_lt, cast_to_nat_of_lt_aleph_0 hc, cast_to_nat_of_lt_aleph_0 hd]
#align cardinal.to_nat_lt_iff_lt_of_lt_aleph_0 Cardinal.toNat_lt_iff_lt_of_lt_aleph0

theorem toNat_le_of_le_of_lt_aleph0 {c d : Cardinal} (hd : d < ℵ₀) (hcd : c ≤ d) :
    c.toNat ≤ d.toNat :=
  (toNat_le_iff_le_of_lt_aleph0 (hcd.trans_lt hd) hd).mpr hcd
#align cardinal.to_nat_le_of_le_of_lt_aleph_0 Cardinal.toNat_le_of_le_of_lt_aleph0

theorem toNat_lt_of_lt_of_lt_aleph0 {c d : Cardinal} (hd : d < ℵ₀) (hcd : c < d) :
    c.toNat < d.toNat :=
  (toNat_lt_iff_lt_of_lt_aleph0 (hcd.trans hd) hd).mpr hcd
#align cardinal.to_nat_lt_of_lt_of_lt_aleph_0 Cardinal.toNat_lt_of_lt_of_lt_aleph0

@[simp]
theorem toNat_cast (n : ℕ) : Cardinal.toNat n = n :=
  by
  rw [to_nat_apply_of_lt_aleph_0 (nat_lt_aleph_0 n), ← nat_cast_inj]
  exact (Classical.choose_spec (lt_aleph_0.1 (nat_lt_aleph_0 n))).symm
#align cardinal.to_nat_cast Cardinal.toNat_cast

/-- `to_nat` has a right-inverse: coercion. -/
theorem toNat_rightInverse : Function.RightInverse (coe : ℕ → Cardinal) toNat :=
  toNat_cast
#align cardinal.to_nat_right_inverse Cardinal.toNat_rightInverse

theorem toNat_surjective : Surjective toNat :=
  toNat_rightInverse.Surjective
#align cardinal.to_nat_surjective Cardinal.toNat_surjective

theorem exists_nat_eq_of_le_nat {c : Cardinal} {n : ℕ} (h : c ≤ n) : ∃ m, m ≤ n ∧ c = m :=
  let he := cast_toNat_of_lt_aleph0 (h.trans_lt <| nat_lt_aleph0 n)
  ⟨c.toNat, nat_cast_le.1 (he.trans_le h), he.symm⟩
#align cardinal.exists_nat_eq_of_le_nat Cardinal.exists_nat_eq_of_le_nat

@[simp]
theorem mk_toNat_of_infinite [h : Infinite α] : (#α).toNat = 0 :=
  dif_neg (infinite_iff.1 h).not_lt
#align cardinal.mk_to_nat_of_infinite Cardinal.mk_toNat_of_infinite

@[simp]
theorem aleph0_toNat : toNat ℵ₀ = 0 :=
  toNat_apply_of_aleph0_le le_rfl
#align cardinal.aleph_0_to_nat Cardinal.aleph0_toNat

theorem mk_toNat_eq_card [Fintype α] : (#α).toNat = Fintype.card α := by simp
#align cardinal.mk_to_nat_eq_card Cardinal.mk_toNat_eq_card

@[simp]
theorem zero_toNat : toNat 0 = 0 := by rw [← to_nat_cast 0, Nat.cast_zero]
#align cardinal.zero_to_nat Cardinal.zero_toNat

@[simp]
theorem one_toNat : toNat 1 = 1 := by rw [← to_nat_cast 1, Nat.cast_one]
#align cardinal.one_to_nat Cardinal.one_toNat

theorem toNat_eq_iff {c : Cardinal} {n : ℕ} (hn : n ≠ 0) : toNat c = n ↔ c = n :=
  ⟨fun h =>
    (cast_toNat_of_lt_aleph0
            (lt_of_not_ge (hn ∘ h.symm.trans ∘ toNat_apply_of_aleph0_le))).symm.trans
      (congr_arg coe h),
    fun h => (congr_arg toNat h).trans (toNat_cast n)⟩
#align cardinal.to_nat_eq_iff Cardinal.toNat_eq_iff

@[simp]
theorem toNat_eq_one {c : Cardinal} : toNat c = 1 ↔ c = 1 := by
  rw [to_nat_eq_iff one_ne_zero, Nat.cast_one]
#align cardinal.to_nat_eq_one Cardinal.toNat_eq_one

theorem toNat_eq_one_iff_unique {α : Type _} : (#α).toNat = 1 ↔ Subsingleton α ∧ Nonempty α :=
  toNat_eq_one.trans eq_one_iff_unique
#align cardinal.to_nat_eq_one_iff_unique Cardinal.toNat_eq_one_iff_unique

@[simp]
theorem toNat_lift (c : Cardinal.{v}) : (lift.{u, v} c).toNat = c.toNat :=
  by
  apply nat_cast_injective
  cases' lt_or_ge c ℵ₀ with hc hc
  · rw [cast_to_nat_of_lt_aleph_0, ← lift_nat_cast, cast_to_nat_of_lt_aleph_0 hc]
    rwa [← lift_aleph_0, lift_lt]
  · rw [cast_to_nat_of_aleph_0_le, ← lift_nat_cast, cast_to_nat_of_aleph_0_le hc, lift_zero]
    rwa [← lift_aleph_0, lift_le]
#align cardinal.to_nat_lift Cardinal.toNat_lift

theorem toNat_congr {β : Type v} (e : α ≃ β) : (#α).toNat = (#β).toNat := by
  rw [← to_nat_lift, lift_mk_eq.mpr ⟨e⟩, to_nat_lift]
#align cardinal.to_nat_congr Cardinal.toNat_congr

@[simp]
theorem toNat_mul (x y : Cardinal) : (x * y).toNat = x.toNat * y.toNat :=
  by
  rcases eq_or_ne x 0 with (rfl | hx1)
  · rw [zero_mul, zero_to_nat, zero_mul]
  rcases eq_or_ne y 0 with (rfl | hy1)
  · rw [mul_zero, zero_to_nat, mul_zero]
  cases' lt_or_le x ℵ₀ with hx2 hx2
  · cases' lt_or_le y ℵ₀ with hy2 hy2
    · lift x to ℕ using hx2
      lift y to ℕ using hy2
      rw [← Nat.cast_mul, to_nat_cast, to_nat_cast, to_nat_cast]
    · rw [to_nat_apply_of_aleph_0_le hy2, mul_zero, to_nat_apply_of_aleph_0_le]
      exact aleph_0_le_mul_iff'.2 (Or.inl ⟨hx1, hy2⟩)
  · rw [to_nat_apply_of_aleph_0_le hx2, zero_mul, to_nat_apply_of_aleph_0_le]
    exact aleph_0_le_mul_iff'.2 (Or.inr ⟨hx2, hy1⟩)
#align cardinal.to_nat_mul Cardinal.toNat_mul

/-- `cardinal.to_nat` as a `monoid_with_zero_hom`. -/
@[simps]
def toNatHom : Cardinal →*₀ ℕ where
  toFun := toNat
  map_zero' := zero_toNat
  map_one' := one_toNat
  map_mul' := toNat_mul
#align cardinal.to_nat_hom Cardinal.toNatHom

theorem toNat_finset_prod (s : Finset α) (f : α → Cardinal) :
    toNat (∏ i in s, f i) = ∏ i in s, toNat (f i) :=
  map_prod toNatHom _ _
#align cardinal.to_nat_finset_prod Cardinal.toNat_finset_prod

@[simp]
theorem toNat_add_of_lt_aleph0 {a : Cardinal.{u}} {b : Cardinal.{v}} (ha : a < ℵ₀) (hb : b < ℵ₀) :
    (lift.{v, u} a + lift.{u, v} b).toNat = a.toNat + b.toNat :=
  by
  apply Cardinal.nat_cast_injective
  replace ha : lift.{v, u} a < ℵ₀ := by
    rw [← lift_aleph_0]
    exact lift_lt.2 ha
  replace hb : lift.{u, v} b < ℵ₀ := by
    rw [← lift_aleph_0]
    exact lift_lt.2 hb
  rw [Nat.cast_add, ← toNat_lift.{v, u} a, ← toNat_lift.{u, v} b, cast_to_nat_of_lt_aleph_0 ha,
    cast_to_nat_of_lt_aleph_0 hb, cast_to_nat_of_lt_aleph_0 (add_lt_aleph_0 ha hb)]
#align cardinal.to_nat_add_of_lt_aleph_0 Cardinal.toNat_add_of_lt_aleph0

/-- This function sends finite cardinals to the corresponding natural, and infinite cardinals
  to `⊤`. -/
def toPartEnat : Cardinal →+ PartEnat
    where
  toFun c := if c < ℵ₀ then c.toNat else ⊤
  map_zero' := by simp [if_pos (zero_lt_one.trans one_lt_aleph_0)]
  map_add' x y := by
    by_cases hx : x < ℵ₀
    · obtain ⟨x0, rfl⟩ := lt_aleph_0.1 hx
      by_cases hy : y < ℵ₀
      · obtain ⟨y0, rfl⟩ := lt_aleph_0.1 hy
        simp only [add_lt_aleph_0 hx hy, hx, hy, to_nat_cast, if_true]
        rw [← Nat.cast_add, to_nat_cast, Nat.cast_add]
      · rw [if_neg hy, if_neg, PartEnat.add_top]
        contrapose! hy
        apply le_add_self.trans_lt hy
    · rw [if_neg hx, if_neg, PartEnat.top_add]
      contrapose! hx
      apply le_self_add.trans_lt hx
#align cardinal.to_part_enat Cardinal.toPartEnat

theorem toPartEnat_apply_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : c.toPartEnat = c.toNat :=
  if_pos h
#align cardinal.to_part_enat_apply_of_lt_aleph_0 Cardinal.toPartEnat_apply_of_lt_aleph0

theorem toPartEnat_apply_of_aleph0_le {c : Cardinal} (h : ℵ₀ ≤ c) : c.toPartEnat = ⊤ :=
  if_neg h.not_lt
#align cardinal.to_part_enat_apply_of_aleph_0_le Cardinal.toPartEnat_apply_of_aleph0_le

@[simp]
theorem toPartEnat_cast (n : ℕ) : Cardinal.toPartEnat n = n := by
  rw [to_part_enat_apply_of_lt_aleph_0 (nat_lt_aleph_0 n), to_nat_cast]
#align cardinal.to_part_enat_cast Cardinal.toPartEnat_cast

@[simp]
theorem mk_toPartEnat_of_infinite [h : Infinite α] : (#α).toPartEnat = ⊤ :=
  toPartEnat_apply_of_aleph0_le (infinite_iff.1 h)
#align cardinal.mk_to_part_enat_of_infinite Cardinal.mk_toPartEnat_of_infinite

@[simp]
theorem aleph0_toPartEnat : toPartEnat ℵ₀ = ⊤ :=
  toPartEnat_apply_of_aleph0_le le_rfl
#align cardinal.aleph_0_to_part_enat Cardinal.aleph0_toPartEnat

theorem toPartEnat_surjective : Surjective toPartEnat := fun x =>
  PartEnat.cases_on x ⟨ℵ₀, toPartEnat_apply_of_aleph0_le le_rfl⟩ fun n => ⟨n, toPartEnat_cast n⟩
#align cardinal.to_part_enat_surjective Cardinal.toPartEnat_surjective

theorem mk_toPartEnat_eq_coe_card [Fintype α] : (#α).toPartEnat = Fintype.card α := by simp
#align cardinal.mk_to_part_enat_eq_coe_card Cardinal.mk_toPartEnat_eq_coe_card

theorem mk_int : (#ℤ) = ℵ₀ :=
  mk_denumerable ℤ
#align cardinal.mk_int Cardinal.mk_int

theorem mk_pNat : (#ℕ+) = ℵ₀ :=
  mk_denumerable ℕ+
#align cardinal.mk_pnat Cardinal.mk_pNat

/-- **König's theorem** -/
theorem sum_lt_prod {ι} (f g : ι → Cardinal) (H : ∀ i, f i < g i) : sum f < prod g :=
  lt_of_not_ge fun ⟨F⟩ =>
    by
    have : Inhabited (∀ i : ι, (g i).out) :=
      by
      refine' ⟨fun i => Classical.choice <| mk_ne_zero_iff.1 _⟩
      rw [mk_out]
      exact (H i).ne_bot
    let G := inv_fun F
    have sG : surjective G := inv_fun_surjective F.2
    choose C hc using
      show ∀ i, ∃ b, ∀ a, G ⟨i, a⟩ i ≠ b by
        intro i
        simp only [-not_exists, not_exists.symm, not_forall.symm]
        refine' fun h => (H i).not_le _
        rw [← mk_out (f i), ← mk_out (g i)]
        exact ⟨embedding.of_surjective _ h⟩
    exact
      let ⟨⟨i, a⟩, h⟩ := sG C
      hc i a (congr_fun h _)
#align cardinal.sum_lt_prod Cardinal.sum_lt_prod

@[simp]
theorem mk_empty : (#Empty) = 0 :=
  mk_eq_zero _
#align cardinal.mk_empty Cardinal.mk_empty

@[simp]
theorem mk_pEmpty : (#PEmpty) = 0 :=
  mk_eq_zero _
#align cardinal.mk_pempty Cardinal.mk_pEmpty

@[simp]
theorem mk_pUnit : (#PUnit) = 1 :=
  mk_eq_one PUnit
#align cardinal.mk_punit Cardinal.mk_pUnit

theorem mk_unit : (#Unit) = 1 :=
  mk_pUnit
#align cardinal.mk_unit Cardinal.mk_unit

@[simp]
theorem mk_singleton {α : Type u} (x : α) : (#({x} : Set α)) = 1 :=
  mk_eq_one _
#align cardinal.mk_singleton Cardinal.mk_singleton

@[simp]
theorem mk_pLift_true : (#PLift True) = 1 :=
  mk_eq_one _
#align cardinal.mk_plift_true Cardinal.mk_pLift_true

@[simp]
theorem mk_pLift_false : (#PLift False) = 0 :=
  mk_eq_zero _
#align cardinal.mk_plift_false Cardinal.mk_pLift_false

@[simp]
theorem mk_vector (α : Type u) (n : ℕ) : (#Vector α n) = (#α) ^ℕ n :=
  (mk_congr (Equiv.vectorEquivFin α n)).trans <| by simp
#align cardinal.mk_vector Cardinal.mk_vector

theorem mk_list_eq_sum_pow (α : Type u) : (#List α) = sum fun n : ℕ => (#α) ^ℕ n :=
  calc
    (#List α) = (#Σn, Vector α n) := mk_congr (Equiv.sigmaFiberEquiv List.length).symm
    _ = sum fun n : ℕ => (#α) ^ℕ n := by simp
    
#align cardinal.mk_list_eq_sum_pow Cardinal.mk_list_eq_sum_pow

theorem mk_quot_le {α : Type u} {r : α → α → Prop} : (#Quot r) ≤ (#α) :=
  mk_le_of_surjective Quot.exists_rep
#align cardinal.mk_quot_le Cardinal.mk_quot_le

theorem mk_quotient_le {α : Type u} {s : Setoid α} : (#Quotient s) ≤ (#α) :=
  mk_quot_le
#align cardinal.mk_quotient_le Cardinal.mk_quotient_le

theorem mk_subtype_le_of_subset {α : Type u} {p q : α → Prop} (h : ∀ ⦃x⦄, p x → q x) :
    (#Subtype p) ≤ (#Subtype q) :=
  ⟨Embedding.subtypeMap (Embedding.refl α) h⟩
#align cardinal.mk_subtype_le_of_subset Cardinal.mk_subtype_le_of_subset

@[simp]
theorem mk_emptyCollection (α : Type u) : (#(∅ : Set α)) = 0 :=
  mk_eq_zero _
#align cardinal.mk_emptyc Cardinal.mk_emptyCollection

theorem mk_emptyCollection_iff {α : Type u} {s : Set α} : (#s) = 0 ↔ s = ∅ :=
  by
  constructor
  · intro h
    rw [mk_eq_zero_iff] at h
    exact eq_empty_iff_forall_not_mem.2 fun x hx => h.elim' ⟨x, hx⟩
  · rintro rfl
    exact mk_emptyc _
#align cardinal.mk_emptyc_iff Cardinal.mk_emptyCollection_iff

@[simp]
theorem mk_univ {α : Type u} : (#@univ α) = (#α) :=
  mk_congr (Equiv.Set.univ α)
#align cardinal.mk_univ Cardinal.mk_univ

theorem mk_image_le {α β : Type u} {f : α → β} {s : Set α} : (#f '' s) ≤ (#s) :=
  mk_le_of_surjective surjective_onto_image
#align cardinal.mk_image_le Cardinal.mk_image_le

theorem mk_image_le_lift {α : Type u} {β : Type v} {f : α → β} {s : Set α} :
    lift.{u} (#f '' s) ≤ lift.{v} (#s) :=
  lift_mk_le.{v, u, 0}.mpr ⟨Embedding.ofSurjective _ surjective_onto_image⟩
#align cardinal.mk_image_le_lift Cardinal.mk_image_le_lift

theorem mk_range_le {α β : Type u} {f : α → β} : (#range f) ≤ (#α) :=
  mk_le_of_surjective surjective_onto_range
#align cardinal.mk_range_le Cardinal.mk_range_le

theorem mk_range_le_lift {α : Type u} {β : Type v} {f : α → β} :
    lift.{u} (#range f) ≤ lift.{v} (#α) :=
  lift_mk_le.{v, u, 0}.mpr ⟨Embedding.ofSurjective _ surjective_onto_range⟩
#align cardinal.mk_range_le_lift Cardinal.mk_range_le_lift

theorem mk_range_eq (f : α → β) (h : Injective f) : (#range f) = (#α) :=
  mk_congr (Equiv.ofInjective f h).symm
#align cardinal.mk_range_eq Cardinal.mk_range_eq

theorem mk_range_eq_of_injective {α : Type u} {β : Type v} {f : α → β} (hf : Injective f) :
    lift.{u} (#range f) = lift.{v} (#α) :=
  lift_mk_eq'.mpr ⟨(Equiv.ofInjective f hf).symm⟩
#align cardinal.mk_range_eq_of_injective Cardinal.mk_range_eq_of_injective

theorem mk_range_eq_lift {α : Type u} {β : Type v} {f : α → β} (hf : Injective f) :
    lift.{max u w} (#range f) = lift.{max v w} (#α) :=
  lift_mk_eq.mpr ⟨(Equiv.ofInjective f hf).symm⟩
#align cardinal.mk_range_eq_lift Cardinal.mk_range_eq_lift

theorem mk_image_eq {α β : Type u} {f : α → β} {s : Set α} (hf : Injective f) : (#f '' s) = (#s) :=
  mk_congr (Equiv.Set.image f s hf).symm
#align cardinal.mk_image_eq Cardinal.mk_image_eq

theorem mk_unionᵢ_le_sum_mk {α ι : Type u} {f : ι → Set α} : (#⋃ i, f i) ≤ sum fun i => #f i :=
  calc
    (#⋃ i, f i) ≤ (#Σi, f i) := mk_le_of_surjective (Set.sigmaToUnionᵢ_surjective f)
    _ = sum fun i => #f i := mk_sigma _
    
#align cardinal.mk_Union_le_sum_mk Cardinal.mk_unionᵢ_le_sum_mk

theorem mk_unionᵢ_eq_sum_mk {α ι : Type u} {f : ι → Set α}
    (h : ∀ i j, i ≠ j → Disjoint (f i) (f j)) : (#⋃ i, f i) = sum fun i => #f i :=
  calc
    (#⋃ i, f i) = (#Σi, f i) := mk_congr (Set.unionEqSigmaOfDisjoint h)
    _ = sum fun i => #f i := mk_sigma _
    
#align cardinal.mk_Union_eq_sum_mk Cardinal.mk_unionᵢ_eq_sum_mk

theorem mk_unionᵢ_le {α ι : Type u} (f : ι → Set α) : (#⋃ i, f i) ≤ (#ι) * ⨆ i, #f i :=
  mk_unionᵢ_le_sum_mk.trans (sum_le_supᵢ _)
#align cardinal.mk_Union_le Cardinal.mk_unionᵢ_le

theorem mk_unionₛ_le {α : Type u} (A : Set (Set α)) : (#⋃₀ A) ≤ (#A) * ⨆ s : A, #s :=
  by
  rw [sUnion_eq_Union]
  apply mk_Union_le
#align cardinal.mk_sUnion_le Cardinal.mk_unionₛ_le

theorem mk_bUnion_le {ι α : Type u} (A : ι → Set α) (s : Set ι) :
    (#⋃ x ∈ s, A x) ≤ (#s) * ⨆ x : s, #A x.1 :=
  by
  rw [bUnion_eq_Union]
  apply mk_Union_le
#align cardinal.mk_bUnion_le Cardinal.mk_bUnion_le

theorem finset_card_lt_aleph0 (s : Finset α) : (#(↑s : Set α)) < ℵ₀ :=
  lt_aleph0_of_finite _
#align cardinal.finset_card_lt_aleph_0 Cardinal.finset_card_lt_aleph0

theorem mk_set_eq_nat_iff_finset {α} {s : Set α} {n : ℕ} :
    (#s) = n ↔ ∃ t : Finset α, (t : Set α) = s ∧ t.card = n :=
  by
  constructor
  · intro h
    lift s to Finset α using lt_aleph_0_iff_set_finite.1 (h.symm ▸ nat_lt_aleph_0 n)
    simpa using h
  · rintro ⟨t, rfl, rfl⟩
    exact mk_coe_finset
#align cardinal.mk_set_eq_nat_iff_finset Cardinal.mk_set_eq_nat_iff_finset

theorem mk_eq_nat_iff_finset {n : ℕ} : (#α) = n ↔ ∃ t : Finset α, (t : Set α) = univ ∧ t.card = n :=
  by rw [← mk_univ, mk_set_eq_nat_iff_finset]
#align cardinal.mk_eq_nat_iff_finset Cardinal.mk_eq_nat_iff_finset

theorem mk_eq_nat_iff_fintype {n : ℕ} : (#α) = n ↔ ∃ h : Fintype α, @Fintype.card α h = n :=
  by
  rw [mk_eq_nat_iff_finset]
  constructor
  · rintro ⟨t, ht, hn⟩
    exact ⟨⟨t, eq_univ_iff_forall.1 ht⟩, hn⟩
  · rintro ⟨⟨t, ht⟩, hn⟩
    exact ⟨t, eq_univ_iff_forall.2 ht, hn⟩
#align cardinal.mk_eq_nat_iff_fintype Cardinal.mk_eq_nat_iff_fintype

theorem mk_union_add_mk_inter {α : Type u} {S T : Set α} :
    (#(S ∪ T : Set α)) + (#(S ∩ T : Set α)) = (#S) + (#T) :=
  Quot.sound ⟨Equiv.Set.unionSumInter S T⟩
#align cardinal.mk_union_add_mk_inter Cardinal.mk_union_add_mk_inter

/-- The cardinality of a union is at most the sum of the cardinalities
of the two sets. -/
theorem mk_union_le {α : Type u} (S T : Set α) : (#(S ∪ T : Set α)) ≤ (#S) + (#T) :=
  @mk_union_add_mk_inter α S T ▸ self_le_add_right (#(S ∪ T : Set α)) (#(S ∩ T : Set α))
#align cardinal.mk_union_le Cardinal.mk_union_le

theorem mk_union_of_disjoint {α : Type u} {S T : Set α} (H : Disjoint S T) :
    (#(S ∪ T : Set α)) = (#S) + (#T) :=
  Quot.sound ⟨Equiv.Set.union H.le_bot⟩
#align cardinal.mk_union_of_disjoint Cardinal.mk_union_of_disjoint

theorem mk_insert {α : Type u} {s : Set α} {a : α} (h : a ∉ s) :
    (#(insert a s : Set α)) = (#s) + 1 :=
  by
  rw [← union_singleton, mk_union_of_disjoint, mk_singleton]
  simpa
#align cardinal.mk_insert Cardinal.mk_insert

theorem mk_sum_compl {α} (s : Set α) : (#s) + (#(sᶜ : Set α)) = (#α) :=
  mk_congr (Equiv.Set.sumCompl s)
#align cardinal.mk_sum_compl Cardinal.mk_sum_compl

theorem mk_le_mk_of_subset {α} {s t : Set α} (h : s ⊆ t) : (#s) ≤ (#t) :=
  ⟨Set.embeddingOfSubset s t h⟩
#align cardinal.mk_le_mk_of_subset Cardinal.mk_le_mk_of_subset

theorem mk_subtype_mono {p q : α → Prop} (h : ∀ x, p x → q x) : (#{ x // p x }) ≤ (#{ x // q x }) :=
  ⟨embeddingOfSubset _ _ h⟩
#align cardinal.mk_subtype_mono Cardinal.mk_subtype_mono

theorem le_mk_diff_add_mk (S T : Set α) : (#S) ≤ (#(S \ T : Set α)) + (#T) :=
  (mk_le_mk_of_subset <| subset_diff_union _ _).trans <| mk_union_le _ _
#align cardinal.le_mk_diff_add_mk Cardinal.le_mk_diff_add_mk

theorem mk_diff_add_mk {S T : Set α} (h : T ⊆ S) : (#(S \ T : Set α)) + (#T) = (#S) :=
  (mk_union_of_disjoint <| disjoint_sdiff_self_left).symm.trans <| by rw [diff_union_of_subset h]
#align cardinal.mk_diff_add_mk Cardinal.mk_diff_add_mk

theorem mk_union_le_aleph0 {α} {P Q : Set α} : (#(P ∪ Q : Set α)) ≤ ℵ₀ ↔ (#P) ≤ ℵ₀ ∧ (#Q) ≤ ℵ₀ := by
  simp
#align cardinal.mk_union_le_aleph_0 Cardinal.mk_union_le_aleph0

theorem mk_image_eq_lift {α : Type u} {β : Type v} (f : α → β) (s : Set α) (h : Injective f) :
    lift.{u} (#f '' s) = lift.{v} (#s) :=
  lift_mk_eq.{v, u, 0}.mpr ⟨(Equiv.Set.image f s h).symm⟩
#align cardinal.mk_image_eq_lift Cardinal.mk_image_eq_lift

theorem mk_image_eq_of_injOn_lift {α : Type u} {β : Type v} (f : α → β) (s : Set α)
    (h : InjOn f s) : lift.{u} (#f '' s) = lift.{v} (#s) :=
  lift_mk_eq.{v, u, 0}.mpr ⟨(Equiv.Set.imageOfInjOn f s h).symm⟩
#align cardinal.mk_image_eq_of_inj_on_lift Cardinal.mk_image_eq_of_injOn_lift

theorem mk_image_eq_of_injOn {α β : Type u} (f : α → β) (s : Set α) (h : InjOn f s) :
    (#f '' s) = (#s) :=
  mk_congr (Equiv.Set.imageOfInjOn f s h).symm
#align cardinal.mk_image_eq_of_inj_on Cardinal.mk_image_eq_of_injOn

theorem mk_subtype_of_equiv {α β : Type u} (p : β → Prop) (e : α ≃ β) :
    (#{ a : α // p (e a) }) = (#{ b : β // p b }) :=
  mk_congr (Equiv.subtypeEquivOfSubtype e)
#align cardinal.mk_subtype_of_equiv Cardinal.mk_subtype_of_equiv

theorem mk_sep (s : Set α) (t : α → Prop) : (#({ x ∈ s | t x } : Set α)) = (#{ x : s | t x.1 }) :=
  mk_congr (Equiv.Set.sep s t)
#align cardinal.mk_sep Cardinal.mk_sep

theorem mk_preimage_of_injective_lift {α : Type u} {β : Type v} (f : α → β) (s : Set β)
    (h : Injective f) : lift.{v} (#f ⁻¹' s) ≤ lift.{u} (#s) :=
  by
  rw [lift_mk_le.{u, v, 0}]; use Subtype.coind (fun x => f x.1) fun x => x.2
  apply Subtype.coind_injective; exact h.comp Subtype.val_injective
#align cardinal.mk_preimage_of_injective_lift Cardinal.mk_preimage_of_injective_lift

theorem mk_preimage_of_subset_range_lift {α : Type u} {β : Type v} (f : α → β) (s : Set β)
    (h : s ⊆ range f) : lift.{u} (#s) ≤ lift.{v} (#f ⁻¹' s) :=
  by
  rw [lift_mk_le.{v, u, 0}]
  refine' ⟨⟨_, _⟩⟩
  · rintro ⟨y, hy⟩
    rcases Classical.subtype_of_exists (h hy) with ⟨x, rfl⟩
    exact ⟨x, hy⟩
  rintro ⟨y, hy⟩ ⟨y', hy'⟩; dsimp
  rcases Classical.subtype_of_exists (h hy) with ⟨x, rfl⟩
  rcases Classical.subtype_of_exists (h hy') with ⟨x', rfl⟩
  simp; intro hxx'; rw [hxx']
#align cardinal.mk_preimage_of_subset_range_lift Cardinal.mk_preimage_of_subset_range_lift

theorem mk_preimage_of_injective_of_subset_range_lift {β : Type v} (f : α → β) (s : Set β)
    (h : Injective f) (h2 : s ⊆ range f) : lift.{v} (#f ⁻¹' s) = lift.{u} (#s) :=
  le_antisymm (mk_preimage_of_injective_lift f s h) (mk_preimage_of_subset_range_lift f s h2)
#align cardinal.mk_preimage_of_injective_of_subset_range_lift Cardinal.mk_preimage_of_injective_of_subset_range_lift

theorem mk_preimage_of_injective (f : α → β) (s : Set β) (h : Injective f) : (#f ⁻¹' s) ≤ (#s) := by
  convert mk_preimage_of_injective_lift.{u, u} f s h using 1 <;> rw [lift_id]
#align cardinal.mk_preimage_of_injective Cardinal.mk_preimage_of_injective

theorem mk_preimage_of_subset_range (f : α → β) (s : Set β) (h : s ⊆ range f) : (#s) ≤ (#f ⁻¹' s) :=
  by convert mk_preimage_of_subset_range_lift.{u, u} f s h using 1 <;> rw [lift_id]
#align cardinal.mk_preimage_of_subset_range Cardinal.mk_preimage_of_subset_range

theorem mk_preimage_of_injective_of_subset_range (f : α → β) (s : Set β) (h : Injective f)
    (h2 : s ⊆ range f) : (#f ⁻¹' s) = (#s) := by
  convert mk_preimage_of_injective_of_subset_range_lift.{u, u} f s h h2 using 1 <;> rw [lift_id]
#align cardinal.mk_preimage_of_injective_of_subset_range Cardinal.mk_preimage_of_injective_of_subset_range

theorem mk_subset_ge_of_subset_image_lift {α : Type u} {β : Type v} (f : α → β) {s : Set α}
    {t : Set β} (h : t ⊆ f '' s) : lift.{u} (#t) ≤ lift.{v} (#({ x ∈ s | f x ∈ t } : Set α)) :=
  by
  rw [image_eq_range] at h
  convert mk_preimage_of_subset_range_lift _ _ h using 1
  rw [mk_sep]
  rfl
#align cardinal.mk_subset_ge_of_subset_image_lift Cardinal.mk_subset_ge_of_subset_image_lift

theorem mk_subset_ge_of_subset_image (f : α → β) {s : Set α} {t : Set β} (h : t ⊆ f '' s) :
    (#t) ≤ (#({ x ∈ s | f x ∈ t } : Set α)) :=
  by
  rw [image_eq_range] at h
  convert mk_preimage_of_subset_range _ _ h using 1
  rw [mk_sep]
  rfl
#align cardinal.mk_subset_ge_of_subset_image Cardinal.mk_subset_ge_of_subset_image

theorem le_mk_iff_exists_subset {c : Cardinal} {α : Type u} {s : Set α} :
    c ≤ (#s) ↔ ∃ p : Set α, p ⊆ s ∧ (#p) = c :=
  by
  rw [le_mk_iff_exists_set, ← Subtype.exists_set_subtype]
  apply exists_congr; intro t; rw [mk_image_eq]; apply Subtype.val_injective
#align cardinal.le_mk_iff_exists_subset Cardinal.le_mk_iff_exists_subset

theorem two_le_iff : (2 : Cardinal) ≤ (#α) ↔ ∃ x y : α, x ≠ y := by
  rw [← Nat.cast_two, nat_succ, succ_le_iff, Nat.cast_one, one_lt_iff_nontrivial, nontrivial_iff]
#align cardinal.two_le_iff Cardinal.two_le_iff

theorem two_le_iff' (x : α) : (2 : Cardinal) ≤ (#α) ↔ ∃ y : α, y ≠ x := by
  rw [two_le_iff, ← nontrivial_iff, nontrivial_iff_exists_ne x]
#align cardinal.two_le_iff' Cardinal.two_le_iff'

theorem mk_eq_two_iff : (#α) = 2 ↔ ∃ x y : α, x ≠ y ∧ ({x, y} : Set α) = univ :=
  by
  simp only [← @Nat.cast_two Cardinal, mk_eq_nat_iff_finset, Finset.card_eq_two]
  constructor
  · rintro ⟨t, ht, x, y, hne, rfl⟩
    exact ⟨x, y, hne, by simpa using ht⟩
  · rintro ⟨x, y, hne, h⟩
    exact ⟨{x, y}, by simpa using h, x, y, hne, rfl⟩
#align cardinal.mk_eq_two_iff Cardinal.mk_eq_two_iff

theorem mk_eq_two_iff' (x : α) : (#α) = 2 ↔ ∃! y, y ≠ x :=
  by
  rw [mk_eq_two_iff]; constructor
  · rintro ⟨a, b, hne, h⟩
    simp only [eq_univ_iff_forall, mem_insert_iff, mem_singleton_iff] at h
    rcases h x with (rfl | rfl)
    exacts[⟨b, hne.symm, fun z => (h z).resolve_left⟩, ⟨a, hne, fun z => (h z).resolve_right⟩]
  · rintro ⟨y, hne, hy⟩
    exact ⟨x, y, hne.symm, eq_univ_of_forall fun z => or_iff_not_imp_left.2 (hy z)⟩
#align cardinal.mk_eq_two_iff' Cardinal.mk_eq_two_iff'

theorem exists_not_mem_of_length_lt {α : Type _} (l : List α) (h : ↑l.length < (#α)) :
    ∃ z : α, z ∉ l := by
  contrapose! h
  calc
    (#α) = (#(Set.univ : Set α)) := mk_univ.symm
    _ ≤ (#l.to_finset) := mk_le_mk_of_subset fun x _ => list.mem_to_finset.mpr (h x)
    _ = l.to_finset.card := Cardinal.mk_coe_finset
    _ ≤ l.length := cardinal.nat_cast_le.mpr (List.toFinset_card_le l)
    
#align cardinal.exists_not_mem_of_length_lt Cardinal.exists_not_mem_of_length_lt

theorem three_le {α : Type _} (h : 3 ≤ (#α)) (x : α) (y : α) : ∃ z : α, z ≠ x ∧ z ≠ y :=
  by
  have : ↑(3 : ℕ) ≤ (#α); simpa using h
  have : ↑(2 : ℕ) < (#α); rwa [← succ_le_iff, ← Cardinal.nat_succ]
  have := exists_not_mem_of_length_lt [x, y] this
  simpa [not_or] using this
#align cardinal.three_le Cardinal.three_le

/-- The function `a ^< b`, defined as the supremum of `a ^ c` for `c < b`. -/
def powerlt (a b : Cardinal.{u}) : Cardinal.{u} :=
  ⨆ c : Iio b, a^c
#align cardinal.powerlt Cardinal.powerlt

-- mathport name: «expr ^< »
infixl:80 " ^< " => powerlt

theorem le_powerlt {b c : Cardinal.{u}} (a) (h : c < b) : (a^c) ≤ a ^< b :=
  by
  apply @le_csupᵢ _ _ _ (fun y : Iio b => a^y) _ ⟨c, h⟩
  rw [← image_eq_range]
  exact bddAbove_image.{u, u} _ bddAbove_Iio
#align cardinal.le_powerlt Cardinal.le_powerlt

theorem powerlt_le {a b c : Cardinal.{u}} : a ^< b ≤ c ↔ ∀ x < b, (a^x) ≤ c :=
  by
  rw [powerlt, csupᵢ_le_iff']
  · simp
  · rw [← image_eq_range]
    exact bddAbove_image.{u, u} _ bddAbove_Iio
#align cardinal.powerlt_le Cardinal.powerlt_le

theorem powerlt_le_powerlt_left {a b c : Cardinal} (h : b ≤ c) : a ^< b ≤ a ^< c :=
  powerlt_le.2 fun x hx => le_powerlt a <| hx.trans_le h
#align cardinal.powerlt_le_powerlt_left Cardinal.powerlt_le_powerlt_left

theorem powerlt_mono_left (a) : Monotone fun c => a ^< c := fun b c => powerlt_le_powerlt_left
#align cardinal.powerlt_mono_left Cardinal.powerlt_mono_left

theorem powerlt_succ {a b : Cardinal} (h : a ≠ 0) : a ^< succ b = (a^b) :=
  (powerlt_le.2 fun c h' => power_le_power_left h <| le_of_lt_succ h').antisymm <|
    le_powerlt a (lt_succ b)
#align cardinal.powerlt_succ Cardinal.powerlt_succ

theorem powerlt_min {a b c : Cardinal} : a ^< min b c = min (a ^< b) (a ^< c) :=
  (powerlt_mono_left a).map_min
#align cardinal.powerlt_min Cardinal.powerlt_min

theorem powerlt_max {a b c : Cardinal} : a ^< max b c = max (a ^< b) (a ^< c) :=
  (powerlt_mono_left a).map_max
#align cardinal.powerlt_max Cardinal.powerlt_max

theorem zero_powerlt {a : Cardinal} (h : a ≠ 0) : 0 ^< a = 1 :=
  by
  apply (powerlt_le.2 fun c hc => zero_power_le _).antisymm
  rw [← power_zero]
  exact le_powerlt 0 (pos_iff_ne_zero.2 h)
#align cardinal.zero_powerlt Cardinal.zero_powerlt

@[simp]
theorem powerlt_zero {a : Cardinal} : a ^< 0 = 0 :=
  by
  convert Cardinal.supᵢ_of_empty _
  exact Subtype.isEmpty_of_false fun x => (Cardinal.zero_le _).not_lt
#align cardinal.powerlt_zero Cardinal.powerlt_zero

end Cardinal

namespace Tactic

open Cardinal Positivity

/-- Extension for the `positivity` tactic: The cardinal power of a positive cardinal is positive. -/
@[positivity]
unsafe def positivity_cardinal_pow : expr → tactic strictness
  | q(@Pow.pow _ _ $(inst) $(a) $(b)) => do
    let strictness_a ← core a
    match strictness_a with
      | positive p => positive <$> mk_app `` power_pos [b, p]
      | _ => failed
  |-- We already know that `0 ≤ x` for all `x : cardinal`
    _ =>
    failed
#align tactic.positivity_cardinal_pow tactic.positivity_cardinal_pow

end Tactic

