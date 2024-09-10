/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Countable
import Mathlib.Logic.Small.Set
import Mathlib.Order.SuccPred.CompleteLinearOrder
import Mathlib.SetTheory.Cardinal.SchroederBernstein
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# Cardinal Numbers

We define cardinal numbers as a quotient of types under the equivalence relation of equinumerity.

## Main definitions

* `Cardinal` is the type of cardinal numbers (in a given universe).
* `Cardinal.mk α` or `#α` is the cardinality of `α`. The notation `#` lives in the locale
  `Cardinal`.
* Addition `c₁ + c₂` is defined by `Cardinal.add_def α β : #α + #β = #(α ⊕ β)`.
* Multiplication `c₁ * c₂` is defined by `Cardinal.mul_def : #α * #β = #(α × β)`.
* The order `c₁ ≤ c₂` is defined by `Cardinal.le_def α β : #α ≤ #β ↔ Nonempty (α ↪ β)`.
* Exponentiation `c₁ ^ c₂` is defined by `Cardinal.power_def α β : #α ^ #β = #(β → α)`.
* `Cardinal.isLimit c` means that `c` is a (weak) limit cardinal: `c ≠ 0 ∧ ∀ x < c, succ x < c`.
* `Cardinal.aleph0` or `ℵ₀` is the cardinality of `ℕ`. This definition is universe polymorphic:
  `Cardinal.aleph0.{u} : Cardinal.{u}` (contrast with `ℕ : Type`, which lives in a specific
  universe). In some cases the universe level has to be given explicitly.
* `Cardinal.sum` is the sum of an indexed family of cardinals, i.e. the cardinality of the
  corresponding sigma type.
* `Cardinal.prod` is the product of an indexed family of cardinals, i.e. the cardinality of the
  corresponding pi type.
* `Cardinal.powerlt a b` or `a ^< b` is defined as the supremum of `a ^ c` for `c < b`.

## Main instances

* Cardinals form a `CanonicallyOrderedCommSemiring` with the aforementioned sum and product.
* Cardinals form a `SuccOrder`. Use `Order.succ c` for the smallest cardinal greater than `c`.
* The less than relation on cardinals forms a well-order.
* Cardinals form a `ConditionallyCompleteLinearOrderBot`. Bounded sets for cardinals in universe
  `u` are precisely the sets indexed by some type in universe `u`, see
  `Cardinal.bddAbove_iff_small`. One can use `sSup` for the cardinal supremum, and `sInf` for the
  minimum of a set of cardinals.

## Main Statements

* Cantor's theorem: `Cardinal.cantor c : c < 2 ^ c`.
* König's theorem: `Cardinal.sum_lt_prod`

## Implementation notes

* There is a type of cardinal numbers in every universe level:
  `Cardinal.{u} : Type (u + 1)` is the quotient of types in `Type u`.
  The operation `Cardinal.lift` lifts cardinal numbers to a higher level.
* Cardinal arithmetic specifically for infinite cardinals (like `κ * κ = κ`) is in the file
  `Mathlib/SetTheory/Cardinal/Ordinal.lean`.
* There is an instance `Pow Cardinal`, but this will only fire if Lean already knows that both
  the base and the exponent live in the same universe. As a workaround, you can add
  ```
    local infixr:80 " ^' " => @HPow.hPow Cardinal Cardinal Cardinal _
  ```
  to a file. This notation will work even if Lean doesn't know yet that the base and the exponent
  live in the same universe (but no exponents in other types can be used).
  (Porting note: This last point might need to be updated.)

## References

* <https://en.wikipedia.org/wiki/Cardinal_number>

## Tags

cardinal number, cardinal arithmetic, cardinal exponentiation, aleph,
Cantor's theorem, König's theorem, Konig's theorem
-/

assert_not_exists Field

open Mathlib (Vector)
open Function Set Order

noncomputable section

universe u v w

variable {α β : Type u}

/-- The equivalence relation on types given by equivalence (bijective correspondence) of types.
  Quotienting by this equivalence relation gives the cardinal numbers.
-/
instance Cardinal.isEquivalent : Setoid (Type u) where
  r α β := Nonempty (α ≃ β)
  iseqv := ⟨
    fun α => ⟨Equiv.refl α⟩,
    fun ⟨e⟩ => ⟨e.symm⟩,
    fun ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩⟩

/-- `Cardinal.{u}` is the type of cardinal numbers in `Type u`,
  defined as the quotient of `Type u` by existence of an equivalence
  (a bijection with explicit inverse). -/
@[pp_with_univ]
def Cardinal : Type (u + 1) :=
  Quotient Cardinal.isEquivalent

namespace Cardinal

/-- The cardinal number of a type -/
def mk : Type u → Cardinal :=
  Quotient.mk'

@[inherit_doc]
scoped prefix:max "#" => Cardinal.mk

instance canLiftCardinalType : CanLift Cardinal.{u} (Type u) mk fun _ => True :=
  ⟨fun c _ => Quot.inductionOn c fun α => ⟨α, rfl⟩⟩

@[elab_as_elim]
theorem inductionOn {p : Cardinal → Prop} (c : Cardinal) (h : ∀ α, p #α) : p c :=
  Quotient.inductionOn c h

@[elab_as_elim]
theorem inductionOn₂ {p : Cardinal → Cardinal → Prop} (c₁ : Cardinal) (c₂ : Cardinal)
    (h : ∀ α β, p #α #β) : p c₁ c₂ :=
  Quotient.inductionOn₂ c₁ c₂ h

@[elab_as_elim]
theorem inductionOn₃ {p : Cardinal → Cardinal → Cardinal → Prop} (c₁ : Cardinal) (c₂ : Cardinal)
    (c₃ : Cardinal) (h : ∀ α β γ, p #α #β #γ) : p c₁ c₂ c₃ :=
  Quotient.inductionOn₃ c₁ c₂ c₃ h

protected theorem eq : #α = #β ↔ Nonempty (α ≃ β) :=
  Quotient.eq'

@[simp]
theorem mk'_def (α : Type u) : @Eq Cardinal ⟦α⟧ #α :=
  rfl

@[simp]
theorem mk_out (c : Cardinal) : #c.out = c :=
  Quotient.out_eq _

/-- The representative of the cardinal of a type is equivalent to the original type. -/
def outMkEquiv {α : Type v} : (#α).out ≃ α :=
  Nonempty.some <| Cardinal.eq.mp (by simp)

theorem mk_congr (e : α ≃ β) : #α = #β :=
  Quot.sound ⟨e⟩

alias _root_.Equiv.cardinal_eq := mk_congr

/-- Lift a function between `Type*`s to a function between `Cardinal`s. -/
def map (f : Type u → Type v) (hf : ∀ α β, α ≃ β → f α ≃ f β) : Cardinal.{u} → Cardinal.{v} :=
  Quotient.map f fun α β ⟨e⟩ => ⟨hf α β e⟩

@[simp]
theorem map_mk (f : Type u → Type v) (hf : ∀ α β, α ≃ β → f α ≃ f β) (α : Type u) :
    map f hf #α = #(f α) :=
  rfl

/-- Lift a binary operation `Type* → Type* → Type*` to a binary operation on `Cardinal`s. -/
def map₂ (f : Type u → Type v → Type w) (hf : ∀ α β γ δ, α ≃ β → γ ≃ δ → f α γ ≃ f β δ) :
    Cardinal.{u} → Cardinal.{v} → Cardinal.{w} :=
  Quotient.map₂ f fun α β ⟨e₁⟩ γ δ ⟨e₂⟩ => ⟨hf α β γ δ e₁ e₂⟩

/-- The universe lift operation on cardinals. You can specify the universes explicitly with
  `lift.{u v} : Cardinal.{v} → Cardinal.{max v u}` -/
@[pp_with_univ]
def lift (c : Cardinal.{v}) : Cardinal.{max v u} :=
  map ULift.{u, v} (fun _ _ e => Equiv.ulift.trans <| e.trans Equiv.ulift.symm) c

@[simp]
theorem mk_uLift (α) : #(ULift.{v, u} α) = lift.{v} #α :=
  rfl

-- Porting note: simpNF is not happy with universe levels, but this is needed as simp lemma
-- further down in this file
/-- `lift.{max u v, u}` equals `lift.{v, u}`. -/
@[simp, nolint simpNF]
theorem lift_umax : lift.{max u v, u} = lift.{v, u} :=
  funext fun a => inductionOn a fun _ => (Equiv.ulift.trans Equiv.ulift.symm).cardinal_eq

-- Porting note: simpNF is not happy with universe levels, but this is needed as simp lemma
-- further down in this file
/-- `lift.{max v u, u}` equals `lift.{v, u}`. -/
@[simp, nolint simpNF]
theorem lift_umax' : lift.{max v u, u} = lift.{v, u} :=
  lift_umax

-- Porting note: simpNF is not happy with universe levels, but this is needed as simp lemma
-- further down in this file
/-- A cardinal lifted to a lower or equal universe equals itself. -/
@[simp, nolint simpNF]
theorem lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a :=
  inductionOn a fun _ => mk_congr Equiv.ulift

/-- A cardinal lifted to the same universe equals itself. -/
@[simp]
theorem lift_id (a : Cardinal) : lift.{u, u} a = a :=
  lift_id'.{u, u} a

/-- A cardinal lifted to the zero universe equals itself. -/
-- porting note (#10618): simp can prove this
-- @[simp]
theorem lift_uzero (a : Cardinal.{u}) : lift.{0} a = a :=
  lift_id'.{0, u} a

@[simp]
theorem lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lift.{v} a) = lift.{max v w} a :=
  inductionOn a fun _ => (Equiv.ulift.trans <| Equiv.ulift.trans Equiv.ulift.symm).cardinal_eq

/-- We define the order on cardinal numbers by `#α ≤ #β` if and only if
  there exists an embedding (injective function) from α to β. -/
instance : LE Cardinal.{u} :=
  ⟨fun q₁ q₂ =>
    Quotient.liftOn₂ q₁ q₂ (fun α β => Nonempty <| α ↪ β) fun _ _ _ _ ⟨e₁⟩ ⟨e₂⟩ =>
      propext ⟨fun ⟨e⟩ => ⟨e.congr e₁ e₂⟩, fun ⟨e⟩ => ⟨e.congr e₁.symm e₂.symm⟩⟩⟩

instance partialOrder : PartialOrder Cardinal.{u} where
  le := (· ≤ ·)
  le_refl := by
    rintro ⟨α⟩
    exact ⟨Embedding.refl _⟩
  le_trans := by
    rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨e₁⟩ ⟨e₂⟩
    exact ⟨e₁.trans e₂⟩
  le_antisymm := by
    rintro ⟨α⟩ ⟨β⟩ ⟨e₁⟩ ⟨e₂⟩
    exact Quotient.sound (e₁.antisymm e₂)

instance linearOrder : LinearOrder Cardinal.{u} :=
  { Cardinal.partialOrder with
    le_total := by
      rintro ⟨α⟩ ⟨β⟩
      apply Embedding.total
    decidableLE := Classical.decRel _ }

theorem le_def (α β : Type u) : #α ≤ #β ↔ Nonempty (α ↪ β) :=
  Iff.rfl

theorem mk_le_of_injective {α β : Type u} {f : α → β} (hf : Injective f) : #α ≤ #β :=
  ⟨⟨f, hf⟩⟩

theorem _root_.Function.Embedding.cardinal_le {α β : Type u} (f : α ↪ β) : #α ≤ #β :=
  ⟨f⟩

theorem mk_le_of_surjective {α β : Type u} {f : α → β} (hf : Surjective f) : #β ≤ #α :=
  ⟨Embedding.ofSurjective f hf⟩

theorem le_mk_iff_exists_set {c : Cardinal} {α : Type u} : c ≤ #α ↔ ∃ p : Set α, #p = c :=
  ⟨inductionOn c fun _ ⟨⟨f, hf⟩⟩ => ⟨Set.range f, (Equiv.ofInjective f hf).cardinal_eq.symm⟩,
    fun ⟨_, e⟩ => e ▸ ⟨⟨Subtype.val, fun _ _ => Subtype.eq⟩⟩⟩

theorem mk_subtype_le {α : Type u} (p : α → Prop) : #(Subtype p) ≤ #α :=
  ⟨Embedding.subtype p⟩

theorem mk_set_le (s : Set α) : #s ≤ #α :=
  mk_subtype_le s

@[simp]
lemma mk_preimage_down {s : Set α} : #(ULift.down.{v} ⁻¹' s) = lift.{v} (#s) := by
  rw [← mk_uLift, Cardinal.eq]
  constructor
  let f : ULift.down ⁻¹' s → ULift s := fun x ↦ ULift.up (restrictPreimage s ULift.down x)
  have : Function.Bijective f :=
    ULift.up_bijective.comp (restrictPreimage_bijective _ (ULift.down_bijective))
  exact Equiv.ofBijective f this

theorem out_embedding {c c' : Cardinal} : c ≤ c' ↔ Nonempty (c.out ↪ c'.out) := by
  trans
  · rw [← Quotient.out_eq c, ← Quotient.out_eq c']
  · rw [mk'_def, mk'_def, le_def]

theorem lift_mk_le {α : Type v} {β : Type w} :
    lift.{max u w} #α ≤ lift.{max u v} #β ↔ Nonempty (α ↪ β) :=
  ⟨fun ⟨f⟩ => ⟨Embedding.congr Equiv.ulift Equiv.ulift f⟩, fun ⟨f⟩ =>
    ⟨Embedding.congr Equiv.ulift.symm Equiv.ulift.symm f⟩⟩

/-- A variant of `Cardinal.lift_mk_le` with specialized universes.
Because Lean often can not realize it should use this specialization itself,
we provide this statement separately so you don't have to solve the specialization problem either.
-/
theorem lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #α ≤ lift.{u} #β ↔ Nonempty (α ↪ β) :=
  lift_mk_le.{0}

theorem lift_mk_eq {α : Type u} {β : Type v} :
    lift.{max v w} #α = lift.{max u w} #β ↔ Nonempty (α ≃ β) :=
  Quotient.eq'.trans
    ⟨fun ⟨f⟩ => ⟨Equiv.ulift.symm.trans <| f.trans Equiv.ulift⟩, fun ⟨f⟩ =>
      ⟨Equiv.ulift.trans <| f.trans Equiv.ulift.symm⟩⟩

/-- A variant of `Cardinal.lift_mk_eq` with specialized universes.
Because Lean often can not realize it should use this specialization itself,
we provide this statement separately so you don't have to solve the specialization problem either.
-/
theorem lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #α = lift.{u} #β ↔ Nonempty (α ≃ β) :=
  lift_mk_eq.{u, v, 0}

@[simp]
theorem lift_le {a b : Cardinal.{v}} : lift.{u, v} a ≤ lift.{u, v} b ↔ a ≤ b :=
  inductionOn₂ a b fun α β => by
    rw [← lift_umax]
    exact lift_mk_le.{u}

-- Porting note: changed `simps` to `simps!` because the linter told to do so.
/-- `Cardinal.lift` as an `OrderEmbedding`. -/
@[simps! (config := .asFn)]
def liftOrderEmbedding : Cardinal.{v} ↪o Cardinal.{max v u} :=
  OrderEmbedding.ofMapLEIff lift.{u, v} fun _ _ => lift_le

theorem lift_injective : Injective lift.{u, v} :=
  liftOrderEmbedding.injective

@[simp]
theorem lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.{v, u} b ↔ a = b :=
  lift_injective.eq_iff

@[simp]
theorem lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v, u} b ↔ a < b :=
  liftOrderEmbedding.lt_iff_lt

theorem lift_strictMono : StrictMono lift := fun _ _ => lift_lt.2

theorem lift_monotone : Monotone lift :=
  lift_strictMono.monotone

instance : Zero Cardinal.{u} :=
  -- `PEmpty` might be more canonical, but this is convenient for defeq with natCast
  ⟨lift #(Fin 0)⟩

instance : Inhabited Cardinal.{u} :=
  ⟨0⟩

@[simp]
theorem mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0 :=
  (Equiv.equivOfIsEmpty α (ULift (Fin 0))).cardinal_eq

@[simp]
theorem lift_zero : lift 0 = 0 := mk_eq_zero _

@[simp]
theorem lift_eq_zero {a : Cardinal.{v}} : lift.{u} a = 0 ↔ a = 0 :=
  lift_injective.eq_iff' lift_zero

theorem mk_eq_zero_iff {α : Type u} : #α = 0 ↔ IsEmpty α :=
  ⟨fun e =>
    let ⟨h⟩ := Quotient.exact e
    h.isEmpty,
    @mk_eq_zero α⟩

theorem mk_ne_zero_iff {α : Type u} : #α ≠ 0 ↔ Nonempty α :=
  (not_iff_not.2 mk_eq_zero_iff).trans not_isEmpty_iff

@[simp]
theorem mk_ne_zero (α : Type u) [Nonempty α] : #α ≠ 0 :=
  mk_ne_zero_iff.2 ‹_›

instance : One Cardinal.{u} :=
  -- `PUnit` might be more canonical, but this is convenient for defeq with natCast
  ⟨lift #(Fin 1)⟩

instance : Nontrivial Cardinal.{u} :=
  ⟨⟨1, 0, mk_ne_zero _⟩⟩

theorem mk_eq_one (α : Type u) [Unique α] : #α = 1 :=
  (Equiv.equivOfUnique α (ULift (Fin 1))).cardinal_eq

theorem le_one_iff_subsingleton {α : Type u} : #α ≤ 1 ↔ Subsingleton α :=
  ⟨fun ⟨f⟩ => ⟨fun _ _ => f.injective (Subsingleton.elim _ _)⟩, fun ⟨h⟩ =>
    ⟨fun _ => ULift.up 0, fun _ _ _ => h _ _⟩⟩

@[simp]
theorem mk_le_one_iff_set_subsingleton {s : Set α} : #s ≤ 1 ↔ s.Subsingleton :=
  le_one_iff_subsingleton.trans s.subsingleton_coe

alias ⟨_, _root_.Set.Subsingleton.cardinal_mk_le_one⟩ := mk_le_one_iff_set_subsingleton

instance : Add Cardinal.{u} :=
  ⟨map₂ Sum fun _ _ _ _ => Equiv.sumCongr⟩

theorem add_def (α β : Type u) : #α + #β = #(α ⊕ β) :=
  rfl

instance : NatCast Cardinal.{u} :=
  ⟨fun n => lift #(Fin n)⟩

@[simp]
theorem mk_sum (α : Type u) (β : Type v) : #(α ⊕ β) = lift.{v, u} #α + lift.{u, v} #β :=
  mk_congr (Equiv.ulift.symm.sumCongr Equiv.ulift.symm)

@[simp]
theorem mk_option {α : Type u} : #(Option α) = #α + 1 := by
  rw [(Equiv.optionEquivSumPUnit.{u, u} α).cardinal_eq, mk_sum, mk_eq_one PUnit, lift_id, lift_id]

@[simp]
theorem mk_psum (α : Type u) (β : Type v) : #(α ⊕' β) = lift.{v} #α + lift.{u} #β :=
  (mk_congr (Equiv.psumEquivSum α β)).trans (mk_sum α β)

@[simp]
theorem mk_fintype (α : Type u) [h : Fintype α] : #α = Fintype.card α :=
  mk_congr (Fintype.equivOfCardEq (by simp))

protected theorem cast_succ (n : ℕ) : ((n + 1 : ℕ) : Cardinal.{u}) = n + 1 := by
  change #(ULift.{u} (Fin (n+1))) = # (ULift.{u} (Fin n)) + 1
  rw [← mk_option, mk_fintype, mk_fintype]
  simp only [Fintype.card_ulift, Fintype.card_fin, Fintype.card_option]

instance : Mul Cardinal.{u} :=
  ⟨map₂ Prod fun _ _ _ _ => Equiv.prodCongr⟩

theorem mul_def (α β : Type u) : #α * #β = #(α × β) :=
  rfl

@[simp]
theorem mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v, u} #α * lift.{u, v} #β :=
  mk_congr (Equiv.ulift.symm.prodCongr Equiv.ulift.symm)

private theorem mul_comm' (a b : Cardinal.{u}) : a * b = b * a :=
  inductionOn₂ a b fun α β => mk_congr <| Equiv.prodComm α β

/-- The cardinal exponential. `#α ^ #β` is the cardinal of `β → α`. -/
instance instPowCardinal : Pow Cardinal.{u} Cardinal.{u} :=
  ⟨map₂ (fun α β => β → α) fun _ _ _ _ e₁ e₂ => e₂.arrowCongr e₁⟩

theorem power_def (α β : Type u) : #α ^ #β = #(β → α) :=
  rfl

theorem mk_arrow (α : Type u) (β : Type v) : #(α → β) = (lift.{u} #β^lift.{v} #α) :=
  mk_congr (Equiv.ulift.symm.arrowCongr Equiv.ulift.symm)

@[simp]
theorem lift_power (a b : Cardinal.{u}) : lift.{v} (a ^ b) = lift.{v} a ^ lift.{v} b :=
  inductionOn₂ a b fun _ _ =>
    mk_congr <| Equiv.ulift.trans (Equiv.ulift.arrowCongr Equiv.ulift).symm

@[simp]
theorem power_zero {a : Cardinal} : a ^ (0 : Cardinal) = 1 :=
  inductionOn a fun _ => mk_eq_one _

@[simp]
theorem power_one {a : Cardinal.{u}} : a ^ (1 : Cardinal) = a :=
  inductionOn a fun α => mk_congr (Equiv.funUnique (ULift.{u} (Fin 1)) α)

theorem power_add {a b c : Cardinal} : a ^ (b + c) = a ^ b * a ^ c :=
  inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.sumArrowEquivProdArrow β γ α

instance commSemiring : CommSemiring Cardinal.{u} where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  zero_add a := inductionOn a fun α => mk_congr <| Equiv.emptySum (ULift (Fin 0)) α
  add_zero a := inductionOn a fun α => mk_congr <| Equiv.sumEmpty α (ULift (Fin 0))
  add_assoc a b c := inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.sumAssoc α β γ
  add_comm a b := inductionOn₂ a b fun α β => mk_congr <| Equiv.sumComm α β
  zero_mul a := inductionOn a fun α => mk_eq_zero _
  mul_zero a := inductionOn a fun α => mk_eq_zero _
  one_mul a := inductionOn a fun α => mk_congr <| Equiv.uniqueProd α (ULift (Fin 1))
  mul_one a := inductionOn a fun α => mk_congr <| Equiv.prodUnique α (ULift (Fin 1))
  mul_assoc a b c := inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.prodAssoc α β γ
  mul_comm := mul_comm'
  left_distrib a b c := inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.prodSumDistrib α β γ
  right_distrib a b c := inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.sumProdDistrib α β γ
  nsmul := nsmulRec
  npow n c := c ^ (n : Cardinal)
  npow_zero := @power_zero
  npow_succ n c := show c ^ (↑(n + 1) : Cardinal) = c ^ (↑n : Cardinal) * c
    by rw [Cardinal.cast_succ, power_add, power_one, mul_comm']
  natCast := (fun n => lift.{u} #(Fin n) : ℕ → Cardinal.{u})
  natCast_zero := rfl
  natCast_succ := Cardinal.cast_succ

@[simp]
theorem one_power {a : Cardinal} : (1 : Cardinal) ^ a = 1 :=
  inductionOn a fun _ => mk_eq_one _

-- porting note (#10618): simp can prove this
-- @[simp]
theorem mk_bool : #Bool = 2 := by simp

-- porting note (#10618): simp can prove this
-- @[simp]
theorem mk_Prop : #Prop = 2 := by simp

@[simp]
theorem zero_power {a : Cardinal} : a ≠ 0 → (0 : Cardinal) ^ a = 0 :=
  inductionOn a fun _ heq =>
    mk_eq_zero_iff.2 <|
      isEmpty_pi.2 <|
        let ⟨a⟩ := mk_ne_zero_iff.1 heq
        ⟨a, inferInstance⟩

theorem power_ne_zero {a : Cardinal} (b : Cardinal) : a ≠ 0 → a ^ b ≠ 0 :=
  inductionOn₂ a b fun _ _ h =>
    let ⟨a⟩ := mk_ne_zero_iff.1 h
    mk_ne_zero_iff.2 ⟨fun _ => a⟩

theorem mul_power {a b c : Cardinal} : (a * b) ^ c = a ^ c * b ^ c :=
  inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.arrowProdEquivProdArrow α β γ

theorem power_mul {a b c : Cardinal} : a ^ (b * c) = (a ^ b) ^ c := by
  rw [mul_comm b c]
  exact inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.curry γ β α

@[simp]
theorem pow_cast_right (a : Cardinal.{u}) (n : ℕ) : a ^ (↑n : Cardinal.{u}) = a ^ n :=
  rfl

@[simp]
theorem lift_one : lift 1 = 1 := mk_eq_one _

@[simp]
theorem lift_eq_one {a : Cardinal.{v}} : lift.{u} a = 1 ↔ a = 1 :=
  lift_injective.eq_iff' lift_one

@[simp]
theorem lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = lift.{v} a + lift.{v} b :=
  inductionOn₂ a b fun _ _ =>
    mk_congr <| Equiv.ulift.trans (Equiv.sumCongr Equiv.ulift Equiv.ulift).symm

@[simp]
theorem lift_mul (a b : Cardinal.{u}) : lift.{v} (a * b) = lift.{v} a * lift.{v} b :=
  inductionOn₂ a b fun _ _ =>
    mk_congr <| Equiv.ulift.trans (Equiv.prodCongr Equiv.ulift Equiv.ulift).symm

-- Porting note: Proof used to be simp, needed to remind simp that 1 + 1 = 2
theorem lift_two : lift.{u, v} 2 = 2 := by simp [← one_add_one_eq_two]

@[simp]
theorem mk_set {α : Type u} : #(Set α) = 2 ^ #α := by simp [← one_add_one_eq_two, Set, mk_arrow]

/-- A variant of `Cardinal.mk_set` expressed in terms of a `Set` instead of a `Type`. -/
@[simp]
theorem mk_powerset {α : Type u} (s : Set α) : #(↥(𝒫 s)) = 2 ^ #(↥s) :=
  (mk_congr (Equiv.Set.powerset s)).trans mk_set

theorem lift_two_power (a : Cardinal) : lift.{v} (2 ^ a) = 2 ^ lift.{v} a := by
  simp [← one_add_one_eq_two]

section OrderProperties

open Sum

protected theorem zero_le : ∀ a : Cardinal, 0 ≤ a := by
  rintro ⟨α⟩
  exact ⟨Embedding.ofIsEmpty⟩

private theorem add_le_add' : ∀ {a b c d : Cardinal}, a ≤ b → c ≤ d → a + c ≤ b + d := by
  rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨δ⟩ ⟨e₁⟩ ⟨e₂⟩; exact ⟨e₁.sumMap e₂⟩

instance add_covariantClass : CovariantClass Cardinal Cardinal (· + ·) (· ≤ ·) :=
  ⟨fun _ _ _ => add_le_add' le_rfl⟩

instance add_swap_covariantClass : CovariantClass Cardinal Cardinal (swap (· + ·)) (· ≤ ·) :=
  ⟨fun _ _ _ h => add_le_add' h le_rfl⟩

instance canonicallyOrderedCommSemiring : CanonicallyOrderedCommSemiring Cardinal.{u} :=
  { Cardinal.commSemiring,
    Cardinal.partialOrder with
    bot := 0
    bot_le := Cardinal.zero_le
    add_le_add_left := fun a b => add_le_add_left
    exists_add_of_le := fun {a b} =>
      inductionOn₂ a b fun α β ⟨⟨f, hf⟩⟩ =>
        have : α ⊕ ((range f)ᶜ : Set β) ≃ β := by
          classical
          exact (Equiv.sumCongr (Equiv.ofInjective f hf) (Equiv.refl _)).trans <|
            Equiv.Set.sumCompl (range f)
        ⟨#(↥(range f)ᶜ), mk_congr this.symm⟩
    le_self_add := fun a b => (add_zero a).ge.trans <| add_le_add_left (Cardinal.zero_le _) _
    eq_zero_or_eq_zero_of_mul_eq_zero := fun {a b} =>
      inductionOn₂ a b fun α β => by
        simpa only [mul_def, mk_eq_zero_iff, isEmpty_prod] using id }

instance : CanonicallyLinearOrderedAddCommMonoid Cardinal.{u} :=
  { Cardinal.canonicallyOrderedCommSemiring, Cardinal.linearOrder with }

-- Computable instance to prevent a non-computable one being found via the one above
instance : CanonicallyOrderedAddCommMonoid Cardinal.{u} :=
  { Cardinal.canonicallyOrderedCommSemiring with }

instance : LinearOrderedCommMonoidWithZero Cardinal.{u} :=
  { Cardinal.commSemiring,
    Cardinal.linearOrder with
    mul_le_mul_left := @mul_le_mul_left' _ _ _ _
    zero_le_one := zero_le _ }

-- Computable instance to prevent a non-computable one being found via the one above
instance : CommMonoidWithZero Cardinal.{u} :=
  { Cardinal.canonicallyOrderedCommSemiring with }

-- Porting note: new
-- Computable instance to prevent a non-computable one being found via the one above
instance : CommMonoid Cardinal.{u} :=
  { Cardinal.canonicallyOrderedCommSemiring with }

theorem zero_power_le (c : Cardinal.{u}) : (0 : Cardinal.{u}) ^ c ≤ 1 := by
  by_cases h : c = 0
  · rw [h, power_zero]
  · rw [zero_power h]
    apply zero_le

theorem power_le_power_left : ∀ {a b c : Cardinal}, a ≠ 0 → b ≤ c → a ^ b ≤ a ^ c := by
  rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ hα ⟨e⟩
  let ⟨a⟩ := mk_ne_zero_iff.1 hα
  exact ⟨@Function.Embedding.arrowCongrLeft _ _ _ ⟨a⟩ e⟩

theorem self_le_power (a : Cardinal) {b : Cardinal} (hb : 1 ≤ b) : a ≤ a ^ b := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact zero_le _
  · convert power_le_power_left ha hb
    exact power_one.symm

/-- **Cantor's theorem** -/
theorem cantor (a : Cardinal.{u}) : a < 2 ^ a := by
  induction' a using Cardinal.inductionOn with α
  rw [← mk_set]
  refine ⟨⟨⟨singleton, fun a b => singleton_eq_singleton_iff.1⟩⟩, ?_⟩
  rintro ⟨⟨f, hf⟩⟩
  exact cantor_injective f hf

instance : NoMaxOrder Cardinal.{u} where exists_gt a := ⟨_, cantor a⟩

-- short-circuit type class inference
instance : DistribLattice Cardinal.{u} := inferInstance

theorem one_lt_iff_nontrivial {α : Type u} : 1 < #α ↔ Nontrivial α := by
  rw [← not_le, le_one_iff_subsingleton, ← not_nontrivial_iff_subsingleton, Classical.not_not]

theorem power_le_max_power_one {a b c : Cardinal} (h : b ≤ c) : a ^ b ≤ max (a ^ c) 1 := by
  by_cases ha : a = 0
  · simp [ha, zero_power_le]
  · exact (power_le_power_left ha h).trans (le_max_left _ _)

theorem power_le_power_right {a b c : Cardinal} : a ≤ b → a ^ c ≤ b ^ c :=
  inductionOn₃ a b c fun _ _ _ ⟨e⟩ => ⟨Embedding.arrowCongrRight e⟩

theorem power_pos {a : Cardinal} (b : Cardinal) (ha : 0 < a) : 0 < a ^ b :=
  (power_ne_zero _ ha.ne').bot_lt

end OrderProperties

protected theorem lt_wf : @WellFounded Cardinal.{u} (· < ·) :=
  ⟨fun a =>
    by_contradiction fun h => by
      let ι := { c : Cardinal // ¬Acc (· < ·) c }
      let f : ι → Cardinal := Subtype.val
      haveI hι : Nonempty ι := ⟨⟨_, h⟩⟩
      obtain ⟨⟨c : Cardinal, hc : ¬Acc (· < ·) c⟩, ⟨h_1 : ∀ j, (f ⟨c, hc⟩).out ↪ (f j).out⟩⟩ :=
        Embedding.min_injective fun i => (f i).out
      refine hc (Acc.intro _ fun j h' => by_contradiction fun hj => h'.2 ?_)
      have : #_ ≤ #_ := ⟨h_1 ⟨j, hj⟩⟩
      simpa only [mk_out] using this⟩

instance : WellFoundedRelation Cardinal.{u} :=
  ⟨(· < ·), Cardinal.lt_wf⟩

-- Porting note: this no longer is automatically inferred.
instance : WellFoundedLT Cardinal.{u} :=
  ⟨Cardinal.lt_wf⟩

instance wo : @IsWellOrder Cardinal.{u} (· < ·) where

instance : ConditionallyCompleteLinearOrderBot Cardinal :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _

@[simp]
theorem sInf_empty : sInf (∅ : Set Cardinal.{u}) = 0 :=
  dif_neg Set.not_nonempty_empty

lemma sInf_eq_zero_iff {s : Set Cardinal} : sInf s = 0 ↔ s = ∅ ∨ ∃ a ∈ s, a = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases s.eq_empty_or_nonempty with rfl | hne
    · exact Or.inl rfl
    · exact Or.inr ⟨sInf s, csInf_mem hne, h⟩
  · rcases h with rfl | ⟨a, ha, rfl⟩
    · exact Cardinal.sInf_empty
    · exact eq_bot_iff.2 (csInf_le' ha)

lemma iInf_eq_zero_iff {ι : Sort*} {f : ι → Cardinal} :
    (⨅ i, f i) = 0 ↔ IsEmpty ι ∨ ∃ i, f i = 0 := by
  simp [iInf, sInf_eq_zero_iff]

/-- Note that the successor of `c` is not the same as `c + 1` except in the case of finite `c`. -/
instance : SuccOrder Cardinal := ConditionallyCompleteLinearOrder.toSuccOrder

theorem succ_def (c : Cardinal) : succ c = sInf { c' | c < c' } :=
  dif_neg <| not_isMax c

theorem succ_pos : ∀ c : Cardinal, 0 < succ c :=
  bot_lt_succ

theorem succ_ne_zero (c : Cardinal) : succ c ≠ 0 :=
  (succ_pos _).ne'

theorem add_one_le_succ (c : Cardinal.{u}) : c + 1 ≤ succ c := by
  -- Porting note: rewrote the next three lines to avoid defeq abuse.
  have : Set.Nonempty { c' | c < c' } := exists_gt c
  simp_rw [succ_def, le_csInf_iff'' this, mem_setOf]
  intro b hlt
  rcases b, c with ⟨⟨β⟩, ⟨γ⟩⟩
  cases' le_of_lt hlt with f
  have : ¬Surjective f := fun hn => (not_le_of_lt hlt) (mk_le_of_surjective hn)
  simp only [Surjective, not_forall] at this
  rcases this with ⟨b, hb⟩
  calc
    #γ + 1 = #(Option γ) := mk_option.symm
    _ ≤ #β := (f.optionElim b hb).cardinal_le

/-- A cardinal is a limit if it is not zero or a successor cardinal. Note that `ℵ₀` is a limit
  cardinal by this definition, but `0` isn't.

  Use `IsSuccPrelimit` if you want to include the `c = 0` case. -/
def IsLimit (c : Cardinal) : Prop :=
  c ≠ 0 ∧ IsSuccPrelimit c

protected theorem IsLimit.ne_zero {c} (h : IsLimit c) : c ≠ 0 :=
  h.1

protected theorem IsLimit.isSuccPrelimit {c} (h : IsLimit c) : IsSuccPrelimit c :=
  h.2

@[deprecated IsLimit.isSuccPrelimit (since := "2024-09-05")]
alias IsLimit.isSuccLimit := IsLimit.isSuccPrelimit

theorem IsLimit.succ_lt {x c} (h : IsLimit c) : x < c → succ x < c :=
  h.isSuccPrelimit.succ_lt

theorem isSuccPrelimit_zero : IsSuccPrelimit (0 : Cardinal) :=
  isSuccPrelimit_bot

@[deprecated isSuccPrelimit_zero (since := "2024-09-05")]
alias isSuccLimit_zero := isSuccPrelimit_zero

/-- The indexed sum of cardinals is the cardinality of the
  indexed disjoint union, i.e. sigma type. -/
def sum {ι} (f : ι → Cardinal) : Cardinal :=
  mk (Σi, (f i).out)

theorem le_sum {ι} (f : ι → Cardinal) (i) : f i ≤ sum f := by
  rw [← Quotient.out_eq (f i)]
  exact ⟨⟨fun a => ⟨i, a⟩, fun a b h => by injection h⟩⟩

@[simp]
theorem mk_sigma {ι} (f : ι → Type*) : #(Σ i, f i) = sum fun i => #(f i) :=
  mk_congr <| Equiv.sigmaCongrRight fun _ => outMkEquiv.symm

@[simp]
theorem sum_const (ι : Type u) (a : Cardinal.{v}) :
    (sum fun _ : ι => a) = lift.{v} #ι * lift.{u} a :=
  inductionOn a fun α =>
    mk_congr <|
      calc
        (Σ _ : ι, Quotient.out #α) ≃ ι × Quotient.out #α := Equiv.sigmaEquivProd _ _
        _ ≃ ULift ι × ULift α := Equiv.ulift.symm.prodCongr (outMkEquiv.trans Equiv.ulift.symm)

theorem sum_const' (ι : Type u) (a : Cardinal.{u}) : (sum fun _ : ι => a) = #ι * a := by simp

@[simp]
theorem sum_add_distrib {ι} (f g : ι → Cardinal) : sum (f + g) = sum f + sum g := by
  have := mk_congr (Equiv.sigmaSumDistrib (Quotient.out ∘ f) (Quotient.out ∘ g))
  simp only [comp_apply, mk_sigma, mk_sum, mk_out, lift_id] at this
  exact this

@[simp]
theorem sum_add_distrib' {ι} (f g : ι → Cardinal) :
    (Cardinal.sum fun i => f i + g i) = sum f + sum g :=
  sum_add_distrib f g

@[simp]
theorem lift_sum {ι : Type u} (f : ι → Cardinal.{v}) :
    Cardinal.lift.{w} (Cardinal.sum f) = Cardinal.sum fun i => Cardinal.lift.{w} (f i) :=
  Equiv.cardinal_eq <|
    Equiv.ulift.trans <|
      Equiv.sigmaCongrRight fun a =>
    -- Porting note: Inserted universe hint .{_,_,v} below
        Nonempty.some <| by rw [← lift_mk_eq.{_,_,v}, mk_out, mk_out, lift_lift]

theorem sum_le_sum {ι} (f g : ι → Cardinal) (H : ∀ i, f i ≤ g i) : sum f ≤ sum g :=
  ⟨(Embedding.refl _).sigmaMap fun i =>
      Classical.choice <| by have := H i; rwa [← Quot.out_eq (f i), ← Quot.out_eq (g i)] at this⟩

theorem mk_le_mk_mul_of_mk_preimage_le {c : Cardinal} (f : α → β) (hf : ∀ b : β, #(f ⁻¹' {b}) ≤ c) :
    #α ≤ #β * c := by
  simpa only [← mk_congr (@Equiv.sigmaFiberEquiv α β f), mk_sigma, ← sum_const'] using
    sum_le_sum _ _ hf

theorem lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le {α : Type u} {β : Type v} {c : Cardinal}
    (f : α → β) (hf : ∀ b : β, lift.{v} #(f ⁻¹' {b}) ≤ c) : lift.{v} #α ≤ lift.{u} #β * c :=
  (mk_le_mk_mul_of_mk_preimage_le fun x : ULift.{v} α => ULift.up.{u} (f x.1)) <|
    ULift.forall.2 fun b =>
      (mk_congr <|
            (Equiv.ulift.image _).trans
              (Equiv.trans
                (by
                  rw [Equiv.image_eq_preimage]
                  /- Porting note: Need to insert the following `have` b/c bad fun coercion
                   behaviour for Equivs -/
                  have : DFunLike.coe (Equiv.symm (Equiv.ulift (α := α))) = ULift.up (α := α) := rfl
                  rw [this]
                  simp only [preimage, mem_singleton_iff, ULift.up_inj, mem_setOf_eq, coe_setOf]
                  exact Equiv.refl _)
                Equiv.ulift.symm)).trans_le
        (hf b)

/-- The range of an indexed cardinal function, whose outputs live in a higher universe than the
    inputs, is always bounded above. -/
theorem bddAbove_range {ι : Type u} (f : ι → Cardinal.{max u v}) : BddAbove (Set.range f) :=
  ⟨sum f, by
    rintro a ⟨i, rfl⟩
    exact le_sum f i⟩

instance (a : Cardinal.{u}) : Small.{u} (Set.Iic a) := by
  rw [← mk_out a]
  apply @small_of_surjective (Set a.out) (Iic #a.out) _ fun x => ⟨#x, mk_set_le x⟩
  rintro ⟨x, hx⟩
  simpa using le_mk_iff_exists_set.1 hx

instance (a : Cardinal.{u}) : Small.{u} (Set.Iio a) :=
  small_subset Iio_subset_Iic_self

/-- A set of cardinals is bounded above iff it's small, i.e. it corresponds to a usual ZFC set. -/
theorem bddAbove_iff_small {s : Set Cardinal.{u}} : BddAbove s ↔ Small.{u} s :=
  ⟨fun ⟨a, ha⟩ => @small_subset _ (Iic a) s (fun x h => ha h) _, by
    rintro ⟨ι, ⟨e⟩⟩
    suffices (range fun x : ι => (e.symm x).1) = s by
      rw [← this]
      apply bddAbove_range.{u, u}
    ext x
    refine ⟨?_, fun hx => ⟨e ⟨x, hx⟩, ?_⟩⟩
    · rintro ⟨a, rfl⟩
      exact (e.symm a).2
    · simp_rw [Equiv.symm_apply_apply]⟩

theorem bddAbove_of_small (s : Set Cardinal.{u}) [h : Small.{u} s] : BddAbove s :=
  bddAbove_iff_small.2 h

theorem bddAbove_image (f : Cardinal.{u} → Cardinal.{max u v}) {s : Set Cardinal.{u}}
    (hs : BddAbove s) : BddAbove (f '' s) := by
  rw [bddAbove_iff_small] at hs ⊢
  exact small_lift _

theorem bddAbove_range_comp {ι : Type u} {f : ι → Cardinal.{v}} (hf : BddAbove (range f))
    (g : Cardinal.{v} → Cardinal.{max v w}) : BddAbove (range (g ∘ f)) := by
  rw [range_comp]
  exact bddAbove_image g hf

theorem iSup_le_sum {ι} (f : ι → Cardinal) : iSup f ≤ sum f :=
  ciSup_le' <| le_sum _

theorem sum_le_iSup_lift {ι : Type u}
    (f : ι → Cardinal.{max u v}) : sum f ≤ Cardinal.lift #ι * iSup f := by
  rw [← (iSup f).lift_id, ← lift_umax, lift_umax.{max u v, u}, ← sum_const]
  exact sum_le_sum _ _ (le_ciSup <| bddAbove_range f)

theorem sum_le_iSup {ι : Type u} (f : ι → Cardinal.{u}) : sum f ≤ #ι * iSup f := by
  rw [← lift_id #ι]
  exact sum_le_iSup_lift f

theorem sum_nat_eq_add_sum_succ (f : ℕ → Cardinal.{u}) :
    Cardinal.sum f = f 0 + Cardinal.sum fun i => f (i + 1) := by
  refine (Equiv.sigmaNatSucc fun i => Quotient.out (f i)).cardinal_eq.trans ?_
  simp only [mk_sum, mk_out, lift_id, mk_sigma]

-- Porting note: LFS is not in normal form.
-- @[simp]
/-- A variant of `ciSup_of_empty` but with `0` on the RHS for convenience -/
protected theorem iSup_of_empty {ι} (f : ι → Cardinal) [IsEmpty ι] : iSup f = 0 :=
  ciSup_of_empty f

lemma exists_eq_of_iSup_eq_of_not_isSuccPrelimit
    {ι : Type u} (f : ι → Cardinal.{v}) (ω : Cardinal.{v})
    (hω : ¬ Order.IsSuccPrelimit ω)
    (h : ⨆ i : ι, f i = ω) : ∃ i, f i = ω := by
  subst h
  refine (isLUB_csSup' ?_).exists_of_not_isSuccPrelimit hω
  contrapose! hω with hf
  rw [iSup, csSup_of_not_bddAbove hf, csSup_empty]
  exact isSuccPrelimit_bot

@[deprecated exists_eq_of_iSup_eq_of_not_isSuccPrelimit (since := "2024-09-05")]
alias exists_eq_of_iSup_eq_of_not_isSuccLimit := exists_eq_of_iSup_eq_of_not_isSuccPrelimit

lemma exists_eq_of_iSup_eq_of_not_isLimit
    {ι : Type u} [hι : Nonempty ι] (f : ι → Cardinal.{v}) (hf : BddAbove (range f))
    (ω : Cardinal.{v}) (hω : ¬ ω.IsLimit)
    (h : ⨆ i : ι, f i = ω) : ∃ i, f i = ω := by
  refine (not_and_or.mp hω).elim (fun e ↦ ⟨hι.some, ?_⟩)
    (Cardinal.exists_eq_of_iSup_eq_of_not_isSuccPrelimit.{u, v} f ω · h)
  cases not_not.mp e
  rw [← le_zero_iff] at h ⊢
  exact (le_ciSup hf _).trans h

-- Porting note: simpNF is not happy with universe levels.
@[simp, nolint simpNF]
theorem lift_mk_shrink (α : Type u) [Small.{v} α] :
    Cardinal.lift.{max u w} #(Shrink.{v} α) = Cardinal.lift.{max v w} #α :=
  lift_mk_eq.2 ⟨(equivShrink α).symm⟩

@[simp]
theorem lift_mk_shrink' (α : Type u) [Small.{v} α] :
    Cardinal.lift.{u} #(Shrink.{v} α) = Cardinal.lift.{v} #α :=
  lift_mk_shrink.{u, v, 0} α

@[simp]
theorem lift_mk_shrink'' (α : Type max u v) [Small.{v} α] :
    Cardinal.lift.{u} #(Shrink.{v} α) = #α := by
  rw [← lift_umax', lift_mk_shrink.{max u v, v, 0} α, ← lift_umax, lift_id]

/-- The indexed product of cardinals is the cardinality of the Pi type
  (dependent product). -/
def prod {ι : Type u} (f : ι → Cardinal) : Cardinal :=
  #(∀ i, (f i).out)

@[simp]
theorem mk_pi {ι : Type u} (α : ι → Type v) : #(∀ i, α i) = prod fun i => #(α i) :=
  mk_congr <| Equiv.piCongrRight fun _ => outMkEquiv.symm

@[simp]
theorem prod_const (ι : Type u) (a : Cardinal.{v}) :
    (prod fun _ : ι => a) = lift.{u} a ^ lift.{v} #ι :=
  inductionOn a fun _ =>
    mk_congr <| Equiv.piCongr Equiv.ulift.symm fun _ => outMkEquiv.trans Equiv.ulift.symm

theorem prod_const' (ι : Type u) (a : Cardinal.{u}) : (prod fun _ : ι => a) = a ^ #ι :=
  inductionOn a fun _ => (mk_pi _).symm

theorem prod_le_prod {ι} (f g : ι → Cardinal) (H : ∀ i, f i ≤ g i) : prod f ≤ prod g :=
  ⟨Embedding.piCongrRight fun i =>
      Classical.choice <| by have := H i; rwa [← mk_out (f i), ← mk_out (g i)] at this⟩

@[simp]
theorem prod_eq_zero {ι} (f : ι → Cardinal.{u}) : prod f = 0 ↔ ∃ i, f i = 0 := by
  lift f to ι → Type u using fun _ => trivial
  simp only [mk_eq_zero_iff, ← mk_pi, isEmpty_pi]

theorem prod_ne_zero {ι} (f : ι → Cardinal) : prod f ≠ 0 ↔ ∀ i, f i ≠ 0 := by simp [prod_eq_zero]

@[simp]
theorem lift_prod {ι : Type u} (c : ι → Cardinal.{v}) :
    lift.{w} (prod c) = prod fun i => lift.{w} (c i) := by
  lift c to ι → Type v using fun _ => trivial
  simp only [← mk_pi, ← mk_uLift]
  exact mk_congr (Equiv.ulift.trans <| Equiv.piCongrRight fun i => Equiv.ulift.symm)

theorem prod_eq_of_fintype {α : Type u} [h : Fintype α] (f : α → Cardinal.{v}) :
    prod f = Cardinal.lift.{u} (∏ i, f i) := by
  revert f
  refine Fintype.induction_empty_option ?_ ?_ ?_ α (h_fintype := h)
  · intro α β hβ e h f
    letI := Fintype.ofEquiv β e.symm
    rw [← e.prod_comp f, ← h]
    exact mk_congr (e.piCongrLeft _).symm
  · intro f
    rw [Fintype.univ_pempty, Finset.prod_empty, lift_one, Cardinal.prod, mk_eq_one]
  · intro α hα h f
    rw [Cardinal.prod, mk_congr Equiv.piOptionEquivProd, mk_prod, lift_umax'.{v, u}, mk_out, ←
        Cardinal.prod, lift_prod, Fintype.prod_option, lift_mul, ← h fun a => f (some a)]
    simp only [lift_id]

@[simp]
theorem lift_sInf (s : Set Cardinal) : lift.{u, v} (sInf s) = sInf (lift.{u, v} '' s) := by
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · simp
  · exact lift_monotone.map_csInf hs

@[simp]
theorem lift_iInf {ι} (f : ι → Cardinal) : lift.{u, v} (iInf f) = ⨅ i, lift.{u, v} (f i) := by
  unfold iInf
  convert lift_sInf (range f)
  simp_rw [← comp_apply (f := lift), range_comp]

theorem lift_down {a : Cardinal.{u}} {b : Cardinal.{max u v}} :
    b ≤ lift.{v,u} a → ∃ a', lift.{v,u} a' = b :=
  inductionOn₂ a b fun α β => by
    rw [← lift_id #β, ← lift_umax, ← lift_umax.{u, v}, lift_mk_le.{v}]
    exact fun ⟨f⟩ =>
      ⟨#(Set.range f),
        Eq.symm <| lift_mk_eq.{_, _, v}.2
          ⟨Function.Embedding.equivOfSurjective (Embedding.codRestrict _ f Set.mem_range_self)
              fun ⟨a, ⟨b, e⟩⟩ => ⟨b, Subtype.eq e⟩⟩⟩

theorem le_lift_iff {a : Cardinal.{u}} {b : Cardinal.{max u v}} :
    b ≤ lift.{v, u} a ↔ ∃ a', lift.{v, u} a' = b ∧ a' ≤ a :=
  ⟨fun h =>
    let ⟨a', e⟩ := lift_down h
    ⟨a', e, lift_le.1 <| e.symm ▸ h⟩,
    fun ⟨_, e, h⟩ => e ▸ lift_le.2 h⟩

theorem lt_lift_iff {a : Cardinal.{u}} {b : Cardinal.{max u v}} :
    b < lift.{v, u} a ↔ ∃ a', lift.{v, u} a' = b ∧ a' < a :=
  ⟨fun h =>
    let ⟨a', e⟩ := lift_down h.le
    ⟨a', e, lift_lt.1 <| e.symm ▸ h⟩,
    fun ⟨_, e, h⟩ => e ▸ lift_lt.2 h⟩

@[simp]
theorem lift_succ (a) : lift.{v, u} (succ a) = succ (lift.{v, u} a) :=
  le_antisymm
    (le_of_not_gt fun h => by
      rcases lt_lift_iff.1 h with ⟨b, e, h⟩
      rw [lt_succ_iff, ← lift_le, e] at h
      exact h.not_lt (lt_succ _))
    (succ_le_of_lt <| lift_lt.2 <| lt_succ a)

-- Porting note: simpNF is not happy with universe levels.
@[simp, nolint simpNF]
theorem lift_umax_eq {a : Cardinal.{u}} {b : Cardinal.{v}} :
    lift.{max v w} a = lift.{max u w} b ↔ lift.{v} a = lift.{u} b := by
  rw [← lift_lift.{v, w, u}, ← lift_lift.{u, w, v}, lift_inj]

@[simp]
theorem lift_min {a b : Cardinal} : lift.{u, v} (min a b) = min (lift.{u, v} a) (lift.{u, v} b) :=
  lift_monotone.map_min

@[simp]
theorem lift_max {a b : Cardinal} : lift.{u, v} (max a b) = max (lift.{u, v} a) (lift.{u, v} b) :=
  lift_monotone.map_max

/-- The lift of a supremum is the supremum of the lifts. -/
theorem lift_sSup {s : Set Cardinal} (hs : BddAbove s) :
    lift.{u} (sSup s) = sSup (lift.{u} '' s) := by
  apply ((le_csSup_iff' (bddAbove_image.{_,u} _ hs)).2 fun c hc => _).antisymm (csSup_le' _)
  · intro c hc
    by_contra h
    obtain ⟨d, rfl⟩ := Cardinal.lift_down (not_le.1 h).le
    simp_rw [lift_le] at h hc
    rw [csSup_le_iff' hs] at h
    exact h fun a ha => lift_le.1 <| hc (mem_image_of_mem _ ha)
  · rintro i ⟨j, hj, rfl⟩
    exact lift_le.2 (le_csSup hs hj)

/-- The lift of a supremum is the supremum of the lifts. -/
theorem lift_iSup {ι : Type v} {f : ι → Cardinal.{w}} (hf : BddAbove (range f)) :
    lift.{u} (iSup f) = ⨆ i, lift.{u} (f i) := by
  rw [iSup, iSup, lift_sSup hf, ← range_comp]
  simp [Function.comp_def]

/-- To prove that the lift of a supremum is bounded by some cardinal `t`,
it suffices to show that the lift of each cardinal is bounded by `t`. -/
theorem lift_iSup_le {ι : Type v} {f : ι → Cardinal.{w}} {t : Cardinal} (hf : BddAbove (range f))
    (w : ∀ i, lift.{u} (f i) ≤ t) : lift.{u} (iSup f) ≤ t := by
  rw [lift_iSup hf]
  exact ciSup_le' w

@[simp]
theorem lift_iSup_le_iff {ι : Type v} {f : ι → Cardinal.{w}} (hf : BddAbove (range f))
    {t : Cardinal} : lift.{u} (iSup f) ≤ t ↔ ∀ i, lift.{u} (f i) ≤ t := by
  rw [lift_iSup hf]
  exact ciSup_le_iff' (bddAbove_range_comp.{_,_,u} hf _)

universe v' w'

/-- To prove an inequality between the lifts to a common universe of two different supremums,
it suffices to show that the lift of each cardinal from the smaller supremum
if bounded by the lift of some cardinal from the larger supremum.
-/
theorem lift_iSup_le_lift_iSup {ι : Type v} {ι' : Type v'} {f : ι → Cardinal.{w}}
    {f' : ι' → Cardinal.{w'}} (hf : BddAbove (range f)) (hf' : BddAbove (range f')) {g : ι → ι'}
    (h : ∀ i, lift.{w'} (f i) ≤ lift.{w} (f' (g i))) : lift.{w'} (iSup f) ≤ lift.{w} (iSup f') := by
  rw [lift_iSup hf, lift_iSup hf']
  exact ciSup_mono' (bddAbove_range_comp.{_,_,w} hf' _) fun i => ⟨_, h i⟩

/-- A variant of `lift_iSup_le_lift_iSup` with universes specialized via `w = v` and `w' = v'`.
This is sometimes necessary to avoid universe unification issues. -/
theorem lift_iSup_le_lift_iSup' {ι : Type v} {ι' : Type v'} {f : ι → Cardinal.{v}}
    {f' : ι' → Cardinal.{v'}} (hf : BddAbove (range f)) (hf' : BddAbove (range f')) (g : ι → ι')
    (h : ∀ i, lift.{v'} (f i) ≤ lift.{v} (f' (g i))) : lift.{v'} (iSup f) ≤ lift.{v} (iSup f') :=
  lift_iSup_le_lift_iSup hf hf' h

/-- `ℵ₀` is the smallest infinite cardinal. -/
def aleph0 : Cardinal.{u} :=
  lift #ℕ

@[inherit_doc]
scoped notation "ℵ₀" => Cardinal.aleph0

theorem mk_nat : #ℕ = ℵ₀ :=
  (lift_id _).symm

theorem aleph0_ne_zero : ℵ₀ ≠ 0 :=
  mk_ne_zero _

theorem aleph0_pos : 0 < ℵ₀ :=
  pos_iff_ne_zero.2 aleph0_ne_zero

@[simp]
theorem lift_aleph0 : lift ℵ₀ = ℵ₀ :=
  lift_lift _

@[simp]
theorem aleph0_le_lift {c : Cardinal.{u}} : ℵ₀ ≤ lift.{v} c ↔ ℵ₀ ≤ c := by
  rw [← lift_aleph0.{v, u}, lift_le]

@[simp]
theorem lift_le_aleph0 {c : Cardinal.{u}} : lift.{v} c ≤ ℵ₀ ↔ c ≤ ℵ₀ := by
  rw [← lift_aleph0.{v, u}, lift_le]

@[simp]
theorem aleph0_lt_lift {c : Cardinal.{u}} : ℵ₀ < lift.{v} c ↔ ℵ₀ < c := by
  rw [← lift_aleph0.{v, u}, lift_lt]

@[simp]
theorem lift_lt_aleph0 {c : Cardinal.{u}} : lift.{v} c < ℵ₀ ↔ c < ℵ₀ := by
  rw [← lift_aleph0.{v, u}, lift_lt]

/-! ### Properties about the cast from `ℕ` -/
section castFromN

-- porting note (#10618): simp can prove this
-- @[simp]
theorem mk_fin (n : ℕ) : #(Fin n) = n := by simp

@[simp]
theorem lift_natCast (n : ℕ) : lift.{u} (n : Cardinal.{v}) = n := by induction n <;> simp [*]

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem lift_ofNat (n : ℕ) [n.AtLeastTwo] :
    lift.{u} (no_index (OfNat.ofNat n : Cardinal.{v})) = OfNat.ofNat n :=
  lift_natCast n

@[simp]
theorem lift_eq_nat_iff {a : Cardinal.{u}} {n : ℕ} : lift.{v} a = n ↔ a = n :=
  lift_injective.eq_iff' (lift_natCast n)

@[simp]
theorem lift_eq_ofNat_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    lift.{v} a = (no_index (OfNat.ofNat n)) ↔ a = OfNat.ofNat n :=
  lift_eq_nat_iff

@[simp]
theorem nat_eq_lift_iff {n : ℕ} {a : Cardinal.{u}} :
    (n : Cardinal) = lift.{v} a ↔ (n : Cardinal) = a := by
  rw [← lift_natCast.{v,u} n, lift_inj]

@[simp]
theorem zero_eq_lift_iff {a : Cardinal.{u}} :
    (0 : Cardinal) = lift.{v} a ↔ 0 = a := by
  simpa using nat_eq_lift_iff (n := 0)

@[simp]
theorem one_eq_lift_iff {a : Cardinal.{u}} :
    (1 : Cardinal) = lift.{v} a ↔ 1 = a := by
  simpa using nat_eq_lift_iff (n := 1)

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem ofNat_eq_lift_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n : Cardinal)) = lift.{v} a ↔ (OfNat.ofNat n : Cardinal) = a :=
  nat_eq_lift_iff

@[simp]
theorem lift_le_nat_iff {a : Cardinal.{u}} {n : ℕ} : lift.{v} a ≤ n ↔ a ≤ n := by
  rw [← lift_natCast.{v,u}, lift_le]

@[simp]
theorem lift_le_one_iff {a : Cardinal.{u}} :
    lift.{v} a ≤ 1 ↔ a ≤ 1 := by
  simpa using lift_le_nat_iff (n := 1)

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem lift_le_ofNat_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    lift.{v} a ≤ (no_index (OfNat.ofNat n)) ↔ a ≤ OfNat.ofNat n :=
  lift_le_nat_iff

@[simp]
theorem nat_le_lift_iff {n : ℕ} {a : Cardinal.{u}} : n ≤ lift.{v} a ↔ n ≤ a := by
  rw [← lift_natCast.{v,u}, lift_le]

@[simp]
theorem one_le_lift_iff {a : Cardinal.{u}} :
    (1 : Cardinal) ≤ lift.{v} a ↔ 1 ≤ a := by
  simpa using nat_le_lift_iff (n := 1)

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem ofNat_le_lift_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n : Cardinal)) ≤ lift.{v} a ↔ (OfNat.ofNat n : Cardinal) ≤ a :=
  nat_le_lift_iff

@[simp]
theorem lift_lt_nat_iff {a : Cardinal.{u}} {n : ℕ} : lift.{v} a < n ↔ a < n := by
  rw [← lift_natCast.{v,u}, lift_lt]

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem lift_lt_ofNat_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    lift.{v} a < (no_index (OfNat.ofNat n)) ↔ a < OfNat.ofNat n :=
  lift_lt_nat_iff

@[simp]
theorem nat_lt_lift_iff {n : ℕ} {a : Cardinal.{u}} : n < lift.{v} a ↔ n < a := by
  rw [← lift_natCast.{v,u}, lift_lt]

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem zero_lt_lift_iff {a : Cardinal.{u}} :
    (0 : Cardinal) < lift.{v} a ↔ 0 < a := by
  simpa using nat_lt_lift_iff (n := 0)

@[simp]
theorem one_lt_lift_iff {a : Cardinal.{u}} :
    (1 : Cardinal) < lift.{v} a ↔ 1 < a := by
  simpa using nat_lt_lift_iff (n := 1)

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem ofNat_lt_lift_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n : Cardinal)) < lift.{v} a ↔ (OfNat.ofNat n : Cardinal) < a :=
  nat_lt_lift_iff

theorem lift_mk_fin (n : ℕ) : lift #(Fin n) = n := rfl

theorem mk_coe_finset {α : Type u} {s : Finset α} : #s = ↑(Finset.card s) := by simp

theorem mk_finset_of_fintype [Fintype α] : #(Finset α) = 2 ^ Fintype.card α := by
  simp [Pow.pow]

theorem card_le_of_finset {α} (s : Finset α) : (s.card : Cardinal) ≤ #α :=
  @mk_coe_finset _ s ▸ mk_set_le _

-- Porting note: was `simp`. LHS is not normal form.
-- @[simp, norm_cast]
@[norm_cast]
theorem natCast_pow {m n : ℕ} : (↑(m ^ n) : Cardinal) = (↑m : Cardinal) ^ (↑n : Cardinal) := by
  induction n <;> simp [pow_succ, power_add, *, Pow.pow]

-- porting note (#10618): simp can prove this
-- @[simp, norm_cast]
@[norm_cast]
theorem natCast_le {m n : ℕ} : (m : Cardinal) ≤ n ↔ m ≤ n := by
  rw [← lift_mk_fin, ← lift_mk_fin, lift_le, le_def, Function.Embedding.nonempty_iff_card_le,
    Fintype.card_fin, Fintype.card_fin]

-- porting note (#10618): simp can prove this
-- @[simp, norm_cast]
@[norm_cast]
theorem natCast_lt {m n : ℕ} : (m : Cardinal) < n ↔ m < n := by
  rw [lt_iff_le_not_le, ← not_le]
  simp only [natCast_le, not_le, and_iff_right_iff_imp]
  exact fun h ↦ le_of_lt h

instance : CharZero Cardinal :=
  ⟨StrictMono.injective fun _ _ => natCast_lt.2⟩

theorem natCast_inj {m n : ℕ} : (m : Cardinal) = n ↔ m = n :=
  Nat.cast_inj

theorem natCast_injective : Injective ((↑) : ℕ → Cardinal) :=
  Nat.cast_injective

@[norm_cast]
theorem nat_succ (n : ℕ) : (n.succ : Cardinal) = succ ↑n := by
  rw [Nat.cast_succ]
  refine (add_one_le_succ _).antisymm (succ_le_of_lt ?_)
  rw [← Nat.cast_succ]
  exact natCast_lt.2 (Nat.lt_succ_self _)

lemma succ_natCast (n : ℕ) : Order.succ (n : Cardinal) = n + 1 := by
  rw [← Cardinal.nat_succ]
  norm_cast

lemma natCast_add_one_le_iff {n : ℕ} {c : Cardinal} : n + 1 ≤ c ↔ n < c := by
  rw [← Order.succ_le_iff, Cardinal.succ_natCast]

lemma two_le_iff_one_lt {c : Cardinal} : 2 ≤ c ↔ 1 < c := by
  convert natCast_add_one_le_iff
  norm_cast

@[simp]
theorem succ_zero : succ (0 : Cardinal) = 1 := by norm_cast

theorem exists_finset_le_card (α : Type*) (n : ℕ) (h : n ≤ #α) :
    ∃ s : Finset α, n ≤ s.card := by
  obtain hα|hα := finite_or_infinite α
  · let hα := Fintype.ofFinite α
    use Finset.univ
    simpa only [mk_fintype, Nat.cast_le] using h
  · obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq α n
    exact ⟨s, hs.ge⟩

theorem card_le_of {α : Type u} {n : ℕ} (H : ∀ s : Finset α, s.card ≤ n) : #α ≤ n := by
  contrapose! H
  apply exists_finset_le_card α (n+1)
  simpa only [nat_succ, succ_le_iff] using H

theorem cantor' (a) {b : Cardinal} (hb : 1 < b) : a < b ^ a := by
  rw [← succ_le_iff, (by norm_cast : succ (1 : Cardinal) = 2)] at hb
  exact (cantor a).trans_le (power_le_power_right hb)

theorem one_le_iff_pos {c : Cardinal} : 1 ≤ c ↔ 0 < c := by
  rw [← succ_zero, succ_le_iff]

theorem one_le_iff_ne_zero {c : Cardinal} : 1 ≤ c ↔ c ≠ 0 := by
  rw [one_le_iff_pos, pos_iff_ne_zero]

@[simp]
theorem lt_one_iff_zero {c : Cardinal} : c < 1 ↔ c = 0 := by
  simpa using lt_succ_bot_iff (a := c)

theorem nat_lt_aleph0 (n : ℕ) : (n : Cardinal.{u}) < ℵ₀ :=
  succ_le_iff.1
    (by
      rw [← nat_succ, ← lift_mk_fin, aleph0, lift_mk_le.{u}]
      exact ⟨⟨(↑), fun a b => Fin.ext⟩⟩)

@[simp]
theorem one_lt_aleph0 : 1 < ℵ₀ := by simpa using nat_lt_aleph0 1

theorem one_le_aleph0 : 1 ≤ ℵ₀ :=
  one_lt_aleph0.le

theorem lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ ∃ n : ℕ, c = n :=
  ⟨fun h => by
    rcases lt_lift_iff.1 h with ⟨c, rfl, h'⟩
    rcases le_mk_iff_exists_set.1 h'.1 with ⟨S, rfl⟩
    suffices S.Finite by
      lift S to Finset ℕ using this
      simp
    contrapose! h'
    haveI := Infinite.to_subtype h'
    exact ⟨Infinite.natEmbedding S⟩, fun ⟨n, e⟩ => e.symm ▸ nat_lt_aleph0 _⟩

lemma succ_eq_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : Order.succ c = c + 1 := by
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp h
  rw [hn, succ_natCast]

theorem aleph0_le {c : Cardinal} : ℵ₀ ≤ c ↔ ∀ n : ℕ, ↑n ≤ c :=
  ⟨fun h n => (nat_lt_aleph0 _).le.trans h, fun h =>
    le_of_not_lt fun hn => by
      rcases lt_aleph0.1 hn with ⟨n, rfl⟩
      exact (Nat.lt_succ_self _).not_le (natCast_le.1 (h (n + 1)))⟩

theorem isSuccPrelimit_aleph0 : IsSuccPrelimit ℵ₀ :=
  isSuccPrelimit_of_succ_lt fun a ha => by
    rcases lt_aleph0.1 ha with ⟨n, rfl⟩
    rw [← nat_succ]
    apply nat_lt_aleph0

@[deprecated isSuccPrelimit_aleph0 (since := "2024-09-05")]
alias isSuccLimit_aleph0 := isSuccPrelimit_aleph0

theorem isLimit_aleph0 : IsLimit ℵ₀ :=
  ⟨aleph0_ne_zero, isSuccPrelimit_aleph0⟩

lemma not_isLimit_natCast : (n : ℕ) → ¬ IsLimit (n : Cardinal.{u})
  | 0, e => e.1 rfl
  | Nat.succ n, e => Order.not_isSuccPrelimit_succ _ (nat_succ n ▸ e.2)

theorem IsLimit.aleph0_le {c : Cardinal} (h : IsLimit c) : ℵ₀ ≤ c := by
  by_contra! h'
  rcases lt_aleph0.1 h' with ⟨n, rfl⟩
  exact not_isLimit_natCast n h

lemma exists_eq_natCast_of_iSup_eq {ι : Type u} [Nonempty ι] (f : ι → Cardinal.{v})
    (hf : BddAbove (range f)) (n : ℕ) (h : ⨆ i, f i = n) : ∃ i, f i = n :=
  exists_eq_of_iSup_eq_of_not_isLimit.{u, v} f hf _ (not_isLimit_natCast n) h

@[simp]
theorem range_natCast : range ((↑) : ℕ → Cardinal) = Iio ℵ₀ :=
  ext fun x => by simp only [mem_Iio, mem_range, eq_comm, lt_aleph0]

theorem mk_eq_nat_iff {α : Type u} {n : ℕ} : #α = n ↔ Nonempty (α ≃ Fin n) := by
  rw [← lift_mk_fin, ← lift_uzero #α, lift_mk_eq']

theorem lt_aleph0_iff_finite {α : Type u} : #α < ℵ₀ ↔ Finite α := by
  simp only [lt_aleph0, mk_eq_nat_iff, finite_iff_exists_equiv_fin]

theorem lt_aleph0_iff_fintype {α : Type u} : #α < ℵ₀ ↔ Nonempty (Fintype α) :=
  lt_aleph0_iff_finite.trans (finite_iff_nonempty_fintype _)

theorem lt_aleph0_of_finite (α : Type u) [Finite α] : #α < ℵ₀ :=
  lt_aleph0_iff_finite.2 ‹_›

-- porting note (#10618): simp can prove this
-- @[simp]
theorem lt_aleph0_iff_set_finite {S : Set α} : #S < ℵ₀ ↔ S.Finite :=
  lt_aleph0_iff_finite.trans finite_coe_iff

alias ⟨_, _root_.Set.Finite.lt_aleph0⟩ := lt_aleph0_iff_set_finite

@[simp]
theorem lt_aleph0_iff_subtype_finite {p : α → Prop} : #{ x // p x } < ℵ₀ ↔ { x | p x }.Finite :=
  lt_aleph0_iff_set_finite

theorem mk_le_aleph0_iff : #α ≤ ℵ₀ ↔ Countable α := by
  rw [countable_iff_nonempty_embedding, aleph0, ← lift_uzero #α, lift_mk_le']

@[simp]
theorem mk_le_aleph0 [Countable α] : #α ≤ ℵ₀ :=
  mk_le_aleph0_iff.mpr ‹_›

-- porting note (#10618): simp can prove this
-- @[simp]
theorem le_aleph0_iff_set_countable {s : Set α} : #s ≤ ℵ₀ ↔ s.Countable := mk_le_aleph0_iff

alias ⟨_, _root_.Set.Countable.le_aleph0⟩ := le_aleph0_iff_set_countable

@[simp]
theorem le_aleph0_iff_subtype_countable {p : α → Prop} :
    #{ x // p x } ≤ ℵ₀ ↔ { x | p x }.Countable :=
  le_aleph0_iff_set_countable

instance canLiftCardinalNat : CanLift Cardinal ℕ (↑) fun x => x < ℵ₀ :=
  ⟨fun _ hx =>
    let ⟨n, hn⟩ := lt_aleph0.mp hx
    ⟨n, hn.symm⟩⟩

theorem add_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a + b < ℵ₀ :=
  match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [← Nat.cast_add]; apply nat_lt_aleph0

theorem add_lt_aleph0_iff {a b : Cardinal} : a + b < ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀ :=
  ⟨fun h => ⟨(self_le_add_right _ _).trans_lt h, (self_le_add_left _ _).trans_lt h⟩,
   fun ⟨h1, h2⟩ => add_lt_aleph0 h1 h2⟩

theorem aleph0_le_add_iff {a b : Cardinal} : ℵ₀ ≤ a + b ↔ ℵ₀ ≤ a ∨ ℵ₀ ≤ b := by
  simp only [← not_lt, add_lt_aleph0_iff, not_and_or]

/-- See also `Cardinal.nsmul_lt_aleph0_iff_of_ne_zero` if you already have `n ≠ 0`. -/
theorem nsmul_lt_aleph0_iff {n : ℕ} {a : Cardinal} : n • a < ℵ₀ ↔ n = 0 ∨ a < ℵ₀ := by
  cases n with
  | zero => simpa using nat_lt_aleph0 0
  | succ n =>
      simp only [Nat.succ_ne_zero, false_or_iff]
      induction' n with n ih
      · simp
      rw [succ_nsmul, add_lt_aleph0_iff, ih, and_self_iff]

/-- See also `Cardinal.nsmul_lt_aleph0_iff` for a hypothesis-free version. -/
theorem nsmul_lt_aleph0_iff_of_ne_zero {n : ℕ} {a : Cardinal} (h : n ≠ 0) : n • a < ℵ₀ ↔ a < ℵ₀ :=
  nsmul_lt_aleph0_iff.trans <| or_iff_right h

theorem mul_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a * b < ℵ₀ :=
  match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [← Nat.cast_mul]; apply nat_lt_aleph0

theorem mul_lt_aleph0_iff {a b : Cardinal} : a * b < ℵ₀ ↔ a = 0 ∨ b = 0 ∨ a < ℵ₀ ∧ b < ℵ₀ := by
  refine ⟨fun h => ?_, ?_⟩
  · by_cases ha : a = 0
    · exact Or.inl ha
    right
    by_cases hb : b = 0
    · exact Or.inl hb
    right
    rw [← Ne, ← one_le_iff_ne_zero] at ha hb
    constructor
    · rw [← mul_one a]
      exact (mul_le_mul' le_rfl hb).trans_lt h
    · rw [← one_mul b]
      exact (mul_le_mul' ha le_rfl).trans_lt h
  rintro (rfl | rfl | ⟨ha, hb⟩) <;> simp only [*, mul_lt_aleph0, aleph0_pos, zero_mul, mul_zero]

/-- See also `Cardinal.aleph0_le_mul_iff`. -/
theorem aleph0_le_mul_iff {a b : Cardinal} : ℵ₀ ≤ a * b ↔ a ≠ 0 ∧ b ≠ 0 ∧ (ℵ₀ ≤ a ∨ ℵ₀ ≤ b) := by
  let h := (@mul_lt_aleph0_iff a b).not
  rwa [not_lt, not_or, not_or, not_and_or, not_lt, not_lt] at h

/-- See also `Cardinal.aleph0_le_mul_iff'`. -/
theorem aleph0_le_mul_iff' {a b : Cardinal.{u}} : ℵ₀ ≤ a * b ↔ a ≠ 0 ∧ ℵ₀ ≤ b ∨ ℵ₀ ≤ a ∧ b ≠ 0 := by
  have : ∀ {a : Cardinal.{u}}, ℵ₀ ≤ a → a ≠ 0 := fun a => ne_bot_of_le_ne_bot aleph0_ne_zero a
  simp only [aleph0_le_mul_iff, and_or_left, and_iff_right_of_imp this, @and_left_comm (a ≠ 0)]
  simp only [and_comm, or_comm]

theorem mul_lt_aleph0_iff_of_ne_zero {a b : Cardinal} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b < ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀ := by simp [mul_lt_aleph0_iff, ha, hb]

theorem power_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a ^ b < ℵ₀ :=
  match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [← natCast_pow]; apply nat_lt_aleph0

theorem eq_one_iff_unique {α : Type*} : #α = 1 ↔ Subsingleton α ∧ Nonempty α :=
  calc
    #α = 1 ↔ #α ≤ 1 ∧ 1 ≤ #α := le_antisymm_iff
    _ ↔ Subsingleton α ∧ Nonempty α :=
      le_one_iff_subsingleton.and (one_le_iff_ne_zero.trans mk_ne_zero_iff)

theorem infinite_iff {α : Type u} : Infinite α ↔ ℵ₀ ≤ #α := by
  rw [← not_lt, lt_aleph0_iff_finite, not_finite_iff_infinite]

lemma aleph0_le_mk_iff : ℵ₀ ≤ #α ↔ Infinite α := infinite_iff.symm
lemma mk_lt_aleph0_iff : #α < ℵ₀ ↔ Finite α := by simp [← not_le, aleph0_le_mk_iff]

@[simp]
theorem aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ ≤ #α :=
  infinite_iff.1 ‹_›

@[simp]
theorem mk_eq_aleph0 (α : Type*) [Countable α] [Infinite α] : #α = ℵ₀ :=
  mk_le_aleph0.antisymm <| aleph0_le_mk _

theorem denumerable_iff {α : Type u} : Nonempty (Denumerable α) ↔ #α = ℵ₀ :=
  ⟨fun ⟨h⟩ => mk_congr ((@Denumerable.eqv α h).trans Equiv.ulift.symm), fun h => by
    cases' Quotient.exact h with f
    exact ⟨Denumerable.mk' <| f.trans Equiv.ulift⟩⟩

-- porting note (#10618): simp can prove this
-- @[simp]
theorem mk_denumerable (α : Type u) [Denumerable α] : #α = ℵ₀ :=
  denumerable_iff.1 ⟨‹_›⟩

theorem _root_.Set.countable_infinite_iff_nonempty_denumerable {α : Type*} {s : Set α} :
    s.Countable ∧ s.Infinite ↔ Nonempty (Denumerable s) := by
  rw [nonempty_denumerable_iff, ← Set.infinite_coe_iff, countable_coe_iff]

@[simp]
theorem aleph0_add_aleph0 : ℵ₀ + ℵ₀ = ℵ₀ :=
  mk_denumerable _

theorem aleph0_mul_aleph0 : ℵ₀ * ℵ₀ = ℵ₀ :=
  mk_denumerable _

@[simp]
theorem nat_mul_aleph0 {n : ℕ} (hn : n ≠ 0) : ↑n * ℵ₀ = ℵ₀ :=
  le_antisymm (lift_mk_fin n ▸ mk_le_aleph0) <|
    le_mul_of_one_le_left (zero_le _) <| by
      rwa [← Nat.cast_one, natCast_le, Nat.one_le_iff_ne_zero]

@[simp]
theorem aleph0_mul_nat {n : ℕ} (hn : n ≠ 0) : ℵ₀ * n = ℵ₀ := by rw [mul_comm, nat_mul_aleph0 hn]

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem ofNat_mul_aleph0 {n : ℕ} [Nat.AtLeastTwo n] : no_index (OfNat.ofNat n) * ℵ₀ = ℵ₀ :=
  nat_mul_aleph0 (NeZero.ne n)

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem aleph0_mul_ofNat {n : ℕ} [Nat.AtLeastTwo n] : ℵ₀ * no_index (OfNat.ofNat n) = ℵ₀ :=
  aleph0_mul_nat (NeZero.ne n)

@[simp]
theorem add_le_aleph0 {c₁ c₂ : Cardinal} : c₁ + c₂ ≤ ℵ₀ ↔ c₁ ≤ ℵ₀ ∧ c₂ ≤ ℵ₀ :=
  ⟨fun h => ⟨le_self_add.trans h, le_add_self.trans h⟩, fun h =>
    aleph0_add_aleph0 ▸ add_le_add h.1 h.2⟩

@[simp]
theorem aleph0_add_nat (n : ℕ) : ℵ₀ + n = ℵ₀ :=
  (add_le_aleph0.2 ⟨le_rfl, (nat_lt_aleph0 n).le⟩).antisymm le_self_add

@[simp]
theorem nat_add_aleph0 (n : ℕ) : ↑n + ℵ₀ = ℵ₀ := by rw [add_comm, aleph0_add_nat]

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem ofNat_add_aleph0 {n : ℕ} [Nat.AtLeastTwo n] : no_index (OfNat.ofNat n) + ℵ₀ = ℵ₀ :=
  nat_add_aleph0 n

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem aleph0_add_ofNat {n : ℕ} [Nat.AtLeastTwo n] : ℵ₀ + no_index (OfNat.ofNat n) = ℵ₀ :=
  aleph0_add_nat n

theorem exists_nat_eq_of_le_nat {c : Cardinal} {n : ℕ} (h : c ≤ n) : ∃ m, m ≤ n ∧ c = m := by
  lift c to ℕ using h.trans_lt (nat_lt_aleph0 _)
  exact ⟨c, mod_cast h, rfl⟩

theorem mk_int : #ℤ = ℵ₀ :=
  mk_denumerable ℤ

theorem mk_pNat : #ℕ+ = ℵ₀ :=
  mk_denumerable ℕ+

end castFromN

variable {c : Cardinal}

/-- **König's theorem** -/
theorem sum_lt_prod {ι} (f g : ι → Cardinal) (H : ∀ i, f i < g i) : sum f < prod g :=
  lt_of_not_ge fun ⟨F⟩ => by
    have : Inhabited (∀ i : ι, (g i).out) := by
      refine ⟨fun i => Classical.choice <| mk_ne_zero_iff.1 ?_⟩
      rw [mk_out]
      exact (H i).ne_bot
    let G := invFun F
    have sG : Surjective G := invFun_surjective F.2
    choose C hc using
      show ∀ i, ∃ b, ∀ a, G ⟨i, a⟩ i ≠ b by
        intro i
        simp only [not_exists.symm, not_forall.symm]
        refine fun h => (H i).not_le ?_
        rw [← mk_out (f i), ← mk_out (g i)]
        exact ⟨Embedding.ofSurjective _ h⟩
    let ⟨⟨i, a⟩, h⟩ := sG C
    exact hc i a (congr_fun h _)

/-! Cardinalities of sets: cardinality of empty, finite sets, unions, subsets etc. -/
section sets

-- porting note (#10618): simp can prove this
-- @[simp]
theorem mk_empty : #Empty = 0 :=
  mk_eq_zero _

-- porting note (#10618): simp can prove this
-- @[simp]
theorem mk_pempty : #PEmpty = 0 :=
  mk_eq_zero _

-- porting note (#10618): simp can prove this
-- @[simp]
theorem mk_punit : #PUnit = 1 :=
  mk_eq_one PUnit

theorem mk_unit : #Unit = 1 :=
  mk_punit

-- porting note (#10618): simp can prove this
-- @[simp]
theorem mk_singleton {α : Type u} (x : α) : #({x} : Set α) = 1 :=
  mk_eq_one _

-- porting note (#10618): simp can prove this
-- @[simp]
theorem mk_plift_true : #(PLift True) = 1 :=
  mk_eq_one _

-- porting note (#10618): simp can prove this
-- @[simp]
theorem mk_plift_false : #(PLift False) = 0 :=
  mk_eq_zero _

@[simp]
theorem mk_vector (α : Type u) (n : ℕ) : #(Vector α n) = #α ^ n :=
  (mk_congr (Equiv.vectorEquivFin α n)).trans <| by simp

theorem mk_list_eq_sum_pow (α : Type u) : #(List α) = sum fun n : ℕ => #α ^ n :=
  calc
    #(List α) = #(Σn, Vector α n) := mk_congr (Equiv.sigmaFiberEquiv List.length).symm
    _ = sum fun n : ℕ => #α ^ n := by simp

theorem mk_quot_le {α : Type u} {r : α → α → Prop} : #(Quot r) ≤ #α :=
  mk_le_of_surjective Quot.exists_rep

theorem mk_quotient_le {α : Type u} {s : Setoid α} : #(Quotient s) ≤ #α :=
  mk_quot_le

theorem mk_subtype_le_of_subset {α : Type u} {p q : α → Prop} (h : ∀ ⦃x⦄, p x → q x) :
    #(Subtype p) ≤ #(Subtype q) :=
  ⟨Embedding.subtypeMap (Embedding.refl α) h⟩

-- porting note (#10618): simp can prove this
-- @[simp]
theorem mk_emptyCollection (α : Type u) : #(∅ : Set α) = 0 :=
  mk_eq_zero _

theorem mk_emptyCollection_iff {α : Type u} {s : Set α} : #s = 0 ↔ s = ∅ := by
  constructor
  · intro h
    rw [mk_eq_zero_iff] at h
    exact eq_empty_iff_forall_not_mem.2 fun x hx => h.elim' ⟨x, hx⟩
  · rintro rfl
    exact mk_emptyCollection _

@[simp]
theorem mk_univ {α : Type u} : #(@univ α) = #α :=
  mk_congr (Equiv.Set.univ α)

theorem mk_image_le {α β : Type u} {f : α → β} {s : Set α} : #(f '' s) ≤ #s :=
  mk_le_of_surjective surjective_onto_image

theorem mk_image_le_lift {α : Type u} {β : Type v} {f : α → β} {s : Set α} :
    lift.{u} #(f '' s) ≤ lift.{v} #s :=
  lift_mk_le.{0}.mpr ⟨Embedding.ofSurjective _ surjective_onto_image⟩

theorem mk_range_le {α β : Type u} {f : α → β} : #(range f) ≤ #α :=
  mk_le_of_surjective surjective_onto_range

theorem mk_range_le_lift {α : Type u} {β : Type v} {f : α → β} :
    lift.{u} #(range f) ≤ lift.{v} #α :=
  lift_mk_le.{0}.mpr ⟨Embedding.ofSurjective _ surjective_onto_range⟩

theorem mk_range_eq (f : α → β) (h : Injective f) : #(range f) = #α :=
  mk_congr (Equiv.ofInjective f h).symm

theorem mk_range_eq_lift {α : Type u} {β : Type v} {f : α → β} (hf : Injective f) :
    lift.{max u w} #(range f) = lift.{max v w} #α :=
  lift_mk_eq.{v,u,w}.mpr ⟨(Equiv.ofInjective f hf).symm⟩

theorem mk_range_eq_of_injective {α : Type u} {β : Type v} {f : α → β} (hf : Injective f) :
    lift.{u} #(range f) = lift.{v} #α :=
  lift_mk_eq'.mpr ⟨(Equiv.ofInjective f hf).symm⟩

lemma lift_mk_le_lift_mk_of_injective {α : Type u} {β : Type v} {f : α → β} (hf : Injective f) :
    Cardinal.lift.{v} (#α) ≤ Cardinal.lift.{u} (#β) := by
  rw [← Cardinal.mk_range_eq_of_injective hf]
  exact Cardinal.lift_le.2 (Cardinal.mk_set_le _)

lemma lift_mk_le_lift_mk_of_surjective {α : Type u} {β : Type v} {f : α → β} (hf : Surjective f) :
    Cardinal.lift.{u} (#β) ≤ Cardinal.lift.{v} (#α) :=
  lift_mk_le_lift_mk_of_injective (injective_surjInv hf)

theorem mk_image_eq_of_injOn {α β : Type u} (f : α → β) (s : Set α) (h : InjOn f s) :
    #(f '' s) = #s :=
  mk_congr (Equiv.Set.imageOfInjOn f s h).symm

theorem mk_image_eq_of_injOn_lift {α : Type u} {β : Type v} (f : α → β) (s : Set α)
    (h : InjOn f s) : lift.{u} #(f '' s) = lift.{v} #s :=
  lift_mk_eq.{v, u, 0}.mpr ⟨(Equiv.Set.imageOfInjOn f s h).symm⟩

theorem mk_image_eq {α β : Type u} {f : α → β} {s : Set α} (hf : Injective f) : #(f '' s) = #s :=
  mk_image_eq_of_injOn _ _ hf.injOn

theorem mk_image_eq_lift {α : Type u} {β : Type v} (f : α → β) (s : Set α) (h : Injective f) :
    lift.{u} #(f '' s) = lift.{v} #s :=
  mk_image_eq_of_injOn_lift _ _ h.injOn

theorem mk_iUnion_le_sum_mk {α ι : Type u} {f : ι → Set α} : #(⋃ i, f i) ≤ sum fun i => #(f i) :=
  calc
    #(⋃ i, f i) ≤ #(Σi, f i) := mk_le_of_surjective (Set.sigmaToiUnion_surjective f)
    _ = sum fun i => #(f i) := mk_sigma _

theorem mk_iUnion_le_sum_mk_lift {α : Type u} {ι : Type v} {f : ι → Set α} :
    lift.{v} #(⋃ i, f i) ≤ sum fun i => #(f i) :=
  calc
    lift.{v} #(⋃ i, f i) ≤ #(Σi, f i) :=
      mk_le_of_surjective <| ULift.up_surjective.comp (Set.sigmaToiUnion_surjective f)
    _ = sum fun i => #(f i) := mk_sigma _

theorem mk_iUnion_eq_sum_mk {α ι : Type u} {f : ι → Set α}
    (h : Pairwise fun i j => Disjoint (f i) (f j)) : #(⋃ i, f i) = sum fun i => #(f i) :=
  calc
    #(⋃ i, f i) = #(Σi, f i) := mk_congr (Set.unionEqSigmaOfDisjoint h)
    _ = sum fun i => #(f i) := mk_sigma _

theorem mk_iUnion_eq_sum_mk_lift {α : Type u} {ι : Type v} {f : ι → Set α}
    (h : Pairwise fun i j => Disjoint (f i) (f j)) :
    lift.{v} #(⋃ i, f i) = sum fun i => #(f i) :=
  calc
    lift.{v} #(⋃ i, f i) = #(Σi, f i) :=
      mk_congr <| .trans Equiv.ulift (Set.unionEqSigmaOfDisjoint h)
    _ = sum fun i => #(f i) := mk_sigma _

theorem mk_iUnion_le {α ι : Type u} (f : ι → Set α) : #(⋃ i, f i) ≤ #ι * ⨆ i, #(f i) :=
  mk_iUnion_le_sum_mk.trans (sum_le_iSup _)

theorem mk_iUnion_le_lift {α : Type u} {ι : Type v} (f : ι → Set α) :
    lift.{v} #(⋃ i, f i) ≤ lift.{u} #ι * ⨆ i, lift.{v} #(f i) := by
  refine mk_iUnion_le_sum_mk_lift.trans <| Eq.trans_le ?_ (sum_le_iSup_lift _)
  rw [← lift_sum, lift_id'.{_,u}]

theorem mk_sUnion_le {α : Type u} (A : Set (Set α)) : #(⋃₀ A) ≤ #A * ⨆ s : A, #s := by
  rw [sUnion_eq_iUnion]
  apply mk_iUnion_le

theorem mk_biUnion_le {ι α : Type u} (A : ι → Set α) (s : Set ι) :
    #(⋃ x ∈ s, A x) ≤ #s * ⨆ x : s, #(A x.1) := by
  rw [biUnion_eq_iUnion]
  apply mk_iUnion_le

theorem mk_biUnion_le_lift {α : Type u} {ι : Type v} (A : ι → Set α) (s : Set ι) :
    lift.{v} #(⋃ x ∈ s, A x) ≤ lift.{u} #s * ⨆ x : s, lift.{v} #(A x.1) := by
  rw [biUnion_eq_iUnion]
  apply mk_iUnion_le_lift

theorem finset_card_lt_aleph0 (s : Finset α) : #(↑s : Set α) < ℵ₀ :=
  lt_aleph0_of_finite _

theorem mk_set_eq_nat_iff_finset {α} {s : Set α} {n : ℕ} :
    #s = n ↔ ∃ t : Finset α, (t : Set α) = s ∧ t.card = n := by
  constructor
  · intro h
    lift s to Finset α using lt_aleph0_iff_set_finite.1 (h.symm ▸ nat_lt_aleph0 n)
    simpa using h
  · rintro ⟨t, rfl, rfl⟩
    exact mk_coe_finset

theorem mk_eq_nat_iff_finset {n : ℕ} :
    #α = n ↔ ∃ t : Finset α, (t : Set α) = univ ∧ t.card = n := by
  rw [← mk_univ, mk_set_eq_nat_iff_finset]

theorem mk_eq_nat_iff_fintype {n : ℕ} : #α = n ↔ ∃ h : Fintype α, @Fintype.card α h = n := by
  rw [mk_eq_nat_iff_finset]
  constructor
  · rintro ⟨t, ht, hn⟩
    exact ⟨⟨t, eq_univ_iff_forall.1 ht⟩, hn⟩
  · rintro ⟨⟨t, ht⟩, hn⟩
    exact ⟨t, eq_univ_iff_forall.2 ht, hn⟩

theorem mk_union_add_mk_inter {α : Type u} {S T : Set α} :
    #(S ∪ T : Set α) + #(S ∩ T : Set α) = #S + #T := by
  classical
  exact Quot.sound ⟨Equiv.Set.unionSumInter S T⟩

/-- The cardinality of a union is at most the sum of the cardinalities
of the two sets. -/
theorem mk_union_le {α : Type u} (S T : Set α) : #(S ∪ T : Set α) ≤ #S + #T :=
  @mk_union_add_mk_inter α S T ▸ self_le_add_right #(S ∪ T : Set α) #(S ∩ T : Set α)

theorem mk_union_of_disjoint {α : Type u} {S T : Set α} (H : Disjoint S T) :
    #(S ∪ T : Set α) = #S + #T := by
  classical
  exact Quot.sound ⟨Equiv.Set.union H.le_bot⟩

theorem mk_insert {α : Type u} {s : Set α} {a : α} (h : a ∉ s) :
    #(insert a s : Set α) = #s + 1 := by
  rw [← union_singleton, mk_union_of_disjoint, mk_singleton]
  simpa

theorem mk_insert_le {α : Type u} {s : Set α} {a : α} : #(insert a s : Set α) ≤ #s + 1 := by
  by_cases h : a ∈ s
  · simp only [insert_eq_of_mem h, self_le_add_right]
  · rw [mk_insert h]

theorem mk_sum_compl {α} (s : Set α) : #s + #(sᶜ : Set α) = #α := by
  classical
  exact mk_congr (Equiv.Set.sumCompl s)

theorem mk_le_mk_of_subset {α} {s t : Set α} (h : s ⊆ t) : #s ≤ #t :=
  ⟨Set.embeddingOfSubset s t h⟩

theorem mk_le_iff_forall_finset_subset_card_le {α : Type u} {n : ℕ} {t : Set α} :
    #t ≤ n ↔ ∀ s : Finset α, (s : Set α) ⊆ t → s.card ≤ n := by
  refine ⟨fun H s hs ↦ by simpa using (mk_le_mk_of_subset hs).trans H, fun H ↦ ?_⟩
  apply card_le_of (fun s ↦ ?_)
  classical
  let u : Finset α := s.image Subtype.val
  have : u.card = s.card := Finset.card_image_of_injOn Subtype.coe_injective.injOn
  rw [← this]
  apply H
  simp only [u, Finset.coe_image, image_subset_iff, Subtype.coe_preimage_self, subset_univ]

theorem mk_subtype_mono {p q : α → Prop} (h : ∀ x, p x → q x) :
    #{ x // p x } ≤ #{ x // q x } :=
  ⟨embeddingOfSubset _ _ h⟩

theorem le_mk_diff_add_mk (S T : Set α) : #S ≤ #(S \ T : Set α) + #T :=
  (mk_le_mk_of_subset <| subset_diff_union _ _).trans <| mk_union_le _ _

theorem mk_diff_add_mk {S T : Set α} (h : T ⊆ S) : #(S \ T : Set α) + #T = #S := by
  refine (mk_union_of_disjoint <| ?_).symm.trans <| by rw [diff_union_of_subset h]
  exact disjoint_sdiff_self_left

theorem mk_union_le_aleph0 {α} {P Q : Set α} :
    #(P ∪ Q : Set α) ≤ ℵ₀ ↔ #P ≤ ℵ₀ ∧ #Q ≤ ℵ₀ := by
  simp only [le_aleph0_iff_subtype_countable, mem_union, setOf_mem_eq, Set.union_def,
    ← countable_union]

theorem mk_subtype_of_equiv {α β : Type u} (p : β → Prop) (e : α ≃ β) :
    #{ a : α // p (e a) } = #{ b : β // p b } :=
  mk_congr (Equiv.subtypeEquivOfSubtype e)

theorem mk_sep (s : Set α) (t : α → Prop) : #({ x ∈ s | t x } : Set α) = #{ x : s | t x.1 } :=
  mk_congr (Equiv.Set.sep s t)

theorem mk_preimage_of_injective_lift {α : Type u} {β : Type v} (f : α → β) (s : Set β)
    (h : Injective f) : lift.{v} #(f ⁻¹' s) ≤ lift.{u} #s := by
  rw [lift_mk_le.{0}]
  -- Porting note: Needed to insert `mem_preimage.mp` below
  use Subtype.coind (fun x => f x.1) fun x => mem_preimage.mp x.2
  apply Subtype.coind_injective; exact h.comp Subtype.val_injective

theorem mk_preimage_of_subset_range_lift {α : Type u} {β : Type v} (f : α → β) (s : Set β)
    (h : s ⊆ range f) : lift.{u} #s ≤ lift.{v} #(f ⁻¹' s) := by
  rw [← image_preimage_eq_iff] at h
  nth_rewrite 1 [← h]
  apply mk_image_le_lift

theorem mk_preimage_of_injective_of_subset_range_lift {β : Type v} (f : α → β) (s : Set β)
    (h : Injective f) (h2 : s ⊆ range f) : lift.{v} #(f ⁻¹' s) = lift.{u} #s :=
  le_antisymm (mk_preimage_of_injective_lift f s h) (mk_preimage_of_subset_range_lift f s h2)

theorem mk_preimage_of_injective_of_subset_range (f : α → β) (s : Set β) (h : Injective f)
    (h2 : s ⊆ range f) : #(f ⁻¹' s) = #s := by
  convert mk_preimage_of_injective_of_subset_range_lift.{u, u} f s h h2 using 1 <;> rw [lift_id]

theorem mk_preimage_of_injective (f : α → β) (s : Set β) (h : Injective f) :
    #(f ⁻¹' s) ≤ #s := by
  rw [← lift_id #(↑(f ⁻¹' s)), ← lift_id #(↑s)]
  exact mk_preimage_of_injective_lift f s h

theorem mk_preimage_of_subset_range (f : α → β) (s : Set β) (h : s ⊆ range f) :
    #s ≤ #(f ⁻¹' s) := by
  rw [← lift_id #(↑(f ⁻¹' s)), ← lift_id #(↑s)]
  exact mk_preimage_of_subset_range_lift f s h

theorem mk_subset_ge_of_subset_image_lift {α : Type u} {β : Type v} (f : α → β) {s : Set α}
    {t : Set β} (h : t ⊆ f '' s) : lift.{u} #t ≤ lift.{v} #({ x ∈ s | f x ∈ t } : Set α) := by
  rw [image_eq_range] at h
  convert mk_preimage_of_subset_range_lift _ _ h using 1
  rw [mk_sep]
  rfl

theorem mk_subset_ge_of_subset_image (f : α → β) {s : Set α} {t : Set β} (h : t ⊆ f '' s) :
    #t ≤ #({ x ∈ s | f x ∈ t } : Set α) := by
  rw [image_eq_range] at h
  convert mk_preimage_of_subset_range _ _ h using 1
  rw [mk_sep]
  rfl

theorem le_mk_iff_exists_subset {c : Cardinal} {α : Type u} {s : Set α} :
    c ≤ #s ↔ ∃ p : Set α, p ⊆ s ∧ #p = c := by
  rw [le_mk_iff_exists_set, ← Subtype.exists_set_subtype]
  apply exists_congr; intro t; rw [mk_image_eq]; apply Subtype.val_injective

theorem two_le_iff : (2 : Cardinal) ≤ #α ↔ ∃ x y : α, x ≠ y := by
  rw [← Nat.cast_two, nat_succ, succ_le_iff, Nat.cast_one, one_lt_iff_nontrivial, nontrivial_iff]

theorem two_le_iff' (x : α) : (2 : Cardinal) ≤ #α ↔ ∃ y : α, y ≠ x := by
  rw [two_le_iff, ← nontrivial_iff, nontrivial_iff_exists_ne x]

theorem mk_eq_two_iff : #α = 2 ↔ ∃ x y : α, x ≠ y ∧ ({x, y} : Set α) = univ := by
  classical
  simp only [← @Nat.cast_two Cardinal, mk_eq_nat_iff_finset, Finset.card_eq_two]
  constructor
  · rintro ⟨t, ht, x, y, hne, rfl⟩
    exact ⟨x, y, hne, by simpa using ht⟩
  · rintro ⟨x, y, hne, h⟩
    exact ⟨{x, y}, by simpa using h, x, y, hne, rfl⟩

theorem mk_eq_two_iff' (x : α) : #α = 2 ↔ ∃! y, y ≠ x := by
  rw [mk_eq_two_iff]; constructor
  · rintro ⟨a, b, hne, h⟩
    simp only [eq_univ_iff_forall, mem_insert_iff, mem_singleton_iff] at h
    rcases h x with (rfl | rfl)
    exacts [⟨b, hne.symm, fun z => (h z).resolve_left⟩, ⟨a, hne, fun z => (h z).resolve_right⟩]
  · rintro ⟨y, hne, hy⟩
    exact ⟨x, y, hne.symm, eq_univ_of_forall fun z => or_iff_not_imp_left.2 (hy z)⟩

theorem exists_not_mem_of_length_lt {α : Type*} (l : List α) (h : ↑l.length < #α) :
    ∃ z : α, z ∉ l := by
  classical
  contrapose! h
  calc
    #α = #(Set.univ : Set α) := mk_univ.symm
    _ ≤ #l.toFinset := mk_le_mk_of_subset fun x _ => List.mem_toFinset.mpr (h x)
    _ = l.toFinset.card := Cardinal.mk_coe_finset
    _ ≤ l.length := Cardinal.natCast_le.mpr (List.toFinset_card_le l)

theorem three_le {α : Type*} (h : 3 ≤ #α) (x : α) (y : α) : ∃ z : α, z ≠ x ∧ z ≠ y := by
  have : ↑(3 : ℕ) ≤ #α := by simpa using h
  have : ↑(2 : ℕ) < #α := by rwa [← succ_le_iff, ← Cardinal.nat_succ]
  have := exists_not_mem_of_length_lt [x, y] this
  simpa [not_or] using this

end sets

section powerlt

/-- The function `a ^< b`, defined as the supremum of `a ^ c` for `c < b`. -/
def powerlt (a b : Cardinal.{u}) : Cardinal.{u} :=
  ⨆ c : Iio b, a ^ (c : Cardinal)

@[inherit_doc]
infixl:80 " ^< " => powerlt

theorem le_powerlt {b c : Cardinal.{u}} (a) (h : c < b) : (a^c) ≤ a ^< b := by
  refine le_ciSup (f := fun y : Iio b => a ^ (y : Cardinal)) ?_ ⟨c, h⟩
  rw [← image_eq_range]
  exact bddAbove_image.{u, u} _ bddAbove_Iio

theorem powerlt_le {a b c : Cardinal.{u}} : a ^< b ≤ c ↔ ∀ x < b, a ^ x ≤ c := by
  rw [powerlt, ciSup_le_iff']
  · simp
  · rw [← image_eq_range]
    exact bddAbove_image.{u, u} _ bddAbove_Iio

theorem powerlt_le_powerlt_left {a b c : Cardinal} (h : b ≤ c) : a ^< b ≤ a ^< c :=
  powerlt_le.2 fun _ hx => le_powerlt a <| hx.trans_le h

theorem powerlt_mono_left (a) : Monotone fun c => a ^< c := fun _ _ => powerlt_le_powerlt_left

theorem powerlt_succ {a b : Cardinal} (h : a ≠ 0) : a ^< succ b = a ^ b :=
  (powerlt_le.2 fun _ h' => power_le_power_left h <| le_of_lt_succ h').antisymm <|
    le_powerlt a (lt_succ b)

theorem powerlt_min {a b c : Cardinal} : a ^< min b c = min (a ^< b) (a ^< c) :=
  (powerlt_mono_left a).map_min

theorem powerlt_max {a b c : Cardinal} : a ^< max b c = max (a ^< b) (a ^< c) :=
  (powerlt_mono_left a).map_max

theorem zero_powerlt {a : Cardinal} (h : a ≠ 0) : 0 ^< a = 1 := by
  apply (powerlt_le.2 fun c _ => zero_power_le _).antisymm
  rw [← power_zero]
  exact le_powerlt 0 (pos_iff_ne_zero.2 h)

@[simp]
theorem powerlt_zero {a : Cardinal} : a ^< 0 = 0 := by
  convert Cardinal.iSup_of_empty _
  exact Subtype.isEmpty_of_false fun x => mem_Iio.not.mpr (Cardinal.zero_le x).not_lt

end powerlt
end Cardinal

-- namespace Tactic

-- open Cardinal Positivity

-- Porting note: Meta code, do not port directly
-- /-- Extension for the `positivity` tactic: The cardinal power of a positive cardinal is
--  positive. -/
-- @[positivity]
-- unsafe def positivity_cardinal_pow : expr → tactic strictness
--   | q(@Pow.pow _ _ $(inst) $(a) $(b)) => do
--     let strictness_a ← core a
--     match strictness_a with
--       | positive p => positive <$> mk_app `` power_pos [b, p]
--       | _ => failed
--   |-- We already know that `0 ≤ x` for all `x : Cardinal`
--     _ =>
--     failed

-- end Tactic

set_option linter.style.longFile 2100
