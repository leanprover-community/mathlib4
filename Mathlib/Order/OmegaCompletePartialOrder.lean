/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Control.Monad.Basic
import Mathlib.Data.Part
import Mathlib.Order.Hom.Order
import Mathlib.Data.Nat.Order.Basic

#align_import order.omega_complete_partial_order from "leanprover-community/mathlib"@"92ca63f0fb391a9ca5f22d2409a6080e786d99f7"

/-!
# Omega Complete Partial Orders

An omega-complete partial order is a partial order with a supremum
operation on increasing sequences indexed by natural numbers (which we
call `ωSup`). In this sense, it is strictly weaker than join complete
semi-lattices as only ω-sized totally ordered sets have a supremum.

The concept of an omega-complete partial order (ωCPO) is useful for the
formalization of the semantics of programming languages. Its notion of
supremum helps define the meaning of recursive procedures.

## Main definitions

 * class `OmegaCompletePartialOrder`
 * `ite`, `map`, `bind`, `seq` as continuous morphisms

## Instances of `OmegaCompletePartialOrder`

 * `Part`
 * every `CompleteLattice`
 * pi-types
 * product types
 * `OrderHom`
 * `ContinuousHom` (with notation →𝒄)
   * an instance of `OmegaCompletePartialOrder (α →𝒄 β)`
 * `ContinuousHom.ofFun`
 * `ContinuousHom.ofMono`
 * continuous functions:
   * `id`
   * `ite`
   * `const`
   * `Part.bind`
   * `Part.map`
   * `Part.seq`

## References

 * [Chain-complete posets and directed sets with applications][markowsky1976]
 * [Recursive definitions of partial functions and their computations][cadiou1972]
 * [Semantics of Programming Languages: Structures and Techniques][gunter1992]
-/


universe u v

-- porting note: can this really be a good idea?
attribute [-simp] Part.bind_eq_bind Part.map_eq_map

open Classical

namespace OrderHom

variable {α : Type*} {β : Type*} {γ : Type*}
variable [Preorder α] [Preorder β] [Preorder γ]

/-- `Part.bind` as a monotone function -/
@[simps]
def bind {β γ} (f : α →o Part β) (g : α →o β → Part γ) : α →o Part γ where
  toFun x := f x >>= g x
  monotone' := by
    intro x y h a
    -- ⊢ a ∈ (fun x => ↑f x >>= ↑g x) x → a ∈ (fun x => ↑f x >>= ↑g x) y
    simp only [and_imp, exists_prop, Part.bind_eq_bind, Part.mem_bind_iff, exists_imp]
    -- ⊢ ∀ (x_1 : β), x_1 ∈ ↑f x → a ∈ ↑g x x_1 → ∃ a_3, a_3 ∈ ↑f y ∧ a ∈ ↑g y a_3
    intro b hb ha
    -- ⊢ ∃ a_1, a_1 ∈ ↑f y ∧ a ∈ ↑g y a_1
    refine' ⟨b, f.monotone h _ hb, g.monotone h _ _ ha⟩
    -- 🎉 no goals
#align order_hom.bind OrderHom.bind
#align order_hom.bind_coe OrderHom.bind_coe

end OrderHom

namespace OmegaCompletePartialOrder

/-- A chain is a monotone sequence.

See the definition on page 114 of [gunter1992]. -/
def Chain (α : Type u) [Preorder α] :=
  ℕ →o α
#align omega_complete_partial_order.chain OmegaCompletePartialOrder.Chain

namespace Chain

variable {α : Type u} {β : Type v} {γ : Type*}
variable [Preorder α] [Preorder β] [Preorder γ]

instance : OrderHomClass (Chain α) ℕ α := inferInstanceAs <| OrderHomClass (ℕ →o α) ℕ α
instance : CoeFun (Chain α) fun _ => ℕ → α := ⟨FunLike.coe⟩

instance [Inhabited α] : Inhabited (Chain α) :=
  ⟨⟨default, fun _ _ _ => le_rfl⟩⟩

instance : Membership α (Chain α) :=
  ⟨fun a (c : ℕ →o α) => ∃ i, a = c i⟩

variable (c c' : Chain α)
variable (f : α →o β)
variable (g : β →o γ)

instance : LE (Chain α) where le x y := ∀ i, ∃ j, x i ≤ y j

/-- `map` function for `Chain` -/
-- Porting note: `simps` doesn't work with type synonyms
-- @[simps! (config := { fullyApplied := false })]
def map : Chain β :=
  f.comp c
#align omega_complete_partial_order.chain.map OmegaCompletePartialOrder.Chain.map

@[simp] theorem map_coe : ⇑(map c f) = f ∘ c := rfl
#align omega_complete_partial_order.chain.map_coe OmegaCompletePartialOrder.Chain.map_coe

variable {f}

theorem mem_map (x : α) : x ∈ c → f x ∈ Chain.map c f :=
  fun ⟨i, h⟩ => ⟨i, h.symm ▸ rfl⟩
#align omega_complete_partial_order.chain.mem_map OmegaCompletePartialOrder.Chain.mem_map

theorem exists_of_mem_map {b : β} : b ∈ c.map f → ∃ a, a ∈ c ∧ f a = b :=
  fun ⟨i, h⟩ => ⟨c i, ⟨i, rfl⟩, h.symm⟩
#align omega_complete_partial_order.chain.exists_of_mem_map OmegaCompletePartialOrder.Chain.exists_of_mem_map

@[simp]
theorem mem_map_iff {b : β} : b ∈ c.map f ↔ ∃ a, a ∈ c ∧ f a = b :=
  ⟨exists_of_mem_map _, fun h => by
    rcases h with ⟨w, h, h'⟩
    -- ⊢ b ∈ map c f
    subst b
    -- ⊢ ↑f w ∈ map c f
    apply mem_map c _ h⟩
    -- 🎉 no goals
#align omega_complete_partial_order.chain.mem_map_iff OmegaCompletePartialOrder.Chain.mem_map_iff

@[simp]
theorem map_id : c.map OrderHom.id = c :=
  OrderHom.comp_id _
#align omega_complete_partial_order.chain.map_id OmegaCompletePartialOrder.Chain.map_id

theorem map_comp : (c.map f).map g = c.map (g.comp f) :=
  rfl
#align omega_complete_partial_order.chain.map_comp OmegaCompletePartialOrder.Chain.map_comp

@[mono]
theorem map_le_map {g : α →o β} (h : f ≤ g) : c.map f ≤ c.map g :=
  fun i => by simp [mem_map_iff]; intros; exists i; apply h
              -- ⊢ ∃ j, ↑f (↑c i) ≤ ↑g (↑c j)
                                  -- ⊢ ∃ j, ↑f (↑c i) ≤ ↑g (↑c j)
                                          -- ⊢ ↑f (↑c i) ≤ ↑g (↑c i)
                                                    -- 🎉 no goals
#align omega_complete_partial_order.chain.map_le_map OmegaCompletePartialOrder.Chain.map_le_map

/-- `OmegaCompletePartialOrder.Chain.zip` pairs up the elements of two chains
that have the same index. -/
-- Porting note: `simps` doesn't work with type synonyms
-- @[simps!]
def zip (c₀ : Chain α) (c₁ : Chain β) : Chain (α × β) :=
  OrderHom.prod c₀ c₁
#align omega_complete_partial_order.chain.zip OmegaCompletePartialOrder.Chain.zip

@[simp] theorem zip_coe (c₀ : Chain α) (c₁ : Chain β) (n : ℕ) : c₀.zip c₁ n = (c₀ n, c₁ n) := rfl
#align omega_complete_partial_order.chain.zip_coe OmegaCompletePartialOrder.Chain.zip_coe

end Chain

end OmegaCompletePartialOrder

open OmegaCompletePartialOrder

-- porting note: removed "set_option extends_priority 50"

/-- An omega-complete partial order is a partial order with a supremum
operation on increasing sequences indexed by natural numbers (which we
call `ωSup`). In this sense, it is strictly weaker than join complete
semi-lattices as only ω-sized totally ordered sets have a supremum.

See the definition on page 114 of [gunter1992]. -/
class OmegaCompletePartialOrder (α : Type*) extends PartialOrder α where
  /-- The supremum of an increasing sequence -/
  ωSup : Chain α → α
  /-- `ωSup` is an upper bound of the increasing sequence -/
  le_ωSup : ∀ c : Chain α, ∀ i, c i ≤ ωSup c
  /-- `ωSup` is a lower bound of the set of upper bounds of the increasing sequence -/
  ωSup_le : ∀ (c : Chain α) (x), (∀ i, c i ≤ x) → ωSup c ≤ x
#align omega_complete_partial_order OmegaCompletePartialOrder

namespace OmegaCompletePartialOrder

variable {α : Type u} {β : Type v} {γ : Type*}

variable [OmegaCompletePartialOrder α]

/-- Transfer an `OmegaCompletePartialOrder` on `β` to an `OmegaCompletePartialOrder` on `α`
using a strictly monotone function `f : β →o α`, a definition of ωSup and a proof that `f` is
continuous with regard to the provided `ωSup` and the ωCPO on `α`. -/
@[reducible]
protected def lift [PartialOrder β] (f : β →o α) (ωSup₀ : Chain β → β)
    (h : ∀ x y, f x ≤ f y → x ≤ y) (h' : ∀ c, f (ωSup₀ c) = ωSup (c.map f)) :
    OmegaCompletePartialOrder β where
  ωSup := ωSup₀
  ωSup_le c x hx := h _ _ (by rw [h']; apply ωSup_le; intro i; apply f.monotone (hx i))
                              -- ⊢ ωSup (Chain.map c f) ≤ ↑f x
                           -- ⊢ ↑f (↑c i) ≤ ωSup (Chain.map c f)
                                    -- 🎉 no goals
                                       -- ⊢ ∀ (i : ℕ), ↑(Chain.map c f) i ≤ ↑f x
                                                      -- ⊢ ↑(Chain.map c f) i ≤ ↑f x
                                                               -- 🎉 no goals
  le_ωSup c i := h _ _ (by rw [h']; apply le_ωSup (c.map f))
#align omega_complete_partial_order.lift OmegaCompletePartialOrder.lift

theorem le_ωSup_of_le {c : Chain α} {x : α} (i : ℕ) (h : x ≤ c i) : x ≤ ωSup c :=
  le_trans h (le_ωSup c _)
#align omega_complete_partial_order.le_ωSup_of_le OmegaCompletePartialOrder.le_ωSup_of_le

theorem ωSup_total {c : Chain α} {x : α} (h : ∀ i, c i ≤ x ∨ x ≤ c i) : ωSup c ≤ x ∨ x ≤ ωSup c :=
  by_cases
    (fun (this : ∀ i, c i ≤ x) => Or.inl (ωSup_le _ _ this))
    (fun (this : ¬∀ i, c i ≤ x) =>
      have : ∃ i, ¬c i ≤ x := by simp only [not_forall] at this ⊢; assumption
                                 -- ⊢ ∃ i, ¬↑c i ≤ x
                                                                   -- 🎉 no goals
      let ⟨i, hx⟩ := this
      have : x ≤ c i := (h i).resolve_left hx
      Or.inr <| le_ωSup_of_le _ this)
#align omega_complete_partial_order.ωSup_total OmegaCompletePartialOrder.ωSup_total

@[mono]
theorem ωSup_le_ωSup_of_le {c₀ c₁ : Chain α} (h : c₀ ≤ c₁) : ωSup c₀ ≤ ωSup c₁ :=
  (ωSup_le _ _) fun i => by
    obtain ⟨_, h⟩ := h i
    -- ⊢ ↑c₀ i ≤ ωSup c₁
    exact le_trans h (le_ωSup _ _)
    -- 🎉 no goals
#align omega_complete_partial_order.ωSup_le_ωSup_of_le OmegaCompletePartialOrder.ωSup_le_ωSup_of_le

theorem ωSup_le_iff (c : Chain α) (x : α) : ωSup c ≤ x ↔ ∀ i, c i ≤ x := by
  constructor <;> intros
  -- ⊢ ωSup c ≤ x → ∀ (i : ℕ), ↑c i ≤ x
                  -- ⊢ ↑c i✝ ≤ x
                  -- ⊢ ωSup c ≤ x
  · trans ωSup c
    -- ⊢ ↑c i✝ ≤ ωSup c
    exact le_ωSup _ _
    -- ⊢ ωSup c ≤ x
    assumption
    -- 🎉 no goals
  exact ωSup_le _ _ ‹_›
  -- 🎉 no goals
#align omega_complete_partial_order.ωSup_le_iff OmegaCompletePartialOrder.ωSup_le_iff

/-- A subset `p : α → Prop` of the type closed under `ωSup` induces an
`OmegaCompletePartialOrder` on the subtype `{a : α // p a}`. -/
def subtype {α : Type*} [OmegaCompletePartialOrder α] (p : α → Prop)
    (hp : ∀ c : Chain α, (∀ i ∈ c, p i) → p (ωSup c)) : OmegaCompletePartialOrder (Subtype p) :=
  OmegaCompletePartialOrder.lift (OrderHom.Subtype.val p)
    (fun c => ⟨ωSup _, hp (c.map (OrderHom.Subtype.val p)) fun _ ⟨n, q⟩ => q.symm ▸ (c n).2⟩)
    (fun _ _ h => h) (fun _ => rfl)
#align omega_complete_partial_order.subtype OmegaCompletePartialOrder.subtype

section Continuity

open Chain

variable [OmegaCompletePartialOrder β]
variable [OmegaCompletePartialOrder γ]

/-- A monotone function `f : α →o β` is continuous if it distributes over ωSup.

In order to distinguish it from the (more commonly used) continuity from topology
(see `Mathlib/Topology/Basic.lean`), the present definition is often referred to as
"Scott-continuity" (referring to Dana Scott). It corresponds to continuity
in Scott topological spaces (not defined here). -/
def Continuous (f : α →o β) : Prop :=
  ∀ c : Chain α, f (ωSup c) = ωSup (c.map f)
#align omega_complete_partial_order.continuous OmegaCompletePartialOrder.Continuous

/-- `Continuous' f` asserts that `f` is both monotone and continuous. -/
def Continuous' (f : α → β) : Prop :=
  ∃ hf : Monotone f, Continuous ⟨f, hf⟩
#align omega_complete_partial_order.continuous' OmegaCompletePartialOrder.Continuous'

theorem Continuous'.to_monotone {f : α → β} (hf : Continuous' f) : Monotone f :=
  hf.fst
#align omega_complete_partial_order.continuous'.to_monotone OmegaCompletePartialOrder.Continuous'.to_monotone

theorem Continuous.of_bundled (f : α → β) (hf : Monotone f) (hf' : Continuous ⟨f, hf⟩) :
    Continuous' f :=
  ⟨hf, hf'⟩
#align omega_complete_partial_order.continuous.of_bundled OmegaCompletePartialOrder.Continuous.of_bundled

theorem Continuous.of_bundled' (f : α →o β) (hf' : Continuous f) : Continuous' f :=
  ⟨f.mono, hf'⟩
#align omega_complete_partial_order.continuous.of_bundled' OmegaCompletePartialOrder.Continuous.of_bundled'

theorem Continuous'.to_bundled (f : α → β) (hf : Continuous' f) : Continuous ⟨f, hf.to_monotone⟩ :=
  hf.snd
#align omega_complete_partial_order.continuous'.to_bundled OmegaCompletePartialOrder.Continuous'.to_bundled

@[simp, norm_cast]
theorem continuous'_coe : ∀ {f : α →o β}, Continuous' f ↔ Continuous f
  | ⟨_, hf⟩ => ⟨fun ⟨_, hc⟩ => hc, fun hc => ⟨hf, hc⟩⟩
#align omega_complete_partial_order.continuous'_coe OmegaCompletePartialOrder.continuous'_coe

variable (f : α →o β) (g : β →o γ)

theorem continuous_id : Continuous (@OrderHom.id α _) := by intro c; rw [c.map_id]; rfl
                                                            -- ⊢ ↑OrderHom.id (ωSup c) = ωSup (map c OrderHom.id)
                                                                     -- ⊢ ↑OrderHom.id (ωSup c) = ωSup c
                                                                                    -- 🎉 no goals
#align omega_complete_partial_order.continuous_id OmegaCompletePartialOrder.continuous_id

theorem continuous_comp (hfc : Continuous f) (hgc : Continuous g) : Continuous (g.comp f) := by
  dsimp [Continuous] at *; intro;
  -- ⊢ ∀ (c : Chain α), ↑g (↑f (ωSup c)) = ωSup (map c (OrderHom.comp g f))
                           -- ⊢ ↑g (↑f (ωSup c✝)) = ωSup (map c✝ (OrderHom.comp g f))
  rw [hfc, hgc, Chain.map_comp]
  -- 🎉 no goals
#align omega_complete_partial_order.continuous_comp OmegaCompletePartialOrder.continuous_comp

theorem id_continuous' : Continuous' (@id α) :=
  continuous_id.of_bundled' _
#align omega_complete_partial_order.id_continuous' OmegaCompletePartialOrder.id_continuous'

theorem continuous_const (x : β) : Continuous (OrderHom.const α x) := fun c =>
  eq_of_forall_ge_iff fun z => by rw [ωSup_le_iff, Chain.map_coe, OrderHom.const_coe_coe]; simp
                                  -- ⊢ Function.const α x (ωSup c) ≤ z ↔ ∀ (i : ℕ), (Function.const α x ∘ ↑c) i ≤ z
                                                                                           -- 🎉 no goals
#align omega_complete_partial_order.continuous_const OmegaCompletePartialOrder.continuous_const

theorem const_continuous' (x : β) : Continuous' (Function.const α x) :=
  Continuous.of_bundled' (OrderHom.const α x) (continuous_const x)
#align omega_complete_partial_order.const_continuous' OmegaCompletePartialOrder.const_continuous'

end Continuity

end OmegaCompletePartialOrder

namespace Part

variable {α : Type u} {β : Type v} {γ : Type*}

open OmegaCompletePartialOrder

theorem eq_of_chain {c : Chain (Part α)} {a b : α} (ha : some a ∈ c) (hb : some b ∈ c) : a = b := by
  cases' ha with i ha; replace ha := ha.symm
  -- ⊢ a = b
                       -- ⊢ a = b
  cases' hb with j hb; replace hb := hb.symm
  -- ⊢ a = b
                       -- ⊢ a = b
  rw [eq_some_iff] at ha hb
  -- ⊢ a = b
  cases' le_total i j with hij hji
  -- ⊢ a = b
  · have := c.monotone hij _ ha; apply mem_unique this hb
    -- ⊢ a = b
                                 -- 🎉 no goals
  · have := c.monotone hji _ hb; apply Eq.symm; apply mem_unique this ha
    -- ⊢ a = b
                                 -- ⊢ b = a
                                                -- 🎉 no goals
  --Porting note: Old proof
  -- wlog h : i ≤ j := le_total i j using a b i j, b a j i
  -- rw [eq_some_iff] at ha hb
  -- have := c.monotone h _ ha; apply mem_unique this hb
#align part.eq_of_chain Part.eq_of_chain

/-- The (noncomputable) `ωSup` definition for the `ω`-CPO structure on `Part α`. -/
protected noncomputable def ωSup (c : Chain (Part α)) : Part α :=
  if h : ∃ a, some a ∈ c then some (Classical.choose h) else none
#align part.ωSup Part.ωSup

theorem ωSup_eq_some {c : Chain (Part α)} {a : α} (h : some a ∈ c) : Part.ωSup c = some a :=
  have : ∃ a, some a ∈ c := ⟨a, h⟩
  have a' : some (Classical.choose this) ∈ c := Classical.choose_spec this
  calc
    Part.ωSup c = some (Classical.choose this) := dif_pos this
    _ = some a := congr_arg _ (eq_of_chain a' h)
#align part.ωSup_eq_some Part.ωSup_eq_some

theorem ωSup_eq_none {c : Chain (Part α)} (h : ¬∃ a, some a ∈ c) : Part.ωSup c = none :=
  dif_neg h
#align part.ωSup_eq_none Part.ωSup_eq_none

theorem mem_chain_of_mem_ωSup {c : Chain (Part α)} {a : α} (h : a ∈ Part.ωSup c) : some a ∈ c := by
  simp only [Part.ωSup] at h; split_ifs at h with h_1
  -- ⊢ some a ∈ c
                              -- ⊢ some a ∈ c
  · have h' := Classical.choose_spec h_1
    -- ⊢ some a ∈ c
    rw [← eq_some_iff] at h
    -- ⊢ some a ∈ c
    rw [← h]
    -- ⊢ some (choose h_1) ∈ c
    exact h'
    -- 🎉 no goals
  · rcases h with ⟨⟨⟩⟩
    -- 🎉 no goals
#align part.mem_chain_of_mem_ωSup Part.mem_chain_of_mem_ωSup

noncomputable instance omegaCompletePartialOrder :
    OmegaCompletePartialOrder (Part α) where
  ωSup := Part.ωSup
  le_ωSup c i := by
    intro x hx
    -- ⊢ x ∈ Part.ωSup c
    rw [← eq_some_iff] at hx ⊢
    -- ⊢ Part.ωSup c = some x
    rw [ωSup_eq_some, ← hx]
    -- ⊢ some x ∈ c
    rw [← hx]
    -- ⊢ ↑c i ∈ c
    exact ⟨i, rfl⟩
    -- 🎉 no goals
  ωSup_le := by
    rintro c x hx a ha
    -- ⊢ a ∈ x
    replace ha := mem_chain_of_mem_ωSup ha
    -- ⊢ a ∈ x
    cases' ha with i ha
    -- ⊢ a ∈ x
    apply hx i
    -- ⊢ a ∈ ↑c i
    rw [← ha]
    -- ⊢ a ∈ some a
    apply mem_some
    -- 🎉 no goals
#align part.omega_complete_partial_order Part.omegaCompletePartialOrder

section Inst

theorem mem_ωSup (x : α) (c : Chain (Part α)) : x ∈ ωSup c ↔ some x ∈ c := by
  simp [OmegaCompletePartialOrder.ωSup, Part.ωSup]
  -- ⊢ (x ∈ if h : ∃ a, some a ∈ c then some (choose h) else none) ↔ some x ∈ c
  constructor
  -- ⊢ (x ∈ if h : ∃ a, some a ∈ c then some (choose h) else none) → some x ∈ c
  · split_ifs with h
    -- ⊢ x ∈ some (choose h) → some x ∈ c
    swap
    -- ⊢ x ∈ none → some x ∈ c
    rintro ⟨⟨⟩⟩
    -- ⊢ x ∈ some (choose h) → some x ∈ c
    intro h'
    -- ⊢ some x ∈ c
    have hh := Classical.choose_spec h
    -- ⊢ some x ∈ c
    simp only [mem_some_iff] at h'
    -- ⊢ some x ∈ c
    subst x
    -- ⊢ some (choose h) ∈ c
    exact hh
    -- 🎉 no goals
  · intro h
    -- ⊢ x ∈ if h : ∃ a, some a ∈ c then some (choose h) else none
    have h' : ∃ a : α, some a ∈ c := ⟨_, h⟩
    -- ⊢ x ∈ if h : ∃ a, some a ∈ c then some (choose h) else none
    rw [dif_pos h']
    -- ⊢ x ∈ some (choose h')
    have hh := Classical.choose_spec h'
    -- ⊢ x ∈ some (choose h')
    rw [eq_of_chain hh h]
    -- ⊢ x ∈ some x
    simp
    -- 🎉 no goals
#align part.mem_ωSup Part.mem_ωSup

end Inst

end Part

namespace Pi

variable {α : Type*} {β : α → Type*} {γ : Type*}

open OmegaCompletePartialOrder OmegaCompletePartialOrder.Chain

instance [∀ a, OmegaCompletePartialOrder (β a)] :
    OmegaCompletePartialOrder (∀ a, β a) where
  ωSup c a := ωSup (c.map (Pi.evalOrderHom a))
  ωSup_le c f hf a :=
    ωSup_le _ _ <| by
      rintro i
      -- ⊢ ↑(map c (evalOrderHom a)) i ≤ f a
      apply hf
      -- 🎉 no goals
  le_ωSup c i x := le_ωSup_of_le _ <| le_rfl

namespace OmegaCompletePartialOrder

variable [∀ x, OmegaCompletePartialOrder <| β x]
variable [OmegaCompletePartialOrder γ]

theorem flip₁_continuous' (f : ∀ x : α, γ → β x) (a : α) (hf : Continuous' fun x y => f y x) :
    Continuous' (f a) :=
  Continuous.of_bundled _ (fun _ _ h => hf.to_monotone h a) fun c => congr_fun (hf.to_bundled _ c) a
#align pi.omega_complete_partial_order.flip₁_continuous' Pi.OmegaCompletePartialOrder.flip₁_continuous'

theorem flip₂_continuous' (f : γ → ∀ x, β x) (hf : ∀ x, Continuous' fun g => f g x) :
    Continuous' f :=
  Continuous.of_bundled _ (fun x y h a => (hf a).to_monotone h)
    (by intro c; ext a; apply (hf a).to_bundled _ c)
        -- ⊢ ↑{ toFun := f, monotone' := (_ : ∀ (x y : γ), x ≤ y → ∀ (a : α), (fun g => f …
                 -- ⊢ ↑{ toFun := f, monotone' := (_ : ∀ (x y : γ), x ≤ y → ∀ (a : α), (fun g => f …
                        -- 🎉 no goals
#align pi.omega_complete_partial_order.flip₂_continuous' Pi.OmegaCompletePartialOrder.flip₂_continuous'

end OmegaCompletePartialOrder

end Pi

namespace Prod

open OmegaCompletePartialOrder

variable {α : Type*} {β : Type*} {γ : Type*}
variable [OmegaCompletePartialOrder α]
variable [OmegaCompletePartialOrder β]
variable [OmegaCompletePartialOrder γ]

/-- The supremum of a chain in the product `ω`-CPO. -/
@[simps]
protected def ωSup (c : Chain (α × β)) : α × β :=
  (ωSup (c.map OrderHom.fst), ωSup (c.map OrderHom.snd))
#align prod.ωSup Prod.ωSup
#align prod.ωSup_snd Prod.ωSup_snd
#align prod.ωSup_fst Prod.ωSup_fst

@[simps! ωSup_fst ωSup_snd]
instance : OmegaCompletePartialOrder (α × β) where
  ωSup := Prod.ωSup
  ωSup_le := fun _ _ h => ⟨ωSup_le _ _ fun i => (h i).1, ωSup_le _ _ fun i => (h i).2⟩
  le_ωSup c i := ⟨le_ωSup (c.map OrderHom.fst) i, le_ωSup (c.map OrderHom.snd) i⟩

theorem ωSup_zip (c₀ : Chain α) (c₁ : Chain β) : ωSup (c₀.zip c₁) = (ωSup c₀, ωSup c₁) := by
  apply eq_of_forall_ge_iff; rintro ⟨z₁, z₂⟩
  -- ⊢ ∀ (c : α × β), ωSup (Chain.zip c₀ c₁) ≤ c ↔ (ωSup c₀, ωSup c₁) ≤ c
                             -- ⊢ ωSup (Chain.zip c₀ c₁) ≤ (z₁, z₂) ↔ (ωSup c₀, ωSup c₁) ≤ (z₁, z₂)
  simp [ωSup_le_iff, forall_and]
  -- 🎉 no goals
#align prod.ωSup_zip Prod.ωSup_zip

end Prod

open OmegaCompletePartialOrder

namespace CompleteLattice

variable (α : Type u)

-- see Note [lower instance priority]
/-- Any complete lattice has an `ω`-CPO structure where the countable supremum is a special case
of arbitrary suprema. -/
instance (priority := 100) [CompleteLattice α] : OmegaCompletePartialOrder α where
  ωSup c := ⨆ i, c i
  ωSup_le := fun ⟨c, _⟩ s hs => by
    simp only [iSup_le_iff, OrderHom.coe_mk] at hs ⊢; intro i; apply hs i
    -- ⊢ ∀ (i : ℕ), ↑{ toFun := c, monotone' := monotone'✝ } i ≤ s
                                -- ⊢ ↑{ toFun := c, monotone' := monotone'✝ } i ≤ ⨆ (i : ℕ), ↑{ toFun := c, monot …
                                                             -- ⊢ ↑{ toFun := c, monotone' := monotone'✝ } i ≤ ↑{ toFun := c, monotone' := mon …
                                                                                    -- 🎉 no goals
                                                      -- ⊢ ↑{ toFun := c, monotone' := monotone'✝ } i ≤ s
                                                               -- 🎉 no goals
  le_ωSup := fun ⟨c, _⟩ i => by simp only [OrderHom.coe_mk]; apply le_iSup_of_le i; rfl

variable {α} {β : Type v} [OmegaCompletePartialOrder α] [CompleteLattice β]

theorem sSup_continuous (s : Set <| α →o β) (hs : ∀ f ∈ s, Continuous f) : Continuous (sSup s) := by
  intro c
  -- ⊢ ↑(sSup s) (ωSup c) = ωSup (Chain.map c (sSup s))
  apply eq_of_forall_ge_iff
  -- ⊢ ∀ (c_1 : β), ↑(sSup s) (ωSup c) ≤ c_1 ↔ ωSup (Chain.map c (sSup s)) ≤ c_1
  intro z
  -- ⊢ ↑(sSup s) (ωSup c) ≤ z ↔ ωSup (Chain.map c (sSup s)) ≤ z
  suffices (∀ f ∈ s, ∀ (n), (f : _) (c n) ≤ z) ↔ ∀ (n), ∀ f ∈ s, (f : _) (c n) ≤ z by
    simpa (config := { contextual := true }) [ωSup_le_iff, hs _ _ _] using this
  exact ⟨fun H n f hf => H f hf n, fun H f hf n => H n f hf⟩
  -- 🎉 no goals
#align complete_lattice.Sup_continuous CompleteLattice.sSup_continuous

theorem iSup_continuous {ι : Sort*} {f : ι → α →o β} (h : ∀ i, Continuous (f i)) :
    Continuous (⨆ i, f i) :=
  sSup_continuous _ <| Set.forall_range_iff.2 h
#align complete_lattice.supr_continuous CompleteLattice.iSup_continuous

theorem sSup_continuous' (s : Set (α → β)) (hc : ∀ f ∈ s, Continuous' f) :
    Continuous' (sSup s) := by
  lift s to Set (α →o β) using fun f hf => (hc f hf).to_monotone
  -- ⊢ Continuous' (sSup ((fun x x_1 => x '' x_1) FunLike.coe s))
  simp only [Set.ball_image_iff, continuous'_coe] at hc
  -- ⊢ Continuous' (sSup ((fun x x_1 => x '' x_1) FunLike.coe s))
  rw [sSup_image]
  -- ⊢ Continuous' (⨆ (a : α →o β) (_ : a ∈ s), ↑a)
  norm_cast
  -- ⊢ Continuous (⨆ (i : α →o β) (_ : i ∈ s), i)
  exact iSup_continuous fun f => iSup_continuous fun hf => hc f hf
  -- 🎉 no goals
#align complete_lattice.Sup_continuous' CompleteLattice.sSup_continuous'

theorem sup_continuous {f g : α →o β} (hf : Continuous f) (hg : Continuous g) :
    Continuous (f ⊔ g) := by
  rw [← sSup_pair]; apply sSup_continuous
  -- ⊢ Continuous (sSup {f, g})
                    -- ⊢ ∀ (f_1 : α →o β), f_1 ∈ {f, g} → Continuous f_1
  rintro f (rfl | rfl | _) <;> assumption
  -- ⊢ Continuous f
                               -- 🎉 no goals
                               -- 🎉 no goals
#align complete_lattice.sup_continuous CompleteLattice.sup_continuous

theorem top_continuous : Continuous (⊤ : α →o β) := by
  intro c; apply eq_of_forall_ge_iff; intro z
  -- ⊢ ↑⊤ (ωSup c) = ωSup (Chain.map c ⊤)
           -- ⊢ ∀ (c_1 : β), ↑⊤ (ωSup c) ≤ c_1 ↔ ωSup (Chain.map c ⊤) ≤ c_1
                                      -- ⊢ ↑⊤ (ωSup c) ≤ z ↔ ωSup (Chain.map c ⊤) ≤ z
  simp only [OrderHom.instTopOrderHom_top, OrderHom.const_coe_coe, Function.const, top_le_iff,
    ωSup_le_iff, Chain.map_coe, Function.comp, forall_const]
#align complete_lattice.top_continuous CompleteLattice.top_continuous

theorem bot_continuous : Continuous (⊥ : α →o β) := by
  rw [← sSup_empty]
  -- ⊢ Continuous (sSup ∅)
  exact sSup_continuous _ fun f hf => hf.elim
  -- 🎉 no goals
#align complete_lattice.bot_continuous CompleteLattice.bot_continuous

end CompleteLattice

namespace CompleteLattice

variable {α β : Type*} [OmegaCompletePartialOrder α] [CompleteLinearOrder β]

theorem inf_continuous (f g : α →o β) (hf : Continuous f) (hg : Continuous g) :
    Continuous (f ⊓ g) := by
  refine' fun c => eq_of_forall_ge_iff fun z => _
  -- ⊢ ↑(f ⊓ g) (ωSup c) ≤ z ↔ ωSup (Chain.map c (f ⊓ g)) ≤ z
  simp only [inf_le_iff, hf c, hg c, ωSup_le_iff, ←forall_or_left, ←forall_or_right,
             Chain.map_coe, OrderHom.coe_inf, ge_iff_le, Pi.inf_apply, Function.comp]
  exact ⟨λ h _ => h _ _, λ h i j => (h (max j i)).imp (le_trans $ f.mono $ c.mono $ le_max_left _ _)
    (le_trans $ g.mono $ c.mono $ le_max_right _ _)⟩
#align complete_lattice.inf_continuous CompleteLattice.inf_continuous

theorem inf_continuous' {f g : α → β} (hf : Continuous' f) (hg : Continuous' g) :
    Continuous' (f ⊓ g) :=
  ⟨_, inf_continuous _ _ hf.snd hg.snd⟩
#align complete_lattice.inf_continuous' CompleteLattice.inf_continuous'

end CompleteLattice

namespace OmegaCompletePartialOrder

variable {α : Type u} {α' : Type*} {β : Type v} {β' : Type*} {γ : Type*} {φ : Type*}

variable [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
variable [OmegaCompletePartialOrder γ] [OmegaCompletePartialOrder φ]
variable [OmegaCompletePartialOrder α'] [OmegaCompletePartialOrder β']

namespace OrderHom

/-- The `ωSup` operator for monotone functions. -/
@[simps]
protected def ωSup (c : Chain (α →o β)) : α →o β where
  toFun a := ωSup (c.map (OrderHom.apply a))
  monotone' _ _ h := ωSup_le_ωSup_of_le ((Chain.map_le_map _) fun a => a.monotone h)
#align omega_complete_partial_order.order_hom.ωSup OmegaCompletePartialOrder.OrderHom.ωSup
#align omega_complete_partial_order.order_hom.ωSup_coe OmegaCompletePartialOrder.OrderHom.ωSup_coe

@[simps! ωSup_coe]
instance omegaCompletePartialOrder : OmegaCompletePartialOrder (α →o β) :=
  OmegaCompletePartialOrder.lift OrderHom.coeFnHom OrderHom.ωSup (fun _ _ h => h) fun _ => rfl
#align omega_complete_partial_order.order_hom.omega_complete_partial_order OmegaCompletePartialOrder.OrderHom.omegaCompletePartialOrder
#align omega_complete_partial_order.order_hom.omega_complete_partial_order_ωSup_coe OmegaCompletePartialOrder.OrderHom.omegaCompletePartialOrder_ωSup_coe

end OrderHom

section

variable (α β)

/-- A monotone function on `ω`-continuous partial orders is said to be continuous
if for every chain `c : chain α`, `f (⊔ i, c i) = ⊔ i, f (c i)`.
This is just the bundled version of `OrderHom.continuous`. -/
structure ContinuousHom extends OrderHom α β where
  /-- The underlying function of a `ContinuousHom` is continuous, i.e. it preserves `ωSup` -/
  cont : Continuous toOrderHom
#align omega_complete_partial_order.continuous_hom OmegaCompletePartialOrder.ContinuousHom

attribute [nolint docBlame] ContinuousHom.toOrderHom

@[inherit_doc] infixr:25 " →𝒄 " => ContinuousHom -- Input: \r\MIc

instance : OrderHomClass (α →𝒄 β) α β where
  coe f := f.toFun
  coe_injective' := by rintro ⟨⟩ ⟨⟩ h; congr; exact FunLike.ext' h
                       -- ⊢ { toOrderHom := toOrderHom✝¹, cont := cont✝¹ } = { toOrderHom := toOrderHom✝ …
                                       -- ⊢ toOrderHom✝¹ = toOrderHom✝
                                              -- 🎉 no goals
  map_rel f _ _ h := f.mono h

-- Porting note: removed to avoid conflict with the generic instance
-- instance : Coe (α →𝒄 β) (α →o β) where coe := ContinuousHom.toOrderHom

instance : PartialOrder (α →𝒄 β) :=
  (PartialOrder.lift fun f => f.toOrderHom.toFun) <| by rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ h; congr
                                                        -- ⊢ { toOrderHom := { toFun := toFun✝¹, monotone' := monotone'✝¹ }, cont := cont …
                                                                            -- 🎉 no goals

end

namespace ContinuousHom

-- Not a `simp` lemma because in many cases projection is simpler than a generic coercion
theorem toOrderHom_eq_coe (f : α →𝒄 β) : f.1 = f := rfl

@[simp] theorem coe_mk (f : α →o β) (hf : Continuous f) : ⇑(mk f hf) = f := rfl
@[simp] theorem coe_toOrderHom (f : α →𝒄 β) : ⇑f.1 = f := rfl

/-- See Note [custom simps projection]. We specify this explicitly because we don't have a FunLike
instance.
-/
def Simps.apply (h : α →𝒄 β) : α → β :=
  h

initialize_simps_projections ContinuousHom (toFun → apply)

theorem congr_fun {f g : α →𝒄 β} (h : f = g) (x : α) : f x = g x :=
  FunLike.congr_fun h x
#align omega_complete_partial_order.continuous_hom.congr_fun OmegaCompletePartialOrder.ContinuousHom.congr_fun

theorem congr_arg (f : α →𝒄 β) {x y : α} (h : x = y) : f x = f y :=
  _root_.congr_arg f h
#align omega_complete_partial_order.continuous_hom.congr_arg OmegaCompletePartialOrder.ContinuousHom.congr_arg

protected theorem monotone (f : α →𝒄 β) : Monotone f :=
  f.monotone'
#align omega_complete_partial_order.continuous_hom.monotone OmegaCompletePartialOrder.ContinuousHom.monotone

@[mono]
theorem apply_mono {f g : α →𝒄 β} {x y : α} (h₁ : f ≤ g) (h₂ : x ≤ y) : f x ≤ g y :=
  OrderHom.apply_mono (show (f : α →o β) ≤ g from h₁) h₂
#align omega_complete_partial_order.continuous_hom.apply_mono OmegaCompletePartialOrder.ContinuousHom.apply_mono

theorem ite_continuous' {p : Prop} [hp : Decidable p] (f g : α → β) (hf : Continuous' f)
    (hg : Continuous' g) : Continuous' fun x => if p then f x else g x := by
  split_ifs <;> simp [*]
  -- ⊢ Continuous' fun x => f x
                -- 🎉 no goals
                -- 🎉 no goals
#align omega_complete_partial_order.continuous_hom.ite_continuous' OmegaCompletePartialOrder.ContinuousHom.ite_continuous'

theorem ωSup_bind {β γ : Type v} (c : Chain α) (f : α →o Part β) (g : α →o β → Part γ) :
    ωSup (c.map (f.bind g)) = ωSup (c.map f) >>= ωSup (c.map g) := by
  apply eq_of_forall_ge_iff; intro x
  -- ⊢ ∀ (c_1 : Part γ), ωSup (Chain.map c (OrderHom.bind f g)) ≤ c_1 ↔ ωSup (Chain …
                             -- ⊢ ωSup (Chain.map c (OrderHom.bind f g)) ≤ x ↔ ωSup (Chain.map c f) >>= ωSup ( …
  simp only [ωSup_le_iff, Part.bind_le, Chain.mem_map_iff, and_imp, OrderHom.bind_coe, exists_imp]
  -- ⊢ (∀ (i : ℕ), ↑(Chain.map c (OrderHom.bind f g)) i ≤ x) ↔ ∀ (a : β), a ∈ ωSup  …
  constructor <;> intro h'''
  -- ⊢ (∀ (i : ℕ), ↑(Chain.map c (OrderHom.bind f g)) i ≤ x) → ∀ (a : β), a ∈ ωSup  …
                  -- ⊢ ∀ (a : β), a ∈ ωSup (Chain.map c f) → ωSup (Chain.map c g) a ≤ x
                  -- ⊢ ∀ (i : ℕ), ↑(Chain.map c (OrderHom.bind f g)) i ≤ x
  · intro b hb
    -- ⊢ ωSup (Chain.map c g) b ≤ x
    apply ωSup_le _ _ _
    -- ⊢ ∀ (i : ℕ), ↑(Chain.map (Chain.map c g) (Pi.evalOrderHom b)) i ≤ x
    rintro i y hy
    -- ⊢ y ∈ x
    simp only [Part.mem_ωSup] at hb
    -- ⊢ y ∈ x
    rcases hb with ⟨j, hb⟩
    -- ⊢ y ∈ x
    replace hb := hb.symm
    -- ⊢ y ∈ x
    simp only [Part.eq_some_iff, Chain.map_coe, Function.comp_apply, OrderHom.apply_coe] at hy hb
    -- ⊢ y ∈ x
    replace hb : b ∈ f (c (max i j)) := f.mono (c.mono (le_max_right i j)) _ hb
    -- ⊢ y ∈ x
    replace hy : y ∈ g (c (max i j)) b := g.mono (c.mono (le_max_left i j)) _ _ hy
    -- ⊢ y ∈ x
    apply h''' (max i j)
    -- ⊢ y ∈ ↑(Chain.map c (OrderHom.bind f g)) (max i j)
    simp only [exists_prop, Part.bind_eq_bind, Part.mem_bind_iff, Chain.map_coe,
      Function.comp_apply, OrderHom.bind_coe]
    exact ⟨_, hb, hy⟩
    -- 🎉 no goals
  · intro i
    -- ⊢ ↑(Chain.map c (OrderHom.bind f g)) i ≤ x
    intro y hy
    -- ⊢ y ∈ x
    simp only [exists_prop, Part.bind_eq_bind, Part.mem_bind_iff, Chain.map_coe,
      Function.comp_apply, OrderHom.bind_coe] at hy
    rcases hy with ⟨b, hb₀, hb₁⟩
    -- ⊢ y ∈ x
    apply h''' b _
    -- ⊢ y ∈ ωSup (Chain.map c g) b
    · apply le_ωSup (c.map g) _ _ _ hb₁
      -- 🎉 no goals
    · apply le_ωSup (c.map f) i _ hb₀
      -- 🎉 no goals
#align omega_complete_partial_order.continuous_hom.ωSup_bind OmegaCompletePartialOrder.ContinuousHom.ωSup_bind

theorem bind_continuous' {β γ : Type v} (f : α → Part β) (g : α → β → Part γ) :
    Continuous' f → Continuous' g → Continuous' fun x => f x >>= g x
  | ⟨hf, hf'⟩, ⟨hg, hg'⟩ =>
    Continuous.of_bundled' (OrderHom.bind ⟨f, hf⟩ ⟨g, hg⟩)
      (by intro c; rw [ωSup_bind, ← hf', ← hg']; rfl)
          -- ⊢ ↑(OrderHom.bind { toFun := f, monotone' := hf } { toFun := g, monotone' := h …
                   -- ⊢ ↑(OrderHom.bind { toFun := f, monotone' := hf } { toFun := g, monotone' := h …
                                                 -- 🎉 no goals
#align omega_complete_partial_order.continuous_hom.bind_continuous' OmegaCompletePartialOrder.ContinuousHom.bind_continuous'

theorem map_continuous' {β γ : Type v} (f : β → γ) (g : α → Part β) (hg : Continuous' g) :
    Continuous' fun x => f <$> g x := by
  simp only [map_eq_bind_pure_comp]; apply bind_continuous' _ _ hg; apply const_continuous'
  -- ⊢ Continuous' fun x => g x >>= pure ∘ f
                                     -- ⊢ Continuous' fun x => pure ∘ f
                                                                    -- 🎉 no goals
#align omega_complete_partial_order.continuous_hom.map_continuous' OmegaCompletePartialOrder.ContinuousHom.map_continuous'

theorem seq_continuous' {β γ : Type v} (f : α → Part (β → γ)) (g : α → Part β) (hf : Continuous' f)
    (hg : Continuous' g) : Continuous' fun x => f x <*> g x := by
  simp only [seq_eq_bind_map]
  -- ⊢ Continuous' fun x => do
  apply bind_continuous' _ _ hf
  -- ⊢ Continuous' fun x x_1 => x_1 <$> g x
  apply Pi.OmegaCompletePartialOrder.flip₂_continuous'
  -- ⊢ ∀ (x : β → γ), Continuous' fun g_1 => x <$> g g_1
  intro
  -- ⊢ Continuous' fun g_1 => x✝ <$> g g_1
  apply map_continuous' _ _ hg
  -- 🎉 no goals
#align omega_complete_partial_order.continuous_hom.seq_continuous' OmegaCompletePartialOrder.ContinuousHom.seq_continuous'

theorem continuous (F : α →𝒄 β) (C : Chain α) : F (ωSup C) = ωSup (C.map F) :=
  ContinuousHom.cont _ _
#align omega_complete_partial_order.continuous_hom.continuous OmegaCompletePartialOrder.ContinuousHom.continuous

/-- Construct a continuous function from a bare function, a continuous function, and a proof that
they are equal. -/
-- Porting note: removed `@[reducible]`
@[simps!]
def copy (f : α → β) (g : α →𝒄 β) (h : f = g) : α →𝒄 β where
  toOrderHom := g.1.copy f h
  cont := by rw [OrderHom.copy_eq]; exact g.cont
             -- ⊢ Continuous g.toOrderHom
                                    -- 🎉 no goals
#align omega_complete_partial_order.continuous_hom.of_fun OmegaCompletePartialOrder.ContinuousHom.copy
#align omega_complete_partial_order.continuous_hom.of_fun_apply OmegaCompletePartialOrder.ContinuousHom.copy_apply

-- Porting note: `of_mono` now defeq `mk`
#align omega_complete_partial_order.continuous_hom.of_mono OmegaCompletePartialOrder.ContinuousHom.mk

/-- The identity as a continuous function. -/
@[simps!]
def id : α →𝒄 α := ⟨OrderHom.id, continuous_id⟩
#align omega_complete_partial_order.continuous_hom.id OmegaCompletePartialOrder.ContinuousHom.id
#align omega_complete_partial_order.continuous_hom.id_apply OmegaCompletePartialOrder.ContinuousHom.id_apply

/-- The composition of continuous functions. -/
@[simps!]
def comp (f : β →𝒄 γ) (g : α →𝒄 β) : α →𝒄 γ := ⟨.comp f.1 g.1, continuous_comp _ _ g.cont f.cont⟩
#align omega_complete_partial_order.continuous_hom.comp OmegaCompletePartialOrder.ContinuousHom.comp
#align omega_complete_partial_order.continuous_hom.comp_apply OmegaCompletePartialOrder.ContinuousHom.comp_apply

@[ext]
protected theorem ext (f g : α →𝒄 β) (h : ∀ x, f x = g x) : f = g := FunLike.ext f g h
#align omega_complete_partial_order.continuous_hom.ext OmegaCompletePartialOrder.ContinuousHom.ext

protected theorem coe_inj (f g : α →𝒄 β) (h : (f : α → β) = g) : f = g :=
  FunLike.ext' h
#align omega_complete_partial_order.continuous_hom.coe_inj OmegaCompletePartialOrder.ContinuousHom.coe_inj

@[simp]
theorem comp_id (f : β →𝒄 γ) : f.comp id = f := rfl
#align omega_complete_partial_order.continuous_hom.comp_id OmegaCompletePartialOrder.ContinuousHom.comp_id

@[simp]
theorem id_comp (f : β →𝒄 γ) : id.comp f = f := rfl
#align omega_complete_partial_order.continuous_hom.id_comp OmegaCompletePartialOrder.ContinuousHom.id_comp

@[simp]
theorem comp_assoc (f : γ →𝒄 φ) (g : β →𝒄 γ) (h : α →𝒄 β) : f.comp (g.comp h) = (f.comp g).comp h :=
  rfl
#align omega_complete_partial_order.continuous_hom.comp_assoc OmegaCompletePartialOrder.ContinuousHom.comp_assoc

@[simp]
theorem coe_apply (a : α) (f : α →𝒄 β) : (f : α →o β) a = f a :=
  rfl
#align omega_complete_partial_order.continuous_hom.coe_apply OmegaCompletePartialOrder.ContinuousHom.coe_apply

/-- `Function.const` is a continuous function. -/
@[simps!]
def const (x : β) : α →𝒄 β := ⟨.const _ x, continuous_const x⟩
#align omega_complete_partial_order.continuous_hom.const OmegaCompletePartialOrder.ContinuousHom.const
#align omega_complete_partial_order.continuous_hom.const_apply OmegaCompletePartialOrder.ContinuousHom.const_apply

instance [Inhabited β] : Inhabited (α →𝒄 β) :=
  ⟨const default⟩

/-- The map from continuous functions to monotone functions is itself a monotone function. -/
@[simps]
def toMono : (α →𝒄 β) →o α →o β where
  toFun f := f
  monotone' _ _ h := h
#align omega_complete_partial_order.continuous_hom.to_mono OmegaCompletePartialOrder.ContinuousHom.toMono
#align omega_complete_partial_order.continuous_hom.to_mono_coe OmegaCompletePartialOrder.ContinuousHom.toMono_coe

/-- When proving that a chain of applications is below a bound `z`, it suffices to consider the
functions and values being selected from the same index in the chains.

This lemma is more specific than necessary, i.e. `c₀` only needs to be a
chain of monotone functions, but it is only used with continuous functions. -/
@[simp]
theorem forall_forall_merge (c₀ : Chain (α →𝒄 β)) (c₁ : Chain α) (z : β) :
    (∀ i j : ℕ, (c₀ i) (c₁ j) ≤ z) ↔ ∀ i : ℕ, (c₀ i) (c₁ i) ≤ z := by
  constructor <;> introv h
  -- ⊢ (∀ (i j : ℕ), ↑(↑c₀ i) (↑c₁ j) ≤ z) → ∀ (i : ℕ), ↑(↑c₀ i) (↑c₁ i) ≤ z
                  -- ⊢ ↑(↑c₀ i) (↑c₁ i) ≤ z
                  -- ⊢ ↑(↑c₀ i) (↑c₁ j) ≤ z
  · apply h
    -- 🎉 no goals
  · apply le_trans _ (h (max i j))
    -- ⊢ ↑(↑c₀ i) (↑c₁ j) ≤ ↑(↑c₀ (max i j)) (↑c₁ (max i j))
    trans c₀ i (c₁ (max i j))
    -- ⊢ ↑(↑c₀ i) (↑c₁ j) ≤ ↑(↑c₀ i) (↑c₁ (max i j))
    · apply (c₀ i).monotone
      -- ⊢ ↑c₁ j ≤ ↑c₁ (max i j)
      apply c₁.monotone
      -- ⊢ j ≤ max i j
      apply le_max_right
      -- 🎉 no goals
    · apply c₀.monotone
      -- ⊢ i ≤ max i j
      apply le_max_left
      -- 🎉 no goals
#align omega_complete_partial_order.continuous_hom.forall_forall_merge OmegaCompletePartialOrder.ContinuousHom.forall_forall_merge

@[simp]
theorem forall_forall_merge' (c₀ : Chain (α →𝒄 β)) (c₁ : Chain α) (z : β) :
    (∀ j i : ℕ, (c₀ i) (c₁ j) ≤ z) ↔ ∀ i : ℕ, (c₀ i) (c₁ i) ≤ z := by
  rw [forall_swap, forall_forall_merge]
  -- 🎉 no goals
#align omega_complete_partial_order.continuous_hom.forall_forall_merge' OmegaCompletePartialOrder.ContinuousHom.forall_forall_merge'

/-- The `ωSup` operator for continuous functions, which takes the pointwise countable supremum
of the functions in the `ω`-chain. -/
@[simps!]
protected def ωSup (c : Chain (α →𝒄 β)) : α →𝒄 β :=
  .mk (ωSup <| c.map toMono) <| fun c' ↦ by
    apply eq_of_forall_ge_iff; intro z
    -- ⊢ ∀ (c_1 : β), ↑(ωSup (Chain.map c toMono)) (ωSup c') ≤ c_1 ↔ ωSup (Chain.map  …
                               -- ⊢ ↑(ωSup (Chain.map c toMono)) (ωSup c') ≤ z ↔ ωSup (Chain.map c' (ωSup (Chain …
    simp only [ωSup_le_iff, (c _).continuous, Chain.map_coe, OrderHom.apply_coe, toMono_coe,
      OrderHom.omegaCompletePartialOrder_ωSup_coe, forall_forall_merge, OrderHomClass.coe_coe,
      forall_forall_merge', (· ∘ ·), Function.eval]
#align omega_complete_partial_order.continuous_hom.ωSup OmegaCompletePartialOrder.ContinuousHom.ωSup
#align omega_complete_partial_order.continuous_hom.ωSup_apply OmegaCompletePartialOrder.ContinuousHom.ωSup_apply

@[simps ωSup]
instance : OmegaCompletePartialOrder (α →𝒄 β) :=
  OmegaCompletePartialOrder.lift ContinuousHom.toMono ContinuousHom.ωSup
    (fun _ _ h => h) (fun _ => rfl)

namespace Prod

/-- The application of continuous functions as a continuous function.  -/
@[simps]
def apply : (α →𝒄 β) × α →𝒄 β where
  toFun f := f.1 f.2
  monotone' x y h := by
    dsimp
    -- ⊢ ↑x.fst x.snd ≤ ↑y.fst y.snd
    trans y.fst x.snd <;> [apply h.1; apply y.1.monotone h.2]
    -- 🎉 no goals
  cont := by
    intro c
    -- ⊢ ↑{ toFun := fun f => ↑f.fst f.snd, monotone' := (_ : ∀ (x y : (α →𝒄 β) × α), …
    apply le_antisymm
    -- ⊢ ↑{ toFun := fun f => ↑f.fst f.snd, monotone' := (_ : ∀ (x y : (α →𝒄 β) × α), …
    · apply ωSup_le
      -- ⊢ ∀ (i : ℕ), ↑(Chain.map (Chain.map (Chain.map c OrderHom.fst) toMono) (OrderH …
      intro i
      -- ⊢ ↑(Chain.map (Chain.map (Chain.map c OrderHom.fst) toMono) (OrderHom.apply (ω …
      dsimp
      -- ⊢ ↑(↑c i).fst (ωSup (Chain.map c OrderHom.snd)) ≤ ωSup (Chain.map c { toFun := …
      rw [(c _).fst.continuous]
      -- ⊢ ωSup (Chain.map (Chain.map c OrderHom.snd) ↑(↑c i).fst) ≤ ωSup (Chain.map c  …
      apply ωSup_le
      -- ⊢ ∀ (i_1 : ℕ), ↑(Chain.map (Chain.map c OrderHom.snd) ↑(↑c i).fst) i_1 ≤ ωSup  …
      intro j
      -- ⊢ ↑(Chain.map (Chain.map c OrderHom.snd) ↑(↑c i).fst) j ≤ ωSup (Chain.map c {  …
      apply le_ωSup_of_le (max i j)
      -- ⊢ ↑(Chain.map (Chain.map c OrderHom.snd) ↑(↑c i).fst) j ≤ ↑(Chain.map c { toFu …
      apply apply_mono
      -- ⊢ (↑c i).fst ≤ (↑c (max i j)).fst
      exact monotone_fst (OrderHom.mono _ (le_max_left _ _))
      -- ⊢ ↑(Chain.map c OrderHom.snd) j ≤ (↑c (max i j)).snd
      exact monotone_snd (OrderHom.mono _ (le_max_right _ _))
      -- 🎉 no goals
    · apply ωSup_le
      -- ⊢ ∀ (i : ℕ), ↑(Chain.map c { toFun := fun f => ↑f.fst f.snd, monotone' := (_ : …
      intro i
      -- ⊢ ↑(Chain.map c { toFun := fun f => ↑f.fst f.snd, monotone' := (_ : ∀ (x y : ( …
      apply le_ωSup_of_le i
      -- ⊢ ↑(Chain.map c { toFun := fun f => ↑f.fst f.snd, monotone' := (_ : ∀ (x y : ( …
      dsimp
      -- ⊢ ↑(↑c i).fst (↑c i).snd ≤ ↑(↑c i).fst (ωSup (Chain.map c OrderHom.snd))
      apply OrderHom.mono _
      -- ⊢ (↑c i).snd ≤ ωSup (Chain.map c OrderHom.snd)
      apply le_ωSup_of_le i
      -- ⊢ (↑c i).snd ≤ ↑(Chain.map c OrderHom.snd) i
      rfl
      -- 🎉 no goals
#align omega_complete_partial_order.continuous_hom.prod.apply OmegaCompletePartialOrder.ContinuousHom.Prod.apply
#align omega_complete_partial_order.continuous_hom.prod.apply_apply OmegaCompletePartialOrder.ContinuousHom.Prod.apply_apply

end Prod

theorem ωSup_def (c : Chain (α →𝒄 β)) (x : α) : ωSup c x = ContinuousHom.ωSup c x :=
  rfl
#align omega_complete_partial_order.continuous_hom.ωSup_def OmegaCompletePartialOrder.ContinuousHom.ωSup_def

theorem ωSup_apply_ωSup (c₀ : Chain (α →𝒄 β)) (c₁ : Chain α) :
    ωSup c₀ (ωSup c₁) = Prod.apply (ωSup (c₀.zip c₁)) := by simp [Prod.apply_apply, Prod.ωSup_zip]
                                                            -- 🎉 no goals
#align omega_complete_partial_order.continuous_hom.ωSup_apply_ωSup OmegaCompletePartialOrder.ContinuousHom.ωSup_apply_ωSup

/-- A family of continuous functions yields a continuous family of functions. -/
@[simps]
def flip {α : Type*} (f : α → β →𝒄 γ) : β →𝒄 α → γ where
  toFun x y := f y x
  monotone' x y h a := (f a).monotone h
  cont := by intro _; ext x; change f _ _ = _; rw [(f _).continuous]; rfl
             -- ⊢ ↑{ toFun := fun x y => ↑(f y) x, monotone' := (_ : ∀ (x y : β), x ≤ y → ∀ (a …
                      -- ⊢ ↑{ toFun := fun x y => ↑(f y) x, monotone' := (_ : ∀ (x y : β), x ≤ y → ∀ (a …
                             -- ⊢ ↑(f x) (ωSup c✝) = ωSup (Chain.map c✝ { toFun := fun x y => ↑(f y) x, monoto …
                                               -- ⊢ ωSup (Chain.map c✝ ↑(f x)) = ωSup (Chain.map c✝ { toFun := fun x y => ↑(f y) …
                                                                      -- 🎉 no goals
#align omega_complete_partial_order.continuous_hom.flip OmegaCompletePartialOrder.ContinuousHom.flip
#align omega_complete_partial_order.continuous_hom.flip_apply OmegaCompletePartialOrder.ContinuousHom.flip_apply

/-- `Part.bind` as a continuous function. -/
@[simps! apply] --Porting note: removed `(config := { rhsMd := reducible })`
noncomputable def bind {β γ : Type v} (f : α →𝒄 Part β) (g : α →𝒄 β → Part γ) : α →𝒄 Part γ :=
  .mk (OrderHom.bind f g.toOrderHom) fun c => by
    rw [ωSup_bind, ← f.continuous, g.toOrderHom_eq_coe, ← g.continuous]
    -- ⊢ ↑(OrderHom.bind ↑f ↑g) (ωSup c) = ↑f (ωSup c) >>= ↑g (ωSup c)
    rfl
    -- 🎉 no goals
#align omega_complete_partial_order.continuous_hom.bind OmegaCompletePartialOrder.ContinuousHom.bind
#align omega_complete_partial_order.continuous_hom.bind_apply OmegaCompletePartialOrder.ContinuousHom.bind_apply

/-- `Part.map` as a continuous function. -/
@[simps! apply] --Porting note: removed `(config := { rhsMd := reducible })`
noncomputable def map {β γ : Type v} (f : β → γ) (g : α →𝒄 Part β) : α →𝒄 Part γ :=
  .copy (fun x => f <$> g x) (bind g (const (pure ∘ f))) <| by
    ext1
    -- ⊢ f <$> ↑g x✝ = ↑(bind g (const (pure ∘ f))) x✝
    simp only [map_eq_bind_pure_comp, bind, coe_mk, OrderHom.bind_coe, coe_apply, coe_toOrderHom,
      const_apply]
#align omega_complete_partial_order.continuous_hom.map OmegaCompletePartialOrder.ContinuousHom.map
#align omega_complete_partial_order.continuous_hom.map_apply OmegaCompletePartialOrder.ContinuousHom.map_apply

/-- `Part.seq` as a continuous function. -/
@[simps! apply] --Porting note: removed `(config := { rhsMd := reducible })`
noncomputable def seq {β γ : Type v} (f : α →𝒄 Part (β → γ)) (g : α →𝒄 Part β) : α →𝒄 Part γ :=
  .copy (fun x => f x <*> g x) (bind f <| flip <| _root_.flip map g) <| by
      ext
      -- ⊢ (a✝ ∈ Seq.seq (↑f x✝) fun x => ↑g x✝) ↔ a✝ ∈ ↑(bind f (flip (_root_.flip map …
      simp only [seq_eq_bind_map, Part.bind_eq_bind, Part.mem_bind_iff, flip_apply, _root_.flip,
        map_apply, bind_apply]
#align omega_complete_partial_order.continuous_hom.seq OmegaCompletePartialOrder.ContinuousHom.seq
#align omega_complete_partial_order.continuous_hom.seq_apply OmegaCompletePartialOrder.ContinuousHom.seq_apply

end ContinuousHom

end OmegaCompletePartialOrder
