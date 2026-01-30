/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Ira Fesefeldt
-/
module

public import Mathlib.Control.Monad.Basic
public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Order.Part
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.ScottContinuity

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

@[expose] public section

assert_not_exists IsOrderedMonoid

universe u v
variable {ι : Sort*} {α β γ δ : Type*}

namespace OmegaCompletePartialOrder

/-- A chain is a monotone sequence.

See the definition on page 114 of [gunter1992]. -/
def Chain (α : Type u) [Preorder α] :=
  ℕ →o α

namespace Chain
variable [Preorder α] [Preorder β] [Preorder γ]

instance : FunLike (Chain α) ℕ α := inferInstanceAs <| FunLike (ℕ →o α) ℕ α
instance : OrderHomClass (Chain α) ℕ α := inferInstanceAs <| OrderHomClass (ℕ →o α) ℕ α

/-- See note [partially-applied ext lemmas]. -/
@[ext] lemma ext ⦃f g : Chain α⦄ (h : ⇑f = ⇑g) : f = g := DFunLike.ext' h

instance [Inhabited α] : Inhabited (Chain α) :=
  ⟨⟨default, fun _ _ _ => le_rfl⟩⟩

instance : Membership α (Chain α) :=
  ⟨fun (c : ℕ →o α) a => ∃ i, a = c i⟩

variable (c c' : Chain α)
variable (f : α →o β)
variable (g : β →o γ)

instance : LE (Chain α) where le x y := ∀ i, ∃ j, x i ≤ y j

lemma isChain_range : IsChain (· ≤ ·) (Set.range c) := Monotone.isChain_range (OrderHomClass.mono c)

lemma directed : Directed (· ≤ ·) c := directedOn_range.2 c.isChain_range.directedOn

/-- `map` function for `Chain` -/
-- Not `@[simps]`: we need `@[simps!]` to see through the type synonym `Chain β = ℕ →o β`,
-- but then we'd get the `FunLike` instance for `OrderHom` instead.
def map : Chain β :=
  f.comp c

@[simp] theorem map_coe : ⇑(map c f) = f ∘ c := rfl

variable {f}

theorem mem_map (x : α) : x ∈ c → f x ∈ Chain.map c f :=
  fun ⟨i, h⟩ => ⟨i, h.symm ▸ rfl⟩

theorem exists_of_mem_map {b : β} : b ∈ c.map f → ∃ a, a ∈ c ∧ f a = b :=
  fun ⟨i, h⟩ => ⟨c i, ⟨i, rfl⟩, h.symm⟩

@[simp]
theorem mem_map_iff {b : β} : b ∈ c.map f ↔ ∃ a, a ∈ c ∧ f a = b :=
  ⟨exists_of_mem_map _, fun h => by
    rcases h with ⟨w, h, h'⟩
    subst b
    apply mem_map c _ h⟩

@[simp]
theorem map_id : c.map OrderHom.id = c :=
  OrderHom.comp_id _

theorem map_comp : (c.map f).map g = c.map (g.comp f) :=
  rfl

@[mono]
theorem map_le_map {g : α →o β} (h : f ≤ g) : c.map f ≤ c.map g :=
  fun i => by simp only [map_coe, Function.comp_apply]; exists i; apply h

/-- `OmegaCompletePartialOrder.Chain.zip` pairs up the elements of two chains
that have the same index. -/
-- Not `@[simps]`: we need `@[simps!]` to see through the type synonym `Chain β = ℕ →o β`,
-- but then we'd get the `FunLike` instance for `OrderHom` instead.
def zip (c₀ : Chain α) (c₁ : Chain β) : Chain (α × β) :=
  OrderHom.prod c₀ c₁

@[simp] theorem zip_coe (c₀ : Chain α) (c₁ : Chain β) (n : ℕ) : c₀.zip c₁ n = (c₀ n, c₁ n) := rfl

/-- An example of a `Chain` constructed from an ordered pair. -/
def pair (a b : α) (hab : a ≤ b) : Chain α where
  toFun
    | 0 => a
    | _ => b
  monotone' _ _ _ := by aesop

@[simp] lemma pair_zero (a b : α) (hab) : pair a b hab 0 = a := rfl
@[simp] lemma pair_succ (a b : α) (hab) (n : ℕ) : pair a b hab (n + 1) = b := rfl

@[simp] lemma range_pair (a b : α) (hab) : Set.range (pair a b hab) = {a, b} := by
  ext; exact Nat.or_exists_add_one.symm.trans (by aesop)

@[simp] lemma pair_zip_pair (a₁ a₂ : α) (b₁ b₂ : β) (ha hb) :
    (pair a₁ a₂ ha).zip (pair b₁ b₂ hb) = pair (a₁, b₁) (a₂, b₂) (Prod.le_def.2 ⟨ha, hb⟩) := by
  unfold Chain; ext n : 2; cases n <;> rfl

end Chain

end OmegaCompletePartialOrder

open OmegaCompletePartialOrder Chain

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

namespace OmegaCompletePartialOrder
variable [OmegaCompletePartialOrder α]

/-- Transfer an `OmegaCompletePartialOrder` on `β` to an `OmegaCompletePartialOrder` on `α`
using a strictly monotone function `f : β →o α`, a definition of ωSup and a proof that `f` is
continuous with regard to the provided `ωSup` and the ωCPO on `α`. -/
protected abbrev lift [PartialOrder β] (f : β →o α) (ωSup₀ : Chain β → β)
    (h : ∀ x y, f x ≤ f y → x ≤ y) (h' : ∀ c, f (ωSup₀ c) = ωSup (c.map f)) :
    OmegaCompletePartialOrder β where
  ωSup := ωSup₀
  ωSup_le c x hx := h _ _ (by rw [h']; apply ωSup_le; intro i; apply f.monotone (hx i))
  le_ωSup c i := h _ _ (by rw [h']; apply le_ωSup (c.map f))

theorem le_ωSup_of_le {c : Chain α} {x : α} (i : ℕ) (h : x ≤ c i) : x ≤ ωSup c :=
  le_trans h (le_ωSup c _)

theorem ωSup_total {c : Chain α} {x : α} (h : ∀ i, c i ≤ x ∨ x ≤ c i) : ωSup c ≤ x ∨ x ≤ ωSup c :=
  by_cases
    (fun (this : ∀ i, c i ≤ x) => Or.inl (ωSup_le _ _ this))
    (fun (this : ¬∀ i, c i ≤ x) =>
      have : ∃ i, ¬c i ≤ x := by simp only [not_forall] at this ⊢; assumption
      let ⟨i, hx⟩ := this
      have : x ≤ c i := (h i).resolve_left hx
      Or.inr <| le_ωSup_of_le _ this)

@[mono]
theorem ωSup_le_ωSup_of_le {c₀ c₁ : Chain α} (h : c₀ ≤ c₁) : ωSup c₀ ≤ ωSup c₁ :=
  (ωSup_le _ _) fun i => by
    obtain ⟨_, h⟩ := h i
    exact le_trans h (le_ωSup _ _)

@[simp] theorem ωSup_le_iff {c : Chain α} {x : α} : ωSup c ≤ x ↔ ∀ i, c i ≤ x := by
  constructor <;> intros
  · trans ωSup c
    · exact le_ωSup _ _
    · assumption
  exact ωSup_le _ _ ‹_›

lemma isLUB_range_ωSup (c : Chain α) : IsLUB (Set.range c) (ωSup c) := by
  constructor
  · simp only [upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
      Set.mem_setOf_eq]
    exact fun a ↦ le_ωSup c a
  · simp only [lowerBounds, upperBounds, Set.mem_range, forall_exists_index,
      forall_apply_eq_imp_iff, Set.mem_setOf_eq]
    exact fun ⦃a⦄ a_1 ↦ ωSup_le c a a_1

lemma ωSup_eq_of_isLUB {c : Chain α} {a : α} (h : IsLUB (Set.range c) a) : a = ωSup c := by
  rw [le_antisymm_iff]
  simp only [IsLUB, IsLeast, upperBounds, lowerBounds, Set.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff, Set.mem_setOf_eq] at h
  constructor
  · apply h.2
    exact fun a ↦ le_ωSup c a
  · rw [ωSup_le_iff]
    apply h.1

/-- A subset `p : α → Prop` of the type closed under `ωSup` induces an
`OmegaCompletePartialOrder` on the subtype `{a : α // p a}`. -/
def subtype {α : Type*} [OmegaCompletePartialOrder α] (p : α → Prop)
    (hp : ∀ c : Chain α, (∀ i ∈ c, p i) → p (ωSup c)) : OmegaCompletePartialOrder (Subtype p) :=
  OmegaCompletePartialOrder.lift (OrderHom.Subtype.val p)
    (fun c => ⟨ωSup _, hp (c.map (OrderHom.Subtype.val p)) fun _ ⟨n, q⟩ => q.symm ▸ (c n).2⟩)
    (fun _ _ h => h) (fun _ => rfl)

section Continuity

variable [OmegaCompletePartialOrder β]
variable [OmegaCompletePartialOrder γ]
variable {f : α → β} {g : β → γ}

/-- A function `f` between `ω`-complete partial orders is `ωScottContinuous` if it is
Scott continuous over chains. -/
@[fun_prop]
def ωScottContinuous (f : α → β) : Prop :=
    ScottContinuousOn (Set.range fun c : Chain α => Set.range c) f

lemma _root_.ScottContinuous.ωScottContinuous (hf : ScottContinuous f) : ωScottContinuous f :=
  hf.scottContinuousOn

lemma ωScottContinuous.monotone (h : ωScottContinuous f) : Monotone f :=
  ScottContinuousOn.monotone _ (fun a b hab => by
    use pair a b hab; exact range_pair a b hab) h

lemma ωScottContinuous.isLUB {c : Chain α} (hf : ωScottContinuous f) :
    IsLUB (Set.range (c.map ⟨f, hf.monotone⟩)) (f (ωSup c)) := by
  simpa [map_coe, OrderHom.coe_mk, Set.range_comp]
    using hf (by simp) (Set.range_nonempty _) (isChain_range c).directedOn (isLUB_range_ωSup c)

@[fun_prop, to_fun (attr := simp)]
lemma ωScottContinuous.id : ωScottContinuous (id : α → α) := ScottContinuousOn.id

lemma ωScottContinuous.map_ωSup (hf : ωScottContinuous f) (c : Chain α) :
    f (ωSup c) = ωSup (c.map ⟨f, hf.monotone⟩) := ωSup_eq_of_isLUB hf.isLUB

/-- `ωScottContinuous f` asserts that `f` is both monotone and distributes over ωSup. -/
lemma ωScottContinuous_iff_monotone_map_ωSup :
    ωScottContinuous f ↔ ∃ hf : Monotone f, ∀ c : Chain α, f (ωSup c) = ωSup (c.map ⟨f, hf⟩) := by
  refine ⟨fun hf ↦ ⟨hf.monotone, hf.map_ωSup⟩, ?_⟩
  intro hf _ ⟨c, hc⟩ _ _ _ hda
  convert isLUB_range_ωSup (c.map { toFun := f, monotone' := hf.1 })
  · rw [map_coe, OrderHom.coe_mk, ← hc, ← (Set.range_comp f ⇑c)]
  · rw [← hc] at hda
    rw [← hf.2 c, ωSup_eq_of_isLUB hda]

alias ⟨ωScottContinuous.monotone_map_ωSup, ωScottContinuous.of_monotone_map_ωSup⟩ :=
  ωScottContinuous_iff_monotone_map_ωSup

/- A monotone function `f : α →o β` is ωScott continuous if and only if it distributes over ωSup. -/
lemma ωScottContinuous_iff_map_ωSup_of_orderHom {f : α →o β} :
    ωScottContinuous f ↔ ∀ c : Chain α, f (ωSup c) = ωSup (c.map f) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  exact exists_prop_of_true f.monotone'

alias ⟨ωScottContinuous.map_ωSup_of_orderHom, ωScottContinuous.of_map_ωSup_of_orderHom⟩ :=
  ωScottContinuous_iff_map_ωSup_of_orderHom

attribute [local push ←] Function.comp_def
attribute [local push] Function.const_def

@[fun_prop, to_fun]
lemma ωScottContinuous.comp (hg : ωScottContinuous g) (hf : ωScottContinuous f) :
    ωScottContinuous (g.comp f) :=
  ωScottContinuous.of_monotone_map_ωSup
    ⟨hg.monotone.comp hf.monotone, by simp [hf.map_ωSup, hg.map_ωSup, map_comp]⟩

@[fun_prop, to_fun (attr := simp)]
lemma ωScottContinuous.const {x : β} : ωScottContinuous (Function.const α x) :=
  ScottContinuousOn.const x

end Continuity

end OmegaCompletePartialOrder

namespace Part

theorem eq_of_chain {c : Chain (Part α)} {a b : α} (ha : some a ∈ c) (hb : some b ∈ c) : a = b := by
  obtain ⟨i, ha⟩ := ha; replace ha := ha.symm
  obtain ⟨j, hb⟩ := hb; replace hb := hb.symm
  rw [eq_some_iff] at ha hb
  rcases le_total i j with hij | hji
  · have := c.monotone hij _ ha; apply mem_unique this hb
  · have := c.monotone hji _ hb; apply Eq.symm; apply mem_unique this ha

open Classical in
/-- The (noncomputable) `ωSup` definition for the `ω`-CPO structure on `Part α`. -/
protected noncomputable def ωSup (c : Chain (Part α)) : Part α :=
  if h : ∃ a, some a ∈ c then some (Classical.choose h) else none

theorem ωSup_eq_some {c : Chain (Part α)} {a : α} (h : some a ∈ c) : Part.ωSup c = some a :=
  have : ∃ a, some a ∈ c := ⟨a, h⟩
  have a' : some (Classical.choose this) ∈ c := Classical.choose_spec this
  calc
    Part.ωSup c = some (Classical.choose this) := dif_pos this
    _ = some a := congr_arg _ (eq_of_chain a' h)

theorem ωSup_eq_none {c : Chain (Part α)} (h : ¬∃ a, some a ∈ c) : Part.ωSup c = none :=
  dif_neg h

theorem mem_chain_of_mem_ωSup {c : Chain (Part α)} {a : α} (h : a ∈ Part.ωSup c) : some a ∈ c := by
  simp only [Part.ωSup] at h; split_ifs at h with h_1
  · have h' := Classical.choose_spec h_1
    rw [← eq_some_iff] at h
    rw [← h]
    exact h'
  · rcases h with ⟨⟨⟩⟩

noncomputable instance omegaCompletePartialOrder :
    OmegaCompletePartialOrder (Part α) where
  ωSup := Part.ωSup
  le_ωSup c i := by
    intro x hx
    rw [← eq_some_iff] at hx ⊢
    rw [ωSup_eq_some]
    rw [← hx]
    exact ⟨i, rfl⟩
  ωSup_le := by
    rintro c x hx a ha
    replace ha := mem_chain_of_mem_ωSup ha
    obtain ⟨i, ha⟩ := ha
    apply hx i
    rw [← ha]
    apply mem_some

section Inst

theorem mem_ωSup (x : α) (c : Chain (Part α)) : x ∈ ωSup c ↔ some x ∈ c := by
  simp only [ωSup, Part.ωSup]
  constructor
  · split_ifs with h
    swap
    · rintro ⟨⟨⟩⟩
    intro h'
    have hh := Classical.choose_spec h
    simp only [mem_some_iff] at h'
    subst x
    exact hh
  · intro h
    have h' : ∃ a : α, some a ∈ c := ⟨_, h⟩
    rw [dif_pos h']
    have hh := Classical.choose_spec h'
    rw [eq_of_chain hh h]
    simp

end Inst

end Part

section Pi

variable {β : α → Type*}

instance [∀ a, OmegaCompletePartialOrder (β a)] :
    OmegaCompletePartialOrder (∀ a, β a) where
  ωSup c a := ωSup (c.map (Pi.evalOrderHom a))
  ωSup_le _ _ hf a :=
    ωSup_le _ _ <| by
      rintro i
      apply hf
  le_ωSup _ _ _ := le_ωSup_of_le _ <| le_rfl

namespace OmegaCompletePartialOrder

variable [∀ x, OmegaCompletePartialOrder <| β x]
variable [OmegaCompletePartialOrder γ]
variable {f : γ → ∀ x, β x}

lemma ωScottContinuous.apply₂ (hf : ωScottContinuous f) (a : α) : ωScottContinuous (f · a) :=
  ωScottContinuous.of_monotone_map_ωSup
    ⟨fun _ _ h ↦ hf.monotone h a, fun c ↦ congr_fun (hf.map_ωSup c) a⟩

@[fun_prop]
lemma ωScottContinuous.apply (x : α) : ωScottContinuous (fun f : ∀ x, β x ↦ f x) :=
  apply₂ id x

@[fun_prop]
lemma ωScottContinuous.of_apply₂ (hf : ∀ a, ωScottContinuous (f · a)) : ωScottContinuous f :=
  ωScottContinuous.of_monotone_map_ωSup
    ⟨fun _ _ h a ↦ (hf a).monotone h, fun c ↦ by ext a; apply (hf a).map_ωSup c⟩

lemma ωScottContinuous_iff_apply₂ : ωScottContinuous f ↔ ∀ a, ωScottContinuous (f · a) :=
  ⟨ωScottContinuous.apply₂, ωScottContinuous.of_apply₂⟩

end OmegaCompletePartialOrder

end Pi

namespace Prod

variable [OmegaCompletePartialOrder α]
variable [OmegaCompletePartialOrder β]
variable [OmegaCompletePartialOrder γ]

/-- The supremum of a chain in the product `ω`-CPO. -/
@[simps]
protected def ωSupImpl (c : Chain (α × β)) : α × β :=
  (ωSup (c.map OrderHom.fst), ωSup (c.map OrderHom.snd))

@[simps! ωSup_fst ωSup_snd]
instance : OmegaCompletePartialOrder (α × β) where
  ωSup := Prod.ωSupImpl
  ωSup_le := fun _ _ h => ⟨ωSup_le _ _ fun i => (h i).1, ωSup_le _ _ fun i => (h i).2⟩
  le_ωSup c i := ⟨le_ωSup (c.map OrderHom.fst) i, le_ωSup (c.map OrderHom.snd) i⟩

theorem ωSup_zip (c₀ : Chain α) (c₁ : Chain β) : ωSup (c₀.zip c₁) = (ωSup c₀, ωSup c₁) := rfl

@[fun_prop]
lemma ωScottContinuous.prodMk
    {f : α → β} (hf : ωScottContinuous f)
    {g : α → γ} (hg : ωScottContinuous g) :
    ωScottContinuous fun x ↦ (f x, g x) :=
  ScottContinuousOn.prodMk (fun a b hab ↦ ⟨pair a b hab, range_pair a b hab⟩) hf hg

@[fun_prop]
lemma ωScottContinuous_fst : ωScottContinuous (Prod.fst : α × β → α) :=
  ScottContinuousOn.fst

@[fun_prop]
lemma ωScottContinuous_snd : ωScottContinuous (Prod.snd : α × β → β) :=
  ScottContinuousOn.snd

end Prod

namespace CompleteLattice

-- see Note [lower instance priority]
/-- Any complete lattice has an `ω`-CPO structure where the countable supremum is a special case
of arbitrary suprema. -/
instance (priority := 100) [CompleteLattice α] : OmegaCompletePartialOrder α where
  ωSup c := ⨆ i, c i
  ωSup_le := fun ⟨c, _⟩ s hs => by simpa only [iSup_le_iff]
  le_ωSup := fun ⟨c, _⟩ i => le_iSup_of_le i le_rfl

variable [OmegaCompletePartialOrder α] [CompleteLattice β] {f g : α → β}

lemma ωScottContinuous.iSup {f : ι → α → β} (hf : ∀ i, ωScottContinuous (f i)) :
    ωScottContinuous (⨆ i, f i) := by
  refine ωScottContinuous.of_monotone_map_ωSup
    ⟨Monotone.iSup fun i ↦ (hf i).monotone, fun c ↦ eq_of_forall_ge_iff fun a ↦ ?_⟩
  simp +contextual [ωSup_le_iff, (hf _).map_ωSup, @forall_swap ι]

lemma ωScottContinuous.sSup {s : Set (α → β)} (hs : ∀ f ∈ s, ωScottContinuous f) :
    ωScottContinuous (sSup s) := by
  rw [sSup_eq_iSup]; exact ωScottContinuous.iSup fun f ↦ ωScottContinuous.iSup <| hs f

lemma ωScottContinuous.sup (hf : ωScottContinuous f) (hg : ωScottContinuous g) :
    ωScottContinuous (f ⊔ g) := by
  rw [← sSup_pair]
  apply ωScottContinuous.sSup
  rintro f (rfl | rfl | _) <;> assumption

lemma ωScottContinuous.top : ωScottContinuous (⊤ : α → β) :=
  ωScottContinuous.of_monotone_map_ωSup
    ⟨monotone_const, fun c ↦ eq_of_forall_ge_iff fun a ↦ by simp⟩

lemma ωScottContinuous.bot : ωScottContinuous (⊥ : α → β) := by
  rw [← sSup_empty]; exact ωScottContinuous.sSup (by simp)

end CompleteLattice

namespace CompleteLattice

variable [OmegaCompletePartialOrder α] [CompleteLinearOrder β] {f g : α → β}

-- TODO Prove this result for `ScottContinuousOn` and deduce this as a special case
-- Also consider if it holds in greater generality (e.g. finite sets)
-- N.B. The Scott Topology coincides with the Upper Topology on a Complete Linear Order
-- `Topology.IsScott.scott_eq_upper_of_completeLinearOrder`
-- We have that the product topology coincides with the upper topology
-- https://github.com/leanprover-community/mathlib4/pull/12133
lemma ωScottContinuous.inf (hf : ωScottContinuous f) (hg : ωScottContinuous g) :
    ωScottContinuous (f ⊓ g) := by
  refine ωScottContinuous.of_monotone_map_ωSup
    ⟨hf.monotone.inf hg.monotone, fun c ↦ eq_of_forall_ge_iff fun a ↦ ?_⟩
  simp only [Pi.inf_apply, hf.map_ωSup c, hg.map_ωSup c, inf_le_iff, ωSup_le_iff, Chain.map_coe,
    Function.comp, OrderHom.coe_mk, ← forall_or_left, ← forall_or_right]
  exact ⟨fun h _ ↦ h _ _, fun h i j ↦
    (h (max j i)).imp (le_trans <| hf.monotone <| c.mono <| le_max_left _ _)
      (le_trans <| hg.monotone <| c.mono <| le_max_right _ _)⟩

end CompleteLattice

namespace OmegaCompletePartialOrder
variable [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
variable [OmegaCompletePartialOrder γ] [OmegaCompletePartialOrder δ]

namespace OrderHom

/-- The `ωSup` operator for monotone functions. -/
@[simps]
protected def ωSup (c : Chain (α →o β)) : α →o β where
  toFun a := ωSup (c.map (OrderHom.apply a))
  monotone' _ _ h := ωSup_le_ωSup_of_le ((Chain.map_le_map _) fun a => a.monotone h)

@[simps! ωSup_coe]
instance omegaCompletePartialOrder : OmegaCompletePartialOrder (α →o β) :=
  OmegaCompletePartialOrder.lift OrderHom.coeFnHom OrderHom.ωSup (fun _ _ h => h) fun _ => rfl

end OrderHom

variable (α β) in
/-- A monotone function on `ω`-continuous partial orders is said to be continuous
if for every chain `c : chain α`, `f (⊔ i, c i) = ⊔ i, f (c i)`.
This is just the bundled version of `OrderHom.continuous`. -/
structure ContinuousHom extends OrderHom α β where
  /-- The underlying function of a `ContinuousHom` is continuous, i.e. it preserves `ωSup` -/
  protected map_ωSup' (c : Chain α) : toFun (ωSup c) = ωSup (c.map toOrderHom)

attribute [nolint docBlame] ContinuousHom.toOrderHom

@[inherit_doc] infixr:25 " →𝒄 " => ContinuousHom -- Input: \r\MIc

instance : FunLike (α →𝒄 β) α β where
  coe f := f.toFun
  coe_injective' := by rintro ⟨⟩ ⟨⟩ h; congr; exact DFunLike.ext' h

instance : OrderHomClass (α →𝒄 β) α β where
  map_rel f _ _ h := f.mono h

instance : PartialOrder (α →𝒄 β) :=
  (PartialOrder.lift fun f => f.toOrderHom.toFun) <| by rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ h; congr

namespace ContinuousHom

@[fun_prop]
protected lemma ωScottContinuous (f : α →𝒄 β) : ωScottContinuous f :=
  ωScottContinuous.of_map_ωSup_of_orderHom f.map_ωSup'

-- Not a `simp` lemma because in many cases projection is simpler than a generic coercion
theorem toOrderHom_eq_coe (f : α →𝒄 β) : f.1 = f := rfl

@[simp] theorem coe_mk (f : α →o β) (hf) : ⇑(mk f hf) = f := rfl

@[simp] theorem coe_toOrderHom (f : α →𝒄 β) : ⇑f.1 = f := rfl

/-- See Note [custom simps projection]. We specify this explicitly because we don't have a DFunLike
instance.
-/
def Simps.apply (h : α →𝒄 β) : α → β :=
  h

initialize_simps_projections ContinuousHom (toFun → apply)

/-- Constructs a `ContinuousHom` from a function `f` and a proof of `ωScottContinuous f`.
By default, the proof is inferred by `fun_prop`, which makes it ideal for simple cases.
-/
@[simps!]
def ofFun (f : α → β) (hf : ωScottContinuous f := by fun_prop) : α →𝒄 β where
  toFun := f
  monotone' := hf.monotone
  map_ωSup' := hf.map_ωSup

protected theorem congr_fun {f g : α →𝒄 β} (h : f = g) (x : α) : f x = g x :=
  DFunLike.congr_fun h x

protected theorem congr_arg (f : α →𝒄 β) {x y : α} (h : x = y) : f x = f y :=
  congr_arg f h

protected theorem monotone (f : α →𝒄 β) : Monotone f :=
  f.monotone'

@[mono]
theorem apply_mono {f g : α →𝒄 β} {x y : α} (h₁ : f ≤ g) (h₂ : x ≤ y) : f x ≤ g y :=
  OrderHom.apply_mono (show (f : α →o β) ≤ g from h₁) h₂

theorem ωSup_bind {β γ : Type v} (c : Chain α) (f : α →o Part β) (g : α →o β → Part γ) :
    ωSup (c.map (f.partBind g)) = ωSup (c.map f) >>= ωSup (c.map g) := by
  apply eq_of_forall_ge_iff; intro x
  simp only [ωSup_le_iff, Part.bind_le]
  constructor <;> intro h'''
  · intro b hb
    apply ωSup_le _ _ _
    rintro i y hy
    simp only [Part.mem_ωSup] at hb
    rcases hb with ⟨j, hb⟩
    replace hb := hb.symm
    simp only [Part.eq_some_iff, Chain.map_coe, Function.comp_apply] at hy hb
    replace hb : b ∈ f (c (max i j)) := f.mono (c.mono (le_max_right i j)) _ hb
    replace hy : y ∈ g (c (max i j)) b := g.mono (c.mono (le_max_left i j)) _ _ hy
    apply h''' (max i j)
    simp only [Part.mem_bind_iff, Chain.map_coe,
      Function.comp_apply, OrderHom.partBind_coe]
    exact ⟨_, hb, hy⟩
  · intro i y hy
    simp only [Part.mem_bind_iff, Chain.map_coe,
      Function.comp_apply, OrderHom.partBind_coe] at hy
    rcases hy with ⟨b, hb₀, hb₁⟩
    apply h''' b _
    · apply le_ωSup (c.map g) _ _ _ hb₁
    · apply le_ωSup (c.map f) i _ hb₀

-- TODO: We should move `ωScottContinuous` to the root namespace
lemma ωScottContinuous.bind {β γ} {f : α → Part β} {g : α → β → Part γ} (hf : ωScottContinuous f)
    (hg : ωScottContinuous g) : ωScottContinuous fun x ↦ f x >>= g x :=
  ωScottContinuous.of_monotone_map_ωSup
    ⟨hf.monotone.partBind hg.monotone, fun c ↦ by rw [hf.map_ωSup, hg.map_ωSup, ← ωSup_bind]; rfl⟩

lemma ωScottContinuous.map {β γ} {f : β → γ} {g : α → Part β} (hg : ωScottContinuous g) :
    ωScottContinuous fun x ↦ f <$> g x := by
  simpa only [map_eq_bind_pure_comp] using ωScottContinuous.bind hg ωScottContinuous.const

lemma ωScottContinuous.seq {β γ} {f : α → Part (β → γ)} {g : α → Part β} (hf : ωScottContinuous f)
    (hg : ωScottContinuous g) : ωScottContinuous fun x ↦ f x <*> g x := by
  simp only [seq_eq_bind_map]
  exact ωScottContinuous.bind hf <| ωScottContinuous.of_apply₂ fun _ ↦ ωScottContinuous.map hg

theorem continuous (F : α →𝒄 β) (C : Chain α) : F (ωSup C) = ωSup (C.map F) :=
  F.ωScottContinuous.map_ωSup _

/-- Construct a continuous function from a bare function, a continuous function, and a proof that
they are equal. -/
@[simps!]
def copy (f : α → β) (g : α →𝒄 β) (h : f = g) : α →𝒄 β where
  toOrderHom := g.1.copy f h
  map_ωSup' := by rw [OrderHom.copy_eq]; exact g.map_ωSup'

/-- The identity as a continuous function. -/
@[simps!]
def id : α →𝒄 α := ⟨OrderHom.id, ωScottContinuous.id.map_ωSup⟩

/-- The composition of continuous functions. -/
@[simps!]
def comp (f : β →𝒄 γ) (g : α →𝒄 β) : α →𝒄 γ :=
  ⟨.comp f.1 g.1, (f.ωScottContinuous.comp g.ωScottContinuous).map_ωSup⟩

@[ext]
protected theorem ext (f g : α →𝒄 β) (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

protected theorem coe_inj (f g : α →𝒄 β) (h : (f : α → β) = g) : f = g :=
  DFunLike.ext' h

@[simp]
theorem comp_id (f : β →𝒄 γ) : f.comp id = f := rfl

@[simp]
theorem id_comp (f : β →𝒄 γ) : id.comp f = f := rfl

@[simp]
theorem comp_assoc (f : γ →𝒄 δ) (g : β →𝒄 γ) (h : α →𝒄 β) : f.comp (g.comp h) = (f.comp g).comp h :=
  rfl

@[simp]
theorem coe_apply (a : α) (f : α →𝒄 β) : (f : α →o β) a = f a :=
  rfl

/-- `Function.const` is a continuous function. -/
@[simps!]
def const (x : β) : α →𝒄 β := ⟨.const _ x, ωScottContinuous.const.map_ωSup⟩

instance [Inhabited β] : Inhabited (α →𝒄 β) :=
  ⟨const default⟩

/-- The map from continuous functions to monotone functions is itself a monotone function. -/
@[simps]
def toMono : (α →𝒄 β) →o α →o β where
  toFun f := f
  monotone' _ _ h := h

/-- When proving that a chain of applications is below a bound `z`, it suffices to consider the
functions and values being selected from the same index in the chains.

This lemma is more specific than necessary, i.e. `c₀` only needs to be a
chain of monotone functions, but it is only used with continuous functions. -/
@[simp]
theorem forall_forall_merge (c₀ : Chain (α →𝒄 β)) (c₁ : Chain α) (z : β) :
    (∀ i j : ℕ, (c₀ i) (c₁ j) ≤ z) ↔ ∀ i : ℕ, (c₀ i) (c₁ i) ≤ z := by
  constructor <;> introv h
  · apply h
  · apply le_trans _ (h (max i j))
    trans c₀ i (c₁ (max i j))
    · apply (c₀ i).monotone
      apply c₁.monotone
      apply le_max_right
    · apply c₀.monotone
      apply le_max_left

@[simp]
theorem forall_forall_merge' (c₀ : Chain (α →𝒄 β)) (c₁ : Chain α) (z : β) :
    (∀ j i : ℕ, (c₀ i) (c₁ j) ≤ z) ↔ ∀ i : ℕ, (c₀ i) (c₁ i) ≤ z := by
  rw [forall_swap, forall_forall_merge]

/-- The `ωSup` operator for continuous functions, which takes the pointwise countable supremum
of the functions in the `ω`-chain. -/
@[simps!]
protected def ωSup (c : Chain (α →𝒄 β)) : α →𝒄 β where
  toOrderHom := ωSup <| c.map toMono
  map_ωSup' c' := eq_of_forall_ge_iff fun a ↦ by simp [(c _).ωScottContinuous.map_ωSup]

@[simps ωSup]
instance : OmegaCompletePartialOrder (α →𝒄 β) :=
  OmegaCompletePartialOrder.lift ContinuousHom.toMono ContinuousHom.ωSup
    (fun _ _ h => h) (fun _ => rfl)

@[fun_prop]
lemma ωScottContinuous_apply
    {f : α → β →𝒄 γ} (hf : ωScottContinuous f) {g : α → β} (hg : ωScottContinuous g) :
    ωScottContinuous fun x ↦ f x (g x) := by
  apply ωScottContinuous.of_monotone_map_ωSup ⟨?_, fun c ↦ ?_⟩
  · intro x y hxy
    apply OrderHom.apply_mono (hf.monotone hxy) (hg.monotone hxy)
  · rw [hf.map_ωSup, hg.map_ωSup]
    simp only [ωSup_def, ωSup_apply]
    apply le_antisymm
    · apply ωSup_le
      intro i
      dsimp
      rw [(f (c i)).continuous]
      apply ωSup_le
      intro j
      apply le_ωSup_of_le (i ⊔ j)
      apply apply_mono
      · apply hf.monotone (c.monotone le_sup_left)
      · apply hg.monotone (c.monotone le_sup_right)
    · simp only [ωSup_le_iff]
      intro i
      apply le_ωSup_of_le i
      apply (f (c i)).monotone
      apply le_ωSup_of_le i
      rfl

namespace Prod

/-- The application of continuous functions as a continuous function. -/
@[simps!]
def apply : (α →𝒄 β) × α →𝒄 β := ofFun (fun f ↦ f.1 f.2)

end Prod

theorem ωSup_apply_ωSup (c₀ : Chain (α →𝒄 β)) (c₁ : Chain α) :
    ωSup c₀ (ωSup c₁) = Prod.apply (ωSup (c₀.zip c₁)) := by simp [Prod.apply_apply, Prod.ωSup_zip]

/-- A family of continuous functions yields a continuous family of functions. -/
@[simps!]
def flip {α : Type*} (f : α → β →𝒄 γ) : β →𝒄 α → γ :=
  ofFun fun x y ↦ f y x

/-- `Part.bind` as a continuous function. -/
@[simps! apply]
noncomputable def bind {β γ : Type v} (f : α →𝒄 Part β) (g : α →𝒄 β → Part γ) : α →𝒄 Part γ :=
  .mk (OrderHom.partBind f g.toOrderHom) fun c => by
    rw [ωSup_bind, ← f.continuous, g.toOrderHom_eq_coe, ← g.continuous]
    rfl

/-- `Part.map` as a continuous function. -/
@[simps! apply]
noncomputable def map {β γ : Type v} (f : β → γ) (g : α →𝒄 Part β) : α →𝒄 Part γ :=
  .copy (fun x => f <$> g x) (bind g (const (pure ∘ f))) <| by
    ext1
    simp only [map_eq_bind_pure_comp, bind, coe_mk, OrderHom.partBind_coe, coe_apply,
      coe_toOrderHom, const_apply, Part.bind_eq_bind]

/-- `Part.seq` as a continuous function. -/
@[simps! apply]
noncomputable def seq {β γ : Type v} (f : α →𝒄 Part (β → γ)) (g : α →𝒄 Part β) : α →𝒄 Part γ :=
  .copy (fun x => f x <*> g x) (bind f <| flip <| _root_.flip map g) <| by
      ext
      simp only [seq_eq_bind_map, Part.bind_eq_bind, Part.mem_bind_iff, flip_apply, _root_.flip,
        map_apply, bind_apply, Part.map_eq_map]

end ContinuousHom

namespace fixedPoints

open Function

/-- Iteration of a function on an initial element interpreted as a chain. -/
def iterateChain (f : α →o α) (x : α) (h : x ≤ f x) : Chain α :=
  ⟨fun n => f^[n] x, f.monotone.monotone_iterate_of_le_map h⟩

variable (f : α →𝒄 α) (x : α)

/-- The supremum of iterating a function on x arbitrary often is a fixed point -/
theorem ωSup_iterate_mem_fixedPoint (h : x ≤ f x) :
    ωSup (iterateChain f x h) ∈ fixedPoints f := by
  rw [mem_fixedPoints, IsFixedPt, f.continuous]
  apply le_antisymm
  · apply ωSup_le
    intro n
    simp only [Chain.map_coe, OrderHomClass.coe_coe, comp_apply]
    have : iterateChain f x h (n.succ) = f (iterateChain f x h n) :=
      Function.iterate_succ_apply' ..
    rw [← this]
    apply le_ωSup
  · apply ωSup_le
    rintro (_ | n)
    · apply le_trans h
      change ((iterateChain f x h).map f) 0 ≤ ωSup ((iterateChain f x h).map (f : α →o α))
      apply le_ωSup
    · have : iterateChain f x h (n.succ) = (iterateChain f x h).map f n :=
        Function.iterate_succ_apply' ..
      rw [this]
      apply le_ωSup

/-- The supremum of iterating a function on x arbitrary often is smaller than any prefixed point.

A prefixed point is a value `a` with `f a ≤ a`. -/
theorem ωSup_iterate_le_prefixedPoint (h : x ≤ f x) {a : α}
    (h_a : f a ≤ a) (h_x_le_a : x ≤ a) :
    ωSup (iterateChain f x h) ≤ a := by
  apply ωSup_le
  intro n
  induction n with
  | zero => exact h_x_le_a
  | succ n h_ind =>
    have : iterateChain f x h (n.succ) = f (iterateChain f x h n) :=
      Function.iterate_succ_apply' ..
    rw [this]
    exact le_trans (f.monotone h_ind) h_a

/-- The supremum of iterating a function on x arbitrary often is smaller than any fixed point. -/
theorem ωSup_iterate_le_fixedPoint (h : x ≤ f x) {a : α}
    (h_a : a ∈ fixedPoints f) (h_x_le_a : x ≤ a) :
    ωSup (iterateChain f x h) ≤ a := by
  rw [mem_fixedPoints] at h_a
  obtain h_a := Eq.le h_a
  exact ωSup_iterate_le_prefixedPoint f x h h_a h_x_le_a

end fixedPoints

end OmegaCompletePartialOrder
