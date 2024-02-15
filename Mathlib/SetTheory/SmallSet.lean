import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Logic.Small.Defs
import Mathlib.Tactic.Set
import Mathlib.Tactic -- todo remove

set_option autoImplicit false

namespace Set

open Function

variable {α β : Type*} {f : α → β}

@[simp]
theorem injective_rangeFactorization :
    Injective (rangeFactorization f) ↔ Injective f := by
  simp [Injective, rangeFactorization]

@[simp]
theorem bijective_rangeFactorization :
    Bijective (rangeFactorization f) ↔ Injective f := by
  simp [Bijective, surjective_onto_range]

alias ⟨_, _root_.Function.Injective.rangeFactorization⟩ := injective_rangeFactorization

end Set

namespace Setoid

variable {α β : Type*}

def kerLift (f : α → β) : Quotient (ker f) → β :=
  Quotient.lift f fun _ _ h ↦ h

@[simp]
theorem kerLift_mk {f : α → β} (x : α) : kerLift f ⟦x⟧ = f x := rfl

theorem kerLift_injective (f : α → β) : Function.Injective (kerLift f) := by
  intro x y h
  induction x using Quotient.ind
  induction y using Quotient.ind
  set instSetoid : Setoid α := ker f
  simpa using h

end Setoid

-- Throughout this file, `u` represents the small universe and `v` represents the big universe.
universe u v

def SmallSet (α : Type v) : Type (max (u + 1) v) :=
  Quotient (Setoid.ker (fun ⟨_, f⟩ ↦ Set.range f : (ι : Type u) × (ι → α) → Set α))

namespace SmallSet

variable {α : Type v}

/-- Range of a function as a `SmallSet`.

This is the fundamental constructor for `SmallSet`.-/
def range {β : Type u} (f : β → α) : SmallSet α := Quotient.mk'' ⟨β, f⟩

/-- Interpret a `SmallSet α` as a `Set α`.

This is the fundamental eliminator for `SmallSet`.-/
instance instSetLike : SetLike (SmallSet α) α where
  coe := Setoid.kerLift _
  coe_injective' := Setoid.kerLift_injective _

/-- `SmallSet.range` corresponds to `Set.range` as expected.

This is the defining equation for `SmallSet`.-/
@[simp]
theorem coe_range {ι : Type u} (f : ι → α) : (range f : Set α) = Set.range f := rfl

/-- All `SmallSet`s are constructed from `SmallSet.range`.-/
@[eliminator]
theorem inductionOn {P : SmallSet α → Prop} (s : SmallSet α) (h : ∀ (ι : Type u) (f : ι → α), P (range f)) : P s := by
  induction s using Quotient.ind
  apply h

@[simp, norm_cast]
theorem mem_coe {a : α} {s : SmallSet α} : a ∈ (s : Set α) ↔ a ∈ (s : SmallSet α) :=
  Iff.rfl

@[simp]
theorem setOf_mem {α} {s : SmallSet α} : { a | a ∈ s } = s :=
  rfl

@[simp]
theorem coe_mem {s : SmallSet α} (x : (s : Set α)) : ↑x ∈ s :=
  x.2

theorem ext_iff {s₁ s₂ : SmallSet α} : s₁ = s₂ ↔ ∀ a, a ∈ s₁ ↔ a ∈ s₂ :=
  SetLike.ext_iff

@[ext]
theorem ext {s₁ s₂ : SmallSet α} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ :=
  SetLike.ext

@[simp, norm_cast]
theorem coe_inj {s₁ s₂ : SmallSet α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂ :=
  SetLike.coe_set_eq

@[simp]
theorem coe_eq_range {ι : Type u} {s : SmallSet α} (f : ι → α) : (s : Set α) = Set.range f ↔ s = range f := by
  rw [← coe_range, coe_inj]

@[simp]
theorem range_eq_coe {ι : Type u} {s : SmallSet α} (f : ι → α) : Set.range f = s ↔ range f = s := by
  rw [← coe_range, coe_inj]

@[simp]
theorem mem_range {ι : Type u} (f : ι → α) (x : α) : x ∈ range f ↔ ∃ i, f i = x := by
  rw [← mem_coe, coe_range, Set.mem_range]

noncomputable section Small

open Function

instance small_coe_sort (s : SmallSet.{u, v} α) : Small.{u, v} s := by
  induction' s with ι f
  rw [← SetLike.coe_sort_coe, coe_range]
  exact inferInstance
  -- let fInv := Set.rangeSplitting f
  -- suffices Bijective (Set.rangeFactorization fInv) from
  --   ⟨⟨Set.range fInv, ⟨Equiv.ofBijective _ this⟩⟩⟩
  -- simp [Set.rangeSplitting_injective]

theorem _root_.Set.small_coe_sort (s : Set α) :
    Small.{u} s ↔ ∃ (ι : Type u) (f : ι → α), s = Set.range f := by
  refine ⟨fun ⟨ι, ⟨f⟩⟩ ↦ ?_, fun ⟨ι, f, hf⟩ ↦ ?_⟩
  · use ι, Subtype.val ∘ f.symm
    simp
  · subst hf
    exact inferInstance

def ofSet_of_small (s : Set α) [Small.{u} s] : SmallSet.{u} α :=
  range (Subtype.val ∘ (equivShrink s).symm)

@[simp]
theorem coe_ofSet {s : Set α} {h : Small.{u} s} : (@ofSet_of_small α s h : Set α) = s := by
  simp [ofSet_of_small]

@[simp]
theorem mem_ofSet {s : Set α} {h : Small.{u} s} {x : α} : x ∈ @ofSet_of_small α s h ↔ x ∈ s := by
  rw [← mem_coe, coe_ofSet]

@[simp]
theorem ofSet_coe {s : SmallSet.{u} α} : ofSet_of_small s = s := by
  ext x
  simp

def equiv_small_set : SmallSet.{u} α ≃o {s : Set α // Small.{u} s} where
  toFun s := ⟨s, inferInstance⟩
  invFun := fun ⟨s, h⟩ ↦ ofSet_of_small s
  left_inv s := by simp
  right_inv := by
    rintro ⟨s, h⟩
    simp
  map_rel_iff' := by simp

-- /-- `s.τ : Type u` is the type of elements of `s`.

-- `s.τ` is equivalent to `↥s` except that it lives in a smaller universe.
-- TODO: Can we override the default coercion given by `SetLike`? -/
-- def τ (s : SmallSet α) : Type u := Shrink.{u} s

-- def equiv_τ (s : SmallSet α) : s ≃ s.τ := equivShrink s

-- namespace τ

-- def mk {s : SmallSet α} (x : α) (hx : x ∈ s) : s.τ := s.equiv_τ ⟨x, hx⟩

-- @[coe]
-- def val {s : SmallSet α} (x : s.τ) : α := s.equiv_τ.symm x

-- instance {s : SmallSet α} : CoeOut (s.τ) α where
--   coe := val

-- @[simp]
-- def prop {s : SmallSet α} (x : s.τ) : x.val ∈ s := (s.equiv_τ.symm x).prop

-- @[simp]
-- lemma

-- end τ
end Small

/-- Like `range`, but indexed by a `u`-small type. -/
def rangeS.{w} {ι : Type w} [Small.{u} ι] (f : ι → α) : SmallSet.{u} α := sorry

#check rangeS

instance : HasSubset (SmallSet α) where
  Subset := (· ≤ ·)

instance : IsPartialOrder (SmallSet α) (· ⊆ ·) :=
  inferInstanceAs (IsPartialOrder (SmallSet α) (· ≤ ·))

instance : HasSSubset (SmallSet α) where
  SSubset := (· < ·)

instance : IsStrictOrder (SmallSet α) (· ⊂ ·) :=
  inferInstanceAs (IsStrictOrder (SmallSet α) (· < ·))

instance : Inter (SmallSet α) where
  inter s t := sorry

instance : ConditionallyCompleteLattice (SmallSet α) where
  sup := (· ∩ ·)
  le_sup_left := sorry
  le_sup_right := sorry
  sup_le := sorry
  inf := sorry
  inf_le_left := sorry
  inf_le_right := sorry
  le_inf := sorry
  sSup := sorry
  sInf := sorry
  le_csSup := sorry
  csSup_le := sorry
  csInf_le := sorry
  le_csInf := sorry

instance : OrderBot (SmallSet α) where
  bot := sorry
  bot_le := sorry

instance [Small.{u} α] : BoundedOrder (SmallSet α) where
  top := sorry
  le_top := sorry

-- TODO: Should this be an instance? Seems like you wouldn't usually use `SmallSet.{u, u}`
def completeLattice [Small.{u} α] : CompleteLattice (SmallSet α) := sorry

end SmallSet
