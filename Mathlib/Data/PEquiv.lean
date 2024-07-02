/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Data.Option.Basic
import Mathlib.Data.Set.Basic

#align_import data.pequiv from "leanprover-community/mathlib"@"7c3269ca3fa4c0c19e4d127cd7151edbdbf99ed4"

/-!

# Partial Equivalences

In this file, we define partial equivalences `PEquiv`, which are a bijection between a subset of `α`
and a subset of `β`. Notationally, a `PEquiv` is denoted by "`≃.`" (note that the full stop is part
of the notation). The way we store these internally is with two functions `f : α → Option β` and
the reverse function `g : β → Option α`, with the condition that if `f a` is `some b`,
then `g b` is `some a`.

## Main results

- `PEquiv.ofSet`: creates a `PEquiv` from a set `s`,
  which sends an element to itself if it is in `s`.
- `PEquiv.single`: given two elements `a : α` and `b : β`, create a `PEquiv` that sends them to
  each other, and ignores all other elements.
- `PEquiv.injective_of_forall_ne_isSome`/`injective_of_forall_isSome`: If the domain of a `PEquiv`
  is all of `α` (except possibly one point), its `toFun` is injective.

## Canonical order

`PEquiv` is canonically ordered by inclusion; that is, if a function `f` defined on a subset `s`
is equal to `g` on that subset, but `g` is also defined on a larger set, then `f ≤ g`. We also have
a definition of `⊥`, which is the empty `PEquiv` (sends all to `none`), which in the end gives us a
`SemilatticeInf` with an `OrderBot` instance.

## Tags

pequiv, partial equivalence

-/


universe u v w x

/-- A `PEquiv` is a partial equivalence, a representation of a bijection between a subset
  of `α` and a subset of `β`. See also `PartialEquiv` for a version that requires `toFun` and
`invFun` to be globally defined functions and has `source` and `target` sets as extra fields. -/
structure PEquiv (α : Type u) (β : Type v) where
  /-- The underlying partial function of a `PEquiv` -/
  toFun : α → Option β
  /-- The partial inverse of `toFun` -/
  invFun : β → Option α
  /-- `invFun` is the partial inverse of `toFun`  -/
  inv : ∀ (a : α) (b : β), a ∈ invFun b ↔ b ∈ toFun a
#align pequiv PEquiv

/-- A `PEquiv` is a partial equivalence, a representation of a bijection between a subset
  of `α` and a subset of `β`. See also `PartialEquiv` for a version that requires `toFun` and
`invFun` to be globally defined functions and has `source` and `target` sets as extra fields. -/
infixr:25 " ≃. " => PEquiv

namespace PEquiv

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

open Function Option

instance : FunLike (α ≃. β) α (Option β) :=
  { coe := toFun
    coe_injective' := by
      rintro ⟨f₁, f₂, hf⟩ ⟨g₁, g₂, hg⟩ (rfl : f₁ = g₁)
      congr with y x
      simp only [hf, hg] }

@[simp] theorem coe_mk (f₁ : α → Option β) (f₂ h) : (mk f₁ f₂ h : α → Option β) = f₁ :=
  rfl

theorem coe_mk_apply (f₁ : α → Option β) (f₂ : β → Option α) (h) (x : α) :
    (PEquiv.mk f₁ f₂ h : α → Option β) x = f₁ x :=
  rfl
#align pequiv.coe_mk_apply PEquiv.coe_mk_apply

@[ext] theorem ext {f g : α ≃. β} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h
#align pequiv.ext PEquiv.ext

theorem ext_iff {f g : α ≃. β} : f = g ↔ ∀ x, f x = g x :=
  DFunLike.ext_iff
#align pequiv.ext_iff PEquiv.ext_iff

/-- The identity map as a partial equivalence. -/
@[refl]
protected def refl (α : Type*) : α ≃. α where
  toFun := some
  invFun := some
  inv _ _ := eq_comm
#align pequiv.refl PEquiv.refl

/-- The inverse partial equivalence. -/
@[symm]
protected def symm (f : α ≃. β) : β ≃. α where
  toFun := f.2
  invFun := f.1
  inv _ _ := (f.inv _ _).symm
#align pequiv.symm PEquiv.symm

theorem mem_iff_mem (f : α ≃. β) : ∀ {a : α} {b : β}, a ∈ f.symm b ↔ b ∈ f a :=
  f.3 _ _
#align pequiv.mem_iff_mem PEquiv.mem_iff_mem

theorem eq_some_iff (f : α ≃. β) : ∀ {a : α} {b : β}, f.symm b = some a ↔ f a = some b :=
  f.3 _ _
#align pequiv.eq_some_iff PEquiv.eq_some_iff

/-- Composition of partial equivalences `f : α ≃. β` and `g : β ≃. γ`. -/
@[trans]
protected def trans (f : α ≃. β) (g : β ≃. γ) :
    α ≃. γ where
  toFun a := (f a).bind g
  invFun a := (g.symm a).bind f.symm
  inv a b := by simp_all [and_comm, eq_some_iff f, eq_some_iff g, bind_eq_some]
#align pequiv.trans PEquiv.trans

@[simp]
theorem refl_apply (a : α) : PEquiv.refl α a = some a :=
  rfl
#align pequiv.refl_apply PEquiv.refl_apply

@[simp]
theorem symm_refl : (PEquiv.refl α).symm = PEquiv.refl α :=
  rfl
#align pequiv.symm_refl PEquiv.symm_refl

@[simp]
theorem symm_symm (f : α ≃. β) : f.symm.symm = f := by cases f; rfl
#align pequiv.symm_symm PEquiv.symm_symm

theorem symm_bijective : Function.Bijective (PEquiv.symm : (α ≃. β) → β ≃. α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

theorem symm_injective : Function.Injective (@PEquiv.symm α β) :=
  symm_bijective.injective
#align pequiv.symm_injective PEquiv.symm_injective

theorem trans_assoc (f : α ≃. β) (g : β ≃. γ) (h : γ ≃. δ) :
    (f.trans g).trans h = f.trans (g.trans h) :=
  ext fun _ => Option.bind_assoc _ _ _
#align pequiv.trans_assoc PEquiv.trans_assoc

theorem mem_trans (f : α ≃. β) (g : β ≃. γ) (a : α) (c : γ) :
    c ∈ f.trans g a ↔ ∃ b, b ∈ f a ∧ c ∈ g b :=
  Option.bind_eq_some'
#align pequiv.mem_trans PEquiv.mem_trans

theorem trans_eq_some (f : α ≃. β) (g : β ≃. γ) (a : α) (c : γ) :
    f.trans g a = some c ↔ ∃ b, f a = some b ∧ g b = some c :=
  Option.bind_eq_some'
#align pequiv.trans_eq_some PEquiv.trans_eq_some

theorem trans_eq_none (f : α ≃. β) (g : β ≃. γ) (a : α) :
    f.trans g a = none ↔ ∀ b c, b ∉ f a ∨ c ∉ g b := by
  simp only [eq_none_iff_forall_not_mem, mem_trans, imp_iff_not_or.symm]
  push_neg
  exact forall_swap
#align pequiv.trans_eq_none PEquiv.trans_eq_none

@[simp]
theorem refl_trans (f : α ≃. β) : (PEquiv.refl α).trans f = f := by
  ext; dsimp [PEquiv.trans]; rfl
#align pequiv.refl_trans PEquiv.refl_trans

@[simp]
theorem trans_refl (f : α ≃. β) : f.trans (PEquiv.refl β) = f := by
  ext; dsimp [PEquiv.trans]; simp
#align pequiv.trans_refl PEquiv.trans_refl

protected theorem inj (f : α ≃. β) {a₁ a₂ : α} {b : β} (h₁ : b ∈ f a₁) (h₂ : b ∈ f a₂) :
    a₁ = a₂ := by rw [← mem_iff_mem] at *; cases h : f.symm b <;> simp_all
#align pequiv.inj PEquiv.inj

/-- If the domain of a `PEquiv` is `α` except a point, its forward direction is injective. -/
theorem injective_of_forall_ne_isSome (f : α ≃. β) (a₂ : α)
    (h : ∀ a₁ : α, a₁ ≠ a₂ → isSome (f a₁)) : Injective f :=
  HasLeftInverse.injective
    ⟨fun b => Option.recOn b a₂ fun b' => Option.recOn (f.symm b') a₂ id, fun x => by
      classical
        cases hfx : f x
        · have : x = a₂ := not_imp_comm.1 (h x) (hfx.symm ▸ by simp)
          simp [this]
        · dsimp only
          rw [(eq_some_iff f).2 hfx]
          rfl⟩
#align pequiv.injective_of_forall_ne_is_some PEquiv.injective_of_forall_ne_isSome

/-- If the domain of a `PEquiv` is all of `α`, its forward direction is injective. -/
theorem injective_of_forall_isSome {f : α ≃. β} (h : ∀ a : α, isSome (f a)) : Injective f :=
  (Classical.em (Nonempty α)).elim
    (fun hn => injective_of_forall_ne_isSome f (Classical.choice hn) fun a _ => h a) fun hn x =>
    (hn ⟨x⟩).elim
#align pequiv.injective_of_forall_is_some PEquiv.injective_of_forall_isSome

section OfSet

variable (s : Set α) [DecidablePred (· ∈ s)]

/-- Creates a `PEquiv` that is the identity on `s`, and `none` outside of it. -/
def ofSet (s : Set α) [DecidablePred (· ∈ s)] :
    α ≃. α where
  toFun a := if a ∈ s then some a else none
  invFun a := if a ∈ s then some a else none
  inv a b := by
    dsimp only
    split_ifs with hb ha ha
    · simp [eq_comm]
    · simp [ne_of_mem_of_not_mem hb ha]
    · simp [ne_of_mem_of_not_mem ha hb]
    · simp
#align pequiv.of_set PEquiv.ofSet

theorem mem_ofSet_self_iff {s : Set α} [DecidablePred (· ∈ s)] {a : α} : a ∈ ofSet s a ↔ a ∈ s := by
  dsimp [ofSet]; split_ifs <;> simp [*]
#align pequiv.mem_of_set_self_iff PEquiv.mem_ofSet_self_iff

theorem mem_ofSet_iff {s : Set α} [DecidablePred (· ∈ s)] {a b : α} :
    a ∈ ofSet s b ↔ a = b ∧ a ∈ s := by
  dsimp [ofSet]
  split_ifs with h
  · simp only [mem_def, eq_comm, some.injEq, iff_self_and]
    rintro rfl
    exact h
  · simp only [mem_def, false_iff, not_and]
    rintro rfl
    exact h
#align pequiv.mem_of_set_iff PEquiv.mem_ofSet_iff

@[simp]
theorem ofSet_eq_some_iff {s : Set α} {_ : DecidablePred (· ∈ s)} {a b : α} :
    ofSet s b = some a ↔ a = b ∧ a ∈ s :=
  mem_ofSet_iff
#align pequiv.of_set_eq_some_iff PEquiv.ofSet_eq_some_iff

theorem ofSet_eq_some_self_iff {s : Set α} {_ : DecidablePred (· ∈ s)} {a : α} :
    ofSet s a = some a ↔ a ∈ s :=
  mem_ofSet_self_iff
#align pequiv.of_set_eq_some_self_iff PEquiv.ofSet_eq_some_self_iff

@[simp]
theorem ofSet_symm : (ofSet s).symm = ofSet s :=
  rfl
#align pequiv.of_set_symm PEquiv.ofSet_symm

@[simp]
theorem ofSet_univ : ofSet Set.univ = PEquiv.refl α :=
  rfl
#align pequiv.of_set_univ PEquiv.ofSet_univ

@[simp]
theorem ofSet_eq_refl {s : Set α} [DecidablePred (· ∈ s)] :
    ofSet s = PEquiv.refl α ↔ s = Set.univ :=
  ⟨fun h => by
    rw [Set.eq_univ_iff_forall]
    intro
    rw [← mem_ofSet_self_iff, h]
    exact rfl, fun h => by simp only [← ofSet_univ, h]⟩
#align pequiv.of_set_eq_refl PEquiv.ofSet_eq_refl

end OfSet

theorem symm_trans_rev (f : α ≃. β) (g : β ≃. γ) : (f.trans g).symm = g.symm.trans f.symm :=
  rfl
#align pequiv.symm_trans_rev PEquiv.symm_trans_rev

theorem self_trans_symm (f : α ≃. β) : f.trans f.symm = ofSet { a | (f a).isSome } := by
  ext
  dsimp [PEquiv.trans]
  simp only [eq_some_iff f, Option.isSome_iff_exists, Option.mem_def, bind_eq_some',
    ofSet_eq_some_iff]
  constructor
  · rintro ⟨b, hb₁, hb₂⟩
    exact ⟨PEquiv.inj _ hb₂ hb₁, b, hb₂⟩
  · simp (config := { contextual := true })
#align pequiv.self_trans_symm PEquiv.self_trans_symm

theorem symm_trans_self (f : α ≃. β) : f.symm.trans f = ofSet { b | (f.symm b).isSome } :=
  symm_injective <| by simp [symm_trans_rev, self_trans_symm, -symm_symm]
#align pequiv.symm_trans_self PEquiv.symm_trans_self

theorem trans_symm_eq_iff_forall_isSome {f : α ≃. β} :
    f.trans f.symm = PEquiv.refl α ↔ ∀ a, isSome (f a) := by
  rw [self_trans_symm, ofSet_eq_refl, Set.eq_univ_iff_forall]; rfl
#align pequiv.trans_symm_eq_iff_forall_is_some PEquiv.trans_symm_eq_iff_forall_isSome

instance instBotPEquiv : Bot (α ≃. β) :=
  ⟨{  toFun := fun _ => none
      invFun := fun _ => none
      inv := by simp }⟩

instance : Inhabited (α ≃. β) :=
  ⟨⊥⟩

@[simp]
theorem bot_apply (a : α) : (⊥ : α ≃. β) a = none :=
  rfl
#align pequiv.bot_apply PEquiv.bot_apply

@[simp]
theorem symm_bot : (⊥ : α ≃. β).symm = ⊥ :=
  rfl
#align pequiv.symm_bot PEquiv.symm_bot

@[simp]
theorem trans_bot (f : α ≃. β) : f.trans (⊥ : β ≃. γ) = ⊥ := by
  ext; dsimp [PEquiv.trans]; simp
#align pequiv.trans_bot PEquiv.trans_bot

@[simp]
theorem bot_trans (f : β ≃. γ) : (⊥ : α ≃. β).trans f = ⊥ := by
  ext; dsimp [PEquiv.trans]; simp
#align pequiv.bot_trans PEquiv.bot_trans

theorem isSome_symm_get (f : α ≃. β) {a : α} (h : isSome (f a)) :
    isSome (f.symm (Option.get _ h)) :=
  isSome_iff_exists.2 ⟨a, by rw [f.eq_some_iff, some_get]⟩
#align pequiv.is_some_symm_get PEquiv.isSome_symm_get

section Single

variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- Create a `PEquiv` which sends `a` to `b` and `b` to `a`, but is otherwise `none`. -/
def single (a : α) (b : β) :
    α ≃. β where
  toFun x := if x = a then some b else none
  invFun x := if x = b then some a else none
  inv x y := by
    dsimp only
    split_ifs with h1 h2
    · simp [*]
    · simp only [mem_def, some.injEq, iff_false] at *
      exact Ne.symm h2
    · simp only [mem_def, some.injEq, false_iff] at *
      exact Ne.symm h1
    · simp
#align pequiv.single PEquiv.single

theorem mem_single (a : α) (b : β) : b ∈ single a b a :=
  if_pos rfl
#align pequiv.mem_single PEquiv.mem_single

theorem mem_single_iff (a₁ a₂ : α) (b₁ b₂ : β) : b₁ ∈ single a₂ b₂ a₁ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  dsimp [single]; split_ifs <;> simp [*, eq_comm]
#align pequiv.mem_single_iff PEquiv.mem_single_iff

@[simp]
theorem symm_single (a : α) (b : β) : (single a b).symm = single b a :=
  rfl
#align pequiv.symm_single PEquiv.symm_single

@[simp]
theorem single_apply (a : α) (b : β) : single a b a = some b :=
  if_pos rfl
#align pequiv.single_apply PEquiv.single_apply

theorem single_apply_of_ne {a₁ a₂ : α} (h : a₁ ≠ a₂) (b : β) : single a₁ b a₂ = none :=
  if_neg h.symm
#align pequiv.single_apply_of_ne PEquiv.single_apply_of_ne

theorem single_trans_of_mem (a : α) {b : β} {c : γ} {f : β ≃. γ} (h : c ∈ f b) :
    (single a b).trans f = single a c := by
  ext
  dsimp [single, PEquiv.trans]
  split_ifs <;> simp_all
#align pequiv.single_trans_of_mem PEquiv.single_trans_of_mem

theorem trans_single_of_mem {a : α} {b : β} (c : γ) {f : α ≃. β} (h : b ∈ f a) :
    f.trans (single b c) = single a c :=
  symm_injective <| single_trans_of_mem _ ((mem_iff_mem f).2 h)
#align pequiv.trans_single_of_mem PEquiv.trans_single_of_mem

@[simp]
theorem single_trans_single (a : α) (b : β) (c : γ) :
    (single a b).trans (single b c) = single a c :=
  single_trans_of_mem _ (mem_single _ _)
#align pequiv.single_trans_single PEquiv.single_trans_single

@[simp]
theorem single_subsingleton_eq_refl [Subsingleton α] (a b : α) : single a b = PEquiv.refl α := by
  ext i j
  dsimp [single]
  rw [if_pos (Subsingleton.elim i a), Subsingleton.elim i j, Subsingleton.elim b j]
#align pequiv.single_subsingleton_eq_refl PEquiv.single_subsingleton_eq_refl

theorem trans_single_of_eq_none {b : β} (c : γ) {f : δ ≃. β} (h : f.symm b = none) :
    f.trans (single b c) = ⊥ := by
  ext
  simp only [eq_none_iff_forall_not_mem, Option.mem_def, f.eq_some_iff] at h
  dsimp [PEquiv.trans, single]
  simp only [mem_def, bind_eq_some, iff_false, not_exists, not_and]
  intros
  split_ifs <;> simp_all
#align pequiv.trans_single_of_eq_none PEquiv.trans_single_of_eq_none

theorem single_trans_of_eq_none (a : α) {b : β} {f : β ≃. δ} (h : f b = none) :
    (single a b).trans f = ⊥ :=
  symm_injective <| trans_single_of_eq_none _ h
#align pequiv.single_trans_of_eq_none PEquiv.single_trans_of_eq_none

theorem single_trans_single_of_ne {b₁ b₂ : β} (h : b₁ ≠ b₂) (a : α) (c : γ) :
    (single a b₁).trans (single b₂ c) = ⊥ :=
  single_trans_of_eq_none _ (single_apply_of_ne h.symm _)
#align pequiv.single_trans_single_of_ne PEquiv.single_trans_single_of_ne

end Single

section Order

instance instPartialOrderPEquiv : PartialOrder (α ≃. β) where
  le f g := ∀ (a : α) (b : β), b ∈ f a → b ∈ g a
  le_refl _ _ _ := id
  le_trans f g h fg gh a b := gh a b ∘ fg a b
  le_antisymm f g fg gf :=
    ext
      (by
        intro a
        cases' h : g a with b
        · exact eq_none_iff_forall_not_mem.2 fun b hb => Option.not_mem_none b <| h ▸ fg a b hb
        · exact gf _ _ h)

theorem le_def {f g : α ≃. β} : f ≤ g ↔ ∀ (a : α) (b : β), b ∈ f a → b ∈ g a :=
  Iff.rfl
#align pequiv.le_def PEquiv.le_def

instance : OrderBot (α ≃. β) :=
  { instBotPEquiv with bot_le := fun _ _ _ h => (not_mem_none _ h).elim }

instance [DecidableEq α] [DecidableEq β] : SemilatticeInf (α ≃. β) :=
  { instPartialOrderPEquiv with
    inf := fun f g =>
      { toFun := fun a => if f a = g a then f a else none
        invFun := fun b => if f.symm b = g.symm b then f.symm b else none
        inv := fun a b => by
          have hf := @mem_iff_mem _ _ f a b
          have hg := @mem_iff_mem _ _ g a b
          simp only [Option.mem_def] at *
          split_ifs with h1 h2 h2 <;> try simp [hf]
          · contrapose! h2
            rw [h2]
            rw [← h1, hf, h2] at hg
            simp only [mem_def, true_iff_iff, eq_self_iff_true] at hg
            rw [hg]
          · contrapose! h1
            rw [h1] at hf h2
            rw [← h2] at hg
            simp only [iff_true] at hf hg
            rw [hf, hg] }
    inf_le_left := fun _ _ _ _ => by simp only [coe_mk, mem_def]; split_ifs <;> simp [*]
    inf_le_right := fun _ _ _ _ => by simp only [coe_mk, mem_def]; split_ifs <;> simp [*]
    le_inf := fun f g h fg gh a b => by
      intro H
      have hf := fg a b H
      have hg := gh a b H
      simp only [Option.mem_def, PEquiv.coe_mk_apply] at *
      rw [hf, hg, if_pos rfl] }

end Order

end PEquiv

namespace Equiv

variable {α : Type*} {β : Type*} {γ : Type*}

/-- Turns an `Equiv` into a `PEquiv` of the whole type. -/
def toPEquiv (f : α ≃ β) : α ≃. β where
  toFun := some ∘ f
  invFun := some ∘ f.symm
  inv := by simp [Equiv.eq_symm_apply, eq_comm]
#align equiv.to_pequiv Equiv.toPEquiv

@[simp]
theorem toPEquiv_refl : (Equiv.refl α).toPEquiv = PEquiv.refl α :=
  rfl
#align equiv.to_pequiv_refl Equiv.toPEquiv_refl

theorem toPEquiv_trans (f : α ≃ β) (g : β ≃ γ) :
    (f.trans g).toPEquiv = f.toPEquiv.trans g.toPEquiv :=
  rfl
#align equiv.to_pequiv_trans Equiv.toPEquiv_trans

theorem toPEquiv_symm (f : α ≃ β) : f.symm.toPEquiv = f.toPEquiv.symm :=
  rfl
#align equiv.to_pequiv_symm Equiv.toPEquiv_symm

theorem toPEquiv_apply (f : α ≃ β) (x : α) : f.toPEquiv x = some (f x) :=
  rfl
#align equiv.to_pequiv_apply Equiv.toPEquiv_apply

end Equiv
