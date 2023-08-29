/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Data.W.Basic

#align_import data.pfunctor.univariate.basic from "leanprover-community/mathlib"@"8631e2d5ea77f6c13054d9151d82b83069680cb1"

/-!
# Polynomial functors

This file defines polynomial functors and the W-type construction as a
polynomial functor.  (For the M-type construction, see
pfunctor/M.lean.)
-/

-- "W", "Idx"
set_option linter.uppercaseLean3 false

universe u

/-- A polynomial functor `P` is given by a type `A` and a family `B` of types over `A`. `P` maps
any type `α` to a new type `P.obj α`, which is defined as the sigma type `Σ x, P.B x → α`.

An element of `P.obj α` is a pair `⟨a, f⟩`, where `a` is an element of a type `A` and
`f : B a → α`. Think of `a` as the shape of the object and `f` as an index to the relevant
elements of `α`.
-/
structure PFunctor where
  /-- The head type -/
  A : Type u
  /-- The child family of types -/
  B : A → Type u
#align pfunctor PFunctor

namespace PFunctor

instance : Inhabited PFunctor :=
  ⟨⟨default, default⟩⟩

variable (P : PFunctor) {α β : Type u}

/-- Applying `P` to an object of `Type` -/
def Obj (α : Type*) :=
  Σx : P.A, P.B x → α
#align pfunctor.obj PFunctor.Obj

/-- Applying `P` to a morphism of `Type` -/
def map {α β : Type*} (f : α → β) : P.Obj α → P.Obj β :=
  fun ⟨a, g⟩ => ⟨a, f ∘ g⟩
#align pfunctor.map PFunctor.map

instance Obj.inhabited [Inhabited P.A] [Inhabited α] : Inhabited (P.Obj α) :=
  ⟨⟨default, default⟩⟩
#align pfunctor.obj.inhabited PFunctor.Obj.inhabited

instance : Functor P.Obj where map := @map P

protected theorem map_eq {α β : Type _} (f : α → β) (a : P.A) (g : P.B a → α) :
    @Functor.map P.Obj _ _ _ f ⟨a, g⟩ = ⟨a, f ∘ g⟩ :=
  rfl
#align pfunctor.map_eq PFunctor.map_eq

protected theorem id_map {α : Type*} : ∀ x : P.Obj α, id <$> x = id x := fun ⟨_a, _b⟩ => rfl
#align pfunctor.id_map PFunctor.id_map

protected theorem comp_map {α β γ : Type _} (f : α → β) (g : β → γ) :
    ∀ x : P.Obj α, (g ∘ f) <$> x = g <$> f <$> x := fun ⟨_a, _b⟩ => rfl
#align pfunctor.comp_map PFunctor.comp_map

instance : LawfulFunctor P.Obj where
  map_const := rfl
  id_map := @PFunctor.id_map P
  comp_map := @PFunctor.comp_map P

/-- re-export existing definition of W-types and
adapt it to a packaged definition of polynomial functor -/
def W :=
  WType P.B
#align pfunctor.W PFunctor.W

/- inhabitants of W types is awkward to encode as an instance
assumption because there needs to be a value `a : P.A`
such that `P.B a` is empty to yield a finite tree -/
-- attribute [nolint has_nonempty_instance] W

variable {P}

/-- root element of a W tree -/
def W.head : W P → P.A
  | ⟨a, _f⟩ => a
#align pfunctor.W.head PFunctor.W.head

/-- children of the root of a W tree -/
def W.children : ∀ x : W P, P.B (W.head x) → W P
  | ⟨_a, f⟩ => f
#align pfunctor.W.children PFunctor.W.children

/-- destructor for W-types -/
def W.dest : W P → P.Obj (W P)
  | ⟨a, f⟩ => ⟨a, f⟩
#align pfunctor.W.dest PFunctor.W.dest

/-- constructor for W-types -/
def W.mk : P.Obj (W P) → W P
  | ⟨a, f⟩ => ⟨a, f⟩
#align pfunctor.W.mk PFunctor.W.mk

@[simp]
theorem W.dest_mk (p : P.Obj (W P)) : W.dest (W.mk p) = p := by cases p; rfl
                                                                -- ⊢ dest (mk { fst := fst✝, snd := snd✝ }) = { fst := fst✝, snd := snd✝ }
                                                                         -- 🎉 no goals
#align pfunctor.W.dest_mk PFunctor.W.dest_mk

@[simp]
theorem W.mk_dest (p : W P) : W.mk (W.dest p) = p := by cases p; rfl
                                                        -- ⊢ mk (dest (WType.mk a✝ f✝)) = WType.mk a✝ f✝
                                                                 -- 🎉 no goals
#align pfunctor.W.mk_dest PFunctor.W.mk_dest

variable (P)

/-- `Idx` identifies a location inside the application of a pfunctor.
For `F : PFunctor`, `x : F.obj α` and `i : F.Idx`, `i` can designate
one part of `x` or is invalid, if `i.1 ≠ x.1` -/
def IdxCat :=
  Σx : P.A, P.B x
#align pfunctor.Idx PFunctor.IdxCat

instance IdxCat.inhabited [Inhabited P.A] [Inhabited (P.B default)] : Inhabited P.IdxCat :=
  ⟨⟨default, default⟩⟩
#align pfunctor.Idx.inhabited PFunctor.IdxCat.inhabited

variable {P}

/-- `x.iget i` takes the component of `x` designated by `i` if any is or returns
a default value -/
def Obj.iget [DecidableEq P.A] {α} [Inhabited α] (x : P.Obj α) (i : P.IdxCat) : α :=
  if h : i.1 = x.1 then x.2 (cast (congr_arg _ h) i.2) else default
#align pfunctor.obj.iget PFunctor.Obj.iget

@[simp]
theorem fst_map {α β : Type u} (x : P.Obj α) (f : α → β) : (f <$> x).1 = x.1 := by cases x; rfl
                                                                                   -- ⊢ (f <$> { fst := fst✝, snd := snd✝ }).fst = { fst := fst✝, snd := snd✝ }.fst
                                                                                            -- 🎉 no goals
#align pfunctor.fst_map PFunctor.fst_map

@[simp]
theorem iget_map [DecidableEq P.A] {α β : Type u} [Inhabited α] [Inhabited β] (x : P.Obj α)
    (f : α → β) (i : P.IdxCat) (h : i.1 = x.1) : (f <$> x).iget i = f (x.iget i) := by
  simp only [Obj.iget, fst_map, *, dif_pos, eq_self_iff_true]
  -- ⊢ Sigma.snd (f <$> x) (cast (_ : B P i.fst = B P (f <$> x).fst) i.snd) = f (Si …
  cases x
  -- ⊢ Sigma.snd (f <$> { fst := fst✝, snd := snd✝ }) (cast (_ : B P i.fst = B P (f …
  rfl
  -- 🎉 no goals
#align pfunctor.iget_map PFunctor.iget_map

end PFunctor

/-
Composition of polynomial functors.
-/
namespace PFunctor

/-- functor composition for polynomial functors -/
def comp (P₂ P₁ : PFunctor.{u}) : PFunctor.{u} :=
  ⟨Σa₂ : P₂.1, P₂.2 a₂ → P₁.1, fun a₂a₁ => Σu : P₂.2 a₂a₁.1, P₁.2 (a₂a₁.2 u)⟩
#align pfunctor.comp PFunctor.comp

/-- constructor for composition -/
def comp.mk (P₂ P₁ : PFunctor.{u}) {α : Type} (x : P₂.Obj (P₁.Obj α)) : (comp P₂ P₁).Obj α :=
  ⟨⟨x.1, Sigma.fst ∘ x.2⟩, fun a₂a₁ => (x.2 a₂a₁.1).2 a₂a₁.2⟩
#align pfunctor.comp.mk PFunctor.comp.mk

/-- destructor for composition -/
def comp.get (P₂ P₁ : PFunctor.{u}) {α : Type} (x : (comp P₂ P₁).Obj α) : P₂.Obj (P₁.Obj α) :=
  ⟨x.1.1, fun a₂ => ⟨x.1.2 a₂, fun a₁ => x.2 ⟨a₂, a₁⟩⟩⟩
#align pfunctor.comp.get PFunctor.comp.get

end PFunctor

/-
Lifting predicates and relations.
-/
namespace PFunctor

variable {P : PFunctor.{u}}

open Functor

theorem liftp_iff {α : Type u} (p : α → Prop) (x : P.Obj α) :
    Liftp p x ↔ ∃ a f, x = ⟨a, f⟩ ∧ ∀ i, p (f i) := by
  constructor
  -- ⊢ Liftp p x → ∃ a f, x = { fst := a, snd := f } ∧ ∀ (i : B P a), p (f i)
  · rintro ⟨y, hy⟩
    -- ⊢ ∃ a f, x = { fst := a, snd := f } ∧ ∀ (i : B P a), p (f i)
    cases' h : y with a f
    -- ⊢ ∃ a f, x = { fst := a, snd := f } ∧ ∀ (i : B P a), p (f i)
    refine' ⟨a, fun i => (f i).val, _, fun i => (f i).property⟩
    -- ⊢ x = { fst := a, snd := fun i => ↑(f i) }
    rw [← hy, h, PFunctor.map_eq]
    -- ⊢ { fst := a, snd := Subtype.val ∘ f } = { fst := a, snd := fun i => ↑(f i) }
    congr
    -- 🎉 no goals
  rintro ⟨a, f, xeq, pf⟩
  -- ⊢ Liftp p x
  use ⟨a, fun i => ⟨f i, pf i⟩⟩
  -- ⊢ Subtype.val <$> { fst := a, snd := fun i => { val := f i, property := (_ : p …
  rw [xeq]; rfl
  -- ⊢ Subtype.val <$> { fst := a, snd := fun i => { val := f i, property := (_ : p …
            -- 🎉 no goals
#align pfunctor.liftp_iff PFunctor.liftp_iff

theorem liftp_iff' {α : Type u} (p : α → Prop) (a : P.A) (f : P.B a → α) :
    @Liftp.{u} P.Obj _ α p ⟨a, f⟩ ↔ ∀ i, p (f i) := by
  simp only [liftp_iff, Sigma.mk.inj_iff]; constructor <;> intro h
  -- ⊢ (∃ a_1 f_1, { fst := a, snd := f } = { fst := a_1, snd := f_1 } ∧ ∀ (i : B P …
                                           -- ⊢ (∃ a_1 f_1, { fst := a, snd := f } = { fst := a_1, snd := f_1 } ∧ ∀ (i : B P …
                                                           -- ⊢ ∀ (i : B P a), p (f i)
                                                           -- ⊢ ∃ a_1 f_1, { fst := a, snd := f } = { fst := a_1, snd := f_1 } ∧ ∀ (i : B P  …
  · rcases h with ⟨a', f', heq, h'⟩
    -- ⊢ ∀ (i : B P a), p (f i)
    cases heq
    -- ⊢ ∀ (i : B P a), p (f i)
    assumption
    -- 🎉 no goals
  repeat' first |constructor|assumption
  -- 🎉 no goals
#align pfunctor.liftp_iff' PFunctor.liftp_iff'

theorem liftr_iff {α : Type u} (r : α → α → Prop) (x y : P.Obj α) :
    Liftr r x y ↔ ∃ a f₀ f₁, x = ⟨a, f₀⟩ ∧ y = ⟨a, f₁⟩ ∧ ∀ i, r (f₀ i) (f₁ i) := by
  constructor
  -- ⊢ Liftr r x y → ∃ a f₀ f₁, x = { fst := a, snd := f₀ } ∧ y = { fst := a, snd : …
  · rintro ⟨u, xeq, yeq⟩
    -- ⊢ ∃ a f₀ f₁, x = { fst := a, snd := f₀ } ∧ y = { fst := a, snd := f₁ } ∧ ∀ (i  …
    cases' h : u with a f
    -- ⊢ ∃ a f₀ f₁, x = { fst := a, snd := f₀ } ∧ y = { fst := a, snd := f₁ } ∧ ∀ (i  …
    use a, fun i => (f i).val.fst, fun i => (f i).val.snd
    -- ⊢ x = { fst := a, snd := fun i => (↑(f i)).fst } ∧ y = { fst := a, snd := fun  …
    constructor
    -- ⊢ x = { fst := a, snd := fun i => (↑(f i)).fst }
    · rw [← xeq, h]
      -- ⊢ (fun t => (↑t).fst) <$> { fst := a, snd := f } = { fst := a, snd := fun i => …
      rfl
      -- 🎉 no goals
    constructor
    -- ⊢ y = { fst := a, snd := fun i => (↑(f i)).snd }
    · rw [← yeq, h]
      -- ⊢ (fun t => (↑t).snd) <$> { fst := a, snd := f } = { fst := a, snd := fun i => …
      rfl
      -- 🎉 no goals
    intro i
    -- ⊢ r (↑(f i)).fst (↑(f i)).snd
    exact (f i).property
    -- 🎉 no goals
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  -- ⊢ Liftr r x y
  use ⟨a, fun i => ⟨(f₀ i, f₁ i), h i⟩⟩
  -- ⊢ (fun t => (↑t).fst) <$> { fst := a, snd := fun i => { val := (f₀ i, f₁ i), p …
  constructor
  -- ⊢ (fun t => (↑t).fst) <$> { fst := a, snd := fun i => { val := (f₀ i, f₁ i), p …
  · rw [xeq]
    -- ⊢ (fun t => (↑t).fst) <$> { fst := a, snd := fun i => { val := (f₀ i, f₁ i), p …
    rfl
    -- 🎉 no goals
  rw [yeq]; rfl
  -- ⊢ (fun t => (↑t).snd) <$> { fst := a, snd := fun i => { val := (f₀ i, f₁ i), p …
            -- 🎉 no goals
#align pfunctor.liftr_iff PFunctor.liftr_iff

open Set

theorem supp_eq {α : Type u} (a : P.A) (f : P.B a → α) :
    @supp.{u} P.Obj _ α (⟨a, f⟩ : P.Obj α) = f '' univ := by
  ext x; simp only [supp, image_univ, mem_range, mem_setOf_eq]
  -- ⊢ x ∈ supp { fst := a, snd := f } ↔ x ∈ f '' univ
         -- ⊢ (∀ ⦃p : α → Prop⦄, Liftp p { fst := a, snd := f } → p x) ↔ ∃ y, f y = x
  constructor <;> intro h
  -- ⊢ (∀ ⦃p : α → Prop⦄, Liftp p { fst := a, snd := f } → p x) → ∃ y, f y = x
                  -- ⊢ ∃ y, f y = x
                  -- ⊢ ∀ ⦃p : α → Prop⦄, Liftp p { fst := a, snd := f } → p x
  · apply @h fun x => ∃ y : P.B a, f y = x
    -- ⊢ Liftp (fun x => ∃ y, f y = x) { fst := a, snd := f }
    rw [liftp_iff']
    -- ⊢ ∀ (i : B P a), ∃ y, f y = f i
    intro
    -- ⊢ ∃ y, f y = f i✝
    refine' ⟨_, rfl⟩
    -- 🎉 no goals
  · simp only [liftp_iff']
    -- ⊢ ∀ ⦃p : α → Prop⦄, (∀ (i : B P a), p (f i)) → p x
    cases h
    -- ⊢ ∀ ⦃p : α → Prop⦄, (∀ (i : B P a), p (f i)) → p x
    subst x
    -- ⊢ ∀ ⦃p : α → Prop⦄, (∀ (i : B P a), p (f i)) → p (f w✝)
    tauto
    -- 🎉 no goals
#align pfunctor.supp_eq PFunctor.supp_eq

end PFunctor
