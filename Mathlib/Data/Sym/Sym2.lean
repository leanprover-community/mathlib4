/-
Copyright (c) 2020 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Data.SetLike.Basic

#align_import data.sym.sym2 from "leanprover-community/mathlib"@"8631e2d5ea77f6c13054d9151d82b83069680cb1"

/-!
# The symmetric square

This file defines the symmetric square, which is `α × α` modulo
swapping.  This is also known as the type of unordered pairs.

More generally, the symmetric square is the second symmetric power
(see `Data.Sym.Basic`). The equivalence is `Sym2.equivSym`.

From the point of view that an unordered pair is equivalent to a
multiset of cardinality two (see `Sym2.equivMultiset`), there is a
`Mem` instance `Sym2.Mem`, which is a `Prop`-valued membership
test.  Given `h : a ∈ z` for `z : Sym2 α`, then `Mem.other h` is the other
element of the pair, defined using `Classical.choice`.  If `α` has
decidable equality, then `h.other'` computably gives the other element.

The universal property of `Sym2` is provided as `Sym2.lift`, which
states that functions from `Sym2 α` are equivalent to symmetric
two-argument functions from `α`.

Recall that an undirected graph (allowing self loops, but no multiple
edges) is equivalent to a symmetric relation on the vertex type `α`.
Given a symmetric relation on `α`, the corresponding edge set is
constructed by `Sym2.fromRel` which is a special case of `Sym2.lift`.

## Notation

The symmetric square has a setoid instance, so `⟦(a, b)⟧` denotes a
term of the symmetric square.

## Tags

symmetric square, unordered pairs, symmetric powers
-/


-- porting note: using `aesop` in place of `tidy` to simplify proofs
-- porting note: remove import `Tactic.Linarith.Default`
-- porting note: adding the above porting note here to avoid module docs linter error

open Finset Function Sym

universe u

variable {α β γ : Type*}

namespace Sym2

/-- This is the relation capturing the notion of pairs equivalent up to permutations.
-/
@[aesop (rule_sets [Sym2]) [safe [constructors, cases], norm unfold]]
inductive Rel (α : Type u) : α × α → α × α → Prop
  | refl (x y : α) : Rel _ (x, y) (x, y)
  | swap (x y : α) : Rel _ (x, y) (y, x)
#align sym2.rel Sym2.Rel

-- porting note: somehow the name was not aligned
attribute [refl] Rel.refl

@[symm]
theorem Rel.symm {x y : α × α} : Rel α x y → Rel α y x := by aesop (rule_sets [Sym2])
                                                             -- 🎉 no goals
#align sym2.rel.symm Sym2.Rel.symm

@[trans]
theorem Rel.trans {x y z : α × α} (a : Rel α x y) (b : Rel α y z) : Rel α x z := by
  aesop (rule_sets [Sym2])
  -- 🎉 no goals
#align sym2.rel.trans Sym2.Rel.trans

theorem Rel.is_equivalence : Equivalence (Rel α) :=
  { refl := fun (x, y)↦Rel.refl x y, symm := Rel.symm, trans := Rel.trans }
#align sym2.rel.is_equivalence Sym2.Rel.is_equivalence

instance Rel.setoid (α : Type u) : Setoid (α × α) :=
  ⟨Rel α, Rel.is_equivalence⟩
#align sym2.rel.setoid Sym2.Rel.setoid

@[simp]
theorem rel_iff {x y z w : α} : (x, y) ≈ (z, w) ↔ x = z ∧ y = w ∨ x = w ∧ y = z :=
  show Rel _ _ _ ↔ _ by aesop (rule_sets [Sym2])
                        -- 🎉 no goals
#align sym2.rel_iff Sym2.rel_iff

end Sym2

/-- `Sym2 α` is the symmetric square of `α`, which, in other words, is the
type of unordered pairs.

It is equivalent in a natural way to multisets of cardinality 2 (see
`Sym2.equivMultiset`).
-/
@[reducible]
def Sym2 (α : Type u) :=
  Quotient (Sym2.Rel.setoid α)
#align sym2 Sym2

namespace Sym2

@[elab_as_elim]
protected theorem ind {f : Sym2 α → Prop} (h : ∀ x y, f ⟦(x, y)⟧) : ∀ i, f i :=
  Quotient.ind <| Prod.rec <| h
#align sym2.ind Sym2.ind

@[elab_as_elim]
protected theorem inductionOn {f : Sym2 α → Prop} (i : Sym2 α) (hf : ∀ x y, f ⟦(x, y)⟧) : f i :=
  i.ind hf
#align sym2.induction_on Sym2.inductionOn

@[elab_as_elim]
protected theorem inductionOn₂ {f : Sym2 α → Sym2 β → Prop} (i : Sym2 α) (j : Sym2 β)
    (hf : ∀ a₁ a₂ b₁ b₂, f ⟦(a₁, a₂)⟧ ⟦(b₁, b₂)⟧) : f i j :=
  Quotient.inductionOn₂ i j <| by
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    -- ⊢ f (Quotient.mk (Rel.setoid α) (a₁, a₂)) (Quotient.mk (Rel.setoid β) (b₁, b₂))
    exact hf _ _ _ _
    -- 🎉 no goals
#align sym2.induction_on₂ Sym2.inductionOn₂

-- porting note: `exists` seems to be an invalid identifier
protected theorem «exists» {α : Sort _} {f : Sym2 α → Prop} :
    (∃ x : Sym2 α, f x) ↔ ∃ x y, f ⟦(x, y)⟧ :=
  (surjective_quotient_mk _).exists.trans Prod.exists
#align sym2.exists Sym2.exists

-- porting note: `forall` seems to be an invalid identifier
protected theorem «forall» {α : Sort _} {f : Sym2 α → Prop} :
    (∀ x : Sym2 α, f x) ↔ ∀ x y, f ⟦(x, y)⟧ :=
  (surjective_quotient_mk _).forall.trans Prod.forall
#align sym2.forall Sym2.forall

-- porting note: The `⟦⟧` notation does not infer the setoid structure automatically
theorem eq_swap {a b : α} : Eq (α := Sym2 α) ⟦(a, b)⟧ ⟦(b, a)⟧ := by
  rw [Quotient.eq]
  -- ⊢ (a, b) ≈ (b, a)
  apply Rel.swap
  -- 🎉 no goals
#align sym2.eq_swap Sym2.eq_swap

@[simp]
theorem mk''_prod_swap_eq {p : α × α} : Eq (α := Sym2 α) ⟦p.swap⟧ ⟦p⟧ := by
  cases p
  -- ⊢ Quotient.mk (Rel.setoid α) (Prod.swap (fst✝, snd✝)) = Quotient.mk (Rel.setoi …
  exact eq_swap
  -- 🎉 no goals
#align sym2.mk_prod_swap_eq Sym2.mk''_prod_swap_eq

theorem congr_right {a b c : α} : Eq (α := Sym2 α) ⟦(a, b)⟧ ⟦(a, c)⟧ ↔ b = c := by
  constructor <;> intro h
  -- ⊢ Quotient.mk (Rel.setoid α) (a, b) = Quotient.mk (Rel.setoid α) (a, c) → b = c
                  -- ⊢ b = c
                  -- ⊢ Quotient.mk (Rel.setoid α) (a, b) = Quotient.mk (Rel.setoid α) (a, c)
  · rw [Quotient.eq] at h
    -- ⊢ b = c
    cases h <;> rfl
    -- ⊢ b = b
                -- 🎉 no goals
                -- 🎉 no goals
  rw [h]
  -- 🎉 no goals
#align sym2.congr_right Sym2.congr_right

theorem congr_left {a b c : α} : Eq (α := Sym2 α) ⟦(b, a)⟧ ⟦(c, a)⟧ ↔ b = c := by
  constructor <;> intro h
  -- ⊢ Quotient.mk (Rel.setoid α) (b, a) = Quotient.mk (Rel.setoid α) (c, a) → b = c
                  -- ⊢ b = c
                  -- ⊢ Quotient.mk (Rel.setoid α) (b, a) = Quotient.mk (Rel.setoid α) (c, a)
  · rw [Quotient.eq] at h
    -- ⊢ b = c
    cases h <;> rfl
    -- ⊢ b = b
                -- 🎉 no goals
                -- 🎉 no goals
  rw [h]
  -- 🎉 no goals
#align sym2.congr_left Sym2.congr_left

theorem eq_iff {x y z w : α} : Eq (α := Sym2 α) ⟦(x, y)⟧ ⟦(z, w)⟧ ↔ x = z ∧ y = w ∨ x = w ∧ y = z :=
  by simp
     -- 🎉 no goals
#align sym2.eq_iff Sym2.eq_iff

theorem mk''_eq_mk''_iff {p q : α × α} : Eq (α := Sym2 α) ⟦p⟧ ⟦q⟧ ↔ p = q ∨ p = q.swap := by
  cases p
  -- ⊢ Quotient.mk (Rel.setoid α) (fst✝, snd✝) = Quotient.mk (Rel.setoid α) q ↔ (fs …
  cases q
  -- ⊢ Quotient.mk (Rel.setoid α) (fst✝¹, snd✝¹) = Quotient.mk (Rel.setoid α) (fst✝ …
  simp only [eq_iff, Prod.mk.inj_iff, Prod.swap_prod_mk]
  -- 🎉 no goals
#align sym2.mk_eq_mk_iff Sym2.mk''_eq_mk''_iff

/-- The universal property of `Sym2`; symmetric functions of two arguments are equivalent to
functions from `Sym2`. Note that when `β` is `Prop`, it can sometimes be more convenient to use
`Sym2.fromRel` instead. -/
def lift : { f : α → α → β // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁ } ≃ (Sym2 α → β)
    where
  toFun f :=
    Quotient.lift (uncurry ↑f) <| by
      rintro _ _ ⟨⟩
      -- ⊢ uncurry ↑f (x✝, y✝) = uncurry ↑f (x✝, y✝)
      exacts [rfl, f.prop _ _]
      -- 🎉 no goals
  invFun F := ⟨curry (F ∘ Quotient.mk''), fun a₁ a₂ => congr_arg F eq_swap⟩
  left_inv f := Subtype.ext rfl
  right_inv F := funext <| Sym2.ind fun x y => rfl
#align sym2.lift Sym2.lift

@[simp]
theorem lift_mk'' (f : { f : α → α → β // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁ }) (a₁ a₂ : α) :
    lift f ⟦(a₁, a₂)⟧ = (f : α → α → β) a₁ a₂ :=
  rfl
#align sym2.lift_mk Sym2.lift_mk''

@[simp]
theorem coe_lift_symm_apply (F : Sym2 α → β) (a₁ a₂ : α) :
    (lift.symm F : α → α → β) a₁ a₂ = F ⟦(a₁, a₂)⟧ :=
  rfl
#align sym2.coe_lift_symm_apply Sym2.coe_lift_symm_apply

/-- A two-argument version of `Sym2.lift`. -/
def lift₂ :
    { f : α → α → β → β → γ //
        ∀ a₁ a₂ b₁ b₂, f a₁ a₂ b₁ b₂ = f a₂ a₁ b₁ b₂ ∧ f a₁ a₂ b₁ b₂ = f a₁ a₂ b₂ b₁ } ≃
      (Sym2 α → Sym2 β → γ)
    where
  toFun f :=
    Quotient.lift₂ (fun (a : α × α) (b : β × β) => f.1 a.1 a.2 b.1 b.2)
      (by
        rintro _ _ _ _ ⟨⟩ ⟨⟩
        exacts [rfl, (f.2 _ _ _ _).2, (f.2 _ _ _ _).1, (f.2 _ _ _ _).1.trans (f.2 _ _ _ _).2])
        -- 🎉 no goals
  invFun F :=
    ⟨fun a₁ a₂ b₁ b₂ => F ⟦(a₁, a₂)⟧ ⟦(b₁, b₂)⟧, fun a₁ a₂ b₁ b₂ => by
      constructor
      -- ⊢ (fun a₁ a₂ b₁ b₂ => F (Quotient.mk (Rel.setoid α) (a₁, a₂)) (Quotient.mk (Re …
      exacts [congr_arg₂ F eq_swap rfl, congr_arg₂ F rfl eq_swap]⟩
      -- 🎉 no goals
  left_inv f := Subtype.ext rfl
  right_inv F := funext₂ fun a b => Sym2.inductionOn₂ a b fun _ _ _ _ => rfl
#align sym2.lift₂ Sym2.lift₂

@[simp]
theorem lift₂_mk''
  (f :
    { f : α → α → β → β → γ //
      ∀ a₁ a₂ b₁ b₂, f a₁ a₂ b₁ b₂ = f a₂ a₁ b₁ b₂ ∧ f a₁ a₂ b₁ b₂ = f a₁ a₂ b₂ b₁ })
  (a₁ a₂ : α) (b₁ b₂ : β) : lift₂ f ⟦(a₁, a₂)⟧ ⟦(b₁, b₂)⟧ = (f : α → α → β → β → γ) a₁ a₂ b₁ b₂ :=
  rfl
#align sym2.lift₂_mk Sym2.lift₂_mk''

@[simp]
theorem coe_lift₂_symm_apply (F : Sym2 α → Sym2 β → γ) (a₁ a₂ : α) (b₁ b₂ : β) :
    (lift₂.symm F : α → α → β → β → γ) a₁ a₂ b₁ b₂ = F ⟦(a₁, a₂)⟧ ⟦(b₁, b₂)⟧ :=
  rfl
#align sym2.coe_lift₂_symm_apply Sym2.coe_lift₂_symm_apply

/-- The functor `Sym2` is functorial, and this function constructs the induced maps.
-/
def map (f : α → β) : Sym2 α → Sym2 β :=
  Quotient.map (Prod.map f f)
    (by
      intro _ _ h
      -- ⊢ Prod.map f f a✝ ≈ Prod.map f f b✝
      cases h
      -- ⊢ Prod.map f f (x✝, y✝) ≈ Prod.map f f (x✝, y✝)
      · constructor
        -- 🎉 no goals
      apply Rel.swap)
      -- 🎉 no goals
#align sym2.map Sym2.map

@[simp]
theorem map_id : map (@id α) = id := by
  ext ⟨⟨x, y⟩⟩
  -- ⊢ map id (Quot.mk Setoid.r (x, y)) = id (Quot.mk Setoid.r (x, y))
  rfl
  -- 🎉 no goals
#align sym2.map_id Sym2.map_id

theorem map_comp {g : β → γ} {f : α → β} : Sym2.map (g ∘ f) = Sym2.map g ∘ Sym2.map f := by
  ext ⟨⟨x, y⟩⟩
  -- ⊢ map (g ∘ f) (Quot.mk Setoid.r (x, y)) = (map g ∘ map f) (Quot.mk Setoid.r (x …
  rfl
  -- 🎉 no goals
#align sym2.map_comp Sym2.map_comp

theorem map_map {g : β → γ} {f : α → β} (x : Sym2 α) : map g (map f x) = map (g ∘ f) x := by
  revert x; apply Sym2.ind; aesop
  -- ⊢ ∀ (x : Sym2 α), map g (map f x) = map (g ∘ f) x
            -- ⊢ ∀ (x y : α), map g (map f (Quotient.mk (Rel.setoid α) (x, y))) = map (g ∘ f) …
                            -- 🎉 no goals
#align sym2.map_map Sym2.map_map

@[simp]
theorem map_pair_eq (f : α → β) (x y : α) : map f ⟦(x, y)⟧ = ⟦(f x, f y)⟧ :=
  rfl
#align sym2.map_pair_eq Sym2.map_pair_eq

theorem map.injective {f : α → β} (hinj : Injective f) : Injective (map f) := by
  intro z z'
  -- ⊢ map f z = map f z' → z = z'
  refine' Quotient.ind₂ (fun z z' => _) z z'
  -- ⊢ map f (Quotient.mk (Rel.setoid α) z) = map f (Quotient.mk (Rel.setoid α) z') …
  cases' z with x y
  -- ⊢ map f (Quotient.mk (Rel.setoid α) (x, y)) = map f (Quotient.mk (Rel.setoid α …
  cases' z' with x' y'
  -- ⊢ map f (Quotient.mk (Rel.setoid α) (x, y)) = map f (Quotient.mk (Rel.setoid α …
  repeat' rw [map_pair_eq, eq_iff]
  -- ⊢ f x = f x' ∧ f y = f y' ∨ f x = f y' ∧ f y = f x' → x = x' ∧ y = y' ∨ x = y' …
  rintro (h | h) <;> simp [hinj h.1, hinj h.2]
  -- ⊢ x = x' ∧ y = y' ∨ x = y' ∧ y = x'
                     -- 🎉 no goals
                     -- 🎉 no goals
#align sym2.map.injective Sym2.map.injective

section Membership

/-! ### Membership and set coercion -/


/-- This is a predicate that determines whether a given term is a member of a term of the
symmetric square.  From this point of view, the symmetric square is the subtype of
cardinality-two multisets on `α`.
-/
protected def Mem (x : α) (z : Sym2 α) : Prop :=
  ∃ y : α, z = ⟦(x, y)⟧
#align sym2.mem Sym2.Mem

@[aesop norm (rule_sets [Sym2])]
theorem mem_iff' {a b c : α} : Sym2.Mem a ⟦(b, c)⟧ ↔ a = b ∨ a = c :=
  { mp := by
      rintro ⟨_, h⟩
      -- ⊢ a = b ∨ a = c
      rw [eq_iff] at h
      -- ⊢ a = b ∨ a = c
      aesop
      -- 🎉 no goals
    mpr := by
      rintro (rfl | rfl)
      -- ⊢ Sym2.Mem a (Quotient.mk (Rel.setoid α) (a, c))
      · exact ⟨_, rfl⟩
        -- 🎉 no goals
      rw [eq_swap]
      -- ⊢ Sym2.Mem a (Quotient.mk (Rel.setoid α) (a, b))
      exact ⟨_, rfl⟩ }
      -- 🎉 no goals
#align sym2.mem_iff' Sym2.mem_iff'

instance : SetLike (Sym2 α) α where
  coe z := { x | z.Mem x }
  coe_injective' z z' h := by
    simp only [Set.ext_iff, Set.mem_setOf_eq] at h
    -- ⊢ z = z'
    induction' z using Sym2.ind with x y
    -- ⊢ Quotient.mk (Rel.setoid α) (x, y) = z'
    induction' z' using Sym2.ind with x' y'
    -- ⊢ Quotient.mk (Rel.setoid α) (x, y) = Quotient.mk (Rel.setoid α) (x', y')
    have hx := h x; have hy := h y; have hx' := h x'; have hy' := h y'
    -- ⊢ Quotient.mk (Rel.setoid α) (x, y) = Quotient.mk (Rel.setoid α) (x', y')
                    -- ⊢ Quotient.mk (Rel.setoid α) (x, y) = Quotient.mk (Rel.setoid α) (x', y')
                                    -- ⊢ Quotient.mk (Rel.setoid α) (x, y) = Quotient.mk (Rel.setoid α) (x', y')
                                                      -- ⊢ Quotient.mk (Rel.setoid α) (x, y) = Quotient.mk (Rel.setoid α) (x', y')
    simp only [mem_iff', eq_self_iff_true, or_true_iff, iff_true_iff,
      true_or_iff, true_iff_iff] at hx hy hx' hy'
    aesop
    -- 🎉 no goals

@[simp]
theorem mem_iff_mem {x : α} {z : Sym2 α} : Sym2.Mem x z ↔ x ∈ z :=
  Iff.rfl
#align sym2.mem_iff_mem Sym2.mem_iff_mem

theorem mem_iff_exists {x : α} {z : Sym2 α} : x ∈ z ↔ ∃ y : α, z = ⟦(x, y)⟧ :=
  Iff.rfl
#align sym2.mem_iff_exists Sym2.mem_iff_exists

@[ext]
theorem ext {p q : Sym2 α} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  SetLike.ext h
#align sym2.ext Sym2.ext

theorem mem_mk''_left (x y : α) : x ∈ (⟦(x, y)⟧ : Sym2 α) :=
  ⟨y, rfl⟩
#align sym2.mem_mk_left Sym2.mem_mk''_left

theorem mem_mk''_right (x y : α) : y ∈ (⟦(x, y)⟧ : Sym2 α) :=
  eq_swap.subst <| mem_mk''_left y x
#align sym2.mem_mk_right Sym2.mem_mk''_right

@[simp, aesop norm (rule_sets [Sym2])]
theorem mem_iff {a b c : α} : a ∈ (⟦(b, c)⟧ : Sym2 α) ↔ a = b ∨ a = c :=
  mem_iff'
#align sym2.mem_iff Sym2.mem_iff

theorem out_fst_mem (e : Sym2 α) : e.out.1 ∈ e :=
  ⟨e.out.2, by rw [Prod.mk.eta, e.out_eq]⟩
               -- 🎉 no goals
#align sym2.out_fst_mem Sym2.out_fst_mem

theorem out_snd_mem (e : Sym2 α) : e.out.2 ∈ e :=
  ⟨e.out.1, by rw [eq_swap, Prod.mk.eta, e.out_eq]⟩
               -- 🎉 no goals
#align sym2.out_snd_mem Sym2.out_snd_mem

theorem ball {p : α → Prop} {a b : α} : (∀ c ∈ (⟦(a, b)⟧ : Sym2 α), p c) ↔ p a ∧ p b := by
  refine' ⟨fun h => ⟨h _ <| mem_mk''_left _ _, h _ <| mem_mk''_right _ _⟩, fun h c hc => _⟩
  -- ⊢ p c
  obtain rfl | rfl := Sym2.mem_iff.1 hc
  -- ⊢ p c
  · exact h.1
    -- 🎉 no goals
  · exact h.2
    -- 🎉 no goals
#align sym2.ball Sym2.ball

/-- Given an element of the unordered pair, give the other element using `Classical.choose`.
See also `Mem.other'` for the computable version.
-/
noncomputable def Mem.other {a : α} {z : Sym2 α} (h : a ∈ z) : α :=
  Classical.choose h
#align sym2.mem.other Sym2.Mem.other

@[simp]
theorem other_spec {a : α} {z : Sym2 α} (h : a ∈ z) : ⟦(a, Mem.other h)⟧ = z := by
  erw [← Classical.choose_spec h]
  -- 🎉 no goals
#align sym2.other_spec Sym2.other_spec

theorem other_mem {a : α} {z : Sym2 α} (h : a ∈ z) : Mem.other h ∈ z := by
  convert mem_mk''_right a <| Mem.other h
  -- ⊢ z = Quotient.mk (Rel.setoid α) (a, Mem.other h)
  rw [other_spec h]
  -- 🎉 no goals
#align sym2.other_mem Sym2.other_mem

theorem mem_and_mem_iff {x y : α} {z : Sym2 α} (hne : x ≠ y) : x ∈ z ∧ y ∈ z ↔ z = ⟦(x, y)⟧ := by
  constructor
  -- ⊢ x ∈ z ∧ y ∈ z → z = Quotient.mk (Rel.setoid α) (x, y)
  · induction' z using Sym2.ind with x' y'
    -- ⊢ x ∈ Quotient.mk (Rel.setoid α) (x', y') ∧ y ∈ Quotient.mk (Rel.setoid α) (x' …
    rw [mem_iff, mem_iff]
    -- ⊢ (x = x' ∨ x = y') ∧ (y = x' ∨ y = y') → Quotient.mk (Rel.setoid α) (x', y')  …
    aesop
    -- 🎉 no goals
  · rintro rfl
    -- ⊢ x ∈ Quotient.mk (Rel.setoid α) (x, y) ∧ y ∈ Quotient.mk (Rel.setoid α) (x, y)
    simp
    -- 🎉 no goals
#align sym2.mem_and_mem_iff Sym2.mem_and_mem_iff

theorem eq_of_ne_mem {x y : α} {z z' : Sym2 α} (h : x ≠ y) (h1 : x ∈ z) (h2 : y ∈ z) (h3 : x ∈ z')
    (h4 : y ∈ z') : z = z' :=
  ((mem_and_mem_iff h).mp ⟨h1, h2⟩).trans ((mem_and_mem_iff h).mp ⟨h3, h4⟩).symm
#align sym2.eq_of_ne_mem Sym2.eq_of_ne_mem

instance Mem.decidable [DecidableEq α] (x : α) (z : Sym2 α) : Decidable (x ∈ z) :=
  Quotient.recOnSubsingleton z fun ⟨_, _⟩ => decidable_of_iff' _ mem_iff
#align sym2.mem.decidable Sym2.Mem.decidable

end Membership

@[simp]
theorem mem_map {f : α → β} {b : β} {z : Sym2 α} : b ∈ Sym2.map f z ↔ ∃ a, a ∈ z ∧ f a = b := by
  induction' z using Sym2.ind with x y
  -- ⊢ b ∈ map f (Quotient.mk (Rel.setoid α) (x, y)) ↔ ∃ a, a ∈ Quotient.mk (Rel.se …
  simp only [map, Quotient.map_mk, Prod.map_mk, mem_iff]
  -- ⊢ b = f x ∨ b = f y ↔ ∃ a, (a = x ∨ a = y) ∧ f a = b
  constructor
  -- ⊢ b = f x ∨ b = f y → ∃ a, (a = x ∨ a = y) ∧ f a = b
  · rintro (rfl | rfl)
    -- ⊢ ∃ a, (a = x ∨ a = y) ∧ f a = f x
    · exact ⟨x, by simp⟩
      -- 🎉 no goals
    · exact ⟨y, by simp⟩
      -- 🎉 no goals
  · rintro ⟨w, rfl | rfl, rfl⟩ <;> simp
    -- ⊢ f w = f w ∨ f w = f y
                                   -- 🎉 no goals
                                   -- 🎉 no goals
#align sym2.mem_map Sym2.mem_map

@[congr]
theorem map_congr {f g : α → β} {s : Sym2 α} (h : ∀ x ∈ s, f x = g x) : map f s = map g s := by
  ext y
  -- ⊢ y ∈ map f s ↔ y ∈ map g s
  simp only [mem_map]
  -- ⊢ (∃ a, a ∈ s ∧ f a = y) ↔ ∃ a, a ∈ s ∧ g a = y
  constructor <;>
  -- ⊢ (∃ a, a ∈ s ∧ f a = y) → ∃ a, a ∈ s ∧ g a = y
    · rintro ⟨w, hw, rfl⟩
      -- ⊢ ∃ a, a ∈ s ∧ g a = f w
      -- ⊢ ∃ a, a ∈ s ∧ f a = g w
      -- 🎉 no goals
      exact ⟨w, hw, by simp [hw, h]⟩
      -- 🎉 no goals
#align sym2.map_congr Sym2.map_congr

/-- Note: `Sym2.map_id` will not simplify `Sym2.map id z` due to `Sym2.map_congr`. -/
@[simp]
theorem map_id' : (map fun x : α => x) = id :=
  map_id
#align sym2.map_id' Sym2.map_id'

/-! ### Diagonal -/


/-- A type `α` is naturally included in the diagonal of `α × α`, and this function gives the image
of this diagonal in `Sym2 α`.
-/
def diag (x : α) : Sym2 α :=
  ⟦(x, x)⟧
#align sym2.diag Sym2.diag

theorem diag_injective : Function.Injective (Sym2.diag : α → Sym2 α) := fun x y h => by
  cases Quotient.exact h <;> rfl
  -- ⊢ x = x
                             -- 🎉 no goals
                             -- 🎉 no goals
#align sym2.diag_injective Sym2.diag_injective

/-- A predicate for testing whether an element of `Sym2 α` is on the diagonal.
-/
def IsDiag : Sym2 α → Prop :=
  lift ⟨Eq, fun _ _ => propext eq_comm⟩
#align sym2.is_diag Sym2.IsDiag

theorem mk''_isDiag_iff {x y : α} : IsDiag ⟦(x, y)⟧ ↔ x = y :=
  Iff.rfl
#align sym2.mk_is_diag_iff Sym2.mk''_isDiag_iff

@[simp]
theorem isDiag_iff_proj_eq (z : α × α) : IsDiag ⟦z⟧ ↔ z.1 = z.2 :=
  Prod.recOn z fun _ _ => mk''_isDiag_iff
#align sym2.is_diag_iff_proj_eq Sym2.isDiag_iff_proj_eq

@[simp]
theorem diag_isDiag (a : α) : IsDiag (diag a) :=
  Eq.refl a
#align sym2.diag_is_diag Sym2.diag_isDiag

theorem IsDiag.mem_range_diag {z : Sym2 α} : IsDiag z → z ∈ Set.range (@diag α) := by
  induction' z using Sym2.ind with x y
  -- ⊢ IsDiag (Quotient.mk (Rel.setoid α) (x, y)) → Quotient.mk (Rel.setoid α) (x,  …
  rintro (rfl : x = y)
  -- ⊢ Quotient.mk (Rel.setoid α) (x, x) ∈ Set.range diag
  exact ⟨_, rfl⟩
  -- 🎉 no goals
#align sym2.is_diag.mem_range_diag Sym2.IsDiag.mem_range_diag

theorem isDiag_iff_mem_range_diag (z : Sym2 α) : IsDiag z ↔ z ∈ Set.range (@diag α) :=
  ⟨IsDiag.mem_range_diag, fun ⟨i, hi⟩ => hi ▸ diag_isDiag i⟩
#align sym2.is_diag_iff_mem_range_diag Sym2.isDiag_iff_mem_range_diag

instance IsDiag.decidablePred (α : Type u) [DecidableEq α] : DecidablePred (@IsDiag α) := by
  refine' fun z => Quotient.recOnSubsingleton z fun a => _
  -- ⊢ Decidable (IsDiag (Quotient.mk (Rel.setoid α) a))
  erw [isDiag_iff_proj_eq]
  -- ⊢ Decidable (a.fst = a.snd)
  infer_instance
  -- 🎉 no goals
#align sym2.is_diag.decidable_pred Sym2.IsDiag.decidablePred

theorem other_ne {a : α} {z : Sym2 α} (hd : ¬IsDiag z) (h : a ∈ z) : Mem.other h ≠ a := by
  contrapose! hd
  -- ⊢ IsDiag z
  have h' := Sym2.other_spec h
  -- ⊢ IsDiag z
  rw [hd] at h'
  -- ⊢ IsDiag z
  rw [← h']
  -- ⊢ IsDiag (Quotient.mk (Rel.setoid α) (a, a))
  simp
  -- 🎉 no goals
#align sym2.other_ne Sym2.other_ne

section Relations

/-! ### Declarations about symmetric relations -/


variable {r : α → α → Prop}

/-- Symmetric relations define a set on `Sym2 α` by taking all those pairs
of elements that are related.
-/
def fromRel (sym : Symmetric r) : Set (Sym2 α) :=
  setOf (lift ⟨r, fun _ _ => propext ⟨(sym ·), (sym ·)⟩⟩)
#align sym2.from_rel Sym2.fromRel

@[simp]
theorem fromRel_proj_prop {sym : Symmetric r} {z : α × α} : ⟦z⟧ ∈ fromRel sym ↔ r z.1 z.2 :=
  Iff.rfl
#align sym2.from_rel_proj_prop Sym2.fromRel_proj_prop

-- porting note: commenting out `simp`, `simp` can prove it
-- @[simp]
theorem fromRel_prop {sym : Symmetric r} {a b : α} : ⟦(a, b)⟧ ∈ fromRel sym ↔ r a b :=
  Iff.rfl
#align sym2.from_rel_prop Sym2.fromRel_prop

theorem fromRel_bot : fromRel (fun (x y : α) z => z : Symmetric ⊥) = ∅ := by
  apply Set.eq_empty_of_forall_not_mem fun e => _
  -- ⊢ ∀ (e : Sym2 α), ¬e ∈ fromRel (_ : ∀ (x y : α), ⊥ x y → ⊥ x y)
  apply Sym2.ind
  -- ⊢ ∀ (x y : α), ¬Quotient.mk (Rel.setoid α) (x, y) ∈ fromRel (_ : ∀ (x y : α),  …
  simp [-Set.bot_eq_empty, Prop.bot_eq_false]
  -- 🎉 no goals
#align sym2.from_rel_bot Sym2.fromRel_bot

theorem fromRel_top : fromRel (fun (x y : α) z => z : Symmetric ⊤) = Set.univ := by
  apply Set.eq_univ_of_forall fun e => _
  -- ⊢ ∀ (e : Sym2 α), e ∈ fromRel (_ : ∀ (x y : α), ⊤ x y → ⊤ x y)
  apply Sym2.ind
  -- ⊢ ∀ (x y : α), Quotient.mk (Rel.setoid α) (x, y) ∈ fromRel (_ : ∀ (x y : α), ⊤ …
  simp [-Set.top_eq_univ, Prop.top_eq_true]
  -- 🎉 no goals
#align sym2.from_rel_top Sym2.fromRel_top

theorem fromRel_irreflexive {sym : Symmetric r} :
    Irreflexive r ↔ ∀ {z}, z ∈ fromRel sym → ¬IsDiag z :=
  { mp := by intro h; apply Sym2.ind; aesop
             -- ⊢ ∀ {z : Sym2 α}, z ∈ fromRel sym → ¬IsDiag z
                      -- ⊢ ∀ (x y : α), Quotient.mk (Rel.setoid α) (x, y) ∈ fromRel sym → ¬IsDiag (Quot …
                                      -- 🎉 no goals
    mpr := fun h x hr => h (fromRel_prop.mpr hr) rfl }
#align sym2.from_rel_irreflexive Sym2.fromRel_irreflexive

theorem mem_fromRel_irrefl_other_ne {sym : Symmetric r} (irrefl : Irreflexive r) {a : α}
    {z : Sym2 α} (hz : z ∈ fromRel sym) (h : a ∈ z) : Mem.other h ≠ a :=
  other_ne (fromRel_irreflexive.mp irrefl hz) h
#align sym2.mem_from_rel_irrefl_other_ne Sym2.mem_fromRel_irrefl_other_ne

instance fromRel.decidablePred (sym : Symmetric r) [h : DecidableRel r] :
    DecidablePred (· ∈ Sym2.fromRel sym) := fun z => Quotient.recOnSubsingleton z fun _ => h _ _
#align sym2.from_rel.decidable_pred Sym2.fromRel.decidablePred

/-- The inverse to `Sym2.fromRel`. Given a set on `Sym2 α`, give a symmetric relation on `α`
(see `Sym2.toRel_symmetric`). -/
def ToRel (s : Set (Sym2 α)) (x y : α) : Prop :=
  ⟦(x, y)⟧ ∈ s
#align sym2.to_rel Sym2.ToRel

@[simp]
theorem toRel_prop (s : Set (Sym2 α)) (x y : α) : ToRel s x y ↔ ⟦(x, y)⟧ ∈ s :=
  Iff.rfl
#align sym2.to_rel_prop Sym2.toRel_prop

theorem toRel_symmetric (s : Set (Sym2 α)) : Symmetric (ToRel s) := fun x y => by simp [eq_swap]
                                                                                  -- 🎉 no goals
#align sym2.to_rel_symmetric Sym2.toRel_symmetric

theorem toRel_fromRel (sym : Symmetric r) : ToRel (fromRel sym) = r :=
  rfl
#align sym2.to_rel_from_rel Sym2.toRel_fromRel

theorem fromRel_toRel (s : Set (Sym2 α)) : fromRel (toRel_symmetric s) = s :=
  Set.ext fun z => Sym2.ind (fun _ _ => Iff.rfl) z
#align sym2.from_rel_to_rel Sym2.fromRel_toRel

end Relations

section SymEquiv

/-! ### Equivalence to the second symmetric power -/


attribute [local instance] Vector.Perm.isSetoid

private def fromVector : Vector α 2 → α × α
  | ⟨[a, b], _⟩ => (a, b)
-- porting note: remove alignment for private definition

private theorem perm_card_two_iff {a₁ b₁ a₂ b₂ : α} :
    [a₁, b₁].Perm [a₂, b₂] ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ a₁ = b₂ ∧ b₁ = a₂ :=
  { mp := by
      simp [← Multiset.coe_eq_coe, ← Multiset.cons_coe, Multiset.cons_eq_cons]
      -- ⊢ a₁ = a₂ ∧ b₁ = b₂ ∨ ¬a₁ = a₂ ∧ b₁ = a₂ ∧ b₂ = a₁ → a₁ = a₂ ∧ b₁ = b₂ ∨ a₁ =  …
      aesop
      -- 🎉 no goals
    mpr := fun
        | .inl ⟨h₁, h₂⟩ | .inr ⟨h₁, h₂⟩ => by
          rw [h₁, h₂]
          -- 🎉 no goals
          -- ⊢ [b₂, a₂] ~ [a₂, b₂]
          -- 🎉 no goals
          first | done | apply List.Perm.swap'; rfl }
          -- 🎉 no goals
-- porting note: remove alignment for private theorem

/-- The symmetric square is equivalent to length-2 vectors up to permutations.
-/
def sym2EquivSym' : Equiv (Sym2 α) (Sym' α 2)
    where
  toFun :=
    Quotient.map (fun x : α × α => ⟨[x.1, x.2], rfl⟩)
      (by
        rintro _ _ ⟨_⟩
        -- ⊢ (fun x => { val := [x.fst, x.snd], property := (_ : List.length [x.fst, x.sn …
        · constructor; apply List.Perm.refl
          -- ⊢ [(x✝, y✝).snd] ~ [(x✝, y✝).snd]
                       -- 🎉 no goals
        apply List.Perm.swap'
        -- ⊢ [] ~ []
        rfl)
        -- 🎉 no goals
  invFun :=
    Quotient.map fromVector
      (by
        rintro ⟨x, hx⟩ ⟨y, hy⟩ h
        -- ⊢ Sym2.fromVector { val := x, property := hx } ≈ Sym2.fromVector { val := y, p …
        cases' x with _ x; · simp at hx
        -- ⊢ Sym2.fromVector { val := [], property := hx } ≈ Sym2.fromVector { val := y,  …
                             -- 🎉 no goals
        cases' x with _ x; · simp at hx
        -- ⊢ Sym2.fromVector { val := [head✝], property := hx } ≈ Sym2.fromVector { val : …
                             -- 🎉 no goals
        cases' x with _ x; swap
        -- ⊢ Sym2.fromVector { val := [head✝¹, head✝], property := hx } ≈ Sym2.fromVector …
                           -- ⊢ Sym2.fromVector { val := head✝² :: head✝¹ :: head✝ :: x, property := hx } ≈  …
        · exfalso
          -- ⊢ False
          simp at hx
          -- 🎉 no goals
        cases' y with _ y; · simp at hy
        -- ⊢ Sym2.fromVector { val := [head✝¹, head✝], property := hx } ≈ Sym2.fromVector …
                             -- 🎉 no goals
        cases' y with _ y; · simp at hy
        -- ⊢ Sym2.fromVector { val := [head✝², head✝¹], property := hx } ≈ Sym2.fromVecto …
                             -- 🎉 no goals
        cases' y with _ y; swap
        -- ⊢ Sym2.fromVector { val := [head✝³, head✝²], property := hx } ≈ Sym2.fromVecto …
                           -- ⊢ Sym2.fromVector { val := [head✝⁴, head✝³], property := hx } ≈ Sym2.fromVecto …
        · exfalso
          -- ⊢ False
          simp at hy
          -- 🎉 no goals
        rcases perm_card_two_iff.mp h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        -- ⊢ Sym2.fromVector { val := [head✝¹, head✝], property := hx } ≈ Sym2.fromVector …
        · constructor
          -- 🎉 no goals
        apply Sym2.Rel.swap)
        -- 🎉 no goals
  left_inv := by apply Sym2.ind; aesop (add norm unfold [Sym2.fromVector])
                 -- ⊢ ∀ (x y : α), Quotient.map Sym2.fromVector (_ : ∀ ⦃a b : Vector α 2⦄, (fun x  …
                                 -- 🎉 no goals
  right_inv x := by
    refine' Quotient.recOnSubsingleton x fun x => _
    -- ⊢ Quotient.map (fun x => { val := [x.fst, x.snd], property := (_ : List.length …
    · cases' x with x hx
      -- ⊢ Quotient.map (fun x => { val := [x.fst, x.snd], property := (_ : List.length …
      cases' x with _ x
      -- ⊢ Quotient.map (fun x => { val := [x.fst, x.snd], property := (_ : List.length …
      · simp at hx
        -- 🎉 no goals
      cases' x with _ x
      -- ⊢ Quotient.map (fun x => { val := [x.fst, x.snd], property := (_ : List.length …
      · simp at hx
        -- 🎉 no goals
      cases' x with _ x
      -- ⊢ Quotient.map (fun x => { val := [x.fst, x.snd], property := (_ : List.length …
      swap
      -- ⊢ Quotient.map (fun x => { val := [x.fst, x.snd], property := (_ : List.length …
      · exfalso
        -- ⊢ False
        simp at hx
        -- 🎉 no goals
      rfl
      -- 🎉 no goals
#align sym2.sym2_equiv_sym' Sym2.sym2EquivSym'

/-- The symmetric square is equivalent to the second symmetric power.
-/
def equivSym (α : Type*) : Sym2 α ≃ Sym α 2 :=
  Equiv.trans sym2EquivSym' symEquivSym'.symm
#align sym2.equiv_sym Sym2.equivSym

/-- The symmetric square is equivalent to multisets of cardinality
two. (This is currently a synonym for `equivSym`, but it's provided
in case the definition for `Sym` changes.)
-/
def equivMultiset (α : Type*) : Sym2 α ≃ { s : Multiset α // Multiset.card s = 2 } :=
  equivSym α
#align sym2.equiv_multiset Sym2.equivMultiset

end SymEquiv

section Decidable

/-- An algorithm for computing `Sym2.Rel`.
-/
@[aesop norm unfold (rule_sets [Sym2])]
def relBool [DecidableEq α] (x y : α × α) : Bool :=
  if x.1 = y.1 then x.2 = y.2 else if x.1 = y.2 then x.2 = y.1 else false
#align sym2.rel_bool Sym2.relBool

@[aesop norm unfold (rule_sets [Sym2])]
theorem relBool_spec [DecidableEq α] (x y : α × α) : ↥(relBool x y) ↔ Rel α x y := by
  cases' x with x₁ x₂; cases' y with y₁ y₂
  -- ⊢ relBool (x₁, x₂) y = true ↔ Rel α (x₁, x₂) y
                       -- ⊢ relBool (x₁, x₂) (y₁, y₂) = true ↔ Rel α (x₁, x₂) (y₁, y₂)
  aesop (rule_sets [Sym2]) (add norm unfold [relBool])
  -- 🎉 no goals
#align sym2.rel_bool_spec Sym2.relBool_spec

/-- Given `[DecidableEq α]` and `[Fintype α]`, the following instance gives `Fintype (Sym2 α)`.
-/
instance instRelDecidable (α : Type*) [DecidableEq α] : DecidableRel (Sym2.Rel α) := fun x y =>
  decidable_of_bool (relBool x y) (relBool_spec x y)
-- Porting note: add this other version needed for Data.Finset.Sym
instance instRelDecidable' (α : Type*) [DecidableEq α] :
  DecidableRel (· ≈ · : α × α → α × α → Prop) := instRelDecidable _

-- porting note: extra definitions and lemmas for proving decidable equality in `Sym2`
/-- An algorithm for deciding equality in `Sym2 α`. -/
@[aesop norm unfold (rule_sets [Sym2])]
def eqBool [DecidableEq α] : Sym2 α → Sym2 α → Bool :=
  Sym2.lift₂.toFun
    ⟨fun x₁ x₂ y₁ y₂ => relBool (x₁, x₂) (y₁, y₂), by aesop (add norm unfold [relBool])⟩
                                                      -- 🎉 no goals

@[aesop norm unfold (rule_sets [Sym2])]
theorem eqBool_spec [DecidableEq α] (a b : Sym2 α) : (eqBool a b) ↔ (a = b) :=
  Sym2.inductionOn₂ a b <| by aesop (rule_sets [Sym2])
                              -- 🎉 no goals



/-! ### The other element of an element of the symmetric square -/


/--
A function that gives the other element of a pair given one of the elements.  Used in `Mem.other'`.
-/
@[aesop norm unfold (rule_sets [Sym2])]
private def pairOther [DecidableEq α] (a : α) (z : α × α) : α :=
  if a = z.1 then z.2 else z.1
-- porting note: remove align for private def

/-- Get the other element of the unordered pair using the decidable equality.
This is the computable version of `Mem.other`.
-/
@[aesop norm unfold (rule_sets [Sym2])]
def Mem.other' [DecidableEq α] {a : α} {z : Sym2 α} (h : a ∈ z) : α :=
  Quotient.rec (fun s _ => pairOther a s) (by
    clear h z
    -- ⊢ ∀ (a_1 b : α × α) (p : a_1 ≈ b), Eq.ndrec (motive := fun x => a ∈ x → α) (fu …
    intro x y h
    -- ⊢ Eq.ndrec (motive := fun x => a ∈ x → α) (fun x_1 => Sym2.pairOther a x) (_ : …
    ext hy
    -- ⊢ Eq.ndrec (motive := fun x => a ∈ x → α) (fun x_1 => Sym2.pairOther a x) (_ : …
    convert_to Sym2.pairOther a x = _
    -- ⊢ Eq.ndrec (motive := fun x => a ∈ x → α) (fun x_1 => Sym2.pairOther a x) (_ : …
    · have : ∀ {c e h}, @Eq.ndrec (Quotient (Rel.setoid α)) (Quotient.mk (Rel.setoid α) x)
          (fun x => a ∈ x → α) (fun _ => Sym2.pairOther a x) c e h = Sym2.pairOther a x := by
          intro _ e _; subst e; rfl
      apply this
      -- 🎉 no goals
    · rw [mem_iff] at hy
      -- ⊢ Sym2.pairOther a x = Sym2.pairOther a y
      have : relBool x y := (relBool_spec x y).mpr h
      -- ⊢ Sym2.pairOther a x = Sym2.pairOther a y
      aesop (add norm unfold [pairOther, relBool]))
      -- 🎉 no goals
    z h
#align sym2.mem.other' Sym2.Mem.other'

@[simp]
theorem other_spec' [DecidableEq α] {a : α} {z : Sym2 α} (h : a ∈ z) : ⟦(a, Mem.other' h)⟧ = z := by
  induction z using Sym2.ind
  -- ⊢ Quotient.mk (Rel.setoid α) (a, Mem.other' h) = Quotient.mk (Rel.setoid α) (x …
  have h' := mem_iff.mp h
  -- ⊢ Quotient.mk (Rel.setoid α) (a, Mem.other' h) = Quotient.mk (Rel.setoid α) (x …
  aesop (add norm unfold [Quotient.rec, Quot.rec]) (rule_sets [Sym2])
  -- 🎉 no goals
#align sym2.other_spec' Sym2.other_spec'

@[simp]
theorem other_eq_other' [DecidableEq α] {a : α} {z : Sym2 α} (h : a ∈ z) :
  Mem.other h = Mem.other' h := by rw [← congr_right, other_spec' h, other_spec]
                                   -- 🎉 no goals
#align sym2.other_eq_other' Sym2.other_eq_other'

theorem other_mem' [DecidableEq α] {a : α} {z : Sym2 α} (h : a ∈ z) : Mem.other' h ∈ z := by
  rw [← other_eq_other']
  -- ⊢ Mem.other h ∈ z
  exact other_mem h
  -- 🎉 no goals
#align sym2.other_mem' Sym2.other_mem'

theorem other_invol' [DecidableEq α] {a : α} {z : Sym2 α} (ha : a ∈ z) (hb : Mem.other' ha ∈ z) :
    Mem.other' hb = a := by
  induction z using Sym2.ind
  -- ⊢ Mem.other' hb = a
  aesop (rule_sets [Sym2]) (add norm unfold [Quotient.rec, Quot.rec])
  -- 🎉 no goals
#align sym2.other_invol' Sym2.other_invol'

theorem other_invol {a : α} {z : Sym2 α} (ha : a ∈ z) (hb : Mem.other ha ∈ z) : Mem.other hb = a :=
  by classical
    rw [other_eq_other'] at hb ⊢
    convert other_invol' ha hb using 2
    apply other_eq_other'
#align sym2.other_invol Sym2.other_invol

theorem filter_image_quotient_mk''_isDiag [DecidableEq α] (s : Finset α) :
    ((s ×ˢ s).image Quotient.mk'').filter IsDiag = s.diag.image Quotient.mk'' := by
  ext z
  -- ⊢ z ∈ filter IsDiag (image Quotient.mk'' (s ×ˢ s)) ↔ z ∈ image Quotient.mk'' ( …
  induction' z using Sym2.inductionOn
  -- ⊢ Quotient.mk (Rel.setoid α) (x✝, y✝) ∈ filter IsDiag (image Quotient.mk'' (s  …
  simp only [mem_image, mem_diag, exists_prop, mem_filter, Prod.exists, mem_product]
  -- ⊢ (∃ a b, (a ∈ s ∧ b ∈ s) ∧ Quotient.mk'' (a, b) = Quotient.mk (Rel.setoid α)  …
  constructor
  -- ⊢ (∃ a b, (a ∈ s ∧ b ∈ s) ∧ Quotient.mk'' (a, b) = Quotient.mk (Rel.setoid α)  …
  · rintro ⟨⟨a, b, ⟨ha, hb⟩, (h : Quotient.mk _ _ = _)⟩, hab⟩
    -- ⊢ ∃ a b, (a ∈ s ∧ a = b) ∧ Quotient.mk'' (a, b) = Quotient.mk (Rel.setoid α) ( …
    rw [← h, Sym2.mk''_isDiag_iff] at hab
    -- ⊢ ∃ a b, (a ∈ s ∧ a = b) ∧ Quotient.mk'' (a, b) = Quotient.mk (Rel.setoid α) ( …
    exact ⟨a, b, ⟨ha, hab⟩, h⟩
    -- 🎉 no goals
  · rintro ⟨a, b, ⟨ha, rfl⟩, h⟩
    -- ⊢ (∃ a b, (a ∈ s ∧ b ∈ s) ∧ Quotient.mk'' (a, b) = Quotient.mk (Rel.setoid α)  …
    rw [← h]
    -- ⊢ (∃ a_1 b, (a_1 ∈ s ∧ b ∈ s) ∧ Quotient.mk'' (a_1, b) = Quotient.mk'' (a, a)) …
    exact ⟨⟨a, a, ⟨ha, ha⟩, rfl⟩, rfl⟩
    -- 🎉 no goals
#align sym2.filter_image_quotient_mk_is_diag Sym2.filter_image_quotient_mk''_isDiag

theorem filter_image_quotient_mk''_not_isDiag [DecidableEq α] (s : Finset α) :
    (((s ×ˢ s).image Quotient.mk'').filter fun a : Sym2 α => ¬a.IsDiag) =
      s.offDiag.image Quotient.mk'' := by
  ext z
  -- ⊢ z ∈ filter (fun a => ¬IsDiag a) (image Quotient.mk'' (s ×ˢ s)) ↔ z ∈ image Q …
  induction z using Sym2.inductionOn
  -- ⊢ Quotient.mk (Rel.setoid α) (x✝, y✝) ∈ filter (fun a => ¬IsDiag a) (image Quo …
  simp only [mem_image, mem_offDiag, mem_filter, Prod.exists, mem_product]
  -- ⊢ (∃ a b, (a ∈ s ∧ b ∈ s) ∧ Quotient.mk'' (a, b) = Quotient.mk (Rel.setoid α)  …
  constructor
  -- ⊢ (∃ a b, (a ∈ s ∧ b ∈ s) ∧ Quotient.mk'' (a, b) = Quotient.mk (Rel.setoid α)  …
  · rintro ⟨⟨a, b, ⟨ha, hb⟩, (h : Quotient.mk _ _ = _)⟩, hab⟩
    -- ⊢ ∃ a b, (a ∈ s ∧ b ∈ s ∧ a ≠ b) ∧ Quotient.mk'' (a, b) = Quotient.mk (Rel.set …
    rw [← h, Sym2.mk''_isDiag_iff] at hab
    -- ⊢ ∃ a b, (a ∈ s ∧ b ∈ s ∧ a ≠ b) ∧ Quotient.mk'' (a, b) = Quotient.mk (Rel.set …
    exact ⟨a, b, ⟨ha, hb, hab⟩, h⟩
    -- 🎉 no goals
  · rintro ⟨a, b, ⟨ha, hb, hab⟩, (h : Quotient.mk _ _ = _)⟩
    -- ⊢ (∃ a b, (a ∈ s ∧ b ∈ s) ∧ Quotient.mk'' (a, b) = Quotient.mk (Rel.setoid α)  …
    rw [Ne.def, ← Sym2.mk''_isDiag_iff, h] at hab
    -- ⊢ (∃ a b, (a ∈ s ∧ b ∈ s) ∧ Quotient.mk'' (a, b) = Quotient.mk (Rel.setoid α)  …
    exact ⟨⟨a, b, ⟨ha, hb⟩, h⟩, hab⟩
    -- 🎉 no goals
#align sym2.filter_image_quotient_mk_not_is_diag Sym2.filter_image_quotient_mk''_not_isDiag

end Decidable

instance [Subsingleton α] : Subsingleton (Sym2 α) :=
  (equivSym α).injective.subsingleton

instance [Unique α] : Unique (Sym2 α) :=
  Unique.mk' _

instance [IsEmpty α] : IsEmpty (Sym2 α) :=
  (equivSym α).isEmpty

instance [Nontrivial α] : Nontrivial (Sym2 α) :=
  diag_injective.nontrivial

end Sym2
