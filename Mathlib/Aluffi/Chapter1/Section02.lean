import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Log


set_option autoImplicit false

-- 2.1
-- How many different bijections are there between a set S with n elements and itself?
-- example (α : Type _) [Fintype α] [DecidableEq α] :
--     Fintype.card (Equiv.Perm α) = Nat.factorial (Fintype.card α) := by
--   induction' hn : Fintype.card α with n IH generalizing α
--   · rw [Fintype.card_eq_zero_iff] at hn
--     exact Fintype.card_unique
--   · have : Nonempty α
--     · simp [←Fintype.card_pos_iff, hn]
--     inhabit α
--     specialize IH {a : α // a ≠ default} ?_
--     · simp [hn]
--     let e : α ≃ {a : α // a ≠ default} ⊕ Unit
--     · refine' ⟨λ a => if ha : a = default then Sum.inr () else Sum.inl ⟨a, ha⟩,
--                λ a => Sum.rec Subtype.val (λ _ => default) a, _, _⟩
--       · intro x
--         by_cases hx : x = default <;>
--         simp [hx]
--       · rintro (x|_)
--         · simp [x.prop]
--         · simp
--     rw [Fintype.card_congr (e.permCongr), Fintype.card,
--         ←(Finset.filter_union_filter_neg_eq
--           (λ p => p (Sum.inr ()) = Sum.inr ()) (Finset.univ : Finset (Equiv.Perm _))),
--         Finset.card_union_eq]
--     rw [Nat.factorial_succ, add_mul, one_mul, add_comm]
--     refine' congr_arg₂ _ _ _
--     · rw [←IH, Fintype.card]
--       have : n = Fintype.card {a : α // a ≠ default}
--       · simp [hn]
--       classical
--       have key :
--         Finset.filter (λ p => p (Sum.inr ()) ≠ Sum.inr ()) (Finset.univ : Finset (Equiv.Perm ({a : α // a ≠ default} ⊕ Unit))) =
--         (Finset.bunionᵢ (Finset.univ (α := ({a : α // a ≠ default}))) (λ x => (Finset.univ (α := Equiv.Perm {a : α // a ≠ default})).image
--           (λ p => (p.sumCongr (Equiv.refl _)).trans (Equiv.swap (Sum.inl x) (Sum.inr ())))))
--       · ext p
--         simp only [ne_eq, Finset.mem_univ, forall_true_left, Finset.mem_filter, true_and,
--                    Finset.mem_bunionᵢ, Finset.mem_image, Subtype.exists]
--         constructor
--         · intro hp
--           _
--         · _
--     · _
example (α : Type _) [Fintype α] [DecidableEq α] :
    Fintype.card (Equiv.Perm α) = Nat.factorial (Fintype.card α) := Fintype.card_perm

-- 2.2
-- Prove statement (2) in Proposition 2.1.
-- You may assume that given a family of disjoint subsets of a set,
-- there is a way to choose one element in each member of the family
-- Proposition 2.1. Assume A ≠ 0, and let f : A → B be a function.
-- (2) f has a right-inverse if and only if it is surjective.
open Function in
example (A B : Type _) [Inhabited A] (f : A → B) :
    HasRightInverse f ↔ Surjective f := by
  constructor
  · rintro ⟨g, hg⟩ x
    exact ⟨g x, hg x⟩
  · intro h
    exact ⟨λ y => (h y).choose, λ y => (h y).choose_spec⟩

-- 2.3
-- Prove that the inverse of a bijection is a bijection and that the composition of two bijections
-- is a bijection
open Function in
example {α β : Type _} (f : α → β) (hf : Bijective f) :
    Bijective (hf.surjective.surjInv (f := f)) := by
  constructor
  · intros b b' h
    rwa [←hf.injective.eq_iff, hf.surjective.surjInv_eq (f := f),
        hf.surjective.surjInv_eq (f := f)] at h
  · intro a
    refine' ⟨f a, _⟩
    rw [←hf.injective.eq_iff, hf.surjective.surjInv_eq (f := f)]

open Function in
example {α β γ : Type _} (f : α → β) (hf : Bijective f) (g : β → γ) (hg : Bijective g) :
    Bijective (g ∘ f) := by
  constructor
  · intro x y h
    exact hf.injective (hg.injective h)
  · intro z
    obtain ⟨y, hy⟩ := hg.surjective z
    obtain ⟨x, hx⟩ := hf.surjective y
    refine' ⟨x, _⟩
    simp [hx, hy]

-- 2.4
-- Prove that `isomorphism' is an equivalence relation (on any set of sets).
example : Setoid (Type _) where
  r X Y := Nonempty (X ≃ Y)
  iseqv := by
    refine' ⟨_, _, _⟩
    · intro X
      exact ⟨Equiv.refl X⟩
    · rintro X Y ⟨e⟩
      exact ⟨e.symm⟩
    · intro X Y Z ⟨e⟩ ⟨f⟩
      exact ⟨e.trans f⟩

-- 2.5.
-- Formulate a notion of epimorphism, in the style of the notion of monomorphism seen in §2.6,
-- and prove a result analogous to Proposition 2.3, for epimorphisms and surjections. 1
universe u v w in
def epi {A : Sort u} {B : Sort v} (f : A → B) : Prop :=
    ∀ {Z : Sort w} ⦃g g' : B → Z⦄, g ∘ f = g' ∘ f → g = g'

example {A B : Type _} (f : A → B) :
    Function.Surjective f ↔ epi f := by
  constructor
  · intro h Z g g' hg
    funext b
    obtain ⟨a, ha⟩ := h b
    rw [←ha]
    exact congr_fun hg a
  · intro h b
    specialize @h Prop (λ x => ∃ a, f a = x) (λ _ => True) _
    · ext a
      simp
    · simp [congr_fun h b]

-- 2.6
-- With notation as in Example 2.4, explain how any function f : A -> B
-- determines a section of π_A.
example {A B : Type _} (f : A → B) :
    Function.RightInverse (λ a : A => (a, f a)) Prod.fst := by
  intro a
  rfl

-- 2.7
-- Let f : A → B be any function. Prove that the graph Γ_f of f is isomorphic to A.
example {A B : Type _} (f : A → B) :
    { p : A × B | p.2 = f p.1 } ≃ A where
  toFun := λ ⟨⟨a, _⟩, _⟩ => a
  invFun := λ a => ⟨⟨a, f a⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨a, b⟩, h⟩
    simpa using h.symm
  right_inv := by
    intro a
    simp

def rel16 (a b : ℝ) : Prop := ∃ z : ℤ, b - a = z

instance rel16s : Setoid ℝ where
  r := rel16
  iseqv := by
    simp_rw [rel16]
    refine' ⟨_, _, _⟩
    · intro
      use 0
      simp
    · rintro _ _ ⟨z, hz⟩
      refine' ⟨-z, _⟩
      simp [←hz]
    · rintro _ _ _ ⟨z, hz⟩ ⟨w, hw⟩
      refine' ⟨w + z, _⟩
      simp [←hz, ←hw]

-- 2.8
-- Describe as explicitly as you can all terms in the canonical decomposition (cf. §2.8)
-- of the function ℝ → ℂ defined by r ↦ e^(2πir).
-- (This exercise matches one assigned previously. Which one?): 1.6
example :
    (λ r : ℝ => Complex.exp (2 * Real.pi * Complex.I * r)) =
    -- `Subtype.val` is always injective by `Subtype.val_injective`
    (Subtype.val (p := (· ∈ Set.range (λ r : ℝ => Complex.exp (2 * Real.pi * Complex.I * r)))) ∘
      Quotient.lift (λ r : ℝ => ⟨Complex.exp (2 * Real.pi * Complex.I * r), _, rfl⟩)
      (λ a b => by
        rintro ⟨z, hz⟩
        rw [sub_eq_iff_eq_add] at hz
        subst b
        simp [mul_add, mul_comm _ (z : ℂ), Complex.exp_add])
    -- `Quotient.mk'` is always surjective by `surjective_quotient_mk`
      ∘ Quotient.mk') := by
  ext r : 1
  simp [Quotient.mk'] -- ideally, there would be a `Quotient.lift_mk'`

-- isomorphism proof
example : Function.Bijective (Quotient.lift
    (β := Subtype ((· ∈ Set.range λ r : ℝ => Complex.exp (2 * Real.pi * Complex.I * r))))
    (s := rel16s)
    (λ r : ℝ => ⟨Complex.exp (2 * Real.pi * Complex.I * r), _, rfl⟩)
    (λ a b => by
        rintro ⟨z, hz⟩
        rw [sub_eq_iff_eq_add] at hz
        subst b
        simp [mul_add, mul_comm _ (z : ℂ), Complex.exp_add])) := by
  refine' ⟨_, _⟩
  · rintro a b
    induction' a, b using Quotient.inductionOn₂ with a b
    simp only [Quotient.lift_mk, Subtype.mk.injEq, Quotient.eq]
    intro h
    rw [eq_comm, Complex.exp_eq_exp_iff_exp_sub_eq_one, ←mul_sub, Complex.exp_eq_one_iff] at h
    obtain ⟨n, h⟩ := h
    rw [mul_comm (↑n : ℂ), mul_eq_mul_left_iff] at h
    norm_cast at h
    refine' ⟨n, h.resolve_right _⟩
    simp [not_or, Real.pi_ne_zero, Complex.I_ne_zero]
  · rintro ⟨z, r, rfl⟩
    refine' ⟨⟦r⟧, _⟩
    simp

-- 2.9
-- Show that if A' ≅ A" and B' ≅ B" and further A' ∩ B' = 0 and A" ∩ B" = 0, then A' ∪ B' ≅ A" ∪ B".
-- Conclude that the operation A ⨆ B (as described in §1.4) is well-defined up to isomorphism
-- (cf. §2.9). 1§2.9, 5.7]
noncomputable
def equiv29 {X : Type _} (A A' B B' : Set X) (fA : A ≃ A') (fB : B ≃ B') (h : A ∩ B = ∅)
    (h' : A' ∩ B' = ∅) : ↑(A ∪ B) ≃ ↑(A' ∪ B') := by
  classical
  exact ⟨
    λ x => if hx : (x : X) ∈ A then ⟨fA ⟨x, hx⟩, by simp⟩ else
      have hx' : (x : X) ∈ B := x.prop.resolve_left hx
      ⟨fB ⟨x, hx'⟩, by simp⟩,
    λ x => if hx : (x : X) ∈ A' then ⟨fA.symm ⟨x, hx⟩, by simp⟩ else
      have hx' : (x : X) ∈ B' := x.prop.resolve_left hx
      ⟨fB.symm ⟨x, hx'⟩, by simp⟩,
    by
      rintro ⟨x, hx⟩
      by_cases hxA : x ∈ A
      · simp [hxA]
      · have hxB : x ∈ B := hx.resolve_left hxA
        have hxB' : (fB ⟨x, hxB⟩ : X) ∉ A'
        · intro H
          simpa using h'.le <| Set.mem_inter H (fB ⟨x, hxB⟩).prop
        simp [hxA, hxB'],
    by
      rintro ⟨x, hx⟩
      by_cases hxA : x ∈ A'
      · simp [hxA]
      · have hxB : x ∈ B' := hx.resolve_left hxA
        have hxB' : (fB.symm ⟨x, hxB⟩ : X) ∉ A
        · intro H
          simpa using h.le <| Set.mem_inter H (fB.symm ⟨x, hxB⟩).prop
        simp [hxA, hxB']⟩

-- 2.10. Show that if A and B are finite sets, then |B^A| = |B|^|A|. [§2.1, 2.11, §11.4.11]
example (A B : Type _) [DecidableEq A] [Fintype A] [Fintype B] :
    Fintype.card (A → B) = Fintype.card B ^ Fintype.card A := by
  induction' hn : Fintype.card A with n IH generalizing A
  · rw [Fintype.card_eq_zero_iff] at hn
    rw [Fintype.card_unique]
    simp
  · have : 0 < Fintype.card A := by simp [hn]
    rw [Fintype.card_pos_iff] at this
    inhabit A
    specialize IH ({a : A // a ≠ default}) _
    · simp [hn]
    rw [pow_succ, ←IH, ←Fintype.card_prod]
    refine Fintype.card_congr {
      toFun := λ f => ⟨f default, λ ⟨a, ha⟩ => f a⟩
      invFun := λ ⟨b, f⟩ a => if ha : a = default then b else f ⟨a, ha⟩
      left_inv := by
        intro f
        ext a
        dsimp
        split
        · subst a
          rfl
        · rfl
      right_inv := by
        rintro ⟨b, f⟩
        simp only [ne_eq, dite_true, Subtype.coe_eta, dite_eq_ite, Prod.mk.injEq, true_and]
        ext ⟨a, ha⟩
        simp [ha]
    }

-- 2.11. to In view of Exercise 2.10, it is not unreasonable to use 2^A to denote the set of
-- functions from an arbitrary set A to a set with 2 elements (say {0,1}).
-- Prove that there is a bijection between 2^A and the power set of A (cf. § 1.2). [§1.2, III.2.31]
noncomputable example (A : Type _) : (A → Fin 2) ≃ Set A where
  toFun f := {a : A | f a = 0}
  invFun s a := by classical exact if a ∈ s then 0 else 1
  left_inv f := by
    ext a s
    dsimp
    split_ifs with h
    · simp [h]
    · refine' le_antisymm (Nat.succ_le_of_lt (Nat.pos_of_ne_zero _)) _
      · simpa [Fin.ext_iff] using h
      · exact le_top (α := Fin 2)
  right_inv s := by
    ext
    dsimp
    split <;>
    simp [*]
