/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fin.Fin2
import Mathlib.Data.PFun
import Mathlib.Data.Vector3
import Mathlib.NumberTheory.PellMatiyasevic

#align_import number_theory.dioph from "leanprover-community/mathlib"@"a66d07e27d5b5b8ac1147cacfe353478e5c14002"

/-!
# Diophantine functions and Matiyasevic's theorem

Hilbert's tenth problem asked whether there exists an algorithm which for a given integer polynomial
determines whether this polynomial has integer solutions. It was answered in the negative in 1970,
the final step being completed by Matiyasevic who showed that the power function is Diophantine.

Here a function is called Diophantine if its graph is Diophantine as a set. A subset `S ⊆ ℕ ^ α` in
turn is called Diophantine if there exists an integer polynomial on `α ⊕ β` such that `v ∈ S` iff
there exists `t : ℕ^β` with `p (v, t) = 0`.

## Main definitions

* `IsPoly`: a predicate stating that a function is a multivariate integer polynomial.
* `Poly`: the type of multivariate integer polynomial functions.
* `Dioph`: a predicate stating that a set is Diophantine, i.e. a set `S ⊆ ℕ^α` is
  Diophantine if there exists a polynomial on `α ⊕ β` such that `v ∈ S` iff there
  exists `t : ℕ^β` with `p (v, t) = 0`.
* `dioph_fn`: a predicate on a function stating that it is Diophantine in the sense that its graph
  is Diophantine as a set.

## Main statements

* `pell_dioph` states that solutions to Pell's equation form a Diophantine set.
* `pow_dioph` states that the power function is Diophantine, a version of Matiyasevic's theorem.

## References

* [M. Carneiro, _A Lean formalization of Matiyasevic's theorem_][carneiro2018matiyasevic]
* [M. Davis, _Hilbert's tenth problem is unsolvable_][MR317916]

## Tags

Matiyasevic's theorem, Hilbert's tenth problem

## TODO

* Finish the solution of Hilbert's tenth problem.
* Connect `Poly` to `MvPolynomial`
-/


open Fin2 Function Nat Sum

local infixr:67 " ::ₒ " => Option.elim'

local infixr:65 " ⊗ " => Sum.elim

universe u

/-!
### Multivariate integer polynomials

Note that this duplicates `MvPolynomial`.
-/


section Polynomials

variable {α β γ : Type*}

/-- A predicate asserting that a function is a multivariate integer polynomial.
  (We are being a bit lazy here by allowing many representations for multiplication,
  rather than only allowing monomials and addition, but the definition is equivalent
  and this is easier to use.) -/
inductive IsPoly : ((α → ℕ) → ℤ) → Prop
  | proj : ∀ i, IsPoly fun x : α → ℕ => x i
  | const : ∀ n : ℤ, IsPoly fun _ : α → ℕ => n
  | sub : ∀ {f g : (α → ℕ) → ℤ}, IsPoly f → IsPoly g → IsPoly fun x => f x - g x
  | mul : ∀ {f g : (α → ℕ) → ℤ}, IsPoly f → IsPoly g → IsPoly fun x => f x * g x
#align is_poly IsPoly

theorem IsPoly.neg {f : (α → ℕ) → ℤ} : IsPoly f → IsPoly (-f) := by
  rw [← zero_sub]; exact (IsPoly.const 0).sub
  -- ⊢ IsPoly f → IsPoly (0 - f)
                   -- 🎉 no goals
#align is_poly.neg IsPoly.neg

theorem IsPoly.add {f g : (α → ℕ) → ℤ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly (f + g) := by
  rw [← sub_neg_eq_add]; exact hf.sub hg.neg
  -- ⊢ IsPoly (f - -g)
                         -- 🎉 no goals
#align is_poly.add IsPoly.add

/-- The type of multivariate integer polynomials -/
def Poly (α : Type u) := { f : (α → ℕ) → ℤ // IsPoly f }
#align poly Poly

namespace Poly

section

instance funLike : FunLike (Poly α) (α → ℕ) fun _ => ℤ :=
  ⟨Subtype.val, Subtype.val_injective⟩
#align poly.fun_like Poly.funLike

-- Porting note: This instance is not necessary anymore
-- /-- Helper instance for when there are too many metavariables to apply `fun_like.has_coe_to_fun`
-- directly. -/
-- instance : CoeFun (Poly α) fun _ => (α → ℕ) → ℤ := FunLike.hasCoeToFun

/-- The underlying function of a `Poly` is a polynomial -/
protected theorem isPoly (f : Poly α) : IsPoly f := f.2
#align poly.is_poly Poly.isPoly

/-- Extensionality for `Poly α` -/
@[ext]
theorem ext {f g : Poly α} : (∀ x, f x = g x) → f = g := FunLike.ext _ _
#align poly.ext Poly.ext

/-- The `i`th projection function, `x_i`. -/
def proj (i : α) : Poly α := ⟨_, IsPoly.proj i⟩
#align poly.proj Poly.proj

@[simp]
theorem proj_apply (i : α) (x) : proj i x = x i := rfl
#align poly.proj_apply Poly.proj_apply

/-- The constant function with value `n : ℤ`. -/
def const (n : ℤ) : Poly α := ⟨_, IsPoly.const n⟩
#align poly.const Poly.const

@[simp]
theorem const_apply (n) (x : α → ℕ) : const n x = n := rfl
#align poly.const_apply Poly.const_apply

instance : Zero (Poly α) := ⟨const 0⟩

instance : One (Poly α) := ⟨const 1⟩

instance : Neg (Poly α) := ⟨fun f => ⟨-f, f.2.neg⟩⟩

instance : Add (Poly α) := ⟨fun f g => ⟨f + g, f.2.add g.2⟩⟩

instance : Sub (Poly α) := ⟨fun f g => ⟨f - g, f.2.sub g.2⟩⟩

instance : Mul (Poly α) := ⟨fun f g => ⟨f * g, f.2.mul g.2⟩⟩

@[simp]
theorem coe_zero : ⇑(0 : Poly α) = const 0 := rfl
#align poly.coe_zero Poly.coe_zero

@[simp]
theorem coe_one : ⇑(1 : Poly α) = const 1 := rfl
#align poly.coe_one Poly.coe_one

@[simp]
theorem coe_neg (f : Poly α) : ⇑(-f) = -f := rfl
#align poly.coe_neg Poly.coe_neg

@[simp]
theorem coe_add (f g : Poly α) : ⇑(f + g) = f + g := rfl
#align poly.coe_add Poly.coe_add

@[simp]
theorem coe_sub (f g : Poly α) : ⇑(f - g) = f - g := rfl
#align poly.coe_sub Poly.coe_sub

@[simp]
theorem coe_mul (f g : Poly α) : ⇑(f * g) = f * g := rfl
#align poly.coe_mul Poly.coe_mul

@[simp]
theorem zero_apply (x) : (0 : Poly α) x = 0 := rfl
#align poly.zero_apply Poly.zero_apply

@[simp]
theorem one_apply (x) : (1 : Poly α) x = 1 := rfl
#align poly.one_apply Poly.one_apply

@[simp]
theorem neg_apply (f : Poly α) (x) : (-f) x = -f x := rfl
#align poly.neg_apply Poly.neg_apply

@[simp]
theorem add_apply (f g : Poly α) (x : α → ℕ) : (f + g) x = f x + g x := rfl
#align poly.add_apply Poly.add_apply

@[simp]
theorem sub_apply (f g : Poly α) (x : α → ℕ) : (f - g) x = f x - g x := rfl
#align poly.sub_apply Poly.sub_apply

@[simp]
theorem mul_apply (f g : Poly α) (x : α → ℕ) : (f * g) x = f x * g x := rfl
#align poly.mul_apply Poly.mul_apply

instance (α : Type*) : Inhabited (Poly α) := ⟨0⟩

instance : AddCommGroup (Poly α) := by
  refine' { add := ((· + ·) : Poly α → Poly α → Poly α)
            neg := (Neg.neg : Poly α → Poly α)
            sub := Sub.sub
            zero := 0
            zsmul := @zsmulRec _ ⟨(0 : Poly α)⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩
            nsmul := @nsmulRec _ ⟨(0 : Poly α)⟩ ⟨(· + ·)⟩
            .. }
  all_goals
    intros
    first
      | rfl
      | ext; simp_rw [add_apply]
        first
          | rw [← add_assoc]
          | rw [zero_apply, zero_add]
          | rw [zero_apply, add_zero]
          | rw [neg_apply, add_left_neg, zero_apply]
          | rw [add_comm]

instance : AddGroupWithOne (Poly α) :=
  { (inferInstance : AddCommGroup (Poly α)) with
      one := 1
      natCast := fun n => Poly.const n
      intCast := Poly.const }

instance : CommRing (Poly α) := by
  refine' { (inferInstance : AddCommGroup (Poly α)),
            (inferInstance : AddGroupWithOne (Poly α)) with
              add := ((· + ·) : Poly α → Poly α → Poly α)
              zero := 0
              mul := (· * ·)
              one := 1
              npow := @npowRec _ ⟨(1 : Poly α)⟩ ⟨(· * ·)⟩
              .. }
  all_goals
    intros
    first
      | rfl
      | ext; simp only [add_apply, mul_apply]
        first
          | rw [mul_add]
          | rw [add_mul]
          | rw [zero_apply, zero_mul]
          | rw [zero_apply, mul_zero]
          | rw [← mul_assoc]
          | rw [one_apply, one_mul]
          | rw [one_apply, mul_one]
          | rw [mul_comm]

theorem induction {C : Poly α → Prop} (H1 : ∀ i, C (proj i)) (H2 : ∀ n, C (const n))
    (H3 : ∀ f g, C f → C g → C (f - g)) (H4 : ∀ f g, C f → C g → C (f * g)) (f : Poly α) : C f := by
  cases' f with f pf
  -- ⊢ C { val := f, property := pf }
  induction' pf with i n f g pf pg ihf ihg f g pf pg ihf ihg
  apply H1; apply H2; apply H3 _ _ ihf ihg; apply H4 _ _ ihf ihg
            -- ⊢ C { val := fun x => f x - g x, property := (_ : IsPoly fun x => f x - g x) }
                      -- ⊢ C { val := fun x => f x * g x, property := (_ : IsPoly fun x => f x * g x) }
                                            -- 🎉 no goals
#align poly.induction Poly.induction

/-- The sum of squares of a list of polynomials. This is relevant for
  Diophantine equations, because it means that a list of equations
  can be encoded as a single equation: `x = 0 ∧ y = 0 ∧ z = 0` is
  equivalent to `x^2 + y^2 + z^2 = 0`. -/
def sumsq : List (Poly α) → Poly α
  | [] => 0
  | p::ps => p * p + sumsq ps
#align poly.sumsq Poly.sumsq

theorem sumsq_nonneg (x : α → ℕ) : ∀ l, 0 ≤ sumsq l x
  | [] => le_refl 0
  | p::ps => by
    rw [sumsq]
    -- ⊢ 0 ≤ ↑(p * p + sumsq ps) x
    exact add_nonneg (mul_self_nonneg _) (sumsq_nonneg _ ps)
    -- 🎉 no goals
#align poly.sumsq_nonneg Poly.sumsq_nonneg

theorem sumsq_eq_zero (x) : ∀ l, sumsq l x = 0 ↔ l.All₂ fun a : Poly α => a x = 0
  | [] => eq_self_iff_true _
  | p::ps => by
    rw [List.all₂_cons, ← sumsq_eq_zero _ ps]; rw [sumsq]
    -- ⊢ ↑(sumsq (p :: ps)) x = 0 ↔ ↑p x = 0 ∧ ↑(sumsq ps) x = 0
                                               -- ⊢ ↑(p * p + sumsq ps) x = 0 ↔ ↑p x = 0 ∧ ↑(sumsq ps) x = 0
    exact
      ⟨fun h : p x * p x + sumsq ps x = 0 =>
        have : p x = 0 :=
          eq_zero_of_mul_self_eq_zero <|
            le_antisymm
              (by
                rw [← h]
                have t := add_le_add_left (sumsq_nonneg x ps) (p x * p x)
                rwa [add_zero] at t)
              (mul_self_nonneg _)
        ⟨this, by simp [this] at h; exact h⟩,
      fun ⟨h1, h2⟩ => by rw [add_apply, mul_apply, h1, h2]; rfl⟩
#align poly.sumsq_eq_zero Poly.sumsq_eq_zero

end

/-- Map the index set of variables, replacing `x_i` with `x_(f i)`. -/
def map {α β} (f : α → β) (g : Poly α) : Poly β :=
  ⟨fun v => g <| v ∘ f, Poly.induction (C := fun g => IsPoly (fun v => g (v ∘ f)))
    (fun i => by simp; apply IsPoly.proj) (fun n => by simp; apply IsPoly.const)
                 -- ⊢ IsPoly fun v => ↑(v (f i))
                       -- 🎉 no goals
                                                       -- ⊢ IsPoly fun v => n
                                                             -- 🎉 no goals
    (fun f g pf pg => by simp; apply IsPoly.sub pf pg)
                         -- ⊢ IsPoly fun v => ↑f (v ∘ f✝) - ↑g (v ∘ f✝)
                               -- 🎉 no goals
    (fun f g pf pg => by simp; apply IsPoly.mul pf pg) _⟩
                         -- ⊢ IsPoly fun v => ↑f (v ∘ f✝) * ↑g (v ∘ f✝)
                               -- 🎉 no goals
#align poly.map Poly.map

@[simp]
theorem map_apply {α β} (f : α → β) (g : Poly α) (v) : map f g v = g (v ∘ f) := rfl
#align poly.map_apply Poly.map_apply

end Poly

end Polynomials

/-! ### Diophantine sets -/


/-- A set `S ⊆ ℕ^α` is Diophantine if there exists a polynomial on
  `α ⊕ β` such that `v ∈ S` iff there exists `t : ℕ^β` with `p (v, t) = 0`. -/
def Dioph {α : Type u} (S : Set (α → ℕ)) : Prop :=
  ∃ (β : Type u) (p : Poly (Sum α β)), ∀ v, S v ↔ ∃ t, p (v ⊗ t) = 0
#align dioph Dioph

namespace Dioph

section

variable {α β γ : Type u} {S S' : Set (α → ℕ)}

theorem ext (d : Dioph S) (H : ∀ v, v ∈ S ↔ v ∈ S') : Dioph S' := by rwa [← Set.ext H]
                                                                     -- 🎉 no goals
#align dioph.ext Dioph.ext

theorem of_no_dummies (S : Set (α → ℕ)) (p : Poly α) (h : ∀ v, S v ↔ p v = 0) : Dioph S :=
  ⟨PEmpty, ⟨p.map inl, fun v => (h v).trans ⟨fun h => ⟨PEmpty.elim, h⟩, fun ⟨_, ht⟩ => ht⟩⟩⟩
#align dioph.of_no_dummies Dioph.of_no_dummies

theorem inject_dummies_lem (f : β → γ) (g : γ → Option β) (inv : ∀ x, g (f x) = some x)
    (p : Poly (Sum α β)) (v : α → ℕ) :
    (∃ t, p (v ⊗ t) = 0) ↔ ∃ t, p.map (inl ⊗ inr ∘ f) (v ⊗ t) = 0 := by
  dsimp; refine ⟨fun t => ?_, fun t => ?_⟩ <;> cases' t with t ht
  -- ⊢ (∃ t, ↑p (v ⊗ t) = 0) ↔ ∃ t, ↑p ((v ⊗ t) ∘ (inl ⊗ inr ∘ f)) = 0
         -- ⊢ ∃ t, ↑p ((v ⊗ t) ∘ (inl ⊗ inr ∘ f)) = 0
                                               -- ⊢ ∃ t, ↑p ((v ⊗ t) ∘ (inl ⊗ inr ∘ f)) = 0
                                               -- ⊢ ∃ t, ↑p (v ⊗ t) = 0
  · have : (v ⊗ (0 ::ₒ t) ∘ g) ∘ (inl ⊗ inr ∘ f) = v ⊗ t :=
      funext fun s => by cases' s with a b <;> dsimp [(· ∘ ·)]; try rw [inv]; rfl
    exact ⟨(0 ::ₒ t) ∘ g, by rwa [this]⟩
    -- 🎉 no goals
  · have : v ⊗ t ∘ f = (v ⊗ t) ∘ (inl ⊗ inr ∘ f) := funext fun s => by cases' s with a b <;> rfl
    -- ⊢ ∃ t, ↑p (v ⊗ t) = 0
    exact ⟨t ∘ f, by rwa [this]⟩
    -- 🎉 no goals
#align dioph.inject_dummies_lem Dioph.inject_dummies_lem

theorem inject_dummies (f : β → γ) (g : γ → Option β) (inv : ∀ x, g (f x) = some x)
    (p : Poly (Sum α β)) (h : ∀ v, S v ↔ ∃ t, p (v ⊗ t) = 0) :
    ∃ q : Poly (Sum α γ), ∀ v, S v ↔ ∃ t, q (v ⊗ t) = 0 :=
  ⟨p.map (inl ⊗ inr ∘ f), fun v => (h v).trans <| inject_dummies_lem f g inv _ _⟩
#align dioph.inject_dummies Dioph.inject_dummies

variable (β)

theorem reindex_dioph (f : α → β) : ∀ _ : Dioph S, Dioph {v | v ∘ f ∈ S}
  | ⟨γ, p, pe⟩ => ⟨γ, p.map (inl ∘ f ⊗ inr), fun v =>
      (pe _).trans <|
        exists_congr fun t =>
          suffices v ∘ f ⊗ t = (v ⊗ t) ∘ (inl ∘ f ⊗ inr) by simp [this]
                                                            -- 🎉 no goals
                             -- ⊢ (v ∘ f ⊗ t) (inl a) = ((v ⊗ t) ∘ (inl ∘ f ⊗ inr)) (inl a)
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
          funext fun s => by cases' s with a b <;> rfl⟩
#align dioph.reindex_dioph Dioph.reindex_dioph

variable {β}

theorem DiophList.all₂ (l : List (Set <| α → ℕ)) (d : l.All₂ Dioph) :
    Dioph {v | l.All₂ fun S : Set (α → ℕ) => v ∈ S} := by
  suffices ∃ (β : _) (pl : List (Poly (Sum α β))), ∀ v, List.All₂ (fun S : Set _ => S v) l ↔
          ∃ t, List.All₂ (fun p : Poly (Sum α β) => p (v ⊗ t) = 0) pl
    from
    let ⟨β, pl, h⟩ := this
    ⟨β, Poly.sumsq pl, fun v => (h v).trans <| exists_congr fun t => (Poly.sumsq_eq_zero _ _).symm⟩
  induction' l with S l IH
  -- ⊢ ∃ β pl, ∀ (v : α → ℕ), List.All₂ (fun S => S v) [] ↔ ∃ t, List.All₂ (fun p = …
  exact ⟨ULift Empty, [], fun _ => by simp⟩
  -- ⊢ ∃ β pl, ∀ (v : α → ℕ), List.All₂ (fun S => S v) (S :: l) ↔ ∃ t, List.All₂ (f …
  simp at d
  -- ⊢ ∃ β pl, ∀ (v : α → ℕ), List.All₂ (fun S => S v) (S :: l) ↔ ∃ t, List.All₂ (f …
  exact
    let ⟨⟨β, p, pe⟩, dl⟩ := d
    let ⟨γ, pl, ple⟩ := IH dl
    ⟨Sum β γ, p.map (inl ⊗ inr ∘ inl)::pl.map fun q => q.map (inl ⊗ inr ∘ inr),
      fun v => by
      simp; exact
        Iff.trans (and_congr (pe v) (ple v))
          ⟨fun ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ =>
            ⟨m ⊗ n, by
              rw [show (v ⊗ m ⊗ n) ∘ (inl ⊗ inr ∘ inl) = v ⊗ m from
                    funext fun s => by cases' s with a b <;> rfl]; exact hm, by
              refine List.All₂.imp (fun q hq => ?_) hn; dsimp [(· ∘ ·)]
              rw [show
                    (fun x : Sum α γ => (v ⊗ m ⊗ n) ((inl ⊗ fun x : γ => inr (inr x)) x)) = v ⊗ n
                    from funext fun s => by cases' s with a b <;> rfl]; exact hq⟩,
            fun ⟨t, hl, hr⟩ =>
            ⟨⟨t ∘ inl, by
                rwa [show (v ⊗ t) ∘ (inl ⊗ inr ∘ inl) = v ⊗ t ∘ inl from
                    funext fun s => by cases' s with a b <;> rfl] at hl⟩,
              ⟨t ∘ inr, by
                refine List.All₂.imp (fun q hq => ?_) hr; dsimp [(· ∘ ·)] at hq
                rwa [show
                    (fun x : Sum α γ => (v ⊗ t) ((inl ⊗ fun x : γ => inr (inr x)) x)) =
                      v ⊗ t ∘ inr
                    from funext fun s => by cases' s with a b <;> rfl] at hq ⟩⟩⟩⟩
#align dioph.dioph_list.all₂ Dioph.DiophList.all₂

theorem inter (d : Dioph S) (d' : Dioph S') : Dioph (S ∩ S') := DiophList.all₂ [S, S'] ⟨d, d'⟩
#align dioph.inter Dioph.inter

theorem union : ∀ (_ : Dioph S) (_ : Dioph S'), Dioph (S ∪ S')
  | ⟨β, p, pe⟩, ⟨γ, q, qe⟩ =>
    ⟨Sum β γ, p.map (inl ⊗ inr ∘ inl) * q.map (inl ⊗ inr ∘ inr), fun v => by
      refine
        Iff.trans (or_congr ((pe v).trans ?_) ((qe v).trans ?_))
          (exists_or.symm.trans
            (exists_congr fun t =>
              (@mul_eq_zero _ _ _ (p ((v ⊗ t) ∘ (inl ⊗ inr ∘ inl)))
                  (q ((v ⊗ t) ∘ (inl ⊗ inr ∘ inr)))).symm))
      -- Porting note: putting everything on the same line fails
      · refine inject_dummies_lem _ ?_ ?_ _ _
        -- ⊢ β ⊕ γ → Option β
        exact some ⊗ fun _ => none
        -- ⊢ ∀ (x : β), (some ⊗ fun x => none) (inl x) = some x
        exact fun _ => by simp only [elim_inl]
        -- 🎉 no goals
      -- Porting note: putting everything on the same line fails
      · refine inject_dummies_lem _ ?_ ?_ _ _
        -- ⊢ β ⊕ γ → Option γ
        exact (fun _ => none) ⊗ some
        -- ⊢ ∀ (x : γ), ((fun x => none) ⊗ some) (inr x) = some x
        exact fun _ => by simp only [elim_inr]⟩
        -- 🎉 no goals
#align dioph.union Dioph.union

/-- A partial function is Diophantine if its graph is Diophantine. -/
def DiophPfun (f : (α → ℕ) →. ℕ) : Prop :=
  Dioph {v : Option α → ℕ | f.graph (v ∘ some, v none)}
#align dioph.dioph_pfun Dioph.DiophPfun

/-- A function is Diophantine if its graph is Diophantine. -/
def DiophFn (f : (α → ℕ) → ℕ) : Prop :=
  Dioph {v : Option α → ℕ | f (v ∘ some) = v none}
#align dioph.dioph_fn Dioph.DiophFn

theorem reindex_diophFn {f : (α → ℕ) → ℕ} (g : α → β) (d : DiophFn f) :
    DiophFn fun v => f (v ∘ g) := by convert reindex_dioph (Option β) (Option.map g) d
                                     -- 🎉 no goals
#align dioph.reindex_dioph_fn Dioph.reindex_diophFn

theorem ex_dioph {S : Set (Sum α β → ℕ)} : Dioph S → Dioph {v | ∃ x, v ⊗ x ∈ S}
  | ⟨γ, p, pe⟩ =>
    ⟨Sum β γ, p.map ((inl ⊗ inr ∘ inl) ⊗ inr ∘ inr), fun v =>
      ⟨fun ⟨x, hx⟩ =>
        let ⟨t, ht⟩ := (pe _).1 hx
        ⟨x ⊗ t, by
          simp; rw [show (v ⊗ x ⊗ t) ∘ ((inl ⊗ inr ∘ inl) ⊗ inr ∘ inr) = (v ⊗ x) ⊗ t from
          -- ⊢ ↑p ((v ⊗ x ⊗ t) ∘ ((inl ⊗ inr ∘ inl) ⊗ inr ∘ inr)) = 0
            funext fun s => by cases' s with a b <;> try { cases a <;> rfl }; rfl]
          exact ht⟩,
          -- 🎉 no goals
        fun ⟨t, ht⟩ =>
        ⟨t ∘ inl,
          (pe _).2
            ⟨t ∘ inr, by
              simp at ht
              -- ⊢ ↑p ((v ⊗ t ∘ inl) ⊗ t ∘ inr) = 0
              rwa [show (v ⊗ t) ∘ ((inl ⊗ inr ∘ inl) ⊗ inr ∘ inr) = (v ⊗ t ∘ inl) ⊗ t ∘ inr from
                funext fun s => by cases' s with a b <;> try { cases a <;> rfl }; rfl] at ht⟩⟩⟩⟩
#align dioph.ex_dioph Dioph.ex_dioph

theorem ex1_dioph {S : Set (Option α → ℕ)} : Dioph S → Dioph {v | ∃ x, x ::ₒ v ∈ S}
  | ⟨β, p, pe⟩ =>
    ⟨Option β, p.map (inr none ::ₒ inl ⊗ inr ∘ some), fun v =>
      ⟨fun ⟨x, hx⟩ =>
        let ⟨t, ht⟩ := (pe _).1 hx
        ⟨x ::ₒ t, by
          simp
          -- ⊢ ↑p ((v ⊗ x ::ₒ t) ∘ (inr none ::ₒ inl ⊗ inr ∘ some)) = 0
          rw [show (v ⊗ x ::ₒ t) ∘ (inr none ::ₒ inl ⊗ inr ∘ some) = x ::ₒ v ⊗ t from
            funext fun s => by cases' s with a b <;> try { cases a <;> rfl}; rfl]
          exact ht⟩,
          -- 🎉 no goals
        fun ⟨t, ht⟩ =>
        ⟨t none,
          (pe _).2
            ⟨t ∘ some, by
              simp at ht
              -- ⊢ ↑p (t none ::ₒ v ⊗ t ∘ some) = 0
              rwa [show (v ⊗ t) ∘ (inr none ::ₒ inl ⊗ inr ∘ some) = t none ::ₒ v ⊗ t ∘ some from
                funext fun s => by cases' s with a b <;> try { cases a <;> rfl }; rfl] at ht ⟩⟩⟩⟩
#align dioph.ex1_dioph Dioph.ex1_dioph

theorem dom_dioph {f : (α → ℕ) →. ℕ} (d : DiophPfun f) : Dioph f.Dom :=
  cast (congr_arg Dioph <| Set.ext fun _ => (PFun.dom_iff_graph _ _).symm) (ex1_dioph d)
#align dioph.dom_dioph Dioph.dom_dioph

theorem diophFn_iff_pFun (f : (α → ℕ) → ℕ) : DiophFn f = @DiophPfun α f := by
  refine' congr_arg Dioph (Set.ext fun v => _); exact PFun.lift_graph.symm
  -- ⊢ v ∈ {v | f (v ∘ some) = v none} ↔ v ∈ {v | PFun.graph ↑f (v ∘ some, v none)}
                                                -- 🎉 no goals
#align dioph.dioph_fn_iff_pfun Dioph.diophFn_iff_pFun

theorem abs_poly_dioph (p : Poly α) : DiophFn fun v => (p v).natAbs :=
  of_no_dummies _ ((p.map some - Poly.proj none) * (p.map some + Poly.proj none))
    fun v => (by dsimp; exact Int.eq_natAbs_iff_mul_eq_zero)
                 -- ⊢ setOf (fun v => Int.natAbs (↑p (v ∘ some)) = v none) v ↔ (↑p (v ∘ some) - ↑( …
                        -- 🎉 no goals
#align dioph.abs_poly_dioph Dioph.abs_poly_dioph

theorem proj_dioph (i : α) : DiophFn fun v => v i :=
  abs_poly_dioph (Poly.proj i)
#align dioph.proj_dioph Dioph.proj_dioph

theorem diophPfun_comp1 {S : Set (Option α → ℕ)} (d : Dioph S) {f} (df : DiophPfun f) :
    Dioph {v : α → ℕ | ∃ h : f.Dom v, f.fn v h ::ₒ v ∈ S} :=
  ext (ex1_dioph (d.inter df)) fun v =>
    ⟨fun ⟨x, hS, (h : Exists _)⟩ => by
      rw [show (x ::ₒ v) ∘ some = v from funext fun s => rfl] at h;
      -- ⊢ v ∈ {v | ∃ h, PFun.fn f v h ::ₒ v ∈ S}
        cases' h with hf h; refine' ⟨hf, _⟩; rw [PFun.fn, h]; exact hS,
        -- ⊢ v ∈ {v | ∃ h, PFun.fn f v h ::ₒ v ∈ S}
                            -- ⊢ PFun.fn f v hf ::ₒ v ∈ S
                                             -- ⊢ (v, (x ::ₒ v) none).snd ::ₒ v ∈ S
                                                              -- 🎉 no goals
    fun ⟨x, hS⟩ =>
      ⟨f.fn v x, hS, show Exists _ by
        rw [show (f.fn v x ::ₒ v) ∘ some = v from funext fun s => rfl]; exact ⟨x, rfl⟩⟩⟩
        -- ⊢ ∃ h, Part.get (f (v, (PFun.fn f v x ::ₒ v) none).fst) h = (v, (PFun.fn f v x …
                                                                        -- 🎉 no goals
#align dioph.dioph_pfun_comp1 Dioph.diophPfun_comp1

theorem diophFn_comp1 {S : Set (Option α → ℕ)} (d : Dioph S) {f : (α → ℕ) → ℕ} (df : DiophFn f) :
    Dioph {v | f v ::ₒ v ∈ S} :=
  ext (diophPfun_comp1 d <| cast (diophFn_iff_pFun f) df)
    fun _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨trivial, h⟩⟩
#align dioph.dioph_fn_comp1 Dioph.diophFn_comp1

end

section

variable {α β : Type} {n : ℕ}

open Vector3

open scoped Vector3

-- Porting note: Fails because declaration is in an imported module
-- attribute [local reducible] Vector3

theorem diophFn_vec_comp1 {S : Set (Vector3 ℕ (succ n))} (d : Dioph S) {f : Vector3 ℕ n → ℕ}
    (df : DiophFn f) : Dioph {v : Vector3 ℕ n | (f v::v) ∈ S} :=
  Dioph.ext (diophFn_comp1 (reindex_dioph _ (none::some) d) df) (fun v => by
    dsimp
    -- ⊢ ((f v ::ₒ v) ∘ none :: some) ∈ S ↔ v ∈ {v | (f v :: v) ∈ S}
    -- Porting note: `congr` use to be enough here
    refine iff_of_eq (congrFun (congrArg Membership.mem ?_) S)
    -- ⊢ ((f v ::ₒ v) ∘ none :: some) = f v :: v
    ext x; cases x <;> rfl)
    -- ⊢ ((f v ::ₒ v) ∘ none :: some) x = (f v :: v) x
           -- ⊢ ((f v ::ₒ v) ∘ none :: some) fz = (f v :: v) fz
                       -- 🎉 no goals
                       -- 🎉 no goals
#align dioph.dioph_fn_vec_comp1 Dioph.diophFn_vec_comp1

theorem vec_ex1_dioph (n) {S : Set (Vector3 ℕ (succ n))} (d : Dioph S) :
    Dioph {v : Fin2 n → ℕ | ∃ x, (x::v) ∈ S} :=
  ext (ex1_dioph <| reindex_dioph _ (none::some) d) fun v =>
    exists_congr fun x => by
      dsimp
      -- ⊢ ((x ::ₒ v) ∘ none :: some) ∈ S ↔ (x :: v) ∈ S
      rw [show Option.elim' x v ∘ cons none some = x::v from
          funext fun s => by cases' s with a b <;> rfl]
#align dioph.vec_ex1_dioph Dioph.vec_ex1_dioph

theorem diophFn_vec (f : Vector3 ℕ n → ℕ) : DiophFn f ↔ Dioph {v | f (v ∘ fs) = v fz} :=
  ⟨reindex_dioph _ (fz ::ₒ fs), reindex_dioph _ (none::some)⟩
#align dioph.dioph_fn_vec Dioph.diophFn_vec

theorem diophPfun_vec (f : Vector3 ℕ n →. ℕ) : DiophPfun f ↔ Dioph {v | f.graph (v ∘ fs, v fz)} :=
  ⟨reindex_dioph _ (fz ::ₒ fs), reindex_dioph _ (none::some)⟩
#align dioph.dioph_pfun_vec Dioph.diophPfun_vec

theorem diophFn_compn :
    ∀ {n} {S : Set (Sum α (Fin2 n) → ℕ)} (_ : Dioph S) {f : Vector3 ((α → ℕ) → ℕ) n}
      (_ : VectorAllP DiophFn f), Dioph {v : α → ℕ | (v ⊗ fun i => f i v) ∈ S}
  | 0, S, d, f => fun _ =>
    ext (reindex_dioph _ (id ⊗ Fin2.elim0) d) fun v => by
      dsimp
      -- ⊢ v ∘ (id ⊗ elim0) ∈ S ↔ (v ⊗ fun i => f i v) ∈ S
      -- Porting note: `congr` use to be enough here
      refine iff_of_eq (congrFun (congrArg Membership.mem ?_) S)
      -- ⊢ v ∘ (id ⊗ elim0) = v ⊗ fun i => f i v
      ext x; obtain _ | _ | _ := x; rfl
      -- ⊢ (v ∘ (id ⊗ elim0)) x = (v ⊗ fun i => f i v) x
             -- ⊢ (v ∘ (id ⊗ elim0)) (inl val✝) = (v ⊗ fun i => f i v) (inl val✝)
                                    -- 🎉 no goals
  | succ n, S, d, f =>
    f.consElim fun f fl => by
        simp
        -- ⊢ DiophFn f → VectorAllP DiophFn fl → Dioph {v | (v ⊗ fun i => (f :: fl) i v)  …
        exact fun df dfl =>
          have : Dioph {v | (v ∘ inl ⊗ f (v ∘ inl)::v ∘ inr) ∈ S} :=
            ext (diophFn_comp1 (reindex_dioph _ (some ∘ inl ⊗ none::some ∘ inr) d) <|
                reindex_diophFn inl df)
              fun v => by
                dsimp
                -- Porting note: `congr` use to be enough here
                refine iff_of_eq (congrFun (congrArg Membership.mem ?_) S)
                ext x; obtain _ | _ | _ := x <;> rfl
          have : Dioph {v | (v ⊗ f v::fun i : Fin2 n => fl i v) ∈ S} :=
            @diophFn_compn n (fun v => S (v ∘ inl ⊗ f (v ∘ inl)::v ∘ inr)) this _ dfl
          ext this fun v => by
            dsimp;
            -- Porting note: `congr` use to be enough here
            refine iff_of_eq (congrFun (congrArg Membership.mem ?_) S)
            ext x; obtain _ | _ | _ := x <;> rfl
#align dioph.dioph_fn_compn Dioph.diophFn_compn

theorem dioph_comp {S : Set (Vector3 ℕ n)} (d : Dioph S) (f : Vector3 ((α → ℕ) → ℕ) n)
    (df : VectorAllP DiophFn f) : Dioph {v | (fun i => f i v) ∈ S} :=
  diophFn_compn (reindex_dioph _ inr d) df
#align dioph.dioph_comp Dioph.dioph_comp

theorem diophFn_comp {f : Vector3 ℕ n → ℕ} (df : DiophFn f) (g : Vector3 ((α → ℕ) → ℕ) n)
    (dg : VectorAllP DiophFn g) : DiophFn fun v => f fun i => g i v :=
  dioph_comp ((diophFn_vec _).1 df) ((fun v => v none)::fun i v => g i (v ∘ some)) <| by
    simp
    -- ⊢ (DiophFn fun v => v none) ∧ VectorAllP DiophFn fun i v => g i (v ∘ some)
    exact ⟨proj_dioph none, (vectorAllP_iff_forall _ _).2 fun i =>
          reindex_diophFn _ <| (vectorAllP_iff_forall _ _).1 dg _⟩
#align dioph.dioph_fn_comp Dioph.diophFn_comp

scoped notation:35 x " D∧ " y => Dioph.inter x y

scoped notation:35 x " D∨ " y => Dioph.union x y

scoped notation:30 "D∃" => Dioph.vec_ex1_dioph

scoped prefix:arg "&" => Fin2.ofNat'

theorem proj_dioph_of_nat {n : ℕ} (m : ℕ) [IsLT m n] : DiophFn fun v : Vector3 ℕ n => v &m :=
  proj_dioph &m
#align dioph.proj_dioph_of_nat Dioph.proj_dioph_of_nat

scoped prefix:100 "D&" => Dioph.proj_dioph_of_nat

theorem const_dioph (n : ℕ) : DiophFn (const (α → ℕ) n) :=
  abs_poly_dioph (Poly.const n)
#align dioph.const_dioph Dioph.const_dioph

scoped prefix:100 "D." => Dioph.const_dioph

variable {f g : (α → ℕ) → ℕ} (df : DiophFn f) (dg : DiophFn g)

theorem dioph_comp2 {S : ℕ → ℕ → Prop} (d : Dioph fun v : Vector3 ℕ 2 => S (v &0) (v &1)) :
    Dioph fun v => S (f v) (g v) := dioph_comp d [f, g] ⟨df, dg⟩
#align dioph.dioph_comp2 Dioph.dioph_comp2

theorem diophFn_comp2 {h : ℕ → ℕ → ℕ} (d : DiophFn fun v : Vector3 ℕ 2 => h (v &0) (v &1)) :
    DiophFn fun v => h (f v) (g v) := diophFn_comp d [f, g] ⟨df, dg⟩
#align dioph.dioph_fn_comp2 Dioph.diophFn_comp2

theorem eq_dioph : Dioph fun v => f v = g v :=
  dioph_comp2 df dg <|
    of_no_dummies _ (Poly.proj &0 - Poly.proj &1) fun v => by
      exact Int.ofNat_inj.symm.trans ⟨@sub_eq_zero_of_eq ℤ _ (v &0) (v &1), eq_of_sub_eq_zero⟩
      -- 🎉 no goals
#align dioph.eq_dioph Dioph.eq_dioph

-- mathport name: eq_dioph
scoped infixl:50 " D= " => Dioph.eq_dioph

theorem add_dioph : DiophFn fun v => f v + g v :=
  diophFn_comp2 df dg <| abs_poly_dioph (@Poly.proj (Fin2 2) &0 + @Poly.proj (Fin2 2) &1)
#align dioph.add_dioph Dioph.add_dioph

-- mathport name: add_dioph
scoped infixl:80 " D+ " => Dioph.add_dioph

theorem mul_dioph : DiophFn fun v => f v * g v :=
  diophFn_comp2 df dg <| abs_poly_dioph (@Poly.proj (Fin2 2) &0 * @Poly.proj (Fin2 2) &1)
#align dioph.mul_dioph Dioph.mul_dioph

-- mathport name: mul_dioph
scoped infixl:90 " D* " => Dioph.mul_dioph

theorem le_dioph : Dioph {v | f v ≤ g v} :=
  dioph_comp2 df dg <|
    ext ((D∃) 2 <| D&1 D+ D&0 D= D&2) fun _ => ⟨fun ⟨_, hx⟩ => le.intro hx, le.dest⟩
#align dioph.le_dioph Dioph.le_dioph

scoped infixl:50 " D≤ " => Dioph.le_dioph

theorem lt_dioph : Dioph {v | f v < g v} := df D+ D.1 D≤ dg
#align dioph.lt_dioph Dioph.lt_dioph

scoped infixl:50 " D< " => Dioph.lt_dioph

theorem ne_dioph : Dioph {v | f v ≠ g v} :=
  ext (df D< dg D∨ dg D< df) fun v => by dsimp; exact lt_or_lt_iff_ne (α := ℕ)
                                         -- ⊢ v ∈ {v | f v < g v} ∪ {v | g v < f v} ↔ ¬f v = g v
                                                -- 🎉 no goals
#align dioph.ne_dioph Dioph.ne_dioph

scoped infixl:50 " D≠ " => Dioph.ne_dioph

theorem sub_dioph : DiophFn fun v => f v - g v :=
  diophFn_comp2 df dg <|
    (diophFn_vec _).2 <|
      ext (D&1 D= D&0 D+ D&2 D∨ D&1 D≤ D&2 D∧ D&0 D= D.0) <|
        (vectorAll_iff_forall _).1 fun x y z =>
          show y = x + z ∨ y ≤ z ∧ x = 0 ↔ y - z = x from
            ⟨fun o => by
              rcases o with (ae | ⟨yz, x0⟩)
              -- ⊢ y - z = x
              · rw [ae, add_tsub_cancel_right]
                -- 🎉 no goals
              · rw [x0, tsub_eq_zero_iff_le.mpr yz], by
                -- 🎉 no goals
              rintro rfl
              -- ⊢ y = y - z + z ∨ y ≤ z ∧ y - z = 0
              cases' le_total y z with yz zy
              -- ⊢ y = y - z + z ∨ y ≤ z ∧ y - z = 0
              · exact Or.inr ⟨yz, tsub_eq_zero_iff_le.mpr yz⟩
                -- 🎉 no goals
              · exact Or.inl (tsub_add_cancel_of_le zy).symm⟩
                -- 🎉 no goals
#align dioph.sub_dioph Dioph.sub_dioph

scoped infixl:80 " D- " => Dioph.sub_dioph

theorem dvd_dioph : Dioph fun v => f v ∣ g v :=
  dioph_comp ((D∃) 2 <| D&2 D= D&1 D* D&0) [f, g] ⟨df, dg⟩
#align dioph.dvd_dioph Dioph.dvd_dioph

scoped infixl:50 " D∣ " => Dioph.dvd_dioph

theorem mod_dioph : DiophFn fun v => f v % g v :=
  have : Dioph fun v : Vector3 ℕ 3 => (v &2 = 0 ∨ v &0 < v &2) ∧ ∃ x : ℕ, v &0 + v &2 * x = v &1 :=
    (D&2 D= D.0 D∨ D&0 D< D&2) D∧ (D∃) 3 <| D&1 D+ D&3 D* D&0 D= D&2
  diophFn_comp2 df dg <|
    (diophFn_vec _).2 <|
      ext this <|
        (vectorAll_iff_forall _).1 fun z x y =>
          show ((y = 0 ∨ z < y) ∧ ∃ c, z + y * c = x) ↔ x % y = z from
            ⟨fun ⟨h, c, hc⟩ => by
              rw [← hc]; simp; cases' h with x0 hl; rw [x0, mod_zero]
              -- ⊢ (z + y * c) % y = z
                         -- ⊢ z % y = z
                               -- ⊢ z % y = z
                                                    -- ⊢ z % y = z
              exact mod_eq_of_lt hl, fun e => by
              -- 🎉 no goals
                rw [← e]
                -- ⊢ (y = 0 ∨ x % y < y) ∧ ∃ c, x % y + y * c = x
                exact ⟨or_iff_not_imp_left.2 fun h => mod_lt _ (Nat.pos_of_ne_zero h), x / y,
                  mod_add_div _ _⟩⟩
#align dioph.mod_dioph Dioph.mod_dioph

scoped infixl:80 " D% " => Dioph.mod_dioph

theorem modEq_dioph {h : (α → ℕ) → ℕ} (dh : DiophFn h) : Dioph fun v => f v ≡ g v [MOD h v] :=
  df D% dh D= dg D% dh
#align dioph.modeq_dioph Dioph.modEq_dioph

scoped notation " D≡ " => Dioph.modEq_dioph

theorem div_dioph : DiophFn fun v => f v / g v :=
  have :
    Dioph fun v : Vector3 ℕ 3 =>
      v &2 = 0 ∧ v &0 = 0 ∨ v &0 * v &2 ≤ v &1 ∧ v &1 < (v &0 + 1) * v &2 :=
    (D&2 D= D.0 D∧ D&0 D= D.0) D∨ D&0 D* D&2 D≤ D&1 D∧ D&1 D< (D&0 D+ D.1) D* D&2
  diophFn_comp2 df dg <|
    (diophFn_vec _).2 <|
      ext this <|
        (vectorAll_iff_forall _).1 fun z x y =>
          show y = 0 ∧ z = 0 ∨ z * y ≤ x ∧ x < (z + 1) * y ↔ x / y = z by
            refine Iff.trans ?_ eq_comm
            -- ⊢ y = 0 ∧ z = 0 ∨ z * y ≤ x ∧ x < (z + 1) * y ↔ z = x / y
            exact y.eq_zero_or_pos.elim
              (fun y0 => by
                rw [y0, Nat.div_zero]
                exact ⟨fun o => (o.resolve_right fun ⟨_, h2⟩ => Nat.not_lt_zero _ h2).right,
                  fun z0 => Or.inl ⟨rfl, z0⟩⟩)
              fun ypos =>
                Iff.trans ⟨fun o => o.resolve_left fun ⟨h1, _⟩ => Nat.ne_of_gt ypos h1, Or.inr⟩
                  (le_antisymm_iff.trans <| and_congr (Nat.le_div_iff_mul_le ypos) <|
                    Iff.trans ⟨lt_succ_of_le, le_of_lt_succ⟩ (div_lt_iff_lt_mul ypos)).symm
#align dioph.div_dioph Dioph.div_dioph

-- mathport name: div_dioph
scoped infixl:80 " D/ " => Dioph.div_dioph

open Pell

theorem pell_dioph :
    Dioph fun v : Vector3 ℕ 4 => ∃ h : 1 < v &0, xn h (v &1) = v &2 ∧ yn h (v &1) = v &3 := by
  have proof := D.1 D< D&0 D∧ D&1 D≤ D&3 D∧
      ((D&2 D= D.1 D∧ D&3 D= D.0) D∨
      ((D∃) 4 <| (D∃) 5 <| (D∃) 6 <| (D∃) 7 <| (D∃) 8 <|
      D&7 D* D&7 D- (D&5 D* D&5 D- D.1) D* D&8 D* D&8 D= D.1 D∧
      D&4 D* D&4 D- (D&5 D* D&5 D- D.1) D* D&3 D* D&3 D= D.1 D∧
      D&2 D* D&2 D- (D&0 D* D&0 D- D.1) D* D&1 D* D&1 D= D.1 D∧
      D.1 D< D&0 D∧ (D≡ (D&0) (D.1) (D.4 D* D&8)) D∧ (D≡ (D&0) (D&5) (D&4)) D∧
      D.0 D< D&3 D∧ D&8 D* D&8 D∣ D&3 D∧
      (D≡ (D&2) (D&7) (D&4)) D∧
      (D≡ (D&1) (D&6) (D.4 D* (D&8)))))
  -- Porting note: copying directly `proof` in the proof of the following have fails
  have : Dioph {v : Vector3 ℕ 4 |
    1 < v &0 ∧ v &1 ≤ v &3 ∧
    (v &2 = 1 ∧ v &3 = 0 ∨
    ∃ u w s t b : ℕ,
      v &2 * v &2 - (v &0 * v &0 - 1) * v &3 * v &3 = 1 ∧
      u * u - (v &0 * v &0 - 1) * w * w = 1 ∧
      s * s - (b * b - 1) * t * t = 1 ∧
      1 < b ∧ b ≡ 1 [MOD 4 * v &3] ∧ b ≡ v &0 [MOD u] ∧
      0 < w ∧ v &3 * v &3 ∣ w ∧
      s ≡ v &2 [MOD u] ∧
      t ≡ v &1 [MOD 4 * v &3])} := by
    exact proof
  exact Dioph.ext this fun v => matiyasevic.symm
  -- 🎉 no goals
#align dioph.pell_dioph Dioph.pell_dioph

theorem xn_dioph : DiophPfun fun v : Vector3 ℕ 2 => ⟨1 < v &0, fun h => xn h (v &1)⟩ :=
  have : Dioph fun v : Vector3 ℕ 3 => ∃ y, ∃ h : 1 < v &1, xn h (v &2) = v &0 ∧ yn h (v &2) = y :=
    let D_pell := pell_dioph.reindex_dioph (Fin2 4) [&2, &3, &1, &0]
    (D∃) 3 D_pell
  (diophPfun_vec _).2 <|
    Dioph.ext this fun _ => ⟨fun ⟨_, h, xe, _⟩ => ⟨h, xe⟩, fun ⟨h, xe⟩ => ⟨_, h, xe, rfl⟩⟩
#align dioph.xn_dioph Dioph.xn_dioph

/-- A version of **Matiyasevic's theorem** -/
theorem pow_dioph : DiophFn fun v => f v ^ g v := by
  have proof :=
    let D_pell := pell_dioph.reindex_dioph (Fin2 9) [&4, &8, &1, &0]
    (D&2 D= D.0 D∧ D&0 D= D.1) D∨ (D.0 D< D&2 D∧
    ((D&1 D= D.0 D∧ D&0 D= D.0) D∨ (D.0 D< D&1 D∧
    ((D∃) 3 <| (D∃) 4 <| (D∃) 5 <| (D∃) 6 $ (D∃) 7 <| (D∃) 8 <| D_pell D∧
    (D≡ (D&1) (D&0 D* (D&4 D- D&7) D+ D&6) (D&3)) D∧
    D.2 D* D&4 D* D&7 D= D&3 D+ (D&7 D* D&7 D+ D.1) D∧
    D&6 D< D&3 D∧ D&7 D≤ D&5 D∧ D&8 D≤ D&5 D∧
    D&4 D* D&4 D- ((D&5 D+ D.1) D* (D&5 D+ D.1) D- D.1) D* (D&5 D* D&2) D* (D&5 D* D&2) D= D.1))))
  -- Porting note: copying directly `proof` in the proof of the following have fails
  have : Dioph {v : Vector3 ℕ 3 |
    v &2 = 0 ∧ v &0 = 1 ∨ 0 < v &2 ∧
    (v &1 = 0 ∧ v &0 = 0 ∨ 0 < v &1 ∧
    ∃ w a t z x y : ℕ,
      (∃ a1 : 1 < a, xn a1 (v &2) = x ∧ yn a1 (v &2) = y) ∧
      x ≡ y * (a - v &1) + v &0 [MOD t] ∧
      2 * a * v &1 = t + (v &1 * v &1 + 1) ∧
      v &0 < t ∧ v &1 ≤ w ∧ v &2 ≤ w ∧
      a * a - ((w + 1) * (w + 1) - 1) * (w * z) * (w * z) = 1)} := by
    exact proof
  exact diophFn_comp2 df dg <| (diophFn_vec _).2 <| Dioph.ext this fun v => Iff.symm <|
    eq_pow_of_pell.trans <| or_congr Iff.rfl <| and_congr Iff.rfl <| or_congr Iff.rfl <|
       and_congr Iff.rfl <|
        ⟨fun ⟨w, a, t, z, a1, h⟩ => ⟨w, a, t, z, _, _, ⟨a1, rfl, rfl⟩, h⟩,
        fun ⟨w, a, t, z, _, _, ⟨a1, rfl, rfl⟩, h⟩ => ⟨w, a, t, z, a1, h⟩⟩
#align dioph.pow_dioph Dioph.pow_dioph

end

end Dioph
