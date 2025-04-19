/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fin.Fin2
import Mathlib.Data.PFun
import Mathlib.Data.Vector3
import Mathlib.NumberTheory.PellMatiyasevic

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
* `DiophFn`: a predicate on a function stating that it is Diophantine in the sense that its graph
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

variable {α β : Type*}

/-- A predicate asserting that a function is a multivariate integer polynomial.
  (We are being a bit lazy here by allowing many representations for multiplication,
  rather than only allowing monomials and addition, but the definition is equivalent
  and this is easier to use.) -/
inductive IsPoly : ((α → ℕ) → ℤ) → Prop
  | proj : ∀ i, IsPoly fun x : α → ℕ => x i
  | const : ∀ n : ℤ, IsPoly fun _ : α → ℕ => n
  | sub : ∀ {f g : (α → ℕ) → ℤ}, IsPoly f → IsPoly g → IsPoly fun x => f x - g x
  | mul : ∀ {f g : (α → ℕ) → ℤ}, IsPoly f → IsPoly g → IsPoly fun x => f x * g x

theorem IsPoly.neg {f : (α → ℕ) → ℤ} : IsPoly f → IsPoly (-f) := by
  rw [← zero_sub]; exact (IsPoly.const 0).sub

theorem IsPoly.add {f g : (α → ℕ) → ℤ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly (f + g) := by
  rw [← sub_neg_eq_add]; exact hf.sub hg.neg

/-- The type of multivariate integer polynomials -/
def Poly (α : Type u) := { f : (α → ℕ) → ℤ // IsPoly f }

namespace Poly

section

instance instFunLike : FunLike (Poly α) (α → ℕ) ℤ :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- The underlying function of a `Poly` is a polynomial -/
protected theorem isPoly (f : Poly α) : IsPoly f := f.2

/-- Extensionality for `Poly α` -/
@[ext]
theorem ext {f g : Poly α} : (∀ x, f x = g x) → f = g := DFunLike.ext _ _

/-- The `i`th projection function, `x_i`. -/
def proj (i : α) : Poly α := ⟨_, IsPoly.proj i⟩

@[simp]
theorem proj_apply (i : α) (x) : proj i x = x i := rfl

/-- The constant function with value `n : ℤ`. -/
def const (n : ℤ) : Poly α := ⟨_, IsPoly.const n⟩

@[simp]
theorem const_apply (n) (x : α → ℕ) : const n x = n := rfl

instance : Zero (Poly α) := ⟨const 0⟩

instance : One (Poly α) := ⟨const 1⟩

instance : Neg (Poly α) := ⟨fun f => ⟨-f, f.2.neg⟩⟩

instance : Add (Poly α) := ⟨fun f g => ⟨f + g, f.2.add g.2⟩⟩

instance : Sub (Poly α) := ⟨fun f g => ⟨f - g, f.2.sub g.2⟩⟩

instance : Mul (Poly α) := ⟨fun f g => ⟨f * g, f.2.mul g.2⟩⟩

@[simp]
theorem coe_zero : ⇑(0 : Poly α) = const 0 := rfl

@[simp]
theorem coe_one : ⇑(1 : Poly α) = const 1 := rfl

@[simp]
theorem coe_neg (f : Poly α) : ⇑(-f) = -f := rfl

@[simp]
theorem coe_add (f g : Poly α) : ⇑(f + g) = f + g := rfl

@[simp]
theorem coe_sub (f g : Poly α) : ⇑(f - g) = f - g := rfl

@[simp]
theorem coe_mul (f g : Poly α) : ⇑(f * g) = f * g := rfl

@[simp]
theorem zero_apply (x) : (0 : Poly α) x = 0 := rfl

@[simp]
theorem one_apply (x) : (1 : Poly α) x = 1 := rfl

@[simp]
theorem neg_apply (f : Poly α) (x) : (-f) x = -f x := rfl

@[simp]
theorem add_apply (f g : Poly α) (x : α → ℕ) : (f + g) x = f x + g x := rfl

@[simp]
theorem sub_apply (f g : Poly α) (x : α → ℕ) : (f - g) x = f x - g x := rfl

@[simp]
theorem mul_apply (f g : Poly α) (x : α → ℕ) : (f * g) x = f x * g x := rfl

instance (α : Type*) : Inhabited (Poly α) := ⟨0⟩

instance : AddCommGroup (Poly α) where
  add := ((· + ·) : Poly α → Poly α → Poly α)
  neg := (Neg.neg : Poly α → Poly α)
  sub := Sub.sub
  zero := 0
  nsmul := @nsmulRec _ ⟨(0 : Poly α)⟩ ⟨(· + ·)⟩
  zsmul := @zsmulRec _ ⟨(0 : Poly α)⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec _ ⟨(0 : Poly α)⟩ ⟨(· + ·)⟩)
  add_zero _ := by ext; simp_rw [add_apply, zero_apply, add_zero]
  zero_add _ := by ext; simp_rw [add_apply, zero_apply, zero_add]
  add_comm _ _ := by ext; simp_rw [add_apply, add_comm]
  add_assoc _ _ _ := by ext; simp_rw [add_apply, ← add_assoc]
  neg_add_cancel _ := by ext; simp_rw [add_apply, neg_apply, neg_add_cancel, zero_apply]

instance : AddGroupWithOne (Poly α) :=
  { (inferInstance : AddCommGroup (Poly α)) with
      one := 1
      natCast := fun n => Poly.const n
      intCast := Poly.const }

instance : CommRing (Poly α) where
  __ := (inferInstance : AddCommGroup (Poly α))
  __ := (inferInstance : AddGroupWithOne (Poly α))
  mul := (· * ·)
  npow := @npowRec _ ⟨(1 : Poly α)⟩ ⟨(· * ·)⟩
  mul_zero _ := by ext; rw [mul_apply, zero_apply, mul_zero]
  zero_mul _ := by ext; rw [mul_apply, zero_apply, zero_mul]
  mul_one _ := by ext; rw [mul_apply, one_apply, mul_one]
  one_mul _ := by ext; rw [mul_apply, one_apply, one_mul]
  mul_comm _ _ := by ext; simp_rw [mul_apply, mul_comm]
  mul_assoc _ _ _ := by ext; simp_rw [mul_apply, mul_assoc]
  left_distrib _ _ _ := by ext; simp_rw [add_apply, mul_apply]; apply mul_add
  right_distrib _ _ _ :=  by ext; simp only [add_apply, mul_apply]; apply add_mul

theorem induction {C : Poly α → Prop} (H1 : ∀ i, C (proj i)) (H2 : ∀ n, C (const n))
    (H3 : ∀ f g, C f → C g → C (f - g)) (H4 : ∀ f g, C f → C g → C (f * g)) (f : Poly α) : C f := by
  obtain ⟨f, pf⟩ := f
  induction pf with
  | proj => apply H1
  | const => apply H2
  | sub _ _ ihf ihg => apply H3 _ _ ihf ihg
  | mul _ _ ihf ihg => apply H4 _ _ ihf ihg

/-- The sum of squares of a list of polynomials. This is relevant for
  Diophantine equations, because it means that a list of equations
  can be encoded as a single equation: `x = 0 ∧ y = 0 ∧ z = 0` is
  equivalent to `x^2 + y^2 + z^2 = 0`. -/
def sumsq : List (Poly α) → Poly α
  | [] => 0
  | p::ps => p * p + sumsq ps

theorem sumsq_nonneg (x : α → ℕ) : ∀ l, 0 ≤ sumsq l x
  | [] => le_refl 0
  | p::ps => by
    rw [sumsq]
    exact add_nonneg (mul_self_nonneg _) (sumsq_nonneg _ ps)

theorem sumsq_eq_zero (x) : ∀ l, sumsq l x = 0 ↔ l.Forall fun a : Poly α => a x = 0
  | [] => eq_self_iff_true _
  | p::ps => by
    rw [List.forall_cons, ← sumsq_eq_zero _ ps]; rw [sumsq]
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
        ⟨this, by simpa [this] using h⟩,
      fun ⟨h1, h2⟩ => by rw [add_apply, mul_apply, h1, h2]; rfl⟩

end

/-- Map the index set of variables, replacing `x_i` with `x_(f i)`. -/
def map {α β} (f : α → β) (g : Poly α) : Poly β :=
  ⟨fun v => g <| v ∘ f, Poly.induction (C := fun g => IsPoly (fun v => g (v ∘ f)))
    (fun i => by simpa using IsPoly.proj _) (fun n => by simpa using IsPoly.const _)
    (fun f g pf pg => by simpa using IsPoly.sub pf pg)
    (fun f g pf pg => by simpa using IsPoly.mul pf pg) _⟩

@[simp]
theorem map_apply {α β} (f : α → β) (g : Poly α) (v) : map f g v = g (v ∘ f) := rfl

end Poly

end Polynomials

/-! ### Diophantine sets -/


/-- A set `S ⊆ ℕ^α` is Diophantine if there exists a polynomial on
  `α ⊕ β` such that `v ∈ S` iff there exists `t : ℕ^β` with `p (v, t) = 0`. -/
def Dioph {α : Type u} (S : Set (α → ℕ)) : Prop :=
  ∃ (β : Type u) (p : Poly (α ⊕ β)), ∀ v, S v ↔ ∃ t, p (v ⊗ t) = 0

namespace Dioph

section

variable {α β γ : Type u} {S S' : Set (α → ℕ)}

theorem ext (d : Dioph S) (H : ∀ v, v ∈ S ↔ v ∈ S') : Dioph S' := by rwa [← Set.ext H]

theorem of_no_dummies (S : Set (α → ℕ)) (p : Poly α) (h : ∀ v, S v ↔ p v = 0) : Dioph S :=
  ⟨PEmpty, ⟨p.map inl, fun v => (h v).trans ⟨fun h => ⟨PEmpty.elim, h⟩, fun ⟨_, ht⟩ => ht⟩⟩⟩

theorem inject_dummies_lem (f : β → γ) (g : γ → Option β) (inv : ∀ x, g (f x) = some x)
    (p : Poly (α ⊕ β)) (v : α → ℕ) :
    (∃ t, p (v ⊗ t) = 0) ↔ ∃ t, p.map (inl ⊗ inr ∘ f) (v ⊗ t) = 0 := by
  dsimp; refine ⟨fun t => ?_, fun t => ?_⟩ <;> obtain ⟨t, ht⟩ := t
  · have : (v ⊗ (0 ::ₒ t) ∘ g) ∘ (inl ⊗ inr ∘ f) = v ⊗ t :=
      funext fun s => by rcases s with a | b <;> dsimp [(· ∘ ·)]; try rw [inv]; rfl
    exact ⟨(0 ::ₒ t) ∘ g, by rwa [this]⟩
  · have : v ⊗ t ∘ f = (v ⊗ t) ∘ (inl ⊗ inr ∘ f) := funext fun s => by rcases s with a | b <;> rfl
    exact ⟨t ∘ f, by rwa [this]⟩

theorem inject_dummies (f : β → γ) (g : γ → Option β) (inv : ∀ x, g (f x) = some x)
    (p : Poly (α ⊕ β)) (h : ∀ v, S v ↔ ∃ t, p (v ⊗ t) = 0) :
    ∃ q : Poly (α ⊕ γ), ∀ v, S v ↔ ∃ t, q (v ⊗ t) = 0 :=
  ⟨p.map (inl ⊗ inr ∘ f), fun v => (h v).trans <| inject_dummies_lem f g inv _ _⟩

variable (β) in
theorem reindex_dioph (f : α → β) : Dioph S → Dioph {v | v ∘ f ∈ S}
  | ⟨γ, p, pe⟩ => ⟨γ, p.map (inl ∘ f ⊗ inr), fun v =>
      (pe _).trans <|
        exists_congr fun t =>
          suffices v ∘ f ⊗ t = (v ⊗ t) ∘ (inl ∘ f ⊗ inr) by simp [this]
          funext fun s => by rcases s with a | b <;> rfl⟩

theorem DiophList.forall (l : List (Set <| α → ℕ)) (d : l.Forall Dioph) :
    Dioph {v | l.Forall fun S : Set (α → ℕ) => v ∈ S} := by
  suffices ∃ (β : _) (pl : List (Poly (α ⊕ β))), ∀ v, List.Forall (fun S : Set _ => S v) l ↔
          ∃ t, List.Forall (fun p : Poly (α ⊕ β) => p (v ⊗ t) = 0) pl
    from
    let ⟨β, pl, h⟩ := this
    ⟨β, Poly.sumsq pl, fun v => (h v).trans <| exists_congr fun t => (Poly.sumsq_eq_zero _ _).symm⟩
  induction l with | nil => exact ⟨ULift Empty, [], fun _ => by simp⟩ | cons S l IH =>
  simp? at d says simp only [List.forall_cons] at d
  exact
    let ⟨⟨β, p, pe⟩, dl⟩ := d
    let ⟨γ, pl, ple⟩ := IH dl
    ⟨β ⊕ γ, p.map (inl ⊗ inr ∘ inl)::pl.map fun q => q.map (inl ⊗ inr ∘ inr),
      fun v => by
      simpa using
        Iff.trans (and_congr (pe v) (ple v))
          ⟨fun ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ =>
            ⟨m ⊗ n, by
              rw [show (v ⊗ m ⊗ n) ∘ (inl ⊗ inr ∘ inl) = v ⊗ m from
                    funext fun s => by rcases s with a | b <;> rfl]; exact hm, by
              refine List.Forall.imp (fun q hq => ?_) hn; dsimp [Function.comp_def]
              rw [show
                    (fun x : α ⊕ γ => (v ⊗ m ⊗ n) ((inl ⊗ fun x : γ => inr (inr x)) x)) = v ⊗ n
                    from funext fun s => by rcases s with a | b <;> rfl]; exact hq⟩,
            fun ⟨t, hl, hr⟩ =>
            ⟨⟨t ∘ inl, by
                rwa [show (v ⊗ t) ∘ (inl ⊗ inr ∘ inl) = v ⊗ t ∘ inl from
                    funext fun s => by rcases s with a | b <;> rfl] at hl⟩,
              ⟨t ∘ inr, by
                refine List.Forall.imp (fun q hq => ?_) hr; dsimp [Function.comp_def] at hq
                rwa [show
                    (fun x : α ⊕ γ => (v ⊗ t) ((inl ⊗ fun x : γ => inr (inr x)) x)) =
                      v ⊗ t ∘ inr
                    from funext fun s => by rcases s with a | b <;> rfl] at hq ⟩⟩⟩⟩

/-- Diophantine sets are closed under intersection. -/
theorem inter (d : Dioph S) (d' : Dioph S') : Dioph (S ∩ S') := DiophList.forall [S, S'] ⟨d, d'⟩

/-- Diophantine sets are closed under union. -/
theorem union : ∀ (_ : Dioph S) (_ : Dioph S'), Dioph (S ∪ S')
  | ⟨β, p, pe⟩, ⟨γ, q, qe⟩ =>
    ⟨β ⊕ γ, p.map (inl ⊗ inr ∘ inl) * q.map (inl ⊗ inr ∘ inr), fun v => by
      refine
        Iff.trans (or_congr ((pe v).trans ?_) ((qe v).trans ?_))
          (exists_or.symm.trans
            (exists_congr fun t =>
              (@mul_eq_zero _ _ _ (p ((v ⊗ t) ∘ (inl ⊗ inr ∘ inl)))
                  (q ((v ⊗ t) ∘ (inl ⊗ inr ∘ inr)))).symm))
      · -- Porting note: putting everything on the same line fails
        refine inject_dummies_lem _ (some ⊗ fun _ => none) ?_ _ _
        exact fun _ => by simp only [elim_inl]
      · -- Porting note: putting everything on the same line fails
        refine inject_dummies_lem _ ((fun _ => none) ⊗ some) ?_ _ _
        exact fun _ => by simp only [elim_inr]⟩

/-- A partial function is Diophantine if its graph is Diophantine. -/
def DiophPFun (f : (α → ℕ) →. ℕ) : Prop :=
  Dioph {v : Option α → ℕ | f.graph (v ∘ some, v none)}

/-- A function is Diophantine if its graph is Diophantine. -/
def DiophFn (f : (α → ℕ) → ℕ) : Prop :=
  Dioph {v : Option α → ℕ | f (v ∘ some) = v none}

theorem reindex_diophFn {f : (α → ℕ) → ℕ} (g : α → β) (d : DiophFn f) :
    DiophFn fun v => f (v ∘ g) := by convert reindex_dioph (Option β) (Option.map g) d

theorem ex_dioph {S : Set (α ⊕ β → ℕ)} : Dioph S → Dioph {v | ∃ x, v ⊗ x ∈ S}
  | ⟨γ, p, pe⟩ =>
    ⟨β ⊕ γ, p.map ((inl ⊗ inr ∘ inl) ⊗ inr ∘ inr), fun v =>
      ⟨fun ⟨x, hx⟩ =>
        let ⟨t, ht⟩ := (pe _).1 hx
        ⟨x ⊗ t, by
          simp only [Poly.map_apply]
          rw [show (v ⊗ x ⊗ t) ∘ ((inl ⊗ inr ∘ inl) ⊗ inr ∘ inr) = (v ⊗ x) ⊗ t from
            funext fun s => by rcases s with a | b <;> try { cases a <;> rfl }; rfl]
          exact ht⟩,
        fun ⟨t, ht⟩ =>
        ⟨t ∘ inl,
          (pe _).2
            ⟨t ∘ inr, by
              simp only [Poly.map_apply] at ht
              rwa [show (v ⊗ t) ∘ ((inl ⊗ inr ∘ inl) ⊗ inr ∘ inr) = (v ⊗ t ∘ inl) ⊗ t ∘ inr from
                funext fun s => by rcases s with a | b <;> try { cases a <;> rfl }; rfl] at ht⟩⟩⟩⟩

theorem ex1_dioph {S : Set (Option α → ℕ)} : Dioph S → Dioph {v | ∃ x, x ::ₒ v ∈ S}
  | ⟨β, p, pe⟩ =>
    ⟨Option β, p.map (inr none ::ₒ inl ⊗ inr ∘ some), fun v =>
      ⟨fun ⟨x, hx⟩ =>
        let ⟨t, ht⟩ := (pe _).1 hx
        ⟨x ::ₒ t, by
          simp only [Poly.map_apply]
          rw [show (v ⊗ x ::ₒ t) ∘ (inr none ::ₒ inl ⊗ inr ∘ some) = x ::ₒ v ⊗ t from
            funext fun s => by rcases s with a | b <;> try { cases a <;> rfl}; rfl]
          exact ht⟩,
        fun ⟨t, ht⟩ =>
        ⟨t none,
          (pe _).2
            ⟨t ∘ some, by
              simp only [Poly.map_apply] at ht
              rwa [show (v ⊗ t) ∘ (inr none ::ₒ inl ⊗ inr ∘ some) = t none ::ₒ v ⊗ t ∘ some from
                funext fun s => by rcases s with a | b <;> try { cases a <;> rfl }; rfl] at ht ⟩⟩⟩⟩

theorem dom_dioph {f : (α → ℕ) →. ℕ} (d : DiophPFun f) : Dioph f.Dom :=
  cast (congr_arg Dioph <| Set.ext fun _ => (PFun.dom_iff_graph _ _).symm) (ex1_dioph d)

theorem diophFn_iff_pFun (f : (α → ℕ) → ℕ) : DiophFn f = @DiophPFun α f := by
  refine congr_arg Dioph (Set.ext fun v => ?_); exact PFun.lift_graph.symm

theorem abs_poly_dioph (p : Poly α) : DiophFn fun v => (p v).natAbs :=
  of_no_dummies _ ((p.map some - Poly.proj none) * (p.map some + Poly.proj none))
    fun v => (by dsimp; exact Int.natAbs_eq_iff_mul_eq_zero)

theorem proj_dioph (i : α) : DiophFn fun v => v i :=
  abs_poly_dioph (Poly.proj i)

theorem diophPFun_comp1 {S : Set (Option α → ℕ)} (d : Dioph S) {f} (df : DiophPFun f) :
    Dioph {v : α → ℕ | ∃ h : f.Dom v, f.fn v h ::ₒ v ∈ S} :=
  ext (ex1_dioph (d.inter df)) fun v =>
    ⟨fun ⟨x, hS, (h : Exists _)⟩ => by
      rw [show (x ::ₒ v) ∘ some = v from funext fun s => rfl] at h
      obtain ⟨hf, h⟩ := h; refine ⟨hf, ?_⟩; rw [PFun.fn, h]; exact hS,
    fun ⟨x, hS⟩ =>
      ⟨f.fn v x, hS, show Exists _ by
        rw [show (f.fn v x ::ₒ v) ∘ some = v from funext fun s => rfl]; exact ⟨x, rfl⟩⟩⟩

theorem diophFn_comp1 {S : Set (Option α → ℕ)} (d : Dioph S) {f : (α → ℕ) → ℕ} (df : DiophFn f) :
    Dioph {v | f v ::ₒ v ∈ S} :=
  ext (diophPFun_comp1 d <| cast (diophFn_iff_pFun f) df)
    fun _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨trivial, h⟩⟩

end

section

variable {α : Type} {n : ℕ}

open Vector3

open scoped Vector3

theorem diophFn_vec_comp1 {S : Set (Vector3 ℕ (succ n))} (d : Dioph S) {f : Vector3 ℕ n → ℕ}
    (df : DiophFn f) : Dioph {v : Vector3 ℕ n | (f v::v) ∈ S} :=
  Dioph.ext (diophFn_comp1 (reindex_dioph _ (none::some) d) df) (fun v => by
    dsimp
    -- Porting note: `congr` used to be enough here
    suffices ((f v ::ₒ v) ∘ none :: some) = f v :: v by rw [this]; rfl
    ext x; cases x <;> rfl)

/-- Deleting the first component preserves the Diophantine property. -/
theorem vec_ex1_dioph (n) {S : Set (Vector3 ℕ (succ n))} (d : Dioph S) :
    Dioph {v : Fin2 n → ℕ | ∃ x, (x::v) ∈ S} :=
  ext (ex1_dioph <| reindex_dioph _ (none::some) d) fun v =>
    exists_congr fun x => by
      dsimp
      rw [show Option.elim' x v ∘ cons none some = x::v from
          funext fun s => by rcases s with a | b <;> rfl]

theorem diophFn_vec (f : Vector3 ℕ n → ℕ) : DiophFn f ↔ Dioph {v | f (v ∘ fs) = v fz} :=
  ⟨reindex_dioph _ (fz ::ₒ fs), reindex_dioph _ (none::some)⟩

theorem diophPFun_vec (f : Vector3 ℕ n →. ℕ) : DiophPFun f ↔ Dioph {v | f.graph (v ∘ fs, v fz)} :=
  ⟨reindex_dioph _ (fz ::ₒ fs), reindex_dioph _ (none::some)⟩

theorem diophFn_compn :
    ∀ {n} {S : Set (α ⊕ (Fin2 n) → ℕ)} (_ : Dioph S) {f : Vector3 ((α → ℕ) → ℕ) n}
      (_ : VectorAllP DiophFn f), Dioph {v : α → ℕ | (v ⊗ fun i => f i v) ∈ S}
  | 0, S, d, f => fun _ =>
    ext (reindex_dioph _ (id ⊗ Fin2.elim0) d) fun v => by
      dsimp
      -- Porting note: `congr` used to be enough here
      suffices v ∘ (id ⊗ elim0) = v ⊗ fun i ↦ f i v by rw [this]
      ext x; obtain _ | _ | _ := x; rfl
  | succ n, S, d, f =>
    f.consElim fun f fl => by
        simp only [vectorAllP_cons, and_imp]
        exact fun df dfl =>
          have : Dioph {v | (v ∘ inl ⊗ f (v ∘ inl)::v ∘ inr) ∈ S} :=
            ext (diophFn_comp1 (reindex_dioph _ (some ∘ inl ⊗ none::some ∘ inr) d) <|
                reindex_diophFn inl df)
              fun v => by
                dsimp
                -- Porting note: `congr` used to be enough here
                suffices (f (v ∘ inl) ::ₒ v) ∘ (some ∘ inl ⊗ none :: some ∘ inr) =
                    v ∘ inl ⊗ f (v ∘ inl) :: v ∘ inr by rw [this]
                ext x; obtain _ | _ | _ := x <;> rfl
          have : Dioph {v | (v ⊗ f v::fun i : Fin2 n => fl i v) ∈ S} :=
            @diophFn_compn n (fun v => S (v ∘ inl ⊗ f (v ∘ inl)::v ∘ inr)) this _ dfl
          ext this fun v => by
            dsimp
            -- Porting note: `congr` used to be enough here
            suffices (v ⊗ f v :: fun i ↦ fl i v) = v ⊗ fun i ↦ (f :: fl) i v by rw [this]
            ext x; obtain _ | _ | _ := x <;> rfl

theorem dioph_comp {S : Set (Vector3 ℕ n)} (d : Dioph S) (f : Vector3 ((α → ℕ) → ℕ) n)
    (df : VectorAllP DiophFn f) : Dioph {v | (fun i => f i v) ∈ S} :=
  diophFn_compn (reindex_dioph _ inr d) df

theorem diophFn_comp {f : Vector3 ℕ n → ℕ} (df : DiophFn f) (g : Vector3 ((α → ℕ) → ℕ) n)
    (dg : VectorAllP DiophFn g) : DiophFn fun v => f fun i => g i v :=
  dioph_comp ((diophFn_vec _).1 df) ((fun v => v none)::fun i v => g i (v ∘ some)) <| by
    simp only [vectorAllP_cons]
    exact ⟨proj_dioph none, (vectorAllP_iff_forall _ _).2 fun i =>
          reindex_diophFn _ <| (vectorAllP_iff_forall _ _).1 dg _⟩

@[inherit_doc]
scoped notation:35 x " D∧ " y => Dioph.inter x y

@[inherit_doc]
scoped notation:35 x " D∨ " y => Dioph.union x y

@[inherit_doc]
scoped notation:30 "D∃" => Dioph.vec_ex1_dioph

/-- Local abbreviation for `Fin2.ofNat'` -/
scoped prefix:arg "&" => Fin2.ofNat'

theorem proj_dioph_of_nat {n : ℕ} (m : ℕ) [IsLT m n] : DiophFn fun v : Vector3 ℕ n => v &m :=
  proj_dioph &m

/-- Projection preserves Diophantine functions. -/
scoped prefix:100 "D&" => Dioph.proj_dioph_of_nat

theorem const_dioph (n : ℕ) : DiophFn (const (α → ℕ) n) :=
  abs_poly_dioph (Poly.const n)

/-- The constant function is Diophantine. -/
scoped prefix:100 "D." => Dioph.const_dioph

section
variable {f g : (α → ℕ) → ℕ} (df : DiophFn f) (dg : DiophFn g)
include df dg

theorem dioph_comp2 {S : ℕ → ℕ → Prop} (d : Dioph fun v : Vector3 ℕ 2 => S (v &0) (v &1)) :
    Dioph fun v => S (f v) (g v) := dioph_comp d [f, g] ⟨df, dg⟩

theorem diophFn_comp2 {h : ℕ → ℕ → ℕ} (d : DiophFn fun v : Vector3 ℕ 2 => h (v &0) (v &1)) :
    DiophFn fun v => h (f v) (g v) := diophFn_comp d [f, g] ⟨df, dg⟩

/-- The set of places where two Diophantine functions are equal is Diophantine. -/
theorem eq_dioph : Dioph fun v => f v = g v :=
  dioph_comp2 df dg <|
    of_no_dummies _ (Poly.proj &0 - Poly.proj &1) fun v => by
      exact Int.ofNat_inj.symm.trans ⟨@sub_eq_zero_of_eq ℤ _ (v &0) (v &1), eq_of_sub_eq_zero⟩

@[inherit_doc]
scoped infixl:50 " D= " => Dioph.eq_dioph

/-- Diophantine functions are closed under addition. -/
theorem add_dioph : DiophFn fun v => f v + g v :=
  diophFn_comp2 df dg <| abs_poly_dioph (@Poly.proj (Fin2 2) &0 + @Poly.proj (Fin2 2) &1)

@[inherit_doc]
scoped infixl:80 " D+ " => Dioph.add_dioph

/-- Diophantine functions are closed under multiplication. -/
theorem mul_dioph : DiophFn fun v => f v * g v :=
  diophFn_comp2 df dg <| abs_poly_dioph (@Poly.proj (Fin2 2) &0 * @Poly.proj (Fin2 2) &1)

@[inherit_doc]
scoped infixl:90 " D* " => Dioph.mul_dioph

/-- The set of places where one Diophantine function is at most another is Diophantine. -/
theorem le_dioph : Dioph {v | f v ≤ g v} :=
  dioph_comp2 df dg <|
    ext ((D∃) 2 <| D&1 D+ D&0 D= D&2) fun _ => ⟨fun ⟨_, hx⟩ => le.intro hx, le.dest⟩

@[inherit_doc]
scoped infixl:50 " D≤ " => Dioph.le_dioph

/-- The set of places where one Diophantine function is less than another is Diophantine. -/
theorem lt_dioph : Dioph {v | f v < g v} := df D+ D.1 D≤ dg

@[inherit_doc]
scoped infixl:50 " D< " => Dioph.lt_dioph

/-- The set of places where two Diophantine functions are unequal is Diophantine. -/
theorem ne_dioph : Dioph {v | f v ≠ g v} :=
  ext (df D< dg D∨ dg D< df) fun v => by dsimp; exact lt_or_lt_iff_ne (α := ℕ)

@[inherit_doc]
scoped infixl:50 " D≠ " => Dioph.ne_dioph

/-- Diophantine functions are closed under subtraction. -/
theorem sub_dioph : DiophFn fun v => f v - g v :=
  diophFn_comp2 df dg <|
    (diophFn_vec _).2 <|
      ext (D&1 D= D&0 D+ D&2 D∨ D&1 D≤ D&2 D∧ D&0 D= D.0) <|
        (vectorAll_iff_forall _).1 fun x y z =>
          show y = x + z ∨ y ≤ z ∧ x = 0 ↔ y - z = x from
            ⟨fun o => by
              rcases o with (ae | ⟨yz, x0⟩)
              · rw [ae, add_tsub_cancel_right]
              · rw [x0, tsub_eq_zero_iff_le.mpr yz], by
              rintro rfl
              rcases le_total y z with yz | zy
              · exact Or.inr ⟨yz, tsub_eq_zero_iff_le.mpr yz⟩
              · exact Or.inl (tsub_add_cancel_of_le zy).symm⟩

@[inherit_doc]
scoped infixl:80 " D- " => Dioph.sub_dioph

/-- The set of places where one Diophantine function divides another is Diophantine. -/
theorem dvd_dioph : Dioph fun v => f v ∣ g v :=
  dioph_comp ((D∃) 2 <| D&2 D= D&1 D* D&0) [f, g] ⟨df, dg⟩

@[inherit_doc]
scoped infixl:50 " D∣ " => Dioph.dvd_dioph

/-- Diophantine functions are closed under the modulo operation. -/
theorem mod_dioph : DiophFn fun v => f v % g v :=
  have : Dioph fun v : Vector3 ℕ 3 => (v &2 = 0 ∨ v &0 < v &2) ∧ ∃ x : ℕ, v &0 + v &2 * x = v &1 :=
    (D&2 D= D.0 D∨ D&0 D< D&2) D∧ (D∃) 3 <| D&1 D+ D&3 D* D&0 D= D&2
  diophFn_comp2 df dg <|
    (diophFn_vec _).2 <|
      ext this <|
        (vectorAll_iff_forall _).1 fun z x y =>
          show ((y = 0 ∨ z < y) ∧ ∃ c, z + y * c = x) ↔ x % y = z from
            ⟨fun ⟨h, c, hc⟩ => by
              rw [← hc]; simp only [add_mul_mod_self_left]; rcases h with x0 | hl
              · rw [x0, mod_zero]
              exact mod_eq_of_lt hl, fun e => by
                rw [← e]
                exact ⟨or_iff_not_imp_left.2 fun h => mod_lt _ (Nat.pos_of_ne_zero h), x / y,
                  mod_add_div _ _⟩⟩

@[inherit_doc]
scoped infixl:80 " D% " => Dioph.mod_dioph

/-- The set of places where two Diophantine functions are congruent modulo a third
is Diophantine. -/
theorem modEq_dioph {h : (α → ℕ) → ℕ} (dh : DiophFn h) : Dioph fun v => f v ≡ g v [MOD h v] :=
  df D% dh D= dg D% dh

@[inherit_doc]
scoped notation " D≡ " => Dioph.modEq_dioph

/-- Diophantine functions are closed under integer division. -/
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
            exact y.eq_zero_or_pos.elim
              (fun y0 => by
                rw [y0, Nat.div_zero]
                exact ⟨fun o => (o.resolve_right fun ⟨_, h2⟩ => Nat.not_lt_zero _ h2).right,
                  fun z0 => Or.inl ⟨rfl, z0⟩⟩)
              fun ypos =>
                Iff.trans ⟨fun o => o.resolve_left fun ⟨h1, _⟩ => Nat.ne_of_gt ypos h1, Or.inr⟩
                  (le_antisymm_iff.trans <| and_congr (Nat.le_div_iff_mul_le ypos) <|
                    Iff.trans ⟨lt_succ_of_le, le_of_lt_succ⟩ (div_lt_iff_lt_mul ypos)).symm

end

@[inherit_doc]
scoped infixl:80 " D/ " => Dioph.div_dioph

open Pell

theorem pell_dioph :
    Dioph fun v : Vector3 ℕ 4 => ∃ h : 1 < v &0, xn h (v &1) = v &2 ∧ yn h (v &1) = v &3 := by
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
      t ≡ v &1 [MOD 4 * v &3])} :=
  (D.1 D< D&0 D∧ D&1 D≤ D&3 D∧
    ((D&2 D= D.1 D∧ D&3 D= D.0) D∨
    ((D∃) 4 <| (D∃) 5 <| (D∃) 6 <| (D∃) 7 <| (D∃) 8 <|
    D&7 D* D&7 D- (D&5 D* D&5 D- D.1) D* D&8 D* D&8 D= D.1 D∧
    D&4 D* D&4 D- (D&5 D* D&5 D- D.1) D* D&3 D* D&3 D= D.1 D∧
    D&2 D* D&2 D- (D&0 D* D&0 D- D.1) D* D&1 D* D&1 D= D.1 D∧
    D.1 D< D&0 D∧ (D≡ (D&0) (D.1) (D.4 D* D&8)) D∧ (D≡ (D&0) (D&5) (D&4)) D∧
    D.0 D< D&3 D∧ D&8 D* D&8 D∣ D&3 D∧
    (D≡ (D&2) (D&7) (D&4)) D∧
    (D≡ (D&1) (D&6) (D.4 D* (D&8))))) :)
  exact Dioph.ext this fun v => matiyasevic.symm

theorem xn_dioph : DiophPFun fun v : Vector3 ℕ 2 => ⟨1 < v &0, fun h => xn h (v &1)⟩ :=
  have : Dioph fun v : Vector3 ℕ 3 => ∃ y, ∃ h : 1 < v &1, xn h (v &2) = v &0 ∧ yn h (v &2) = y :=
    let D_pell := pell_dioph.reindex_dioph (Fin2 4) [&2, &3, &1, &0]
    (D∃) 3 D_pell
  (diophPFun_vec _).2 <|
    Dioph.ext this fun _ => ⟨fun ⟨_, h, xe, _⟩ => ⟨h, xe⟩, fun ⟨h, xe⟩ => ⟨_, h, xe, rfl⟩⟩

/-- A version of **Matiyasevic's theorem** -/
theorem pow_dioph {f g : (α → ℕ) → ℕ} (df : DiophFn f) (dg : DiophFn g) :
    DiophFn fun v => f v ^ g v := by
  have : Dioph {v : Vector3 ℕ 3 |
    v &2 = 0 ∧ v &0 = 1 ∨ 0 < v &2 ∧
    (v &1 = 0 ∧ v &0 = 0 ∨ 0 < v &1 ∧
    ∃ w a t z x y : ℕ,
      (∃ a1 : 1 < a, xn a1 (v &2) = x ∧ yn a1 (v &2) = y) ∧
      x ≡ y * (a - v &1) + v &0 [MOD t] ∧
      2 * a * v &1 = t + (v &1 * v &1 + 1) ∧
      v &0 < t ∧ v &1 ≤ w ∧ v &2 ≤ w ∧
      a * a - ((w + 1) * (w + 1) - 1) * (w * z) * (w * z) = 1)} :=
  (D&2 D= D.0 D∧ D&0 D= D.1) D∨ (D.0 D< D&2 D∧
    ((D&1 D= D.0 D∧ D&0 D= D.0) D∨ (D.0 D< D&1 D∧
    ((D∃) 3 <| (D∃) 4 <| (D∃) 5 <| (D∃) 6 <| (D∃) 7 <| (D∃) 8 <|
    pell_dioph.reindex_dioph (Fin2 9) [&4, &8, &1, &0] D∧
    (D≡ (D&1) (D&0 D* (D&4 D- D&7) D+ D&6) (D&3)) D∧
    D.2 D* D&4 D* D&7 D= D&3 D+ (D&7 D* D&7 D+ D.1) D∧
    D&6 D< D&3 D∧ D&7 D≤ D&5 D∧ D&8 D≤ D&5 D∧
    D&4 D* D&4 D- ((D&5 D+ D.1) D* (D&5 D+ D.1) D- D.1) D* (D&5 D* D&2) D* (D&5 D* D&2) D= D.1))) :)
  exact diophFn_comp2 df dg <| (diophFn_vec _).2 <| Dioph.ext this fun v => Iff.symm <|
    eq_pow_of_pell.trans <| or_congr Iff.rfl <| and_congr Iff.rfl <| or_congr Iff.rfl <|
       and_congr Iff.rfl <|
        ⟨fun ⟨w, a, t, z, a1, h⟩ => ⟨w, a, t, z, _, _, ⟨a1, rfl, rfl⟩, h⟩,
        fun ⟨w, a, t, z, _, _, ⟨a1, rfl, rfl⟩, h⟩ => ⟨w, a, t, z, a1, h⟩⟩

end

end Dioph
