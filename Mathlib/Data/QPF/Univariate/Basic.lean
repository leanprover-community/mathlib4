/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Data.PFunctor.Univariate.M

#align_import data.qpf.univariate.basic from "leanprover-community/mathlib"@"14b69e9f3c16630440a2cbd46f1ddad0d561dee7"

/-!

# Quotients of Polynomial Functors

We assume the following:

`P`   : a polynomial functor
`W`   : its W-type
`M`   : its M-type
`F`   : a functor

We define:

`q`   : `Qpf` data, representing `F` as a quotient of `P`

The main goal is to construct:

`Fix`   : the initial algebra with structure map `F Fix → Fix`.
`Cofix` : the final coalgebra with structure map `Cofix → F Cofix`

We also show that the composition of qpfs is a qpf, and that the quotient of a qpf
is a qpf.

The present theory focuses on the univariate case for qpfs

## References

* [Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial
  Functors*][avigad-carneiro-hudon2019]

-/


universe u

/-- Quotients of polynomial functors.

Roughly speaking, saying that `F` is a quotient of a polynomial functor means that for each `α`,
elements of `F α` are represented by pairs `⟨a, f⟩`, where `a` is the shape of the object and
`f` indexes the relevant elements of `α`, in a suitably natural manner.
-/
class Qpf (F : Type u → Type u) [Functor F] where
  P : PFunctor.{u}
  abs : ∀ {α}, P.Obj α → F α
  repr : ∀ {α}, F α → P.Obj α
  abs_repr : ∀ {α} (x : F α), abs (repr x) = x
  abs_map : ∀ {α β} (f : α → β) (p : P.Obj α), abs (f <$> p) = f <$> abs p
#align qpf Qpf

namespace Qpf

variable {F : Type u → Type u} [Functor F] [q : Qpf F]

open Functor (Liftp Liftr)

/-
Show that every qpf is a lawful functor.

Note: every functor has a field, `map_const`, and `lawfulFunctor` has the defining
characterization. We can only propagate the assumption.
-/
theorem id_map {α : Type _} (x : F α) : id <$> x = x := by
  rw [← abs_repr x]
  -- ⊢ id <$> abs (repr x) = abs (repr x)
  cases' repr x with a f
  -- ⊢ id <$> abs { fst := a, snd := f } = abs { fst := a, snd := f }
  rw [← abs_map]
  -- ⊢ abs (id <$> { fst := a, snd := f }) = abs { fst := a, snd := f }
  rfl
  -- 🎉 no goals
#align qpf.id_map Qpf.id_map

theorem comp_map {α β γ : Type _} (f : α → β) (g : β → γ) (x : F α) :
    (g ∘ f) <$> x = g <$> f <$> x := by
  rw [← abs_repr x]
  -- ⊢ (g ∘ f) <$> abs (repr x) = g <$> f <$> abs (repr x)
  cases' repr x with a f
  -- ⊢ (g ∘ f✝) <$> abs { fst := a, snd := f } = g <$> f✝ <$> abs { fst := a, snd : …
  rw [← abs_map, ← abs_map, ← abs_map]
  -- ⊢ abs ((g ∘ f✝) <$> { fst := a, snd := f }) = abs (g <$> f✝ <$> { fst := a, sn …
  rfl
  -- 🎉 no goals
#align qpf.comp_map Qpf.comp_map

theorem lawfulFunctor
    (h : ∀ α β : Type u, @Functor.mapConst F _ α _ = Functor.map ∘ Function.const β) :
    LawfulFunctor F :=
  { map_const := @h
    id_map := @id_map F _ _
    comp_map := @comp_map F _ _ }
#align qpf.is_lawful_functor Qpf.lawfulFunctor

/-
Lifting predicates and relations
-/
section

open Functor

theorem liftp_iff {α : Type u} (p : α → Prop) (x : F α) :
    Liftp p x ↔ ∃ a f, x = abs ⟨a, f⟩ ∧ ∀ i, p (f i) := by
  constructor
  -- ⊢ Liftp p x → ∃ a f, x = abs { fst := a, snd := f } ∧ ∀ (i : PFunctor.B (P F)  …
  · rintro ⟨y, hy⟩
    -- ⊢ ∃ a f, x = abs { fst := a, snd := f } ∧ ∀ (i : PFunctor.B (P F) a), p (f i)
    cases' h : repr y with a f
    -- ⊢ ∃ a f, x = abs { fst := a, snd := f } ∧ ∀ (i : PFunctor.B (P F) a), p (f i)
    use a, fun i => (f i).val
    -- ⊢ x = abs { fst := a, snd := fun i => ↑(f i) } ∧ ∀ (i : PFunctor.B (P F) a), p …
    constructor
    -- ⊢ x = abs { fst := a, snd := fun i => ↑(f i) }
    · rw [← hy, ← abs_repr y, h, ← abs_map]
      -- ⊢ abs (Subtype.val <$> { fst := a, snd := f }) = abs { fst := a, snd := fun i  …
      rfl
      -- 🎉 no goals
    intro i
    -- ⊢ p ↑(f i)
    apply (f i).property
    -- 🎉 no goals
  rintro ⟨a, f, h₀, h₁⟩
  -- ⊢ Liftp p x
  use abs ⟨a, fun i => ⟨f i, h₁ i⟩⟩
  -- ⊢ Subtype.val <$> abs { fst := a, snd := fun i => { val := f i, property := (_ …
  rw [← abs_map, h₀]; rfl
  -- ⊢ abs (Subtype.val <$> { fst := a, snd := fun i => { val := f i, property := ( …
                      -- 🎉 no goals
#align qpf.liftp_iff Qpf.liftp_iff

theorem liftp_iff' {α : Type u} (p : α → Prop) (x : F α) :
    Liftp p x ↔ ∃ u : q.P.Obj α, abs u = x ∧ ∀ i, p (u.snd i) := by
  constructor
  -- ⊢ Liftp p x → ∃ u, abs u = x ∧ ∀ (i : PFunctor.B (P F) u.fst), p (Sigma.snd u i)
  · rintro ⟨y, hy⟩
    -- ⊢ ∃ u, abs u = x ∧ ∀ (i : PFunctor.B (P F) u.fst), p (Sigma.snd u i)
    cases' h : repr y with a f
    -- ⊢ ∃ u, abs u = x ∧ ∀ (i : PFunctor.B (P F) u.fst), p (Sigma.snd u i)
    use ⟨a, fun i => (f i).val⟩
    -- ⊢ abs { fst := a, snd := fun i => ↑(f i) } = x ∧ ∀ (i : PFunctor.B (P F) { fst …
    dsimp
    -- ⊢ abs { fst := a, snd := fun i => ↑(f i) } = x ∧ ∀ (i : PFunctor.B (P F) a), p …
    constructor
    -- ⊢ abs { fst := a, snd := fun i => ↑(f i) } = x
    · rw [← hy, ← abs_repr y, h, ← abs_map]
      -- ⊢ abs { fst := a, snd := fun i => ↑(f i) } = abs (Subtype.val <$> { fst := a,  …
      rfl
      -- 🎉 no goals
    intro i
    -- ⊢ p ↑(f i)
    apply (f i).property
    -- 🎉 no goals
  rintro ⟨⟨a, f⟩, h₀, h₁⟩; dsimp at *
  -- ⊢ Liftp p x
                           -- ⊢ Liftp p x
  use abs ⟨a, fun i => ⟨f i, h₁ i⟩⟩
  -- ⊢ Subtype.val <$> abs { fst := a, snd := fun i => { val := f i, property := (_ …
  rw [← abs_map, ← h₀]; rfl
  -- ⊢ abs (Subtype.val <$> { fst := a, snd := fun i => { val := f i, property := ( …
                        -- 🎉 no goals
#align qpf.liftp_iff' Qpf.liftp_iff'

theorem liftr_iff {α : Type u} (r : α → α → Prop) (x y : F α) :
    Liftr r x y ↔ ∃ a f₀ f₁, x = abs ⟨a, f₀⟩ ∧ y = abs ⟨a, f₁⟩ ∧ ∀ i, r (f₀ i) (f₁ i) := by
  constructor
  -- ⊢ Liftr r x y → ∃ a f₀ f₁, x = abs { fst := a, snd := f₀ } ∧ y = abs { fst :=  …
  · rintro ⟨u, xeq, yeq⟩
    -- ⊢ ∃ a f₀ f₁, x = abs { fst := a, snd := f₀ } ∧ y = abs { fst := a, snd := f₁ } …
    cases' h : repr u with a f
    -- ⊢ ∃ a f₀ f₁, x = abs { fst := a, snd := f₀ } ∧ y = abs { fst := a, snd := f₁ } …
    use a, fun i => (f i).val.fst, fun i => (f i).val.snd
    -- ⊢ x = abs { fst := a, snd := fun i => (↑(f i)).fst } ∧ y = abs { fst := a, snd …
    constructor
    -- ⊢ x = abs { fst := a, snd := fun i => (↑(f i)).fst }
    · rw [← xeq, ← abs_repr u, h, ← abs_map]
      -- ⊢ abs ((fun t => (↑t).fst) <$> { fst := a, snd := f }) = abs { fst := a, snd : …
      rfl
      -- 🎉 no goals
    constructor
    -- ⊢ y = abs { fst := a, snd := fun i => (↑(f i)).snd }
    · rw [← yeq, ← abs_repr u, h, ← abs_map]
      -- ⊢ abs ((fun t => (↑t).snd) <$> { fst := a, snd := f }) = abs { fst := a, snd : …
      rfl
      -- 🎉 no goals
    intro i
    -- ⊢ r (↑(f i)).fst (↑(f i)).snd
    exact (f i).property
    -- 🎉 no goals
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  -- ⊢ Liftr r x y
  use abs ⟨a, fun i => ⟨(f₀ i, f₁ i), h i⟩⟩
  -- ⊢ (fun t => (↑t).fst) <$> abs { fst := a, snd := fun i => { val := (f₀ i, f₁ i …
  constructor
  -- ⊢ (fun t => (↑t).fst) <$> abs { fst := a, snd := fun i => { val := (f₀ i, f₁ i …
  · rw [xeq, ← abs_map]
    -- ⊢ abs ((fun t => (↑t).fst) <$> { fst := a, snd := fun i => { val := (f₀ i, f₁  …
    rfl
    -- 🎉 no goals
  rw [yeq, ← abs_map]; rfl
  -- ⊢ abs ((fun t => (↑t).snd) <$> { fst := a, snd := fun i => { val := (f₀ i, f₁  …
                       -- 🎉 no goals
#align qpf.liftr_iff Qpf.liftr_iff

end

/-
Think of trees in the `W` type corresponding to `P` as representatives of elements of the
least fixed point of `F`, and assign a canonical representative to each equivalence class
of trees.
-/
/-- does recursion on `q.P.W` using `g : F α → α` rather than `g : P α → α` -/
def recF {α : Type _} (g : F α → α) : q.P.W → α
  | ⟨a, f⟩ => g (abs ⟨a, fun x => recF g (f x)⟩)
set_option linter.uppercaseLean3 false in
#align qpf.recF Qpf.recF

theorem recF_eq {α : Type _} (g : F α → α) (x : q.P.W) :
    recF g x = g (abs (recF g <$> x.dest)) := by
  cases x
  -- ⊢ recF g (WType.mk a✝ f✝) = g (abs (recF g <$> PFunctor.W.dest (WType.mk a✝ f✝ …
  rfl
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align qpf.recF_eq Qpf.recF_eq

theorem recF_eq' {α : Type _} (g : F α → α) (a : q.P.A) (f : q.P.B a → q.P.W) :
    recF g ⟨a, f⟩ = g (abs (recF g <$> ⟨a, f⟩)) :=
  rfl
set_option linter.uppercaseLean3 false in
#align qpf.recF_eq' Qpf.recF_eq'

/-- two trees are equivalent if their F-abstractions are -/
inductive Wequiv : q.P.W → q.P.W → Prop
  | ind (a : q.P.A) (f f' : q.P.B a → q.P.W) : (∀ x, Wequiv (f x) (f' x)) → Wequiv ⟨a, f⟩ ⟨a, f'⟩
  | abs (a : q.P.A) (f : q.P.B a → q.P.W) (a' : q.P.A) (f' : q.P.B a' → q.P.W) :
      abs ⟨a, f⟩ = abs ⟨a', f'⟩ → Wequiv ⟨a, f⟩ ⟨a', f'⟩
  | trans (u v w : q.P.W) : Wequiv u v → Wequiv v w → Wequiv u w
set_option linter.uppercaseLean3 false in
#align qpf.Wequiv Qpf.Wequiv

/-- `recF` is insensitive to the representation -/
theorem recF_eq_of_Wequiv {α : Type u} (u : F α → α) (x y : q.P.W) :
    Wequiv x y → recF u x = recF u y := by
  intro h
  -- ⊢ recF u x = recF u y
  induction h
  case ind a f f' _ ih => simp only [recF_eq', PFunctor.map_eq, Function.comp, ih]
  -- ⊢ recF u (WType.mk a✝¹ f✝) = recF u (WType.mk a'✝ f'✝)
  -- 🎉 no goals
  case abs a f a' f' h => simp only [recF_eq', abs_map, h]
  -- ⊢ recF u u✝ = recF u w✝
  -- 🎉 no goals
  case trans x y z _ _ ih₁ ih₂ => exact Eq.trans ih₁ ih₂
  -- 🎉 no goals
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align qpf.recF_eq_of_Wequiv Qpf.recF_eq_of_Wequiv

theorem Wequiv.abs' (x y : q.P.W) (h : Qpf.abs x.dest = Qpf.abs y.dest) : Wequiv x y := by
  cases x
  -- ⊢ Wequiv (WType.mk a✝ f✝) y
  cases y
  -- ⊢ Wequiv (WType.mk a✝¹ f✝¹) (WType.mk a✝ f✝)
  apply Wequiv.abs
  -- ⊢ Qpf.abs { fst := a✝¹, snd := f✝¹ } = Qpf.abs { fst := a✝, snd := f✝ }
  apply h
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align qpf.Wequiv.abs' Qpf.Wequiv.abs'

theorem Wequiv.refl (x : q.P.W) : Wequiv x x := by
  cases' x with a f
  -- ⊢ Wequiv (WType.mk a f) (WType.mk a f)
  exact Wequiv.abs a f a f rfl
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align qpf.Wequiv.refl Qpf.Wequiv.refl

theorem Wequiv.symm (x y : q.P.W) : Wequiv x y → Wequiv y x := by
  intro h
  -- ⊢ Wequiv y x
  induction h
  case ind a f f' _ ih => exact Wequiv.ind _ _ _ ih
  -- ⊢ Wequiv (WType.mk a'✝ f'✝) (WType.mk a✝¹ f✝)
  -- 🎉 no goals
  case abs a f a' f' h => exact Wequiv.abs _ _ _ _ h.symm
  -- ⊢ Wequiv w✝ u✝
  -- 🎉 no goals
  case trans x y z _ _ ih₁ ih₂ => exact Qpf.Wequiv.trans _ _ _ ih₂ ih₁
  -- 🎉 no goals
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align qpf.Wequiv.symm Qpf.Wequiv.symm

/-- maps every element of the W type to a canonical representative -/
def Wrepr : q.P.W → q.P.W :=
  recF (PFunctor.W.mk ∘ repr)
set_option linter.uppercaseLean3 false in
#align qpf.Wrepr Qpf.Wrepr

theorem Wrepr_equiv (x : q.P.W) : Wequiv (Wrepr x) x := by
  induction' x with a f ih
  -- ⊢ Wequiv (Wrepr (WType.mk a f)) (WType.mk a f)
  apply Wequiv.trans
  · change Wequiv (Wrepr ⟨a, f⟩) (PFunctor.W.mk (Wrepr <$> ⟨a, f⟩))
    -- ⊢ Wequiv (Wrepr (WType.mk a f)) (PFunctor.W.mk (Wrepr <$> { fst := a, snd := f …
    apply Wequiv.abs'
    -- ⊢ abs (PFunctor.W.dest (Wrepr (WType.mk a f))) = abs (PFunctor.W.dest (PFuncto …
    have : Wrepr ⟨a, f⟩ = PFunctor.W.mk (repr (abs (Wrepr <$> ⟨a, f⟩))) := rfl
    -- ⊢ abs (PFunctor.W.dest (Wrepr (WType.mk a f))) = abs (PFunctor.W.dest (PFuncto …
    rw [this, PFunctor.W.dest_mk, abs_repr]
    -- ⊢ abs (Wrepr <$> { fst := a, snd := f }) = abs (PFunctor.W.dest (PFunctor.W.mk …
    rfl
    -- 🎉 no goals
  apply Wequiv.ind; exact ih
  -- ⊢ ∀ (x : PFunctor.B (P F) a), Wequiv ((Wrepr ∘ f) x) (f x)
                    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align qpf.Wrepr_equiv Qpf.Wrepr_equiv

/-- Define the fixed point as the quotient of trees under the equivalence relation `Wequiv`. -/
def Wsetoid : Setoid q.P.W :=
  ⟨Wequiv, @Wequiv.refl _ _ _, @Wequiv.symm _ _ _, @Wequiv.trans _ _ _⟩
set_option linter.uppercaseLean3 false in
#align qpf.W_setoid Qpf.Wsetoid

attribute [local instance] Wsetoid

/-- inductive type defined as initial algebra of a Quotient of Polynomial Functor -/
--@[nolint has_nonempty_instance] Porting note: linter does not exist
def Fix (F : Type u → Type u) [Functor F] [q : Qpf F] :=
  Quotient (Wsetoid : Setoid q.P.W)
#align qpf.fix Qpf.Fix

/-- recursor of a type defined by a qpf -/
def Fix.rec {α : Type _} (g : F α → α) : Fix F → α :=
  Quot.lift (recF g) (recF_eq_of_Wequiv g)
#align qpf.fix.rec Qpf.Fix.rec

/-- access the underlying W-type of a fixpoint data type -/
def fixToW : Fix F → q.P.W :=
  Quotient.lift Wrepr (recF_eq_of_Wequiv fun x => @PFunctor.W.mk q.P (repr x))
set_option linter.uppercaseLean3 false in
#align qpf.fix_to_W Qpf.fixToW

/-- constructor of a type defined by a qpf -/
def Fix.mk (x : F (Fix F)) : Fix F :=
  Quot.mk _ (PFunctor.W.mk (fixToW <$> repr x))
#align qpf.fix.mk Qpf.Fix.mk

/-- destructor of a type defined by a qpf -/
def Fix.dest : Fix F → F (Fix F) :=
  Fix.rec (Functor.map Fix.mk)
#align qpf.fix.dest Qpf.Fix.dest

theorem Fix.rec_eq {α : Type _} (g : F α → α) (x : F (Fix F)) :
    Fix.rec g (Fix.mk x) = g (Fix.rec g <$> x) := by
  have : recF g ∘ fixToW = Fix.rec g := by
    apply funext
    apply Quotient.ind
    intro x
    apply recF_eq_of_Wequiv
    rw [fixToW]
    apply Wrepr_equiv
  conv =>
    lhs
    rw [Fix.rec, Fix.mk]
    dsimp
  cases' h : repr x with a f
  -- ⊢ recF g (PFunctor.W.mk (fixToW <$> { fst := a, snd := f })) = g (rec g <$> x)
  rw [PFunctor.map_eq, recF_eq, ← PFunctor.map_eq, PFunctor.W.dest_mk, ← PFunctor.comp_map, abs_map,
    ← h, abs_repr, this]
#align qpf.fix.rec_eq Qpf.Fix.rec_eq

theorem Fix.ind_aux (a : q.P.A) (f : q.P.B a → q.P.W) :
    Fix.mk (abs ⟨a, fun x => ⟦f x⟧⟩) = ⟦⟨a, f⟩⟧ := by
  have : Fix.mk (abs ⟨a, fun x => ⟦f x⟧⟩) = ⟦Wrepr ⟨a, f⟩⟧ := by
    apply Quot.sound; apply Wequiv.abs'
    rw [PFunctor.W.dest_mk, abs_map, abs_repr, ← abs_map, PFunctor.map_eq]
    conv =>
      rhs
      simp only [Wrepr, recF_eq, PFunctor.W.dest_mk, abs_repr, Function.comp]
  rw [this]
  -- ⊢ Quotient.mk Wsetoid (Wrepr (WType.mk a f)) = Quotient.mk Wsetoid (WType.mk a …
  apply Quot.sound
  -- ⊢ Setoid.r (Wrepr (WType.mk a f)) (WType.mk a f)
  apply Wrepr_equiv
  -- 🎉 no goals
#align qpf.fix.ind_aux Qpf.Fix.ind_aux

theorem Fix.ind_rec {α : Type u} (g₁ g₂ : Fix F → α)
    (h : ∀ x : F (Fix F), g₁ <$> x = g₂ <$> x → g₁ (Fix.mk x) = g₂ (Fix.mk x)) :
    ∀ x, g₁ x = g₂ x := by
  apply Quot.ind
  -- ⊢ ∀ (a : PFunctor.W (P F)), g₁ (Quot.mk Setoid.r a) = g₂ (Quot.mk Setoid.r a)
  intro x
  -- ⊢ g₁ (Quot.mk Setoid.r x) = g₂ (Quot.mk Setoid.r x)
  induction' x with a f ih
  -- ⊢ g₁ (Quot.mk Setoid.r (WType.mk a f)) = g₂ (Quot.mk Setoid.r (WType.mk a f))
  change g₁ ⟦⟨a, f⟩⟧ = g₂ ⟦⟨a, f⟩⟧
  -- ⊢ g₁ (Quotient.mk Wsetoid (WType.mk a f)) = g₂ (Quotient.mk Wsetoid (WType.mk  …
  rw [← Fix.ind_aux a f]; apply h
  -- ⊢ g₁ (mk (abs { fst := a, snd := fun x => Quotient.mk Wsetoid (f x) })) = g₂ ( …
                          -- ⊢ g₁ <$> abs { fst := a, snd := fun x => Quotient.mk Wsetoid (f x) } = g₂ <$>  …
  rw [← abs_map, ← abs_map, PFunctor.map_eq, PFunctor.map_eq]
  -- ⊢ abs { fst := a, snd := g₁ ∘ fun x => Quotient.mk Wsetoid (f x) } = abs { fst …
  congr with x
  -- ⊢ (g₁ ∘ fun x => Quotient.mk Wsetoid (f x)) x = (g₂ ∘ fun x => Quotient.mk Wse …
  apply ih
  -- 🎉 no goals
#align qpf.fix.ind_rec Qpf.Fix.ind_rec

theorem Fix.rec_unique {α : Type u} (g : F α → α) (h : Fix F → α)
    (hyp : ∀ x, h (Fix.mk x) = g (h <$> x)) : Fix.rec g = h := by
  ext x
  -- ⊢ rec g x = h x
  apply Fix.ind_rec
  -- ⊢ ∀ (x : F (Fix F)), rec g <$> x = (fun x => h x) <$> x → rec g (mk x) = h (mk …
  intro x hyp'
  -- ⊢ rec g (mk x) = h (mk x)
  rw [hyp, ← hyp', Fix.rec_eq]
  -- 🎉 no goals
#align qpf.fix.rec_unique Qpf.Fix.rec_unique

theorem Fix.mk_dest (x : Fix F) : Fix.mk (Fix.dest x) = x := by
  change (Fix.mk ∘ Fix.dest) x = id x
  -- ⊢ (mk ∘ dest) x = id x
  apply Fix.ind_rec (mk ∘ dest) id
  -- ⊢ ∀ (x : F (Fix F)), (mk ∘ dest) <$> x = id <$> x → (mk ∘ dest) (mk x) = id (m …
  intro x
  -- ⊢ (mk ∘ dest) <$> x = id <$> x → (mk ∘ dest) (mk x) = id (mk x)
  rw [Function.comp_apply, id_eq, Fix.dest, Fix.rec_eq, id_map, comp_map]
  -- ⊢ mk <$> rec (Functor.map mk) <$> x = x → mk (mk <$> rec (Functor.map mk) <$>  …
  intro h
  -- ⊢ mk (mk <$> rec (Functor.map mk) <$> x) = mk x
  rw [h]
  -- 🎉 no goals
#align qpf.fix.mk_dest Qpf.Fix.mk_dest

theorem Fix.dest_mk (x : F (Fix F)) : Fix.dest (Fix.mk x) = x := by
  unfold Fix.dest; rw [Fix.rec_eq, ← Fix.dest, ← comp_map]
  -- ⊢ rec (Functor.map mk) (mk x) = x
                   -- ⊢ (mk ∘ dest) <$> x = x
  conv =>
    rhs
    rw [← id_map x]
  congr with x
  -- ⊢ (mk ∘ dest) x = id x
  apply Fix.mk_dest
  -- 🎉 no goals
#align qpf.fix.dest_mk Qpf.Fix.dest_mk

theorem Fix.ind (p : Fix F → Prop) (h : ∀ x : F (Fix F), Liftp p x → p (Fix.mk x)) : ∀ x, p x := by
  apply Quot.ind
  -- ⊢ ∀ (a : PFunctor.W (P F)), p (Quot.mk Setoid.r a)
  intro x
  -- ⊢ p (Quot.mk Setoid.r x)
  induction' x with a f ih
  -- ⊢ p (Quot.mk Setoid.r (WType.mk a f))
  change p ⟦⟨a, f⟩⟧
  -- ⊢ p (Quotient.mk Wsetoid (WType.mk a f))
  rw [← Fix.ind_aux a f]
  -- ⊢ p (mk (abs { fst := a, snd := fun x => Quotient.mk Wsetoid (f x) }))
  apply h
  -- ⊢ Liftp p (abs { fst := a, snd := fun x => Quotient.mk Wsetoid (f x) })
  rw [liftp_iff]
  -- ⊢ ∃ a_1 f_1, abs { fst := a, snd := fun x => Quotient.mk Wsetoid (f x) } = abs …
  refine' ⟨_, _, rfl, _⟩
  -- ⊢ ∀ (i : PFunctor.B (P F) a), p (Quotient.mk Wsetoid (f i))
  convert ih
  -- 🎉 no goals
#align qpf.fix.ind Qpf.Fix.ind

end Qpf

/-
Construct the final coalgebra to a qpf.
-/
namespace Qpf

variable {F : Type u → Type u} [Functor F] [q : Qpf F]

open Functor (Liftp Liftr)

/-- does recursion on `q.P.M` using `g : α → F α` rather than `g : α → P α` -/
def corecF {α : Type _} (g : α → F α) : α → q.P.M :=
  PFunctor.M.corec fun x => repr (g x)
set_option linter.uppercaseLean3 false in
#align qpf.corecF Qpf.corecF

theorem corecF_eq {α : Type _} (g : α → F α) (x : α) :
    PFunctor.M.dest (corecF g x) = corecF g <$> repr (g x) := by rw [corecF, PFunctor.M.dest_corec]
                                                                 -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align qpf.corecF_eq Qpf.corecF_eq

-- Equivalence
/-- A pre-congruence on `q.P.M` *viewed as an F-coalgebra*. Not necessarily symmetric. -/
def IsPrecongr (r : q.P.M → q.P.M → Prop) : Prop :=
  ∀ ⦃x y⦄, r x y → abs (Quot.mk r <$> PFunctor.M.dest x) = abs (Quot.mk r <$> PFunctor.M.dest y)
#align qpf.is_precongr Qpf.IsPrecongr

/-- The maximal congruence on `q.P.M`. -/
def Mcongr : q.P.M → q.P.M → Prop := fun x y => ∃ r, IsPrecongr r ∧ r x y
set_option linter.uppercaseLean3 false in
#align qpf.Mcongr Qpf.Mcongr

/-- coinductive type defined as the final coalgebra of a qpf -/
def Cofix (F : Type u → Type u) [Functor F] [q : Qpf F] :=
  Quot (@Mcongr F _ q)
#align qpf.cofix Qpf.Cofix

instance [Inhabited q.P.A] : Inhabited (Cofix F) :=
  ⟨Quot.mk _ default⟩

/-- corecursor for type defined by `Cofix` -/
def Cofix.corec {α : Type _} (g : α → F α) (x : α) : Cofix F :=
  Quot.mk _ (corecF g x)
#align qpf.cofix.corec Qpf.Cofix.corec

/-- destructor for type defined by `Cofix` -/
def Cofix.dest : Cofix F → F (Cofix F) :=
  Quot.lift (fun x => Quot.mk Mcongr <$> abs (PFunctor.M.dest x))
    (by
      rintro x y ⟨r, pr, rxy⟩
      -- ⊢ (fun x => Quot.mk Mcongr <$> abs (PFunctor.M.dest x)) x = (fun x => Quot.mk  …
      dsimp
      -- ⊢ Quot.mk Mcongr <$> abs (PFunctor.M.dest x) = Quot.mk Mcongr <$> abs (PFuncto …
      have : ∀ x y, r x y → Mcongr x y := by
        intro x y h
        exact ⟨r, pr, h⟩
      rw [← Quot.factor_mk_eq _ _ this]
      -- ⊢ (Quot.factor (fun x y => r x y) (fun x y => Mcongr x y) this ∘ Quot.mk fun x …
      conv =>
        lhs
        rw [comp_map, ← abs_map, pr rxy, abs_map, ← comp_map])
#align qpf.cofix.dest Qpf.Cofix.dest

theorem Cofix.dest_corec {α : Type u} (g : α → F α) (x : α) :
    Cofix.dest (Cofix.corec g x) = Cofix.corec g <$> g x := by
  conv =>
    lhs
    rw [Cofix.dest, Cofix.corec];
  dsimp
  -- ⊢ Quot.mk Mcongr <$> abs (PFunctor.M.dest (corecF g x)) = corec g <$> g x
  rw [corecF_eq, abs_map, abs_repr, ← comp_map]; rfl
  -- ⊢ (Quot.mk Mcongr ∘ corecF g) <$> g x = corec g <$> g x
                                                 -- 🎉 no goals
#align qpf.cofix.dest_corec Qpf.Cofix.dest_corec

-- Porting note: Needed to add `(motive := _)` to get `Quot.inductionOn` to work
private theorem Cofix.bisim_aux (r : Cofix F → Cofix F → Prop) (h' : ∀ x, r x x)
    (h : ∀ x y, r x y → Quot.mk r <$> Cofix.dest x = Quot.mk r <$> Cofix.dest y) :
    ∀ x y, r x y → x = y := by
  intro x
  -- ⊢ ∀ (y : Cofix F), r x y → x = y
  apply Quot.inductionOn (motive := _) x
  -- ⊢ ∀ (a : PFunctor.M (P F)) (y : Cofix F), r (Quot.mk Mcongr a) y → Quot.mk Mco …
  clear x
  -- ⊢ ∀ (a : PFunctor.M (P F)) (y : Cofix F), r (Quot.mk Mcongr a) y → Quot.mk Mco …
  intro x y
  -- ⊢ r (Quot.mk Mcongr x) y → Quot.mk Mcongr x = y
  apply Quot.inductionOn (motive := _) y
  -- ⊢ ∀ (a : PFunctor.M (P F)), r (Quot.mk Mcongr x) (Quot.mk Mcongr a) → Quot.mk  …
  clear y
  -- ⊢ ∀ (a : PFunctor.M (P F)), r (Quot.mk Mcongr x) (Quot.mk Mcongr a) → Quot.mk  …
  intro y rxy
  -- ⊢ Quot.mk Mcongr x = Quot.mk Mcongr y
  apply Quot.sound
  -- ⊢ Mcongr x y
  let r' x y := r (Quot.mk _ x) (Quot.mk _ y)
  -- ⊢ Mcongr x y
  have : IsPrecongr r' := by
    intro a b r'ab
    have h₀ :
      Quot.mk r <$> Quot.mk Mcongr <$> abs (PFunctor.M.dest a) =
        Quot.mk r <$> Quot.mk Mcongr <$> abs (PFunctor.M.dest b) :=
      h _ _ r'ab
    have h₁ : ∀ u v : q.P.M, Mcongr u v → Quot.mk r' u = Quot.mk r' v := by
      intro u v cuv
      apply Quot.sound
      simp only
      rw [Quot.sound cuv]
      apply h'
    let f : Quot r → Quot r' :=
      Quot.lift (Quot.lift (Quot.mk r') h₁)
        (by
          intro c; apply Quot.inductionOn (motive := _) c; clear c
          intro c d; apply Quot.inductionOn (motive := _) d; clear d
          intro d rcd; apply Quot.sound; apply rcd)
    have : f ∘ Quot.mk r ∘ Quot.mk Mcongr = Quot.mk r' := rfl
    rw [← this, PFunctor.comp_map _ _ f, PFunctor.comp_map _ _ (Quot.mk r), abs_map, abs_map,
      abs_map, h₀]
    rw [PFunctor.comp_map _ _ f, PFunctor.comp_map _ _ (Quot.mk r), abs_map, abs_map, abs_map]
  refine' ⟨r', this, rxy⟩
  -- 🎉 no goals

theorem Cofix.bisim_rel (r : Cofix F → Cofix F → Prop)
    (h : ∀ x y, r x y → Quot.mk r <$> Cofix.dest x = Quot.mk r <$> Cofix.dest y) :
    ∀ x y, r x y → x = y := by
  let r' (x y) := x = y ∨ r x y
  -- ⊢ ∀ (x y : Cofix F), r x y → x = y
  intro x y rxy
  -- ⊢ x = y
  apply Cofix.bisim_aux r'
  · intro x
    -- ⊢ r' x x
    left
    -- ⊢ x = x
    rfl
    -- 🎉 no goals
  · intro x y r'xy
    -- ⊢ Quot.mk r' <$> dest x = Quot.mk r' <$> dest y
    cases' r'xy with r'xy r'xy
    -- ⊢ Quot.mk r' <$> dest x = Quot.mk r' <$> dest y
    · rw [r'xy]
      -- 🎉 no goals
    have : ∀ x y, r x y → r' x y := fun x y h => Or.inr h
    -- ⊢ Quot.mk r' <$> dest x = Quot.mk r' <$> dest y
    rw [← Quot.factor_mk_eq _ _ this]
    -- ⊢ (Quot.factor (fun x y => r x y) (fun x y => r' x y) this ∘ Quot.mk fun x y = …
    dsimp
    -- ⊢ (Quot.factor (fun x y => r x y) (fun x y => x = y ∨ r x y) this ∘ Quot.mk fu …
    rw [@comp_map _ _ q _ _ _ (Quot.mk r), @comp_map _ _ q _ _ _ (Quot.mk r)]
    -- ⊢ Quot.factor (fun x y => r x y) (fun x y => x = y ∨ r x y) this <$> Quot.mk r …
    rw [h _ _ r'xy]
    -- 🎉 no goals
  right; exact rxy
  -- ⊢ r x y
         -- 🎉 no goals
#align qpf.cofix.bisim_rel Qpf.Cofix.bisim_rel

theorem Cofix.bisim (r : Cofix F → Cofix F → Prop)
    (h : ∀ x y, r x y → Liftr r (Cofix.dest x) (Cofix.dest y)) : ∀ x y, r x y → x = y := by
  apply Cofix.bisim_rel
  -- ⊢ ∀ (x y : Cofix F), r x y → (Quot.mk fun x y => r x y) <$> dest x = (Quot.mk  …
  intro x y rxy
  -- ⊢ (Quot.mk fun x y => r x y) <$> dest x = (Quot.mk fun x y => r x y) <$> dest y
  rcases (liftr_iff r _ _).mp (h x y rxy) with ⟨a, f₀, f₁, dxeq, dyeq, h'⟩
  -- ⊢ (Quot.mk fun x y => r x y) <$> dest x = (Quot.mk fun x y => r x y) <$> dest y
  rw [dxeq, dyeq, ← abs_map, ← abs_map, PFunctor.map_eq, PFunctor.map_eq]
  -- ⊢ abs { fst := a, snd := (Quot.mk fun x y => r x y) ∘ f₀ } = abs { fst := a, s …
  congr 2 with i
  -- ⊢ ((Quot.mk fun x y => r x y) ∘ f₀) i = ((Quot.mk fun x y => r x y) ∘ f₁) i
  apply Quot.sound
  -- ⊢ r (f₀ i) (f₁ i)
  apply h'
  -- 🎉 no goals
#align qpf.cofix.bisim Qpf.Cofix.bisim

theorem Cofix.bisim' {α : Type*} (Q : α → Prop) (u v : α → Cofix F)
    (h : ∀ x, Q x → ∃ a f f', Cofix.dest (u x) = abs ⟨a, f⟩ ∧ Cofix.dest (v x) = abs ⟨a, f'⟩ ∧
      ∀ i, ∃ x', Q x' ∧ f i = u x' ∧ f' i = v x') :
    ∀ x, Q x → u x = v x := fun x Qx =>
  let R := fun w z : Cofix F => ∃ x', Q x' ∧ w = u x' ∧ z = v x'
  Cofix.bisim R
    (fun x y ⟨x', Qx', xeq, yeq⟩ => by
      rcases h x' Qx' with ⟨a, f, f', ux'eq, vx'eq, h'⟩
      -- ⊢ Liftr R (dest x) (dest y)
      rw [liftr_iff]
      -- ⊢ ∃ a f₀ f₁, dest x = abs { fst := a, snd := f₀ } ∧ dest y = abs { fst := a, s …
      refine' ⟨a, f, f', xeq.symm ▸ ux'eq, yeq.symm ▸ vx'eq, h'⟩)
      -- 🎉 no goals
    _ _ ⟨x, Qx, rfl, rfl⟩
#align qpf.cofix.bisim' Qpf.Cofix.bisim'

end Qpf

/-
Composition of qpfs.
-/
namespace Qpf

variable {F₂ : Type u → Type u} [Functor F₂] [q₂ : Qpf F₂]

variable {F₁ : Type u → Type u} [Functor F₁] [q₁ : Qpf F₁]

/-- composition of qpfs gives another qpf -/
def comp : Qpf (Functor.Comp F₂ F₁) where
  P := PFunctor.comp q₂.P q₁.P
  abs {α} := by
    dsimp [Functor.Comp]
    -- ⊢ PFunctor.Obj (PFunctor.comp (P F₂) (P F₁)) α → F₂ (F₁ α)
    intro p
    -- ⊢ F₂ (F₁ α)
    exact abs ⟨p.1.1, fun x => abs ⟨p.1.2 x, fun y => p.2 ⟨x, y⟩⟩⟩
    -- 🎉 no goals
  repr {α} := by
    dsimp [Functor.Comp]
    -- ⊢ F₂ (F₁ α) → PFunctor.Obj (PFunctor.comp (P F₂) (P F₁)) α
    intro y
    -- ⊢ PFunctor.Obj (PFunctor.comp (P F₂) (P F₁)) α
    refine' ⟨⟨(repr y).1, fun u => (repr ((repr y).2 u)).1⟩, _⟩
    -- ⊢ PFunctor.B (PFunctor.comp (P F₂) (P F₁)) { fst := (repr y).fst, snd := fun u …
    dsimp [PFunctor.comp]
    -- ⊢ (u : PFunctor.B (P F₂) (repr y).fst) × PFunctor.B (P F₁) (repr (Sigma.snd (r …
    intro x
    -- ⊢ α
    exact (repr ((repr y).2 x.1)).snd x.2
    -- 🎉 no goals
  abs_repr {α} := by
    dsimp [Functor.Comp]
    -- ⊢ ∀ (x : F₂ (F₁ α)), abs { fst := (repr x).fst, snd := fun x_1 => abs { fst := …
    intro x
    -- ⊢ abs { fst := (repr x).fst, snd := fun x_1 => abs { fst := (repr (Sigma.snd ( …
    conv =>
      rhs
      rw [← abs_repr x]
    cases' h : repr x with a f
    -- ⊢ abs { fst := { fst := a, snd := f }.fst, snd := fun x => abs { fst := (repr  …
    dsimp
    -- ⊢ abs { fst := a, snd := fun x => abs { fst := (repr (f x)).fst, snd := fun y  …
    congr with x
    -- ⊢ abs { fst := (repr (f x)).fst, snd := fun y => Sigma.snd (repr (f x)) y } =  …
    cases' h' : repr (f x) with b g
    -- ⊢ abs { fst := { fst := b, snd := g }.fst, snd := fun y => Sigma.snd { fst :=  …
    dsimp; rw [← h', abs_repr]
    -- ⊢ abs { fst := b, snd := fun y => g y } = f x
           -- 🎉 no goals
  abs_map {α β} f := by
    dsimp [Functor.Comp, PFunctor.comp]
    -- ⊢ ∀ (p : PFunctor.Obj { A := (a₂ : (P F₂).A) × (PFunctor.B (P F₂) a₂ → (P F₁). …
    intro p
    -- ⊢ abs { fst := (f <$> p).fst.fst, snd := fun x => abs { fst := Sigma.snd (f <$ …
    cases' p with a g; dsimp
    -- ⊢ abs { fst := (f <$> { fst := a, snd := g }).fst.fst, snd := fun x => abs { f …
                       -- ⊢ abs { fst := (f <$> { fst := a, snd := g }).fst.fst, snd := fun x => abs { f …
    cases' a with b h; dsimp
    -- ⊢ abs { fst := (f <$> { fst := { fst := b, snd := h }, snd := g }).fst.fst, sn …
                       -- ⊢ abs { fst := (f <$> { fst := { fst := b, snd := h }, snd := g }).fst.fst, sn …
    symm
    -- ⊢ f <$> abs { fst := b, snd := fun x => abs { fst := h x, snd := fun y => g {  …
    trans
    symm
    -- ⊢ ?a = f <$> abs { fst := b, snd := fun x => abs { fst := h x, snd := fun y => …
    apply abs_map
    -- ⊢ abs ((fun x x_1 => x <$> x_1) f <$> { fst := b, snd := fun x => abs { fst := …
    congr
    -- ⊢ (fun x x_1 => x <$> x_1) f <$> { fst := b, snd := fun x => abs { fst := h x, …
    rw [PFunctor.map_eq]
    -- ⊢ { fst := b, snd := (fun x x_1 => x <$> x_1) f ∘ fun x => abs { fst := h x, s …
    dsimp [Function.comp]
    -- ⊢ { fst := b, snd := fun x => f <$> abs { fst := h x, snd := fun y => g { fst  …
    congr
    -- ⊢ (fun x => f <$> abs { fst := h x, snd := fun y => g { fst := x, snd := y } } …
    ext x
    -- ⊢ f <$> abs { fst := h x, snd := fun y => g { fst := x, snd := y } } = abs { f …
    rw [← abs_map]
    -- ⊢ abs (f <$> { fst := h x, snd := fun y => g { fst := x, snd := y } }) = abs { …
    rfl
    -- 🎉 no goals
#align qpf.comp Qpf.comp

end Qpf

/-
Quotients.

We show that if `F` is a qpf and `G` is a suitable quotient of `F`, then `G` is a qpf.
-/
namespace Qpf

variable {F : Type u → Type u} [Functor F] [q : Qpf F]

variable {G : Type u → Type u} [Functor G]

variable {FG_abs : ∀ {α}, F α → G α}

variable {FG_repr : ∀ {α}, G α → F α}

/-- Given a qpf `F` and a well-behaved surjection `FG_abs` from `F α` to
functor `G α`, `G` is a qpf. We can consider `G` a quotient on `F` where
elements `x y : F α` are in the same equivalence class if
`FG_abs x = FG_abs y`. -/
def quotientQpf (FG_abs_repr : ∀ {α} (x : G α), FG_abs (FG_repr x) = x)
    (FG_abs_map : ∀ {α β} (f : α → β) (x : F α), FG_abs (f <$> x) = f <$> FG_abs x) : Qpf G where
  P := q.P
  abs {α} p := FG_abs (abs p)
  repr {α} x := repr (FG_repr x)
  abs_repr {α} x := by simp only; rw [abs_repr, FG_abs_repr]
                       -- ⊢ FG_abs (abs (repr (FG_repr x))) = x
                                  -- 🎉 no goals
  abs_map {α β} f x := by simp only; rw [abs_map, FG_abs_map]
                          -- ⊢ FG_abs (abs (f <$> x)) = f <$> FG_abs (abs x)
                                     -- 🎉 no goals
#align qpf.quotient_qpf Qpf.quotientQpf

end Qpf

/-
Support.
-/
namespace Qpf

variable {F : Type u → Type u} [Functor F] [q : Qpf F]

open Functor (Liftp Liftr supp)

open Set

theorem mem_supp {α : Type u} (x : F α) (u : α) :
    u ∈ supp x ↔ ∀ a f, abs ⟨a, f⟩ = x → u ∈ f '' univ := by
  rw [supp]; dsimp; constructor
  -- ⊢ u ∈ {y | ∀ ⦃p : α → Prop⦄, Liftp p x → p y} ↔ ∀ (a : (P F).A) (f : PFunctor. …
             -- ⊢ (∀ ⦃p : α → Prop⦄, Liftp p x → p u) ↔ ∀ (a : (P F).A) (f : PFunctor.B (P F)  …
                    -- ⊢ (∀ ⦃p : α → Prop⦄, Liftp p x → p u) → ∀ (a : (P F).A) (f : PFunctor.B (P F)  …
  · intro h a f haf
    -- ⊢ u ∈ f '' univ
    have : Liftp (fun u => u ∈ f '' univ) x := by
      rw [liftp_iff]
      refine' ⟨a, f, haf.symm, fun i => mem_image_of_mem _ (mem_univ _)⟩
    exact h this
    -- 🎉 no goals
  intro h p; rw [liftp_iff]
  -- ⊢ Liftp p x → p u
             -- ⊢ (∃ a f, x = abs { fst := a, snd := f } ∧ ∀ (i : PFunctor.B (P F) a), p (f i) …
  rintro ⟨a, f, xeq, h'⟩
  -- ⊢ p u
  rcases h a f xeq.symm with ⟨i, _, hi⟩
  -- ⊢ p u
  rw [← hi]; apply h'
  -- ⊢ p (f i)
             -- 🎉 no goals
#align qpf.mem_supp Qpf.mem_supp

theorem supp_eq {α : Type u} (x : F α) :
    supp x = { u | ∀ a f, abs ⟨a, f⟩ = x → u ∈ f '' univ } := by
  ext
  -- ⊢ x✝ ∈ supp x ↔ x✝ ∈ {u | ∀ (a : (P F).A) (f : PFunctor.B (P F) a → α), abs {  …
  apply mem_supp
  -- 🎉 no goals
#align qpf.supp_eq Qpf.supp_eq

theorem has_good_supp_iff {α : Type u} (x : F α) :
    (∀ p, Liftp p x ↔ ∀ u ∈ supp x, p u) ↔
      ∃ a f, abs ⟨a, f⟩ = x ∧ ∀ a' f', abs ⟨a', f'⟩ = x → f '' univ ⊆ f' '' univ := by
  constructor
  -- ⊢ (∀ (p : α → Prop), Liftp p x ↔ ∀ (u : α), u ∈ supp x → p u) → ∃ a f, abs { f …
  · intro h
    -- ⊢ ∃ a f, abs { fst := a, snd := f } = x ∧ ∀ (a' : (P F).A) (f' : PFunctor.B (P …
    have : Liftp (supp x) x := by rw [h]; intro u; exact id
    -- ⊢ ∃ a f, abs { fst := a, snd := f } = x ∧ ∀ (a' : (P F).A) (f' : PFunctor.B (P …
    rw [liftp_iff] at this
    -- ⊢ ∃ a f, abs { fst := a, snd := f } = x ∧ ∀ (a' : (P F).A) (f' : PFunctor.B (P …
    rcases this with ⟨a, f, xeq, h'⟩
    -- ⊢ ∃ a f, abs { fst := a, snd := f } = x ∧ ∀ (a' : (P F).A) (f' : PFunctor.B (P …
    refine' ⟨a, f, xeq.symm, _⟩
    -- ⊢ ∀ (a' : (P F).A) (f' : PFunctor.B (P F) a' → α), abs { fst := a', snd := f'  …
    intro a' f' h''
    -- ⊢ f '' univ ⊆ f' '' univ
    rintro u ⟨i, _, hfi⟩
    -- ⊢ u ∈ f' '' univ
    have : u ∈ supp x := by rw [← hfi]; apply h'
    -- ⊢ u ∈ f' '' univ
    exact (mem_supp x u).mp this _ _ h''
    -- 🎉 no goals
  rintro ⟨a, f, xeq, h⟩ p; rw [liftp_iff]; constructor
  -- ⊢ Liftp p x ↔ ∀ (u : α), u ∈ supp x → p u
                           -- ⊢ (∃ a f, x = abs { fst := a, snd := f } ∧ ∀ (i : PFunctor.B (P F) a), p (f i) …
                                           -- ⊢ (∃ a f, x = abs { fst := a, snd := f } ∧ ∀ (i : PFunctor.B (P F) a), p (f i) …
  · rintro ⟨a', f', xeq', h'⟩ u usuppx
    -- ⊢ p u
    rcases (mem_supp x u).mp usuppx a' f' xeq'.symm with ⟨i, _, f'ieq⟩
    -- ⊢ p u
    rw [← f'ieq]
    -- ⊢ p (f' i)
    apply h'
    -- 🎉 no goals
  intro h'
  -- ⊢ ∃ a f, x = abs { fst := a, snd := f } ∧ ∀ (i : PFunctor.B (P F) a), p (f i)
  refine' ⟨a, f, xeq.symm, _⟩; intro i
  -- ⊢ ∀ (i : PFunctor.B (P F) a), p (f i)
                               -- ⊢ p (f i)
  apply h'; rw [mem_supp]
  -- ⊢ f i ∈ supp x
            -- ⊢ ∀ (a : (P F).A) (f_1 : PFunctor.B (P F) a → α), abs { fst := a, snd := f_1 } …
  intro a' f' xeq'
  -- ⊢ f i ∈ f' '' univ
  apply h a' f' xeq'
  -- ⊢ f i ∈ f '' univ
  apply mem_image_of_mem _ (mem_univ _)
  -- 🎉 no goals
#align qpf.has_good_supp_iff Qpf.has_good_supp_iff

/-- A qpf is said to be uniform if every polynomial functor
representing a single value all have the same range. -/
def IsUniform : Prop :=
  ∀ ⦃α : Type u⦄ (a a' : q.P.A) (f : q.P.B a → α) (f' : q.P.B a' → α),
    abs ⟨a, f⟩ = abs ⟨a', f'⟩ → f '' univ = f' '' univ
#align qpf.is_uniform Qpf.IsUniform

/-- does `abs` preserve `Liftp`? -/
def LiftpPreservation : Prop :=
  ∀ ⦃α⦄ (p : α → Prop) (x : q.P.Obj α), Liftp p (abs x) ↔ Liftp p x
#align qpf.liftp_preservation Qpf.LiftpPreservation

/-- does `abs` preserve `supp`? -/
def SuppPreservation : Prop :=
  ∀ ⦃α⦄ (x : q.P.Obj α), supp (abs x) = supp x
#align qpf.supp_preservation Qpf.SuppPreservation

theorem supp_eq_of_isUniform (h : q.IsUniform) {α : Type u} (a : q.P.A) (f : q.P.B a → α) :
    supp (abs ⟨a, f⟩) = f '' univ := by
  ext u; rw [mem_supp]; constructor
  -- ⊢ u ∈ supp (abs { fst := a, snd := f }) ↔ u ∈ f '' univ
         -- ⊢ (∀ (a_1 : (P F).A) (f_1 : PFunctor.B (P F) a_1 → α), abs { fst := a_1, snd : …
                        -- ⊢ (∀ (a_1 : (P F).A) (f_1 : PFunctor.B (P F) a_1 → α), abs { fst := a_1, snd : …
  · intro h'
    -- ⊢ u ∈ f '' univ
    apply h' _ _ rfl
    -- 🎉 no goals
  intro h' a' f' e
  -- ⊢ u ∈ f' '' univ
  rw [← h _ _ _ _ e.symm]; apply h'
  -- ⊢ u ∈ f '' univ
                           -- 🎉 no goals
#align qpf.supp_eq_of_is_uniform Qpf.supp_eq_of_isUniform

theorem liftp_iff_of_isUniform (h : q.IsUniform) {α : Type u} (x : F α) (p : α → Prop) :
    Liftp p x ↔ ∀ u ∈ supp x, p u := by
  rw [liftp_iff, ← abs_repr x]
  -- ⊢ (∃ a f, abs (repr x) = abs { fst := a, snd := f } ∧ ∀ (i : PFunctor.B (P F)  …
  cases' repr x with a f; constructor
  -- ⊢ (∃ a_1 f_1, abs { fst := a, snd := f } = abs { fst := a_1, snd := f_1 } ∧ ∀  …
                          -- ⊢ (∃ a_1 f_1, abs { fst := a, snd := f } = abs { fst := a_1, snd := f_1 } ∧ ∀  …
  · rintro ⟨a', f', abseq, hf⟩ u
    -- ⊢ u ∈ supp (abs { fst := a, snd := f }) → p u
    rw [supp_eq_of_isUniform h, h _ _ _ _ abseq]
    -- ⊢ u ∈ f' '' univ → p u
    rintro ⟨i, _, hi⟩
    -- ⊢ p u
    rw [← hi]
    -- ⊢ p (f' i)
    apply hf
    -- 🎉 no goals
  intro h'
  -- ⊢ ∃ a_1 f_1, abs { fst := a, snd := f } = abs { fst := a_1, snd := f_1 } ∧ ∀ ( …
  refine' ⟨a, f, rfl, fun i => h' _ _⟩
  -- ⊢ f i ∈ supp (abs { fst := a, snd := f })
  rw [supp_eq_of_isUniform h]
  -- ⊢ f i ∈ f '' univ
  exact ⟨i, mem_univ i, rfl⟩
  -- 🎉 no goals
#align qpf.liftp_iff_of_is_uniform Qpf.liftp_iff_of_isUniform

theorem supp_map (h : q.IsUniform) {α β : Type u} (g : α → β) (x : F α) :
    supp (g <$> x) = g '' supp x := by
  rw [← abs_repr x]; cases' repr x with a f; rw [← abs_map, PFunctor.map_eq]
  -- ⊢ supp (g <$> abs (repr x)) = g '' supp (abs (repr x))
                     -- ⊢ supp (g <$> abs { fst := a, snd := f }) = g '' supp (abs { fst := a, snd :=  …
                                             -- ⊢ supp (abs { fst := a, snd := g ∘ f }) = g '' supp (abs { fst := a, snd := f })
  rw [supp_eq_of_isUniform h, supp_eq_of_isUniform h, image_comp]
  -- 🎉 no goals
#align qpf.supp_map Qpf.supp_map

theorem suppPreservation_iff_uniform : q.SuppPreservation ↔ q.IsUniform := by
  constructor
  -- ⊢ SuppPreservation → IsUniform
  · intro h α a a' f f' h'
    -- ⊢ f '' univ = f' '' univ
    rw [← PFunctor.supp_eq, ← PFunctor.supp_eq, ← h, h', h]
    -- 🎉 no goals
  · rintro h α ⟨a, f⟩
    -- ⊢ supp (abs { fst := a, snd := f }) = supp { fst := a, snd := f }
    rwa [supp_eq_of_isUniform, PFunctor.supp_eq]
    -- 🎉 no goals
#align qpf.supp_preservation_iff_uniform Qpf.suppPreservation_iff_uniform

theorem suppPreservation_iff_liftpPreservation : q.SuppPreservation ↔ q.LiftpPreservation := by
  constructor <;> intro h
  -- ⊢ SuppPreservation → LiftpPreservation
                  -- ⊢ LiftpPreservation
                  -- ⊢ SuppPreservation
  · rintro α p ⟨a, f⟩
    -- ⊢ Liftp p (abs { fst := a, snd := f }) ↔ Liftp p { fst := a, snd := f }
    have h' := h
    -- ⊢ Liftp p (abs { fst := a, snd := f }) ↔ Liftp p { fst := a, snd := f }
    rw [suppPreservation_iff_uniform] at h'
    -- ⊢ Liftp p (abs { fst := a, snd := f }) ↔ Liftp p { fst := a, snd := f }
    dsimp only [SuppPreservation, supp] at h
    -- ⊢ Liftp p (abs { fst := a, snd := f }) ↔ Liftp p { fst := a, snd := f }
    rw [liftp_iff_of_isUniform h', supp_eq_of_isUniform h', PFunctor.liftp_iff']
    -- ⊢ (∀ (u : α), u ∈ f '' univ → p u) ↔ ∀ (i : PFunctor.B (P F) a), p (f i)
    simp only [image_univ, mem_range, exists_imp]
    -- ⊢ (∀ (u : α) (x : PFunctor.B (P F) a), f x = u → p u) ↔ ∀ (i : PFunctor.B (P F …
    constructor <;> intros <;> subst_vars <;> solve_by_elim
    -- ⊢ (∀ (u : α) (x : PFunctor.B (P F) a), f x = u → p u) → ∀ (i : PFunctor.B (P F …
                    -- ⊢ p (f i✝)
                    -- ⊢ p u✝
                               -- ⊢ p (f i✝)
                               -- ⊢ p (f x✝)
                                              -- 🎉 no goals
                                              -- 🎉 no goals
  · rintro α ⟨a, f⟩
    -- ⊢ supp (abs { fst := a, snd := f }) = supp { fst := a, snd := f }
    simp only [LiftpPreservation] at h
    -- ⊢ supp (abs { fst := a, snd := f }) = supp { fst := a, snd := f }
    simp only [supp, h]
    -- 🎉 no goals
#align qpf.supp_preservation_iff_liftp_preservation Qpf.suppPreservation_iff_liftpPreservation

theorem liftpPreservation_iff_uniform : q.LiftpPreservation ↔ q.IsUniform := by
  rw [← suppPreservation_iff_liftpPreservation, suppPreservation_iff_uniform]
  -- 🎉 no goals
#align qpf.liftp_preservation_iff_uniform Qpf.liftpPreservation_iff_uniform

end Qpf
