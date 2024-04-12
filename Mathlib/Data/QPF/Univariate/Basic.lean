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

* `P`: a polynomial functor
* `W`: its W-type
* `M`: its M-type
* `F`: a functor

We define:

* `q`: `QPF` data, representing `F` as a quotient of `P`

The main goal is to construct:

* `Fix`: the initial algebra with structure map `F Fix → Fix`.
* `Cofix`: the final coalgebra with structure map `Cofix → F Cofix`

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
class QPF (F : Type u → Type u) [Functor F] where
  P : PFunctor.{u}
  abs : ∀ {α}, P α → F α
  repr : ∀ {α}, F α → P α
  abs_repr : ∀ {α} (x : F α), abs (repr x) = x
  abs_map : ∀ {α β} (f : α → β) (p : P α), abs (P.map f p) = f <$> abs p
#align qpf QPF

namespace QPF

variable {F : Type u → Type u} [Functor F] [q : QPF F]

open Functor (Liftp Liftr)

/-
Show that every qpf is a lawful functor.

Note: every functor has a field, `map_const`, and `lawfulFunctor` has the defining
characterization. We can only propagate the assumption.
-/
theorem id_map {α : Type _} (x : F α) : id <$> x = x := by
  rw [← abs_repr x]
  cases' repr x with a f
  rw [← abs_map]
  rfl
#align qpf.id_map QPF.id_map

theorem comp_map {α β γ : Type _} (f : α → β) (g : β → γ) (x : F α) :
    (g ∘ f) <$> x = g <$> f <$> x := by
  rw [← abs_repr x]
  cases' repr x with a f
  rw [← abs_map, ← abs_map, ← abs_map]
  rfl
#align qpf.comp_map QPF.comp_map

theorem lawfulFunctor
    (h : ∀ α β : Type u, @Functor.mapConst F _ α _ = Functor.map ∘ Function.const β) :
    LawfulFunctor F :=
  { map_const := @h
    id_map := @id_map F _ _
    comp_map := @comp_map F _ _ }
#align qpf.is_lawful_functor QPF.lawfulFunctor

/-
Lifting predicates and relations
-/
section

open Functor

theorem liftp_iff {α : Type u} (p : α → Prop) (x : F α) :
    Liftp p x ↔ ∃ a f, x = abs ⟨a, f⟩ ∧ ∀ i, p (f i) := by
  constructor
  · rintro ⟨y, hy⟩
    cases' h : repr y with a f
    use a, fun i => (f i).val
    constructor
    · rw [← hy, ← abs_repr y, h, ← abs_map]
      rfl
    intro i
    apply (f i).property
  rintro ⟨a, f, h₀, h₁⟩
  use abs ⟨a, fun i => ⟨f i, h₁ i⟩⟩
  rw [← abs_map, h₀]; rfl
#align qpf.liftp_iff QPF.liftp_iff

theorem liftp_iff' {α : Type u} (p : α → Prop) (x : F α) :
    Liftp p x ↔ ∃ u : q.P α, abs u = x ∧ ∀ i, p (u.snd i) := by
  constructor
  · rintro ⟨y, hy⟩
    cases' h : repr y with a f
    use ⟨a, fun i => (f i).val⟩
    dsimp
    constructor
    · rw [← hy, ← abs_repr y, h, ← abs_map]
      rfl
    intro i
    apply (f i).property
  rintro ⟨⟨a, f⟩, h₀, h₁⟩; dsimp at *
  use abs ⟨a, fun i => ⟨f i, h₁ i⟩⟩
  rw [← abs_map, ← h₀]; rfl
#align qpf.liftp_iff' QPF.liftp_iff'

theorem liftr_iff {α : Type u} (r : α → α → Prop) (x y : F α) :
    Liftr r x y ↔ ∃ a f₀ f₁, x = abs ⟨a, f₀⟩ ∧ y = abs ⟨a, f₁⟩ ∧ ∀ i, r (f₀ i) (f₁ i) := by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    cases' h : repr u with a f
    use a, fun i => (f i).val.fst, fun i => (f i).val.snd
    constructor
    · rw [← xeq, ← abs_repr u, h, ← abs_map]
      rfl
    constructor
    · rw [← yeq, ← abs_repr u, h, ← abs_map]
      rfl
    intro i
    exact (f i).property
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  use abs ⟨a, fun i => ⟨(f₀ i, f₁ i), h i⟩⟩
  constructor
  · rw [xeq, ← abs_map]
    rfl
  rw [yeq, ← abs_map]; rfl
#align qpf.liftr_iff QPF.liftr_iff

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
#align qpf.recF QPF.recF

theorem recF_eq {α : Type _} (g : F α → α) (x : q.P.W) :
    recF g x = g (abs (q.P.map (recF g) x.dest)) := by
  cases x
  rfl
set_option linter.uppercaseLean3 false in
#align qpf.recF_eq QPF.recF_eq

theorem recF_eq' {α : Type _} (g : F α → α) (a : q.P.A) (f : q.P.B a → q.P.W) :
    recF g ⟨a, f⟩ = g (abs (q.P.map (recF g) ⟨a, f⟩)) :=
  rfl
set_option linter.uppercaseLean3 false in
#align qpf.recF_eq' QPF.recF_eq'

/-- two trees are equivalent if their F-abstractions are -/
inductive Wequiv : q.P.W → q.P.W → Prop
  | ind (a : q.P.A) (f f' : q.P.B a → q.P.W) : (∀ x, Wequiv (f x) (f' x)) → Wequiv ⟨a, f⟩ ⟨a, f'⟩
  | abs (a : q.P.A) (f : q.P.B a → q.P.W) (a' : q.P.A) (f' : q.P.B a' → q.P.W) :
      abs ⟨a, f⟩ = abs ⟨a', f'⟩ → Wequiv ⟨a, f⟩ ⟨a', f'⟩
  | trans (u v w : q.P.W) : Wequiv u v → Wequiv v w → Wequiv u w
set_option linter.uppercaseLean3 false in
#align qpf.Wequiv QPF.Wequiv

/-- `recF` is insensitive to the representation -/
theorem recF_eq_of_Wequiv {α : Type u} (u : F α → α) (x y : q.P.W) :
    Wequiv x y → recF u x = recF u y := by
  intro h
  induction h with
  | ind a f f' _ ih => simp only [recF_eq', PFunctor.map_eq, Function.comp, ih]
  | abs a f a' f' h => simp only [recF_eq', abs_map, h]
  | trans x y z _ _ ih₁ ih₂ => exact Eq.trans ih₁ ih₂
set_option linter.uppercaseLean3 false in
#align qpf.recF_eq_of_Wequiv QPF.recF_eq_of_Wequiv

theorem Wequiv.abs' (x y : q.P.W) (h : QPF.abs x.dest = QPF.abs y.dest) : Wequiv x y := by
  cases x
  cases y
  apply Wequiv.abs
  apply h
set_option linter.uppercaseLean3 false in
#align qpf.Wequiv.abs' QPF.Wequiv.abs'

theorem Wequiv.refl (x : q.P.W) : Wequiv x x := by
  cases' x with a f
  exact Wequiv.abs a f a f rfl
set_option linter.uppercaseLean3 false in
#align qpf.Wequiv.refl QPF.Wequiv.refl

theorem Wequiv.symm (x y : q.P.W) : Wequiv x y → Wequiv y x := by
  intro h
  induction h with
  | ind a f f' _ ih => exact Wequiv.ind _ _ _ ih
  | abs a f a' f' h => exact Wequiv.abs _ _ _ _ h.symm
  | trans x y z _ _ ih₁ ih₂ => exact QPF.Wequiv.trans _ _ _ ih₂ ih₁
set_option linter.uppercaseLean3 false in
#align qpf.Wequiv.symm QPF.Wequiv.symm

/-- maps every element of the W type to a canonical representative -/
def Wrepr : q.P.W → q.P.W :=
  recF (PFunctor.W.mk ∘ repr)
set_option linter.uppercaseLean3 false in
#align qpf.Wrepr QPF.Wrepr

theorem Wrepr_equiv (x : q.P.W) : Wequiv (Wrepr x) x := by
  induction' x with a f ih
  apply Wequiv.trans
  · change Wequiv (Wrepr ⟨a, f⟩) (PFunctor.W.mk (q.P.map Wrepr ⟨a, f⟩))
    apply Wequiv.abs'
    have : Wrepr ⟨a, f⟩ = PFunctor.W.mk (repr (abs (q.P.map Wrepr ⟨a, f⟩))) := rfl
    rw [this, PFunctor.W.dest_mk, abs_repr]
    rfl
  apply Wequiv.ind; exact ih
set_option linter.uppercaseLean3 false in
#align qpf.Wrepr_equiv QPF.Wrepr_equiv

/-- Define the fixed point as the quotient of trees under the equivalence relation `Wequiv`. -/
def Wsetoid : Setoid q.P.W :=
  ⟨Wequiv, @Wequiv.refl _ _ _, @Wequiv.symm _ _ _, @Wequiv.trans _ _ _⟩
set_option linter.uppercaseLean3 false in
#align qpf.W_setoid QPF.Wsetoid

attribute [local instance] Wsetoid

/-- inductive type defined as initial algebra of a Quotient of Polynomial Functor -/
--@[nolint has_nonempty_instance] Porting note: linter does not exist
def Fix (F : Type u → Type u) [Functor F] [q : QPF F] :=
  Quotient (Wsetoid : Setoid q.P.W)
#align qpf.fix QPF.Fix

/-- recursor of a type defined by a qpf -/
def Fix.rec {α : Type _} (g : F α → α) : Fix F → α :=
  Quot.lift (recF g) (recF_eq_of_Wequiv g)
#align qpf.fix.rec QPF.Fix.rec

/-- access the underlying W-type of a fixpoint data type -/
def fixToW : Fix F → q.P.W :=
  Quotient.lift Wrepr (recF_eq_of_Wequiv fun x => @PFunctor.W.mk q.P (repr x))
set_option linter.uppercaseLean3 false in
#align qpf.fix_to_W QPF.fixToW

/-- constructor of a type defined by a qpf -/
def Fix.mk (x : F (Fix F)) : Fix F :=
  Quot.mk _ (PFunctor.W.mk (q.P.map fixToW (repr x)))
#align qpf.fix.mk QPF.Fix.mk

/-- destructor of a type defined by a qpf -/
def Fix.dest : Fix F → F (Fix F) :=
  Fix.rec (Functor.map Fix.mk)
#align qpf.fix.dest QPF.Fix.dest

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
  rw [PFunctor.map_eq, recF_eq, ← PFunctor.map_eq, PFunctor.W.dest_mk, PFunctor.map_map, abs_map,
    ← h, abs_repr, this]
#align qpf.fix.rec_eq QPF.Fix.rec_eq

theorem Fix.ind_aux (a : q.P.A) (f : q.P.B a → q.P.W) :
    Fix.mk (abs ⟨a, fun x => ⟦f x⟧⟩) = ⟦⟨a, f⟩⟧ := by
  have : Fix.mk (abs ⟨a, fun x => ⟦f x⟧⟩) = ⟦Wrepr ⟨a, f⟩⟧ := by
    apply Quot.sound; apply Wequiv.abs'
    rw [PFunctor.W.dest_mk, abs_map, abs_repr, ← abs_map, PFunctor.map_eq]
    conv =>
      rhs
      simp only [Wrepr, recF_eq, PFunctor.W.dest_mk, abs_repr, Function.comp]
  rw [this]
  apply Quot.sound
  apply Wrepr_equiv
#align qpf.fix.ind_aux QPF.Fix.ind_aux

theorem Fix.ind_rec {α : Type u} (g₁ g₂ : Fix F → α)
    (h : ∀ x : F (Fix F), g₁ <$> x = g₂ <$> x → g₁ (Fix.mk x) = g₂ (Fix.mk x)) :
    ∀ x, g₁ x = g₂ x := by
  apply Quot.ind
  intro x
  induction' x with a f ih
  change g₁ ⟦⟨a, f⟩⟧ = g₂ ⟦⟨a, f⟩⟧
  rw [← Fix.ind_aux a f]; apply h
  rw [← abs_map, ← abs_map, PFunctor.map_eq, PFunctor.map_eq]
  congr with x
  apply ih
#align qpf.fix.ind_rec QPF.Fix.ind_rec

theorem Fix.rec_unique {α : Type u} (g : F α → α) (h : Fix F → α)
    (hyp : ∀ x, h (Fix.mk x) = g (h <$> x)) : Fix.rec g = h := by
  ext x
  apply Fix.ind_rec
  intro x hyp'
  rw [hyp, ← hyp', Fix.rec_eq]
#align qpf.fix.rec_unique QPF.Fix.rec_unique

theorem Fix.mk_dest (x : Fix F) : Fix.mk (Fix.dest x) = x := by
  change (Fix.mk ∘ Fix.dest) x = id x
  apply Fix.ind_rec (mk ∘ dest) id
  intro x
  rw [Function.comp_apply, id_eq, Fix.dest, Fix.rec_eq, id_map, comp_map]
  intro h
  rw [h]
#align qpf.fix.mk_dest QPF.Fix.mk_dest

theorem Fix.dest_mk (x : F (Fix F)) : Fix.dest (Fix.mk x) = x := by
  unfold Fix.dest; rw [Fix.rec_eq, ← Fix.dest, ← comp_map]
  conv =>
    rhs
    rw [← id_map x]
  congr with x
  apply Fix.mk_dest
#align qpf.fix.dest_mk QPF.Fix.dest_mk

theorem Fix.ind (p : Fix F → Prop) (h : ∀ x : F (Fix F), Liftp p x → p (Fix.mk x)) : ∀ x, p x := by
  apply Quot.ind
  intro x
  induction' x with a f ih
  change p ⟦⟨a, f⟩⟧
  rw [← Fix.ind_aux a f]
  apply h
  rw [liftp_iff]
  refine' ⟨_, _, rfl, _⟩
  convert ih
#align qpf.fix.ind QPF.Fix.ind

end QPF

/-
Construct the final coalgebra to a qpf.
-/
namespace QPF

variable {F : Type u → Type u} [Functor F] [q : QPF F]

open Functor (Liftp Liftr)

/-- does recursion on `q.P.M` using `g : α → F α` rather than `g : α → P α` -/
def corecF {α : Type _} (g : α → F α) : α → q.P.M :=
  PFunctor.M.corec fun x => repr (g x)
set_option linter.uppercaseLean3 false in
#align qpf.corecF QPF.corecF

theorem corecF_eq {α : Type _} (g : α → F α) (x : α) :
    PFunctor.M.dest (corecF g x) = q.P.map (corecF g) (repr (g x)) := by
  rw [corecF, PFunctor.M.dest_corec]
set_option linter.uppercaseLean3 false in
#align qpf.corecF_eq QPF.corecF_eq

-- Equivalence
/-- A pre-congruence on `q.P.M` *viewed as an F-coalgebra*. Not necessarily symmetric. -/
def IsPrecongr (r : q.P.M → q.P.M → Prop) : Prop :=
  ∀ ⦃x y⦄, r x y →
    abs (q.P.map (Quot.mk r) (PFunctor.M.dest x)) = abs (q.P.map (Quot.mk r) (PFunctor.M.dest y))
#align qpf.is_precongr QPF.IsPrecongr

/-- The maximal congruence on `q.P.M`. -/
def Mcongr : q.P.M → q.P.M → Prop := fun x y => ∃ r, IsPrecongr r ∧ r x y
set_option linter.uppercaseLean3 false in
#align qpf.Mcongr QPF.Mcongr

/-- coinductive type defined as the final coalgebra of a qpf -/
def Cofix (F : Type u → Type u) [Functor F] [q : QPF F] :=
  Quot (@Mcongr F _ q)
#align qpf.cofix QPF.Cofix

instance [Inhabited q.P.A] : Inhabited (Cofix F) :=
  ⟨Quot.mk _ default⟩

/-- corecursor for type defined by `Cofix` -/
def Cofix.corec {α : Type _} (g : α → F α) (x : α) : Cofix F :=
  Quot.mk _ (corecF g x)
#align qpf.cofix.corec QPF.Cofix.corec

/-- destructor for type defined by `Cofix` -/
def Cofix.dest : Cofix F → F (Cofix F) :=
  Quot.lift (fun x => Quot.mk Mcongr <$> abs (PFunctor.M.dest x))
    (by
      rintro x y ⟨r, pr, rxy⟩
      dsimp
      have : ∀ x y, r x y → Mcongr x y := by
        intro x y h
        exact ⟨r, pr, h⟩
      rw [← Quot.factor_mk_eq _ _ this]
      conv =>
        lhs
        rw [comp_map, ← abs_map, pr rxy, abs_map, ← comp_map])
#align qpf.cofix.dest QPF.Cofix.dest

theorem Cofix.dest_corec {α : Type u} (g : α → F α) (x : α) :
    Cofix.dest (Cofix.corec g x) = Cofix.corec g <$> g x := by
  conv =>
    lhs
    rw [Cofix.dest, Cofix.corec];
  dsimp
  rw [corecF_eq, abs_map, abs_repr, ← comp_map]; rfl
#align qpf.cofix.dest_corec QPF.Cofix.dest_corec

-- Porting note: Needed to add `(motive := _)` to get `Quot.inductionOn` to work
private theorem Cofix.bisim_aux (r : Cofix F → Cofix F → Prop) (h' : ∀ x, r x x)
    (h : ∀ x y, r x y → Quot.mk r <$> Cofix.dest x = Quot.mk r <$> Cofix.dest y) :
    ∀ x y, r x y → x = y := by
  intro x
  apply Quot.inductionOn (motive := _) x
  clear x
  intro x y
  apply Quot.inductionOn (motive := _) y
  clear y
  intro y rxy
  apply Quot.sound
  let r' x y := r (Quot.mk _ x) (Quot.mk _ y)
  have : IsPrecongr r' := by
    intro a b r'ab
    have h₀ :
      Quot.mk r <$> Quot.mk Mcongr <$> abs (PFunctor.M.dest a) =
        Quot.mk r <$> Quot.mk Mcongr <$> abs (PFunctor.M.dest b) :=
      h _ _ r'ab
    have h₁ : ∀ u v : q.P.M, Mcongr u v → Quot.mk r' u = Quot.mk r' v := by
      intro u v cuv
      apply Quot.sound
      simp only [r']
      rw [Quot.sound cuv]
      apply h'
    let f : Quot r → Quot r' :=
      Quot.lift (Quot.lift (Quot.mk r') h₁)
        (by
          intro c; apply Quot.inductionOn (motive := _) c; clear c
          intro c d; apply Quot.inductionOn (motive := _) d; clear d
          intro d rcd; apply Quot.sound; apply rcd)
    have : f ∘ Quot.mk r ∘ Quot.mk Mcongr = Quot.mk r' := rfl
    rw [← this, ← PFunctor.map_map _ _ f, ← PFunctor.map_map _ _ (Quot.mk r), abs_map, abs_map,
      abs_map, h₀]
    rw [← PFunctor.map_map _ _ f, ← PFunctor.map_map _ _ (Quot.mk r), abs_map, abs_map, abs_map]
  exact ⟨r', this, rxy⟩

theorem Cofix.bisim_rel (r : Cofix F → Cofix F → Prop)
    (h : ∀ x y, r x y → Quot.mk r <$> Cofix.dest x = Quot.mk r <$> Cofix.dest y) :
    ∀ x y, r x y → x = y := by
  let r' (x y) := x = y ∨ r x y
  intro x y rxy
  apply Cofix.bisim_aux r'
  · intro x
    left
    rfl
  · intro x y r'xy
    cases' r'xy with r'xy r'xy
    · rw [r'xy]
    have : ∀ x y, r x y → r' x y := fun x y h => Or.inr h
    rw [← Quot.factor_mk_eq _ _ this]
    dsimp [r']
    rw [@comp_map _ _ q _ _ _ (Quot.mk r), @comp_map _ _ q _ _ _ (Quot.mk r)]
    rw [h _ _ r'xy]
  right; exact rxy
#align qpf.cofix.bisim_rel QPF.Cofix.bisim_rel

theorem Cofix.bisim (r : Cofix F → Cofix F → Prop)
    (h : ∀ x y, r x y → Liftr r (Cofix.dest x) (Cofix.dest y)) : ∀ x y, r x y → x = y := by
  apply Cofix.bisim_rel
  intro x y rxy
  rcases (liftr_iff r _ _).mp (h x y rxy) with ⟨a, f₀, f₁, dxeq, dyeq, h'⟩
  rw [dxeq, dyeq, ← abs_map, ← abs_map, PFunctor.map_eq, PFunctor.map_eq]
  congr 2 with i
  apply Quot.sound
  apply h'
#align qpf.cofix.bisim QPF.Cofix.bisim

theorem Cofix.bisim' {α : Type*} (Q : α → Prop) (u v : α → Cofix F)
    (h : ∀ x, Q x → ∃ a f f', Cofix.dest (u x) = abs ⟨a, f⟩ ∧ Cofix.dest (v x) = abs ⟨a, f'⟩ ∧
      ∀ i, ∃ x', Q x' ∧ f i = u x' ∧ f' i = v x') :
    ∀ x, Q x → u x = v x := fun x Qx =>
  let R := fun w z : Cofix F => ∃ x', Q x' ∧ w = u x' ∧ z = v x'
  Cofix.bisim R
    (fun x y ⟨x', Qx', xeq, yeq⟩ => by
      rcases h x' Qx' with ⟨a, f, f', ux'eq, vx'eq, h'⟩
      rw [liftr_iff]
      exact ⟨a, f, f', xeq.symm ▸ ux'eq, yeq.symm ▸ vx'eq, h'⟩)
    _ _ ⟨x, Qx, rfl, rfl⟩
#align qpf.cofix.bisim' QPF.Cofix.bisim'

end QPF

/-
Composition of qpfs.
-/
namespace QPF

variable {F₂ : Type u → Type u} [Functor F₂] [q₂ : QPF F₂]
variable {F₁ : Type u → Type u} [Functor F₁] [q₁ : QPF F₁]

/-- composition of qpfs gives another qpf -/
def comp : QPF (Functor.Comp F₂ F₁) where
  P := PFunctor.comp q₂.P q₁.P
  abs {α} := by
    dsimp [Functor.Comp]
    intro p
    exact abs ⟨p.1.1, fun x => abs ⟨p.1.2 x, fun y => p.2 ⟨x, y⟩⟩⟩
  repr {α} := by
    dsimp [Functor.Comp]
    intro y
    refine' ⟨⟨(repr y).1, fun u => (repr ((repr y).2 u)).1⟩, _⟩
    dsimp [PFunctor.comp]
    intro x
    exact (repr ((repr y).2 x.1)).snd x.2
  abs_repr {α} := by
    dsimp [Functor.Comp]
    intro x
    conv =>
      rhs
      rw [← abs_repr x]
    cases' repr x with a f
    dsimp
    congr with x
    cases' h' : repr (f x) with b g
    dsimp; rw [← h', abs_repr]
  abs_map {α β} f := by
    dsimp (config := { unfoldPartialApp := true }) [Functor.Comp, PFunctor.comp]
    intro p
    cases' p with a g; dsimp
    cases' a with b h; dsimp
    symm
    trans
    symm
    apply abs_map
    congr
    rw [PFunctor.map_eq]
    dsimp [Function.comp_def]
    congr
    ext x
    rw [← abs_map]
    rfl
#align qpf.comp QPF.comp

end QPF

/-
Quotients.

We show that if `F` is a qpf and `G` is a suitable quotient of `F`, then `G` is a qpf.
-/
namespace QPF

variable {F : Type u → Type u} [Functor F] [q : QPF F]
variable {G : Type u → Type u} [Functor G]
variable {FG_abs : ∀ {α}, F α → G α}
variable {FG_repr : ∀ {α}, G α → F α}

/-- Given a qpf `F` and a well-behaved surjection `FG_abs` from `F α` to
functor `G α`, `G` is a qpf. We can consider `G` a quotient on `F` where
elements `x y : F α` are in the same equivalence class if
`FG_abs x = FG_abs y`. -/
def quotientQPF (FG_abs_repr : ∀ {α} (x : G α), FG_abs (FG_repr x) = x)
    (FG_abs_map : ∀ {α β} (f : α → β) (x : F α), FG_abs (f <$> x) = f <$> FG_abs x) : QPF G where
  P := q.P
  abs {α} p := FG_abs (abs p)
  repr {α} x := repr (FG_repr x)
  abs_repr {α} x := by simp only; rw [abs_repr, FG_abs_repr]
  abs_map {α β} f x := by simp only; rw [abs_map, FG_abs_map]
#align qpf.quotient_qpf QPF.quotientQPF

end QPF

/-
Support.
-/
namespace QPF

variable {F : Type u → Type u} [Functor F] [q : QPF F]

open Functor (Liftp Liftr supp)

open Set

theorem mem_supp {α : Type u} (x : F α) (u : α) :
    u ∈ supp x ↔ ∀ a f, abs ⟨a, f⟩ = x → u ∈ f '' univ := by
  rw [supp]; dsimp; constructor
  · intro h a f haf
    have : Liftp (fun u => u ∈ f '' univ) x := by
      rw [liftp_iff]
      exact ⟨a, f, haf.symm, fun i => mem_image_of_mem _ (mem_univ _)⟩
    exact h this
  intro h p; rw [liftp_iff]
  rintro ⟨a, f, xeq, h'⟩
  rcases h a f xeq.symm with ⟨i, _, hi⟩
  rw [← hi]; apply h'
#align qpf.mem_supp QPF.mem_supp

theorem supp_eq {α : Type u} (x : F α) :
    supp x = { u | ∀ a f, abs ⟨a, f⟩ = x → u ∈ f '' univ } := by
  ext
  apply mem_supp
#align qpf.supp_eq QPF.supp_eq

theorem has_good_supp_iff {α : Type u} (x : F α) :
    (∀ p, Liftp p x ↔ ∀ u ∈ supp x, p u) ↔
      ∃ a f, abs ⟨a, f⟩ = x ∧ ∀ a' f', abs ⟨a', f'⟩ = x → f '' univ ⊆ f' '' univ := by
  constructor
  · intro h
    have : Liftp (supp x) x := by rw [h]; intro u; exact id
    rw [liftp_iff] at this
    rcases this with ⟨a, f, xeq, h'⟩
    refine' ⟨a, f, xeq.symm, _⟩
    intro a' f' h''
    rintro u ⟨i, _, hfi⟩
    have : u ∈ supp x := by rw [← hfi]; apply h'
    exact (mem_supp x u).mp this _ _ h''
  rintro ⟨a, f, xeq, h⟩ p; rw [liftp_iff]; constructor
  · rintro ⟨a', f', xeq', h'⟩ u usuppx
    rcases (mem_supp x u).mp usuppx a' f' xeq'.symm with ⟨i, _, f'ieq⟩
    rw [← f'ieq]
    apply h'
  intro h'
  refine' ⟨a, f, xeq.symm, _⟩; intro i
  apply h'; rw [mem_supp]
  intro a' f' xeq'
  apply h a' f' xeq'
  apply mem_image_of_mem _ (mem_univ _)
#align qpf.has_good_supp_iff QPF.has_good_supp_iff

/-- A qpf is said to be uniform if every polynomial functor
representing a single value all have the same range. -/
def IsUniform : Prop :=
  ∀ ⦃α : Type u⦄ (a a' : q.P.A) (f : q.P.B a → α) (f' : q.P.B a' → α),
    abs ⟨a, f⟩ = abs ⟨a', f'⟩ → f '' univ = f' '' univ
#align qpf.is_uniform QPF.IsUniform

/-- does `abs` preserve `Liftp`? -/
def LiftpPreservation : Prop :=
  ∀ ⦃α⦄ (p : α → Prop) (x : q.P α), Liftp p (abs x) ↔ Liftp p x
#align qpf.liftp_preservation QPF.LiftpPreservation

/-- does `abs` preserve `supp`? -/
def SuppPreservation : Prop :=
  ∀ ⦃α⦄ (x : q.P α), supp (abs x) = supp x
#align qpf.supp_preservation QPF.SuppPreservation

theorem supp_eq_of_isUniform (h : q.IsUniform) {α : Type u} (a : q.P.A) (f : q.P.B a → α) :
    supp (abs ⟨a, f⟩) = f '' univ := by
  ext u; rw [mem_supp]; constructor
  · intro h'
    apply h' _ _ rfl
  intro h' a' f' e
  rw [← h _ _ _ _ e.symm]; apply h'
#align qpf.supp_eq_of_is_uniform QPF.supp_eq_of_isUniform

theorem liftp_iff_of_isUniform (h : q.IsUniform) {α : Type u} (x : F α) (p : α → Prop) :
    Liftp p x ↔ ∀ u ∈ supp x, p u := by
  rw [liftp_iff, ← abs_repr x]
  cases' repr x with a f; constructor
  · rintro ⟨a', f', abseq, hf⟩ u
    rw [supp_eq_of_isUniform h, h _ _ _ _ abseq]
    rintro ⟨i, _, hi⟩
    rw [← hi]
    apply hf
  intro h'
  refine' ⟨a, f, rfl, fun i => h' _ _⟩
  rw [supp_eq_of_isUniform h]
  exact ⟨i, mem_univ i, rfl⟩
#align qpf.liftp_iff_of_is_uniform QPF.liftp_iff_of_isUniform

theorem supp_map (h : q.IsUniform) {α β : Type u} (g : α → β) (x : F α) :
    supp (g <$> x) = g '' supp x := by
  rw [← abs_repr x]; cases' repr x with a f; rw [← abs_map, PFunctor.map_eq]
  rw [supp_eq_of_isUniform h, supp_eq_of_isUniform h, image_comp]
#align qpf.supp_map QPF.supp_map

theorem suppPreservation_iff_uniform : q.SuppPreservation ↔ q.IsUniform := by
  constructor
  · intro h α a a' f f' h'
    rw [← PFunctor.supp_eq, ← PFunctor.supp_eq, ← h, h', h]
  · rintro h α ⟨a, f⟩
    rwa [supp_eq_of_isUniform, PFunctor.supp_eq]
#align qpf.supp_preservation_iff_uniform QPF.suppPreservation_iff_uniform

theorem suppPreservation_iff_liftpPreservation : q.SuppPreservation ↔ q.LiftpPreservation := by
  constructor <;> intro h
  · rintro α p ⟨a, f⟩
    have h' := h
    rw [suppPreservation_iff_uniform] at h'
    dsimp only [SuppPreservation, supp] at h
    rw [liftp_iff_of_isUniform h', supp_eq_of_isUniform h', PFunctor.liftp_iff']
    simp only [image_univ, mem_range, exists_imp]
    constructor <;> intros <;> subst_vars <;> solve_by_elim
  · rintro α ⟨a, f⟩
    simp only [LiftpPreservation] at h
    simp only [supp, h]
#align qpf.supp_preservation_iff_liftp_preservation QPF.suppPreservation_iff_liftpPreservation

theorem liftpPreservation_iff_uniform : q.LiftpPreservation ↔ q.IsUniform := by
  rw [← suppPreservation_iff_liftpPreservation, suppPreservation_iff_uniform]
#align qpf.liftp_preservation_iff_uniform QPF.liftpPreservation_iff_uniform

end QPF
