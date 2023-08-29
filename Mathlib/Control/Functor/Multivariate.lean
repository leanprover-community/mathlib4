/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
import Mathlib.Data.Fin.Fin2
import Mathlib.Data.TypeVec

#align_import control.functor.multivariate from "leanprover-community/mathlib"@"008205aa645b3f194c1da47025c5f110c8406eab"

/-!

Functors between the category of tuples of types, and the category Type

Features:

`MvFunctor n` : the type class of multivariate functors
`f <$$> x`    : notation for map

-/


universe u v w

open MvFunctor

/-- Multivariate functors, i.e. functor between the category of type vectors
and the category of Type -/
class MvFunctor {n : ℕ} (F : TypeVec n → Type*) where
  /-- Multivariate map, if `f : α ⟹ β` and `x : F α` then `f <$$> x : F β`. -/
  map : ∀ {α β : TypeVec n}, α ⟹ β → F α → F β
#align mvfunctor MvFunctor

/-- Multivariate map, if `f : α ⟹ β` and `x : F α` then `f <$$> x : F β` -/
scoped[MvFunctor] infixr:100 " <$$> " => MvFunctor.map

variable {n : ℕ}

namespace MvFunctor

variable {α β γ : TypeVec.{u} n} {F : TypeVec.{u} n → Type v} [MvFunctor F]

/-- predicate lifting over multivariate functors -/
def LiftP {α : TypeVec n} (P : ∀ i, α i → Prop) (x : F α) : Prop :=
  ∃ u : F (fun i => Subtype (P i)), (fun i => @Subtype.val _ (P i)) <$$> u = x
#align mvfunctor.liftp MvFunctor.LiftP

/-- relational lifting over multivariate functors -/
def LiftR {α : TypeVec n} (R : ∀ {i}, α i → α i → Prop) (x y : F α) : Prop :=
  ∃ u : F (fun i => { p : α i × α i // R p.fst p.snd }),
    (fun i (t : { p : α i × α i // R p.fst p.snd }) => t.val.fst) <$$> u = x ∧
      (fun i (t : { p : α i × α i // R p.fst p.snd }) => t.val.snd) <$$> u = y
#align mvfunctor.liftr MvFunctor.LiftR

/-- given `x : F α` and a projection `i` of type vector `α`, `supp x i` is the set
of `α.i` contained in `x` -/
def supp {α : TypeVec n} (x : F α) (i : Fin2 n) : Set (α i) :=
  { y : α i | ∀ ⦃P⦄, LiftP P x → P i y }
#align mvfunctor.supp MvFunctor.supp

theorem of_mem_supp {α : TypeVec n} {x : F α} {P : ∀ ⦃i⦄, α i → Prop} (h : LiftP P x) (i : Fin2 n) :
    ∀ y ∈ supp x i, P y := fun _y hy => hy h
#align mvfunctor.of_mem_supp MvFunctor.of_mem_supp

end MvFunctor



/-- laws for `MvFunctor` -/
class LawfulMvFunctor {n : ℕ} (F : TypeVec n → Type*) [MvFunctor F] : Prop where
  /-- `map` preserved identities, i.e., maps identity on `α` to identity on `F α` -/
  id_map : ∀ {α : TypeVec n} (x : F α), TypeVec.id <$$> x = x
  /-- `map` preserves compositions -/
  comp_map :
    ∀ {α β γ : TypeVec n} (g : α ⟹ β) (h : β ⟹ γ) (x : F α), (h ⊚ g) <$$> x = h <$$> g <$$> x
#align is_lawful_mvfunctor LawfulMvFunctor

open Nat TypeVec

namespace MvFunctor

export LawfulMvFunctor (comp_map)

open LawfulMvFunctor

variable {α β γ : TypeVec.{u} n}

variable {F : TypeVec.{u} n → Type v} [MvFunctor F]

variable (P : α ⟹ «repeat» n Prop) (R : α ⊗ α ⟹ «repeat» n Prop)

/-- adapt `MvFunctor.LiftP` to accept predicates as arrows -/
def LiftP' : F α → Prop :=
  MvFunctor.LiftP fun i x => ofRepeat <| P i x
#align mvfunctor.liftp' MvFunctor.LiftP'


/-- adapt `MvFunctor.LiftR` to accept relations as arrows -/
def LiftR' : F α → F α → Prop :=
  MvFunctor.LiftR @fun i x y => ofRepeat <| R i <| TypeVec.prod.mk _ x y
#align mvfunctor.liftr' MvFunctor.LiftR'

variable [LawfulMvFunctor F]

@[simp]
theorem id_map (x : F α) : TypeVec.id <$$> x = x :=
  LawfulMvFunctor.id_map x
#align mvfunctor.id_map MvFunctor.id_map

@[simp]
theorem id_map' (x : F α) : (fun _i a => a) <$$> x = x :=
  id_map x
#align mvfunctor.id_map' MvFunctor.id_map'

theorem map_map (g : α ⟹ β) (h : β ⟹ γ) (x : F α) : h <$$> g <$$> x = (h ⊚ g) <$$> x :=
  Eq.symm <| comp_map _ _ _
#align mvfunctor.map_map MvFunctor.map_map

section LiftP'

variable (F)

theorem exists_iff_exists_of_mono {P : F α → Prop} {q : F β → Prop}
                                  (f : α ⟹ β) (g : β ⟹ α)
                                  (h₀ : f ⊚ g = TypeVec.id)
                                  (h₁ : ∀ u : F α, P u ↔ q (f <$$> u)) :
      (∃ u : F α, P u) ↔ ∃ u : F β, q u := by
  constructor <;> rintro ⟨u, h₂⟩
  -- ⊢ (∃ u, P u) → ∃ u, q u
                  -- ⊢ ∃ u, q u
                  -- ⊢ ∃ u, P u
  · refine ⟨f <$$> u, ?_⟩
    -- ⊢ q (f <$$> u)
    apply (h₁ u).mp h₂
    -- 🎉 no goals
  · refine ⟨g <$$> u, ?_⟩
    -- ⊢ P (g <$$> u)
    apply (h₁ _).mpr _
    -- ⊢ q (f <$$> g <$$> u)
    simp only [MvFunctor.map_map, h₀, LawfulMvFunctor.id_map, h₂]
    -- 🎉 no goals
#align mvfunctor.exists_iff_exists_of_mono MvFunctor.exists_iff_exists_of_mono

variable {F}

theorem LiftP_def (x : F α) : LiftP' P x ↔ ∃ u : F (Subtype_ P), subtypeVal P <$$> u = x :=
  exists_iff_exists_of_mono F _ _ (toSubtype_of_subtype P) (by simp [MvFunctor.map_map])
                                                               -- 🎉 no goals
#align mvfunctor.liftp_def MvFunctor.LiftP_def

theorem LiftR_def (x y : F α) :
    LiftR' R x y ↔
      ∃ u : F (Subtype_ R),
        (TypeVec.prod.fst ⊚ subtypeVal R) <$$> u = x ∧
          (TypeVec.prod.snd ⊚ subtypeVal R) <$$> u = y :=
  exists_iff_exists_of_mono _ _ _ (toSubtype'_of_subtype' R)
    (by simp only [map_map, comp_assoc, subtypeVal_toSubtype']; simp [comp])
        -- ⊢ ∀ (u : F fun i => { p // (fun i x y => ofRepeat (R i (prod.mk i x y))) i p.f …
                                                                -- 🎉 no goals
#align mvfunctor.liftr_def MvFunctor.LiftR_def

end LiftP'

end MvFunctor

open Nat

namespace MvFunctor

open TypeVec

section LiftPLastPredIff

variable {F : TypeVec.{u} (n + 1) → Type*} [MvFunctor F] [LawfulMvFunctor F] {α : TypeVec.{u} n}

open MvFunctor

variable {β : Type u}

variable (pp : β → Prop)

private def f :
    ∀ n α,
      (fun i : Fin2 (n + 1) => { p_1 // ofRepeat (PredLast' α pp i p_1) }) ⟹ fun i : Fin2 (n + 1) =>
        { p_1 : (α ::: β) i // PredLast α pp p_1 }
  | _, α, Fin2.fs i, x =>
    ⟨x.val, cast (by simp only [PredLast]; erw [const_iff_true]) x.property⟩
                     -- ⊢ ofRepeat (PredLast' α pp (Fin2.fs i) ↑x) = True
                                           -- 🎉 no goals
  | _, α, Fin2.fz, x => ⟨x.val, x.property⟩

private def g :
    ∀ n α,
      (fun i : Fin2 (n + 1) => { p_1 : (α ::: β) i // PredLast α pp p_1 }) ⟹ fun i : Fin2 (n + 1) =>
        { p_1 // ofRepeat (PredLast' α pp i p_1) }
  | _, α, Fin2.fs i, x =>
    ⟨x.val, cast (by simp only [PredLast]; erw [const_iff_true]) x.property⟩
                     -- ⊢ True = ofRepeat (PredLast' α pp (Fin2.fs i) ↑x)
                                           -- 🎉 no goals
  | _, α, Fin2.fz, x => ⟨x.val, x.property⟩

theorem LiftP_PredLast_iff {β} (P : β → Prop) (x : F (α ::: β)) :
    LiftP' (PredLast' _ P) x ↔ LiftP (PredLast _ P) x := by
  dsimp only [LiftP, LiftP']
  -- ⊢ (∃ u, (fun i => Subtype.val) <$$> u = x) ↔ ∃ u, (fun i => Subtype.val) <$$>  …
  apply exists_iff_exists_of_mono F (f _ n α) (g _ n α)
  -- ⊢ MvFunctor.f P n α ⊚ MvFunctor.g P n α = TypeVec.id
  · ext i ⟨x, _⟩
    -- ⊢ ↑((MvFunctor.f P n α ⊚ MvFunctor.g P n α) i { val := x, property := property …
    cases i <;> rfl
    -- ⊢ ↑((MvFunctor.f P n α ⊚ MvFunctor.g P n α) Fin2.fz { val := x, property := pr …
                -- 🎉 no goals
                -- 🎉 no goals
  · intros
    -- ⊢ (fun i => Subtype.val) <$$> u✝ = x ↔ (fun i => Subtype.val) <$$> MvFunctor.f …
    rw [MvFunctor.map_map]
    -- ⊢ (fun i => Subtype.val) <$$> u✝ = x ↔ ((fun i => Subtype.val) ⊚ MvFunctor.f P …
    dsimp [(· ⊚ ·)]
    -- ⊢ (fun i => Subtype.val) <$$> u✝ = x ↔ (fun i x => ↑(MvFunctor.f P n α i x)) < …
    suffices (fun i => Subtype.val) = (fun i x => (MvFunctor.f P n α i x).val)
      by rw[this];
    ext i ⟨x, _⟩
    -- ⊢ ↑{ val := x, property := property✝ } = ↑(MvFunctor.f P n α i { val := x, pro …
    cases i <;> rfl
    -- ⊢ ↑{ val := x, property := property✝ } = ↑(MvFunctor.f P n α Fin2.fz { val :=  …
                -- 🎉 no goals
                -- 🎉 no goals
#align mvfunctor.liftp_last_pred_iff MvFunctor.LiftP_PredLast_iff

open Function

variable (rr : β → β → Prop)

private def f' :
    ∀ n α,
      (fun i : Fin2 (n + 1) =>
          { p_1 : _ × _ // ofRepeat (RelLast' α rr i (TypeVec.prod.mk _ p_1.fst p_1.snd)) }) ⟹
        fun i : Fin2 (n + 1) => { p_1 : (α ::: β) i × _ // RelLast α rr p_1.fst p_1.snd }
  | _, α, Fin2.fs i, x =>
    ⟨x.val, cast (by simp only [RelLast]; erw [repeatEq_iff_eq]) x.property⟩
                     -- ⊢ ofRepeat (RelLast' α rr (Fin2.fs i) (prod.mk (Fin2.fs i) (↑x).fst (↑x).snd)) …
                                          -- 🎉 no goals
  | _, α, Fin2.fz, x => ⟨x.val, x.property⟩

private def g' :
    ∀ n α,
      (fun i : Fin2 (n + 1) => { p_1 : (α ::: β) i × _ // RelLast α rr p_1.fst p_1.snd }) ⟹
        fun i : Fin2 (n + 1) =>
        { p_1 : _ × _ // ofRepeat (RelLast' α rr i (TypeVec.prod.mk _ p_1.1 p_1.2)) }
  | _, α, Fin2.fs i, x =>
    ⟨x.val, cast (by simp only [RelLast]; erw [repeatEq_iff_eq]) x.property⟩
                     -- ⊢ ((↑x).fst = (↑x).snd) = ofRepeat (RelLast' α rr (Fin2.fs i) (prod.mk (Fin2.f …
                                          -- 🎉 no goals
  | _, α, Fin2.fz, x => ⟨x.val, x.property⟩

theorem LiftR_RelLast_iff (x y : F (α ::: β)) :
    LiftR' (RelLast' _ rr) x y ↔ LiftR (RelLast (i := _) _ rr) x y := by
  dsimp only [LiftR, LiftR']
  -- ⊢ (∃ u, (fun i t => (↑t).fst) <$$> u = x ∧ (fun i t => (↑t).snd) <$$> u = y) ↔ …
  apply exists_iff_exists_of_mono F (f' rr _ _) (g' rr _ _)
  -- ⊢ MvFunctor.f' rr n α ⊚ MvFunctor.g' rr n α = TypeVec.id
  · ext i ⟨x, _⟩ : 2
    -- ⊢ (MvFunctor.f' rr n α ⊚ MvFunctor.g' rr n α) i { val := x, property := proper …
    cases i <;> rfl
    -- ⊢ (MvFunctor.f' rr n α ⊚ MvFunctor.g' rr n α) Fin2.fz { val := x, property :=  …
                -- 🎉 no goals
                -- 🎉 no goals
  · intros
    -- ⊢ (fun i t => (↑t).fst) <$$> u✝ = x ∧ (fun i t => (↑t).snd) <$$> u✝ = y ↔ (fun …
    simp [MvFunctor.map_map, (· ⊚ ·)]
    -- ⊢ (fun i t => (↑t).fst) <$$> u✝ = x ∧ (fun i t => (↑t).snd) <$$> u✝ = y ↔ (fun …
    -- porting note: proof was
    -- rw [MvFunctor.map_map, MvFunctor.map_map, (· ⊚ ·), (· ⊚ ·)]
    -- congr <;> ext i ⟨x, _⟩ <;> cases i <;> rfl
    suffices  (fun i t => t.val.fst) = ((fun i x => (MvFunctor.f' rr n α i x).val.fst))
            ∧ (fun i t => t.val.snd) = ((fun i x => (MvFunctor.f' rr n α i x).val.snd))
    by  rcases this with ⟨left, right⟩
        rw[left, right];
    constructor <;> ext i ⟨x, _⟩ <;> cases i <;> rfl
    -- ⊢ (fun i t => (↑t).fst) = fun i x => (↑(MvFunctor.f' rr n α i x)).fst
                    -- ⊢ (↑{ val := x, property := property✝ }).fst = (↑(MvFunctor.f' rr n α i { val  …
                    -- ⊢ (↑{ val := x, property := property✝ }).snd = (↑(MvFunctor.f' rr n α i { val  …
                                     -- ⊢ (↑{ val := x, property := property✝ }).fst = (↑(MvFunctor.f' rr n α Fin2.fz  …
                                     -- ⊢ (↑{ val := x, property := property✝ }).snd = (↑(MvFunctor.f' rr n α Fin2.fz  …
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
#align mvfunctor.liftr_last_rel_iff MvFunctor.LiftR_RelLast_iff

end LiftPLastPredIff

end MvFunctor
