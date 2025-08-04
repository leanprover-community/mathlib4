/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
import Mathlib.Data.PFunctor.Multivariate.Basic
import Mathlib.Data.PFunctor.Univariate.M
import Mathlib.Tactic.DepRewrite

/-!
# The M construction as a multivariate polynomial functor.

M types are potentially infinite tree-like structures. They are defined
as the greatest fixpoint of a polynomial functor.

## Main definitions

* `M.mk`     - constructor
* `M.dest`   - destructor
* `M.corec`  - corecursor: useful for formulating infinite, productive computations
* `M.bisim`  - bisimulation: proof technique to show the equality of infinite objects

## Implementation notes

Dual view of M-types:

* `mp`: polynomial functor
* `M`: greatest fixed point of a polynomial functor

Specifically, we define the polynomial functor `mp` as:

* A := a possibly infinite tree-like structure without information in the nodes
* B := given the tree-like structure `t`, `B t` is a valid path
  from the root of `t` to any given node.

As a result `mp α` is made of a dataless tree and a function from
its valid paths to values of `α`

The difference with the polynomial functor of an initial algebra is
that `A` is a possibly infinite tree.

## Reference

* Jeremy Avigad, Mario M. Carneiro and Simon Hudon.
  [*Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/

theorem congr_heq' {α₁ α₂ β₁ β₂ : Sort _} {f : α₁ → β₁} {g : α₂ → β₂} {x : α₁} {y : α₂}
    (h₀ : β₁ = β₂) (h₁ : f ≍ g) (h₂ : x ≍ y) : f x ≍ g y := by
  cases h₀; exact heq_of_eq <| congr_heq h₁ h₂

theorem dcongr_heq
    {α₁ α₂ : Sort _}
    {β₁ : α₁ → Sort _}
    {β₂ : α₂ → Sort _}
    {f₁ : ∀ a, β₁ a}
    {f₂ : ∀ a, β₂ a}
    {a₁ : α₁} {a₂ : α₂}
    (hat : α₁ = α₂)
    (ht : ∀ a₁ a₂, a₁ ≍ a₂ → β₁ a₁ = β₂ a₂)
    (hf : β₁ ≍ β₂ → f₁ ≍ f₂)
    (hargs : a₁ ≍ a₂)
    : f₁ a₁ ≍ f₂ a₂ := by
  subst hat
  obtain rfl : β₁ = β₂ := funext fun v => ht v v .rfl
  rw [eq_of_heq hargs, eq_of_heq <| hf .rfl]

universe u v

open MvFunctor

namespace MvPFunctor

open TypeVec

variable {n : ℕ} (P : MvPFunctor.{u} (n + 1))

/-- A path from the root of a tree to one of its node
    It takes data from a univariate cofixpoint (alg) and
    follows it through the focus'th constructor argument.
-/
inductive M.Path : (alg : P.last.M) → (focus : Fin2 n) → Type u
  | root (x : P.last.M)
          (a : P.A)
          (f : P.last.B a → P.last.M)
          (h : PFunctor.M.dest x = ⟨a, f⟩)
          (i : Fin2 n)
          (c : P.drop.B a i) : M.Path x i
  | child (x : P.last.M)
          (a : P.A)
          (f : P.last.B a → P.last.M)
          (h : PFunctor.M.dest x = ⟨a, f⟩)
          (j : P.last.B a)
          (i : Fin2 n)
          (c : M.Path (f j) i) : M.Path x i

instance M.Path.inhabited (x : P.last.M) {i} [Inhabited (P.drop.B x.head i)] :
    Inhabited (M.Path P x i) :=
  let a := PFunctor.M.head x
  let f := PFunctor.M.children x
  ⟨M.Path.root _ a f
      (PFunctor.M.casesOn' x
        (r := fun _ => PFunctor.M.dest x = ⟨a, f⟩)
        <| by
        intros; simp [a]; rfl)
      _ default⟩

/-- Polynomial functor of the M-type of `P`. `A` is a data-less
possibly infinite tree whereas, for a given `a : A`, `B a` is a valid
path in tree `a` so that `mp α` is made of a tree and a function
from its valid paths to the values it contains -/
def mp : MvPFunctor n where
  A := P.last.M
  B := M.Path P

/-- `n`-ary M-type for `P` -/
def M (α : TypeVec n) : Type _ :=
  P.mp α

instance mvfunctorM : MvFunctor P.M := by delta M; infer_instance

instance inhabitedM {α : TypeVec _} [I : Inhabited P.A] [∀ i : Fin2 n, Inhabited (α i)] :
    Inhabited (P.M α) :=
  @Obj.inhabited _ (mp P) _ (@PFunctor.M.inhabited P.last I) _

/-- construct through corecursion the shape of an M-type
without its contents -/
def M.corecShape {β : Type v}
    (gen_head : β → P.A)
    (gen_body : ∀ b : β, P.last.B (gen_head b) → β) :
    β → P.last.M :=
  PFunctor.M.corec fun (b : β) => ⟨gen_head b, gen_body b⟩

/-- Proof of type equality as an arrow -/
def castDropB {a a' : P.A} (h : a = a') : P.drop.B a ⟹ P.drop.B a' := fun _i b => Eq.recOn h b

/-- Proof of type equality as a function -/
def castLastB {a a' : P.A} (h : a = a') : P.last.B a → P.last.B a' := fun b => Eq.recOn h b

/-- Using corecursion, construct the contents of an M-type -/
def M.corecContents {α : TypeVec.{u} n}
    {β : Type v}
    (gen_head : β → P.A)
    (gen_base : ∀ b : β, P.drop.B (gen_head b) ⟹ α)
    (gen_cfix : ∀ b : β, P.last.B (gen_head b) → β)
    -- TODO: Try to replace this `x` with an inline usage
    (x : P.last.M)
    (start : β)
    (h : x = M.corecShape P gen_head gen_cfix start) :
    M.Path P x ⟹ α
  | _, M.Path.root x a f h' i c =>
    have : a = gen_head start := by
      rw [h, M.corecShape, PFunctor.M.dest_corec] at h'
      cases h'
      rfl
    gen_base start i (P.castDropB this i c)
  | _, M.Path.child x a f h' j i c =>
    have h₀ : a = gen_head start := by
      rw [h, M.corecShape, PFunctor.M.dest_corec] at h'
      cases h'
      rfl
    have h₁ : f j = M.corecShape P gen_head gen_cfix (gen_cfix start (castLastB P h₀ j)) := by
      rw [h, M.corecShape, PFunctor.M.dest_corec] at h'
      cases h'
      rfl
    M.corecContents gen_head gen_base gen_cfix (f j) (gen_cfix start (P.castLastB h₀ j)) h₁ i c

/-- Corecursor for M-type of `P` -/
def M.corec' {α : TypeVec n} {β : Type v}
    (gen_head : β → P.A)
    (gen_base : ∀ b : β, P.drop.B (gen_head b) ⟹ α)
    (gen_cfix : ∀ b : β, P.last.B (gen_head b) → β) : β → P.M α := fun b =>
  ⟨
    M.corecShape P gen_head gen_cfix b,
    M.corecContents P gen_head gen_base gen_cfix _ _ rfl
  ⟩

def M.corecU
    {α : TypeVec.{u} n} {β : Type v}
    (gen : β → P.uLift (α.uLift.append1 <| ULift.{u, v} β))
    : β → P.M α :=
  M.corec' P
    (gen · |>.fst.down)
    (gen · |>.snd |> dropFun |>.uLift_arrow)
    (fun x => (.up · |> (gen x |>.snd |> lastFun) |>.down))

def gen_fn {P : _} {α : TypeVec.{u} n} {β : Type u} (gen : β → P (α.append1 β))
    : β → uLift P (TypeVec.uLift α ::: ULift β) :=
  /- (uLift_append1_ULift_uLift.symm ▸ uLift_up.{u, u} P <| gen ·) -/
  (cast (congr rfl uLift_append1_ULift_uLift.symm) <| uLift_up.{u, u} P <| gen ·)

theorem gen_fn_fst {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : TypeVec.{u} n} {β : Type u}
    (g : β → P (α ::: β)) (x : β)
    : (gen_fn g x).fst.down = (g x).fst := by
  apply eq_of_heq
  apply HEq.trans (b := (P.uLift_up (g x)).fst.down)
  · congr!
    · exact uLift_append1_ULift_uLift
    · apply cast_heq
  · rfl

/-- Corecursor for M-type of `P` -/
def M.corec {α : TypeVec.{u} n} {β : Type u} (gen : β → P (α.append1 β)) : β → P.M α :=
  M.corecU P (gen_fn gen)

/-- Implementation of destructor for M-type of `P` -/
def M.pathDestLeft {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a → P.last.M}
    (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) : P.drop.B a ⟹ α := fun i c =>
  f' i (M.Path.root x a f h i c)

/-- Implementation of destructor for M-type of `P` -/
def M.pathDestRight {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a → P.last.M}
    (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) :
    ∀ j : P.last.B a, M.Path P (f j) ⟹ α := fun j i c => f' i (M.Path.child x a f h j i c)

/-- Destructor for M-type of `P` -/
def M.dest' {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a → P.last.M}
    (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) : P (α.append1 (P.M α)) :=
  ⟨a, splitFun (M.pathDestLeft P h f') fun x => ⟨f x, M.pathDestRight P h f' x⟩⟩

/-- Destructor for M-types -/
def M.dest {α : TypeVec n} (x : P.M α) : P (α ::: P.M α) :=
  M.dest' P (Sigma.eta <| PFunctor.M.dest x.fst).symm x.snd

/-- Constructor for M-types -/
def M.mk {α : TypeVec n} : P (α.append1 (P.M α)) → P.M α :=
  M.corec _ fun i => appendFun id (M.dest P) <$$> i

theorem M.dest'_eq_dest' {α : TypeVec n} {x : P.last.M} {a₁ : P.A}
    {f₁ : P.last.B a₁ → P.last.M} (h₁ : PFunctor.M.dest x = ⟨a₁, f₁⟩) {a₂ : P.A}
    {f₂ : P.last.B a₂ → P.last.M} (h₂ : PFunctor.M.dest x = ⟨a₂, f₂⟩) (f' : M.Path P x ⟹ α) :
    M.dest' P h₁ f' = M.dest' P h₂ f' := by cases h₁.symm.trans h₂; rfl

theorem M.dest_eq_dest' {α : TypeVec n} {x : P.last.M} {a : P.A}
    {f : P.last.B a → P.last.M} (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) :
    M.dest P ⟨x, f'⟩ = M.dest' P h f' :=
  M.dest'_eq_dest' _ _ _ _

theorem M.dest_corec' {α : TypeVec.{u} n} {β : Type v} (g₀ : β → P.A)
    (g₁ : ∀ b : β, P.drop.B (g₀ b) ⟹ α) (g₂ : ∀ b : β, P.last.B (g₀ b) → β) (x : β) :
    M.dest P (M.corec' P g₀ g₁ g₂ x) = ⟨g₀ x, splitFun (g₁ x) (M.corec' P g₀ g₁ g₂ ∘ g₂ x)⟩ :=
  rfl

theorem M.dest_corecU {α : TypeVec n} {β : Type v}
    (g : β → P.uLift (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β))
    (x : β) :
    M.dest P (M.corecU P g x) =
      (P.uLift_down <|
      (Arrow.uLift_up ⊚ (Arrow.uLift_down ::: (M.corecU P g ·.down))) <$$> g x) := by
  trans
  · apply M.dest_corec'
  dsimp only
  rw [←Sigma.eta (g x)]
  dsimp only
  rw [MvPFunctor.map_eq]
  congr 1
  change splitFun _ (_ ∘ (ULift.down ∘ lastFun (g x).snd ∘ ULift.up)) = _
  conv =>
    lhs; rhs; lhs; rhs
    change fun x ↦ ULift.down ∘ (lastFun (g x).snd) ∘ ULift.up
  conv_rhs => rw [← split_dropFun_lastFun (g x).snd, ] 
  rw [Arrow.uLift_up_splitFun, comp_assoc,
    appendFun_comp_splitFun,
    ← splitFun_comp, ←comp_assoc,
    Arrow.uLift_up_down, id_comp]
  dsimp
  rw [Arrow.uLift_arrow_splitFun]
  rfl


instance heq_setoid {t : Sort u} : Setoid t :=
  ⟨ (· ≍ ·), ⟨ HEq.refl, _root_.id ∘ HEq.symm, HEq.trans ⟩ ⟩


theorem gen_snd {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : TypeVec.{u} n} {β : Type u}
    (g : β → P (α ::: β)) (x : β) : (gen_fn g x).snd ≍ (P.uLift_up (g x)).snd := by
  apply dcongr_heq
  · rw [uLift_append1_ULift_uLift]
  · congr!
    <;> rw [uLift_append1_ULift_uLift]
  · intro heq
    congr!
    rw [uLift_append1_ULift_uLift]
  apply cast_heq

theorem M.dest_corec {α : TypeVec n} {β : Type u} (g : β → P (α.append1 β)) (x : β) :
    M.dest P (M.corec P g x) = appendFun id (M.corec P g) <$$> g x := by
  trans
  · exact M.dest_corecU (α := α) P (gen_fn g) x
  change P.uLift_down
    ((Arrow.uLift_up ⊚ (Arrow.uLift_down ::: (corec P g ∘ ULift.down))) <$$> gen_fn g x) = _
  unfold uLift_down
  rw [←Sigma.eta (g x)]
  have gen_fst := gen_fn_fst P g x
  have gen_snd := gen_snd P g x
  congr 1
  · apply Function.hfunext rfl
    rintro a b r
    subst r
    cases a
    · change corec P g ∘ ULift.down ∘ (gen_fn g x).snd Fin2.fz ∘ ULift.up ≍
        corec P g ∘ (g x).snd Fin2.fz
      congr! 2
      apply Function.hfunext
      · assumption
      intro a b heq
      obtain rfl : a = cast (by rw [gen_fst]) b := eq_cast_iff_heq.mpr heq
      clear heq
      dsimp [gen_fn]
      apply HEq.trans (b := (((P.uLift_up (g x))).snd Fin2.fz { down := b }).down)
      case h₂ => rfl
      congr!
      apply eq_of_heq
      refine congr_heq' rfl ?_ ?arg
      case arg =>
        congr! 1
        apply cast_heq
      apply dcongr_heq rfl
      · intro _ _ heq
        obtain rfl := eq_of_heq heq
        conv =>
          lhs; lhs; lhs
          change (gen_fn g x).fst
        conv =>
          rhs; lhs; lhs
          dsimp [uLift_up]
          rw [←gen_fst]
          change (gen_fn g x).fst
        congr!
        rw [uLift_append1_ULift_uLift]
      case hargs => rfl
      intro _
      exact gen_snd
    case fs a =>
      change ULift.down ∘ (gen_fn g x).snd a.fs ∘ ULift.up ≍ (g x).snd a.fs
      apply HEq.trans (b := (ULift.down ∘ (((g x).snd.arrow_uLift)) a.fs ∘ ULift.up))
      case h₂ => rfl
      apply Function.hfunext
      · exact congrFun (congrArg P.B gen_fst) a.fs
      intro a b heq
      change ULift.down _ ≍ ULift.down _
      congr!
      dsimp
      apply congr_heq
      case h₂ => congr!
      apply dcongr_heq rfl
      · intro a b h
        obtain rfl := eq_of_heq h
        rw [←gen_fst]
        cases a <;> rfl
      case hargs => rfl
      congr!

theorem M.bisim_lemma {α : TypeVec n} {a₁ : (mp P).A} {f₁ : (mp P).B a₁ ⟹ α} {a' : P.A}
    {f' : (P.B a').drop ⟹ α} {f₁' : (P.B a').last → M P α}
    (e₁ : M.dest P ⟨a₁, f₁⟩ = ⟨a', splitFun f' f₁'⟩) :
    ∃ (g₁' : _)(e₁' : PFunctor.M.dest a₁ = ⟨a', g₁'⟩),
      f' = M.pathDestLeft P e₁' f₁ ∧
        f₁' = fun x : (last P).B a' => ⟨g₁' x, M.pathDestRight P e₁' f₁ x⟩ := by
  generalize ef : @splitFun n _ (append1 α (M P α)) f' f₁' = ff at e₁
  let he₁' := PFunctor.M.dest a₁
  rcases e₁' : he₁' with ⟨a₁', g₁'⟩
  rw [M.dest_eq_dest' _ e₁'] at e₁
  cases e₁; exact ⟨g₁', e₁', splitFun_inj ef⟩

theorem M.bisim {α : TypeVec n} (R : P.M α → P.M α → Prop)
    (h :
      ∀ x y,
        R x y →
          ∃ a f f₁ f₂,
            M.dest P x = ⟨a, splitFun f f₁⟩ ∧
              M.dest P y = ⟨a, splitFun f f₂⟩ ∧ ∀ i, R (f₁ i) (f₂ i))
    (x y) (r : R x y) : x = y := by
  obtain ⟨a₁, f₁⟩ := x
  obtain ⟨a₂, f₂⟩ := y
  dsimp [mp] at *
  have : a₁ = a₂ := by
    refine
      PFunctor.M.bisim (fun a₁ a₂ => ∃ x y, R x y ∧ x.1 = a₁ ∧ y.1 = a₂) ?_ _ _
        ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩
    rintro _ _ ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩
    rcases h _ _ r with ⟨a', f', f₁', f₂', e₁, e₂, h'⟩
    rcases M.bisim_lemma P e₁ with ⟨g₁', e₁', rfl, rfl⟩
    rcases M.bisim_lemma P e₂ with ⟨g₂', e₂', _, rfl⟩
    rw [e₁', e₂']
    exact ⟨_, _, _, rfl, rfl, fun b => ⟨_, _, h' b, rfl, rfl⟩⟩
  subst this
  congr with i p
  induction p with (
    obtain ⟨a', f', f₁', f₂', e₁, e₂, h''⟩ := h _ _ r
    obtain ⟨g₁', e₁', rfl, rfl⟩ := M.bisim_lemma P e₁
    obtain ⟨g₂', e₂', e₃, rfl⟩ := M.bisim_lemma P e₂
    cases h'.symm.trans e₁'
    cases h'.symm.trans e₂')
  | root x a f h' i c =>
    exact congr_fun (congr_fun e₃ i) c
  | child x a f h' i c p IH =>
    exact IH _ _ (h'' _)

theorem M.bisim₀ {α : TypeVec n} (R : P.M α → P.M α → Prop) (h₀ : Equivalence R)
    (h : ∀ x y, R x y → (id ::: Quot.mk R) <$$> M.dest _ x = (id ::: Quot.mk R) <$$> M.dest _ y)
    (x y) (r : R x y) : x = y := by
  apply M.bisim P R _ _ _ r
  clear r x y
  introv Hr
  specialize h _ _ Hr
  clear Hr
  revert h
  rcases M.dest P x with ⟨ax, fx⟩
  rcases M.dest P y with ⟨ay, fy⟩
  intro h
  rw [map_eq, map_eq] at h
  injection h with h₀ h₁
  subst ay
  simp? at h₁ says simp only [heq_eq_eq] at h₁
  have Hdrop : dropFun fx = dropFun fy := by
    replace h₁ := congr_arg dropFun h₁
    simpa using h₁
  exists ax, dropFun fx, lastFun fx, lastFun fy
  rw [split_dropFun_lastFun, Hdrop, split_dropFun_lastFun]
  simp only [true_and]
  intro i
  replace h₁ := congr_fun (congr_fun h₁ Fin2.fz) i
  simp only [TypeVec.comp, appendFun, splitFun] at h₁
  replace h₁ := Quot.eqvGen_exact h₁
  rw [h₀.eqvGen_iff] at h₁
  exact h₁

theorem M.bisim' {α : TypeVec n} (R : P.M α → P.M α → Prop)
    (h : ∀ x y, R x y → (id ::: Quot.mk R) <$$> M.dest _ x = (id ::: Quot.mk R) <$$> M.dest _ y)
    (x y) (r : R x y) : x = y := by
  have := M.bisim₀ P (Relation.EqvGen R) ?_ ?_
  · solve_by_elim [Relation.EqvGen.rel]
  · apply Relation.EqvGen.is_equivalence
  · clear r x y
    introv Hr
    have : ∀ x y, R x y → Relation.EqvGen R x y := @Relation.EqvGen.rel _ R
    induction Hr
    · rw [← Quot.factor_mk_eq R (Relation.EqvGen R) this]
      rwa [appendFun_comp_id, ← MvFunctor.map_map, ← MvFunctor.map_map, h]
    all_goals simp_all

theorem M.dest_map {α β : TypeVec n} (g : α ⟹ β) (x : P.M α) :
    M.dest P (g <$$> x) = (appendFun g fun x => g <$$> x) <$$> M.dest P x := by
  obtain ⟨a, f⟩ := x
  rw [map_eq]
  conv =>
    rhs
    rw [M.dest, M.dest', map_eq, appendFun_comp_splitFun]
  rfl

theorem M.map_dest {α β : TypeVec n} (g : (α ::: P.M α) ⟹ (β ::: P.M β)) (x : P.M α)
    (h : ∀ x : P.M α, lastFun g x = (dropFun g <$$> x : P.M β)) :
    g <$$> M.dest P x = M.dest P (dropFun g <$$> x) := by
  rw [M.dest_map]; congr
  apply eq_of_drop_last_eq (by simp)
  simp only [lastFun_appendFun]
  ext1; apply h

end MvPFunctor
