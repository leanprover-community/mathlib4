/-
Copyright (c) 2021 Roberto Alvarez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roberto Alvarez
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.EckmannHilton
import Mathlib.Logic.Equiv.TransferInstance
import Mathlib.Algebra.Group.Ext

#align_import topology.homotopy.homotopy_group from "leanprover-community/mathlib"@"4c3e1721c58ef9087bbc2c8c38b540f70eda2e53"

/-!
# `n`th homotopy group

We define the `n`th homotopy group at `x : X`, `π_n X x`, as the equivalence classes
of functions from the `n`-dimensional cube to the topological space `X`
that send the boundary to the base point `x`, up to homotopic equivalence.
Note that such functions are generalized loops `GenLoop (Fin n) x`; in particular
`GenLoop (Fin 1) x ≃ Path x x`.

We show that `π_0 X x` is equivalent to the path-connected components, and
that `π_1 X x` is equivalent to the fundamental group at `x`.
We provide a group instance using path composition and show commutativity when `n > 1`.

## definitions

* `GenLoop N x` is the type of continuous functions `I^N → X` that send the boundary to `x`,
* `HomotopyGroup.Pi n X x` denoted `π_ n X x` is the quotient of `GenLoop (Fin n) x` by
  homotopy relative to the boundary,
* group instance `Group (π_(n+1) X x)`,
* commutative group instance `CommGroup (π_(n+2) X x)`.

TODO:
* `Ω^M (Ω^N X) ≃ₜ Ω^(M⊕N) X`, and `Ω^M X ≃ₜ Ω^N X` when `M ≃ N`. Similarly for `π_`.
* Path-induced homomorphisms. Show that `HomotopyGroup.pi1EquivFundamentalGroup`
  is a group isomorphism.
* Examples with `𝕊^n`: `π_n (𝕊^n) = ℤ`, `π_m (𝕊^n)` trivial for `m < n`.
* Actions of π_1 on π_n.
* Lie algebra: `⁅π_(n+1), π_(m+1)⁆` contained in `π_(n+m+1)`.

-/


open scoped unitInterval Topology

open Homeomorph

noncomputable section

scoped[Topology] notation "I^" N => N → I

namespace Cube

/-- The points in a cube with at least one projection equal to 0 or 1. -/
def boundary (N : Type*) : Set (I^N) :=
  {y | ∃ i, y i = 0 ∨ y i = 1}
#align cube.boundary Cube.boundary

variable {N : Type*} [DecidableEq N]

/-- The forward direction of the homeomorphism
  between the cube $I^N$ and $I × I^{N\setminus\{j\}}$. -/
@[reducible]
def splitAt (i : N) : (I^N) ≃ₜ I × I^{ j // j ≠ i } :=
  funSplitAt I i
#align cube.split_at Cube.splitAt

/-- The backward direction of the homeomorphism
  between the cube $I^N$ and $I × I^{N\setminus\{j\}}$. -/
@[reducible]
def insertAt (i : N) : (I × I^{ j // j ≠ i }) ≃ₜ I^N :=
  (funSplitAt I i).symm
#align cube.insert_at Cube.insertAt

theorem insertAt_boundary (i : N) {t₀ : I} {t}
    (H : (t₀ = 0 ∨ t₀ = 1) ∨ t ∈ boundary { j // j ≠ i }) : insertAt i ⟨t₀, t⟩ ∈ boundary N := by
  obtain H | ⟨j, H⟩ := H
  -- ⊢ ↑(insertAt i) (t₀, t) ∈ boundary N
  · use i; rwa [funSplitAt_symm_apply, dif_pos rfl]
    -- ⊢ ↑(insertAt i) (t₀, t) i = 0 ∨ ↑(insertAt i) (t₀, t) i = 1
           -- 🎉 no goals
  · use j; rwa [funSplitAt_symm_apply, dif_neg j.prop, Subtype.coe_eta]
    -- ⊢ ↑(insertAt i) (t₀, t) ↑j = 0 ∨ ↑(insertAt i) (t₀, t) ↑j = 1
           -- 🎉 no goals
#align cube.insert_at_boundary Cube.insertAt_boundary

end Cube

variable (N X : Type*) [TopologicalSpace X] (x : X)

/-- The space of paths with both endpoints equal to a specified point `x : X`. -/
@[reducible]
def LoopSpace :=
  Path x x
#align loop_space LoopSpace

-- mathport name: exprΩ
scoped[Topology.Homotopy] notation "Ω" => LoopSpace

instance LoopSpace.inhabited : Inhabited (Path x x) :=
  ⟨Path.refl x⟩
#align loop_space.inhabited LoopSpace.inhabited

/-- The `n`-dimensional generalized loops based at `x` in a space `X` are
  continuous functions `I^n → X` that sends the boundary to `x`.
  We allow an arbitrary indexing type `N` in place of `Fin n` here. -/
def GenLoop : Set C(I^N, X) :=
  {p | ∀ y ∈ Cube.boundary N, p y = x}
#align gen_loop GenLoop

scoped[Topology.Homotopy] notation "Ω^" => GenLoop

open Topology.Homotopy

variable {N X x}

namespace GenLoop

instance funLike : FunLike (Ω^ N X x) (I^N) fun _ => X where
  coe f := f.1
  coe_injective' := fun ⟨⟨f, _⟩, _⟩ ⟨⟨g, _⟩, _⟩ _ => by congr
                                                        -- 🎉 no goals
#align gen_loop.fun_like GenLoop.funLike

@[ext]
theorem ext (f g : Ω^ N X x) (H : ∀ y, f y = g y) : f = g :=
  FunLike.coe_injective' (funext H)
#align gen_loop.ext GenLoop.ext

@[simp]
theorem mk_apply (f : C(I^N, X)) (H y) : (⟨f, H⟩ : Ω^ N X x) y = f y :=
  rfl
#align gen_loop.mk_apply GenLoop.mk_apply

/-- Copy of a `GenLoop` with a new map from the unit cube equal to the old one.
  Useful to fix definitional equalities. -/
def copy (f : Ω^ N X x) (g : (I^N) → X) (h : g = f) : Ω^ N X x :=
  ⟨⟨g, h.symm ▸ f.1.2⟩, by convert f.2⟩
                           -- 🎉 no goals
#align gen_loop.copy GenLoop.copy

/- porting note: this now requires the `funLike` instance,
  so the instance is now put before `copy`. -/
theorem coe_copy (f : Ω^ N X x) {g : (I^N) → X} (h : g = f) : ⇑(copy f g h) = g :=
  rfl
#align gen_loop.coe_copy GenLoop.coe_copy

theorem copy_eq (f : Ω^ N X x) {g : (I^N) → X} (h : g = f) : copy f g h = f := by
  ext x
  -- ⊢ ↑(copy f g h) x = ↑f x
  exact congr_fun h x
  -- 🎉 no goals
#align gen_loop.copy_eq GenLoop.copy_eq

theorem boundary (f : Ω^ N X x) : ∀ y ∈ Cube.boundary N, f y = x :=
  f.2
#align gen_loop.boundary GenLoop.boundary

/-- The constant `GenLoop` at `x`. -/
def const : Ω^ N X x :=
  ⟨ContinuousMap.const _ x, fun _ _ => rfl⟩
#align gen_loop.const GenLoop.const

@[simp]
theorem const_apply {t} : (@const N X _ x) t = x :=
  rfl
#align gen_loop.const_apply GenLoop.const_apply

instance inhabited : Inhabited (Ω^ N X x) :=
  ⟨const⟩

/-- The "homotopic relative to boundary" relation between `GenLoop`s. -/
def Homotopic (f g : Ω^ N X x) : Prop :=
  f.1.HomotopicRel g.1 (Cube.boundary N)
#align gen_loop.homotopic GenLoop.Homotopic

namespace Homotopic

variable {f g h : Ω^ N X x}

@[refl]
theorem refl (f : Ω^ N X x) : Homotopic f f :=
  ContinuousMap.HomotopicRel.refl _
#align gen_loop.homotopic.refl GenLoop.Homotopic.refl

@[symm]
nonrec theorem symm (H : Homotopic f g) : Homotopic g f :=
  H.symm
#align gen_loop.homotopic.symm GenLoop.Homotopic.symm

@[trans]
nonrec theorem trans (H0 : Homotopic f g) (H1 : Homotopic g h) : Homotopic f h :=
  H0.trans H1
#align gen_loop.homotopic.trans GenLoop.Homotopic.trans

theorem equiv : Equivalence (@Homotopic N X _ x) :=
  ⟨Homotopic.refl, Homotopic.symm, Homotopic.trans⟩
#align gen_loop.homotopic.equiv GenLoop.Homotopic.equiv

instance setoid (N) (x : X) : Setoid (Ω^ N X x) :=
  ⟨Homotopic, equiv⟩
#align gen_loop.homotopic.setoid GenLoop.Homotopic.setoid

end Homotopic

section LoopHomeo

variable [DecidableEq N]

/-- Loop from a generalized loop by currying $I^N → X$ into $I → (I^{N\setminus\{j\}} → X)$. -/
@[simps]
def toLoop (i : N) (p : Ω^ N X x) : Ω (Ω^ { j // j ≠ i } X x) const
    where
  toFun t :=
    ⟨(p.val.comp (Cube.insertAt i).toContinuousMap).curry t, fun y yH =>
      p.property (Cube.insertAt i (t, y)) (Cube.insertAt_boundary i <| Or.inr yH)⟩
  source' := by ext t; refine' p.property (Cube.insertAt i (0, t)) ⟨i, Or.inl _⟩; simp
                -- ⊢ ↑(ContinuousMap.toFun (ContinuousMap.mk fun t => { val := ↑(ContinuousMap.cu …
                       -- ⊢ ↑(Cube.insertAt i) (0, t) i = 0
                                                                                  -- 🎉 no goals
  target' := by ext t; refine' p.property (Cube.insertAt i (1, t)) ⟨i, Or.inr _⟩; simp
                -- ⊢ ↑(ContinuousMap.toFun (ContinuousMap.mk fun t => { val := ↑(ContinuousMap.cu …
                       -- ⊢ ↑(Cube.insertAt i) (1, t) i = 1
                                                                                  -- 🎉 no goals
#align gen_loop.to_loop GenLoop.toLoop


theorem continuous_toLoop (i : N) : Continuous (@toLoop N X _ x _ i) :=
  Path.continuous_uncurry_iff.1 <|
    Continuous.subtype_mk
      (ContinuousMap.continuous_eval'.comp <|
        Continuous.prod_map
          (ContinuousMap.continuous_curry.comp <|
            (ContinuousMap.continuous_comp_left _).comp continuous_subtype_val)
          continuous_id)
      _
#align gen_loop.continuous_to_loop GenLoop.continuous_toLoop

/-- Generalized loop from a loop by uncurrying $I → (I^{N\setminus\{j\}} → X)$ into $I^N → X$. -/
@[simps]
def fromLoop (i : N) (p : Ω (Ω^ { j // j ≠ i } X x) const) : Ω^ N X x :=
  ⟨(ContinuousMap.comp ⟨Subtype.val, by continuity⟩ p.toContinuousMap).uncurry.comp
                                        -- 🎉 no goals
    (Cube.splitAt i).toContinuousMap,
    by
    rintro y ⟨j, Hj⟩
    -- ⊢ ↑(ContinuousMap.comp (ContinuousMap.uncurry (ContinuousMap.comp (ContinuousM …
    simp only [ContinuousMap.comp_apply, toContinuousMap_apply,
      funSplitAt_apply, ContinuousMap.uncurry_apply, ContinuousMap.coe_mk,
      Function.uncurry_apply_pair]
    obtain rfl | Hne := eq_or_ne j i
    -- ⊢ (↑↑(↑p.toContinuousMap (y j)) fun j_1 => y ↑j_1) = x
    · cases' Hj with Hj Hj <;> simp only [Hj, p.coe_toContinuousMap, p.source, p.target] <;> rfl
      -- ⊢ (↑↑(↑p.toContinuousMap (y j)) fun j_1 => y ↑j_1) = x
                               -- ⊢ (↑↑const fun j_1 => y ↑j_1) = x
                               -- ⊢ (↑↑const fun j_1 => y ↑j_1) = x
                                                                                             -- 🎉 no goals
                                                                                             -- 🎉 no goals
    · exact GenLoop.boundary _ _ ⟨⟨j, Hne⟩, Hj⟩⟩
      -- 🎉 no goals
#align gen_loop.from_loop GenLoop.fromLoop

theorem continuous_fromLoop (i : N) : Continuous (@fromLoop N X _ x _ i) :=
  ((ContinuousMap.continuous_comp_left _).comp <|
        ContinuousMap.continuous_uncurry.comp <|
          (ContinuousMap.continuous_comp _).comp continuous_induced_dom).subtype_mk
    _
#align gen_loop.continuous_from_loop GenLoop.continuous_fromLoop

theorem to_from (i : N) (p : Ω (Ω^ { j // j ≠ i } X x) const) : toLoop i (fromLoop i p) = p := by
  simp_rw [toLoop, fromLoop, ContinuousMap.comp_assoc,
    toContinuousMap_comp_symm, ContinuousMap.comp_id]
  ext; rfl
  -- ⊢ ↑(↑{ toContinuousMap := ContinuousMap.mk fun t => { val := ↑(ContinuousMap.c …
       -- 🎉 no goals
#align gen_loop.to_from GenLoop.to_from

/-- The `n+1`-dimensional loops are in bijection with the loops in the space of
  `n`-dimensional loops with base point `const`.
  We allow an arbitrary indexing type `N` in place of `Fin n` here. -/
@[simps]
def loopHomeo (i : N) : Ω^ N X x ≃ₜ Ω (Ω^ { j // j ≠ i } X x) const
    where
  toFun := toLoop i
  invFun := fromLoop i
  left_inv p := by ext; exact congr_arg p (Equiv.apply_symm_apply _ _)
                   -- ⊢ ↑(fromLoop i (toLoop i p)) y✝ = ↑p y✝
                        -- 🎉 no goals
  right_inv := to_from i
  continuous_toFun := continuous_toLoop i
  continuous_invFun := continuous_fromLoop i
#align gen_loop.loop_homeo GenLoop.loopHomeo

theorem toLoop_apply (i : N) {p : Ω^ N X x} {t} {tn} :
    toLoop i p t tn = p (Cube.insertAt i ⟨t, tn⟩) :=
  rfl
#align gen_loop.to_loop_apply GenLoop.toLoop_apply

theorem fromLoop_apply (i : N) {p : Ω (Ω^ { j // j ≠ i } X x) const} {t : I^N} :
    fromLoop i p t = p (t i) (Cube.splitAt i t).snd :=
  rfl
#align gen_loop.from_loop_apply GenLoop.fromLoop_apply

/-- Composition with `Cube.insertAt` as a continuous map. -/
@[reducible]
def cCompInsert (i : N) : C(C(I^N, X), C(I × I^{ j // j ≠ i }, X)) :=
  ⟨fun f => f.comp (Cube.insertAt i).toContinuousMap,
    (Cube.insertAt i).toContinuousMap.continuous_comp_left⟩
#align gen_loop.c_comp_insert GenLoop.cCompInsert

/-- A homotopy between `n+1`-dimensional loops `p` and `q` constant on the boundary
  seen as a homotopy between two paths in the space of `n`-dimensional paths. -/
def homotopyTo (i : N) {p q : Ω^ N X x} (H : p.1.HomotopyRel q.1 (Cube.boundary N)) :
    C(I × I, C(I^{ j // j ≠ i }, X)) :=
  ((⟨_, ContinuousMap.continuous_curry⟩ : C(_, _)).comp <|
      (cCompInsert i).comp H.toContinuousMap.curry).uncurry
#align gen_loop.homotopy_to GenLoop.homotopyTo

-- porting note: `@[simps]` no longer too slow in Lean 4 but does not generate this lemma.
theorem homotopyTo_apply (i : N) {p q : Ω^ N X x} (H : p.1.HomotopyRel q.1 <| Cube.boundary N)
    (t : I × I) (tₙ : I^{ j // j ≠ i }) :
    homotopyTo i H t tₙ = H (t.fst, Cube.insertAt i (t.snd, tₙ)) :=
  rfl
#align gen_loop.homotopy_to_apply GenLoop.homotopyTo_apply

theorem homotopicTo (i : N) {p q : Ω^ N X x} :
    Homotopic p q → (toLoop i p).Homotopic (toLoop i q) := by
  refine' Nonempty.map fun H => ⟨⟨⟨fun t => ⟨homotopyTo i H t, _⟩, _⟩, _, _⟩, _⟩
  · rintro y ⟨i, iH⟩
    -- ⊢ ↑(↑(homotopyTo i✝ H) t) y = x
    rw [homotopyTo_apply, H.eq_fst, p.2]
    -- ⊢ ↑(Cube.insertAt i✝) (t.snd, y) ∈ Cube.boundary N
    all_goals apply Cube.insertAt_boundary; right; exact ⟨i, iH⟩
    -- 🎉 no goals
  · continuity
    -- 🎉 no goals
  iterate 2 intro; ext; erw [homotopyTo_apply, toLoop_apply]; swap
  · apply H.apply_zero
    -- 🎉 no goals
  · apply H.apply_one
    -- 🎉 no goals
  intro t y yH
  -- ⊢ ↑(ContinuousMap.mk fun x_1 => ContinuousMap.toFun { toContinuousMap := Conti …
  constructor <;> ext <;> erw [homotopyTo_apply]
  -- ⊢ ↑(ContinuousMap.mk fun x_1 => ContinuousMap.toFun { toContinuousMap := Conti …
                  -- ⊢ ↑(↑(ContinuousMap.mk fun x_1 => ContinuousMap.toFun { toContinuousMap := Con …
                  -- ⊢ ↑(↑(ContinuousMap.mk fun x_1 => ContinuousMap.toFun { toContinuousMap := Con …
                          -- ⊢ ↑H ((t, y).fst, ↑(Cube.insertAt i) ((t, y).snd, y✝)) = ↑(↑(toLoop i p).toCon …
                          -- ⊢ ↑H ((t, y).fst, ↑(Cube.insertAt i) ((t, y).snd, y✝)) = ↑(↑(toLoop i q).toCon …
  apply H.eq_fst; on_goal 2 => apply H.eq_snd
  -- ⊢ ↑(Cube.insertAt i) ((t, y).snd, y✝) ∈ Cube.boundary N
                  -- ⊢ ↑(Cube.insertAt i) ((t, y).snd, y✝) ∈ Cube.boundary N
                  -- ⊢ ↑(Cube.insertAt i) ((t, y).snd, y✝) ∈ Cube.boundary N
  all_goals use i; rw [funSplitAt_symm_apply, dif_pos rfl]; exact yH
  -- 🎉 no goals
#align gen_loop.homotopic_to GenLoop.homotopicTo

/-- The converse to `GenLoop.homotopyTo`: a homotopy between two loops in the space of
  `n`-dimensional loops can be seen as a homotopy between two `n+1`-dimensional paths. -/
@[simps!] def homotopyFrom (i : N) {p q : Ω^ N X x} (H : (toLoop i p).Homotopy (toLoop i q)) :
    C(I × I^N, X) :=
  (ContinuousMap.comp ⟨_, ContinuousMap.continuous_uncurry⟩
          (ContinuousMap.comp ⟨Subtype.val, by continuity⟩ H.toContinuousMap).curry).uncurry.comp <|
                                               -- 🎉 no goals
    (ContinuousMap.id I).prodMap (Cube.splitAt i).toContinuousMap
#align gen_loop.homotopy_from GenLoop.homotopyFrom
-- porting note: @[simps!] no longer too slow in Lean 4.
#align gen_loop.homotopy_from_apply GenLoop.homotopyFrom_apply

theorem homotopicFrom (i : N) {p q : Ω^ N X x} :
    (toLoop i p).Homotopic (toLoop i q) → Homotopic p q := by
  refine' Nonempty.map fun H => ⟨⟨homotopyFrom i H, _, _⟩, _⟩
  pick_goal 3
  · rintro t y ⟨j, jH⟩
    -- ⊢ ↑(ContinuousMap.mk fun x_1 => ContinuousMap.toFun { toContinuousMap := homot …
    erw [homotopyFrom_apply]
    obtain rfl | h := eq_or_ne j i
    · constructor
      -- ⊢ (↑↑(↑H ((t, y).fst, Prod.snd (t, y) j)) fun j_1 => Prod.snd (t, y) ↑j_1) = ↑ …
      · rw [H.eq_fst]; exacts [congr_arg p ((Cube.splitAt j).left_inv _), jH]
        -- ⊢ (↑↑(↑(toLoop j p).toContinuousMap (Prod.snd (t, y) j)) fun j_1 => Prod.snd ( …
                       -- 🎉 no goals
      · rw [H.eq_snd]; exacts [congr_arg q ((Cube.splitAt j).left_inv _), jH]
        -- ⊢ (↑↑(↑(toLoop j q).toContinuousMap (Prod.snd (t, y) j)) fun j_1 => Prod.snd ( …
                       -- 🎉 no goals
    · rw [p.2 _ ⟨j, jH⟩, q.2 _ ⟨j, jH⟩]; constructor <;> · apply boundary; exact ⟨⟨j, h⟩, jH⟩
      -- ⊢ (↑↑(↑H ((t, y).fst, Prod.snd (t, y) i)) fun j => Prod.snd (t, y) ↑j) = x ∧ ( …
                                         -- ⊢ (↑↑(↑H ((t, y).fst, Prod.snd (t, y) i)) fun j => Prod.snd (t, y) ↑j) = x
                                                           -- ⊢ (fun j => Prod.snd (t, y) ↑j) ∈ Cube.boundary { j // ¬j = i }
                                                                           -- 🎉 no goals
                                                           -- ⊢ (fun j => Prod.snd (t, y) ↑j) ∈ Cube.boundary { j // ¬j = i }
                                                                           -- 🎉 no goals
    /- porting note: the following is indented two spaces more than it should be due to
      strange behavior of `erw` -/
    all_goals
      intro
      apply (homotopyFrom_apply _ _ _).trans
      first
      | rw [H.apply_zero]
      | rw [H.apply_one]
      first
      | apply congr_arg p
      | apply congr_arg q
      apply (Cube.splitAt i).left_inv
#align gen_loop.homotopic_from GenLoop.homotopicFrom

/-- Concatenation of two `GenLoop`s along the `i`th coordinate. -/
def transAt (i : N) (f g : Ω^ N X x) : Ω^ N X x :=
  copy (fromLoop i <| (toLoop i f).trans <| toLoop i g)
    (fun t => if (t i : ℝ) ≤ 1 / 2
      then f (Function.update t i <| Set.projIcc 0 1 zero_le_one (2 * t i))
      else g (Function.update t i <| Set.projIcc 0 1 zero_le_one (2 * t i - 1)))
    (by
      ext1; symm
      -- ⊢ (if ↑(x✝ i) ≤ 1 / 2 then ↑f (Function.update x✝ i (Set.projIcc 0 1 (_ : 0 ≤  …
            -- ⊢ ↑(fromLoop i (Path.trans (toLoop i f) (toLoop i g))) x✝ = if ↑(x✝ i) ≤ 1 / 2 …
      dsimp only [Path.trans, fromLoop, Path.coe_mk_mk, Function.comp_apply, mk_apply,
        ContinuousMap.comp_apply, toContinuousMap_apply, funSplitAt_apply,
        ContinuousMap.uncurry_apply, ContinuousMap.coe_mk, Function.uncurry_apply_pair]
      split_ifs; change f _ = _; swap; change g _ = _
      -- ⊢ (↑↑(Path.extend (toLoop i f) (2 * ↑(x✝ i))) fun j => x✝ ↑j) = ↑f (Function.u …
                 -- ⊢ ↑f (↑(Homeomorph.toContinuousMap (Cube.insertAt i)) (Set.projIcc 0 1 Path.ex …
                                 -- ⊢ (↑↑(Path.extend (toLoop i g) (2 * ↑(x✝ i) - 1)) fun j => x✝ ↑j) = ↑g (Functi …
                                       -- ⊢ ↑g (↑(Homeomorph.toContinuousMap (Cube.insertAt i)) (Set.projIcc 0 1 Path.ex …
      all_goals congr 1)
      -- 🎉 no goals
#align gen_loop.trans_at GenLoop.transAt

/-- Reversal of a `GenLoop` along the `i`th coordinate. -/
def symmAt (i : N) (f : Ω^ N X x) : Ω^ N X x :=
  (copy (fromLoop i (toLoop i f).symm) fun t => f fun j => if j = i then σ (t i) else t j) <| by
    ext1; change _ = f _; congr; ext1; simp
    -- ⊢ (↑f fun j => if j = i then σ (x✝ i) else x✝ j) = ↑(fromLoop i (Path.symm (to …
          -- ⊢ (↑f fun j => if j = i then σ (x✝ i) else x✝ j) = ↑f (↑(Homeomorph.toContinuo …
                          -- ⊢ (fun j => if j = i then σ (x✝ i) else x✝ j) = ↑(Homeomorph.toContinuousMap ( …
                                 -- ⊢ (if x✝ = i then σ (x✝¹ i) else x✝¹ x✝) = ↑(Homeomorph.toContinuousMap (Cube. …
                                       -- 🎉 no goals
#align gen_loop.symm_at GenLoop.symmAt

theorem transAt_distrib {i j : N} (h : i ≠ j) (a b c d : Ω^ N X x) :
    transAt i (transAt j a b) (transAt j c d) = transAt j (transAt i a c) (transAt i b d) := by
  ext; simp_rw [transAt, coe_copy, Function.update_apply, if_neg h, if_neg h.symm]
  -- ⊢ ↑(transAt i (transAt j a b) (transAt j c d)) y✝ = ↑(transAt j (transAt i a c …
       -- ⊢ (if ↑(y✝ i) ≤ 1 / 2 then if ↑(y✝ j) ≤ 1 / 2 then ↑a (Function.update (Functi …
  split_ifs <;>
    · congr 1; ext1; simp only [Function.update, eq_rec_constant, dite_eq_ite]
      -- ⊢ Function.update (Function.update y✝ i (Set.projIcc 0 1 transAt.proof_2 (2 *  …
               -- ⊢ Function.update (Function.update y✝ i (Set.projIcc 0 1 transAt.proof_2 (2 *  …
                     -- ⊢ (if x✝ = j then Set.projIcc 0 1 transAt.proof_2 (2 * ↑(y✝ j)) else if x✝ = i …
      -- ⊢ Function.update (Function.update y✝ i (Set.projIcc 0 1 transAt.proof_2 (2 *  …
      -- ⊢ x✝ = j → ¬x✝ = i
                          -- ⊢ ¬x✝ = i
                                      -- 🎉 no goals
               -- ⊢ Function.update (Function.update y✝ i (Set.projIcc 0 1 transAt.proof_2 (2 *  …
                     -- ⊢ (if x✝ = j then Set.projIcc 0 1 transAt.proof_2 (2 * ↑(y✝ j) - 1) else if x✝ …
      -- ⊢ Function.update (Function.update y✝ i (Set.projIcc 0 1 transAt.proof_2 (2 *  …
      -- ⊢ x✝ = j → ¬x✝ = i
                          -- ⊢ ¬x✝ = i
                                      -- 🎉 no goals
               -- ⊢ Function.update (Function.update y✝ i (Set.projIcc 0 1 transAt.proof_2 (2 *  …
                     -- ⊢ (if x✝ = j then Set.projIcc 0 1 transAt.proof_2 (2 * ↑(y✝ j)) else if x✝ = i …
      -- ⊢ Function.update (Function.update y✝ i (Set.projIcc 0 1 transAt.proof_2 (2 *  …
      -- ⊢ x✝ = j → ¬x✝ = i
                          -- ⊢ ¬x✝ = i
                                      -- 🎉 no goals
               -- ⊢ Function.update (Function.update y✝ i (Set.projIcc 0 1 transAt.proof_2 (2 *  …
                     -- ⊢ (if x✝ = j then Set.projIcc 0 1 transAt.proof_2 (2 * ↑(y✝ j) - 1) else if x✝ …
      apply ite_ite_comm; rintro rfl; exact h.symm
      -- ⊢ x✝ = j → ¬x✝ = i
                          -- ⊢ ¬x✝ = i
                                      -- 🎉 no goals
#align gen_loop.trans_at_distrib GenLoop.transAt_distrib

theorem fromLoop_trans_toLoop {i : N} {p q : Ω^ N X x} :
    fromLoop i ((toLoop i p).trans <| toLoop i q) = transAt i p q :=
  (copy_eq _ _).symm
#align gen_loop.from_loop_trans_to_loop GenLoop.fromLoop_trans_toLoop

theorem fromLoop_symm_toLoop {i : N} {p : Ω^ N X x} : fromLoop i (toLoop i p).symm = symmAt i p :=
  (copy_eq _ _).symm
#align gen_loop.from_loop_symm_to_loop GenLoop.fromLoop_symm_toLoop

end LoopHomeo

end GenLoop

/-- The `n`th homotopy group at `x` defined as the quotient of `Ω^n x` by the
  `GenLoop.Homotopic` relation. -/
def HomotopyGroup (N X : Type*) [TopologicalSpace X] (x : X) : Type _ :=
  Quotient (GenLoop.Homotopic.setoid N x)
#align homotopy_group HomotopyGroup

-- porting note: in Lean 3 this instance was derived
instance : Inhabited (HomotopyGroup N X x) :=
  inferInstanceAs <| Inhabited <| Quotient (GenLoop.Homotopic.setoid N x)

variable [DecidableEq N]

open GenLoop

/-- Equivalence between the homotopy group of X and the fundamental group of
  `Ω^{j // j ≠ i} x`. -/
def homotopyGroupEquivFundamentalGroup (i : N) :
    HomotopyGroup N X x ≃ FundamentalGroup (Ω^ { j // j ≠ i } X x) const := by
  refine' Equiv.trans _ (CategoryTheory.Groupoid.isoEquivHom _ _).symm
  -- ⊢ HomotopyGroup N X x ≃ (const ⟶ const)
  apply Quotient.congr (loopHomeo i).toEquiv
  -- ⊢ ∀ (a₁ a₂ : ↑(Ω^ N X x)), Setoid.r a₁ a₂ ↔ Setoid.r (↑(loopHomeo i).toEquiv a …
  exact fun p q => ⟨homotopicTo i, homotopicFrom i⟩
  -- 🎉 no goals
#align homotopy_group_equiv_fundamental_group homotopyGroupEquivFundamentalGroup

/-- Homotopy group of finite index. -/
@[reducible]
def HomotopyGroup.Pi (n) (X : Type*) [TopologicalSpace X] (x : X) :=
  HomotopyGroup (Fin n) _ x
#align homotopy_group.pi HomotopyGroup.Pi

-- mathport name: exprπ_
scoped[Topology] notation "π_" => HomotopyGroup.Pi

/-- The 0-dimensional generalized loops based at `x` are in bijection with `X`. -/
def genLoopHomeoOfIsEmpty (N x) [IsEmpty N] : Ω^ N X x ≃ₜ X where
  toFun f := f 0
  invFun y := ⟨ContinuousMap.const _ y, fun _ ⟨i, _⟩ => isEmptyElim i⟩
  left_inv f := by ext; exact congr_arg f (Subsingleton.elim _ _)
                   -- ⊢ ↑((fun y => { val := ContinuousMap.const (N → ↑I) y, property := (_ : ∀ (x_1 …
                        -- 🎉 no goals
  right_inv _ := rfl
  continuous_toFun := (ContinuousMap.continuous_eval_const (0 : N → I)).comp continuous_induced_dom
  continuous_invFun := ContinuousMap.const'.2.subtype_mk _
#align gen_loop_homeo_of_is_empty genLoopHomeoOfIsEmpty

/-- The homotopy "group" indexed by an empty type is in bijection with
  the path components of `X`, aka the `ZerothHomotopy`. -/
def homotopyGroupEquivZerothHomotopyOfIsEmpty (N x) [IsEmpty N] :
    HomotopyGroup N X x ≃ ZerothHomotopy X :=
  Quotient.congr (genLoopHomeoOfIsEmpty N x).toEquiv
    (by
      -- joined iff homotopic
      intros a₁ a₂;
      -- ⊢ Setoid.r a₁ a₂ ↔ Setoid.r (↑(genLoopHomeoOfIsEmpty N x).toEquiv a₁) (↑(genLo …
      constructor <;> rintro ⟨H⟩
      -- ⊢ Setoid.r a₁ a₂ → Setoid.r (↑(genLoopHomeoOfIsEmpty N x).toEquiv a₁) (↑(genLo …
                      -- ⊢ Setoid.r (↑(genLoopHomeoOfIsEmpty N x).toEquiv a₁) (↑(genLoopHomeoOfIsEmpty  …
                      -- ⊢ Setoid.r a₁ a₂
      exacts
        [⟨{ toFun := fun t => H ⟨t, isEmptyElim⟩
            source' := (H.apply_zero _).trans (congr_arg a₁ <| Subsingleton.elim _ _)
            target' := (H.apply_one _).trans (congr_arg a₂ <| Subsingleton.elim _ _) }⟩,
        ⟨{  toFun := fun t0 => H t0.fst
            map_zero_left := fun _ => H.source.trans (congr_arg a₁ <| Subsingleton.elim _ _)
            map_one_left := fun _ => H.target.trans (congr_arg a₂ <| Subsingleton.elim _ _)
            prop' := fun _ _ ⟨i, _⟩ => isEmptyElim i }⟩])
#align homotopy_group_equiv_zeroth_homotopy_of_is_empty homotopyGroupEquivZerothHomotopyOfIsEmpty

/-- The 0th homotopy "group" is in bijection with `ZerothHomotopy`. -/
def HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 X x ≃ ZerothHomotopy X :=
  homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0) x
#align homotopy_group.pi_0_equiv_zeroth_homotopy HomotopyGroup.pi0EquivZerothHomotopy

/-- The 1-dimensional generalized loops based at `x` are in bijection with loops at `x`. -/
def genLoopEquivOfUnique (N) [Unique N] : Ω^ N X x ≃ Ω X x where
  toFun p :=
    Path.mk ⟨fun t => p fun _ => t, by continuity⟩
                                       -- 🎉 no goals
      (GenLoop.boundary _ (fun _ => 0) ⟨default, Or.inl rfl⟩)
      (GenLoop.boundary _ (fun _ => 1) ⟨default, Or.inr rfl⟩)
  invFun p :=
    ⟨⟨fun c => p (c default), by continuity⟩,
                                 -- 🎉 no goals
      by
      rintro y ⟨i, iH | iH⟩ <;> cases Unique.eq_default i <;> apply (congr_arg p iH).trans
      -- ⊢ ↑(ContinuousMap.mk fun c => ↑p (c default)) y = x
                                -- ⊢ ↑(ContinuousMap.mk fun c => ↑p (c default)) y = x
                                -- ⊢ ↑(ContinuousMap.mk fun c => ↑p (c default)) y = x
                                                              -- ⊢ ↑p 0 = x
                                                              -- ⊢ ↑p 1 = x
      exacts [p.source, p.target]⟩
      -- 🎉 no goals
  left_inv p := by ext y; exact congr_arg p (eq_const_of_unique y).symm
                   -- ⊢ ↑((fun p => { val := ContinuousMap.mk fun c => ↑p (c default), property := ( …
                          -- 🎉 no goals
  right_inv p := by ext; rfl
                    -- ⊢ ↑((fun p => { toContinuousMap := ContinuousMap.mk fun t => ↑p fun x => t, so …
                         -- 🎉 no goals

#align gen_loop_equiv_of_unique genLoopEquivOfUnique

/- TODO (?): deducing this from `homotopyGroupEquivFundamentalGroup` would require
  combination of `CategoryTheory.Functor.mapAut` and
  `FundamentalGroupoid.fundamentalGroupoidFunctor` applied to `genLoopHomeoOfIsEmpty`,
  with possibly worse defeq. -/
/-- The homotopy group at `x` indexed by a singleton is in bijection with the fundamental group,
  i.e. the loops based at `x` up to homotopy. -/
def homotopyGroupEquivFundamentalGroupOfUnique (N) [Unique N] :
    HomotopyGroup N X x ≃ FundamentalGroup X x := by
  refine' Equiv.trans _ (CategoryTheory.Groupoid.isoEquivHom _ _).symm
  -- ⊢ HomotopyGroup N X x ≃ (x ⟶ x)
  refine' Quotient.congr (genLoopEquivOfUnique N) _
  -- ⊢ ∀ (a₁ a₂ : ↑(Ω^ N X x)), Setoid.r a₁ a₂ ↔ Setoid.r (↑(genLoopEquivOfUnique N …
  intros a₁ a₂; constructor <;> rintro ⟨H⟩
  -- ⊢ Setoid.r a₁ a₂ ↔ Setoid.r (↑(genLoopEquivOfUnique N) a₁) (↑(genLoopEquivOfUn …
                -- ⊢ Setoid.r a₁ a₂ → Setoid.r (↑(genLoopEquivOfUnique N) a₁) (↑(genLoopEquivOfUn …
                                -- ⊢ Setoid.r (↑(genLoopEquivOfUnique N) a₁) (↑(genLoopEquivOfUnique N) a₂)
                                -- ⊢ Setoid.r a₁ a₂
  · exact
      ⟨{  toFun := fun tx => H (tx.fst, fun _ => tx.snd)
          map_zero_left := fun _ => H.apply_zero _
          map_one_left := fun _ => H.apply_one _
          prop' := fun t y iH => H.prop' _ _ ⟨default, iH⟩ }⟩
  refine'
    ⟨⟨⟨⟨fun tx => H (tx.fst, tx.snd default), H.continuous.comp _⟩, fun y => _, fun y => _⟩, _⟩⟩
  · exact continuous_fst.prod_mk ((continuous_apply _).comp continuous_snd)
    -- 🎉 no goals
  · exact (H.apply_zero _).trans (congr_arg a₁ (eq_const_of_unique y).symm)
    -- 🎉 no goals
  · exact (H.apply_one _).trans (congr_arg a₂ (eq_const_of_unique y).symm)
    -- 🎉 no goals
  · rintro t y ⟨i, iH⟩
    -- ⊢ ↑(ContinuousMap.mk fun x_1 => ContinuousMap.toFun { toContinuousMap := Conti …
    cases Unique.eq_default i; constructor
    -- ⊢ ↑(ContinuousMap.mk fun x_1 => ContinuousMap.toFun { toContinuousMap := Conti …
                               -- ⊢ ↑(ContinuousMap.mk fun x_1 => ContinuousMap.toFun { toContinuousMap := Conti …
    · exact (H.eq_fst _ iH).trans (congr_arg a₁ (eq_const_of_unique y).symm)
      -- 🎉 no goals
    · exact (H.eq_snd _ iH).trans (congr_arg a₂ (eq_const_of_unique y).symm)
      -- 🎉 no goals
#align homotopy_group_equiv_fundamental_group_of_unique homotopyGroupEquivFundamentalGroupOfUnique

/-- The first homotopy group at `x` is in bijection with the fundamental group. -/
def HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 X x ≃ FundamentalGroup X x :=
  homotopyGroupEquivFundamentalGroupOfUnique (Fin 1)
#align homotopy_group.pi_1_equiv_fundamental_group HomotopyGroup.pi1EquivFundamentalGroup

namespace HomotopyGroup

/-- Group structure on `HomotopyGroup N X x` for nonempty `N` (in particular `π_(n+1) X x`). -/
instance group (N) [DecidableEq N] [Nonempty N] : Group (HomotopyGroup N X x) :=
  (homotopyGroupEquivFundamentalGroup <| Classical.arbitrary N).group
#align homotopy_group.group HomotopyGroup.group

/-- Group structure on `HomotopyGroup` obtained by pulling back path composition along the
  `i`th direction. The group structures for two different `i j : N` distribute over each
  other, and therefore are equal by the Eckmann-Hilton argument. -/
@[reducible]
def auxGroup (i : N) : Group (HomotopyGroup N X x) :=
  (homotopyGroupEquivFundamentalGroup i).group
#align homotopy_group.aux_group HomotopyGroup.auxGroup

theorem isUnital_auxGroup (i : N) :
    EckmannHilton.IsUnital (auxGroup i).mul (⟦const⟧ : HomotopyGroup N X x) :=
  ⟨⟨(auxGroup i).one_mul⟩, ⟨(auxGroup i).mul_one⟩⟩
#align homotopy_group.is_unital_aux_group HomotopyGroup.isUnital_auxGroup

theorem auxGroup_indep (i j : N) : (auxGroup i : Group (HomotopyGroup N X x)) = auxGroup j := by
  by_cases h : i = j; · rw [h]
  -- ⊢ auxGroup i = auxGroup j
                        -- 🎉 no goals
  refine' Group.ext (EckmannHilton.mul (isUnital_auxGroup i) (isUnital_auxGroup j) _)
  -- ⊢ ∀ (a b c d : HomotopyGroup N X x), Mul.mul (Mul.mul a b) (Mul.mul c d) = Mul …
  rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩
  -- ⊢ Mul.mul (Mul.mul (Quot.mk Setoid.r a) (Quot.mk Setoid.r b)) (Mul.mul (Quot.m …
  change Quotient.mk' _ = _
  -- ⊢ Quotient.mk' (↑(loopHomeo i).symm (Path.trans (↑(loopHomeo i).toEquiv (↑(loo …
  apply congr_arg Quotient.mk'
  -- ⊢ ↑(loopHomeo i).symm (Path.trans (↑(loopHomeo i).toEquiv (↑(loopHomeo j).symm …
  simp only [fromLoop_trans_toLoop, transAt_distrib h, coe_toEquiv, loopHomeo_apply,
    coe_symm_toEquiv, loopHomeo_symm_apply]
#align homotopy_group.aux_group_indep HomotopyGroup.auxGroup_indep

theorem transAt_indep {i} (j) (f g : Ω^ N X x) :
    (⟦transAt i f g⟧ : HomotopyGroup N X x) = ⟦transAt j f g⟧ := by
  simp_rw [← fromLoop_trans_toLoop]
  -- ⊢ Quotient.mk (Homotopic.setoid N x) (fromLoop i (Path.trans (toLoop i f) (toL …
  let m := fun (G) (_ : Group G) => ((· * ·) : G → G → G)
  -- ⊢ Quotient.mk (Homotopic.setoid N x) (fromLoop i (Path.trans (toLoop i f) (toL …
  exact congr_fun₂ (congr_arg (m <| HomotopyGroup N X x) <| auxGroup_indep i j) ⟦g⟧ ⟦f⟧
  -- 🎉 no goals
#align homotopy_group.trans_at_indep HomotopyGroup.transAt_indep

theorem symmAt_indep {i} (j) (f : Ω^ N X x) :
    (⟦symmAt i f⟧ : HomotopyGroup N X x) = ⟦symmAt j f⟧ := by
  simp_rw [← fromLoop_symm_toLoop]
  -- ⊢ Quotient.mk (Homotopic.setoid N x) (fromLoop i (Path.symm (toLoop i f))) = Q …
  let inv := fun (G) (_ : Group G) => ((·⁻¹) : G → G)
  -- ⊢ Quotient.mk (Homotopic.setoid N x) (fromLoop i (Path.symm (toLoop i f))) = Q …
  exact congr_fun (congr_arg (inv <| HomotopyGroup N X x) <| auxGroup_indep i j) ⟦f⟧
  -- 🎉 no goals
#align homotopy_group.symm_at_indep HomotopyGroup.symmAt_indep

/-- Characterization of multiplicative identity -/
theorem one_def [Nonempty N] : (1 : HomotopyGroup N X x) = ⟦const⟧ :=
  rfl
#align homotopy_group.one_def HomotopyGroup.one_def

/-- Characterization of multiplication -/
theorem mul_spec [Nonempty N] {i} {p q : Ω^ N X x} :
  -- porting note: TODO: introduce `HomotopyGroup.mk` and remove defeq abuse.
    ((· * ·) : _ → _ → HomotopyGroup N X x) ⟦p⟧ ⟦q⟧ = ⟦transAt i q p⟧ := by
  rw [transAt_indep _ q, ← fromLoop_trans_toLoop]; apply Quotient.sound; rfl
  -- ⊢ (fun x_1 x_2 => x_1 * x_2) (Quotient.mk (Homotopic.setoid N x) p) (Quotient. …
                                                   -- ⊢ ↑(loopHomeo (Classical.arbitrary N)).symm (Path.trans (↑(loopHomeo (Classica …
                                                                         -- 🎉 no goals
#align homotopy_group.mul_spec HomotopyGroup.mul_spec

/-- Characterization of multiplicative inverse -/
theorem inv_spec [Nonempty N] {i} {p : Ω^ N X x} : ((⟦p⟧)⁻¹ : HomotopyGroup N X x) = ⟦symmAt i p⟧ :=
  by rw [symmAt_indep _ p, ← fromLoop_symm_toLoop]; apply Quotient.sound; rfl
     -- ⊢ (Quotient.mk (Homotopic.setoid N x) p)⁻¹ = Quotient.mk (Homotopic.setoid N x …
                                                    -- ⊢ ↑(loopHomeo (Classical.arbitrary N)).symm (Path.symm (↑(loopHomeo (Classical …
                                                                          -- 🎉 no goals
#align homotopy_group.inv_spec HomotopyGroup.inv_spec

/-- Multiplication on `HomotopyGroup N X x` is commutative for nontrivial `N`.
  In particular, multiplication on `π_(n+2)` is commutative. -/
instance commGroup [Nontrivial N] : CommGroup (HomotopyGroup N X x) :=
  let h := exists_ne (Classical.arbitrary N)
  @EckmannHilton.commGroup (HomotopyGroup N X x) _ 1 (isUnital_auxGroup <| Classical.choose h) _
    (by
      rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩
      -- ⊢ Mul.mul (Quot.mk Setoid.r a * Quot.mk Setoid.r b) (Quot.mk Setoid.r c * Quot …
      apply congr_arg Quotient.mk'
      -- ⊢ ↑(loopHomeo (Classical.choose h)).symm (Path.trans (↑(loopHomeo (Classical.c …
      simp only [fromLoop_trans_toLoop, transAt_distrib <| Classical.choose_spec h, coe_toEquiv,
        loopHomeo_apply, coe_symm_toEquiv, loopHomeo_symm_apply])
#align homotopy_group.comm_group HomotopyGroup.commGroup

end HomotopyGroup
