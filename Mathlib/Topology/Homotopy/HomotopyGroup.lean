/-
Copyright (c) 2021 Roberto Alvarez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roberto Alvarez
-/
import Mathlib.Algebra.Group.Ext
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.EckmannHilton

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

/-- `I^N` is notation (in the Topology namespace) for `N → I`,
i.e. the unit cube indexed by a type `N`. -/
scoped[Topology] notation "I^" N => N → I

namespace Cube

/-- The points in a cube with at least one projection equal to 0 or 1. -/
def boundary (N : Type*) : Set (I^N) :=
  {y | ∃ i, y i = 0 ∨ y i = 1}

variable {N : Type*} [DecidableEq N]

/-- The forward direction of the homeomorphism
  between the cube $I^N$ and $I × I^{N\setminus\{j\}}$. -/
abbrev splitAt (i : N) : (I^N) ≃ₜ I × I^{ j // j ≠ i } :=
  funSplitAt I i

/-- The backward direction of the homeomorphism
  between the cube $I^N$ and $I × I^{N\setminus\{j\}}$. -/
abbrev insertAt (i : N) : (I × I^{ j // j ≠ i }) ≃ₜ I^N :=
  (funSplitAt I i).symm

theorem insertAt_boundary (i : N) {t₀ : I} {t}
    (H : (t₀ = 0 ∨ t₀ = 1) ∨ t ∈ boundary { j // j ≠ i }) : insertAt i ⟨t₀, t⟩ ∈ boundary N := by
  obtain H | ⟨j, H⟩ := H
  · use i; rwa [funSplitAt_symm_apply, dif_pos rfl]
  · use j; rwa [funSplitAt_symm_apply, dif_neg j.prop, Subtype.coe_eta]

end Cube

variable (N X : Type*) [TopologicalSpace X] (x : X)

/-- The space of paths with both endpoints equal to a specified point `x : X`.
Denoted as `Ω`, within the `Topology.Homotopy` namespace. -/
abbrev LoopSpace :=
  Path x x

@[inherit_doc] scoped[Topology.Homotopy] notation "Ω" => LoopSpace

instance LoopSpace.inhabited : Inhabited (Path x x) :=
  ⟨Path.refl x⟩

/-- The `n`-dimensional generalized loops based at `x` in a space `X` are
  continuous functions `I^n → X` that sends the boundary to `x`.
  We allow an arbitrary indexing type `N` in place of `Fin n` here. -/
def GenLoop : Set C(I^N, X) :=
  {p | ∀ y ∈ Cube.boundary N, p y = x}

@[inherit_doc] scoped[Topology.Homotopy] notation "Ω^" => GenLoop

open Topology.Homotopy

variable {N X x}

namespace GenLoop

instance instFunLike : FunLike (Ω^ N X x) (I^N) X where
  coe f := f.1
  coe_injective' := fun ⟨⟨f, _⟩, _⟩ ⟨⟨g, _⟩, _⟩ _ => by congr

@[ext]
theorem ext (f g : Ω^ N X x) (H : ∀ y, f y = g y) : f = g :=
  DFunLike.coe_injective' (funext H)

@[simp]
theorem mk_apply (f : C(I^N, X)) (H y) : (⟨f, H⟩ : Ω^ N X x) y = f y :=
  rfl

instance instContinuousEval : ContinuousEval (Ω^ N X x) (I^N) X :=
  .of_continuous_forget continuous_subtype_val

instance instContinuousEvalConst : ContinuousEvalConst (Ω^ N X x) (I^N) X := inferInstance

/-- Copy of a `GenLoop` with a new map from the unit cube equal to the old one.
  Useful to fix definitional equalities. -/
def copy (f : Ω^ N X x) (g : (I^N) → X) (h : g = f) : Ω^ N X x :=
  ⟨⟨g, h.symm ▸ f.1.2⟩, by convert f.2⟩

theorem coe_copy (f : Ω^ N X x) {g : (I^N) → X} (h : g = f) : ⇑(copy f g h) = g :=
  rfl

theorem copy_eq (f : Ω^ N X x) {g : (I^N) → X} (h : g = f) : copy f g h = f := by
  ext x
  exact congr_fun h x

theorem boundary (f : Ω^ N X x) : ∀ y ∈ Cube.boundary N, f y = x :=
  f.2

/-- The constant `GenLoop` at `x`. -/
def const : Ω^ N X x :=
  ⟨ContinuousMap.const _ x, fun _ _ => rfl⟩

@[simp]
theorem const_apply {t} : (@const N X _ x) t = x :=
  rfl

instance inhabited : Inhabited (Ω^ N X x) :=
  ⟨const⟩

/-- The "homotopic relative to boundary" relation between `GenLoop`s. -/
def Homotopic (f g : Ω^ N X x) : Prop :=
  f.1.HomotopicRel g.1 (Cube.boundary N)

namespace Homotopic

variable {f g h : Ω^ N X x}

@[refl]
theorem refl (f : Ω^ N X x) : Homotopic f f :=
  ContinuousMap.HomotopicRel.refl _

@[symm]
nonrec theorem symm (H : Homotopic f g) : Homotopic g f :=
  H.symm

@[trans]
nonrec theorem trans (H0 : Homotopic f g) (H1 : Homotopic g h) : Homotopic f h :=
  H0.trans H1

theorem equiv : Equivalence (@Homotopic N X _ x) :=
  ⟨Homotopic.refl, Homotopic.symm, Homotopic.trans⟩

instance setoid (N) (x : X) : Setoid (Ω^ N X x) :=
  ⟨Homotopic, equiv⟩

end Homotopic

section LoopHomeo

variable [DecidableEq N]

/-- Loop from a generalized loop by currying $I^N → X$ into $I → (I^{N\setminus\{j\}} → X)$. -/
@[simps]
def toLoop (i : N) (p : Ω^ N X x) : Ω (Ω^ { j // j ≠ i } X x) const where
  toFun t :=
    ⟨(p.val.comp (Cube.insertAt i)).curry t, fun y yH =>
      p.property (Cube.insertAt i (t, y)) (Cube.insertAt_boundary i <| Or.inr yH)⟩
  source' := by ext t; refine p.property (Cube.insertAt i (0, t)) ⟨i, Or.inl ?_⟩; simp
  target' := by ext t; refine p.property (Cube.insertAt i (1, t)) ⟨i, Or.inr ?_⟩; simp


theorem continuous_toLoop (i : N) : Continuous (@toLoop N X _ x _ i) :=
  Path.continuous_uncurry_iff.1 <|
    Continuous.subtype_mk
      (continuous_eval.comp <|
        Continuous.prodMap
          (ContinuousMap.continuous_curry.comp <|
            (ContinuousMap.continuous_precomp _).comp continuous_subtype_val)
          continuous_id)
      _

/-- Generalized loop from a loop by uncurrying $I → (I^{N\setminus\{j\}} → X)$ into $I^N → X$. -/
@[simps]
def fromLoop (i : N) (p : Ω (Ω^ { j // j ≠ i } X x) const) : Ω^ N X x :=
  ⟨(ContinuousMap.comp ⟨Subtype.val, by fun_prop⟩ p.toContinuousMap).uncurry.comp
    (Cube.splitAt i),
    by
    rintro y ⟨j, Hj⟩
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_coe,
      funSplitAt_apply, ContinuousMap.uncurry_apply, ContinuousMap.coe_mk,
      Function.uncurry_apply_pair]
    obtain rfl | Hne := eq_or_ne j i
    · rcases Hj with Hj | Hj <;> simp only [Hj, p.coe_toContinuousMap, p.source, p.target] <;> rfl
    · exact GenLoop.boundary _ _ ⟨⟨j, Hne⟩, Hj⟩⟩

theorem continuous_fromLoop (i : N) : Continuous (@fromLoop N X _ x _ i) :=
  ((ContinuousMap.continuous_precomp _).comp <|
        ContinuousMap.continuous_uncurry.comp <|
          (ContinuousMap.continuous_postcomp _).comp continuous_induced_dom).subtype_mk
    _

theorem to_from (i : N) (p : Ω (Ω^ { j // j ≠ i } X x) const) : toLoop i (fromLoop i p) = p := by
  simp_rw [toLoop, fromLoop, ContinuousMap.comp_assoc,
    toContinuousMap_comp_symm, ContinuousMap.comp_id]
  ext; rfl

/-- The `n+1`-dimensional loops are in bijection with the loops in the space of
  `n`-dimensional loops with base point `const`.
  We allow an arbitrary indexing type `N` in place of `Fin n` here. -/
@[simps]
def loopHomeo (i : N) : Ω^ N X x ≃ₜ Ω (Ω^ { j // j ≠ i } X x) const where
  toFun := toLoop i
  invFun := fromLoop i
  left_inv p := by ext; exact congr_arg p (by dsimp; exact Equiv.apply_symm_apply _ _)
  right_inv := to_from i
  continuous_toFun := continuous_toLoop i
  continuous_invFun := continuous_fromLoop i

theorem toLoop_apply (i : N) {p : Ω^ N X x} {t} {tn} :
    toLoop i p t tn = p (Cube.insertAt i ⟨t, tn⟩) :=
  rfl

theorem fromLoop_apply (i : N) {p : Ω (Ω^ { j // j ≠ i } X x) const} {t : I^N} :
    fromLoop i p t = p (t i) (Cube.splitAt i t).snd :=
  rfl

/-- Composition with `Cube.insertAt` as a continuous map. -/
abbrev cCompInsert (i : N) : C(C(I^N, X), C(I × I^{ j // j ≠ i }, X)) :=
  ⟨fun f => f.comp (Cube.insertAt i),
    (toContinuousMap <| Cube.insertAt i).continuous_precomp⟩

/-- A homotopy between `n+1`-dimensional loops `p` and `q` constant on the boundary
  seen as a homotopy between two paths in the space of `n`-dimensional paths. -/
def homotopyTo (i : N) {p q : Ω^ N X x} (H : p.1.HomotopyRel q.1 (Cube.boundary N)) :
    C(I × I, C(I^{ j // j ≠ i }, X)) :=
  ((⟨_, ContinuousMap.continuous_curry⟩ : C(_, _)).comp <|
      (cCompInsert i).comp H.toContinuousMap.curry).uncurry

-- `@[simps]` generates this lemma but it's named `homotopyTo_apply_apply` instead
theorem homotopyTo_apply (i : N) {p q : Ω^ N X x} (H : p.1.HomotopyRel q.1 <| Cube.boundary N)
    (t : I × I) (tₙ : I^{ j // j ≠ i }) :
    homotopyTo i H t tₙ = H (t.fst, Cube.insertAt i (t.snd, tₙ)) :=
  rfl

theorem homotopicTo (i : N) {p q : Ω^ N X x} :
    Homotopic p q → (toLoop i p).Homotopic (toLoop i q) := by
  refine Nonempty.map fun H => ⟨⟨⟨fun t => ⟨homotopyTo i H t, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩
  · rintro y ⟨i, iH⟩
    rw [homotopyTo_apply, H.eq_fst, p.2]
    all_goals apply Cube.insertAt_boundary; right; exact ⟨i, iH⟩
  · fun_prop
  iterate 2
    intro
    ext
    dsimp
    rw [homotopyTo_apply, toLoop_apply]
    swap
  · apply H.apply_zero
  · apply H.apply_one
  intro t y yH
  ext
  dsimp
  rw [homotopyTo_apply]
  apply H.eq_fst; use i
  rw [funSplitAt_symm_apply, dif_pos rfl]; exact yH

/-- The converse to `GenLoop.homotopyTo`: a homotopy between two loops in the space of
  `n`-dimensional loops can be seen as a homotopy between two `n+1`-dimensional paths. -/
@[simps!] def homotopyFrom (i : N) {p q : Ω^ N X x} (H : (toLoop i p).Homotopy (toLoop i q)) :
    C(I × I^N, X) :=
  (ContinuousMap.comp ⟨_, ContinuousMap.continuous_uncurry⟩
          (ContinuousMap.comp ⟨Subtype.val, by fun_prop⟩ H.toContinuousMap).curry).uncurry.comp <|
    (ContinuousMap.id I).prodMap (Cube.splitAt i)

theorem homotopicFrom (i : N) {p q : Ω^ N X x} :
    (toLoop i p).Homotopic (toLoop i q) → Homotopic p q := by
  refine Nonempty.map fun H => ⟨⟨homotopyFrom i H, ?_, ?_⟩, ?_⟩
  pick_goal 3
  · rintro t y ⟨j, jH⟩
    erw [homotopyFrom_apply]
    obtain rfl | h := eq_or_ne j i
    · simp only [Prod.map_apply, id_eq, funSplitAt_apply, Function.uncurry_apply_pair]
      rw [H.eq_fst]
      exacts [congr_arg p ((Cube.splitAt j).left_inv _), jH]
    · rw [p.2 _ ⟨j, jH⟩]; apply boundary; exact ⟨⟨j, h⟩, jH⟩
  all_goals
    intro
    apply (homotopyFrom_apply _ _ _).trans
    simp only [Prod.map_apply, id_eq, funSplitAt_apply,
      Function.uncurry_apply_pair, ContinuousMap.HomotopyWith.apply_zero,
      ContinuousMap.HomotopyWith.apply_one, ne_eq, Path.coe_toContinuousMap, toLoop_apply_coe,
      ContinuousMap.curry_apply, ContinuousMap.comp_apply]
    first
    | apply congr_arg p
    | apply congr_arg q
    apply (Cube.splitAt i).left_inv

/-- Concatenation of two `GenLoop`s along the `i`th coordinate. -/
def transAt (i : N) (f g : Ω^ N X x) : Ω^ N X x :=
  copy (fromLoop i <| (toLoop i f).trans <| toLoop i g)
    (fun t => if (t i : ℝ) ≤ 1 / 2
      then f (Function.update t i <| Set.projIcc 0 1 zero_le_one (2 * t i))
      else g (Function.update t i <| Set.projIcc 0 1 zero_le_one (2 * t i - 1)))
    (by
      ext1; symm
      dsimp only [Path.trans, fromLoop, Path.coe_mk_mk, Function.comp_apply, mk_apply,
        ContinuousMap.comp_apply, ContinuousMap.coe_coe, funSplitAt_apply,
        ContinuousMap.uncurry_apply, ContinuousMap.coe_mk, Function.uncurry_apply_pair]
      split_ifs
      · change f _ = _; congr 1
      · change g _ = _; congr 1)

/-- Reversal of a `GenLoop` along the `i`th coordinate. -/
def symmAt (i : N) (f : Ω^ N X x) : Ω^ N X x :=
  (copy (fromLoop i (toLoop i f).symm) fun t => f fun j => if j = i then σ (t i) else t j) <| by
    ext1; change _ = f _; congr; ext1; simp

theorem transAt_distrib {i j : N} (h : i ≠ j) (a b c d : Ω^ N X x) :
    transAt i (transAt j a b) (transAt j c d) = transAt j (transAt i a c) (transAt i b d) := by
  ext; simp_rw [transAt, coe_copy, Function.update_apply, if_neg h, if_neg h.symm]
  split_ifs <;>
    · congr 1; ext1; simp only [Function.update, eq_rec_constant, dite_eq_ite]
      apply ite_ite_comm; rintro rfl; exact h.symm

theorem fromLoop_trans_toLoop {i : N} {p q : Ω^ N X x} :
    fromLoop i ((toLoop i p).trans <| toLoop i q) = transAt i p q :=
  (copy_eq _ _).symm

theorem fromLoop_symm_toLoop {i : N} {p : Ω^ N X x} : fromLoop i (toLoop i p).symm = symmAt i p :=
  (copy_eq _ _).symm

end LoopHomeo

end GenLoop

/-- The `n`th homotopy group at `x` defined as the quotient of `Ω^n x` by the
  `GenLoop.Homotopic` relation. -/
def HomotopyGroup (N X : Type*) [TopologicalSpace X] (x : X) : Type _ :=
  Quotient (GenLoop.Homotopic.setoid N x)

instance : Inhabited (HomotopyGroup N X x) :=
  inferInstanceAs <| Inhabited <| Quotient (GenLoop.Homotopic.setoid N x)

variable [DecidableEq N]

open GenLoop

/-- Equivalence between the homotopy group of X and the fundamental group of
  `Ω^{j // j ≠ i} x`. -/
def homotopyGroupEquivFundamentalGroup (i : N) :
    HomotopyGroup N X x ≃ FundamentalGroup (Ω^ { j // j ≠ i } X x) const := by
  refine Equiv.trans ?_ (CategoryTheory.Groupoid.isoEquivHom _ _).symm
  apply Quotient.congr (loopHomeo i).toEquiv
  exact fun p q => ⟨homotopicTo i, homotopicFrom i⟩

/-- Homotopy group of finite index, denoted as `π_n` within the Topology namespace. -/
abbrev HomotopyGroup.Pi (n) (X : Type*) [TopologicalSpace X] (x : X) :=
  HomotopyGroup (Fin n) _ x

@[inherit_doc] scoped[Topology] notation "π_" => HomotopyGroup.Pi

/-- The 0-dimensional generalized loops based at `x` are in bijection with `X`. -/
def genLoopHomeoOfIsEmpty (N x) [IsEmpty N] : Ω^ N X x ≃ₜ X where
  toFun f := f 0
  invFun y := ⟨ContinuousMap.const _ y, fun _ ⟨i, _⟩ => isEmptyElim i⟩
  left_inv f := by ext; exact congr_arg f (Subsingleton.elim _ _)
  continuous_invFun := ContinuousMap.const'.2.subtype_mk _

/-- The homotopy "group" indexed by an empty type is in bijection with
  the path components of `X`, aka the `ZerothHomotopy`. -/
def homotopyGroupEquivZerothHomotopyOfIsEmpty (N x) [IsEmpty N] :
    HomotopyGroup N X x ≃ ZerothHomotopy X :=
  Quotient.congr (genLoopHomeoOfIsEmpty N x).toEquiv
    (by
      -- joined iff homotopic
      intro a₁ a₂
      constructor <;> rintro ⟨H⟩
      exacts
        [⟨{ toFun := fun t => H ⟨t, isEmptyElim⟩
            source' := (H.apply_zero _).trans (congr_arg a₁ <| Subsingleton.elim _ _)
            target' := (H.apply_one _).trans (congr_arg a₂ <| Subsingleton.elim _ _) }⟩,
        ⟨{  toFun := fun t0 => H t0.fst
            map_zero_left := fun _ => H.source.trans (congr_arg a₁ <| Subsingleton.elim _ _)
            map_one_left := fun _ => H.target.trans (congr_arg a₂ <| Subsingleton.elim _ _)
            prop' := fun _ _ ⟨i, _⟩ => isEmptyElim i }⟩])

/-- The 0th homotopy "group" is in bijection with `ZerothHomotopy`. -/
def HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 X x ≃ ZerothHomotopy X :=
  homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0) x

/-- The 1-dimensional generalized loops based at `x` are in bijection with loops at `x`. -/
def genLoopEquivOfUnique (N) [Unique N] : Ω^ N X x ≃ Ω X x where
  toFun p :=
    Path.mk ⟨fun t => p fun _ => t, by continuity⟩
      (GenLoop.boundary _ (fun _ => 0) ⟨default, Or.inl rfl⟩)
      (GenLoop.boundary _ (fun _ => 1) ⟨default, Or.inr rfl⟩)
  invFun p :=
    ⟨⟨fun c => p (c default), by continuity⟩,
      by
      rintro y ⟨i, iH | iH⟩ <;> cases Unique.eq_default i <;> apply (congr_arg p iH).trans
      exacts [p.source, p.target]⟩
  left_inv p := by ext y; exact congr_arg p (eq_const_of_unique y).symm

/- TODO (?): deducing this from `homotopyGroupEquivFundamentalGroup` would require
  combination of `CategoryTheory.Functor.mapAut` and
  `FundamentalGroupoid.fundamentalGroupoidFunctor` applied to `genLoopHomeoOfIsEmpty`,
  with possibly worse defeq. -/
/-- The homotopy group at `x` indexed by a singleton is in bijection with the fundamental group,
  i.e. the loops based at `x` up to homotopy. -/
def homotopyGroupEquivFundamentalGroupOfUnique (N) [Unique N] :
    HomotopyGroup N X x ≃ FundamentalGroup X x := by
  refine Equiv.trans ?_ (CategoryTheory.Groupoid.isoEquivHom _ _).symm
  refine Quotient.congr (genLoopEquivOfUnique N) ?_
  intro a₁ a₂; constructor <;> rintro ⟨H⟩
  · exact
      ⟨{  toFun := fun tx => H (tx.fst, fun _ => tx.snd)
          map_zero_left := fun _ => H.apply_zero _
          map_one_left := fun _ => H.apply_one _
          prop' := fun t y iH => H.prop' _ _ ⟨default, iH⟩ }⟩
  refine
    ⟨⟨⟨⟨fun tx => H (tx.fst, tx.snd default), H.continuous.comp ?_⟩, fun y => ?_, fun y => ?_⟩, ?_⟩⟩
  · fun_prop
  · exact (H.apply_zero _).trans (congr_arg a₁ (eq_const_of_unique y).symm)
  · exact (H.apply_one _).trans (congr_arg a₂ (eq_const_of_unique y).symm)
  · rintro t y ⟨i, iH⟩
    cases Unique.eq_default i
    exact (H.eq_fst _ iH).trans (congr_arg a₁ (eq_const_of_unique y).symm)

/-- The first homotopy group at `x` is in bijection with the fundamental group. -/
def HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 X x ≃ FundamentalGroup X x :=
  homotopyGroupEquivFundamentalGroupOfUnique (Fin 1)

namespace HomotopyGroup

/-- Group structure on `HomotopyGroup N X x` for nonempty `N` (in particular `π_(n+1) X x`). -/
instance group (N) [DecidableEq N] [Nonempty N] : Group (HomotopyGroup N X x) :=
  (homotopyGroupEquivFundamentalGroup <| Classical.arbitrary N).group

/-- Group structure on `HomotopyGroup` obtained by pulling back path composition along the
  `i`th direction. The group structures for two different `i j : N` distribute over each
  other, and therefore are equal by the Eckmann-Hilton argument. -/
abbrev auxGroup (i : N) : Group (HomotopyGroup N X x) :=
  (homotopyGroupEquivFundamentalGroup i).group

theorem isUnital_auxGroup (i : N) :
    EckmannHilton.IsUnital (auxGroup i).mul (⟦const⟧ : HomotopyGroup N X x) where
  left_id := (auxGroup i).one_mul
  right_id := (auxGroup i).mul_one

theorem auxGroup_indep (i j : N) : (auxGroup i : Group (HomotopyGroup N X x)) = auxGroup j := by
  by_cases h : i = j; · rw [h]
  refine Group.ext (EckmannHilton.mul (isUnital_auxGroup i) (isUnital_auxGroup j) ?_)
  rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩
  change Quotient.mk' _ = _
  apply congr_arg Quotient.mk'
  simp only [fromLoop_trans_toLoop, transAt_distrib h, coe_toEquiv, loopHomeo_apply,
    coe_symm_toEquiv, loopHomeo_symm_apply]

theorem transAt_indep {i} (j) (f g : Ω^ N X x) :
    (⟦transAt i f g⟧ : HomotopyGroup N X x) = ⟦transAt j f g⟧ := by
  simp_rw [← fromLoop_trans_toLoop]
  let m := fun (G) (_ : Group G) => ((· * ·) : G → G → G)
  exact congr_fun₂ (congr_arg (m <| HomotopyGroup N X x) <| auxGroup_indep i j) ⟦g⟧ ⟦f⟧

theorem symmAt_indep {i} (j) (f : Ω^ N X x) :
    (⟦symmAt i f⟧ : HomotopyGroup N X x) = ⟦symmAt j f⟧ := by
  simp_rw [← fromLoop_symm_toLoop]
  let inv := fun (G) (_ : Group G) => ((·⁻¹) : G → G)
  exact congr_fun (congr_arg (inv <| HomotopyGroup N X x) <| auxGroup_indep i j) ⟦f⟧

/-- Characterization of multiplicative identity -/
theorem one_def [Nonempty N] : (1 : HomotopyGroup N X x) = ⟦const⟧ :=
  rfl

/-- Characterization of multiplication -/
theorem mul_spec [Nonempty N] {i} {p q : Ω^ N X x} :
    -- TODO: introduce `HomotopyGroup.mk` and remove defeq abuse.
    ((· * ·) : _ → _ → HomotopyGroup N X x) ⟦p⟧ ⟦q⟧ = ⟦transAt i q p⟧ := by
  rw [transAt_indep (Classical.arbitrary N) q, ← fromLoop_trans_toLoop]
  apply Quotient.sound
  rfl

/-- Characterization of multiplicative inverse -/
theorem inv_spec [Nonempty N] {i} {p : Ω^ N X x} :
    ((⟦p⟧)⁻¹ : HomotopyGroup N X x) = ⟦symmAt i p⟧ := by
  rw [symmAt_indep (Classical.arbitrary N) p, ← fromLoop_symm_toLoop]
  apply Quotient.sound
  rfl

/-- Multiplication on `HomotopyGroup N X x` is commutative for nontrivial `N`.
  In particular, multiplication on `π_(n+2)` is commutative. -/
instance commGroup [Nontrivial N] : CommGroup (HomotopyGroup N X x) :=
  let h := exists_ne (Classical.arbitrary N)
  @EckmannHilton.commGroup (HomotopyGroup N X x) _ 1 (isUnital_auxGroup <| Classical.choose h) _
    (by
      rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩
      apply congr_arg Quotient.mk'
      simp only [fromLoop_trans_toLoop, transAt_distrib <| Classical.choose_spec h, coe_toEquiv,
        loopHomeo_apply, coe_symm_toEquiv, loopHomeo_symm_apply])

end HomotopyGroup
