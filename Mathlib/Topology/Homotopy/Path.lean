/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Analysis.Convex.Basic

/-!
# Homotopy between paths

In this file, we define a `Homotopy` between two `Path`s. In addition, we define a relation
`Homotopic` on `Path`s, and prove that it is an equivalence relation.

## Definitions

* `Path.Homotopy p₀ p₁` is the type of homotopies between paths `p₀` and `p₁`
* `Path.Homotopy.refl p` is the constant homotopy between `p` and itself
* `Path.Homotopy.symm F` is the `Path.Homotopy p₁ p₀` defined by reversing the homotopy
* `Path.Homotopy.trans F G`, where `F : Path.Homotopy p₀ p₁`, `G : Path.Homotopy p₁ p₂` is the
  `Path.Homotopy p₀ p₂` defined by putting the first homotopy on `[0, 1/2]` and the second on
  `[1/2, 1]`
* `Path.Homotopy.hcomp F G`, where `F : Path.Homotopy p₀ q₀` and `G : Path.Homotopy p₁ q₁` is
  a `Path.Homotopy (p₀.trans p₁) (q₀.trans q₁)`
* `Path.Homotopic p₀ p₁` is the relation saying that there is a homotopy between `p₀` and `p₁`
* `Path.Homotopic.setoid x₀ x₁` is the setoid on `Path`s from `Path.Homotopic`
* `Path.Homotopic.Quotient x₀ x₁` is the quotient type from `Path x₀ x₀` by `Path.Homotopic.setoid`

-/

@[expose] public section


universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {x₀ x₁ x₂ x₃ : X}

noncomputable section

open unitInterval

namespace Path

/-- The type of homotopies between two paths.
-/
abbrev Homotopy (p₀ p₁ : Path x₀ x₁) :=
  ContinuousMap.HomotopyRel p₀.toContinuousMap p₁.toContinuousMap {0, 1}

namespace Homotopy

section

variable {p₀ p₁ : Path x₀ x₁}

theorem coeFn_injective : @Function.Injective (Homotopy p₀ p₁) (I × I → X) (⇑) :=
  DFunLike.coe_injective

@[simp]
theorem source (F : Homotopy p₀ p₁) (t : I) : F (t, 0) = x₀ :=
  calc F (t, 0) = p₀ 0 := ContinuousMap.HomotopyRel.eq_fst _ _ (.inl rfl)
  _ = x₀ := p₀.source

@[simp]
theorem target (F : Homotopy p₀ p₁) (t : I) : F (t, 1) = x₁ :=
  calc F (t, 1) = p₀ 1 := ContinuousMap.HomotopyRel.eq_fst _ _ (.inr rfl)
  _ = x₁ := p₀.target

/-- Evaluating a path homotopy at an intermediate point, giving us a `Path`.
-/
@[simps]
def eval (F : Homotopy p₀ p₁) (t : I) : Path x₀ x₁ where
  toFun := F.toHomotopy.curry t
  source' := by simp
  target' := by simp

@[simp]
theorem eval_zero (F : Homotopy p₀ p₁) : F.eval 0 = p₀ := by
  ext t
  simp

@[simp]
theorem eval_one (F : Homotopy p₀ p₁) : F.eval 1 = p₁ := by
  ext t
  simp

end

section

variable {p₀ p₁ p₂ : Path x₀ x₁}

/-- Given a path `p`, we can define a `Homotopy p p` by `F (t, x) = p x`.
-/
@[simps!]
def refl (p : Path x₀ x₁) : Homotopy p p :=
  ContinuousMap.HomotopyRel.refl p.toContinuousMap {0, 1}

/-- Given a `Homotopy p₀ p₁`, we can define a `Homotopy p₁ p₀` by reversing the homotopy.
-/
@[simps!]
def symm (F : Homotopy p₀ p₁) : Homotopy p₁ p₀ :=
  ContinuousMap.HomotopyRel.symm F

@[simp]
theorem symm_symm (F : Homotopy p₀ p₁) : F.symm.symm = F :=
  ContinuousMap.HomotopyRel.symm_symm F

theorem symm_bijective : Function.Bijective (Homotopy.symm : Homotopy p₀ p₁ → Homotopy p₁ p₀) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
Given `Homotopy p₀ p₁` and `Homotopy p₁ p₂`, we can define a `Homotopy p₀ p₂` by putting the first
homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) : Homotopy p₀ p₂ :=
  ContinuousMap.HomotopyRel.trans F G

theorem trans_apply (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) (x : I × I) :
    (F.trans G) x =
      if h : (x.1 : ℝ) ≤ 1 / 2 then
        F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else
        G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
  ContinuousMap.HomotopyRel.trans_apply _ _ _

theorem symm_trans (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) :
    (F.trans G).symm = G.symm.trans F.symm :=
  ContinuousMap.HomotopyRel.symm_trans _ _

/-- Casting a `Homotopy p₀ p₁` to a `Homotopy q₀ q₁` where `p₀ = q₀` and `p₁ = q₁`. -/
@[simps!]
def cast {p₀ p₁ q₀ q₁ : Path x₀ x₁} (F : Homotopy p₀ p₁) (h₀ : p₀ = q₀) (h₁ : p₁ = q₁) :
    Homotopy q₀ q₁ :=
  ContinuousMap.HomotopyRel.cast F (congr_arg _ h₀) (congr_arg _ h₁)

/-- If paths `p` and `q` are homotopic as paths `x ⟶ y`,
then they are homotopic as paths `x' ⟶ y'`, where `x' = x` and `y' = y`. -/
@[simp]
def pathCast {x x' y y' : X} {p q : Path x y} (F : p.Homotopy q) (hx : x' = x) (hy : y' = y) :
    (p.cast hx hy).Homotopy (q.cast hx hy) :=
  F

end

section

variable {p₀ q₀ : Path x₀ x₁} {p₁ q₁ : Path x₁ x₂}

/-- Suppose `p₀` and `q₀` are paths from `x₀` to `x₁`, `p₁` and `q₁` are paths from `x₁` to `x₂`.
Furthermore, suppose `F : Homotopy p₀ q₀` and `G : Homotopy p₁ q₁`. Then we can define a homotopy
from `p₀.trans p₁` to `q₀.trans q₁`.
-/
def hcomp (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) : Homotopy (p₀.trans p₁) (q₀.trans q₁) where
  toFun x :=
    if (x.2 : ℝ) ≤ 1 / 2 then (F.eval x.1).extend (2 * x.2) else (G.eval x.1).extend (2 * x.2 - 1)
  continuous_toFun := continuous_if_le (continuous_induced_dom.comp continuous_snd) continuous_const
    (F.toHomotopy.continuous.comp (by fun_prop)).continuousOn
    (G.toHomotopy.continuous.comp (by fun_prop)).continuousOn fun x hx ↦ by norm_num [hx]
  map_zero_left x := by simp [Path.trans]
  map_one_left x := by simp [Path.trans]
  prop' x t ht := by
    rcases ht with ht | ht
    · norm_num [ht]
    · rw [Set.mem_singleton_iff] at ht
      norm_num [ht]

theorem hcomp_apply (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) (x : I × I) :
    F.hcomp G x =
      if h : (x.2 : ℝ) ≤ 1 / 2 then
        F.eval x.1 ⟨2 * x.2, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.2.2.1, h⟩⟩
      else
        G.eval x.1
          ⟨2 * x.2 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.2.2.2⟩⟩ :=
  show ite _ _ _ = _ by split_ifs <;> exact Path.extend_apply _ _

theorem hcomp_half (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) (t : I) :
    F.hcomp G (t, ⟨1 / 2, by norm_num, by norm_num⟩) = x₁ :=
  show ite _ _ _ = _ by norm_num

end

/--
Suppose `p` is a path, then we have a homotopy from `p` to `p.reparam f` by the convexity of `I`.
-/
def reparam (p : Path x₀ x₁) (f : I → I) (hf : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    Homotopy p (p.reparam f hf hf₀ hf₁) where
  toFun x := p ⟨σ x.1 * x.2 + x.1 * f x.2,
    show (σ x.1 : ℝ) • (x.2 : ℝ) + (x.1 : ℝ) • (f x.2 : ℝ) ∈ I from
      convex_Icc _ _ x.2.2 (f x.2).2 (by unit_interval) (by unit_interval) (by simp)⟩
  map_zero_left x := by norm_num
  map_one_left x := by norm_num
  prop' t x hx := by
    rcases hx with hx | hx
    · rw [hx]
      simp [hf₀]
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      simp [hf₁]
  continuous_toFun := by fun_prop

/-- Suppose `F : Homotopy p q`. Then we have a `Homotopy p.symm q.symm` by reversing the second
argument.
-/
@[simps]
def symm₂ {p q : Path x₀ x₁} (F : p.Homotopy q) : p.symm.Homotopy q.symm where
  toFun x := F ⟨x.1, σ x.2⟩
  map_zero_left := by simp [Path.symm]
  map_one_left := by simp [Path.symm]
  prop' t x hx := by
    rcases hx with hx | hx
    · rw [hx]
      simp
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      simp

/--
Given `F : Homotopy p q`, and `f : C(X, Y)`, we can define a homotopy from `p.map f.continuous` to
`q.map f.continuous`.
-/
@[simps]
def map {p q : Path x₀ x₁} (F : p.Homotopy q) (f : C(X, Y)) :
    Homotopy (p.map f.continuous) (q.map f.continuous) where
  toFun := f ∘ F
  map_zero_left := by simp
  map_one_left := by simp
  prop' t x hx := by
    rcases hx with hx | hx
    · simp [hx]
    · rw [Set.mem_singleton_iff] at hx
      simp [hx]

end Homotopy

/-- Two paths `p₀` and `p₁` are `Path.Homotopic` if there exists a `Homotopy` between them.
-/
def Homotopic (p₀ p₁ : Path x₀ x₁) : Prop :=
  Nonempty (p₀.Homotopy p₁)

namespace Homotopic

@[refl]
theorem refl (p : Path x₀ x₁) : p.Homotopic p :=
  ⟨Homotopy.refl p⟩

@[symm]
theorem symm ⦃p₀ p₁ : Path x₀ x₁⦄ (h : p₀.Homotopic p₁) : p₁.Homotopic p₀ :=
  h.map Homotopy.symm

theorem symm₂ {p q : Path x₀ x₁} (h : p.Homotopic q) : p.symm.Homotopic q.symm :=
  h.map Homotopy.symm₂

@[trans]
theorem trans ⦃p₀ p₁ p₂ : Path x₀ x₁⦄ (h₀ : p₀.Homotopic p₁) (h₁ : p₁.Homotopic p₂) :
    p₀.Homotopic p₂ :=
  h₀.map2 Homotopy.trans h₁

theorem equivalence : Equivalence (@Homotopic X _ x₀ x₁) :=
  ⟨refl, (symm ·), (trans · ·)⟩

instance : IsEquiv (Path x₀ x₁) Homotopic where
  refl := refl
  symm := symm
  trans := trans

nonrec theorem map {p q : Path x₀ x₁} (h : p.Homotopic q) (f : C(X, Y)) :
    Homotopic (p.map f.continuous) (q.map f.continuous) :=
  h.map fun F => F.map f

theorem hcomp {p₀ p₁ : Path x₀ x₁} {q₀ q₁ : Path x₁ x₂} (hp : p₀.Homotopic p₁)
    (hq : q₀.Homotopic q₁) : (p₀.trans q₀).Homotopic (p₁.trans q₁) :=
  hp.map2 Homotopy.hcomp hq

/-- If paths `p` and `q` are homotopic as paths `x ⟶ y`,
then they are homotopic as paths `x' ⟶ y'`, where `x' = x` and `y' = y`. -/
theorem pathCast {p q : Path x₀ x₁} (hpq : p.Homotopic q) (hsource : x₂ = x₀) (htarget : x₃ = x₁) :
    (p.cast hsource htarget).Homotopic (q.cast hsource htarget) :=
  hpq

/--
The setoid on `Path`s defined by the equivalence relation `Path.Homotopic`. That is, two paths are
equivalent if there is a `Homotopy` between them.
-/
@[instance_reducible]
protected def setoid (x₀ x₁ : X) : Setoid (Path x₀ x₁) :=
  ⟨Homotopic, equivalence⟩

/-- The quotient on `Path x₀ x₁` by the equivalence relation `Path.Homotopic`.
-/
protected def Quotient (x₀ x₁ : X) :=
  Quotient (Homotopic.setoid x₀ x₁)

attribute [local instance] Homotopic.setoid

instance : Inhabited (Homotopic.Quotient () ()) :=
  ⟨Quotient.mk' <| Path.refl ()⟩

namespace Quotient

/-- The canonical map from `Path x₀ x₁` to `Path.Homotopic.Quotient x₀ x₁`. -/
def mk (p : Path x₀ x₁) : Path.Homotopic.Quotient x₀ x₁ :=
  Quotient.mk' p

theorem mk_surjective : Function.Surjective (@mk X _ x₀ x₁) :=
  Quotient.mk'_surjective

/-- `Path.Homotopic.Quotient.mk` is the simp normal form. -/
@[simp] theorem mk'_eq_mk (p : Path x₀ x₁) : Quotient.mk' p = mk p := rfl
@[simp] theorem mk''_eq_mk (p : Path x₀ x₁) : Quotient.mk'' p = mk p := rfl

theorem exact {p q : Path x₀ x₁} (h : Quotient.mk p = Quotient.mk q) :
    Homotopic p q := by
  exact _root_.Quotient.exact h

theorem eq {p q : Path x₀ x₁} : mk p = mk q ↔ Homotopic p q :=
  _root_.Quotient.eq

/--
A reasoning principle for quotients that allows proofs about quotients to assume that all values are
constructed with `Quotient.mk`.
-/
@[induction_eliminator]
protected theorem ind {x y : X} {motive : Homotopic.Quotient x y → Prop} :
    (mk : (a : Path x y) → motive (Quotient.mk a)) → (q : Homotopic.Quotient x y) → motive q :=
  Quot.ind

/--
A reasoning principle for quotients that allows proofs about quotients to assume that all values are
constructed with `Quotient.mk`. This is the two-variable version of `ind`.
-/
@[elab_as_elim]
protected theorem ind₂ {Y : Type*} [TopologicalSpace Y] {x₀ y₀ : X} {x₁ y₁ : Y}
    {motive : Homotopic.Quotient x₀ y₀ → Path.Homotopic.Quotient x₁ y₁ → Prop}
    (mk : (a : Path x₀ y₀) → (b : Path x₁ y₁) → motive (Quotient.mk a) (Quotient.mk b))
    (q₀ : Homotopic.Quotient x₀ y₀) (q₁ : Path.Homotopic.Quotient x₁ y₁) : motive q₀ q₁ := by
  induction q₀ using Quot.ind with | mk a =>
  induction q₁ using Quot.ind with | mk b =>
  exact mk a b

/-- The constant path homotopy class at a point. This is `Path.refl` descended to the quotient. -/
def refl (x : X) : Path.Homotopic.Quotient x x :=
  mk (Path.refl x)

@[simp, grind =]
theorem mk_refl (x : X) : mk (Path.refl x) = refl x :=
  rfl

/-- The reverse of a path homotopy class. This is `Path.symm` descended to the quotient. -/
def symm (P : Path.Homotopic.Quotient x₀ x₁) : Path.Homotopic.Quotient x₁ x₀ :=
  _root_.Quotient.map Path.symm (fun _ _ h => Homotopic.symm₂ h) P

@[simp, grind =]
theorem mk_symm (P : Path x₀ x₁) : mk P.symm = symm (mk P) :=
  rfl

/-- Cast a path homotopy class using equalities of endpoints. -/
def cast {x y : X} (γ : Homotopic.Quotient x y) {x' y'} (hx : x' = x) (hy : y' = y) :
    Homotopic.Quotient x' y' :=
  _root_.Quotient.map (fun p => p.cast hx hy) (fun _ _ h => h) γ

@[simp, grind =]
theorem mk_cast {x y : X} (P : Path x y) {x' y'} (hx : x' = x) (hy : y' = y) :
    mk (P.cast hx hy) = (mk P).cast hx hy :=
  rfl

@[simp, grind =]
theorem cast_rfl_rfl {x y : X} (γ : Homotopic.Quotient x y) : γ.cast rfl rfl = γ := by
  induction γ using Quotient.ind with | mk γ =>
  rfl

@[simp, grind =]
theorem cast_cast {x y : X} (γ : Homotopic.Quotient x y) {x' y'} (hx : x' = x) (hy : y' = y)
    {x'' y''} (hx' : x'' = x') (hy' : y'' = y') :
    (γ.cast hx hy).cast hx' hy' = γ.cast (hx'.trans hx) (hy'.trans hy) := by
  induction γ using Quotient.ind with | mk γ =>
  rfl

/-- The composition of path homotopy classes. This is `Path.trans` descended to the quotient. -/
def trans (P₀ : Path.Homotopic.Quotient x₀ x₁) (P₁ : Path.Homotopic.Quotient x₁ x₂) :
    Path.Homotopic.Quotient x₀ x₂ :=
  Quotient.map₂ Path.trans (fun (_ : Path x₀ x₁) _ hp (_ : Path x₁ x₂) _ hq => hcomp hp hq) P₀ P₁

@[deprecated (since := "2025-11-13")]
noncomputable alias _root_.Path.Homotopic.Quotient.comp := Quotient.trans

@[simp, grind =]
theorem mk_trans (P₀ : Path x₀ x₁) (P₁ : Path x₁ x₂) :
    mk (P₀.trans P₁) = Quotient.trans (mk P₀) (mk P₁) :=
  rfl

@[deprecated (since := "2025-11-13")]
noncomputable alias _root_.Path.Homotopic.comp_lift := Quotient.mk_trans

/-- The image of a path homotopy class `P₀` under a map `f`.
This is `Path.map` descended to the quotient. -/
def map (P₀ : Path.Homotopic.Quotient x₀ x₁) (f : C(X, Y)) :
    Path.Homotopic.Quotient (f x₀) (f x₁) :=
  _root_.Quotient.map
    (fun q : Path x₀ x₁ => q.map f.continuous) (fun _ _ h => Path.Homotopic.map h f) P₀

@[deprecated (since := "2025-11-13")]
noncomputable alias _root_.Path.Homotopic.Quotient.mapFn := Quotient.map

theorem mk_map (P₀ : Path x₀ x₁) (f : C(X, Y)) : mk (P₀.map f.continuous) = map (mk P₀) f :=
  rfl

@[deprecated (since := "2025-11-13")]
noncomputable alias _root_.Path.Homotopic.map_lift := Quotient.mk_map

end Quotient

-- Porting note: we didn't previously need the `α := ...` and `β := ...` hints.
theorem hpath_hext {p₁ : Path x₀ x₁} {p₂ : Path x₂ x₃} (hp : ∀ t, p₁ t = p₂ t) :
    HEq (α := Path.Homotopic.Quotient _ _) ⟦p₁⟧ (β := Path.Homotopic.Quotient _ _) ⟦p₂⟧ := by
  obtain rfl : x₀ = x₂ := by convert hp 0 <;> simp
  obtain rfl : x₁ = x₃ := by convert hp 1 <;> simp
  rw [heq_iff_eq]; congr; ext t; exact hp t

end Homotopic

/-- A path `Path x₀ x₁` generates a homotopy between constant functions `fun _ ↦ x₀` and
`fun _ ↦ x₁`. -/
@[simps!]
def toHomotopyConst (p : Path x₀ x₁) :
    (ContinuousMap.const Y x₀).Homotopy (ContinuousMap.const Y x₁) where
  toContinuousMap := p.toContinuousMap.comp ContinuousMap.fst
  map_zero_left _ := p.source
  map_one_left _ := p.target

end Path

/-- Two constant continuous maps with nonempty domain are homotopic if and only if their values are
joined by a path in the codomain. -/
@[simp]
theorem ContinuousMap.homotopic_const_iff [Nonempty Y] :
    (ContinuousMap.const Y x₀).Homotopic (ContinuousMap.const Y x₁) ↔ Joined x₀ x₁ := by
  inhabit Y
  refine ⟨fun ⟨H⟩ ↦ ⟨⟨(H.toContinuousMap.comp .prodSwap).curry default, ?_, ?_⟩⟩,
    fun ⟨p⟩ ↦ ⟨p.toHomotopyConst⟩⟩ <;> simp

namespace ContinuousMap.Homotopy

/-- Given a homotopy `H : f ∼ g`, get the path traced by the point `x` as it moves from
`f x` to `g x`.
-/
@[simps]
def evalAt {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (x : X) : Path (f x) (g x) where
  toFun t := H (t, x)
  source' := H.apply_zero x
  target' := H.apply_one x

@[simp]
theorem pathExtend_evalAt {f g : C(X, Y)} (H : f.Homotopy g) (x : X) :
    (H.evalAt x).extend = (fun t ↦ H.extend t x) := rfl

end ContinuousMap.Homotopy

namespace Path

/-! ### Path restriction to subintervals -/

open Set.Icc

variable {X : Type*} [TopologicalSpace X] {x y : X}

/-- Extract a subpath from `γ` on the interval `[a, b]`.
This is `γ` reparametrized via the affine map `t ↦ a + t (b - a)`. -/
def subpathOn (γ : Path x y) (a b : unitInterval) : Path (γ a) (γ b) where
  toFun t := γ (convexCombo a b t)
  source' := by simp
  target' := by simp

@[simp]
theorem subpathOn_apply (γ : Path x y) (a b : unitInterval) (t : unitInterval) :
    (γ.subpathOn a b) t = γ (convexCombo a b t) := by
  unfold subpathOn convexCombo
  simp only [Path.coe_mk_mk]

/-- Splitting a sub-path in halves rejoining them gives the original path. -/
private theorem subpathOn_trans_aux₁ (γ : Path x y) (a b : unitInterval) (_hab : a ≤ b) :
    ((γ.subpathOn a (Set.Icc.convexCombo a b unitInterval.half)).trans
      (γ.subpathOn (Set.Icc.convexCombo a b unitInterval.half) b)) =
    (γ.subpathOn a b) := by
  ext t
  simp only [trans, one_div, extend, Set.IccExtend, subpathOn, coe_mk',
    ContinuousMap.coe_mk, Function.comp_apply, Set.projIcc]
  split_ifs with h <;> (congr 1; ext; simp only [unitInterval.half, one_div]; norm_num)
  · have := t.2.1; have := t.2.2
    rw [min_eq_right (by linarith : 2 * (t : ℝ) ≤ 1),
        max_eq_right (by linarith : 0 ≤ 2 * (t : ℝ))]; ring
  · have := t.2.1; have := t.2.2
    rw [min_eq_right (by linarith : 2 * (t : ℝ) - 1 ≤ 1),
        max_eq_right (by linarith : 0 ≤ 2 * (t : ℝ) - 1)]; ring

/--
Splitting a sub-path into pieces and rejoining them is independent, up to homotopy,
of the splitting point.
-/
private theorem subpathOn_trans_aux₂ (γ : Path x y) (a b : unitInterval) (_hab : a ≤ b)
    (s t : unitInterval) :
    Path.Homotopic
      ((γ.subpathOn a (convexCombo a b s)).trans
        (γ.subpathOn (convexCombo a b s) b))
      ((γ.subpathOn a (convexCombo a b t)).trans
        (γ.subpathOn (convexCombo a b t) b)) := by
  refine ⟨{
      toFun := fun ⟨u, v⟩ =>
        ((γ.subpathOn a (convexCombo a b (convexCombo s t u))).trans
          (γ.subpathOn (convexCombo a b (convexCombo s t u)) b)) v
      continuous_toFun := by
        simp only [trans_apply, one_div, subpathOn_apply, convexCombo]
        simp only [← extend_apply, dite_eq_ite]
        apply continuous_if_le (hfg := by grind) <;> fun_prop
      map_zero_left v := by simp [Path.trans_apply]
      map_one_left v := by simp [Path.trans_apply]
      prop' u x hx := by
        rcases hx with rfl | rfl
        · simp [Path.trans]
        · simp [Path.trans]
          norm_num
    }⟩

/--
A subpath from a to b composed with a subpath from b to c is homotopic to
the subpath from a to c.
-/
theorem subpathOn_trans
    (γ : Path x y) (a b c : unitInterval) (hab : a ≤ b) (hbc : b ≤ c) :
    Path.Homotopic
      ((γ.subpathOn a b).trans (γ.subpathOn b c))
      (γ.subpathOn a c) := by
  suffices ∀ s : unitInterval,
    Path.Homotopic
      ((γ.subpathOn a (Set.Icc.convexCombo a c s)).trans
        (γ.subpathOn (Set.Icc.convexCombo a c s) c))
      (γ.subpathOn a c) by
    have hac : (a : ℝ) ≤ c := hab.trans hbc
    have hab' : (a : ℝ) ≤ b := hab
    have hbc' : (b : ℝ) ≤ c := hbc
    let s : unitInterval :=
      ⟨((b - a) / (c - a)),
        by
          by_cases hca : (c : ℝ) - a = 0
          · have hba : (b : ℝ) - a = 0 := by linarith
            simp [hca, hba]
          · exact div_nonneg (sub_nonneg.mpr hab') (sub_nonneg.mpr hac),
        by
          by_cases hca : (c : ℝ) - a = 0
          · have hba : (b : ℝ) - a = 0 := by linarith
            simp [hca, hba]
          · have hca_nonneg : 0 ≤ (c : ℝ) - a := sub_nonneg.mpr hac
            exact div_le_one_of_le₀ (by linarith) hca_nonneg⟩
    convert this s <;> exact Set.Icc.eq_convexCombo hab hbc
  intro s
  rw [← Path.subpathOn_trans_aux₁ γ a c (hab.trans hbc)]
  apply Path.subpathOn_trans_aux₂ γ a c (hab.trans hbc) s

/-- A subpath from a point to itself is the constant path. -/
theorem subpathOn_self_eq_refl (γ : Path x y) (a : unitInterval) :
    γ.subpathOn a a = Path.refl (γ a) := by
  ext t
  simp [Path.refl, Path.subpathOn]

/-- A subpath from a point to itself is homotopic to the constant path. -/
theorem subpathOn_self (γ : Path x y) (a : unitInterval) :
    Homotopic (γ.subpathOn a a) (Path.refl (γ a)) := by
  simpa [subpathOn_self_eq_refl] using Homotopic.refl (Path.refl (γ a))

/-- The subpath from `0` to `1` equals the original path, after casting the endpoints of `γ`
back to `γ 0` and `γ 1`.

The cast is on the RHS so that the lemma rewrites `γ.subpathOn 0 1` (the cluttered form) to
`γ.cast …` (which names the simple `γ` up to a cast); this matches the direction of the
`@[simp]` lemma `Path.Homotopic.Quotient.subpathOn_zero_one`. -/
theorem subpathOn_zero_one_eq_cast (γ : Path x y) :
    γ.subpathOn 0 1 = γ.cast γ.source γ.target := by
  ext t
  simp [Path.cast, Path.subpathOn]

/-- The subpath from `0` to `1` is homotopic to the original path, up to casting endpoints. -/
theorem subpathOn_zero_one (γ : Path x y) :
    Homotopic (γ.subpathOn 0 1) (γ.cast γ.source γ.target) := by
  rw [subpathOn_zero_one_eq_cast]

namespace Homotopic.Quotient

@[simp]
theorem subpathOn_trans {x y : X} (p : Path x y)
    (a b c : unitInterval) (hab : a ≤ b) (hbc : b ≤ c) :
    trans (mk (p.subpathOn a b)) (mk (p.subpathOn b c)) =
      mk (p.subpathOn a c) := by
  simp only [← mk_trans, eq]
  exact Path.subpathOn_trans p a b c hab hbc

@[simp]
theorem subpathOn_self {x y : X} (p : Path x y) (a : unitInterval) :
    mk (p.subpathOn a a) = refl (p a) := by
  simp only [← mk_refl, eq]
  exact Path.subpathOn_self p a

@[simp]
theorem subpathOn_zero_one {x y : X} (p : Path x y) :
    mk (p.subpathOn 0 1) = (mk p).cast (by simp) (by simp) := by
  simp only [← mk_cast, eq]
  exact Path.subpathOn_zero_one p

end Homotopic.Quotient

end Path
