/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Convex.Basic

#align_import topology.homotopy.path from "leanprover-community/mathlib"@"bb9d1c5085e0b7ea619806a68c5021927cecb2a6"

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
#align path.homotopy Path.Homotopy

namespace Homotopy

section

variable {p₀ p₁ : Path x₀ x₁}

theorem coeFn_injective : @Function.Injective (Homotopy p₀ p₁) (I × I → X) (⇑) :=
  DFunLike.coe_injective
#align path.homotopy.coe_fn_injective Path.Homotopy.coeFn_injective

@[simp]
theorem source (F : Homotopy p₀ p₁) (t : I) : F (t, 0) = x₀ :=
  calc F (t, 0) = p₀ 0 := ContinuousMap.HomotopyRel.eq_fst _ _ (.inl rfl)
  _ = x₀ := p₀.source
#align path.homotopy.source Path.Homotopy.source

@[simp]
theorem target (F : Homotopy p₀ p₁) (t : I) : F (t, 1) = x₁ :=
  calc F (t, 1) = p₀ 1 := ContinuousMap.HomotopyRel.eq_fst _ _ (.inr rfl)
  _ = x₁ := p₀.target
#align path.homotopy.target Path.Homotopy.target

/-- Evaluating a path homotopy at an intermediate point, giving us a `Path`.
-/
def eval (F : Homotopy p₀ p₁) (t : I) : Path x₀ x₁ where
  toFun := F.toHomotopy.curry t
  source' := by simp
  target' := by simp
#align path.homotopy.eval Path.Homotopy.eval

@[simp]
theorem eval_zero (F : Homotopy p₀ p₁) : F.eval 0 = p₀ := by
  ext t
  simp [eval]
#align path.homotopy.eval_zero Path.Homotopy.eval_zero

@[simp]
theorem eval_one (F : Homotopy p₀ p₁) : F.eval 1 = p₁ := by
  ext t
  simp [eval]
#align path.homotopy.eval_one Path.Homotopy.eval_one

end

section

variable {p₀ p₁ p₂ : Path x₀ x₁}

/-- Given a path `p`, we can define a `Homotopy p p` by `F (t, x) = p x`.
-/
@[simps!]
def refl (p : Path x₀ x₁) : Homotopy p p :=
  ContinuousMap.HomotopyRel.refl p.toContinuousMap {0, 1}
#align path.homotopy.refl Path.Homotopy.refl

/-- Given a `Homotopy p₀ p₁`, we can define a `Homotopy p₁ p₀` by reversing the homotopy.
-/
@[simps!]
def symm (F : Homotopy p₀ p₁) : Homotopy p₁ p₀ :=
  ContinuousMap.HomotopyRel.symm F
#align path.homotopy.symm Path.Homotopy.symm

@[simp]
theorem symm_symm (F : Homotopy p₀ p₁) : F.symm.symm = F :=
  ContinuousMap.HomotopyRel.symm_symm F
#align path.homotopy.symm_symm Path.Homotopy.symm_symm

theorem symm_bijective : Function.Bijective (Homotopy.symm : Homotopy p₀ p₁ → Homotopy p₁ p₀) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
Given `Homotopy p₀ p₁` and `Homotopy p₁ p₂`, we can define a `Homotopy p₀ p₂` by putting the first
homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) : Homotopy p₀ p₂ :=
  ContinuousMap.HomotopyRel.trans F G
#align path.homotopy.trans Path.Homotopy.trans

theorem trans_apply (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) (x : I × I) :
    (F.trans G) x =
      if h : (x.1 : ℝ) ≤ 1 / 2 then
        F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else
        G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
  ContinuousMap.HomotopyRel.trans_apply _ _ _
#align path.homotopy.trans_apply Path.Homotopy.trans_apply

theorem symm_trans (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) :
    (F.trans G).symm = G.symm.trans F.symm :=
  ContinuousMap.HomotopyRel.symm_trans _ _
#align path.homotopy.symm_trans Path.Homotopy.symm_trans

/-- Casting a `Homotopy p₀ p₁` to a `Homotopy q₀ q₁` where `p₀ = q₀` and `p₁ = q₁`. -/
@[simps!]
def cast {p₀ p₁ q₀ q₁ : Path x₀ x₁} (F : Homotopy p₀ p₁) (h₀ : p₀ = q₀) (h₁ : p₁ = q₁) :
    Homotopy q₀ q₁ :=
  ContinuousMap.HomotopyRel.cast F (congr_arg _ h₀) (congr_arg _ h₁)
#align path.homotopy.cast Path.Homotopy.cast

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
    (F.toHomotopy.continuous.comp (by continuity)).continuousOn
    (G.toHomotopy.continuous.comp (by continuity)).continuousOn fun x hx => by norm_num [hx]
  map_zero_left x := by simp [Path.trans]
  map_one_left x := by simp [Path.trans]
  prop' x t ht := by
    cases' ht with ht ht
    · set_option tactic.skipAssignedInstances false in norm_num [ht]
    · rw [Set.mem_singleton_iff] at ht
      set_option tactic.skipAssignedInstances false in norm_num [ht]
#align path.homotopy.hcomp Path.Homotopy.hcomp

theorem hcomp_apply (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) (x : I × I) :
    F.hcomp G x =
      if h : (x.2 : ℝ) ≤ 1 / 2 then
        F.eval x.1 ⟨2 * x.2, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.2.2.1, h⟩⟩
      else
        G.eval x.1
          ⟨2 * x.2 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.2.2.2⟩⟩ :=
  show ite _ _ _ = _ by split_ifs <;> exact Path.extend_extends _ _
#align path.homotopy.hcomp_apply Path.Homotopy.hcomp_apply

theorem hcomp_half (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) (t : I) :
    F.hcomp G (t, ⟨1 / 2, by norm_num, by norm_num⟩) = x₁ :=
  show ite _ _ _ = _ by norm_num
#align path.homotopy.hcomp_half Path.Homotopy.hcomp_half

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
    cases' hx with hx hx
    · rw [hx]
      simp [hf₀]
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      simp [hf₁]
  continuous_toFun := by
    -- Porting note: was `continuity` in auto-param
    refine continuous_const.path_eval ?_
    apply Continuous.subtype_mk
    apply Continuous.add <;> apply Continuous.mul
    · exact continuous_induced_dom.comp (unitInterval.continuous_symm.comp continuous_fst)
    · continuity
    · continuity
    · continuity
#align path.homotopy.reparam Path.Homotopy.reparam

/-- Suppose `F : Homotopy p q`. Then we have a `Homotopy p.symm q.symm` by reversing the second
argument.
-/
@[simps]
def symm₂ {p q : Path x₀ x₁} (F : p.Homotopy q) : p.symm.Homotopy q.symm where
  toFun x := F ⟨x.1, σ x.2⟩
  map_zero_left := by simp [Path.symm]
  map_one_left := by simp [Path.symm]
  prop' t x hx := by
    cases' hx with hx hx
    · rw [hx]
      simp
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      simp
#align path.homotopy.symm₂ Path.Homotopy.symm₂

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
    cases' hx with hx hx
    · simp [hx]
    · rw [Set.mem_singleton_iff] at hx
      simp [hx]
#align path.homotopy.map Path.Homotopy.map

end Homotopy

/-- Two paths `p₀` and `p₁` are `Path.Homotopic` if there exists a `Homotopy` between them.
-/
def Homotopic (p₀ p₁ : Path x₀ x₁) : Prop :=
  Nonempty (p₀.Homotopy p₁)
#align path.homotopic Path.Homotopic

namespace Homotopic

@[refl]
theorem refl (p : Path x₀ x₁) : p.Homotopic p :=
  ⟨Homotopy.refl p⟩
#align path.homotopic.refl Path.Homotopic.refl

@[symm]
theorem symm ⦃p₀ p₁ : Path x₀ x₁⦄ (h : p₀.Homotopic p₁) : p₁.Homotopic p₀ :=
  h.map Homotopy.symm
#align path.homotopic.symm Path.Homotopic.symm

@[trans]
theorem trans ⦃p₀ p₁ p₂ : Path x₀ x₁⦄ (h₀ : p₀.Homotopic p₁) (h₁ : p₁.Homotopic p₂) :
    p₀.Homotopic p₂ :=
  h₀.map2 Homotopy.trans h₁
#align path.homotopic.trans Path.Homotopic.trans

theorem equivalence : Equivalence (@Homotopic X _ x₀ x₁) :=
  ⟨refl, (symm ·), (trans · ·)⟩
#align path.homotopic.equivalence Path.Homotopic.equivalence

nonrec theorem map {p q : Path x₀ x₁} (h : p.Homotopic q) (f : C(X, Y)) :
    Homotopic (p.map f.continuous) (q.map f.continuous) :=
  h.map fun F => F.map f
#align path.homotopic.map Path.Homotopic.map

theorem hcomp {p₀ p₁ : Path x₀ x₁} {q₀ q₁ : Path x₁ x₂} (hp : p₀.Homotopic p₁)
    (hq : q₀.Homotopic q₁) : (p₀.trans q₀).Homotopic (p₁.trans q₁) :=
  hp.map2 Homotopy.hcomp hq
#align path.homotopic.hcomp Path.Homotopic.hcomp

/--
The setoid on `Path`s defined by the equivalence relation `Path.Homotopic`. That is, two paths are
equivalent if there is a `Homotopy` between them.
-/
protected def setoid (x₀ x₁ : X) : Setoid (Path x₀ x₁) :=
  ⟨Homotopic, equivalence⟩
#align path.homotopic.setoid Path.Homotopic.setoid

/-- The quotient on `Path x₀ x₁` by the equivalence relation `Path.Homotopic`.
-/
protected def Quotient (x₀ x₁ : X) :=
  Quotient (Homotopic.setoid x₀ x₁)
#align path.homotopic.quotient Path.Homotopic.Quotient

attribute [local instance] Homotopic.setoid

instance : Inhabited (Homotopic.Quotient () ()) :=
  ⟨Quotient.mk' <| Path.refl ()⟩

/-- The composition of path homotopy classes. This is `Path.trans` descended to the quotient. -/
def Quotient.comp (P₀ : Path.Homotopic.Quotient x₀ x₁) (P₁ : Path.Homotopic.Quotient x₁ x₂) :
    Path.Homotopic.Quotient x₀ x₂ :=
  Quotient.map₂ Path.trans (fun (_ : Path x₀ x₁) _ hp (_ : Path x₁ x₂) _ hq => hcomp hp hq) P₀ P₁
#align path.homotopic.quotient.comp Path.Homotopic.Quotient.comp

theorem comp_lift (P₀ : Path x₀ x₁) (P₁ : Path x₁ x₂) : ⟦P₀.trans P₁⟧ = Quotient.comp ⟦P₀⟧ ⟦P₁⟧ :=
  rfl
#align path.homotopic.comp_lift Path.Homotopic.comp_lift

/-- The image of a path homotopy class `P₀` under a map `f`.
    This is `Path.map` descended to the quotient. -/
def Quotient.mapFn (P₀ : Path.Homotopic.Quotient x₀ x₁) (f : C(X, Y)) :
    Path.Homotopic.Quotient (f x₀) (f x₁) :=
  Quotient.map (fun q : Path x₀ x₁ => q.map f.continuous) (fun _ _ h => Path.Homotopic.map h f) P₀
#align path.homotopic.quotient.map_fn Path.Homotopic.Quotient.mapFn

theorem map_lift (P₀ : Path x₀ x₁) (f : C(X, Y)) : ⟦P₀.map f.continuous⟧ = Quotient.mapFn ⟦P₀⟧ f :=
  rfl
#align path.homotopic.map_lift Path.Homotopic.map_lift

-- Porting note: Type was originally `HEq ⟦p₁⟧ ⟦p₂⟧`
theorem hpath_hext {p₁ : Path x₀ x₁} {p₂ : Path x₂ x₃} (hp : ∀ t, p₁ t = p₂ t) :
    @HEq (Path.Homotopic.Quotient _ _) ⟦p₁⟧ (Path.Homotopic.Quotient _ _) ⟦p₂⟧ := by
  obtain rfl : x₀ = x₂ := by convert hp 0 <;> simp
  obtain rfl : x₁ = x₃ := by convert hp 1 <;> simp
  rw [heq_iff_eq]; congr; ext t; exact hp t
#align path.homotopic.hpath_hext Path.Homotopic.hpath_hext

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
def evalAt {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
    (H : ContinuousMap.Homotopy f g) (x : X) : Path (f x) (g x) where
  toFun t := H (t, x)
  source' := H.apply_zero x
  target' := H.apply_one x
#align continuous_map.homotopy.eval_at ContinuousMap.Homotopy.evalAt

end ContinuousMap.Homotopy
