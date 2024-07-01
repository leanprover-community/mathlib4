/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.AddTorsor
import Mathlib.Topology.Algebra.Constructions
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.Topology.Algebra.ConstMulAction

#align_import topology.algebra.mul_action from "leanprover-community/mathlib"@"d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46"

/-!
# Continuous monoid action

In this file we define class `ContinuousSMul`. We say `ContinuousSMul M X` if `M` acts on `X` and
the map `(c, x) ↦ c • x` is continuous on `M × X`. We reuse this class for topological
(semi)modules, vector spaces and algebras.

## Main definitions

* `ContinuousSMul M X` : typeclass saying that the map `(c, x) ↦ c • x` is continuous
  on `M × X`;
* `Units.continuousSMul`: scalar multiplication by `Mˣ` is continuous when scalar
  multiplication by `M` is continuous. This allows `Homeomorph.smul` to be used with on monoids
  with `G = Mˣ`.

-- Porting note: These have all moved
* `Homeomorph.smul_of_ne_zero`: if a group with zero `G₀` (e.g., a field) acts on `X` and `c : G₀`
  is a nonzero element of `G₀`, then scalar multiplication by `c` is a homeomorphism of `X`;
* `Homeomorph.smul`: scalar multiplication by an element of a group `G` acting on `X`
  is a homeomorphism of `X`.

## Main results

Besides homeomorphisms mentioned above, in this file we provide lemmas like `Continuous.smul`
or `Filter.Tendsto.smul` that provide dot-syntax access to `ContinuousSMul`.
-/

open Topology Pointwise

open Filter

/-- Class `ContinuousSMul M X` says that the scalar multiplication `(•) : M → X → X`
is continuous in both arguments. We use the same class for all kinds of multiplicative actions,
including (semi)modules and algebras. -/
class ContinuousSMul (M X : Type*) [SMul M X] [TopologicalSpace M] [TopologicalSpace X] :
    Prop where
  /-- The scalar multiplication `(•)` is continuous. -/
  continuous_smul : Continuous fun p : M × X => p.1 • p.2
#align has_continuous_smul ContinuousSMul

export ContinuousSMul (continuous_smul)

/-- Class `ContinuousVAdd M X` says that the additive action `(+ᵥ) : M → X → X`
is continuous in both arguments. We use the same class for all kinds of additive actions,
including (semi)modules and algebras. -/
class ContinuousVAdd (M X : Type*) [VAdd M X] [TopologicalSpace M] [TopologicalSpace X] :
    Prop where
  /-- The additive action `(+ᵥ)` is continuous. -/
  continuous_vadd : Continuous fun p : M × X => p.1 +ᵥ p.2
#align has_continuous_vadd ContinuousVAdd

export ContinuousVAdd (continuous_vadd)

attribute [to_additive] ContinuousSMul

section Main

variable {M X Y α : Type*} [TopologicalSpace M] [TopologicalSpace X] [TopologicalSpace Y]

section SMul

variable [SMul M X] [ContinuousSMul M X]

@[to_additive]
instance : ContinuousSMul (ULift M) X :=
  ⟨(continuous_smul (M := M)).comp₂ (continuous_uLift_down.comp continuous_fst) continuous_snd⟩

@[to_additive]
instance (priority := 100) ContinuousSMul.continuousConstSMul : ContinuousConstSMul M X where
  continuous_const_smul _ := continuous_smul.comp (continuous_const.prod_mk continuous_id)
#align has_continuous_smul.has_continuous_const_smul ContinuousSMul.continuousConstSMul
#align has_continuous_vadd.has_continuous_const_vadd ContinuousVAdd.continuousConstVAdd

@[to_additive]
theorem Filter.Tendsto.smul {f : α → M} {g : α → X} {l : Filter α} {c : M} {a : X}
    (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) :
    Tendsto (fun x => f x • g x) l (𝓝 <| c • a) :=
  (continuous_smul.tendsto _).comp (hf.prod_mk_nhds hg)
#align filter.tendsto.smul Filter.Tendsto.smul
#align filter.tendsto.vadd Filter.Tendsto.vadd

@[to_additive]
theorem Filter.Tendsto.smul_const {f : α → M} {l : Filter α} {c : M} (hf : Tendsto f l (𝓝 c))
    (a : X) : Tendsto (fun x => f x • a) l (𝓝 (c • a)) :=
  hf.smul tendsto_const_nhds
#align filter.tendsto.smul_const Filter.Tendsto.smul_const
#align filter.tendsto.vadd_const Filter.Tendsto.vadd_const

variable {f : Y → M} {g : Y → X} {b : Y} {s : Set Y}

@[to_additive]
theorem ContinuousWithinAt.smul (hf : ContinuousWithinAt f s b) (hg : ContinuousWithinAt g s b) :
    ContinuousWithinAt (fun x => f x • g x) s b :=
  Filter.Tendsto.smul hf hg
#align continuous_within_at.smul ContinuousWithinAt.smul
#align continuous_within_at.vadd ContinuousWithinAt.vadd

@[to_additive (attr := fun_prop)]
theorem ContinuousAt.smul (hf : ContinuousAt f b) (hg : ContinuousAt g b) :
    ContinuousAt (fun x => f x • g x) b :=
  Filter.Tendsto.smul hf hg
#align continuous_at.smul ContinuousAt.smul
#align continuous_at.vadd ContinuousAt.vadd

@[to_additive (attr := fun_prop)]
theorem ContinuousOn.smul (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => f x • g x) s := fun x hx => (hf x hx).smul (hg x hx)
#align continuous_on.smul ContinuousOn.smul
#align continuous_on.vadd ContinuousOn.vadd

@[to_additive (attr := continuity, fun_prop)]
theorem Continuous.smul (hf : Continuous f) (hg : Continuous g) : Continuous fun x => f x • g x :=
  continuous_smul.comp (hf.prod_mk hg)
#align continuous.smul Continuous.smul
#align continuous.vadd Continuous.vadd

/-- If a scalar action is central, then its right action is continuous when its left action is. -/
@[to_additive "If an additive action is central, then its right action is continuous when its left
action is."]
instance ContinuousSMul.op [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] : ContinuousSMul Mᵐᵒᵖ X :=
  ⟨by
    suffices Continuous fun p : M × X => MulOpposite.op p.fst • p.snd from
      this.comp (MulOpposite.continuous_unop.prod_map continuous_id)
    simpa only [op_smul_eq_smul] using (continuous_smul : Continuous fun p : M × X => _)⟩
#align has_continuous_smul.op ContinuousSMul.op
#align has_continuous_vadd.op ContinuousVAdd.op

@[to_additive]
instance MulOpposite.continuousSMul : ContinuousSMul M Xᵐᵒᵖ :=
  ⟨MulOpposite.continuous_op.comp <|
      continuous_smul.comp <| continuous_id.prod_map MulOpposite.continuous_unop⟩
#align mul_opposite.has_continuous_smul MulOpposite.continuousSMul
#align add_opposite.has_continuous_vadd AddOpposite.continuousVAdd

@[to_additive]
protected theorem Specializes.smul {a b : M} {x y : X} (h₁ : a ⤳ b) (h₂ : x ⤳ y) :
    (a • x) ⤳ (b • y) :=
  (h₁.prod h₂).map continuous_smul

@[to_additive]
protected theorem Inseparable.smul {a b : M} {x y : X} (h₁ : Inseparable a b)
    (h₂ : Inseparable x y) : Inseparable (a • x) (b • y) :=
  (h₁.prod h₂).map continuous_smul

@[to_additive]
lemma IsCompact.smul_set {k : Set M} {u : Set X} (hk : IsCompact k) (hu : IsCompact u) :
    IsCompact (k • u) := by
  rw [← Set.image_smul_prod]
  exact IsCompact.image (hk.prod hu) continuous_smul

@[to_additive]
lemma smul_set_closure_subset (K : Set M) (L : Set X) :
    closure K • closure L ⊆ closure (K • L) :=
  Set.smul_subset_iff.2 fun _x hx _y hy ↦ map_mem_closure₂ continuous_smul hx hy fun _a ha _b hb ↦
    Set.smul_mem_smul ha hb

/-- Suppose that `N` acts on `X` and `M` continuously acts on `Y`.
Suppose that `g : Y → X` is an action homomorphism in the following sense:
there exists a continuous function `f : N → M` such that `g (c • x) = f c • g x`.
Then the action of `N` on `X` is continuous as well.

In many cases, `f = id` so that `g` is an action homomorphism in the sense of `MulActionHom`.
However, this version also works for semilinear maps and `f = Units.val`. -/
@[to_additive
  "Suppose that `N` additively acts on `X` and `M` continuously additively acts on `Y`.
Suppose that `g : Y → X` is an additive action homomorphism in the following sense:
there exists a continuous function `f : N → M` such that `g (c +ᵥ x) = f c +ᵥ g x`.
Then the action of `N` on `X` is continuous as well.

In many cases, `f = id` so that `g` is an action homomorphism in the sense of `AddActionHom`.
However, this version also works for `f = AddUnits.val`."]
lemma Inducing.continuousSMul {N : Type*} [SMul N Y] [TopologicalSpace N] {f : N → M}
    (hg : Inducing g) (hf : Continuous f) (hsmul : ∀ {c x}, g (c • x) = f c • g x) :
    ContinuousSMul N Y where
  continuous_smul := by
    simpa only [hg.continuous_iff, Function.comp_def, hsmul]
      using (hf.comp continuous_fst).smul <| hg.continuous.comp continuous_snd

@[to_additive]
instance SMulMemClass.continuousSMul {S : Type*} [SetLike S X] [SMulMemClass S M X] (s : S) :
    ContinuousSMul M s :=
  inducing_subtype_val.continuousSMul continuous_id rfl

end SMul

section Monoid

variable [Monoid M] [MulAction M X] [ContinuousSMul M X]

@[to_additive]
instance Units.continuousSMul : ContinuousSMul Mˣ X :=
  inducing_id.continuousSMul Units.continuous_val rfl
#align units.has_continuous_smul Units.continuousSMul
#align add_units.has_continuous_vadd AddUnits.continuousVAdd

/-- If an action is continuous, then composing this action with a continuous homomorphism gives
again a continuous action. -/
@[to_additive]
theorem MulAction.continuousSMul_compHom
    {N : Type*} [TopologicalSpace N] [Monoid N] {f : N →* M} (hf : Continuous f) :
    letI : MulAction N X := MulAction.compHom _ f
    ContinuousSMul N X := by
  let _ : MulAction N X := MulAction.compHom _ f
  exact ⟨(hf.comp continuous_fst).smul continuous_snd⟩

@[to_additive]
instance Submonoid.continuousSMul {S : Submonoid M} : ContinuousSMul S X :=
  inducing_id.continuousSMul continuous_subtype_val rfl

end Monoid

section Group

variable [Group M] [MulAction M X] [ContinuousSMul M X]

@[to_additive]
instance Subgroup.continuousSMul {S : Subgroup M} : ContinuousSMul S X :=
  S.toSubmonoid.continuousSMul

end Group

@[to_additive]
instance Prod.continuousSMul [SMul M X] [SMul M Y] [ContinuousSMul M X] [ContinuousSMul M Y] :
    ContinuousSMul M (X × Y) :=
  ⟨(continuous_fst.smul (continuous_fst.comp continuous_snd)).prod_mk
      (continuous_fst.smul (continuous_snd.comp continuous_snd))⟩

@[to_additive]
instance {ι : Type*} {γ : ι → Type*} [∀ i, TopologicalSpace (γ i)] [∀ i, SMul M (γ i)]
    [∀ i, ContinuousSMul M (γ i)] : ContinuousSMul M (∀ i, γ i) :=
  ⟨continuous_pi fun i =>
      (continuous_fst.smul continuous_snd).comp <|
        continuous_fst.prod_mk ((continuous_apply i).comp continuous_snd)⟩

end Main

section LatticeOps

variable {ι : Sort*} {M X : Type*} [TopologicalSpace M] [SMul M X]

@[to_additive]
theorem continuousSMul_sInf {ts : Set (TopologicalSpace X)}
    (h : ∀ t ∈ ts, @ContinuousSMul M X _ _ t) : @ContinuousSMul M X _ _ (sInf ts) :=
  -- Porting note: {} doesn't work because `sInf ts` isn't found by TC search. `(_)` finds it by
  -- unification instead.
  @ContinuousSMul.mk M X _ _ (_) <| by
      -- Porting note: needs `( :)`
      rw [← (@sInf_singleton _ _ ‹TopologicalSpace M›:)]
      exact
        continuous_sInf_rng.2 fun t ht =>
          continuous_sInf_dom₂ (Eq.refl _) ht
            (@ContinuousSMul.continuous_smul _ _ _ _ t (h t ht))
#align has_continuous_smul_Inf continuousSMul_sInf
#align has_continuous_vadd_Inf continuousVAdd_sInf

@[to_additive]
theorem continuousSMul_iInf {ts' : ι → TopologicalSpace X}
    (h : ∀ i, @ContinuousSMul M X _ _ (ts' i)) : @ContinuousSMul M X _ _ (⨅ i, ts' i) :=
  continuousSMul_sInf <| Set.forall_mem_range.mpr h
#align has_continuous_smul_infi continuousSMul_iInf
#align has_continuous_vadd_infi continuousVAdd_iInf

@[to_additive]
theorem continuousSMul_inf {t₁ t₂ : TopologicalSpace X} [@ContinuousSMul M X _ _ t₁]
    [@ContinuousSMul M X _ _ t₂] : @ContinuousSMul M X _ _ (t₁ ⊓ t₂) := by
  rw [inf_eq_iInf]
  refine continuousSMul_iInf fun b => ?_
  cases b <;> assumption
#align has_continuous_smul_inf continuousSMul_inf
#align has_continuous_vadd_inf continuousVAdd_inf

end LatticeOps

section AddTorsor

variable (G : Type*) (P : Type*) [AddGroup G] [AddTorsor G P] [TopologicalSpace G]
variable [PreconnectedSpace G] [TopologicalSpace P] [ContinuousVAdd G P]

/-- An `AddTorsor` for a connected space is a connected space. This is not an instance because
it loops for a group as a torsor over itself. -/
protected theorem AddTorsor.connectedSpace : ConnectedSpace P :=
  { isPreconnected_univ := by
      convert
        isPreconnected_univ.image (Equiv.vaddConst (Classical.arbitrary P) : G → P)
          (continuous_id.vadd continuous_const).continuousOn
      rw [Set.image_univ, Equiv.range_eq_univ]
    toNonempty := inferInstance }
#align add_torsor.connected_space AddTorsor.connectedSpace

end AddTorsor
