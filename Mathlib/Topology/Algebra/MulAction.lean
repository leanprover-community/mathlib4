/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.AddTorsor.Defs
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Order.Filter.Pointwise
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Connected.Basic

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

## Main results

Besides homeomorphisms mentioned above, in this file we provide lemmas like `Continuous.smul`
or `Filter.Tendsto.smul` that provide dot-syntax access to `ContinuousSMul`.
-/

@[expose] public section

open Topology Pointwise

open Filter

/-- Class `ContinuousSMul M X` says that the scalar multiplication `(•) : M → X → X`
is continuous in both arguments. We use the same class for all kinds of multiplicative actions,
including (semi)modules and algebras. -/
class ContinuousSMul (M X : Type*) [SMul M X] [TopologicalSpace M] [TopologicalSpace X] :
    Prop where
  /-- The scalar multiplication `(•)` is continuous. -/
  continuous_smul : Continuous fun p : M × X => p.1 • p.2

export ContinuousSMul (continuous_smul)

/-- Class `ContinuousVAdd M X` says that the additive action `(+ᵥ) : M → X → X`
is continuous in both arguments. We use the same class for all kinds of additive actions,
including (semi)modules and algebras. -/
class ContinuousVAdd (M X : Type*) [VAdd M X] [TopologicalSpace M] [TopologicalSpace X] :
    Prop where
  /-- The additive action `(+ᵥ)` is continuous. -/
  continuous_vadd : Continuous fun p : M × X => p.1 +ᵥ p.2

export ContinuousVAdd (continuous_vadd)

attribute [to_additive] ContinuousSMul

attribute [continuity, fun_prop] continuous_smul continuous_vadd

section Main

variable {M X Y α : Type*} [TopologicalSpace M] [TopologicalSpace X] [TopologicalSpace Y]

section SMul

variable [SMul M X] [ContinuousSMul M X]

lemma IsScalarTower.continuousSMul {M : Type*} (N : Type*) {α : Type*} [Monoid N] [SMul M N]
    [MulAction N α] [SMul M α] [IsScalarTower M N α] [TopologicalSpace M] [TopologicalSpace N]
    [TopologicalSpace α] [ContinuousSMul M N] [ContinuousSMul N α] : ContinuousSMul M α :=
  { continuous_smul := by
      suffices Continuous (fun p : M × α ↦ (p.1 • (1 : N)) • p.2) by simpa
      fun_prop }

@[to_additive]
instance : ContinuousSMul (ULift M) X :=
  ⟨(continuous_smul (M := M)).comp₂ (continuous_uliftDown.comp continuous_fst) continuous_snd⟩

@[to_additive]
instance (priority := 100) ContinuousSMul.continuousConstSMul : ContinuousConstSMul M X where
  continuous_const_smul _ := continuous_smul.comp (continuous_const.prodMk continuous_id)

theorem ContinuousSMul.induced {R : Type*} {α : Type*} {β : Type*} {F : Type*} [FunLike F α β]
    [Semiring R] [AddCommMonoid α] [AddCommMonoid β] [Module R α] [Module R β]
    [TopologicalSpace R] [LinearMapClass F R α β] [tβ : TopologicalSpace β] [ContinuousSMul R β]
    (f : F) : @ContinuousSMul R α _ _ (tβ.induced f) := by
  let tα := tβ.induced f
  refine ⟨continuous_induced_rng.2 ?_⟩
  simp only [Function.comp_def, map_smul]
  fun_prop

@[to_additive]
theorem Filter.Tendsto.smul {f : α → M} {g : α → X} {l : Filter α} {c : M} {a : X}
    (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) :
    Tendsto (fun x => f x • g x) l (𝓝 <| c • a) :=
  (continuous_smul.tendsto _).comp (hf.prodMk_nhds hg)

@[to_additive]
theorem Filter.Tendsto.smul_const {f : α → M} {l : Filter α} {c : M} (hf : Tendsto f l (𝓝 c))
    (a : X) : Tendsto (fun x => f x • a) l (𝓝 (c • a)) :=
  hf.smul tendsto_const_nhds

variable {f : Y → M} {g : Y → X} {b : Y} {s : Set Y}

@[to_additive]
theorem ContinuousWithinAt.smul (hf : ContinuousWithinAt f s b) (hg : ContinuousWithinAt g s b) :
    ContinuousWithinAt (fun x => f x • g x) s b :=
  Filter.Tendsto.smul hf hg

@[to_additive (attr := fun_prop)]
theorem ContinuousAt.smul (hf : ContinuousAt f b) (hg : ContinuousAt g b) :
    ContinuousAt (fun x => f x • g x) b :=
  Filter.Tendsto.smul hf hg

@[to_additive (attr := fun_prop)]
theorem ContinuousOn.smul (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => f x • g x) s := fun x hx => (hf x hx).smul (hg x hx)

@[to_additive (attr := continuity, fun_prop)]
theorem Continuous.smul (hf : Continuous f) (hg : Continuous g) : Continuous fun x => f x • g x :=
  continuous_smul.comp (hf.prodMk hg)

/-- If a scalar action is central, then its right action is continuous when its left action is. -/
@[to_additive /-- If an additive action is central, then its right action is continuous when its
left action is. -/]
instance ContinuousSMul.op [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] : ContinuousSMul Mᵐᵒᵖ X :=
  ⟨by
    suffices Continuous fun p : M × X => MulOpposite.op p.fst • p.snd from
      this.comp (MulOpposite.continuous_unop.prodMap continuous_id)
    simpa only [op_smul_eq_smul] using (continuous_smul : Continuous fun p : M × X => _)⟩

@[to_additive]
instance MulOpposite.continuousSMul : ContinuousSMul M Xᵐᵒᵖ :=
  ⟨MulOpposite.continuous_op.comp <|
      continuous_smul.comp <| continuous_id.prodMap MulOpposite.continuous_unop⟩

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
  /-- Suppose that `N` additively acts on `X` and `M` continuously additively acts on `Y`.
Suppose that `g : Y → X` is an additive action homomorphism in the following sense:
there exists a continuous function `f : N → M` such that `g (c +ᵥ x) = f c +ᵥ g x`.
Then the action of `N` on `X` is continuous as well.

In many cases, `f = id` so that `g` is an action homomorphism in the sense of `AddActionHom`.
However, this version also works for `f = AddUnits.val`. -/]
lemma Topology.IsInducing.continuousSMul {N : Type*} [SMul N Y] [TopologicalSpace N] {f : N → M}
    (hg : IsInducing g) (hf : Continuous f) (hsmul : ∀ {c x}, g (c • x) = f c • g x) :
    ContinuousSMul N Y where
  continuous_smul := by
    simpa only [hg.continuous_iff, Function.comp_def, hsmul]
      using (hf.comp continuous_fst).smul <| hg.continuous.comp continuous_snd

@[to_additive]
instance SMulMemClass.continuousSMul {S : Type*} [SetLike S X] [SMulMemClass S M X] (s : S) :
    ContinuousSMul M s :=
  IsInducing.subtypeVal.continuousSMul continuous_id rfl

end SMul

section Monoid

variable [Monoid M] [MulAction M X] [ContinuousSMul M X]

@[to_additive]
instance Units.continuousSMul : ContinuousSMul Mˣ X :=
  IsInducing.id.continuousSMul Units.continuous_val rfl

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
  IsInducing.id.continuousSMul continuous_subtype_val rfl

end Monoid

section Group

variable [Group M] [MulAction M X] [ContinuousSMul M X]

@[to_additive]
instance Subgroup.continuousSMul {S : Subgroup M} : ContinuousSMul S X :=
  S.toSubmonoid.continuousSMul

variable (M)

/-- The stabilizer of a continuous group action on a discrete space is an open subgroup. -/
lemma stabilizer_isOpen [DiscreteTopology X] (x : X) : IsOpen (MulAction.stabilizer M x : Set M) :=
  IsOpen.preimage (f := fun g ↦ g • x) (by fun_prop) (isOpen_discrete {x})

end Group

section GroupWithZero

variable {G₀ X : Type*} [GroupWithZero G₀] [Zero X] [MulActionWithZero G₀ X]
  [TopologicalSpace G₀] [(𝓝[≠] (0 : G₀)).NeBot] [TopologicalSpace X] [ContinuousSMul G₀ X]

theorem Set.univ_smul_nhds_zero {s : Set X} (hs : s ∈ 𝓝 0) : (univ : Set G₀) • s = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ ?_
  have : Tendsto (· • x) (𝓝 (0 : G₀)) (𝓝 0) :=
    zero_smul G₀ x ▸ tendsto_id.smul tendsto_const_nhds
  rcases Filter.nonempty_of_mem (inter_mem_nhdsWithin {0}ᶜ <| mem_map.1 <| this hs)
    with ⟨c, hc₀, hc⟩
  simp only [mem_compl_iff, mem_singleton_iff] at hc₀
  simp only [mem_smul, mem_univ, true_and]
  exact ⟨c⁻¹, c • x, hc, inv_smul_smul₀ hc₀ _⟩

@[simp]
theorem Filter.top_smul_nhds_zero : (⊤ : Filter G₀) • 𝓝 (0 : X) = ⊤ := by
  rw [(hasBasis_top.smul (basis_sets _)).eq_top_iff]
  rintro ⟨_, s⟩ ⟨-, hs⟩
  exact Set.univ_smul_nhds_zero hs

end GroupWithZero

@[to_additive]
instance Prod.continuousSMul [SMul M X] [SMul M Y] [ContinuousSMul M X] [ContinuousSMul M Y] :
    ContinuousSMul M (X × Y) :=
  ⟨(continuous_fst.smul (continuous_fst.comp continuous_snd)).prodMk
      (continuous_fst.smul (continuous_snd.comp continuous_snd))⟩

@[to_additive]
instance {ι : Type*} {γ : ι → Type*} [∀ i, TopologicalSpace (γ i)] [∀ i, SMul M (γ i)]
    [∀ i, ContinuousSMul M (γ i)] : ContinuousSMul M (∀ i, γ i) :=
  ⟨continuous_pi fun i =>
      (continuous_fst.smul continuous_snd).comp <|
        continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)⟩

@[to_additive]
instance {ι : Type*} {γ : ι → Type*} [∀ i, TopologicalSpace (γ i)]
    {N : ι → Type*} [∀ i, TopologicalSpace (N i)] [∀ i, SMul (N i) (γ i)]
    [∀ i, ContinuousSMul (N i) (γ i)] : ContinuousSMul (∀ i, N i) (∀ i, γ i) :=
  ⟨continuous_pi fun i ↦
    (Continuous.smul ((continuous_apply i).comp (Continuous.fst continuous_id'))
      ((continuous_apply i).comp (Continuous.snd continuous_id')))⟩

end Main

section LatticeOps

variable {ι : Sort*} {M X : Type*} [TopologicalSpace M] [SMul M X]

@[to_additive]
theorem continuousSMul_sInf {ts : Set (TopologicalSpace X)}
    (h : ∀ t ∈ ts, @ContinuousSMul M X _ _ t) : @ContinuousSMul M X _ _ (sInf ts) :=
  let _ := sInf ts
  { continuous_smul := by
      -- Porting note: needs `( :)`
      rw [← (sInf_singleton (a := ‹TopologicalSpace M›) :)]
      exact
        continuous_sInf_rng.2 fun t ht =>
          continuous_sInf_dom₂ (Eq.refl _) ht
            (@ContinuousSMul.continuous_smul _ _ _ _ t (h t ht)) }

@[to_additive]
theorem continuousSMul_iInf {ts' : ι → TopologicalSpace X}
    (h : ∀ i, @ContinuousSMul M X _ _ (ts' i)) : @ContinuousSMul M X _ _ (⨅ i, ts' i) :=
  continuousSMul_sInf <| Set.forall_mem_range.mpr h

@[to_additive]
theorem continuousSMul_inf {t₁ t₂ : TopologicalSpace X} [@ContinuousSMul M X _ _ t₁]
    [@ContinuousSMul M X _ _ t₂] : @ContinuousSMul M X _ _ (t₁ ⊓ t₂) := by
  rw [inf_eq_iInf]
  refine continuousSMul_iInf fun b => ?_
  cases b <;> assumption

end LatticeOps

section AddTorsor

variable (G : Type*) (P : Type*) [AddGroup G] [AddTorsor G P] [TopologicalSpace G]
variable [PreconnectedSpace G] [TopologicalSpace P] [ContinuousVAdd G P]

include G in
/-- An `AddTorsor` for a connected space is a connected space. This is not an instance because
it loops for a group as a torsor over itself. -/
protected theorem AddTorsor.connectedSpace : ConnectedSpace P :=
  { isPreconnected_univ := by
      convert
        isPreconnected_univ.image (Equiv.vaddConst (Classical.arbitrary P) : G → P)
          (continuous_id.vadd continuous_const).continuousOn
      rw [Set.image_univ, Equiv.range_eq_univ]
    toNonempty := inferInstance }

end AddTorsor
