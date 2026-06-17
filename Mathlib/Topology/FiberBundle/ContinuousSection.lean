/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.FiberBundle.Constructions

/-!
# Continuous sections of fibre bundles

In this file we define continuous sections of topological fibre bundles and prove that if a bundle
carries a continuous fibrewise action by a topological group `G`, its sections are acted on by both
`G` and `G`-valued functions on the base space.

## Main results / definitions
* `ContinuousSection F E`: the type of continuous sections of `E`. Denoted `Cₛ⟮F, E⟯`.
* `ContinuousSection.equivContinuousMap`: continuous sections of a trivial bundle `Trivial B F`
  correspond to continuous maps `B → F`.
* `ContinuousSection.prodEquiv`: continuous sections of a product bundle `E ×ᵇ E'` correspond to
  pairs of continuous sections of `E` and `E'`.
* `ContinuousSection.pullback f s`: the continuous section of the pullback bundle `f *ᵖ E` given
  by precomposing a given continuous section `s` of `E` with `f`.

## TODO
* Introduce typeclasses for continuity of other fibrewise algebraic structures and show that
  sections inherit the corresponding structures in these cases.
* Show that vector bundles satisfy these typeclasses, so that this API in particular applies
  to them.
-/

@[expose] public section

open Bundle FiberBundle Function Filter

variable (F : Type*) [TopologicalSpace F] {B : Type*} [TopologicalSpace B]
  (E : B → Type*) [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E]

/-- The type of continuous sections of a topological `FiberBundle F E`, written `Cₛ(F, E)` in
the `Bundle` namespace. -/
structure ContinuousSection (F : Type*) [TopologicalSpace F] {B : Type*} [TopologicalSpace B]
    (E : B → Type*) [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] where
  toFun : ∀ b, E b
  continuous_toFun : Continuous fun b ↦ (⟨b, toFun b⟩ : TotalSpace F E)

@[inherit_doc] scoped[Bundle] notation "Cₛ⟮" F ", " E "⟯" => ContinuousSection F E

namespace ContinuousSection

variable {F E}

instance : DFunLike Cₛ⟮F, E⟯ B E where
  coe := ContinuousSection.toFun
  coe_injective := by rintro ⟨⟩ ⟨⟩ h; congr

variable {s t : Cₛ⟮F, E⟯}

@[simp]
theorem coeFn_mk (s : ∀ b, E b) (hs : Continuous fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) :
    (mk s hs : ∀ b, E b) = s := rfl

protected theorem continuous (s : Cₛ⟮F, E⟯) : Continuous fun b ↦ (⟨b, s b⟩ : TotalSpace F E) :=
  s.continuous_toFun

theorem coe_inj ⦃s t : Cₛ⟮F, E⟯⦄ (h : (s : ∀ b, E b) = t) : s = t :=
  DFunLike.ext' h

theorem coe_injective : Injective ((↑) : Cₛ⟮F, E⟯ → ∀ b, E b) :=
  coe_inj

@[ext]
theorem ext (h : ∀ x, s x = t x) : s = t := DFunLike.ext _ _ h

/-- Continuous sections of trivial bundles are equivalently continuous maps. -/
@[simps]
def equivContinuousMap : Cₛ⟮F, Trivial B F⟯ ≃ C(B, F) where
  toFun s := ⟨fun b ↦ s b, (TotalSpace.continuous_trivialSnd B F).comp s.continuous⟩
  invFun f := ⟨fun b ↦ f b, (Trivial.homeomorphProd B F).symm.continuous.comp <|
    continuous_id.prodMk f.continuous⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Continuous sections of product bundles correspond to pairs of continuous sections
of the factors. -/
noncomputable def prodEquiv {F' : Type*} [TopologicalSpace F'] {E' : B → Type*}
    [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (TotalSpace F' E')] [FiberBundle F' E']
    [∀ x, Zero (E x)] [∀ x, Zero (E' x)] : Cₛ⟮F × F', E ×ᵇ E'⟯ ≃ Cₛ⟮F, E⟯ × Cₛ⟮F', E'⟯ where
  toFun s := ⟨⟨fun b ↦ (s b).1, continuous_fst.comp <|
    (Prod.isInducing_diag F E F' E').continuous.comp s.continuous⟩, ⟨fun b ↦ (s b).2,
        continuous_snd.comp <| (Prod.isInducing_diag F E F' E').continuous.comp s.continuous⟩⟩
  invFun s := ⟨fun b ↦ (s.1 b, s.2 b), (Prod.isInducing_diag F E F' E').continuous_iff.2 <|
    continuous_prodMk.2 ⟨s.1.continuous, s.2.continuous⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The pullback of a continuous section of `E` to the pullback bundle `f *ᵖ E` given by
precomposition with `f`. -/
@[simps]
def pullback {B' : Type*} [TopologicalSpace B'] [∀ _b, Zero (E _b)] {K : Type*} [FunLike K B' B]
    [ContinuousMapClass K B' B] (f : K) (s : Cₛ⟮F, E⟯) : Cₛ⟮F, f *ᵖ E⟯ where
  toFun b := s (f b)
  continuous_toFun :=
    (Pullback.continuous_iff F E f _).2 ⟨continuous_id, s.continuous.comp (map_continuous f)⟩

end ContinuousSection

section Operations

variable {F E}

omit [TopologicalSpace F] [(b : B) → TopologicalSpace (E b)] [FiberBundle F E] in
lemma ContinuousWithinAt.smul_section {G : Type*} [TopologicalSpace G] [∀ b, SMul G (E b)]
    [ContinuousSMul G (TotalSpace F E)] {f : B → G} {s : ∀ b, E b} {u : Set B} {b : B}
    (hf : ContinuousWithinAt f u b)
    (hs : ContinuousWithinAt (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) u b) :
    ContinuousWithinAt (fun b ↦ (⟨b, (f • s) b⟩ : TotalSpace F E)) u b :=
  hf.smul hs

omit [TopologicalSpace F] [(b : B) → TopologicalSpace (E b)] [FiberBundle F E] in
lemma ContinuousAt.smul_section {G : Type*} [TopologicalSpace G] [∀ b, SMul G (E b)]
    [ContinuousSMul G (TotalSpace F E)] {f : B → G} {s : ∀ b, E b} {b : B}
    (hf : ContinuousAt f b) (hs : ContinuousAt (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) b) :
    ContinuousAt (fun b ↦ (⟨b, (f • s) b⟩ : TotalSpace F E)) b :=
  hf.smul hs

omit [TopologicalSpace F] [(b : B) → TopologicalSpace (E b)] [FiberBundle F E] in
lemma ContinuousOn.smul_section {G : Type*} [TopologicalSpace G] [∀ b, SMul G (E b)]
    [ContinuousSMul G (TotalSpace F E)] {f : B → G} {s : ∀ b, E b} {u : Set B}
    (hf : ContinuousOn f u) (hs : ContinuousOn (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) u) :
    ContinuousOn (fun b ↦ (⟨b, (f • s) b⟩ : TotalSpace F E)) u :=
  hf.smul hs

omit [TopologicalSpace F] [(b : B) → TopologicalSpace (E b)] [FiberBundle F E] in
lemma Continuous.smul_section {G : Type*} [TopologicalSpace G] [∀ b, SMul G (E b)]
    [ContinuousSMul G (TotalSpace F E)] {f : B → G} {s : ∀ b, E b}
    (hf : Continuous f) (hs : Continuous (fun b ↦ (⟨b, s b⟩ : TotalSpace F E))) :
    Continuous (fun b ↦ (⟨b, (f • s) b⟩ : TotalSpace F E)) :=
  hf.smul hs

omit [TopologicalSpace F] [(b : B) → TopologicalSpace (E b)] [FiberBundle F E] in
lemma ContinuousWithinAt.const_smul_section {G : Type*} [TopologicalSpace G] [∀ b, SMul G (E b)]
    [ContinuousSMul G (TotalSpace F E)] {s : ∀ b, E b} {u : Set B} {b : B}
    (g : G) (hs : ContinuousWithinAt (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) u b) :
    ContinuousWithinAt (fun b ↦ (⟨b, (g • s) b⟩ : TotalSpace F E)) u b :=
  continuousWithinAt_const.smul_section hs

omit [TopologicalSpace F] [(b : B) → TopologicalSpace (E b)] [FiberBundle F E] in
lemma ContinuousAt.const_smul_section {G : Type*} [TopologicalSpace G] [∀ b, SMul G (E b)]
    [ContinuousSMul G (TotalSpace F E)] {s : ∀ b, E b} {b : B}
    (g : G) (hs : ContinuousAt (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) b) :
    ContinuousAt (fun b ↦ (⟨b, (g • s) b⟩ : TotalSpace F E)) b :=
  continuousAt_const.smul_section hs

omit [TopologicalSpace F] [(b : B) → TopologicalSpace (E b)] [FiberBundle F E] in
lemma ContinuousOn.const_smul_section {G : Type*} [TopologicalSpace G] [∀ b, SMul G (E b)]
    [ContinuousSMul G (TotalSpace F E)] {s : ∀ b, E b} {u : Set B}
    (g : G) (hs : ContinuousOn (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) u) :
    ContinuousOn (fun b ↦ (⟨b, (g • s) b⟩ : TotalSpace F E)) u :=
  continuousOn_const.smul_section hs

omit [TopologicalSpace F] [(b : B) → TopologicalSpace (E b)] [FiberBundle F E] in
lemma Continuous.const_smul_section {G : Type*} [TopologicalSpace G] [∀ b, SMul G (E b)]
    [ContinuousSMul G (TotalSpace F E)] {s : ∀ b, E b}
    (g : G) (hs : Continuous (fun b ↦ (⟨b, s b⟩ : TotalSpace F E))) :
    Continuous (fun b ↦ (⟨b, (g • s) b⟩ : TotalSpace F E)) :=
  continuous_const.smul_section hs

namespace ContinuousSection

/-- For every bundle `E` with a continuous fibrewise `G`-action, the type `Cₛ⟮F, E⟯` of sections
of `E` carries a `G`-action too. -/
instance instSMul {G : Type*} [TopologicalSpace G] [∀ b, SMul G (E b)]
    [ContinuousSMul G (TotalSpace F E)] : SMul G Cₛ⟮F, E⟯ :=
  ⟨fun c s ↦ ⟨c • ⇑s, s.continuous.const_smul_section c⟩⟩

@[simp]
theorem coe_smul {G : Type*} [TopologicalSpace G] [∀ b, SMul G (E b)]
    [ContinuousSMul G (TotalSpace F E)] (g : G) (s : Cₛ⟮F, E⟯) : ⇑(g • s) = g • ⇑s :=
  rfl

/-- For every bundle `E` with a continuous fibrewise `G`-action, the continuous functions `B → G`
act on the continuous sections of `E`. -/
instance instSMul' {G : Type*} [TopologicalSpace G] [∀ b, SMul G (E b)]
    [ContinuousSMul G (TotalSpace F E)] : SMul C(B, G) Cₛ⟮F, E⟯ :=
  ⟨fun f s ↦ ⟨⇑f • ⇑s, f.continuous.smul_section s.continuous⟩⟩

@[simp]
theorem coe_smul' {G : Type*} [TopologicalSpace G] [∀ b, SMul G (E b)]
    [ContinuousSMul G (TotalSpace F E)] (f : C(B, G)) (s : Cₛ⟮F, E⟯) : ⇑(f • s) = ⇑f • ⇑s :=
  rfl

instance {G : Type*} [SMul G G] [TopologicalSpace G] [ContinuousConstSMul G G]
    [∀ b, SMul G (E b)] [∀ b, IsScalarTower G G (E b)] [ContinuousSMul G (TotalSpace F E)] :
    IsScalarTower G C(B, G) Cₛ⟮F, E⟯ where
  smul_assoc g f s := by ext x; simp

end ContinuousSection

end Operations
