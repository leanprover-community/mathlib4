/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Convenient.ContinuousMapGeneratedBy

/-!
# The topological space of `X`-continuous maps

Let `X i` be a family of topological spaces. Let `Z` and `T` be topological spaces.
In this file, we endow the type `ContinuousMapGeneratedBy X Z T` of
`X`-continuous maps `Z → T` with the coarsest topology which makes
the precomposition maps `ContinuousMapGeneratedBy X Z T → C(X i, T)`
continuous for any continuous map `X i → Z`, where `C(X i, T)`
is endowed with the compact-open topology.

If we assume that the spaces `X i` are locally compact and that the products
`X i × X j` are `X`-generated, we obtain that the curryfication of maps induces
a bijection between the type of `X`-continuous maps `Y × Z → T` and the type of
`X`-continuous maps `Z → ContinuousMapGeneratedBy X Y T` for all
topological spaces `Y`, `Z` and `T`.

## References
* [Martín Escardó, Jimmie Lawson and Alex Simpson, *Comparing Cartesian closed
  categories of (core) compactly generated spaces*][escardo-lawson-simpson-2004]

-/
universe v v' v'' t u

@[expose] public section

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
  {Y : Type v} [TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]
  {T : Type v''} [TopologicalSpace T]

namespace Topology.ContinuousMapGeneratedBy

/-- Given a continuous map `f : X i → Z`, this is the map
`ContinuousMapGeneratedBy X Z T → C(X i, T)` given by the precomposition with `f`.
This is used in order to define a topology on `ContinuousMapGeneratedBy X Z T`. -/
def precomp {i : ι} (f : C(X i, Z)) : ContinuousMapGeneratedBy X Z T → C(X i, T) :=
  fun g ↦ ⟨_, g.prop f⟩

@[simp]
lemma precomp_apply {i : ι} (f : C(X i, Z)) (g : ContinuousMapGeneratedBy X Z T) :
    ⇑(precomp f g) = g ∘ f := rfl

instance : TopologicalSpace (ContinuousMapGeneratedBy X Z T) :=
  ⨅ (i : ι) (f : C(X i, Z)), .induced (precomp f) inferInstance

lemma continuous_iff {A : Type*} [TopologicalSpace A] {φ : A → ContinuousMapGeneratedBy X Z T} :
    Continuous φ ↔ ∀ (i : ι) (f : C(X i, Z)), Continuous (precomp f ∘ φ) := by
  simp only [continuous_iInf_rng, continuous_induced_rng]

@[continuity, fun_prop]
lemma continuous_precomp {i : ι} (f : C(X i, Z)) : Continuous (precomp (T := T) f) := by
  rw [continuous_iff_le_induced]
  exact (iInf_le _ i).trans (iInf_le _ _)

lemma continuousGeneratedBy_iff_uncurry [∀ i, LocallyCompactSpace (X i)]
    (g : Z → ContinuousMapGeneratedBy X Y T) :
    ContinuousGeneratedBy X g ↔
      ∀ ⦃i₁ : ι⦄ (f₁ : C(X i₁, Z)) ⦃i₂ : ι⦄ (f₂ : C(X i₂, Y)) ,
        Continuous (fun (x₁, x₂) ↦ g (f₁ x₁) (f₂ x₂)) := by
  simp only [continuousGeneratedBy_def, continuous_iff]
  exact forall_congr' (fun i₁ ↦ forall_congr' (fun f₁ ↦
    forall_congr' (fun i₂ ↦ forall_congr' (fun f₂ ↦
      ⟨fun h ↦ ContinuousMap.continuous_uncurry_of_continuous ⟨_, h⟩,
        fun h ↦ (ContinuousMap.curry ⟨_, h⟩).continuous⟩))))

lemma continuousGeneratedBy_dom_prod_iff [∀ i j, IsGeneratedBy X (X i × X j)]
    (g : Y × Z → T) :
    ContinuousGeneratedBy X g ↔
      ∀ (i₁ : ι) (f₁ : C(X i₁, Z)) (i₂ : ι) (f₂ : C(X i₂, Y)),
        Continuous (fun (x₁, x₂) ↦ g ⟨f₂ x₂, f₁ x₁⟩) := by
  refine ⟨fun h i₁ f₁ i₂ f₂ ↦ ?_, fun h ↦ ?_⟩
  · rw [IsGeneratedBy.continuous_iff X]
    intro j p
    let φ : X i₁ × X i₂ → Y × Z := fun (x₁, x₂) ↦ (f₂ x₂, f₁ x₁)
    replace h := h.comp (show Continuous φ by continuity).continuousGeneratedBy
    rw [continuousGeneratedBy_def] at h
    exact h p
  · rw [continuousGeneratedBy_def]
    intro i f
    exact (h i (ContinuousMap.snd.comp f) i (ContinuousMap.fst.comp f)).comp
      (Continuous.prodMk continuous_id continuous_id)

variable [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]

/-- The bijection between the type of `X`-continuous maps `Y × Z → T` and the type of
`X`-continuous maps `Z → ContinuousMapGeneratedBy X Y T`. -/
def curryEquiv :
  ContinuousMapGeneratedBy X (Y × Z) T ≃
    ContinuousMapGeneratedBy X Z (ContinuousMapGeneratedBy X Y T) where
  toFun g :=
    { toFun z := g.comp ⟨fun y ↦ (y, z), (Continuous.prodMk_left z).continuousGeneratedBy⟩
      prop := by
        simpa only [continuousGeneratedBy_iff_uncurry,
          continuousGeneratedBy_dom_prod_iff] using g.prop }
  invFun g :=
    { toFun x := g x.2 x.1
      prop := by
        simpa only [continuousGeneratedBy_iff_uncurry,
          continuousGeneratedBy_dom_prod_iff] using g.prop }

@[simp]
lemma curryEquiv_apply_apply (g : ContinuousMapGeneratedBy X (Y × Z) T) (y : Y) (z : Z) :
    curryEquiv g z y = g (y, z) := rfl

@[simp]
lemma curryEquiv_symm_apply (g : ContinuousMapGeneratedBy X Z (ContinuousMapGeneratedBy X Y T))
    (y : Y) (z : Z) :
    curryEquiv.symm g (y, z) = g z y := rfl

/-- The evaluation `Y × ContinuousMapGeneratedBy X Y Z → Z` as a `X`-continuous map. -/
def ev : ContinuousMapGeneratedBy X (Y × ContinuousMapGeneratedBy X Y Z) Z :=
  curryEquiv.symm .id

@[simp]
lemma ev_apply (y : Y) (f : ContinuousMapGeneratedBy X Y Z) :
    ev (y, f) = f y := rfl

/-- Given a `X`-continuous map `p : Z → T`, this is the postcomposition with `p`
`ContinuousMapGeneratedBy X Y Z → ContinuousMapGeneratedBy X Y T`
as a `X`-continuous map. -/
def postcomp (p : ContinuousMapGeneratedBy X Z T) :
    ContinuousMapGeneratedBy X (ContinuousMapGeneratedBy X Y Z)
      (ContinuousMapGeneratedBy X Y T) :=
  curryEquiv (p.comp ev)

@[simp]
lemma postcomp_apply (p : ContinuousMapGeneratedBy X Z T) (g : ContinuousMapGeneratedBy X Y Z) :
    p.postcomp g = p.comp g := rfl

end Topology.ContinuousMapGeneratedBy
