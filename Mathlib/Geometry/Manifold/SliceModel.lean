/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.IsImmersionEmbedding
import Mathlib.Geometry.Manifold.Instances.Real -- XXX: disentangle these later
/-!
# Embedded submanifolds

We define a new typeclass `SliceModel` for models with corners.
This will be used to define immersed and embedded submanifolds.

TODO: expand this doc-string!

-/

open scoped Manifold ContDiff
open Topology Function Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' E'' E''' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E''']
    [NormedSpace 𝕜 E''']
  {F F' : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H H' H'' H''' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace H''] [TopologicalSpace H''']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {I'' : ModelWithCorners 𝕜 E'' H''}
  {J : ModelWithCorners 𝕜 E''' H'''}
  {M M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] {n : WithTop ℕ∞}

variable (I I' F) in
/-- Two models with corners `I` and `I'` form a **slice model** if "I includes into I'".
More precisely, there are an embedding `H → H'` and a continuous linear map `E → E'` so the diagram
  H  -I  → E'
  |        |
  |        |
  H' -I' → E'
commutes. More precisely, we prescribe a linear equivalence `E × F → E`, for some normed space `F`,
which induces the map `E → E'` in the obvious way.
-/
class SliceModel where
  equiv: (E × F) ≃L[𝕜] E'
  map: H → H'
  hmap : Topology.IsEmbedding map
  compatible : I' ∘ map = equiv ∘ ((·, 0) : E → E × F) ∘ I

namespace SliceModel

/-- A choice of inverse of `map`: its value outside of `range map` is unspecified. -/
noncomputable def inverse [Nonempty H] (h : SliceModel F I I') : H' → H :=
  (Function.extend h.map id (fun _ ↦ (Classical.arbitrary H)))

-- warm-up: I' ∘ map ⊆ im equiv ∘ I: that's basically obvious, nothing to prove

lemma inverse_left_inv [Nonempty H] (h : SliceModel F I I') (x : H) :
    h.inverse (h.map x) = x :=
  Injective.extend_apply h.hmap.injective ..

lemma inverse_right_inv [Nonempty H] (h : SliceModel F I I') (z : H') (hz : z ∈ range h.map) :
    h.map (h.inverse z) = z := by
  choose x hx using hz
  rw [← hx, h.inverse_left_inv]

end SliceModel

-- PRed in #24168
section

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [Unique G]

namespace LinearEquiv

variable (𝕜 E) in
/-- The natural equivalence `E × G ≃ₗ[𝕜] E` for any `Unique` type `G`.
This is `Equiv.prodUnique` as a linear equivalence. -/
def prodUnique : (E × G) ≃ₗ[𝕜] E where
  toEquiv := Equiv.prodUnique E G
  map_add' x y := by simp
  map_smul' r x := by simp

@[simp]
lemma prodUnique_toEquiv : (prodUnique 𝕜 E).toEquiv = Equiv.prodUnique E G := rfl

end LinearEquiv

namespace ContinuousLinearEquiv

variable (𝕜 E) in
/-- The natural equivalence `E × G ≃L[𝕜] E` for any `Unique` type `G`.
This is `Equiv.prodUnique` as a continuous linear equivalence. -/
def prodUnique : (E × G) ≃L[𝕜] E where
  toLinearEquiv := LinearEquiv.prodUnique 𝕜 E
  continuous_toFun := by
    show Continuous (Equiv.prodUnique E G)
    dsimp; fun_prop
  continuous_invFun := by
    show Continuous fun x ↦ (x, default)
    fun_prop

@[simp]
lemma prodUnique_toEquiv : (prodUnique 𝕜 E).toEquiv = Equiv.prodUnique E G := rfl

@[simp]
lemma prodUnique_apply (x : E × G) : prodUnique 𝕜 E x = x.1 := rfl

@[simp]
lemma prodUnique_symm_apply (x : E) : (prodUnique 𝕜 E (G := G)).symm x = (x, default) := rfl

/- do I want all/any of these lemma?
@[simp]
lemma prodSingle_coe {y : G} :
    (prodSingleton 𝕜 E (y := y)) = ((·, y) : E → E × G) := rfl
-/

section

variable (R M₁ M₂ M₃ : Type*) [Semiring R]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [Module R M₁] [Module R M₂] [Module R M₃]
  [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace M₃]

/-- The product of topological modules is associative up to continuous linear isomorphism.
This is `LinearEquiv.prodAssoc` prodAssoc as a continuous linear equivalence. -/
def prodAssoc : ((M₁ × M₂) × M₃) ≃L[R] M₁ × M₂ × M₃ where
  toLinearEquiv := LinearEquiv.prodAssoc R M₁ M₂ M₃
  continuous_toFun := (continuous_fst.comp continuous_fst).prodMk
    ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  continuous_invFun := (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
    (continuous_snd.comp continuous_snd)

@[simp]
lemma prodAssoc_toLinearEquiv :
  (prodAssoc 𝕜 E E' E'').toLinearEquiv = LinearEquiv.prodAssoc 𝕜 E E' E'' := rfl

-- not simp as the combination of existing lemmas. TODO: should this one still be added?
lemma prodAssoc_toEquiv :
  (prodAssoc 𝕜 E E' E'').toEquiv = Equiv.prodAssoc E E' E'' := rfl

end

end ContinuousLinearEquiv

end

section instances

/-- Every model with corners is a slice model over itself. -/
instance : SliceModel (⊥ : Subspace 𝕜 E) I I where
  equiv := ContinuousLinearEquiv.prodUnique 𝕜 E
  map := id
  hmap := Topology.IsEmbedding.id
  compatible := by ext x; dsimp

-- apparently all missing: LinearEquiv.prodCongr, ContinuousLinearEquiv.prodCongr

instance [h : SliceModel F I I'] : SliceModel F (J.prod I) (J.prod I') where
  equiv := by
    let sdf := h.equiv
    -- want h.equiv.prodCongr (.id), and probably re-associating...
    sorry
  map := Prod.map id h.map
  hmap := IsEmbedding.id.prodMap h.hmap
  compatible := sorry

-- a bit more cumbersome, as equiv needs some reordering
instance [h : SliceModel F I I'] : SliceModel F (I.prod J) (I'.prod J) where
  equiv := sorry
  map := Prod.map h.map id
  hmap := h.hmap.prodMap IsEmbedding.id
  compatible := sorry

instance (h : (E × F) ≃L[𝕜] E') : SliceModel F (𝓘(𝕜, E)) (𝓘(𝕜, E')) where
  equiv := h
  map := h ∘ (·, (0 : F))
  hmap := by
    apply IsEmbedding.comp
    · sorry -- apply ContinuousLinearEquiv.isEmbedding
    have : IsEmbedding (@Prod.swap E F) := sorry -- missing, it seems
    rw [← IsEmbedding.of_comp_iff this]
    have : ((·, (0 : F)) : E → E × F) = Prod.swap ∘ Prod.mk 0 := by
      ext x
      simp_all; sorry
    convert isEmbedding_prodMk (0 : F)
  compatible := by simp

/-- *Any* model with corners on `E` which is an embedding is a slice model with the trivial model
on `E`. (The embedding condition excludes strange cases of submanifolds with boundary).
For boundaryless models, that is always true. -/
instance {I : ModelWithCorners 𝕜 E H} (hI : IsEmbedding I) :
    SliceModel (⊥ : Subspace 𝕜 E) I 𝓘(𝕜, E) where
  equiv := ContinuousLinearEquiv.prodUnique 𝕜 E
  map := I
  hmap := hI
  compatible := by ext; simp

-- TODO: prove that I is an embedding if I is boundaryless, then add the corresponding instance
-- TODO: think about the boundary case, and which particular version of submanifolds this enforces...

open scoped Manifold

-- XXX: can this be golfed using the previous instance?
noncomputable instance {n : ℕ} [NeZero n] :
    SliceModel (⊥ : Subspace ℝ ((Fin n → ℝ))) (𝓡∂ n) (𝓡 n) where
  equiv := ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin n))
  map := Subtype.val
  hmap := Topology.IsEmbedding.subtypeVal
  compatible := by
    ext x'
    simp only [modelWithCornersSelf_coe, comp_apply, id_eq, ContinuousLinearEquiv.prodUnique_apply]
    rfl

-- should be a not-too-hard exercise
noncomputable instance {n m : ℕ} [NeZero n] :
    SliceModel (⊥ : Subspace ℝ ((Fin m → ℝ))) (𝓡 n) (𝓡 (n + m)) where
  equiv := sorry -- see zulip! ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin n))
  map := sorry -- easy from `equiv`
  hmap := sorry -- should be easy: `equiv` is an embedding, and prodMk{Left,Right} also are
  compatible := by -- should be obvious then
    ext x'
    sorry

noncomputable instance {n : ℕ} [NeZero n] :
    SliceModel (⊥ : Subspace ℝ ((Fin n → ℝ))) (modelWithCornersEuclideanQuadrant n) (𝓡∂ n) where
  equiv := ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin n))
  map := fun ⟨x, hx⟩ ↦ ⟨x, hx 0⟩
  hmap :=
    -- general result: two subtypes, one contained in the other: is Subtype.val always an
    -- embedding? can one prove this?
    sorry
  compatible := by
    ext x
    simp_all only [comp_apply, ContinuousLinearEquiv.prodUnique_apply]
    rfl

-- TODO: make an instance/ figure out why Lean complains about synthesisation order!
def instTrans (h : SliceModel F I I') (h' : SliceModel F' I' I'') : SliceModel (F × F') I I'' where
  equiv := (ContinuousLinearEquiv.prodAssoc 𝕜 E F F').symm.trans
    ((h.equiv.prod (ContinuousLinearEquiv.refl 𝕜 F')).trans h'.equiv)
  map := h'.map ∘ h.map
  hmap := h'.hmap.comp h.hmap
  compatible := by -- paste the two commutative diagrams together
    ext x
    simp [h.compatible, h'.compatible]
    sorry

end instances
