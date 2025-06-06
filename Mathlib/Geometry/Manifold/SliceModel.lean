/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.Instances.Real -- XXX: disentangle these later
/-!
# Embedded submanifolds

We define a new typeclass `SliceModel` for models with corners.

A future PR will use this to define immersed and embedded submanifolds.

TODO: expand this doc-string!

-/

section -- TODO: upstream; written by Ben Eltschig

/-- The canonical linear homeomorphism between `EuclideanSpace 𝕜 (ι ⊕ κ)` and
`EuclideanSpace 𝕜 ι × EuclideanSpace 𝕜 κ`. Note that this is not an isometry because
product spaces are equipped with the supremum norm. -/
def EuclideanSpace.sumEquivProd {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ] :
    EuclideanSpace 𝕜 (ι ⊕ κ) ≃L[𝕜] EuclideanSpace 𝕜 ι × EuclideanSpace 𝕜 κ :=
  (PiLp.sumPiLpEquivProdLpPiLp 2 _).toContinuousLinearEquiv.trans <|
    WithLp.prodContinuousLinearEquiv _ _ _ _

/-- The canonical linear homeomorphism between `EuclideanSpace 𝕜 (Fin (n + m))` and
`EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)`. -/
def EuclideanSpace.finAddEquivProd {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ} :
    EuclideanSpace 𝕜 (Fin (n + m)) ≃L[𝕜] EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 finSumFinEquiv.symm).toContinuousLinearEquiv.trans
    sumEquivProd

end

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

section

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [Unique G]

namespace ContinuousLinearEquiv

-- PRed in #23971

variable (𝕜 E) in
/-- The natural equivalence `E × G ≃L[𝕜] E` for any `Unique` type `G`.
This is `Equiv.prodUnique` as a continuous linear equivalence. -/
def prodUnique : (E × G) ≃L[𝕜] E where
  toLinearEquiv := LinearEquiv.prodUnique
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

section prodAssoc -- PRed in #25522

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

-- TODO: move up to Equiv.prodAssoc or so, then this one is implied...
@[simp]
lemma prodAssoc_apply (p₁ : E) (p₂ : E') (p₃ : E'') :
  (prodAssoc 𝕜 E E' E'') ((p₁, p₂), p₃) = (p₁, (p₂, p₃)) := rfl

end prodAssoc

section prodCongr -- already present, but differently named: #25513 renames these

variable {R M₁ M₂ M₃ M₄ : Type*} [Semiring R]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
  [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄]
  [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace M₃] [TopologicalSpace M₄]

/-- Product of continuous linear equivalences; the maps come from `Equiv.prodCongr`.
This is `LinearEquiv.prodCongr` as a continuous linear equivalence. -/
def prodCongr (e₁ : M₁ ≃L[R] M₂) (e₂ : M₃ ≃L[R] M₄) : (M₁ × M₃) ≃L[R] M₂ × M₄ := e₁.prod e₂

theorem prodCongr_symm (e₁ : M₁ ≃L[R] M₂) (e₂ : M₃ ≃L[R] M₄) :
    (e₁.prodCongr e₂).symm = e₁.symm.prodCongr e₂.symm := prod_symm e₁ e₂

@[simp]
theorem prodCongr_apply (e₁ : M₁ ≃L[R] M₂) (e₂ : M₃ ≃L[R] M₄) (p) :
    e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2) := prod_apply e₁ e₂ p

@[simp, norm_cast]
lemma coe_prodCongr (e₁ : M₁ ≃L[R] M₂) (e₂ : M₃ ≃L[R] M₄) :
    (e₁.prodCongr e₂ : (M₁ × M₃) →L[R] M₂ × M₄) = (e₁ : M₁ →L[R] M₂).prodMap (e₂ : M₃ →L[R] M₄) :=
  rfl

end prodCongr

end ContinuousLinearEquiv

end

section instances

/-- Every model with corners is a slice model over itself. -/
instance : SliceModel (⊥ : Subspace 𝕜 E) I I where
  equiv := ContinuousLinearEquiv.prodUnique 𝕜 E
  map := id
  hmap := Topology.IsEmbedding.id
  compatible := by ext x; dsimp

/-- If `I` is a slice model of `I'`, then `J.prod I` is a slice model of `J.prod I'`. -/
instance [h : SliceModel F I I'] : SliceModel F (J.prod I) (J.prod I') where
  -- Up to the obvious maps, we just apply h.equiv.
  equiv := (ContinuousLinearEquiv.prodAssoc 𝕜 E''' E F).trans <|
    (ContinuousLinearEquiv.refl 𝕜 E''').prodCongr h.equiv
  map := Prod.map id h.map
  hmap := IsEmbedding.id.prodMap h.hmap
  compatible := by
    dsimp
    ext ⟨x, y⟩ <;> simp
    -- XXX: is there a better tactic for this?
    change (I' ∘ SliceModel.map F I I') y = ((SliceModel.equiv I I') ∘ ((·, 0) : E → E × F) ∘ I) y
    rw [h.compatible]

/-- If `I` is a slice model of `I'`, then `I.prod J` is a slice model of `I'.prod J`. -/
-- a bit more cumbersome, as equiv needs some reordering
instance [h : SliceModel F I I'] : SliceModel F (I.prod J) (I'.prod J) where
  equiv := by
    letI pre := (ContinuousLinearEquiv.prodComm 𝕜 E E''').prodCongr (.refl 𝕜 F)
    letI post := ContinuousLinearEquiv.prodComm 𝕜 E' E'''
    letI main : ((E''' × E) × F) ≃L[𝕜] E''' × E' :=
      (ContinuousLinearEquiv.prodAssoc 𝕜 E''' E F).trans <|
      (ContinuousLinearEquiv.refl 𝕜 E''').prodCongr h.equiv
    apply pre.trans (main.trans post.symm)
  map := Prod.map h.map id
  hmap := h.hmap.prodMap IsEmbedding.id
  compatible := by
    ext ⟨x, y⟩ <;> simp
    -- XXX: is there a better tactic for this?
    change (I' ∘ SliceModel.map F I I') x = ((SliceModel.equiv I I') ∘ ((·, 0) : E → E × F) ∘ I) x
    rw [h.compatible]

/-- If `E' ≃ E × F`, then the trivial models with corners of `E` and `E'` form a slice model. -/
instance (h : (E × F) ≃L[𝕜] E') : SliceModel F (𝓘(𝕜, E)) (𝓘(𝕜, E')) where
  equiv := h
  map := h ∘ (·, (0 : F))
  hmap := by
    apply h.toHomeomorph.isEmbedding.comp
    rw [← IsEmbedding.of_comp_iff (ContinuousLinearEquiv.prodComm 𝕜 E F).toHomeomorph.isEmbedding]
    exact isEmbedding_prodMk (0 : F)
  compatible := by simp

/-- *Any* model with corners on `E` which is an embedding is a slice model with the trivial model
on `E`. (The embedding condition excludes strange cases of submanifolds with boundary).
For boundaryless models, that is always true. -/
def SliceModel.ofEmbedding {I : ModelWithCorners 𝕜 E H} (hI : IsEmbedding I) :
    SliceModel (⊥ : Subspace 𝕜 E) I 𝓘(𝕜, E) where
  equiv := ContinuousLinearEquiv.prodUnique 𝕜 E
  map := I
  hmap := hI
  compatible := by ext; simp

-- TODO: prove that I is an embedding if I is boundaryless, then add the corresponding instance
-- TODO: think about the boundary case, and which particular version of submanifolds this enforces...

open scoped Manifold

/-- Euclidean half-space is a slice model w.r.t. Euclidean space. -/
-- NB. Golfing this using the previous instance is not as obvious because of instance mismatches.
noncomputable instance {n : ℕ} [NeZero n] :
    SliceModel (⊥ : Subspace ℝ ((Fin n → ℝ))) (𝓡∂ n) (𝓡 n) where
  equiv := ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin n))
  map := Subtype.val
  hmap := Topology.IsEmbedding.subtypeVal
  compatible := by
    ext x'
    simp only [modelWithCornersSelf_coe, comp_apply, id_eq, ContinuousLinearEquiv.prodUnique_apply]
    rfl

/-- The standard model on `ℝ^n` is a slice model for the standard model for `ℝ^m`, for `n < m`. -/
noncomputable instance {n m : ℕ} [NeZero n] :
    SliceModel ((EuclideanSpace ℝ (Fin m))) (𝓡 n) (𝓡 (n + m)) where
  equiv := EuclideanSpace.finAddEquivProd |>.symm
  map x := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm (x, 0)
  hmap := sorry -- should be easy: `equiv` is an embedding, and prodMk{Left,Right} also are
  compatible := by ext; simp


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
