/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.AlgebraicGeometry.Limits

/-!
# Affine space

## Main definitions
- `AlgebraicGeometry.AffineSpace`: `𝔸(n; S)` is the affine `n`-space over `S`.
- `AlgebraicGeometry.AffineSpace.coord`: The standard coordinate functions on the affine space.
- `AlgebraicGeometry.AffineSpace.homOfVector`:
  The morphism `X ⟶ 𝔸(n; S)` given by a `X ⟶ S` and a choice of `n`-coordinate functions.
- `AlgebraicGeometry.AffineSpace.homOverEquiv`:
  `S`-morphisms into `Spec 𝔸(n; S)` are equivalent to the choice of `n` global sections.
- `AlgebraicGeometry.AffineSpace.SpecIso`: `𝔸(n; Spec R) ≅ Spec R[n]`

-/

open CategoryTheory Limits MvPolynomial

noncomputable section

namespace AlgebraicGeometry

universe u

variable (n : Type) (S : Scheme.{u})

local notation3 "ℤ[" n "]" => CommRingCat.of (MvPolynomial n (ULift ℤ))

/-- `𝔸(n; S)` is the affine `n`-space over `S`. -/
def AffineSpace (n : Type) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (Spec ℤ[n]))

namespace AffineSpace

/-- `𝔸(n; S)` is the affine `n`-space over `S`. -/
scoped [AlgebraicGeometry] notation "𝔸("n"; "S")" => AffineSpace n S

variable {n} in
lemma of_mvPolynomial_int_ext {R} {f g : ℤ[n] ⟶ R} (h : ∀ i, f (.X i) = g (.X i)) : f = g := by
  suffices f.comp (MvPolynomial.mapEquiv _ ULift.ringEquiv.symm).toRingHom =
      g.comp (MvPolynomial.mapEquiv _ ULift.ringEquiv.symm).toRingHom by
    ext x
    obtain ⟨x, rfl⟩ := (MvPolynomial.mapEquiv _ ULift.ringEquiv.symm).surjective x
    exact DFunLike.congr_fun this x
  ext1
  · exact RingHom.ext_int _ _
  · simpa using h _


@[simps (config := .lemmasOnly)]
instance over : 𝔸(n; S).CanonicallyOver S where
  hom := pullback.fst _ _

/-- The map from the affine `n`-space over `S` to the integral model `Spec ℤ[n]`. -/
def toSpecMvPoly : 𝔸(n; S) ⟶ Spec ℤ[n] := pullback.snd _ _

variable {X : Scheme.{u}}

/-- Morphisms into `Spec ℤ[n]` are equivalent the choice of `n` global sections. -/
@[simps]
def toSpecMvPolyIntEquiv : (X ⟶ Spec ℤ[n]) ≃ (n → Γ(X, ⊤)) where
  toFun f i := f.app ⊤ ((Scheme.ΓSpecIso ℤ[n]).inv (.X i))
  invFun v := X.toSpecΓ ≫ Spec.map
    (MvPolynomial.eval₂Hom ((algebraMap ℤ _).comp ULift.ringEquiv.toRingHom) v)
  left_inv f := by
    apply (ΓSpec.adjunction.homEquiv _ _).symm.injective
    apply Quiver.Hom.unop_inj
    rw [Adjunction.homEquiv_symm_apply, Adjunction.homEquiv_symm_apply]
    simp only [Functor.rightOp_obj, Scheme.Γ_obj, Scheme.Spec_obj, algebraMap_int_eq,
      RingEquiv.toRingHom_eq_coe, TopologicalSpace.Opens.map_top, Functor.rightOp_map, op_comp,
      Scheme.Γ_map, unop_comp, Quiver.Hom.unop_op, Scheme.comp_app, Scheme.toSpecΓ_app_top,
      Scheme.ΓSpecIso_naturality, ΓSpec.adjunction_counit_app, Category.assoc,
      Iso.cancel_iso_inv_left, ← Iso.eq_inv_comp]
    apply of_mvPolynomial_int_ext
    intro i
    rw [coe_eval₂Hom, eval₂_X]
    rfl
  right_inv v := by
    ext i
    simp only [algebraMap_int_eq, RingEquiv.toRingHom_eq_coe, Scheme.comp_coeBase,
      TopologicalSpace.Opens.map_comp_obj, TopologicalSpace.Opens.map_top, Scheme.comp_app,
      Scheme.toSpecΓ_app_top, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply,
      CommRingCat.coe_of]
    erw [Iso.hom_inv_id_apply]
    rw [coe_eval₂Hom, eval₂_X]

lemma toSpecMvPolyIntEquiv_comp {X Y : Scheme} (f : X ⟶ Y) (g : Y ⟶ Spec ℤ[n]) (i) :
    toSpecMvPolyIntEquiv n (f ≫ g) i = f.app ⊤ (toSpecMvPolyIntEquiv n g i) := rfl

variable {n} in
/-- The standard coordinates of `𝔸(n; S)`. -/
def coord (i : n) : Γ(𝔸(n; S), ⊤) := toSpecMvPolyIntEquiv _ (toSpecMvPoly n S) i

section homOfVector

variable {n S}

/-- The morphism `X ⟶ 𝔸(n; S)` given by a `X ⟶ S` and a choice of `n`-coordinate functions. -/
def homOfVector (f : X ⟶ S) (v : n → Γ(X, ⊤)) : X ⟶ 𝔸(n; S) :=
  pullback.lift f ((toSpecMvPolyIntEquiv n).symm v) (by simp)

variable (f : X ⟶ S) (v : n → Γ(X, ⊤))

@[reassoc (attr := simp)]
lemma homOfVector_over : homOfVector f v ≫ 𝔸(n; S) ↘ S = f :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma homOfVector_toSpecMvPoly :
    homOfVector f v ≫ toSpecMvPoly n S = (toSpecMvPolyIntEquiv n).symm v :=
  pullback.lift_snd _ _ _

@[local simp]
lemma homOfVector_app_top_coord (i) :
    (homOfVector f v).app ⊤ (coord S i) = v i := by
  rw [coord, ← toSpecMvPolyIntEquiv_comp, homOfVector_toSpecMvPoly,
    Equiv.apply_symm_apply]

@[ext 1100]
lemma hom_ext {f g : X ⟶ 𝔸(n; S)}
    (h₁ : f ≫ 𝔸(n; S) ↘ S = g ≫ 𝔸(n; S) ↘ S)
    (h₂ : ∀ i, f.app ⊤ (coord S i) = g.app ⊤ (coord S i)) : f = g := by
  apply pullback.hom_ext h₁
  show f ≫ toSpecMvPoly _ _ = g ≫ toSpecMvPoly _ _
  apply (toSpecMvPolyIntEquiv n).injective
  ext i
  rw [toSpecMvPolyIntEquiv_comp, toSpecMvPolyIntEquiv_comp]
  exact h₂ i

@[reassoc]
lemma comp_homOfVector {X Y : Scheme} (v : n → Γ(Y, ⊤)) (f : X ⟶ Y) (g : Y ⟶ S) :
    f ≫ homOfVector g v = homOfVector (f ≫ g) (f.app ⊤ ∘ v) := by
  ext1 <;> simp [-TopologicalSpace.Opens.map_top]; rfl

end homOfVector

variable [X.Over S]

variable {n}

instance (v : n → Γ(X, ⊤)) : (homOfVector (X ↘ S) v).IsOver S where

/-- `S`-morphisms into `Spec 𝔸(n; S)` are equivalent to the choice of `n` global sections. -/
@[simps]
def homOverEquiv : { f : X ⟶ 𝔸(n; S) // f.IsOver S } ≃ (n → Γ(X, ⊤)) where
  toFun f i := f.1.app ⊤ (coord S i)
  invFun v := ⟨homOfVector (X ↘ S) v, inferInstance⟩
  left_inv f := by
    ext : 2
    · simp [f.2.1]
    · rw [homOfVector_app_top_coord]
  right_inv v := by ext i; simp [-TopologicalSpace.Opens.map_top, homOfVector_app_top_coord]

lemma ext_of_isAffine {X Y : Scheme} [IsAffine Y] {f g : X ⟶ Y} (e : f.app ⊤ = g.app ⊤) :
    f = g := by
  rw [← cancel_mono Y.toSpecΓ, Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, e]

variable (n) in
/--
The affine space over an affine base is isomorphic to the spectrum of the polynomial ring.
Also see `AffineSpace.SpecIso`.
-/
@[simps (config := .lemmasOnly) hom inv]
def isoOfIsAffine [IsAffine S] :
    𝔸(n; S) ≅ Spec (.of (MvPolynomial n Γ(S, ⊤))) where
      hom := 𝔸(n; S).toSpecΓ ≫ Spec.map (eval₂Hom ((𝔸(n; S) ↘ S).app ⊤) (coord S))
      inv := homOfVector (Spec.map C ≫ S.isoSpec.inv)
        ((Scheme.ΓSpecIso (.of (MvPolynomial n Γ(S, ⊤)))).inv ∘ MvPolynomial.X)
      hom_inv_id := by
        ext1
        · simp only [Category.assoc, homOfVector_over, Category.id_comp]
          rw [← Spec.map_comp_assoc, CommRingCat.comp_eq_ring_hom_comp, eval₂Hom_comp_C,
            ← Scheme.toSpecΓ_naturality_assoc]
          simp [Scheme.isoSpec]
        · simp only [Scheme.comp_coeBase, TopologicalSpace.Opens.map_comp_obj, Scheme.comp_app,
            CommRingCat.coe_comp_of, RingHom.coe_comp, Function.comp_apply, Scheme.id.base,
            Scheme.id_app]
          -- note: `rw [homOfVector_app_top_coord]` works but takes 3 more seconds
          conv => enter [1, 2, 2]; rw [homOfVector_app_top_coord]
          simp only [TopologicalSpace.Opens.map_top, Scheme.toSpecΓ_app_top, Function.comp_apply,
            CommRingCat.id_apply]
          erw [elementwise_of% Scheme.ΓSpecIso_naturality, Iso.hom_inv_id_apply]
          exact eval₂_X _ _ _
      inv_hom_id := by
        apply ext_of_isAffine
        simp only [Scheme.comp_coeBase, TopologicalSpace.Opens.map_comp_obj,
          TopologicalSpace.Opens.map_top, Scheme.comp_app, Scheme.toSpecΓ_app_top,
          Scheme.ΓSpecIso_naturality, Category.assoc, Scheme.id_app, ← Iso.eq_inv_comp,
          Category.comp_id]
        apply ringHom_ext'
        · show _ = CommRingCat.ofHom C ≫ _
          rw [CommRingCat.comp_eq_ring_hom_comp, RingHom.comp_assoc, eval₂Hom_comp_C,
            ← CommRingCat.comp_eq_ring_hom_comp, ← cancel_mono (Scheme.ΓSpecIso _).hom]
          erw [← Scheme.comp_app]
          rw [homOfVector_over, Scheme.comp_app]
          simp only [TopologicalSpace.Opens.map_top, Category.assoc, Scheme.ΓSpecIso_naturality, ←
            Scheme.toSpecΓ_app_top]
          erw [← Scheme.comp_app_assoc]
          rw [Scheme.isoSpec, asIso_inv, IsIso.hom_inv_id]
          simp
          rfl
        · intro i
          erw [CommRingCat.comp_apply, coe_eval₂Hom]
          simp only [eval₂_X]
          exact homOfVector_app_top_coord _ _ _

@[simp]
lemma isoOfIsAffine_hom_app_top [IsAffine S] :
    (isoOfIsAffine n S).hom.app ⊤ =
      (Scheme.ΓSpecIso _).hom ≫ eval₂Hom ((𝔸(n; S) ↘ S).app ⊤) (coord S) := by
  simp [isoOfIsAffine_hom]

@[local simp]
lemma isoOfIsAffine_inv_app_top_coord [IsAffine S] (i) :
    (isoOfIsAffine n S).inv.app ⊤ (coord _ i) = (Scheme.ΓSpecIso (.of _)).inv (.X i) :=
  homOfVector_app_top_coord _ _ _

@[reassoc (attr := simp)]
lemma isoOfIsAffine_inv_over [IsAffine S] :
    (isoOfIsAffine n S).inv ≫ 𝔸(n; S) ↘ S = Spec.map C ≫ S.isoSpec.inv :=
  pullback.lift_fst _ _ _

instance [IsAffine S] : IsAffine 𝔸(n; S) := isAffine_of_isIso (isoOfIsAffine n S).hom

variable (n) in
/-- The affine space over an affine base is isomorphic to the spectrum of the polynomial ring. -/
def SpecIso (R : CommRingCat.{u}) :
    𝔸(n; Spec R) ≅ Spec (.of (MvPolynomial n R)) :=
  isoOfIsAffine _ _ ≪≫ Scheme.Spec.mapIso (MvPolynomial.mapEquiv _
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv).toCommRingCatIso.op

@[simp]
lemma SpecIso_hom_app_top (R : CommRingCat.{u}) :
    (SpecIso n R).hom.app ⊤ = (Scheme.ΓSpecIso _).hom ≫
      eval₂Hom ((Scheme.ΓSpecIso _).inv ≫ (𝔸(n; Spec R) ↘ Spec R).app ⊤) (coord (Spec R)) := by
  simp only [SpecIso, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, RingEquiv.toCommRingCatIso_hom,
    RingEquiv.toRingHom_eq_coe, Scheme.Spec_map, Quiver.Hom.unop_op, Scheme.comp_coeBase,
    TopologicalSpace.Opens.map_comp_obj, TopologicalSpace.Opens.map_top, Scheme.comp_app,
    isoOfIsAffine_hom_app_top]
  erw [Scheme.ΓSpecIso_naturality_assoc]
  congr 1
  apply ringHom_ext'
  · ext; simp; rfl
  · simp

@[local simp]
lemma SpecIso_inv_app_top_coord (R : CommRingCat.{u}) (i) :
    (SpecIso n R).inv.app ⊤ (coord _ i) = (Scheme.ΓSpecIso (.of _)).inv (.X i) := by
  simp only [SpecIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, RingEquiv.toCommRingCatIso_inv,
    mapEquiv_symm, RingEquiv.toRingHom_eq_coe, Scheme.Spec_map, Quiver.Hom.unop_op,
    Scheme.comp_coeBase, TopologicalSpace.Opens.map_comp_obj, TopologicalSpace.Opens.map_top,
    Scheme.comp_app, CommRingCat.comp_apply]
  erw [isoOfIsAffine_inv_app_top_coord, ← CommRingCat.comp_apply]
  rw [← Scheme.ΓSpecIso_inv_naturality]
  erw [CommRingCat.comp_apply]
  congr 1
  exact map_X _ _

@[reassoc (attr := simp)]
lemma SpecIso_inv_over (R : CommRingCat.{u}) :
    (SpecIso n R).inv ≫ 𝔸(n; Spec R) ↘ Spec R = Spec.map C := by
  simp only [SpecIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, RingEquiv.toCommRingCatIso_inv,
    mapEquiv_symm, RingEquiv.toRingHom_eq_coe, Scheme.Spec_map, Quiver.Hom.unop_op, Category.assoc,
    isoOfIsAffine_inv_over, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  congr 1
  rw [Iso.inv_comp_eq]
  ext
  exact map_C _ _

section functorial

variable (n) in
/-- `𝔸(n; S)` is functorial wrt `S`. -/
def map {S T : Scheme.{u}} (f : S ⟶ T) : 𝔸(n; S) ⟶ 𝔸(n; T) :=
  homOfVector (𝔸(n; S) ↘ S ≫ f) (coord S)

@[reassoc (attr := simp)]
lemma map_over {S T : Scheme.{u}} (f : S ⟶ T) : map n f ≫ 𝔸(n; T) ↘ T = 𝔸(n; S) ↘ S ≫ f :=
  pullback.lift_fst _ _ _

@[local simp]
lemma map_app_top_coord {S T : Scheme.{u}} (f : S ⟶ T) (i) :
    (map n f).app ⊤ (coord T i) = coord S i :=
  homOfVector_app_top_coord _ _ _

@[simp]
lemma map_id : map n (𝟙 S) = 𝟙 𝔸(n; S) := by
  ext1 <;> simp [-TopologicalSpace.Opens.map_top]; rfl

@[reassoc, simp]
lemma map_comp {S S' S'' : Scheme} (f : S ⟶ S') (g : S' ⟶ S'') :
    map n (f ≫ g) = map n f ≫ map n g := by
  ext1
  · simp
  · simp only [TopologicalSpace.Opens.map_top, Scheme.comp_coeBase,
      TopologicalSpace.Opens.map_comp_obj, Scheme.comp_app, CommRingCat.comp_apply]
    erw [map_app_top_coord, map_app_top_coord, map_app_top_coord]

lemma map_Spec_map {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    map n (Spec.map φ) =
      (SpecIso n S).hom ≫ Spec.map (MvPolynomial.map φ) ≫ (SpecIso n R).inv := by
  rw [← Iso.inv_comp_eq]
  ext1
  · simp only [map_over, Category.assoc, SpecIso_inv_over, SpecIso_inv_over_assoc,
      ← Spec.map_comp, CommRingCat.comp_eq_ring_hom_comp]
    rw [map_comp_C]
  · simp only [Scheme.comp_coeBase, TopologicalSpace.Opens.map_comp_obj,
      TopologicalSpace.Opens.map_top, Scheme.comp_app, CommRingCat.comp_apply]
    conv_lhs => enter[2]; tactic => exact map_app_top_coord _ _
    conv_rhs => enter[2]; tactic => exact SpecIso_inv_app_top_coord _ _
    erw [SpecIso_inv_app_top_coord, ← CommRingCat.comp_apply]
    rw [← Scheme.ΓSpecIso_inv_naturality]
    erw [CommRingCat.comp_apply, map_X]
    rfl

/-- The map between affine spaces over affine bases is
isomorphic to the natural map between polynomial rings.  -/
def mapSpecMap {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    Arrow.mk (map n (Spec.map φ)) ≅
      Arrow.mk (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := n) φ))) :=
  Arrow.isoMk (SpecIso n S) (SpecIso n R) (by simp [map_Spec_map]; rfl)

/-- `𝔸(n; S)` is functorial wrt `n`. -/
def reindex {n m : Type} (i : m → n) (S : Scheme.{u}) : 𝔸(n; S) ⟶ 𝔸(m; S) :=
  homOfVector (𝔸(n; S) ↘ S) (coord S ∘ i)

@[reassoc (attr := simp)]
lemma reindex_over {n m : Type} (i : m → n) (S : Scheme.{u}) :
    reindex i S ≫ 𝔸(m; S) ↘ S = 𝔸(n; S) ↘ S :=
  pullback.lift_fst _ _ _

@[local simp]
lemma reindex_app_top_coord {n m : Type} (i : m → n) (S : Scheme.{u}) (j : m) :
    (reindex i S).app ⊤ (coord S j) = coord S (i j) :=
  homOfVector_app_top_coord _ _ _

@[simp]
lemma reindex_id : reindex id S = 𝟙 𝔸(n; S) := by
  ext1 <;> simp [-TopologicalSpace.Opens.map_top]; rfl

lemma reindex_comp {n₁ n₂ n₃ : Type} (i : n₁ → n₂) (j : n₂ → n₃) (S : Scheme.{u}) :
    reindex (j ∘ i) S = reindex j S ≫ reindex i S := by
  have H₁ : reindex (j ∘ i) S ≫ 𝔸(n₁; S) ↘ S = (reindex j S ≫ reindex i S) ≫ 𝔸(n₁; S) ↘ S := by simp
  have H₂ (k) : (reindex (j ∘ i) S).app ⊤ (coord S k) =
      (reindex j S).app ⊤ ((reindex i S).app ⊤ (coord S k)) := by
    rw [reindex_app_top_coord, reindex_app_top_coord, reindex_app_top_coord]
    rfl
  exact hom_ext H₁ H₂

-- These time out if added to `reindex_comp` directly.
attribute [reassoc] reindex_comp
attribute [simp] reindex_comp

end functorial

end AffineSpace

end AlgebraicGeometry
