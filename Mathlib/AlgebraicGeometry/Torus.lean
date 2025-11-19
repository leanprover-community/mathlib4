/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Algebraic torus

## Main definitions

- `AlgebraicGeometry.Torus`: `𝕋(n; S)` is the split algebraic torus of dimension `n` over `S`.
- `AlgebraicGeometry.Torus.coord`: The standard coordinate functions on the torus.
- `AlgebraicGeometry.Torus.homOfVector`:
  The morphism `X ⟶ 𝕋(n; S)` given by a `X ⟶ S` and a choice of `n`-coordinate functions.
- `AlgebraicGeometry.Torus.homOverEquiv`:
  `S`-morphisms into `Spec 𝕋(n; S)` are equivalent to the choice of `n` invertible global sections.
- `AlgebraicGeometry.Torus.SpecIso`: `𝕋(n; Spec R) ≅ Spec R[X̲, X̲⁻¹]`.

-/

open CategoryTheory Limits MvPolynomial

noncomputable section

namespace AlgebraicGeometry

universe v u

variable (n : Type v) (S : Scheme.{max u v})

section Affine

variable (R : Type*) (σ : Type*) [CommRing R] {S : Type*} [CommRing S]

/-- `R[σ, σ⁻¹]`. This is the ring representing `S ↦ Fun(σ, Sˣ)`. -/
abbrev TorusRing : Type _ :=
  Localization (M := MvPolynomial σ R) (.closure (Set.range X))

variable {R σ}

/-- The monomial `Xᵢ` for `i : σ` in `R[σ, σ⁻¹]`. -/
abbrev TorusRing.X (i : σ) : TorusRing R σ := (algebraMap (MvPolynomial σ R) (TorusRing R σ) (.X i))

lemma TorusRing.isUnit_X (i : σ) : IsUnit (TorusRing.X (R := R) i) :=
  IsLocalization.map_units (R := MvPolynomial σ R) (TorusRing R σ)
    (M := .closure (Set.range MvPolynomial.X))
    ⟨MvPolynomial.X i, Submonoid.subset_closure ⟨i, rfl⟩⟩

/-- The monomial `Xᵢ` for `i : σ` as a unit in `R[σ, σ⁻¹]`. -/
abbrev TorusRing.XUnit (i : σ) : (TorusRing R σ)ˣ := (isUnit_X i).unit

/-- To give a ring hom `R[σ, σ⁻¹] →+* S`, it suffices to give a ring hom `R →+* S` and
an assignment of variables `σ → Sˣ`. -/
def TorusRing.lift (f : R →+* S) (v : σ → Sˣ) : TorusRing R σ →+* S :=
  IsLocalization.lift
    (R := MvPolynomial σ R) (M := .closure (Set.range MvPolynomial.X))
    (g := MvPolynomial.eval₂Hom f (Units.val ∘ v)) <| by
    simp only [Subtype.forall]
    show _ ≤ (IsUnit.submonoid _).comap _
    simp [Set.range_subset_iff, IsUnit.mem_submonoid_iff]

@[simp]
lemma TorusRing.lift_X (f : R →+* S) (v : σ → Sˣ) (i : σ) : TorusRing.lift f v (.X i) = v i := by
  simp [lift]

@[simp]
lemma TorusRing.lift_algebraMap (f : R →+* S) (v : σ → Sˣ) (r : R) :
    (TorusRing.lift f v (algebraMap R _ r)) = f r := by
  simp [lift, IsScalarTower.algebraMap_apply R (MvPolynomial σ R)]

lemma TorusRing.lift_comp (f : R →+* S) (v : σ → Sˣ) :
    (TorusRing.lift f v).comp (algebraMap R _) = f := by
  ext; exact TorusRing.lift_algebraMap f v _

@[ext high]
lemma TorusRing.ringHom_ext (f g : TorusRing R σ →+* S)
    (h₁ : f.comp (algebraMap R _) = g.comp (algebraMap R _))
    (h₂ : ∀ i, f (.X i) = g (.X i)) : f = g := by
  apply IsLocalization.ringHom_ext
      (R := MvPolynomial σ R) (M := .closure (Set.range MvPolynomial.X))
  ext x
  · exact DFunLike.congr_fun h₁ x
  · exact h₂ _

/-- The ring equiv `R[σ, σ⁻¹] ≅ S[σ, σ⁻¹]` if `R ≅ S`. -/
def TorusRing.equiv (e : R ≃+* S) : TorusRing R σ ≃+* TorusRing S σ where
  __ := TorusRing.lift ((algebraMap S (TorusRing S σ)).comp e.toRingHom) XUnit
  invFun := TorusRing.lift ((algebraMap R (TorusRing R σ)).comp e.symm.toRingHom) XUnit
  left_inv x := by
    dsimp
    show _ = RingHom.id _ x
    rw [← RingHom.comp_apply]
    congr 1
    ext <;> simp
  right_inv x := by
    dsimp
    show _ = RingHom.id _ x
    rw [← RingHom.comp_apply]
    congr 1
    ext <;> simp

end Affine

local notation3 "𝕋[" n "]" => CommRingCat.of (TorusRing (ULift ℤ) n)
local notation3 "𝕋[" n "].{" u "," v "}" => CommRingCat.of (TorusRing (ULift.{max u v} ℤ) n)

/-- `𝕋(n; S)` is the split algebraic torus of dimension `n` over `S`.
Note that `n` is an arbitrary index type (e.g. `Fin m`). -/
def Torus (n : Type v) (S : Scheme.{max u v}) : Scheme.{max u v} :=
  pullback (terminal.from S) (terminal.from (Spec 𝕋[n].{u, v}))

namespace Torus

/-- `𝕋(n; S)` is the (split) algebraic torus of dimension `n`-space over `S`. -/
scoped [AlgebraicGeometry] notation "𝕋("n"; "S")" => Torus n S

variable {n} in
lemma torusRing_int_ringHom_ext {R} {f g : 𝕋[n].{u, v} ⟶ R} (h : ∀ i, f (.X i) = g (.X i)) :
    f = g := by
  ext1
  apply IsLocalization.ringHom_ext
    (R := MvPolynomial n (ULift.{max u v} ℤ)) (M := .closure (Set.range MvPolynomial.X))
  ext x
  · obtain ⟨x, rfl⟩ := ULift.ringEquiv.symm.surjective x
    simp
  · simpa using h x

@[simps (config := .lemmasOnly)]
instance over : 𝕋(n; S).CanonicallyOver S where
  hom := pullback.fst _ _

/-- The map from the split algebraic torus over `S` to the integral model `Spec ℤ[X̲, X̲⁻¹]`. -/
def toSpecTorusRing : 𝕋(n; S) ⟶ Spec 𝕋[n].{u, v} := pullback.snd _ _

variable {X : Scheme.{max u v}}

/--
Morphisms into `Spec 𝕋[n]` are equivalent the choice of `n` invertible global sections.
Use `homOverEquiv` instead.
-/
@[simps]
def toSpecTorusRingEquiv : (X ⟶ Spec 𝕋[n].{u, v}) ≃ (n → Γ(X, ⊤)ˣ) where
  toFun f i := (TorusRing.XUnit i).map
    ((Scheme.ΓSpecIso 𝕋[n].{u, v}).inv ≫ f.appTop).hom.toMonoidHom
  invFun v := X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (TorusRing.lift ((Int.castRingHom _).comp ULift.ringEquiv.toRingHom) v))
  left_inv f := by
    show ΓSpec.adjunction.homEquiv _ _ _ = _
    rw [← Equiv.eq_symm_apply, Adjunction.homEquiv_symm_apply]
    apply Quiver.Hom.unop_inj
    apply torusRing_int_ringHom_ext
    simp [TorusRing.lift_X]
  right_inv v := by
    ext i
    simp [TorusRing.lift_X]

lemma toSpecTorusRingEquiv_comp {X Y : Scheme} (f : X ⟶ Y) (g : Y ⟶ Spec 𝕋[n].{u, v}) (i) :
    toSpecTorusRingEquiv n (f ≫ g) i = f.appTop (toSpecTorusRingEquiv n g i) := rfl

variable {n} in
/-- The standard coordinates in `Γ(𝕋(n; S), ⊤)ˣ` of the split algebraic torus. -/
def coord (i : n) : Γ(𝕋(n; S), ⊤)ˣ := toSpecTorusRingEquiv _ (toSpecTorusRing n S) i

section homOfVector

variable {n S}

/-- The morphism `X ⟶ 𝕋(n; S)` given by a `X ⟶ S` and a choice of `n`-coordinate functions. -/
def homOfVector (f : X ⟶ S) (v : n → Γ(X, ⊤)ˣ) : X ⟶ 𝕋(n; S) :=
  pullback.lift f ((toSpecTorusRingEquiv n).symm v) (terminal.hom_ext _ _)

variable (f : X ⟶ S) (v : n → Γ(X, ⊤)ˣ)

@[reassoc (attr := simp)]
lemma homOfVector_over : homOfVector f v ≫ 𝕋(n; S) ↘ S = f :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma homOfVector_toSpecMvPoly :
    homOfVector f v ≫ toSpecTorusRing n S = (toSpecTorusRingEquiv n).symm v :=
  pullback.lift_snd _ _ _

@[simp]
lemma homOfVector_appTop_coord (i) :
    (homOfVector f v).appTop (coord S i) = v i := by
  rw [coord, ← toSpecTorusRingEquiv_comp, homOfVector_toSpecMvPoly,
    Equiv.apply_symm_apply]

@[ext 1100]
lemma hom_ext {f g : X ⟶ 𝕋(n; S)}
    (h₁ : f ≫ 𝕋(n; S) ↘ S = g ≫ 𝕋(n; S) ↘ S)
    (h₂ : ∀ i, f.appTop (coord S i) = g.appTop (coord S i).val) : f = g := by
  apply pullback.hom_ext h₁
  show f ≫ toSpecTorusRing _ _ = g ≫ toSpecTorusRing _ _
  apply (toSpecTorusRingEquiv n).injective
  ext i
  rw [toSpecTorusRingEquiv_comp, toSpecTorusRingEquiv_comp]
  exact h₂ i

@[reassoc]
lemma comp_homOfVector {X Y : Scheme} (v : n → Γ(Y, ⊤)ˣ) (f : X ⟶ Y) (g : Y ⟶ S) :
    f ≫ homOfVector g v = homOfVector (f ≫ g) (Units.map f.appTop.hom.toMonoidHom ∘ v) := by
  ext1 <;> simp

end homOfVector

variable [X.Over S]

variable {n}

instance (v : n → Γ(X, ⊤)ˣ) : (homOfVector (X ↘ S) v).IsOver S where

/-- `S`-morphisms into `Spec 𝕋(n; S)` are equivalent to the choice of `n` global sections. -/
@[simps]
def homOverEquiv : { f : X ⟶ 𝕋(n; S) // f.IsOver S } ≃ (n → Γ(X, ⊤)ˣ) where
  toFun f i := (coord S i).map f.1.appTop.hom.toMonoidHom
  invFun v := ⟨homOfVector (X ↘ S) v, inferInstance⟩
  left_inv f := by
    ext : 2
    · simp [f.2.1]
    · rw [homOfVector_appTop_coord]
      rfl
  right_inv v := by ext i; simp [-TopologicalSpace.Opens.map_top, homOfVector_appTop_coord]

lemma isoSpec_inv_appTop (S : Scheme.{u}) [IsAffine S] :
    S.isoSpec.inv.appTop = (Scheme.ΓSpecIso _).inv := by
  rw [← Iso.comp_hom_eq_id, ← Scheme.toSpecΓ_appTop, ← Scheme.comp_appTop,
    Scheme.toSpecΓ_isoSpec_inv, Scheme.id_appTop]

variable (n) in
/--
The (split) torus over `Spec R` indexed by `σ` is isomorphic to `Spec R[σ, σ⁻¹]`.
Also see `Torus.SpecIso`.
-/
@[simps (config := .lemmasOnly) hom inv]
def isoOfIsAffine [IsAffine S] :
    𝕋(n; S) ≅ Spec (.of (TorusRing Γ(S, ⊤) n)) where
  hom := 𝕋(n; S).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (TorusRing.lift (𝕋(n; S) ↘ S).appTop.hom (coord S)))
  inv := homOfVector (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) _)) ≫ S.isoSpec.inv)
    fun i ↦ (TorusRing.XUnit (R := Γ(S, ⊤)) i).map
      (Scheme.ΓSpecIso (.of (TorusRing Γ(S, ⊤) n))).inv.hom.toMonoidHom
  hom_inv_id := by
    ext1
    · simp only [Category.assoc, homOfVector_over, comp_over]
      rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, TorusRing.lift_comp,
        CommRingCat.ofHom_hom, ← Scheme.toSpecΓ_naturality_assoc, ← Scheme.isoSpec_hom,
        Iso.hom_inv_id, Category.comp_id]
    · -- simp says
      simp only [RingHom.toMonoidHom_eq_coe, Category.assoc, Scheme.comp_app,
        Scheme.comp_coeBase, TopologicalSpace.Opens.map_comp_obj, TopologicalSpace.Opens.map_top,
        Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp,
        CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply, homOfVector_appTop_coord,
        Units.coe_map, IsUnit.unit_spec, MonoidHom.coe_coe, Scheme.id_app, CommRingCat.hom_id,
        RingHom.id_apply]
      rw [CommRingCat.hom_inv_apply, TorusRing.lift_X]
  inv_hom_id := by
    apply ext_of_isAffine
    simp only [RingHom.toMonoidHom_eq_coe, Scheme.comp_appTop,
      Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality, Category.assoc, Scheme.id_app,
      ← Iso.eq_inv_comp, Category.comp_id]
    ext1
    apply TorusRing.ringHom_ext
    · ext
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
        TorusRing.lift_algebraMap]
      simp only [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Scheme.comp_appTop,
        homOfVector_over]
      simp only [Scheme.comp_appTop, isoSpec_inv_appTop, CommRingCat.of_carrier,
        ← Scheme.ΓSpecIso_inv_naturality]
      rfl
    · intro i
      simp [TorusRing.lift_X]

@[simp]
lemma isoOfIsAffine_hom_appTop [IsAffine S] :
    (isoOfIsAffine.{v, u} n S).hom.appTop = (Scheme.ΓSpecIso _).hom ≫
      CommRingCat.ofHom (TorusRing.lift (R := Γ(S, ⊤)) (σ := n)
        (𝕋(n; S) ↘ S).appTop.hom (coord S)) := by
  simp [isoOfIsAffine]

@[simp]
lemma isoOfIsAffine_inv_appTop_coord [IsAffine S] (i) :
    (isoOfIsAffine n S).inv.appTop (coord S i) = (Scheme.ΓSpecIso (.of _)).inv (.X i) :=
  homOfVector_appTop_coord _ _ _

@[reassoc (attr := simp)]
lemma isoOfIsAffine_inv_over [IsAffine S] :
    (isoOfIsAffine n S).inv ≫ 𝕋(n; S) ↘ S =
      Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ S.isoSpec.inv :=
  pullback.lift_fst _ _ _

instance [IsAffine S] : IsAffine 𝕋(n; S) := isAffine_of_isIso (isoOfIsAffine n S).hom

variable (n) in
/-- The (split) algebraic torus over `Spec R` indexed by `σ` is isomorphic to `Spec R[σ, σ⁻¹]`. -/
def SpecIso (R : CommRingCat.{max u v}) :
    𝕋(n; Spec R) ≅ Spec (.of (TorusRing R n)) :=
  isoOfIsAffine _ _ ≪≫ Scheme.Spec.mapIso
    ((TorusRing.equiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm).toCommRingCatIso).op

@[simp]
lemma SpecIso_inv_appTop_coord (R : CommRingCat.{max u v}) (i) :
    (SpecIso n R).inv.appTop (coord (Spec R) i) = (Scheme.ΓSpecIso (.of _)).inv (.X i) := by
  simp only [SpecIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, RingEquiv.toCommRingCatIso_inv,
    Scheme.Spec_map, Quiver.Hom.unop_op, Scheme.comp_app, TopologicalSpace.Opens.map_top,
    CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, isoOfIsAffine_inv_appTop_coord]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
      CommRingCat.comp_apply]
  congr 1
  exact TorusRing.lift_X _ _ _

@[reassoc (attr := simp)]
lemma SpecIso_inv_over (R : CommRingCat.{max u v}) :
    (SpecIso n R).inv ≫ 𝕋(n; Spec R) ↘ Spec R = Spec.map (CommRingCat.ofHom (algebraMap _ _)) := by
  simp only [SpecIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv,
    mapEquiv_symm, RingEquiv.toRingHom_eq_coe, Scheme.Spec_map, Quiver.Hom.unop_op, Category.assoc,
    isoOfIsAffine_inv_over, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  congr 1
  rw [Iso.inv_comp_eq]
  ext : 2
  exact TorusRing.lift_algebraMap _ _ _

section functorial

variable (n) in
/-- `𝔸(n; S)` is functorial wrt `S`. -/
def map {S T : Scheme.{max u v}} (f : S ⟶ T) : 𝕋(n; S) ⟶ 𝕋(n; T) :=
  homOfVector (𝕋(n; S) ↘ S ≫ f) (coord S)

@[reassoc (attr := simp)]
lemma map_over {S T : Scheme.{max u v}} (f : S ⟶ T) : map n f ≫ 𝕋(n; T) ↘ T = 𝕋(n; S) ↘ S ≫ f :=
  pullback.lift_fst _ _ _

@[simp]
lemma map_appTop_coord {S T : Scheme.{max u v}} (f : S ⟶ T) (i) :
    (map n f).appTop (coord T i) = (coord S i).1 :=
  homOfVector_appTop_coord _ _ _

@[reassoc (attr := simp)]
lemma map_toSpecTorusRing {S T : Scheme.{max u v}} (f : S ⟶ T) :
    map n f ≫ toSpecTorusRing n T = toSpecTorusRing n S := by
  apply (toSpecTorusRingEquiv _).injective
  ext i
  rw [toSpecTorusRingEquiv_comp, ← coord, map_appTop_coord, coord]

@[simp]
lemma map_id : map n (𝟙 S) = 𝟙 𝕋(n; S) := by
  ext1 <;> simp

@[reassoc, simp]
lemma map_comp {S S' S'' : Scheme} (f : S ⟶ S') (g : S' ⟶ S'') :
    map n (f ≫ g) = map n f ≫ map n g := by
  ext1
  · simp
  · simp

lemma isPullback_map {S T : Scheme.{max u v}} (f : S ⟶ T) :
    IsPullback (map n f) (𝕋(n; S) ↘ S) (𝕋(n; T) ↘ T) f := by
  refine (IsPullback.paste_horiz_iff (.flip <| .of_hasPullback _ _) (map_over f)).mp ?_
  simp only [terminal.comp_from, ]
  convert (IsPullback.of_hasPullback _ _).flip
  rw [← toSpecTorusRing, ← toSpecTorusRing, map_toSpecTorusRing]

/-- `𝕋(n; S)` is functorial wrt `n`. -/
def reindex {n m : Type v} (i : m → n) (S : Scheme.{max u v}) : 𝕋(n; S) ⟶ 𝕋(m; S) :=
  homOfVector (𝕋(n; S) ↘ S) (coord S ∘ i)

@[simp, reassoc]
lemma reindex_over {n m : Type v} (i : m → n) (S : Scheme.{max u v}) :
    reindex i S ≫ 𝕋(m; S) ↘ S = 𝕋(n; S) ↘ S :=
  pullback.lift_fst _ _ _

@[simp]
lemma reindex_appTop_coord {n m : Type v} (i : m → n) (S : Scheme.{max u v}) (j : m) :
    (reindex i S).appTop (coord S j) = coord S (i j) :=
  homOfVector_appTop_coord _ _ _

@[simp]
lemma reindex_id : reindex id S = 𝟙 𝕋(n; S) := by
  ext1 <;> simp

@[simp, reassoc]
lemma reindex_comp {n₁ n₂ n₃ : Type v} (i : n₁ → n₂) (j : n₂ → n₃) (S : Scheme.{max u v}) :
    reindex (j ∘ i) S = reindex j S ≫ reindex i S := by
  have H₁ : reindex (j ∘ i) S ≫ 𝕋(n₁; S) ↘ S = (reindex j S ≫ reindex i S) ≫ 𝕋(n₁; S) ↘ S := by simp
  have H₂ (k) : (reindex (j ∘ i) S).appTop (coord S k) =
      (reindex j S).appTop ((reindex i S).appTop (coord S k).1) := by
    rw [reindex_appTop_coord, reindex_appTop_coord, reindex_appTop_coord]
    rfl
  exact hom_ext H₁ H₂

@[reassoc (attr := simp)]
lemma map_reindex {n₁ n₂ : Type v} (i : n₁ → n₂) {S T : Scheme.{max u v}} (f : S ⟶ T) :
    map n₂ f ≫ reindex i T = reindex i S ≫ map n₁ f := by
  apply hom_ext <;> simp

/-- The torus as a functor. -/
@[simps]
def functor : (Type v)ᵒᵖ ⥤ Scheme.{max u v} ⥤ Scheme.{max u v} where
  obj n := { obj := Torus n.unop, map := map n.unop, map_id := map_id, map_comp := map_comp }
  map {n m} i := { app := reindex i.unop, naturality := fun _ _ ↦ map_reindex i.unop }
  map_id n := by ext: 2; exact reindex_id _
  map_comp f g := by ext: 2; dsimp; exact reindex_comp _ _ _

end functorial

section instances

instance : IsAffineHom (𝕋(n; S) ↘ S) := MorphismProperty.pullback_fst _ _ inferInstance

end instances

end Torus

end AlgebraicGeometry
