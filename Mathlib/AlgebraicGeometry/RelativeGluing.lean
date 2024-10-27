/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Relative gluing

We show https://stacks.math.columbia.edu/tag/01LH

-/

universe t u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

variable (S : Scheme.{u})

/-- Given a morphism `f : X ⟶ Y` with range contained in `U`, this is the induced morphism
`X ⟶ U` by the universal property of `U.ι`. -/
def Scheme.Opens.lift {X Y : Scheme.{u}} (U : Y.Opens) (f : X ⟶ Y) (hf : Set.range f.base ⊆ U) :
    X ⟶ U :=
  IsOpenImmersion.lift U.ι f (by simp [hf])

@[reassoc (attr := simp)]
lemma Scheme.Opens.lift_fac {X Y : Scheme.{u}} (U : Y.Opens) (f : X ⟶ Y)
    (hf : Set.range f.base ⊆ U) :
    U.lift f hf ≫ U.ι = f :=
  IsOpenImmersion.lift_fac _ _ _

/--
A pre-relative gluing data on `S` is given by an indexed basis `{Uᵢ}` of the topology of `S`
(in applications this is usually the basis of affine opens), for every `i` a scheme `Xᵢ` over `Uᵢ`
and for every `i ≤ j` transition maps `Xᵢ ⟶ Xⱼ` satisfying compatibility conditions.
-/
structure PreRelativeGluingData where
  /-- The indexing type. -/
  ι : Type u
  /-- The opens `Uᵢ` of `S`. -/
  U (i : ι) : S.Opens
  hU : TopologicalSpace.Opens.IsBasis (Set.range U)
  /-- The schemes `Xᵢ` ... -/
  X (i : ι) : Scheme.{u}
  /-- ... over `Uᵢ`. -/
  f (i : ι) : X i ⟶ U i
  /-- For `i ≤ j`, the transition map `Xᵢ ⟶ Xⱼ`. -/
  ρ {i j : ι} (hij : U i ≤ U j) : X i ⟶ X j
  w {i j : ι} (hij : U i ≤ U j) : ρ hij ≫ f j = f i ≫ S.homOfLE hij
  comp {i j k : ι} (hij : U i ≤ U j) (hjk : U j ≤ U k) : ρ hij ≫ ρ hjk = ρ (hij.trans hjk)

attribute [reassoc (attr := simp)] PreRelativeGluingData.w

variable {S} (d : PreRelativeGluingData S) in
lemma PreRelativeGluingData.f_ι {i j : d.ι} (hij : d.U i ≤ d.U j) :
    d.f i ≫ (d.U i).ι = d.ρ hij ≫ d.f j ≫ (d.U j).ι := by
  simp

variable {S} (d : PreRelativeGluingData S) in
/-- The restriction of `ρᵢⱼ` to `Xᵢ ⟶ fⱼ⁻¹(Uᵢ)`. -/
def PreRelativeGluingData.ρres {i j : d.ι} (hij : d.U i ≤ d.U j) :
    d.X i ⟶ (d.f j ⁻¹ᵁ (d.U j).ι ⁻¹ᵁ d.U i) :=
  (d.f j ⁻¹ᵁ (d.U j).ι ⁻¹ᵁ d.U i).lift (d.ρ hij) <| by
    rintro x ⟨y, rfl⟩
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe]
    rw [← Scheme.comp_base_apply, ← Scheme.comp_base_apply, d.w_assoc]
    simp only [Scheme.homOfLE_ι, Scheme.comp_coeBase, TopCat.coe_comp, Function.comp_apply]
    exact ((d.f i).base y).property

variable {S} (d : PreRelativeGluingData S) in
@[reassoc (attr := simp)]
lemma PreRelativeGluingData.ρres_ι {i j : d.ι} (hij : d.U i ≤ d.U j) :
    d.ρres hij ≫ (d.f j ⁻¹ᵁ (d.U j).ι ⁻¹ᵁ d.U i).ι = d.ρ hij :=
  (d.f j ⁻¹ᵁ (d.U j).ι ⁻¹ᵁ d.U i).lift_fac _ _

/--
A relative gluing data on `S` is a pre-relative gluing data where for every `i ≤ j`,
`ρᵢⱼ` induces an isomorphism `Xᵢ ⟶ fⱼ⁻¹(Uᵢ)`.
-/
structure RelativeGluingData extends PreRelativeGluingData S where
  ρIso {i j : ι} (hij : U i ≤ U j) : IsIso (toPreRelativeGluingData.ρres hij)

namespace RelativeGluingData

variable {S} (d : RelativeGluingData S)

instance {i j : d.ι} (hij : d.U i ≤ d.U j) : IsIso (d.ρres hij) :=
  d.ρIso hij

instance {i j : d.ι} (hij : d.U i ≤ d.U j) : Mono (d.ρ hij) := by
  rw [← d.ρres_ι]
  infer_instance

/-- A compatible family on an `T` over a relative gluing datum is
a morphism `g : T ⟶ S` and a compatible family of `S`-morphisms
`hᵢ : g⁻¹(Uᵢ) ⟶ Xᵢ`. -/
structure CompatibleFamily (T : Scheme.{u}) : Type _ where
  /-- The structure morphism. -/
  g : T ⟶ S
  /-- For every `i`, a morphism `g⁻¹(Uᵢ) ⟶ Xᵢ` -/
  h (i : d.ι) : (g ⁻¹ᵁ (d.U i)).toScheme ⟶ d.X i
  hcompf (i : d.ι) : h i ≫ d.f i = g ∣_ (d.U i)
  hcompρ (i j : d.ι) (hij : d.U i ≤ d.U j) : h i ≫ d.ρ hij =
    T.homOfLE (g.preimage_le_preimage_of_le hij) ≫ h j

attribute [reassoc] CompatibleFamily.hcompf

open TopologicalSpace

lemma CompatibleFamily.eq_iff {T : Scheme.{u}} {C C' : d.CompatibleFamily T} :
    C = C' ↔ ∃ hg : C.g = C'.g, ∀ i, C.h i = (T.isoOfEq (by rw [hg])).hom ≫ C'.h i := by
  constructor
  · rintro rfl
    simp
  · obtain ⟨g, h⟩ := C
    obtain ⟨g', h'⟩ := C'
    rintro ⟨rfl : g = g', e⟩
    simp only [Scheme.isoOfEq_rfl, Iso.refl_hom, Category.id_comp] at e
    simp only [mk.injEq, heq_eq_eq, true_and]
    ext i : 1
    exact e i

@[ext (iff := false)]
lemma CompatibleFamily.ext {T : Scheme.{u}} {C C' : d.CompatibleFamily T}
    (hg : C.g = C'.g) (hi : ∀ i, C.h i = (T.isoOfEq (by rw [hg])).hom ≫ C'.h i) : C = C' := by
  rw [CompatibleFamily.eq_iff]
  exact ⟨hg, hi⟩

@[reassoc]
lemma morphismRestrict_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) (U U' : Y.Opens) (hUU' : U ≤ U') :
    f ∣_ U ≫ Y.homOfLE hUU' = X.homOfLE (f.preimage_le_preimage_of_le hUU') ≫ f ∣_ U' := by
  rw [← cancel_mono U'.ι]
  simp

/-- Map a compatible family along a morphism of schemes. -/
@[simps]
def compatibleFamilyMap {T T' : Scheme.{u}} (p : T' ⟶ T) (C : d.CompatibleFamily T) :
    d.CompatibleFamily T' where
  g := p ≫ C.g
  h i := p ∣_ (C.g ⁻¹ᵁ (d.U i)) ≫ C.h i
  hcompf i := by
    simp only [Scheme.comp_coeBase, TopologicalSpace.Opens.map_comp_obj, Category.assoc]
    rw [C.hcompf, morphismRestrict_comp]
  hcompρ i j hij := by
    simp only [Scheme.comp_coeBase, TopologicalSpace.Opens.map_comp_obj, Category.assoc, C.hcompρ]
    rw [morphismRestrict_naturality_assoc]

@[simp]
lemma compatibleFamilyMap_id {T : Scheme.{u}} (C : d.CompatibleFamily T) :
    d.compatibleFamilyMap (𝟙 T) C = C := by
  ext : 1 <;> simp

@[simp]
lemma compatibleFamilyMap_comp {X Y Z : Scheme.{u}} (p : X ⟶ Y) (q : Y ⟶ Z)
    (C : d.CompatibleFamily Z) :
    d.compatibleFamilyMap (p ≫ q) C = d.compatibleFamilyMap p (d.compatibleFamilyMap q C) := by
  ext i : 1
  · simp
  · simp only [compatibleFamilyMap_g, Scheme.comp_coeBase, TopologicalSpace.Opens.map_comp_obj,
      compatibleFamilyMap_h, eqToHom_refl, Category.id_comp]
    rw [morphismRestrict_comp]
    simp

/--
The functor sending a scheme `T` to the type of compatible families on `T` over
the relative gluing datum `d`.

This is actually a representable sheaf.
-/
@[simps map]
def presheaf : Scheme.{u}ᵒᵖ ⥤ Type _ where
  obj := fun ⟨T⟩ ↦ d.CompatibleFamily T
  map p := d.compatibleFamilyMap p.unop
  map_id X := by
    ext : 1
    simp
  map_comp f g := by
    ext : 1
    simp

section IsSheaf

variable {T : Scheme.{u}} {𝒰 : T.OpenCover}
  {x : Presieve.FamilyOfElements d.presheaf (Presieve.ofArrows 𝒰.obj 𝒰.map)}
  (hx : x.Compatible)

variable (x) in
private def H (i : 𝒰.J) := x (𝒰.map i) (Presieve.ofArrows.mk i)

lemma H_def (i : 𝒰.J) : d.H x i = x (𝒰.map i) (Presieve.ofArrows.mk i) := rfl

private def aux : T ⟶ S :=
  𝒰.glueMorphisms (fun i ↦ (d.H x i).g) <| by
    intro i j
    rw [Presieve.pullbackCompatible_iff] at hx
    have h := hx (Presieve.ofArrows.mk i) (Presieve.ofArrows.mk j)
    simp only [presheaf, Quiver.Hom.unop_op] at h
    apply_fun CompatibleFamily.g at h
    simp only [compatibleFamilyMap_g] at h
    exact h

@[reassoc (attr := simp)]
private lemma aux_spec (j : 𝒰.J) :
    𝒰.map j ≫ d.aux hx = (d.H x j).g :=
  𝒰.ι_glueMorphisms _ _ j

private def 𝒱 (i : d.ι) : (d.aux hx ⁻¹ᵁ (d.U i)).toScheme.OpenCover where
  J := 𝒰.J
  obj j := (d.H x j).g ⁻¹ᵁ (d.U i)
  map j := IsOpenImmersion.lift (d.aux hx ⁻¹ᵁ (d.U i)).ι
      (((d.H x j).g ⁻¹ᵁ (d.U i)).ι ≫ 𝒰.map j) <| by
    simp only [Scheme.comp_coeBase, TopCat.coe_comp, Scheme.Opens.range_ι,
      TopologicalSpace.Opens.map_coe]
    intro t ht
    obtain ⟨y, rfl⟩ := ht
    simp only [Function.comp_apply, Set.mem_preimage, SetLike.mem_coe]
    rw [← Scheme.comp_base_apply]
    erw [Scheme.OpenCover.ι_glueMorphisms]
    exact y.property
  f x := 𝒰.f x.val
  covers z := by
    obtain ⟨y, hy⟩ := 𝒰.covers z.val
    simp only [Set.mem_range]
    have hym : y ∈ (d.H x (𝒰.f z.val)).g ⁻¹ᵁ (d.U i) := by
      rw [← d.aux_spec hx]
      show (𝒰.map (𝒰.f z.val) ≫ d.aux hx).base y ∈ d.U i
      simp only [Scheme.comp_coeBase, TopCat.coe_comp, Function.comp_apply, hy]
      exact z.property
    use ⟨y, hym⟩
    have : Function.Injective ((d.aux hx ⁻¹ᵁ (d.U i)).ι.base) := Subtype.val_injective
    apply this
    rw [← Scheme.comp_base_apply, IsOpenImmersion.lift_fac]
    simp only [Scheme.comp_coeBase, TopCat.coe_comp, Function.comp_apply]
    exact hy

@[reassoc (attr := simp)]
private lemma 𝒱.map_ι (i : d.ι) (j : 𝒰.J) :
    (d.𝒱 hx i).map j ≫ (d.aux hx ⁻¹ᵁ (d.U i)).ι = ((d.H x j).g ⁻¹ᵁ (d.U i)).ι ≫ 𝒰.map j :=
  IsOpenImmersion.lift_fac _ _ _

/-- -/
lemma foo' {X Y : Scheme.{u}} {U : Y.Opens} (f : X ⟶ U) :
    X.topIso.inv ≫ (X.isoOfEq (by simp)).inv ≫ (f ≫ U.ι) ∣_ U = f := by
  rw [← cancel_mono U.ι]
  simp

@[reassoc (attr := simp)]
lemma Scheme.isoOfEq_hom_isoOfEq_hom {X : Scheme.{u}} {U V W : X.Opens} (hUV : U = V)
    (hVW : V = W) :
    (X.isoOfEq hUV).hom ≫ (X.isoOfEq hVW).hom = (X.isoOfEq (hUV.trans hVW)).hom := by
  rw [← cancel_mono W.ι]
  simp

@[simp]
lemma Scheme.isoOfEq_inv {X : Scheme.{u}} {U V : X.Opens} (hUV : U = V) :
    (X.isoOfEq hUV).inv = (X.isoOfEq hUV.symm).hom := by
  rw [← cancel_mono U.ι]
  simp

private lemma fst_H_eq_snd_H (i : d.ι) (k l : 𝒰.J) :
    pullback.fst ((d.𝒱 hx i).map l) ((d.𝒱 hx i).map k) ≫ (d.H x l).h i =
      pullback.snd ((d.𝒱 hx i).map l) ((d.𝒱 hx i).map k) ≫ (d.H x k).h i := by
  set p1 := pullback.fst ((𝒱 d hx i).map l) ((𝒱 d hx i).map k)
  set p2 := pullback.snd ((𝒱 d hx i).map l) ((𝒱 d hx i).map k)
  set u1 : (𝒱 d hx i).obj l ⟶ 𝒰.obj l := ((d.H x l).g ⁻¹ᵁ (d.U i)).ι
  set u2 : (𝒱 d hx i).obj k ⟶ 𝒰.obj k := ((d.H x k).g ⁻¹ᵁ (d.U i)).ι
  have h := hx (p1 ≫ u1) (p2 ≫ u2) (Presieve.ofArrows.mk l) (Presieve.ofArrows.mk k) <| by
    simp only [Category.assoc, u1, u2]
    rw [← 𝒱.map_ι]
    rw [← 𝒱.map_ι]
    simp only [p1, p2]
    rw [pullback.condition_assoc]
  simp only [presheaf, Quiver.Hom.unop_op] at h
  rw [CompatibleFamily.eq_iff] at h
  obtain ⟨hg, hc⟩ := h
  simp only [compatibleFamilyMap_g, Scheme.comp_coeBase, TopologicalSpace.Opens.map_comp_obj,
    compatibleFamilyMap_h] at hc
  replace hc := hc i
  simp only [H]
  rw [← foo' p1]
  rw [← foo' p2]
  simp_rw [Category.assoc]
  erw [hc]
  simp
  rfl

private def auxh (i : d.ι) : (d.aux hx ⁻¹ᵁ (d.U i)).toScheme ⟶ d.X i :=
  (d.𝒱 hx i).glueMorphisms (fun j ↦ (d.H x j).h i) <| fun k l ↦ d.fst_H_eq_snd_H hx i l k

@[reassoc (attr := simp)]
lemma auxh_spec (i : d.ι) (j : 𝒰.J) :
    (d.𝒱 hx i).map j ≫ d.auxh hx i = (d.H x j).h i :=
  (d.𝒱 hx i).ι_glueMorphisms _ _ _

@[reassoc]
lemma 𝓋_map_homOfLE {k : 𝒰.J} {i j} (hij : d.U i ≤ d.U j) :
    (d.𝒱 hx i).map k ≫ T.homOfLE ((d.aux hx).preimage_le_preimage_of_le hij) =
      (𝒰.obj k).homOfLE (Scheme.Hom.preimage_le_preimage_of_le _ hij) ≫ (d.𝒱 hx j).map k := by
  rw [← cancel_mono (d.aux hx ⁻¹ᵁ d.U j).ι]
  simp

@[simps]
private def auxFamily : d.CompatibleFamily T where
  g := d.aux hx
  h := d.auxh hx
  hcompf i := by
    apply (d.𝒱 hx i).hom_ext
    intro j
    simp only [auxh_spec_assoc]
    rw [(d.H x j).hcompf]
    rw [← cancel_mono (d.U i).ι]
    simp
  hcompρ i j hij := by
    apply (d.𝒱 hx i).hom_ext
    intro k
    simp only [auxh_spec_assoc]
    rw [(d.H x k).hcompρ]
    rw [d.𝓋_map_homOfLE_assoc _ hij]
    simp

lemma auxFamily_isAmalgamation : x.IsAmalgamation (d.auxFamily hx) := by
  rintro Y - ⟨i⟩
  simp only [presheaf, Quiver.Hom.unop_op]
  rw [CompatibleFamily.eq_iff]
  simp only [compatibleFamilyMap_g, auxFamily_g, Scheme.comp_coeBase,
    TopologicalSpace.Opens.map_comp_obj, compatibleFamilyMap_h, auxFamily_h, aux_spec, H,
    exists_true_left]
  intro j
  rw [← IsIso.Iso.inv_inv, IsIso.eq_inv_comp]
  simp_rw [← d.H_def (x := x), ← d.auxh_spec hx j i]
  rw [← Category.assoc]
  congr
  rw [← cancel_mono (d.aux hx ⁻¹ᵁ (d.U j)).ι]
  simp

lemma auxFamily_unique (C : d.CompatibleFamily T) (hC : x.IsAmalgamation C) :
    C = d.auxFamily hx := by
  symm
  rw [CompatibleFamily.eq_iff]
  have hg : (AlgebraicGeometry.RelativeGluingData.auxFamily d hx).g = C.g := by
    apply 𝒰.hom_ext
    intro i
    simp only [auxFamily_g, aux_spec]
    have := hC (𝒰.map i) ⟨i⟩
    simp only [presheaf, Quiver.Hom.unop_op] at this
    apply_fun CompatibleFamily.g at this
    simpa using this.symm
  use hg
  intro i
  apply (d.𝒱 hx i).hom_ext
  intro j
  have := hC (𝒰.map j) ⟨j⟩
  rw [CompatibleFamily.eq_iff] at this
  obtain ⟨_, hc⟩ := this
  simp only [auxFamily_h, auxh_spec, auxFamily_g]
  simp only [presheaf, Quiver.Hom.unop_op, compatibleFamilyMap_g, Scheme.comp_coeBase,
    TopologicalSpace.Opens.map_comp_obj, compatibleFamilyMap_h] at hc
  rw [← cancel_epi ((𝒰.obj j).isoOfEq _).hom]
  · simp_rw [H_def]
    rw [← hc, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← cancel_mono (C.g ⁻¹ᵁ d.U i).ι]
    simp only [morphismRestrict_ι, Category.assoc, Scheme.isoOfEq_hom_ι, 𝒱.map_ι]
    rw [← Category.assoc]
    congr 1
    erw [Scheme.isoOfEq_hom_ι]

end IsSheaf

lemma presheaf_isSheaf : Presheaf.IsSheaf Scheme.zariskiTopology d.presheaf := by
  rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_pretopology]
  rintro T s ⟨𝒰, rfl⟩
  intro x hx
  exact ⟨d.auxFamily hx, d.auxFamily_isAmalgamation hx, d.auxFamily_unique hx⟩

/-- `d.presheaf` wrapped as a sheaf. -/
def sheaf : Sheaf Scheme.zariskiTopology (Type _) where
  val := d.presheaf
  cond := d.presheaf_isSheaf

section OpenSubfunctor

variable {i : d.ι} {T : Scheme.{u}} (f : T ⟶ d.X i)

private def auxg : T ⟶ S := f ≫ d.f i ≫ (d.U i).ι

lemma auxg_mem (x : T) : (d.auxg f).base x ∈ d.U i :=
  Subtype.property _

lemma range_auxg_ι_f_subset {j : d.ι} :
    Set.range ((d.auxg f ⁻¹ᵁ d.U j).ι ≫ f).base ⊆ d.f i ⁻¹ᵁ (d.U i).ι ⁻¹ᵁ d.U j := by
  simp [auxg]
  rintro a ⟨a, rfl⟩
  exact a.property

private def auxhOfLE {j : d.ι} (hji : d.U j ≤ d.U i) : (d.auxg f ⁻¹ᵁ d.U j).toScheme ⟶ d.X j :=
  (d.f i ⁻¹ᵁ (d.U i).ι ⁻¹ᵁ d.U j).lift _ (d.range_auxg_ι_f_subset f) ≫ inv (d.ρres hji)

@[reassoc]
lemma auxhOfLE_ρres_ι {j : d.ι} (hji : d.U j ≤ d.U i) :
    d.auxhOfLE f hji ≫ d.ρres hji ≫ (d.f i ⁻¹ᵁ (d.U i).ι ⁻¹ᵁ d.U j).ι =
      (d.auxg f ⁻¹ᵁ d.U j).ι ≫ f := by
  simp only [auxhOfLE, Category.assoc, IsIso.inv_hom_id_assoc]
  simp

@[reassoc (attr := simp)]
lemma auxhOfLE_ρ {j : d.ι} (hji : d.U j ≤ d.U i) :
    d.auxhOfLE f hji ≫ d.ρ hji = (d.auxg f ⁻¹ᵁ d.U j).ι ≫ f := by
  rw [← d.ρres_ι, auxhOfLE_ρres_ι]

@[reassoc (attr := simp)]
lemma auxhOfLE_f {j : d.ι} (hji : d.U j ≤ d.U i) :
    d.auxhOfLE f hji ≫ d.f j = d.auxg f ∣_ d.U j := by
  rw [← cancel_mono (d.U j).ι, Category.assoc, morphismRestrict_ι]
  rw [d.f_ι hji, ← d.ρres_ι, Category.assoc, auxhOfLE_ρres_ι_assoc]
  rfl

@[reassoc]
lemma auxhOfLE_trans {j k : d.ι} (hji : d.U j ≤ d.U i) (hkj : d.U k ≤ d.U j) :
    T.homOfLE ((d.auxg f).preimage_le_preimage_of_le hkj) ≫
      d.auxhOfLE f hji = d.auxhOfLE f (hkj.trans hji) ≫ d.ρ hkj := by
  rw [← cancel_mono (d.ρ hji)]
  simp only [Category.assoc, auxhOfLE_ρ, Scheme.homOfLE_ι_assoc]
  rw [d.comp]
  simp

@[reassoc]
lemma auxhOfLE_comp {j : d.ι} (hji : d.U j ≤ d.U i) {Y : Scheme.{u}} (h : Y ⟶ T) :
    d.auxhOfLE (h ≫ f) hji = h ∣_ d.auxg f ⁻¹ᵁ d.U j ≫ d.auxhOfLE f hji := by
  rw [← cancel_mono (d.ρ hji)]
  simp only [auxhOfLE_ρ, Category.assoc, morphismRestrict_ι_assoc]
  rfl

open TopologicalSpace

section

/-- An `OpensCover` is an indexed covering by open sets. See `Scheme.OpenCover` for
the more general version for open immersions. -/
structure _root_.AlgebraicGeometry.Scheme.OpensCover (X : Scheme.{u}) where
  /-- The indexing type. -/
  J : Type*
  /-- The family of opens. -/
  U : J → X.Opens
  /-- For `x : X` an index `i` such that `x ∈ Uᵢ`. -/
  f : X → J
  covers : ∀ x, x ∈ U (f x)

/-- Turn a cover by open sets into an `OpenCover`. -/
@[simps map]
def _root_.AlgebraicGeometry.Scheme.OpensCover.openCover {X : Scheme.{u}} (𝒰 : X.OpensCover) :
    X.OpenCover where
  J := 𝒰.J
  obj i := 𝒰.U i
  map i := (𝒰.U i).ι
  f := 𝒰.f
  covers x := by simp [𝒰.covers]

/-- Pullback of a cover `𝒰` by open sets along a morphism. The covering opens
are simply given by `f⁻¹ᵁ 𝒰.U i`. -/
@[simps]
def _root_.AlgebraicGeometry.Scheme.OpensCover.pullbackCover {X Y : Scheme.{u}}
    (𝒰 : Y.OpensCover) (f : X ⟶ Y) : X.OpensCover where
  J := 𝒰.J
  U j := f ⁻¹ᵁ 𝒰.U j
  f x := 𝒰.f (f.base x)
  covers x := 𝒰.covers (f.base x)

/-- From a covering family of opens, construct an `OpenCover`. -/
def _root_.AlgebraicGeometry.Scheme.OpenCover.fromOpens {X : Scheme.{u}} {ι : Type*}
    (U : ι → X.Opens) (f : X → ι) (covers : ∀ x, x ∈ U (f x)) : X.OpenCover where
  J := ι
  obj i := U i
  map i := (U i).ι
  f := f
  covers x := by simp [covers]

variable {X : Scheme.{u}} {ι : Type*} {ℬ : ι → X.Opens} (hℬ : Opens.IsBasis <| Set.range ℬ)

section

variable {X : Type*} [TopologicalSpace X] {ℬ : Set <| Opens X} (hℬ : Opens.IsBasis ℬ)

/-- Given a basis of opens `ℬ` and any open `U`, this is the set of all opens
of `ℬ` contained in `U`. -/
@[nolint unusedArguments]
def coveringSet (_ : Opens.IsBasis ℬ) (U : Opens X) : Set (Opens X) :=
  { V : Opens X | V ∈ ℬ ∧ V ≤ U }

@[simp]
lemma coveringSet_mem (U V : Opens X) : V ∈ coveringSet hℬ U ↔ V ∈ ℬ ∧ V ≤ U := by
  simp [coveringSet]

lemma coveringSet_subset (U : Opens X) : coveringSet hℬ U ⊆ ℬ := by
  intro V hV
  exact hV.left

lemma sSup_coveringSet (U : Opens X) : U = sSup (coveringSet hℬ U) := by
  refine le_antisymm (fun u hu ↦ ?_) ?_
  · obtain ⟨V, hV⟩ := Opens.isBasis_iff_nbhd.mp hℬ hu
    simp only [Opens.coe_sSup, Set.mem_setOf_eq, Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    tauto
  · rw [sSup_le_iff]
    intro V hV
    exact hV.2

end

section

variable {X : Type*} [TopologicalSpace X] {ι : Type*} {ℬ : ι → Opens X}
  (hℬ : Opens.IsBasis <| Set.range ℬ)

/-- Given an indexed basis of opens `ℬ`, this is for an open `U` the set of indices `i`
where `ℬ i ≤ U`. -/
def coveringIndexSet (U : Opens X) : Set ι := ℬ ⁻¹' coveringSet hℬ U

@[simp]
lemma coveringIndexSet_mem (U : Opens X) (i : ι) :
    i ∈ coveringIndexSet hℬ U ↔ ℬ i ≤ U := by
  simp [coveringIndexSet]

lemma iSup_coveringIndexSet (U : Opens X) :
    U = ⨆ i ∈ coveringIndexSet hℬ U, ℬ i := by
  nth_rw 1 [sSup_coveringSet hℬ U]
  aesop

variable {hℬ} in
lemma coveringIndexSet_le {U : Opens X} {i : ι} (hi : i ∈ coveringIndexSet hℬ U) :
    ℬ i ≤ U := by
  simpa using hi

lemma coveringIndexSet_exists_of_mem {U : Opens X} {x : X} (hx : x ∈ U) :
    ∃ i ∈ coveringIndexSet hℬ U, x ∈ ℬ i := by
  rw [iSup_coveringIndexSet hℬ U] at hx
  simpa using hx

end

/-- Construct an open cover from a covering family of open immersions. See
`Scheme.OpenCover.mkOfiSupEqTop` for an alternative covering condition. -/
def _root_.AlgebraicGeometry.Scheme.OpenCover.mkOfCovers {X : Scheme.{u}}
    (J : Type*) (obj : J → Scheme.{u}) (map : (j : J) → obj j ⟶ X)
    (covers : ∀ x, ∃ j y, (map j).base y = x)
    (IsOpen : ∀ j, IsOpenImmersion (map j) := by infer_instance) : X.OpenCover where
  J := J
  obj := obj
  map := map
  f x := (covers x).choose
  covers x := (covers x).choose_spec
  IsOpen := IsOpen

/-- Construct an open cover from a covering family of open immersions. See
`Scheme.OpenCover.mkOfCovers` for an alternative covering condition. -/
def _root_.AlgebraicGeometry.Scheme.OpenCover.mkOfiSupEqTop {X : Scheme.{u}}
    (J : Type*) (obj : J → Scheme.{u}) (map : (j : J) → obj j ⟶ X)
    (iSup_eq_top : ⋃ j, Set.range (map j).base = ⊤)
    (IsOpen : ∀ j, IsOpenImmersion (map j) := by infer_instance) : X.OpenCover :=
  have covers (x : X) : ∃ j y, (map j).base y = x := by
    have : x ∈ ⋃ j, Set.range (map j).base := by
      rw [iSup_eq_top]
      trivial
    simpa using this
  Scheme.OpenCover.mkOfCovers J obj map covers IsOpen

/-- Any compatible family on `T` over a relative gluing datum `d` induces
a natural open cover on `T`. -/
@[simps! (config := .lemmasOnly) map]
def CompatibleFamily.openCover {T : Scheme.{u}} (C : d.CompatibleFamily T) :
    T.OpenCover :=
  Scheme.OpenCover.mkOfiSupEqTop d.ι (fun i ↦ C.g ⁻¹ᵁ d.U i)
    (fun i ↦ (C.g ⁻¹ᵁ d.U i).ι) <| by
  simp only [Scheme.Opens.range_ι, Opens.map_coe, Set.top_eq_univ]
  have : ⋃ i, (d.U i : Set S) = Set.univ := by
    rw [Set.iUnion_eq_univ_iff]
    intro s
    obtain ⟨i, ⟨i, rfl⟩, hi⟩ := Opens.isBasis_iff_nbhd.mp d.hU (Opens.mem_top s)
    use i
    exact hi.left
  rw [← Set.preimage_iUnion, this]
  simp

end

@[simps! (config := .lemmasOnly) map]
private def 𝒲new (j : d.ι) : (d.auxg f ⁻¹ᵁ d.U j).toScheme.OpenCover :=
  Scheme.OpenCover.mkOfCovers
      (coveringIndexSet d.hU (d.U i ⊓ d.U j))
      (fun k ↦ d.auxg f ⁻¹ᵁ d.U k)
      (fun k ↦
        have hk : d.U k ≤ d.U j := le_trans (coveringIndexSet_le k.property) inf_le_right
        T.homOfLE ((d.auxg f).preimage_le_preimage_of_le hk)) <| by
    intro ⟨x, (hx : (d.auxg f).base x ∈ d.U j)⟩
    have hx' : (d.auxg f).base x ∈ d.U i ⊓ d.U j :=
      ⟨d.auxg_mem f x, hx⟩
    obtain ⟨o, ocov, ho⟩ := coveringIndexSet_exists_of_mem d.hU hx'
    simp only [Subtype.exists]
    use o, ocov, ⟨x, ho⟩
    apply Subtype.ext
    simp only [Scheme.homOfLE_apply]

variable {f} in
lemma 𝒲new_le_right {j : d.ι} (k : (d.𝒲new f j).J) : d.U k.val ≤ d.U j :=
  le_trans (coveringIndexSet_le k.property) inf_le_right

variable {f} in
lemma 𝒲new_le_left {j : d.ι} (k : (d.𝒲new f j).J) : d.U k.val ≤ d.U i :=
  le_trans (coveringIndexSet_le k.property) inf_le_left

@[reassoc]
lemma 𝒲_new_pullback_fst_ι (j : d.ι) (k l : (d.𝒲new f j).J) :
    pullback.fst ((d.𝒲new f j).map k) ((d.𝒲new f j).map l) ≫ (d.auxg f⁻¹ᵁ d.U k.val).ι =
      pullback.snd ((d.𝒲new f j).map k) ((d.𝒲new f j).map l) ≫ (d.auxg f⁻¹ᵁ d.U l.val).ι := by
  dsimp only [𝒲new_map]
  have h (a : (d.𝒲new f j).J) : d.U a.val ≤ d.U j :=
    le_trans (coveringIndexSet_le a.property) inf_le_right
  rw [← T.homOfLE_ι ((d.auxg f).preimage_le_preimage_of_le (h k))]
  rw [← T.homOfLE_ι ((d.auxg f).preimage_le_preimage_of_le (h l))]
  rw [pullback.condition_assoc]

@[simps!]
private def 𝒲'new (j : d.ι) (k l : (d.𝒲new f j).J) :
    (pullback ((d.𝒲new f j).map k) ((d.𝒲new f j).map l)).OpenCover :=
  let ι := coveringIndexSet d.hU (d.U k.val ⊓ d.U l.val)
  have hlek (s : ι) : d.U s.val ≤ d.U k.val :=
    le_trans (coveringIndexSet_le s.property) inf_le_left
  have hlel (s : ι) : d.U s.val ≤ d.U l.val :=
    le_trans (coveringIndexSet_le s.property) inf_le_right
  let diag (s : ι) : (d.auxg f ⁻¹ᵁ d.U s.val).toScheme ⟶
      pullback ((d.𝒲new f j).map k) ((d.𝒲new f j).map l) :=
    pullback.lift (T.homOfLE <| (d.auxg f).preimage_le_preimage_of_le (hlek s))
      (T.homOfLE <| (d.auxg f).preimage_le_preimage_of_le (hlel s)) (by simp [𝒲new_map])
  haveI : IsOpenImmersion ((pullback.fst ((d.𝒲new f j).map k) ((d.𝒲new f j).map l))) :=
    IsOpenImmersion.pullback_fst_of_right _ _
  haveI (s : ι) : IsOpenImmersion (diag s) := by
    dsimp [diag]
    apply @IsOpenImmersion.of_comp _ _ _ _ (pullback.fst _ _) ?_ ?_
    · apply IsOpenImmersion.pullback_fst_of_right
    · simp only [𝒲new_map, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]
      infer_instance
  Scheme.OpenCover.mkOfCovers
    (coveringIndexSet d.hU (d.U k.val ⊓ d.U l.val))
    (fun s ↦ d.auxg f ⁻¹ᵁ (d.U s))
    (fun s ↦ diag s)
    (fun x ↦ by
      dsimp at x ⊢
      set Wk := (d.auxg f) ⁻¹ᵁ (d.U k.val)
      let x1 : Wk := (pullback.fst ((d.𝒲new f j).map k) ((d.𝒲new f j).map l)).base x
      set Wl := (d.auxg f) ⁻¹ᵁ (d.U l.val)
      let x2 : Wl := (pullback.snd ((d.𝒲new f j).map k) ((d.𝒲new f j).map l)).base x
      have hx1 : (d.auxg f).base x1 ∈ d.U k.val := x1.property
      have hx2 : (d.auxg f).base x2 ∈ d.U l.val := x2.property
      have heq : (d.auxg f).base (Wk.ι.base x1) = (d.auxg f).base x2 := by
        simp only [x1]
        rw [← Scheme.comp_base_apply]
        erw [← Scheme.comp_base_apply]
        rw [𝒲_new_pullback_fst_ι_assoc]
        rfl
      have hx1' : (d.auxg f).base (Wk.ι.base x1) ∈ d.U k.val ⊓ d.U l.val := by
        refine ⟨hx1, ?_⟩
        rw [heq]
        exact hx2
      obtain ⟨o, hocov, ho⟩ := coveringIndexSet_exists_of_mem d.hU hx1'
      use ⟨o, hocov⟩
      use ⟨x1.val, ho⟩
      have hinj : Function.Injective (pullback.fst ((d.𝒲new f j).map k)
          ((d.𝒲new f j).map l)).base := (Scheme.Hom.isOpenEmbedding _).inj
      apply hinj
      erw [← Scheme.comp_base_apply]
      simp only [diag, 𝒲new_map, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]
      apply Subtype.ext
      erw [Scheme.homOfLE_apply]
      rfl
    )

variable {f} in
lemma 𝒲'new_le {j : d.ι} {k l : (d.𝒲new f j).J} (a : (d.𝒲'new f j k l).J) :
    d.U a.val ≤ d.U i :=
  le_trans (le_trans (coveringIndexSet_le a.property) inf_le_left) (d.𝒲new_le_left k)

variable {f} in
lemma 𝒲'new_le_left {j : d.ι} {k l : (d.𝒲new f j).J} (a : (d.𝒲'new f j k l).J) :
    d.U a.val ≤ d.U k.val :=
  le_trans (coveringIndexSet_le a.property) inf_le_left

variable {f} in
lemma 𝒲'new_le_right {j : d.ι} {k l : (d.𝒲new f j).J} (a : (d.𝒲'new f j k l).J) :
    d.U a.val ≤ d.U l.val :=
  le_trans (coveringIndexSet_le a.property) inf_le_right

private def auxhGeneralnew (j : d.ι) : (d.auxg f ⁻¹ᵁ d.U j).toScheme ⟶ d.X j :=
  let 𝒲 := d.𝒲new f j
  𝒲.glueMorphisms (fun x ↦ d.auxhOfLE f (d.𝒲new_le_left x) ≫ d.ρ (d.𝒲new_le_right x)) <| by
    intro k l
    set 𝒲' := d.𝒲'new f j k l
    apply 𝒲'.hom_ext
    intro a
    have h1 : 𝒲'.map a ≫ pullback.fst (𝒲.map k) (𝒲.map l) ≫ d.auxhOfLE f (d.𝒲new_le_left k) =
        d.auxhOfLE f (d.𝒲'new_le a) ≫ d.ρ (d.𝒲'new_le_left a) := by
      simp [𝒲', 𝒲, d.auxhOfLE_trans f _ (d.𝒲'new_le_left a)]
    have h2 : 𝒲'.map a ≫ pullback.snd (𝒲.map k) (𝒲.map l) ≫ d.auxhOfLE f (d.𝒲new_le_left l) =
        d.auxhOfLE f (d.𝒲'new_le a) ≫ d.ρ (d.𝒲'new_le_right a) := by
      simp [𝒲', 𝒲, d.auxhOfLE_trans f _ (d.𝒲'new_le_right a)]
    rw [reassoc_of% h1, reassoc_of% h2, d.comp, d.comp]

@[reassoc (attr := simp)]
lemma 𝒲new_map_auxhGeneralnew {j : d.ι} (k : (d.𝒲new f j).J) :
    (d.𝒲new f j).map k ≫ d.auxhGeneralnew f j =
      d.auxhOfLE f (d.𝒲new_le_left k) ≫ d.ρ (d.𝒲new_le_right k) := by
  simp only [auxhGeneralnew, Scheme.OpenCover.ι_glueMorphisms]

private def 𝒲newJmkOfLE {j k : d.ι} (hkj : d.U k ≤ d.U j) (hki : d.U k ≤ d.U i) : (d.𝒲new f j).J :=
  ⟨k, by simp [hkj, hki]⟩

/-- -/
@[reassoc]
lemma 𝒲new_map_auxhGeneralnew' {j : d.ι} {k : d.ι} (hkj : d.U k ≤ d.U j) (hki : d.U k ≤ d.U i) :
    (d.𝒲new f j).map (d.𝒲newJmkOfLE f hkj hki) ≫ d.auxhGeneralnew f j =
      d.auxhOfLE f (d.𝒲new_le_left (d.𝒲newJmkOfLE f hkj hki)) ≫
        d.ρ (d.𝒲new_le_right (d.𝒲newJmkOfLE f hkj hki)) := by
  simp only [auxhGeneralnew, Scheme.OpenCover.ι_glueMorphisms]

@[reassoc (attr := simp)]
lemma homOfLE_auxhGeneralnew {j : d.ι} {k : d.ι} (hkj : d.U k ≤ d.U j) (hki : d.U k ≤ d.U i) :
    T.homOfLE ((d.auxg f).preimage_le_preimage_of_le hkj) ≫ d.auxhGeneralnew f j =
      d.auxhOfLE f hki ≫ d.ρ hkj :=
  d.𝒲new_map_auxhGeneralnew' f hkj hki

/-- Given a morphism `f : T ⟶ Xᵢ`, this is the induced
compatible family on `T` over `d`. -/
@[simps h, simps (config := .lemmasOnly) g]
def subfamily : d.CompatibleFamily T where
  g := f ≫ d.f i ≫ (d.U i).ι
  h j := d.auxhGeneralnew f j
  hcompf j := by
    rw [← cancel_mono (d.U j).ι]
    simp only [morphismRestrict_ι, Category.assoc]
    apply (d.𝒲new f j).hom_ext
    intro k
    simp only [𝒲new_map_auxhGeneralnew_assoc, d.w_assoc]
    simp [auxhOfLE_f_assoc, 𝒲new_map, auxg]
  hcompρ j k hjk := by
    dsimp
    apply (d.𝒲new f j).hom_ext
    intro a
    have ha : d.U a.val ≤ d.U j := (d.𝒲new_le_right a)
    simp only [𝒲new_map, Scheme.homOfLE_homOfLE_assoc]
    rw [d.homOfLE_auxhGeneralnew f (ha.trans hjk) (d.𝒲new_le_left a)]
    rw [d.homOfLE_auxhGeneralnew_assoc f ha (d.𝒲new_le_left a), d.comp]

end OpenSubfunctor

@[reassoc (attr := simp)]
lemma _root_.AlgebraicGeometry.Scheme.homOfLE_isoOfEq_hom
    {X : Scheme.{u}} {U V V' : X.Opens} (hUV : U ≤ V) (hVV' : V = V') :
    X.homOfLE hUV ≫ (X.isoOfEq hVV').hom = X.homOfLE (hVV' ▸ hUV) := by
  rw [← cancel_mono V'.ι]
  simp

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.isoOfEq_isoOfEq {X : Scheme.{u}}
    {U V W : X.Opens} (hUV : U = V) (hVW : V = W) :
    X.isoOfEq hUV ≪≫ X.isoOfEq hVW = X.isoOfEq (hUV.trans hVW) := by
  ext : 1
  rw [← cancel_mono W.ι]
  simp

@[simp]
lemma auxhGeneralnew_apply {i : d.ι} {T : Scheme.{u}} (f : T ⟶ d.X i) :
    d.auxhGeneralnew f i = (d.auxg f ⁻¹ᵁ d.U i).ι ≫ f := by
  apply (d.𝒲new _ i).hom_ext
  intro a
  simp only [𝒲new_map_auxhGeneralnew, auxhOfLE_ρ, subfamily_g]
  simp only [𝒲new_map, ← Category.assoc]
  simp

/-- -/
lemma subfamily_h' {i : d.ι} {T : Scheme.{u}} (f : T ⟶ d.X i) :
    (d.subfamily f).h i = (T.isoOfEq (by simp [subfamily_g])).hom ≫ T.topIso.hom ≫ f := by
  simp only [subfamily_h, auxhGeneralnew_apply, Scheme.topIso_hom, Scheme.isoOfEq_hom_ι_assoc]
  rfl

lemma subfamily_apply_h {i : d.ι} {T : Scheme.{u}} (C : d.CompatibleFamily T) :
    d.subfamily (C.h i) = d.compatibleFamilyMap (C.g ⁻¹ᵁ d.U i).ι C := by
  rw [CompatibleFamily.eq_iff]
  have h : C.h i ≫ d.f i ≫ (d.U i).ι = (C.g ⁻¹ᵁ d.U i).ι ≫ C.g := by
    simp [reassoc_of% C.hcompf]
  use h
  intro j
  simp only [subfamily_g, Scheme.comp_coeBase, TopologicalSpace.Opens.map_comp_obj, subfamily_h,
    compatibleFamilyMap_g, compatibleFamilyMap_h]
  apply (d.𝒲new _ j).hom_ext
  intro a
  rw [𝒲new_map_auxhGeneralnew, 𝒲new_map, Scheme.homOfLE_isoOfEq_hom_assoc]
  have hle : d.auxg (C.h i) ⁻¹ᵁ d.U a.val ≤ (C.g ⁻¹ᵁ d.U i).ι ⁻¹ᵁ C.g ⁻¹ᵁ d.U a.val := by
    simp only [auxg, h]
    rfl
  rw [← Scheme.homOfLE_homOfLE_assoc _ hle]
  rw [← morphismRestrict_naturality_assoc (C.g ⁻¹ᵁ d.U i).ι (C.g ⁻¹ᵁ d.U a.val) (C.g ⁻¹ᵁ d.U j)
    (C.g.preimage_le_preimage_of_le <| d.𝒲new_le_right a) (C.h j)]
  rw [← C.hcompρ _ _ (d.𝒲new_le_right a), ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono (d.ρ (d.𝒲new_le_left a)), auxhOfLE_ρ, Category.assoc, C.hcompρ,
    ← Category.assoc]
  congr 1
  simp only [Category.assoc, morphismRestrict_naturality, Scheme.homOfLE_homOfLE_assoc]
  rw [← cancel_mono (C.g ⁻¹ᵁ d.U i).ι]
  simp

@[simp]
lemma subfamily_comp {i : d.ι} {T Y : Scheme.{u}} (f : Y ⟶ T) (h : T ⟶ d.X i) :
    d.subfamily (f ≫ h) = d.compatibleFamilyMap f (d.subfamily h) := by
  rw [CompatibleFamily.eq_iff]
  simp only [subfamily_g, subfamily_h,
    compatibleFamilyMap_g, Scheme.isoOfEq_rfl, Iso.refl_hom, compatibleFamilyMap_h,
    Category.id_comp, Category.assoc, exists_const]
  intro j
  apply (d.𝒲new (f ≫ h) j).hom_ext
  intro k
  simp only [𝒲new_map]
  rw [← morphismRestrict_naturality_assoc f _ _
    ((h ≫ d.f i ≫ (d.U i).ι).preimage_le_preimage_of_le (d.𝒲new_le_right k))]
  rw [d.homOfLE_auxhGeneralnew _ (d.𝒲new_le_right k) (d.𝒲new_le_left k)]
  rw [d.homOfLE_auxhGeneralnew _ (d.𝒲new_le_right k) (d.𝒲new_le_left k)]
  rw [auxhOfLE_comp, Category.assoc]
  rfl

lemma subfamily_injective (i : d.ι) (T : Scheme.{u}) :
    Function.Injective (d.subfamily (i := i) (T := T)) := by
  intro a b hab
  rw [CompatibleFamily.eq_iff] at hab
  obtain ⟨hg, hh⟩ := hab
  replace hh := hh i
  rw [subfamily_h', subfamily_h'] at hh
  conv_rhs at hh => rw [← Category.assoc, ← Iso.trans_hom, Scheme.isoOfEq_isoOfEq]
  rwa [cancel_epi, cancel_epi] at hh

/-- `Hom(-, Xᵢ)` is a sub(pre)sheaf of `d.presheaf`. -/
@[simps]
def subsheaf (i : d.ι) : yoneda.obj (d.X i) ⟶ d.presheaf where
  app _ f := d.subfamily f
  naturality T Y f := by
    ext : 1
    simp

instance : IsOpenImmersion.RespectsIso :=
  haveI : MorphismProperty.RespectsIso @IsOpenImmersion :=
    AlgebraicGeometry.isOpenImmersion_respectsIso
  this

lemma _root_.CategoryTheory.IsPullback.of_evaluation_isPullback {C D : Type*} [Category C]
    [Category D] {P X Y Z : C ⥤ D}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : ∀ A, IsPullback (fst.app A) (snd.app A) (f.app A) (g.app A)) :
    IsPullback fst snd f g where
  w := by
    ext A
    exact (h A).w
  isLimit' := by
    refine ⟨evaluationJointlyReflectsLimits _ (fun A ↦ ?_)⟩
    exact (IsLimit.equivOfNatIsoOfIso _ _ _ (PullbackCone.isoMk _)).invFun (h A).isLimit'.some

lemma _root_.CategoryTheory.Limits.Types.isPullback_of {P X Y Z : Type u}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hc : ∀ p, f (fst p) = g (snd p))
    (hp : ∀ x y, f x = g y → ∃! p, fst p = x ∧ snd p = y) :
    IsPullback fst snd f g where
  w := by
    ext p
    simp [hc]
  isLimit' := by
    rw [Types.isLimit_iff]
    intro s hs
    have hl := hs (WalkingCospan.Hom.inl)
    simp only [cospan_one, cospan_map_inl] at hl
    have hr := hs (WalkingCospan.Hom.inr)
    simp only [cospan_one, cospan_map_inr] at hr
    obtain ⟨p, ⟨hpl, hpr⟩, hu⟩ := hp (s .left) (s .right) (by rw [hl, hr])
    use p
    refine ⟨fun j ↦ ?_, fun y hy ↦ hu y ⟨hy .left, hy .right⟩⟩
    obtain _ | (_ | _) := j <;> simp [hpl, hpr, hl]

lemma subsheaf_isOpenImmersion (i : d.ι) : IsOpenImmersion.presheaf (d.subsheaf i) := by
  apply MorphismProperty.relative.of_exists
  intro Y g
  let C : d.CompatibleFamily Y := g.app _ (𝟙 Y)
  have hg {T : Scheme.{u}} (p : T ⟶ Y) : g.app _ p = d.presheaf.map p.op C := by
    simp only [C, ← FunctorToTypes.naturality, yoneda_obj_map, Quiver.Hom.unop_op, Category.comp_id]
  refine ⟨C.g ⁻¹ᵁ d.U i, yoneda.map (C.h i), (C.g ⁻¹ᵁ d.U i).ι, ?_, inferInstance⟩
  apply IsPullback.of_evaluation_isPullback
  intro ⟨T⟩
  apply Types.isPullback_of
  · intro p
    simp [hg, subfamily_apply_h]
  · intro (a : T ⟶ d.X i) (b : T ⟶ Y) hab
    dsimp at hab ⊢
    rw [hg] at hab
    simp at hab
    have hb : Set.range b.base ⊆ C.g ⁻¹ᵁ d.U i := by
      apply_fun CompatibleFamily.g at hab
      simp [subfamily_g] at hab
      rintro - ⟨t, rfl⟩
      simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe]
      rw [← Scheme.comp_base_apply, ← hab]
      simp only [Scheme.comp_coeBase, TopCat.coe_comp, Function.comp_apply]
      apply Subtype.property
    let p : T ⟶ C.g ⁻¹ᵁ d.U i := (C.g ⁻¹ᵁ d.U i).lift b hb
    use p
    simp [p]
    constructor
    · apply subfamily_injective
      simp [subfamily_apply_h]
      rw [← compatibleFamilyMap_comp]
      simp only [Scheme.Opens.lift_fac, p]
      exact hab.symm
    · rintro q - hqb
      rw [← cancel_mono (C.g ⁻¹ᵁ d.U i).ι]
      simpa

open Opposite

instance : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc d.subsheaf) where
  imageSieve_mem {T} (C : d.CompatibleFamily T) := by
    rw [Pretopology.mem_toGrothendieck]
    refine ⟨Presieve.ofArrows _ (fun i ↦ (C.g ⁻¹ᵁ d.U i).ι), ⟨C.openCover, rfl⟩, ?_⟩
    rintro - - ⟨i⟩
    use (Sigma.ι (fun b ↦ yoneda.obj (d.X b)) i).app (op (C.g ⁻¹ᵁ d.U i)) (C.h i)
    show ((Sigma.ι (fun b ↦ yoneda.obj (d.X b)) i).app (op ↑(C.g ⁻¹ᵁ d.U i)) ≫
      (Sigma.desc d.subsheaf).app (op ↑(C.g ⁻¹ᵁ d.U i))) ((C.h i)) = _
    rw [← NatTrans.comp_app]
    simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, subsheaf_app, subfamily_apply_h]
    rfl

@[stacks 01LH]
instance sheaf_representable : d.presheaf.IsRepresentable := by
  haveI inst : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc d.subsheaf) :=
    inferInstance
  exact @Scheme.representability
    d.sheaf _ _ d.subsheaf d.subsheaf_isOpenImmersion inst

/-- A gluing with respect to the relative gluing datum `d` is a scheme `X`
with morphism `f : X ⟶ S` and compatible isomorphisms `f⁻¹(Uᵢ) ⟶ Xᵢ`. -/
structure Glued where
  /-- The glued scheme. -/
  X : Scheme.{u}
  /-- The structure morphism. -/
  f : X ⟶ S
  /-- The isomorphism `f⁻¹(Uᵢ) ⟶ Xᵢ` -/
  iso (i : d.ι) : (f ⁻¹ᵁ d.U i).toScheme ≅ d.X i
  isow (i : d.ι) : (iso i).hom ≫ d.f i = f ∣_ d.U i
  iso_inv_homOfLE_iso_hom_eq {i j : d.ι} (hij : d.U i ≤ d.U j) :
    (iso i).inv ≫ X.homOfLE (f.preimage_le_preimage_of_le hij) ≫
      (iso j).hom = d.ρ hij

attribute [reassoc (attr := simp)] Glued.isow

variable {d} in
@[reassoc]
lemma Glued.homOfLE_iso_hom (G : d.Glued) {i j : d.ι} (hij : d.U i ≤ d.U j) :
    G.X.homOfLE (G.f.preimage_le_preimage_of_le hij) ≫ (G.iso j).hom =
      (G.iso i).hom ≫ d.ρ hij := by
  rw [← G.iso_inv_homOfLE_iso_hom_eq hij]
  simp

variable {d} in
@[reassoc]
lemma Glued.ι_f (G : d.Glued) (i : d.ι) :
    (G.f ⁻¹ᵁ d.U i).ι ≫ G.f = (G.iso i).hom ≫ d.f i ≫ (d.U i).ι := by
  simp

@[reassoc]
lemma _root_.AlgebraicGeometry.Scheme.isoOfEq_morphismRestrict {X Y : Scheme.{u}}
    (f : X ⟶ Y) (U U' : Y.Opens) (hUU' : U = U') :
    (X.isoOfEq (by rw [hUU'])).hom ≫ f ∣_ U' = f ∣_ U ≫ (Y.isoOfEq hUU').hom := by
  rw [← cancel_mono U'.ι]
  simp

lemma _root_.AlgebraicGeometry.Scheme.Hom.range_subset_iff_preimage_eq_top {X Y : Scheme.{u}}
    (f : X.Hom Y) {U : Y.Opens} :
    Set.range f.base ⊆ U ↔ f ⁻¹ᵁ U = ⊤ := by
  simp [Opens.ext_iff]

@[reassoc]
lemma _root_.AlgebraicGeometry.Scheme.morphismRestrict_eq_lift {X Y : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.Opens) (hf : Set.range f.base ⊆ U) :
    X.topIso.inv ≫ (X.isoOfEq (f.range_subset_iff_preimage_eq_top.mp hf).symm).hom ≫
      f ∣_ U = U.lift f hf := by
  rw [← cancel_mono U.ι]
  simp

/-- Any representative of `d.presheaf` is a gluing for the relative gluing datum `d`. -/
def mkGluedFromRepresentable (X : Scheme.{u}) (R : d.presheaf.RepresentableBy X) : d.Glued where
  X := X
  f := (R.homEquiv (𝟙 X)).g
  iso i := by
    let g : X ⟶ S := (R.homEquiv (𝟙 X)).g
    let C₀ : d.CompatibleFamily X := R.homEquiv (𝟙 X)
    let v : (g ⁻¹ᵁ d.U i).toScheme ⟶ d.X i := C₀.h i
    let C : d.CompatibleFamily (d.X i) := (d.subsheaf i).app (op <| d.X i) (𝟙 _)
    let C' : d.CompatibleFamily (g ⁻¹ᵁ d.U i) := (d.subsheaf i).app (op _) v
    let u' : d.X i ⟶ X := R.homEquiv.symm C
    have hRC' : R.homEquiv.symm C' = (g ⁻¹ᵁ d.U i).ι := by
      apply R.homEquiv.injective
      simp only [Equiv.apply_symm_apply]
      rw [R.homEquiv_eq]
      simp only [subsheaf_app, presheaf_map, Quiver.Hom.unop_op, C', v, C₀]
      rw [d.subfamily_apply_h]
    have hC₀C : d.presheaf.map u'.op C₀ = C := by
      simp only [C₀]
      rw [← R.homEquiv_comp]
      simp [u']
    rw [CompatibleFamily.eq_iff] at hC₀C
    have hg := hC₀C.choose
    have hi := hC₀C.choose_spec i
    simp only [presheaf_map, Quiver.Hom.unop_op, compatibleFamilyMap_g, subsheaf_app, subfamily_g,
      Category.id_comp, C] at hg
    have hu' : Set.range u'.base ⊆ g ⁻¹ᵁ d.U i := by
      simp only [Opens.map_coe]
      rintro - ⟨x, rfl⟩
      rw [Set.mem_preimage, SetLike.mem_coe, ← Scheme.comp_base_apply, hg]
      simp only [Scheme.comp_coeBase, TopCat.coe_comp, Function.comp_apply]
      apply Subtype.property
    let u : d.X i ⟶ g ⁻¹ᵁ d.U i := (g ⁻¹ᵁ d.U i).lift u' hu'
    simp at hi
    have hpreimu' : u' ⁻¹ᵁ C₀.g ⁻¹ᵁ d.U i = ⊤ := by
      rw [← u'.range_subset_iff_preimage_eq_top]
      exact hu'
    have huv : u ≫ v = 𝟙 (d.X i) := by
      simp [u, v]
      rw [← cancel_epi ((d.X i).isoOfEq hpreimu'.symm).hom] at hi
      rw [← cancel_epi (d.X i).topIso.inv] at hi
      rw [Scheme.morphismRestrict_eq_lift_assoc _ _ hu'] at hi
      rw [hi]
      simp only [Scheme.isoOfEq_hom_isoOfEq_hom_assoc]
      simp only [C]
      simp only [subsheaf_app, subfamily_h, auxhGeneralnew_apply, Category.comp_id]
      have foo : ⊤ = C.g ⁻¹ᵁ d.U i :=
        (Eq.trans (Eq.symm hpreimu')
            (Eq.mpr (id (congrArg (fun _a ↦ _a ⁻¹ᵁ d.U i = C.g ⁻¹ᵁ d.U i) hg))
              (Eq.refl (C.g ⁻¹ᵁ d.U i))))
      have foo' : ⊤ = d.auxg (𝟙 (d.X i)) ⁻¹ᵁ d.U i := foo
      rw [(d.X i).isoOfEq_hom_ι foo']
      simp
    have hvu : v ≫ u = 𝟙 (g ⁻¹ᵁ d.U i).toScheme := by
      rw [← cancel_mono (g ⁻¹ᵁ d.U i).ι]
      simp only [Category.assoc, Scheme.Opens.lift_fac, Category.id_comp, v, u]
      apply R.homEquiv.injective
      rw [R.homEquiv_comp]
      simp only [Equiv.apply_symm_apply, Quiver.Hom.unop_op, u']
      rw [← hRC']
      simp only [Quiver.Hom.unop_op, Equiv.apply_symm_apply, C, C']
      rw [← FunctorToTypes.naturality]
      rfl
    exact ⟨v, u, hvu, huv⟩
  isow i := by
    rw [(R.homEquiv (𝟙 X)).hcompf]
  iso_inv_homOfLE_iso_hom_eq {i j} hij := by
    rw [Iso.inv_comp_eq, (R.homEquiv (𝟙 X)).hcompρ]

/-- Any relative gluing datum admits a gluing. -/
lemma exists_glued : Nonempty d.Glued := by
  obtain ⟨X, ⟨a⟩⟩ := Functor.IsRepresentable.has_representation (F := d.presheaf)
  constructor
  exact d.mkGluedFromRepresentable X a

end RelativeGluingData

end AlgebraicGeometry
