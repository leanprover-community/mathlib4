/-
Copyright (c) 2026 John Rozmarynowycz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Rozmarynowycz
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.CategoryTheory.Subfunctor.SubmonoidFunctor
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.Algebraize

/-!
## Functors of Localized Rings

Given a functor `R : C ⥤ CommRingCat` and a functor of `R`-submonoids `S`,
we define the functor `C ⥤ CommRingCat` that assigns `U ↦ S(U)⁻¹R(U)` and
`i : U ⟶ V` to a ring morphism `S(U)⁻¹R(U) ⟶ S(V)⁻¹R(V)`.

We show that this functor satisfies the following universal property: given
`R' : C ⥤ CommRingCat` and `p : R ⟶ R'` such that `p.app U` maps `S(U)`
into `(R'(U))ˣ`, the induced map `R(U) × S(U) ⟶ R'(U)` via `p.app U`
is surjective and for all `x,y : R(U)`,`p.app U x = p.app U y` implies
there exists some element `c : S(U)` such that
`c * x = c * y`, then for all `R'' : C ⥤ CommRingCat` admitting a morphism
`q : R ⟶ R''`, `q` factors through `R' ⟶ R''` uniquely.

-/

@[expose] public section

universe v₁ u₁ u

open CategoryTheory CommRingCat

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {R : C ⥤ CommRingCat.{u}}
  (S : SubmonoidFunctor (R ⋙ (forget₂ CommRingCat.{u} CommMonCat.{u}) ⋙
  (forget₂ CommMonCat.{u} MonCat.{u})))

/-- The associated submonoid `S(U)` of `R(U)` recovered after the forgetful functor -/
abbrev SubmonoidFunctor.ringObj (U : C) : Submonoid (R.obj U) := S.obj U

/-- The functor of submonoids mapping property recovered after the forgetful functor -/
lemma SubmonoidFunctor.map_mem_ringObj {X Y : C} (i : X ⟶ Y) (s : ringObj S X) :
    R.map i s ∈ ringObj S Y := S.map i s.2

variable (R) in
/-- Given `R : C ⥤ CommRingCat` and a functor of submonoids `S`, there
is a functor that takes `U ↦ S(U)⁻¹R(U)` such that if `i : U ⟶ V` then
there is a morphism`S(U)⁻¹(R)(U) →+* S(v)⁻¹R(V)`. -/
@[simps obj map]
noncomputable abbrev LocalizationFunctor : C ⥤ CommRingCat where
  obj _ := of (Localization (S.ringObj _))
  map {U V} i:= ofHom (IsLocalization.map (Localization
    (S.ringObj V)) (R.map i).hom (S.map i))
  map_comp i j := by
    ext x
    simpa [Functor.map_comp, hom_comp, RingHom.coe_comp] using
      Eq.symm (IsLocalization.map_map (S.map i) (S.map j) x)

instance {U : C} : IsLocalization (S.ringObj U) ((LocalizationFunctor R S).obj U) := inferInstance

/-- `S.IsLocalization p` implies `p : R ⟶ R'` is the localization map and `R'` is the localized
functor `LocalizationFunctor R S` up to isomorphism. -/
@[mk_iff] class SubmonoidFunctor.IsLocalization {R' : C ⥤ CommRingCat} (p : R ⟶ R') : Prop where
  toIsLocalizationMap (U : C) : (S.ringObj U).IsLocalizationMap (p.app U)

instance {U : C} {R' : C ⥤ CommRingCat} (p : R ⟶ R') [S.IsLocalization p] :
    letI := (p.app U).hom.toAlgebra;  IsLocalization (S.ringObj U) (R'.obj U) := by
  apply letI := (p.app U).hom.toAlgebra; IsLocalization'.mk
  apply SubmonoidFunctor.IsLocalization.toIsLocalizationMap

namespace LocalizationFunctor

lemma IsLocalization.eq_iff_exists {R' : C ⥤ CommRingCat} (p : R ⟶ R') [S.IsLocalization p]
    {U : C} {x₁ x₂ : R.obj U} :
      (p.app U).hom x₁ = (p.app U).hom x₂ ↔ ∃ c : S.ringObj U, c * x₁ = c * x₂ :=
Submonoid.LocalizationMap.eq_iff_exists (Submonoid.LocalizationMap.mk (p.app U).hom.toMulHom
  (SubmonoidFunctor.IsLocalization.toIsLocalizationMap U))

/-- The canonical map from `R` to its localization. -/
noncomputable abbrev ι : R ⟶ LocalizationFunctor R S where
  app U := ofHom (algebraMap (R.obj U) ((LocalizationFunctor R S).obj U))
  naturality := by cat_disch

lemma ι_apply (U : C) (r : R.obj U) : ((ι S).app U).hom r = Localization.mk r 1 := by rfl

instance : S.IsLocalization (ι S) where
  toIsLocalizationMap _ := (_root_.IsLocalization'.toIsLocalizationMap)

lemma mk_eq_quotmk {R : Type*} [CommRing R] {S : Submonoid R} (r : R) (s : S) :
    (Quot.mk ⇑(OreLocalization.oreEqv S R) (r, s)) = IsLocalization.mk' (Localization S)  r s := by
  have : Quot.mk ⇑(OreLocalization.oreEqv S R) (r, s) = LocalizedModule.mk r s := by rfl
  rw [this, IsLocalizedModule.mk_eq_mk', IsLocalization.mk'_eq_mk']
  rfl

lemma mk_eq_mk {R : Type*} [CommRing R] {S : Submonoid R} (r : R) (s : S) : Localization.mk r s =
    IsLocalization.mk' (Localization S) r s := by rw [← mk_eq_quotmk]; rfl

/-- If `p` is a morphism `R ⟶ R'` such that for all `U : C` and all `x : S.ringObj U` is a unit
in `R'` under `p`, then there is a morphism  `S.LocalizationFunctor R ⟶ R'`. -/
noncomputable def lift' {R' : C ⥤ CommRingCat} (p : R ⟶ R')
    (h : ∀ (U : C) (x : S.ringObj U), IsUnit ((p.app U).hom x)) :
      LocalizationFunctor R S ⟶ R' where
  app U := ofHom (@IsLocalization.lift (R.obj U) _
    (S.ringObj U) ((LocalizationFunctor R S).obj U) _ _ (R'.obj U) _ _ _ (h U))
  naturality {U V} i := by
    ext1
    ext m
    obtain ⟨r,s⟩ := m
    simp only [hom_comp, ConcreteCategory.hom_ofHom, Function.comp_apply]
    rw [mk_eq_quotmk, IsLocalization.map_mk', IsLocalization.lift_mk']
    exact
      (Submonoid.LocalizationMap.mul_inv_left (h V)
        ⟨((R.map i).hom) ↑s, S.map_mem_ringObj i s⟩
          ((p.app V).hom ((R.map i).hom r))
            ((R'.map i).hom
              ((IsLocalization.lift (h U))
                (IsLocalization.mk' (↑((LocalizationFunctor R S).obj U)) r s)))).mpr
        (by
      simp only [NatTrans.naturality_apply, IsLocalization.lift_mk', RingHom.toMonoidHom_eq_coe,
        MonoidHom.coe_coe, map_mul]
      rw [← mul_assoc, mul_comm, ← mul_assoc]
      have : ((R'.map i).hom) (1 /ₚ (@DFunLike.coe (↥(S.ringObj U) →*
        (↑(R'.obj U))ˣ) (↥(S.ringObj U)) (fun x ↦ (↑(R'.obj U))ˣ) MonoidHom.instFunLike
          (IsUnit.liftRight ((p.app U).hom.toMonoidHom.restrict (S.ringObj U))
            (Eq.ndrec (motive := fun f ↦ ∀ (x : ↥(S.ringObj U)), IsUnit (f x)) (h U) (id (Eq.refl
              ((p.app U).hom.toMonoidHom.restrict (S.ringObj U)))))) s)) *
                ((R'.map i).hom ((p.app U).hom ↑s)) = 1 := by
        simpa [IsUnit.liftRight_apply] using map_mul_eq_one (R'.map i).hom
          (by simp_all only [IsUnit.val_inv_mul])
      simp_all only [RingHom.toMonoidHom_eq_coe, one_divp, one_mul])

@[simp]
lemma lift'_comp {R' : C ⥤ CommRingCat} (p : R ⟶ R')
    (h : ∀ (U : C) (x : S.ringObj U), IsUnit ((p.app U).hom x)) : ι S ≫ lift' S p h  = p := by
  ext U x
  dsimp only [lift', ι]
  simp

section

variable {R' : C ⥤ CommRingCat} (p : R ⟶ R') [S.IsLocalization p]


/-- The canonical isomorphism from the localization functor to any pair `(R', p : R ⟶ R')`
satisfying the universal property. -/
noncomputable def fromLocalization :
    LocalizationFunctor R S ⟶ R' :=
  lift' S p (by intro U x; apply (SubmonoidFunctor.IsLocalization.toIsLocalizationMap U).map_units)

lemma fromLocalization.inj {U : C} :
    Function.Injective ((fromLocalization S p).app U).hom := fun x y eq1 => by
  dsimp at x y
  induction x with | _ a
  induction y with | _ a'
  dsimp only [fromLocalization, lift'] at eq1
  simp only [ConcreteCategory.hom_ofHom] at eq1
  simp_all only [mk_eq_mk]
  simp_rw [IsLocalization.lift_mk', Submonoid.LocalizationMap.mul_inv_left,
    ← mul_assoc] at eq1
  have : (p.app U).hom.toMonoidHom ↑a.2 * (p.app U).hom a'.1 =
    (p.app U).hom (a.2 * a'.1) := by rw [RingHom.map_mul]; rfl
  rw [this] at eq1
  symm at eq1
  simp_rw [Submonoid.LocalizationMap.mul_inv_left, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    ← RingHom.map_mul, IsLocalization.eq_iff_exists S] at eq1
  rw [IsLocalization.mk'_eq_iff_eq]
  simp only [dsimp% ι_apply]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  simp only [OneMemClass.coe_one, one_mul, Subtype.exists, exists_prop]
  obtain ⟨c, hc⟩ := eq1
  use c
  aesop

lemma fromLocalization.surj {U : C} : Function.Surjective ((fromLocalization S p).app U).hom :=
  fun z => let ⟨⟨m, (s : S.ringObj U)⟩, eq1⟩ :=
  (@SubmonoidFunctor.IsLocalization.toIsLocalizationMap _ _ _ _ _ p _ U).surj z
    ⟨IsLocalization.mk' ((LocalizationFunctor R S).obj U) m s, by
      dsimp only [fromLocalization, lift']
      simp only [ConcreteCategory.hom_ofHom]
      rw [IsLocalization.lift_mk', ← eq1, Submonoid.LocalizationMap.mul_inv_left, mul_comm];
      simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]⟩

lemma fromLocalization.bij {U : C} : Function.Bijective ((fromLocalization S p).app U).hom :=
  ⟨fromLocalization.inj S p, fromLocalization.surj S p⟩

instance fromLocalization_iso : IsIso (fromLocalization S p) := by
  rw [CategoryTheory.NatTrans.isIso_iff_isIso_app]
  intro X
  rw [ConcreteCategory.isIso_iff_bijective]
  apply fromLocalization.bij

/-- If `R' : C ⥤ CommRingCat` and `p : R ⟶ R'` satisfy the universal property of localization,
then `LocalizationFunctor R S` and `R'` are isomorphic. -/
noncomputable def iso : LocalizationFunctor R S ≅ R' := asIso (fromLocalization S p)

/-- The ring equivalence between `R'(U)` and `(LocalizationFunctor R S)(U)` for each `U : C`. -/
noncomputable def isoApp (U : C) : (LocalizationFunctor R S).obj U ≅ R'.obj U :=
  asIso ((fromLocalization S p).app U)

theorem iso_inv_apply_aux {U : C} (r : R'.obj U) : ((iso S p).inv.app U) r = Localization.mk
    (((@SubmonoidFunctor.IsLocalization.toIsLocalizationMap _ _ _ _ _ p _ U).surj r).choose :
      (R.obj U) × (S.ringObj U)).1
      ((@SubmonoidFunctor.IsLocalization.toIsLocalizationMap _ _ _ _ _ p _ U).surj r).choose.2 := by
  apply_fun ((iso S p).hom.app U).hom using
    RingEquiv.injective (CategoryTheory.Iso.commRingCatIsoToRingEquiv (isoApp S p U))
  rw [Iso.inv_hom_id_app_apply]
  simp only [iso, fromLocalization, asIso_hom, lift', ConcreteCategory.hom_ofHom]
  rw [mk_eq_mk, IsLocalization.lift_mk', Units.eq_mul_inv_iff_mul_eq, IsUnit.coe_liftRight,
    RingHom.toMonoidHom_eq_coe, MonoidHom.restrict_apply, MonoidHom.coe_coe,
    ((@SubmonoidFunctor.IsLocalization.toIsLocalizationMap _ _ _ _ _ p _ U).surj _).choose_spec]

end

section

variable {R' R'' : C ⥤ CommRingCat} (p : R ⟶ R') [S.IsLocalization p] (q : R ⟶ R'')

/-- If `R : C ⥤ CommRingCat` and `p : R ⟶ R'` form a localization of `R`, then for any morphism
`q : R ⟶ R''` such that `(q.app U)` maps all elements of `S(U)` to a unit, then there is a
canonical morphism `R' ⟶ R''`. -/
noncomputable def lift (h : ∀ (U : C) (x : S.ringObj U), IsUnit ((q.app U).hom x)) : R' ⟶ R'' :=
  (iso S p).inv ≫ lift' S q h

@[simp]
lemma lift_comp_iso (h : ∀ (U : C) (x : S.ringObj U), IsUnit ((q.app U).hom x)) :
    (iso S p).hom ≫ lift S p q h = lift' S q h :=
  Iso.hom_inv_id_assoc (iso S p) (lift' S q h)

/-- If The canonical lift map from `R' ⟶ R''` is unique -/
theorem lift_unique (h : ∀ (U : C) (x : S.ringObj U), IsUnit ((q.app U).hom x))
    (l : R' ⟶ R'') (hcomp : p ≫ l = q) : lift S p q h = l := by
  ext U r
  dsimp [lift, lift']
  have : ∀ (U : C) x, (p ≫ l).app U x = q.app U x := by aesop
  simp only [NatTrans.comp_app, hom_comp, Function.comp_apply] at this
  have : ∀ x, (( (iso S p).hom ≫ l).app U) ((algebraMap (↑(R.obj U))
    (Localization (S.ringObj U))) x) = (q.app U).hom x := by
    intro x
    rw [← this, NatTrans.comp_app_apply]
    congr 1
    dsimp only [iso, asIso, fromLocalization, lift']
    simp
  rw [IsLocalization.lift_unique (h U) (this), NatTrans.comp_app_apply, Iso.inv_hom_id_app_apply]

end

end LocalizationFunctor

end CategoryTheory
