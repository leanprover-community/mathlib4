/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Morphism from the spectrum of a field to a locally ringed space

In this file, we construct the following:
Given a locally ringed space `X`, a point `x : X`, a commutative ring `F`
with `hF : IsField F` and a local ring homomorphism `f : X.stalk x ⟶ F`,
`AlgebraicGeometry.LocallyRingedSpace.HomFromFieldSpec x F hF f` is the
morphism from the spectrum of `F` to `X` induced by `f`.

Details of our construction:
1. For the continuous function from the topological space of Spec(`F`) to the topological space of
   `X`, we define it as the constant map `fun _ ↦ x`.
2. `(HomFromFieldSpec x F hF f).val.c` belongs to the type
      `X.presheaf ⟶ ⟨fun _ ↦ x, continuous_const⟩ _* (Scheme.Spec.obj { unop := F }).presheaf`.
   In other words, in order to construct `(HomFromFieldSpec x F hF f).val.c`, we need to define a
   map from
                                         `X.presheaf.obj O`
   to
        `(⟨fun _ ↦ x, continuous_const⟩ _* (Scheme.Spec.obj { unop := F }).presheaf).obj O`
   for any
                                   `O : (TopologicalSpace.Opens X)ᵒᵖ`.
   We construct it by considering the cases `x ∈ O.unop` and `x ∉ O.unop` separately. It is not
   very difficult to prove the naturality of the map we have defined.
3. The most complicated part is completing `(HomFromFieldSpec x F hF f).val.c`, in which we need to
   show that for any `x1 : Scheme.Spec.obj { unop := F }`, the stalk map induced by our construction
   is a local ring homomorphism. We achieve this by observing that the the stalk map can actually be
   written as `RingHom.comp g h` for some `g` and `h`. We then show that both `g` and `h` are local,
   and use the fact that a composition of two local ring homomorphisms is local. In order to show
   that `g` is local, we prove that both the domain and the codomain of `g` are fields; it is true
   that if the domain and codomain of some ring homomorphism are both fields, then the homomorphism
   is local (see `isLocalRingHom_of_isField_of_isField`). To prove `h` is local, we show that `h` is
   essentially a composition of `f` and some isomorphism (see `stalkFunctor_map_natTrans_eq`).
-/

/--
If two rings are isomorphic and one of them is a field, then the other ring is also a field.
-/
theorem isField_of_iso {R : CommRingCat} {S : CommRingCat} (i : R ≅ S) (hS : IsField S) :
    IsField R where
  exists_pair_ne := by
    rcases hS.exists_pair_ne with ⟨x, y, hxy⟩
    exact ⟨i.symm.hom x, i.symm.hom y, fun h ↦ by
      have : i.hom (i.inv x) = i.hom (i.inv y) := congrArg i.hom h
      rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, CategoryTheory.Iso.inv_hom_id,
        CategoryTheory.id_apply] at this
      exact hxy this⟩
  mul_comm := fun x y ↦ by
    have (r : R) : r = i.inv (i.hom r) := by
      rw [← CategoryTheory.comp_apply, CategoryTheory.Iso.hom_inv_id, CategoryTheory.id_apply]
    rw [this x, this y, ← map_mul, mul_comm, map_mul]
  mul_inv_cancel := by
    intro a ha
    rcases hS.mul_inv_cancel (fun h ↦ by
      have := congr_arg i.inv h
      rw [← CategoryTheory.comp_apply, CategoryTheory.Iso.hom_inv_id, CategoryTheory.id_apply,
        map_zero] at this
      exact ha this) with ⟨b, hb⟩
    exact ⟨i.inv b, by
      let hb' := congr_arg i.inv hb
      rw [map_mul, ← CategoryTheory.comp_apply, CategoryTheory.Iso.hom_inv_id,
        CategoryTheory.id_apply, map_one] at hb'
      exact hb'⟩

/-- If the domain and codomain of a ring homomorphism are both fields, then the homomorphism is
local. -/
theorem isLocalRingHom_of_isField_of_isField
    {R : CommRingCat} {S : CommRingCat} (hR : IsField R) (hS : IsField S) (f : R ⟶ S) :
    IsLocalRingHom f := IsLocalRingHom.mk fun r hfr ↦ by
  rw [isUnit_iff_exists] at hfr ⊢
  have hfr0 : f r ≠ 0 := fun h ↦ by
    have := hS.nontrivial
    rw [h] at hfr
    simp only [zero_mul, zero_ne_one, mul_zero, and_self, exists_const] at hfr
  have hr0 : r ≠ 0 := fun h ↦ by rw [h, map_zero] at hfr0; exact hfr0 rfl
  obtain ⟨s, hs⟩ := hR.mul_inv_cancel hr0
  exact ⟨s, hs, by rw [mul_comm]; exact hs⟩

instance AlgebraicGeometry.SheafedSpace.CommRingCat.section_over_bot_unique
    {X : SheafedSpace CommRingCat} : Unique (X.presheaf.obj { unop := ⊥ }) where
  default := 0
  uniq := fun a ↦ by
    let U : Empty → TopologicalSpace.Opens X.toPresheafedSpace := fun _ ↦ ⊥
    let h := TopCat.Sheaf.eq_of_locally_eq X.sheaf U
    simp only [IsEmpty.forall_iff, true_implies] at h
    rw [congrArg X.sheaf.val.obj (congrArg Opposite.op <| show _ = ⊥ by
      simp only [iSup_eq_bot, implies_true])] at h
    exact h a 0

noncomputable instance AlgebraicGeometry.Spec.structureSheaf.section_over_bot_unique
    {R : Type _} [CommRing R] : Unique ((Spec.structureSheaf R).val.obj { unop := ⊥ }) := by
  rw [show (Spec.structureSheaf R).val.obj { unop := ⊥ } =
    (Scheme.Spec.obj ⟨R, _⟩).presheaf.obj { unop := ⊥ } by rfl]
  exact SheafedSpace.CommRingCat.section_over_bot_unique

namespace AlgebraicGeometry

namespace LocallyRingedSpace

variable {X : LocallyRingedSpace} (x : X)
variable (F : CommRingCat) (hF : IsField F)
variable (f : X.stalk x ⟶ F) [IsLocalRingHom f]

namespace HomFromFieldSpec

/-- The map of sections on `O` induced by `(HomFromFieldSpec x F hF f).val.c` for the case
`x ∈ O.unop`. -/
noncomputable def valCAppOpensOfMem (O : (TopologicalSpace.Opens X)ᵒᵖ) (hxO : x ∈ O.unop) :
    X.presheaf.obj O ⟶
    (⟨fun _ ↦ x, continuous_const⟩ _* (Scheme.Spec.obj (Opposite.op F)).presheaf).obj O :=
  let x' : O.unop := ⟨x, hxO⟩
  let hom1 := @TopCat.Presheaf.germ CommRingCat _ _ X.toTopCat X.presheaf O.unop x'
  let hom2 := RingHom.comp (StructureSheaf.toOpen F ⊤) f
  CategoryTheory.CategoryStruct.comp hom1 (CategoryTheory.CategoryStruct.comp hom2
    ((Scheme.Spec.obj (Opposite.op F)).presheaf.map (TopologicalSpace.Opens.leTop _).op))

/-- The map of sections on `O` induced by `(HomFromFieldSpec x F hF f).val.c` for the case
`x ∉ O.unop`. -/
noncomputable def valCAppOpensOfNotMem (O : (TopologicalSpace.Opens X)ᵒᵖ) (hxO : x ∉ O.unop) :
    X.presheaf.obj O ⟶
    (⟨fun _ ↦ x, continuous_const⟩ _* (Scheme.Spec.obj (Opposite.op F)).presheaf).obj O where
  toFun := fun _ ↦ 0
  map_one' := by
    rw [TopCat.Presheaf.pushforwardObj_obj, CategoryTheory.Functor.op_obj,
      (le_bot_iff.mp fun _ ↦ hxO : (@TopologicalSpace.Opens.map (Scheme.Spec.obj (Opposite.op F))
      X.toTopCat ⟨fun _ ↦ x, continuous_const⟩).obj O.unop = ⊥)]
    exact Eq.symm (Subsingleton.eq_zero 1)
  map_mul' := by simp_rw [mul_zero, implies_true]
  map_zero' := rfl
  map_add' := by simp_rw [add_zero, implies_true]

/-- The map of sections on `O` induced by `(HomFromFieldSpec x F hF f).val.c`. -/
noncomputable def valCAppOpens (O : (TopologicalSpace.Opens X)ᵒᵖ) :
    X.presheaf.obj O ⟶
    (⟨fun _ ↦ x, continuous_const⟩ _* (Scheme.Spec.obj (Opposite.op F)).presheaf).obj O :=
  let _ := Classical.propDecidable (x ∈ O.unop)
  if hxO : x ∈ O.unop then valCAppOpensOfMem x F f O hxO
  else valCAppOpensOfNotMem x F O hxO

/-- `valCAppOpens` satisfies the natural property, which is an important basis for our construction
of the morphism from Spec(`F`) to `X`. -/
theorem valCAppOpens_naturality : ∀ {O1 O2 : (TopologicalSpace.Opens X)ᵒᵖ} (i : O1 ⟶ O2),
    CategoryTheory.CategoryStruct.comp (X.presheaf.map i) (valCAppOpens x F f O2) =
    CategoryTheory.CategoryStruct.comp (valCAppOpens x F f O1)
    ((⟨fun _ ↦ x, continuous_const⟩ _* (Scheme.Spec.obj (Opposite.op F)).presheaf).map i) := by
  intro O1 O2 i
  ext s
  rw [valCAppOpens, valCAppOpens]
  by_cases hxO2 : x ∈ O2.unop
  · have hxO1 : x ∈ O1.unop := CategoryTheory.le_of_op_hom i hxO2
    simp only [hxO2, hxO1, CategoryTheory.comp_apply]
    erw [RingHom.comp_apply, TopCat.Presheaf.germ_res_apply]
    rfl
  · simp only [hxO2]
    have : Unique (((Scheme.Spec.obj (Opposite.op F)).presheaf.obj
        { unop := (TopologicalSpace.Opens.map ⟨fun _ ↦ x, continuous_const⟩).obj O2.unop })) := by
      rw [(le_bot_iff.mp fun _ ↦ hxO2 : (@TopologicalSpace.Opens.map
        (Scheme.Spec.obj (Opposite.op F)) X.toTopCat ⟨fun _ ↦ x, continuous_const⟩).obj _ = ⊥)]
      exact @Spec.structureSheaf.section_over_bot_unique F _
    exact Eq.trans (this.eq_default _) (this.default_eq _)

/-- `(FirstCocone x F).ι.app = fun O ↦ (IsoForFirstCocone x F O).hom`. -/
noncomputable def IsoForFirstCocone (O : (TopologicalSpace.OpenNhds x)ᵒᵖ) :
    (Spec.structureSheaf F).val.obj
    (Opposite.op ((TopologicalSpace.Opens.map ⟨fun _ ↦ x, continuous_const⟩).obj
    ((TopologicalSpace.OpenNhds.inclusion x).obj O.unop))) ≅ F :=
  CategoryTheory.Iso.trans
    (CategoryTheory.eqToIso <| by
      rw [TopologicalSpace.Opens.map]; simp only; congr; simp only [Set.preimage_eq_univ_iff];
      intro x' h; change ∃ _, x = x' at h; rcases h with ⟨_, h1⟩; rw [← h1]; exact O.1.2)
    (StructureSheaf.globalSectionsIso F).symm

/-- As mentioned in the description of this file, there is a map `g` for which we want to show that
both the domain and codomain are fields. The domain of `g` is actually a colimit in terms of some
functor. Here we construct a concone in terms of the same functor. Note that `(FirstCocone x F).pt`
is defined as `F`. If we can prove that this cocone is a colimit, then because
colimits are unique up to isomorphisms, we will immediately have that the domain of `g` is
isomorphic to `F`. As `F` is a field, the domain of `g` is a field, which is what we want. -/
noncomputable def FirstCocone :
    CategoryTheory.Limits.Cocone
    ((TopologicalSpace.OpenNhds.inclusion x).op.comp
    ((TopologicalSpace.Opens.map ⟨fun _ ↦ x, continuous_const⟩).op.comp
    (Spec.structureSheaf F).val)) where
  pt := F
  ι := {
    app := fun O ↦ (IsoForFirstCocone x F O).hom
    naturality := fun O1 O2 i ↦ by
      have hO (O : (TopologicalSpace.OpenNhds x)ᵒᵖ) : (TopologicalSpace.Opens.map
          (@ContinuousMap.mk _ _ (PrimeSpectrum.Top F).str _ (fun _ ↦ x) continuous_const)).obj
          ((TopologicalSpace.OpenNhds.inclusion x).obj O.unop) = ⊤ := by
        ext
        simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
        exact O.1.2
      have heqToHom1 : ((TopologicalSpace.Opens.map ⟨fun _ ↦ x, continuous_const⟩).map
          ((TopologicalSpace.OpenNhds.inclusion x).map i.unop)).op =
          CategoryTheory.eqToHom (by rw [hO O1, hO O2]) := rfl
      have heqToHom2 : (Spec.structureSheaf F).val.map
          ((TopologicalSpace.Opens.map ⟨fun _ ↦ x, continuous_const⟩).map
          ((TopologicalSpace.OpenNhds.inclusion x).map i.unop)).op =
          CategoryTheory.eqToHom (by rw [hO O1, hO O2]) := by
        rw [heqToHom1, CategoryTheory.eqToHom_map]
      simp only [CategoryTheory.Functor.const_obj_obj, CategoryTheory.Functor.comp_map,
        CategoryTheory.Functor.op_map, Quiver.Hom.unop_op, CategoryTheory.Functor.const_obj_map,
        IsoForFirstCocone, CategoryTheory.Iso.trans_hom, CategoryTheory.eqToIso.hom,
        CategoryTheory.Iso.symm_hom, StructureSheaf.globalSectionsIso_inv,
        CategoryTheory.IsIso.eq_comp_inv, CategoryTheory.Category.assoc,
        CategoryTheory.IsIso.inv_hom_id, CategoryTheory.Category.comp_id, heqToHom2,
        CategoryTheory.eqToHom_trans] }

theorem FirstCocone.isColimit_fac (O : (TopologicalSpace.OpenNhds x)ᵒᵖ)
    (s : CategoryTheory.Limits.Cocone ((TopologicalSpace.OpenNhds.inclusion x).op.comp
      ((TopologicalSpace.Opens.map ⟨fun _ ↦ x, continuous_const⟩).op.comp
        (Spec.structureSheaf F).val))) :
    CategoryTheory.CategoryStruct.comp ((FirstCocone x F).ι.app O)
      ((fun s ↦ CategoryTheory.CategoryStruct.comp (IsoForFirstCocone x F { unop := ⊤ }).symm.hom
        (s.ι.app { unop := ⊤ })) s) = s.ι.app O := by
  simp only [FirstCocone, IsoForFirstCocone, CategoryTheory.Iso.trans_hom,
    CategoryTheory.eqToIso.hom, CategoryTheory.Iso.symm_hom, StructureSheaf.globalSectionsIso_inv,
    CategoryTheory.eqToIso_refl, CategoryTheory.Iso.refl_trans, CategoryTheory.Iso.symm_symm_eq,
    StructureSheaf.globalSectionsIso_hom, CategoryTheory.Category.assoc,
    CategoryTheory.IsIso.inv_hom_id_assoc, CategoryTheory.eqToHom_comp_iff]
  rw [← CategoryTheory.eqToHom_map _ <| by
    rw [Opposite.op_inj_iff]; ext; exact ⟨fun _ ↦ O.1.2, fun _ ↦ trivial⟩]
  exact Eq.symm (s.ι.naturality (Opposite.op (LE.le.hom fun _ _ ↦ trivial : O.unop ⟶ ⊤)))

/-- As mentioned in the description of this file, there is a map `g` for which we want to show that
both the domain and codomain are fields. The domain of `g` is actually a colimit in terms of some
functor. Recall that `FirstCocone x F` is a cocone in terms of the same functor and
`(FirstCocone x F).pt` is defined as `F`. This definition proves that `FirstCocone x F` is a
colimit. Because colimits are unique up to isomorphisms, this definition implies that the domain of
`g` is isomorphic to `F`. As `F` is a field, the domain of `g` is also a field, which is what we
want. -/
noncomputable def FirstCocone.isColimit :
    CategoryTheory.Limits.IsColimit (FirstCocone x F) where
  desc := fun s ↦
    CategoryTheory.CategoryStruct.comp (IsoForFirstCocone x F (Opposite.op ⊤)).symm.hom
    (s.ι.app (Opposite.op ⊤))
  fac := fun s O ↦ FirstCocone.isColimit_fac x F O s
  uniq := fun s hom h ↦ by
    simp only [CategoryTheory.Iso.symm_hom]
    rw [(CategoryTheory.Iso.eq_inv_comp _).mpr (h _)]

/-- The domain of the map `g` mentioned in the description of this file is isomorphic to `F`. -/
noncomputable def FirstFieldIso :
    (⟨fun _ ↦ x, continuous_const⟩ _* (Spec.structureSheaf F).val).stalk x ≅ F :=
  (CategoryTheory.Limits.colimit.isColimit ((TopologicalSpace.OpenNhds.inclusion x).op.comp
  ((TopologicalSpace.Opens.map ⟨fun _ ↦ x, continuous_const⟩).op.comp
  (Spec.structureSheaf F).val))).coconePointUniqueUpToIso (FirstCocone.isColimit x F)

/-- `(SecondCocone F hF x1).ι.app = fun O ↦ (IsoForSecondCocone F hF x1 O).hom`. -/
noncomputable def IsoForSecondCocone
    (x1 : Scheme.Spec.obj (Opposite.op F)) (O : (TopologicalSpace.OpenNhds x1)ᵒᵖ) :
    (Spec.structureSheaf F).val.obj
    { unop := (TopologicalSpace.OpenNhds.inclusion x1).obj O.unop } ≅ F :=
  CategoryTheory.Iso.trans
    (CategoryTheory.eqToIso <| by
      rw [show (TopologicalSpace.OpenNhds.inclusion x1).obj O.unop = ⊤ by
        ext x2; rw [Eq.trans ((@PrimeSpectrum.instUnique _ hF.toField).eq_default x2)
        ((@PrimeSpectrum.instUnique _ hF.toField).default_eq x1)]; simp; exact O.1.2])
    (StructureSheaf.globalSectionsIso F).symm

/-- As mentioned in the description of this file, there is a map `g` for which we want to
show that both the domain and codomain are fields. The codomain of `g` is actually a colimit
in terms of some functor. Here we construct a concone in terms of the same functor. Note that
`(SecondCocone F hF x1).pt` is defined as `F`. If we can prove that this cocone is a colimit,
then because colimits are unique up to isomorphisms, we will immediately have that the codomain
of `g` is isomorphic to `F`. As `F` is a field, the codomain of `g` is a field, which is what we
want. -/
noncomputable def SecondCocone (x1 : Scheme.Spec.obj (Opposite.op F)) :
    CategoryTheory.Limits.Cocone
    ((TopologicalSpace.OpenNhds.inclusion x1).op.comp (Spec.structureSheaf F).val) where
  pt := F
  ι := {
    app := fun O ↦ (IsoForSecondCocone F hF x1 O).hom
    naturality := fun O1 O2 i ↦ by
      have : ((TopologicalSpace.OpenNhds.inclusion x1).map i.unop).op = CategoryTheory.eqToHom (by
          simp only [Opposite.op.injEq]
          ext x2
          rw [Eq.trans ((@PrimeSpectrum.instUnique _ hF.toField).eq_default x2)
            ((@PrimeSpectrum.instUnique _ hF.toField).default_eq x1)]
          exact ⟨fun _ ↦ O2.1.2, fun _ ↦ O1.1.2⟩) :=
        CategoryTheory.eq_of_comp_right_eq fun {_} ↦ congrFun rfl
      simp only [CategoryTheory.Functor.const_obj_obj, CategoryTheory.Functor.comp_map,
        CategoryTheory.Functor.op_map, CategoryTheory.Functor.const_obj_map,
        CategoryTheory.Category.comp_id, IsoForSecondCocone, this, CategoryTheory.eqToHom_map,
        CategoryTheory.Iso.trans_hom, CategoryTheory.eqToIso.hom,
        CategoryTheory.eqToHom_trans_assoc] }

set_option maxHeartbeats 500000 in
/-- As mentioned in the description of this file, there is a map `g` for which we want to show
that both the domain and codomain are fields. The codomain of `g` is actually a colimit in terms
of some functor. Recall that `SecondCocone F hF x1` is a cocone in terms of the same functor and
`(SecondCocone F hF x1).pt` is defined as `F`. This definition proves that `SecondCocone F hF x1`
is a colimit. Because colimits are unique up to isomorphisms, this definition implies that the
codomain of `g` is isomorphic to `F`. As `F` is a field, the codomain of `g` is also a field,
which is what we want. -/
noncomputable def SecondCocone.isColimit (x1 : (Scheme.Spec.obj (Opposite.op F))) :
    CategoryTheory.Limits.IsColimit (SecondCocone F hF x1) where
  desc := fun s ↦
    CategoryTheory.CategoryStruct.comp (IsoForSecondCocone F hF x1 (Opposite.op ⊤)).symm.hom
    (s.ι.app (Opposite.op ⊤))
  fac := fun s O ↦ by
    simp only [SecondCocone, IsoForSecondCocone, CategoryTheory.Functor.comp_obj,
      CategoryTheory.Functor.op_obj, CategoryTheory.Iso.trans_hom, CategoryTheory.eqToIso.hom,
      CategoryTheory.Iso.symm_hom, StructureSheaf.globalSectionsIso_inv,
      CategoryTheory.eqToIso_refl, CategoryTheory.Iso.refl_trans, CategoryTheory.Iso.symm_symm_eq,
      StructureSheaf.globalSectionsIso_hom, CategoryTheory.Category.assoc,
      CategoryTheory.IsIso.inv_hom_id_assoc, CategoryTheory.eqToHom_comp_iff]
    rw [← CategoryTheory.eqToHom_map _ (by
      simp only [Opposite.op.injEq]
      ext x2
      simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, true_iff]
      rw [Eq.trans ((@PrimeSpectrum.instUnique _ hF.toField).eq_default x2)
        ((@PrimeSpectrum.instUnique _ hF.toField).default_eq x1)]
      exact O.1.2)]
    exact Eq.symm (s.ι.naturality (Opposite.op (LE.le.hom fun _ _ ↦ trivial : O.unop ⟶ ⊤)))
  uniq := fun s hom h ↦ by
    simp_rw [← h _, SecondCocone]
    rw [← CategoryTheory.Category.assoc, CategoryTheory.Iso.symm_hom, CategoryTheory.Iso.inv_hom_id,
      CategoryTheory.Category.id_comp]

set_option maxHeartbeats 300000 in
/-- The codomain of the map `g` mentioned in the description of this file is isomorphic to `F`. -/
noncomputable def SecondFieldIso (x1 : Scheme.Spec.obj (Opposite.op F)) :
    TopCat.Presheaf.stalk (Spec.structureSheaf F).val x1 ≅ F :=
  (CategoryTheory.Limits.colimit.isColimit ((TopologicalSpace.OpenNhds.inclusion x1).op.comp
  (Spec.structureSheaf F).val)).coconePointUniqueUpToIso (SecondCocone.isColimit F hF x1)

/-- The map `h` mentioned in the description of this file is essentially a composition of `f` and
some ring isomorphism. -/
theorem stalkFunctor_map_natTrans_eq :
    (TopCat.Presheaf.stalkFunctor CommRingCat x).map
    ⟨fun O ↦ valCAppOpens x F f O, fun O1 O2 i ↦ valCAppOpens_naturality x F f i⟩ =
    CategoryTheory.CategoryStruct.comp f (FirstFieldIso x F).inv := by
  refine' Eq.symm (CategoryTheory.Limits.IsColimit.uniq _
    (@CategoryTheory.Limits.Cocone.mk _ _ _ _ _ _
      (CategoryTheory.CategoryStruct.comp
        (@CategoryTheory.NatTrans.mk _ _ _ _ _ _ _ _)
        (CategoryTheory.Limits.colimit.cocone _).ι)) _ _)
  intro O
  have hxO (O : (TopologicalSpace.OpenNhds x)ᵒᵖ) :
    x ∈ (TopologicalSpace.OpenNhds.inclusion x).obj O.unop := O.1.2
  simp only [CategoryTheory.Functor.op_obj, CategoryTheory.NatTrans.comp_app, valCAppOpens,
    FirstFieldIso, hxO, ↓reduceDite, valCAppOpensOfMem, ← CommRingCat.comp_eq_ring_hom_comp,
    FirstCocone.isColimit, CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso,
    CategoryTheory.Functor.mapIso_inv, CategoryTheory.Limits.IsColimit.uniqueUpToIso_inv,
    CategoryTheory.Limits.Cocones.forget_map, CategoryTheory.Category.assoc,
    CategoryTheory.Limits.IsColimit.descCoconeMorphism_hom]
  congr
  exact Eq.symm (@CategoryTheory.Limits.colimit.w _ _ _ _
    ((TopologicalSpace.OpenNhds.inclusion x).op.comp
    ((TopologicalSpace.Opens.map ⟨fun _ ↦ x, continuous_const⟩).op.comp
      (Spec.structureSheaf F).val)) _ _ _
      (CategoryTheory.opHomOfLE fun _ _ ↦ trivial : Opposite.op ⊤ ⟶ O))

end HomFromFieldSpec

open HomFromFieldSpec

/-- The locally ringed space morphism from Spec(`F`) to `X` induced by `f`. -/
noncomputable def HomFromFieldSpec :
    (Scheme.Spec.obj (Opposite.op F)).toLocallyRingedSpace ⟶ X where
  val := {
    base := ⟨fun _ ↦ x, continuous_const⟩
    c := ⟨fun O ↦ valCAppOpens x F f O, fun O1 O2 i ↦ valCAppOpens_naturality x F f i⟩ }
  prop := fun x1 ↦ by
    let g := TopCat.Presheaf.stalkPushforward _ ⟨fun _ ↦ x, continuous_const⟩
      (Spec.structureSheaf F).val x1
    let h := (TopCat.Presheaf.stalkFunctor _
      ((@DFunLike.coe (Spec.topObj F ⟶ X.toPresheafedSpace) _
      (fun _ ↦ (CategoryTheory.forget TopCat).obj X.toPresheafedSpace) _
      ⟨fun _ ↦ x, continuous_const⟩) x1)).map
      ⟨fun O ↦ valCAppOpens x F f O, fun O1 O2 i ↦ valCAppOpens_naturality x F f i⟩
    have hg : IsLocalRingHom g := isLocalRingHom_of_isField_of_isField
      (isField_of_iso (FirstFieldIso x F) hF) (isField_of_iso (SecondFieldIso F hF x1) hF) g
    have hh : IsLocalRingHom h := by
      change IsLocalRingHom ((TopCat.Presheaf.stalkFunctor CommRingCat x).map _)
      erw [stalkFunctor_map_natTrans_eq]
      exact CommRingCat.isLocalRingHom_comp f (FirstFieldIso x F).inv
    exact @isLocalRingHom_comp _ _ _ _ _ _ g h hg hh

end LocallyRingedSpace

end AlgebraicGeometry
