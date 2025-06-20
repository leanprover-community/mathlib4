/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Shapes
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.Tactic.ApplyFun

/-!
# The equalizer diagram sheaf condition for a presieve

In `Mathlib/CategoryTheory/Sites/IsSheafFor.lean` it is defined what it means for a presheaf to be a
sheaf *for* a particular presieve. In this file we provide equivalent conditions in terms of
equalizer diagrams.

* In `Equalizer.Presieve.sheaf_condition`, the sheaf condition at a presieve is shown to be
  equivalent to that of https://stacks.math.columbia.edu/tag/00VM (and combined with
  `isSheaf_pretopology`, this shows the notions of `IsSheaf` are exactly equivalent.)

* In `Equalizer.Sieve.equalizer_sheaf_condition`, the sheaf condition at a sieve is shown to be
  equivalent to that of Equation (3) p. 122 in Maclane-Moerdijk [MM92].

## References

* [MM92]: *Sheaves in geometry and logic*, Saunders MacLane, and Ieke Moerdijk:
  Chapter III, Section 4.
* https://stacks.math.columbia.edu/tag/00VL (sheaves on a pretopology or site)

-/


universe t w v u

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

namespace Equalizer

variable {C : Type u} [Category.{v} C] (P : Cᵒᵖ ⥤ Type max v u) {X : C} (R : Presieve X)
  (S : Sieve X)

noncomputable section

/--
The middle object of the fork diagram given in Equation (3) of [MM92], as well as the fork diagram
of the Stacks entry.
-/
@[stacks 00VM "This is the middle object of the fork diagram there."]
def FirstObj : Type max v u :=
  ∏ᶜ fun f : ΣY, { f : Y ⟶ X // R f } => P.obj (op f.1)

variable {P R}

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/10688): added to ease automation
@[ext]
lemma FirstObj.ext (z₁ z₂ : FirstObj P R) (h : ∀ (Y : C) (f : Y ⟶ X)
    (hf : R f), (Pi.π _ ⟨Y, f, hf⟩ : FirstObj P R ⟶ _) z₁ =
      (Pi.π _ ⟨Y, f, hf⟩ : FirstObj P R ⟶ _) z₂) : z₁ = z₂ := by
  apply Limits.Types.limit_ext
  rintro ⟨⟨Y, f, hf⟩⟩
  exact h Y f hf

variable (P R)

/-- Show that `FirstObj` is isomorphic to `FamilyOfElements`. -/
@[simps]
def firstObjEqFamily : FirstObj P R ≅ R.FamilyOfElements P where
  hom t _ _ hf := Pi.π (fun f : ΣY, { f : Y ⟶ X // R f } => P.obj (op f.1)) ⟨_, _, hf⟩ t
  inv := Pi.lift fun f x => x _ f.2.2

instance : Inhabited (FirstObj P (⊥ : Presieve X)) :=
  (firstObjEqFamily P _).toEquiv.inhabited

-- Porting note: was not needed in mathlib
instance : Inhabited (FirstObj P ((⊥ : Sieve X) : Presieve X)) :=
  (inferInstance : Inhabited (FirstObj P (⊥ : Presieve X)))

/--
The left morphism of the fork diagram given in Equation (3) of [MM92], as well as the fork diagram
of the Stacks entry.
-/
@[stacks 00VM "This is the left morphism of the fork diagram there."]
def forkMap : P.obj (op X) ⟶ FirstObj P R :=
  Pi.lift fun f => P.map f.2.1.op

/-!
This section establishes the equivalence between the sheaf condition of Equation (3) [MM92] and
the definition of `IsSheafFor`.
-/


namespace Sieve

/-- The rightmost object of the fork diagram of Equation (3) [MM92], which contains the data used
to check a family is compatible.
-/
def SecondObj : Type max v u :=
  ∏ᶜ fun f : Σ (Y Z : _) (_ : Z ⟶ Y), { f' : Y ⟶ X // S f' } => P.obj (op f.2.1)

variable {P S}

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/10688): added to ease automation
@[ext]
lemma SecondObj.ext (z₁ z₂ : SecondObj P S) (h : ∀ (Y Z : C) (g : Z ⟶ Y) (f : Y ⟶ X)
    (hf : S.arrows f), (Pi.π _ ⟨Y, Z, g, f, hf⟩ : SecondObj P S ⟶ _) z₁ =
      (Pi.π _ ⟨Y, Z, g, f, hf⟩ : SecondObj P S ⟶ _) z₂) : z₁ = z₂ := by
  apply Limits.Types.limit_ext
  rintro ⟨⟨Y, Z, g, f, hf⟩⟩
  apply h

variable (P S)

/-- The map `p` of Equations (3,4) [MM92]. -/
def firstMap : FirstObj P (S : Presieve X) ⟶ SecondObj P S :=
  Pi.lift fun fg =>
    Pi.π _ (⟨_, _, S.downward_closed fg.2.2.2.2 fg.2.2.1⟩ : ΣY, { f : Y ⟶ X // S f })

instance : Inhabited (SecondObj P (⊥ : Sieve X)) :=
  ⟨firstMap _ _ default⟩

/-- The map `a` of Equations (3,4) [MM92]. -/
def secondMap : FirstObj P (S : Presieve X) ⟶ SecondObj P S :=
  Pi.lift fun fg => Pi.π _ ⟨_, fg.2.2.2⟩ ≫ P.map fg.2.2.1.op

theorem w : forkMap P (S : Presieve X) ≫ firstMap P S = forkMap P S ≫ secondMap P S := by
  ext
  simp [firstMap, secondMap, forkMap]

/--
The family of elements given by `x : FirstObj P S` is compatible iff `firstMap` and `secondMap`
map it to the same point.
-/
theorem compatible_iff (x : FirstObj P S.arrows) :
    ((firstObjEqFamily P S.arrows).hom x).Compatible ↔ firstMap P S x = secondMap P S x := by
  rw [Presieve.compatible_iff_sieveCompatible]
  constructor
  · intro t
    apply SecondObj.ext
    intros Y Z g f hf
    simpa [firstMap, secondMap] using t _ g hf
  · intro t Y Z f g hf
    rw [Types.limit_ext_iff'] at t
    simpa [firstMap, secondMap] using t ⟨⟨Y, Z, g, f, hf⟩⟩

/-- `P` is a sheaf for `S`, iff the fork given by `w` is an equalizer. -/
theorem equalizer_sheaf_condition :
    Presieve.IsSheafFor P (S : Presieve X) ↔ Nonempty (IsLimit (Fork.ofι _ (w P S))) := by
  rw [Types.type_equalizer_iff_unique,
    ← Equiv.forall_congr_right (firstObjEqFamily P (S : Presieve X)).toEquiv.symm]
  simp_rw [← compatible_iff]
  simp only [inv_hom_id_apply, Iso.toEquiv_symm_fun]
  apply forall₂_congr
  intro x _
  apply existsUnique_congr
  intro t
  rw [← Iso.toEquiv_symm_fun]
  rw [Equiv.eq_symm_apply]
  constructor
  · intro q
    funext Y f hf
    simpa [firstObjEqFamily, forkMap] using q _ _
  · intro q Y f hf
    rw [← q]
    simp [firstObjEqFamily, forkMap]

end Sieve

/-!
This section establishes the equivalence between the sheaf condition of
https://stacks.math.columbia.edu/tag/00VM and the definition of `isSheafFor`.
-/


namespace Presieve

variable [R.hasPullbacks]

/--
The rightmost object of the fork diagram of the Stacks entry, which
contains the data used to check a family of elements for a presieve is compatible.
-/
@[simp, stacks 00VM "This is the rightmost object of the fork diagram there."]
def SecondObj : Type max v u :=
  ∏ᶜ fun fg : (ΣY, { f : Y ⟶ X // R f }) × ΣZ, { g : Z ⟶ X // R g } =>
    haveI := Presieve.hasPullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
    P.obj (op (pullback fg.1.2.1 fg.2.2.1))

/-- The map `pr₀*` of the Stacks entry. -/
@[stacks 00VM "This is the map `pr₀*` there."]
def firstMap : FirstObj P R ⟶ SecondObj P R :=
  Pi.lift fun fg =>
    haveI := Presieve.hasPullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
    Pi.π _ _ ≫ P.map (pullback.fst _ _).op

instance [HasPullbacks C] : Inhabited (SecondObj P (⊥ : Presieve X)) :=
  ⟨firstMap _ _ default⟩

/-- The map `pr₁*` of the Stacks entry. -/
@[stacks 00VM "This is the map `pr₁*` there."]
def secondMap : FirstObj P R ⟶ SecondObj P R :=
  Pi.lift fun fg =>
    haveI := Presieve.hasPullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
    Pi.π _ _ ≫ P.map (pullback.snd _ _).op

theorem w : forkMap P R ≫ firstMap P R = forkMap P R ≫ secondMap P R := by
  dsimp
  ext fg
  simp only [firstMap, secondMap, forkMap]
  simp only [limit.lift_π, limit.lift_π_assoc, assoc, Fan.mk_π_app]
  haveI := Presieve.hasPullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
  rw [← P.map_comp, ← op_comp, pullback.condition]
  simp

/--
The family of elements given by `x : FirstObj P S` is compatible iff `firstMap` and `secondMap`
map it to the same point.
-/
theorem compatible_iff (x : FirstObj P R) :
    ((firstObjEqFamily P R).hom x).Compatible ↔ firstMap P R x = secondMap P R x := by
  rw [Presieve.pullbackCompatible_iff]
  constructor
  · intro t
    apply Limits.Types.limit_ext
    rintro ⟨⟨Y, f, hf⟩, Z, g, hg⟩
    simpa [firstMap, secondMap] using t hf hg
  · intro t Y Z f g hf hg
    rw [Types.limit_ext_iff'] at t
    simpa [firstMap, secondMap] using t ⟨⟨⟨Y, f, hf⟩, Z, g, hg⟩⟩

/-- `P` is a sheaf for `R`, iff the fork given by `w` is an equalizer. -/
@[stacks 00VM]
theorem sheaf_condition : R.IsSheafFor P ↔ Nonempty (IsLimit (Fork.ofι _ (w P R))) := by
  rw [Types.type_equalizer_iff_unique,
    ← Equiv.forall_congr_right (firstObjEqFamily P R).toEquiv.symm]
  simp_rw [← compatible_iff, ← Iso.toEquiv_fun, Equiv.apply_symm_apply]
  apply forall₂_congr
  intro x _
  apply existsUnique_congr
  intro t
  rw [Equiv.eq_symm_apply]
  constructor
  · intro q
    funext Y f hf
    simpa [forkMap] using q _ _
  · intro q Y f hf
    rw [← q]
    simp [forkMap]

namespace Arrows

variable (P : Cᵒᵖ ⥤ Type w) {X : C} (R : Presieve X) (S : Sieve X)

open Presieve

variable {B : C} {I : Type t} [Small.{w} I] (X : I → C) (π : (i : I) → X i ⟶ B)
    [(Presieve.ofArrows X π).hasPullbacks]

/--
The middle object of the fork diagram of the Stacks entry.
The difference between this and `Equalizer.FirstObj P (ofArrows X π)` arises if the family of
arrows `π` contains duplicates. The `Presieve.ofArrows` doesn't see those.
-/
@[stacks 00VM "The middle object of the fork diagram there."]
def FirstObj : Type w := ∏ᶜ (fun i ↦ P.obj (op (X i)))

@[ext]
lemma FirstObj.ext (z₁ z₂ : FirstObj P X) (h : ∀ i, (Pi.π _ i : FirstObj P X ⟶ _) z₁ =
    (Pi.π _ i : FirstObj P X ⟶ _) z₂) : z₁ = z₂ := by
  apply Limits.Types.limit_ext
  rintro ⟨i⟩
  exact h i

/--
The rightmost object of the fork diagram of the Stacks entry.
The difference between this and `Equalizer.Presieve.SecondObj P (ofArrows X π)` arises if the
family of arrows `π` contains duplicates. The `Presieve.ofArrows` doesn't see those.
-/
@[stacks 00VM "The rightmost object of the fork diagram there."]
def SecondObj : Type w  :=
  ∏ᶜ (fun (ij : I × I) ↦ P.obj (op (pullback (π ij.1) (π ij.2))))

@[ext]
lemma SecondObj.ext (z₁ z₂ : SecondObj P X π) (h : ∀ ij, (Pi.π _ ij : SecondObj P X π ⟶ _) z₁ =
    (Pi.π _ ij : SecondObj P X π ⟶ _) z₂) : z₁ = z₂ := by
  apply Limits.Types.limit_ext
  rintro ⟨i⟩
  exact h i

/--
The left morphism of the fork diagram.
-/
def forkMap : P.obj (op B) ⟶ FirstObj P X := Pi.lift (fun i ↦ P.map (π i).op)

/--
The first of the two parallel morphisms of the fork diagram, induced by the first projection in
each pullback.
-/
def firstMap : FirstObj P X ⟶ SecondObj P X π :=
  Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.fst _ _).op

/--
The second of the two parallel morphisms of the fork diagram, induced by the second projection in
each pullback.
-/
def secondMap : FirstObj P X ⟶ SecondObj P X π :=
  Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.snd _ _).op

theorem w : forkMap P X π ≫ firstMap P X π = forkMap P X π ≫ secondMap P X π := by
  ext x ij
  simp only [firstMap, secondMap, forkMap, types_comp_apply, Types.pi_lift_π_apply,
    ← FunctorToTypes.map_comp_apply, ← op_comp, pullback.condition]

/--
The family of elements given by `x : FirstObj P S` is compatible iff `firstMap` and `secondMap`
map it to the same point.
See `CategoryTheory.Equalizer.Presieve.Arrows.compatible_iff_of_small` for a version with
less universe assumptions.
-/
theorem compatible_iff {I : Type w} (X : I → C) (π : (i : I) → X i ⟶ B)
    [(Presieve.ofArrows X π).hasPullbacks] (x : FirstObj P X) :
    (Arrows.Compatible P π ((Types.productIso _).hom x)) ↔
      firstMap P X π x = secondMap P X π x := by
  rw [Arrows.pullbackCompatible_iff]
  constructor
  · intro t
    ext ij
    simpa [firstMap, secondMap] using t ij.1 ij.2
  · intro t i j
    apply_fun Pi.π (fun (ij : I × I) ↦ P.obj (op (pullback (π ij.1) (π ij.2)))) ⟨i, j⟩ at t
    simpa [firstMap, secondMap] using t

/-- Version of `CategoryTheory.Equalizer.Presieve.Arrows.compatible_iff` for a small
indexing type. -/
lemma compatible_iff_of_small (x : FirstObj P X) :
    (Arrows.Compatible P π ((equivShrink _).symm ((Types.Small.productIso _).hom x))) ↔
      firstMap P X π x = secondMap P X π x := by
  rw [Arrows.pullbackCompatible_iff]
  refine ⟨fun t ↦ ?_, fun t i j ↦ ?_⟩
  · ext ij
    simpa [firstMap, secondMap] using t ij.1 ij.2
  · apply_fun Pi.π (fun (ij : I × I) ↦ P.obj (op (pullback (π ij.1) (π ij.2)))) ⟨i, j⟩ at t
    simpa [firstMap, secondMap] using t

/-- `P` is a sheaf for `Presieve.ofArrows X π`, iff the fork given by `w` is an equalizer. -/
@[stacks 00VM]
theorem sheaf_condition : (Presieve.ofArrows X π).IsSheafFor P ↔
    Nonempty (IsLimit (Fork.ofι (forkMap P X π) (w P X π))) := by
  rw [Types.type_equalizer_iff_unique, isSheafFor_arrows_iff]
  simp only [FirstObj]
  rw [← Equiv.forall_congr_right ((equivShrink _).trans (Types.Small.productIso _).toEquiv.symm)]
  simp_rw [← compatible_iff_of_small, ← Iso.toEquiv_fun, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.symm_apply_apply]
  apply forall₂_congr
  intro x _
  apply existsUnique_congr
  intro t
  rw [Equiv.eq_symm_apply, ← Equiv.symm_apply_eq]
  constructor
  · intro q
    funext i
    simpa [forkMap] using q i
  · intro q i
    rw [← q]
    simp [forkMap]

end Arrows

/-- The sheaf condition for a single morphism is the same as the canonical fork diagram being
limiting. -/
lemma isSheafFor_singleton_iff {F : Cᵒᵖ ⥤ Type*} {X Y : C} {f : X ⟶ Y}
    (c : PullbackCone f f) (hc : IsLimit c) :
    Presieve.IsSheafFor F (.singleton f) ↔
      Nonempty
        (IsLimit (Fork.ofι (F.map f.op) (f := F.map c.fst.op) (g := F.map c.snd.op)
          (by simp [← Functor.map_comp, ← op_comp, c.condition]))) := by
  have h (x : F.obj (op X)) : (∀ {Z : C} (p₁ p₂ : Z ⟶ X),
      p₁ ≫ f = p₂ ≫ f → F.map p₁.op x = F.map p₂.op x) ↔ F.map c.fst.op x = F.map c.snd.op x := by
    refine ⟨fun H ↦ H _ _ c.condition, fun H Z p₁ p₂ h ↦ ?_⟩
    rw [← PullbackCone.IsLimit.lift_fst hc _ _ h, op_comp, FunctorToTypes.map_comp_apply, H]
    simp [← FunctorToTypes.map_comp_apply, ← op_comp]
  rw [Types.type_equalizer_iff_unique, Presieve.isSheafFor_singleton]
  simp_rw [h]

/-- Special case of `isSheafFor_singleton_iff` with `c = pullback.cone f f`. -/
lemma isSheafFor_singleton_iff_of_hasPullback {F : Cᵒᵖ ⥤ Type*} {X Y : C} {f : X ⟶ Y}
    [HasPullback f f] :
    Presieve.IsSheafFor F (.singleton f) ↔
      Nonempty
        (IsLimit (Fork.ofι (F.map f.op) (f := F.map (pullback.fst f f).op)
          (g := F.map (pullback.snd f f).op)
          (by simp [← Functor.map_comp, ← op_comp, pullback.condition]))) :=
  isSheafFor_singleton_iff (pullback.cone f f) (pullback.isLimit f f)

end Presieve

end

end Equalizer

variable {C : Type*} [Category C]

/--
If
- `F` contravariantly maps (suitable) coproducts to products,
- (suitable) coproducts exist in `C`, and
- (suitable) coproducts distribute over pullbacks, then:

`F` is a sheaf for the single object covering `{ ∐ᵢ Yᵢ ⟶ X }`
if and only if it is a presieve for `{ fᵢ : Yᵢ ⟶ X }ᵢ`.

Note: The second two conditions are satisfied if `C` is (finitary) extensive.
-/
lemma Presieve.isSheafFor_sigmaDesc_iff {F : Cᵒᵖ ⥤ Type v} {X : C} {ι : Type*} [Small.{v} ι]
    {Y : ι → C}
    (f : ∀ i, Y i ⟶ X) [(ofArrows Y f).hasPullbacks]
    [HasCoproduct Y] [HasCoproduct fun (ij : ι × ι) ↦ pullback (f ij.1) (f ij.2)]
    [HasPullback (Limits.Sigma.desc f) (Limits.Sigma.desc f)]
    [PreservesLimit (Discrete.functor <| fun i ↦ op (Y i)) F]
    [PreservesLimit (Discrete.functor fun (ij : ι × ι) ↦ op (pullback (f ij.1) (f ij.2))) F]
    [IsIso (Limits.Sigma.desc fun (ij : ι × ι) ↦ Limits.pullback.map (f ij.fst) (f ij.snd)
      (Limits.Sigma.desc f) (Limits.Sigma.desc f) (Limits.Sigma.ι _ _) (Limits.Sigma.ι _ _) (𝟙 X)
      (by simp) (by simp))] :
    Presieve.IsSheafFor F (.singleton <| Limits.Sigma.desc f) ↔
      Presieve.IsSheafFor F (.ofArrows Y f) := by
  let e : (∐ fun (ij : ι × ι) ↦ pullback (f ij.1) (f ij.2)) ⟶
      pullback (Limits.Sigma.desc f) (Limits.Sigma.desc f) :=
    Limits.Sigma.desc fun ij ↦
    pullback.map _ _ _ _ (Limits.Sigma.ι _ _) (Limits.Sigma.ι _ _) (𝟙 X) (by simp) (by simp)
  rw [Equalizer.Presieve.isSheafFor_singleton_iff (pullback.cone _ _) (pullback.isLimit _ _),
    Equalizer.Presieve.Arrows.sheaf_condition]
  refine (Fork.isLimitEquivOfIsos _ _ ?_ ?_ ?_ ?_ ?_ ?_).nonempty_congr
  · exact F.mapIso (opCoproductIsoProduct Y) ≪≫ PreservesProduct.iso F _
  · exact F.mapIso (.op <| asIso e) ≪≫ F.mapIso (opCoproductIsoProduct _) ≪≫
      PreservesProduct.iso F _
  · exact Iso.refl _
  · refine Pi.hom_ext _ _ fun ij ↦ ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, PreservesProduct.iso_hom, Category.assoc,
      limit.cone_x, PullbackCone.fst_limit_cone, Iso.op_hom, asIso_hom, e, piComparison_comp_π,
      Equalizer.Presieve.Arrows.firstMap]
    rw [← F.map_comp, opCoproductIsoProduct_hom_comp_π, ← F.map_comp, ← op_comp, Sigma.ι_desc,
      ← F.map_comp, ← op_comp, pullback.lift_fst, Pi.lift_π, piComparison_comp_π_assoc,
      ← F.map_comp, ← F.map_comp]
    simp
  · refine Pi.hom_ext _ _ fun ij ↦ ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, PreservesProduct.iso_hom, Category.assoc,
      limit.cone_x, PullbackCone.snd_limit_cone, Iso.op_hom, asIso_hom, e, piComparison_comp_π,
      Equalizer.Presieve.Arrows.secondMap]
    rw [← F.map_comp, opCoproductIsoProduct_hom_comp_π, ← F.map_comp, ← op_comp, Sigma.ι_desc,
      ← F.map_comp, ← op_comp, pullback.lift_snd, Pi.lift_π, piComparison_comp_π_assoc,
      ← F.map_comp, ← F.map_comp]
    simp
  · refine Pi.hom_ext _ _ fun i ↦ ?_
    simp only [Fork.ofι_pt, Fork.ι_ofι, Iso.trans_hom, Functor.mapIso_hom, PreservesProduct.iso_hom,
      Category.assoc, piComparison_comp_π]
    rw [← F.map_comp, ← F.map_comp, opCoproductIsoProduct_hom_comp_π, ← op_comp, Sigma.ι_desc]
    simp [Equalizer.Presieve.Arrows.forkMap]

end CategoryTheory
