/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.Tactic.ApplyFun

#align_import category_theory.sites.sheaf_of_types from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# The equalizer diagram sheaf condition for a presieve

In `Mathlib/CategoryTheory/Sites/IsSheafFor.lean` it is defined what it means for a presheaf to be a
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


universe w v u

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

namespace Equalizer

variable {C : Type u} [Category.{v} C] (P : Cᵒᵖ ⥤ Type max v u) {X : C} (R : Presieve X)
  (S : Sieve X)

noncomputable section

/--
The middle object of the fork diagram given in Equation (3) of [MM92], as well as the fork diagram
of <https://stacks.math.columbia.edu/tag/00VM>.
-/
def FirstObj : Type max v u :=
  ∏ᶜ fun f : ΣY, { f : Y ⟶ X // R f } => P.obj (op f.1)
#align category_theory.equalizer.first_obj CategoryTheory.Equalizer.FirstObj

variable {P R}

-- Porting note (#10688): added to ease automation
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
  hom t Y f hf := Pi.π (fun f : ΣY, { f : Y ⟶ X // R f } => P.obj (op f.1)) ⟨_, _, hf⟩ t
  inv := Pi.lift fun f x => x _ f.2.2
#align category_theory.equalizer.first_obj_eq_family CategoryTheory.Equalizer.firstObjEqFamily

instance : Inhabited (FirstObj P (⊥ : Presieve X)) :=
  (firstObjEqFamily P _).toEquiv.inhabited

-- Porting note: was not needed in mathlib
instance : Inhabited (FirstObj P ((⊥ : Sieve X) : Presieve X)) :=
  (inferInstance : Inhabited (FirstObj P (⊥ : Presieve X)))

/--
The left morphism of the fork diagram given in Equation (3) of [MM92], as well as the fork diagram
of <https://stacks.math.columbia.edu/tag/00VM>.
-/
def forkMap : P.obj (op X) ⟶ FirstObj P R :=
  Pi.lift fun f => P.map f.2.1.op
#align category_theory.equalizer.fork_map CategoryTheory.Equalizer.forkMap

/-!
This section establishes the equivalence between the sheaf condition of Equation (3) [MM92] and
the definition of `IsSheafFor`.
-/


namespace Sieve

/-- The rightmost object of the fork diagram of Equation (3) [MM92], which contains the data used
to check a family is compatible.
-/
def SecondObj : Type max v u :=
  ∏ᶜ fun f : Σ(Y Z : _) (_ : Z ⟶ Y), { f' : Y ⟶ X // S f' } => P.obj (op f.2.1)
#align category_theory.equalizer.sieve.second_obj CategoryTheory.Equalizer.Sieve.SecondObj

variable {P S}

-- Porting note (#10688): added to ease automation
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
#align category_theory.equalizer.sieve.first_map CategoryTheory.Equalizer.Sieve.firstMap

instance : Inhabited (SecondObj P (⊥ : Sieve X)) :=
  ⟨firstMap _ _ default⟩

/-- The map `a` of Equations (3,4) [MM92]. -/
def secondMap : FirstObj P (S : Presieve X) ⟶ SecondObj P S :=
  Pi.lift fun fg => Pi.π _ ⟨_, fg.2.2.2⟩ ≫ P.map fg.2.2.1.op
#align category_theory.equalizer.sieve.second_map CategoryTheory.Equalizer.Sieve.secondMap

theorem w : forkMap P (S : Presieve X) ≫ firstMap P S = forkMap P S ≫ secondMap P S := by
  ext
  simp [firstMap, secondMap, forkMap]
#align category_theory.equalizer.sieve.w CategoryTheory.Equalizer.Sieve.w

/--
The family of elements given by `x : FirstObj P S` is compatible iff `firstMap` and `secondMap`
map it to the same point.
-/
theorem compatible_iff (x : FirstObj P S) :
    ((firstObjEqFamily P S).hom x).Compatible ↔ firstMap P S x = secondMap P S x := by
  rw [Presieve.compatible_iff_sieveCompatible]
  constructor
  · intro t
    apply SecondObj.ext
    intros Y Z g f hf
    simpa [firstMap, secondMap] using t _ g hf
  · intro t Y Z f g hf
    rw [Types.limit_ext_iff'] at t
    simpa [firstMap, secondMap] using t ⟨⟨Y, Z, g, f, hf⟩⟩
#align category_theory.equalizer.sieve.compatible_iff CategoryTheory.Equalizer.Sieve.compatible_iff

/-- `P` is a sheaf for `S`, iff the fork given by `w` is an equalizer. -/
theorem equalizer_sheaf_condition :
    Presieve.IsSheafFor P (S : Presieve X) ↔ Nonempty (IsLimit (Fork.ofι _ (w P S))) := by
  rw [Types.type_equalizer_iff_unique,
    ← Equiv.forall_congr_left (firstObjEqFamily P (S : Presieve X)).toEquiv.symm]
  simp_rw [← compatible_iff]
  simp only [inv_hom_id_apply, Iso.toEquiv_symm_fun]
  apply forall₂_congr
  intro x _
  apply exists_unique_congr
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
#align category_theory.equalizer.sieve.equalizer_sheaf_condition CategoryTheory.Equalizer.Sieve.equalizer_sheaf_condition

end Sieve

/-!
This section establishes the equivalence between the sheaf condition of
https://stacks.math.columbia.edu/tag/00VM and the definition of `isSheafFor`.
-/


namespace Presieve

variable [R.hasPullbacks]

/--
The rightmost object of the fork diagram of https://stacks.math.columbia.edu/tag/00VM, which
contains the data used to check a family of elements for a presieve is compatible.
-/
@[simp] def SecondObj : Type max v u :=
  ∏ᶜ fun fg : (ΣY, { f : Y ⟶ X // R f }) × ΣZ, { g : Z ⟶ X // R g } =>
    haveI := Presieve.hasPullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
    P.obj (op (pullback fg.1.2.1 fg.2.2.1))
#align category_theory.equalizer.presieve.second_obj CategoryTheory.Equalizer.Presieve.SecondObj

/-- The map `pr₀*` of <https://stacks.math.columbia.edu/tag/00VL>. -/
def firstMap : FirstObj P R ⟶ SecondObj P R :=
  Pi.lift fun fg =>
    haveI := Presieve.hasPullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
    Pi.π _ _ ≫ P.map pullback.fst.op
#align category_theory.equalizer.presieve.first_map CategoryTheory.Equalizer.Presieve.firstMap

instance [HasPullbacks C] : Inhabited (SecondObj P (⊥ : Presieve X)) :=
  ⟨firstMap _ _ default⟩

/-- The map `pr₁*` of <https://stacks.math.columbia.edu/tag/00VL>. -/
def secondMap : FirstObj P R ⟶ SecondObj P R :=
  Pi.lift fun fg =>
    haveI := Presieve.hasPullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
    Pi.π _ _ ≫ P.map pullback.snd.op
#align category_theory.equalizer.presieve.second_map CategoryTheory.Equalizer.Presieve.secondMap

theorem w : forkMap P R ≫ firstMap P R = forkMap P R ≫ secondMap P R := by
  dsimp
  ext fg
  simp only [firstMap, secondMap, forkMap]
  simp only [limit.lift_π, limit.lift_π_assoc, assoc, Fan.mk_π_app]
  haveI := Presieve.hasPullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
  rw [← P.map_comp, ← op_comp, pullback.condition]
  simp
#align category_theory.equalizer.presieve.w CategoryTheory.Equalizer.Presieve.w

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
#align category_theory.equalizer.presieve.compatible_iff CategoryTheory.Equalizer.Presieve.compatible_iff

/-- `P` is a sheaf for `R`, iff the fork given by `w` is an equalizer.
See <https://stacks.math.columbia.edu/tag/00VM>.
-/
theorem sheaf_condition : R.IsSheafFor P ↔ Nonempty (IsLimit (Fork.ofι _ (w P R))) := by
  rw [Types.type_equalizer_iff_unique]
  erw [← Equiv.forall_congr_left (firstObjEqFamily P R).toEquiv.symm]
  simp_rw [← compatible_iff, ← Iso.toEquiv_fun, Equiv.apply_symm_apply]
  apply forall₂_congr
  intro x _
  apply exists_unique_congr
  intro t
  rw [Equiv.eq_symm_apply]
  constructor
  · intro q
    funext Y f hf
    simpa [forkMap] using q _ _
  · intro q Y f hf
    rw [← q]
    simp [forkMap]
#align category_theory.equalizer.presieve.sheaf_condition CategoryTheory.Equalizer.Presieve.sheaf_condition

namespace Arrows

variable (P : Cᵒᵖ ⥤ Type w) {X : C} (R : Presieve X) (S : Sieve X)

open Presieve

variable {B : C} {I : Type} (X : I → C) (π : (i : I) → X i ⟶ B)
    [(Presieve.ofArrows X π).hasPullbacks]
-- TODO: allow `I : Type w` 

/--
The middle object of the fork diagram of <https://stacks.math.columbia.edu/tag/00VM>.
The difference between this and `Equalizer.FirstObj P (ofArrows X π)` arrises if the family of
arrows `π` contains duplicates. The `Presieve.ofArrows` doesn't see those.
-/
def FirstObj : Type w := ∏ᶜ (fun i ↦ P.obj (op (X i)))

@[ext]
lemma FirstObj.ext (z₁ z₂ : FirstObj P X) (h : ∀ i, (Pi.π _ i : FirstObj P X ⟶ _) z₁ =
    (Pi.π _ i : FirstObj P X ⟶ _) z₂) : z₁ = z₂ := by
  apply Limits.Types.limit_ext
  rintro ⟨i⟩
  exact h i

/--
The rightmost object of the fork diagram of https://stacks.math.columbia.edu/tag/00VM.
The difference between this and `Equalizer.Presieve.SecondObj P (ofArrows X π)` arrises if the
family of arrows `π` contains duplicates. The `Presieve.ofArrows` doesn't see those.
-/
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
def firstMap : FirstObj P X ⟶ SecondObj P X π := Pi.lift fun _ => Pi.π _ _ ≫ P.map pullback.fst.op

/--
The second of the two parallel morphisms of the fork diagram, induced by the second projection in
each pullback.
-/
def secondMap : FirstObj P X ⟶ SecondObj P X π := Pi.lift fun _ => Pi.π _ _ ≫ P.map pullback.snd.op

theorem w : forkMap P X π ≫ firstMap P X π = forkMap P X π ≫ secondMap P X π := by
  ext x ij
  simp only [firstMap, secondMap, forkMap, types_comp_apply, Types.pi_lift_π_apply,
    ← FunctorToTypes.map_comp_apply, ← op_comp, pullback.condition]

/--
The family of elements given by `x : FirstObj P S` is compatible iff `firstMap` and `secondMap`
map it to the same point.
-/
theorem compatible_iff (x : FirstObj P X) : (Arrows.Compatible P π ((Types.productIso _).hom x)) ↔
    firstMap P X π x = secondMap P X π x := by
  rw [Arrows.pullbackCompatible_iff]
  constructor
  · intro t
    ext ij
    simpa [firstMap, secondMap] using t ij.1 ij.2
  · intro t i j
    apply_fun Pi.π (fun (ij : I × I) ↦ P.obj (op (pullback (π ij.1) (π ij.2)))) ⟨i, j⟩ at t
    simpa [firstMap, secondMap] using t

/--
`P` is a sheaf for `Presieve.ofArrows X π`, iff the fork given by `w` is an equalizer.
See <https://stacks.math.columbia.edu/tag/00VM>.
-/
theorem sheaf_condition : (Presieve.ofArrows X π).IsSheafFor P ↔
    Nonempty (IsLimit (Fork.ofι (forkMap P X π) (w P X π))) := by
  rw [Types.type_equalizer_iff_unique, isSheafFor_arrows_iff]
  erw [← Equiv.forall_congr_left (Types.productIso _).toEquiv.symm]
  simp_rw [← compatible_iff, ← Iso.toEquiv_fun, Equiv.apply_symm_apply]
  apply forall₂_congr
  intro x _
  apply exists_unique_congr
  intro t
  erw [Equiv.eq_symm_apply]
  constructor
  · intro q
    funext i
    simpa [forkMap] using q i
  · intro q i
    rw [← q]
    simp [forkMap]

end Arrows

end Presieve

end

end Equalizer
