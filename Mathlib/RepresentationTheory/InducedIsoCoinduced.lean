/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Induced

/-!
# (Co)induced representations of a finite index subgroup

Given a commutative ring `k`, a finite index subgroup `S ≤ G`, and a `k`-linear `S`-representation
`A`, this file defines an isomorphism $Ind_S^G(A) ≅ Coind_S^G(A).$

-/

universe u

namespace Rep

open CategoryTheory Finsupp TensorProduct Representation

variable {k G : Type u} [CommRing k] [Group G] {S : Subgroup G}
  [DecidableRel (QuotientGroup.rightRel S)] (A : Rep k S)

noncomputable def indToCoindAux (g : G) : A →ₗ[k] (G → A) :=
  LinearMap.pi (fun g₁ => if h : (QuotientGroup.rightRel S).r g₁ g then
    A.ρ ⟨g₁ * g⁻¹, by rcases h with ⟨s, rfl⟩; exact mul_inv_cancel_right s.1 g ▸ s.2⟩ else 0)

variable {A}

@[simp]
lemma indToCoindAux_self (g : G) (a : A) :
    indToCoindAux A g a g = a := by
  rw [indToCoindAux, LinearMap.pi_apply, dif_pos]
  · simp [← S.1.one_def]
  · rfl

lemma indToCoindAux_of_not_rel (g g₁ : G) (a : A) (h : ¬(QuotientGroup.rightRel S).r g₁ g) :
    indToCoindAux A g a g₁ = 0 := by
  simp [indToCoindAux, dif_neg h]

@[simp]
lemma indToCoindAux_mul_snd (g g₁ : G) (a : A) (s : S) :
    indToCoindAux A g a (s * g₁) = A.ρ s (indToCoindAux A g a g₁) := by
  rcases em ((QuotientGroup.rightRel S).r g₁ g) with ⟨s₁, rfl⟩ | h
  · simp only [indToCoindAux, LinearMap.pi_apply]
    rw [dif_pos ⟨s * s₁, mul_assoc ..⟩, dif_pos ⟨s₁, rfl⟩]
    simp [S.1.smul_def, smul_eq_mul, mul_assoc, ← S.1.mul_def]
  · rw [indToCoindAux_of_not_rel _ _ _ h, indToCoindAux_of_not_rel, map_zero]
    exact mt (fun ⟨s₁, hs₁⟩ => ⟨s⁻¹ * s₁, by simp_all [S.1.smul_def, mul_assoc]⟩) h

@[simp]
lemma indToCoindAux_mul_fst (g₁ g₂ : G) (a : A) (s : S) :
     indToCoindAux A (s * g₁) (A.ρ s a) g₂ = indToCoindAux A g₁ a g₂ := by
  rcases em ((QuotientGroup.rightRel S).r g₂ g₁) with ⟨s₁, rfl⟩ | h
  · simp only [indToCoindAux, LinearMap.pi_apply]
    rw [dif_pos ⟨s₁ * s⁻¹, by simp [S.1.smul_def, smul_eq_mul, mul_assoc]⟩, dif_pos ⟨s₁, rfl⟩,
      ← Module.End.mul_apply, ← map_mul]
    congr
    ext
    simp [S.1.smul_def, mul_assoc]
  · rw [indToCoindAux_of_not_rel (h := h), indToCoindAux_of_not_rel]
    exact mt (fun ⟨s₁, hs₁⟩ => ⟨s₁ * s, by simp_all [S.1.smul_def, mul_assoc]⟩) h

@[simp]
lemma indToCoindAux_snd_mul_inv (g₁ g₂ g₃ : G) (a : A) :
    indToCoindAux A g₁ a (g₂ * g₃⁻¹) = indToCoindAux A (g₁ * g₃) a g₂ := by
  rcases em ((QuotientGroup.rightRel S).r (g₂ * g₃⁻¹) g₁) with ⟨s, hs⟩ | h
  · simp [S.1.smul_def, mul_assoc, ← eq_mul_inv_iff_mul_eq.1 hs]
  · rw [indToCoindAux_of_not_rel (h := h), indToCoindAux_of_not_rel]
    exact mt (fun ⟨s, hs⟩ => ⟨s, by simpa [S.1.smul_def, eq_mul_inv_iff_mul_eq, mul_assoc]⟩) h

@[simp]
lemma indToCoindAux_fst_mul_inv (g₁ g₂ g₃ : G) (a : A) :
    indToCoindAux A (g₁ * g₂⁻¹) a g₃ = indToCoindAux A g₁ a (g₃ * g₂) := by
  simpa using (indToCoindAux_snd_mul_inv g₁ g₃ g₂⁻¹ a).symm

@[simp]
lemma indToCoindAux_comm {A B : Rep k S} (f : A ⟶ B) (g₁ g₂ : G) (a : A) :
    indToCoindAux B g₁ (f.hom a) g₂ = f.hom (indToCoindAux A g₁ a g₂) := by
  rcases em ((QuotientGroup.rightRel S).r g₂ g₁) with ⟨s, rfl⟩ | h
  · simp [S.1.smul_def, hom_comm_apply]
  · simp [indToCoindAux_of_not_rel (h := h)]

variable (A) in
noncomputable abbrev indToCoind :
    ind S.subtype A →ₗ[k] coind S.subtype A :=
  Representation.Coinvariants.lift _ (TensorProduct.lift <| linearCombination _ fun g =>
    LinearMap.codRestrict _ (indToCoindAux A g) fun _ _ _ => by simp) fun _ => by ext; simp

variable [Fintype (G ⧸ S)]

variable (A) in
@[simps]
noncomputable def coindToInd : coind S.subtype A →ₗ[k] ind S.subtype A where
  toFun f := ∑ g : Quotient (QuotientGroup.rightRel S), Quotient.liftOn g (fun g =>
    IndV.mk S.subtype _ g (f.1 g)) fun g₁ g₂ ⟨s, (hs : _ * _ = _)⟩ =>
      (Submodule.Quotient.eq _).2 <| mem_augmentationSubmodule_of_eq s
        (single g₂ 1 ⊗ₜ[k] f.1 g₂) _ <| by have := f.2 s g₂; simp_all
  map_add' _ _ := by simpa [← Finset.sum_add_distrib, TensorProduct.tmul_add] using
      Finset.sum_congr rfl fun z _ => Quotient.inductionOn z fun _ => by simp
  map_smul' _ _ := by simpa [Finset.smul_sum] using Finset.sum_congr rfl fun z _ =>
    Quotient.inductionOn z fun _ => by simp

omit [DecidableRel (QuotientGroup.rightRel S)] in
lemma coindToInd_of_support_subset_orbit (g : G) (f : coind S.subtype A)
    (hx : f.1.support ⊆ MulAction.orbit S g) :
    coindToInd A f = IndV.mk S.subtype _ g (f.1 g) := by
  rw [coindToInd_apply, Finset.sum_eq_single ⟦g⟧]
  · simp
  · intro b _ hb
    induction b using Quotient.inductionOn with | h b =>
    have : f.1 b = 0 := by
      simp_all only [Function.support_subset_iff, ne_eq, Quotient.eq]
      contrapose! hx
      use b, hx, hb
    simp_all
  · simp

variable (A) in
@[simps! hom_hom_hom inv_hom_hom]
noncomputable def indCoindIso : ind S.subtype A ≅ coind S.subtype A :=
  Action.mkIso ({
    hom := ModuleCat.ofHom <| indToCoind A
    inv := ModuleCat.ofHom <| coindToInd A
    hom_inv_id := by
      ext g a
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
        TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
        LinearMap.coe_restrictScalars]
      rw [coindToInd_of_support_subset_orbit g]
      · simp
      · simp only [Function.support_subset_iff]
        intro x hx
        contrapose! hx
        simpa using indToCoindAux_of_not_rel (h := hx) ..
    inv_hom_id := by
      ext f g
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
        coindToInd_apply A, map_sum, AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
      rw [Finset.sum_eq_single ⟦g⟧]
      · simp
      · intro b _ hb
        induction b using Quotient.inductionOn with | h b =>
        simpa using indToCoindAux_of_not_rel b g (f.1 b) (mt Quotient.sound hb.symm)
      · simp }) fun g => by ext; simp [ModuleCat.endRingEquiv]

variable (k S)

@[simps! hom_app inv_app]
noncomputable def indCoindNatIso : indFunctor k S.subtype ≅ coindFunctor k S.subtype :=
  NatIso.ofComponents (fun _ => indCoindIso _) fun f =>
    Action.hom_ext _ _ <| ModuleCat.hom_ext <| IndV.hom_ext _ _ fun _ => by
      simp only [coindFunctor_obj]; ext; simp

@[simps! counit_app_hom_hom unit_app_hom_hom]
noncomputable def resIndAdjunction : Action.res _ S.subtype ⊣ indFunctor k S.subtype :=
  (resCoindAdjunction k S.subtype).ofNatIsoRight (indCoindNatIso k S).symm

@[simp]
lemma resIndAdjunction_homEquiv_apply
    {B : Rep k G} (f : (Action.res _ S.subtype).obj B ⟶ A) :
    (resIndAdjunction k S).homEquiv _ _ f =
      resCoindHomLEquiv S.subtype B A f ≫ (indCoindIso A).inv := by
  simp only [resIndAdjunction, Adjunction.ofNatIsoRight, resCoindAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv]
  rfl

@[simp]
lemma resIndAdjunction_homEquiv_symm_apply
    {B : Rep k G} (f : B ⟶ (indFunctor k S.subtype).obj A) :
    ((resIndAdjunction k S).homEquiv _ _).symm f =
      (resCoindHomLEquiv S.subtype B A).symm (f ≫ (indCoindIso A).hom) := by
  simp only [resIndAdjunction, Adjunction.ofNatIsoRight, resCoindAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv]
  rfl

@[simps! counit_app_hom_hom unit_app_hom_hom]
noncomputable def coindResAdjunction : coindFunctor k S.subtype ⊣ Action.res _ S.subtype :=
  (indResAdjunction k S.subtype).ofNatIsoLeft (indCoindNatIso k S)

@[simp]
lemma coindResAdjunction_homEquiv_apply {B : Rep k G} (f : coind S.subtype A ⟶ B) :
    (coindResAdjunction k S).homEquiv _ _ f =
      indResHomLEquiv S.subtype A B ((indCoindIso A).hom ≫ f) := by
  simp only [coindResAdjunction, Adjunction.ofNatIsoLeft, indResAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv]
  rfl

@[simp]
lemma coindResAdjunction_homEquiv_symm_apply
    {B : Rep k G} (f : A ⟶ (Action.res _ S.subtype).obj B) :
    ((coindResAdjunction k S).homEquiv _ _).symm f =
      (indCoindIso A).inv ≫ (indResHomLEquiv S.subtype A B).symm f := by
  simp only [coindResAdjunction, Adjunction.ofNatIsoLeft, indResAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv]
  rfl

noncomputable instance : Limits.PreservesLimits (indFunctor k S.subtype) :=
  (resIndAdjunction k S).rightAdjoint_preservesLimits

noncomputable instance : Limits.PreservesColimits (coindFunctor k S.subtype) :=
  (coindResAdjunction k S).leftAdjoint_preservesColimits

end Rep
