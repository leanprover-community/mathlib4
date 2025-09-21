/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.GroupTheory.Index
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Induced

/-!
# (Co)induced representations of a finite index subgroup

Given a commutative ring `k`, a finite index subgroup `S ≤ G`, and a `k`-linear `S`-representation
`A`, this file defines an isomorphism $Ind_S^G(A) ≅ Coind_S^G(A)$. Given `g : G` and `a : A`, the
forward map sends `⟦g ⊗ₜ[k] a⟧` to the function `G → A`supported at `sg` by `ρ(s)(a)` for `s : S`
and which is 0 elsewhere. Meanwhile, the inverse sends `f : G → A` to `∑ᵢ ⟦gᵢ ⊗ₜ[k] f(gᵢ)⟧` for
`1 ≤ i ≤ n`, where `g₁, ..., gₙ` is a set of right coset representatives of `S`.

## Main definitions

* `Rep.indCoindIso A`: An isomorphism `Ind_S^G(A) ≅ Coind_S^G(A)` for a finite index subgroup
  `S ≤ G` and a `k`-linear `S`-representation `A`.
* `Rep.indCoindNatIso k S`: A natural isomorphism between the functors `Ind_S^G` and `Coind_S^G`.

-/

universe u

namespace Rep

open CategoryTheory Finsupp TensorProduct Representation

variable {k G : Type u} [CommRing k] [Group G] {S : Subgroup G}
  [DecidableRel (QuotientGroup.rightRel S)] (A : Rep k S)

/-- Let `S ≤ G` be a subgroup and `(A, ρ)` a `k`-linear `S`-representation. Then given `g : G` and
`a : A`, this is the function `G → A` sending `sg` to `ρ(s)(a)` for all `s : S` and everything else
to 0. -/
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
    simp [S.1.smul_def, mul_assoc, ← S.1.mul_def]
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
    simp [Subtype.ext_iff, S.1.smul_def, mul_assoc]
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

lemma indToCoindAux_comm {A B : Rep k S} (f : A ⟶ B) (g₁ g₂ : G) (a : A) :
    indToCoindAux B g₁ (f.hom a) g₂ = f.hom (indToCoindAux A g₁ a g₂) := by
  rcases em ((QuotientGroup.rightRel S).r g₂ g₁) with ⟨s, rfl⟩ | h
  · simp [S.1.smul_def, hom_comm_apply]
  · simp [indToCoindAux_of_not_rel (h := h)]

variable (A) in
/-- Let `S ≤ G` be a subgroup and `A` a `k`-linear `S`-representation. This is the `k`-linear map
`Ind_S^G(A) →ₗ[k] Coind_S^G(A)` sending `(⟦g ⊗ₜ[k] a⟧, sg) ↦ ρ(s)(a)`. -/
noncomputable abbrev indToCoind :
    ind S.subtype A →ₗ[k] coind S.subtype A :=
  Representation.Coinvariants.lift _ (TensorProduct.lift <| linearCombination _ fun g =>
    LinearMap.codRestrict _ (indToCoindAux A g) fun _ _ _ => by simp) fun _ => by ext; simp

variable [S.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable (A) in
/-- Let `S ≤ G` be a finite index subgroup, `g₁, ..., gₙ` a set of right coset representatives of
`S`, and `A` a `k`-linear `S`-representation. This is the `k`-linear map
`Coind_S^G(A) →ₗ[k] Ind_S^G(A)` sending `f : G → A` to `∑ᵢ ⟦gᵢ ⊗ₜ[k] f(gᵢ)⟧` for `1 ≤ i ≤ n`. -/
@[simps]
noncomputable def coindToInd : coind S.subtype A →ₗ[k] ind S.subtype A where
  toFun f := ∑ g : Quotient (QuotientGroup.rightRel S), Quotient.liftOn g (fun g =>
    IndV.mk S.subtype _ g (f.1 g)) fun g₁ g₂ ⟨s, (hs : _ * _ = _)⟩ =>
      (Submodule.Quotient.eq _).2 <| Coinvariants.mem_ker_of_eq s
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

variable (A)

/-- Let `S ≤ G` be a finite index subgroup, `g₁, ..., gₙ` a set of right coset representatives of
`S`, and `A` a `k`-linear `S`-representation. This is an isomorphism `Ind_S^G(A) ≅ Coind_S^G(A)`.
The forward map sends `(⟦g ⊗ₜ[k] a⟧, sg) ↦ ρ(s)(a)`, and the inverse sends `f : G → A` to
`∑ᵢ ⟦gᵢ ⊗ₜ[k] f(gᵢ)⟧` for `1 ≤ i ≤ n`. -/
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
      · simp })
    fun _ => by ext; simp [ModuleCat.endRingEquiv]

variable (k S)

/-- Given a finite index subgroup `S ≤ G`, this is a natural isomorphism between the `Ind_S^G` and
`Coind_G^S` functors `Rep k S ⥤ Rep k G`. -/
@[simps! hom_app inv_app]
noncomputable def indCoindNatIso : indFunctor k S.subtype ≅ coindFunctor k S.subtype :=
  NatIso.ofComponents (fun _ => indCoindIso _) fun f => by
    simp only [indFunctor_obj, coindFunctor_obj]; ext; simp [indToCoindAux_comm]

/-- Given a finite index subgroup `S ≤ G`, `Ind_S^G` is right adjoint to the restriction functor
`Res k G ⥤ Res k S`, since it is naturally isomorphic to `Coind_S^G`. -/
noncomputable def resIndAdjunction : Action.res _ S.subtype ⊣ indFunctor k S.subtype :=
  (resCoindAdjunction k S.subtype).ofNatIsoRight (indCoindNatIso k S).symm

noncomputable instance : (indFunctor k S.subtype).IsRightAdjoint :=
  (resIndAdjunction k S).isRightAdjoint

variable {k S}

@[simp]
lemma resIndAdjunction_counit_app :
    (resIndAdjunction k S).counit.app A = (Action.res _ S.subtype).map (indCoindIso A).hom ≫
      (resCoindAdjunction k S.subtype).counit.app A := rfl

@[simp]
lemma resIndAdjunction_unit_app (B : Rep k G) :
    (resIndAdjunction k S).unit.app B = (resCoindAdjunction k S.subtype).unit.app B ≫
      (indCoindIso ((Action.res _ S.subtype).obj B)).inv := rfl

lemma resIndAdjunction_homEquiv_apply
    {B : Rep k G} (f : (Action.res _ S.subtype).obj B ⟶ A) :
    (resIndAdjunction k S).homEquiv _ _ f =
      resCoindHomEquiv S.subtype B A f ≫ (indCoindIso A).inv := by
  simp only [resIndAdjunction, Adjunction.ofNatIsoRight, resCoindAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv]
  rfl

lemma resIndAdjunction_homEquiv_symm_apply
    {B : Rep k G} (f : B ⟶ (indFunctor k S.subtype).obj A) :
    ((resIndAdjunction k S).homEquiv _ _).symm f =
      (resCoindHomEquiv S.subtype B A).symm (f ≫ (indCoindIso A).hom) := by
  simp only [resIndAdjunction, Adjunction.ofNatIsoRight, resCoindAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv]
  rfl

variable (k S) in
/-- Given a finite index subgroup `S ≤ G`, `Coind_S^G` is left adjoint to the restriction functor
`Res k G ⥤ Res k S`, since it is naturally isomorphic to `Ind_S^G`. -/
noncomputable def coindResAdjunction : coindFunctor k S.subtype ⊣ Action.res _ S.subtype :=
  (indResAdjunction k S.subtype).ofNatIsoLeft (indCoindNatIso k S)

noncomputable instance : (coindFunctor k S.subtype).IsLeftAdjoint :=
  (coindResAdjunction k S).isLeftAdjoint

@[simp]
lemma coindResAdjunction_counit_app (B : Rep k G) :
    (coindResAdjunction k S).counit.app B = (indCoindIso <| (Action.res _ S.subtype).obj B).inv ≫
      (indResAdjunction k S.subtype).counit.app B := by
  simp [coindResAdjunction, Adjunction.ofNatIsoLeft, Adjunction.equivHomsetLeftOfNatIso,
    indResAdjunction]

@[simp]
lemma coindResAdjunction_unit_app :
    (coindResAdjunction k S).unit.app A = (indResAdjunction k S.subtype).unit.app A ≫
      (Action.res _ S.subtype).map (indCoindIso A).hom := by
  ext
  simp [coindResAdjunction, Adjunction.ofNatIsoLeft, Adjunction.equivHomsetLeftOfNatIso,
    indResAdjunction]

lemma coindResAdjunction_homEquiv_apply {B : Rep k G} (f : coind S.subtype A ⟶ B) :
    (coindResAdjunction k S).homEquiv _ _ f =
      indResHomEquiv S.subtype A B ((indCoindIso A).hom ≫ f) := by
  simp only [coindResAdjunction, Adjunction.ofNatIsoLeft, indResAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv]
  rfl

lemma coindResAdjunction_homEquiv_symm_apply
    {B : Rep k G} (f : A ⟶ (Action.res _ S.subtype).obj B) :
    ((coindResAdjunction k S).homEquiv _ _).symm f =
      (indCoindIso A).inv ≫ (indResHomEquiv S.subtype A B).symm f := by
  simp only [coindResAdjunction, Adjunction.ofNatIsoLeft, indResAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv]
  rfl

end Rep
