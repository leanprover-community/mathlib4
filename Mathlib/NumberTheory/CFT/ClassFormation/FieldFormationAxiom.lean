/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.NumberTheory.CFT.ClassFormation.Basic
public import Mathlib.NumberTheory.CFT.ClassFormation.GroupCohomology
public import Mathlib.NumberTheory.CFT.ClassFormation.Sheaves
public import Mathlib.NumberTheory.CFT.ClassFormation.GaloisCategoryCorrespondence
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.IndexNormal

/-!
# The field formation axiom

-/

@[expose] public section

universe w v u

lemma IsPGroup.exists_subgroup {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {d : ℕ} (hG : Nat.card G = p ^ (d + 1)) :
    ∃ (H : Subgroup G) (_ : H.Normal), Nat.card H = p ^ d := by
  obtain ⟨H, h⟩ := Sylow.exists_subgroup_card_pow_prime (G := G) p (n := d) (by
    rw [hG]
    exact dvd_of_mul_right_eq p (by lia))
  refine ⟨H, Subgroup.normal_of_index_eq_minFac_card ?_, h⟩
  rw [hG, show (p ^ (d + 1)).minFac = p from Nat.Prime.pow_minFac Fact.out (by simp)]
  rw [← H.index_mul_card, h, add_comm, pow_add, pow_one] at hG
  exact mul_left_injective₀ (NeZero.ne _) hG

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [GaloisCategory C]

open PreGaloisCategory GaloisCategory

namespace Formation

variable (Φ : Formation C)

example (X : Type u) [Finite X] :
    Subsingleton X ↔ Nat.card X ≤ 1 := by exact Iff.symm Finite.card_le_one_iff_subsingleton

lemma isZero_H_of_degMap_eq_one
    {Y X : C} [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X]
    (f : Y ⟶ X) [IsGaloisCover f] (n : ℕ) [NeZero n] (hf : degMap f = 1) :
    IsZero (Φ.H f n) := by
  obtain _ | n := n
  · aesop
  · apply Functor.map_isZero
    have : Subsingleton (Aut (Over.mk f)) := by
      rw [← natCard_aut_overMk] at hf
      rw [← Finite.card_le_one_iff_subsingleton, hf]
    apply isZero_groupCohomology_succ_of_subsingleton

lemma exists_fac_of_degMap_eq_pow {Y X : C} [PreGaloisCategory.IsConnected Y]
    [PreGaloisCategory.IsConnected X] (f : Y ⟶ X)
    [IsGaloisCover f] {p d : ℕ} [Fact p.Prime]
    (hf : degMap f = p ^ d) (hd : 2 ≤ d) :
    ∃ (d₁ d₂ : ℕ) (_ : 0 ≠ d₁) (_ : 0 ≠ d₂) (_ : d₁ + d₂ = d)
      (Z : C) (a : Y ⟶ Z) (b : Z ⟶ X) (_ : PreGaloisCategory.IsConnected Z),
        a ≫ b = f ∧ IsGaloisCover a ∧ IsGaloisCover b ∧ degMap a = p ^ d₁ ∧
          degMap b = p ^ d₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := d) (by lia)
  have hf' := natCard_aut_overMk f
  rw [hf] at hf'
  obtain ⟨H, _, h₁⟩ := IsPGroup.exists_subgroup hf'
  obtain ⟨Z, _, a, b, fac, _, _, h₂⟩ := exists_of_normal_subgroup H
  have ha : degMap a = Nat.card H := by
    rw [degMap_eq_card_range_overMap a b f, h₂]
  refine ⟨d, 1, by lia, by simp, by lia, Z, a, b, inferInstance, fac,
    inferInstance, inferInstance, by rw [ha, h₁], ?_⟩
  rw [degMap_comp' a b f, ha, h₁, Nat.succ_eq_add_one,
    pow_add, pow_one] at hf
  rw [pow_one]
  exact mul_right_injective₀ (NeZero.ne _) hf

section

variable {Z Y X : C}
  (f : Z ⟶ Y) (g : Y ⟶ X) (fg : Z ⟶ X)
  [PreGaloisCategory.IsConnected Z] [PreGaloisCategory.IsConnected Y]
  [PreGaloisCategory.IsConnected X]
  [IsGaloisCover f] [IsGaloisCover g] [IsGaloisCover fg]

@[reassoc]
lemma inflation_comp_restriction_eq_zero
    (n : ℕ) [NeZero n] (hfg : f ≫ g = fg := by cat_disch) :
    Φ.inflation f g fg n ≫ Φ.restriction f g fg n = 0 := by
  dsimp only [inflation, restriction]
  rw [← Functor.map_comp, ← groupCohomology.map_comp,
    groupCohomology.map_eq_zero _ _ _ (by aesop), Functor.map_zero]

/-- The short complex consisting of the inflation and the restriction,
in nonzero degree. -/
noncomputable abbrev shortComplexHOfComp
    (n : ℕ) [NeZero n] (hfg : f ≫ g = fg := by cat_disch) :
    ShortComplex Ab.{v} :=
  ShortComplex.mk (Φ.inflation f g fg n) (Φ.restriction f g fg n)
    (Φ.inflation_comp_restriction_eq_zero f g fg n)

noncomputable def repAddEquivQuotientToInvariants (hfg : f ≫ g = fg := by cat_disch) :
    Φ.rep g ≃+ Representation.invariants
        ((Φ.rep fg).ρ.comp (autMapOfIsGaloisCover f g fg).ker.subtype) :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk'
      (fun x ↦ ⟨Φ.sheaf.obj.map (isConnectedHomMk f).op x, by
        simp only [Representation.mem_invariants, MonoidHom.coe_comp, Subgroup.coe_subtype,
          Function.comp_apply, Subtype.forall, MonoidHom.mem_ker]
        intro σ hσ
        dsimp
        rw [autMapOfIsGaloisCover_eq_one_iff' f g fg] at hσ
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
        congr 4
        ext
        simpa⟩) (by simp)) (by
    obtain ⟨h₁, h₂⟩ := (isSheafFor_singleton_iff_of_isGaloisCover ..).1
      (GaloisCategory.isSheafFor_singleton _ Φ.isSheaf_forget (isConnectedHomMk f))
    refine ⟨fun x₁ x₂ hx ↦ h₁ (by simpa using hx), fun ⟨y, hy⟩ ↦ ?_⟩
    obtain ⟨x, rfl⟩ := h₂ y (fun σ ↦ by
      simp only [Representation.mem_invariants, MonoidHom.coe_comp, Subgroup.coe_subtype,
        Function.comp_apply, representation_apply, Subtype.forall, MonoidHom.mem_ker] at hy
      exact hy ((Aut.overMap f g fg) σ⁻¹) (by simp))
    exact ⟨x, rfl⟩)

@[simp]
lemma repAddEquivQuotientToInvariants_apply_val (x : Φ.rep g)
    (hfg : f ≫ g = fg := by cat_disch) :
    ((Φ.repAddEquivQuotientToInvariants f g fg) x).val =
      Φ.sheaf.obj.map (isConnectedHomMk f).op x := rfl

noncomputable def shortComplexHOfCompIso₁ (hfg : f ≫ g = fg := by cat_disch) :
    AddCommGrpCat.of (groupCohomology ((Φ.rep fg).quotientToInvariants
      (autMapOfIsGaloisCover f g fg).ker) 1) ≅
    Φ.H g 1 :=
  (forget₂ _ Ab).mapIso (groupCohomology.mapIso (autQuotientMulEquiv f g fg)
    (AddEquiv.toLinearEquiv (Φ.repAddEquivQuotientToInvariants f g fg).symm (by simp)) (by
      intro σ
      induction σ using QuotientGroup.induction_on with | _ σ
      ext x
      dsimp
      simp only [Representation.subrepresentation_apply]
      obtain ⟨y, hy⟩ := (Φ.repAddEquivQuotientToInvariants f g fg).surjective x
      rw [← hy, AddEquiv.symm_apply_apply]
      apply (Φ.repAddEquivQuotientToInvariants f g fg).injective
      ext
      simp only [AddEquiv.apply_symm_apply, autQuotientMulEquiv_mk f g fg σ,
        LinearMap.coe_restrict_apply, representation_apply,
        Φ.repAddEquivQuotientToInvariants_apply_val f g fg,
        ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      congr 4
      ext
      simp) 1)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
lemma shortComplexHOfCompIso_comm₁₂ (hfg : f ≫ g = fg := by cat_disch) :
    (Φ.shortComplexHOfCompIso₁ f g fg).hom ≫ Φ.inflation f g fg 1 =
      (forget₂ _ Ab).map (groupCohomology.H1InfRes (Φ.rep fg)
        (autMapOfIsGaloisCover f g fg).ker).f := by
  rw [← cancel_epi (Φ.shortComplexHOfCompIso₁ f g fg).inv, Iso.inv_hom_id_assoc]
  dsimp only [shortComplexHOfCompIso₁, Functor.mapIso_inv]
  erw [← Functor.map_comp]
  dsimp only [inflation]
  congr 1
  dsimp [groupCohomology.mapIso, groupCohomology.H1InfRes]
  rw [← groupCohomology.map_comp]
  rfl

@[simps! -isSimp]
noncomputable def shortComplexHOfCompIso₃ (hfg : f ≫ g = fg := by cat_disch) :
    AddCommGrpCat.of
      (groupCohomology ((Φ.rep fg).res (autMapOfIsGaloisCover f g fg).ker.subtype) 1) ≅
    Φ.H f 1 :=
  (forget₂ _ _).mapIso (groupCohomology.mapIso
    (kerAutMapOfIsGaloisCoverMulEquiv f g fg) (.refl _ _) (by cat_disch) _)

@[reassoc]
lemma shortComplexHOfCompIso_comm₂₃ (hfg : f ≫ g = fg := by cat_disch) :
    dsimp% AddCommGrpCat.ofHom (groupCohomology.map (autMapOfIsGaloisCover f g fg).ker.subtype
      (𝟙 (Rep.res (autMapOfIsGaloisCover f g fg).ker.subtype (Φ.rep fg))) 1).hom ≫
    (Φ.shortComplexHOfCompIso₃ f g fg).hom = Φ.restriction f g fg 1 := by
  dsimp only [shortComplexHOfCompIso₃, Functor.mapIso_hom]
  rw [← ModuleCat.forget₂_map, ← Functor.map_comp, groupCohomology.mapIso_hom,
    ← groupCohomology.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
noncomputable def shortComplexHOfCompIso (hfg : f ≫ g = fg := by cat_disch) :
    (groupCohomology.H1InfRes (Φ.rep fg) (autMapOfIsGaloisCover f g fg).ker).map
      (forget₂ _ _) ≅ Φ.shortComplexHOfComp f g fg 1 :=
  ShortComplex.isoMk (Φ.shortComplexHOfCompIso₁ f g fg) (Iso.refl _)
    (Φ.shortComplexHOfCompIso₃ f g fg)
      (by simp [Φ.shortComplexHOfCompIso_comm₁₂ f g fg])
      (by simp [Φ.shortComplexHOfCompIso_comm₂₃ f g fg])

lemma shortComplexHOfComp_one_exact (hfg : f ≫ g = fg := by cat_disch) :
    (Φ.shortComplexHOfComp f g fg 1).Exact :=
  ShortComplex.exact_of_iso (Φ.shortComplexHOfCompIso f g fg)
    (ShortComplex.Exact.map (groupCohomology.H1InfRes_exact ..) _)

lemma isZero_H_one_comp (hf : IsZero (Φ.H f 1)) (hg : IsZero (Φ.H g 1))
    (hfg : f ≫ g = fg := by cat_disch) :
    IsZero (Φ.H fg 1) :=
  (Φ.shortComplexHOfComp_one_exact f g fg).isZero_X₂ (hg.eq_of_src ..) (hf.eq_of_tgt ..)

end

/-- The cohomology in degree `1` of a formation vanishes for Galois covers
of degree the power of a prime `p` when it vanishes for cyclic covers of degree `p`. -/
lemma isZero_H_of_isPGroup {Y X : C}
    [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X]
    (f : Y ⟶ X) [IsGaloisCover f] {p : ℕ} [Fact p.Prime]
    (hf : IsPGroup p (Aut (Over.mk f)))
    (h : ∀ ⦃Y' X' : C⦄ (g : Y' ⟶ X') (a : Y ⟶ Y') (b : X' ⟶ X)
      [PreGaloisCategory.IsConnected Y']
      [PreGaloisCategory.IsConnected X'] [IsGaloisCover g],
        a ≫ g ≫ b = f → degMap g = p → IsZero (Φ.H g 1)) :
    IsZero (Φ.H f 1) := by
  rw [IsPGroup.iff_card, natCard_aut_overMk] at hf
  obtain ⟨n, hn'⟩ := hf
  induction n using Nat.strong_induction_on generalizing Y X with | _ n hn
  obtain _ | _ | n := n
  · exact Φ.isZero_H_of_degMap_eq_one f 1 (by simpa using hn')
  · exact h f (𝟙 Y) (𝟙 X) (by simp) (by simpa using hn')
  · obtain ⟨d₁, d₂, _, _, _, Z, a, b, _, fac, _, _, hd₁, hd₂⟩ :=
      exists_fac_of_degMap_eq_pow f hn' (by simp)
    refine Φ.isZero_H_one_comp a b f ?_ ?_ fac
    · exact hn _ (by lia) a (fun _ _  f' a' b' _ _ _ fac' hf' ↦
        h f' a' (b' ≫ b) (by rw [reassoc_of% fac', fac]) hf') hd₁
    · exact hn _ (by lia) b (fun _ _ f' a' b' _ _ _ fac' hf' ↦
        h f' (a ≫ a') b' (by rw [Category.assoc, fac', fac]) hf') hd₂

lemma isZero_H_of_isZero_H_of_isCyclic {Y X : C}
    [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X]
    (f : Y ⟶ X) [IsGaloisCover f]
    (h : ∀ ⦃Y' X' : C⦄ (g : Y' ⟶ X') (a : Y ⟶ Y') (b : X' ⟶ X)
      [PreGaloisCategory.IsConnected Y']
      [PreGaloisCategory.IsConnected X'] [IsGaloisCover g],
        a ≫ g ≫ b = f → Nat.Prime (degMap g) → IsZero (Φ.H g 1)) :
    IsZero (Φ.H f 1) := by
  sorry

end Formation

/-- Constructor for field formations, assuming that the cohomology vanishes
in degree `1` for cyclic covers of prime degree. -/
abbrev FieldFormation.mk' (Φ : Formation C)
    (h : ∀ ⦃Y X : C⦄ [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X]
      (f : Y ⟶ X) [IsGaloisCover f], Nat.Prime (degMap f) → IsZero (Φ.H f 1)) :
    FieldFormation C where
  toFormation := Φ
  isZero_H_one f _ _ _ :=
    Φ.isZero_H_of_isZero_H_of_isCyclic f (fun _ _ g _ _ _ _ _ _ hg ↦ h g hg)

end CategoryTheory
