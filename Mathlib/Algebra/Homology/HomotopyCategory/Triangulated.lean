import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.ArrowTwo

open CategoryTheory Category Limits Pretriangulated

variable {C : Type _} [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {X₁ X₂ X₃ : CochainComplex C ℤ} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)

namespace CochainComplex

namespace MappingCone

open HomComplex

@[simps! mor₁ mor₂ mor₃ obj₁ obj₂ obj₃]
noncomputable def mappingConeCompTriangle : Triangle (CochainComplex C ℤ) :=
  Triangle.mk (map' f (f ≫ g) (𝟙 X₁) g (by rw [id_comp]))
    (map' (f ≫ g) g f (𝟙 X₃) (by rw [comp_id]))
    (triangleδ g ≫ (inr f)⟦1⟧')

lemma mappingConeCompTriangle_mor₃_naturality {Y₁ Y₂ Y₃ : CochainComplex C ℤ} (f' : Y₁ ⟶ Y₂)
    (g' : Y₂ ⟶ Y₃) (φ : Arrow₂.mk f g ⟶ Arrow₂.mk f' g') :
    map' g g' φ.τ₁ φ.τ₂ φ.commg.symm ≫ (mappingConeCompTriangle f' g').mor₃ =
      (mappingConeCompTriangle f g).mor₃ ≫ (map' f f' φ.τ₀ φ.τ₁ φ.commf.symm)⟦(1 : ℤ)⟧' := by
  ext n
  simp [from_ext_iff _ _ _ (n+1) rfl, map']

namespace MappingConeCompHomotopyEquiv

@[simp]
noncomputable def hom : mappingCone g ⟶ mappingCone (mappingConeCompTriangle f g).mor₁ :=
  lift _ (descCocycle g (Cochain.ofHom (inr f)) 0 (zero_add 1) (by simp))
    (descCochain _ 0 (Cochain.ofHom (inr (f ≫ g))) (neg_add_self 1)) (by
    ext ⟨p, _, rfl⟩
    dsimp [mappingConeCompTriangle, map']
    simp [from_ext_iff _ _ _ _ rfl,
      inl_v_d_assoc _ (p+1) p (p+2) (by linarith) (by linarith)])

@[simp]
noncomputable def inv : mappingCone (mappingConeCompTriangle f g).mor₁ ⟶ mappingCone g :=
  desc _ ((snd f).comp (inl g) (zero_add (-1)))
    (desc _ ((Cochain.ofHom f).comp (inl g) (zero_add (-1))) (inr g) (by simp)) (by
      ext p
      dsimp [map']
      rw [from_ext_iff _ _ _ (p+1) rfl, to_ext_iff _ _ _ (p+1) rfl]
      simp [δ_zero_cochain_comp, ε_neg,
        Cochain.comp_v _ _ (add_neg_self 1) p (p+1) p (by linarith) (by linarith)])


lemma hom_inv_id : hom f g ≫ inv f g = 𝟙 _ := by
  ext n
  dsimp [map']
  simp [lift_desc_f _ _ _ _ _ _ _ n (n+1) rfl,
    from_ext_iff _ _ _ (n+1) rfl]

open CochainComplex.HomComplex

set_option maxHeartbeats 400000 in
noncomputable def homotopyInvHomId : Homotopy (inv f g ≫ hom f g) (𝟙 _) :=
  (Cochain.equivHomotopy _ _).symm (by
    refine' ⟨-((snd _).comp ((fst (f ≫ g)).1.comp ((inl f).comp (inl _) (by linarith))
      (show 1 + (-2) = -1 by linarith)) (zero_add (-1))), _⟩
    simp only [δ_neg, δ_zero_cochain_comp, ε_neg, ε_1, one_smul, neg_smul,
      δ_comp _ _ (show 1+(-2) = -1 by linarith) 2 (-1) 0 (by linarith) (by linarith) (by linarith),
      δ_comp _ _ (show (-1)+(-1) = -2 by linarith) 0 0 (-1) (by linarith)
        (by linarith) (by linarith),
      ε_even 2 ⟨1, by linarith⟩, δ_inl, δ_snd, Cocycle.δ_eq_zero, Cochain.zero_comp,
      add_zero, Cochain.neg_comp, neg_neg]
    ext n
    rw [from_ext_iff _ _ _ (n+1) rfl, from_ext_iff _ _ _ (n+1) rfl,
      from_ext_iff _ _ _ (n+2) (show n+1+1 = n+2 by linarith)]
    simp only [to_ext_iff _ _ _ (n+1) rfl,
      map', Cochain.comp_v _ _ (add_neg_self 1) n (n + 1) n (by linarith) (by linarith),
      Cochain.comp_v _ _ (show 1 + -2 = -1 by linarith) (n + 1) (n + 2) n
        (by linarith) (by linarith),
      Cochain.comp_v _ _ (show (-1) + -1 = -2 by linarith) (n + 2) (n + 1) n
        (by linarith) (by linarith), Cochain.ofHom_v, mappingConeCompTriangle_obj₁,
      mappingConeCompTriangle_obj₂, mappingConeCompTriangle_mor₁, inv, hom,
      Cochain.ofHom_comp, ofHom_desc, ofHom_lift, descCocycle_coe, Cocycle.coe_zero,
      Cochain.zero_cochain_comp_v, inl_v_descCochain_v_assoc, assoc, inl_v_snd_v_assoc,
      zero_comp, Cochain.id_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      Cochain.comp_add, Cochain.comp_neg, Cochain.comp_assoc_of_second_is_zero_cochain,
      neg_add_rev, neg_neg, Cochain.add_v, Cochain.neg_v, Cochain.comp_zero_cochain_v,
      HomologicalComplex.id_f, Preadditive.comp_add, Preadditive.comp_neg, inl_v_fst_v_assoc,
      neg_zero, add_zero, comp_id, add_left_neg, and_self, inr_f_snd_v_assoc,
      liftCochain_v_fst_v, inl_v_descCochain_v, inr_f_descCochain_v_assoc,
      inr_f_fst_v_assoc, comp_zero, zero_add, inl_v_fst_v, liftCochain_v_snd_v, Cochain.zero_v,
      inl_v_snd_v, neg_add_cancel_right, inr_f_descCochain_v, inr_f_fst_v, inr_f_snd_v])

end MappingConeCompHomotopyEquiv

@[simps]
noncomputable def mappingConeCompHomotopyEquiv : HomotopyEquiv (mappingCone g)
    (mappingCone (mappingConeCompTriangle f g).mor₁) where
  hom := MappingConeCompHomotopyEquiv.hom f g
  inv := MappingConeCompHomotopyEquiv.inv f g
  homotopyHomInvId := Homotopy.ofEq (MappingConeCompHomotopyEquiv.hom_inv_id f g)
  homotopyInvHomId := MappingConeCompHomotopyEquiv.homotopyInvHomId f g

lemma mappingConeCompHomotopyEquiv_comm₁ :
    inr (mappingConeCompTriangle f g).mor₁ ≫
      (mappingConeCompHomotopyEquiv f g).inv = (mappingConeCompTriangle f g).mor₂ := by
  dsimp [map', MappingConeCompHomotopyEquiv.inv]
  simp

lemma mappingConeCompHomotopyEquiv_comm₂ :
    (mappingConeCompHomotopyEquiv f g).hom ≫ triangleδ (mappingConeCompTriangle f g).mor₁ =
      (mappingConeCompTriangle f g).mor₃ := by
  ext n
  dsimp [map']
  simp [lift_f _ _ _ _ _ (n+1) rfl, from_ext_iff _ _ _ (n+1) rfl]

end MappingCone

end CochainComplex

namespace HomotopyCategory

set_option maxHeartbeats 400000 in
lemma mappingConeCompTriangle_distinguished :
  (quotient _ _).mapTriangle.obj (CochainComplex.MappingCone.mappingConeCompTriangle f g) ∈
    distTriang (HomotopyCategory C (ComplexShape.up ℤ)) := by
  refine' ⟨_, _, (CochainComplex.MappingCone.mappingConeCompTriangle f g).mor₁, ⟨_⟩⟩
  refine' Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (isoOfHomotopyEquiv
    (CochainComplex.MappingCone.mappingConeCompHomotopyEquiv f g)) _ _ _
  . dsimp
    simp
  . rw [← cancel_mono (isoOfHomotopyEquiv
      (CochainComplex.MappingCone.mappingConeCompHomotopyEquiv f g)).inv,
      assoc, Iso.hom_inv_id, comp_id, Iso.refl_hom, id_comp,
      isoOfHomotopyEquiv_inv]
    simp only [Functor.mapTriangle_obj, Triangle.mk_mor₂]
    rw [← CochainComplex.MappingCone.mappingConeCompHomotopyEquiv_comm₁]
    simp
  . simp only [Functor.mapTriangle_obj, Triangle.mk_mor₃,
      ← CochainComplex.MappingCone.mappingConeCompHomotopyEquiv_comm₂ f g]
    simp

noncomputable instance : IsTriangulated (HomotopyCategory C (ComplexShape.up ℤ)) :=
  IsTriangulated.mk' (by
    rintro ⟨X₁ : CochainComplex C ℤ⟩ ⟨X₂ : CochainComplex C ℤ⟩ ⟨X₃ : CochainComplex C ℤ⟩ u₁₂' u₂₃'
    obtain ⟨u₁₂, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective u₁₂'
    obtain ⟨u₂₃, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective u₂₃'
    refine' ⟨_, _, _, _, _, _, _, _,
      Iso.refl _, Iso.refl _, Iso.refl _, by dsimp ; simp, by dsimp ; simp,
        _, _, mappingCone_triangle_distinguished u₁₂,
        _, _, mappingCone_triangle_distinguished u₂₃,
        _, _, mappingCone_triangle_distinguished (u₁₂ ≫ u₂₃), ⟨_⟩⟩
    let α := CochainComplex.MappingCone.triangleMap' u₁₂ (u₁₂ ≫ u₂₃) (𝟙 X₁) u₂₃ (by rw [id_comp])
    let β := CochainComplex.MappingCone.triangleMap' (u₁₂ ≫ u₂₃) u₂₃ u₁₂ (𝟙 X₃) (by rw [comp_id])
    apply Triangulated.Octahedron.mk ((HomotopyCategory.quotient _ _).map α.hom₃)
      ((HomotopyCategory.quotient _ _).map β.hom₃)
      ((quotient C (ComplexShape.up ℤ)).mapTriangle.map α).comm₂
      (((quotient C (ComplexShape.up ℤ)).mapTriangle.map α).comm₃.symm.trans
        (Eq.trans (by congr ; dsimp ; simp) (comp_id _)))
      (((HomotopyCategory.quotient _ _).mapTriangle.map β).comm₂.trans (id_comp _))
      (((HomotopyCategory.quotient _ _).mapTriangle.map β).comm₃)
    refine' isomorphic_distinguished _ (mappingConeCompTriangle_distinguished u₁₂ u₂₃) _ _
    refine' Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) _ _ _
    . dsimp
      simp
    . dsimp
      simp
    . dsimp
      erw [CategoryTheory.Functor.map_id, comp_id, id_comp, Functor.map_comp, assoc, assoc,
        ← NatTrans.naturality]
      rfl)

end HomotopyCategory
