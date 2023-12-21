import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.RingTheory.Artinian
import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts
import Mathlib.Algebra.Category.Ring.Constructions

open TopologicalSpace AlgebraicGeometry Opposite CategoryTheory

universe u
variable (R : Type u) [CommRing R] [IsArtinianRing R]

namespace IsArtinianRing

instance : Finite (PrimeSpectrum R) := @Finite.of_equiv _ {I : Ideal R | I.IsPrime}
  (Set.finite_coe_iff.mpr IsArtinianRing.primeSpectrum_finite)
  ⟨fun x ↦ ⟨x.1, x.2⟩, fun x ↦ ⟨x.1, x.2⟩, fun _ ↦ by aesop, fun _ ↦ by aesop⟩

noncomputable instance : Fintype (PrimeSpectrum R) :=
  Classical.choice <| finite_iff_nonempty_fintype (PrimeSpectrum R) |>.mp inferInstance

instance : T1Space (PrimeSpectrum R) where
  t1 p := PrimeSpectrum.isClosed_singleton_iff_isMaximal _ |>.mpr (isMaximal_of_isPrime p.asIdeal)

instance : DiscreteTopology (PrimeSpectrum R) := discrete_of_t1_of_finite

variable {R}
def openCover (i : PrimeSpectrum R) : Opens (PrimeSpectrum R) :=
  ⟨{i}, by continuity⟩

lemma openCover.pairwiseDisjoint (i j : PrimeSpectrum R) (hij : i ≠ j) :
    openCover i ⊓ openCover j = ⊥ := by
  ext p
  simp only [ge_iff_le, Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, Opens.coe_bot,
    Set.mem_empty_iff_false, iff_false, not_and]
  intro hp
  rw [Set.mem_singleton_iff.mp hp]
  contrapose! hij
  ext1
  rw [Set.mem_singleton_iff.mp hij]

variable (R) in
lemma openCover.is_cover : ⨆ (i : PrimeSpectrum R), openCover i = ⊤ :=
  eq_top_iff.mpr <| fun p _ ↦ by simpa using ⟨p, Set.mem_singleton _⟩

instance (i : PrimeSpectrum R) : Unique (openCover i) where
  default := ⟨i, by aesop⟩
  uniq p := Subtype.ext <| by rw [Set.mem_singleton_iff.mp p.2]; rfl

noncomputable def sectionsOnOpenCover (i : PrimeSpectrum R) :
    (Spec.structureSheaf R).presheaf.obj (op <| openCover i) ≅
    CommRingCat.of <| Localization.AtPrime i.asIdeal :=
  let e (x : openCover i) :  Localization.AtPrime i.asIdeal ≃+* Localization.AtPrime x.1.asIdeal :=
    IsLocalization.ringEquivOfRingEquiv
      (S := Localization.AtPrime i.asIdeal)
      (Q := Localization.AtPrime x.1.asIdeal)
      (M := i.asIdeal.primeCompl) (T := x.1.asIdeal.primeCompl) (RingEquiv.refl R) <| by
      rw [Set.mem_singleton_iff.mp x.2]; simp
  RingEquiv.toCommRingCatIso
  { toFun := fun f ↦ f.1 ⟨i, by aesop⟩
    invFun := fun q ↦ ⟨fun x ↦ e _ q, fun x ↦ by
        simp_rw [Set.mem_singleton_iff.mp x.2]
        induction' q using Localization.induction_on with d
        rcases d with ⟨r, ⟨s, hs⟩⟩
        refine ⟨(openCover i), Set.mem_singleton _, 𝟙 _, r, s, fun p ↦ ⟨?_, ?_⟩⟩
        · rw [Set.mem_singleton_iff.mp p.2]; exact hs
        · dsimp
          rw [Localization.mk_eq_mk', IsLocalization.map_mk']
          erw [IsLocalization.mk'_spec]
          rfl⟩
    left_inv := by
      rintro ⟨f, hf⟩
      simp only [unop_op, StructureSheaf.isLocallyFraction_pred, id_eq,
        IsLocalization.ringEquivOfRingEquiv_apply, RingEquiv.coe_ringHom_refl]
      refine Subtype.ext <| funext fun (x : openCover i) ↦ ?_
      simp only [unop_op]
      have eq1 : x = (⟨i, by aesop⟩ : openCover i) := Subsingleton.elim _ _
      rw [eq1]
      simp only [IsLocalization.map_id]
    right_inv := by
      intro p
      simp only [unop_op, id_eq, IsLocalization.ringEquivOfRingEquiv_apply,
        RingEquiv.coe_ringHom_refl, IsLocalization.map_id]
    map_mul' := fun x y ↦ by
      simp only [unop_op, StructureSheaf.isLocallyFraction_pred, id_eq]
      rfl
    map_add' := fun x y ↦ by
      simp only [unop_op, StructureSheaf.isLocallyFraction_pred, id_eq]
      rfl }

variable (R) in
lemma globalSectionsEquivProd : Nonempty <|
    (Spec.structureSheaf R).presheaf.obj (op ⊤) ≅
    ∏ fun (i : PrimeSpectrum R) ↦ CommRingCat.of (Localization.AtPrime i.asIdeal) := by
  refine (Spec.structureSheaf R).sections_on_disjoint_opens_iso_product (openCover (R := R))
    openCover.pairwiseDisjoint |>.map fun e ↦ ?_ ≪≫ e ≪≫ ?_
  · fconstructor
    · exact (Spec.structureSheaf R).presheaf.map (Quiver.Hom.op <| homOfLE le_top)
    · exact (Spec.structureSheaf R).presheaf.map
        (Quiver.Hom.op <| homOfLE <| eq_top_iff.mp <| openCover.is_cover R)
    · aesop_cat
    · aesop_cat
  · fconstructor
    · exact Limits.Pi.map fun p ↦ (sectionsOnOpenCover p).hom
    · exact Limits.Pi.map fun p ↦ (sectionsOnOpenCover p).inv
    · aesop_cat
    · aesop_cat

lemma equivProdLocalization' : Nonempty <|
    R ≃+* ((i : PrimeSpectrum R) → Localization.AtPrime i.asIdeal) := by
  refine globalSectionsEquivProd R |>.map fun e ↦
    RingEquiv.ofHomInv (?_ : R →+* ((i : PrimeSpectrum R) → Localization.AtPrime i.asIdeal))
      (?_ : ((i : PrimeSpectrum R) → Localization.AtPrime i.asIdeal) →+* R) ?_ ?_
  · exact (CommRingCat.piIsoPi _ |>.hom)
      |>.comp e.hom |>.comp (StructureSheaf.globalSectionsIso R).hom
  · exact (StructureSheaf.globalSectionsIso R).inv |>.comp e.inv |>.comp
      (CommRingCat.piIsoPi
        fun (i : PrimeSpectrum R) ↦ CommRingCat.of <| Localization.AtPrime i.asIdeal).inv
  · refine RingHom.ext fun r ↦ ?_
    simp only [CommRingCat.coe_of, StructureSheaf.globalSectionsIso_inv, RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply, RingHom.id_apply]
    erw [← comp_apply, ← comp_apply, ← comp_apply, ← comp_apply, ← comp_apply,
      Iso.hom_inv_id_assoc, e.hom_inv_id_assoc, Iso.hom_inv_id]
    rfl
  · refine RingHom.ext fun r ↦ ?_
    simp only [CommRingCat.coe_of, StructureSheaf.globalSectionsIso_inv, RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply, RingHom.id_apply]
    erw [← comp_apply, ← comp_apply, ← comp_apply, ← comp_apply, ← comp_apply,
      (StructureSheaf.globalSectionsIso R).inv_hom_id_assoc, e.inv_hom_id_assoc, Iso.inv_hom_id]
    rfl

/--
If $R$ is an artinian ring, then $R \cong \prod_{\mathfrak{p}}R_{\mathfrak{p}}$
-/
noncomputable def equivProdLocalization :
    R ≃+* ((i : PrimeSpectrum R) → Localization.AtPrime i.asIdeal) :=
  Classical.choice equivProdLocalization'


section local_ring

instance isNotherianRing_of_local [LocalRing R] : IsNoetherianRing R := sorry

end local_ring

instance : IsNoetherian R R :=
  @isNoetherianRing_of_ringEquiv (f := equivProdLocalization.symm) <| IsNoetherianRing.Pi _

end IsArtinianRing
