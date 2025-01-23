--import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib

open TensorProduct

section

variable {R M M' N : Type*} [CommRing R] (S : Submonoid R) [AddCommGroup M]
  [AddCommGroup M'] [AddCommGroup N] [Module R M] [Module R M'] [Module R N]
  (g : M →ₗ[R] M') (f : M' →ₗ[R] N)

lemma IsLocalizedModule.injective_of [IsLocalizedModule S g]
    (H : ∀ m, f (g m) = 0 → g m = 0) :
    Function.Injective f :=
  sorry

lemma Algebra.Extension.Cotangent.smul_eq_of {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S]
    {P : Extension R S} (x : P.ker) {g : S} (f : P.Ring) (hf : algebraMap P.Ring S f = g) :
    g • mk x = mk ⟨f * x.val, Ideal.mul_mem_left _ _ x.property⟩ :=
  sorry

end

namespace Algebra.Generators

lemma ofComp_toAlgHom_surjective {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] (P : Generators R S) (Q : Generators S T) :
    Function.Surjective (Q.ofComp P).toAlgHom := by
  intro p
  induction p using MvPolynomial.induction_on with
  | h_C a =>
      use MvPolynomial.rename Sum.inr (P.σ a)
      simp [Algebra.Generators.ofComp, Algebra.Generators.Hom.toAlgHom]
      erw [MvPolynomial.aeval_rename]
      erw [Sum.elim_comp_inr]
      show MvPolynomial.aeval (fun i ↦ IsScalarTower.toAlgHom R _ _ _) _ = _
      rw [← MvPolynomial.comp_aeval]
      simp
  | h_add p q hp hq =>
      obtain ⟨p, rfl⟩ := hp
      obtain ⟨q, rfl⟩ := hq
      use p + q
      simp
  | h_X p i hp =>
      obtain ⟨(p : MvPolynomial (Q.vars ⊕ P.vars) R), rfl⟩ := hp
      use p * MvPolynomial.X (R := R) (Sum.inl i)
      simp [Algebra.Generators.ofComp, Algebra.Generators.Hom.toAlgHom]

lemma map_ofComp_toAlgHom_ker_eq_ker {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] (P : Generators R S) (Q : Generators S T) :
    Ideal.map (Q.ofComp P).toAlgHom (Q.comp P).ker = Q.ker := by
  have := Algebra.Generators.Cotangent.map_ofComp_ker Q P
  rw [SetLike.ext'_iff] at this ⊢
  dsimp at this
  rw [← this]
  ext x
  simp [SetLike.mem_coe, Ideal.mem_map_iff_of_surjective _ (ofComp_toAlgHom_surjective P Q)]

lemma ker_comp_eq_sup {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] (P : Generators R S) (Q : Generators S T) :
    (Q.comp P).ker =
      Ideal.map (Q.toComp P).toAlgHom P.ker ⊔ Ideal.comap (Q.ofComp P).toAlgHom Q.ker := by
  rw [← map_ofComp_toAlgHom_ker_eq_ker P Q]
  rw [Ideal.comap_map_of_surjective _ (ofComp_toAlgHom_surjective P Q)]
  rw [← sup_assoc]
  erw [Algebra.Generators.map_toComp_ker, ← RingHom.ker_eq_comap_bot]
  apply le_antisymm
  · apply le_trans ?_ le_sup_left
    apply le_sup_right
  · simp only [le_sup_left, sup_of_le_left, sup_le_iff, le_refl, and_true]
    intro x hx
    simp only [RingHom.mem_ker] at hx
    rw [Generators.ker_eq_ker_aeval_val, RingHom.mem_ker]
    show algebraMap T T ((MvPolynomial.aeval (Q.comp P).val) x) = 0
    rw [← Generators.Hom.algebraMap_toAlgHom (Q.ofComp P), hx, map_zero]

universe u v uT

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {T : Type uT} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

lemma comp_localizationAway_ker (g : S) [IsLocalization.Away g T] (P : Generators R S)
    (f : P.Ring) (h : algebraMap P.Ring S f = g) :
    ((Generators.localizationAway g).comp P).ker =
      Ideal.map ((Generators.localizationAway (S := T) g).toComp P).toAlgHom P.ker ⊔
        Ideal.span {MvPolynomial.rename Sum.inr f * MvPolynomial.X (Sum.inl ()) - 1} := by
  set Q := Generators.localizationAway (S := T) g
  have : Q.ker = Ideal.map (Q.ofComp P).toAlgHom
      (Ideal.span {MvPolynomial.rename Sum.inr f * MvPolynomial.X (Sum.inl ()) - 1}) := by
    rw [Ideal.map_span]
    simp
    erw [← (Algebra.Presentation.localizationAway T g).span_range_relation_eq_ker]
    congr
    simp [Algebra.Presentation.localizationAway_rels]
    rw [Set.range_unique]
    simp [Generators.Hom.toAlgHom]
    erw [MvPolynomial.aeval_rename]
    erw [Sum.elim_comp_inr]
    rw [← MvPolynomial.algebraMap_eq]
    erw [← IsScalarTower.coe_toAlgHom' R S (MvPolynomial Unit S)]
    erw [← MvPolynomial.comp_aeval_apply]
    rw [← Algebra.Generators.algebraMap_apply]
    rw [h]
    rfl
  rw [ker_comp_eq_sup]
  erw [Algebra.Generators.map_toComp_ker]
  rw [this, Ideal.comap_map_of_surjective _ (ofComp_toAlgHom_surjective P Q)]
  rw [← RingHom.ker_eq_comap_bot]
  rw [← sup_assoc]
  simp [Q]

set_option maxHeartbeats 280000 in
-- `T ⊗[S] (I/I²) → J/J²` is injective.
lemma liftBaseChange_injective (g : S) [IsLocalization.Away g T]
    (P : Generators R S) :
    Function.Injective (LinearMap.liftBaseChange T
      (Extension.Cotangent.map
        ((Presentation.localizationAway g (S := T)).toComp P).toExtensionHom)) := by
  set Q := Generators.localizationAway g (S := T)
  letI : Algebra P.Ring (Q.comp P).Ring := (Q.toComp P).toAlgHom.toAlgebra
  obtain ⟨f, hf⟩ := P.algebraMap_surjective g
  let f' : P.Ring ⧸ P.ker ^ 2 := f
  let π : (Q.comp P).Ring →ₐ[R] Localization.Away f' :=
    MvPolynomial.aeval (R := R) (S₁ := Localization.Away f')
      (Sum.elim
        (fun j : PUnit ↦ IsLocalization.Away.invSelf f')
        (fun i : P.vars ↦ algebraMap P.Ring _ (MvPolynomial.X i)))
  have : IsScalarTower P.Ring (P.Ring ⧸ P.ker ^ 2) (Localization.Away f') := inferInstance
  letI : DistribMulAction (P.Ring ⧸ P.ker ^ 2) (P.Ring ⧸ P.ker ^ 2) := inferInstance
  have hsple : Ideal.span
      {(MvPolynomial.rename Sum.inr) f * MvPolynomial.X (Sum.inl ()) - 1} ≤ RingHom.ker π := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    rw [SetLike.mem_coe, RingHom.mem_ker]
    rw [map_sub, map_one, map_mul]
    simp only [MvPolynomial.aeval_X, Sum.elim_inl, π, Q]
    erw [MvPolynomial.aeval_rename]
    rw [Sum.elim_comp_inr]
    simp_rw [← IsScalarTower.toAlgHom_apply (R := R)]
    rw [← MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_X_left_apply]
    rw [IsScalarTower.coe_toAlgHom']
    rw [IsScalarTower.algebraMap_apply P.Ring (P.Ring ⧸ P.ker ^ 2) (Localization.Away f')]
    rw [Ideal.Quotient.algebraMap_eq]
    rw [IsLocalization.Away.mul_invSelf ((Ideal.Quotient.mk (P.ker ^ 2)) f)
      (S := Localization.Away ((Ideal.Quotient.mk (P.ker ^ 2)) f))]
    simp
  letI : MulZeroClass (Localization.Away f') := inferInstance
  have : (Q.comp P).ker ^ 2 ≤ RingHom.ker π := by
    rw [comp_localizationAway_ker _ _ _ hf]
    rw [sq]
    rw [Ideal.sup_mul]
    rw [Ideal.mul_sup]
    rw [Ideal.mul_sup]
    apply sup_le
    · apply sup_le
      rw [← Ideal.map_mul]
      rw [Ideal.map_le_iff_le_comap]
      rw [← sq]
      intro x hx
      show π (MvPolynomial.rename Sum.inr x) = 0
      dsimp only [π]
      erw [MvPolynomial.aeval_rename]
      rw [Sum.elim_comp_inr]
      simp_rw [← IsScalarTower.toAlgHom_apply (R := R)]
      rw [← MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_X_left_apply]
      rw [IsScalarTower.toAlgHom_apply,
        IsScalarTower.algebraMap_apply P.Ring (P.Ring ⧸ P.ker ^ 2) (Localization.Away f')]
      rw [Ideal.Quotient.algebraMap_eq]
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      rw [map_zero]
      rw [Ideal.mul_le]
      intro x hx y hy
      show π (x * y) = 0
      rw [map_mul]
      have : π y = 0 := hsple hy
      rw [this, mul_zero]
    · apply sup_le
      rw [Ideal.mul_le]
      intro x hx y hy
      show π (x * y) = 0
      rw [map_mul]
      have : π x = 0 := hsple hx
      rw [this, zero_mul]
      rw [Ideal.mul_le]
      intro x hx y hy
      show π (x * y) = 0
      rw [map_mul]
      have : π x = 0 := hsple hx
      rw [this]
      rw [zero_mul]
  have hπ (x : (Q.comp P).Ring) (hx : x ∈ (Q.comp P).ker ^ 2) : π x = 0 := this hx
  apply IsLocalizedModule.injective_of (Submonoid.powers g)
    (TensorProduct.mk S T P.toExtension.Cotangent 1)
  intro x hx
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  --set γ := (Q.toComp P).toExtensionHom.toAlgHom
  simp at hx
  erw [Algebra.Extension.Cotangent.map_mk] at hx
  have : (Q.toComp P).toExtensionHom.toAlgHom x ∈ (Q.comp P).ker ^ 2 := by
    rwa [Extension.Cotangent.mk_eq_zero_iff] at hx
  have hπx : π ((Q.toComp P).toExtensionHom.toAlgHom x) = 0 := hπ _ this
  simp only [π, Generators.toComp, Generators.Hom.toExtensionHom, Extension.Hom.toAlgHom] at this
  dsimp [Hom.toAlgHom] at this
  have : algebraMap P.Ring (Localization.Away f') x.val = 0 := by
    convert hπx
    change _ = MvPolynomial.aeval _ (MvPolynomial.rename Sum.inr x.val)
    rw [MvPolynomial.aeval_rename, Sum.elim_comp_inr]
    simp_rw [← IsScalarTower.toAlgHom_apply (R := R)]
    rw [← MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_X_left_apply]
  rw [IsScalarTower.algebraMap_apply P.Ring (P.Ring ⧸ P.ker ^ 2) (Localization.Away f')] at this
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers f') (Localization.Away f')] at this
  obtain ⟨⟨m, ⟨n, rfl⟩⟩, hm⟩ := this
  dsimp at hm
  rw [IsLocalizedModule.eq_zero_iff (Submonoid.powers g)]
  use ⟨g ^ n, n, rfl⟩
  dsimp [f'] at hm
  rw [← map_pow, ← map_mul] at hm
  simp
  rw [Submonoid.smul_def]
  simp
  erw [Algebra.Extension.Cotangent.smul_eq_of x (g := g ^ n) (f ^ n)]
  · rw [Extension.Cotangent.mk_eq_zero_iff]
    rw [Ideal.Quotient.eq_zero_iff_mem] at hm
    simpa using hm
  · simp at hf
    simp [hf]

end Algebra.Generators
