import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Presentation

open TensorProduct

section

variable {R M M' N : Type*} [CommRing R] (S : Submonoid R) [AddCommGroup M]
  [AddCommGroup M'] [AddCommGroup N] [Module R M] [Module R M'] [Module R N]
  (g : M →ₗ[R] M') (f : M' →ₗ[R] N)

lemma IsLocalizedModule.injective_of_map_eq {R M M' N : Type*} [CommSemiring R] (S : Submonoid R)
  [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N] [Module R M] [Module R M'] [Module R N]
  (g : M →ₗ[R] M') (f : M' →ₗ[R] N)
  [IsLocalizedModule S g]
    (H : ∀ {x y}, f (g x) = f (g y) → g x = g y) :
    Function.Injective f := by
  intro a b hab
  obtain ⟨⟨x, m⟩, (hxm : m • a = g x)⟩ := IsLocalizedModule.surj S g a
  obtain ⟨⟨y, n⟩, (hym : n • b = g y)⟩ := IsLocalizedModule.surj S g b
  suffices h : f (g (n.val • x)) = f (g (m.val • y)) by
    apply H at h
    rw [map_smul, map_smul] at h
    rwa [← IsLocalizedModule.smul_inj g (n * m), mul_smul, mul_comm, mul_smul, hxm, hym]
  simp [← hxm, ← hym, hab, ← S.smul_def, ← mul_smul, mul_comm, ← mul_smul]

lemma IsLocalizedModule.injective_of_map_zero [IsLocalizedModule S g]
    (H : ∀ m, f (g m) = 0 → g m = 0) :
    Function.Injective f := by
  refine IsLocalizedModule.injective_of_map_eq S g _ (fun hxy ↦ ?_)
  rw [← sub_eq_zero, ← map_sub]
  apply H
  simpa [sub_eq_zero]

lemma Algebra.Extension.Cotangent.smul_mk_eq_mk_smul {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S]
    {P : Extension R S} (x : P.ker) {g : S} (f : P.Ring) (hf : algebraMap P.Ring S f = g) :
    g • mk x = mk (f • x) := by
  ext
  simp only [val_smul, val_mk, map_smul, val_smul']
  rw [← sub_eq_zero, ← sub_smul]
  apply smul_eq_zero_of_mem
  simp [hf]

end

namespace Algebra.Generators

lemma toAlgHom_ofComp_surjective {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] (P : Generators R S) (Q : Generators S T) :
    Function.Surjective (Q.ofComp P).toAlgHom := by
  intro p
  induction p using MvPolynomial.induction_on with
  | h_C a =>
      use MvPolynomial.rename Sum.inr (P.σ a)
      simp only [Hom.toAlgHom, ofComp, Generators.comp, MvPolynomial.aeval_rename,
        Sum.elim_comp_inr]
      simp_rw [Function.comp_def, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.toAlgHom_apply R,
        ← MvPolynomial.comp_aeval]
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
  simp only [SetLike.ext'_iff, Submodule.map_coe, Submodule.coe_restrictScalars] at this ⊢
  rw [← this]
  ext x
  simp [SetLike.mem_coe, Ideal.mem_map_iff_of_surjective _ (toAlgHom_ofComp_surjective P Q)]

lemma ker_comp_eq_sup {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] (P : Generators R S) (Q : Generators S T) :
    (Q.comp P).ker =
      Ideal.map (Q.toComp P).toAlgHom P.ker ⊔ Ideal.comap (Q.ofComp P).toAlgHom Q.ker := by
  rw [← map_ofComp_toAlgHom_ker_eq_ker P Q,
    Ideal.comap_map_of_surjective _ (toAlgHom_ofComp_surjective P Q)]
  rw [← sup_assoc, Algebra.Generators.map_toComp_ker, ← RingHom.ker_eq_comap_bot]
  apply le_antisymm (le_trans le_sup_right le_sup_left)
  simp only [le_sup_left, sup_of_le_left, sup_le_iff, le_refl, and_true]
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
  have : Q.ker = Ideal.span {MvPolynomial.C g * MvPolynomial.X () - 1} := by
    convert (Algebra.Presentation.localizationAway T g).span_range_relation_eq_ker.symm
    simp [Presentation.localizationAway]
  have : Q.ker = Ideal.map (Q.ofComp P).toAlgHom
      (Ideal.span {MvPolynomial.rename Sum.inr f * MvPolynomial.X (Sum.inl ()) - 1}) := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_mul, map_one, this]
    simp only [Hom.toAlgHom, MvPolynomial.aeval_X, ofComp_val, Sum.elim_inl, sub_left_inj,
      Generators.comp, Generators.ofComp, Generators.localizationAway, Q]
    rw [MvPolynomial.aeval_rename, Sum.elim_comp_inr]
    simp_rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.coe_toAlgHom' R S (MvPolynomial Unit S)]
    rw [Function.comp_def, ← MvPolynomial.comp_aeval_apply, ← Algebra.Generators.algebraMap_apply,
      h]
  rw [ker_comp_eq_sup, Algebra.Generators.map_toComp_ker, this,
    Ideal.comap_map_of_surjective _ (toAlgHom_ofComp_surjective P Q), ← RingHom.ker_eq_comap_bot,
    ← sup_assoc]
  simp [Q]

section

open MvPolynomial

variable (g : S) [IsLocalization.Away g T] (P : Generators R S)

variable (T) in
private noncomputable
def aux : ((Generators.localizationAway g (S := T)).comp P).Ring →ₐ[R]
      Localization.Away (Ideal.Quotient.mk (P.ker ^ 2) (P.σ g)) :=
  aeval (R := R) (S₁ := Localization.Away _)
    (Sum.elim
      (fun _ ↦ IsLocalization.Away.invSelf <| (Ideal.Quotient.mk (P.ker ^ 2) (P.σ g)))
      (fun i : P.vars ↦ algebraMap P.Ring _ (X i)))

@[simp]
lemma aux_toAlgHom_toComp (x : P.Ring) :
    (aux T g P) (((Generators.localizationAway g (S := T)).toComp P).toAlgHom x) =
      algebraMap P.Ring _ x := by
  simp only [toComp_toAlgHom, Ideal.mem_comap, RingHom.mem_ker, aux, Generators.comp,
    Generators.localizationAway, AlgHom.toRingHom_eq_coe, MvPolynomial.aeval_rename,
    Sum.elim_comp_inr, ← IsScalarTower.toAlgHom_apply (R := R), ← MvPolynomial.comp_aeval_apply,
    aeval_X_left_apply]

@[simp]
lemma aux_X_inl :
    (aux T g P) (X (Sum.inl ())) =
      IsLocalization.Away.invSelf ((Ideal.Quotient.mk (P.ker ^ 2)) (P.σ g)) := by
  simp [aux]

lemma aux_relation_eq_zero :
    (aux T g P) ((rename Sum.inr) (P.σ g) * X (Sum.inl ()) - 1) = 0 := by
  rw [map_sub, map_one, map_mul, ← toComp_toAlgHom (Generators.localizationAway g (S := T)) P]
  erw [aux_toAlgHom_toComp (T := T) g P (P.σ g)]
  rw [aux_X_inl, IsScalarTower.algebraMap_apply P.Ring (P.Ring ⧸ P.ker ^ 2) (Localization.Away _)]
  rw [Ideal.Quotient.algebraMap_eq, IsLocalization.Away.mul_invSelf
    ((Ideal.Quotient.mk (P.ker ^ 2)) _)
    (S := Localization.Away ((Ideal.Quotient.mk (P.ker ^ 2)) _))]
  simp

lemma sq_ker_comp_le_ker_aux :
    ((Generators.localizationAway g (S := T)).comp P).ker ^ 2 ≤ RingHom.ker (aux T g P) := by
  have hsple {x} (hx : x ∈ Ideal.span {(rename Sum.inr) (P.σ g) * X (Sum.inl ()) - 1}) :
        (aux T g P) x = 0 := by
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
    rw [map_mul, aux_relation_eq_zero, zero_mul]
  rw [comp_localizationAway_ker _ _ (P.σ g) (by simp), sq, Ideal.sup_mul, Ideal.mul_sup,
    Ideal.mul_sup]
  apply sup_le
  · apply sup_le
    · rw [← Ideal.map_mul, Ideal.map_le_iff_le_comap, ← sq]
      intro x hx
      simp only [Ideal.mem_comap, RingHom.mem_ker, aux_toAlgHom_toComp (T := T) g P x]
      rw [IsScalarTower.algebraMap_apply P.Ring (P.Ring ⧸ P.ker ^ 2) (Localization.Away _),
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
    · rw [Ideal.mul_le]
      intro x hx y hy
      simp [hsple hy]
  · apply sup_le <;>
    · rw [Ideal.mul_le]
      intro x hx y hy
      simp [hsple hx]

end

-- `T ⊗[S] (I/I²) → J/J²` is injective.
lemma liftBaseChange_injective (g : S) [IsLocalization.Away g T]
    (P : Generators R S) :
    Function.Injective (LinearMap.liftBaseChange T
      (Extension.Cotangent.map
        ((Presentation.localizationAway g (S := T)).toComp P).toExtensionHom)) := by
  set Q := Generators.localizationAway g (S := T)
  letI : Algebra P.Ring (Q.comp P).Ring := (Q.toComp P).toAlgHom.toAlgebra
  let f : P.Ring ⧸ P.ker ^ 2 := P.σ g
  let π : (Q.comp P).Ring →ₐ[R] Localization.Away f := aux T g P
  have hπ (x : (Q.comp P).Ring) (hx : x ∈ (Q.comp P).ker ^ 2) : π x = 0 :=
    sq_ker_comp_le_ker_aux _ _ hx
  apply IsLocalizedModule.injective_of_map_zero (Submonoid.powers g)
    (TensorProduct.mk S T P.toExtension.Cotangent 1)
  intro x hx
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  simp only [LinearEquiv.coe_coe, LinearMap.ringLmapEquivSelf_symm_apply,
    mk_apply, lift.tmul, LinearMap.coe_restrictScalars, LinearMap.coe_smulRight,
    LinearMap.one_apply, LinearMap.smul_apply, one_smul, Algebra.Extension.Cotangent.map_mk] at hx
  have : (Q.toComp P).toExtensionHom.toAlgHom x ∈ (Q.comp P).ker ^ 2 := by
    rwa [Extension.Cotangent.mk_eq_zero_iff] at hx
  have hπx : π ((Q.toComp P).toExtensionHom.toAlgHom x) = 0 := hπ _ this
  have : algebraMap P.Ring (Localization.Away f) x.val = 0 := by
    convert hπx
    symm
    apply aux_toAlgHom_toComp
  rw [IsScalarTower.algebraMap_apply _ (P.Ring ⧸ P.ker ^ 2) _,
    IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f)] at this
  obtain ⟨⟨m, ⟨n, rfl⟩⟩, hm⟩ := this
  rw [IsLocalizedModule.eq_zero_iff (Submonoid.powers g)]
  use ⟨g ^ n, n, rfl⟩
  dsimp [f] at hm
  rw [← map_pow, ← map_mul] at hm
  rw [Submonoid.smul_def]
  rw [Algebra.Extension.Cotangent.smul_mk_eq_mk_smul x (g := g ^ n) ((P.σ g) ^ n) (by simp)]
  rw [Extension.Cotangent.mk_eq_zero_iff]
  rw [Ideal.Quotient.eq_zero_iff_mem] at hm
  simpa using hm

end Algebra.Generators
