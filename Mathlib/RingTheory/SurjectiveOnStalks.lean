/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Ring Homomorphisms surjective on stalks

In this file, we prove some results on ring homomorphisms surjective on stalks, to be used in
the development of immersions in algebraic geometry.

A ring homomorphism `R →+* S` is surjective on stalks if `R_p →+* S_q` is surjective for all pairs
of primes `p = f⁻¹(q)`. We show that this property is stable under composition and base change, and
that surjections and localizations satisfy this.

-/

variable {R : Type*} [CommRing R] (M : Submonoid R) {S : Type*} [CommRing S]
variable {T : Type*} [CommRing T]
variable {g : S →+* T} {f : R →+* S}

namespace RingHom

/--
A ring homomorphism `R →+* S` is surjective on stalks if `R_p →+* S_q` is surjective for all pairs
of primes `p = f⁻¹(q)`.
-/
def SurjectiveOnStalks (f : R →+* S) : Prop :=
  ∀ (P : Ideal S) (_ : P.IsPrime), Function.Surjective (Localization.localRingHom _ P f rfl)

/--
`R_p →+* S_q` is surjective if and only if
every `x : S` is of the form `f x / f r` for some `f r ∉ q`.
This is useful when proving `SurjectiveOnStalks`.
-/
lemma surjective_localRingHom_iff (P : Ideal S) [P.IsPrime] :
    Function.Surjective (Localization.localRingHom _ P f rfl) ↔
      ∀ s : S, ∃ x r : R, ∃ c ∉ P, f r ∉ P ∧ c * f r * s = c * f x := by
  constructor
  · intro H y
    obtain ⟨a, ha⟩ := H (IsLocalization.mk' _ y (1 : P.primeCompl))
    obtain ⟨a, t, rfl⟩ := IsLocalization.mk'_surjective (P.comap f).primeCompl a
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq,
      Submonoid.coe_one, one_mul, IsLocalization.eq_iff_exists P.primeCompl] at ha
    obtain ⟨c, hc⟩ := ha
    simp only [← mul_assoc] at hc
    exact ⟨_, _, _, c.2, t.2, hc.symm⟩
  · refine fun H y ↦ Localization.ind (fun ⟨y, t, h⟩ ↦ ?_) y
    simp only
    obtain ⟨yx, ys, yc, hyc, hy, ey⟩ := H y
    obtain ⟨tx, ts, yt, hyt, ht, et⟩ := H t
    refine ⟨Localization.mk (yx * ts) ⟨ys * tx, Submonoid.mul_mem _ hy ?_⟩, ?_⟩
    · exact fun H ↦ mul_mem (P.primeCompl.mul_mem hyt ht) h (et ▸ Ideal.mul_mem_left _ yt H)
    · simp only [Localization.mk_eq_mk', Localization.localRingHom_mk', map_mul f,
        IsLocalization.mk'_eq_iff_eq, IsLocalization.eq_iff_exists P.primeCompl]
      refine ⟨⟨yc, hyc⟩ * ⟨yt, hyt⟩, ?_⟩
      simp only [Submonoid.coe_mul]
      convert congr($(ey.symm) * $(et)) using 1 <;> ring

lemma surjectiveOnStalks_iff_forall_ideal :
    f.SurjectiveOnStalks ↔
      ∀ I : Ideal S, I ≠ ⊤ → ∀ s : S, ∃ x r : R, ∃ c ∉ I, f r ∉ I ∧ c * f r * s = c * f x := by
  simp_rw [SurjectiveOnStalks, surjective_localRingHom_iff]
  refine ⟨fun H I hI s ↦ ?_, fun H I hI ↦ H I hI.ne_top⟩
  obtain ⟨M, hM, hIM⟩ := I.exists_le_maximal hI
  obtain ⟨x, r, c, hc, hr, e⟩ := H M hM.isPrime s
  exact ⟨x, r, c, fun h ↦ hc (hIM h), fun h ↦ hr (hIM h), e⟩

lemma surjectiveOnStalks_iff_forall_maximal :
    f.SurjectiveOnStalks ↔ ∀ (I : Ideal S) (_ : I.IsMaximal),
      Function.Surjective (Localization.localRingHom _ I f rfl) := by
  refine ⟨fun H I hI ↦ H I hI.isPrime, fun H I hI ↦ ?_⟩
  simp_rw [surjective_localRingHom_iff] at H ⊢
  intro s
  obtain ⟨M, hM, hIM⟩ := I.exists_le_maximal hI.ne_top
  obtain ⟨x, r, c, hc, hr, e⟩ := H M hM s
  exact ⟨x, r, c, fun h ↦ hc (hIM h), fun h ↦ hr (hIM h), e⟩

lemma surjectiveOnStalks_iff_forall_maximal' :
    f.SurjectiveOnStalks ↔ ∀ I : Ideal S, I.IsMaximal →
      ∀ s : S, ∃ x r : R, ∃ c ∉ I, f r ∉ I ∧ c * f r * s = c * f x := by
  simp only [surjectiveOnStalks_iff_forall_maximal, surjective_localRingHom_iff]

lemma surjectiveOnStalks_of_exists_div (h : ∀ x : S, ∃ r s : R, IsUnit (f s) ∧ f s * x = f r) :
    SurjectiveOnStalks f :=
  surjectiveOnStalks_iff_forall_ideal.mpr fun I hI x ↦
    let ⟨r, s, hr, hr'⟩ := h x
    ⟨r, s, 1, by simpa [← Ideal.eq_top_iff_one], fun h ↦ hI (I.eq_top_of_isUnit_mem h hr), by simpa⟩

lemma surjectiveOnStalks_of_surjective (h : Function.Surjective f) :
    SurjectiveOnStalks f :=
  surjectiveOnStalks_iff_forall_ideal.mpr fun _ _ s ↦
    let ⟨r, hr⟩ := h s
    ⟨r, 1, 1, by simpa [← Ideal.eq_top_iff_one], by simpa [← Ideal.eq_top_iff_one], by simp [hr]⟩

lemma SurjectiveOnStalks.comp (hg : SurjectiveOnStalks g) (hf : SurjectiveOnStalks f) :
    SurjectiveOnStalks (g.comp f) := by
  intros I hI
  have := (hg I hI).comp (hf _ (hI.comap g))
  rwa [← RingHom.coe_comp, ← Localization.localRingHom_comp] at this

lemma SurjectiveOnStalks.of_comp (hg : SurjectiveOnStalks (g.comp f)) :
    SurjectiveOnStalks g := by
  intros I hI
  have := hg I hI
  rw [Localization.localRingHom_comp (I.comap (g.comp f)) (I.comap g) _ _ rfl _ rfl,
    RingHom.coe_comp] at this
  exact this.of_comp


open TensorProduct

variable [Algebra R T] [Algebra R S] in
/--
If `R → T` is surjective on stalks, and `J` is some prime of `T`,
then every element `x` in `S ⊗[R] T` satisfies `(1 ⊗ r • t) * x = a ⊗ t` for some
`r : R`, `a : S`, and `t : T` such that `r • t ∉ J`.
-/
lemma SurjectiveOnStalks.exists_mul_eq_tmul
    (hf₂ : (algebraMap R T).SurjectiveOnStalks)
    (x : S ⊗[R] T) (J : Ideal T) (hJ : J.IsPrime) :
    ∃ (t : T) (r : R) (a : S), (r • t ∉ J) ∧
      (1 : S) ⊗ₜ[R] (r • t) * x = a ⊗ₜ[R] t := by
  induction x with
  | zero =>
    exact ⟨1, 1, 0, by rw [one_smul]; exact J.primeCompl.one_mem,
      by rw [mul_zero, TensorProduct.zero_tmul]⟩
  | tmul x₁ x₂ =>
    obtain ⟨y, s, c, hs, hc, e⟩ := (surjective_localRingHom_iff _).mp (hf₂ J hJ) x₂
    simp_rw [Algebra.smul_def]
    refine ⟨c, s, y • x₁, J.primeCompl.mul_mem hc hs, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm _ c, e,
      TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
  | add x₁ x₂ hx₁ hx₂ =>
    obtain ⟨t₁, r₁, a₁, hr₁, e₁⟩ := hx₁
    obtain ⟨t₂, r₂, a₂, hr₂, e₂⟩ := hx₂
    have : (r₁ * r₂) • (t₁ * t₂) = (r₁ • t₁) * (r₂ • t₂) := by
      simp_rw [← smul_eq_mul]; rw [smul_smul_smul_comm]
    refine ⟨t₁ * t₂, r₁ * r₂, r₂ • a₁ + r₁ • a₂, this.symm ▸ J.primeCompl.mul_mem hr₁ hr₂, ?_⟩
    rw [this, ← one_mul (1 : S), ← Algebra.TensorProduct.tmul_mul_tmul, mul_add, mul_comm (_ ⊗ₜ _),
      mul_assoc, e₁, Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_mul_assoc,
      ← TensorProduct.smul_tmul, mul_comm (_ ⊗ₜ _), mul_assoc, e₂,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_mul_assoc, ← TensorProduct.smul_tmul,
      TensorProduct.add_tmul, mul_comm t₁ t₂]

variable (S) in
lemma surjectiveOnStalks_of_isLocalization
    [Algebra R S] [IsLocalization M S] :
    SurjectiveOnStalks (algebraMap R S) := by
  refine surjectiveOnStalks_of_exists_div fun s ↦ ?_
  obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective M s
  exact ⟨x, s, IsLocalization.map_units S s, IsLocalization.mk'_spec' S x s⟩

lemma SurjectiveOnStalks.baseChange
    [Algebra R T] [Algebra R S]
    (hf : (algebraMap R T).SurjectiveOnStalks) :
    (algebraMap S (S ⊗[R] T)).SurjectiveOnStalks := by
  let g : T →+* S ⊗[R] T := Algebra.TensorProduct.includeRight.toRingHom
  intros J hJ
  rw [surjective_localRingHom_iff]
  intro x
  obtain ⟨t, r, a, ht, e⟩ := hf.exists_mul_eq_tmul x (J.comap g) inferInstance
  refine ⟨a, algebraMap _ _ r, 1 ⊗ₜ (r • t), ht, ?_, ?_⟩
  · intro H
    simp only [Algebra.algebraMap_eq_smul_one (A := S), Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, id_apply, smul_tmul, ← Algebra.algebraMap_eq_smul_one (A := T)] at H
    rw [Ideal.mem_comap, Algebra.smul_def, g.map_mul] at ht
    exact ht (J.mul_mem_right _ H)
  · simp only [tmul_smul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHomCompTriple.comp_apply, Algebra.smul_mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one, id_apply, ← e]
    rw [Algebra.algebraMap_eq_smul_one, ← smul_tmul', smul_mul_assoc]

lemma surjectiveOnStalks_iff_of_isLocalHom [IsLocalRing S] [IsLocalHom f] :
    f.SurjectiveOnStalks ↔ Function.Surjective f := by
  refine ⟨fun H x ↦ ?_, fun h ↦ surjectiveOnStalks_of_surjective h⟩
  obtain ⟨y, r, c, hc, hr, e⟩ :=
    (surjective_localRingHom_iff _).mp (H (IsLocalRing.maximalIdeal _) inferInstance) x
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hc hr
  refine ⟨(isUnit_of_map_unit f r hr).unit⁻¹ * y, ?_⟩
  apply hr.mul_right_injective
  apply hc.mul_right_injective
  simp only [← map_mul, ← mul_assoc, IsUnit.mul_val_inv, one_mul, e]

end RingHom
