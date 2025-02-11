import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.Localization

open TensorProduct

universe u v

section

open Localization in
lemma AlgHom.exists_cover_eq_of_eq {R A B : Type*} [CommRing R] (S : Submonoid R)
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Finite R A]
    (Rₚ : Type*) (Aₚ Bₚ : Type u) [CommRing Rₚ] [CommRing Aₚ] [CommRing Bₚ]
    [Algebra R Rₚ] [Algebra R Aₚ] [Algebra R Bₚ] [Algebra Rₚ Aₚ] [Algebra Rₚ Bₚ]
    [Algebra A Aₚ] [Algebra B Bₚ]
    [IsScalarTower R A Aₚ] [IsScalarTower R B Bₚ] [IsScalarTower R Rₚ Aₚ] [IsScalarTower R Rₚ Bₚ]
    [IsLocalization S Rₚ] [IsLocalization (Algebra.algebraMapSubmonoid A S) Aₚ]
    [IsLocalization (Algebra.algebraMapSubmonoid B S) Bₚ]
    (f g : A →ₐ[R] B) (hf : IsLocalization.mapₐ S Rₚ Aₚ Bₚ f = IsLocalization.mapₐ S Rₚ Aₚ Bₚ g) :
    ∃ (r : S),
      Algebra.TensorProduct.map (.id (Away r.val) (Away r.val)) f =
        Algebra.TensorProduct.map (.id (Away r.val) (Away r.val)) g := by
  let u : B →ₗ[R] Bₚ := (IsScalarTower.toAlgHom R B Bₚ).toLinearMap
  have : IsLocalizedModule S u := by
    simp only [u]
    rw [isLocalizedModule_iff_isLocalization]
    infer_instance
  obtain ⟨s, hs⟩ := by
    refine Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S
      (N := B) (N' := Bₚ) (M := A) u f g ?_
    ext x
    simpa using DFunLike.congr_fun hf (algebraMap A Aₚ x)
  use s
  ext a
  simp only [Algebra.TensorProduct.map_restrictScalars_comp_includeRight, coe_comp,
    Function.comp_apply, Algebra.TensorProduct.includeRight_apply, u]
  have hun : IsUnit ((algebraMap R (Away s.val ⊗[R] B) s)) := by
    rw [IsScalarTower.algebraMap_apply R (Away s.val) _]
    apply (IsLocalization.Away.algebraMap_isUnit s.val).map
  suffices s.val • ((1 : Away s.val) ⊗ₜ[R] f a) = s.val • (1 ⊗ₜ[R] g a) by
    apply hun.mul_left_cancel
    rwa [← Algebra.smul_def, ← Algebra.smul_def]
  have := DFunLike.congr_fun hs a
  simp only [Submonoid.smul_def, LinearMap.smul_apply, LieHom.coe_toLinearMap, coe_toLieHom] at this
  rw [← TensorProduct.tmul_smul]
  rw [← TensorProduct.tmul_smul, this]

end

section Equalizer

def AlgHom.equalizerCongr {R A A' B B' : Type*} [CommSemiring R]
    [Semiring A] [Semiring A'] [Semiring B] [Semiring B']
    [Algebra R A] [Algebra R A'] [Algebra R B] [Algebra R B']
    (eA : A ≃ₐ[R] A') (eB : B ≃ₐ[R] B')
    {f g : A →ₐ[R] B} {f' g' : A' →ₐ[R] B'}
    (hf : eB.toAlgHom.comp f = f'.comp eA) (hg : eB.toAlgHom.comp g = g'.comp eA) :
    AlgHom.equalizer f g ≃ₐ[R] AlgHom.equalizer f' g' :=
  AlgEquiv.ofAlgHom
    (AlgHom.codRestrict (eA.toAlgHom.comp (equalizer f g).val) _ <| by
      intro x
      simp only [AlgEquiv.toAlgHom_eq_coe, coe_comp, AlgHom.coe_coe, Subalgebra.coe_val,
        Function.comp_apply, mem_equalizer]
      rw [← hf', x.2, hg'])
    (AlgHom.codRestrict (eA.symm.toAlgHom.comp (equalizer f' g').val) _ <| by
      intro x
      simp only [AlgEquiv.toAlgHom_eq_coe, coe_comp, AlgHom.coe_coe, Subalgebra.coe_val,
        Function.comp_apply, mem_equalizer]
      apply eB.injective
      rw [hf', hg', AlgEquiv.apply_symm_apply, x.2])
    (by ext; simp)
    (by ext; simp)
   where
    hf' (x) : eB (f x) = f' (eA x) := DFunLike.congr_fun hf x
    hg' (x) : eB (g x) = g' (eA x) := DFunLike.congr_fun hg x

def AlgHom.equalizerCongrOfEq {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] {f g f' g' : A →ₐ[R] B}
    (hf : f = f') (hg : g = g') :
    AlgHom.equalizer f g ≃ₐ[R] AlgHom.equalizer f' g' :=
  AlgHom.equalizerCongr AlgEquiv.refl AlgEquiv.refl
    (by subst hf; simp) (by subst hg; simp)

end Equalizer

class Algebra.FiniteEtale (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  extends Algebra.Etale R S, Module.Finite R S : Prop

lemma Algebra.FiniteEtale.of_equiv {R S S' : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteEtale R S] [CommRing S'] [Algebra R S'] (e : S ≃ₐ[R] S') :
    Algebra.FiniteEtale R S' := by
  have := Algebra.Etale.of_equiv e
  have := Module.Finite.equiv e.toLinearEquiv
  constructor

instance (n : ℕ) (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsSplitOfRank n R S] : Algebra.FiniteEtale R S := by
  obtain ⟨e⟩ := Algebra.IsSplitOfRank.nonempty_algEquiv_fun n R S
  have : Algebra.FiniteEtale R (Fin n → R) := by constructor
  exact Algebra.FiniteEtale.of_equiv e.symm

--lemma Algebra.FiniteEtale.mk (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
--    (h₁ : Algebra.Etale R S) (h₂ : Module.Finite R S) :
--    Algebra.FiniteEtale R S :=
--  inferInstance

section

lemma Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    (T : Type u) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [Algebra.Etale T (T ⊗[R] S)] :
    Algebra.Etale R S :=
  sorry

lemma Algebra.FiniteEtale.of_finiteEtale_tensorProduct_of_faithfullyFlat {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    (T : Type u) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [Algebra.FiniteEtale T (T ⊗[R] S)] :
    Algebra.FiniteEtale R S :=
  sorry

end

section rankAtStalk

lemma Algebra.exists_cover_rankAtStalk_eq {R : Type*} (S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Module.FinitePresentation R S] [Module.Flat R S] (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p,
      Module.rankAtStalk (R := Localization.Away r) (Localization.Away r ⊗[R] S) =
        Module.rankAtStalk S ⟨p, inferInstance⟩ := by
  have := Module.isLocallyConstant_rankAtStalk (R := R) (M := S)
  obtain ⟨U, hU, hp, heq⟩ := (Module.isLocallyConstant_rankAtStalk (M := S)).exists_open ⟨p, ‹_›⟩
  obtain ⟨V, ⟨r, rfl⟩, (hr : r ∉ p), hrU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hU
  refine ⟨r, hr, ?_⟩
  ext q
  rw [Module.rankAtStalk_tensorProduct]
  apply heq
  apply hrU
  simp only [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Set.mem_compl_iff,
    PrimeSpectrum.mem_zeroLocus, Ideal.coe_comap, Set.singleton_subset_iff, Set.mem_preimage,
    SetLike.mem_coe]
  obtain ⟨-, b⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint (.powers r) _ q.asIdeal).mp q.2
  rw [Set.disjoint_left] at b
  simp only [SetLike.mem_coe, Ideal.coe_comap, Set.mem_preimage] at b
  apply b
  use 1
  simp

end rankAtStalk

section

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

lemma RingHom.OfLocalizationSpan.of_exists_of_isPrime
    (hP : RingHom.OfLocalizationSpan P)
    {R S : Type u}
    [CommRing R] [CommRing S] (f : R →+* S)
    (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p, P (Localization.awayMap f r)) :
    P f := by
  have := H
  choose u hu₁ hu₂ using this
  apply hP f (Set.range (fun p : PrimeSpectrum R ↦ u p.asIdeal))
  · rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    rw [_root_.eq_top_iff]
    rintro p -
    simp only [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.carrier_eq_coe,
      PrimeSpectrum.basicOpen_eq_zeroLocus_compl, TopologicalSpace.Opens.coe_mk, Set.mem_iUnion,
      Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
    use p
    apply hu₁
  · simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    rintro ⟨p, ⟨p, rfl⟩⟩
    apply hu₂

end

section Etale

def RingHom.Etale {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Algebra.Etale R S

lemma RingHom.etale_algebraMap_iff {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).Etale ↔ Algebra.Etale R S := by
  simp only [RingHom.Etale]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

lemma RingHom.FormallyEtale.of_localRingHom {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
      (hf : f.FinitePresentation)
      (H : ∀ (p : Ideal S) [p.IsPrime], (Localization.localRingHom _ p f rfl).FormallyEtale) :
    f.FormallyEtale :=
  sorry

lemma RingHom.Etale.ofLocalizationSpan :
    RingHom.OfLocalizationSpan RingHom.Etale :=
  sorry

lemma RingHom.FormallyEtale.ofLocalizationSpan :
    RingHom.OfLocalizationSpan RingHom.FormallyEtale :=
  sorry

lemma RingHom.FormallyEtale.of_exists_of_prime {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FinitePresentation)
    (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      (Localization.awayMap f r).FormallyEtale) :
    f.FormallyEtale :=
  sorry

lemma RingHom.FormallyEtale.respectsIso :
    RingHom.RespectsIso RingHom.FormallyEtale :=
  sorry

lemma Algebra.finite_etale_of_exists_cover' {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S]
    (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      Algebra.FiniteEtale (Localization.Away r) (Localization.Away r ⊗[R] S)) :
    Algebra.FiniteEtale R S :=
  sorry

def AlgHom.extendScalarsOfIsLocalization {R S T A : Type*}
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra R A]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra S A] [IsScalarTower R S A]
    (M : Submonoid R) [IsLocalization M S]
    (P : Submonoid S) [IsLocalization P T]
    (f : T →ₐ[R] A) : T →ₐ[S] A where
  __ := f
  commutes' s := by
    simp
    sorry

@[simp]
lemma AlgHom.extendScalarsOfIsLocalization_apply {R S T A : Type*}
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra R A]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra S A] [IsScalarTower R S A]
    (M : Submonoid R) [IsLocalization M S]
    (P : Submonoid S) [IsLocalization P T]
    (f : T →ₐ[R] A) (t : T) :
    f.extendScalarsOfIsLocalization M P t = f t :=
  rfl

lemma Algebra.etale_of_exists_cover' {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S]
    (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      Algebra.Etale (Localization.Away r) (Localization.Away r ⊗[R] S)) : Algebra.Etale R S := by
  rw [← RingHom.etale_algebraMap_iff]
  apply RingHom.Etale.ofLocalizationSpan.of_exists_of_isPrime
  intro p hp
  obtain ⟨r, hr, h⟩ := H p
  refine ⟨r, hr, ?_⟩
  algebraize [Localization.awayMap (algebraMap R S) r]
  have : IsScalarTower R (Localization.Away r) (Localization.Away ((algebraMap R S) r)) := sorry
  let e : Localization.Away r ⊗[R] S ≃ₐ[Localization.Away r]
      Localization.Away ((algebraMap R S) r) :=
    AlgEquiv.ofAlgHom
      (Algebra.TensorProduct.lift (Algebra.ofId _ _) (IsScalarTower.toAlgHom _ _ _)
        fun _ _ ↦ Commute.all _ _)
      --((IsLocalization.liftAlgHom _).extendScalarsOfIsLocalization (.powers r)
      --  (.powers (algebraMap R S r)))
      ⟨IsLocalization.Away.lift (algebraMap R S r) (g := TensorProduct.includeRight.toRingHom)
        (by simp; sorry), sorry⟩
      (by
        apply AlgHom.coe_ringHom_injective
        apply IsLocalization.ringHom_ext (M := .powers (algebraMap R S r))
        ext x
        simp)
      (by ext; simp;)
  rw [RingHom.Etale]
  apply Algebra.Etale.of_equiv e

end Etale

namespace RingHom

/-- A ring hom is split of (constant) rank `n` if `S` is `R`-split of rank `n`. -/
def IsSplitOfRank (n : ℕ) {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Algebra.IsSplitOfRank n R S

end RingHom

section

variable {E F : Type*}

@[simps!]
def AlgHom.compRight (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (σ : E → F) :
    (F → S) →ₐ[R] E → S :=
  Pi.algHom R _ (fun f ↦ Pi.evalAlgHom R _ (σ f))

inductive Function.Coequalizer.Rel {E F : Type*} (σ τ : E → F) : F → F → Prop where
  | intro (x : E) : Rel σ τ (σ x) (τ x)

/-- The coequalizer of two functions `σ τ : E → F` is the quotient of `F` by
the equivalence relation generated by `σ x ≈ σ y`. -/
def Function.coequalizer {E : Type u} {F : Type v} (σ τ : E → F) : Type v :=
  Quot (Function.Coequalizer.Rel σ τ)

namespace Function.Coequalizer

variable (σ τ : E → F)

/-- The canonical map from `F` to the coequalizer. -/
def mk (f : F) : Function.coequalizer σ τ :=
  Quot.mk _ f

lemma condition (e : E) : mk σ τ (σ e) = mk σ τ (τ e) :=
  Quot.sound (.intro e)

lemma mk_surjective : Function.Surjective (Function.Coequalizer.mk σ τ) :=
  Quot.mk_surjective

/-- If `u : F → G` is a function with `u ∘ σ = u ∘ τ`, `u` descends to a function from the
coequalizer. -/
def desc {G : Type*} (u : F → G) (hu : u ∘ σ = u ∘ τ) : Function.coequalizer σ τ → G :=
  Quot.lift u (fun _ _ (.intro e) ↦ congrFun hu e)

@[simp] lemma desc_mk {G : Type*} (u : F → G) (hu : u ∘ σ = u ∘ τ) (f : F) :
    desc σ τ u hu (mk σ τ f) = u f :=
  rfl

end Function.Coequalizer

instance [Finite F] (σ τ : E → F) : Finite (Function.coequalizer σ τ) :=
  Finite.of_surjective _ (Function.Coequalizer.mk_surjective σ τ)

def RingHom.compRight (R : Type*) [CommRing R] {E F : Type*} (σ : E → F) :
    (F → R) →+* (E → R) :=
  Pi.ringHom (fun f ↦ Pi.evalRingHom _ (σ f))

@[simp]
lemma RingHom.compRight_apply (R : Type*) [CommRing R] {E F : Type*} (σ : E → F)
    (x : F → R) (i : E) :
    compRight R σ x i = x (σ i) :=
  rfl

def AlgHom.equalizerCompRightEquiv (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (σ τ : E → F) :
    AlgHom.equalizer (AlgHom.compRight R S σ) (AlgHom.compRight R S τ) ≃ₐ[R]
      Function.coequalizer σ τ → S :=
  AlgEquiv.ofAlgHom
    (Pi.algHom R _ (Function.Coequalizer.desc σ τ
      (fun f ↦ (Pi.evalAlgHom R (fun _ ↦ S) f).comp
        (equalizer (compRight R S σ) (compRight R S τ)).val)
        (by ext f ⟨x, hx⟩; exact congrFun hx f)))
    (AlgHom.codRestrict (.compRight _ _ (Function.Coequalizer.mk _ _))
      (equalizer _ _)
      (fun x ↦ by ext e; simp only [compRight_apply]; rw [Function.Coequalizer.condition]))
    (by
      ext f x
      obtain ⟨x, rfl⟩ := Function.Coequalizer.mk_surjective _ _ x
      simp)
    (by ext f x; simp)

instance (R : Type*) [CommRing R] [Finite E] [Finite F] (σ τ : E → F) :
    Algebra.IsSplitOfRank (Nat.card (Function.coequalizer σ τ)) R
      (AlgHom.equalizer (AlgHom.compRight R R σ) (AlgHom.compRight R R τ)) :=
  Algebra.IsSplitOfRank.of_card_eq rfl (AlgHom.equalizerCompRightEquiv R R σ τ)

lemma AlgHom.eq_compRight_of_no_nontrivial_isIdempotentElem {R E F : Type*} [_root_.Finite E]
    [Nonempty E] [CommRing R] (H : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1)
    (f : (E → R) →ₐ[R] F → R) : ∃ (σ : F → E), f = .compRight R R σ := by
  nontriviality R
  cases nonempty_fintype E
  classical
  have hor (i) (j) : f (Pi.single j 1) i = 0 ∨ f (Pi.single j 1) i = 1 := by
    apply H
    unfold IsIdempotentElem
    rw [← Pi.mul_apply, ← map_mul, ← Pi.single_mul_left]
    simp
  have (x : F) : ∃ (y : E), f (Pi.single y 1) x = 1 := by
    by_contra! hc
    replace hc (y : E) : f (Pi.single y 1) x = 0 := by
      obtain (h|h) := hor x y
      · assumption
      · simp [hc] at h
    have : 1 = ∑ y : E, f (Pi.single y 1) x := by
      rw [← Fintype.sum_apply]
      rw [← map_sum, Finset.univ_sum_single, ← Pi.one_def, map_one, Pi.one_apply]
    simp_rw [hc] at this
    simp at this
  have (x : F) : ∃! (y : E), f (Pi.single y 1) x = 1 := by
    apply existsUnique_of_exists_of_unique
    · exact this x
    · intro a b ha hb
      by_contra! h
      have : (Pi.single a 1) * (Pi.single b 1 : E → R) = 0 := by
        simp [← Pi.single_mul_left, h]
      apply_fun ((f ·) · x) at this
      simp [ha, hb] at this
  choose σ hσ hun using this
  use σ
  simp at hσ
  ext x i
  induction x using Pi.single_induction with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single j r =>
      have : Pi.single j r = r • (Pi.single j 1 : E → R) := by simp [← Pi.single_smul]
      rw [this]
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, AlgHom.compRight_apply]
      congr
      obtain (h|h) := hor i j
      · have : j ≠ σ i := by
          intro hj
          subst hj
          simp [hσ] at h
        simp [this, h]
      · have := hun i j h
        subst this
        simp [hσ]

lemma AlgHom.eq_compRight_of_no_nontrivial_isIdempotentElem' {R E F : Type*} [_root_.Finite E]
    [CommRing R] [Nontrivial R] (H : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1)
    (f : (E → R) →ₐ[R] F → R) : ∃ (σ : F → E), f = .compRight R R σ := by
  cases isEmpty_or_nonempty E
  · have : Subsingleton (F → R) := f.codomain_trivial
    cases isEmpty_or_nonempty F
    · use default
      apply Subsingleton.elim
    · simpa using false_of_nontrivial_of_subsingleton (F → R)
  · apply eq_compRight_of_no_nontrivial_isIdempotentElem H

lemma IsIdempotentElem.eq_one_of_isUnit {R : Type*} [CommRing R]
    {e : R} (he : IsIdempotentElem e) (heu : IsUnit e) : e = 1 := by
  rw [eq_comm, ← sub_eq_zero]
  apply heu.mul_left_cancel
  simp [he]

lemma IsLocalRing.isIdempotentElem_iff_eq_zero_or_eq_one {R : Type*} [CommRing R] [IsLocalRing R]
    {e : R} : IsIdempotentElem e ↔ e = 0 ∨ e = 1 := by
  refine ⟨fun he ↦ ?_, ?_⟩
  · obtain (h|h) := IsLocalRing.isUnit_or_isUnit_one_sub_self e
    · exact Or.inr (he.eq_one_of_isUnit h)
    · exact Or.inl (by simpa using he.one_sub.eq_one_of_isUnit h)
  · rintro (h|h) <;> subst h
    · exact IsIdempotentElem.zero
    · exact IsIdempotentElem.one

lemma RingHom.eq_compRight_of_isLocalHom {R E F : Type*} [_root_.Finite E] [CommRing R]
    (f : (E → R) →ₐ[R] F → R) [IsLocalRing R] :
    ∃ (σ : F → E), f = .compRight R R σ := by
  apply AlgHom.eq_compRight_of_no_nontrivial_isIdempotentElem'
  intro e he
  rwa [IsLocalRing.isIdempotentElem_iff_eq_zero_or_eq_one] at he

-- TODO: fix `IsLocalization.mapₐ` to have the correct universe generality
open Localization in
lemma AlgHom.exists_cover_eq_compRight'' {R : Type*} {E F : Type u}
    [_root_.Finite E] [_root_.Finite F]
    [CommRing R]
    (f : (E → R) →ₐ[R] F → R) (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p, ∃ (σ : F → E),
      Algebra.TensorProduct.map (.id (Away r) (Away r)) f =
        Algebra.TensorProduct.map (.id (Away r) (Away r)) (.compRight _ _ σ) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid (E → R) p.primeCompl)
      (E → Localization.AtPrime p) := by
    rw [← isLocalizedModule_iff_isLocalization]
    convert IsLocalizedModule.pi p.primeCompl (fun _ ↦ Algebra.linearMap R (Localization.AtPrime p))
    infer_instance
  have : IsLocalization (Algebra.algebraMapSubmonoid (F → R) p.primeCompl)
      (F → Localization.AtPrime p) := by
    rw [← isLocalizedModule_iff_isLocalization]
    convert IsLocalizedModule.pi p.primeCompl (fun _ ↦ Algebra.linearMap R (Localization.AtPrime p))
    infer_instance
  let fₚ : (E → Localization.AtPrime p) →ₐ[Localization.AtPrime p] F → Localization.AtPrime p :=
    IsLocalization.mapₐ p.primeCompl (Localization.AtPrime p)
      (E → Localization.AtPrime p)
      (F → Localization.AtPrime p) f
  obtain ⟨σ, hσ⟩ := RingHom.eq_compRight_of_isLocalHom fₚ
  let gₚ : (E → Localization.AtPrime p) →ₐ[Localization.AtPrime p] F → Localization.AtPrime p :=
    IsLocalization.mapₐ p.primeCompl (Localization.AtPrime p)
      (E → Localization.AtPrime p)
      (F → Localization.AtPrime p) (.compRight R R σ)
  have : fₚ = gₚ := by
    rw [hσ]
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid (E → R) p.primeCompl)
    ext x i
    simp only [toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      compRight_apply, IsLocalization.mapₐ_coe, IsLocalization.map_eq, gₚ]
    rfl
  obtain ⟨⟨r, hr⟩, heq⟩ := AlgHom.exists_cover_eq_of_eq _ _ _ _ f (.compRight R R σ) this
  exact ⟨r, hr, σ, heq⟩

set_option maxHeartbeats 0 in
open Localization in
lemma AlgHom.exists_cover_eq_compRight''₂ {R : Type*} {E F : Type u}
    [_root_.Finite E] [_root_.Finite F] [CommRing R] (f g : (E → R) →ₐ[R] F → R)
    (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p, ∃ (σ τ : F → E),
      Algebra.TensorProduct.map (.id (Away r) (Away r)) f =
        Algebra.TensorProduct.map (.id (Away r) (Away r)) (.compRight _ _ σ) ∧
      Algebra.TensorProduct.map (.id (Away r) (Away r)) g =
        Algebra.TensorProduct.map (.id (Away r) (Away r)) (.compRight _ _ τ) := by
  obtain ⟨r, hr, σ, hσ⟩ := AlgHom.exists_cover_eq_compRight'' f p
  obtain ⟨r', hr', τ, hτ⟩ := AlgHom.exists_cover_eq_compRight'' g p
  letI : Algebra (Localization.Away r) (Localization.Away (r * r')) := by
    refine (IsLocalization.Away.lift r (g := algebraMap R _) ?_).toAlgebra
    apply isUnit_of_mul_isUnit_left (y := algebraMap _ _ r')
    rw [← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit (r * r')
  letI : Algebra (Localization.Away r') (Localization.Away (r * r')) := by
    refine (IsLocalization.Away.lift r' (g := algebraMap R _) ?_).toAlgebra
    apply isUnit_of_mul_isUnit_right (x := algebraMap _ _ r)
    rw [← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit (r * r')
  have : IsScalarTower R (Away r) (Localization.Away (r * r')) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower R (Away r') (Localization.Away (r * r')) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    simp [RingHom.algebraMap_toAlgebra]
  let eE : Localization.Away (r * r') ⊗[R] (E → R) ≃ₐ[Localization.Away (r * r')]
      Localization.Away (r * r') ⊗[Away r] (Localization.Away r ⊗[R] (E → R)) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  let eF : Localization.Away (r * r') ⊗[R] (F → R) ≃ₐ[Localization.Away (r * r')]
      Localization.Away (r * r') ⊗[Away r] (Localization.Away r ⊗[R] (F → R)) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  let eE' : Localization.Away (r * r') ⊗[R] (E → R) ≃ₐ[Localization.Away (r * r')]
      Localization.Away (r * r') ⊗[Away r'] (Localization.Away r' ⊗[R] (E → R)) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  let eF' : Localization.Away (r * r') ⊗[R] (F → R) ≃ₐ[Localization.Away (r * r')]
      Localization.Away (r * r') ⊗[Away r'] (Localization.Away r' ⊗[R] (F → R)) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  have heq (u : (E → R) →ₐ[R] F → R) : Algebra.TensorProduct.map
      (AlgHom.id (Away (r * r')) (Away (r * r'))) u =
      eF.symm.toAlgHom.comp ((Algebra.TensorProduct.map (.id _ _)
        (Algebra.TensorProduct.map (.id _ _) u)).comp eE.toAlgHom) := by
    ext
    simp [eF, eE]
  have heq' (u : (E → R) →ₐ[R] F → R) : Algebra.TensorProduct.map
      (AlgHom.id (Away (r * r')) (Away (r * r'))) u =
      eF'.symm.toAlgHom.comp ((Algebra.TensorProduct.map (.id _ _)
        (Algebra.TensorProduct.map (.id _ _) u)).comp eE'.toAlgHom) := by
    ext
    simp [eF', eE']
  refine ⟨r * r', ?_, σ, τ, ?_, ?_⟩
  · intro hr
    cases Ideal.IsPrime.mem_or_mem inferInstance hr <;> contradiction
  · rw [heq, hσ, ← heq]
  · rw [heq', hτ, ← heq']

end

lemma Algebra.FiniteEtale.equalizer_fun {R : Type u} {E F : Type} [CommRing R] [Finite E] [Finite F]
    (f g : (E → R) →ₐ[R] (F → R)) :
    Algebra.FiniteEtale R (AlgHom.equalizer f g) := by
  apply Algebra.finite_etale_of_exists_cover'
  intro p hp
  obtain ⟨r, hr, σ, τ, hσ, hτ⟩ := AlgHom.exists_cover_eq_compRight''₂ f g p
  use r, hr
  set A := Localization.Away r
  let f' : A ⊗[R] (E → R) →ₐ[A] A ⊗[R] (F → R) := Algebra.TensorProduct.map (.id _ _) f
  let g' : A ⊗[R] (E → R) →ₐ[A] A ⊗[R] (F → R) := Algebra.TensorProduct.map (.id _ _) g
  let cong₁ : A ⊗[R] AlgHom.equalizer f g ≃ₐ[A] AlgHom.equalizer f' g' :=
    AlgHom.tensorEqualizerEquiv A A f g
  let T := AlgHom.equalizer
    (TensorProduct.map (.id A A) (.compRight R R σ))
    (TensorProduct.map (.id A A) (.compRight R R τ))
  let cong₂ : AlgHom.equalizer f' g' ≃ₐ[A] T := AlgHom.equalizerCongrOfEq hσ hτ
  let cong₃ : T ≃ₐ[A] A ⊗[R] AlgHom.equalizer (AlgHom.compRight R R σ) (AlgHom.compRight R R τ) :=
    (AlgHom.tensorEqualizerEquiv A A _ _).symm
  let cong : A ⊗[R] AlgHom.equalizer f g ≃ₐ[A] A ⊗[R]
      AlgHom.equalizer (AlgHom.compRight R R σ) (AlgHom.compRight R R τ) :=
    cong₁.trans (cong₂.trans cong₃)
  apply Algebra.FiniteEtale.of_equiv cong.symm

lemma Algebra.FiniteEtale.equalizer_of_isSplitOfRank {R S T : Type u} {n m : ℕ} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] [Algebra.IsSplitOfRank n R S] [Algebra.IsSplitOfRank m R T] (f g : S →ₐ[R] T) :
    Algebra.FiniteEtale R (AlgHom.equalizer f g) := by
  obtain ⟨eS⟩ := Algebra.IsSplitOfRank.nonempty_algEquiv_fun n R S
  obtain ⟨eT⟩ := Algebra.IsSplitOfRank.nonempty_algEquiv_fun m R T
  let f' : (Fin n → R) →ₐ[R] Fin m → R := eT.toAlgHom.comp (f.comp eS.symm)
  let g' : (Fin n → R) →ₐ[R] Fin m → R := eT.toAlgHom.comp (g.comp eS.symm)
  have : Algebra.FiniteEtale R (AlgHom.equalizer f' g') :=
    Algebra.FiniteEtale.equalizer_fun f' g'
  let cong : AlgHom.equalizer f g ≃ₐ[R] AlgHom.equalizer f' g' :=
    AlgHom.equalizerCongr eS eT (by ext; simp [f', g']) (by ext; simp [f', g'])
  exact Algebra.FiniteEtale.of_equiv cong.symm

lemma Algebra.FiniteEtale.equalizer_of_rankAtStalk_eq {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T]
    [Module.Finite R S] [Module.Finite R T] [Algebra.Etale R S] [Algebra.Etale R T]
    {n m : ℕ} (hn : Module.rankAtStalk (R := R) S = n) (hm : Module.rankAtStalk (R := R) T = m)
    (f g : S →ₐ[R] T) :
    Algebra.FiniteEtale R (AlgHom.equalizer f g) := by
  wlog hS : Algebra.IsSplitOfRank n R S
  · obtain ⟨A, _, _, _, hA⟩ := Algebra.IsSplitOfRank.exists_isSplitOfRank_tensorProduct hn
    let f' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) f
    let g' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) g
    let cong : A ⊗[R] AlgHom.equalizer f g ≃ₐ[A] AlgHom.equalizer f' g' :=
      AlgHom.tensorEqualizerEquiv A A f g
    have : Algebra.FiniteEtale A (AlgHom.equalizer f' g') := by
      apply this (n := n) (m := m)
      · ext p
        rw [Module.rankAtStalk_tensorProduct, hn]
        rfl
      · ext p
        rw [Module.rankAtStalk_tensorProduct, hm]
        rfl
      exact hA
    have : Algebra.FiniteEtale A (A ⊗[R] AlgHom.equalizer f g) :=
      Algebra.FiniteEtale.of_equiv cong.symm
    exact Algebra.FiniteEtale.of_finiteEtale_tensorProduct_of_faithfullyFlat A
  clear hn
  wlog hT : Algebra.IsSplitOfRank m R T
  · obtain ⟨A, _, _, _, hA⟩ := Algebra.IsSplitOfRank.exists_isSplitOfRank_tensorProduct hm
    let f' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) f
    let g' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) g
    let cong : A ⊗[R] AlgHom.equalizer f g ≃ₐ[A] AlgHom.equalizer f' g' :=
      AlgHom.tensorEqualizerEquiv A A f g
    have : Algebra.FiniteEtale A (AlgHom.equalizer f' g') := by
      apply this (m := m)
      · ext p
        rw [Module.rankAtStalk_tensorProduct, hm]
        rfl
      · infer_instance
      · exact hA
    have : Algebra.FiniteEtale A (A ⊗[R] AlgHom.equalizer f g) :=
      Algebra.FiniteEtale.of_equiv cong.symm
    exact Algebra.FiniteEtale.of_finiteEtale_tensorProduct_of_faithfullyFlat A
  apply Algebra.FiniteEtale.equalizer_of_isSplitOfRank

set_option maxHeartbeats 0 in
theorem Algebra.Etale.equalizer {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    [Module.Finite R S] [Module.Finite R T] [Algebra.Etale R S] [Algebra.Etale R T]
    (f g : S →ₐ[R] T) :
    Algebra.FiniteEtale R (AlgHom.equalizer f g) := by
  wlog h : ∃ (n : ℕ), Module.rankAtStalk (R := R) S = n
  · apply Algebra.finite_etale_of_exists_cover'
    intro p hp
    obtain ⟨r, hr, hn⟩ := Algebra.exists_cover_rankAtStalk_eq S p
    use r, hr
    let A := Localization.Away r
    let f' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) f
    let g' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) g
    let cong : A ⊗[R] AlgHom.equalizer f g ≃ₐ[A] AlgHom.equalizer f' g' :=
      AlgHom.tensorEqualizerEquiv A A f g
    have : Algebra.FiniteEtale A (AlgHom.equalizer f' g') := by
      apply this
      use Module.rankAtStalk S ⟨p, hp⟩
    exact Algebra.FiniteEtale.of_equiv (S := AlgHom.equalizer f' g') cong.symm
  obtain ⟨n, hn⟩ := h
  wlog h : ∃ (m : ℕ), Module.rankAtStalk (R := R) T = m
  · apply Algebra.finite_etale_of_exists_cover'
    intro p hp
    obtain ⟨r, hr, hm⟩ := Algebra.exists_cover_rankAtStalk_eq T p
    use r, hr
    let A := Localization.Away r
    let f' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) f
    let g' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) g
    let cong : A ⊗[R] AlgHom.equalizer f g ≃ₐ[A] AlgHom.equalizer f' g' :=
      AlgHom.tensorEqualizerEquiv A A f g
    have : Algebra.FiniteEtale A (AlgHom.equalizer f' g') := by
      apply this (n := n)
      · ext p
        rw [Module.rankAtStalk_tensorProduct, hn]
        rfl
      · use (Module.rankAtStalk T ⟨p, hp⟩)
    exact Algebra.FiniteEtale.of_equiv (S := AlgHom.equalizer f' g') cong.symm
  obtain ⟨m, hm⟩ := h
  apply Algebra.FiniteEtale.equalizer_of_rankAtStalk_eq hn hm
