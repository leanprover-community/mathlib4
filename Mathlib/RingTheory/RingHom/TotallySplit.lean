import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.Localization

open TensorProduct

universe u

section

lemma Algebra.IsSplitOfRank.rankAtStalk_eq {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (n : ℕ) [Algebra.IsSplitOfRank n R S] :
    Module.rankAtStalk (R := R) S = n :=
  sorry

lemma Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    (T : Type u) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [Algebra.Etale T (T ⊗[R] S)] :
    Algebra.Etale R S :=
  sorry

instance Algebra.IsSplitOfRank.baseChange (R S T : Type*) [CommRing R]
    [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
    (n : ℕ) [Algebra.IsSplitOfRank n R S] :
    Algebra.IsSplitOfRank n T (T ⊗[R] S) :=
  sorry

end

section

noncomputable
instance {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] (r : R) :
    Algebra (Localization.Away r) (Localization.Away (algebraMap R S r)) :=
  (Localization.awayMap (algebraMap R S) r).toAlgebra

def AlgHom.extendScalarsOfIsLocalization  {R : Type*}
    [CommSemiring R] (S : Submonoid R) (R' : Type*) {A B : Type*}
    [CommSemiring R'] [Algebra R R'] [IsLocalization S R']
    [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra R B] [Algebra R' A] [Algebra R' B]
    [IsScalarTower R R' A] [IsScalarTower R R' B]
    (f : A →ₐ[R] B) : A →ₐ[R'] B :=
  sorry

@[simp]
lemma AlgHom.restrictScalars_extendScalarsOfIsLocalization {R : Type*}
    [CommSemiring R] (S : Submonoid R) (R' : Type*) {A B : Type*}
    [CommSemiring R'] [Algebra R R'] [IsLocalization S R']
    [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra R B] [Algebra R' A] [Algebra R' B]
    [IsScalarTower R R' A] [IsScalarTower R R' B]
    (f : A →ₐ[R] B) : (f.extendScalarsOfIsLocalization S R').restrictScalars R = f :=
  sorry

@[simp]
lemma AlgHom.extendScalarsOfIsLocalization_apply {R : Type*}
    [CommSemiring R] (S : Submonoid R) (R' : Type*) {A B : Type*}
    [CommSemiring R'] [Algebra R R'] [IsLocalization S R']
    [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra R B] [Algebra R' A] [Algebra R' B]
    [IsScalarTower R R' A] [IsScalarTower R R' B]
    (f : A →ₐ[R] B) (a : A) : f.extendScalarsOfIsLocalization S R' a = f a :=
  sorry

end

section rankAtStalk

lemma Algebra.exists_cover_rankAtStalk_eq {R : Type*} (S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Module.FinitePresentation R S] [Module.Flat R S] (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p, ∃ (n : ℕ),
      Module.rankAtStalk (R := Localization.Away r) (Localization.Away r ⊗[R] S) = n :=
  sorry

/-
lemma Algebra.exists_cover_isSplitOfRank₂ {R : Type*} (S T : Type*) [CommRing R]
    [CommRing S] [Algebra R S] [Module.FinitePresentation R S] [Module.Flat R S]
    [CommRing T] [Algebra R T] [Module.FinitePresentation R T] [Module.Flat R T]
    (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p, ∃ (n m : ℕ),
      IsSplitOfRank n (Localization.Away r) (Localization.Away (algebraMap R S r)) ∧
      IsSplitOfRank m (Localization.Away r) (Localization.Away (algebraMap R T r)) :=
  this is wrong
-/

end rankAtStalk

namespace RingHom

/-- A ring hom is split of (constant) rank `n` if `S` is `R`-split of rank `n`. -/
def IsSplitOfRank (n : ℕ) {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Algebra.IsSplitOfRank n R S

end RingHom

section

variable {E F : Type*}

def AlgHom.compRight (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (σ : E → F) :
    (F → S) →ₐ[R] E → S :=
  Pi.algHom R _ (fun f ↦ Pi.evalAlgHom R _ (σ f))

def RingHom.compRight (R : Type*) [CommRing R] {E F : Type*} (σ : E → F) :
    (F → R) →+* (E → R) :=
  Pi.ringHom (fun f ↦ Pi.evalRingHom _ (σ f))

instance {R E : Type*} [CommRing R] (r : R) :
    IsLocalization.Away ((algebraMap R (E → R)) r) (E → Localization.Away r) :=
  sorry

instance {R E : Type*} [CommRing R] (r : R) (f : (E → R) →ₐ[R] F → R) :
    IsLocalization.Away (f ((algebraMap R (E → R)) r)) (F → Localization.Away r) := by
  simp only [AlgHom.commutes]
  infer_instance

lemma RingHom.eq_compRight_of_isLocalHom {R E F : Type*} [CommRing R] (f : (E → R) →+* F → R)
    [IsLocalRing R] [IsLocalHom f] :
    ∃ (σ : F → E), f = .compRight R σ :=
  sorry

def AlgHom.equalizerCompRightEquiv (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (σ τ : E → F) :
    (AlgHom.equalizer (AlgHom.compRight R S σ) (AlgHom.compRight R S τ)) ≃ₐ[R]
      { x | σ x = τ x } → S :=
  sorry

instance (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (σ τ : E → F) :
    Algebra.IsSplitOfRank (Nat.card { x | σ x = τ x }) R
      (AlgHom.equalizer (AlgHom.compRight R S σ) (AlgHom.compRight R S τ)) :=
  sorry

lemma AlgHom.exists_cover_eq_compRight' {R E F : Type*} [CommRing R] (f : (E → R) →ₐ[R] F → R)
    (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p, ∃ (σ : F → E),
      IsLocalization.Away.mapₐ _ _ f (algebraMap _ _ r) = .compRight R (Localization.Away r) σ :=
  sorry

lemma AlgHom.exists_cover_eq_compRight'₂ {R E F : Type*} [CommRing R] (f g : (E → R) →ₐ[R] F → R)
    (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p, ∃ (σ τ : F → E),
      IsLocalization.Away.mapₐ _ _ f (algebraMap _ _ r) = .compRight R (Localization.Away r) σ ∧
      IsLocalization.Away.mapₐ _ _ g (algebraMap _ _ r) = .compRight R (Localization.Away r) τ :=
  sorry

end

lemma RingHom.FormallyEtale.of_localRingHom {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
      (hf : f.FinitePresentation)
      (H : ∀ (p : Ideal S) [p.IsPrime], (Localization.localRingHom _ p f rfl).FormallyEtale) :
    f.FormallyEtale :=
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

lemma Algebra.etale_of_exists_cover {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S]
    (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      Algebra.Etale (Localization.Away r) (Localization.Away (algebraMap R S r))) :
  Algebra.Etale R S := sorry

lemma Algebra.etale_of_exists_cover' {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S]
    (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      Algebra.Etale (Localization.Away r) (Localization.Away r ⊗[R] S)) :
  Algebra.Etale R S := sorry

lemma Algebra.Etale.equalizer_fun {R : Type u} {E F : Type} [CommRing R] [Finite E] [Finite F]
    (f g : (E → R) →ₐ[R] (F → R)) :
    Algebra.Etale R (AlgHom.equalizer f g) := by
  apply Algebra.etale_of_exists_cover
  intro p hp
  obtain ⟨r, hr, σ, τ, hσ, hτ⟩ := AlgHom.exists_cover_eq_compRight'₂ f g p
  set A := Localization.Away r
  set a := (IsLocalization.Away.mapₐ (E → A) (F → A) f
    ((algebraMap R (E → R)) r)).extendScalarsOfIsLocalization (.powers r) (Localization.Away r)
  set b := (IsLocalization.Away.mapₐ (E → A) (F → A) g
    ((algebraMap R (E → R)) r)).extendScalarsOfIsLocalization (.powers r) (Localization.Away r)
  set a' := AlgHom.compRight A A σ
  set b' := AlgHom.compRight A A τ
  use r, hr
  let e : Localization.Away (algebraMap R (AlgHom.equalizer f g) r) ≃ₐ[A] AlgHom.equalizer a b :=
    sorry
  let cong : AlgHom.equalizer a b ≃ₐ[A] AlgHom.equalizer a' b' :=
    sorry
  have : Algebra.Etale A ↥(AlgHom.equalizer a b) := Algebra.Etale.of_equiv cong.symm
  apply Algebra.Etale.of_equiv e.symm

lemma Algebra.Etale.equalizer_of_isSplitOfRank {R S T : Type u} {n m : ℕ} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] [Algebra.IsSplitOfRank n R S] [Algebra.IsSplitOfRank m R T] (f g : S →ₐ[R] T) :
    Algebra.Etale R (AlgHom.equalizer f g) := by
  obtain ⟨eS⟩ := Algebra.IsSplitOfRank.nonempty_algEquiv_fun n R S
  obtain ⟨eT⟩ := Algebra.IsSplitOfRank.nonempty_algEquiv_fun m R T
  let f' : (Fin n → R) →ₐ[R] Fin m → R := eT.toAlgHom.comp (f.comp eS.symm)
  let g' : (Fin n → R) →ₐ[R] Fin m → R := eT.toAlgHom.comp (g.comp eS.symm)
  have : Algebra.Etale R (AlgHom.equalizer f' g') := Algebra.Etale.equalizer_fun f' g'
  let cong : AlgHom.equalizer f g ≃ₐ[R] AlgHom.equalizer f' g' := sorry
  exact Algebra.Etale.of_equiv cong.symm

lemma Algebra.Etale.equalizer_of_rankAtStalk_eq {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T]
    [Module.Finite R S] [Module.Finite R T] [Algebra.Etale R S] [Algebra.Etale R T]
    {n m : ℕ} (hn : Module.rankAtStalk (R := R) S = n) (hm : Module.rankAtStalk (R := R) T = m)
    (f g : S →ₐ[R] T) :
    Algebra.Etale R (AlgHom.equalizer f g) := by
  wlog hS : Algebra.IsSplitOfRank n R S
  · obtain ⟨A, _, _, _, hA⟩ := Algebra.IsSplitOfRank.exists_isSplitOfRank_tensorProduct hn
    let f' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) f
    let g' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) g
    let cong : A ⊗[R] AlgHom.equalizer f g ≃ₐ[A] AlgHom.equalizer f' g' :=
      AlgHom.tensorEqualizerEquiv A A f g
    have : Algebra.Etale A (AlgHom.equalizer f' g') := by
      apply this (n := n) (m := m)
      · ext p
        rw [Module.rankAtStalk_tensorProduct, hn]
        rfl
      · ext p
        rw [Module.rankAtStalk_tensorProduct, hm]
        rfl
      exact hA
    have : Algebra.Etale A (A ⊗[R] AlgHom.equalizer f g) := Algebra.Etale.of_equiv cong.symm
    exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat A
  clear hn
  wlog hT : Algebra.IsSplitOfRank m R T
  · obtain ⟨A, _, _, _, hA⟩ := Algebra.IsSplitOfRank.exists_isSplitOfRank_tensorProduct hm
    let f' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) f
    let g' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) g
    let cong : A ⊗[R] AlgHom.equalizer f g ≃ₐ[A] AlgHom.equalizer f' g' :=
      AlgHom.tensorEqualizerEquiv A A f g
    have : Algebra.Etale A (AlgHom.equalizer f' g') := by
      apply this (m := m)
      · ext p
        rw [Module.rankAtStalk_tensorProduct, hm]
        rfl
      · infer_instance
      · exact hA
    have : Algebra.Etale A (A ⊗[R] AlgHom.equalizer f g) := Algebra.Etale.of_equiv cong.symm
    exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat A
  apply Algebra.Etale.equalizer_of_isSplitOfRank

set_option maxHeartbeats 0 in
theorem Algebra.Etale.equalizer {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    [Module.Finite R S] [Module.Finite R T] [Algebra.Etale R S] [Algebra.Etale R T]
    (f g : S →ₐ[R] T) :
    Algebra.Etale R (AlgHom.equalizer f g) := by
  wlog h : ∃ (n : ℕ), Module.rankAtStalk (R := R) S = n
  · apply Algebra.etale_of_exists_cover'
    intro p hp
    obtain ⟨r, hr, n, hn⟩ := Algebra.exists_cover_rankAtStalk_eq S p
    use r, hr
    let A := Localization.Away r
    let f' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) f
    let g' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) g
    let cong : A ⊗[R] AlgHom.equalizer f g ≃ₐ[A] AlgHom.equalizer f' g' :=
      AlgHom.tensorEqualizerEquiv A A f g
    have : Algebra.Etale A (AlgHom.equalizer f' g') := by
      apply this
      use n
    exact Algebra.Etale.of_equiv (A := AlgHom.equalizer f' g') cong.symm
  obtain ⟨n, hn⟩ := h
  wlog h : ∃ (m : ℕ), Module.rankAtStalk (R := R) T = m
  · apply Algebra.etale_of_exists_cover'
    intro p hp
    obtain ⟨r, hr, m, hm⟩ := Algebra.exists_cover_rankAtStalk_eq T p
    use r, hr
    let A := Localization.Away r
    let f' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) f
    let g' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) g
    let cong : A ⊗[R] AlgHom.equalizer f g ≃ₐ[A] AlgHom.equalizer f' g' :=
      AlgHom.tensorEqualizerEquiv A A f g
    have : Algebra.Etale A (AlgHom.equalizer f' g') := by
      apply this (n := n)
      · ext p
        rw [Module.rankAtStalk_tensorProduct, hn]
        rfl
      · use m
    exact Algebra.Etale.of_equiv (A := AlgHom.equalizer f' g') cong.symm
  obtain ⟨m, hm⟩ := h
  apply Algebra.Etale.equalizer_of_rankAtStalk_eq hn hm
