import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.Localization

open TensorProduct

universe u v

section Equalizer

def LinearMap.toEqLocus {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f g : M →ₗ[R] N)
    {P : Type*} [AddCommMonoid P] [Module R P] (u : P →ₗ[R] M) (hu : f ∘ₗ u = g ∘ₗ u) :
    P →ₗ[R] eqLocus f g :=
  sorry

def AlgHom.toEqualizer {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f g : A →ₐ[R] B)
    {C : Type*} [Semiring C] [Algebra R C] (u : C →ₐ[R] A)
    (hu : f.comp u = g.comp u) :
    C →ₐ[R] equalizer f g :=
  AlgHom.codRestrict u (equalizer f g) (fun c ↦ DFunLike.congr_fun hu c)

def AlgHom.equalizerCongr {R A A' B B' : Type*} [CommSemiring R]
    [Semiring A] [Semiring A'] [Semiring B] [Semiring B']
    [Algebra R A] [Algebra R A'] [Algebra R B] [Algebra R B']
    (eA : A ≃ₐ[R] A') (eB : B ≃ₐ[R] B')
    (f g : A →ₐ[R] B) (f' g' : A' →ₐ[R] B')
    (H : eB.toAlgHom.comp f = f'.comp eA) :
    AlgHom.equalizer f g ≃ₐ[R] AlgHom.equalizer f' g' :=
  sorry

def AlgHom.equalizerCongrOfEq {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] {f g f' g' : A →ₐ[R] B}
    (hf : f = f') (hg : g = g') :
    AlgHom.equalizer f g ≃ₐ[R] AlgHom.equalizer f' g' :=
  sorry

end Equalizer

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

end rankAtStalk

section Etale

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

lemma Algebra.etale_of_exists_cover' {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S]
    (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      Algebra.Etale (Localization.Away r) (Localization.Away r ⊗[R] S)) :
  Algebra.Etale R S := sorry

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

def Function.coequalizer {E : Type u} {F : Type v} (σ τ : E → F) : Type v := sorry

def Function.Coequalizer.mk (σ τ : E → F) (f : F) : Function.coequalizer σ τ :=
  sorry

lemma Function.Coequalizer.condition (σ τ : E → F) (e : E) :
    Function.Coequalizer.mk σ τ (σ e) = Function.Coequalizer.mk σ τ (τ e) :=
  sorry

lemma Function.Coequalizer.mk_surjective (σ τ : E → F) :
    Function.Surjective (Function.Coequalizer.mk σ τ) :=
  sorry

def Function.Coequalizer.desc (σ τ : E → F) {G : Type*} (u : F → G)
    (hu : u ∘ σ = u ∘ τ) :
    Function.coequalizer σ τ → G :=
  sorry

@[simp]
lemma Function.Coequalizer.desc_mk (σ τ : E → F) {G : Type*} (u : F → G)
    (hu : u ∘ σ = u ∘ τ) (f : F) :
    desc σ τ u hu (mk σ τ f) = u f :=
  sorry

instance [Finite F] (σ τ : E → F) : Finite (Function.coequalizer σ τ) :=
  Finite.of_surjective _ (Function.Coequalizer.mk_surjective σ τ)

def RingHom.compRight (R : Type*) [CommRing R] {E F : Type*} (σ : E → F) :
    (F → R) →+* (E → R) :=
  Pi.ringHom (fun f ↦ Pi.evalRingHom _ (σ f))

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

lemma RingHom.eq_compRight_of_isLocalHom {R E F : Type*} [CommRing R] (f : (E → R) →+* F → R)
    [IsLocalRing R] [IsLocalHom f] :
    ∃ (σ : F → E), f = .compRight R σ :=
  sorry

open Localization in
lemma AlgHom.exists_cover_eq_compRight'' {R E F : Type*} [CommRing R] (f : (E → R) →ₐ[R] F → R)
    (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p, ∃ (σ : F → E),
      Algebra.TensorProduct.map (.id (Away r) (Away r)) f =
        Algebra.TensorProduct.map (.id (Away r) (Away r)) (.compRight _ _ σ) :=
  sorry

set_option maxHeartbeats 0 in
open Localization in
lemma AlgHom.exists_cover_eq_compRight''₂ {R E F : Type*} [CommRing R] (f g : (E → R) →ₐ[R] F → R)
    (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p, ∃ (σ τ : F → E),
      Algebra.TensorProduct.map (.id (Away r) (Away r)) f =
        Algebra.TensorProduct.map (.id (Away r) (Away r)) (.compRight _ _ σ) ∧
      Algebra.TensorProduct.map (.id (Away r) (Away r)) g =
        Algebra.TensorProduct.map (.id (Away r) (Away r)) (.compRight _ _ τ) := by
  obtain ⟨r, hr, σ, hσ⟩ := AlgHom.exists_cover_eq_compRight'' f p
  obtain ⟨r', hr', τ, hτ⟩ := AlgHom.exists_cover_eq_compRight'' g p
  letI : Algebra (Localization.Away r) (Localization.Away (r * r')) :=
    (IsLocalization.map (M := .powers r) (T := .powers (r * r'))
      (Localization.Away (r * r')) (RingHom.id R) sorry).toAlgebra
  letI : Algebra (Localization.Away r') (Localization.Away (r * r')) :=
    (IsLocalization.map (M := .powers r') (T := .powers (r * r'))
      (Localization.Away (r * r')) (RingHom.id R) sorry).toAlgebra
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

lemma Algebra.Etale.equalizer_fun {R : Type u} {E F : Type} [CommRing R] [Finite E] [Finite F]
    (f g : (E → R) →ₐ[R] (F → R)) :
    Algebra.Etale R (AlgHom.equalizer f g) := by
  apply Algebra.etale_of_exists_cover'
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
  apply Algebra.Etale.of_equiv cong.symm

lemma Algebra.Etale.equalizer_of_isSplitOfRank {R S T : Type u} {n m : ℕ} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] [Algebra.IsSplitOfRank n R S] [Algebra.IsSplitOfRank m R T] (f g : S →ₐ[R] T) :
    Algebra.Etale R (AlgHom.equalizer f g) := by
  obtain ⟨eS⟩ := Algebra.IsSplitOfRank.nonempty_algEquiv_fun n R S
  obtain ⟨eT⟩ := Algebra.IsSplitOfRank.nonempty_algEquiv_fun m R T
  let f' : (Fin n → R) →ₐ[R] Fin m → R := eT.toAlgHom.comp (f.comp eS.symm)
  let g' : (Fin n → R) →ₐ[R] Fin m → R := eT.toAlgHom.comp (g.comp eS.symm)
  have : Algebra.Etale R (AlgHom.equalizer f' g') := Algebra.Etale.equalizer_fun f' g'
  let cong : AlgHom.equalizer f g ≃ₐ[R] AlgHom.equalizer f' g' :=
    AlgHom.equalizerCongr eS eT f g f' g' (by ext; simp [f', g'])
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
