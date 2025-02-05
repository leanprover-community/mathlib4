import Mathlib

open TensorProduct

universe u v

section Hard

instance (priority := 900) {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FinitePresentation R S] : Algebra.FinitePresentation R S := by
  sorry

instance (priority := 900) {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S] : Module.FinitePresentation R S :=
  sorry

end Hard

section

variable {R : Type*} [CommSemiring R] (S : Submonoid R) {M M' M'' : Type*}
  [AddCommMonoid M] [AddCommMonoid M']
  [AddCommMonoid M''] [Module R M] [Module R M'] [Module R M'']
  (f : M →ₗ[R] M') (g : M →ₗ[R] M'') [IsLocalizedModule S f]

@[simp]
lemma IsLocalizedModule.iso_symm_apply'' (x) : (iso S f).symm (f x) = LocalizedModule.mk x 1 := by
  show ((iso S f).symm.toLinearMap.comp f) x = _
  --have := iso_symm_comp S f
  rw [iso_symm_comp]
  simp

@[simp]
lemma IsLocalizedModule.iso_mk_one (x) : (iso S f) (LocalizedModule.mk x 1) = f x := by
  simp
  --show ((iso S f).symm.toLinearMap.comp f) x = _
  ----have := iso_symm_comp S f
  --rw [iso_symm_comp]
  --simp

@[simp]
lemma LocalizedModule.lift_mk_one (h : ∀ (x : S), IsUnit ((algebraMap R (Module.End R M'')) x))
    (m : M) :
    (lift S g h) (mk m 1) = g m := by
  conv_rhs => rw [← LocalizedModule.lift_comp S g h]
  simp

@[simp]
lemma IsLocalizedModule.lift_comp_iso
    (h : ∀ (x : S), IsUnit ((algebraMap R (Module.End R M'')) x)) :
    IsLocalizedModule.lift S f g h ∘ₗ iso S f = LocalizedModule.lift S g h := by
  apply IsLocalizedModule.ext S (LocalizedModule.mkLinearMap S M) h
  ext x
  simp

@[simp]
lemma IsLocalizedModule.lift_iso (h : ∀ (x : S), IsUnit ((algebraMap R (Module.End R M'')) x)) (x) :
    IsLocalizedModule.lift S f g h ((iso S f) x) =
      LocalizedModule.lift _ g h x := by
  rw [← IsLocalizedModule.lift_comp_iso S f]
  dsimp

end

section

instance IsLocalizedModule.prodMap {R M N M' N' : Type*} [CommSemiring R] (S : Submonoid R)
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [AddCommMonoid M'] [AddCommMonoid N'] [Module R M'] [Module R N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    [IsLocalizedModule S f] [IsLocalizedModule S g] :
    IsLocalizedModule S (f.prodMap g) := by
  let e₃ : Localization S ⊗[R] (M × N) ≃ₗ[R] M' × N' :=
    TensorProduct.prodRight R (Localization S) M N ≪≫ₗ
        ((isBaseChange S (Localization S)
            (LocalizedModule.mkLinearMap S M)).equiv.restrictScalars R ≪≫ₗ iso S f).prod
        ((isBaseChange S (Localization S)
            (LocalizedModule.mkLinearMap S N)).equiv.restrictScalars R ≪≫ₗ iso S g)
  have : (f.prodMap g) = e₃ ∘ₗ (TensorProduct.mk R (Localization S) (M × N) 1) := by
    ext x : 2 <;> simp [e₃, -IsLocalizedModule.iso_apply, IsBaseChange.equiv_tmul]
  rw [this]
  infer_instance

@[simps!]
def LinearEquiv.extendScalarsOfIsLocalization
    {R : Type*} [CommSemiring R] (S : Submonoid R) (A : Type*)
    [CommSemiring A] [Algebra R A] [IsLocalization S A] {M N : Type*} [AddCommMonoid M] [Module R M]
    [Module A M] [IsScalarTower R A M] [AddCommMonoid N] [Module R N] [Module A N]
    [IsScalarTower R A N] (f : M ≃ₗ[R] N) :
    M ≃ₗ[A] N :=
  .ofLinear (LinearMap.extendScalarsOfIsLocalization S A f)
    (LinearMap.extendScalarsOfIsLocalization S A f.symm)
    (by ext; simp) (by ext; simp)

@[simps]
def LinearEquiv.extendScalarsOfIsLocalizationEquiv
    {R : Type*} [CommSemiring R] (S : Submonoid R) (A : Type*)
    [CommSemiring A] [Algebra R A] [IsLocalization S A] {M N : Type*} [AddCommMonoid M] [Module R M]
    [Module A M] [IsScalarTower R A M] [AddCommMonoid N] [Module R N] [Module A N]
    [IsScalarTower R A N] :
    (M ≃ₗ[R] N) ≃ M ≃ₗ[A] N where
  toFun e := e.extendScalarsOfIsLocalization S A
  invFun e := e.restrictScalars R
  left_inv e := by ext; simp
  right_inv e := by ext; simp

instance {R : Type*} [CommRing R] (S : Submonoid R) (M : Type*) [AddCommMonoid M] [Module R M]
    [Subsingleton M] : Subsingleton (LocalizedModule S M) := by
  rw [LocalizedModule.subsingleton_iff]
  intro m
  use 1, S.one_mem, Subsingleton.elim _ _

instance {R S T : Type*} [CommSemiring R] [Semiring S] [Semiring T] [Algebra R S] [Algebra R T]
    [Subsingleton T] :
    Inhabited (S →ₐ[R] T) where
  default := AlgHom.ofLinearMap default (Subsingleton.elim _ _) (fun _ _ ↦ (Subsingleton.elim _ _))

@[simp]
lemma AlgHom.default_apply {R S T : Type*} [CommSemiring R] [Semiring S] [Semiring T] [Algebra R S]
    [Algebra R T] [Subsingleton T] (x : S) :
    (default : S →ₐ[R] T) x = 0 :=
  rfl

instance {R S T : Type*} [CommSemiring R] [Semiring S] [Semiring T] [Algebra R S] [Algebra R T]
    [Subsingleton S] [Subsingleton T] :
    Inhabited (S ≃ₐ[R] T) where
  default := AlgEquiv.ofAlgHom default default
    (AlgHom.ext fun _ ↦ Subsingleton.elim _ _)
    (AlgHom.ext fun _ ↦ Subsingleton.elim _ _)

@[simp]
lemma AlgEquiv.default_apply {R S T : Type*} [CommSemiring R] [Semiring S] [Semiring T]
    [Algebra R S] [Algebra R T] [Subsingleton S] [Subsingleton T] (x : S) :
    (default : S ≃ₐ[R] T) x = 0 :=
  rfl

instance (R : Type u) [CommRing R] (n : Type) [Finite n] :
    Algebra.Etale R (n → R) where
  formallyEtale :=
    have : Algebra.Etale R R :=
      Algebra.instEtaleOfIsStandardSmoothOfRelativeDimensionOfNatNat.{u, 0, 0}
    have : Algebra.FormallyEtale R R := Algebra.Etale.formallyEtale
    Algebra.FormallyEtale.instForallOfFinite (fun _ : n ↦ R)

instance (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S] :
    Algebra.Smooth R S where

instance (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S] :
    Algebra.Unramified R S where

instance (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S] :
    Module.Flat R S :=
  -- done, but needs to be PRed
  sorry

instance (R S : Type u) [CommRing R] [CommRing S] :
    letI : Algebra (R × S) S := (RingHom.snd R S).toAlgebra
    Algebra.Etale (R × S) S :=
  sorry

instance (R S : Type u) [CommRing R] [CommRing S] :
    letI : Algebra (R × S) R := (RingHom.fst R S).toAlgebra
    Algebra.Etale (R × S) R :=
  sorry

lemma exists_split_of_formallyUnramified (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra S T), Nonempty (S ⊗[R] S ≃ₐ[S] S × T) :=
  sorry

-- in PR
def TensorProduct.AlgebraTensorModule.prodRight (R S M N P : Type*)
    [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module S M] [IsScalarTower R S M] [Module R N] [Module R P] :
    M ⊗[R] (N × P) ≃ₗ[S] M ⊗[R] N × M ⊗[R] P :=
  sorry

-- in PR
@[simp]
lemma TensorProduct.AlgebraTensorModule.prodRight_tmul (R S M N P : Type*)
    [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module S M] [IsScalarTower R S M] [Module R N] [Module R P] (m) (x) :
    prodRight R S M N P (m ⊗ₜ x) = (m ⊗ₜ x.1, m ⊗ₜ x.2) :=
  sorry

lemma Algebra.TensorProduct.map_mul_of_map_mul_tmul {R S A B C : Type*} [CommRing R]
    [CommRing S] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R A] [Algebra R B]
    [Algebra S A] [IsScalarTower R S A] [Algebra S C]
    {f : A ⊗[R] B →ₗ[S] C}
    (hf : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f (a₁ ⊗ₜ b₁ * a₂ ⊗ₜ b₂) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
    (x y : A ⊗[R] B) :
    f (x * y) = f x * f y := by
  induction x with
  | zero => simp
  | add a b ha hb => simp [ha, hb, add_mul]
  | tmul a b =>
      induction y with
      | zero => simp
      | add c d hc hd => simp [hc, hd, mul_add]
      | tmul => apply hf

def Algebra.TensorProduct.prodRight (R S T A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra R A] [Algebra R B] :
    T ⊗[R] (A × B) ≃ₐ[S] T ⊗[R] A × T ⊗[R] B :=
  AlgEquiv.ofLinearEquiv (TensorProduct.AlgebraTensorModule.prodRight R S T A B)
    (by simp [Algebra.TensorProduct.one_def])
    (map_mul_of_map_mul_tmul (fun _ _ _ _ ↦ by simp))

def AlgEquiv.prodCongr {R S T A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra R A] [Algebra R B]
    (l : S ≃ₐ[R] A) (r : T ≃ₐ[R] B) :
    (S × T) ≃ₐ[R] A × B :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.prodCongr l r) <| by simp

def AlgEquiv.funUnique (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (ι : Type*) [Unique ι] :
    (ι → S) ≃ₐ[R] S :=
  AlgEquiv.ofAlgHom (Pi.evalAlgHom R (fun _ ↦ S) default) (Pi.constAlgHom R ι S)
    (by ext; simp) (by ext f i; simp [Unique.default_eq i])

--def AlgEquiv.prodPiEquiv' (R α β : Type*) [CommRing R]
--    (A : α → Type u) (B : β → Type u) [∀ a, CommRing (A a)] [∀ a, Algebra R (A a)]
--    [∀ b, CommRing (B b)] [∀ b, Algebra R (B b)] :
--    (Π a, A a × Π b, B b) ≃ₐ[R] (Π x : α ⊕ β, Sum.elim A B x) :=
--  sorry

def Algebra.prodPiEquiv (R A α β : Type*) [CommRing R] [CommRing A] [Algebra R A] :
    (α ⊕ β → A) ≃ₐ[R] (α → A) × (β → A) :=
  AlgEquiv.ofLinearEquiv (LinearEquiv.sumArrowLequivProdArrow α β R A) rfl <| fun x y ↦ by
    ext <;> simp

def AlgEquiv.piCongrLeft {ι ι' R : Type*} (S : ι → Type*) (e : ι' ≃ ι)
    [CommSemiring R] [∀ i, Semiring (S i)] [∀ i, Algebra R (S i)] :
    (Π i, S (e i)) ≃ₐ[R] Π i, S i :=
  AlgEquiv.ofLinearEquiv (LinearEquiv.piCongrLeft R S e) (by ext; simp) _

noncomputable
def Algebra.TensorProduct.cancelBaseChange (R S T A B : Type*)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R T] [Algebra R A] [Algebra R B]
    [Algebra T A] [IsScalarTower R T A] [Algebra S A]
    [IsScalarTower R S A] [Algebra S T] [IsScalarTower S T A] :
    A ⊗[S] (S ⊗[R] B) ≃ₐ[T] A ⊗[R] B :=
  AlgEquiv.symm <| AlgEquiv.ofLinearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T A B).symm
    (by simp [Algebra.TensorProduct.one_def]) <|
      map_mul_of_map_mul_tmul (fun _ _ _ _ ↦ by simp)

end

section rankAtStalk

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

lemma Module.rankAtStalk_eq_zero_of_subsingleton [Subsingleton M] :
    rankAtStalk (R := R) M = 0 := by
  ext p
  exact Module.finrank_zero_of_subsingleton

lemma Module.rankAtStalk_eq_zero_iff_subsingleton [Module.Flat R M]
      [Module.FinitePresentation R M] :
    rankAtStalk (R := R) M = 0 ↔ Subsingleton M := by
  refine ⟨fun h ↦ ?_, fun _ ↦ rankAtStalk_eq_zero_of_subsingleton⟩
  simp_rw [← Module.support_eq_empty_iff (R := R), Set.eq_empty_iff_forall_not_mem,
    Module.not_mem_support_iff]
  intro p
  have : Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) :=
    free_of_flat_of_isLocalRing
  apply Module.subsingleton_of_rank_zero (R := (Localization.AtPrime p.asIdeal))
  have hr : finrank (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) = 0 :=
    (funext_iff.mp h) p
  simp [← Module.finrank_eq_rank, hr]

lemma Module.rankAtStalk_pi {ι : Type*} [Finite ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Flat R (M i)]
    [∀ i, Module.FinitePresentation R (M i)] (p : PrimeSpectrum R) :
    rankAtStalk (∀ i, M i) p = ∑ᶠ i, rankAtStalk (M i) p := by
  cases nonempty_fintype ι
  let f : (Π i, M i) →ₗ[R] Π i, LocalizedModule p.asIdeal.primeCompl (M i) :=
    LinearMap.pi
      (fun i ↦ LocalizedModule.mkLinearMap p.asIdeal.primeCompl (M i) ∘ₗ LinearMap.proj i)
  have : IsLocalizedModule p.asIdeal.primeCompl f := sorry
  let e : LocalizedModule p.asIdeal.primeCompl (Π i, M i) ≃ₗ[Localization.AtPrime p.asIdeal]
      (Π i, LocalizedModule p.asIdeal.primeCompl (M i)) :=
    (IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl _) f).extendScalarsOfIsLocalization
      p.asIdeal.primeCompl _
  dsimp [rankAtStalk]
  rw [e.finrank_eq]
  have (i : ι) : Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl (M i)) :=
    free_of_flat_of_isLocalRing
  rw [Module.finrank_pi_fintype, finsum_eq_sum_of_fintype]

lemma Module.rankAtStalk_prod (M N : Type*) [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N]
    [Module.Flat R M] [Module.Flat R N]
    [Module.FinitePresentation R M] [Module.FinitePresentation R N]
    (p : PrimeSpectrum R) :
    rankAtStalk (M × N) p = rankAtStalk M p + rankAtStalk N p := by
  let e : (LocalizedModule p.asIdeal.primeCompl (M × N)) ≃ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule p.asIdeal.primeCompl M × LocalizedModule p.asIdeal.primeCompl N :=
    (IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl _)
      (LinearMap.prodMap (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N))).extendScalarsOfIsLocalization
      p.asIdeal.primeCompl _
  dsimp [rankAtStalk]
  have : Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl N) :=
    free_of_flat_of_isLocalRing
  have : Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) :=
    free_of_flat_of_isLocalRing
  simp [e.finrank_eq]

lemma Module.rankAtStalk_tensorProduct {S : Type*} [CommRing S] [Algebra R S]
    [Module.Flat R M] [Module.FinitePresentation R M]
    (p : PrimeSpectrum S) :
    rankAtStalk (S ⊗[R] M) p = rankAtStalk M ((algebraMap R S).specComap p) := by
  dsimp [rankAtStalk]
  let q : PrimeSpectrum R := ((algebraMap R S).specComap p)
  letI : Algebra (Localization.AtPrime q.asIdeal) (Localization.AtPrime p.asIdeal) :=
    (Localization.localRingHom q.asIdeal p.asIdeal (algebraMap R S) rfl).toAlgebra
  have : IsScalarTower R (Localization.AtPrime q.asIdeal) (Localization.AtPrime p.asIdeal) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    simp [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map,
      IsScalarTower.algebraMap_apply R S (Localization.AtPrime p.asIdeal)]
  let e₁ : (LocalizedModule p.asIdeal.primeCompl (S ⊗[R] M)) ≃ₗ[Localization.AtPrime p.asIdeal]
      (Localization.AtPrime p.asIdeal) ⊗[S] (S ⊗[R] M) := by
    refine (IsBaseChange.equiv (f := ?_) ?_).symm
    · exact LocalizedModule.mkLinearMap p.asIdeal.primeCompl (S ⊗[R] M)
    · apply IsLocalizedModule.isBaseChange p.asIdeal.primeCompl
  let e₂ : (LocalizedModule q.asIdeal.primeCompl M) ≃ₗ[Localization.AtPrime q.asIdeal]
      (Localization.AtPrime q.asIdeal) ⊗[R] M := by
    refine (IsBaseChange.equiv (f := ?_) ?_).symm
    · exact LocalizedModule.mkLinearMap q.asIdeal.primeCompl M
    · apply IsLocalizedModule.isBaseChange q.asIdeal.primeCompl
  let e : (LocalizedModule p.asIdeal.primeCompl (S ⊗[R] M)) ≃ₗ[Localization.AtPrime p.asIdeal]
      (Localization.AtPrime p.asIdeal) ⊗[Localization.AtPrime q.asIdeal]
        (LocalizedModule q.asIdeal.primeCompl M) :=
    e₁ ≪≫ₗ (TensorProduct.AlgebraTensorModule.cancelBaseChange
        R S _ (Localization.AtPrime p.asIdeal) M) ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange
        R (Localization.AtPrime q.asIdeal) _ _ M).symm ≪≫ₗ
        (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) e₂.symm)
  rw [e.finrank_eq]
  have : Free (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl M) :=
    free_of_flat_of_isLocalRing
  apply Module.finrank_baseChange

noncomputable
def IsLocalizedModule.mapEquiv {R : Type*} [CommSemiring R] (S : Submonoid R)
    (A : Type*) {M N M' N' : Type*} [CommSemiring A] [Algebra R A] [IsLocalization S A]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid M'] [AddCommMonoid N']
    [Module R M] [Module R N] [Module R M'] [Module R N']
    [Module A M'] [Module A N'] [IsScalarTower R A M'] [IsScalarTower R A N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N') [IsLocalizedModule S f] [IsLocalizedModule S g]
    (e : M ≃ₗ[R] N) :
    M' ≃ₗ[A] N' :=
  LinearEquiv.ofLinear
    (IsLocalizedModule.mapExtendScalars S f g A e)
    (IsLocalizedModule.mapExtendScalars S g f A e.symm)
    (by
      apply LinearMap.restrictScalars_injective R
      apply IsLocalizedModule.linearMap_ext S g g
      ext
      simp)
    (by
      apply LinearMap.restrictScalars_injective R
      apply IsLocalizedModule.linearMap_ext S f f
      ext
      simp)

lemma Module.rankAtStalk_eq_of_equiv {N : Type*} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    rankAtStalk (R := R) M = rankAtStalk N := by
  ext p
  dsimp [rankAtStalk]
  exact IsLocalizedModule.mapEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N) e |>.finrank_eq

lemma Module.rankAtStalk_eq_finrank_of_free [Module.Free R M] :
    rankAtStalk (R := R) M = Module.finrank R M := by
  ext p
  simp [rankAtStalk, Module.finrank_of_isLocalizedModule_of_free _ p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)]

lemma Module.nontrivial_of_rankAtStalk_gt_zero (p : PrimeSpectrum R)
    (h : rankAtStalk (R := R) M p > 0) :
    Nontrivial M := by
  by_contra! hn
  have : Subsingleton M := not_nontrivial_iff_subsingleton.mp hn
  have := Module.finrank_zero_of_subsingleton (R := Localization.AtPrime p.asIdeal)
    (M := LocalizedModule p.asIdeal.primeCompl M)
  simp [rankAtStalk, this] at h

@[simp]
lemma Module.rankAtStalk_self [Nontrivial R] : rankAtStalk (R := R) R = 1 := by
  simp [rankAtStalk_eq_finrank_of_free]

end rankAtStalk

class Algebra.IsSplitOfRank (n : outParam ℕ) (R S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] : Prop where
  nonempty_algEquiv_fun' : Nonempty (S ≃ₐ[R] Fin n → R)

namespace Algebra.IsSplitOfRank

section

variable {n : ℕ}
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

variable (n R S) in
lemma nonempty_algEquiv_fun [IsSplitOfRank n R S] : Nonempty (S ≃ₐ[R] Fin n → R) :=
  nonempty_algEquiv_fun'

instance {T : Type*} [CommRing T] [Algebra R T] [IsSplitOfRank n R S] :
    IsSplitOfRank n T (T ⊗[R] S) := by
  obtain ⟨e⟩ := Algebra.IsSplitOfRank.nonempty_algEquiv_fun n R S
  refine ⟨⟨?_⟩⟩
  exact (Algebra.TensorProduct.congr AlgEquiv.refl e).trans
    ((Algebra.TensorProduct.piRight R T T (fun _ : Fin n ↦ R)).trans <|
      AlgEquiv.piCongrRight fun i ↦ TensorProduct.rid R T T)

lemma of_equiv {S' : Type*} [CommRing S'] [Algebra R S'] (e : S ≃ₐ[R] S') [IsSplitOfRank n R S] :
    IsSplitOfRank n R S' := by
  obtain ⟨f⟩ := nonempty_algEquiv_fun n R S
  exact ⟨⟨e.symm.trans f⟩⟩

lemma iff_subsingleton_of_isEmpty (hn : n = 0) :
    IsSplitOfRank n R S ↔ Subsingleton S := by
  subst hn
  exact ⟨fun ⟨⟨e⟩⟩ ↦ e.subsingleton, fun hs ↦ ⟨⟨default⟩⟩⟩

lemma of_card_eq {ι : Type*} [Finite ι] (h : Nat.card ι = n) (e : S ≃ₐ[R] ι → R) :
    IsSplitOfRank n R S := by
  cases nonempty_fintype ι
  let f : (ι → R) ≃ₐ[R] (Fin n → R) := AlgEquiv.piCongrLeft _
    (Fintype.equivOfCardEq (by simpa using h.symm))
  refine ⟨⟨e.trans f⟩⟩

lemma of_subsingleton [Subsingleton R] : IsSplitOfRank n R S := by
  have : Subsingleton S := RingHom.codomain_trivial (algebraMap R S)
  exact ⟨⟨default⟩⟩

end

section

variable {n : ℕ} {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

instance [IsSplitOfRank n R S] : Etale R S := by
  obtain ⟨e⟩ := Algebra.IsSplitOfRank.nonempty_algEquiv_fun n R S
  exact Algebra.Etale.of_equiv e.symm

lemma exists_isSplitOfRank_tensorProduct [Etale R S] [Module.Finite R S] {n : ℕ}
    (hn : Module.rankAtStalk (R := R) S = n) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
      IsSplitOfRank n T (T ⊗[R] S) := by
  induction n generalizing R S with
  | zero =>
      use R, inferInstance, inferInstance
      let e : R ⊗[R] S ≃ₐ[R] S := TensorProduct.lid R S
      have : IsSplitOfRank 0 R S := by
        rw [iff_subsingleton_of_isEmpty]
        simp only [Nat.cast_zero] at hn
        rwa [Module.rankAtStalk_eq_zero_iff_subsingleton] at hn
        rfl
      apply IsSplitOfRank.of_equiv e.symm
  | succ n ih =>
      cases subsingleton_or_nontrivial R
      · use R, inferInstance, inferInstance
        have : IsSplitOfRank (n + 1) R S := .of_subsingleton
        apply IsSplitOfRank.of_equiv (TensorProduct.lid R S).symm
      have : Nontrivial S := by
        apply Module.nontrivial_of_rankAtStalk_gt_zero (R := R) (p := Nonempty.some inferInstance)
        simp [hn]
      obtain ⟨U, _, _, ⟨e⟩⟩ := exists_split_of_formallyUnramified R S
      algebraize [RingHom.snd S U]
      have : IsScalarTower S (S × U) U := IsScalarTower.of_algebraMap_eq' rfl
      have : Etale S U := by
        have : Etale S (S × U) := Etale.of_equiv e
        apply Etale.comp S (S × U) U
      have : Module.Finite S U := by
        have : Module.Finite S (S × U) := Module.Finite.equiv e.toLinearEquiv
        have : Module.Finite (S × U) U :=
          Module.Finite.of_surjective (Algebra.linearMap (S × U) U) (RingHom.snd S U).surjective
        apply Module.Finite.trans (S × U)
      have (p : PrimeSpectrum S) : Module.rankAtStalk (R := S) (S × U) p = n + 1 := by
        rw [Module.rankAtStalk_eq_of_equiv e.symm.toLinearEquiv]
        simp [Module.rankAtStalk_tensorProduct, hn]
      -- why does instance search not find this instance?
      have h : Module.Flat S S := inferInstance
      simp_rw [Module.rankAtStalk_prod , Module.rankAtStalk_self, Pi.one_apply] at this
      have : Module.rankAtStalk (R := S) U = n := by
        ext p
        simp only [Pi.natCast_def, Nat.cast_id]
        have := this p
        omega
      obtain ⟨V, _, _, hV⟩ := ih this
      obtain ⟨f⟩ := hV.nonempty_algEquiv_fun
      algebraize [(algebraMap S V).comp (algebraMap R S)]
      let e₁ : V ⊗[R] S ≃ₐ[V] V ⊗[S] (S ⊗[R] S) :=
        (Algebra.TensorProduct.cancelBaseChange R S V V S).symm
      let e₂ : V ⊗[S] (S ⊗[R] S) ≃ₐ[V] V ⊗[S] (S × U) :=
        TensorProduct.congr AlgEquiv.refl e
      let e₃ : V ⊗[S] (S × U) ≃ₐ[V] V ⊗[S] S × V ⊗[S] U :=
        TensorProduct.prodRight S V V S U
      let e₄ : (V ⊗[S] S × V ⊗[S] U) ≃ₐ[V] V × (Fin n → V) :=
        AlgEquiv.prodCongr (TensorProduct.rid S V V) f
      let e₅ : (V × (Fin n → V)) ≃ₐ[V] (Unit ⊕ Fin n) → V :=
        AlgEquiv.trans (AlgEquiv.prodCongr (AlgEquiv.funUnique _ _ _).symm AlgEquiv.refl)
          (Algebra.prodPiEquiv V V Unit (Fin n))
      let e := e₁.trans <| e₂.trans <| e₃.trans <| e₄.trans e₅
      refine ⟨V, inferInstance, inferInstance, ?_⟩
      exact IsSplitOfRank.of_card_eq (ι := Unit ⊕ Fin n) (by simp [add_comm]) e

end

end Algebra.IsSplitOfRank

class Algebra.IsSplit (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : Prop where
