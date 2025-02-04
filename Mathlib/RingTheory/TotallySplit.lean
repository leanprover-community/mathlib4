import Mathlib

open TensorProduct

universe u v

section

instance (priority := 900) {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FinitePresentation R S] : Algebra.FinitePresentation R S :=
  sorry

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

lemma exists_split_of_formallyUnramified (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra S T), Nonempty (S ⊗[R] S ≃ₐ[S] S × T) :=
  sorry

def TensorProduct.AlgebraTensorModule.prodRight (R S M N P : Type*)
    [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module S M] [IsScalarTower R S M] [Module R N] [Module R P] :
    M ⊗[R] (N × P) ≃ₗ[S] M ⊗[R] N × M ⊗[R] P :=
  sorry

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

def Algebra.funEquivOfUnique (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
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
    ((α → A) × (β → A)) ≃ₐ[R] (α ⊕ β → A) :=
  sorry

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

lemma Module.rankAtStalk_eq_zero_iff_subsingleton :
    rankAtStalk (R := R) M = 0 ↔ Subsingleton M :=
  sorry

lemma Module.rankAtStalk_pi {ι : Type*} (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (p : PrimeSpectrum R) :
    rankAtStalk (∀ i, M i) p = ∑ᶠ i, rankAtStalk (M i) p :=
  sorry

lemma Module.rankAtStalk_prod (M N : Type*) [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] (p : PrimeSpectrum R) :
    rankAtStalk (M × N) p = rankAtStalk M p + rankAtStalk N p :=
  sorry

lemma Module.rankAtStalk_tensorProduct {S : Type*} [CommRing S] [Algebra R S]
    (p : PrimeSpectrum S) :
    rankAtStalk (S ⊗[R] M) p = rankAtStalk M ((algebraMap R S).specComap p) :=
  sorry

lemma Module.rankAtStalk_eq_of_equiv {N : Type*} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    rankAtStalk (R := R) M = rankAtStalk N :=
  sorry

@[simp]
lemma Module.rankAtStalk_self : rankAtStalk (R := R) R = 1 := sorry

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
    IsSplitOfRank n R S' :=
  sorry

lemma iff_subsingleton_of_isEmpty (hn : n = 0) :
    IsSplitOfRank n R S ↔ Subsingleton S :=
  sorry

lemma of_card_eq {ι : Type*} [Finite ι] (h : Nat.card ι = n) (e : S ≃ₐ[R] ι → R) :
    IsSplitOfRank n R S :=
  sorry

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
      obtain ⟨U, _, _, ⟨e⟩⟩ := exists_split_of_formallyUnramified R S
      -- let g : S →+* U := ((RingHom.snd S U).comp e).comp (algebraMap S (S ⊗[R] S))
      algebraize [RingHom.snd S U]
      have : IsScalarTower S (S × U) U := IsScalarTower.of_algebraMap_eq' rfl
      have : Etale S U := by
        have : Etale S (S × U) := Etale.of_equiv e
        have : Etale (S × U) U := by
          -- it is an open immersion
          sorry
        apply Etale.comp S (S × U) U
      have : Module.Finite S U := by
        have : Module.Finite S (S × U) := Module.Finite.equiv e.toLinearEquiv
        have : Module.Finite (S × U) U := by
          -- structure map is surjective
          sorry
        apply Module.Finite.trans (S × U)
      have (p : PrimeSpectrum S) : Module.rankAtStalk (R := S) (S × U) p = n + 1 := by
        rw [Module.rankAtStalk_eq_of_equiv e.symm.toLinearEquiv]
        simp [Module.rankAtStalk_tensorProduct, hn]
      simp_rw [Module.rankAtStalk_prod, Module.rankAtStalk_self, Pi.one_apply] at this
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
        AlgEquiv.trans (AlgEquiv.prodCongr (Algebra.funEquivOfUnique _ _ _).symm AlgEquiv.refl)
          (Algebra.prodPiEquiv V V Unit (Fin n))
      let e := e₁.trans <| e₂.trans <| e₃.trans <| e₄.trans e₅
      refine ⟨V, inferInstance, inferInstance, ?_⟩
      exact IsSplitOfRank.of_card_eq (ι := Unit ⊕ Fin n) (by simp [add_comm]) e

end

end Algebra.IsSplitOfRank

class Algebra.IsSplit (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : Prop where
