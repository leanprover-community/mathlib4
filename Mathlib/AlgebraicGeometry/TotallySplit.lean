import Mathlib

suppress_compilation

universe u

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

open TensorProduct IsLocalRing AlgebraicGeometry CategoryTheory Limits

def degree {X S : Scheme.{u}} (f : X ⟶ S) : X → ℕ := sorry

namespace AlgebraicGeometry

def Scheme.trivialCover (X : Scheme.{u}) (n : ℕ) :
    (∐ fun _ : Fin n ↦ X) ⟶ X :=
  Sigma.desc (fun _ ↦ 𝟙 X)

def trivialCover' (X : ℕ → Scheme.{u}) :
    (∐ fun n : ℕ ↦ (∐ fun _ : Fin n ↦ X n)) ⟶ ∐ X :=
  Sigma.desc (fun n ↦ Sigma.desc fun _ : Fin n ↦ Sigma.ι X n)

class IsSplitOfDegree (n : outParam ℕ) {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  is_split : Nonempty (Over.mk f ≅ Over.mk (S.trivialCover n))

namespace IsSplitOfDegree

lemma trivialCover (S : Scheme.{u}) (n : ℕ) :
    IsSplitOfDegree n (S.trivialCover n) where
  is_split := ⟨Iso.refl _⟩

instance (priority := 900) (n : ℕ) {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSplitOfDegree n f] : IsFinite f :=
  sorry

lemma iff_exists_cofan (n : ℕ) {X S : Scheme.{u}} (f : X ⟶ S) :
    IsSplitOfDegree n f ↔ True :=
  sorry

end IsSplitOfDegree

lemma degree_eq_of_isSplitOfDegree {X S : Scheme.{u}} (f : X ⟶ S) {n : ℕ}
    [IsSplitOfDegree n f] : degree f = n :=
  sorry

inductive IsSplitAux : {X Y : Scheme.{u}} → (X ⟶ Y) → Prop where
  | empty {X S : Scheme.{u}} (f : X ⟶ S) [IsEmpty X] : IsSplitAux f
  | cons {X S Y : Scheme.{u}} (f : X ⟶ S) (hf : IsSplitAux f) (n : ℕ) :
      IsSplitAux (coprod.map f (Y.trivialCover n))

class IsSplit {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  is_coprod : ∃ (X : ℕ → Scheme.{u}), Nonempty (Arrow.mk f ≅ Arrow.mk (trivialCover' X))

instance (priority := 900) IsSplit.of_isSplitOfDegree {X S : Scheme.{u}} (f : X ⟶ S)
    (n : ℕ) [IsSplitOfDegree n f] : IsSplit f :=
  sorry

namespace IsSplit

variable {X S : Scheme.{u}} (f : X ⟶ S)

instance (priority := 900) [IsSplit f] : IsFinite f :=
  sorry

instance (priority := 900) [IsSplit f] : IsFinite f :=
  sorry

end IsSplit

theorem main_aux (n : ℕ) {X S : Scheme.{u}} (f : X ⟶ S) (hn : degree f = n)
    [IsEtale f] [IsFinite f] :
    ∃ (W : Scheme.{u}) (g : W ⟶ S),
      Flat g ∧ Surjective g ∧ IsFinite g ∧ IsSplit (pullback.snd f g) :=
  sorry

theorem main {X S : Scheme.{u}} (f : X ⟶ S) [IsEtale f] [IsFinite f] :
    ∃ (W : Scheme.{u}) (g : W ⟶ S),
      Flat g ∧ Surjective g ∧ IsFinite g ∧ IsSplit (pullback.snd f g) :=
  sorry

end AlgebraicGeometry
