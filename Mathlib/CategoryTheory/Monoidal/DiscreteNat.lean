import Mathlib.Algebra.Group.Nat
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.CategoryTheory.Functor.Currying

namespace CategoryTheory

namespace MonoidalCategory

variable {C D : Type*} [Category C] [Category D]
  [MonoidalCategory C] [MonoidalCategory D] (X : C)

def powerNat : ℕ → C
  | 0 => 𝟙_ C
  | 1 => X
  | n + 2 => powerNat (n + 1) ⊗ X

def powerNatZero : powerNat X 0 ≅ 𝟙_ C := Iso.refl _

def powerNatOne : powerNat X 1 ≅ X := Iso.refl _

def powerNatSucc : ∀ (n : ℕ), powerNat X (n + 1) ≅ powerNat X n ⊗ X
  | 0 => (λ_ X).symm
  | _ + 1 => Iso.refl _

def powerNatAdd : ∀ (a b : ℕ), powerNat X (a + b) ≅ powerNat X a ⊗ powerNat X b
  | a, 0 => (ρ_ (powerNat X a)).symm
  | a, b + 1 => powerNatSucc X (a + b) ≪≫ (powerNatAdd a b ⊗ Iso.refl _) ≪≫
      α_ _ _ _ ≪≫ (Iso.refl _ ⊗ (powerNatSucc X b).symm)

noncomputable def mapPowerNatIso (F : MonoidalFunctor C D) (X : C) :
    ∀ (n : ℕ), F.obj (powerNat X n) ≅ powerNat (F.obj X) n
  | 0 => F.εIso.symm
  | 1 => Iso.refl _
  | n + 2 => F.mapIso (powerNatSucc X (n + 1)) ≪≫ (F.μIso _  _).symm ≪≫
        (mapPowerNatIso F X (n + 1) ⊗ Iso.refl _) ≪≫ (powerNatSucc _ _).symm

end MonoidalCategory

namespace FreeMonoidalCategory

open MonoidalCategory

abbrev toDiscreteNat : MonoidalFunctor (FreeMonoidalCategory _root_.Unit) (Discrete ℕ) :=
  FreeMonoidalCategory.project (fun _ => Discrete.mk 1)

@[simp]
def len {X : Type*} : FreeMonoidalCategory X → ℕ
  | unit => 0
  | of _ => 1
  | tensor x y => x.len + y.len

def isoPowerNatOf :
    ∀ (A : FreeMonoidalCategory _root_.Unit),
      A ≅ powerNat (FreeMonoidalCategory.of Unit.unit) A.len
  | unit => Iso.refl _
  | of _ => Iso.refl _
  | tensor x y => (isoPowerNatOf x ⊗ isoPowerNatOf y) ≪≫
      (powerNatAdd (FreeMonoidalCategory.of Unit.unit) x.len y.len).symm

@[simp]
lemma len_powerNat_of {X : Type*} (x : X) (n : ℕ) :
    (powerNat (FreeMonoidalCategory.of x) n).len = n := by
  induction' n with n hn
  · rfl
  · obtain _ | n := n
    · rfl
    · unfold powerNat
      simpa using hn

@[simp]
lemma toDiscreteNat_obj_eq (A : FreeMonoidalCategory _root_.Unit) :
    toDiscreteNat.obj A = Discrete.mk A.len := by
  ext
  dsimp
  induction' A with _ a b ha hb
  · rfl
  · rfl
  · change _ = _ + _
    rw [← ha, ← hb]
    rfl

instance : toDiscreteNat.EssSurj where
  mem_essImage := fun ⟨n⟩ =>
    ⟨powerNat (FreeMonoidalCategory.of Unit.unit) n, ⟨eqToIso (by simp)⟩⟩

noncomputable instance : toDiscreteNat.Full where
  preimage {a b} f :=
    a.isoPowerNatOf.hom ≫ eqToHom (by rw [show a.len = b.len by simpa using f.1.1]) ≫
      b.isoPowerNatOf.inv

instance : toDiscreteNat.Faithful where
  map_injective  _ := Subsingleton.elim _ _

@[simps]
def discreteNatEquivalence : FreeMonoidalCategory _root_.Unit ≌ Discrete ℕ where
  functor := toDiscreteNat.toFunctor
  inverse := Discrete.functor (powerNat (FreeMonoidalCategory.of Unit.unit))
  unitIso := NatIso.ofComponents (fun x => isoPowerNatOf x ≪≫ eqToIso (by simp)) (by aesop_cat)
  counitIso := NatIso.ofComponents (fun ⟨n⟩ => eqToIso (by simp)) (by aesop_cat)

noncomputable instance : toDiscreteNat.IsEquivalence  :=
  Functor.IsEquivalence.ofEquivalence discreteNatEquivalence

noncomputable def fromDiscreteNat :
    MonoidalFunctor (Discrete ℕ) (FreeMonoidalCategory _root_.Unit) :=
  monoidalInverse toDiscreteNat

@[simp]
lemma fromDiscreteNat_toFunctor :
    fromDiscreteNat.toFunctor =
      Discrete.functor (powerNat (FreeMonoidalCategory.of Unit.unit)) := rfl

end FreeMonoidalCategory

namespace MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C] (X : C)

noncomputable def fromDiscreteNat' : MonoidalFunctor (Discrete ℕ) C :=
  FreeMonoidalCategory.fromDiscreteNat.comp (FreeMonoidalCategory.project (fun _ => X))

noncomputable def fromDiscreteNat'ObjIso (n : ℕ) :
    (fromDiscreteNat' X).obj ⟨n⟩ ≅ powerNat X n :=
  mapPowerNatIso (FreeMonoidalCategory.project (fun (_ : _root_.Unit) => X))
    (FreeMonoidalCategory.of Unit.unit) n

end MonoidalCategory

end CategoryTheory
