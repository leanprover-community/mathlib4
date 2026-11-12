module

import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.Tactic.Transport.Test

namespace TransportYoneda

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj TransportTest

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] {A : C}

abbrev elems (f : A ⊗ A ⟶ A) : ∀ T : C, (T ⟶ A) → (T ⟶ A) → (T ⟶ A) :=
  fun _ x y ↦ lift x y ≫ f

abbrev HomRel : (A ⊗ A ⟶ A) → (∀ T : C, (T ⟶ A) → (T ⟶ A) → (T ⟶ A)) → Prop :=
  MapRel elems

instance : MapTransport (HomRel (A := A)) elems where

theorem elems_injective : Function.Injective (elems (A := A)) := by
  intro f g h
  have := congr_fun (congr_fun (congr_fun h (A ⊗ A)) (fst A A)) (snd A A)
  simpa [elems] using this

instance : InjMapClass (A ⊗ A ⟶ A) (∀ T : C, (T ⟶ A) → (T ⟶ A) → (T ⟶ A)) :=
  MapRel.instInjMapClass elems_injective

@[transport]
theorem transport_braiding_comp [BraidedCategory C] {g : A ⊗ A ⟶ A}
    {φ : ∀ T : C, (T ⟶ A) → (T ⟶ A) → (T ⟶ A)} (h : HomRel g φ) :
    HomRel ((β_ A A).hom ≫ g) (fun T x y ↦ φ T y x) := by
  subst h
  funext T x y
  simp [elems]

variable [GrpObj A]

@[transport]
theorem transport_mul : HomRel (A := A) μ (fun _ x y ↦ x * y) := by
  rfl

@[transport]
theorem transport_comp_inv {g : A ⊗ A ⟶ A} {φ : ∀ T : C, (T ⟶ A) → (T ⟶ A) → (T ⟶ A)}
    (h : HomRel g φ) : HomRel (g ≫ ι) (fun T x y ↦ (φ T x y)⁻¹) := by
  subst h
  funext T x y
  simp [elems, Hom.inv_def]

@[transport]
theorem transport_inv_inv_comp {g : A ⊗ A ⟶ A} {φ : ∀ T : C, (T ⟶ A) → (T ⟶ A) → (T ⟶ A)}
    (h : HomRel g φ) : HomRel ((ι[A] ⊗ₘ ι) ≫ g) (fun T x y ↦ φ T x⁻¹ y⁻¹) := by
  subst h
  funext T x y
  simp [elems, Hom.inv_def]

example [BraidedCategory C] : μ ≫ ι = (β_ A A).hom ≫ (ι[A] ⊗ₘ ι) ≫ μ := by
  transport (A ⊗ A ⟶ A) to (∀ T : C, (T ⟶ A) → (T ⟶ A) → (T ⟶ A))
  guard_target = (fun (T : C) (x y : T ⟶ A) ↦ (x * y)⁻¹) = fun T x y ↦ y⁻¹ * x⁻¹
  funext T x y
  exact mul_inv_rev x y

end TransportYoneda
