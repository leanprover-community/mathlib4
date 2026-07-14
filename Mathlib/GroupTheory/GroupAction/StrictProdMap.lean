import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.Prod
import Mathlib.Algebra.Group.Hom.Defs

namespace MonoidHom

variable {A B C D : Type*} [Monoid A] [Monoid B] [Monoid C] [Monoid D]

/-- `Prod.map` of two strict monoid homomorphisms is a strict monoid homomorphism.
This shows that the property of being strict is preserved under product formation. -/
def prodMapStrict (f : A →* B) (g : C →* D) (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (Prod.map f g) := by
  intro ⟨a₁, c₁⟩ ⟨a₂, c₂⟩ h
  simp only [Prod.map_apply] at h
  have ha : f a₁ = f a₂ := by simp [Prod.ext_iff] at h; exact h.1
  have hc : g c₁ = g c₂ := by simp [Prod.ext_iff] at h; exact h.2
  simp [Prod.ext_iff, hf ha, hg hc]

end MonoidHom

namespace GroupHom

variable {A B C D : Type*} [Group A] [Group B] [Group C] [Group D]

/-- `Prod.map` of two strict group homomorphisms is a strict group homomorphism.
If f and g are injective group homomorphisms, their product map is also injective. -/
theorem prodMap_strictness (f : A →* B) (g : C →* D) (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (Prod.map f g) :=
  MonoidHom.prodMapStrict f g hf hg

end GroupHom

namespace StrictMonoidHom

/-- Auxiliary definition: a strict monoid homomorphism bundles injectivity with the homomorphism. -/
structure StrictMonoidHom (A B : Type*) [Monoid A] [Monoid B] where
  toFun : A → B
  map_one' : toFun 1 = 1
  map_mul' : ∀ a b, toFun (a * b) = toFun a * toFun b
  injective' : Function.Injective toFun

variable {A B C D : Type*} [Monoid A] [Monoid B] [Monoid C] [Monoid D]

/-- `Prod.map` of two strict monoid homomorphisms is a strict monoid homomorphism.
This demonstrates stability of the strict homomorphism property under product formation. -/
def prodMap (f : StrictMonoidHom A B) (g : StrictMonoidHom C D) :
    StrictMonoidHom (A × C) (B × D) where
  toFun := Prod.map f.toFun g.toFun
  map_one' := by simp [f.map_one', g.map_one']
  map_mul' := fun ⟨a₁, c₁⟩ ⟨a₂, c₂⟩ => by
    simp [f.map_mul', g.map_mul']
  injective' := fun ⟨a₁, c₁⟩ ⟨a₂, c₂⟩ h => by
    simp only [Prod.map_apply] at h
    have ha : f.toFun a₁ = f.toFun a₂ := by simp [Prod.ext_iff] at h; exact h.1
    have hc : g.toFun c₁ = g.toFun c₂ := by simp [Prod.ext_iff] at h; exact h.2
    simp [Prod.ext_iff, f.injective' ha, g.injective' hc]

end StrictMonoidHom

namespace StrictGroupHom

/-- Auxiliary definition: a strict group homomorphism bundles injectivity with the group homomorphism. -/
structure StrictGroupHom (A B : Type*) [Group A] [Group B] where
  toFun : A → B
  map_one' : toFun 1 = 1
  map_mul' : ∀ a b, toFun (a * b) = toFun a * toFun b
  map_inv' : ∀ a, toFun a⁻¹ = (toFun a)⁻¹
  injective' : Function.Injective toFun

variable {A B C D : Type*} [Group A] [Group B] [Group C] [Group D]

/-- `Prod.map` of two strict group homomorphisms is a strict group homomorphism.
Strict group homomorphisms (injective group homomorphisms) are stable under product formation.
If f : A → B and g : C → D are strict group homomorphisms, then
Prod.map f g : A × C → B × D is also a strict group homomorphism. -/
def prodMap (f : StrictGroupHom A B) (g : StrictGroupHom C D) :
    StrictGroupHom (A × C) (B × D) where
  toFun := Prod.map f.toFun g.toFun
  map_one' := by simp [f.map_one', g.map_one']
  map_mul' := fun ⟨a₁, c₁⟩ ⟨a₂, c₂⟩ => by
    simp [f.map_mul', g.map_mul']
  map_inv' := fun ⟨a, c⟩ => by
    simp [f.map_inv', g.map_inv']
  injective' := fun ⟨a₁, c₁⟩ ⟨a₂, c₂⟩ h => by
    simp only [Prod.map_apply] at h
    have ha : f.toFun a₁ = f.toFun a₂ := by simp [Prod.ext_iff] at h; exact h.1
    have hc : g.toFun c₁ = g.toFun c₂ := by simp [Prod.ext_iff] at h; exact h.2
    simp [Prod.ext_iff, f.injective' ha, g.injective' hc]

end StrictGroupHom
