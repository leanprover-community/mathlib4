/-
Copyright (c) 2025 Francisco Silva. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francisco Silva
-/

import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Group.PUnit
import Mathlib.Data.Finite.Perm
import Mathlib.Algebra.Group.End

/-!
# Regular wreath product

This file defines the regular wreath product of groups, and the canonical maps in and out of the
product. The regular wreath product of `D` and `Q` is the product `(Q → D) × Q` with the group
operation `⟨a₁, a₂⟩ * ⟨b₁, b₂⟩ = ⟨a₁ * (fun x ↦ b₁ (a₂⁻¹ * x)), a₂ * b₂⟩`.

## Main definitions

* `RegularWreathProduct D Q` : The regular wreath product of groups `D` and `Q`.
* `rightHom` : The canonical projection `D ≀ᵣ Q →* Q`.
* `inl` : The canonical map `Q →* D ≀ᵣ Q`.
* `toPerm` : The homomorphism from `D ≀ᵣ Q` to `Equiv.Perm (Λ × Q)`, where `Λ` is a `D`-set.
* `IteratedWreathProduct G n` : The iterated wreath product of a group `G` `n` times.
* `Sylow.mulEquivIteratedWreathProduct` : The isomorphism between the Sylow `p`-subgroup of `Perm
  p^n` and the iterated wreath product of the cyclic group of order `p` `n` times.

## Notation

This file introduces the global notation `D ≀ᵣ Q` for `RegularWreathProduct D Q`.

## Tags
group, regular wreath product, sylow p-subgroup
-/

variable (D Q : Type*) [Group D] [Group Q]

/-- The regular wreath product of groups `Q` and `D`. It is the product `(Q → D) × Q` with the group
operation `⟨a₁, a₂⟩ * ⟨b₁, b₂⟩ = ⟨a₁ * (fun x ↦ b₁ (a₂⁻¹ * x)), a₂ * b₂⟩`. -/
@[ext]
structure RegularWreathProduct where
  /-- The function of Q → D -/
  left : Q → D
  /-- The element of Q -/
  right : Q

@[inherit_doc] infix:65 " ≀ᵣ " => RegularWreathProduct

namespace RegularWreathProduct
variable {D Q}

instance : Mul (D ≀ᵣ Q) where
  mul a b := ⟨a.1 * (fun x ↦ b.1 (a.2⁻¹ * x)), a.2 * b.2⟩

lemma mul_def (a b : D ≀ᵣ Q) : a * b = ⟨a.1 * fun x ↦ b.1 (a.2⁻¹ * x), a.2 * b.2⟩ := rfl

@[simp]
theorem mul_left (a b : D ≀ᵣ Q) : (a * b).1 = a.1 * fun x ↦ b.1 (a.2⁻¹ * x) := rfl

@[simp]
theorem mul_right (a b : D ≀ᵣ Q) : (a * b).right = a.right * b.right := rfl

instance : One (RegularWreathProduct D Q) where one := ⟨1, 1⟩

@[simp]
theorem one_left : (1 : D ≀ᵣ Q).left = 1 := rfl

@[simp]
theorem one_right : (1 : D ≀ᵣ Q).right = 1 := rfl

instance : Inv (RegularWreathProduct D Q) where
  inv x := ⟨fun k ↦ x.1⁻¹ (x.2 * k), x.2⁻¹⟩

@[simp]
theorem inv_left (a : D ≀ᵣ Q) : a⁻¹.left = fun x ↦ a.left⁻¹ (a.right * x) := rfl

@[simp]
theorem inv_right (a : D ≀ᵣ Q) : a⁻¹.right = a.right⁻¹ := rfl

instance : Group (RegularWreathProduct D Q) where
  mul_assoc a b c := by ext <;> simp [mul_assoc]
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by ext <;> simp

instance : Inhabited (RegularWreathProduct D Q) := ⟨1⟩

/-- The canonical projection map `D ≀ᵣ Q →* Q`, as a group hom. -/
def rightHom : D ≀ᵣ Q →* Q where
  toFun := RegularWreathProduct.right
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The canonical map `Q →* D ≀ᵣ Q` sending `q` to `⟨1, q⟩` -/
def inl : Q →* D ≀ᵣ Q where
  toFun q := ⟨1, q⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

@[simp]
theorem left_inl (q : Q) : (inl q : D ≀ᵣ Q).left = 1 := rfl

@[simp]
theorem right_inl (q : Q) : (inl q : D ≀ᵣ Q).right = q := rfl

@[simp]
theorem rightHom_eq_right : (rightHom : D ≀ᵣ Q → Q) = right := rfl

@[simp]
theorem rightHom_comp_inl_eq_id : (rightHom : D ≀ᵣ Q →* Q).comp inl = MonoidHom.id _ := by ext; simp

@[simp]
theorem fun_id (q : Q) : rightHom (inl q : D ≀ᵣ Q) = q := by simp

/-- The equivalence map for the representation as a product. -/
def equivProd D Q : D ≀ᵣ Q ≃ (Q → D) × Q where
  toFun := fun ⟨d, q⟩ => ⟨d, q⟩
  invFun := fun ⟨d, q⟩ => ⟨d, q⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance [Finite D] [Finite Q] : Finite (D ≀ᵣ Q) :=
  Finite.of_equiv _ (equivProd D Q).symm

omit [Group D] [Group Q] in
theorem card [Finite Q] : Nat.card (D ≀ᵣ Q) = Nat.card D ^ Nat.card Q * Nat.card Q := by
  rw [Nat.card_congr (equivProd D Q), Nat.card_prod (Q → D) Q, Nat.card_fun]

/-- Define an isomorphism from `D₁ ≀ᵣ Q₁` to `D₂ ≀ᵣ Q₂`
given isomorphisms `D₁ ≀ᵣ Q₁` and `Q₁ ≃* Q₂`. -/
def congr {D₁ Q₁ D₂ Q₂ : Type*} [Group D₁] [Group Q₁] [Group D₂] [Group Q₂]
    (f : D₁ ≃* D₂) (g : Q₁ ≃* Q₂) :
    D₁ ≀ᵣ Q₁ ≃* D₂ ≀ᵣ Q₂ where
  toFun x := ⟨f ∘ (x.left ∘ g.symm), g x.right⟩
  invFun x := ⟨(f.symm ∘ x.left) ∘ g, g.symm x.right⟩
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_mul' x y := by ext <;> simp

section perm

variable (D Q) (Λ : Type*) [MulAction D Λ]

instance : SMul (D ≀ᵣ Q) (Λ × Q) where
  smul w p := ⟨(w.left (w.right * p.2)) • p.1, w.right * p.2⟩

@[simp]
lemma smul_def {w : D ≀ᵣ Q} {p : Λ × Q} : w • p = ⟨(w.1 (w.2 * p.2)) • p.1, w.2 * p.2⟩ := rfl

instance : MulAction (D ≀ᵣ Q) (Λ × Q) where
  one_smul := by simp
  mul_smul := by simp [smul_smul, mul_assoc]

variable [FaithfulSMul D Λ]
instance [Nonempty Q] [Nonempty Λ] : FaithfulSMul (D ≀ᵣ Q) (Λ × Q) where
  eq_of_smul_eq_smul := by
    simp only [smul_def, Prod.mk.injEq, mul_left_inj, Prod.forall]
    intro m₁ m₂ h
    let ⟨a⟩ := ‹Nonempty Λ›
    let ⟨b⟩ := ‹Nonempty Q›
    ext q
    · have hh := fun a => (h a (m₁.right⁻¹ * q)).1
      rw [← (h a b).2] at hh
      group at hh
      exact FaithfulSMul.eq_of_smul_eq_smul hh
    · exact (h a b).2

/-- The map sending the wreath product `D ≀ᵣ Q` to its representation as a permutation of `Λ × Q`
given `D`-set `Λ`. -/
def toPerm : D ≀ᵣ Q →* Equiv.Perm (Λ × Q) :=
  MulAction.toPermHom (D ≀ᵣ Q) (Λ × Q)

theorem toPermInj [Nonempty Λ] : Function.Injective (toPerm D Q Λ) := MulAction.toPerm_injective

end perm

end RegularWreathProduct

section iterated

universe u

/-- The wreath product of group `G` iterated `n` times. -/
def IteratedWreathProduct (G : Type u) : (n : ℕ) → Type u
| 0 => PUnit
| n + 1 => (IteratedWreathProduct G n) ≀ᵣ G

variable (G : Type u) (n : ℕ)

@[simp]
lemma IteratedWreathProduct_zero : IteratedWreathProduct G 0 = PUnit := rfl

@[simp]
lemma IteratedWreathProduct_succ :
    IteratedWreathProduct G (n + 1) = (IteratedWreathProduct G n) ≀ᵣ G := rfl

instance [Finite G] : Finite (IteratedWreathProduct G n) := by
  induction n with
  | zero => rw [IteratedWreathProduct_zero]; infer_instance
  | succ n h => rw [IteratedWreathProduct_succ]; infer_instance

theorem IteratedWreathProduct.card [Finite G] : Nat.card (IteratedWreathProduct G n) =
    Nat.card G ^ (∑ i ∈ Finset.range n, Nat.card G ^ i) := by
  induction n with
  | zero => simp
  | succ n h => rw [IteratedWreathProduct_succ, RegularWreathProduct.card,
      h, geom_sum_succ, pow_succ, pow_mul']

variable [Group G]

instance : Group (IteratedWreathProduct G n) := by
 induction n with
 | zero => rw [IteratedWreathProduct_zero]; infer_instance
 | succ n ih => rw [IteratedWreathProduct_succ]; infer_instance

/-- The homomorphism from `IteratedWreathProduct G n` to `Perm (Fin n → G)`. -/
def iteratedWreathToPermHom (G : Type*) [Group G] :
    (n : ℕ) → (IteratedWreathProduct G n →* Equiv.Perm (Fin n → G))
  | 0 => 1
  | n + 1 => by
      let _ := MulAction.compHom (Fin n → G) (iteratedWreathToPermHom G n)
      exact (Fin.succFunEquiv G n).symm.permCongrHom.toMonoidHom.comp
        (RegularWreathProduct.toPerm (IteratedWreathProduct G n) G (Fin n → G))

lemma iteratedWreathToPermHomInj (G : Type*) [Group G] :
    (n : ℕ) → Function.Injective (iteratedWreathToPermHom G n)
  | 0 => by
      simp only [IteratedWreathProduct_zero]
      apply Function.injective_of_subsingleton
  | n + 1 => by
      let _ := MulAction.compHom (Fin n → G) (iteratedWreathToPermHom G n)
      have : FaithfulSMul (IteratedWreathProduct G n) (Fin n → G) :=
        ⟨fun h ↦ iteratedWreathToPermHomInj G n (Equiv.ext h)⟩
      exact ((Fin.succFunEquiv G n).symm.permCongrHom.toEquiv.comp_injective _).mpr
        (RegularWreathProduct.toPermInj (IteratedWreathProduct G n) G (Fin n → G))

/-- The encoding of the Sylow `p`-subgroups of `Perm α` as an iterated wreath product. -/
noncomputable def Sylow.mulEquivIteratedWreathProduct (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)
    (α : Type*) [Finite α] (hα : Nat.card α = p ^ n)
    (G : Type*) [Group G] [Finite G] (hG : Nat.card G = p)
    (P : Sylow p (Equiv.Perm α)) :
    P ≃* IteratedWreathProduct G n := by
  let e1 : α ≃ (Fin n → G) := (Finite.equivFinOfCardEq hα).trans
    (Finite.equivFinOfCardEq (by rw [Nat.card_fun, Nat.card_fin, hG])).symm
  let f := e1.symm.permCongrHom.toMonoidHom.comp (iteratedWreathToPermHom G n)
  have hf : Function.Injective f :=
    (e1.symm.permCongrHom.comp_injective _).mpr (iteratedWreathToPermHomInj G n)
  let g := (MonoidHom.ofInjective hf).symm
  let P' : Sylow p (Equiv.Perm α) := Sylow.ofCard (MonoidHom.range f) (by
    rw [Nat.card_congr g.toEquiv, IteratedWreathProduct.card, hG, Nat.card_perm, hα,
        ← Nat.multiplicity_eq_factorization hp.out (p ^ n).factorial_ne_zero,
        Nat.Prime.multiplicity_factorial_pow hp.out])
  exact (P.equiv P').trans g

end iterated
