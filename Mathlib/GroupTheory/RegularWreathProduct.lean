/-
Copyright (c) 2025 Francisco Silva. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francisco Silva
-/

import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Group.PUnit

/-!
# Regular wreath product

This file defines the regular wreath product of groups, and the canonical maps in and out of the
product. The regular wreath product of `D` and `Q` is the product of sets with the group
`⟨d₁, q₁⟩ * ⟨d₂, q₂⟩ = ⟨d.1 * (fun x => q.1 (d.2⁻¹ * x)), d.2 * q.2⟩`

## Key definitions

There an hom into the regular wreath product `inl : D →* D ≀ᵣ Q`.

## Notation

This file introduces the global notation `D ≀ᵣ Q` for `RegularWreathProduct D Q`

## Tags
group, regular wreath product, sylow p-subgroup
-/

variable (D Q : Type*) [Group D] [Group Q]

/-- The regular wreath product of groups `Q` and `D`.
    It the product of sets with the group operation
  `⟨d₁, q₁⟩ * ⟨d₂, q₂⟩ = ⟨d.1 * (fun x => q.1 (d.2⁻¹ * x)), d.2 * q.2⟩` -/
@[ext]
structure RegularWreathProduct where
  /-- The function of Q → D -/
  left : Q → D
  /-- The element of Q -/
  right : Q

@[inherit_doc] infix:65  " ≀ᵣ " => RegularWreathProduct

namespace RegularWreathProduct
variable {D Q}

instance : Mul (RegularWreathProduct D Q) where
  mul d q := ⟨d.1 * (fun x => q.1 (d.2⁻¹ * x)), d.2 * q.2⟩

lemma mul_def (d q : RegularWreathProduct D Q) :
    d * q = ⟨d.1 * (fun x => q.1 (d.2⁻¹ * x)), d.2 * q.2⟩ := rfl

@[simp]
theorem mul_left (a b : D ≀ᵣ Q) :
    (a * b).left = a.left * (((fun x => b.left (a.right⁻¹ * x)))) := rfl

@[simp]
theorem mul_right (a b : D ≀ᵣ Q) : (a * b).right = a.right * b.right := rfl

instance : One (RegularWreathProduct D Q) where one := ⟨1, 1⟩

@[simp]
theorem one_left : (1 : D ≀ᵣ Q).left = 1 := rfl

@[simp]
theorem one_right : (1 : D ≀ᵣ Q).right = 1 := rfl

instance : Inv (RegularWreathProduct D Q) where
  inv x := ⟨((fun k => x.1⁻¹ (x.2 * k))), x.2⁻¹⟩

@[simp]
theorem inv_left (a : D ≀ᵣ Q) :
    a⁻¹.left = ((fun x => a.left⁻¹ (a.right * x))) := rfl

@[simp]
theorem inv_right (a : D ≀ᵣ Q) : a⁻¹.right = a.right⁻¹ := rfl

instance : Group (RegularWreathProduct D Q) where
  mul_assoc a b c := RegularWreathProduct.ext (by simp [mul_assoc]; rfl) (by simp [mul_assoc])
  one_mul a := RegularWreathProduct.ext (by simp) (one_mul a.2)
  mul_one a := RegularWreathProduct.ext (by simp; rfl) (mul_one _)
  inv_mul_cancel a :=
    RegularWreathProduct.ext (by simp; exact mul_eq_one_iff_eq_inv.mpr rfl) (by simp)

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

omit [Group D] [Group Q] in
lemma equivProdInj : Function.Injective (equivProd D Q).toFun := by
  intro a b; simp

instance [Finite D] [Finite Q] : Finite (D ≀ᵣ Q) := by
  apply (Equiv.finite_iff (equivProd D Q)).mpr
  apply Finite.instProd

omit [Group D] [Group Q] in
theorem card [Finite Q] :
   Nat.card (D ≀ᵣ Q) = (Nat.card D^Nat.card Q) * Nat.card Q := by
  rw [Nat.card_congr (equivProd D Q)]
  rw [Nat.card_prod (Q → D) Q]
  rw [Nat.card_fun]

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

variable (D : Type*) [Group D]
variable (Q : Type*) [Group Q] [Nonempty Q]
variable (Λ : Type*) [Nonempty Λ] [MulAction D Λ]

instance instSMulRWP : SMul (D ≀ᵣ Q) (Λ × Q) where
  smul w := fun p => ⟨(w.left (w.right * p.2)) • p.1, w.right * p.2⟩

omit [Nonempty Λ] [Nonempty Q] in
@[simp]
lemma rsmul {w : D ≀ᵣ Q} {p : Λ × Q} :
    w • p = ⟨(w.left (w.right * p.2)) • p.1, w.right * p.2⟩ := rfl

instance instMulActionRWP : MulAction (D ≀ᵣ Q) (Λ × Q) where
  one_smul := by simp
  mul_smul := by simp; intro x y a b; constructor
                 · rw [smul_smul]; group
                 · exact mul_assoc x.right y.right b


variable [FaithfulSMul D Λ]
instance instFaithfulSMulRWP : FaithfulSMul (D ≀ᵣ Q) (Λ × Q) where
  eq_of_smul_eq_smul := by
    simp
    intro m₁ m₂ h
    let ⟨a⟩ := ‹Nonempty Λ›
    let ⟨b⟩ := ‹Nonempty Q›
    ext q
    · have hh := fun a => (h a (m₁.right⁻¹ * q)).1
      rw [← (h a b).2] at hh
      group at hh
      apply FaithfulSMul.eq_of_smul_eq_smul at hh
      exact hh
    · exact (h a b).2

/-- The map sending the wreath product `D ≀ᵣ Q` to its representation as a permutation of `Λ × Q`
given `D`-set `Λ`. -/
def toPerm : D ≀ᵣ Q →* Equiv.Perm (Λ × Q) :=
  MulAction.toPermHom (D ≀ᵣ Q) (Λ × Q)

theorem toPermInj :
  Function.Injective (toPerm D Q Λ) := MulAction.toPerm_injective

end perm

end RegularWreathProduct


section iterated

/-- The wreath product of group `G` iterated `n` times. -/
def IteratedWreathProduct (G : Type) : (n : ℕ) → Type
| Nat.zero => PUnit
| Nat.succ n => (IteratedWreathProduct G n) ≀ᵣ G

@[simp]
lemma IteratedWreathProduct_zero (G : Type) :
    IteratedWreathProduct G 0 = PUnit := rfl

@[simp]
lemma IteratedWreathProduct_succ (G : Type)(n : ℕ) :
    IteratedWreathProduct G (n+1) = (IteratedWreathProduct G n) ≀ᵣ G := rfl

variable (G : Type) [inst : Group G]
variable (n : ℕ)

instance : Group (IteratedWreathProduct G n) := by
 induction n with
 | zero => rw [IteratedWreathProduct_zero]; exact CommGroup.toGroup
 | succ n ih => rw [IteratedWreathProduct_succ]; exact RegularWreathProduct.instGroup

instance [Finite G] : Finite (IteratedWreathProduct G n) := by
  induction n with
  | zero => rw [IteratedWreathProduct_zero]; exact Finite.of_subsingleton
  | succ n h => rw [IteratedWreathProduct_succ]; exact RegularWreathProduct.instFinite

lemma elem_P0 (p : ℕ) (P : Sylow p (Equiv.Perm (Fin (1)))) (x : P):
    x = 1 := Subsingleton.eq_one x

theorem iter_wreath_card {p n : ℕ}
    (G : Type) [Finite G] (h : Nat.card G = p) :
    Nat.card (IteratedWreathProduct G n) = p ^ (∑ i ∈ Finset.range n, p ^ i) := by
  induction n with
  | zero => simp
  | succ n h_n =>
    rw [geom_sum_succ, IteratedWreathProduct_succ]
    rw [RegularWreathProduct.card, h_n, h]; group

lemma mu_eq {p n : ℕ} [hp : Fact (Nat.Prime p)] :
    (p ^ n).factorial.factorization p = ∑ i ∈ Finset.range n, p ^ i := by
  rw [← Nat.multiplicity_eq_factorization hp.out (p ^ n).factorial_ne_zero, ← ENat.coe_inj,
    ← (Nat.finiteMultiplicity_iff.2
      ⟨hp.out.ne_one, (p ^ n).factorial_pos⟩).emultiplicity_eq_multiplicity]
  induction n with
  | zero => simp [hp.out.emultiplicity_one]
  | succ n h =>
    rw [pow_succ', hp.out.emultiplicity_factorial_mul, h, Finset.sum_range_succ, ENat.coe_add]

/-- An auxilliary function -/
def aux {A B : Type} (h : A ≃ B) : Equiv.Perm A ≃* Equiv.Perm B where
  toFun x := h.symm.trans (x.trans h)
  invFun y := h.trans (y.trans h.symm)
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp
  map_mul' _ _ := by ext; simp

/-- An auxilliary function -/
noncomputable def f {p n : ℕ} (D : Sylow p (Equiv.Perm (Fin (p^n))))
    (G : Type) [Finite G] [Group G] (h : Nat.card G = p) :
    D ≀ᵣ G →* Equiv.Perm (Fin (p^(n+1))) :=
  (aux ((Equiv.prodCongrRight fun _ =>
  (Finite.equivFinOfCardEq h)).trans finProdFinEquiv)).toMonoidHom.comp
  (RegularWreathProduct.toPerm D G (Fin (p^n)))

lemma f_injective {p n : ℕ} [Fact (Nat.Prime p)] (D : Sylow p (Equiv.Perm (Fin (p^n))))
    (G : Type) [Finite G] [Group G] (h : Nat.card G = p) :
    Function.Injective (f D G h) := by
  have : Function.Injective (RegularWreathProduct.toPerm D G (Fin (p^n))) :=
    RegularWreathProduct.toPermInj D G (Fin (p^n))
  exact (fun a b => Function.Injective.comp a b)
    (aux (((Equiv.prodCongrRight fun _ =>
    (Finite.equivFinOfCardEq h)).trans finProdFinEquiv))).injective this

/-- The Sylow p-subgroups of S_{p^n} are isomorphic to the iterated wreathproduct -/
noncomputable def sylowIsIteratedWreathProduct (p n : ℕ) [Fact (Nat.Prime p)]
    (Z_p : Type) [Group Z_p] [Finite Z_p] (h : Nat.card Z_p = p)
    (P : Sylow p (Equiv.Perm (Fin (p^n)))) :
    P ≃* (IteratedWreathProduct Z_p n) := by
  induction n with
  | zero => exact {
      toFun := 1
      invFun := 1
      left_inv x := by rw [Pi.one_apply, elem_P0 p P x]
      right_inv x:= by rw [Pi.one_apply]; rfl
      map_mul' := by simp}
  | succ n h_n =>
      let P' : Sylow p (Equiv.Perm (Fin (p ^ n))) := Inhabited.default
      have g : (IteratedWreathProduct Z_p (n+1)) ≃* MonoidHom.range (f P' Z_p h) :=
        (RegularWreathProduct.congr (h_n P').symm (MulEquiv.refl Z_p)).trans
        (MonoidHom.ofInjective (f_injective P' Z_p h))
      have sylow_card : Nat.card (MonoidHom.range (f P' Z_p h)) =
      p ^ (Nat.card (Equiv.Perm (Fin (p^(n+1))))).factorization p := by
        rw [Nat.card_congr (g.symm).toEquiv, iter_wreath_card Z_p h, Nat.card_eq_fintype_card]
        rw [Fintype.card_perm,Fintype.card_fin,mu_eq]
      exact (P.equiv (Sylow.ofCard (MonoidHom.range (f P' Z_p h)) sylow_card)).trans (id g.symm)

end iterated
