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

variable (D Q: Type*) [Group D] [Group Q]

/-- The regular wreath product of groups `Q` and `D`.
    It the product of sets with the group operation
  `⟨n₁, g₁⟩ * ⟨n₂, g₂⟩ = ⟨n₁ * φ g₁ n₂, g₁ * g₂⟩` -/
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
theorem fun_id (q:Q) : rightHom (inl q : D ≀ᵣ Q) = q := by simp

/-- The equivalence map for the representation as a product. -/
def equivProd D Q: D ≀ᵣ Q ≃ (Q → D) × Q where
  toFun := fun ⟨d, q⟩ => ⟨d, q⟩
  invFun := fun ⟨d, q⟩ => ⟨d, q⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

omit [Group D] [Group Q] in
lemma equivProdInj: Function.Injective (equivProd D Q).toFun := by
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
(f : D₁ ≃* D₂) (g : Q₁ ≃* Q₂):
  D₁ ≀ᵣ Q₁ ≃* D₂ ≀ᵣ Q₂ where
    toFun x := ⟨f ∘ (x.left ∘ g.symm), g x.right⟩
    invFun x := ⟨(f.symm ∘ x.left) ∘ g, g.symm x.right⟩
    left_inv x := by ext <;> simp
    right_inv x := by ext <;> simp
    map_mul' x y := by ext <;> simp

section perm

variable (D: Type*) [Group D]
variable (Q: Type*) [Group Q] [Nonempty Q]
variable (Λ : Type*) [Nonempty Λ] [MulAction D Λ]

instance instSMulRWP : SMul (D ≀ᵣ Q) (Λ × Q) where
  smul w := fun p => ⟨(w.left (w.right * p.2)) • p.1, w.right * p.2⟩

omit [Nonempty Λ] [Nonempty Q] in
@[simp]
lemma rsmul {w: D ≀ᵣ Q} {p : Λ × Q}:
 w • p = ⟨(w.left (w.right * p.2)) • p.1, w.right * p.2⟩ := rfl

instance instMulActionRWP: MulAction (D ≀ᵣ Q) (Λ × Q) where
  one_smul := by simp;
  mul_smul := by simp; intro x y a b; constructor
                 · rw [smul_smul]; group
                 · exact mul_assoc x.right y.right b


variable [FaithfulSMul D Λ]
instance instFaithfulSMulRWP: FaithfulSMul (D ≀ᵣ Q) (Λ × Q) where
  eq_of_smul_eq_smul := by
    simp; intro m₁ m₂ h;
    let ⟨a⟩ := ‹Nonempty Λ›
    let ⟨b⟩ := ‹Nonempty Q›
    ext q
    · have hh := fun a => (h a (m₁.right⁻¹ * q)).1;
      rw [← (h a b).2] at hh
      group at hh
      apply FaithfulSMul.eq_of_smul_eq_smul at hh
      exact hh
    · exact (h a b).2

/-- The map sending the wreath product `D ≀ᵣ Q` to its representation as a permutation of `Λ × Q`
given `D`-set `Λ`. -/
def toPerm : D ≀ᵣ Q →* Equiv.Perm (Λ × Q) :=
    MulAction.toPermHom (D ≀ᵣ Q) (Λ × Q)

theorem toPermInj:
  Function.Injective (toPerm D Q Λ) := MulAction.toPerm_injective

end perm

end RegularWreathProduct


section iterated

/- The iterated wreath product of group `G` `n` times. -/
def IteratedWreathProduct (G: Type) : (n:ℕ) → Type
| Nat.zero => PUnit
| Nat.succ n => (IteratedWreathProduct G n) ≀ᵣ G

@[simp]
lemma IteratedWreathProduct_zero (G : Type) [Group G] :
  IteratedWreathProduct G 0 = PUnit := rfl

@[simp]
lemma IteratedWreathProduct_succ (G : Type) [Group G] (n : ℕ) :
  IteratedWreathProduct G (n+1) = (IteratedWreathProduct G n) ≀ᵣ G := rfl

variable (G: Type) [inst : Group G]
variable (n: ℕ)

instance: Group (IteratedWreathProduct G n) := by
 induction n with
 | zero => rw [IteratedWreathProduct_zero]; exact CommGroup.toGroup
 | succ n ih => rw [IteratedWreathProduct_succ]; exact RegularWreathProduct.instGroup

instance [Finite G] : Finite (IteratedWreathProduct G n) := by
  induction n with
  | zero => rw [IteratedWreathProduct_zero]; exact Finite.of_subsingleton
  | succ n h => rw [IteratedWreathProduct_succ]; exact RegularWreathProduct.instFinite

lemma elem_P0 (p : ℕ) (P : Sylow p (Equiv.Perm (Fin (1)))) (x:P):
  x = 1 := Subsingleton.eq_one x

theorem iter_wreath_card {p n : ℕ}
  (G : Type) [Group G] [Finite G] (h : Nat.card G = p) :
  Nat.card (IteratedWreathProduct G n) = p ^ (∑ i ∈ Finset.range n, p ^ i) := by
  induction n with
  | zero => simp
  | succ n h_n =>
    rw [geom_sum_succ, IteratedWreathProduct_succ]
    rw [RegularWreathProduct.card, h_n, h]; group

lemma mu_eq {p n :ℕ} [Fact (Nat.Prime p)]:
(p ^ n).factorial.factorization p = ∑ i ∈ Finset.range n, p ^ i := by
  induction n with
  | zero => simp
  | succ n h =>
    rw [Finset.sum_range_succ, ← h]
    let S : Finset ℕ := { k ∈ Finset.range (p^(n+1)) | p ∣ (k+1)}
    have h_disjoint : Disjoint S (Finset.range (p ^ (n + 1)) \ S) := Finset.disjoint_sdiff
    have h_decomp : (p^(n+1)).factorial =
      (∏ k ∈ S, (k+1)) * (∏ k ∈ (Finset.range (p^(n+1)) \ S), (k+1)) := by
      rw [← Finset.prod_union h_disjoint]
      rw [Finset.union_sdiff_of_subset (Finset.filter_subset (fun k ↦ p ∣ k + 1)
        (Finset.range (p ^ (n + 1))))]
      rw [Finset.prod_range_add_one_eq_factorial]
    have h_compl : (∏ k ∈ (Finset.range (p^(n+1)) \ S), (k+1)).factorization p = 0 := by
        rw [Nat.factorization_prod (fun x => (fun _ => Ne.symm (Nat.zero_ne_add_one x)))]
        rw [Finsupp.finset_sum_apply (Finset.range (p ^ (n + 1)) \ S)
          (fun i ↦ (i + 1).factorization) p ]
        apply Finset.sum_eq_zero
        intro x hx
        apply Nat.factorization_eq_zero_of_not_dvd
        apply Finset.mem_sdiff.mp at hx
        have h1 := hx.left; have h2 := hx.right
        have hhh : ¬ (x ∈ { k ∈ Finset.range (p^(n+1)) | p ∣ (k+1)}) ↔
          ¬ (x ∈ Finset.range (p^(n+1)) ∧ (p ∣ (x+1))) :=
          not_congr Finset.mem_filter
        apply hhh.mp at h2
        simp at h2
        simp at h1
        exact h2 h1
    have h1: ∏ k ∈ S, (k + 1) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr; intro x hx;
      exact Ne.symm (Nat.zero_ne_add_one x)
    have h2 : ∏ k ∈ Finset.range (p ^ (n + 1)) \ S, (k + 1) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr; intro x hx; exact Ne.symm (Nat.zero_ne_add_one x)
    have aux : ((∏ k ∈ S, (k + 1)).factorization +
      (∏ k ∈ Finset.range (p ^ (n + 1)) \ S, (k + 1)).factorization) p =
      (∏ k ∈ S, (k + 1)).factorization p +
      (∏ k ∈ Finset.range (p ^ (n + 1)) \ S, (k + 1)).factorization p := rfl
    have res : ((p^(n+1)).factorial).factorization p = (∏ k ∈ S, (k + 1)).factorization p := by
      rw [h_decomp, Nat.factorization_mul h1 h2, aux, h_compl, Nat.add_zero]
    let f : ℕ → ℕ := fun m => p * (m + 1) - 1
    have hf_mem : ∀ m ∈ Finset.range (p^n), f m ∈ S := by
      intro m hm
      apply List.mem_range.mp at hm
      have f_bound : f m < p ^ (n + 1) := by
        replace hm := Nat.sub_le_sub_right (Nat.mul_le_mul_left p (Nat.succ_le_of_lt hm)) 1
        rw [Nat.pow_succ']
        have : p * p ^ n - 1 < p * p ^ n := Nat.sub_one_lt (Ne.symm (NeZero.ne' (p * p ^ n)))
        exact Nat.lt_of_le_of_lt hm this
      have dvd : p ∣ (f m + 1) := by
        rw [Nat.sub_add_cancel NeZero.one_le]
        exact Nat.dvd_mul_right p (m + 1)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr f_bound, dvd⟩
    have hf_inj' : ∀ m₁ m₂ : ℕ , f m₁ = f m₂ → m₁ = m₂ := by
      intro m₁ m₂ h_eq
      have aux1 : p * (m₁ + 1) = f m₁ + 1 := Eq.symm (Nat.sub_add_cancel NeZero.one_le)
      have aux2 : p * (m₂ + 1) = f m₂ + 1 := Eq.symm (Nat.sub_add_cancel NeZero.one_le)
      have : p * (m₁ + 1) = p * (m₂ + 1) := by
        rw [aux1, aux2];
        exact congrFun (congrArg HAdd.hAdd h_eq) 1
      exact Nat.succ_inj.mp (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_neZero p) this)
    have hf_inj : Set.InjOn f ↑(Finset.range (p ^ n)) := fun ⦃x₁⦄ a ⦃x₂⦄ a ↦ hf_inj' x₁ x₂
    have hf_surj : ∀ k ∈ S, ∃ m ∈ Finset.range (p^n), f m = k := by
      intro k hk
      apply Finset.mem_filter.mp at hk
      have hk1 := List.mem_range.mp hk.1
      obtain ⟨x,hx⟩ := exists_eq_mul_right_of_dvd hk.2
      have : 0 < p * x := hx ▸ (Nat.zero_lt_succ k)
      have aux : 0 < x := by exact Nat.lt_of_mul_lt_mul_left this
      have x_bound : x - 1 < p^n := by
        have hk1 := Nat.add_lt_add_right (List.mem_range.mp hk.1) 1
        rw [hx, Nat.pow_succ'] at hk1
        apply Nat.succ_le_of_lt at hk1
        simp at hk1
        apply le_of_nsmul_le_nsmul_right (NeZero.ne p) at hk1
        apply Nat.sub_one_lt_of_le aux
        exact hk1
      have x_fun : f (x-1) = k := by
        apply Nat.eq_sub_of_add_eq at hx;
        have : f (x - 1) = p * (x - 1 + 1) - 1 := rfl
        rw [hx, this, Nat.sub_add_cancel aux]
      use (x - 1); exact ⟨List.mem_range.mpr x_bound, x_fun⟩
    have prod_reindex : ∏ m ∈ Finset.range (p^n), (p * (m + 1)) = ∏ k ∈ S, (k + 1) := by
      apply (Finset.prod_nbij f hf_mem hf_inj hf_surj)
      intro a ha;
      apply (Nat.sub_eq_iff_eq_add NeZero.one_le ).mp; rfl
    rw [← prod_reindex] at res
    have h_prod : (∏ m ∈ Finset.range (p^n), (p * (m + 1))).factorization p =
      ∑ m ∈ Finset.range (p^n), (p * (m + 1)).factorization p := by
      rw [Nat.factorization_prod (fun x => (fun _ => Nat.mul_ne_zero ((NeZero.ne' p).symm)
        (Nat.zero_ne_add_one x).symm))]
      simp
    rw [h_prod] at res
    have h_each : ∀ m ∈ Finset.range (p^n), (p*(m+1)).factorization p =
      1 + (m+1).factorization p := by
      intro m hm
      have aux : (p.factorization + (m + 1).factorization) p =
        p.factorization p + (m + 1).factorization p := rfl
      rw [Nat.factorization_mul ((NeZero.ne' p).symm) (Ne.symm (Nat.zero_ne_add_one m))]
      rw [aux, Nat.Prime.factorization_self (Fact.out)]
    rw [Finset.sum_congr rfl h_each] at res
    rw [Finset.sum_add_distrib,Finset.sum_const, Finset.card_range] at res
    have h_back : ∑ x ∈ Finset.range (p ^ n), (x + 1).factorization p =
      (p ^ n).factorial.factorization p := by
      have aux : ∑ x ∈ Finset.range (p ^ n), (x + 1).factorization p =
        (∑ x ∈ Finset.range (p ^ n), (x + 1).factorization) p := by
        simp
      rw [← Finset.prod_range_add_one_eq_factorial]
      rw [Nat.factorization_prod (fun x => (fun hx => (Nat.zero_ne_add_one x).symm)), aux]
    rw [h_back] at res; simp at res; rw [Nat.add_comm (p ^ n) _] at res
    exact res

/- An auxilliary function -/
def aux {A B : Type} (h : A ≃ B) : Equiv.Perm A →* Equiv.Perm B :=
  MonoidHom.mk'
    (fun k => h.symm.trans (k.trans h))
    (by intro a b; ext x; simp)

lemma aux_injective {A B : Type} (h : A ≃ B) : Function.Injective (aux h) := by
  intro x y h_eq; ext a
  replace h_eq : h.symm.trans (x.trans h) = h.symm.trans (y.trans h) := h_eq
  have eq_fun := Equiv.ext_iff.mp h_eq
  specialize eq_fun (h a)
  simp at eq_fun
  exact eq_fun

noncomputable
/- An auxilliary function -/
def f {p n : ℕ} [Fact (Nat.Prime p)] (D : Sylow p (Equiv.Perm (Fin (p^n))))
  (G : Type) [Finite G] [Group G] (h: Nat.card G = p):
    D ≀ᵣ G →* Equiv.Perm (Fin (p^(n+1))) :=
     (aux ((Equiv.prodCongrRight fun _ => (Finite.equivFinOfCardEq h)).trans finProdFinEquiv)).comp
      (RegularWreathProduct.toPerm D G (Fin (p^n)))


lemma f_injective {p n : ℕ} [Fact (Nat.Prime p)] (D : Sylow p (Equiv.Perm (Fin (p^n))))
  (G : Type) [Finite G] [Group G] [IsCyclic G] (h: Nat.card G = p):
    Function.Injective (f D G h) := by
      have : Function.Injective (RegularWreathProduct.toPerm D G (Fin (p^n))) :=
        RegularWreathProduct.toPermInj D G (Fin (p^n))
      exact (fun a b => Function.Injective.comp a b)
        (aux_injective (((Equiv.prodCongrRight fun _ =>
        (Finite.equivFinOfCardEq h)).trans finProdFinEquiv))) this

noncomputable
/-The Sylow p-subgroups of S_{p^n} are isomorphic to the iterated wreathproduct -/
def sylowIsIteratedWreathProduct (p n : ℕ) [Fact (Nat.Prime p)]
  (Z_p : Type) [Group Z_p] [IsCyclic Z_p] [Finite Z_p] (h: Nat.card Z_p = p)
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
        have g: (IteratedWreathProduct Z_p (n+1)) ≃* MonoidHom.range (f P' Z_p h) :=
          (RegularWreathProduct.congr (h_n P').symm (MulEquiv.refl Z_p)).trans
          (MonoidHom.ofInjective (f_injective P' Z_p h))
        have sylow_card: Nat.card (MonoidHom.range (f P' Z_p h)) =
        p ^ (Nat.card (Equiv.Perm (Fin (p^(n+1))))).factorization p := by
          rw [Nat.card_congr (g.symm).toEquiv, iter_wreath_card Z_p h, Nat.card_eq_fintype_card]
          rw [Fintype.card_perm,Fintype.card_fin,mu_eq]
        exact (P.equiv (Sylow.ofCard (MonoidHom.range (f P' Z_p h)) sylow_card)).trans (id g.symm)

end iterated
