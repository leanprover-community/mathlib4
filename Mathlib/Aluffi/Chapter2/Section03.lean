import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.Perm.Cycle.Concrete

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

-- 3.1. Let φ : G → H be a morpism in a category C with products. Explain why
-- there is a unique morphism (φ × φ) : G x G → H x H.
-- (This morphism is defined explicitly for C = Set in §3.1.) [§3.1, 3.2]
lemma exercise31 {C : Type _} [Category C] [HasBinaryProducts C] (G H : C) (φ : G ⟶ H) :
    Nonempty (Unique {f : prod G G ⟶ prod H H //
      f ≫ prod.fst = prod.fst ≫ φ ∧ f ≫ prod.snd = prod.snd ≫ φ}) := by
  refine' ⟨⟨⟨prod.map φ φ, prod.map_fst _ _, prod.map_snd _ _⟩, _⟩⟩
  rintro ⟨g, gl, gr⟩
  ext
  · simpa using gl
  · simpa using gr

-- 3.2. Let φ : G → H, ψ : H → K be morphisms in a category with products, and
-- consider morphisms between the products G x G, H x H, K x K as in Exercise 3.1.
-- Prove that (φψ) x (φψ) = (φ x φ)(ψ x ψ)
-- (This is part of the commutativity of the diagram displayed in §3.2.)
lemma exercise32 {C : Type _} [Category C] [HasBinaryProducts C] (G H K : C)
    (φ : G ⟶ H) (ψ : H ⟶ K) : prod.map (φ ≫ ψ) (φ ≫ ψ) = prod.map φ φ ≫ prod.map ψ ψ := by
  ext <;>
  simp

-- 3.3. Show that if G, H are abelian groups, then G x H satisfies the universal
-- property for coproducts in Ab (cf. §1.5.5). 1§3.5, 3.6, §III.6.1]
lemma exercise33 {G H : Type _} [AddCommGroup G] [AddCommGroup H] :
    HasBinaryCoproduct (C := AddCommGroupCat) (.of G) (.of H) := by
  constructor
  refine' ⟨⟨.of (G × H), _⟩, _⟩
  · refine' ⟨_, _⟩
    · rintro (_|_)
      · exact AddMonoidHom.inl _ _
      · exact AddMonoidHom.inr _ _
    · rintro (_|_) (_|_) ⟨⟨⟨⟩⟩⟩
      · simp
      · simp
  · refine' BinaryCofan.IsColimit.mk _ _ _ _ _
    · intro T f f'
      exact AddMonoidHom.coprod f f'
    · intro T f f'
      simp
      exact AddMonoidHom.coprod_comp_inl f f'
    · intro T f f'
      exact AddMonoidHom.coprod_comp_inr f f'
    · rintro T f f' g rfl rfl
      sorry -- AddMonoidHom.coprod_inl_inr somehow



lemma exercise33' {G H X : Type _} [AddCommGroup G] [AddCommGroup H] [AddCommGroup X]
    (f : G →+ X) (g : H →+ X) : ((AddMonoidHom.coprod f g).comp (AddMonoidHom.inl _ _)) = f := by
  simp only [AddMonoidHom.coprod_comp_inl]

lemma exercise33'' {G H X : Type _} [AddCommGroup G] [AddCommGroup H] [AddCommGroup X]
    (f : G →+ X) (g : H →+ X) : ((AddMonoidHom.coprod f g).comp (AddMonoidHom.inr _ _)) = g := by
  simp only [AddMonoidHom.coprod_comp_inr]

-- 3.4. Let G, H be groups, and assume that G = H x G. Can you conclude that H
-- is trivial? (Hint: No. Can you construct a counterexample?)
lemma exercise34 : ∃ (G H : Type) (_ : AddGroup G) (_ : AddGroup H), Nonempty (G ≃+ H × G) := by
  refine' ⟨ℕ → Fin 2, Fin 2, inferInstance, inferInstance, ⟨⟨_, _, _, _⟩, _⟩⟩
  · intro f
    exact (f 0, f ∘ Nat.succ)
  · intro ⟨i, f⟩
    exact Nat.rec i (λ x _ => f x)
  · intro _
    ext (_|_) <;>
    simp
  · intro (_, _)
    ext (_|_) <;>
    simp
  · intro f g
    simp only [Pi.add_apply, Prod.mk_add_mk, Prod.mk.injEq, true_and]
    funext
    simp

-- 3.5. Prove that Q is not the direct product of two nontrivial groups.
lemma exercise35 (G H : Type) [AddGroup G] [AddGroup H] (e : ℚ ≃+ G × H) :
    Nonempty (G ≃+ Unit) ∨ Nonempty (H ≃+ Unit) := by
  have h0 : ∀ (G : Type) [AddGroup G], ¬ Nonempty (G ≃+ Unit) → ∃ g : G, g ≠ 0
  · intro G
    contrapose!
    intro H
    have : Unique G := ⟨⟨0⟩, by simp [H]⟩
    exact ⟨default⟩
  by_contra key
  rw [not_or] at key
  obtain ⟨g, hg⟩ : ∃ g : G, g ≠ 0 := h0 _ key.left
  obtain ⟨h, hh⟩ : ∃ h : H, h ≠ 0 := h0 _ key.right
  set x := e.symm.toAddMonoidHom (g, 0) with hx
  set y := e.symm.toAddMonoidHom (0, h) with hy
  obtain ⟨A, B, hA, hB, H⟩ : ∃ (A B : ℤ) (_ : A ≠ 0) (_ : B ≠ 0), A • x = B • y
  · refine' ⟨y.num * x.den, x.num * y.den, _, _, _⟩
    · simp [not_or, hh, Rat.den_nz]
    · simp [not_or, hg, Rat.den_nz]
    · simp [←hx, ←hy, mul_assoc, mul_comm _ x, mul_comm _ y]; ring
  have : A • g = 0 ∧ B • h = 0
  · rw [hx, hy, ←map_zsmul, ←map_zsmul] at H
    simpa [eq_comm] using H
  suffices key : A • x = 0 ∧ B • y = 0
  · simp [hA, hg, hB, hh] at key
  simp [hx, hy, ←map_zsmul, -zsmul_eq_mul, this.left, this.right]

-- 3.6. Consider the product of the cyclic groups C2, C3 (cf. §2.3): C2 x C3. By
-- Exercise 3.3, this group is a coproduct of C2 and C3 in Ab. Show that it is not a
-- coproduct of C2 and C3 in Grp, as follows:
-- find injective homomorphisms C2 → S3, C3 → S3;
-- arguing by contradiction, assume that C2 x C3 is a coproduct of C2, C3, and
-- deduce that there would be a group homomorphism C2 x C3 → S3 with certain properties;
-- show that there is no such homomorphism.
def exercise36_hom2 : Fin 2 →+ Additive (Equiv.Perm (Fin 3)) :=
  AddMonoidHom.mk' (fun k => match k with
  | 0 => 0
  | 1 => Additive.ofMul (Equiv.swap 0 1)) (by
    intros a b
    have : (1 + 1 : Fin 2) = Fin.mk 0 zero_lt_two := rfl
    fin_cases a <;>
    fin_cases b <;>
    simp [this, ←ofMul_mul]
  )

lemma exercise36_hom2_injective : Function.Injective (exercise36_hom2) := by
  intro a b
  fin_cases a <;>
  fin_cases b
  · simp [exercise36_hom2]
  · rw [eq_comm]
    simp [exercise36_hom2]
  · simp [exercise36_hom2]
  · simp [exercise36_hom2]

section
set_option linter.unreachableTactic false
notation3 (prettyPrint := false) "cx["(l", "* => foldr (h t => List.cons h t) List.nil)"]" =>
  Cycle.formPerm (Cycle.ofList l) (by decide)
end

def exercise36_hom3 : Fin 3 →+ Additive (Equiv.Perm (Fin 3)) :=
  AddMonoidHom.mk' (fun k => match k with
  | 0 => 0
  | 1 => Additive.ofMul cx[0, 1, 2]
  | 2 => Additive.ofMul cx[0, 2, 1]
  ) (by
    intros a b
    have h2 : (⟨2, by norm_num⟩ : Fin 3) = 2 := rfl
    have h3 : (3 : Fin 3) = ⟨0, by norm_num⟩ := rfl
    have h4 : (4 : Fin 3) = ⟨1, by norm_num⟩ := rfl
    fin_cases a <;>
    fin_cases b
    · simp
    · simp
    · simp
    · simp
    · norm_num
      simp_rw [←h2, ←ofMul_mul]
      simp [-ofMul_mul]
    · norm_num [h2]
      simp_rw [←ofMul_mul]
      rw [h3, eq_comm]
      simp [-ofMul_mul]
    · simp
    · norm_num [h2]
      simp_rw [h3, ←ofMul_mul]
      rw [eq_comm]
      simp [-ofMul_mul]
    · norm_num [h2]
      simp_rw [h4, ←ofMul_mul]
      rw [eq_comm]
      simp [-ofMul_mul])

lemma exercise36_hom3_injective : Function.Injective (exercise36_hom3) := by
  intro a b
  fin_cases a <;>
  fin_cases b
  · simp [exercise36_hom3]
  · rw [eq_comm]
    simp [exercise36_hom3, add_eq_zero_iff_neg_eq, ←ofMul_inv]
  · rw [eq_comm]
    simp [exercise36_hom3, add_eq_zero_iff_neg_eq, ←ofMul_inv]
  · simp [exercise36_hom3, add_eq_zero_iff_neg_eq, ←ofMul_inv]
  · simp [exercise36_hom3]
  · rw [eq_comm]
    simp [exercise36_hom3]
    simp_rw [←ofMul_mul]
    simp [-ofMul_mul]
  · simp [exercise36_hom3, add_eq_zero_iff_neg_eq, ←ofMul_inv]
  · simp [exercise36_hom3]
    simp_rw [←ofMul_mul]
    simp [-ofMul_mul]
  · simp [exercise36_hom3, add_eq_zero_iff_neg_eq, ←ofMul_inv]

open AddMonoid AddMonoid.Coprod in
lemma exercise36 : ¬ Nonempty (Coprod (Fin 2) (Fin 3) ≃+ Fin 2 × Fin 3) := by
  rintro ⟨e⟩
  have f1 : (1 : Fin 2) = ⟨1, by norm_num⟩ := rfl
  have f1' : (1 : Fin 3) = ⟨1, by norm_num⟩ := rfl
  suffices : exercise36_hom2 1 + exercise36_hom3 1 = exercise36_hom3 1 + exercise36_hom2 1
  · simp only [exercise36_hom2, f1', Fin.mk_one, AddMonoidHom.mk'_apply, exercise36_hom3, mul_one,
               Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, f1] at this
    simp_rw [←ofMul_mul] at this
    simp [-ofMul_mul] at this
  rw [←lift_apply_inl exercise36_hom2 exercise36_hom3,
      ←lift_apply_inr exercise36_hom2 exercise36_hom3,
      ←e.symm_apply_apply (inl 1),
      ←e.symm_apply_apply (inr 1),
      ←map_add, ←map_add, add_comm, map_add, map_add]
