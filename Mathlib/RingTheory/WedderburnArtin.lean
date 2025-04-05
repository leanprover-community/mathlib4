/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.TwoSidedIdeal.SpanAsSum

/-!
# Wedderburn-Artin Theorem (for simple rings)


-/
variable (A : Type*) [Ring A]

open BigOperators Matrix MulOpposite

local notation "M[" ι "," R "]" => Matrix ι ι R

variable (ι : Type) [Fintype ι]


section simple_ring

open MulOpposite

variable (K D : Type*) [Field K] [IsSimpleRing A] [Algebra K A] [DivisionRing D]


namespace TwoSidedIdeal
variable {R : Type*} [Ring R]
/--
Any two-sided-ideal in `A` corresponds to a two-sided-ideal in `Aᵒᵖ`.
-/
@[simps]
def toMop (rel : TwoSidedIdeal R) : (TwoSidedIdeal Rᵐᵒᵖ) :=
  .mk
  { r := fun a b ↦ rel.ringCon b.unop a.unop
    iseqv :=
    { refl := fun a ↦ rel.ringCon.refl a.unop
      symm := rel.ringCon.symm
      trans := fun h1 h2 ↦ rel.ringCon.trans h2 h1 }
    mul' := fun h1 h2 ↦ rel.ringCon.mul h2 h1
    add' := rel.ringCon.add }

/--
Any two-sided-ideal in `Aᵒᵖ` corresponds to a two-sided-ideal in `A`.
-/
@[simps]
def fromMop (rel : TwoSidedIdeal Rᵐᵒᵖ) : (TwoSidedIdeal R) :=
  .mk
  { r := fun a b ↦ rel.ringCon (op b) (op a)
    iseqv :=
    { refl := fun a ↦ rel.ringCon.refl (op a)
      symm := rel.ringCon.symm
      trans := fun h1 h2 ↦ rel.ringCon.trans h2 h1 }
    mul' := fun h1 h2 ↦ rel.ringCon.mul h2 h1
    add' := rel.ringCon.add }

/--
Two-sided-ideals of `A` and that of `Aᵒᵖ` corresponds bijectively to each other.
-/
@[simps]
def toMopOrderIso : (TwoSidedIdeal R) ≃o (TwoSidedIdeal Rᵐᵒᵖ) where
  toFun := toMop
  invFun := fromMop
  left_inv := unop_op
  right_inv := unop_op
  map_rel_iff' {a b} :=
    ⟨fun h x H ↦ b.ringCon.symm <| @h (MulOpposite.op x) <|
        by simpa [toMop, mem_iff] using a.ringCon.symm H,
    fun h x H ↦ b.ringCon.symm <| @h (MulOpposite.unop x) <|
        by simpa [fromMop, mem_iff] using a.ringCon.symm H⟩

end TwoSidedIdeal

instance op_simple : IsSimpleRing Aᵐᵒᵖ := ⟨TwoSidedIdeal.toMopOrderIso.symm.isSimpleOrder⟩

/--
The canonical map from `Aᵒᵖ` to `Hom(A, A)`
-/
@[simps]
def mopToEnd : Aᵐᵒᵖ →+* Module.End A A where
  toFun a :=
    { toFun := fun x ↦ x * a.unop
      map_add' := by simp [add_mul]
      map_smul' := by simp [mul_assoc] }
  map_zero' := by aesop
  map_one' := by aesop
  map_add' := by aesop
  map_mul' := by aesop


/--
The canonical map from `A` to `Hom(A, A)ᵒᵖ`
-/
@[simps]
def toEndMop : A →+* (Module.End A A)ᵐᵒᵖ where
  toFun a := op
    { toFun := fun x ↦ x * a
      map_add' := by simp [add_mul]
      map_smul' := by intros; simp [mul_assoc] }
  map_zero' := by aesop
  map_one' := by aesop
  map_add' := by intros; apply_fun MulOpposite.unop using unop_injective; ext; simp
  map_mul' := by intros; apply_fun MulOpposite.unop using unop_injective; ext; simp

/--
the map `Aᵒᵖ → Hom(A, A)` is bijective
-/
noncomputable def mopEquivEnd : Aᵐᵒᵖ ≃+* Module.End A A :=
  RingEquiv.ofBijective (mopToEnd A) ⟨RingHom.injective_iff_ker_eq_bot _ |>.mpr <|
    SetLike.ext fun α => ⟨by rintro (ha : mopToEnd A α = 0); simpa using (DFunLike.ext_iff.mp ha) 1,
      by rintro rfl; ext; simp⟩, fun φ => ⟨op (φ 1), by ext; simp⟩⟩

/--
the map `Aᵒᵖ → Hom(A, A)` is bijective
-/
@[simps!]
noncomputable def equivEndMop : A ≃+* (Module.End A A)ᵐᵒᵖ :=
  RingEquiv.ofBijective (toEndMop A) ⟨RingHom.injective_iff_ker_eq_bot _ |>.mpr <| SetLike.ext
    fun α => ⟨fun ha => by
      simp only [RingHom.mem_ker, toEndMop_apply, op_eq_zero_iff, DFunLike.ext_iff,
        LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply] at ha
      simpa using ha 1, fun (ha : α = 0) => by simp [ha]⟩,
      fun φ => ⟨φ.unop 1, unop_injective <| by ext; simp⟩⟩

/--
For any ring `D`, `Mₙ(D) ≅ Mₙ(D)ᵒᵖ`.
-/
@[simps]
def matrixEquivMatrixMop (n : ℕ) (D : Type*) [Ring D] :
    Matrix (Fin n) (Fin n) Dᵐᵒᵖ ≃+* (Matrix (Fin n) (Fin n) D)ᵐᵒᵖ where
  toFun := fun M => MulOpposite.op (M.transpose.map (fun d => MulOpposite.unop d))
  invFun := fun M => (MulOpposite.unop M).transpose.map (fun d => MulOpposite.op d)
  left_inv a := by aesop
  right_inv a := by aesop
  map_mul' x y := unop_injective <| by ext; simp [transpose_map, transpose_apply, mul_apply]
  map_add' x y := by aesop

universe u

lemma Ideal.eq_of_le_of_isSimpleModule {A : Type u} [Ring A]
    (I : Ideal A) [simple : IsSimpleModule A I]
    (J : Ideal A) (ineq : J ≤ I) (a : A) (ne_zero : a ≠ 0) (mem : a ∈ J) : J = I := by
  obtain eq | eq : Submodule.comap I.subtype J = ⊥ ∨ Submodule.comap I.subtype J = ⊤ :=
    simple.2 _
  · rw [Submodule.eq_bot_iff] at eq
    specialize eq ⟨a, ineq mem⟩ (by simpa [Subtype.ext_iff])
    rw [Subtype.ext_iff] at eq
    exact ne_zero eq |>.elim
  · simp only [Submodule.comap_subtype_eq_top] at eq
    exact le_antisymm ineq eq

lemma minimal_ideal_isSimpleModule {A : Type u} [Ring A]
    (I : Ideal A) (I_nontrivial : I ≠ ⊥)
    (I_minimal : ∀ J : Ideal A, J ≠ ⊥ → ¬ J < I) :
    IsSimpleModule A I := by
  letI ins1 : Nontrivial I := by
    obtain ⟨y, hy⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr I_nontrivial)
    exact ⟨0, y, hy.symm⟩
  refine ⟨fun J ↦ ?_⟩
  rw [or_iff_not_imp_left]
  intro hJ
  specialize I_minimal (J.map I.subtype : Ideal A) (by
    contrapose! hJ
    apply_fun Submodule.comap (f := I.subtype) at hJ
    rw [Submodule.comap_map_eq_of_injective (hf := Submodule.injective_subtype _)] at hJ
    rw [hJ, Submodule.comap_bot]
    rw [LinearMap.ker_eq_bot]
    exact Submodule.injective_subtype _)
  apply_fun Submodule.map (f := I.subtype) using Submodule.map_injective_of_injective
    (hf := Submodule.injective_subtype I)
  simp only [Submodule.map_top, Submodule.range_subtype]
  contrapose! I_minimal
  refine lt_of_le_of_ne (fun x hx ↦ ?_) I_minimal
  simp only [Submodule.mem_map, Submodule.coe_subtype, Subtype.exists, exists_and_right,
    exists_eq_right] at hx
  exact hx.1

lemma Wedderburn_Artin.aux.one_eq
    {A : Type u} [Ring A] [simple : IsSimpleRing A]
    (I : Ideal A) (I_nontrivial : I ≠ ⊥) :
    ∃ (n : ℕ) (x : Fin n → A) (i : Fin n → I), ∑ j : Fin n, i j * x j = 1 := by

  letI I' : TwoSidedIdeal A := TwoSidedIdeal.span I
  have I'_is_everything : I' = ⊤ := simple.1.2 I' |>.resolve_left (fun r ↦ by
    obtain ⟨y, hy⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr I_nontrivial)
    have hy' : y.1 ∈ I' := by
      change I'.ringCon y 0
      exact .of _ _ <| by simp [y.2]
    rw [r] at hy'
    change _ = _ at hy'
    aesop)
  have one_mem_I' : 1 ∈ I' := by rw [I'_is_everything]; trivial

  rw [TwoSidedIdeal.mem_span_ideal_iff_exists_fin] at one_mem_I'
  obtain ⟨n, finn, x, y, hy⟩ := one_mem_I'
  exact ⟨Fintype.card n, x ∘ (Fintype.equivFin _).symm, y ∘ (Fintype.equivFin _).symm, hy ▸
    Fintype.sum_bijective (Fintype.equivFin _).symm (Equiv.bijective _) _ _ fun k ↦ rfl⟩

private noncomputable abbrev Wedderburn_Artin.aux.n
    {A : Type u} [Ring A] [simple : IsSimpleRing A]
    (I : Ideal A) (I_nontrivial : I ≠ ⊥) : ℕ := by
  classical
  exact Nat.find <| Wedderburn_Artin.aux.one_eq I I_nontrivial

private noncomputable abbrev Wedderburn_Artin.aux.x
    {A : Type u} [Ring A] [simple : IsSimpleRing A]
    (I : Ideal A) (I_nontrivial : I ≠ ⊥) :
    Fin (Wedderburn_Artin.aux.n I I_nontrivial) → A  := by
  classical
  exact (Nat.find_spec <| Wedderburn_Artin.aux.one_eq I I_nontrivial).choose

private noncomputable abbrev Wedderburn_Artin.aux.i
    {A : Type u} [Ring A] [simple : IsSimpleRing A]
    (I : Ideal A) (I_nontrivial : I ≠ ⊥) :
    Fin (Wedderburn_Artin.aux.n I I_nontrivial) → I := by
  classical
  exact (Nat.find_spec <| Wedderburn_Artin.aux.one_eq I I_nontrivial).choose_spec.choose

open Wedderburn_Artin.aux in
private noncomputable abbrev Wedderburn_Artin.aux.nxi_spec
    {A : Type u} [Ring A] [simple : IsSimpleRing A]
    (I : Ideal A) (I_nontrivial : I ≠ ⊥) :
    ∑ j : Fin (n I I_nontrivial), (i I I_nontrivial j) * (x I I_nontrivial j) = 1 := by
  classical
  exact (Nat.find_spec <| Wedderburn_Artin.aux.one_eq I I_nontrivial).choose_spec.choose_spec

lemma Wedderburn_Artin.aux.n_ne_zero
    {A : Type u} [Ring A] [simple : IsSimpleRing A]
    (I : Ideal A) (I_nontrivial : I ≠ ⊥) :
    NeZero <| Wedderburn_Artin.aux.n I I_nontrivial := by
  constructor
  by_contra hn
  let n : ℕ := Wedderburn_Artin.aux.n I I_nontrivial
  let x : Fin n → A := Wedderburn_Artin.aux.x I I_nontrivial
  let i : Fin n → I := Wedderburn_Artin.aux.i I I_nontrivial
  have one_eq : ∑ j : Fin n, (i j) * (x j) = 1 :=
    Wedderburn_Artin.aux.nxi_spec I I_nontrivial

  let e : Fin n ≃ Fin 0 := Fin.castOrderIso hn
  simpa using calc 1
    _ = _ := one_eq.symm
    _ = ∑ j : Fin 0, i (e.symm j) * x (e.symm j) :=
        Fintype.sum_bijective e e.bijective _ _ (fun _ ↦ rfl)
    _ = 0 := by simp

open Wedderburn_Artin.aux in
private noncomputable abbrev Wedderburn_Artin.aux.nxi_ne_zero
    {A : Type u} [Ring A] [simple : IsSimpleRing A]
    (I : Ideal A) (I_nontrivial : I ≠ ⊥) :
    ∀ j, x I I_nontrivial j ≠ 0 ∧ i I I_nontrivial j ≠ 0 := by
  classical
  let n : ℕ := Wedderburn_Artin.aux.n I I_nontrivial
  have n_ne : NeZero n := Wedderburn_Artin.aux.n_ne_zero I I_nontrivial
  have n_ne' : n ≠ 0 := n_ne.1
  let x : Fin n → A := Wedderburn_Artin.aux.x I I_nontrivial
  let i : Fin n → I := Wedderburn_Artin.aux.i I I_nontrivial
  have one_eq : ∑ j : Fin n, (i j) * (x j) = 1 := Wedderburn_Artin.aux.nxi_spec I I_nontrivial

  by_contra! H
  obtain ⟨j, (hj : x j ≠ 0 → i j = 0)⟩ := H
  refine Nat.find_min (aux.one_eq I I_nontrivial) (m := n - 1)
    (show n - 1 < n by omega) ?_

  let e : Fin n ≃ Option (Fin (n - 1)) :=
    (Fin.castOrderIso <| by omega).toEquiv.trans (finSuccEquiv' (j.cast <| by omega))
  have one_eq := calc 1
    _ = _ := one_eq.symm
    _ = ∑ j : Option (Fin (n - 1)), i (e.symm j) * x (e.symm j) :=
        Fintype.sum_bijective e (Equiv.bijective _) _ _ (fun _ ↦ by simp)
  simp only [Equiv.symm_trans_apply, OrderIso.toEquiv_symm, Fin.symm_castOrderIso,
    RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Fintype.sum_option, finSuccEquiv'_symm_none,
    Fin.cast_trans, Fin.cast_eq_self, finSuccEquiv'_symm_some, e] at one_eq
  if xj_eq : x j = 0
  then rw [xj_eq, mul_zero, zero_add] at one_eq; exact ⟨_, _, one_eq.symm⟩
  else erw [hj xj_eq, Submodule.coe_zero, zero_mul, zero_add] at one_eq; exact ⟨_, _, one_eq.symm⟩

lemma Wedderburn_Artin.aux.equivIdeal
    {A : Type u} [Ring A] [simple : IsSimpleRing A]
    (I : Ideal A) (I_nontrivial : I ≠ ⊥) (I_minimal : ∀ J : Ideal A, J ≠ ⊥ → ¬ J < I) :
    ∃ (n : ℕ) (_ : NeZero n), Nonempty ((Fin n → I) ≃ₗ[A] A) := by
  classical
  letI n : ℕ := Wedderburn_Artin.aux.n I I_nontrivial
  have n_ne : NeZero n := Wedderburn_Artin.aux.n_ne_zero I I_nontrivial
  have n_ne' : n ≠ 0 := n_ne.1
  letI x : Fin n → A := Wedderburn_Artin.aux.x I I_nontrivial
  letI i : Fin n → I := Wedderburn_Artin.aux.i I I_nontrivial
  have one_eq : ∑ j : Fin n, (i j) * (x j) = 1 :=
    Wedderburn_Artin.aux.nxi_spec I I_nontrivial

  haveI : IsSimpleModule A I := minimal_ideal_isSimpleModule I I_nontrivial I_minimal

  letI g : (Fin n → I) →ₗ[A] A :=
  { toFun := fun v ↦ ∑ j : Fin n, v j * x j
    map_add' := fun v1 v2 => by simp [add_mul, Finset.sum_add_distrib]
    map_smul' := fun a v => by simp [Finset.mul_sum, mul_assoc] }

  have g_surj : Function.Surjective g := fun a =>
    ⟨fun j ↦ ⟨a * (i j), I.mul_mem_left _ (i j).2⟩,
      by simp [g, mul_assoc, ← Finset.mul_sum, one_eq]⟩

  have g_inj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot]
    by_contra!
    obtain ⟨⟨y, (hy1 : ∑ j : Fin n, _ = 0)⟩, hy2⟩ :=
      Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr this)
    replace hy2 : y ≠ 0 := by contrapose! hy2; subst hy2; rfl
    obtain ⟨j, hj⟩ : ∃ (j : Fin n), y j ≠ 0 := by contrapose! hy2; ext; rw [hy2]; rfl
    have eq1 : Ideal.span {(y j).1} = I :=
      Ideal.eq_of_le_of_isSimpleModule (A := A) I (Ideal.span {(y j).1})
      (by simp only [Ideal.span_le, Set.singleton_subset_iff, Subtype.coe_prop]) (y j).1
      (by contrapose! hj; rwa [Subtype.ext_iff]) <| Ideal.subset_span
        (by simp only [Set.mem_singleton_iff])

    have mem : (i j).1 ∈ Ideal.span {(y j).1} := eq1.symm ▸ (i j).2
    rw [Ideal.mem_span_singleton'] at mem
    obtain ⟨r, hr⟩ := mem
    have hr' : (i j).1 - r * (y j).1 = 0 := by rw [hr, sub_self]
    apply_fun (r * ·) at hy1
    simp only [Finset.mul_sum, ← mul_assoc, mul_zero] at hy1
    have one_eq' : ∑ j : Fin n, ↑(i j) * x j - ∑ _, _ = 1 - 0 := congr_arg₂ (· - ·) one_eq hy1
    rw [← Finset.sum_sub_distrib, sub_zero] at one_eq'
    let e : Fin n ≃ Option (Fin (n - 1)) :=
      (Fin.castOrderIso <| by omega).toEquiv.trans (finSuccEquiv' (j.cast <| by omega))

    have one_eq' := calc 1
      _ = _ := one_eq'.symm
      _ = ∑ k : Option (Fin (n - 1)),
            (i (e.symm k) * x (e.symm k) - r * y (e.symm k) * x (e.symm k)) :=
          Fintype.sum_bijective e (Equiv.bijective _) _ _ (fun _ ↦ by simp)
      _ = ∑ k : Option (Fin (n - 1)),
            ((i (e.symm k) - r * y (e.symm k)) * x (e.symm k)) :=
          Finset.sum_congr rfl (fun _ _ ↦ by simp only [sub_mul, mul_assoc])

    simp only [Equiv.symm_trans_apply, OrderIso.toEquiv_symm, Fin.symm_castOrderIso,
      RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Fintype.sum_option, finSuccEquiv'_symm_none,
      Fin.cast_trans, Fin.cast_eq_self, hr', zero_mul, finSuccEquiv'_symm_some, zero_add,
      e] at one_eq'
    set f := _
    change 1 = ∑ k : Fin (n - 1), (i ∘ f - (r • y) ∘ f) k * (x ∘ f) k at one_eq'
    exact Nat.find_min (Wedderburn_Artin.aux.one_eq I I_nontrivial) (m := n - 1)
      (show n - 1 < n by omega) ⟨_, _, one_eq'.symm⟩
  exact ⟨n, n_ne, ⟨LinearEquiv.ofBijective g ⟨g_inj, g_surj⟩⟩⟩

/-- RingEquiv version of `endVecAlgEquivMatrixEnd` -/
private def endPowEquivMatrix (A : Type*) [Ring A]
    (M : Type*) [AddCommGroup M] [Module A M] (n : ℕ):
    Module.End A (Fin n → M) ≃+* Matrix (Fin n) (Fin n) (Module.End A M) :=
  endVecAlgEquivMatrixEnd (Fin n) ℤ A M

theorem Wedderburn_Artin_ideal_version
    (A : Type u) [Ring A] [IsArtinianRing A] [simple : IsSimpleRing A] :
    ∃ (n : ℕ) (_ : NeZero n) (I : Ideal A) (_ : IsSimpleModule A I),
    Nonempty ((Fin n → I) ≃ₗ[A] A) := by
  classical
  obtain ⟨(I : Ideal A), (I_nontrivial : I ≠ ⊥), (I_minimal : ∀ J : Ideal A, J ≠ ⊥ → ¬ J < I)⟩ :=
      IsArtinian.set_has_minimal (R := A) (M := A) {I | I ≠ ⊥}
    ⟨⊤, show ⊤ ≠ ⊥ by aesop⟩
  haveI : IsSimpleModule A I := minimal_ideal_isSimpleModule I I_nontrivial I_minimal
  obtain ⟨n, hn, ⟨e⟩⟩ := Wedderburn_Artin.aux.equivIdeal I I_nontrivial I_minimal
  exact ⟨n, hn, I, inferInstance, ⟨e⟩⟩

theorem Wedderburn_Artin
    (A : Type u) [Ring A] [IsArtinianRing A] [simple : IsSimpleRing A] :
    ∃ (n : ℕ) (_ : NeZero n) (I : Ideal A) (_ : IsSimpleModule A I),
    Nonempty (A ≃+* M[Fin n, (Module.End A I)ᵐᵒᵖ]) := by
  classical
  obtain ⟨(I : Ideal A), (I_nontrivial : I ≠ ⊥), (I_minimal : ∀ J : Ideal A, J ≠ ⊥ → ¬ J < I)⟩ :=
      IsArtinian.set_has_minimal (R := A) (M := A) {I | I ≠ ⊥}
    ⟨⊤, show ⊤ ≠ ⊥ by aesop⟩
  haveI : IsSimpleModule A I := minimal_ideal_isSimpleModule I I_nontrivial I_minimal
  obtain ⟨n, hn, ⟨e⟩⟩ := Wedderburn_Artin.aux.equivIdeal I I_nontrivial I_minimal
  let endEquiv : Module.End A A ≃+* Module.End A (Fin n → I) :=
  { toFun := fun f ↦ e.symm ∘ₗ f ∘ₗ e
    invFun := fun f ↦ e ∘ₗ f ∘ₗ e.symm
    left_inv := by intro f; ext; simp
    right_inv := by intro f; ext; simp
    map_add' := by intros f g; ext; simp
    map_mul' := by intros f g; ext; simp }
  refine ⟨n, hn, I, inferInstance, ⟨(equivEndMop A).trans <| endEquiv.op.trans <|
    (endPowEquivMatrix A I n).op.trans <| (matrixEquivMatrixMop n (Module.End A I)).symm⟩⟩

theorem Wedderburn_Artin'
    (A : Type u) [Ring A] [IsArtinianRing A] [simple : IsSimpleRing A] :
    ∃ (n : ℕ) (_ : NeZero n) (S : Type u) (_ : DivisionRing S),
    Nonempty (A ≃+* (M[Fin n, S])) := by
  classical
  obtain ⟨n, hn, I, inst, e⟩ := Wedderburn_Artin A
  exact ⟨n, hn, (Module.End A I)ᵐᵒᵖ, inferInstance, e⟩

end simple_ring

universe u v w
section central_simple

variable (K : Type u) (B : Type v) [Field K] [Ring B] [Algebra K B] [FiniteDimensional K B]

lemma Matrix.mem_center_iff (R : Type*) [Ring R] (n : ℕ) (M) :
    M ∈ Subring.center M[Fin n, R] ↔ ∃ α : (Subring.center R), M = α • 1 := by
  constructor
  · if h : n = 0 then subst h; exact fun _ => ⟨0, Subsingleton.elim _ _⟩
    else
      intro h
      rw [Subring.mem_center_iff] at h
      have diag : Matrix.IsDiag M := fun i j hij => by
        simpa only [StdBasisMatrix.mul_left_apply_same, one_mul,
          StdBasisMatrix.mul_right_apply_of_ne (hbj := hij.symm)] using
          Matrix.ext_iff.2 (h (stdBasisMatrix i i 1)) i j
      have (i j : Fin n) : M i i = M j j := by
        simpa [Eq.comm] using Matrix.ext_iff.2 (h (stdBasisMatrix i j 1)) i j
      obtain ⟨b, hb⟩ : ∃ (b : R), M = b • 1 := by
        refine ⟨M ⟨0, by omega⟩ ⟨0, by omega⟩, Matrix.ext fun i j => ?_⟩
        if heq : i = j then subst heq; rw [this i ⟨0, by omega⟩]; simp
        else simp [diag heq, Matrix.one_apply_ne heq]
      suffices b ∈ Subring.center R by aesop
      refine Subring.mem_center_iff.mpr fun g => ?_
      simpa [hb] using Matrix.ext_iff.2 (h (Matrix.diagonal fun _ => g)) ⟨0, by omega⟩ ⟨0, by omega⟩
  · rintro ⟨α, ha⟩; rw [Subring.mem_center_iff]; aesop

lemma Matrix.mem_center_iff' (K R : Type*) [Field K] [Ring R] [Algebra K R] (n : ℕ) (M) :
    M ∈ Subalgebra.center K M[Fin n, R] ↔
    ∃ α : (Subalgebra.center K R), M = α • 1 := Matrix.mem_center_iff R n M

theorem RingEquiv.mem_center_iff {R1 R2 : Type*} [Ring R1] [Ring R2] (e : R1 ≃+* R2) :
    ∀ x, x ∈ Subring.center R1 ↔ e x ∈ Subring.center R2 := fun x => by
  simpa only [Subring.mem_center_iff] using
    ⟨fun h r => e.symm.injective <| by simp [h], fun h r => e.injective <| by simpa using h (e r)⟩

variable {B} in
/--
For a `K`-algebra B, there is a map from `I : Ideal B` to `End(I)ᵒᵖ` defined by `k ↦ x ↦ k • x`.
-/
@[simps]
def algebraMapEndIdealMop (I : Ideal B) : K →+* (Module.End B I)ᵐᵒᵖ where
  toFun k := .op <|
  { toFun := fun x => k • x
    map_add' := fun x y => by simp
    map_smul' := fun k' x => by ext; simp }
  map_one' := unop_injective <| by ext; simp
  map_mul' _ _ := unop_injective <| by ext; simp [MulAction.mul_smul]
  map_zero' := unop_injective <| by ext; simp
  map_add' _ _ := unop_injective <| by ext; simp [add_smul]

instance (I : Ideal B) : Algebra K (Module.End B I)ᵐᵒᵖ where
  algebraMap := algebraMapEndIdealMop K I
  commutes' := fun r ⟨x⟩ => MulOpposite.unop_injective <| DFunLike.ext _ _ fun ⟨i, hi⟩ =>
    Subtype.ext <| show (x (r • ⟨i, hi⟩)).1 = r • (x ⟨i, hi⟩).1 by
      convert Subtype.ext_iff.mp (x.map_smul (algebraMap K B r) ⟨i, hi⟩) using 1 <;> aesop
  smul k x := .op <| (algebraMapEndIdealMop K I k).unop * x.unop
  smul_def' := fun r ⟨x⟩ => MulOpposite.unop_injective <| DFunLike.ext _ _ fun ⟨i, hi⟩ =>
    Subtype.ext <| by
      convert Subtype.ext_iff.mp (x.map_smul (algebraMap K B r) ⟨i, hi⟩) |>.symm using 1 <;> aesop

omit [FiniteDimensional K B] in
lemma algebraEndIdealMop.algebraMap_eq (I : Ideal B) :
    algebraMap K (Module.End B I)ᵐᵒᵖ = algebraMapEndIdealMop K I := rfl

lemma Wedderburn_Artin_algebra_version' (R : Type u) (A : Type v) [CommRing R] [Ring A]
  [sim : IsSimpleRing A] [Algebra R A] [hA : IsArtinianRing A] :
    ∃ (n : ℕ) (_ : NeZero n) (S : Type v) (_ : DivisionRing S) (_ : Algebra R S),
    Nonempty (A ≃ₐ[R] (M[Fin n, S])) := by
  classical
  obtain ⟨n, hn, I, inst_I, ⟨e⟩⟩ := Wedderburn_Artin_ideal_version A

  let endEquiv : Module.End A A ≃+* Module.End A (Fin n → I) :=
  { toFun := fun f ↦ e.symm ∘ₗ f ∘ₗ e
    invFun := fun f ↦ e ∘ₗ f ∘ₗ e.symm
    left_inv := by intro f; ext; simp
    right_inv := by intro f; ext; simp
    map_add' := by intros f g; ext; simp
    map_mul' := by intros f g; ext; simp }

  refine ⟨n, hn, (Module.End A I)ᵐᵒᵖ, inferInstance, inferInstance, ⟨AlgEquiv.ofRingEquiv
    (f := equivEndMop A |>.trans <| endEquiv.op.trans <| (endPowEquivMatrix A I n).op.trans
    (matrixEquivMatrixMop n (Module.End A I)).symm) ?_⟩⟩
  intro r
  rw [Matrix.algebraMap_eq_diagonal]
  ext i j
  apply MulOpposite.unop_injective
  simp only [endPowEquivMatrix, RingEquiv.coe_trans, Function.comp_apply, equivEndMop_apply,
    RingEquiv.op_apply_apply, unop_op, RingEquiv.coe_mk, Equiv.coe_fn_mk, AlgEquiv.coe_ringEquiv,
    matrixEquivMatrixMop_symm_apply, map_apply, transpose_apply, diagonal, Pi.algebraMap_apply,
    MulOpposite.algebraMap_apply, of_apply, endEquiv]
  split_ifs with h
  · subst h
    ext x : 1
    simp only [endVecAlgEquivMatrixEnd_apply_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, unop_op, Module.algebraMap_end_apply,
      endEquiv]
    rw [show r • x = Function.update (0 : Fin n → I) i (r • x) i by simp]
    refine congr_fun (e.injective ?_) i
    simp only [LinearEquiv.apply_symm_apply, endEquiv]
    rw [show Function.update (0 : Fin n → I) i (r • x) = r • Function.update (0 : Fin n → I) i x
      by ext : 1; simp [Function.update]]
    rw [← Algebra.commutes, ← smul_eq_mul, ← e.map_smul]
    exact congr_arg e <| by ext; simp [Pi.single]
  · ext x : 1
    simp only [LinearMap.coe_mk, AddHom.coe_mk, MulOpposite.unop_zero, LinearMap.zero_apply]
    rw [show (0 : I) = Function.update (0 : Fin n → I) i (r • x) j
      by simp [Function.update, if_neg (Ne.symm h)]]
    refine congr_fun (e.injective ?_) j
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_mk, AddHom.coe_mk,
      Function.comp_apply, LinearEquiv.apply_symm_apply]
    rw [show Function.update (0 : Fin n → I) i (r • x) = r • Function.update (0 : Fin n → I) i x
      by ext : 1; simp [Function.update]]
    rw [← Algebra.commutes, ← smul_eq_mul, ← e.map_smul]
    exact congr_arg e <| by ext; simp [Pi.single]

lemma Wedderburn_Artin_algebra_version
    [sim : IsSimpleRing B]:
    ∃ (n : ℕ) (_ : NeZero n) (S : Type v) (_ : DivisionRing S) (_ : Algebra K S),
    Nonempty (B ≃ₐ[K] (M[Fin n, S])) := by
  classical
  have hB : IsArtinianRing B := .of_finite K B
  exact Wedderburn_Artin_algebra_version' K B

end central_simple
