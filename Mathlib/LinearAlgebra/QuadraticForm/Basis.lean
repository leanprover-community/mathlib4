/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Finset.Sym

/-!
# Constructing a bilinear form from a quadratic form, given a basis

This file provides an alternative to `QuadraticForm.associated`; unlike that definition, this one
does not require `Invertible (2 : R)`. Unlike that definition, this only works in the presence of
a basis.

## TODO

Show that `Q
-/

namespace Sym2
variable {α}

def sup [SemilatticeSup α] (x : Sym2 α) : α := Sym2.lift ⟨(· ⊔ ·), sup_comm⟩ x

@[simp] theorem sup_mk [SemilatticeSup α] (a b : α) : s(a, b).sup = a ⊔ b := rfl

def inf [SemilatticeInf α] (x : Sym2 α) : α := Sym2.lift ⟨(· ⊓ ·), inf_comm⟩ x

@[simp] theorem inf_mk [SemilatticeInf α] (a b : α) : s(a, b).inf = a ⊓ b := rfl

theorem inf_le_sup [Lattice α] (s : Sym2 α) : s.inf ≤ s.sup := by
  cases s using Sym2.ind; simp [_root_.inf_le_sup]

@[simps!]
def sortEquiv [LinearOrder α] : Sym2 α ≃ { p : α × α // p.1 ≤ p.2 } where
  toFun s := ⟨(s.inf, s.sup), inf_le_sup _⟩
  invFun p := Sym2.mk p
  left_inv := Sym2.ind fun a b => mk_eq_mk_iff.mpr <| by
    cases le_total a b with
    | inl h => simp [h]
    | inr h => simp [h]
  right_inv := Subtype.rec <| Prod.rec fun x y hxy => Subtype.ext <| Prod.ext (by simp [hxy]) (by simp [hxy])

end Sym2

theorem Finset.offDiag_filter_lt_eq_filter_le {ι}
    [PartialOrder ι]
    [DecidableEq ι] [DecidableRel (LE.le (α := ι))] [DecidableRel (LT.lt (α := ι))]
    (s : Finset ι) :
    s.offDiag.filter (fun i => i.1 < i.2) = s.offDiag.filter (fun i => i.1 ≤ i.2) := by
  ext ⟨i, j⟩
  simp only [mem_filter, mem_offDiag, ne_eq, and_congr_right_iff, and_imp]
  rintro _ _ h
  rw [Ne.le_iff_lt h]


theorem Finset.sum_sym2_filter_not_isDiag {ι α} [LinearOrder ι] [AddCommMonoid α]
    (s : Finset ι) (p : Sym2 ι → α) :
    ∑ i in s.sym2.filter (¬ ·.IsDiag), p i =
      ∑ i in s.offDiag.filter (fun i => i.1 < i.2), p s(i.1, i.2) := by
  rw [Finset.offDiag_filter_lt_eq_filter_le]
  conv_rhs => rw [← Finset.sum_subtype_eq_sum_filter]
  refine (Finset.sum_equiv Sym2.sortEquiv.symm ?_ ?_).symm
  · rintro ⟨⟨i₁, j₁⟩, hij₁⟩
    simp [and_assoc]
  · rintro ⟨⟨i₁, j₁⟩, hij₁⟩
    simp

-- def Finsupp.sym2 {ι α β} [Zero α] [Zero β] (f : ι →₀ α) : Sym2 ι →₀ β where
--   { support := f.support.sym2 (Sym2.map f, _⟩


namespace QuadraticForm

variable {ι R M} [LinearOrder ι] [CommRing R] [AddCommGroup M] [Module R M]

noncomputable def aux (Q : QuadraticForm R M) (b : Basis ι R M) : Sym2 ι → R :=
  Sym2.lift ⟨fun i j => if i = j then Q (b i) else polar Q (b i) (b j), fun i j => by
    dsimp
    obtain rfl | hij := eq_or_ne i j
    · rw [if_pos rfl]
    · rw [if_neg hij, if_neg hij.symm, polar_comm]⟩

noncomputable def equivCoeffs [Fintype ι] (b : Basis ι R M) :
    QuadraticForm R M ≃ₗ[R] (Sym2 ι → R) where
  toFun Q :=
    Sym2.lift ⟨fun i j => if i = j then Q (b i) else polar Q (b i) (b j), fun i j => by
      dsimp
      obtain rfl | hij := eq_or_ne i j
      · rw [if_pos rfl]
      · rw [if_neg hij, if_neg hij.symm, polar_comm]⟩
  invFun coeffs :=
    ∑ ij, coeffs ij • Sym2.lift ⟨fun i j => linMulLin (b.coord i) (b.coord j), fun i j => by
      ext; simp [mul_comm]⟩ ij
  map_add' Q₁ Q₂ := by
    ext ij
    -- induction ij using Sym2.ind with | _ i j => ?_
    -- simp only [add_apply, coeFn_add, Sym2.lift_mk, Pi.add_apply]
    -- obtain rfl | hij := eq_or_ne i j
    -- · simp
    -- · simp [hij, polar_add]
  map_smul' c Q :=by
    ext ij
    -- induction ij using Sym2.ind with | _ i j => ?_
    -- simp only [add_apply, coeFn_add, Sym2.lift_mk, Pi.add_apply]
    -- obtain rfl | hij := eq_or_ne i j
    -- · simp
    -- · simp [hij, polar_smul]
  left_inv Q := by
    dsimp
    sorry
  right_inv coeffs := by
    ext ij
    induction ij using Sym2.ind with | _ i j => ?_
    dsimp
    simp_rw [sum_apply, smul_apply, smul_eq_mul]
    obtain rfl | hij := eq_or_ne i j
    · rw [if_pos rfl, Fintype.sum_eq_single s(i, i), Sym2.lift_mk, Subtype.coe_mk,
        linMulLin_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same,
        mul_one, mul_one]
      simp_rw [Sym2.forall]
      simp only [ne_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, or_self,
        Sym2.lift_mk, linMulLin_apply, not_and_or, Basis.coord_apply, Basis.repr_self]
      rintro x y (hx | hy)
      · rw [Finsupp.single_eq_of_ne (Ne.symm hx), zero_mul, mul_zero]
      · rw [Finsupp.single_eq_of_ne (Ne.symm hy), mul_zero, mul_zero]
    · simp_rw [if_neg hij, coeFn_sum, polar_sum, coeFn_smul, polar_smul]
      rw [Fintype.sum_eq_single s(i, j), Pi.smul_apply, Sym2.lift_mk, Subtype.coe_mk, Pi.smul_apply,
        polar]
      simp_rw[linMulLin_apply, Basis.coord_apply, map_add,
        Finsupp.add_apply, Basis.repr_self,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne hij,Finsupp.single_eq_of_ne hij.symm,
          mul_zero, sub_zero, zero_add, add_zero, zero_mul, mul_one, sub_zero, smul_eq_mul, mul_one]
      simp_rw [Sym2.forall]
      simp only [ne_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, or_self,
        Sym2.lift_mk, linMulLin_apply, not_and_or, not_or, Basis.coord_apply, Basis.repr_self,
        polar, Function.funext_iff, Pi.smul_apply]
      rintro x y ⟨hx | hy, hx | hy⟩ <;> (simp; intros; ring_nf)
      · rw [Finsupp.single_eq_of_ne (Ne.symm hx), zero_mul, mul_zero]
      · rw [Finsupp.single_eq_of_ne (Ne.symm hy), mul_zero, mul_zero]

def __root__.Basis.quadraticForm [Fintype ι] (b : Basis ι R M) : Basis (Sym2 ι) R (QuadraticForm R M) :=
  .ofRepr <|
    .ofLinear
      { toFun := fun Q => ∑ i, Finsupp.single i (aux Q b i)
        map_add' := _
        map_smul' := _ }
      { toFun := fun f =>
          ∑ ij in f.support, f ij • Sym2.lift ⟨fun i j =>
            if i = j then
              (QuadraticForm.sq (R := R)).comp (b.coord i)
            else
              (QuadraticForm.sq (R := R)).comp (b.coord i + b.coord j), sorry⟩ ij
        map_add' := _
        map_smul' := _ }
      (by
        ext
        dsimp
        sorry)
        -- simp [Finsupp.univ_sum_single_apply])
      (by
          simp [aux]
          }

#exit
/-- Given an ordered basis, produce a bilinear form associated with the quadratic form.

Unlike `QuadraticForm.associated`, this is not symmetric; however, as a result it can be used even
in characteristic two. When considered as a matrix, the form is triangular. -/
noncomputable def toBilin (Q : QuadraticForm R M) (bm : Basis ι R M) : LinearMap.BilinForm R M :=
  bm.constr (S := R) fun i =>
    bm.constr (S := R) fun j =>
      if i = j then Q (bm i) else if i < j then polar Q (bm i) (bm j) else 0

theorem toBilin_apply (Q : QuadraticForm R M) (bm : Basis ι R M) (i j : ι) :
    Q.toBilin bm (bm i) (bm j) =
      if i = j then Q (bm i) else if i < j then polar Q (bm i) (bm j) else 0 := by
  simp [toBilin]

theorem toQuadraticForm_toBilin (Q : QuadraticForm R M) (bm : Basis ι R M) :
    (Q.toBilin bm).toQuadraticForm = Q := by
  ext x
  rw [← bm.total_repr x, LinearMap.BilinForm.toQuadraticForm_apply, Finsupp.total_apply,
    Finsupp.sum]
  simp_rw [LinearMap.map_sum₂, map_sum, LinearMap.map_smul₂, _root_.map_smul, toBilin_apply,
    smul_ite, smul_zero, ← Finset.sum_product', ← Finset.diag_union_offDiag,
    Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag, if_true]
  rw [Finset.sum_ite_of_false, QuadraticForm.map_sum, ← Finset.sum_filter]
  · simp_rw [smul_eq_mul, ← polar_smul_right _ (bm.repr x <| Prod.snd _),
      ← polar_smul_left _ (bm.repr x <| Prod.fst _)]
    simp_rw [QuadraticForm.map_smul, ← mul_assoc, Finset.sum_sym2_filter_not_isDiag]
    rfl
  · intro x hx
    rw [Finset.mem_offDiag] at hx
    simpa using hx.2.2

/-- In a free module, every quadratic form can be built from a bilinear form.

See `QuadraticForm.not_forall_toQuadraticForm_surjective` for a counterexample when the module is
not free. -/
theorem toQuadraticForm_surjective [Module.Free R M] :
    Function.Surjective (LinearMap.BilinForm.toQuadraticForm : LinearMap.BilinForm R M → _) := by
  intro Q
  obtain ⟨ι, b⟩ := Module.Free.exists_basis (R := R) (M := M)
  letI : LinearOrder ι := IsWellOrder.linearOrder WellOrderingRel
  exact ⟨_, toQuadraticForm_toBilin _ b⟩

end QuadraticForm
