/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexOp

/-!
# The type of nondegenerate simplices not in a subcomplex

In this file, given a subcomplex `A` of a simplicial set `X`,
we introduce the type `A.N` of nondegenerate simplices of `X`
that are not in `A`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet.Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

/-- The type of nondegenerate simplices which do not belong to
a given subcomplex of a simplicial set. -/
structure N extends X.N where mk' ::
  notMem : simplex ∉ A.obj _

namespace N

variable {A}

lemma mk'_surjective (s : A.N) :
    ∃ (t : X.N) (ht : t.simplex ∉ A.obj _), s = mk' t ht :=
  ⟨s.toN, s.notMem, rfl⟩

/-- Constructor for the type of nondegenerate simplices which
do not belong to a given subcomplex of a simplicial set. -/
@[simps!]
def mk {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n)
    (hx' : x ∉ A.obj _) : A.N where
  simplex := x
  nonDegenerate := hx
  notMem := hx'

lemma mk_surjective (s : A.N) :
    ∃ (n : ℕ) (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n)
      (hx' : x ∉ A.obj _), s = mk x hx hx' :=
  ⟨s.dim, s.simplex, s.nonDegenerate, s.notMem, rfl⟩

lemma ext_iff (x y : A.N) :
    x = y ↔ x.toN = y.toN := by
  grind [cases SSet.Subcomplex.N]

variable (A) in
@[elab_as_elim]
lemma cases {motive : X.N → Prop}
    (mem : ∀ (s : X.N), s.subcomplex ≤ A → motive s)
    (notMem : ∀ (s : A.N), motive s.toN)
    (s : X.N) :
    motive s := by
  by_cases hs : s.subcomplex ≤ A
  · exact mem s hs
  · exact notMem (.mk' s (by simpa using hs))

lemma eq_iff_sMk_eq {X : SSet.{u}} {A : X.Subcomplex} (x y : A.N) :
    x = y ↔ S.mk x.simplex = S.mk y.simplex := by
  rw [N.ext_iff, SSet.N.ext_iff]

instance : PartialOrder A.N :=
  PartialOrder.lift toN (fun _ _ ↦ by simp [ext_iff])

lemma le_iff {x y : A.N} : x ≤ y ↔ x.toN ≤ y.toN :=
  Iff.rfl

lemma lt_iff {x y : A.N} : x < y ↔ x.toN < y.toN :=
  Iff.rfl

section

variable (s : A.N) {d : ℕ} (hd : s.dim = d)

/-- When `A` is a subcomplex of a simplicial set `X`,
and `s : A.N` is such that `s.dim = d`, this is a term
that is equal to `s`, but whose dimension if definitionally equal to `d`. -/
abbrev cast : A.N where
  toN := s.toN.cast hd
  notMem := hd ▸ s.notMem

lemma cast_eq_self : s.cast hd = s := by
  subst hd
  rfl

end

/-- The bijection `A.op.N ≃ A.N` for a subcomplex `A` of a simplicial set.. -/
@[simps -isSimp apply symm_apply]
def opEquiv : A.op.N ≃o A.N where
  toFun x := N.mk' (SSet.N.opEquiv x.toN) x.notMem
  invFun y := N.mk' (SSet.N.opEquiv.symm y.toN) y.notMem
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := SSet.N.opEquiv.map_rel_iff

/-- The bijection `A.N ≃ B.N` on nondegenerate simplices not belonging
to a certain subcomplex that is induced by an isomorphism `X ≅ Y` of
simplicial sets which maps `A : X.Subcomplex` to `B : Y.Subcomplex`. -/
@[simps -isSimp apply symm_apply]
def orderIsoOfIso {Y : SSet.{u}} {B : Y.Subcomplex} (e : X ≅ Y)
    (hA : B.preimage e.hom = A) : A.N ≃o B.N where
  toFun x := N.mk' (SSet.N.orderIsoOfIso e x.toN) (by subst hA; exact x.notMem)
  invFun y := N.mk' ((SSet.N.orderIsoOfIso e).symm y.toN) (by
    obtain rfl : A.preimage e.inv = B := by aesop
    exact y.notMem)
  left_inv _ := by aesop
  right_inv _ := by aesop
  map_rel_iff' {_ _} := (SSet.N.orderIsoOfIso e).map_rel_iff'

end N

lemma existsN {X : SSet.{u}} {n : ℕ} (s : X _⦋n⦌) {A : X.Subcomplex}
    (hs : s ∉ A.obj _) :
    ∃ (x : A.N) (f : ⦋n⦌ ⟶ ⦋x.dim⦌), Epi f ∧ X.map f.op x.simplex = s := by
  refine ⟨⟨(S.mk s).toN, fun h ↦ hs ?_⟩, ⟨(S.mk s).toNπ, inferInstance, S.map_toNπ_op_apply _⟩⟩
  simp only [← ofSimplex_le_iff] at h ⊢
  simpa using h

end SSet.Subcomplex
