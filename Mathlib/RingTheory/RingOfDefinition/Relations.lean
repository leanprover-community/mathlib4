/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.RingTheory.RingOfDefinition.Basic

/-!

# Relations in models

-/

namespace Algebra

variable {R : Type*} [CommRing R]

namespace RingOfDefinition

section

variable (A : Set R)

def Relation : Type _ := MvPolynomial A R

noncomputable instance : CommRing (Relation A) :=
  inferInstanceAs <| CommRing <| MvPolynomial A R

variable {A}

def Relation.eval : Relation A →+* R :=
  MvPolynomial.eval Subtype.val

def Relation.IsHomogeneous (r : Relation A) (n : ℕ) : Prop :=
  MvPolynomial.IsHomogeneous r n

theorem Relation.IsHomogeneous_iff (r : Relation A) (n : ℕ) :
    r.IsHomogeneous n ↔ MvPolynomial.IsHomogeneous r n := by
  rfl

variable {S : Type*} [CommRing S]
variable {f : R →+* S} {A : Set R} {B : Set S}

noncomputable def Relation.map (h : Set.MapsTo f A B) : Relation A →+* Relation B :=
  RingHom.comp (MvPolynomial.rename h.restrict).toRingHom (MvPolynomial.map f)

@[simp]
lemma Relation.map_apply (h : Set.MapsTo f A B) (p : Relation A) :
    Relation.map h p = MvPolynomial.rename h.restrict (MvPolynomial.map f p) :=
  rfl

lemma Relation.isHomogeneous_of_map (h : Set.MapsTo f A B) (hinj : Function.Injective f)
    (r : Relation A) {n : ℕ} (homog : Relation.IsHomogeneous (Relation.map h r) n) :
    r.IsHomogeneous n := by
  simp only [map_apply] at homog
  have h1 : Function.Injective h.restrict := by
    rw [Set.MapsTo.restrict_inj]
    apply Set.injOn_of_injective hinj
  rw [Relation.IsHomogeneous_iff, MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff h1] at homog
  apply MvPolynomial.IsHomogeneous.of_map f hinj
  exact homog

variable (hf : Set.MapsTo f A B)

lemma diag_rename_comm :
    f.comp (MvPolynomial.eval Subtype.val)
    = (MvPolynomial.eval Subtype.val).comp
      ((MvPolynomial.map f).comp (MvPolynomial.rename hf.restrict).toRingHom) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro a
    simp

lemma diag_rename_comm_apply (p : MvPolynomial A R) :
    f ((MvPolynomial.eval Subtype.val) p) =
      (MvPolynomial.eval Subtype.val) ((MvPolynomial.map f) (MvPolynomial.rename hf.restrict p)) := by
  change (f.comp (MvPolynomial.eval Subtype.val)) p
    = ((MvPolynomial.eval Subtype.val).comp
      ((MvPolynomial.map f).comp (MvPolynomial.rename hf.restrict).toRingHom)) p
  rw [diag_rename_comm]

end

section

variable {σ : Type*} {s : Set (MvPolynomial σ R)}

def Relation.coefficients (r : Relation s) : Set R :=
  (MvPolynomial.coefficients r).coefficients

def Relation.Set.coefficients (rs : Set (Relation s)) : Set R :=
  rs.coefficients.coefficients

class HasRelations (rs : Set (Relation s)) (R₀ : Subring R) : Prop where
  has_coeffs : Relation.Set.coefficients rs ⊆ R₀

class HasRelation (r : Relation s) (R₀ : Subring R) : Prop where
  has_coeffs : r.coefficients ⊆ R₀

theorem hasRelation_of_hasRelations (rs : Set (Relation s)) (r : Relation s) (hr : r ∈ rs)
    (R₀ : Subring R) [HasRelations rs R₀] :
    HasRelation r R₀ :=
  sorry

def adjoinRelations (rs : Set (Relation s)) (R₀ : Subring R) : Subring R :=
  (Algebra.adjoin R₀ (Relation.Set.coefficients rs)).toSubring

instance (rs : Set (Relation s)) (R₀ : Subring R) : HasRelations rs (adjoinRelations rs R₀) where
  has_coeffs := Algebra.subset_adjoin

instance (rs₁ rs₂ : Set (Relation s)) (R₀ : Subring R) [HasRelations rs₁ R₀] :
    HasRelations rs₁ (adjoinRelations rs₂ R₀) where
  has_coeffs := sorry

instance (t : Set (MvPolynomial σ R)) (rs : Set (Relation s)) (R₀ : Subring R)
    [HasCoefficients t R₀] : HasCoefficients t (adjoinRelations rs R₀) where
  has_coeffs := sorry

end

namespace Model

variable {σ : Type*} {I : Ideal (MvPolynomial σ R)} (M : Model I)

theorem mapsTo : Set.MapsTo (MvPolynomial.map (M.R₀.subtype)) M.s₀ M.s :=
  Set.mapsTo_preimage (MvPolynomial.map M.R₀.subtype) M.s

theorem mapsTo_restrict_injective : Function.Injective M.mapsTo.restrict := by
  rw [Set.MapsTo.restrict_inj]
  apply Set.injOn_of_injective
  apply MvPolynomial.map_injective
  exact Subtype.val_injective

theorem mapsTo_restrict_surjective : Function.Surjective M.mapsTo.restrict := by
  intro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := MvPolynomial.mem_range_of_coefficients' x (M.coefficients_subset x hx)
  refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
  · show MvPolynomial.map M.R₀.subtype y ∈ M.s
    rw [hy]
    exact hx

noncomputable def definingSetEquiv : M.s₀ ≃ M.s :=
  Equiv.ofBijective M.mapsTo.restrict ⟨M.mapsTo_restrict_injective, M.mapsTo_restrict_surjective⟩

theorem Relation.exists_repr (r : Relation M.s) [RingOfDefinition.HasRelation r M.R₀] :
    ∃ (t : Relation M.s₀), Relation.map M.mapsTo t = r := by
  have hc : MvPolynomial.coefficients r ⊆ Set.range (MvPolynomial.map M.R₀.subtype) := by
    intro p hp
    have hc : MvPolynomial.coefficients p ⊆ M.R₀ :=
      Set.Subset.trans (Set.coefficients_subset_coefficients _ _ hp)
        RingOfDefinition.HasRelation.has_coeffs
    obtain ⟨p₀, hp₀⟩ := MvPolynomial.mem_range_of_coefficients' p hc
    use p₀
  obtain ⟨t', ht'⟩ := MvPolynomial.mem_range_of_coefficients r hc
  use (MvPolynomial.rename M.definingSetEquiv.symm t')
  simp only [Relation.map_apply, MvPolynomial.map_rename, MvPolynomial.rename_rename]
  change MvPolynomial.rename (M.definingSetEquiv ∘ M.definingSetEquiv.symm) _ = _
  simpa

noncomputable def Relation.repr (r : Relation M.s) [RingOfDefinition.HasRelation r M.R₀] :
    Relation M.s₀ :=
  (Model.Relation.exists_repr M r).choose

theorem Relation.repr_map (r : Relation M.s) [RingOfDefinition.HasRelation r M.R₀] :
    Relation.map M.mapsTo (Model.Relation.repr M r) = r :=
  (Model.Relation.exists_repr M r).choose_spec

theorem Relation.repr_homogeneous (r : Relation M.s) [RingOfDefinition.HasRelation r M.R₀] {n : ℕ}
    (homog : r.IsHomogeneous n) : (Relation.repr M r).IsHomogeneous n := by
  apply Relation.isHomogeneous_of_map M.mapsTo
  · apply MvPolynomial.map_injective (SubringClass.subtype M.R₀) Subtype.val_injective
  · rwa [Relation.repr_map]

end Model

end RingOfDefinition

end Algebra
