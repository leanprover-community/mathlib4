/-
Copyright (c) 2025 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.InjectiveProjective

/-!
# Applications of Maschke's theorem

This proves some properties of representations that follow from Maschke's
theorem. In particular, we assume that the group is finite, and we also assume
that the base ring is a field of characteristic zero (or at least a field where
the order of the group is invertible).

In particular, we prove that, if `G` is a finite group whose order is invertible
in a field `k`, then every object of `Rep k G` (resp. `FDRep k G`) is injective and
projective.

We also give two simpleness criteria for an object `V` of `FDRep k G`, when `k` is
an algebraically closed field in which the order of `G` is invertible:
* `FDRep.simple_iff_end_is_rank_one`: `V` is simple if and only `V ⟶ V` is a `k`-vector
space of dimension `1`.
* `FDRep.simple_iff_char_is_norm_one`: when `k` is characteristic zero, `V` is simple
if and only if `∑ g : G, V.character g * V.character g⁻¹ = Fintype.card G`.

-/

universe u

variable {k : Type u} [Field k] {G : Type u} [Fintype G] [Group G]

open CategoryTheory Limits

namespace Rep

variable [NeZero (Fintype.card G : k)]

/--
If `G` is finite and its order is nonzero in the field `k`, then every object of
`Rep k G` is injective.
-/
instance (V : Rep k G) : Injective V := by
  rw [← Rep.equivalenceModuleMonoidAlgebra.map_injective_iff,
    ← Module.injective_iff_injective_object]
  exact Module.injective_of_semisimple_ring _ _

/--
If `G` is finite and its order is nonzero in the field `k`, then every object of
`Rep k G` is projective.
-/
-- Will this clash with the previously defined `Projective` instances?
instance (V : Rep k G) : Projective V := by
  rw [← Rep.equivalenceModuleMonoidAlgebra.map_projective_iff,
    ← IsProjective.iff_projective]
  exact Module.projective_of_semisimple_ring _ _

end Rep

namespace FDRep

variable [NeZero (Fintype.card G : k)]

/--
If `G` is finite and its order is nonzero in the field `k`, then every object of
`FDRep k G` is injective.
-/
instance (V : FDRep k G) : Injective V := (forget₂ (FDRep k G)
  (Rep k G)).injective_of_map_injective _ inferInstance

/--
If `G` is finite and its order is nonzero in the field `k`, then every object of
`FDRep k G` is projective.
-/
instance (V : FDRep k G) : Projective V := (forget₂ (FDRep k G)
  (Rep k G)).projective_of_map_projective _ inferInstance

variable [IsAlgClosed k]

/--
If `G` is finite and its order is nonzero in an algebraically closed field `k`,
then an object of `FDRep k G` is simple if and only if its space of endomorphisms is
a `k`-vector space of dimension `1`.
-/
lemma simple_iff_end_is_rank_one (V : FDRep k G) :
    Simple V ↔ Module.finrank k (V ⟶ V) = 1 where
  mp h := by
    rw [finrank_hom_simple_simple_eq_one_iff]
    exact Nonempty.intro (Iso.refl _)
  mpr h := by
    refine {mono_isIso_iff_nonzero f _ := ⟨fun hf habs ↦ ?_, fun hf ↦ ?_⟩}
    · rw [habs] at hf
      obtain ⟨g, hg⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := k) (M := V ⟶ V)).mp
        (by rw [h]; exact zero_lt_one)
      exact hg (Limits.IsZero.eq_zero_of_src (IsZero.of_iso (isZero_zero _)
        ((isIsoZeroEquivIsoZero _ _).toFun hf).2) g)
    · have : Epi f := by
        have : Epi (Abelian.image.ι f) := by
          have h₁ := Injective.comp_factorThru (𝟙 _) (Abelian.image.ι f)
          have h₂ : Injective.factorThru (𝟙 _) (Abelian.image.ι f) ≫ Abelian.image.ι f ≠ 0 := by
            intro habs
            apply_fun (fun x ↦ x ≫ Abelian.image.ι f) at h₁
            rw [Category.id_comp, Category.assoc, habs, Limits.comp_zero] at h₁
            rw [← Abelian.image.fac f, ← h₁, Limits.comp_zero] at hf
            exact hf (Eq.refl _)
          obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ h₂).mp h (𝟙 V)
          refine Preadditive.epi_of_cancel_zero _ (fun g hg ↦ ?_)
          apply_fun (fun x ↦ x ≫ g) at hc
          simp only [equalizer_as_kernel, Linear.smul_comp, Category.assoc, hg, Limits.comp_zero,
            smul_zero, Category.id_comp] at hc
          exact hc.symm
        rw [← Abelian.image.fac f]
        exact epi_comp _ _
      exact isIso_of_mono_of_epi f

lemma simple_iff_char_is_norm_one [CharZero k] (V : FDRep k G) :
    Simple V ↔ ∑ g : G, V.character g * V.character g⁻¹ = Fintype.card G where
  mp h := by
    have := invertibleOfNonzero (NeZero.ne (Fintype.card G : k))
    have := char_orthonormal V V
    simp only [Nonempty.intro (Iso.refl V), ↓reduceIte] at this
    apply_fun (fun x ↦ x * (Fintype.card G : k)) at this
    rw [mul_comm, ← smul_eq_mul, smul_smul, mul_invOf_self] at this
    simp only [smul_eq_mul, one_mul] at this
    exact this
  mpr h := by
    have := invertibleOfNonzero (NeZero.ne (Fintype.card G : k))
    have eq := FDRep.scalar_product_char_eq_finrank_equivariant V V
    rw [h] at eq
    simp only [invOf_eq_inv, smul_eq_mul, inv_mul_cancel_of_invertible] at eq
    rw [simple_iff_end_is_rank_one, ← Nat.cast_inj (R := k), ← eq, Nat.cast_one]

end FDRep
