/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.CoverPreserving

/-!
# Induced topologies

In this file we study various topologies induced by a functor. Let `F : C ⥤ D` be a functor,
`J` a Grothendieck topology on `C` and `K` a Grothendieck topology on `D`.

- `CategoryTheory.Functor.inducedTopology F K`: The finest topology on `C` making `F` continuous.
- `CategoryTheory.Functor.restrictedTopology F K`: The coarsest topology on `C` containing
  all sieves whose image generate a covering sieve of `K`. In general, this does not make `F` cover
  preserving.

## TODOs

- Define the finest topology on the codomain making a functor cocontinuous
  (@chrisflav).

## References

- [SGA4, III, 3][sga-4-tome-1]
-/

@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

variable {F : C ⥤ D} {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace Functor

/--
The induced topology by a topology on `D` along a functor `F : C ⥤ D` is the finest
topology on `C` making `F` continuous.
[SGA4, III, 3.1][sga-4-tome-1]
-/
def inducedTopology (F : C ⥤ D) (K : GrothendieckTopology D) :
    GrothendieckTopology C :=
  Sheaf.finestTopology <| Set.range fun G : Sheaf K (Type max u₁ v₁ u₂ v₂) ↦ F.op ⋙ G.obj

instance : F.IsContinuous (F.inducedTopology K) K where
  op_comp_isSheaf_of_types G := by
    apply Sheaf.sheaf_for_finestTopology
    use G

@[simp]
lemma le_inducedTopology_iff {J : GrothendieckTopology C} :
    J ≤ F.inducedTopology K ↔ F.IsContinuous J K := by
  refine ⟨fun h ↦ ⟨fun G ↦ ?_⟩, fun h ↦ ?_⟩
  · apply Presieve.isSheaf_of_le _ h
    exact Functor.op_comp_isSheaf_of_types F (F.inducedTopology K) K G
  · apply Sheaf.le_finestTopology
    rintro _ ⟨P, rfl⟩
    exact Functor.op_comp_isSheaf_of_types F J K P

/-- [SGA4, III, Proposition 3.2][sga-4-tome-1] -/
lemma mem_inducedTopology_iff [LocallySmall.{max u₁ v₁ u₂ v₂} C] (X : C) (S : Sieve X)
    (G : (Cᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂) ⥤ (Dᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂))
    (adj : G ⊣ (Functor.whiskeringLeft _ _ _).obj F.op) :
    S ∈ F.inducedTopology K X ↔
      ∀ ⦃Y : C⦄ (f : Y ⟶ X),
        K.W (G.map (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} (S.pullback f)).ι) := by
  refine ⟨?_, ?_⟩
  · intro hS Y f
    apply Functor.W_map_of_adjunction_of_isContinuous (F.inducedTopology K) K _ G adj
    refine Sieve.W_shrinkFunctor_ι_of_mem (F.inducedTopology K) (Sieve.pullback f S) ?_
    exact GrothendieckTopology.pullback_stable (F.inducedTopology K) f hS
  · intro H
    apply Sheaf.mem_finestTopology_of_forall_isSheafFor
    rintro - ⟨P, rfl⟩ Y f
    dsimp
    rw [Presieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp]
    exact (adj.map_comp_bijective_iff _ _).mp (H f _ P.property)

lemma induced_induced_le (G : D ⥤ E) (J : GrothendieckTopology E) :
    F.inducedTopology (G.inducedTopology J) ≤ (F ⋙ G).inducedTopology J := by
  rw [le_inducedTopology_iff]
  exact Functor.isContinuous_comp _ _ _ (G.inducedTopology J) _

lemma inducedTopology_eq_of_iso {F G : C ⥤ D} (e : F ≅ G) :
    F.inducedTopology K = G.inducedTopology K := by
  refine le_antisymm ?_ ?_ <;> rw [le_inducedTopology_iff]
  · apply Functor.isContinuous_of_iso e
  · apply Functor.isContinuous_of_iso e.symm

/-- The coarsest topology containing all sieves whose image under `F` generates a covering sieve
of `K`. -/
def restrictedTopology (F : C ⥤ D) (K : GrothendieckTopology D) : GrothendieckTopology C :=
  Precoverage.toGrothendieck (Precoverage.comap F K.toPrecoverage)

lemma mem_restrictedTopology_of_functorPushforward_mem {X : C} {S : Sieve X}
    (hS : S.functorPushforward F ∈ K _) :
    S ∈ F.restrictedTopology K X := by
  rw [← Sieve.generate_sieve S]
  apply Precoverage.generate_mem_toGrothendieck
  simpa [GrothendieckTopology.mem_toPrecoverage_iff, Sieve.generate_map_eq_functorPushforward]

lemma inducedTopology_le_restrictedTopology : F.inducedTopology K ≤ F.restrictedTopology K :=
  fun _ _ hS ↦ mem_restrictedTopology_of_functorPushforward_mem <|
    (CoverPreserving.of_isContinuous F _ _).cover_preserve hS

/--
If `F` is continuous with the restricted topology, the restricted topology agrees with the
induced topology. This holds for example if `G` is locally faithful, locally full and cover dense.
-/
lemma restrictedTopology_eq_inducedTopology [F.IsContinuous (F.restrictedTopology K) K] :
    F.restrictedTopology K = F.inducedTopology K := by
  refine le_antisymm ?_ inducedTopology_le_restrictedTopology
  rw [le_inducedTopology_iff]
  infer_instance

/-- Variant of `Functor.restrictedTopology_eq_inducedTopology` that is sometimes easier to use. -/
lemma restrictedTopology_eq_inducedTopology_of_isContinuous [F.IsContinuous J K]
    (h : F.restrictedTopology K = J) : F.inducedTopology K = J := by
  subst h
  rw [restrictedTopology_eq_inducedTopology]

end Functor

lemma Precoverage.toGrothendieck_comap_le_restrictedTopology (K : Precoverage D) :
    (K.comap F).toGrothendieck ≤ F.restrictedTopology K.toGrothendieck := by
  rw [Functor.restrictedTopology]
  grw [← K.le_toPrecoverage_toGrothendieck]

end CategoryTheory
