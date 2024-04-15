/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.TypesFiltered
import Mathlib.CategoryTheory.Limits.Final

/-!
# Final functors with filtered (co)domain

If `C` is a filtered category, then the usual equivalent conditions for a functor `F : C ⥤ D` to be
final can be restated. We show:

* `final_iff_of_isFiltered`: a concrete description of finality which is sometimes a convenient way
  to show that a functor is final.
* `final_iff_isFiltered_structuredArrow`: `F` is final if and only if `StructuredArrow d F` is
  filtered for all `d : D`, which strengthens the usual statement that `F` is final if and only
  if `StructuredArrow d F` is connected for all `d : D`.

Additionally, we show that if `D` is a filtered category and `F : C ⥤ D` is fully faithful and
satisfies the additional condition that for every `d : D` there is an object `c : D` and a morphism
`d ⟶ F.obj c`, then `C` is filtered and `F` is final.

## References

* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Section 3.2

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open CategoryTheory.Limits CategoryTheory.Functor Opposite

section ArbitraryUniverses

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

/-- If `StructuredArrow d F` is filtered for any `d : D`, then `F : C ⥤ D` is final. This is
    simply because filtered categories are connected. More profoundly, the converse is also true if
    `C` is filtered, see `final_iff_isFiltered_structuredArrow`. -/
theorem Functor.final_of_isFiltered_structuredArrow [∀ d, IsFiltered (StructuredArrow d F)] :
    Final F where
  out _ := IsFiltered.isConnected _

/-- If `CostructuredArrow F d` is filtered for any `d : D`, then `F : C ⥤ D` is initial. This is
    simply because cofiltered categories are connectged. More profoundly, the converse is also true
    if `C` is cofiltered, see `initial_iff_isCofiltered_costructuredArrow`. -/
theorem Functor.initial_of_isCofiltered_costructuredArrow
    [∀ d, IsCofiltered (CostructuredArrow F d)] : Initial F where
  out _ := IsCofiltered.isConnected _

theorem isFiltered_structuredArrow_of_isFiltered_of_exists [IsFilteredOrEmpty C]
    (h₁ : ∀ d, ∃ c, Nonempty (d ⟶ F.obj c)) (h₂ : ∀ {d : D} {c : C} (s s' : d ⟶ F.obj c),
      ∃ (c' : C) (t : c ⟶ c'), s ≫ F.map t = s' ≫ F.map t) (d : D) :
    IsFiltered (StructuredArrow d F) := by
  have : Nonempty (StructuredArrow d F) := by
    obtain ⟨c, ⟨f⟩⟩ := h₁ d
    exact ⟨.mk f⟩
  suffices IsFilteredOrEmpty (StructuredArrow d F) from IsFiltered.mk
  refine ⟨fun f g => ?_, fun f g η μ => ?_⟩
  · obtain ⟨c, ⟨t, ht⟩⟩ := h₂ (f.hom ≫ F.map (IsFiltered.leftToMax f.right g.right))
        (g.hom ≫ F.map (IsFiltered.rightToMax f.right g.right))
    refine ⟨.mk (f.hom ≫ F.map (IsFiltered.leftToMax f.right g.right ≫ t)), ?_, ?_, trivial⟩
    · exact StructuredArrow.homMk (IsFiltered.leftToMax _ _ ≫ t) rfl
    · exact StructuredArrow.homMk (IsFiltered.rightToMax _ _ ≫ t) (by simpa using ht.symm)
  · refine ⟨.mk (f.hom ≫ F.map (η.right ≫ IsFiltered.coeqHom η.right μ.right)),
      StructuredArrow.homMk (IsFiltered.coeqHom η.right μ.right) (by simp), ?_⟩
    simpa using IsFiltered.coeq_condition _ _

theorem isCofiltered_costructuredArrow_of_isCofiltered_of_exists [IsCofilteredOrEmpty C]
    (h₁ : ∀ d, ∃ c, Nonempty (F.obj c ⟶ d)) (h₂ : ∀ {d : D} {c : C} (s s' : F.obj c ⟶ d),
      ∃ (c' : C) (t : c' ⟶ c), F.map t ≫ s = F.map t ≫ s') (d : D) :
    IsCofiltered (CostructuredArrow F d) := by
  suffices IsFiltered (CostructuredArrow F d)ᵒᵖ from isCofiltered_of_isFiltered_op _
  suffices IsFiltered (StructuredArrow (op d) F.op) from
    IsFiltered.of_equivalence (costructuredArrowOpEquivalence _ _).symm
  apply isFiltered_structuredArrow_of_isFiltered_of_exists
  · intro d
    obtain ⟨c, ⟨t⟩⟩ := h₁ d.unop
    exact ⟨op c, ⟨Quiver.Hom.op t⟩⟩
  · intro d c s s'
    obtain ⟨c', t, ht⟩ := h₂ s.unop s'.unop
    exact ⟨op c', Quiver.Hom.op t, Quiver.Hom.unop_inj ht⟩

/-- If `C` is filtered, then we can give an explicit condition for a functor `F : C ⥤ D` to
    be final. The converse is also true, see `final_iff_of_isFiltered`. -/
theorem Functor.final_of_exists_of_isFiltered [IsFilteredOrEmpty C]
    (h₁ : ∀ d, ∃ c, Nonempty (d ⟶ F.obj c)) (h₂ : ∀ {d : D} {c : C} (s s' : d ⟶ F.obj c),
      ∃ (c' : C) (t : c ⟶ c'), s ≫ F.map t = s' ≫ F.map t) : Functor.Final F := by
  suffices ∀ d, IsFiltered (StructuredArrow d F) from final_of_isFiltered_structuredArrow F
  exact isFiltered_structuredArrow_of_isFiltered_of_exists F h₁ h₂

/-- If `C` is cofiltered, then we can give an explicit condition for a functor `F : C ⥤ D` to
    be final. The converse is also true, see `initial_iff_of_isCofiltered`. -/
theorem Functor.initial_of_exists_of_isCofiltered [IsCofilteredOrEmpty C]
    (h₁ : ∀ d, ∃ c, Nonempty (F.obj c ⟶ d)) (h₂ : ∀ {d : D} {c : C} (s s' : F.obj c ⟶ d),
      ∃ (c' : C) (t : c' ⟶ c), F.map t ≫ s = F.map t ≫ s') : Functor.Initial F := by
  suffices ∀ d, IsCofiltered (CostructuredArrow F d) from
    initial_of_isCofiltered_costructuredArrow F
  exact isCofiltered_costructuredArrow_of_isCofiltered_of_exists F h₁ h₂

/-- In this situation, `F` is also final, see
    `Functor.final_of_exists_of_isFiltered_of_fullyFaithful`. -/
theorem IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful [IsFilteredOrEmpty D] [F.Full]
    [F.Faithful] (h : ∀ d, ∃ c, Nonempty (d ⟶ F.obj c)) : IsFilteredOrEmpty C where
  cocone_objs c c' := by
    obtain ⟨c₀, ⟨f⟩⟩ := h (IsFiltered.max (F.obj c) (F.obj c'))
    exact ⟨c₀, F.preimage (IsFiltered.leftToMax _ _ ≫ f),
      F.preimage (IsFiltered.rightToMax _ _ ≫ f), trivial⟩
  cocone_maps {c c'} f g := by
    obtain ⟨c₀, ⟨f₀⟩⟩ := h (IsFiltered.coeq (F.map f) (F.map g))
    refine ⟨_, F.preimage (IsFiltered.coeqHom (F.map f) (F.map g) ≫ f₀), F.map_injective ?_⟩
    simp [reassoc_of% (IsFiltered.coeq_condition (F.map f) (F.map g))]

/-- In this situation, `F` is also initial, see
    `Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful`. -/
theorem IsCofilteredOrEmpty.of_exists_of_isCofiltered_of_fullyFaithful [IsCofilteredOrEmpty D]
    [F.Full] [F.Faithful] (h : ∀ d, ∃ c, Nonempty (F.obj c ⟶ d)) : IsCofilteredOrEmpty C := by
  suffices IsFilteredOrEmpty Cᵒᵖ from isCofilteredOrEmpty_of_isFilteredOrEmpty_op _
  refine IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful F.op (fun d => ?_)
  obtain ⟨c, ⟨f⟩⟩ := h d.unop
  exact ⟨op c, ⟨f.op⟩⟩

/-- In this situation, `F` is also final, see
    `Functor.final_of_exists_of_isFiltered_of_fullyFaithful`. -/
theorem IsFiltered.of_exists_of_isFiltered_of_fullyFaithful [IsFiltered D] [F.Full] [F.Faithful]
    (h : ∀ d, ∃ c, Nonempty (d ⟶ F.obj c)) : IsFiltered C :=
  { IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful F h with
    nonempty := by
      have : Nonempty D := IsFiltered.nonempty
      obtain ⟨c, -⟩ := h (Classical.arbitrary D)
      exact ⟨c⟩ }

/-- In this situation, `F` is also initial, see
    `Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful`. -/
theorem IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful [IsCofiltered D] [F.Full]
    [F.Faithful] (h : ∀ d, ∃ c, Nonempty (F.obj c ⟶ d)) : IsCofiltered C :=
  { IsCofilteredOrEmpty.of_exists_of_isCofiltered_of_fullyFaithful F h with
    nonempty := by
      have : Nonempty D := IsCofiltered.nonempty
      obtain ⟨c, -⟩ := h (Classical.arbitrary D)
      exact ⟨c⟩ }

/-- In this situation, `C` is also filtered, see
    `IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful`. -/
theorem Functor.final_of_exists_of_isFiltered_of_fullyFaithful [IsFilteredOrEmpty D] [F.Full]
    [F.Faithful] (h : ∀ d, ∃ c, Nonempty (d ⟶ F.obj c)) : Final F := by
  have := IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful F h
  refine Functor.final_of_exists_of_isFiltered F h (fun {d c} s s' => ?_)
  obtain ⟨c₀, ⟨f⟩⟩ := h (IsFiltered.coeq s s')
  refine ⟨c₀, F.preimage (IsFiltered.coeqHom s s' ≫ f), ?_⟩
  simp [reassoc_of% (IsFiltered.coeq_condition s s')]

/-- In this situation, `C` is also cofiltered, see
    `IsCofilteredOrEmpty.of_exists_of_isCofiltered_of_fullyFaithful`. -/
theorem Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful [IsCofilteredOrEmpty D] [F.Full]
    [Faithful F] (h : ∀ d, ∃ c, Nonempty (F.obj c ⟶ d)) : Initial F := by
  suffices Final F.op from initial_of_final_op _
  refine Functor.final_of_exists_of_isFiltered_of_fullyFaithful F.op (fun d => ?_)
  obtain ⟨c, ⟨f⟩⟩ := h d.unop
  exact ⟨op c, ⟨f.op⟩⟩

end ArbitraryUniverses

section LocallySmall

variable {C : Type v₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D] (F : C ⥤ D)

/-- If `C` is filtered, then we can give an explicit condition for a functor `F : C ⥤ D` to
    be final. -/
theorem Functor.final_iff_of_isFiltered [IsFilteredOrEmpty C] :
    Final F ↔ (∀ d, ∃ c, Nonempty (d ⟶ F.obj c)) ∧ (∀ {d : D} {c : C} (s s' : d ⟶ F.obj c),
      ∃ (c' : C) (t : c ⟶ c'), s ≫ F.map t = s' ≫ F.map t) := by
  refine ⟨fun hF => ⟨?_, ?_⟩, fun h => final_of_exists_of_isFiltered F h.1 h.2⟩
  · intro d
    obtain ⟨f⟩ : Nonempty (StructuredArrow d F) := IsConnected.is_nonempty
    exact ⟨_, ⟨f.hom⟩⟩
  · intro d c s s'
    have : colimit.ι (F ⋙ coyoneda.obj (op d)) c s = colimit.ι (F ⋙ coyoneda.obj (op d)) c s' := by
      apply (Final.colimitCompCoyonedaIso F d).toEquiv.injective
      exact Subsingleton.elim _ _
    obtain ⟨c', t₁, t₂, h⟩ := (Types.FilteredColimit.colimit_eq_iff.{v₁, v₁, v₁} _).mp this
    refine ⟨IsFiltered.coeq t₁ t₂, t₁ ≫ IsFiltered.coeqHom t₁ t₂, ?_⟩
    conv_rhs => rw [IsFiltered.coeq_condition t₁ t₂]
    dsimp only [comp_obj, coyoneda_obj_obj, unop_op, Functor.comp_map, coyoneda_obj_map] at h
    simp [reassoc_of% h]

/-- If `C` is cofiltered, then we can give an explicit condition for a functor `F : C ⥤ D` to
    be initial. -/
theorem Functor.initial_iff_of_isCofiltered [IsCofilteredOrEmpty C] :
    Initial F ↔ (∀ d, ∃ c, Nonempty (F.obj c ⟶ d)) ∧ (∀ {d : D} {c : C} (s s' : F.obj c ⟶ d),
      ∃ (c' : C) (t : c' ⟶ c), F.map t ≫ s = F.map t ≫ s') := by
  refine ⟨fun hF => ?_, fun h => initial_of_exists_of_isCofiltered F h.1 h.2⟩
  obtain ⟨h₁, h₂⟩ := F.op.final_iff_of_isFiltered.mp inferInstance
  refine ⟨?_, ?_⟩
  · intro d
    obtain ⟨c, ⟨t⟩⟩ := h₁ (op d)
    exact ⟨c.unop, ⟨t.unop⟩⟩
  · intro d c s s'
    obtain ⟨c', t, ht⟩ := h₂ (Quiver.Hom.op s) (Quiver.Hom.op s')
    exact ⟨c'.unop, t.unop, Quiver.Hom.op_inj ht⟩

theorem Functor.Final.exists_coeq [IsFilteredOrEmpty C] [Final F] {d : D} {c : C}
    (s s' : d ⟶ F.obj c) : ∃ (c' : C) (t : c ⟶ c'), s ≫ F.map t = s' ≫ F.map t :=
  ((final_iff_of_isFiltered F).1 inferInstance).2 s s'

theorem Functor.Initial.exists_eq [IsCofilteredOrEmpty C] [Initial F] {d : D} {c : C}
    (s s' : F.obj c ⟶ d) : ∃ (c' : C) (t : c' ⟶ c), F.map t ≫ s = F.map t ≫ s' :=
  ((initial_iff_of_isCofiltered F).1 inferInstance).2 s s'

/-- If `C` is filtered, then `F : C ⥤ D` is final if and only if `StructuredArrow d F` is filtered
    for all `d : D`. -/
theorem Functor.final_iff_isFiltered_structuredArrow [IsFilteredOrEmpty C] :
    Final F ↔ ∀ d, IsFiltered (StructuredArrow d F) := by
  refine ⟨?_, fun h => final_of_isFiltered_structuredArrow F⟩
  rw [final_iff_of_isFiltered]
  exact fun h => isFiltered_structuredArrow_of_isFiltered_of_exists F h.1 h.2

/-- If `C` is cofiltered, then `F : C ⥤ D` is initial if and only if `CostructuredArrow F d` is
    cofiltered for all `d : D`. -/
theorem Functor.initial_iff_isCofiltered_costructuredArrow [IsCofilteredOrEmpty C] :
    Initial F ↔ ∀ d, IsCofiltered (CostructuredArrow F d) := by
  refine ⟨?_, fun h => initial_of_isCofiltered_costructuredArrow F⟩
  rw [initial_iff_of_isCofiltered]
  exact fun h => isCofiltered_costructuredArrow_of_isCofiltered_of_exists F h.1 h.2

end LocallySmall

end CategoryTheory
