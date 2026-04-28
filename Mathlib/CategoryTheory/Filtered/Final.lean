/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.Final.Connected
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.Sifted

/-!
# Final functors with filtered (co)domain

If `C` is a filtered category, then the usual equivalent conditions for a functor `F : C ⥤ D` to be
final can be restated. We show:

* `final_iff_of_isFiltered`: a concrete description of finality which is sometimes a convenient way
  to show that a functor is final.
* `final_iff_isFiltered_structuredArrow`: `F` is final if and only if `StructuredArrow d F` is
  filtered for all `d : D`, which strengthens the usual statement that `F` is final if and only
  if `StructuredArrow d F` is connected for all `d : D`.
* Under categories of objects of filtered categories are filtered and their forgetful functors
  are final.
* If `D` is a filtered category and `F : C ⥤ D` is fully faithful and satisfies the additional
  condition that for every `d : D` there is an object `c : D` and a morphism `d ⟶ F.obj c`, then
  `C` is filtered and `F` is final.
* Finality and initiality of diagonal functors `diag : C ⥤ C × C` and of projection functors
  of (co)structured arrow categories.
* Finality of `StructuredArrow.post`, given the finality of its arguments.

## References

* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Section 3.2

-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open CategoryTheory.Limits CategoryTheory.Functor Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

/-- If `StructuredArrow d F` is filtered for any `d : D`, then `F : C ⥤ D` is final. This is
simply because filtered categories are connected. More profoundly, the converse is also true if
`C` is filtered, see `final_iff_isFiltered_structuredArrow`. -/
theorem Functor.final_of_isFiltered_structuredArrow [∀ d, IsFiltered (StructuredArrow d F)] :
    Final F where
  out _ := IsFiltered.isConnected _

/-- If `CostructuredArrow F d` is filtered for any `d : D`, then `F : C ⥤ D` is initial. This is
simply because cofiltered categories are connected. More profoundly, the converse is also true
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

/-- The inclusion of a terminal object is final. -/
theorem Functor.final_const_of_isTerminal [IsFiltered C] {X : D} (hX : IsTerminal X) :
    ((Functor.const C).obj X).Final :=
  Functor.final_of_exists_of_isFiltered _ (fun _ => ⟨IsFiltered.nonempty.some, ⟨hX.from _⟩⟩)
    (fun {_ c} _ _ => ⟨c, 𝟙 _, hX.hom_ext _ _⟩)

/-- The inclusion of the terminal object is final. -/
theorem Functor.final_const_terminal [IsFiltered C] [HasTerminal D] :
    ((Functor.const C).obj (⊤_ D)).Final :=
  Functor.final_const_of_isTerminal terminalIsTerminal

/-- If `C` is cofiltered, then we can give an explicit condition for a functor `F : C ⥤ D` to
be final. The converse is also true, see `initial_iff_of_isCofiltered`. -/
theorem Functor.initial_of_exists_of_isCofiltered [IsCofilteredOrEmpty C]
    (h₁ : ∀ d, ∃ c, Nonempty (F.obj c ⟶ d)) (h₂ : ∀ {d : D} {c : C} (s s' : F.obj c ⟶ d),
      ∃ (c' : C) (t : c' ⟶ c), F.map t ≫ s = F.map t ≫ s') : Functor.Initial F := by
  suffices ∀ d, IsCofiltered (CostructuredArrow F d) from
    initial_of_isCofiltered_costructuredArrow F
  exact isCofiltered_costructuredArrow_of_isCofiltered_of_exists F h₁ h₂

/-- The inclusion of an initial object is initial. -/
theorem Functor.initial_const_of_isInitial [IsCofiltered C] {X : D} (hX : IsInitial X) :
    ((Functor.const C).obj X).Initial :=
  Functor.initial_of_exists_of_isCofiltered _ (fun _ => ⟨IsCofiltered.nonempty.some, ⟨hX.to _⟩⟩)
    (fun {_ c} _ _ => ⟨c, 𝟙 _, hX.hom_ext _ _⟩)

/-- The inclusion of the initial object is initial. -/
theorem Functor.initial_const_initial [IsCofiltered C] [HasInitial D] :
    ((Functor.const C).obj (⊥_ D)).Initial :=
  Functor.initial_const_of_isInitial initialIsInitial

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

/-- Any under category on a filtered or empty category is filtered.
(Note that under categories are always cofiltered since they have an initial object.) -/
instance IsFiltered.under [IsFilteredOrEmpty C] (c : C) : IsFiltered (Under c) :=
  isFiltered_structuredArrow_of_isFiltered_of_exists _
    (fun c' => ⟨c', ⟨𝟙 _⟩⟩)
    (fun s s' => IsFilteredOrEmpty.cocone_maps s s') c

/-- Any over category on a cofiltered or empty category is cofiltered.
(Note that over categories are always filtered since they have a terminal object.) -/
instance IsCofiltered.over [IsCofilteredOrEmpty C] (c : C) : IsCofiltered (Over c) :=
  isCofiltered_costructuredArrow_of_isCofiltered_of_exists _
    (fun c' => ⟨c', ⟨𝟙 _⟩⟩)
    (fun s s' => IsCofilteredOrEmpty.cone_maps s s') c

/-- The forgetful functor of the under category on any filtered or empty category is final. -/
instance Under.final_forget [IsFilteredOrEmpty C] (c : C) : Final (Under.forget c) :=
  final_of_exists_of_isFiltered _
    (fun c' => ⟨mk (IsFiltered.leftToMax c c'), ⟨IsFiltered.rightToMax c c'⟩⟩)
    (fun {_} {x} s s' => by
      use mk (x.hom ≫ IsFiltered.coeqHom s s')
      use homMk (IsFiltered.coeqHom s s') (by simp)
      simp only [forget_obj, mk_right, forget_map, homMk_right]
      rw [IsFiltered.coeq_condition])

/-- The forgetful functor of the over category on any cofiltered or empty category is initial. -/
instance Over.initial_forget [IsCofilteredOrEmpty C] (c : C) : Initial (Over.forget c) :=
  initial_of_exists_of_isCofiltered _
    (fun c' => ⟨mk (IsCofiltered.minToLeft c c'), ⟨IsCofiltered.minToRight c c'⟩⟩)
    (fun {_} {x} s s' => by
      use mk (IsCofiltered.eqHom s s' ≫ x.hom)
      use homMk (IsCofiltered.eqHom s s') (by simp)
      simp only [forget_obj, mk_left, forget_map, homMk_left]
      rw [IsCofiltered.eq_condition])

section LocallySmall

variable {C : Type v₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D] (F : C ⥤ D)

/-- Implementation; use `Functor.Final.exists_coeq instead`. -/
theorem Functor.Final.exists_coeq_of_locally_small [IsFilteredOrEmpty C] [Final F] {d : D} {c : C}
    (s s' : d ⟶ F.obj c) : ∃ (c' : C) (t : c ⟶ c'), s ≫ F.map t = s' ≫ F.map t := by
  have : colimit.ι (F ⋙ coyoneda.obj (op d)) c s = colimit.ι (F ⋙ coyoneda.obj (op d)) c s' := by
    apply (Final.colimitCompCoyonedaIso F d).toEquiv.injective
    subsingleton
  obtain ⟨c', t₁, t₂, h⟩ := (Types.FilteredColimit.colimit_eq_iff.{v₁, v₁, v₁} _).mp this
  refine ⟨IsFiltered.coeq t₁ t₂, t₁ ≫ IsFiltered.coeqHom t₁ t₂, ?_⟩
  conv_rhs => rw [IsFiltered.coeq_condition t₁ t₂]
  dsimp at h
  simp [reassoc_of% h]

end LocallySmall

/-- If `C` is filtered, then we can give an explicit condition for a functor `F : C ⥤ D` to
be final. -/
theorem Functor.final_iff_of_isFiltered [IsFilteredOrEmpty C] :
    Final F ↔ (∀ d, ∃ c, Nonempty (d ⟶ F.obj c)) ∧ (∀ {d : D} {c : C} (s s' : d ⟶ F.obj c),
      ∃ (c' : C) (t : c ⟶ c'), s ≫ F.map t = s' ≫ F.map t) := by
  refine ⟨fun hF => ⟨?_, ?_⟩, fun h => final_of_exists_of_isFiltered F h.1 h.2⟩
  · intro d
    obtain ⟨f⟩ : Nonempty (StructuredArrow d F) := IsConnected.is_nonempty
    exact ⟨_, ⟨f.hom⟩⟩
  · let s₁ : C ≌ AsSmall.{max u₁ v₁ u₂ v₂} C := AsSmall.equiv
    let s₂ : D ≌ AsSmall.{max u₁ v₁ u₂ v₂} D := AsSmall.equiv
    have : IsFilteredOrEmpty (AsSmall.{max u₁ v₁ u₂ v₂} C) := .of_equivalence s₁
    intro d c s s'
    obtain ⟨c', t, ht⟩ := Functor.Final.exists_coeq_of_locally_small (s₁.inverse ⋙ F ⋙ s₂.functor)
      (AsSmall.up.map s) (AsSmall.up.map s')
    exact ⟨AsSmall.down.obj c', AsSmall.down.map t, s₂.functor.map_injective (by simp_all [s₁, s₂])⟩

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

/-- If `C` is filtered, then the structured arrow category on the diagonal functor `C ⥤ C × C`
is filtered as well. -/
instance [IsFilteredOrEmpty C] (X : C × C) : IsFiltered (StructuredArrow X (diag C)) := by
  haveI : ∀ Y, IsFiltered (StructuredArrow Y (Under.forget X.1)) := by
    rw [← final_iff_isFiltered_structuredArrow (Under.forget X.1)]
    infer_instance
  apply IsFiltered.of_equivalence (StructuredArrow.ofDiagEquivalence X).symm

/-- The diagonal functor on any filtered category is final. -/
instance Functor.final_diag_of_isFiltered [IsFilteredOrEmpty C] : Final (Functor.diag C) :=
  final_of_isFiltered_structuredArrow _

-- Adding this instance causes performance problems elsewhere, even with low priority
theorem IsFilteredOrEmpty.isSiftedOrEmpty [IsFilteredOrEmpty C] : IsSiftedOrEmpty C :=
  Functor.final_diag_of_isFiltered

-- Adding this instance causes performance problems elsewhere, even with low priority
attribute [local instance] IsFiltered.nonempty in
theorem IsFiltered.isSifted [IsFiltered C] : IsSifted C where

/-- If `C` is cofiltered, then the costructured arrow category on the diagonal functor `C ⥤ C × C`
is cofiltered as well. -/
instance [IsCofilteredOrEmpty C] (X : C × C) : IsCofiltered (CostructuredArrow (diag C) X) := by
  haveI : ∀ Y, IsCofiltered (CostructuredArrow (Over.forget X.1) Y) := by
    rw [← initial_iff_isCofiltered_costructuredArrow (Over.forget X.1)]
    infer_instance
  apply IsCofiltered.of_equivalence (CostructuredArrow.ofDiagEquivalence X).symm

/-- The diagonal functor on any cofiltered category is initial. -/
instance Functor.initial_diag_of_isFiltered [IsCofilteredOrEmpty C] : Initial (Functor.diag C) :=
  initial_of_isCofiltered_costructuredArrow _

/-- If `C` is filtered, then every functor `F : C ⥤ Discrete PUnit` is final. -/
theorem Functor.final_of_isFiltered_of_pUnit [IsFiltered C] (F : C ⥤ Discrete PUnit) :
    Final F := by
  refine final_of_exists_of_isFiltered F (fun _ => ?_) (fun {_} {c} _ _ => ?_)
  · use Classical.choice IsFiltered.nonempty
    exact ⟨Discrete.eqToHom (by simp)⟩
  · use c; use 𝟙 c
    apply Subsingleton.elim

/-- If `C` is cofiltered, then every functor `F : C ⥤ Discrete PUnit` is initial. -/
theorem Functor.initial_of_isCofiltered_pUnit [IsCofiltered C] (F : C ⥤ Discrete PUnit) :
    Initial F := by
  refine initial_of_exists_of_isCofiltered F (fun _ => ?_) (fun {_} {c} _ _ => ?_)
  · use Classical.choice IsCofiltered.nonempty
    exact ⟨Discrete.eqToHom (by simp)⟩
  · use c; use 𝟙 c
    apply Subsingleton.elim

/-- The functor `StructuredArrow.proj : StructuredArrow Y T ⥤ C` is final if `T : C ⥤ D` is final
and `C` is filtered. -/
instance StructuredArrow.final_proj_of_isFiltered [IsFilteredOrEmpty C]
    (T : C ⥤ D) [Final T] (Y : D) : Final (StructuredArrow.proj Y T) := by
  refine ⟨fun X => ?_⟩
  rw [isConnected_iff_of_equivalence (ofStructuredArrowProjEquivalence T Y X)]
  exact (final_comp (Under.forget X) T).out _

/-- The functor `CostructuredArrow.proj : CostructuredArrow Y T ⥤ C` is initial if `T : C ⥤ D` is
initial and `C` is cofiltered. -/
instance CostructuredArrow.initial_proj_of_isCofiltered [IsCofilteredOrEmpty C]
    (T : C ⥤ D) [Initial T] (Y : D) : Initial (CostructuredArrow.proj T Y) := by
  refine ⟨fun X => ?_⟩
  rw [isConnected_iff_of_equivalence (ofCostructuredArrowProjEquivalence T Y X)]
  exact (initial_comp (Over.forget X) T).out _

set_option backward.isDefEq.respectTransparency false in
/-- The functor `StructuredArrow d T ⥤ StructuredArrow e (T ⋙ S)` that `u : e ⟶ S.obj d`
induces via `StructuredArrow.map₂` is final, if `T` and `S` are final and the domain of `T` is
filtered. -/
instance StructuredArrow.final_map₂_id [IsFiltered C] {E : Type u₃} [Category.{v₃} E]
    {T : C ⥤ D} [T.Final] {S : D ⥤ E} [S.Final] {T' : C ⥤ E}
    {d : D} {e : E} (u : e ⟶ S.obj d) (α : T ⋙ S ⟶ T') [IsIso α] :
    Final (map₂ (F := 𝟭 _) u α) := by
  haveI : IsFiltered (StructuredArrow e (T ⋙ S)) :=
    (T ⋙ S).final_iff_isFiltered_structuredArrow.mp inferInstance e
  apply final_of_natIso (map₂IsoPreEquivalenceInverseCompProj d e u α).symm

set_option backward.isDefEq.respectTransparency false in
/-- `StructuredArrow.map` is final if the functor `T` is final and its domain is filtered. -/
instance StructuredArrow.final_map [IsFiltered C] {S S' : D} (f : S ⟶ S') (T : C ⥤ D) [T.Final] :
    Final (map (T := T) f) := by
  haveI := NatIso.isIso_of_isIso_app (𝟙 T)
  have : (map₂ (F := 𝟭 C) (G := 𝟭 D) f (𝟙 T)).Final := by
    apply StructuredArrow.final_map₂_id (S := 𝟭 D) (T := T) (T' := T) f (𝟙 T)
  apply final_of_natIso (mapIsoMap₂ f).symm

/-- `StructuredArrow.post X T S` is final if `T` and `S` are final and the domain of `T` is
filtered. -/
instance StructuredArrow.final_post [IsFiltered C] {E : Type u₃} [Category.{v₃} E] (X : D)
    (T : C ⥤ D) [T.Final] (S : D ⥤ E) [S.Final] : Final (post X T S) := by
  apply final_of_natIso (postIsoMap₂ X T S).symm

/-- The functor `CostructuredArrow T d ⥤ CostructuredArrow (T ⋙ S) e` that `u : S.obj d ⟶ e`
induces via `CostructuredArrow.map₂` is initial, if `T` and `S` are initial and the domain of `T` is
filtered. -/
instance CostructuredArrow.initial_map₂_id [IsCofiltered C] {E : Type u₃} [Category.{v₃} E]
    (T : C ⥤ D) [T.Initial] (S : D ⥤ E) [S.Initial] (d : D) (e : E)
    (u : S.obj d ⟶ e) : Initial (map₂ (F := 𝟭 _) (U := T ⋙ S) (𝟙 (T ⋙ S)) u) := by
  have := (T ⋙ S).initial_iff_isCofiltered_costructuredArrow.mp inferInstance e
  apply initial_of_natIso (map₂IsoPreEquivalenceInverseCompProj T S d e u).symm

/-- `CostructuredArrow.post T S X` is initial if `T` and `S` are initial and the domain of `T` is
cofiltered. -/
instance CostructuredArrow.initial_post [IsCofiltered C] {E : Type u₃} [Category.{v₃} E] (X : D)
    (T : C ⥤ D) [T.Initial] (S : D ⥤ E) [S.Initial] : Initial (post T S X) := by
  apply initial_of_natIso (postIsoMap₂ X T S).symm

section Pi

variable {α : Type u₁} {I : α → Type u₂} [∀ s, Category.{v₂} (I s)]

open IsFiltered in
instance final_eval [∀ s, IsFiltered (I s)] (s : α) : (Pi.eval I s).Final := by
  classical
  apply Functor.final_of_exists_of_isFiltered
  · exact fun i => ⟨Function.update (fun t => nonempty.some) s i, ⟨by simpa using 𝟙 _⟩⟩
  · intro d c f g
    let c't : (∀ s, (c' : I s) × (c s ⟶ c')) := Function.update (fun t => ⟨c t, 𝟙 (c t)⟩)
      s ⟨coeq f g, coeqHom f g⟩
    refine ⟨fun t => (c't t).1, fun t => (c't t).2, ?_⟩
    dsimp only [Pi.eval_obj, Pi.eval_map, c't]
    rw [Function.update_self]
    simpa using coeq_condition _ _

open IsCofiltered in
instance initial_eval [∀ s, IsCofiltered (I s)] (s : α) : (Pi.eval I s).Initial := by
  classical
  apply Functor.initial_of_exists_of_isCofiltered
  · exact fun i => ⟨Function.update (fun t => nonempty.some) s i, ⟨by simpa using 𝟙 _⟩⟩
  · intro d c f g
    let c't : (∀ s, (c' : I s) × (c' ⟶ c s)) := Function.update (fun t => ⟨c t, 𝟙 (c t)⟩)
      s ⟨eq f g, eqHom f g⟩
    refine ⟨fun t => (c't t).1, fun t => (c't t).2, ?_⟩
    dsimp only [Pi.eval_obj, Pi.eval_map, c't]
    rw [Function.update_self]
    simpa using eq_condition _ _

end Pi

section Prod

namespace IsFiltered

attribute [local instance] IsFiltered.isConnected IsCofiltered.isConnected

instance final_fst [IsFiltered D] : (Prod.fst C D).Final := inferInstance

instance final_snd [IsFiltered C] : (Prod.snd C D).Final := inferInstance

instance initial_fst [IsCofiltered D] : (Prod.fst C D).Initial := inferInstance

instance initial_snd [IsCofiltered C] : (Prod.snd C D).Initial := inferInstance

end IsFiltered

end Prod

end CategoryTheory

open CategoryTheory

lemma Monotone.final_functor_iff {J₁ J₂ : Type*} [Preorder J₁] [Preorder J₂]
    [IsDirectedOrder J₁] {f : J₁ → J₂} (hf : Monotone f) :
    hf.functor.Final ↔ ∀ (j₂ : J₂), ∃ (j₁ : J₁), j₂ ≤ f j₁ := by
  rw [Functor.final_iff_of_isFiltered]
  constructor
  · rintro ⟨h, _⟩ j₂
    obtain ⟨j₁, ⟨φ⟩⟩ := h j₂
    exact ⟨j₁, leOfHom φ⟩
  · intro h
    constructor
    · intro j₂
      obtain ⟨j₁, h₁⟩ := h j₂
      exact ⟨j₁, ⟨homOfLE h₁⟩⟩
    · intro _ c _ _
      exact ⟨c, 𝟙 _, rfl⟩
