/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Christian Merten
-/
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.FinitePresentation

/-!

# Finitely presentable objects in `Under R` with `R : CommRingCat`

In this file, we show that finitely presented algebras are finitely presentable in `Under R`,
i.e. `Hom_R(S, -)` preserves filtered colimits.

-/

open CategoryTheory Limits

universe vJ uJ u

variable {J : Type uJ} [Category.{vJ} J] [IsFiltered J]
variable (R : CommRingCat.{u}) (F : J ⥤ CommRingCat.{u}) (α : (Functor.const _).obj R ⟶ F)
variable {S : CommRingCat.{u}} (f : R ⟶ S) (c : Cocone F) (hc : IsColimit c)
variable [PreservesColimit F (forget CommRingCat)]

include hc in
/--
Given a filtered diagram `F` of rings over `R`, `S` an (essentially) of finite type `R`-algebra,
and two ring homs `a : S ⟶ Fᵢ` and `b : S ⟶ Fⱼ` over `R`.
If `a` and `b` agree at `S ⟶ colimit F`,
then there exists `k` such that `a` and `b` are equal at `S ⟶ F_k`.
In other words, the map `colimᵢ Hom_R(S, Fᵢ) ⟶ Hom_R(S, colim F)` is injective.
-/
lemma RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit (hf : f.hom.EssFiniteType)
    {i : J} (a : S ⟶ F.obj i) (ha : f ≫ a = α.app i)
    {j : J} (b : S ⟶ F.obj j) (hb : f ≫ b = α.app j)
    (hab : a ≫ c.ι.app i = b ≫ c.ι.app j) :
    ∃ (k : J) (hik : i ⟶ k) (hjk : j ⟶ k),
      a ≫ F.map hik = b ≫ F.map hjk := by
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  choose k f₁ f₂ h using fun x : S ↦
    (Types.FilteredColimit.isColimit_eq_iff _ hc').mp congr(($hab).hom x)
  let J' : MulticospanShape := ⟨Unit ⊕ Unit, hf.finset, fun _ ↦ .inl .unit, fun _ ↦ .inr .unit⟩
  let D : MulticospanIndex J' J :=
  { left := Sum.elim (fun _ ↦ i) (fun _ ↦ j)
    right x := k x.1
    fst x := f₁ x
    snd x := f₂ x }
  obtain ⟨c'⟩ := IsFiltered.cocone_nonempty D.multicospan
  refine ⟨c'.pt, c'.ι.app (.left (.inl .unit)), c'.ι.app (.left (.inr .unit)), ?_⟩
  ext1
  apply hf.ext
  · rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, reassoc_of% ha, reassoc_of% hb]
    simp [← α.naturality]
  · intro x hx
    rw [← c'.w (.fst (by exact ⟨x, hx⟩)), ← c'.w (.snd (by exact ⟨x, hx⟩))]
    have (x : _) : F.map (f₁ x) (a x) = F.map (f₂ x) (b x) := h x
    simp [D, this]

include hc in
/--
Given a filtered diagram `F` of rings over `R`, `S` a finitely presented `R`-algebra,
and a ring hom `g : S ⟶ colimit F` over `R`.
then there exists `i` such that `g` factors through `Fᵢ`.
In other words, the map `colimᵢ Hom_R(S, Fᵢ) ⟶ Hom_R(S, colim F)` is surjective.
-/
lemma RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit (hf : f.hom.FinitePresentation)
    (g : S ⟶ c.pt) (hg : ∀ i, f ≫ g = α.app i ≫ c.ι.app i) :
    ∃ (i : J) (g' : S ⟶ F.obj i), f ≫ g' = α.app i ∧ g = g' ≫ c.ι.app i := by
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  letI := f.hom.toAlgebra
  obtain ⟨n, hn⟩ := hf
  let P := CommRingCat.of (MvPolynomial (Fin n) R)
  let iP : R ⟶ P := CommRingCat.ofHom MvPolynomial.C
  obtain ⟨π, rfl, hπ, s, hs⟩ :
      ∃ π : P ⟶ S, iP ≫ π = f ∧ Function.Surjective π ∧ (RingHom.ker π.hom).FG := by
    obtain ⟨π, h₁, h₂⟩ := hn
    exact ⟨CommRingCat.ofHom π, by ext1; exact π.comp_algebraMap, h₁, h₂⟩
  obtain ⟨i, g', hg', hg''⟩ : ∃ (i : J) (g' : P ⟶ F.obj i),
      π ≫ g = g' ≫ c.ι.app i ∧ iP ≫ g' = α.app i := by
    choose j x h using fun i ↦ Types.jointly_surjective_of_isColimit hc' ((π ≫ g) (.X i))
    obtain ⟨i, ⟨hi⟩⟩ : ∃ i, Nonempty (∀ a, (j a ⟶ i)) := by
      have : ∃ i, ∀ a, Nonempty (j a ⟶ i) := by
        simpa using IsFiltered.sup_objs_exists (Finset.univ.image j)
      simpa [← exists_true_iff_nonempty, Classical.skolem, -exists_const_iff] using this
    refine ⟨i, CommRingCat.ofHom (MvPolynomial.eval₂Hom
      (α.app i).hom (F.map (hi _) <| x ·)), ?_, ?_⟩
    · ext1
      apply MvPolynomial.ringHom_ext
      · simpa using fun x ↦ congr($(hg i).hom x)
      · intro i
        simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
          Functor.const_obj_obj, CommRingCat.hom_ofHom, MvPolynomial.coe_eval₂Hom,
          MvPolynomial.eval₂_X]
        exact (congr($(c.w (hi i)).hom (x i)).trans (h i)).symm
    · ext x
      simp [P, iP]
  have : ∀ r : s, ∃ (i' : J) (hi' : i ⟶ i'), F.map hi' (g' r) = 0 := by
    intros r
    have := Types.FilteredColimit.isColimit_eq_iff _ hc' (xi := g' r) (j := i) (xj := (0 : F.obj i))
    suffices H : (g' ≫ c.ι.app i) r = 0 by
      obtain ⟨k, f, g, e⟩ := this.mp (by simpa using H)
      exact ⟨k, f, by simpa using e⟩
    rw [← hg']
    simp [show π r = 0 from hs.le (Ideal.subset_span r.2)]
  choose i' hi' hi'' using this
  obtain ⟨c'⟩ := IsFiltered.cocone_nonempty (WidePushoutShape.wideSpan i i' hi')
  refine ⟨c'.pt, CommRingCat.ofHom (RingHom.liftOfSurjective π.hom hπ
    ⟨(g' ≫ F.map (c'.ι.app none)).hom, ?_⟩), ?_, ?_⟩
  · rw [← hs, Ideal.span_le]
    intro r hr
    rw [← c'.w (.init ⟨r, hr⟩)]
    simp [hi'']
  · ext x
    suffices (iP ≫ g' ≫ F.map (c'.ι.app none)) x = α.app c'.pt x by
      simpa [RingHom.liftOfRightInverse_comp_apply] using this
    rw [← Category.assoc, hg'', ← NatTrans.naturality]
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
  · ext x
    obtain ⟨x, rfl⟩ := hπ x
    suffices (π ≫ g) x = (g' ≫ F.map (c'.ι.app none) ≫ c.ι.app _) x by
      simpa [RingHom.liftOfRightInverse_comp_apply, -NatTrans.naturality] using this
    rw [c.w, hg']
    rfl

/-- If `S` is a finitely presented `R`-algebra, then `Hom_R(S, -)` preserves filtered colimits. -/
lemma preservesColimit_coyoneda_of_finitePresentation
    (S : Under R) (hS : S.hom.hom.FinitePresentation) (F : J ⥤ Under R)
    [PreservesColimit (F ⋙ Under.forget R) (forget CommRingCat)] :
    PreservesColimit F (coyoneda.obj (.op S)) := by
  constructor
  intro c hc
  refine ⟨Types.FilteredColimit.isColimitOf _ _ ?_ ?_⟩
  · intro f
    obtain ⟨i, g, h₁, h₂⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
       R (F ⋙ Under.forget R) { app i := (F.obj i).hom } S.hom ((Under.forget R).mapCocone c)
      (PreservesColimit.preserves hc).some hS f.right (by simp)
    exact ⟨i, Under.homMk g h₁, Under.UnderMorphism.ext h₂⟩
  · intro i j f₁ f₂ e
    dsimp at *
    obtain ⟨k, hik, hjk, e⟩ := RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit
      R (F ⋙ Under.forget R) { app i := (F.obj i).hom } S.hom ((Under.forget R).mapCocone c)
      (PreservesColimit.preserves hc).some
      (RingHom.FiniteType.of_finitePresentation hS).essFiniteType
      f₁.right (Under.w f₁) f₂.right (Under.w f₂) congr($(e).right)
    exact ⟨k, hik, hjk, Under.UnderMorphism.ext e⟩

/-- If `S` is a finitely presented `R`-algebra, then `Hom_R(S, -)` preserves filtered colimits. -/
lemma preservesFilteredColimits_coyoneda (S : Under R) (hS : S.hom.hom.FinitePresentation) :
    PreservesFilteredColimits (coyoneda.obj (.op S)) :=
  ⟨fun _ _ _ ↦ ⟨preservesColimit_coyoneda_of_finitePresentation R S hS _⟩⟩

/-- If `S` is a finitely presented `R`-algebra, `S : Under R` is finitely presentable. -/
lemma isFinitelyPresentable (S : Under R) (hS : S.hom.hom.FinitePresentation) :
    IsFinitelyPresentable.{u} S := by
  rw [isFinitelyPresentable_iff_preservesFilteredColimits]
  exact preservesFilteredColimits_coyoneda R S hS

