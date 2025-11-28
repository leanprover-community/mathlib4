/-
Copyright (c) 2024 Lenny Taelman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lenny Taelman
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Topology.Category.LightProfinite.AsLimit
public import Mathlib.Topology.Category.CompHausLike.Limits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.Order.RelClasses

/-!

# Injectivity of light profinite spaces

This file establishes that non-empty light profinite spaces are injective in the
category of light profinite spaces. This is used in the proof that the null sequence
module is internally projective in light condensed abelian groups.

The code below also prepares for proving that non-empty light
profinite spaces are injective in the category of all profinite spaces.

## Implementation notes

The main result is `injective_of_light`, which provides an instance of `Injective S` for
a non-empty light profinite space `S`. The proof uses an inductive extension argument
along a presentation of S as sequential limit of finite spaces. The key lemma is
`light_key_extension_lemma`.

## References

* <https://kskedlaya.org/condensed/sec_profinite_set.html#sec_profinite_set-5>
* <https://www.youtube.com/watch?v=_4G582SIo28&t=3187s>

-/

@[expose] public section

noncomputable section
universe u

open Set Profinite Topology CategoryTheory LightProfinite Fin Limits

namespace Profinite

/-
  Let X be profinite, D i ⊆ X a finite family of clopens, and Z i ⊆ D i closed.
  Assume that the Z i are pairwise disjoint. Then there exist clopens Z i ⊆ C i ⊆ D i
  with the C i disjoint, and such that ∪ C i = ∪ D i
-/

lemma clopen_partition_of_disjoint_closeds_in_clopens
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    {I : Type*} [Finite I] {Z D : I → Set X}
    (Z_closed : ∀ i, IsClosed (Z i)) (D_clopen : ∀ i, IsClopen (D i))
    (Z_subset_D : ∀ i, Z i ⊆ D i) (Z_disj : univ.PairwiseDisjoint Z) :
    ∃ C : I → Set X, (∀ i, IsClopen (C i)) ∧ (∀ i, Z i ⊆ C i) ∧ (∀ i, C i ⊆ D i) ∧
    (⋃ i, D i) ⊆ (⋃ i, C i)  ∧ (univ.PairwiseDisjoint C) := by
  induction I using Finite.induction_empty_option with
  | of_equiv e IH =>
    obtain ⟨C, h1, h2, h3, h4, h5⟩ := IH (Z := Z ∘ e) (D := D ∘ e)
      (fun i ↦ Z_closed (e i)) (fun i ↦ D_clopen (e i))
      (fun i ↦ Z_subset_D (e i)) (by simpa [← e.injective.injOn.pairwiseDisjoint_image])
    refine ⟨C ∘ e.symm, fun i ↦ h1 (e.symm i), fun i ↦ by simpa using h2 (e.symm i),
      fun i ↦ by simpa using h3 (e.symm i), ?_,
      by simpa [← e.symm.injective.injOn.pairwiseDisjoint_image]⟩
    simp only [Function.comp_apply, iUnion_subset_iff] at h4 ⊢
    intro i
    simpa [e.symm.surjective.iUnion_comp C] using h4 (e.symm i)
  | h_empty => exact ⟨fun _ ↦ univ, by simp, by simp, by simp, by simp, fun i ↦ PEmpty.elim i⟩
  | @h_option I _ IH =>
    -- let Z' be the restriction of Z along succ : Fin n → Fin (n+1)
    let Z' : I → Set X := fun i ↦ Z (some i)
    have Z'_closed (i : I) : IsClosed (Z (some i)) := Z_closed (some i)
    have Z'_disj : univ.PairwiseDisjoint (Z ∘ some)  := by
      rw [← (Option.some_injective _).injOn.pairwiseDisjoint_image]
      exact PairwiseDisjoint.subset Z_disj (by simp)
    -- find Z 0 ⊆ V ⊆ D 0 \ ⋃ Z' using clopen_sandwich
    let U : Set X  := D none \ iUnion (Z ∘ some)
    have U_open : IsOpen U := IsOpen.sdiff (D_clopen none).2
      (isClosed_iUnion_of_finite (fun i ↦ Z_closed (some i)))
    have Z0_subset_U : Z none ⊆ U := by
      rw [subset_diff]
      simpa using ⟨Z_subset_D none, fun i ↦ (by apply Z_disj; all_goals simp)⟩
    obtain ⟨V, V_clopen, Z0_subset_V, V_subset_U⟩ :=
      exists_clopen_of_closed_subset_open (Z_closed none) U_open Z0_subset_U
    have V_subset_D0 : V ⊆ D none := subset_trans V_subset_U diff_subset
    -- choose Z' i ⊆ C' i ⊆ D' i = D i.succ \ V using induction hypothesis
    let D' : I → Set X := fun i ↦ D (some i) \ V
    have D'_clopen (i : I): IsClopen (D' i) := IsClopen.diff (D_clopen (some i)) V_clopen
    have Z'_subset_D' (i : I) : Z' i ⊆ D' i := by
      rw [subset_diff]
      refine ⟨by grind, Disjoint.mono_right V_subset_U ?_⟩
      exact Disjoint.mono_left (subset_iUnion_of_subset i fun _ h ↦ h) disjoint_sdiff_right
    obtain ⟨C', C'_clopen, Z'_subset_C', C'_subset_D', C'_cover_D', C'_disj⟩ :=
      IH Z'_closed D'_clopen Z'_subset_D' Z'_disj
    have C'_subset_D (i : I): C' i ⊆ D (some i) := subset_trans (C'_subset_D' i) diff_subset
    -- now choose C0 = D 0 \ ⋃ C' i
    let C0 : Set X := D none \ iUnion (fun i ↦ C' i)
    have C0_subset_D0 : C0 ⊆ D none := diff_subset
    have C0_clopen : IsClopen C0 := IsClopen.diff (D_clopen none)
      (isClopen_iUnion_of_finite C'_clopen)
    have Z0_subset_C0 : Z none ⊆ C0 := by
      unfold C0
      apply subset_diff.mpr
      constructor
      · exact Z_subset_D none
      · apply Disjoint.mono_left Z0_subset_V
        exact disjoint_iUnion_right.mpr fun i ↦ Disjoint.mono_right (C'_subset_D' i)
          disjoint_sdiff_right
    -- patch together to define C := cases C0 C', and verify the needed properties
    let C : Option I → Set X := fun i ↦ Option.casesOn i C0 C'
    have C_clopen : ∀ i, IsClopen (C i) := fun i ↦ Option.casesOn i C0_clopen C'_clopen
    have Z_subset_C : ∀ i, Z i ⊆ C i := fun i ↦ Option.casesOn i Z0_subset_C0 Z'_subset_C'
    have C_subset_D : ∀ i, C i ⊆ D i := fun i ↦ Option.casesOn i C0_subset_D0 C'_subset_D
    have C_cover_D : (⋃ i, D i) ⊆ (⋃ i, C i) := by
      intro x hx
      rw [mem_iUnion] at hx ⊢
      by_cases hx0 : x ∈ C0; { exact ⟨none, hx0⟩ }
      by_cases hxD : x ∈ D none
      · have hxC' : x ∈ ⋃ i, C' i := by grind
        obtain ⟨i, hi⟩ := mem_iUnion.mp hxC'
        exact ⟨some i, hi⟩
      · obtain ⟨none | j, hi⟩ := hx; {grind}
        have hxD' : x ∈ ⋃ i, D' i := mem_iUnion.mpr ⟨j, by grind⟩
        obtain ⟨k, hk⟩ := mem_iUnion.mp <| C'_cover_D' hxD'
        exact ⟨some k, hk⟩
    have C_disj : univ.PairwiseDisjoint C := by
      rw [Set.pairwiseDisjoint_iff]
      rintro (none | i) _ (none | j) _
      · simp
      · simpa [C, C0, Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] using
          Disjoint.mono_right (subset_iUnion (fun i ↦ C' i) j) disjoint_sdiff_left
      · simpa [C, C0, Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] using
          Disjoint.mono_left (subset_iUnion (fun j ↦ C' j) i) disjoint_sdiff_right
      · simpa using (Set.pairwiseDisjoint_iff.mp C'_disj)
          (i := i) (by trivial) (j := j) (by trivial)
    exact ⟨C, C_clopen, Z_subset_C, C_subset_D, C_cover_D, C_disj⟩


/-
  This is the key statement for the inductive proof of injectivity of light
  profinite spaces. Given a commutative square
      X >-f->  Y
      |g       |g'
      v        v
      S -f'->> T
  where Y is profinite, S is finite, f is injective and f' is surjective,
  there exists a diagonal map k : Y → S making the diagram commute.

  It is mathematically equivalent to the previous lemma:
    take Z s to be the fiber of g at s, and D s the fiber of g' at f' s
-/

lemma key_extension_lemma (X Y S T : Type u)
    [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [TotallyDisconnectedSpace Y]
    [TopologicalSpace S] [T2Space S] [Finite S]
    [TopologicalSpace T] [T2Space T]
    (f : X → Y) (hf : Continuous f) (f_inj : Function.Injective f)
    (f' : S → T) (f'_surj : Function.Surjective f')
    (g : X → S) (hg : Continuous g) (g' : Y → T) (hg' : Continuous g')
    (h_comm : g' ∘ f = f' ∘ g) :
  ∃ k : Y → S, (Continuous k) ∧ (f' ∘ k = g') ∧ (k ∘ f = g)  := by
  -- help the instance inference a bit: T is finite
  have : Finite T := Finite.of_surjective f' f'_surj
  -- pick bijection between Fin n and S
  -- obtain ⟨n, φ, ψ, h1, h2⟩ := Finite.exists_equiv_fin S
  -- define Z i to be the image of the fiber of g at i
  let Z : S → Set Y := fun i ↦ f '' (g⁻¹' {i})
  have Z_closed (i) : IsClosed (Z i) :=
    (IsClosedEmbedding.isClosed_iff_image_isClosed (Continuous.isClosedEmbedding hf f_inj)).mp
    (IsClosed.preimage hg isClosed_singleton)
  have Z_disj : univ.PairwiseDisjoint Z := by
    rw [Set.pairwiseDisjoint_iff]
    simp only [image_inter_nonempty_iff, Z]
    rintro _ _ _ _ ⟨_, rfl, ⟨_, rfl, hy⟩⟩
    rw [f_inj hy]
  -- define D i to be the fiber of g' at f' i
  let D : S → Set Y := fun i ↦ g' ⁻¹' ( {f' i})
  have D_clopen i : IsClopen (D i) := IsClopen.preimage (isClopen_discrete {f' i}) hg'
  have Z_subset_D i : Z i ⊆ D i := by
    intro z hz
    rw [mem_preimage, mem_singleton_iff]
    obtain ⟨x, hx1, hx2⟩ := (mem_image _ _ _).mp hz
    rw [← hx2]
    have h_comm' : g' (f x) = f' (g x) := congr_fun h_comm x
    convert rfl
    exact (eq_of_mem_singleton hx1).symm
  have D_cover_univ : univ ⊆ (⋃ i, D i) := by
    intro y _
    simp only [mem_iUnion]
    obtain ⟨s, hs⟩ := f'_surj (g' y)
    use s
    rw [mem_preimage]
    exact hs.symm
  -- obtain clopens Z i ⊆ C i ⊆ D i with C i disjoint, covering Y
  obtain ⟨C, C_clopen, Z_subset_C, C_subset_D, C_cover_D, C_disj⟩ :=
    clopen_partition_of_disjoint_closeds_in_clopens Z_closed D_clopen Z_subset_D Z_disj
  have C_cover_univ : ⋃ i, C i = univ :=  univ_subset_iff.mp
    (subset_trans D_cover_univ C_cover_D)
  -- define k to be the unique map sending C i to ψ i
  have h_glue (i j : S) (x : Y) (hxi : x ∈ C i) (hxj : x ∈ C j) : i = j := by
    rw [Set.pairwiseDisjoint_iff] at C_disj
    apply C_disj
    · simp
    · simp
    · exact ⟨x, by grind⟩
  refine ⟨liftCover C (fun i _ ↦ i) h_glue C_cover_univ, ?_, ?_, ?_⟩
  · apply IsLocallyConstant.continuous
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro s
    convert (C_clopen s).2
    ext y
    simp [preimage_liftCover]
  · ext y
    rw [Function.comp_apply]
    -- y is contained in C i for some i
    have hy : y ∈ ⋃ i, C i := by simp [C_cover_univ]
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    rw [liftCover_of_mem hi]
    exact symm (C_subset_D i hi)
  · ext x
    rw [Function.comp_apply]
    let i := (g x)
    have hC : f x ∈ C i := Z_subset_C i (by simpa [mem_image] using ⟨x, rfl, rfl⟩)
    rw [liftCover_of_mem hC]


-- categorically stated versions of key_extension_lemma

lemma profinite_key_extension_lemma (X Y S T : Profinite.{u}) [Finite S]
    (f : X ⟶ Y) [Mono f] (f' : S ⟶ T) [Epi f']
    (g : X ⟶ S) (g' : Y ⟶ T) (h_comm : f ≫ g' = g ≫ f') :
    ∃ k : Y ⟶ S, (k ≫ f' = g') ∧ (f ≫ k = g)  := by
  obtain ⟨k_fun, k_cont, h2, h3⟩ := key_extension_lemma X Y S T
    f f.hom.continuous ((CompHausLike.mono_iff_injective f).mp inferInstance)
    f' ((epi_iff_surjective f').mp inferInstance)
    g g.hom.continuous g' g'.hom.continuous (by simp [← CompHausLike.coe_comp, h_comm])
  exact ⟨TopCat.ofHom ⟨k_fun, k_cont⟩, ConcreteCategory.hom_ext_iff.mpr (congrFun h2),
    ConcreteCategory.hom_ext_iff.mpr (congrFun h3)⟩

end Profinite

namespace LightProfinite

lemma light_key_extension_lemma (X Y S T : LightProfinite.{u}) [hS : Finite S]
    (f : X ⟶ Y) [Mono f] (f' : S ⟶ T) [Epi f']
    (g : X ⟶ S) (g' : Y ⟶ T) (h_comm : f ≫ g' = g ≫ f') :
    ∃ k : Y ⟶ S, (k ≫ f' = g') ∧ (f ≫ k = g)  := by
  obtain ⟨k_fun, k_cont, h2, h3⟩ := key_extension_lemma X Y S T
    f f.hom.continuous ((CompHausLike.mono_iff_injective f).mp inferInstance)
    f' ((epi_iff_surjective f').mp inferInstance)
    g g.hom.continuous g' g'.hom.continuous (by simp [← CompHausLike.coe_comp, h_comm])
  exact ⟨TopCat.ofHom ⟨k_fun, k_cont⟩, ConcreteCategory.hom_ext_iff.mpr (congrFun h2),
    ConcreteCategory.hom_ext_iff.mpr (congrFun h3)⟩

end LightProfinite

namespace CompHausLike

/-
  The map from a nonempty space to pt is (split) epi in a CompHausLike category of spaces
-/

instance {P : TopCat.{u} → Prop} [HasProp P PUnit.{u + 1}]
    (X : CompHausLike.{u} P) [Nonempty X] :
    IsSplitEpi (isTerminalPUnit.from X) := IsSplitEpi.mk'
  { section_ := const _ (Nonempty.some inferInstance), id := isTerminalPUnit.hom_ext _ _ }

end CompHausLike

/-
  Next we show that nonempty (light) profinite spaces are injective.
-/

instance LightProfinite.injective_of_finite (S : LightProfinite.{u}) [Nonempty S] [Finite S] :
    Injective (S) where
  factors {X Y} g f _ := by
    let f' := CompHausLike.isTerminalPUnit.from S
    let g' := CompHausLike.isTerminalPUnit.from Y
    obtain ⟨k, _, h2⟩ := light_key_extension_lemma _ _ S _ f f' g g'
      (CompHausLike.isTerminalPUnit.hom_ext _ _)
    exact ⟨k, h2⟩

instance Profinite.injective_of_finite (S : Profinite.{u}) [Nonempty S] [Finite S] :
    Injective (S) where
  factors {X Y} g f _ := by
    let f' := CompHausLike.isTerminalPUnit.from S
    let g' := CompHausLike.isTerminalPUnit.from Y
    obtain ⟨k, _, h2⟩ := profinite_key_extension_lemma _ _ S _ f f' g g'
      (CompHausLike.isTerminalPUnit.hom_ext _ _)
    exact ⟨k, h2⟩


namespace LightProfinite

/-
  Main theorem: a nonempty light profinite space is injective in LightProfinite
  TODO: a nonempty light profinite space is injective in Profinite
-/

/-
  Induction step in the proof:

      X        --f-->  Y
      |g' (n+1)        |k n
      v                v
      S. (n+1) --p n-> S. n

  find k n+1 : Y ⟶ S' (n+1) making both diagrams commute. That is:
   - h_up n+1 : k (n+1) ≫ p n = k n   **** recursive, requires k n
   - h_down n+1 : f ≫ k (n+1) = g' (n+1)
  Construction of k (n+1) through extension lemma requires as input:
   - h_comm n : g' (n+1) ≫ p n = f ≫ k n, which can be obtained from h_down n

-/

instance injective_of_light (S : LightProfinite.{u}) [Nonempty S] : Injective S where
  factors {X Y} g f h := by
    -- help the instance inference a bit
    haveI (n : ℕ) : Finite (S.component n) :=
      inferInstanceAs (Finite (FintypeCat.toLightProfinite.obj _))
    haveI : Nonempty (S.component 0) := Nonempty.map (S.proj 0) inferInstance
    haveI (n : ℕ) : Epi (S.transitionMap n) := (LightProfinite.epi_iff_surjective _).mpr
      (S.surjective_transitionMap n)
    -- base step of the induction: find k0 : Y ⟶ S.component 0
    obtain ⟨k0, h_down0⟩ :=  Injective.factors (g ≫ S.proj 0) f
    have h_comm0 : f ≫ k0 = g ≫ S.proj 1 ≫ S.transitionMap 0 := by
      rw [h_down0]
      exact congrArg _ (S.proj_comp_transitionMap 0).symm
    -- key part of induction step: next produces k n+1 out of k n, see diagram above
    have h_step (n : ℕ) (k : Y ⟶ S.component n) (h_down : f ≫ k = g ≫ S.proj n) :
      ∃ k' : Y ⟶ S.component (n+1), k' ≫ S.transitionMap n = k ∧ f ≫ k' = g ≫ S.proj (n+1) := by
      have h_comm : f ≫ k = g ≫ S.proj (n+1) ≫ S.transitionMap n := by
        rw [h_down]
        exact congrArg _ (S.proj_comp_transitionMap n).symm
      exact light_key_extension_lemma _ _ _ _ f (S.transitionMap n) (g ≫ (S.proj (n+1))) k h_comm
    let lifts (n : ℕ) := { k : Y ⟶ S.component n // f ≫ k = g ≫ S.proj n }
    let next (n : ℕ) : lifts n → lifts (n+1) :=
      fun k ↦ ⟨Classical.choose (h_step n k.val k.property),
        (Classical.choose_spec (h_step n k.val k.property)).2⟩
    -- now define sequence of lifts using induction
    let k_seq (n : Nat) : lifts n := Nat.rec ⟨k0, h_down0⟩ next n
    -- h_up and h_down are the required commutativity properties
    have h_down (n : ℕ) : f ≫ (k_seq n).val = g ≫ S.proj n := (k_seq n).property
    have h_up (n : ℕ) : (k_seq (n+1)).val ≫ S.transitionMap n = (k_seq n).val := by
      induction n with
      | zero => exact (Classical.choose_spec (h_step 0 k0 h_down0)).1
      | succ n ih =>
        exact (Classical.choose_spec (h_step (n+1) (k_seq (n+1)).val (k_seq (n+1)).property)).1
    let k_cone : Cone S.diagram :=
      { pt := Y, π := NatTrans.ofOpSequence (fun n ↦ (k_seq n).val) (fun n ↦ (h_up n).symm) }
    -- now the induced map Y ⟶ S = lim S.component is the desired map
    use S.asLimit.lift k_cone
    let g_cone : Cone S.diagram :=
      { pt := X, π := NatTrans.ofOpSequence (fun n ↦ g ≫ S.proj n) (fun n ↦ by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
        exact congrArg _ (S.proj_comp_transitionMap n).symm) }
    have hg : g = S.asLimit.lift g_cone := by
      apply S.asLimit.uniq g_cone
      intro n
      rw [NatTrans.ofOpSequence_app]
    rw [hg]
    have hlim : S.asLimit.lift (k_cone.extend f) = S.asLimit.lift g_cone := by
      unfold Cone.extend
      congr
      ext n
      simp only [Cone.extensions_app, NatTrans.comp_app, Functor.const_map_app,
        NatTrans.ofOpSequence_app]
      erw [h_down]
    rw [← hlim]
    apply S.asLimit.uniq (k_cone.extend f)
    intro n
    simp only [Category.assoc, IsLimit.fac, Cone.extend_π,  Cone.extensions_app,
      NatTrans.comp_app,  Functor.const_map_app]

instance injective_in_profinite_of_light (S : LightProfinite.{u}) [Nonempty S] :
    Injective (lightToProfinite.obj S) := sorry

end LightProfinite
