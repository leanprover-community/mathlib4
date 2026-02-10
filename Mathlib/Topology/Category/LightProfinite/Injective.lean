/-
Copyright (c) 2025 Lenny Taelman. All rights reserved.
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

This file establishes that non-empty light profinite sets are injective in the
category of profinite sets, and thus also in the category of light profinite sets.
This is used in the proof that the null sequence module is internally projective in light
condensed abelian groups.

## Main results

The main result is `Profinite.injective_of_light`, which provides an instance of
`Injective (lightToProfinite.obj S)` for a non-empty light profinite set `S`. We deduce the
instance `LightProfinite.injective` that every light profinite set is an injective object in the
category `LightProfinite`. The proof uses an inductive extension argument along a presentation of
`S` as sequential limit of finite discrete spaces. The key lemma is
`exists_lift_of_finite_of_mono_of_epi`.

## References

* <https://kskedlaya.org/condensed/sec_profinite_set.html#sec_profinite_set-5>
* <https://www.youtube.com/watch?v=_4G582SIo28&t=3187s>

-/

@[expose] public section

universe u

open Set Topology CategoryTheory Limits

namespace Profinite

/-- This is the key statement for the inductive proof of injectivity of light profinite spaces.
Given a commutative square
```
X >-f->  Y
|g       |g'
v        v
S -f'->> T
```
where `Y` is profinite, `S` is finite, `f` is injective and `f'` is surjective,
there exists a diagonal map `k : Y → S` making the diagram commute.
-/
lemma exists_lift_of_finite_of_injective_of_surjective {X Y S T : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [TotallyDisconnectedSpace Y]
    [TopologicalSpace S] [T2Space S] [Finite S]
    [TopologicalSpace T] [T2Space T]
    (f : X → Y) (hf : Continuous f) (f_inj : Function.Injective f)
    (f' : S → T) (f'_surj : Function.Surjective f')
    (g : X → S) (hg : Continuous g) (g' : Y → T) (hg' : Continuous g')
    (h_comm : g' ∘ f = f' ∘ g) : ∃ k : Y → S, (Continuous k) ∧ (f' ∘ k = g') ∧ (k ∘ f = g) := by
  -- `T` is finite because it admits a surjection from a finite set
  have : Finite T := Finite.of_surjective f' f'_surj
  -- define the closed partition `Z` so `Z i` is the image under `f` of the fiber of `g` at `i`
  let Z : S → Set Y := fun i ↦ f '' (g ⁻¹' {i})
  have Z_closed (i) : IsClosed (Z i) :=
    (IsClosedEmbedding.isClosed_iff_image_isClosed (Continuous.isClosedEmbedding hf f_inj)).mp
    (IsClosed.preimage hg isClosed_singleton)
  have Z_disj : univ.PairwiseDisjoint Z := by
    rw [Set.pairwiseDisjoint_iff]
    simp only [image_inter_nonempty_iff, Z]
    rintro _ _ _ _ ⟨_, rfl, ⟨_, rfl, hy⟩⟩
    rw [f_inj hy]
  -- define `D i` to be the fiber of `g'` at `f' i`
  let D : S → Set Y := fun i ↦ g' ⁻¹' ({f' i})
  -- each `D i` is clopen
  have D_clopen i : IsClopen (D i) := IsClopen.preimage (isClopen_discrete {f' i}) hg'
  -- each `Z i` is contained in `D i`
  have Z_subset_D i : Z i ⊆ D i := by
    intro z hz
    rw [mem_preimage, mem_singleton_iff]
    obtain ⟨x, _, _⟩ := (mem_image _ _ _).mp hz
    have h_comm' : g' (f x) = f' (g x) := congr_fun h_comm x
    simp_all
  -- obtain a clopen partition `C` of `Y` such that `Z i ⊆ C i ⊆ D i`.
  obtain ⟨C, C_clopen, Z_subset_C, C_subset_D, C_cover_D, C_disj⟩ :=
    exists_clopen_partition_of_clopen_cover Z_closed D_clopen Z_subset_D Z_disj
  have D_cover_univ : univ ⊆ (⋃ i, D i) := by
    intro y _
    simp only [mem_iUnion]
    obtain ⟨s, hs⟩ := f'_surj (g' y)
    grind
  have C_cover_univ : ⋃ i, C i = univ := univ_subset_iff.mp (subset_trans D_cover_univ C_cover_D)
  -- define k to be the unique map sending C i to ψ i
  have h_glue (i j : S) (x : Y) (hxi : x ∈ C i) (hxj : x ∈ C j) : i = j := by
    rw [Set.pairwiseDisjoint_iff] at C_disj
    exact C_disj (by simp) (by simp) ⟨x, by grind⟩
  refine ⟨liftCover C (fun i _ ↦ i) h_glue C_cover_univ, IsLocallyConstant.continuous ?_, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_isOpen_fiber]
    intro s
    convert (C_clopen s).2
    ext y
    simp [preimage_liftCover]
  · ext y
    -- y is contained in C i for some i
    have hy : y ∈ ⋃ i, C i := by simp [C_cover_univ]
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    simpa [liftCover_of_mem hi] using symm (C_subset_D i hi)
  · ext x
    simp [liftCover_of_mem <| Z_subset_C (g x) (by simpa [mem_image] using ⟨x, rfl, rfl⟩)]

/-- A categorically stated version of `exists_lift_of_finite_of_injective_of_surjective` in the
category `Profinite`. -/
lemma exists_lift_of_finite_of_mono_of_epi {X Y S T : Profinite.{u}} [Finite S]
    (f : X ⟶ Y) [Mono f] (f' : S ⟶ T) [Epi f']
    (g : X ⟶ S) (g' : Y ⟶ T) (h_comm : f ≫ g' = g ≫ f') :
    ∃ k : Y ⟶ S, (k ≫ f' = g') ∧ (f ≫ k = g) := by
  obtain ⟨k_fun, k_cont, h₁, h₂⟩ := exists_lift_of_finite_of_injective_of_surjective
    f (by fun_prop) ((CompHausLike.mono_iff_injective f).mp inferInstance)
    f' ((epi_iff_surjective f').mp inferInstance)
    g (by fun_prop) g' (by fun_prop) (by simp [← CompHausLike.coe_comp, h_comm])
  exact ⟨CompHausLike.ofHom _ ⟨k_fun, k_cont⟩, by ext; simp [← h₁], by ext; simp [← h₂]⟩

/-- Finite sets are injective objects in `Profinite`. -/
instance injective_of_finite (S : Profinite.{u}) [Nonempty S] [Finite S] :
    Injective (S) where
  factors {X Y} g f _ := by
    have (T : Profinite.{u}) [Nonempty T] : IsSplitEpi (CompHausLike.isTerminalPUnit.from T) :=
      IsSplitEpi.mk' { section_ := CompHausLike.const _ (Nonempty.some inferInstance) }
    obtain ⟨k, _, h2⟩ := exists_lift_of_finite_of_mono_of_epi f
        (CompHausLike.isTerminalPUnit.from S) g (CompHausLike.isTerminalPUnit.from Y)
      (CompHausLike.isTerminalPUnit.hom_ext _ _)
    exact ⟨k, h2⟩

/-- A nonempty light profinite space is injective in `Profinite`. -/
instance injective_of_light (S : LightProfinite.{u}) [Nonempty S] :
    Injective (lightToProfinite.obj S) where
  factors {X Y} g f h := by
    -- help the instance inference a bit
    have (n : ℕ) : Finite <| lightToProfinite.obj (S.component n) :=
      inferInstanceAs (Finite (FintypeCat.toLightProfinite.obj _))
    have : Nonempty <| lightToProfinite.obj (S.component 0) :=
      Nonempty.map (S.proj 0) inferInstance
    have (n : ℕ) : Epi (S.transitionMap n) := (LightProfinite.epi_iff_surjective _).mpr
      (S.surjective_transitionMap n)
    -- base step of the induction: find k0 : Y ⟶ S.component 0
    obtain ⟨k0, h_down0⟩ := Injective.factors (g ≫ lightToProfinite.map (S.proj 0)) f
    /- Induction step: `next` produces k n+1 out of k n:
    ```
    X        --f-->  Y
    |g' (n+1)        |k n
    v                v
    S (n+1) --p n-> S n
    ```
    find `k (n+1) : Y ⟶ S' (n+1)` making both diagrams commute. That is:
      - `h_up (n+1) : k (n+1) ≫ p n = k n`
      - `h_down n+1 : f ≫ k (n+1) = g' (n+1)`
    Construction of `k (n+1)` through extension lemma requires as input:
      - `h_comm n : g' (n+1) ≫ p n = f ≫ k n`, which can be obtained from h_down n. -/
    have h_comm (n : ℕ) (k : Y ⟶ lightToProfinite.obj (S.component n)) (h_down :
        f ≫ k = g ≫ lightToProfinite.map (S.proj n)) : f ≫ k =
          g ≫ lightToProfinite.map (S.proj (n + 1)) ≫ lightToProfinite.map (S.transitionMap n) := by
      rw [h_down, ← Functor.map_comp, ← S.proj_comp_transitionMap n]
    have h_step (n : ℕ) (k : Y ⟶ lightToProfinite.obj (S.component n))
        (h_down : f ≫ k = g ≫ lightToProfinite.map (S.proj n)) :
        ∃ k' : Y ⟶ lightToProfinite.obj (S.component (n + 1)), k' ≫
          lightToProfinite.map (S.transitionMap n) = k ∧ f ≫ k' = g ≫
            lightToProfinite.map (S.proj (n + 1)) :=
      exists_lift_of_finite_of_mono_of_epi f (lightToProfinite.map (S.transitionMap n))
        (g ≫ lightToProfinite.map (S.proj (n + 1))) k (h_comm _ _ h_down)
    let lifts (n : ℕ) := { k : Y ⟶ lightToProfinite.obj (S.component n) //
      f ≫ k = g ≫ lightToProfinite.map (S.proj n) }
    let next (n : ℕ) : lifts n → lifts (n + 1) :=
      fun k ↦ ⟨(h_step n k.val k.property).choose, (h_step n k.val k.property).choose_spec.2⟩
    -- now define a sequence of lifts using induction
    let k_seq (n : Nat) : lifts n := Nat.rec ⟨k0, h_down0⟩ next n
    -- `h_up` and `h_down` are the required commutativity properties
    have h_down (n : ℕ) : f ≫ (k_seq n).val = g ≫ lightToProfinite.map (S.proj n) :=
      (k_seq n).prop
    have h_up : ∀ n, (k_seq (n + 1)).val ≫ lightToProfinite.map (S.transitionMap n) = (k_seq n).val
    | 0 => (h_step 0 k0 h_down0).choose_spec.1
    | n + 1 => (h_step (n + 1) (k_seq (n + 1)).val (k_seq (n + 1)).prop).choose_spec.1
    let k_cone : Cone (S.diagram ⋙ lightToProfinite) :=
      { pt := Y, π := NatTrans.ofOpSequence (fun n ↦ (k_seq n).val) (fun n ↦ (h_up n).symm) }
    -- now the induced map `Y ⟶ S = limₙ Sₙ` is the desired map
    refine ⟨(isLimitOfPreserves _ S.asLimit).lift k_cone, ?_⟩
    have hg : g = (isLimitOfPreserves _ S.asLimit).lift (k_cone.extend f) := by
      apply (isLimitOfPreserves _ S.asLimit).uniq (k_cone.extend f)
      intro n
      simp [show k_cone.π.app n = (k_seq n.unop).1 from rfl, h_down]
    rw [hg]
    apply (isLimitOfPreserves _ S.asLimit).uniq (k_cone.extend f)
    intro n
    simp [-Functor.mapCone_pt, -Functor.mapCone_π_app]

end Profinite

instance LightProfinite.injective (S : LightProfinite.{u}) [Nonempty S] : Injective S where
  factors {X Y} g f _ := by
    obtain ⟨h, _⟩ := Injective.factors (lightToProfinite.map g) (lightToProfinite.map f)
    refine ⟨lightToProfiniteFullyFaithful.preimage h, ?_⟩
    apply lightToProfiniteFullyFaithful.map_injective
    cat_disch
