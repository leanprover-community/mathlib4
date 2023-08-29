/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Monad.Types
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Data.Set.Constructions

#align_import topology.category.Compactum from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!

# Compacta and Compact Hausdorff Spaces

Recall that, given a monad `M` on `Type*`, an *algebra* for `M` consists of the following data:
- A type `X : Type*`
- A "structure" map `M X → X`.
This data must also satisfy a distributivity and unit axiom, and algebras for `M` form a category
in an evident way.

See the file `CategoryTheory.Monad.Algebra` for a general version, as well as the following link.
https://ncatlab.org/nlab/show/monad

This file proves the equivalence between the category of *compact Hausdorff topological spaces*
and the category of algebras for the *ultrafilter monad*.

## Notation:

Here are the main objects introduced in this file.
- `Compactum` is the type of compacta, which we define as algebras for the ultrafilter monad.
- `compactumToCompHaus` is the functor `Compactum ⥤ CompHaus`. Here `CompHaus` is the usual
  category of compact Hausdorff spaces.
- `compactumToCompHaus.isEquivalence` is a term of type `IsEquivalence compactumToCompHaus`.

The proof of this equivalence is a bit technical. But the idea is quite simply that the structure
map `Ultrafilter X → X` for an algebra `X` of the ultrafilter monad should be considered as the map
sending an ultrafilter to its limit in `X`. The topology on `X` is then defined by mimicking the
characterization of open sets in terms of ultrafilters.

Any `X : Compactum` is endowed with a coercion to `Type*`, as well as the following instances:
- `TopologicalSpace X`.
- `CompactSpace X`.
- `T2Space X`.

Any morphism `f : X ⟶ Y` of is endowed with a coercion to a function `X → Y`, which is shown to
be continuous in `continuous_of_hom`.

The function `Compactum.ofTopologicalSpace` can be used to construct a `Compactum` from a
topological space which satisfies `CompactSpace` and `T2Space`.

We also add wrappers around structures which already exist. Here are the main ones, all in the
`Compactum` namespace:

- `forget : Compactum ⥤ Type*` is the forgetful functor, which induces a `ConcreteCategory`
  instance for `Compactum`.
- `free : Type* ⥤ Compactum` is the left adjoint to `forget`, and the adjunction is in `adj`.
- `str : Ultrafilter X → X` is the structure map for `X : Compactum`.
  The notation `X.str` is preferred.
- `join : Ultrafilter (Ultrafilter X) → Ultrafilter X` is the monadic join for `X : Compactum`.
  Again, the notation `X.join` is preferred.
- `incl : X → Ultrafilter X` is the unit for `X : Compactum`. The notation `X.incl` is preferred.

## References

- E. Manes, Algebraic Theories, Graduate Texts in Mathematics 26, Springer-Verlag, 1976.
- https://ncatlab.org/nlab/show/ultrafilter

-/

-- porting note: "Compactum" is already upper case
set_option linter.uppercaseLean3 false
universe u

open CategoryTheory Filter Ultrafilter TopologicalSpace CategoryTheory.Limits FiniteInter

open Classical Topology

local notation "β" => ofTypeMonad Ultrafilter

/-- The type `Compactum` of Compacta, defined as algebras for the ultrafilter monad. -/
def Compactum :=
  Monad.Algebra β deriving Category, Inhabited
#align Compactum Compactum

namespace Compactum

/-- The forgetful functor to Type* -/
def forget : Compactum ⥤ Type* :=
  Monad.forget _ --deriving CreatesLimits, Faithful
  -- Porting note: deriving fails, adding manually. Note `CreatesLimits` now noncomputable
#align Compactum.forget Compactum.forget

instance : Faithful forget :=
  show Faithful <| Monad.forget _ from inferInstance

noncomputable instance : CreatesLimits forget :=
  show CreatesLimits <| Monad.forget _ from inferInstance

/-- The "free" Compactum functor. -/
def free : Type* ⥤ Compactum :=
  Monad.free _
#align Compactum.free Compactum.free

/-- The adjunction between `free` and `forget`. -/
def adj : free ⊣ forget :=
  Monad.adj _
#align Compactum.adj Compactum.adj

-- Basic instances
instance : ConcreteCategory Compactum where forget := forget

-- Porting note: changed from forget to X.A
instance : CoeSort Compactum (Type*) :=
  ⟨fun X => X.A⟩

instance {X Y : Compactum} : CoeFun (X ⟶ Y) fun _ => X → Y :=
  ⟨fun f => f.f⟩

instance : HasLimits Compactum :=
  hasLimits_of_hasLimits_createsLimits forget

/-- The structure map for a compactum, essentially sending an ultrafilter to its limit. -/
def str (X : Compactum) : Ultrafilter X → X :=
  X.a
#align Compactum.str Compactum.str

/-- The monadic join. -/
def join (X : Compactum) : Ultrafilter (Ultrafilter X) → Ultrafilter X :=
  (β ).μ.app _
#align Compactum.join Compactum.join

/-- The inclusion of `X` into `Ultrafilter X`. -/
def incl (X : Compactum) : X → Ultrafilter X :=
  (β ).η.app _
#align Compactum.incl Compactum.incl

@[simp]
theorem str_incl (X : Compactum) (x : X) : X.str (X.incl x) = x := by
  change ((β ).η.app _ ≫ X.a) _ = _
  -- ⊢ (NatTrans.app (Monad.η β) X.A ≫ X.a) x = x
  rw [Monad.Algebra.unit]
  -- ⊢ 𝟙 X.A x = x
  rfl
  -- 🎉 no goals
#align Compactum.str_incl Compactum.str_incl

@[simp]
theorem str_hom_commute (X Y : Compactum) (f : X ⟶ Y) (xs : Ultrafilter X) :
    f (X.str xs) = Y.str (map f xs) := by
  change (X.a ≫ f.f) _ = _
  -- ⊢ (X.a ≫ f.f) xs = str Y (Ultrafilter.map f.f xs)
  rw [← f.h]
  -- ⊢ (β.toFunctor.map f.f ≫ Y.a) xs = str Y (Ultrafilter.map f.f xs)
  rfl
  -- 🎉 no goals
#align Compactum.str_hom_commute Compactum.str_hom_commute

@[simp]
theorem join_distrib (X : Compactum) (uux : Ultrafilter (Ultrafilter X)) :
    X.str (X.join uux) = X.str (map X.str uux) := by
  change ((β ).μ.app _ ≫ X.a) _ = _
  -- ⊢ (NatTrans.app (Monad.μ β) X.A ≫ X.a) uux = str X (Ultrafilter.map (str X) uux)
  rw [Monad.Algebra.assoc]
  -- ⊢ (β.toFunctor.map X.a ≫ X.a) uux = str X (Ultrafilter.map (str X) uux)
  rfl
  -- 🎉 no goals
#align Compactum.join_distrib Compactum.join_distrib

-- Porting note: changes to X.A from X since Lean can't see through X to X.A below
instance {X : Compactum} : TopologicalSpace X.A where
  IsOpen U := ∀ F : Ultrafilter X, X.str F ∈ U → U ∈ F
  isOpen_univ _ _ := Filter.univ_sets _
  isOpen_inter _ _ h3 h4 _ h6 := Filter.inter_sets _ (h3 _ h6.1) (h4 _ h6.2)
  isOpen_sUnion := fun _ h1 _ ⟨T, hT, h2⟩ =>
    mem_of_superset (h1 T hT _ h2) (Set.subset_sUnion_of_mem hT)

theorem isClosed_iff {X : Compactum} (S : Set X) :
    IsClosed S ↔ ∀ F : Ultrafilter X, S ∈ F → X.str F ∈ S := by
  rw [← isOpen_compl_iff]
  -- ⊢ IsOpen Sᶜ ↔ ∀ (F : Ultrafilter X.A), S ∈ F → str X F ∈ S
  constructor
  -- ⊢ IsOpen Sᶜ → ∀ (F : Ultrafilter X.A), S ∈ F → str X F ∈ S
  · intro cond F h
    -- ⊢ str X F ∈ S
    by_contra c
    -- ⊢ False
    specialize cond F c
    -- ⊢ False
    rw [compl_mem_iff_not_mem] at cond
    -- ⊢ False
    contradiction
    -- 🎉 no goals
  · intro h1 F h2
    -- ⊢ Sᶜ ∈ F
    specialize h1 F
    -- ⊢ Sᶜ ∈ F
    cases' F.mem_or_compl_mem S with h h
    -- ⊢ Sᶜ ∈ F
    exacts [absurd (h1 h) h2, h]
    -- 🎉 no goals
#align Compactum.is_closed_iff Compactum.isClosed_iff

instance {X : Compactum} : CompactSpace X := by
  constructor
  -- ⊢ IsCompact Set.univ
  rw [isCompact_iff_ultrafilter_le_nhds]
  -- ⊢ ∀ (f : Ultrafilter X.A), ↑f ≤ 𝓟 Set.univ → ∃ a, a ∈ Set.univ ∧ ↑f ≤ 𝓝 a
  intro F _
  -- ⊢ ∃ a, a ∈ Set.univ ∧ ↑F ≤ 𝓝 a
  refine' ⟨X.str F, by tauto, _⟩
  -- ⊢ ↑F ≤ 𝓝 (str X F)
  rw [le_nhds_iff]
  -- ⊢ ∀ (s : Set X.A), str X F ∈ s → IsOpen s → s ∈ ↑F
  intro S h1 h2
  -- ⊢ S ∈ ↑F
  exact h2 F h1
  -- 🎉 no goals

/-- A local definition used only in the proofs. -/
private def basic {X : Compactum} (A : Set X) : Set (Ultrafilter X) :=
  { F | A ∈ F }

/-- A local definition used only in the proofs. -/
private def cl {X : Compactum} (A : Set X) : Set X :=
  X.str '' basic A

private theorem basic_inter {X : Compactum} (A B : Set X) : basic (A ∩ B) = basic A ∩ basic B := by
  ext G
  -- ⊢ G ∈ Compactum.basic (A ∩ B) ↔ G ∈ Compactum.basic A ∩ Compactum.basic B
  constructor
  -- ⊢ G ∈ Compactum.basic (A ∩ B) → G ∈ Compactum.basic A ∩ Compactum.basic B
  · intro hG
    -- ⊢ G ∈ Compactum.basic A ∩ Compactum.basic B
    constructor <;> filter_upwards [hG]with _
    -- ⊢ G ∈ Compactum.basic A
                    -- ⊢ a✝ ∈ A ∩ B → a✝ ∈ A
                    -- ⊢ a✝ ∈ A ∩ B → a✝ ∈ B
    exacts [And.left, And.right]
    -- 🎉 no goals
  · rintro ⟨h1, h2⟩
    -- ⊢ G ∈ Compactum.basic (A ∩ B)
    exact inter_mem h1 h2
    -- 🎉 no goals

private theorem subset_cl {X : Compactum} (A : Set X) : A ⊆ cl A := fun a ha =>
  ⟨X.incl a, ha, by simp⟩
                    -- 🎉 no goals

private theorem cl_cl {X : Compactum} (A : Set X) : cl (cl A) ⊆ cl A := by
  rintro _ ⟨F, hF, rfl⟩
  -- ⊢ str X F ∈ Compactum.cl A
  -- Notation to be used in this proof.
  let fsu := Finset (Set (Ultrafilter X))
  -- ⊢ str X F ∈ Compactum.cl A
  let ssu := Set (Set (Ultrafilter X))
  -- ⊢ str X F ∈ Compactum.cl A
  let ι : fsu → ssu := fun x ↦ ↑x
  -- ⊢ str X F ∈ Compactum.cl A
  let C0 : ssu := { Z | ∃ B ∈ F, X.str ⁻¹' B = Z }
  -- ⊢ str X F ∈ Compactum.cl A
  let AA := { G : Ultrafilter X | A ∈ G }
  -- ⊢ str X F ∈ Compactum.cl A
  let C1 := insert AA C0
  -- ⊢ str X F ∈ Compactum.cl A
  let C2 := finiteInterClosure C1
  -- ⊢ str X F ∈ Compactum.cl A
  -- C0 is closed under intersections.
  have claim1 : ∀ (B) (_ : B ∈ C0) (C) (_ : C ∈ C0), B ∩ C ∈ C0 := by
    rintro B ⟨Q, hQ, rfl⟩ C ⟨R, hR, rfl⟩
    use Q ∩ R
    simp only [and_true_iff, eq_self_iff_true, Set.preimage_inter]
    exact inter_sets _ hQ hR
  -- All sets in C0 are nonempty.
  have claim2 : ∀ B ∈ C0, Set.Nonempty B := by
    rintro B ⟨Q, hQ, rfl⟩
    obtain ⟨q⟩ := Filter.nonempty_of_mem hQ
    use X.incl q
    simpa
  -- The intersection of AA with every set in C0 is nonempty.
  have claim3 : ∀ B ∈ C0, (AA ∩ B).Nonempty := by
    rintro B ⟨Q, hQ, rfl⟩
    have : (Q ∩ cl A).Nonempty := Filter.nonempty_of_mem (inter_mem hQ hF)
    rcases this with ⟨q, hq1, P, hq2, hq3⟩
    refine' ⟨P, hq2, _⟩
    rw [← hq3] at hq1
    simpa
  -- Suffices to show that the intersection of any finite subcollection of C1 is nonempty.
  suffices ∀ T : fsu, ι T ⊆ C1 → (⋂₀ ι T).Nonempty by
    obtain ⟨G, h1⟩ := exists_ultrafilter_of_finite_inter_nonempty _ this
    use X.join G
    have : G.map X.str = F := Ultrafilter.coe_le_coe.1 fun S hS => h1 (Or.inr ⟨S, hS, rfl⟩)
    rw [join_distrib, this]
    exact ⟨h1 (Or.inl rfl), rfl⟩
  -- C2 is closed under finite intersections (by construction!).
  have claim4 := finiteInterClosure_finiteInter C1
  -- ⊢ ∀ (T : fsu), ι T ⊆ C1 → Set.Nonempty (⋂₀ ι T)
  -- C0 is closed under finite intersections by claim1.
  have claim5 : FiniteInter C0 := ⟨⟨_, univ_mem, Set.preimage_univ⟩, claim1⟩
  -- ⊢ ∀ (T : fsu), ι T ⊆ C1 → Set.Nonempty (⋂₀ ι T)
  -- Every element of C2 is nonempty.
  have claim6 : ∀ P ∈ C2, (P : Set (Ultrafilter X)).Nonempty := by
    suffices ∀ P ∈ C2, P ∈ C0 ∨ ∃ Q ∈ C0, P = AA ∩ Q by
      intro P hP
      cases' this P hP with h h
      · exact claim2 _ h
      · rcases h with ⟨Q, hQ, rfl⟩
        exact claim3 _ hQ
    intro P hP
    exact claim5.finiteInterClosure_insert _ hP
  intro T hT
  -- ⊢ Set.Nonempty (⋂₀ ι T)
  -- Suffices to show that the intersection of the T's is contained in C2.
  suffices ⋂₀ ι T ∈ C2 by exact claim6 _ this
  -- ⊢ ⋂₀ ι T ∈ C2
  -- Finish
  apply claim4.finiteInter_mem T
  -- ⊢ ↑T ⊆ finiteInterClosure C1
  intro t ht
  -- ⊢ t ∈ finiteInterClosure C1
  refine' finiteInterClosure.basic (@hT t ht)
  -- 🎉 no goals

theorem isClosed_cl {X : Compactum} (A : Set X) : IsClosed (cl A) := by
  rw [isClosed_iff]
  -- ⊢ ∀ (F : Ultrafilter X.A), Compactum.cl A ∈ F → str X F ∈ Compactum.cl A
  intro F hF
  -- ⊢ str X F ∈ Compactum.cl A
  exact cl_cl _ ⟨F, hF, rfl⟩
  -- 🎉 no goals
#align Compactum.is_closed_cl Compactum.isClosed_cl

theorem str_eq_of_le_nhds {X : Compactum} (F : Ultrafilter X) (x : X) : ↑F ≤ 𝓝 x → X.str F = x := by
  -- Notation to be used in this proof.
  let fsu := Finset (Set (Ultrafilter X))
  -- ⊢ ↑F ≤ 𝓝 x → str X F = x
  let ssu := Set (Set (Ultrafilter X))
  -- ⊢ ↑F ≤ 𝓝 x → str X F = x
  let ι : fsu → ssu := fun x ↦ ↑x
  -- ⊢ ↑F ≤ 𝓝 x → str X F = x
  let T0 : ssu := { S | ∃ A ∈ F, S = basic A }
  -- ⊢ ↑F ≤ 𝓝 x → str X F = x
  let AA := X.str ⁻¹' {x}
  -- ⊢ ↑F ≤ 𝓝 x → str X F = x
  let T1 := insert AA T0
  -- ⊢ ↑F ≤ 𝓝 x → str X F = x
  let T2 := finiteInterClosure T1
  -- ⊢ ↑F ≤ 𝓝 x → str X F = x
  intro cond
  -- ⊢ str X F = x
  -- If F contains a closed set A, then x is contained in A.
  have claim1 : ∀ A : Set X, IsClosed A → A ∈ F → x ∈ A := by
    intro A hA h
    by_contra H
    rw [le_nhds_iff] at cond
    specialize cond Aᶜ H hA.isOpen_compl
    rw [Ultrafilter.mem_coe, Ultrafilter.compl_mem_iff_not_mem] at cond
    contradiction
  -- If A ∈ F, then x ∈ cl A.
  have claim2 : ∀ A : Set X, A ∈ F → x ∈ cl A := by
    intro A hA
    exact claim1 (cl A) (isClosed_cl A) (mem_of_superset hA (subset_cl A))
  -- T0 is closed under intersections.
  have claim3 : ∀ (S1) (_ : S1 ∈ T0) (S2) (_ : S2 ∈ T0), S1 ∩ S2 ∈ T0 := by
    rintro S1 ⟨S1, hS1, rfl⟩ S2 ⟨S2, hS2, rfl⟩
    exact ⟨S1 ∩ S2, inter_mem hS1 hS2, by simp [basic_inter]⟩
  -- For every S ∈ T0, the intersection AA ∩ S is nonempty.
  have claim4 : ∀ S ∈ T0, (AA ∩ S).Nonempty := by
    rintro S ⟨S, hS, rfl⟩
    rcases claim2 _ hS with ⟨G, hG, hG2⟩
    exact ⟨G, hG2, hG⟩
  -- Every element of T0 is nonempty.
  have claim5 : ∀ S ∈ T0, Set.Nonempty S := by
    rintro S ⟨S, hS, rfl⟩
    exact ⟨F, hS⟩
  -- Every element of T2 is nonempty.
  have claim6 : ∀ S ∈ T2, Set.Nonempty S := by
    suffices ∀ S ∈ T2, S ∈ T0 ∨ ∃ Q ∈ T0, S = AA ∩ Q by
      intro S hS
      cases' this _ hS with h h
      · exact claim5 S h
      · rcases h with ⟨Q, hQ, rfl⟩
        exact claim4 Q hQ
    intro S hS
    apply finiteInterClosure_insert
    · constructor
      · use Set.univ
        refine' ⟨Filter.univ_sets _, _⟩
        ext
        refine' ⟨_, by tauto⟩
        · intro
          apply Filter.univ_sets
      · exact claim3
    · exact hS
  -- It suffices to show that the intersection of any finite subset of T1 is nonempty.
  suffices ∀ F : fsu, ↑F ⊆ T1 → (⋂₀ ι F).Nonempty by
    obtain ⟨G, h1⟩ := Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty _ this
    have c1 : X.join G = F := Ultrafilter.coe_le_coe.1 fun P hP => h1 (Or.inr ⟨P, hP, rfl⟩)
    have c2 : G.map X.str = X.incl x := by
      refine' Ultrafilter.coe_le_coe.1 fun P hP => _
      apply mem_of_superset (h1 (Or.inl rfl))
      rintro x ⟨rfl⟩
      exact hP
    simp [← c1, c2]
  -- Finish...
  intro T hT
  -- ⊢ Set.Nonempty (⋂₀ ι T)
  refine' claim6 _ (finiteInter_mem (.finiteInterClosure_finiteInter _) _ _)
  -- ⊢ ↑T ⊆ finiteInterClosure T1
  intro t ht
  -- ⊢ t ∈ finiteInterClosure T1
  exact finiteInterClosure.basic (@hT t ht)
  -- 🎉 no goals
#align Compactum.str_eq_of_le_nhds Compactum.str_eq_of_le_nhds

theorem le_nhds_of_str_eq {X : Compactum} (F : Ultrafilter X) (x : X) : X.str F = x → ↑F ≤ 𝓝 x :=
  fun h => le_nhds_iff.mpr fun s hx hs => hs _ <| by rwa [h]
                                                     -- 🎉 no goals
#align Compactum.le_nhds_of_str_eq Compactum.le_nhds_of_str_eq

-- All the hard work above boils down to this `T2Space` instance.
instance {X : Compactum} : T2Space X := by
  rw [t2_iff_ultrafilter]
  -- ⊢ ∀ {x y : X.A} (f : Ultrafilter X.A), ↑f ≤ 𝓝 x → ↑f ≤ 𝓝 y → x = y
  intro _ _ F hx hy
  -- ⊢ x✝ = y✝
  rw [← str_eq_of_le_nhds _ _ hx, ← str_eq_of_le_nhds _ _ hy]
  -- 🎉 no goals

/-- The structure map of a compactum actually computes limits. -/
theorem lim_eq_str {X : Compactum} (F : Ultrafilter X) : F.lim = X.str F := by
  rw [Ultrafilter.lim_eq_iff_le_nhds, le_nhds_iff]
  -- ⊢ ∀ (s : Set X.A), str X F ∈ s → IsOpen s → s ∈ ↑F
  tauto
  -- 🎉 no goals
#align Compactum.Lim_eq_str Compactum.lim_eq_str

theorem cl_eq_closure {X : Compactum} (A : Set X) : cl A = closure A := by
  ext
  -- ⊢ x✝ ∈ Compactum.cl A ↔ x✝ ∈ closure A
  rw [mem_closure_iff_ultrafilter]
  -- ⊢ x✝ ∈ Compactum.cl A ↔ ∃ u, A ∈ u ∧ ↑u ≤ 𝓝 x✝
  constructor
  -- ⊢ x✝ ∈ Compactum.cl A → ∃ u, A ∈ u ∧ ↑u ≤ 𝓝 x✝
  · rintro ⟨F, h1, h2⟩
    -- ⊢ ∃ u, A ∈ u ∧ ↑u ≤ 𝓝 x✝
    exact ⟨F, h1, le_nhds_of_str_eq _ _ h2⟩
    -- 🎉 no goals
  · rintro ⟨F, h1, h2⟩
    -- ⊢ x✝ ∈ Compactum.cl A
    exact ⟨F, h1, str_eq_of_le_nhds _ _ h2⟩
    -- 🎉 no goals
#align Compactum.cl_eq_closure Compactum.cl_eq_closure

/-- Any morphism of compacta is continuous. -/
theorem continuous_of_hom {X Y : Compactum} (f : X ⟶ Y) : Continuous f := by
  rw [continuous_iff_ultrafilter]
  -- ⊢ ∀ (x : X.A) (g : Ultrafilter X.A), ↑g ≤ 𝓝 x → Tendsto f.f (↑g) (𝓝 (Monad.Alg …
  intro x g h
  -- ⊢ Tendsto f.f (↑g) (𝓝 (Monad.Algebra.Hom.f f x))
  rw [Tendsto, ← coe_map]
  -- ⊢ ↑(Ultrafilter.map f.f g) ≤ 𝓝 (Monad.Algebra.Hom.f f x)
  apply le_nhds_of_str_eq
  -- ⊢ str Y (Ultrafilter.map f.f g) = Monad.Algebra.Hom.f f x
  rw [← str_hom_commute, str_eq_of_le_nhds _ x _]
  -- ⊢ ↑g ≤ 𝓝 x
  apply h
  -- 🎉 no goals
#align Compactum.continuous_of_hom Compactum.continuous_of_hom

/-- Given any compact Hausdorff space, we construct a Compactum. -/
noncomputable def ofTopologicalSpace (X : Type*) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] : Compactum where
  A := X
  a := Ultrafilter.lim
  unit := by
    ext x
    -- ⊢ (NatTrans.app (Monad.η β) X ≫ Ultrafilter.lim) x = 𝟙 X x
    exact lim_eq (pure_le_nhds _)
    -- 🎉 no goals
  assoc := by
    ext FF
    -- ⊢ (NatTrans.app (Monad.μ β) X ≫ Ultrafilter.lim) FF = (β.toFunctor.map Ultrafi …
    change Ultrafilter (Ultrafilter X) at FF
    -- ⊢ (NatTrans.app (Monad.μ β) X ≫ Ultrafilter.lim) FF = (β.toFunctor.map Ultrafi …
    set x := (Ultrafilter.map Ultrafilter.lim FF).lim with c1
    -- ⊢ (NatTrans.app (Monad.μ β) X ≫ Ultrafilter.lim) FF = (β.toFunctor.map Ultrafi …
    have c2 : ∀ (U : Set X) (F : Ultrafilter X), F.lim ∈ U → IsOpen U → U ∈ F := by
      intro U F h1 hU
      exact isOpen_iff_ultrafilter.mp hU _ h1 _ (Ultrafilter.le_nhds_lim _)
    have c3 : ↑(Ultrafilter.map Ultrafilter.lim FF) ≤ 𝓝 x := by
      rw [le_nhds_iff]
      intro U hx hU
      exact mem_coe.2 (c2 _ _ (by rwa [← c1]) hU)
    have c4 : ∀ U : Set X, x ∈ U → IsOpen U → { G : Ultrafilter X | U ∈ G } ∈ FF := by
      intro U hx hU
      suffices Ultrafilter.lim ⁻¹' U ∈ FF by
        apply mem_of_superset this
        intro P hP
        exact c2 U P hP hU
      exact @c3 U (IsOpen.mem_nhds hU hx)
    apply lim_eq
    -- ⊢ ↑(NatTrans.app (Monad.μ β) X FF) ≤ 𝓝 ((β.toFunctor.map Ultrafilter.lim ≫ Ult …
    rw [le_nhds_iff]
    -- ⊢ ∀ (s : Set X), (β.toFunctor.map Ultrafilter.lim ≫ Ultrafilter.lim) FF ∈ s →  …
    exact c4
    -- 🎉 no goals
#align Compactum.of_topological_space Compactum.ofTopologicalSpace

/-- Any continuous map between Compacta is a morphism of compacta. -/
def homOfContinuous {X Y : Compactum} (f : X → Y) (cont : Continuous f) : X ⟶ Y :=
  { f
    h := by
      rw [continuous_iff_ultrafilter] at cont
      -- ⊢ β.toFunctor.map f ≫ Y.a = X.a ≫ f
      ext (F : Ultrafilter X)
      -- ⊢ (β.toFunctor.map f ≫ Y.a) F = (X.a ≫ f) F
      specialize cont (X.str F) F (le_nhds_of_str_eq F (X.str F) rfl)
      -- ⊢ (β.toFunctor.map f ≫ Y.a) F = (X.a ≫ f) F
      simp only [types_comp_apply, ofTypeFunctor_map]
      -- ⊢ Monad.Algebra.a Y (β.toFunctor.map f F) = f (Monad.Algebra.a X F)
      exact str_eq_of_le_nhds (Ultrafilter.map f F) _ cont }
      -- 🎉 no goals
#align Compactum.hom_of_continuous Compactum.homOfContinuous

end Compactum

/-- The functor functor from Compactum to CompHaus. -/
def compactumToCompHaus : Compactum ⥤ CompHaus where
  obj X := { toTop := { α := X } }
  map := @fun X Y f =>
    { toFun := f
      continuous_toFun := Compactum.continuous_of_hom _ }
#align Compactum_to_CompHaus compactumToCompHaus

namespace compactumToCompHaus

/-- The functor `compactumToCompHaus` is full. -/
def full : Full compactumToCompHaus.{u} where preimage X Y {f} := Compactum.homOfContinuous f.1 f.2
#align Compactum_to_CompHaus.full compactumToCompHaus.full

/-- The functor `compactumToCompHaus` is faithful. -/
theorem faithful : Faithful compactumToCompHaus where
  -- Porting note: this used to be obviously (though it consumed a bit of memory)
  map_injective := by
    intro _ _ _ _ h
    -- ⊢ a₁✝ = a₂✝
    -- Porting note: ext gets confused by coercion using forget
    apply Monad.Algebra.Hom.ext
    -- ⊢ a₁✝.f = a₂✝.f
    apply congrArg (fun f => f.toFun) h
    -- 🎉 no goals
#align Compactum_to_CompHaus.faithful compactumToCompHaus.faithful

/-- This definition is used to prove essential surjectivity of `compactumToCompHaus`. -/
def isoOfTopologicalSpace {D : CompHaus} :
    compactumToCompHaus.obj (Compactum.ofTopologicalSpace D) ≅ D where
  hom :=
    { toFun := id
      continuous_toFun :=
        continuous_def.2 fun _ h => by
          rw [isOpen_iff_ultrafilter'] at h
          -- ⊢ IsOpen (id ⁻¹' x✝)
          exact h }
          -- 🎉 no goals
  inv :=
    { toFun := id
      continuous_toFun :=
        continuous_def.2 fun _ h1 => by
          rw [isOpen_iff_ultrafilter']
          -- ⊢ ∀ (F : Ultrafilter ↑D.toTop), Ultrafilter.lim F ∈ id ⁻¹' x✝ → id ⁻¹' x✝ ∈ ↑F
          intro _ h2
          -- ⊢ id ⁻¹' x✝ ∈ ↑F✝
          exact h1 _ h2 }
          -- 🎉 no goals
#align Compactum_to_CompHaus.iso_of_topological_space compactumToCompHaus.isoOfTopologicalSpace

/-- The functor `compactumToCompHaus` is essentially surjective. -/
theorem essSurj : EssSurj compactumToCompHaus :=
  { mem_essImage := fun X => ⟨Compactum.ofTopologicalSpace X, ⟨isoOfTopologicalSpace⟩⟩ }
#align Compactum_to_CompHaus.ess_surj compactumToCompHaus.essSurj

/-- The functor `compactumToCompHaus` is an equivalence of categories. -/
noncomputable instance isEquivalence : IsEquivalence compactumToCompHaus := by
  have := compactumToCompHaus.full
  -- ⊢ IsEquivalence compactumToCompHaus
  have := compactumToCompHaus.faithful
  -- ⊢ IsEquivalence compactumToCompHaus
  have := compactumToCompHaus.essSurj
  -- ⊢ IsEquivalence compactumToCompHaus
  apply Equivalence.ofFullyFaithfullyEssSurj _
  -- 🎉 no goals
#align Compactum_to_CompHaus.is_equivalence compactumToCompHaus.isEquivalence

end compactumToCompHaus

/-- The forgetful functors of `Compactum` and `CompHaus` are compatible via
`compactumToCompHaus`. -/
def compactumToCompHausCompForget :
    compactumToCompHaus ⋙ CategoryTheory.forget CompHaus ≅ Compactum.forget :=
  NatIso.ofComponents fun X => eqToIso rfl
#align Compactum_to_CompHaus_comp_forget compactumToCompHausCompForget

/-
TODO: `forget CompHaus` is monadic, as it is isomorphic to the composition
of an equivalence with the monadic functor `forget Compactum`.
Once we have the API to transfer monadicity of functors along such isomorphisms,
the instance `CreatesLimits (forget CompHaus)` can be deduced from this
monadicity.
-/
noncomputable instance CompHaus.forgetCreatesLimits : CreatesLimits (forget CompHaus) := by
  let e : forget CompHaus ≅ compactumToCompHaus.inv ⋙ Compactum.forget :=
    (((forget CompHaus).leftUnitor.symm ≪≫
    isoWhiskerRight compactumToCompHaus.asEquivalence.symm.unitIso (forget CompHaus)) ≪≫
    compactumToCompHaus.inv.associator compactumToCompHaus (forget CompHaus)) ≪≫
    isoWhiskerLeft _ compactumToCompHausCompForget
  exact createsLimitsOfNatIso e.symm
  -- 🎉 no goals

#align CompHaus.forget_creates_limits CompHaus.forgetCreatesLimits

noncomputable instance Profinite.forgetCreatesLimits : CreatesLimits (forget Profinite) := by
  change CreatesLimits (profiniteToCompHaus ⋙ forget _)
  -- ⊢ CreatesLimits (profiniteToCompHaus ⋙ forget CompHaus)
  infer_instance
  -- 🎉 no goals
#align Profinite.forget_creates_limits Profinite.forgetCreatesLimits
