/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.dold_kan.functor_gamma
! leanprover-community/mathlib commit 5b8284148e8149728f4b90624888d98c36284454
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.DoldKan.SplitSimplicialObject

/-!

# Construction of the inverse functor of the Dold-Kan equivalence


In this file, we construct the functor `Γ₀ : chain_complex C ℕ ⥤ simplicial_object C`
which shall be the inverse functor of the Dold-Kan equivalence in the case of abelian categories,
and more generally pseudoabelian categories.

By definition, when `K` is a chain_complex, `Γ₀.obj K` is a simplicial object which
sends `Δ : simplex_categoryᵒᵖ` to a certain coproduct indexed by the set
`splitting.index_set Δ` whose elements consists of epimorphisms `e : Δ.unop ⟶ Δ'.unop`
(with `Δ' : simplex_categoryᵒᵖ`); the summand attached to such an `e` is `K.X Δ'.unop.len`.
By construction, `Γ₀.obj K` is a split simplicial object whose splitting is `Γ₀.splitting K`.

We also construct `Γ₂ : karoubi (chain_complex C ℕ) ⥤ karoubi (simplicial_object C)`
which shall be an equivalence for any additive category `C`.

-/


noncomputable section

open
  CategoryTheory CategoryTheory.Category CategoryTheory.Limits SimplexCategory SimplicialObject Opposite CategoryTheory.Idempotents

open Simplicial DoldKan

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type _} [Category C] [Preadditive C] (K K' : ChainComplex C ℕ) (f : K ⟶ K')
  {Δ'' Δ' Δ : SimplexCategory} (i' : Δ'' ⟶ Δ') [Mono i'] (i : Δ' ⟶ Δ) [Mono i]

/-- `is_δ₀ i` is a simple condition used to check whether a monomorphism `i` in
`simplex_category` identifies to the coface map `δ 0`. -/
@[nolint unused_arguments]
def Isδ₀ {Δ Δ' : SimplexCategory} (i : Δ' ⟶ Δ) [Mono i] : Prop :=
  Δ.len = Δ'.len + 1 ∧ i.toOrderHom 0 ≠ 0
#align algebraic_topology.dold_kan.is_δ₀ AlgebraicTopology.DoldKan.Isδ₀

namespace Isδ₀

theorem iff {j : ℕ} {i : Fin (j + 2)} : Isδ₀ (SimplexCategory.δ i) ↔ i = 0 :=
  by
  constructor
  · rintro ⟨h₁, h₂⟩
    by_contra
    exact h₂ (Fin.succAbove_ne_zero_zero h)
  · rintro rfl
    exact ⟨rfl, Fin.succ_ne_zero _⟩
#align algebraic_topology.dold_kan.is_δ₀.iff AlgebraicTopology.DoldKan.Isδ₀.iff

theorem eq_δ₀ {n : ℕ} {i : [n] ⟶ [n + 1]} [Mono i] (hi : Isδ₀ i) : i = SimplexCategory.δ 0 :=
  by
  obtain ⟨j, rfl⟩ := SimplexCategory.eq_δ_of_mono i
  rw [Iff] at hi
  rw [hi]
#align algebraic_topology.dold_kan.is_δ₀.eq_δ₀ AlgebraicTopology.DoldKan.Isδ₀.eq_δ₀

end Isδ₀

namespace Γ₀

namespace Obj

/-- In the definition of `(Γ₀.obj K).obj Δ` as a direct sum indexed by `A : splitting.index_set Δ`,
the summand `summand K Δ A` is `K.X A.1.len`. -/
def summand (Δ : SimplexCategoryᵒᵖ) (A : Splitting.IndexSet Δ) : C :=
  K.pt A.1.unop.len
#align algebraic_topology.dold_kan.Γ₀.obj.summand AlgebraicTopology.DoldKan.Γ₀.Obj.summand

/-- The functor `Γ₀` sends a chain complex `K` to the simplicial object which
sends `Δ` to the direct sum of the objects `summand K Δ A` for all `A : splitting.index_set Δ` -/
def obj₂ (K : ChainComplex C ℕ) (Δ : SimplexCategoryᵒᵖ) [HasFiniteCoproducts C] : C :=
  ∐ fun A : Splitting.IndexSet Δ => summand K Δ A
#align algebraic_topology.dold_kan.Γ₀.obj.obj₂ AlgebraicTopology.DoldKan.Γ₀.Obj.obj₂

namespace Termwise

/-- A monomorphism `i : Δ' ⟶ Δ` induces a morphism `K.X Δ.len ⟶ K.X Δ'.len` which
is the identity if `Δ = Δ'`, the differential on the complex `K` if `i = δ 0`, and
zero otherwise. -/
def mapMono (K : ChainComplex C ℕ) {Δ' Δ : SimplexCategory} (i : Δ' ⟶ Δ) [Mono i] :
    K.pt Δ.len ⟶ K.pt Δ'.len := by
  by_cases Δ = Δ'
  · exact eq_to_hom (by congr )
  · by_cases is_δ₀ i
    · exact K.d Δ.len Δ'.len
    · exact 0
#align algebraic_topology.dold_kan.Γ₀.obj.termwise.map_mono AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono

variable (Δ)

theorem mapMono_id : mapMono K (𝟙 Δ) = 𝟙 _ :=
  by
  unfold map_mono
  simp only [eq_self_iff_true, eq_to_hom_refl, dite_eq_ite, if_true]
#align algebraic_topology.dold_kan.Γ₀.obj.termwise.map_mono_id AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_id

variable {Δ}

theorem mapMono_δ₀' (hi : Isδ₀ i) : mapMono K i = K.d Δ.len Δ'.len :=
  by
  unfold map_mono
  classical
    rw [dif_neg, dif_pos hi]
    rintro rfl
    simpa only [self_eq_add_right, Nat.one_ne_zero] using hi.1
#align algebraic_topology.dold_kan.Γ₀.obj.termwise.map_mono_δ₀' AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_δ₀'

@[simp]
theorem mapMono_δ₀ {n : ℕ} : mapMono K (δ (0 : Fin (n + 2))) = K.d (n + 1) n :=
  mapMono_δ₀' K _ (by rw [is_δ₀.iff])
#align algebraic_topology.dold_kan.Γ₀.obj.termwise.map_mono_δ₀ AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_δ₀

theorem mapMono_eq_zero (h₁ : Δ ≠ Δ') (h₂ : ¬Isδ₀ i) : mapMono K i = 0 :=
  by
  unfold map_mono
  rw [Ne.def] at h₁
  split_ifs
  rfl
#align algebraic_topology.dold_kan.Γ₀.obj.termwise.map_mono_eq_zero AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_eq_zero

variable {K K'}

@[simp, reassoc.1]
theorem mapMono_naturality : mapMono K i ≫ f.f Δ'.len = f.f Δ.len ≫ mapMono K' i :=
  by
  unfold map_mono
  split_ifs
  · subst h
    simp only [id_comp, eq_to_hom_refl, comp_id]
  · rw [HomologicalComplex.Hom.comm]
  · rw [zero_comp, comp_zero]
#align algebraic_topology.dold_kan.Γ₀.obj.termwise.map_mono_naturality AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_naturality

variable (K)

@[simp, reassoc.1]
theorem mapMono_comp : mapMono K i ≫ mapMono K i' = mapMono K (i' ≫ i) :=
  by
  -- case where i : Δ' ⟶ Δ is the identity
  by_cases h₁ : Δ = Δ'
  · subst h₁
    simp only [SimplexCategory.eq_id_of_mono i, comp_id, id_comp, map_mono_id K, eq_to_hom_refl]
  -- case where i' : Δ'' ⟶ Δ' is the identity
  by_cases h₂ : Δ' = Δ''
  · subst h₂
    simp only [SimplexCategory.eq_id_of_mono i', comp_id, id_comp, map_mono_id K, eq_to_hom_refl]
  -- then the RHS is always zero
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt (len_lt_of_mono i h₁)
  obtain ⟨k', hk'⟩ := Nat.exists_eq_add_of_lt (len_lt_of_mono i' h₂)
  have eq : Δ.len = Δ''.len + (k + k' + 2) := by linarith
  rw [map_mono_eq_zero K (i' ≫ i) _ _]; rotate_left
  · by_contra
    simpa only [self_eq_add_right, h] using Eq
  · by_contra
    simp only [h.1, add_right_inj] at eq
    linarith
  -- in all cases, the LHS is also zero, either by definition, or because d ≫ d = 0
  by_cases h₃ : is_δ₀ i
  · by_cases h₄ : is_δ₀ i'
    · rw [map_mono_δ₀' K i h₃, map_mono_δ₀' K i' h₄, HomologicalComplex.d_comp_d]
    · simp only [map_mono_eq_zero K i' h₂ h₄, comp_zero]
  · simp only [map_mono_eq_zero K i h₁ h₃, zero_comp]
#align algebraic_topology.dold_kan.Γ₀.obj.termwise.map_mono_comp AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_comp

end Termwise

variable [HasFiniteCoproducts C]

/-- The simplicial morphism on the simplicial object `Γ₀.obj K` induced by
a morphism `Δ' → Δ` in `simplex_category` is defined on each summand
associated to an `A : Γ_index_set Δ` in terms of the epi-mono factorisation
of `θ ≫ A.e`. -/
def map (K : ChainComplex C ℕ) {Δ' Δ : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') : obj₂ K Δ ⟶ obj₂ K Δ' :=
  Sigma.desc fun A =>
    Termwise.mapMono K (image.ι (θ.unop ≫ A.e)) ≫ Sigma.ι (summand K Δ') (A.pull θ)
#align algebraic_topology.dold_kan.Γ₀.obj.map AlgebraicTopology.DoldKan.Γ₀.Obj.map

@[reassoc.1]
theorem map_on_summand₀ {Δ Δ' : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) {θ : Δ ⟶ Δ'}
    {Δ'' : SimplexCategory} {e : Δ'.unop ⟶ Δ''} {i : Δ'' ⟶ A.1.unop} [Epi e] [Mono i]
    (fac : e ≫ i = θ.unop ≫ A.e) :
    Sigma.ι (summand K Δ) A ≫ map K θ =
      Termwise.mapMono K i ≫ Sigma.ι (summand K Δ') (Splitting.IndexSet.mk e) :=
  by
  simp only [map, colimit.ι_desc, cofan.mk_ι_app]
  have h := SimplexCategory.image_eq fac
  subst h
  congr
  · exact SimplexCategory.image_ι_eq fac
  · dsimp only [SimplicialObject.Splitting.IndexSet.pull]
    congr
    exact SimplexCategory.factorThruImage_eq fac
#align algebraic_topology.dold_kan.Γ₀.obj.map_on_summand₀ AlgebraicTopology.DoldKan.Γ₀.Obj.map_on_summand₀

@[reassoc.1]
theorem map_on_summand₀' {Δ Δ' : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) (θ : Δ ⟶ Δ') :
    Sigma.ι (summand K Δ) A ≫ map K θ =
      Termwise.mapMono K (image.ι (θ.unop ≫ A.e)) ≫ Sigma.ι (summand K _) (A.pull θ) :=
  map_on_summand₀ K A (A.fac_pull θ)
#align algebraic_topology.dold_kan.Γ₀.obj.map_on_summand₀' AlgebraicTopology.DoldKan.Γ₀.Obj.map_on_summand₀'

end Obj

variable [HasFiniteCoproducts C]

/-- The functor `Γ₀ : chain_complex C ℕ ⥤ simplicial_object C`, on objects. -/
@[simps]
def obj (K : ChainComplex C ℕ) : SimplicialObject C
    where
  obj Δ := Obj.obj₂ K Δ
  map Δ Δ' θ := Obj.map K θ
  map_id' Δ := by
    ext A
    cases A
    have fac : A.e ≫ 𝟙 A.1.unop = (𝟙 Δ).unop ≫ A.e := by rw [unop_id, comp_id, id_comp]
    erw [obj.map_on_summand₀ K A fac, obj.termwise.map_mono_id, id_comp, comp_id]
    rcases A with ⟨Δ', ⟨e, he⟩⟩
    rfl
  map_comp' Δ'' Δ' Δ θ' θ := by
    ext A
    cases A
    have fac : θ.unop ≫ θ'.unop ≫ A.e = (θ' ≫ θ).unop ≫ A.e := by rw [unop_comp, assoc]
    rw [← image.fac (θ'.unop ≫ A.e), ← assoc, ←
      image.fac (θ.unop ≫ factor_thru_image (θ'.unop ≫ A.e)), assoc] at fac
    simpa only [obj.map_on_summand₀'_assoc K A θ', obj.map_on_summand₀' K _ θ,
      obj.termwise.map_mono_comp_assoc, obj.map_on_summand₀ K A fac]
#align algebraic_topology.dold_kan.Γ₀.obj AlgebraicTopology.DoldKan.Γ₀.obj

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `discrete_cases #[] -/
theorem splitting_map_eq_id (Δ : SimplexCategoryᵒᵖ) :
    SimplicialObject.Splitting.map (Γ₀.obj K)
        (fun n : ℕ => Sigma.ι (Γ₀.Obj.summand K (op [n])) (Splitting.IndexSet.id (op [n]))) Δ =
      𝟙 _ :=
  by
  ext A
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `discrete_cases #[]"
  induction Δ using Opposite.rec'
  induction' Δ with n
  dsimp
  simp only [colimit.ι_desc, cofan.mk_ι_app, comp_id, Γ₀.obj_map]
  rw [Γ₀.obj.map_on_summand₀ K (SimplicialObject.Splitting.IndexSet.id A.1)
      (show A.e ≫ 𝟙 _ = A.e.op.unop ≫ 𝟙 _ by rfl),
    Γ₀.obj.termwise.map_mono_id, A.ext']
  apply id_comp
#align algebraic_topology.dold_kan.Γ₀.splitting_map_eq_id AlgebraicTopology.DoldKan.Γ₀.splitting_map_eq_id

/-- By construction, the simplicial `Γ₀.obj K` is equipped with a splitting. -/
def splitting (K : ChainComplex C ℕ) : SimplicialObject.Splitting (Γ₀.obj K)
    where
  n n := K.pt n
  ι n := Sigma.ι (Γ₀.Obj.summand K (op [n])) (Splitting.IndexSet.id (op [n]))
  map_is_iso' Δ := by
    rw [Γ₀.splitting_map_eq_id]
    apply is_iso.id
#align algebraic_topology.dold_kan.Γ₀.splitting AlgebraicTopology.DoldKan.Γ₀.splitting

@[simp]
theorem splitting_iso_hom_eq_id (Δ : SimplexCategoryᵒᵖ) : ((splitting K).Iso Δ).Hom = 𝟙 _ :=
  splitting_map_eq_id K Δ
#align algebraic_topology.dold_kan.Γ₀.splitting_iso_hom_eq_id AlgebraicTopology.DoldKan.Γ₀.splitting_iso_hom_eq_id

@[reassoc.1]
theorem obj.map_on_summand {Δ Δ' : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) (θ : Δ ⟶ Δ')
    {Δ'' : SimplexCategory} {e : Δ'.unop ⟶ Δ''} {i : Δ'' ⟶ A.1.unop} [Epi e] [Mono i]
    (fac : e ≫ i = θ.unop ≫ A.e) :
    (Γ₀.splitting K).ιSummand A ≫ (Γ₀.obj K).map θ =
      Γ₀.Obj.Termwise.mapMono K i ≫ (Γ₀.splitting K).ιSummand (Splitting.IndexSet.mk e) :=
  by
  dsimp only [SimplicialObject.Splitting.ιSummand, SimplicialObject.Splitting.ιCoprod]
  simp only [assoc, Γ₀.splitting_iso_hom_eq_id, id_comp, comp_id]
  exact Γ₀.obj.map_on_summand₀ K A fac
#align algebraic_topology.dold_kan.Γ₀.obj.map_on_summand AlgebraicTopology.DoldKan.Γ₀.obj.map_on_summand

@[reassoc.1]
theorem obj.map_on_summand' {Δ Δ' : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) (θ : Δ ⟶ Δ') :
    (splitting K).ιSummand A ≫ (obj K).map θ =
      Obj.Termwise.mapMono K (image.ι (θ.unop ≫ A.e)) ≫ (splitting K).ιSummand (A.pull θ) :=
  by
  apply obj.map_on_summand
  apply image.fac
#align algebraic_topology.dold_kan.Γ₀.obj.map_on_summand' AlgebraicTopology.DoldKan.Γ₀.obj.map_on_summand'

@[reassoc.1]
theorem obj.mapMono_on_summand_id {Δ Δ' : SimplexCategory} (i : Δ' ⟶ Δ) [Mono i] :
    (splitting K).ιSummand (Splitting.IndexSet.id (op Δ)) ≫ (obj K).map i.op =
      Obj.Termwise.mapMono K i ≫ (splitting K).ιSummand (Splitting.IndexSet.id (op Δ')) :=
  obj.map_on_summand K (Splitting.IndexSet.id (op Δ)) i.op (rfl : 𝟙 _ ≫ i = i ≫ 𝟙 _)
#align algebraic_topology.dold_kan.Γ₀.obj.map_mono_on_summand_id AlgebraicTopology.DoldKan.Γ₀.obj.mapMono_on_summand_id

@[reassoc.1]
theorem obj.map_epi_on_summand_id {Δ Δ' : SimplexCategory} (e : Δ' ⟶ Δ) [Epi e] :
    (Γ₀.splitting K).ιSummand (Splitting.IndexSet.id (op Δ)) ≫ (Γ₀.obj K).map e.op =
      (Γ₀.splitting K).ιSummand (Splitting.IndexSet.mk e) :=
  by
  simpa only [Γ₀.obj.map_on_summand K (splitting.index_set.id (op Δ)) e.op
      (rfl : e ≫ 𝟙 Δ = e ≫ 𝟙 Δ),
    Γ₀.obj.termwise.map_mono_id] using id_comp _
#align algebraic_topology.dold_kan.Γ₀.obj.map_epi_on_summand_id AlgebraicTopology.DoldKan.Γ₀.obj.map_epi_on_summand_id

/-- The functor `Γ₀ : chain_complex C ℕ ⥤ simplicial_object C`, on morphisms. -/
@[simps]
def map {K K' : ChainComplex C ℕ} (f : K ⟶ K') : obj K ⟶ obj K'
    where
  app Δ := (Γ₀.splitting K).desc Δ fun A => f.f A.1.unop.len ≫ (Γ₀.splitting K').ιSummand A
  naturality' Δ' Δ θ := by
    apply (Γ₀.splitting K).hom_ext'
    intro A
    simp only [(splitting K).ι_desc_assoc, obj.map_on_summand'_assoc K _ θ, (splitting K).ι_desc,
      assoc, obj.map_on_summand' K' _ θ]
    apply obj.termwise.map_mono_naturality_assoc
#align algebraic_topology.dold_kan.Γ₀.map AlgebraicTopology.DoldKan.Γ₀.map

end Γ₀

variable [HasFiniteCoproducts C]

/-- The functor `Γ₀' : chain_complex C ℕ ⥤ simplicial_object.split C`
that induces `Γ₀ : chain_complex C ℕ ⥤ simplicial_object C`, which
shall be the inverse functor of the Dold-Kan equivalence for
abelian or pseudo-abelian categories. -/
@[simps]
def Γ₀' : ChainComplex C ℕ ⥤ SimplicialObject.Split C
    where
  obj K := SimplicialObject.Split.mk' (Γ₀.splitting K)
  map K K' f :=
    { f := Γ₀.map f
      f := f.f
      comm' := fun n => by
        dsimp
        simpa only [← splitting.ι_summand_id, (Γ₀.splitting K).ι_desc] }
#align algebraic_topology.dold_kan.Γ₀' AlgebraicTopology.DoldKan.Γ₀'

/-- The functor `Γ₀ : chain_complex C ℕ ⥤ simplicial_object C`, which is
the inverse functor of the Dold-Kan equivalence when `C` is an abelian
category, or more generally a pseudoabelian category. -/
@[simps]
def Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C :=
  Γ₀' ⋙ Split.forget _
#align algebraic_topology.dold_kan.Γ₀ AlgebraicTopology.DoldKan.Γ₀

/-- The extension of `Γ₀ : chain_complex C ℕ ⥤ simplicial_object C`
on the idempotent completions. It shall be an equivalence of categories
for any additive category `C`. -/
@[simps]
def Γ₂ : Karoubi (ChainComplex C ℕ) ⥤ Karoubi (SimplicialObject C) :=
  (CategoryTheory.Idempotents.functorExtension₂ _ _).obj Γ₀
#align algebraic_topology.dold_kan.Γ₂ AlgebraicTopology.DoldKan.Γ₂

theorem HigherFacesVanish.on_Γ₀_summand_id (K : ChainComplex C ℕ) (n : ℕ) :
    HigherFacesVanish (n + 1) ((Γ₀.splitting K).ιSummand (Splitting.IndexSet.id (op [n + 1]))) :=
  by
  intro j hj
  have eq := Γ₀.obj.map_mono_on_summand_id K (SimplexCategory.δ j.succ)
  rw [Γ₀.obj.termwise.map_mono_eq_zero K, zero_comp] at eq; rotate_left
  · intro h
    exact (Nat.succ_ne_self n) (congr_arg SimplexCategory.len h)
  · exact fun h => Fin.succ_ne_zero j (by simpa only [is_δ₀.iff] using h)
  exact Eq
#align algebraic_topology.dold_kan.higher_faces_vanish.on_Γ₀_summand_id AlgebraicTopology.DoldKan.HigherFacesVanish.on_Γ₀_summand_id

@[simp, reassoc.1]
theorem pInfty_on_Γ₀_splitting_summand_eq_self (K : ChainComplex C ℕ) {n : ℕ} :
    (Γ₀.splitting K).ιSummand (Splitting.IndexSet.id (op [n])) ≫ (PInfty : K[Γ₀.obj K] ⟶ _).f n =
      (Γ₀.splitting K).ιSummand (Splitting.IndexSet.id (op [n])) :=
  by
  rw [P_infty_f]
  cases n
  · simpa only [P_f_0_eq] using comp_id _
  · exact (higher_faces_vanish.on_Γ₀_summand_id K n).comp_P_eq_self
#align algebraic_topology.dold_kan.P_infty_on_Γ₀_splitting_summand_eq_self AlgebraicTopology.DoldKan.pInfty_on_Γ₀_splitting_summand_eq_self

end DoldKan

end AlgebraicTopology

