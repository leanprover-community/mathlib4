/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.DoldKan.SplitSimplicialObject

#align_import algebraic_topology.dold_kan.functor_gamma from "leanprover-community/mathlib"@"32a7e535287f9c73f2e4d2aef306a39190f0b504"

/-!

# Construction of the inverse functor of the Dold-Kan equivalence


In this file, we construct the functor `Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C`
which shall be the inverse functor of the Dold-Kan equivalence in the case of abelian categories,
and more generally pseudoabelian categories.

By definition, when `K` is a chain_complex, `Γ₀.obj K` is a simplicial object which
sends `Δ : SimplexCategoryᵒᵖ` to a certain coproduct indexed by the set
`Splitting.IndexSet Δ` whose elements consists of epimorphisms `e : Δ.unop ⟶ Δ'.unop`
(with `Δ' : SimplexCategoryᵒᵖ`); the summand attached to such an `e` is `K.X Δ'.unop.len`.
By construction, `Γ₀.obj K` is a split simplicial object whose splitting is `Γ₀.splitting K`.

We also construct `Γ₂ : Karoubi (ChainComplex C ℕ) ⥤ Karoubi (SimplicialObject C)`
which shall be an equivalence for any additive category `C`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits SimplexCategory
  SimplicialObject Opposite CategoryTheory.Idempotents Simplicial DoldKan

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category C] [Preadditive C] (K K' : ChainComplex C ℕ) (f : K ⟶ K')
  {Δ Δ' Δ'' : SimplexCategory}

/-- `Isδ₀ i` is a simple condition used to check whether a monomorphism `i` in
`SimplexCategory` identifies to the coface map `δ 0`. -/
@[nolint unusedArguments]
def Isδ₀ {Δ Δ' : SimplexCategory} (i : Δ' ⟶ Δ) [Mono i] : Prop :=
  Δ.len = Δ'.len + 1 ∧ i.toOrderHom 0 ≠ 0
#align algebraic_topology.dold_kan.is_δ₀ AlgebraicTopology.DoldKan.Isδ₀

namespace Isδ₀

theorem iff {j : ℕ} {i : Fin (j + 2)} : Isδ₀ (SimplexCategory.δ i) ↔ i = 0 := by
  constructor
  -- ⊢ Isδ₀ (SimplexCategory.δ i) → i = 0
  · rintro ⟨_, h₂⟩
    -- ⊢ i = 0
    by_contra h
    -- ⊢ False
    exact h₂ (Fin.succAbove_ne_zero_zero h)
    -- 🎉 no goals
  · rintro rfl
    -- ⊢ Isδ₀ (SimplexCategory.δ 0)
    exact ⟨rfl, by dsimp; exact Fin.succ_ne_zero (0 : Fin (j + 1))⟩
    -- 🎉 no goals
#align algebraic_topology.dold_kan.is_δ₀.iff AlgebraicTopology.DoldKan.Isδ₀.iff

theorem eq_δ₀ {n : ℕ} {i : ([n] : SimplexCategory) ⟶ [n + 1]} [Mono i] (hi : Isδ₀ i) :
    i = SimplexCategory.δ 0 := by
  obtain ⟨j, rfl⟩ := SimplexCategory.eq_δ_of_mono i
  -- ⊢ SimplexCategory.δ j = SimplexCategory.δ 0
  rw [iff] at hi
  -- ⊢ SimplexCategory.δ j = SimplexCategory.δ 0
  rw [hi]
  -- 🎉 no goals
#align algebraic_topology.dold_kan.is_δ₀.eq_δ₀ AlgebraicTopology.DoldKan.Isδ₀.eq_δ₀

end Isδ₀

namespace Γ₀

namespace Obj

/-- In the definition of `(Γ₀.obj K).obj Δ` as a direct sum indexed by `A : Splitting.IndexSet Δ`,
the summand `summand K Δ A` is `K.X A.1.len`. -/
def summand (Δ : SimplexCategoryᵒᵖ) (A : Splitting.IndexSet Δ) : C :=
  K.X A.1.unop.len
#align algebraic_topology.dold_kan.Γ₀.obj.summand AlgebraicTopology.DoldKan.Γ₀.Obj.summand

/-- The functor `Γ₀` sends a chain complex `K` to the simplicial object which
sends `Δ` to the direct sum of the objects `summand K Δ A` for all `A : Splitting.IndexSet Δ` -/
def obj₂ (K : ChainComplex C ℕ) (Δ : SimplexCategoryᵒᵖ) [HasFiniteCoproducts C] : C :=
  ∐ fun A : Splitting.IndexSet Δ => summand K Δ A
#align algebraic_topology.dold_kan.Γ₀.obj.obj₂ AlgebraicTopology.DoldKan.Γ₀.Obj.obj₂

namespace Termwise

/-- A monomorphism `i : Δ' ⟶ Δ` induces a morphism `K.X Δ.len ⟶ K.X Δ'.len` which
is the identity if `Δ = Δ'`, the differential on the complex `K` if `i = δ 0`, and
zero otherwise. -/
def mapMono (K : ChainComplex C ℕ) {Δ' Δ : SimplexCategory} (i : Δ' ⟶ Δ) [Mono i] :
    K.X Δ.len ⟶ K.X Δ'.len := by
  by_cases Δ = Δ'
  -- ⊢ HomologicalComplex.X K (len Δ) ⟶ HomologicalComplex.X K (len Δ')
  -- ⊢ HomologicalComplex.X K (len Δ) ⟶ HomologicalComplex.X K (len Δ')
  · exact eqToHom (by congr )
    -- 🎉 no goals
  · by_cases Isδ₀ i
    -- ⊢ HomologicalComplex.X K (len Δ) ⟶ HomologicalComplex.X K (len Δ')
    -- ⊢ HomologicalComplex.X K (len Δ) ⟶ HomologicalComplex.X K (len Δ')
    · exact K.d Δ.len Δ'.len
      -- 🎉 no goals
    · exact 0
      -- 🎉 no goals
#align algebraic_topology.dold_kan.Γ₀.obj.termwise.map_mono AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono

variable (Δ)

theorem mapMono_id : mapMono K (𝟙 Δ) = 𝟙 _ := by
  unfold mapMono
  -- ⊢ (if h : Δ = Δ then eqToHom (_ : HomologicalComplex.X K (len Δ) = Homological …
  simp only [eq_self_iff_true, eqToHom_refl, dite_eq_ite, if_true]
  -- 🎉 no goals
#align algebraic_topology.dold_kan.Γ₀.obj.termwise.map_mono_id AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_id

variable {Δ}

theorem mapMono_δ₀' (i : Δ' ⟶ Δ) [Mono i] (hi : Isδ₀ i) : mapMono K i = K.d Δ.len Δ'.len := by
  unfold mapMono
  -- ⊢ (if h : Δ = Δ' then eqToHom (_ : HomologicalComplex.X K (len Δ) = Homologica …
  suffices Δ ≠ Δ' by
    simp only [dif_neg this, dif_pos hi]
  rintro rfl
  -- ⊢ False
  simpa only [self_eq_add_right, Nat.one_ne_zero] using hi.1
  -- 🎉 no goals
#align algebraic_topology.dold_kan.Γ₀.obj.termwise.map_mono_δ₀' AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_δ₀'

@[simp]
theorem mapMono_δ₀ {n : ℕ} : mapMono K (δ (0 : Fin (n + 2))) = K.d (n + 1) n :=
  mapMono_δ₀' K _ (by rw [Isδ₀.iff])
                      -- 🎉 no goals
#align algebraic_topology.dold_kan.Γ₀.obj.termwise.map_mono_δ₀ AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_δ₀

theorem mapMono_eq_zero (i : Δ' ⟶ Δ) [Mono i] (h₁ : Δ ≠ Δ') (h₂ : ¬Isδ₀ i) : mapMono K i = 0 := by
  unfold mapMono
  -- ⊢ (if h : Δ = Δ' then eqToHom (_ : HomologicalComplex.X K (len Δ) = Homologica …
  rw [Ne.def] at h₁
  -- ⊢ (if h : Δ = Δ' then eqToHom (_ : HomologicalComplex.X K (len Δ) = Homologica …
  split_ifs
  -- ⊢ 0 = 0
  rfl
  -- 🎉 no goals
#align algebraic_topology.dold_kan.Γ₀.obj.termwise.map_mono_eq_zero AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_eq_zero

variable {K K'}

@[reassoc (attr := simp)]
theorem mapMono_naturality (i : Δ ⟶ Δ') [Mono i] :
  mapMono K i ≫ f.f Δ.len = f.f Δ'.len ≫ mapMono K' i := by
  unfold mapMono
  -- ⊢ (if h : Δ' = Δ then eqToHom (_ : HomologicalComplex.X K (len Δ') = Homologic …
  split_ifs with h
  · subst h
    -- ⊢ eqToHom (_ : HomologicalComplex.X K (len Δ') = HomologicalComplex.X K (len Δ …
    simp only [id_comp, eqToHom_refl, comp_id]
    -- 🎉 no goals
  · rw [HomologicalComplex.Hom.comm]
    -- 🎉 no goals
  · rw [zero_comp, comp_zero]
    -- 🎉 no goals
#align algebraic_topology.dold_kan.Γ₀.obj.termwise.map_mono_naturality AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_naturality

variable (K)

@[reassoc (attr := simp)]
theorem mapMono_comp (i' : Δ'' ⟶ Δ') (i : Δ' ⟶ Δ) [Mono i'] [Mono i] :
  mapMono K i ≫ mapMono K i' = mapMono K (i' ≫ i) := by
  -- case where i : Δ' ⟶ Δ is the identity
  by_cases h₁ : Δ = Δ'
  -- ⊢ mapMono K i ≫ mapMono K i' = mapMono K (i' ≫ i)
  · subst h₁
    -- ⊢ mapMono K i ≫ mapMono K i' = mapMono K (i' ≫ i)
    simp only [SimplexCategory.eq_id_of_mono i, comp_id, id_comp, mapMono_id K, eqToHom_refl]
    -- 🎉 no goals
  -- case where i' : Δ'' ⟶ Δ' is the identity
  by_cases h₂ : Δ' = Δ''
  -- ⊢ mapMono K i ≫ mapMono K i' = mapMono K (i' ≫ i)
  · subst h₂
    -- ⊢ mapMono K i ≫ mapMono K i' = mapMono K (i' ≫ i)
    simp only [SimplexCategory.eq_id_of_mono i', comp_id, id_comp, mapMono_id K, eqToHom_refl]
    -- 🎉 no goals
  -- then the RHS is always zero
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt (len_lt_of_mono i h₁)
  -- ⊢ mapMono K i ≫ mapMono K i' = mapMono K (i' ≫ i)
  obtain ⟨k', hk'⟩ := Nat.exists_eq_add_of_lt (len_lt_of_mono i' h₂)
  -- ⊢ mapMono K i ≫ mapMono K i' = mapMono K (i' ≫ i)
  have eq : Δ.len = Δ''.len + (k + k' + 2) := by linarith
  -- ⊢ mapMono K i ≫ mapMono K i' = mapMono K (i' ≫ i)
  rw [mapMono_eq_zero K (i' ≫ i) _ _]; rotate_left
  · by_contra h
    -- ⊢ False
    simp only [self_eq_add_right, h, add_eq_zero_iff, and_false] at eq
    -- 🎉 no goals
  · by_contra h
    -- ⊢ False
    simp only [h.1, add_right_inj] at eq
    -- ⊢ False
    linarith
    -- 🎉 no goals
  -- in all cases, the LHS is also zero, either by definition, or because d ≫ d = 0
  by_cases h₃ : Isδ₀ i
  -- ⊢ mapMono K i ≫ mapMono K i' = 0
  · by_cases h₄ : Isδ₀ i'
    -- ⊢ mapMono K i ≫ mapMono K i' = 0
    · rw [mapMono_δ₀' K i h₃, mapMono_δ₀' K i' h₄, HomologicalComplex.d_comp_d]
      -- 🎉 no goals
    · simp only [mapMono_eq_zero K i' h₂ h₄, comp_zero]
      -- 🎉 no goals
  · simp only [mapMono_eq_zero K i h₁ h₃, zero_comp]
    -- 🎉 no goals
#align algebraic_topology.dold_kan.Γ₀.obj.termwise.map_mono_comp AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_comp

end Termwise

variable [HasFiniteCoproducts C]

/-- The simplicial morphism on the simplicial object `Γ₀.obj K` induced by
a morphism `Δ' → Δ` in `SimplexCategory` is defined on each summand
associated to an `A : Splitting.IndexSet Δ` in terms of the epi-mono factorisation
of `θ ≫ A.e`. -/
def map (K : ChainComplex C ℕ) {Δ' Δ : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') : obj₂ K Δ ⟶ obj₂ K Δ' :=
  Sigma.desc fun A =>
    Termwise.mapMono K (image.ι (θ.unop ≫ A.e)) ≫ Sigma.ι (summand K Δ') (A.pull θ)
#align algebraic_topology.dold_kan.Γ₀.obj.map AlgebraicTopology.DoldKan.Γ₀.Obj.map

@[reassoc]
theorem map_on_summand₀ {Δ Δ' : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) {θ : Δ ⟶ Δ'}
    {Δ'' : SimplexCategory} {e : Δ'.unop ⟶ Δ''} {i : Δ'' ⟶ A.1.unop} [Epi e] [Mono i]
    (fac : e ≫ i = θ.unop ≫ A.e) :
    Sigma.ι (summand K Δ) A ≫ map K θ =
      Termwise.mapMono K i ≫ Sigma.ι (summand K Δ') (Splitting.IndexSet.mk e) := by
  simp only [map, colimit.ι_desc, Cofan.mk_ι_app]
  -- ⊢ Termwise.mapMono K (image.ι (θ.unop ≫ Splitting.IndexSet.e A)) ≫ Sigma.ι (su …
  have h := SimplexCategory.image_eq fac
  -- ⊢ Termwise.mapMono K (image.ι (θ.unop ≫ Splitting.IndexSet.e A)) ≫ Sigma.ι (su …
  subst h
  -- ⊢ Termwise.mapMono K (image.ι (θ.unop ≫ Splitting.IndexSet.e A)) ≫ Sigma.ι (su …
  congr
  -- ⊢ image.ι (θ.unop ≫ Splitting.IndexSet.e A) = i
  · exact SimplexCategory.image_ι_eq fac
    -- 🎉 no goals
  · dsimp only [SimplicialObject.Splitting.IndexSet.pull]
    -- ⊢ Splitting.IndexSet.mk (factorThruImage (θ.unop ≫ Splitting.IndexSet.e A)) =  …
    congr
    -- ⊢ factorThruImage (θ.unop ≫ Splitting.IndexSet.e A) = e
    exact SimplexCategory.factorThruImage_eq fac
    -- 🎉 no goals
#align algebraic_topology.dold_kan.Γ₀.obj.map_on_summand₀ AlgebraicTopology.DoldKan.Γ₀.Obj.map_on_summand₀

@[reassoc]
theorem map_on_summand₀' {Δ Δ' : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) (θ : Δ ⟶ Δ') :
    Sigma.ι (summand K Δ) A ≫ map K θ =
      Termwise.mapMono K (image.ι (θ.unop ≫ A.e)) ≫ Sigma.ι (summand K _) (A.pull θ) :=
  map_on_summand₀ K A (A.fac_pull θ)
#align algebraic_topology.dold_kan.Γ₀.obj.map_on_summand₀' AlgebraicTopology.DoldKan.Γ₀.Obj.map_on_summand₀'

end Obj

variable [HasFiniteCoproducts C]

/-- The functor `Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C`, on objects. -/
@[simps]
def obj (K : ChainComplex C ℕ) : SimplicialObject C where
  obj Δ := Obj.obj₂ K Δ
  map θ := Obj.map K θ
  map_id Δ := colimit.hom_ext (fun ⟨A⟩ => by
    dsimp
    -- ⊢ colimit.ι (Discrete.functor fun A => Obj.summand K Δ A) { as := A } ≫ Obj.ma …
    have fac : A.e ≫ 𝟙 A.1.unop = (𝟙 Δ).unop ≫ A.e := by rw [unop_id, comp_id, id_comp]
    -- ⊢ colimit.ι (Discrete.functor fun A => Obj.summand K Δ A) { as := A } ≫ Obj.ma …
    erw [Obj.map_on_summand₀ K A fac, Obj.Termwise.mapMono_id, id_comp, comp_id]
    -- ⊢ Sigma.ι (Obj.summand K Δ) (Splitting.IndexSet.mk (Splitting.IndexSet.e A)) = …
    rfl)
    -- 🎉 no goals
  map_comp {Δ'' Δ' Δ} θ' θ := colimit.hom_ext (fun ⟨A⟩ => by
    have fac : θ.unop ≫ θ'.unop ≫ A.e = (θ' ≫ θ).unop ≫ A.e := by rw [unop_comp, assoc]
    -- ⊢ colimit.ι (Discrete.functor fun A => Obj.summand K Δ'' A) { as := A } ≫ { ob …
    rw [← image.fac (θ'.unop ≫ A.e), ← assoc, ←
      image.fac (θ.unop ≫ factorThruImage (θ'.unop ≫ A.e)), assoc] at fac
    simp only [Obj.map_on_summand₀'_assoc K A θ', Obj.map_on_summand₀' K _ θ,
      Obj.Termwise.mapMono_comp_assoc, Obj.map_on_summand₀ K A fac]
    rfl)
    -- 🎉 no goals
#align algebraic_topology.dold_kan.Γ₀.obj AlgebraicTopology.DoldKan.Γ₀.obj


theorem splitting_map_eq_id (Δ : SimplexCategoryᵒᵖ) :
    SimplicialObject.Splitting.map (Γ₀.obj K)
        (fun n : ℕ => Sigma.ι (Γ₀.Obj.summand K (op [n])) (Splitting.IndexSet.id (op [n]))) Δ =
      𝟙 _ := colimit.hom_ext (fun ⟨A⟩ => by
  induction' Δ using Opposite.rec' with Δ
  -- ⊢ colimit.ι (Discrete.functor (Splitting.summand (fun n => Obj.summand K (op [ …
  induction' Δ using SimplexCategory.rec with n
  -- ⊢ colimit.ι (Discrete.functor (Splitting.summand (fun n => Obj.summand K (op [ …
  dsimp [Splitting.map]
  -- ⊢ (colimit.ι (Discrete.functor fun A => Obj.summand K A.fst (Splitting.IndexSe …
  simp only [colimit.ι_desc, Cofan.mk_ι_app, Γ₀.obj_map]
  -- ⊢ Sigma.ι (Obj.summand K A.fst) (Splitting.IndexSet.id A.fst) ≫ Obj.map K (Spl …
  erw [Γ₀.Obj.map_on_summand₀ K (SimplicialObject.Splitting.IndexSet.id A.1)
      (show A.e ≫ 𝟙 _ = A.e.op.unop ≫ 𝟙 _ by rfl),
    Γ₀.Obj.Termwise.mapMono_id, A.ext', id_comp, comp_id]
  rfl)
  -- 🎉 no goals
#align algebraic_topology.dold_kan.Γ₀.splitting_map_eq_id AlgebraicTopology.DoldKan.Γ₀.splitting_map_eq_id

/-- By construction, the simplicial `Γ₀.obj K` is equipped with a splitting. -/
def splitting (K : ChainComplex C ℕ) : SimplicialObject.Splitting (Γ₀.obj K) where
  N n := K.X n
  ι n := Sigma.ι (Γ₀.Obj.summand K (op [n])) (Splitting.IndexSet.id (op [n]))
  map_isIso Δ := by
    rw [Γ₀.splitting_map_eq_id]
    -- ⊢ IsIso (𝟙 (Splitting.coprod (fun n => Obj.summand K (op [n]) (Splitting.Index …
    apply IsIso.id
    -- 🎉 no goals
#align algebraic_topology.dold_kan.Γ₀.splitting AlgebraicTopology.DoldKan.Γ₀.splitting

@[simp 1100]
theorem splitting_iso_hom_eq_id (Δ : SimplexCategoryᵒᵖ) : ((splitting K).iso Δ).hom = 𝟙 _ :=
  splitting_map_eq_id K Δ
#align algebraic_topology.dold_kan.Γ₀.splitting_iso_hom_eq_id AlgebraicTopology.DoldKan.Γ₀.splitting_iso_hom_eq_id

@[reassoc]
theorem Obj.map_on_summand {Δ Δ' : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) (θ : Δ ⟶ Δ')
    {Δ'' : SimplexCategory} {e : Δ'.unop ⟶ Δ''} {i : Δ'' ⟶ A.1.unop} [Epi e] [Mono i]
    (fac : e ≫ i = θ.unop ≫ A.e) :
    (Γ₀.splitting K).ιSummand A ≫ (Γ₀.obj K).map θ =
      Γ₀.Obj.Termwise.mapMono K i ≫ (Γ₀.splitting K).ιSummand (Splitting.IndexSet.mk e) := by
  dsimp only [SimplicialObject.Splitting.ιSummand, SimplicialObject.Splitting.ιCoprod]
  -- ⊢ (Sigma.ι (Splitting.summand (splitting K).N Δ) A ≫ (Splitting.iso (splitting …
  simp only [assoc, Γ₀.splitting_iso_hom_eq_id, id_comp, comp_id]
  -- ⊢ Sigma.ι (Splitting.summand (splitting K).N Δ) A ≫ (obj K).map θ = Termwise.m …
  exact Γ₀.Obj.map_on_summand₀ K A fac
  -- 🎉 no goals
#align algebraic_topology.dold_kan.Γ₀.obj.map_on_summand AlgebraicTopology.DoldKan.Γ₀.Obj.map_on_summand

@[reassoc]
theorem Obj.map_on_summand' {Δ Δ' : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) (θ : Δ ⟶ Δ') :
    (splitting K).ιSummand A ≫ (obj K).map θ =
      Obj.Termwise.mapMono K (image.ι (θ.unop ≫ A.e)) ≫ (splitting K).ιSummand (A.pull θ) := by
  apply Obj.map_on_summand
  -- ⊢ factorThruImage (θ.unop ≫ Splitting.IndexSet.e A) ≫ image.ι (θ.unop ≫ Splitt …
  apply image.fac
  -- 🎉 no goals
#align algebraic_topology.dold_kan.Γ₀.obj.map_on_summand' AlgebraicTopology.DoldKan.Γ₀.Obj.map_on_summand'

@[reassoc]
theorem Obj.mapMono_on_summand_id {Δ Δ' : SimplexCategory} (i : Δ' ⟶ Δ) [Mono i] :
    (splitting K).ιSummand (Splitting.IndexSet.id (op Δ)) ≫ (obj K).map i.op =
      Obj.Termwise.mapMono K i ≫ (splitting K).ιSummand (Splitting.IndexSet.id (op Δ')) :=
  Obj.map_on_summand K (Splitting.IndexSet.id (op Δ)) i.op (rfl : 𝟙 _ ≫ i = i ≫ 𝟙 _)
#align algebraic_topology.dold_kan.Γ₀.obj.map_mono_on_summand_id AlgebraicTopology.DoldKan.Γ₀.Obj.mapMono_on_summand_id

@[reassoc]
theorem Obj.map_epi_on_summand_id {Δ Δ' : SimplexCategory} (e : Δ' ⟶ Δ) [Epi e] :
    (Γ₀.splitting K).ιSummand (Splitting.IndexSet.id (op Δ)) ≫ (Γ₀.obj K).map e.op =
      (Γ₀.splitting K).ιSummand (Splitting.IndexSet.mk e) := by
  simpa only [Γ₀.Obj.map_on_summand K (Splitting.IndexSet.id (op Δ)) e.op
      (rfl : e ≫ 𝟙 Δ = e ≫ 𝟙 Δ),
    Γ₀.Obj.Termwise.mapMono_id] using id_comp _
#align algebraic_topology.dold_kan.Γ₀.obj.map_epi_on_summand_id AlgebraicTopology.DoldKan.Γ₀.Obj.map_epi_on_summand_id

/-- The functor `Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C`, on morphisms. -/
@[simps]
def map {K K' : ChainComplex C ℕ} (f : K ⟶ K') : obj K ⟶ obj K' where
  app Δ := (Γ₀.splitting K).desc Δ fun A => f.f A.1.unop.len ≫ (Γ₀.splitting K').ιSummand A
  naturality {Δ' Δ} θ := by
    apply (Γ₀.splitting K).hom_ext'
    -- ⊢ ∀ (A : Splitting.IndexSet Δ'), Splitting.ιSummand (splitting K) A ≫ (obj K). …
    intro A
    -- ⊢ Splitting.ιSummand (splitting K) A ≫ (obj K).map θ ≫ (fun Δ => Splitting.des …
    simp only [(splitting K).ι_desc_assoc, Obj.map_on_summand'_assoc K _ θ, (splitting K).ι_desc,
      assoc, Obj.map_on_summand' K' _ θ]
    apply Obj.Termwise.mapMono_naturality_assoc
    -- 🎉 no goals
#align algebraic_topology.dold_kan.Γ₀.map AlgebraicTopology.DoldKan.Γ₀.map

end Γ₀

variable [HasFiniteCoproducts C]

/-- The functor `Γ₀' : ChainComplex C ℕ ⥤ SimplicialObject.Split C`
that induces `Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C`, which
shall be the inverse functor of the Dold-Kan equivalence for
abelian or pseudo-abelian categories. -/
@[simps]
def Γ₀' : ChainComplex C ℕ ⥤ SimplicialObject.Split C where
  obj K := SimplicialObject.Split.mk' (Γ₀.splitting K)
  map {K K'} f :=
    { F := Γ₀.map f
      f := f.f
      comm := fun n => by
        dsimp
        -- ⊢ (Splitting.ι (Γ₀.splitting K) n ≫ Splitting.desc (Γ₀.splitting K) (op [n]) f …
        simp only [← Splitting.ιSummand_id, (Γ₀.splitting K).ι_desc]
        -- ⊢ HomologicalComplex.Hom.f f (len (Splitting.IndexSet.id (op [n])).fst.unop) ≫ …
        rfl }
        -- 🎉 no goals
#align algebraic_topology.dold_kan.Γ₀' AlgebraicTopology.DoldKan.Γ₀'

/-- The functor `Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C`, which is
the inverse functor of the Dold-Kan equivalence when `C` is an abelian
category, or more generally a pseudoabelian category. -/
@[simps!]
def Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C :=
  Γ₀' ⋙ Split.forget _
#align algebraic_topology.dold_kan.Γ₀ AlgebraicTopology.DoldKan.Γ₀

/-- The extension of `Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C`
on the idempotent completions. It shall be an equivalence of categories
for any additive category `C`. -/
@[simps!]
def Γ₂ : Karoubi (ChainComplex C ℕ) ⥤ Karoubi (SimplicialObject C) :=
  (CategoryTheory.Idempotents.functorExtension₂ _ _).obj Γ₀
#align algebraic_topology.dold_kan.Γ₂ AlgebraicTopology.DoldKan.Γ₂

theorem HigherFacesVanish.on_Γ₀_summand_id (K : ChainComplex C ℕ) (n : ℕ) :
    HigherFacesVanish (n + 1) ((Γ₀.splitting K).ιSummand (Splitting.IndexSet.id (op [n + 1]))) := by
  intro j _
  -- ⊢ Splitting.ιSummand (Γ₀.splitting K) (Splitting.IndexSet.id (op [n + 1])) ≫ S …
  have eq := Γ₀.Obj.mapMono_on_summand_id K (SimplexCategory.δ j.succ)
  -- ⊢ Splitting.ιSummand (Γ₀.splitting K) (Splitting.IndexSet.id (op [n + 1])) ≫ S …
  rw [Γ₀.Obj.Termwise.mapMono_eq_zero K, zero_comp] at eq; rotate_left
  · intro h
    -- ⊢ False
    exact (Nat.succ_ne_self n) (congr_arg SimplexCategory.len h)
    -- 🎉 no goals
  · exact fun h => Fin.succ_ne_zero j (by simpa only [Isδ₀.iff] using h)
    -- 🎉 no goals
  exact eq
  -- 🎉 no goals
#align algebraic_topology.dold_kan.higher_faces_vanish.on_Γ₀_summand_id AlgebraicTopology.DoldKan.HigherFacesVanish.on_Γ₀_summand_id

@[reassoc (attr := simp)]
theorem PInfty_on_Γ₀_splitting_summand_eq_self (K : ChainComplex C ℕ) {n : ℕ} :
    (Γ₀.splitting K).ιSummand (Splitting.IndexSet.id (op [n])) ≫ (PInfty : K[Γ₀.obj K] ⟶ _).f n =
      (Γ₀.splitting K).ιSummand (Splitting.IndexSet.id (op [n])) := by
  rw [PInfty_f]
  -- ⊢ Splitting.ιSummand (Γ₀.splitting K) (Splitting.IndexSet.id (op [n])) ≫ Homol …
  rcases n with _|n
  -- ⊢ Splitting.ιSummand (Γ₀.splitting K) (Splitting.IndexSet.id (op [Nat.zero]))  …
  · simpa only [P_f_0_eq] using comp_id _
    -- 🎉 no goals
  · exact (HigherFacesVanish.on_Γ₀_summand_id K n).comp_P_eq_self
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.P_infty_on_Γ₀_splitting_summand_eq_self AlgebraicTopology.DoldKan.PInfty_on_Γ₀_splitting_summand_eq_self

end DoldKan

end AlgebraicTopology
