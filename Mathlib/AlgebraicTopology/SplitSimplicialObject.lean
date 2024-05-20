/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialObject
import Mathlib.CategoryTheory.Limits.Shapes.Products

#align_import algebraic_topology.split_simplicial_object from "leanprover-community/mathlib"@"dd1f8496baa505636a82748e6b652165ea888733"

/-!

# Split simplicial objects

In this file, we introduce the notion of split simplicial object.
If `C` is a category that has finite coproducts, a splitting
`s : Splitting X` of a simplicial object `X` in `C` consists
of the datum of a sequence of objects `s.N : ℕ → C` (which
we shall refer to as "nondegenerate simplices") and a
sequence of morphisms `s.ι n : s.N n → X _[n]` that have
the property that a certain canonical map identifies `X _[n]`
with the coproduct of objects `s.N i` indexed by all possible
epimorphisms `[n] ⟶ [i]` in `SimplexCategory`. (We do not
assume that the morphisms `s.ι n` are monomorphisms: in the
most common categories, this would be a consequence of the
axioms.)

Simplicial objects equipped with a splitting form a category
`SimplicialObject.Split C`.

## References
* [Stacks: Splitting simplicial objects] https://stacks.math.columbia.edu/tag/017O

-/


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite SimplexCategory

open Simplicial

universe u

variable {C : Type*} [Category C]

namespace SimplicialObject

namespace Splitting

/-- The index set which appears in the definition of split simplicial objects. -/
def IndexSet (Δ : SimplexCategoryᵒᵖ) :=
  ΣΔ' : SimplexCategoryᵒᵖ, { α : Δ.unop ⟶ Δ'.unop // Epi α }
#align simplicial_object.splitting.index_set SimplicialObject.Splitting.IndexSet

namespace IndexSet

/-- The element in `Splitting.IndexSet Δ` attached to an epimorphism `f : Δ ⟶ Δ'`. -/
@[simps]
def mk {Δ Δ' : SimplexCategory} (f : Δ ⟶ Δ') [Epi f] : IndexSet (op Δ) :=
  ⟨op Δ', f, inferInstance⟩
#align simplicial_object.splitting.index_set.mk SimplicialObject.Splitting.IndexSet.mk

variable {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ)

/-- The epimorphism in `SimplexCategory` associated to `A : Splitting.IndexSet Δ` -/
def e :=
  A.2.1
#align simplicial_object.splitting.index_set.e SimplicialObject.Splitting.IndexSet.e

instance : Epi A.e :=
  A.2.2

theorem ext' : A = ⟨A.1, ⟨A.e, A.2.2⟩⟩ := rfl
#align simplicial_object.splitting.index_set.ext' SimplicialObject.Splitting.IndexSet.ext'

theorem ext (A₁ A₂ : IndexSet Δ) (h₁ : A₁.1 = A₂.1) (h₂ : A₁.e ≫ eqToHom (by rw [h₁]) = A₂.e) :
    A₁ = A₂ := by
  rcases A₁ with ⟨Δ₁, ⟨α₁, hα₁⟩⟩
  rcases A₂ with ⟨Δ₂, ⟨α₂, hα₂⟩⟩
  simp only at h₁
  subst h₁
  simp only [eqToHom_refl, comp_id, IndexSet.e] at h₂
  simp only [h₂]
#align simplicial_object.splitting.index_set.ext SimplicialObject.Splitting.IndexSet.ext

instance : Fintype (IndexSet Δ) :=
  Fintype.ofInjective
    (fun A =>
      ⟨⟨A.1.unop.len, Nat.lt_succ_iff.mpr (len_le_of_epi (inferInstance : Epi A.e))⟩,
        A.e.toOrderHom⟩ :
      IndexSet Δ → Sigma fun k : Fin (Δ.unop.len + 1) => Fin (Δ.unop.len + 1) → Fin (k + 1))
    (by
      rintro ⟨Δ₁, α₁⟩ ⟨Δ₂, α₂⟩ h₁
      induction' Δ₁ using Opposite.rec with Δ₁
      induction' Δ₂ using Opposite.rec with Δ₂
      simp only [unop_op, Sigma.mk.inj_iff, Fin.mk.injEq] at h₁
      have h₂ : Δ₁ = Δ₂ := by
        ext1
        simpa only [Fin.mk_eq_mk] using h₁.1
      subst h₂
      refine' ext _ _ rfl _
      ext : 2
      exact eq_of_heq h₁.2)

variable (Δ)

/-- The distinguished element in `Splitting.IndexSet Δ` which corresponds to the
identity of `Δ`. -/
@[simps]
def id : IndexSet Δ :=
  ⟨Δ, ⟨𝟙 _, by infer_instance⟩⟩
#align simplicial_object.splitting.index_set.id SimplicialObject.Splitting.IndexSet.id

instance : Inhabited (IndexSet Δ) :=
  ⟨id Δ⟩

variable {Δ}

/-- The condition that an element `Splitting.IndexSet Δ` is the distinguished
element `Splitting.IndexSet.Id Δ`. -/
@[simp]
def EqId : Prop :=
  A = id _
#align simplicial_object.splitting.index_set.eq_id SimplicialObject.Splitting.IndexSet.EqId

theorem eqId_iff_eq : A.EqId ↔ A.1 = Δ := by
  constructor
  · intro h
    dsimp at h
    rw [h]
    rfl
  · intro h
    rcases A with ⟨_, ⟨f, hf⟩⟩
    simp only at h
    subst h
    refine' ext _ _ rfl _
    haveI := hf
    simp only [eqToHom_refl, comp_id]
    exact eq_id_of_epi f
#align simplicial_object.splitting.index_set.eq_id_iff_eq SimplicialObject.Splitting.IndexSet.eqId_iff_eq

theorem eqId_iff_len_eq : A.EqId ↔ A.1.unop.len = Δ.unop.len := by
  rw [eqId_iff_eq]
  constructor
  · intro h
    rw [h]
  · intro h
    rw [← unop_inj_iff]
    ext
    exact h
#align simplicial_object.splitting.index_set.eq_id_iff_len_eq SimplicialObject.Splitting.IndexSet.eqId_iff_len_eq

theorem eqId_iff_len_le : A.EqId ↔ Δ.unop.len ≤ A.1.unop.len := by
  rw [eqId_iff_len_eq]
  constructor
  · intro h
    rw [h]
  · exact le_antisymm (len_le_of_epi (inferInstance : Epi A.e))
#align simplicial_object.splitting.index_set.eq_id_iff_len_le SimplicialObject.Splitting.IndexSet.eqId_iff_len_le

theorem eqId_iff_mono : A.EqId ↔ Mono A.e := by
  constructor
  · intro h
    dsimp at h
    subst h
    dsimp only [id, e]
    infer_instance
  · intro h
    rw [eqId_iff_len_le]
    exact len_le_of_mono h
#align simplicial_object.splitting.index_set.eq_id_iff_mono SimplicialObject.Splitting.IndexSet.eqId_iff_mono

/-- Given `A : IndexSet Δ₁`, if `p.unop : unop Δ₂ ⟶ unop Δ₁` is an epi, this
is the obvious element in `A : IndexSet Δ₂` associated to the composition
of epimorphisms `p.unop ≫ A.e`. -/
@[simps]
def epiComp {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (A : IndexSet Δ₁) (p : Δ₁ ⟶ Δ₂) [Epi p.unop] :
    IndexSet Δ₂ :=
  ⟨A.1, ⟨p.unop ≫ A.e, epi_comp _ _⟩⟩
#align simplicial_object.splitting.index_set.epi_comp SimplicialObject.Splitting.IndexSet.epiComp


variable {Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ')

/-- When `A : IndexSet Δ` and `θ : Δ → Δ'` is a morphism in `SimplexCategoryᵒᵖ`,
an element in `IndexSet Δ'` can be defined by using the epi-mono factorisation
of `θ.unop ≫ A.e`. -/
def pull : IndexSet Δ' :=
  mk (factorThruImage (θ.unop ≫ A.e))
#align simplicial_object.splitting.index_set.pull SimplicialObject.Splitting.IndexSet.pull

@[reassoc]
theorem fac_pull : (A.pull θ).e ≫ image.ι (θ.unop ≫ A.e) = θ.unop ≫ A.e :=
  image.fac _
#align simplicial_object.splitting.index_set.fac_pull SimplicialObject.Splitting.IndexSet.fac_pull

end IndexSet

variable (N : ℕ → C) (Δ : SimplexCategoryᵒᵖ) (X : SimplicialObject C) (φ : ∀ n, N n ⟶ X _[n])

/-- Given a sequences of objects `N : ℕ → C` in a category `C`, this is
a family of objects indexed by the elements `A : Splitting.IndexSet Δ`.
The `Δ`-simplices of a split simplicial objects shall identify to the
coproduct of objects in such a family. -/
@[simp, nolint unusedArguments]
def summand (A : IndexSet Δ) : C :=
  N A.1.unop.len
#align simplicial_object.splitting.summand SimplicialObject.Splitting.summand

/-- The cofan for `summand N Δ` induced by morphisms `N n ⟶ X_ [n]` for all `n : ℕ`. -/
def cofan' (Δ : SimplexCategoryᵒᵖ) : Cofan (summand N Δ) :=
  Cofan.mk (X.obj Δ) (fun A => φ A.1.unop.len ≫ X.map A.e.op)

end Splitting

--porting note (#5171): removed @[nolint has_nonempty_instance]
/-- A splitting of a simplicial object `X` consists of the datum of a sequence
of objects `N`, a sequence of morphisms `ι : N n ⟶ X _[n]` such that
for all `Δ : SimplexCategoryᵒᵖ`, the canonical map `Splitting.map X ι Δ`
is an isomorphism. -/
structure Splitting (X : SimplicialObject C) where
  /-- The "nondegenerate simplices" `N n` for all `n : ℕ`. -/
  N : ℕ → C
  /-- The "inclusion" `N n ⟶ X _[n]` for all `n : ℕ`. -/
  ι : ∀ n, N n ⟶ X _[n]
  /-- For each `Δ`, `X.obj Δ` identifies to the coproduct of the objects `N A.1.unop.len`
  for all `A : IndexSet Δ`.  -/
  isColimit' : ∀ Δ : SimplexCategoryᵒᵖ, IsColimit (Splitting.cofan' N X ι Δ)
#align simplicial_object.splitting SimplicialObject.Splitting

namespace Splitting

variable {X Y : SimplicialObject C} (s : Splitting X)

/-- The cofan for `summand s.N Δ` induced by a splitting of a simplicial object.  -/
def cofan (Δ : SimplexCategoryᵒᵖ) : Cofan (summand s.N Δ) :=
  Cofan.mk (X.obj Δ) (fun A => s.ι A.1.unop.len ≫ X.map A.e.op)

/-- The cofan `s.cofan Δ` is colimit. -/
def isColimit (Δ : SimplexCategoryᵒᵖ) : IsColimit (s.cofan Δ) := s.isColimit' Δ

@[reassoc]
theorem cofan_inj_eq {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) :
    (s.cofan Δ).inj  A = s.ι A.1.unop.len ≫ X.map A.e.op := rfl
#align simplicial_object.splitting.ι_summand_eq SimplicialObject.Splitting.cofan_inj_eq

theorem cofan_inj_id (n : ℕ) : (s.cofan _).inj (IndexSet.id (op [n])) = s.ι n := by
  erw [cofan_inj_eq, X.map_id, comp_id]
  rfl
#align simplicial_object.splitting.ι_summand_id SimplicialObject.Splitting.cofan_inj_id

/-- As it is stated in `Splitting.hom_ext`, a morphism `f : X ⟶ Y` from a split
simplicial object to any simplicial object is determined by its restrictions
`s.φ f n : s.N n ⟶ Y _[n]` to the distinguished summands in each degree `n`. -/
@[simp]
def φ (f : X ⟶ Y) (n : ℕ) : s.N n ⟶ Y _[n] :=
  s.ι n ≫ f.app (op [n])
#align simplicial_object.splitting.φ SimplicialObject.Splitting.φ

@[reassoc (attr := simp)]
theorem cofan_inj_comp_app (f : X ⟶ Y) {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) :
    (s.cofan Δ).inj A ≫ f.app Δ = s.φ f A.1.unop.len ≫ Y.map A.e.op := by
  simp only [cofan_inj_eq_assoc, φ, assoc]
  erw [NatTrans.naturality]
#align simplicial_object.splitting.ι_summand_comp_app SimplicialObject.Splitting.cofan_inj_comp_app

theorem hom_ext' {Z : C} {Δ : SimplexCategoryᵒᵖ} (f g : X.obj Δ ⟶ Z)
    (h : ∀ A : IndexSet Δ, (s.cofan Δ).inj A ≫ f = (s.cofan Δ).inj A ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext (s.isColimit Δ) _ _ h
#align simplicial_object.splitting.hom_ext' SimplicialObject.Splitting.hom_ext'

theorem hom_ext (f g : X ⟶ Y) (h : ∀ n : ℕ, s.φ f n = s.φ g n) : f = g := by
  ext Δ
  apply s.hom_ext'
  intro A
  induction' Δ using Opposite.rec with Δ
  induction' Δ using SimplexCategory.rec with n
  dsimp
  simp only [s.cofan_inj_comp_app, h]
#align simplicial_object.splitting.hom_ext SimplicialObject.Splitting.hom_ext

/-- The map `X.obj Δ ⟶ Z` obtained by providing a family of morphisms on all the
terms of decomposition given by a splitting `s : Splitting X`  -/
def desc {Z : C} (Δ : SimplexCategoryᵒᵖ) (F : ∀ A : IndexSet Δ, s.N A.1.unop.len ⟶ Z) :
    X.obj Δ ⟶ Z :=
  Cofan.IsColimit.desc (s.isColimit Δ) F
#align simplicial_object.splitting.desc SimplicialObject.Splitting.desc

@[reassoc (attr := simp)]
theorem ι_desc {Z : C} (Δ : SimplexCategoryᵒᵖ) (F : ∀ A : IndexSet Δ, s.N A.1.unop.len ⟶ Z)
    (A : IndexSet Δ) : (s.cofan Δ).inj A ≫ s.desc Δ F = F A := by
  apply Cofan.IsColimit.fac
#align simplicial_object.splitting.ι_desc SimplicialObject.Splitting.ι_desc

/-- A simplicial object that is isomorphic to a split simplicial object is split. -/
@[simps]
def ofIso (e : X ≅ Y) : Splitting Y where
  N := s.N
  ι n := s.ι n ≫ e.hom.app (op [n])
  isColimit' Δ := IsColimit.ofIsoColimit (s.isColimit Δ ) (Cofan.ext (e.app Δ)
    (fun A => by simp [cofan, cofan']))
#align simplicial_object.splitting.of_iso SimplicialObject.Splitting.ofIso

@[reassoc]
theorem cofan_inj_epi_naturality {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (A : IndexSet Δ₁) (p : Δ₁ ⟶ Δ₂)
    [Epi p.unop] : (s.cofan Δ₁).inj A ≫ X.map p = (s.cofan Δ₂).inj (A.epiComp p) := by
  dsimp [cofan]
  rw [assoc, ← X.map_comp]
  rfl
#align simplicial_object.splitting.ι_summand_epi_naturality SimplicialObject.Splitting.cofan_inj_epi_naturality

end Splitting

variable (C)

-- porting note (#5171): removed @[nolint has_nonempty_instance]
/-- The category `SimplicialObject.Split C` is the category of simplicial objects
in `C` equipped with a splitting, and morphisms are morphisms of simplicial objects
which are compatible with the splittings. -/
@[ext]
structure Split where
  /-- the underlying simplicial object -/
  X : SimplicialObject C
  /-- a splitting of the simplicial object -/
  s : Splitting X
#align simplicial_object.split SimplicialObject.Split

namespace Split

variable {C}

/-- The object in `SimplicialObject.Split C` attached to a splitting `s : Splitting X`
of a simplicial object `X`. -/
@[simps]
def mk' {X : SimplicialObject C} (s : Splitting X) : Split C :=
  ⟨X, s⟩
#align simplicial_object.split.mk' SimplicialObject.Split.mk'

-- porting note (#5171): removed @[nolint has_nonempty_instance]
/-- Morphisms in `SimplicialObject.Split C` are morphisms of simplicial objects that
are compatible with the splittings. -/
structure Hom (S₁ S₂ : Split C) where
  /-- the morphism between the underlying simplicial objects -/
  F : S₁.X ⟶ S₂.X
  /-- the morphism between the "nondegenerate" `n`-simplices for all `n : ℕ` -/
  f : ∀ n : ℕ, S₁.s.N n ⟶ S₂.s.N n
  comm : ∀ n : ℕ, S₁.s.ι n ≫ F.app (op [n]) = f n ≫ S₂.s.ι n := by aesop_cat
#align simplicial_object.split.hom SimplicialObject.Split.Hom

@[ext]
theorem Hom.ext {S₁ S₂ : Split C} (Φ₁ Φ₂ : Hom S₁ S₂) (h : ∀ n : ℕ, Φ₁.f n = Φ₂.f n) : Φ₁ = Φ₂ := by
  rcases Φ₁ with ⟨F₁, f₁, c₁⟩
  rcases Φ₂ with ⟨F₂, f₂, c₂⟩
  have h' : f₁ = f₂ := by
    ext
    apply h
  subst h'
  simp only [mk.injEq, and_true]
  apply S₁.s.hom_ext
  intro n
  dsimp
  rw [c₁, c₂]
#align simplicial_object.split.hom.ext SimplicialObject.Split.Hom.ext

attribute [simp, reassoc] Hom.comm

end Split

instance : Category (Split C) where
  Hom := Split.Hom
  id S :=
    { F := 𝟙 _
      f := fun n => 𝟙 _ }
  comp Φ₁₂ Φ₂₃ :=
    { F := Φ₁₂.F ≫ Φ₂₃.F
      f := fun n => Φ₁₂.f n ≫ Φ₂₃.f n
      comm := fun n => by
        dsimp
        simp only [assoc, Split.Hom.comm_assoc, Split.Hom.comm] }

variable {C}

namespace Split

-- Porting note: added as `Hom.ext` is not triggered automatically
@[ext]
theorem hom_ext {S₁ S₂ : Split C} (Φ₁ Φ₂ : S₁ ⟶ S₂) (h : ∀ n : ℕ, Φ₁.f n = Φ₂.f n) : Φ₁ = Φ₂ :=
  Hom.ext _ _ h

theorem congr_F {S₁ S₂ : Split C} {Φ₁ Φ₂ : S₁ ⟶ S₂} (h : Φ₁ = Φ₂) : Φ₁.f = Φ₂.f := by rw [h]
set_option linter.uppercaseLean3 false in
#align simplicial_object.split.congr_F SimplicialObject.Split.congr_F

theorem congr_f {S₁ S₂ : Split C} {Φ₁ Φ₂ : S₁ ⟶ S₂} (h : Φ₁ = Φ₂) (n : ℕ) : Φ₁.f n = Φ₂.f n := by
  rw [h]
#align simplicial_object.split.congr_f SimplicialObject.Split.congr_f

@[simp]
theorem id_F (S : Split C) : (𝟙 S : S ⟶ S).F = 𝟙 S.X :=
  rfl
set_option linter.uppercaseLean3 false in
#align simplicial_object.split.id_F SimplicialObject.Split.id_F

@[simp]
theorem id_f (S : Split C) (n : ℕ) : (𝟙 S : S ⟶ S).f n = 𝟙 (S.s.N n) :=
  rfl
#align simplicial_object.split.id_f SimplicialObject.Split.id_f

@[simp]
theorem comp_F {S₁ S₂ S₃ : Split C} (Φ₁₂ : S₁ ⟶ S₂) (Φ₂₃ : S₂ ⟶ S₃) :
    (Φ₁₂ ≫ Φ₂₃).F = Φ₁₂.F ≫ Φ₂₃.F :=
  rfl
set_option linter.uppercaseLean3 false in
#align simplicial_object.split.comp_F SimplicialObject.Split.comp_F

@[simp]
theorem comp_f {S₁ S₂ S₃ : Split C} (Φ₁₂ : S₁ ⟶ S₂) (Φ₂₃ : S₂ ⟶ S₃) (n : ℕ) :
    (Φ₁₂ ≫ Φ₂₃).f n = Φ₁₂.f n ≫ Φ₂₃.f n :=
  rfl
#align simplicial_object.split.comp_f SimplicialObject.Split.comp_f

@[reassoc (attr := simp 1100)]
theorem cofan_inj_naturality_symm {S₁ S₂ : Split C} (Φ : S₁ ⟶ S₂) {Δ : SimplexCategoryᵒᵖ}
    (A : Splitting.IndexSet Δ) :
    (S₁.s.cofan Δ).inj A ≫ Φ.F.app Δ = Φ.f A.1.unop.len ≫ (S₂.s.cofan Δ).inj A := by
  erw [S₁.s.cofan_inj_eq, S₂.s.cofan_inj_eq, assoc, Φ.F.naturality, ← Φ.comm_assoc]
#align simplicial_object.split.ι_summand_naturality_symm SimplicialObject.Split.cofan_inj_naturality_symm

variable (C)

/-- The functor `SimplicialObject.Split C ⥤ SimplicialObject C` which forgets
the splitting. -/
@[simps]
def forget : Split C ⥤ SimplicialObject C where
  obj S := S.X
  map Φ := Φ.F
#align simplicial_object.split.forget SimplicialObject.Split.forget

/-- The functor `SimplicialObject.Split C ⥤ C` which sends a simplicial object equipped
with a splitting to its nondegenerate `n`-simplices. -/
@[simps]
def evalN (n : ℕ) : Split C ⥤ C where
  obj S := S.s.N n
  map Φ := Φ.f n
set_option linter.uppercaseLean3 false in
#align simplicial_object.split.eval_N SimplicialObject.Split.evalN

/-- The inclusion of each summand in the coproduct decomposition of simplices
in split simplicial objects is a natural transformation of functors
`SimplicialObject.Split C ⥤ C` -/
@[simps]
def natTransCofanInj {Δ : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) :
    evalN C A.1.unop.len ⟶ forget C ⋙ (evaluation SimplexCategoryᵒᵖ C).obj Δ where
  app S := (S.s.cofan Δ).inj A
  naturality _ _ Φ := (cofan_inj_naturality_symm Φ A).symm
#align simplicial_object.split.nat_trans_ι_summand SimplicialObject.Split.natTransCofanInj

end Split

end SimplicialObject
