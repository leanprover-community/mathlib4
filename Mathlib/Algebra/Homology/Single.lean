/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Homology.Homology

#align_import algebra.homology.single from "leanprover-community/mathlib"@"324a7502510e835cdbd3de1519b6c66b51fb2467"

/-!
# Chain complexes supported in a single degree

We define `single V j c : V ⥤ HomologicalComplex V c`,
which constructs complexes in `V` of shape `c`, supported in degree `j`.

Similarly `single₀ V : V ⥤ ChainComplex V ℕ` is the special case for
`ℕ`-indexed chain complexes, with the object supported in degree `0`,
but with better definitional properties.

In `toSingle₀Equiv` we characterize chain maps to an `ℕ`-indexed complex concentrated in degree 0;
they are equivalent to `{ f : C.X 0 ⟶ X // C.d 1 0 ≫ f = 0 }`.
(This is useful translating between a projective resolution and
an augmented exact complex of projectives.)
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open ZeroObject

universe v u

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

namespace HomologicalComplex

variable {ι : Type*} [DecidableEq ι] (c : ComplexShape ι)

/-- The functor `V ⥤ HomologicalComplex V c` creating a chain complex supported in a single degree.

See also `ChainComplex.single₀ : V ⥤ ChainComplex V ℕ`,
which has better definitional properties,
if you are working with `ℕ`-indexed complexes.
-/
@[simps]
def single (j : ι) : V ⥤ HomologicalComplex V c where
  obj A :=
    { X := fun i => if i = j then A else 0
      d := fun i j => 0 }
  map f :=
    { f := fun i => if h : i = j then eqToHom (by dsimp; rw [if_pos h]) ≫ f ≫
                                                  -- ⊢ (if i = j then X✝ else 0) = X✝
                                                         -- 🎉 no goals
              eqToHom (by dsimp; rw [if_pos h]) else 0 }
                          -- ⊢ Y✝ = if i = j then Y✝ else 0
                                 -- 🎉 no goals
  map_id A := by
    ext
    -- ⊢ Hom.f ({ obj := fun A => mk (fun i => if i = j then A else 0) fun i j_1 => 0 …
    dsimp
    -- ⊢ (if h : i✝ = j then eqToHom (_ : (if i✝ = j then A else 0) = A) ≫ 𝟙 A ≫ eqTo …
    split_ifs with h
    -- ⊢ eqToHom (_ : (if i✝ = j then A else 0) = A) ≫ 𝟙 A ≫ eqToHom (_ : A = if i✝ = …
    · subst h
      -- ⊢ eqToHom (_ : (if i✝ = i✝ then A else 0) = A) ≫ 𝟙 A ≫ eqToHom (_ : A = if i✝  …
      simp
      -- 🎉 no goals
    · rw [if_neg h]
      -- ⊢ 0 = 𝟙 0
      simp
      -- 🎉 no goals
  map_comp f g := by
    ext
    -- ⊢ Hom.f ({ obj := fun A => mk (fun i => if i = j then A else 0) fun i j_1 => 0 …
    dsimp
    -- ⊢ (if h : i✝ = j then eqToHom (_ : (if i✝ = j then X✝ else 0) = X✝) ≫ (f ≫ g)  …
    split_ifs with h
    -- ⊢ eqToHom (_ : (if i✝ = j then X✝ else 0) = X✝) ≫ (f ≫ g) ≫ eqToHom (_ : Z✝ =  …
    · subst h
      -- ⊢ eqToHom (_ : (if i✝ = i✝ then X✝ else 0) = X✝) ≫ (f ≫ g) ≫ eqToHom (_ : Z✝ = …
      simp
      -- 🎉 no goals
    · simp
      -- 🎉 no goals
#align homological_complex.single HomologicalComplex.single

/-- The object in degree `j` of `(single V c h).obj A` is just `A`.
-/
@[simps!]
def singleObjXSelf (j : ι) (A : V) : ((single V c j).obj A).X j ≅ A :=
  eqToIso (by simp)
              -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align homological_complex.single_obj_X_self HomologicalComplex.singleObjXSelf

@[simp 1100]
theorem single_map_f_self (j : ι) {A B : V} (f : A ⟶ B) :
    ((single V c j).map f).f j = (singleObjXSelf V c j A).hom ≫
      f ≫ (singleObjXSelf V c j B).inv := by simp
                                             -- 🎉 no goals
#align homological_complex.single_map_f_self HomologicalComplex.single_map_f_self

instance (j : ι) : Faithful (single V c j) where
  map_injective w := by
    have := congr_hom w j
    -- ⊢ a₁✝ = a₂✝
    dsimp at this
    -- ⊢ a₁✝ = a₂✝
    simp only [dif_pos] at this
    -- ⊢ a₁✝ = a₂✝
    rw [← IsIso.inv_comp_eq, inv_eqToHom, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, ← IsIso.comp_inv_eq, Category.assoc, inv_eqToHom, eqToHom_trans,
      eqToHom_refl, Category.comp_id] at this
    exact this
    -- 🎉 no goals

instance (j : ι) : Full (single V c j) where
  preimage f := eqToHom (by simp) ≫ f.f j ≫ eqToHom (by simp)
                            -- 🎉 no goals
                                                        -- 🎉 no goals
  witness f := by
    ext i
    -- ⊢ Hom.f ((single V c j).map ((fun {X Y} f => eqToHom (_ : X = if j = j then X  …
    dsimp
    -- ⊢ (if h : i = j then eqToHom (_ : X ((fun A => mk (fun i => if i = j then A el …
    split_ifs with h
    -- ⊢ eqToHom (_ : X ((fun A => mk (fun i => if i = j then A else 0) fun i j_1 =>  …
    · subst h
      -- ⊢ eqToHom (_ : X ((fun A => mk (fun i_1 => if i_1 = i then A else 0) fun i_1 j …
      simp
      -- 🎉 no goals
    · symm
      -- ⊢ Hom.f f i = 0
      apply zero_of_target_iso_zero
      -- ⊢ X ((single V c j).obj Y✝) i ≅ 0
      dsimp
      -- ⊢ (if i = j then Y✝ else 0) ≅ 0
      rw [if_neg h]
      -- 🎉 no goals

end HomologicalComplex

open HomologicalComplex

namespace ChainComplex

/-- `ChainComplex.single₀ V` is the embedding of `V` into `ChainComplex V ℕ`
as chain complexes supported in degree 0.

This is naturally isomorphic to `single V _ 0`, but has better definitional properties.
-/
def single₀ : V ⥤ ChainComplex V ℕ where
  obj X :=
    { X := fun n =>
        match n with
        | 0 => X
        | _ + 1 => 0
      d := fun i j => 0 }
  map f :=
    { f := fun n =>
        match n with
        | 0 => f
        | n + 1 => 0 }
  map_id X := by
    ext (_|_)
    · rfl
      -- 🎉 no goals
    · simp
      -- 🎉 no goals
  map_comp f g := by
    ext (_|_)
    · rfl
      -- 🎉 no goals
    · simp
      -- 🎉 no goals
#align chain_complex.single₀ ChainComplex.single₀

@[simp]
theorem single₀_obj_X_0 (X : V) : ((single₀ V).obj X).X 0 = X :=
  rfl
set_option linter.uppercaseLean3 false in
#align chain_complex.single₀_obj_X_0 ChainComplex.single₀_obj_X_0

@[simp]
theorem single₀_obj_X_succ (X : V) (n : ℕ) : ((single₀ V).obj X).X (n + 1) = 0 :=
  rfl
set_option linter.uppercaseLean3 false in
#align chain_complex.single₀_obj_X_succ ChainComplex.single₀_obj_X_succ

@[simp]
theorem single₀_obj_X_d (X : V) (i j : ℕ) : ((single₀ V).obj X).d i j = 0 :=
  rfl
set_option linter.uppercaseLean3 false in
#align chain_complex.single₀_obj_X_d ChainComplex.single₀_obj_X_d

@[simp]
theorem single₀_obj_X_dTo (X : V) (j : ℕ) : ((single₀ V).obj X).dTo j = 0 := by
  rw [dTo_eq ((single₀ V).obj X) rfl]
  -- ⊢ (xPrevIso ((single₀ V).obj X) (_ : j + 1 = j + 1)).hom ≫ d ((single₀ V).obj  …
  simp
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align chain_complex.single₀_obj_X_d_to ChainComplex.single₀_obj_X_dTo

@[simp]
theorem single₀_obj_x_dFrom (X : V) (i : ℕ) : ((single₀ V).obj X).dFrom i = 0 := by
  cases i
  -- ⊢ dFrom ((single₀ V).obj X) Nat.zero = 0
  · rw [dFrom_eq_zero]
    -- ⊢ ¬ComplexShape.Rel (ComplexShape.down ℕ) Nat.zero (ComplexShape.next (Complex …
    simp
    -- 🎉 no goals
  · erw [dFrom_eq ((single₀ V).obj X) rfl]
    -- ⊢ d ((single₀ V).obj X) (n✝ + 1) n✝ ≫ (xNextIso ((single₀ V).obj X) (_ : n✝ +  …
    simp
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align chain_complex.single₀_obj_X_d_from ChainComplex.single₀_obj_x_dFrom

@[simp]
theorem single₀_map_f_0 {X Y : V} (f : X ⟶ Y) : ((single₀ V).map f).f 0 = f :=
  rfl
#align chain_complex.single₀_map_f_0 ChainComplex.single₀_map_f_0

@[simp]
theorem single₀_map_f_succ {X Y : V} (f : X ⟶ Y) (n : ℕ) : ((single₀ V).map f).f (n + 1) = 0 :=
  rfl
#align chain_complex.single₀_map_f_succ ChainComplex.single₀_map_f_succ

section

variable [HasEqualizers V] [HasCokernels V] [HasImages V] [HasImageMaps V]

/-- Sending objects to chain complexes supported at `0` then taking `0`-th homology
is the same as doing nothing.
-/
noncomputable def homologyFunctor0Single₀ : single₀ V ⋙ homologyFunctor V _ 0 ≅ 𝟭 V :=
  NatIso.ofComponents (fun X => homology.congr _ _ (by simp) (by simp) ≪≫ homologyZeroZero)
                                                       -- 🎉 no goals
                                                                 -- 🎉 no goals
    fun f => by
      -- Porting note: why can't `aesop_cat` do this?
      dsimp
      -- ⊢ homology.map (_ : dTo ((single₀ V).obj X✝) 0 ≫ dFrom ((single₀ V).obj X✝) 0  …
      ext
      -- ⊢ homology.π (dTo ((single₀ V).obj X✝) 0) (dFrom ((single₀ V).obj X✝) 0) (_ :  …
      simp
      -- 🎉 no goals
#align chain_complex.homology_functor_0_single₀ ChainComplex.homologyFunctor0Single₀

/-- Sending objects to chain complexes supported at `0` then taking `(n+1)`-st homology
is the same as the zero functor.
-/
noncomputable def homologyFunctorSuccSingle₀ (n : ℕ) :
    single₀ V ⋙ homologyFunctor V _ (n + 1) ≅ 0 :=
  NatIso.ofComponents
    (fun X =>
      homology.congr _ _ (by simp) (by simp) ≪≫
                             -- 🎉 no goals
                                       -- 🎉 no goals
        homologyZeroZero ≪≫ (Functor.zero_obj _).isoZero.symm)
    fun f => (Functor.zero_obj _).eq_of_tgt _ _
#align chain_complex.homology_functor_succ_single₀ ChainComplex.homologyFunctorSuccSingle₀

end

variable {V}

/-- Morphisms from an `ℕ`-indexed chain complex `C`
to a single object chain complex with `X` concentrated in degree 0
are the same as morphisms `f : C.X 0 ⟶ X` such that `C.d 1 0 ≫ f = 0`.
-/
@[simps]
def toSingle₀Equiv (C : ChainComplex V ℕ) (X : V) :
    (C ⟶ (single₀ V).obj X) ≃ { f : C.X 0 ⟶ X // C.d 1 0 ≫ f = 0 } where
  toFun f :=
    ⟨f.f 0, by
      rw [← f.comm 1 0]
      -- ⊢ Hom.f f 1 ≫ d ((single₀ V).obj X) 1 0 = 0
      simp⟩
      -- 🎉 no goals
  invFun f :=
    { f := fun i =>
        match i with
        | 0 => f.1
        | n + 1 => 0
      comm' := fun i j h => by
        rcases i with (_|_|i) <;> cases j <;> simp only [single₀_obj_X_d, comp_zero]
                                              -- ⊢ 0 = d C Nat.zero Nat.zero ≫ ↑f
                                              -- 🎉 no goals
                                              -- ⊢ 0 = d C (Nat.succ Nat.zero) Nat.zero ≫ ↑f
                                              -- 🎉 no goals
                                              -- ⊢ 0 = d C (Nat.succ (Nat.succ i)) Nat.zero ≫ ↑f
                                              -- 🎉 no goals
        · rw [C.shape, zero_comp]
          -- ⊢ ¬ComplexShape.Rel (ComplexShape.down ℕ) Nat.zero Nat.zero
          simp
          -- 🎉 no goals
        · exact f.2.symm
          -- 🎉 no goals
        · rw [C.shape, zero_comp]
          -- ⊢ ¬ComplexShape.Rel (ComplexShape.down ℕ) (Nat.succ (Nat.succ i)) Nat.zero
          exact i.succ_succ_ne_one.symm }
          -- 🎉 no goals
  left_inv f := by
    ext i
    -- ⊢ Hom.f
    rcases i with ⟨⟩
    · rfl
      -- 🎉 no goals
    · dsimp
      -- ⊢ 0 = Hom.f f (Nat.succ n✝)
      ext
      -- 🎉 no goals
  right_inv := by aesop_cat
                  -- 🎉 no goals
#align chain_complex.to_single₀_equiv ChainComplex.toSingle₀Equiv

@[ext]
theorem to_single₀_ext {C : ChainComplex V ℕ} {X : V} (f g : C ⟶ (single₀ V).obj X)
    (h : f.f 0 = g.f 0) : f = g :=
  (toSingle₀Equiv C X).injective
    (by
      ext
      -- ⊢ ↑(↑(toSingle₀Equiv C X) f) = ↑(↑(toSingle₀Equiv C X) g)
      exact h)
      -- 🎉 no goals
#align chain_complex.to_single₀_ext ChainComplex.to_single₀_ext

/-- Morphisms from a single object chain complex with `X` concentrated in degree 0
to an `ℕ`-indexed chain complex `C` are the same as morphisms `f : X → C.X`.
-/
@[simps]
def fromSingle₀Equiv (C : ChainComplex V ℕ) (X : V) : ((single₀ V).obj X ⟶ C) ≃ (X ⟶ C.X 0) where
  toFun f := f.f 0
  invFun f :=
    { f := fun i =>
        match i with
        | 0 => f
        | n + 1 => 0
      comm' := fun i j h => by
        cases i <;> cases j <;>
          simp only [shape, ComplexShape.down_Rel, Nat.one_ne_zero, not_false_iff,
            zero_comp, single₀_obj_X_d, Nat.zero_eq, add_eq_zero, comp_zero] }
  left_inv f := by
    ext i
    -- ⊢ Hom.f
    cases i
    · rfl
      -- 🎉 no goals
    · dsimp
      -- ⊢ 0 = Hom.f f (Nat.succ n✝)
      ext
      -- 🎉 no goals
  right_inv g := rfl
#align chain_complex.from_single₀_equiv ChainComplex.fromSingle₀Equiv

variable (V)

/-- `single₀` is the same as `single V _ 0`. -/
def single₀IsoSingle : single₀ V ≅ single V _ 0 :=
  NatIso.ofComponents
    (fun X =>
      { hom := { f := fun i => by cases i <;> exact 𝟙 _ }
                                  -- ⊢ HomologicalComplex.X ((single₀ V).obj X) Nat.zero ⟶ HomologicalComplex.X ((s …
                                              -- 🎉 no goals
                                              -- 🎉 no goals
        inv := { f := fun i => by cases i <;> exact 𝟙 _ }
                                  -- ⊢ HomologicalComplex.X ((single V (ComplexShape.down ℕ) 0).obj X) Nat.zero ⟶ H …
                                              -- 🎉 no goals
                                              -- 🎉 no goals
        hom_inv_id := to_single₀_ext _ _ (by simp)
                                             -- 🎉 no goals
        inv_hom_id := by
          ext (_|_)
          -- ⊢ Hom.f ((Hom.mk fun i => Nat.casesOn (motive := fun t => i = t → (Homological …
          · dsimp
            -- ⊢ 𝟙 (if 0 = 0 then X else 0) ≫ 𝟙 X = 𝟙 (if 0 = 0 then X else 0)
            simp
            -- 🎉 no goals
          · dsimp
            -- ⊢ 𝟙 (if Nat.succ n✝ = 0 then X else 0) ≫ 𝟙 0 = 𝟙 (if Nat.succ n✝ = 0 then X el …
            rw [Category.comp_id] })
            -- 🎉 no goals
    fun f => by ext (_|_) <;> aesop_cat
                -- ⊢ Hom.f ((single₀ V).map f ≫ ((fun X => Iso.mk (Hom.mk fun i => Nat.casesOn (m …
                              -- 🎉 no goals
                              -- 🎉 no goals
#align chain_complex.single₀_iso_single ChainComplex.single₀IsoSingle

instance : Faithful (single₀ V) :=
  Faithful.of_iso (single₀IsoSingle V).symm

instance : Full (single₀ V) :=
  Full.ofIso (single₀IsoSingle V).symm

end ChainComplex

namespace CochainComplex

/-- `CochainComplex.single₀ V` is the embedding of `V` into `CochainComplex V ℕ`
as cochain complexes supported in degree 0.

This is naturally isomorphic to `single V _ 0`, but has better definitional properties.
-/
def single₀ : V ⥤ CochainComplex V ℕ where
  obj X :=
    { X := fun n =>
        match n with
        | 0 => X
        | _ + 1 => 0
      d := fun i j => 0 }
  map f :=
    { f := fun n =>
        match n with
        | 0 => f
        | n + 1 => 0 }
  map_id X := by
    ext (_|_)
    · rfl
      -- 🎉 no goals
    · simp
      -- 🎉 no goals
  map_comp f g := by
    ext (_|_)
    · rfl
      -- 🎉 no goals
    · simp
      -- 🎉 no goals
#align cochain_complex.single₀ CochainComplex.single₀

@[simp]
theorem single₀_obj_X_0 (X : V) : ((single₀ V).obj X).X 0 = X :=
  rfl
set_option linter.uppercaseLean3 false in
#align cochain_complex.single₀_obj_X_0 CochainComplex.single₀_obj_X_0

@[simp]
theorem single₀_obj_X_succ (X : V) (n : ℕ) : ((single₀ V).obj X).X (n + 1) = 0 :=
  rfl
set_option linter.uppercaseLean3 false in
#align cochain_complex.single₀_obj_X_succ CochainComplex.single₀_obj_X_succ

@[simp]
theorem single₀_obj_X_d (X : V) (i j : ℕ) : ((single₀ V).obj X).d i j = 0 :=
  rfl
set_option linter.uppercaseLean3 false in
#align cochain_complex.single₀_obj_X_d CochainComplex.single₀_obj_X_d

@[simp]
theorem single₀_obj_x_dFrom (X : V) (j : ℕ) : ((single₀ V).obj X).dFrom j = 0 := by
  rw [dFrom_eq ((single₀ V).obj X) rfl]
  -- ⊢ d ((single₀ V).obj X) j (j + 1) ≫ (xNextIso ((single₀ V).obj X) (_ : j + 1 = …
  simp
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align cochain_complex.single₀_obj_X_d_from CochainComplex.single₀_obj_x_dFrom

@[simp]
theorem single₀_obj_x_dTo (X : V) (i : ℕ) : ((single₀ V).obj X).dTo i = 0 := by
  cases i
  -- ⊢ dTo ((single₀ V).obj X) Nat.zero = 0
  · rw [dTo_eq_zero]
    -- ⊢ ¬ComplexShape.Rel (ComplexShape.up ℕ) (ComplexShape.prev (ComplexShape.up ℕ) …
    simp
    -- 🎉 no goals
  · erw [dTo_eq ((single₀ V).obj X) rfl]
    -- ⊢ (xPrevIso ((single₀ V).obj X) (_ : n✝ + 1 = n✝ + 1)).hom ≫ d ((single₀ V).ob …
    simp
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align cochain_complex.single₀_obj_X_d_to CochainComplex.single₀_obj_x_dTo

@[simp]
theorem single₀_map_f_0 {X Y : V} (f : X ⟶ Y) : ((single₀ V).map f).f 0 = f :=
  rfl
#align cochain_complex.single₀_map_f_0 CochainComplex.single₀_map_f_0

@[simp]
theorem single₀_map_f_succ {X Y : V} (f : X ⟶ Y) (n : ℕ) : ((single₀ V).map f).f (n + 1) = 0 :=
  rfl
#align cochain_complex.single₀_map_f_succ CochainComplex.single₀_map_f_succ

section

variable [HasEqualizers V] [HasCokernels V] [HasImages V] [HasImageMaps V]

/-- Sending objects to cochain complexes supported at `0` then taking `0`-th homology
is the same as doing nothing.
-/
noncomputable def homologyFunctor0Single₀ : single₀ V ⋙ homologyFunctor V _ 0 ≅ 𝟭 V :=
  NatIso.ofComponents (fun X => homology.congr _ _ (by simp) (by simp) ≪≫ homologyZeroZero)
                                                       -- 🎉 no goals
                                                                 -- 🎉 no goals
    fun f => by
      -- Porting note: why can't `aesop_cat` do this?
      dsimp
      -- ⊢ homology.map (_ : dTo ((single₀ V).obj X✝) 0 ≫ dFrom ((single₀ V).obj X✝) 0  …
      ext
      -- ⊢ homology.π (dTo ((single₀ V).obj X✝) 0) (dFrom ((single₀ V).obj X✝) 0) (_ :  …
      simp
      -- 🎉 no goals
#align cochain_complex.homology_functor_0_single₀ CochainComplex.homologyFunctor0Single₀

/-- Sending objects to cochain complexes supported at `0` then taking `(n+1)`-st homology
is the same as the zero functor.
-/
noncomputable def homologyFunctorSuccSingle₀ (n : ℕ) :
    single₀ V ⋙ homologyFunctor V _ (n + 1) ≅ 0 :=
  NatIso.ofComponents
    (fun X =>
      homology.congr _ _ (by simp) (by simp) ≪≫
                             -- 🎉 no goals
                                       -- 🎉 no goals
        homologyZeroZero ≪≫ (Functor.zero_obj _).isoZero.symm)
    fun f => (Functor.zero_obj _).eq_of_tgt _ _
#align cochain_complex.homology_functor_succ_single₀ CochainComplex.homologyFunctorSuccSingle₀

end

variable {V}

/-- Morphisms from a single object cochain complex with `X` concentrated in degree 0
to an `ℕ`-indexed cochain complex `C`
are the same as morphisms `f : X ⟶ C.X 0` such that `f ≫ C.d 0 1 = 0`.
-/
def fromSingle₀Equiv (C : CochainComplex V ℕ) (X : V) :
    ((single₀ V).obj X ⟶ C) ≃ { f : X ⟶ C.X 0 // f ≫ C.d 0 1 = 0 } where
  toFun f :=
    ⟨f.f 0, by
      rw [f.comm 0 1]
      -- ⊢ d ((single₀ V).obj X) 0 1 ≫ Hom.f f 1 = 0
      simp⟩
      -- 🎉 no goals
  invFun f :=
    { f := fun i =>
        match i with
        | 0 => f.1
        | n + 1 => 0
      comm' := fun i j h => by
        rcases f with ⟨f, hf⟩
        -- ⊢ (fun i =>
        rcases j with (_|_|j) <;> cases i <;> simp only [single₀_obj_X_d, zero_comp]
                                              -- ⊢ f ≫ d C Nat.zero Nat.zero = 0
                                              -- 🎉 no goals
                                              -- ⊢ f ≫ d C Nat.zero (Nat.succ Nat.zero) = 0
                                              -- 🎉 no goals
                                              -- ⊢ f ≫ d C Nat.zero (Nat.succ (Nat.succ j)) = 0
                                              -- 🎉 no goals
        · rw [C.shape, comp_zero]
          -- ⊢ ¬ComplexShape.Rel (ComplexShape.up ℕ) Nat.zero Nat.zero
          simp
          -- 🎉 no goals
        · exact hf
          -- 🎉 no goals
        · rw [C.shape, comp_zero]
          -- ⊢ ¬ComplexShape.Rel (ComplexShape.up ℕ) Nat.zero (Nat.succ (Nat.succ j))
          simp
          -- ⊢ ¬1 = Nat.succ (Nat.succ j)
          exact j.succ_succ_ne_one.symm }
          -- 🎉 no goals
  left_inv f := by
    ext i
    -- ⊢ Hom.f
    rcases i with ⟨⟩
    · rfl
      -- 🎉 no goals
    · dsimp
      -- ⊢ 0 = Hom.f f (Nat.succ n✝)
      ext
      -- 🎉 no goals
  right_inv := by aesop_cat
                  -- 🎉 no goals
#align cochain_complex.from_single₀_equiv CochainComplex.fromSingle₀Equiv

-- porting note: added to ease the following definition
@[ext]
theorem from_single₀_ext {C : CochainComplex V ℕ} {X : V} (f g : (single₀ V).obj X ⟶ C)
    (h : f.f 0 = g.f 0) : f = g :=
  (fromSingle₀Equiv C X).injective
    (by
      ext
      -- ⊢ ↑(↑(fromSingle₀Equiv C X) f) = ↑(↑(fromSingle₀Equiv C X) g)
      exact h)
      -- 🎉 no goals

variable (V)

/-- `single₀` is the same as `single V _ 0`. -/
def single₀IsoSingle : single₀ V ≅ single V _ 0 :=
  NatIso.ofComponents fun X =>
    { hom := { f := fun i => by cases i <;> exact 𝟙 _ }
                                -- ⊢ HomologicalComplex.X ((single₀ V).obj X) Nat.zero ⟶ HomologicalComplex.X ((s …
                                            -- 🎉 no goals
                                            -- 🎉 no goals
      inv := { f := fun i => by cases i <;> exact 𝟙 _ }
                                -- ⊢ HomologicalComplex.X ((single V (ComplexShape.up ℕ) 0).obj X) Nat.zero ⟶ Hom …
                                            -- 🎉 no goals
                                            -- 🎉 no goals
      hom_inv_id := from_single₀_ext _ _ (by simp)
                                             -- 🎉 no goals
      inv_hom_id := by
        ext (_|_)
        -- ⊢ Hom.f ((Hom.mk fun i => Nat.casesOn (motive := fun t => i = t → (Homological …
        · dsimp
          -- ⊢ 𝟙 (if 0 = 0 then X else 0) ≫ 𝟙 X = 𝟙 (if 0 = 0 then X else 0)
          simp
          -- 🎉 no goals
        · dsimp
          -- ⊢ 𝟙 (if Nat.succ n✝ = 0 then X else 0) ≫ 𝟙 0 = 𝟙 (if Nat.succ n✝ = 0 then X el …
          rw [Category.id_comp]
          -- ⊢ 𝟙 0 = 𝟙 (if Nat.succ n✝ = 0 then X else 0)
          rfl }
          -- 🎉 no goals
#align cochain_complex.single₀_iso_single CochainComplex.single₀IsoSingle

instance : Faithful (single₀ V) :=
  Faithful.of_iso (single₀IsoSingle V).symm

instance : Full (single₀ V) :=
  Full.ofIso (single₀IsoSingle V).symm

end CochainComplex
