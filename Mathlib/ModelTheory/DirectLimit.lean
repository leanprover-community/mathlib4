/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Gabin Kolly
-/
import Mathlib.Init.Align
import Mathlib.Data.Fintype.Order
import Mathlib.Algebra.DirectLimit
import Mathlib.ModelTheory.Quotients
import Mathlib.ModelTheory.FinitelyGenerated

#align_import model_theory.direct_limit from "leanprover-community/mathlib"@"f53b23994ac4c13afa38d31195c588a1121d1860"

/-!
# Direct Limits of First-Order Structures
This file constructs the direct limit of a directed system of first-order embeddings.

## Main Definitions
* `FirstOrder.Language.DirectLimit G f` is the direct limit of the directed system `f` of
  first-order embeddings between the structures indexed by `G`.
* `FirstOrder.Language.DirectLimit.lift` is the universal property of the direct limit: maps
  from the components to another module that respect the directed system structure give rise to
  a unique map out of the direct limit.
* `FirstOrder.Language.DirectLimit.equiv_lift` is the equivalence between limits of
  isomorphic direct systems.
-/


universe v w w' u₁ u₂

open FirstOrder

namespace FirstOrder

namespace Language

open Structure Set

variable {L : Language} {ι : Type v} [Preorder ι]
variable {G : ι → Type w} [∀ i, L.Structure (G i)]
variable (f : ∀ i j, i ≤ j → G i ↪[L] G j)

namespace DirectedSystem

/-- A copy of `DirectedSystem.map_self` specialized to `L`-embeddings, as otherwise the
`fun i j h ↦ f i j h` can confuse the simplifier. -/
nonrec theorem map_self [DirectedSystem G fun i j h => f i j h] (i x h) : f i i h x = x :=
  DirectedSystem.map_self (fun i j h => f i j h) i x h
#align first_order.language.directed_system.map_self FirstOrder.Language.DirectedSystem.map_self

/-- A copy of `DirectedSystem.map_map` specialized to `L`-embeddings, as otherwise the
`fun i j h ↦ f i j h` can confuse the simplifier. -/
nonrec theorem map_map [DirectedSystem G fun i j h => f i j h] {i j k} (hij hjk x) :
    f j k hjk (f i j hij x) = f i k (le_trans hij hjk) x :=
  DirectedSystem.map_map (fun i j h => f i j h) hij hjk x
#align first_order.language.directed_system.map_map FirstOrder.Language.DirectedSystem.map_map

variable {G' : ℕ → Type w} [∀ i, L.Structure (G' i)] (f' : ∀ n : ℕ, G' n ↪[L] G' (n + 1))

/-- Given a chain of embeddings of structures indexed by `ℕ`, defines a `DirectedSystem` by
composing them. -/
def natLERec (m n : ℕ) (h : m ≤ n) : G' m ↪[L] G' n :=
  Nat.leRecOn h (@fun k g => (f' k).comp g) (Embedding.refl L _)
#align first_order.language.directed_system.nat_le_rec FirstOrder.Language.DirectedSystem.natLERec

@[simp]
theorem coe_natLERec (m n : ℕ) (h : m ≤ n) :
    (natLERec f' m n h : G' m → G' n) = Nat.leRecOn h (@fun k => f' k) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  ext x
  induction' k with k ih
  · -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [natLERec, Nat.leRecOn_self, Embedding.refl_apply, Nat.leRecOn_self]
  · -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [Nat.leRecOn_succ le_self_add, natLERec, Nat.leRecOn_succ le_self_add, ← natLERec,
      Embedding.comp_apply, ih]
#align first_order.language.directed_system.coe_nat_le_rec FirstOrder.Language.DirectedSystem.coe_natLERec

instance natLERec.directedSystem : DirectedSystem G' fun i j h => natLERec f' i j h :=
  ⟨fun i x _ => congr (congr rfl (Nat.leRecOn_self _)) rfl,
   fun hij hjk => by simp [Nat.leRecOn_trans hij hjk]⟩
#align first_order.language.directed_system.nat_le_rec.directed_system FirstOrder.Language.DirectedSystem.natLERec.directedSystem

end DirectedSystem

-- Porting note: Instead of `Σ i, G i`, we use the alias `Language.Structure.Sigma`
-- which depends on `f`. This way, Lean can infer what `L` and `f` are in the `Setoid` instance.
-- Otherwise we have a "cannot find synthesization order" error. See the discussion at
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/local.20instance.20cannot.20find.20synthesization.20order.20in.20porting

set_option linter.unusedVariables false in
/-- Alias for `Σ i, G i`. -/
@[nolint unusedArguments]
protected abbrev Structure.Sigma (f : ∀ i j, i ≤ j → G i ↪[L] G j) := Σ i, G i

-- Porting note: Setting up notation for `Language.Structure.Sigma`: add a little asterisk to `Σ`
local notation "Σˣ" => Structure.Sigma

/-- Constructor for `FirstOrder.Language.Structure.Sigma` alias. -/
abbrev Structure.Sigma.mk (i : ι) (x : G i) : Σˣ f := ⟨i, x⟩

namespace DirectLimit

/-- Raises a family of elements in the `Σ`-type to the same level along the embeddings. -/
def unify {α : Type*} (x : α → Σˣ f) (i : ι) (h : i ∈ upperBounds (range (Sigma.fst ∘ x)))
    (a : α) : G i :=
  f (x a).1 i (h (mem_range_self a)) (x a).2
#align first_order.language.direct_limit.unify FirstOrder.Language.DirectLimit.unify

variable [DirectedSystem G fun i j h => f i j h]

@[simp]
theorem unify_sigma_mk_self {α : Type*} {i : ι} {x : α → G i} :
    (unify f (fun a => .mk f i (x a)) i fun j ⟨a, hj⟩ =>
      _root_.trans (le_of_eq hj.symm) (refl _)) = x := by
  ext a
  rw [unify]
  apply DirectedSystem.map_self
#align first_order.language.direct_limit.unify_sigma_mk_self FirstOrder.Language.DirectLimit.unify_sigma_mk_self

theorem comp_unify {α : Type*} {x : α → Σˣ f} {i j : ι} (ij : i ≤ j)
    (h : i ∈ upperBounds (range (Sigma.fst ∘ x))) :
    f i j ij ∘ unify f x i h = unify f x j
      fun k hk => _root_.trans (mem_upperBounds.1 h k hk) ij := by
  ext a
  simp [unify, DirectedSystem.map_map]
#align first_order.language.direct_limit.comp_unify FirstOrder.Language.DirectLimit.comp_unify

end DirectLimit

variable (G)

namespace DirectLimit

/-- The directed limit glues together the structures along the embeddings. -/
def setoid [DirectedSystem G fun i j h => f i j h] [IsDirected ι (· ≤ ·)] : Setoid (Σˣ f) where
  r := fun ⟨i, x⟩ ⟨j, y⟩ => ∃ (k : ι) (ik : i ≤ k) (jk : j ≤ k), f i k ik x = f j k jk y
  iseqv :=
    ⟨fun ⟨i, x⟩ => ⟨i, refl i, refl i, rfl⟩, @fun ⟨i, x⟩ ⟨j, y⟩ ⟨k, ik, jk, h⟩ =>
      ⟨k, jk, ik, h.symm⟩,
      @fun ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩ ⟨ij, hiij, hjij, hij⟩ ⟨jk, hjjk, hkjk, hjk⟩ => by
        obtain ⟨ijk, hijijk, hjkijk⟩ := directed_of (· ≤ ·) ij jk
        refine ⟨ijk, le_trans hiij hijijk, le_trans hkjk hjkijk, ?_⟩
        rw [← DirectedSystem.map_map, hij, DirectedSystem.map_map]
        · symm
          rw [← DirectedSystem.map_map, ← hjk, DirectedSystem.map_map] <;> assumption⟩
#align first_order.language.direct_limit.setoid FirstOrder.Language.DirectLimit.setoid

/-- The structure on the `Σ`-type which becomes the structure on the direct limit after quotienting.
 -/
noncomputable def sigmaStructure [IsDirected ι (· ≤ ·)] [Nonempty ι] : L.Structure (Σˣ f) where
  funMap F x :=
    ⟨_,
      funMap F
        (unify f x (Classical.choose (Finite.bddAbove_range fun a => (x a).1))
          (Classical.choose_spec (Finite.bddAbove_range fun a => (x a).1)))⟩
  RelMap R x :=
    RelMap R
      (unify f x (Classical.choose (Finite.bddAbove_range fun a => (x a).1))
        (Classical.choose_spec (Finite.bddAbove_range fun a => (x a).1)))
#align first_order.language.direct_limit.sigma_structure FirstOrder.Language.DirectLimit.sigmaStructure

end DirectLimit

/-- The direct limit of a directed system is the structures glued together along the embeddings. -/
def DirectLimit [DirectedSystem G fun i j h => f i j h] [IsDirected ι (· ≤ ·)] :=
  Quotient (DirectLimit.setoid G f)
#align first_order.language.direct_limit FirstOrder.Language.DirectLimit

attribute [local instance] DirectLimit.setoid

-- Porting note (#10754): Added local instance
attribute [local instance] DirectLimit.sigmaStructure


instance [DirectedSystem G fun i j h => f i j h] [IsDirected ι (· ≤ ·)] [Inhabited ι]
    [Inhabited (G default)] : Inhabited (DirectLimit G f) :=
  ⟨⟦⟨default, default⟩⟧⟩

namespace DirectLimit

variable [IsDirected ι (· ≤ ·)] [DirectedSystem G fun i j h => f i j h]

theorem equiv_iff {x y : Σˣ f} {i : ι} (hx : x.1 ≤ i) (hy : y.1 ≤ i) :
    x ≈ y ↔ (f x.1 i hx) x.2 = (f y.1 i hy) y.2 := by
  cases x
  cases y
  refine ⟨fun xy => ?_, fun xy => ⟨i, hx, hy, xy⟩⟩
  obtain ⟨j, _, _, h⟩ := xy
  obtain ⟨k, ik, jk⟩ := directed_of (· ≤ ·) i j
  have h := congr_arg (f j k jk) h
  apply (f i k ik).injective
  rw [DirectedSystem.map_map, DirectedSystem.map_map] at *
  exact h
#align first_order.language.direct_limit.equiv_iff FirstOrder.Language.DirectLimit.equiv_iff

theorem funMap_unify_equiv {n : ℕ} (F : L.Functions n) (x : Fin n → Σˣ f) (i j : ι)
    (hi : i ∈ upperBounds (range (Sigma.fst ∘ x))) (hj : j ∈ upperBounds (range (Sigma.fst ∘ x))) :
    Structure.Sigma.mk f i (funMap F (unify f x i hi)) ≈ .mk f j (funMap F (unify f x j hj)) := by
  obtain ⟨k, ik, jk⟩ := directed_of (· ≤ ·) i j
  refine ⟨k, ik, jk, ?_⟩
  rw [(f i k ik).map_fun, (f j k jk).map_fun, comp_unify, comp_unify]
#align first_order.language.direct_limit.fun_map_unify_equiv FirstOrder.Language.DirectLimit.funMap_unify_equiv

theorem relMap_unify_equiv {n : ℕ} (R : L.Relations n) (x : Fin n → Σˣ f) (i j : ι)
    (hi : i ∈ upperBounds (range (Sigma.fst ∘ x))) (hj : j ∈ upperBounds (range (Sigma.fst ∘ x))) :
    RelMap R (unify f x i hi) = RelMap R (unify f x j hj) := by
  obtain ⟨k, ik, jk⟩ := directed_of (· ≤ ·) i j
  rw [← (f i k ik).map_rel, comp_unify, ← (f j k jk).map_rel, comp_unify]
#align first_order.language.direct_limit.rel_map_unify_equiv FirstOrder.Language.DirectLimit.relMap_unify_equiv

variable [Nonempty ι]

theorem exists_unify_eq {α : Type*} [Finite α] {x y : α → Σˣ f} (xy : x ≈ y) :
    ∃ (i : ι) (hx : i ∈ upperBounds (range (Sigma.fst ∘ x)))
      (hy : i ∈ upperBounds (range (Sigma.fst ∘ y))), unify f x i hx = unify f y i hy := by
  obtain ⟨i, hi⟩ := Finite.bddAbove_range (Sum.elim (fun a => (x a).1) fun a => (y a).1)
  rw [Sum.elim_range, upperBounds_union] at hi
  simp_rw [← Function.comp_apply (f := Sigma.fst)] at hi
  exact ⟨i, hi.1, hi.2, funext fun a => (equiv_iff G f _ _).1 (xy a)⟩
#align first_order.language.direct_limit.exists_unify_eq FirstOrder.Language.DirectLimit.exists_unify_eq

theorem funMap_equiv_unify {n : ℕ} (F : L.Functions n) (x : Fin n → Σˣ f) (i : ι)
    (hi : i ∈ upperBounds (range (Sigma.fst ∘ x))) :
    funMap F x ≈ .mk f _ (funMap F (unify f x i hi)) :=
  funMap_unify_equiv G f F x (Classical.choose (Finite.bddAbove_range fun a => (x a).1)) i _ hi
#align first_order.language.direct_limit.fun_map_equiv_unify FirstOrder.Language.DirectLimit.funMap_equiv_unify

theorem relMap_equiv_unify {n : ℕ} (R : L.Relations n) (x : Fin n → Σˣ f) (i : ι)
    (hi : i ∈ upperBounds (range (Sigma.fst ∘ x))) :
    RelMap R x = RelMap R (unify f x i hi) :=
  relMap_unify_equiv G f R x (Classical.choose (Finite.bddAbove_range fun a => (x a).1)) i _ hi
#align first_order.language.direct_limit.rel_map_equiv_unify FirstOrder.Language.DirectLimit.relMap_equiv_unify

/-- The direct limit `setoid` respects the structure `sigmaStructure`, so quotienting by it
  gives rise to a valid structure. -/
noncomputable instance prestructure : L.Prestructure (DirectLimit.setoid G f) where
  toStructure := sigmaStructure G f
  fun_equiv {n} {F} x y xy := by
    obtain ⟨i, hx, hy, h⟩ := exists_unify_eq G f xy
    refine
      Setoid.trans (funMap_equiv_unify G f F x i hx)
        (Setoid.trans ?_ (Setoid.symm (funMap_equiv_unify G f F y i hy)))
    rw [h]
  rel_equiv {n} {R} x y xy := by
    obtain ⟨i, hx, hy, h⟩ := exists_unify_eq G f xy
    refine _root_.trans (relMap_equiv_unify G f R x i hx)
      (_root_.trans ?_ (symm (relMap_equiv_unify G f R y i hy)))
    rw [h]
#align first_order.language.direct_limit.prestructure FirstOrder.Language.DirectLimit.prestructure

/-- The `L.Structure` on a direct limit of `L.Structure`s. -/
noncomputable instance instStructureDirectLimit : L.Structure (DirectLimit G f) :=
  Language.quotientStructure
set_option linter.uppercaseLean3 false in
#align first_order.language.direct_limit.Structure FirstOrder.Language.DirectLimit.instStructureDirectLimit

@[simp]
theorem funMap_quotient_mk'_sigma_mk' {n : ℕ} {F : L.Functions n} {i : ι} {x : Fin n → G i} :
    funMap F (fun a => (⟦.mk f i (x a)⟧ : DirectLimit G f)) = ⟦.mk f i (funMap F x)⟧ := by
  simp only [funMap_quotient_mk', Quotient.eq]
  obtain ⟨k, ik, jk⟩ :=
    directed_of (· ≤ ·) i (Classical.choose (Finite.bddAbove_range fun _ : Fin n => i))
  refine ⟨k, jk, ik, ?_⟩
  simp only [Embedding.map_fun, comp_unify]
  rfl
#align first_order.language.direct_limit.fun_map_quotient_mk_sigma_mk FirstOrder.Language.DirectLimit.funMap_quotient_mk'_sigma_mk'

@[simp]
theorem relMap_quotient_mk'_sigma_mk' {n : ℕ} {R : L.Relations n} {i : ι} {x : Fin n → G i} :
    RelMap R (fun a => (⟦.mk f i (x a)⟧ : DirectLimit G f)) = RelMap R x := by
  rw [relMap_quotient_mk']
  obtain ⟨k, _, _⟩ :=
    directed_of (· ≤ ·) i (Classical.choose (Finite.bddAbove_range fun _ : Fin n => i))
  rw [relMap_equiv_unify G f R (fun a => .mk f i (x a)) i]
  rw [unify_sigma_mk_self]
#align first_order.language.direct_limit.rel_map_quotient_mk_sigma_mk FirstOrder.Language.DirectLimit.relMap_quotient_mk'_sigma_mk'

theorem exists_quotient_mk'_sigma_mk'_eq {α : Type*} [Finite α] (x : α → DirectLimit G f) :
    ∃ (i : ι) (y : α → G i), x = fun a => ⟦.mk f i (y a)⟧ := by
  obtain ⟨i, hi⟩ := Finite.bddAbove_range fun a => (x a).out.1
  refine ⟨i, unify f (Quotient.out ∘ x) i hi, ?_⟩
  ext a
  rw [Quotient.eq_mk_iff_out, unify]
  generalize_proofs r
  change _ ≈ .mk f i (f (Quotient.out (x a)).fst i r (Quotient.out (x a)).snd)
  have : (.mk f i (f (Quotient.out (x a)).fst i r (Quotient.out (x a)).snd) : Σˣ f).fst ≤ i :=
    le_rfl
  rw [equiv_iff G f (i := i) (hi _) this]
  · simp only [DirectedSystem.map_self]
  exact ⟨a, rfl⟩
#align first_order.language.direct_limit.exists_quotient_mk_sigma_mk_eq FirstOrder.Language.DirectLimit.exists_quotient_mk'_sigma_mk'_eq

variable (L ι)

/-- The canonical map from a component to the direct limit. -/
def of (i : ι) : G i ↪[L] DirectLimit G f where
  toFun := fun a => ⟦.mk f i a⟧
  inj' x y h := by
    rw [Quotient.eq] at h
    obtain ⟨j, h1, _, h3⟩ := h
    exact (f i j h1).injective h3
  map_fun' F x := by
    simp only
    rw [← funMap_quotient_mk'_sigma_mk']
    rfl
  map_rel' := by
    intro n R x
    change RelMap R (fun a => (⟦.mk f i (x a)⟧ : DirectLimit G f)) ↔ _
    simp only [relMap_quotient_mk'_sigma_mk']


#align first_order.language.direct_limit.of FirstOrder.Language.DirectLimit.of

variable {L ι G f}

@[simp]
theorem of_apply {i : ι} {x : G i} : of L ι G f i x = ⟦.mk f i x⟧ :=
  rfl
#align first_order.language.direct_limit.of_apply FirstOrder.Language.DirectLimit.of_apply

-- Porting note: removed the `@[simp]`, it is not in simp-normal form, but the simp-normal version
-- of this theorem would not be useful.
theorem of_f {i j : ι} {hij : i ≤ j} {x : G i} : of L ι G f j (f i j hij x) = of L ι G f i x := by
  rw [of_apply, of_apply, Quotient.eq]
  refine Setoid.symm ⟨j, hij, refl j, ?_⟩
  simp only [DirectedSystem.map_self]
#align first_order.language.direct_limit.of_f FirstOrder.Language.DirectLimit.of_f

/-- Every element of the direct limit corresponds to some element in
some component of the directed system. -/
theorem exists_of (z : DirectLimit G f) : ∃ i x, of L ι G f i x = z :=
  ⟨z.out.1, z.out.2, by simp⟩
#align first_order.language.direct_limit.exists_of FirstOrder.Language.DirectLimit.exists_of

@[elab_as_elim]
protected theorem inductionOn {C : DirectLimit G f → Prop} (z : DirectLimit G f)
    (ih : ∀ i x, C (of L ι G f i x)) : C z :=
  let ⟨i, x, h⟩ := exists_of z
  h ▸ ih i x
#align first_order.language.direct_limit.induction_on FirstOrder.Language.DirectLimit.inductionOn

theorem iSup_range_of_eq_top : ⨆ i, (of L ι G f i).toHom.range = ⊤ :=
  eq_top_iff.2 (fun x _ ↦ DirectLimit.inductionOn x
    (fun i _ ↦ le_iSup (fun i ↦ Hom.range (Embedding.toHom (of L ι G f i))) i (mem_range_self _)))

/-- Every finitely generated substructure of the direct limit corresponds to some
substructure in some component of the directed system. -/
theorem exists_fg_substructure_in_Sigma (S : L.Substructure (DirectLimit G f)) (S_fg : S.FG) :
    ∃ i, ∃ T : L.Substructure (G i), T.map (of L ι G f i).toHom = S := by
  let ⟨A, A_closure⟩ := S_fg
  let ⟨i, y, eq_y⟩ := exists_quotient_mk'_sigma_mk'_eq G _ (fun a : A ↦ a.1)
  use i
  use Substructure.closure L (range y)
  rw [Substructure.map_closure]
  simp only [Embedding.coe_toHom, of_apply]
  rw [← image_univ, image_image, image_univ, ← eq_y,
    Subtype.range_coe_subtype, Finset.setOf_mem, A_closure]

variable {P : Type u₁} [L.Structure P] (g : ∀ i, G i ↪[L] P)
variable (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
variable (L ι G f)

/-- The universal property of the direct limit: maps from the components to another module
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
def lift : DirectLimit G f ↪[L] P where
  toFun :=
    Quotient.lift (fun x : Σˣ f => (g x.1) x.2) fun x y xy => by
      simp only
      obtain ⟨i, hx, hy⟩ := directed_of (· ≤ ·) x.1 y.1
      rw [← Hg x.1 i hx, ← Hg y.1 i hy]
      exact congr_arg _ ((equiv_iff ..).1 xy)
  inj' x y xy := by
    rw [← Quotient.out_eq x, ← Quotient.out_eq y, Quotient.lift_mk, Quotient.lift_mk] at xy
    obtain ⟨i, hx, hy⟩ := directed_of (· ≤ ·) x.out.1 y.out.1
    rw [← Hg x.out.1 i hx, ← Hg y.out.1 i hy] at xy
    rw [← Quotient.out_eq x, ← Quotient.out_eq y, Quotient.eq, equiv_iff G f hx hy]
    exact (g i).injective xy
  map_fun' F x := by
    obtain ⟨i, y, rfl⟩ := exists_quotient_mk'_sigma_mk'_eq G f x
    change _ = funMap F (Quotient.lift _ _ ∘ Quotient.mk _ ∘ Structure.Sigma.mk f i ∘ y)
    rw [funMap_quotient_mk'_sigma_mk', ← Function.comp.assoc, Quotient.lift_comp_mk]
    simp only [Quotient.lift_mk, Embedding.map_fun]
    rfl
  map_rel' R x := by
    obtain ⟨i, y, rfl⟩ := exists_quotient_mk'_sigma_mk'_eq G f x
    change RelMap R (Quotient.lift _ _ ∘ Quotient.mk _ ∘ Structure.Sigma.mk f i ∘ y) ↔ _
    rw [relMap_quotient_mk'_sigma_mk' G f, ← (g i).map_rel R y, ← Function.comp.assoc,
      Quotient.lift_comp_mk]
    rfl
#align first_order.language.direct_limit.lift FirstOrder.Language.DirectLimit.lift

variable {L ι G f}

@[simp]
theorem lift_quotient_mk'_sigma_mk' {i} (x : G i) : lift L ι G f g Hg ⟦.mk f i x⟧ = (g i) x := by
  change (lift L ι G f g Hg).toFun ⟦.mk f i x⟧ = _
  simp only [lift, Quotient.lift_mk]
#align first_order.language.direct_limit.lift_quotient_mk_sigma_mk FirstOrder.Language.DirectLimit.lift_quotient_mk'_sigma_mk'

theorem lift_of {i} (x : G i) : lift L ι G f g Hg (of L ι G f i x) = g i x := by simp
#align first_order.language.direct_limit.lift_of FirstOrder.Language.DirectLimit.lift_of

theorem lift_unique (F : DirectLimit G f ↪[L] P) (x) :
    F x =
      lift L ι G f (fun i => F.comp <| of L ι G f i)
        (fun i j hij x => by rw [F.comp_apply, F.comp_apply, of_f]) x :=
  DirectLimit.inductionOn x fun i x => by rw [lift_of]; rfl
#align first_order.language.direct_limit.lift_unique FirstOrder.Language.DirectLimit.lift_unique

lemma range_lift : (lift L ι G f g Hg).toHom.range = ⨆ i, (g i).toHom.range := by
  simp_rw [Hom.range_eq_map]
  rw [← iSup_range_of_eq_top, Substructure.map_iSup]
  simp_rw [Hom.range_eq_map, Substructure.map_map]
  rfl

variable (L ι G f)
variable (G' : ι → Type w') [∀ i, L.Structure (G' i)]
variable (f' : ∀ i j, i ≤ j → G' i ↪[L] G' j)
variable (g : ∀ i, G i ≃[L] G' i)
variable (H_commuting : ∀ i j hij x, g j (f i j hij x) = f' i j hij (g i x))
variable [DirectedSystem G' fun i j h => f' i j h]

/-- The isomorphism between limits of isomorphic systems. -/
noncomputable def equiv_lift : DirectLimit G f ≃[L] DirectLimit G' f' := by
  let U i : G i ↪[L] DirectLimit G' f' := (of L _ G' f' i).comp (g i).toEmbedding
  let F : DirectLimit G f ↪[L] DirectLimit G' f' := lift L _ G f U <| by
    intro _ _ _ _
    simp only [U, Embedding.comp_apply, Equiv.coe_toEmbedding, H_commuting, of_f]
  have surj_f : Function.Surjective F := by
    intro x
    rcases x with ⟨i, pre_x⟩
    use of L _ G f i ((g i).symm pre_x)
    simp only [F, U, lift_of, Embedding.comp_apply, Equiv.coe_toEmbedding, Equiv.apply_symm_apply]
    rfl
  exact ⟨Equiv.ofBijective F ⟨F.injective, surj_f⟩, F.map_fun', F.map_rel'⟩

theorem equiv_lift_of {i : ι} (x : G i) :
    equiv_lift L ι G f G' f' g H_commuting (of L ι G f i x) = of L ι G' f' i (g i x) := rfl

variable {L ι G f}

/-- The direct limit of countably many countably generated structures is countably generated. -/
theorem cg {ι : Type*} [Countable ι] [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {G : ι → Type w} [∀ i, L.Structure (G i)] (f : ∀ i j, i ≤ j → G i ↪[L] G j)
    (h : ∀ i, Structure.CG L (G i)) [DirectedSystem G fun i j h => f i j h] :
    Structure.CG L (DirectLimit G f) := by
  refine ⟨⟨⋃ i, DirectLimit.of L ι G f i '' Classical.choose (h i).out, ?_, ?_⟩⟩
  · exact Set.countable_iUnion fun i => Set.Countable.image (Classical.choose_spec (h i).out).1 _
  · rw [eq_top_iff, Substructure.closure_unionᵢ]
    simp_rw [← Embedding.coe_toHom, Substructure.closure_image]
    rw [le_iSup_iff]
    intro S hS x _
    let out := Quotient.out (s := DirectLimit.setoid G f)
    refine hS (out x).1 ⟨(out x).2, ?_, ?_⟩
    · rw [(Classical.choose_spec (h (out x).1).out).2]
      trivial
    · simp only [out, Embedding.coe_toHom, DirectLimit.of_apply, Sigma.eta, Quotient.out_eq]
#align first_order.language.direct_limit.cg FirstOrder.Language.DirectLimit.cg

instance cg' {ι : Type*} [Countable ι] [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {G : ι → Type w} [∀ i, L.Structure (G i)] (f : ∀ i j, i ≤ j → G i ↪[L] G j)
    [h : ∀ i, Structure.CG L (G i)] [DirectedSystem G fun i j h => f i j h] :
    Structure.CG L (DirectLimit G f) :=
  cg f h
#align first_order.language.direct_limit.cg' FirstOrder.Language.DirectLimit.cg'

end DirectLimit

section Substructure

variable [Nonempty ι] [IsDirected ι (· ≤ ·)]
variable {M N : Type*} [L.Structure M] [L.Structure N] (S : ι →o L.Substructure M)

instance : DirectedSystem (fun i ↦ S i) (fun _ _ h ↦ Substructure.inclusion (S.monotone h)) where
  map_self' := fun _ _ _ ↦ rfl
  map_map' := fun _ _ _ ↦ rfl

namespace DirectLimit

/-- The map from a direct limit of a system of substructures of `M` into `M`. -/
def liftInclusion :
    DirectLimit (fun i ↦ S i) (fun _ _ h ↦ Substructure.inclusion (S.monotone h)) ↪[L] M :=
  DirectLimit.lift L ι (fun i ↦ S i) (fun _ _ h ↦ Substructure.inclusion (S.monotone h))
    (fun _ ↦ Substructure.subtype _) (fun _ _ _ _ ↦ rfl)

theorem liftInclusion_of {i : ι} (x : S i) :
    (liftInclusion S) (of L ι _ (fun _ _ h ↦ Substructure.inclusion (S.monotone h)) i x)
    = Substructure.subtype (S i) x := rfl

lemma rangeLiftInclusion : (liftInclusion S).toHom.range = ⨆ i, S i := by
  simp_rw [liftInclusion, range_lift, Substructure.range_subtype]

/-- The isomorphism between a direct limit of a system of substructures and their union. -/
noncomputable def Equiv_iSup :
    DirectLimit (fun i ↦ S i) (fun _ _ h ↦ Substructure.inclusion (S.monotone h)) ≃[L]
    (iSup S : L.Substructure M) := by
  have liftInclusion_in_sup : ∀ x, liftInclusion S x ∈ (⨆ i, S i) := by
    simp only [← rangeLiftInclusion, Hom.mem_range, Embedding.coe_toHom]
    intro x; use x
  let F := Embedding.codRestrict (⨆ i, S i) _ liftInclusion_in_sup
  have F_surj : Function.Surjective F := by
    rintro ⟨m, hm⟩
    rw [← rangeLiftInclusion, Hom.mem_range] at hm
    rcases hm with ⟨a, _⟩; use a
    simpa only [F, Embedding.codRestrict_apply', Subtype.mk.injEq]
  exact ⟨Equiv.ofBijective F ⟨F.injective, F_surj⟩, F.map_fun', F.map_rel'⟩

theorem Equiv_isup_of_apply {i : ι} (x : S i) :
    Equiv_iSup S (of L ι _ (fun _ _ h ↦ Substructure.inclusion (S.monotone h)) i x)
    = Substructure.inclusion (le_iSup _ _) x := rfl

theorem Equiv_isup_symm_inclusion_apply {i : ι} (x : S i) :
    (Equiv_iSup S).symm (Substructure.inclusion (le_iSup _ _) x)
    = of L ι _ (fun _ _ h ↦ Substructure.inclusion (S.monotone h)) i x := by
  apply (Equiv_iSup S).injective
  simp only [Equiv.apply_symm_apply]
  rfl

@[simp]
theorem Equiv_isup_symm_inclusion (i : ι) :
    (Equiv_iSup S).symm.toEmbedding.comp (Substructure.inclusion (le_iSup _ _))
    = of L ι _ (fun _ _ h ↦ Substructure.inclusion (S.monotone h)) i := by
  ext x; exact Equiv_isup_symm_inclusion_apply _ x

end DirectLimit

end Substructure

end Language

end FirstOrder
