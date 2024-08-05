/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Gabin Kolly
-/
import Mathlib.Data.Fintype.Order
import Mathlib.Algebra.DirectLimit
import Mathlib.ModelTheory.Quotients
import Mathlib.ModelTheory.FinitelyGenerated
import Mathlib.Order.Ideal
import Mathlib.PartialEquiv

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
* `FirstOrder.Language.DirectLimit.partialEquiv_limit` is the limit of a directed system
  of PartialEquivs.

## Main Results
* `FirstOrder.Language.BackAndForth.embedding_from_cg` For a countably generated structure `M`
  and a structure `N`, if any PartialEquiv between finitely generated substructures
  can be extended to any element in the domain, then there exists an embedding of `M` in `N`.
* `FirstOrder.Language.BackAndForth.equiv_between_cg` For two countably generated structure
  `M` and `N`, if any PartialEquiv between finitely generated substructures can be extended to
  any element in the domain and to any element in the codomain, then there exists an equivalence
  between `M` and `N`.
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

/-- A copy of `DirectedSystem.map_map` specialized to `L`-embeddings, as otherwise the
`fun i j h ↦ f i j h` can confuse the simplifier. -/
nonrec theorem map_map [DirectedSystem G fun i j h => f i j h] {i j k} (hij hjk x) :
    f j k hjk (f i j hij x) = f i k (le_trans hij hjk) x :=
  DirectedSystem.map_map (fun i j h => f i j h) hij hjk x

variable {G' : ℕ → Type w} [∀ i, L.Structure (G' i)] (f' : ∀ n : ℕ, G' n ↪[L] G' (n + 1))

/-- Given a chain of embeddings of structures indexed by `ℕ`, defines a `DirectedSystem` by
composing them. -/
def natLERec (m n : ℕ) (h : m ≤ n) : G' m ↪[L] G' n :=
  Nat.leRecOn h (@fun k g => (f' k).comp g) (Embedding.refl L _)

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

instance natLERec.directedSystem : DirectedSystem G' fun i j h => natLERec f' i j h :=
  ⟨fun i x _ => congr (congr rfl (Nat.leRecOn_self _)) rfl,
   fun hij hjk => by simp [Nat.leRecOn_trans hij hjk]⟩

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

variable [DirectedSystem G fun i j h => f i j h]

@[simp]
theorem unify_sigma_mk_self {α : Type*} {i : ι} {x : α → G i} :
    (unify f (fun a => .mk f i (x a)) i fun j ⟨a, hj⟩ =>
      _root_.trans (le_of_eq hj.symm) (refl _)) = x := by
  ext a
  rw [unify]
  apply DirectedSystem.map_self

theorem comp_unify {α : Type*} {x : α → Σˣ f} {i j : ι} (ij : i ≤ j)
    (h : i ∈ upperBounds (range (Sigma.fst ∘ x))) :
    f i j ij ∘ unify f x i h = unify f x j
      fun k hk => _root_.trans (mem_upperBounds.1 h k hk) ij := by
  ext a
  simp [unify, DirectedSystem.map_map]

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
          rw [← DirectedSystem.map_map, ← hjk, DirectedSystem.map_map]
          assumption
        assumption⟩

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

end DirectLimit

/-- The direct limit of a directed system is the structures glued together along the embeddings. -/
def DirectLimit [DirectedSystem G fun i j h => f i j h] [IsDirected ι (· ≤ ·)] :=
  Quotient (DirectLimit.setoid G f)

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

theorem funMap_unify_equiv {n : ℕ} (F : L.Functions n) (x : Fin n → Σˣ f) (i j : ι)
    (hi : i ∈ upperBounds (range (Sigma.fst ∘ x))) (hj : j ∈ upperBounds (range (Sigma.fst ∘ x))) :
    Structure.Sigma.mk f i (funMap F (unify f x i hi)) ≈ .mk f j (funMap F (unify f x j hj)) := by
  obtain ⟨k, ik, jk⟩ := directed_of (· ≤ ·) i j
  refine ⟨k, ik, jk, ?_⟩
  rw [(f i k ik).map_fun, (f j k jk).map_fun, comp_unify, comp_unify]

theorem relMap_unify_equiv {n : ℕ} (R : L.Relations n) (x : Fin n → Σˣ f) (i j : ι)
    (hi : i ∈ upperBounds (range (Sigma.fst ∘ x))) (hj : j ∈ upperBounds (range (Sigma.fst ∘ x))) :
    RelMap R (unify f x i hi) = RelMap R (unify f x j hj) := by
  obtain ⟨k, ik, jk⟩ := directed_of (· ≤ ·) i j
  rw [← (f i k ik).map_rel, comp_unify, ← (f j k jk).map_rel, comp_unify]

variable [Nonempty ι]

theorem exists_unify_eq {α : Type*} [Finite α] {x y : α → Σˣ f} (xy : x ≈ y) :
    ∃ (i : ι) (hx : i ∈ upperBounds (range (Sigma.fst ∘ x)))
      (hy : i ∈ upperBounds (range (Sigma.fst ∘ y))), unify f x i hx = unify f y i hy := by
  obtain ⟨i, hi⟩ := Finite.bddAbove_range (Sum.elim (fun a => (x a).1) fun a => (y a).1)
  rw [Sum.elim_range, upperBounds_union] at hi
  simp_rw [← Function.comp_apply (f := Sigma.fst)] at hi
  exact ⟨i, hi.1, hi.2, funext fun a => (equiv_iff G f _ _).1 (xy a)⟩

theorem funMap_equiv_unify {n : ℕ} (F : L.Functions n) (x : Fin n → Σˣ f) (i : ι)
    (hi : i ∈ upperBounds (range (Sigma.fst ∘ x))) :
    funMap F x ≈ .mk f _ (funMap F (unify f x i hi)) :=
  funMap_unify_equiv G f F x (Classical.choose (Finite.bddAbove_range fun a => (x a).1)) i _ hi

theorem relMap_equiv_unify {n : ℕ} (R : L.Relations n) (x : Fin n → Σˣ f) (i : ι)
    (hi : i ∈ upperBounds (range (Sigma.fst ∘ x))) :
    RelMap R x = RelMap R (unify f x i hi) :=
  relMap_unify_equiv G f R x (Classical.choose (Finite.bddAbove_range fun a => (x a).1)) i _ hi

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

/-- The `L.Structure` on a direct limit of `L.Structure`s. -/
noncomputable instance instStructureDirectLimit : L.Structure (DirectLimit G f) :=
  Language.quotientStructure

@[simp]
theorem funMap_quotient_mk'_sigma_mk' {n : ℕ} {F : L.Functions n} {i : ι} {x : Fin n → G i} :
    funMap F (fun a => (⟦.mk f i (x a)⟧ : DirectLimit G f)) = ⟦.mk f i (funMap F x)⟧ := by
  simp only [funMap_quotient_mk', Quotient.eq]
  obtain ⟨k, ik, jk⟩ :=
    directed_of (· ≤ ·) i (Classical.choose (Finite.bddAbove_range fun _ : Fin n => i))
  refine ⟨k, jk, ik, ?_⟩
  simp only [Embedding.map_fun, comp_unify]
  rfl

@[simp]
theorem relMap_quotient_mk'_sigma_mk' {n : ℕ} {R : L.Relations n} {i : ι} {x : Fin n → G i} :
    RelMap R (fun a => (⟦.mk f i (x a)⟧ : DirectLimit G f)) = RelMap R x := by
  rw [relMap_quotient_mk']
  obtain ⟨k, _, _⟩ :=
    directed_of (· ≤ ·) i (Classical.choose (Finite.bddAbove_range fun _ : Fin n => i))
  rw [relMap_equiv_unify G f R (fun a => .mk f i (x a)) i]
  rw [unify_sigma_mk_self]

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



variable {L ι G f}

@[simp]
theorem of_apply {i : ι} {x : G i} : of L ι G f i x = ⟦.mk f i x⟧ :=
  rfl

-- Porting note: removed the `@[simp]`, it is not in simp-normal form, but the simp-normal version
-- of this theorem would not be useful.
theorem of_f {i j : ι} {hij : i ≤ j} {x : G i} : of L ι G f j (f i j hij x) = of L ι G f i x := by
  rw [of_apply, of_apply, Quotient.eq]
  refine Setoid.symm ⟨j, hij, refl j, ?_⟩
  simp only [DirectedSystem.map_self]

/-- Every element of the direct limit corresponds to some element in
some component of the directed system. -/
theorem exists_of (z : DirectLimit G f) : ∃ i x, of L ι G f i x = z :=
  ⟨z.out.1, z.out.2, by simp⟩

@[elab_as_elim]
protected theorem inductionOn {C : DirectLimit G f → Prop} (z : DirectLimit G f)
    (ih : ∀ i x, C (of L ι G f i x)) : C z :=
  let ⟨i, x, h⟩ := exists_of z
  h ▸ ih i x

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

variable {L ι G f}

@[simp]
theorem lift_quotient_mk'_sigma_mk' {i} (x : G i) : lift L ι G f g Hg ⟦.mk f i x⟧ = (g i) x := by
  change (lift L ι G f g Hg).toFun ⟦.mk f i x⟧ = _
  simp only [lift, Quotient.lift_mk]

theorem lift_of {i} (x : G i) : lift L ι G f g Hg (of L ι G f i x) = g i x := by simp

theorem lift_unique (F : DirectLimit G f ↪[L] P) (x) :
    F x =
      lift L ι G f (fun i => F.comp <| of L ι G f i)
        (fun i j hij x => by rw [F.comp_apply, F.comp_apply, of_f]) x :=
  DirectLimit.inductionOn x fun i x => by rw [lift_of]; rfl

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
  · rw [eq_top_iff, Substructure.closure_iUnion]
    simp_rw [← Embedding.coe_toHom, Substructure.closure_image]
    rw [le_iSup_iff]
    intro S hS x _
    let out := Quotient.out (s := DirectLimit.setoid G f)
    refine hS (out x).1 ⟨(out x).2, ?_, ?_⟩
    · rw [(Classical.choose_spec (h (out x).1).out).2]
      trivial
    · simp only [out, Embedding.coe_toHom, DirectLimit.of_apply, Sigma.eta, Quotient.out_eq]

instance cg' {ι : Type*} [Countable ι] [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {G : ι → Type w} [∀ i, L.Structure (G i)] (f : ∀ i j, i ≤ j → G i ↪[L] G j)
    [h : ∀ i, Structure.CG L (G i)] [DirectedSystem G fun i j h => f i j h] :
    Structure.CG L (DirectLimit G f) :=
  cg f h

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

open Substructure.PartialEquiv

variable [Nonempty ι] [IsDirected ι (· ≤ ·)]
variable (S : ι →o M ≃ₚ[L] N)

instance : DirectedSystem (fun i ↦ (S i).dom) (fun _ _ h ↦
  Substructure.inclusion (dom_le_dom (S.monotone h))) where
  map_self' := fun _ _ _ ↦ rfl
  map_map' := fun _ _ _ ↦ rfl

instance : DirectedSystem (fun i ↦ (S i).cod) (fun _ _ h ↦
  Substructure.inclusion (cod_le_cod (S.monotone h))) where
  map_self' := fun _ _ _ ↦ rfl
  map_map' := fun _ _ _ ↦ rfl

/-- The limit of a directed system of PartialEquivs.-/
noncomputable def partialEquiv_limit : M ≃ₚ[L] N where
  dom := iSup (fun i ↦ (S i).dom)
  cod := iSup (fun i ↦ (S i).cod)
  equiv :=
    (DirectLimit.Equiv_iSup {
      toFun := (fun i ↦ (S i).cod)
      monotone' := monotone_cod.comp S.monotone}
    ).comp
      ((DirectLimit.equiv_lift L ι (fun i ↦ (S i).dom)
        (fun _ _ hij ↦ Substructure.inclusion (dom_le_dom (S.monotone hij)))
        (fun i ↦ (S i).cod)
        (fun _ _ hij ↦ Substructure.inclusion (cod_le_cod (S.monotone hij)))
        (fun i ↦ (S i).equiv)
        (fun _ _ hij _ ↦ equiv_inclusion_apply (S.monotone hij) _)
      ).comp
        (DirectLimit.Equiv_iSup {
          toFun := (fun i ↦ (S i).dom)
          monotone' := monotone_dom.comp S.monotone}).symm)

@[simp]
theorem partialEquiv_limit_dom : (partialEquiv_limit S).dom = iSup (fun x ↦ (S x).dom) := rfl

@[simp]
theorem partialEquiv_limit_cod : (partialEquiv_limit S).cod = iSup (fun x ↦ (S x).cod) := rfl

-- the proof is a hack right now, I didn't know how to handle subtle differences in proof terms
-- that prevented me from just using equalities proved previously
theorem le_partialEquiv_limit : ∀ i, S i ≤ partialEquiv_limit S := by
  intro i
  refine ⟨by simp; apply le_iSup (f := fun i ↦ (S i).dom), ?_⟩
  unfold partialEquiv_limit
  ext x
  simp only [OrderHom.coe_mk, Embedding.comp_apply, Substructure.coe_inclusion,
    Equiv.coe_toEmbedding, Equiv.comp_apply]
  refine DirectLimit.Equiv_isup_symm_inclusion_apply
    { toFun := fun i ↦ (S i).dom
      monotone' := monotone_dom.comp S.monotone} x ▸ ?_
  refine DirectLimit.equiv_lift_of L ι (fun i ↦ (S i).dom)
        (fun _ _ hij ↦ Substructure.inclusion (dom_le_dom (S.monotone hij)))
      (fun i ↦ (S i).cod)
      (fun _ _ hij ↦ Substructure.inclusion (cod_le_cod (S.monotone hij)))
      (fun i ↦ (S i).equiv)
      (fun _ _ hij _ ↦ equiv_inclusion_apply (S.monotone hij) _)
      x ▸ ?_
  rw [DirectLimit.equiv_lift_of]
  refine DirectLimit.Equiv_isup_of_apply
    { toFun := fun i ↦ (S i).cod
      monotone' := monotone_cod.comp S.monotone} ((S i).equiv x) ▸ ?_
  rw [DirectLimit.Equiv_isup_of_apply]
  rfl

end DirectLimit

namespace BackAndForth

open PartialEquiv

open DirectLimit

variable (M) (N) (L)

/-- The type of equivalences between finitely generated substructures. -/
def FiniteEquiv := {f : M ≃ₚ[L] N // f.dom.FG}

instance : PartialOrder (FiniteEquiv L M N) := Subtype.partialOrder _

instance FiniteEquivToPartialEquiv : Coe (FiniteEquiv L M N) (M ≃ₚ[L] N) := {coe := Subtype.val}

variable {M} {N} {L}

theorem FiniteEquiv.subtype_val_monotone : Monotone (Subtype.val : FiniteEquiv L M N → M ≃ₚ[L] N) :=
  fun _ _ h ↦ Subtype.coe_le_coe.2 h

/-- The cofinal set of finite equivalences with a given element in their domain. -/
noncomputable def definedAtLeft
    (h : ∀ f : (M ≃ₚ[L] N), ∀ _ : f.dom.FG, ∀ m : M, ∃ g : (M ≃ₚ[L] N), f ≤ g ∧ m ∈ g.dom)
    (m : M) : Order.Cofinal (FiniteEquiv L M N) where
  carrier := {f | m ∈ f.val.dom}
  mem_gt := by
    intro f
    rcases h f.val f.2 m with ⟨g, f_le_g, m_in_dom⟩
    have closure_le_dom : (Substructure.closure L (f.val.dom ∪ {m})) ≤ g.dom := by
      rw [Substructure.closure_le, union_subset_iff]
      exact ⟨dom_le_dom f_le_g, singleton_subset_iff.2 m_in_dom⟩
    have closure_fg : (Substructure.closure L (f.val.dom ∪ {m})).FG := by
      rw [Substructure.closure_union, Substructure.closure_eq]
      exact Substructure.FG.sup f.property (Substructure.fg_closure_singleton _)
    use ⟨domRestrict g closure_le_dom, closure_fg⟩
    constructor
    · simp only [union_singleton]
      exact Substructure.subset_closure <| mem_insert_iff.2 <| Or.inl <| refl m
    · apply le_domRestrict
      rw [Substructure.closure_union]
      simp only [Substructure.closure_eq, ge_iff_le,
        Substructure.closure_le, singleton_subset_iff, le_sup_left]
      exact f_le_g

/-- The cofinal set of finite equivalences with a given element in their codomain. -/
noncomputable def definedAtRight
  (h : ∀ f : (M ≃ₚ[L] N), ∀ _ : f.dom.FG, ∀ n : N, ∃ g : (M ≃ₚ[L] N), f ≤ g ∧ n ∈ g.cod)
  (n : N) : Order.Cofinal (FiniteEquiv L M N) where
  carrier := {f | n ∈ f.val.cod}
  mem_gt := by
    intro f
    rcases h f.val f.2 n with ⟨g, f_le_g, n_in_cod⟩
    have closure_le_cod : (Substructure.closure L (f.val.cod ∪ {n})) ≤ g.cod := by
      rw [Substructure.closure_le, union_subset_iff]
      exact ⟨cod_le_cod f_le_g, singleton_subset_iff.2 n_in_cod⟩
    have closure_fg : (Substructure.closure L (f.val.cod ∪ {n})).FG := by
      rw [Substructure.closure_union, Substructure.closure_eq]
      exact Substructure.FG.sup ((f.1.fg_iff).1 f.prop) (Substructure.fg_closure_singleton _)
    use ⟨codRestrict g closure_le_cod, (codRestrict g closure_le_cod).fg_iff.2 closure_fg⟩
    constructor
    · simp only [union_singleton]
      exact Substructure.subset_closure <| mem_insert_iff.2 <| Or.inl <| refl n
    · apply le_codRestrict
      rw [Substructure.closure_union]
      simp only [Substructure.closure_eq, ge_iff_le,
        Substructure.closure_le, singleton_subset_iff, le_sup_left]
      exact f_le_g

theorem back_iff_symm_of_forth :
    (∀ f : (M ≃ₚ[L] N), ∀ _ : f.dom.FG, ∀ n : N, ∃ g : (M ≃ₚ[L] N), f ≤ g ∧ n ∈ g.cod) ↔
    ∀ f : (N ≃ₚ[L] M), ∀ _ : f.dom.FG, ∀ n : N, ∃ g : (N ≃ₚ[L] M), f ≤ g ∧ n ∈ g.dom := by
  constructor <;>
  · intro H f fg x
    let ⟨g, g_prop⟩ := H f.symm (f.fg_iff.1 fg) x
    use g.symm
    convert g_prop
    exact symm_le_iff.symm

/-- For a countably generated structure `M` and a structure `N`, if any partial equivalence
between finitely generated substructures can be extended to any element in the domain,
then there exists an embedding of `M` in `N`. -/
theorem embedding_from_cg (M_cg : Structure.CG L M) (h : (M ≃ₚ[L] N)) (h_fg : h.dom.FG)
    (H : ∀ f : M ≃ₚ[L] N, ∀ _ : f.dom.FG, ∀ m : M, ∃ g : (M ≃ₚ[L] N), f ≤ g ∧ m ∈ g.dom) :
    ∃ f : M ↪[L] N, h ≤ f.toPartialEquiv := by
  rcases M_cg with ⟨X, _, X_gen⟩
  have _ : Countable (↑X : Type _) := by simpa only [countable_coe_iff]
  have _ : Encodable (↑X : Type _) := Encodable.ofCountable _
  let D : X → Order.Cofinal (FiniteEquiv L M N) := fun x ↦ definedAtLeft H x
  let S : ℕ →o M ≃ₚ[L] N :=
    ⟨Subtype.val ∘ (Order.sequenceOfCofinals ⟨h, h_fg⟩ D),
      FiniteEquiv.subtype_val_monotone.comp (Order.sequenceOfCofinals.monotone _ _)⟩
  let F := partialEquiv_limit S
  have _ : X ⊆ F.dom := by
    intro x hx
    have := Order.sequenceOfCofinals.encode_mem ⟨h, h_fg⟩ D ⟨x, hx⟩
    exact dom_le_dom
      (le_partialEquiv_limit S (Encodable.encode (⟨x, hx⟩ : X) + 1)) this
  have isTop : F.dom = ⊤ := by rwa [← top_le_iff, ← X_gen, Substructure.closure_le]
  exact ⟨dom_top_toEmbedding isTop,
        by convert (le_partialEquiv_limit S 0); apply Embedding.toPartialEquiv_toEmbedding⟩

/-- For two countably generated structure `M` and `N`, if any PartialEquiv
between finitely generated substructures can be extended to any element in the domain and to
any element in the codomain, then there exists an equivalence between `M` and `N`. -/
theorem equiv_between_cg (M_cg : Structure.CG L M) (N_cg : Structure.CG L N)
    (h : (M ≃ₚ[L] N)) (h_fg : h.dom.FG)
    (ext_dom : ∀ f : M ≃ₚ[L] N, ∀ _ : f.dom.FG, ∀ m : M, ∃ g : (M ≃ₚ[L] N),
      f ≤ g ∧ m ∈ g.dom)
    (ext_cod : ∀ f : M ≃ₚ[L] N, ∀ _ : f.dom.FG, ∀ n : N, ∃ g : (M ≃ₚ[L] N),
      f ≤ g ∧ n ∈ g.cod) :
    ∃ f : M ≃[L] N, h ≤ f.toEmbedding.toPartialEquiv := by
  rcases M_cg with ⟨X, X_count, X_gen⟩
  rcases N_cg with ⟨Y, Y_count, Y_gen⟩
  have _ : Countable (↑X : Type _) := by simpa only [countable_coe_iff]
  have _ : Encodable (↑X : Type _) := Encodable.ofCountable _
  have _ : Countable (↑Y : Type _) := by simpa only [countable_coe_iff]
  have _ : Encodable (↑Y : Type _) := Encodable.ofCountable _
  let D : Sum X Y → Order.Cofinal (FiniteEquiv L M N) := fun p ↦
    Sum.recOn p (fun x ↦ definedAtLeft ext_dom x) (fun y ↦ definedAtRight ext_cod y)
  let S : ℕ →o M ≃ₚ[L] N :=
    ⟨Subtype.val ∘ (Order.sequenceOfCofinals ⟨h, h_fg⟩ D),
      FiniteEquiv.subtype_val_monotone.comp (Order.sequenceOfCofinals.monotone _ _)⟩
  let F := DirectLimit.partialEquiv_limit S
  have _ : X ⊆ F.dom := by
    intro x hx
    have := Order.sequenceOfCofinals.encode_mem ⟨h, h_fg⟩ D (Sum.inl ⟨x, hx⟩)
    exact dom_le_dom
      (le_partialEquiv_limit S (Encodable.encode (Sum.inl (⟨x, hx⟩ : X)) + 1)) this
  have _ : Y ⊆ F.cod := by
    intro y hy
    have := Order.sequenceOfCofinals.encode_mem ⟨h, h_fg⟩ D (Sum.inr ⟨y, hy⟩)
    exact cod_le_cod
      (le_partialEquiv_limit S (Encodable.encode (Sum.inr (⟨y, hy⟩ : Y)) + 1)) this
  have dom_top : F.dom = ⊤ := by rwa [← top_le_iff, ← X_gen, Substructure.closure_le]
  have cod_top : F.cod = ⊤ := by rwa [← top_le_iff, ← Y_gen, Substructure.closure_le]
  refine ⟨dom_cod_top_toEquiv dom_top cod_top, ?_⟩
  convert le_partialEquiv_limit S 0
  rw [dom_cod_top_toEquiv_toEmbedding]
  apply Embedding.toPartialEquiv_toEmbedding

end BackAndForth

end Substructure

end Language

end FirstOrder
