/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Combinatorics.Tiling.Tile
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Tilings

This file defines some basic concepts related to tilings in a discrete context.

As definitions relating to tilings mostly are meaningful also for collections of tiles that may
overlap or may not cover the whole space, and such collections of tiles are also often of interest
when working with tilings, our formal definitions are generally made for indexed families of tiles
rather than having a specific type limited to a particular notion of tilings, and further
restrictions on such a family are given as hypotheses where needed. Since collections of possibly
overlapping tiles can be of interest, including the case where two tiles coincide, we work with
indexed families rather than sets (as usual, if a set of tiles is more convenient in a particular
case, it may be considered as a family indexed by itself).

## Main definitions

* `TileSet ps ιₜ`: An indexed family of images of tiles from the protoset `ps`.

* `TileSet.symmetryGroup`: The group of symmetries preserving a `TileSet` up to permutation of the
indices.

## References

* [Branko Grünbaum and G. C. Shephard, *Tilings and Patterns*][GrunbaumShephard1987]
-/


@[expose] public section

namespace DiscreteTiling

open Function
open scoped Pointwise

variable {G X ιₚ : Type*} [Group G] [MulAction G X]

variable {ps : Protoset G X ιₚ} {ι ιₜ ιₜ' ιₜ'' ιₜ''' E E' F : Type*} {ιₜι ιₜ'ι : ι → Type*}
variable [EquivLike E ιₜ' ιₜ] [EquivLike E' ιₜ'' ιₜ'] [FunLike F ιₜ' ιₜ] [EmbeddingLike F ιₜ' ιₜ]

variable (ps ιₜ) in
/-- A `TileSet ps ιₜ` is an indexed family of `PlacedTile ps`. This is a separate definition rather
than just using plain functions to facilitate defining associated API that can be used with dot
notation. -/
@[ext] structure TileSet where
  /-- The tiles in the family. Use the coercion to a function rather than using `tiles`
      directly. -/
  tiles : ιₜ → PlacedTile ps

namespace TileSet

instance [Nonempty ιₚ] : Nonempty (TileSet ps ιₜ) := ⟨⟨fun _ ↦ Classical.arbitrary _⟩⟩

instance [IsEmpty ιₜ] : Unique (TileSet ps ιₜ) where
  default := ⟨isEmptyElim⟩
  uniq _ := TileSet.ext <| funext isEmptyElim

instance : CoeFun (TileSet ps ιₜ) (fun _ ↦ ιₜ → PlacedTile ps) where
  coe := tiles

attribute [coe] tiles

lemma coe_mk (t) : (⟨t⟩ : TileSet ps ιₜ) = t := rfl

@[simp, norm_cast] lemma coe_inj {t₁ t₂ : TileSet ps ιₜ} :
    (t₁ : ιₜ → PlacedTile ps) = t₂ ↔ t₁ = t₂ :=
  TileSet.ext_iff.symm

lemma coe_injective : Injective (TileSet.tiles : TileSet ps ιₜ → ιₜ → PlacedTile ps) :=
  fun _ _ ↦ coe_inj.1

/-- Coercion from a `TileSet` to a set of tiles (losing information about the presence of
duplicate tiles in the `TileSet`). Use the coercion rather than using `coeSet` directly. -/
@[coe] def coeSet (t : TileSet ps ιₜ) : Set (PlacedTile ps) := Set.range t

instance : CoeOut (TileSet ps ιₜ) (Set (PlacedTile ps)) where
  coe := coeSet

instance : Membership (PlacedTile ps) (TileSet ps ιₜ) where
  mem t pt := pt ∈ (t : Set (PlacedTile ps))

@[simp] lemma mem_coeSet {pt : PlacedTile ps} {t : TileSet ps ιₜ} :
    pt ∈ (t : Set (PlacedTile ps)) ↔ pt ∈ t :=
  Iff.rfl

lemma coeSet_apply (t : TileSet ps ιₜ) : t = Set.range t := rfl

protected lemma mem_def {pt : PlacedTile ps} {t : TileSet ps ιₜ} : pt ∈ t ↔ ∃ i, t i = pt :=
  Iff.rfl

lemma apply_mem (t : TileSet ps ιₜ) (i : ιₜ) : t i ∈ t := Set.mem_range_self i

@[simp] lemma exists_mem_iff {t : TileSet ps ιₜ} {f : PlacedTile ps → Prop} :
    (∃ pt ∈ t, f pt) ↔ ∃ i, f (t i) := by
  simp_rw [← mem_coeSet, coeSet_apply, Set.exists_range_iff]

@[simp] lemma forall_mem_iff {t : TileSet ps ιₜ} {f : PlacedTile ps → Prop} :
    (∀ pt ∈ t, f pt) ↔ ∀ i, f (t i) := by
  simp_rw [← mem_coeSet, coeSet_apply, Set.forall_mem_range]

lemma union_of_mem_eq_iUnion (t : TileSet ps ιₜ) : ⋃ pt ∈ t, (pt : Set X) = ⋃ i, (t i : Set X) := by
  ext x
  simp

lemma nonempty_apply_of_forall_nonempty (t : TileSet ps ιₜ) (h : ∀ i, (ps i : Set X).Nonempty)
    (i : ιₜ) : (t i : Set X).Nonempty :=
  PlacedTile.coe_nonempty_iff.2 (h _)

lemma nonempty_of_forall_nonempty (t : TileSet ps ιₜ) (h : ∀ i, (ps i : Set X).Nonempty)
    {pt : PlacedTile ps} (hpt : pt ∈ t) : (pt : Set X).Nonempty := by
  rcases hpt with ⟨i, rfl⟩
  exact t.nonempty_apply_of_forall_nonempty h _

lemma finite_apply_of_forall_finite (t : TileSet ps ιₜ) (h : ∀ i, (ps i : Set X).Finite) (i : ιₜ) :
    (t i : Set X).Finite :=
  PlacedTile.coe_finite_iff.2 (h _)

lemma finite_of_forall_finite (t : TileSet ps ιₜ) (h : ∀ i, (ps i : Set X).Finite)
    {pt : PlacedTile ps} (hpt : pt ∈ t) : (pt : Set X).Finite := by
  rcases hpt with ⟨i, rfl⟩
  exact t.finite_apply_of_forall_finite h _

/-- Reindex a `TileSet` by composition with a function on index types (typically an equivalence for
it to literally be reindexing, though not required to be one in this definition). -/
def reindex (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) : TileSet ps ιₜ' where
  tiles := ↑t ∘ f

@[simp] lemma coe_reindex (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) : t.reindex f = ↑t ∘ f := rfl

@[simp] lemma reindex_apply (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) (i : ιₜ') :
    t.reindex f i = t (f i) :=
  rfl

@[simp] lemma reindex_id (t : TileSet ps ιₜ) : t.reindex id = t := rfl

lemma injective_reindex_iff_injective {t : TileSet ps ιₜ} {f : ιₜ' → ιₜ}
    (ht : Injective t) : Injective (↑t ∘ f) ↔ Injective f :=
  ht.of_comp_iff _

lemma injective_reindex_of_embeddingLike {t : TileSet ps ιₜ} (f : F) (ht : Injective t) :
    Injective (t.reindex f) :=
  (injective_reindex_iff_injective ht).2 <| EmbeddingLike.injective f

@[simp] lemma reindex_reindex (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) (f' : ιₜ'' → ιₜ') :
    (t.reindex f).reindex f' = t.reindex (f ∘ f') :=
  rfl

@[simp] lemma reindex_eq_reindex_iff_of_surjective {t₁ t₂ : TileSet ps ιₜ} {f : ιₜ' → ιₜ}
    (h : Surjective f) : t₁.reindex f = t₂.reindex f ↔ t₁ = t₂ := by
  refine ⟨fun he ↦ TileSet.ext <| funext <| h.forall.2 fun i ↦ ?_,
          fun he ↦ congrArg₂ _ he rfl⟩
  simp_rw [← reindex_apply, he]

@[simp] lemma reindex_eq_reindex_iff_of_equivLike {t₁ t₂ : TileSet ps ιₜ} (f : E) :
    t₁.reindex f = t₂.reindex f ↔ t₁ = t₂ :=
  reindex_eq_reindex_iff_of_surjective (EquivLike.surjective f)

@[simp] lemma reindex_comp_eq_reindex_comp_iff_of_surjective {t₁ t₂ : TileSet ps ιₜ}
    {f₁ f₂ : ιₜ' → ιₜ} {f : ιₜ'' → ιₜ'} (h : Surjective f) :
    t₁.reindex (f₁ ∘ f) = t₂.reindex (f₂ ∘ f) ↔ t₁.reindex f₁ = t₂.reindex f₂ := by
  rw [← reindex_reindex, ← reindex_reindex, reindex_eq_reindex_iff_of_surjective h]

@[simp] lemma reindex_comp_eq_reindex_comp_iff_of_equivLike {t₁ t₂ : TileSet ps ιₜ}
    {f₁ f₂ : ιₜ' → ιₜ} (f : E') :
    t₁.reindex (f₁ ∘ f) = t₂.reindex (f₂ ∘ f) ↔ t₁.reindex f₁ = t₂.reindex f₂ :=
  reindex_comp_eq_reindex_comp_iff_of_surjective (EquivLike.surjective f)

@[simp] lemma reindex_comp_eq_reindex_iff_of_surjective {t₁ t₂ : TileSet ps ιₜ} {f₁ : ιₜ → ιₜ}
    {f : ιₜ' → ιₜ} (h : Surjective f) :
    t₁.reindex (f₁ ∘ f) = t₂.reindex f ↔ t₁.reindex f₁ = t₂ := by
  rw [← reindex_reindex, reindex_eq_reindex_iff_of_surjective h]

@[simp] lemma reindex_comp_eq_reindex_iff_of_equivLike {t₁ t₂ : TileSet ps ιₜ} {f₁ : ιₜ → ιₜ}
    (f : E) : t₁.reindex (f₁ ∘ f) = t₂.reindex f ↔ t₁.reindex f₁ = t₂ :=
  reindex_comp_eq_reindex_iff_of_surjective (EquivLike.surjective f)

@[simp] lemma reindex_eq_reindex_comp_iff_of_surjective {t₁ t₂ : TileSet ps ιₜ} {f₁ : ιₜ → ιₜ}
    {f : ιₜ' → ιₜ} (h : Surjective f) :
    t₁.reindex f = t₂.reindex (f₁ ∘ f) ↔ t₁ = t₂.reindex f₁ := by
  rw [← reindex_reindex, reindex_eq_reindex_iff_of_surjective h]

@[simp] lemma reindex_eq_reindex_comp_iff_of_equivLike {t₁ t₂ : TileSet ps ιₜ} {f₁ : ιₜ → ιₜ}
    (f : E) : t₁.reindex f = t₂.reindex (f₁ ∘ f) ↔ t₁ = t₂.reindex f₁ :=
  reindex_eq_reindex_comp_iff_of_surjective (EquivLike.surjective f)

lemma coeSet_reindex_eq_range_comp (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) :
    (t.reindex f : Set (PlacedTile ps)) = Set.range (t ∘ f) :=
  rfl

lemma coeSet_reindex_subset (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) :
    (t.reindex f : Set (PlacedTile ps)) ⊆ t := Set.range_comp_subset_range f t

lemma mem_of_mem_reindex {t : TileSet ps ιₜ} {f : ιₜ' → ιₜ} {pt : PlacedTile ps}
    (h : pt ∈ t.reindex f) : pt ∈ t :=
  Set.mem_of_mem_of_subset h <| t.coeSet_reindex_subset f

lemma mem_reindex_iff {t : TileSet ps ιₜ} {f : ιₜ' → ιₜ} {pt : PlacedTile ps} :
    pt ∈ (t.reindex f) ↔ ∃ i, t (f i) = pt :=
  Set.mem_range

@[simp] lemma coeSet_reindex_of_surjective (t : TileSet ps ιₜ) {f : ιₜ' → ιₜ} (h : Surjective f) :
    (t.reindex f : Set (PlacedTile ps)) = t :=
  h.range_comp _

@[simp] lemma coeSet_reindex_of_equivLike (t : TileSet ps ιₜ) (f : E) :
    (t.reindex f : Set (PlacedTile ps)) = t :=
  t.coeSet_reindex_of_surjective <| EquivLike.surjective f

@[simp] lemma mem_reindex_iff_of_surjective {t : TileSet ps ιₜ} {f : ιₜ' → ιₜ} {pt : PlacedTile ps}
    (h : Surjective f) : pt ∈ t.reindex f ↔ pt ∈ t :=
  iff_of_eq <| congrArg (pt ∈ ·) <| t.coeSet_reindex_of_surjective h

@[simp] lemma mem_reindex_iff_of_equivLike {t : TileSet ps ιₜ} (f : E) {pt : PlacedTile ps} :
    pt ∈ t.reindex f ↔ pt ∈ t :=
  mem_reindex_iff_of_surjective <| EquivLike.surjective f

/-- If two `TileSet`s have the same set of tiles and no duplicate tiles, this equivalence maps
one index type to the other. -/
noncomputable def equivOfCoeSetEqOfInjective {t₁ : TileSet ps ιₜ} {t₂ : TileSet ps ιₜ'}
    (h : (t₁ : Set (PlacedTile ps)) = t₂) (h₁ : Injective t₁) (h₂ : Injective t₂) : ιₜ' ≃ ιₜ :=
  ((Equiv.ofInjective t₂ h₂).trans (Equiv.cast (congrArg _ h.symm))).trans
    (Equiv.ofInjective t₁ h₁).symm

@[simp] lemma reindex_equivOfCoeSetEqOfInjective {t₁ : TileSet ps ιₜ} {t₂ : TileSet ps ιₜ'}
    (h : (t₁ : Set (PlacedTile ps)) = t₂) (h₁ : Injective t₁) (h₂ : Injective t₂) :
    t₁.reindex (equivOfCoeSetEqOfInjective h h₁ h₂) = t₂ := by
  ext i : 2
  simp only [equivOfCoeSetEqOfInjective, Equiv.coe_trans, reindex_apply, comp_apply,
    Equiv.ofInjective_apply, Equiv.cast_apply]
  erw [Equiv.apply_ofInjective_symm h₁]
  rw [Subtype.coe_eq_iff]
  simp_rw [coeSet_apply] at h
  refine ⟨h ▸ Set.mem_range_self _, ?_⟩
  rw [cast_eq_iff_heq, Subtype.heq_iff_coe_eq]
  simp [h]

instance : MulAction G (TileSet ps ιₜ) where
  smul g t := ⟨(g • ·) ∘ ↑t⟩
  one_smul _ := TileSet.ext <| funext <| fun _ ↦ one_smul _ _
  mul_smul _ _ _ := TileSet.ext <| funext <| fun _ ↦ mul_smul _ _ _

lemma smul_coe (g : G) (t : TileSet ps ιₜ) : (g • t : TileSet ps ιₜ) = (g • ·) ∘ ↑t := rfl

lemma smul_apply (g : G) (t : TileSet ps ιₜ) (i : ιₜ) : (g • t) i = g • (t i) := rfl

@[simp] lemma smul_mem_smul_apply_iff (g : G) {x : X} {t : TileSet ps ιₜ} {i : ιₜ} :
    g • x ∈ (g • t) i ↔ x ∈ t i :=
  PlacedTile.smul_mem_smul_iff g

lemma mem_smul_apply_iff_smul_inv_mem {g : G} {x : X} {t : TileSet ps ιₜ} {i : ιₜ} :
    x ∈ (g • t) i ↔ g⁻¹ • x ∈ t i :=
  PlacedTile.mem_smul_iff_smul_inv_mem

lemma mem_inv_smul_apply_iff_smul_mem {g : G} {x : X} {t : TileSet ps ιₜ} {i : ιₜ} :
    x ∈ (g⁻¹ • t) i ↔ g • x ∈ t i :=
  PlacedTile.mem_inv_smul_iff_smul_mem

@[simp] lemma smul_reindex (g : G) (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) :
    g • (t.reindex f) = (g • t).reindex f :=
  rfl

@[simp] lemma injective_smul_iff (g : G) {t : TileSet ps ιₜ} : Injective (g • t) ↔ Injective t :=
  Injective.of_comp_iff (MulAction.injective g) t

@[simp] lemma coeSet_smul (g : G) (t : TileSet ps ιₜ) :
    (g • t : TileSet ps ιₜ) = g • (t : Set (PlacedTile ps)) := by
  simp [coeSet_apply, smul_coe, Set.range_comp]

@[simp] lemma smul_mem_smul_iff {pt : PlacedTile ps} (g : G) {t : TileSet ps ιₜ} :
    g • pt ∈ g • t ↔ pt ∈ t := by
  rw [← mem_coeSet, ← mem_coeSet, coeSet_smul, Set.smul_mem_smul_set_iff]

lemma mem_smul_iff_smul_inv_mem {pt : PlacedTile ps} {g : G} {t : TileSet ps ιₜ} :
    pt ∈ g • t ↔ g⁻¹ • pt ∈ t := by
  simp_rw [← mem_coeSet, coeSet_smul, Set.mem_smul_set_iff_inv_smul_mem]

lemma mem_inv_smul_iff_smul_mem {pt : PlacedTile ps} {g : G} {t : TileSet ps ιₜ} :
    pt ∈ g⁻¹ • t ↔ g • pt ∈ t := by
  simp_rw [← mem_coeSet, coeSet_smul, Set.mem_inv_smul_set_iff]

@[simp] lemma smul_inter_smul (g : G) (t : TileSet ps ιₜ) (s : Set X) (i : ιₜ) :
    g • s ∩ (g • t) i = g • (s ∩ t i) := by
  simp [smul_apply, Set.smul_set_inter]

/-- The action of both a group element and a permutation of the index type on a `TileSet`, used
in defining the symmetry group. -/
instance : MulAction (G × Equiv.Perm ιₜ) (TileSet ps ιₜ) where
  smul g t := (g.fst • t).reindex g.snd.symm
  one_smul _ := TileSet.ext <| funext <| fun _ ↦ one_smul _ _
  mul_smul g h t := TileSet.ext <| funext <| fun i ↦ by
    change (g.1 * h.1) • t ((g.2 * h.2)⁻¹ i) = g.1 • h.1 • t (h.2⁻¹ (g.2⁻¹ i))
    simp [mul_smul]

lemma smul_prod_eq_reindex (g : G) (f : Equiv.Perm ιₜ) (t : TileSet ps ιₜ) :
    (g, f) • t = (g • t).reindex f.symm :=
  rfl

lemma smul_prod_apply (g : G) (f : Equiv.Perm ιₜ) (t : TileSet ps ιₜ) (i : ιₜ) :
    ((g, f) • t) i = g • t (f.symm i) :=
  rfl

@[simp] lemma smul_prod_one (g : G) (t : TileSet ps ιₜ) : (g, (1 : Equiv.Perm ιₜ)) • t = g • t :=
  rfl

@[simp] lemma smul_prod_refl (g : G) (t : TileSet ps ιₜ) :
    (g, (Equiv.refl ιₜ : Equiv.Perm ιₜ)) • t = g • t :=
  rfl

/-- The symmetry group of a `TileSet ps ιₜ` is the subgroup of `G` that preserves the tiles up to
permutation of the indices. -/
def symmetryGroup (t : TileSet ps ιₜ) : Subgroup G :=
  (MulAction.stabilizer (G × Equiv.Perm ιₜ) t).map (MonoidHom.fst _ _)

/-- A group element is in the symmetry group if and only if there is a permutation of the indices
such that mapping by the group element and that permutation preserves the `TileSet`. -/
lemma mem_symmetryGroup_iff_exists {t : TileSet ps ιₜ} {g : G} :
    g ∈ t.symmetryGroup ↔ ∃ f : Equiv.Perm ιₜ, (g • t).reindex f = t := by
  simp_rw [symmetryGroup, Subgroup.mem_map, MulAction.mem_stabilizer_iff]
  change (∃ x : G × Equiv.Perm ιₜ, _ ∧ x.1 = g) ↔ _
  refine ⟨fun ⟨⟨g', f⟩, ⟨h, hg⟩⟩ ↦ ⟨f.symm, ?_⟩, fun ⟨f, h⟩ ↦ ⟨(g, f.symm), h, rfl⟩⟩
  dsimp only at hg
  subst hg
  exact h

/-- If `g` is in the symmetry group, the image of any tile under `g` is in `t`. -/
lemma exists_smul_eq_of_mem_symmetryGroup {t : TileSet ps ιₜ} {g : G} (i : ιₜ)
    (hg : g ∈ t.symmetryGroup) : ∃ j, g • (t i) = t j := by
  rw [mem_symmetryGroup_iff_exists] at hg
  rcases hg with ⟨f, h⟩
  refine ⟨f.symm i, ?_⟩
  nth_rewrite 2 [← h]
  simp [TileSet.smul_apply]

/-- If `g` is in the symmetry group, every tile in `t` is the image under `g` of some tile in
`t`. -/
lemma exists_smul_eq_of_mem_symmetryGroup' {t : TileSet ps ιₜ} {g : G} (i : ιₜ)
    (hg : g ∈ t.symmetryGroup) : ∃ j, g • (t j) = t i := by
  rcases exists_smul_eq_of_mem_symmetryGroup i (inv_mem hg) with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  simp [← hj]

/-- If `g` is in the symmetry group, the image of any tile under `g` is in `t`. -/
lemma smul_mem_of_mem_of_mem_symmetryGroup {t : TileSet ps ιₜ} {g : G} {pt : PlacedTile ps}
    (hg : g ∈ t.symmetryGroup) (hpt : pt ∈ t) : g • pt ∈ t := by
  rcases hpt with ⟨i, rfl⟩
  simp_rw [TileSet.mem_def, eq_comm]
  exact exists_smul_eq_of_mem_symmetryGroup i hg

/-- If `g` is in the symmetry group, every tile in `t` is the image under `g` of some tile in
`t`. -/
lemma exists_smul_eq_of_mem_of_mem_symmetryGroup {t : TileSet ps ιₜ} {g : G} {pt : PlacedTile ps}
    (hg : g ∈ t.symmetryGroup) (hpt : pt ∈ t) : ∃ pt' ∈ t, g • pt' = pt := by
  rcases hpt with ⟨i, rfl⟩
  rw [exists_mem_iff]
  exact exists_smul_eq_of_mem_symmetryGroup' i hg

@[simp] lemma symmetryGroup_of_isEmpty [IsEmpty ιₜ] (t : TileSet ps ιₜ) : t.symmetryGroup = ⊤ := by
  ext g
  rw [mem_symmetryGroup_iff_exists]
  simp only [Subgroup.mem_top, iff_true]
  exact ⟨Equiv.refl _, Subsingleton.elim _ _⟩

@[simp] lemma symmetryGroup_reindex (t : TileSet ps ιₜ) (f : E) :
    (t.reindex f).symmetryGroup = t.symmetryGroup := by
  ext g
  simp_rw [mem_symmetryGroup_iff_exists]
  refine ⟨fun ⟨e, he⟩ ↦ ?_, fun ⟨e, he⟩ ↦ ?_⟩
  · refine ⟨((EquivLike.toEquiv f).symm.trans e).trans (EquivLike.toEquiv f), ?_⟩
    rw [← reindex_eq_reindex_iff_of_equivLike f, ← he]
    simp [comp_assoc]
  · refine ⟨((EquivLike.toEquiv f).trans e).trans (EquivLike.toEquiv f).symm, ?_⟩
    nth_rewrite 2 [← he]
    simp [← comp_assoc]

@[simp] lemma symmetryGroup_reindex_of_bijective (t : TileSet ps ιₜ) {f : ιₜ' → ιₜ}
    (h : Bijective f) : (t.reindex f).symmetryGroup = t.symmetryGroup :=
  t.symmetryGroup_reindex <| Equiv.ofBijective f h

/-- Mapping the `TileSet` by a group element acts on the symmetry group by conjugation. -/
lemma symmetryGroup_smul (t : TileSet ps ιₜ) (g : G) :
    (g • t).symmetryGroup = (ConjAct.toConjAct g) • t.symmetryGroup := by
  simp_rw [← smul_prod_one, symmetryGroup, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  ext h
  simp only [Subgroup.mem_map, MulAction.mem_stabilizer_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, Prod.inv_mk, inv_one, Prod.exists, Prod.mk_mul_mk, one_mul, mul_one,
    MonoidHom.coe_fst, Prod.mk.injEq, exists_eq_right_right, exists_and_right, exists_eq_right,
    Subgroup.mem_smul_pointwise_iff_exists, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
  rw [exists_comm]
  convert Iff.rfl
  rw [exists_and_right]

lemma mem_symmetryGroup_smul_iff {t : TileSet ps ιₜ} (g : G) {g' : G} :
    g * g' * g⁻¹ ∈ (g • t).symmetryGroup ↔ g' ∈ t.symmetryGroup := by
  simp [symmetryGroup_smul, Subgroup.mem_smul_pointwise_iff_exists, ConjAct.smul_def]

lemma mem_symmetryGroup_smul_iff' {t : TileSet ps ιₜ} {g g' : G} :
    g' ∈ (g • t).symmetryGroup ↔ g⁻¹ * g' * g ∈ t.symmetryGroup := by
  convert mem_symmetryGroup_smul_iff g
  simp [mul_assoc]

lemma symmetryGroup_le_stabilizer_coeSet (t : TileSet ps ιₜ) :
    t.symmetryGroup ≤ MulAction.stabilizer G (t : Set (PlacedTile ps)) := by
  simp_rw [SetLike.le_def, mem_symmetryGroup_iff_exists, MulAction.mem_stabilizer_iff]
  rintro g ⟨f, hf⟩
  nth_rewrite 2 [← hf]
  simp

lemma symmetryGroup_eq_stabilizer_coeSet_of_injective (t : TileSet ps ιₜ) (h : Injective t) :
    t.symmetryGroup = MulAction.stabilizer G (t : Set (PlacedTile ps)) := by
  refine le_antisymm t.symmetryGroup_le_stabilizer_coeSet ?_
  simp_rw [SetLike.le_def, mem_symmetryGroup_iff_exists, MulAction.mem_stabilizer_iff]
  intro g hg
  rw [← coeSet_smul] at hg
  exact ⟨equivOfCoeSetEqOfInjective hg ((injective_smul_iff g).2 h) h, by simp⟩

/-- The disjoint union of two `TileSet`s, indexed by the sum of their index types. -/
protected def sum (t : TileSet ps ιₜ) (t' : TileSet ps ιₜ') : TileSet ps (ιₜ ⊕ ιₜ') where
  tiles := Sum.elim t.tiles t'.tiles

@[simp] lemma coe_sum (t : TileSet ps ιₜ) (t' : TileSet ps ιₜ') : t.sum t' = Sum.elim (↑t) (↑t') :=
  rfl

@[simp] lemma coeSet_sum (t : TileSet ps ιₜ) (t' : TileSet ps ιₜ') :
    (t.sum t' : Set (PlacedTile ps)) = (↑t) ∪ (↑t') :=
  Set.Sum.elim_range _ _

@[simp] lemma mem_sum {pt : PlacedTile ps} {t : TileSet ps ιₜ} {t' : TileSet ps ιₜ'} :
    pt ∈ t.sum t' ↔ pt ∈ t ∨ pt ∈ t' := by
  simp [← mem_coeSet]

lemma reindex_sum (t : TileSet ps ιₜ) (t' : TileSet ps ιₜ'') (f : ιₜ' → ιₜ) (f' : ιₜ''' → ιₜ'') :
    (t.sum t').reindex (Sum.map f f') = (t.reindex f).sum (t'.reindex f') :=
  TileSet.ext <| funext fun x ↦ Sum.recOn x (fun _ ↦ rfl) (fun _ ↦ rfl)

lemma smul_sum (g : G) (t : TileSet ps ιₜ) (t' : TileSet ps ιₜ') :
    g • (t.sum t') = (g • t).sum (g • t') :=
  TileSet.ext <| funext fun x ↦ Sum.recOn x (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- The disjoint union of an indexed family of `TileSet`s, indexed by a sigma type. -/
protected def sigma (t : (i : ι) → TileSet ps (ιₜι i)) : TileSet ps (Σ i, ιₜι i) where
  tiles := Sigma.uncurry (fun i ↦ ↑(t i))

@[simp] lemma coe_sigma (t : (i : ι) → TileSet ps (ιₜι i)) :
    TileSet.sigma t = Sigma.uncurry (fun i ↦ ↑(t i)) :=
  rfl

@[simp] lemma coeSet_sigma (t : (i : ι) → TileSet ps (ιₜι i)) :
    (TileSet.sigma t : Set (PlacedTile ps)) = ⋃ i, (t i : Set (PlacedTile ps)) :=
  Set.range_sigma_eq_iUnion_range _

lemma mem_sigma {pt : PlacedTile ps} {t : (i : ι) → TileSet ps (ιₜι i)} :
    pt ∈ TileSet.sigma t ↔ ∃ i, pt ∈ t i := by
  simp [← mem_coeSet]

lemma reindex_sigma (t : (i : ι) → TileSet ps (ιₜι i)) (f : (i : ι) → (ιₜ'ι i) → (ιₜι i)) :
    (TileSet.sigma t).reindex (Sigma.map id f) = TileSet.sigma fun i ↦ (t i).reindex (f i) :=
  rfl

lemma smul_sigma (g : G) (t : (i : ι) → TileSet ps (ιₜι i)) :
    g • TileSet.sigma t = TileSet.sigma (g • t) :=
  rfl

end TileSet

end DiscreteTiling
