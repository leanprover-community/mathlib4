/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Topology.Path

/-!
# Path connectedness

Continuing from `Mathlib/Topology/Path.lean`, this file defines path components and path-connected
spaces.

## Main definitions

In the file the unit interval `[0, 1]` in `ℝ` is denoted by `I`, and `X` is a topological space.

* `Joined (x y : X)` means there is a path between `x` and `y`.
* `Joined.somePath (h : Joined x y)` selects some path between two points `x` and `y`.
* `pathComponent (x : X)` is the set of points joined to `x`.
* `PathConnectedSpace X` is a predicate class asserting that `X` is non-empty and every two
  points of `X` are joined.

Then there are corresponding relative notions for `F : Set X`.

* `JoinedIn F (x y : X)` means there is a path `γ` joining `x` to `y` with values in `F`.
* `JoinedIn.somePath (h : JoinedIn F x y)` selects a path from `x` to `y` inside `F`.
* `pathComponentIn F (x : X)` is the set of points joined to `x` in `F`.
* `IsPathConnected F` asserts that `F` is non-empty and every two
  points of `F` are joined in `F`.

## Main theorems

* `Joined` is an equivalence relation, while `JoinedIn F` is at least symmetric and transitive.

One can link the absolute and relative version in two directions, using `(univ : Set X)` or the
subtype `↥F`.

* `pathConnectedSpace_iff_univ : PathConnectedSpace X ↔ IsPathConnected (univ : Set X)`
* `isPathConnected_iff_pathConnectedSpace : IsPathConnected F ↔ PathConnectedSpace ↥F`

Furthermore, it is shown that continuous images and quotients of path-connected sets/spaces are
path-connected, and that every path-connected set/space is also connected.
-/

noncomputable section

open Topology Filter unitInterval Set Function Pointwise

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X} {ι : Type*}

/-! ### Being joined by a path -/


/-- The relation "being joined by a path". This is an equivalence relation. -/
def Joined (x y : X) : Prop :=
  Nonempty (Path x y)

@[refl]
theorem Joined.refl (x : X) : Joined x x :=
  ⟨Path.refl x⟩

/-- When two points are joined, choose some path from `x` to `y`. -/
def Joined.somePath (h : Joined x y) : Path x y :=
  Nonempty.some h

@[symm]
theorem Joined.symm {x y : X} (h : Joined x y) : Joined y x :=
  ⟨h.somePath.symm⟩

@[trans]
theorem Joined.trans {x y z : X} (hxy : Joined x y) (hyz : Joined y z) : Joined x z :=
  ⟨hxy.somePath.trans hyz.somePath⟩

@[to_additive]
theorem Joined.mul {M : Type*} [Mul M] [TopologicalSpace M] [ContinuousMul M]
    {a b c d : M} (hs : Joined a b) (ht : Joined c d) : Joined (a * c) (b * d) :=
  ⟨hs.somePath.mul ht.somePath⟩

@[to_additive]
theorem Joined.listProd {M : Type*} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M]
    {l l' : List M} (h : List.Forall₂ Joined l l') :
    Joined l.prod l'.prod := by
  induction h with
  | nil => rfl
  | cons h₁ _ h₂ => exact h₁.mul h₂

@[to_additive]
theorem Joined.inv {G : Type*} [Inv G] [TopologicalSpace G] [ContinuousInv G]
    {x y : G} (h : Joined x y) : Joined x⁻¹ y⁻¹ :=
  ⟨h.somePath.inv⟩

variable (X)

/-- The setoid corresponding the equivalence relation of being joined by a continuous path. -/
def pathSetoid : Setoid X where
  r := Joined
  iseqv := Equivalence.mk Joined.refl Joined.symm Joined.trans

/-- The quotient type of points of a topological space modulo being joined by a continuous path. -/
def ZerothHomotopy :=
  Quotient (pathSetoid X)

instance ZerothHomotopy.inhabited : Inhabited (ZerothHomotopy ℝ) :=
  ⟨@Quotient.mk' ℝ (pathSetoid ℝ) 0⟩

variable {X}

/-! ### Being joined by a path inside a set -/


/-- The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not
reflexive for points that do not belong to `F`. -/
def JoinedIn (F : Set X) (x y : X) : Prop :=
  ∃ γ : Path x y, ∀ t, γ t ∈ F

variable {F : Set X}

theorem JoinedIn.mem (h : JoinedIn F x y) : x ∈ F ∧ y ∈ F := by
  rcases h with ⟨γ, γ_in⟩
  have : γ 0 ∈ F ∧ γ 1 ∈ F := by constructor <;> apply γ_in
  simpa using this

theorem JoinedIn.source_mem (h : JoinedIn F x y) : x ∈ F :=
  h.mem.1

theorem JoinedIn.target_mem (h : JoinedIn F x y) : y ∈ F :=
  h.mem.2

/-- When `x` and `y` are joined in `F`, choose a path from `x` to `y` inside `F` -/
def JoinedIn.somePath (h : JoinedIn F x y) : Path x y :=
  Classical.choose h

theorem JoinedIn.somePath_mem (h : JoinedIn F x y) (t : I) : h.somePath t ∈ F :=
  Classical.choose_spec h t

/-- If `x` and `y` are joined in the set `F`, then they are joined in the subtype `F`. -/
theorem JoinedIn.joined_subtype (h : JoinedIn F x y) :
    Joined (⟨x, h.source_mem⟩ : F) (⟨y, h.target_mem⟩ : F) :=
  ⟨{  toFun := fun t => ⟨h.somePath t, h.somePath_mem t⟩
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }⟩

theorem JoinedIn.ofLine {f : ℝ → X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y)
    (hF : f '' I ⊆ F) : JoinedIn F x y :=
  ⟨Path.ofLine hf h₀ h₁, fun t => hF <| Path.ofLine_mem hf h₀ h₁ t⟩

theorem JoinedIn.joined (h : JoinedIn F x y) : Joined x y :=
  ⟨h.somePath⟩

theorem joinedIn_iff_joined (x_in : x ∈ F) (y_in : y ∈ F) :
    JoinedIn F x y ↔ Joined (⟨x, x_in⟩ : F) (⟨y, y_in⟩ : F) :=
  ⟨fun h => h.joined_subtype, fun h => ⟨h.somePath.map continuous_subtype_val, by simp⟩⟩

@[simp]
theorem joinedIn_univ : JoinedIn univ x y ↔ Joined x y := by
  simp [JoinedIn, Joined, exists_true_iff_nonempty]

theorem JoinedIn.mono {U V : Set X} (h : JoinedIn U x y) (hUV : U ⊆ V) : JoinedIn V x y :=
  ⟨h.somePath, fun t => hUV (h.somePath_mem t)⟩

theorem JoinedIn.refl (h : x ∈ F) : JoinedIn F x x :=
  ⟨Path.refl x, fun _t => h⟩

@[symm]
theorem JoinedIn.symm (h : JoinedIn F x y) : JoinedIn F y x := by
  obtain ⟨hx, hy⟩ := h.mem
  simp_all only [joinedIn_iff_joined]
  exact h.symm

theorem JoinedIn.trans (hxy : JoinedIn F x y) (hyz : JoinedIn F y z) : JoinedIn F x z := by
  obtain ⟨hx, hy⟩ := hxy.mem
  obtain ⟨hx, hy⟩ := hyz.mem
  simp_all only [joinedIn_iff_joined]
  exact hxy.trans hyz

theorem Specializes.joinedIn (h : x ⤳ y) (hx : x ∈ F) (hy : y ∈ F) : JoinedIn F x y := by
  refine ⟨⟨⟨Set.piecewise {1} (const I y) (const I x), ?_⟩, by simp, by simp⟩, fun t ↦ ?_⟩
  · exact isClosed_singleton.continuous_piecewise_of_specializes continuous_const continuous_const
      fun _ ↦ h
  · simp only [Path.coe_mk_mk, piecewise]
    split_ifs <;> assumption

theorem Inseparable.joinedIn (h : Inseparable x y) (hx : x ∈ F) (hy : y ∈ F) : JoinedIn F x y :=
  h.specializes.joinedIn hx hy

theorem JoinedIn.map_continuousOn (h : JoinedIn F x y) {f : X → Y} (hf : ContinuousOn f F) :
    JoinedIn (f '' F) (f x) (f y) :=
  let ⟨γ, hγ⟩ := h
  ⟨γ.map' <| hf.mono (range_subset_iff.mpr hγ), fun t ↦ mem_image_of_mem _ (hγ t)⟩

theorem JoinedIn.map (h : JoinedIn F x y) {f : X → Y} (hf : Continuous f) :
    JoinedIn (f '' F) (f x) (f y) :=
  h.map_continuousOn hf.continuousOn

theorem Topology.IsInducing.joinedIn_image {f : X → Y} (hf : IsInducing f) (hx : x ∈ F)
    (hy : y ∈ F) : JoinedIn (f '' F) (f x) (f y) ↔ JoinedIn F x y := by
  refine ⟨?_, (.map · hf.continuous)⟩
  rintro ⟨γ, hγ⟩
  choose γ' hγ'F hγ' using hγ
  have h₀ : x ⤳ γ' 0 := by rw [← hf.specializes_iff, hγ', γ.source]
  have h₁ : γ' 1 ⤳ y := by rw [← hf.specializes_iff, hγ', γ.target]
  have h : JoinedIn F (γ' 0) (γ' 1) := by
    refine ⟨⟨⟨γ', ?_⟩, rfl, rfl⟩, hγ'F⟩
    simpa only [hf.continuous_iff, comp_def, hγ'] using map_continuous γ
  exact (h₀.joinedIn hx (hγ'F _)).trans <| h.trans <| h₁.joinedIn (hγ'F _) hy

@[to_additive]
theorem JoinedIn.mul {M : Type*} [Mul M] [TopologicalSpace M] [ContinuousMul M]
    {s t : Set M} {a b c d : M} (hs : JoinedIn s a b) (ht : JoinedIn t c d) :
    JoinedIn (s * t) (a * c) (b * d) :=
  ⟨hs.somePath.mul ht.somePath, fun t ↦ Set.mul_mem_mul (hs.somePath_mem t) (ht.somePath_mem t)⟩

@[to_additive]
theorem JoinedIn.inv {G : Type*} [InvolutiveInv G] [TopologicalSpace G] [ContinuousInv G]
    {s : Set G} {a b : G} (hs : JoinedIn s a b) :
    JoinedIn s⁻¹ a⁻¹ b⁻¹ :=
  ⟨hs.somePath.inv, fun t ↦ Set.inv_mem_inv.mpr (hs.somePath_mem t)⟩

/-! ### Path component -/

/-- The path component of `x` is the set of points that can be joined to `x`. -/
def pathComponent (x : X) :=
  { y | Joined x y }

theorem mem_pathComponent_iff : x ∈ pathComponent y ↔ Joined y x := .rfl

@[simp]
theorem mem_pathComponent_self (x : X) : x ∈ pathComponent x :=
  Joined.refl x

@[simp]
theorem pathComponent.nonempty (x : X) : (pathComponent x).Nonempty :=
  ⟨x, mem_pathComponent_self x⟩

theorem mem_pathComponent_of_mem (h : x ∈ pathComponent y) : y ∈ pathComponent x :=
  Joined.symm h

theorem pathComponent_symm : x ∈ pathComponent y ↔ y ∈ pathComponent x :=
  ⟨fun h => mem_pathComponent_of_mem h, fun h => mem_pathComponent_of_mem h⟩

theorem pathComponent_congr (h : x ∈ pathComponent y) : pathComponent x = pathComponent y := by
  ext z
  constructor
  · intro h'
    rw [pathComponent_symm]
    exact (h.trans h').symm
  · intro h'
    rw [pathComponent_symm] at h' ⊢
    exact h'.trans h

theorem pathComponent_subset_component (x : X) : pathComponent x ⊆ connectedComponent x :=
  fun y h =>
  (isConnected_range h.somePath.continuous).subset_connectedComponent ⟨0, by simp⟩ ⟨1, by simp⟩

/-- The path component of `x` in `F` is the set of points that can be joined to `x` in `F`. -/
def pathComponentIn (F : Set X) (x : X) :=
  { y | JoinedIn F x y }

@[simp]
theorem pathComponentIn_univ (x : X) : pathComponentIn univ x = pathComponent x := by
  simp [pathComponentIn, pathComponent, JoinedIn, Joined, exists_true_iff_nonempty]

theorem Joined.mem_pathComponent (hyz : Joined y z) (hxy : y ∈ pathComponent x) :
    z ∈ pathComponent x :=
  hxy.trans hyz

theorem mem_pathComponentIn_self (h : x ∈ F) : x ∈ pathComponentIn F x :=
  JoinedIn.refl h

theorem pathComponentIn_subset : pathComponentIn F x ⊆ F :=
  fun _ hy ↦ hy.target_mem

theorem pathComponentIn_nonempty_iff : (pathComponentIn F x).Nonempty ↔ x ∈ F :=
  ⟨fun ⟨_, ⟨γ, hγ⟩⟩ ↦ γ.source ▸ hγ 0, fun hx ↦ ⟨x, mem_pathComponentIn_self hx⟩⟩

theorem pathComponentIn_congr (h : x ∈ pathComponentIn F y) :
    pathComponentIn F x = pathComponentIn F y := by
  ext; exact ⟨h.trans, h.symm.trans⟩

@[gcongr]
theorem pathComponentIn_mono {G : Set X} (h : F ⊆ G) :
    pathComponentIn F x ⊆ pathComponentIn G x :=
  fun _ ⟨γ, hγ⟩ ↦ ⟨γ, fun t ↦ h (hγ t)⟩

/-! ### Path component of the identity in a group -/

/-- The path component of the identity in a topological monoid, as a submonoid. -/
@[to_additive (attr := simps) /-- The path component of the identity in an additive topological
monoid, as an additive submonoid. -/]
def Submonoid.pathComponentOne (M : Type*) [Monoid M] [TopologicalSpace M] [ContinuousMul M] :
    Submonoid M where
  carrier := pathComponent (1 : M)
  mul_mem' {m₁ m₂} hm₁ hm₂ := by simpa using hm₁.mul hm₂
  one_mem' := mem_pathComponent_self 1

/-- The path component of the identity in a topological group, as a subgroup. -/
@[to_additive (attr := simps!) /-- The path component of the identity in an additive topological
group, as an additive subgroup. -/]
def Subgroup.pathComponentOne (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Subgroup G where
  toSubmonoid := .pathComponentOne G
  inv_mem' {g} hg := by simpa using hg.inv

/-- The path component of the identity in a topological group is normal. -/
@[to_additive]
instance Subgroup.Normal.pathComponentOne (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : (Subgroup.pathComponentOne G).Normal where
  conj_mem _ := fun ⟨γ⟩ g ↦ ⟨⟨⟨(g * γ · * g⁻¹), by fun_prop⟩, by simp, by simp⟩⟩

/-! ### Path connected sets -/


/-- A set `F` is path connected if it contains a point that can be joined to all other in `F`. -/
def IsPathConnected (F : Set X) : Prop :=
  ∃ x ∈ F, ∀ ⦃y⦄, y ∈ F → JoinedIn F x y

theorem isPathConnected_iff_eq : IsPathConnected F ↔ ∃ x ∈ F, pathComponentIn F x = F := by
  constructor <;> rintro ⟨x, x_in, h⟩ <;> use x, x_in
  · ext y
    exact ⟨fun hy => hy.mem.2, @h _⟩
  · intro y y_in
    rwa [← h] at y_in

theorem IsPathConnected.joinedIn (h : IsPathConnected F) :
    ∀ᵉ (x ∈ F) (y ∈ F), JoinedIn F x y := fun _x x_in _y y_in =>
  let ⟨_b, _b_in, hb⟩ := h
  (hb x_in).symm.trans (hb y_in)

theorem isPathConnected_iff :
    IsPathConnected F ↔ F.Nonempty ∧ ∀ᵉ (x ∈ F) (y ∈ F), JoinedIn F x y :=
  ⟨fun h =>
    ⟨let ⟨b, b_in, _hb⟩ := h; ⟨b, b_in⟩, h.joinedIn⟩,
    fun ⟨⟨b, b_in⟩, h⟩ => ⟨b, b_in, h _ b_in⟩⟩

/-- If `f` is continuous on `F` and `F` is path-connected, so is `f(F)`. -/
theorem IsPathConnected.image' (hF : IsPathConnected F)
    {f : X → Y} (hf : ContinuousOn f F) : IsPathConnected (f '' F) := by
  rcases hF with ⟨x, x_in, hx⟩
  use f x, mem_image_of_mem f x_in
  rintro _ ⟨y, y_in, rfl⟩
  refine ⟨(hx y_in).somePath.map' ?_, fun t ↦ ⟨_, (hx y_in).somePath_mem t, rfl⟩⟩
  exact hf.mono (range_subset_iff.2 (hx y_in).somePath_mem)

/-- If `f` is continuous and `F` is path-connected, so is `f(F)`. -/
theorem IsPathConnected.image (hF : IsPathConnected F) {f : X → Y} (hf : Continuous f) :
    IsPathConnected (f '' F) :=
  hF.image' hf.continuousOn

@[to_additive]
theorem IsPathConnected.mul {M : Type*} [Mul M] [TopologicalSpace M] [ContinuousMul M]
    {s t : Set M} (hs : IsPathConnected s) (ht : IsPathConnected t) :
    IsPathConnected (s * t) :=
  let ⟨a, ha_mem, ha⟩ := hs; let ⟨b, hb_mem, hb⟩ := ht
  ⟨a * b, mul_mem_mul ha_mem hb_mem, Set.forall_mem_image2.2 fun _x hx _y hy ↦ (ha hx).mul (hb hy)⟩

@[to_additive]
theorem IsPathConnected.inv {G : Type*} [InvolutiveInv G] [TopologicalSpace G] [ContinuousInv G]
    {s : Set G} (hs : IsPathConnected s) :
    IsPathConnected s⁻¹ :=
  let ⟨a, ha_mem, ha⟩ := hs
  ⟨a⁻¹, inv_mem_inv.mpr ha_mem, fun x hx ↦ by simpa using ha (mem_inv.mp hx) |>.map continuous_inv⟩

/-- If `f : X → Y` is an inducing map, `f(F)` is path-connected iff `F` is. -/
nonrec theorem Topology.IsInducing.isPathConnected_iff {f : X → Y} (hf : IsInducing f) :
    IsPathConnected F ↔ IsPathConnected (f '' F) := by
  simp only [IsPathConnected, forall_mem_image, exists_mem_image]
  refine exists_congr fun x ↦ and_congr_right fun hx ↦ forall₂_congr fun y hy ↦ ?_
  rw [hf.joinedIn_image hx hy]

/-- If `h : X → Y` is a homeomorphism, `h(s)` is path-connected iff `s` is. -/
@[simp]
theorem Homeomorph.isPathConnected_image {s : Set X} (h : X ≃ₜ Y) :
    IsPathConnected (h '' s) ↔ IsPathConnected s :=
  h.isInducing.isPathConnected_iff.symm

/-- If `h : X → Y` is a homeomorphism, `h⁻¹(s)` is path-connected iff `s` is. -/
@[simp]
theorem Homeomorph.isPathConnected_preimage {s : Set Y} (h : X ≃ₜ Y) :
    IsPathConnected (h ⁻¹' s) ↔ IsPathConnected s := by
  rw [← Homeomorph.image_symm]; exact h.symm.isPathConnected_image

theorem IsPathConnected.mem_pathComponent (h : IsPathConnected F) (x_in : x ∈ F) (y_in : y ∈ F) :
    y ∈ pathComponent x :=
  (h.joinedIn x x_in y y_in).joined

theorem IsPathConnected.subset_pathComponent (h : IsPathConnected F) (x_in : x ∈ F) :
    F ⊆ pathComponent x := fun _y y_in => h.mem_pathComponent x_in y_in

theorem IsPathConnected.subset_pathComponentIn {s : Set X} (hs : IsPathConnected s)
    (hxs : x ∈ s) (hsF : s ⊆ F) : s ⊆ pathComponentIn F x :=
  fun y hys ↦ (hs.joinedIn x hxs y hys).mono hsF

theorem isPathConnected_singleton (x : X) : IsPathConnected ({x} : Set X) := by
  refine ⟨x, rfl, ?_⟩
  rintro y rfl
  exact JoinedIn.refl rfl

theorem isPathConnected_pathComponentIn (h : x ∈ F) : IsPathConnected (pathComponentIn F x) :=
  ⟨x, mem_pathComponentIn_self h, fun _ ⟨γ, hγ⟩ ↦ by
    refine ⟨γ, fun t ↦
      ⟨(γ.truncateOfLE t.2.1).cast (γ.extend_zero.symm) (γ.extend_extends' t).symm, fun t' ↦ ?_⟩⟩
    dsimp [Path.truncateOfLE, Path.truncate]
    exact γ.extend_extends' ⟨min (max t'.1 0) t.1, by simp [t.2.1, t.2.2]⟩ ▸ hγ _⟩

theorem isPathConnected_pathComponent : IsPathConnected (pathComponent x) := by
  rw [← pathComponentIn_univ]
  exact isPathConnected_pathComponentIn (mem_univ x)

theorem IsPathConnected.union {U V : Set X} (hU : IsPathConnected U) (hV : IsPathConnected V)
    (hUV : (U ∩ V).Nonempty) : IsPathConnected (U ∪ V) := by
  rcases hUV with ⟨x, xU, xV⟩
  use x, Or.inl xU
  rintro y (yU | yV)
  · exact (hU.joinedIn x xU y yU).mono subset_union_left
  · exact (hV.joinedIn x xV y yV).mono subset_union_right

/-- If a set `W` is path-connected, then it is also path-connected when seen as a set in a smaller
ambient type `U` (when `U` contains `W`). -/
theorem IsPathConnected.preimage_coe {U W : Set X} (hW : IsPathConnected W) (hWU : W ⊆ U) :
    IsPathConnected (((↑) : U → X) ⁻¹' W) := by
  rwa [IsInducing.subtypeVal.isPathConnected_iff, Subtype.image_preimage_val, inter_eq_right.2 hWU]

open Fin.NatCast in -- TODO: refactor to avoid needing this.
theorem IsPathConnected.exists_path_through_family {n : ℕ}
    {s : Set X} (h : IsPathConnected s) (p : Fin (n + 1) → X) (hp : ∀ i, p i ∈ s) :
    ∃ γ : Path (p 0) (p n), range γ ⊆ s ∧ ∀ i, p i ∈ range γ := by
  let p' : ℕ → X := fun k => if h : k < n + 1 then p ⟨k, h⟩ else p ⟨0, n.zero_lt_succ⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : Path (p' 0) (p' n), (∀ i ≤ n, p' i ∈ range γ) ∧ range γ ⊆ s := by
    have hp' : ∀ i ≤ n, p' i ∈ s := by
      intro i hi
      simp [p', Nat.lt_succ_of_le hi, hp]
    clear_value p'
    clear hp p
    induction n with
    | zero =>
      use Path.refl (p' 0)
      constructor
      · rintro i hi
        rw [Nat.le_zero.mp hi]
        exact ⟨0, rfl⟩
      · rw [range_subset_iff]
        rintro _x
        exact hp' 0 le_rfl
    | succ n hn =>
      rcases hn fun i hi => hp' i <| Nat.le_succ_of_le hi with ⟨γ₀, hγ₀⟩
      rcases h.joinedIn (p' n) (hp' n n.le_succ) (p' <| n + 1) (hp' (n + 1) <| le_rfl) with
        ⟨γ₁, hγ₁⟩
      let γ : Path (p' 0) (p' <| n + 1) := γ₀.trans γ₁
      use γ
      have range_eq : range γ = range γ₀ ∪ range γ₁ := γ₀.trans_range γ₁
      constructor
      · rintro i hi
        by_cases hi' : i ≤ n
        · rw [range_eq]
          left
          exact hγ₀.1 i hi'
        · rw [not_le, ← Nat.succ_le_iff] at hi'
          have : i = n.succ := le_antisymm hi hi'
          rw [this]
          use 1
          exact γ.target
      · grind [Set.union_subset, Set.range_subset_iff]
  have hpp' : ∀ k < n + 1, p k = p' k := by
    intro k hk
    simp only [p', hk, dif_pos]
    congr
    ext
    rw [Fin.val_cast_of_lt hk]
  use γ.cast (hpp' 0 n.zero_lt_succ) (hpp' n n.lt_succ_self)
  simp only [γ.cast_coe]
  refine And.intro hγ.2 ?_
  rintro ⟨i, hi⟩
  suffices p ⟨i, hi⟩ = p' i by convert hγ.1 i (Nat.le_of_lt_succ hi)
  rw [← hpp' i hi]
  suffices i = i % n.succ by congr
  rw [Nat.mod_eq_of_lt hi]

open Fin.NatCast in -- TODO: refactor to avoid needing this.
theorem IsPathConnected.exists_path_through_family' {n : ℕ}
    {s : Set X} (h : IsPathConnected s) (p : Fin (n + 1) → X) (hp : ∀ i, p i ∈ s) :
    ∃ (γ : Path (p 0) (p n)) (t : Fin (n + 1) → I), (∀ t, γ t ∈ s) ∧ ∀ i, γ (t i) = p i := by
  rcases h.exists_path_through_family p hp with ⟨γ, hγ⟩
  rcases hγ with ⟨h₁, h₂⟩
  simp only [range, mem_setOf_eq] at h₂
  rw [range_subset_iff] at h₁
  choose! t ht using h₂
  exact ⟨γ, t, h₁, ht⟩

/-! ### Path connected spaces -/


/-- A topological space is path-connected if it is non-empty and every two points can be
joined by a continuous path. -/
@[mk_iff]
class PathConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- A path-connected space must be nonempty. -/
  nonempty : Nonempty X
  /-- Any two points in a path-connected space must be joined by a continuous path. -/
  joined : ∀ x y : X, Joined x y

theorem pathConnectedSpace_iff_zerothHomotopy :
    PathConnectedSpace X ↔ Nonempty (ZerothHomotopy X) ∧ Subsingleton (ZerothHomotopy X) := by
  letI := pathSetoid X
  constructor
  · intro h
    refine ⟨(nonempty_quotient_iff _).mpr h.1, ⟨?_⟩⟩
    rintro ⟨x⟩ ⟨y⟩
    exact Quotient.sound (PathConnectedSpace.joined x y)
  · unfold ZerothHomotopy
    rintro ⟨h, h'⟩
    exact ⟨(nonempty_quotient_iff _).mp h, fun x y => Quotient.exact <| Subsingleton.elim ⟦x⟧ ⟦y⟧⟩

namespace PathConnectedSpace

variable [PathConnectedSpace X]

/-- Use path-connectedness to build a path between two points. -/
def somePath (x y : X) : Path x y :=
  Nonempty.some (joined x y)

end PathConnectedSpace

theorem pathConnectedSpace_iff_univ : PathConnectedSpace X ↔ IsPathConnected (univ : Set X) := by
  simp [pathConnectedSpace_iff, isPathConnected_iff, nonempty_iff_univ_nonempty]

theorem isPathConnected_iff_pathConnectedSpace : IsPathConnected F ↔ PathConnectedSpace F := by
  rw [pathConnectedSpace_iff_univ, IsInducing.subtypeVal.isPathConnected_iff, image_univ,
    Subtype.range_val_subtype, setOf_mem_eq]

theorem isPathConnected_univ [PathConnectedSpace X] : IsPathConnected (univ : Set X) :=
  pathConnectedSpace_iff_univ.mp inferInstance

theorem isPathConnected_range [PathConnectedSpace X] {f : X → Y} (hf : Continuous f) :
    IsPathConnected (range f) := by
  rw [← image_univ]
  exact isPathConnected_univ.image hf

theorem Function.Surjective.pathConnectedSpace [PathConnectedSpace X]
    {f : X → Y} (hf : Surjective f) (hf' : Continuous f) : PathConnectedSpace Y := by
  rw [pathConnectedSpace_iff_univ, ← hf.range_eq]
  exact isPathConnected_range hf'

instance Quotient.instPathConnectedSpace {s : Setoid X} [PathConnectedSpace X] :
    PathConnectedSpace (Quotient s) :=
  Quotient.mk'_surjective.pathConnectedSpace continuous_coinduced_rng

/-- This is a special case of `NormedSpace.instPathConnectedSpace` (and
`IsTopologicalAddGroup.pathConnectedSpace`). It exists only to simplify dependencies. -/
instance Real.instPathConnectedSpace : PathConnectedSpace ℝ where
  joined x y := ⟨⟨⟨fun (t : I) ↦ (1 - t) * x + t * y, by fun_prop⟩, by simp, by simp⟩⟩
  nonempty := inferInstance

theorem pathConnectedSpace_iff_eq : PathConnectedSpace X ↔ ∃ x : X, pathComponent x = univ := by
  simp [pathConnectedSpace_iff_univ, isPathConnected_iff_eq]

-- see Note [lower instance priority]
instance (priority := 100) PathConnectedSpace.connectedSpace [PathConnectedSpace X] :
    ConnectedSpace X := by
  rw [connectedSpace_iff_connectedComponent]
  rcases isPathConnected_iff_eq.mp (pathConnectedSpace_iff_univ.mp ‹_›) with ⟨x, _x_in, hx⟩
  use x
  rw [← univ_subset_iff]
  exact (by simpa using hx : pathComponent x = univ) ▸ pathComponent_subset_component x

theorem IsPathConnected.isConnected (hF : IsPathConnected F) : IsConnected F := by
  rw [isConnected_iff_connectedSpace]
  rw [isPathConnected_iff_pathConnectedSpace] at hF
  exact @PathConnectedSpace.connectedSpace _ _ hF

namespace PathConnectedSpace

variable [PathConnectedSpace X]

open Fin.NatCast in -- TODO: refactor to avoid needing this.
theorem exists_path_through_family {n : ℕ} (p : Fin (n + 1) → X) :
    ∃ γ : Path (p 0) (p n), ∀ i, p i ∈ range γ := by
  have : IsPathConnected (univ : Set X) := pathConnectedSpace_iff_univ.mp (by infer_instance)
  rcases this.exists_path_through_family p fun _i => True.intro with ⟨γ, -, h⟩
  exact ⟨γ, h⟩

open Fin.NatCast in -- TODO: refactor to avoid needing this.
theorem exists_path_through_family' {n : ℕ} (p : Fin (n + 1) → X) :
    ∃ (γ : Path (p 0) (p n)) (t : Fin (n + 1) → I), ∀ i, γ (t i) = p i := by
  have : IsPathConnected (univ : Set X) := pathConnectedSpace_iff_univ.mp (by infer_instance)
  rcases this.exists_path_through_family' p fun _i => True.intro with ⟨γ, t, -, h⟩
  exact ⟨γ, t, h⟩

end PathConnectedSpace
