
#exit
section

variable {G : Type v} [Group G] (A : Rep k G) (S : Subgroup G)
  [S.Normal] [Representation.IsTrivial (A.ρ.comp S.subtype)]

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` which is trivial on `S` factors
through `G ⧸ S`. -/
abbrev ofQuotient : Rep k (G ⧸ S) := Rep.of (A.ρ.ofQuotient S)


/-- A `G`-representation `A` on which a normal subgroup `S ≤ G` acts trivially induces a
`G ⧸ S`-representation on `A`, and composing this with the quotient map `G → G ⧸ S` gives the
original representation by definition. Useful for typechecking. -/
abbrev resOfQuotientIso [Representation.IsTrivial (A.ρ.comp S.subtype)] :
    (Action.res _ (QuotientGroup.mk' S)).obj (A.ofQuotient S) ≅ A := Iso.refl _

end

variable (A : Rep k G)

/-- Given a `k`-linear `G`-representation `(V, ρ)`, this is the representation defined by
restricting `ρ` to a `G`-invariant `k`-submodule of `V`. -/
abbrev subrepresentation (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    Rep k G :=
  Rep.of (A.ρ.subrepresentation W le_comap)

/-- The natural inclusion of a subrepresentation into the ambient representation. -/
@[simps]
def subtype (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    subrepresentation A W le_comap ⟶ A where
  hom := ModuleCat.ofHom W.subtype
  comm _ := rfl

/-- Given a `k`-linear `G`-representation `(V, ρ)` and a `G`-invariant `k`-submodule `W ≤ V`, this
is the representation induced on `V ⧸ W` by `ρ`. -/
abbrev quotient (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    Rep k G :=
  Rep.of (A.ρ.quotient W le_comap)

/-- The natural projection from a representation to its quotient by a subrepresentation. -/
@[simps]
def mkQ (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    A ⟶ quotient A W le_comap where
  hom := ModuleCat.ofHom <| Submodule.mkQ _
  comm _ := rfl

instance : PreservesLimits (forget₂ (Rep k G) (ModuleCat.{u} k)) :=
  Action.preservesLimits_forget _ _

instance : PreservesColimits (forget₂ (Rep k G) (ModuleCat.{u} k)) :=
  Action.preservesColimits_forget _ _

theorem epi_iff_surjective {A B : Rep k G} (f : A ⟶ B) : Epi f ↔ Function.Surjective f.hom :=
  ⟨fun _ => (ModuleCat.epi_iff_surjective ((forget₂ _ _).map f)).1 inferInstance,
  fun h => (forget₂ _ _).epi_of_epi_map ((ModuleCat.epi_iff_surjective <|
    (forget₂ _ _).map f).2 h)⟩

theorem mono_iff_injective {A B : Rep k G} (f : A ⟶ B) : Mono f ↔ Function.Injective f.hom :=
  ⟨fun _ => (ModuleCat.mono_iff_injective ((forget₂ _ _).map f)).1 inferInstance,
  fun h => (forget₂ _ _).mono_of_mono_map ((ModuleCat.mono_iff_injective <|
    (forget₂ _ _).map f).2 h)⟩

instance {A B : Rep k G} (f : A ⟶ B) [Mono f] : Mono f.hom :=
  inferInstanceAs <| Mono ((forget₂ _ _).map f)

instance {A B : Rep k G} (f : A ⟶ B) [Epi f] : Epi f.hom :=
  inferInstanceAs <| Epi ((forget₂ _ _).map f)

open MonoidalCategory in
@[simp]
theorem tensor_ρ {A B : Rep k G} : (A ⊗ B).ρ = A.ρ.tprod B.ρ := rfl

@[simp]
lemma res_obj_ρ {H : Type u} [Monoid H] (f : G →* H) (A : Rep k H) :
    ρ ((Action.res _ f).obj A) = A.ρ.comp f := rfl

@[simp]
lemma coe_res_obj_ρ {H : Type u} [Monoid H] (f : G →* H) (A : Rep k H) (g : G) :
    DFunLike.coe (F := G →* (A →ₗ[k] A)) (ρ ((Action.res _ f).obj A)) g = A.ρ (f g) := rfl

section Linearization

variable (k G)

/-- The monoidal functor sending a type `H` with a `G`-action to the induced `k`-linear
`G`-representation on `k[H].` -/
def linearization : (Action (Type u) G) ⥤ (Rep k G) :=
  (ModuleCat.free k).mapAction G

instance : (linearization k G).Monoidal := by
  dsimp only [linearization]
  infer_instance

variable {k G}

@[simp]
theorem coe_linearization_obj (X : Action (Type u) G) :
    (linearization k G).obj X = (X.V →₀ k) := rfl

theorem linearization_obj_ρ (X : Action (Type u) G) (g : G) :
    ((linearization k G).obj X).ρ g = Finsupp.lmapDomain k k (X.ρ g) :=
  rfl

@[simp]
theorem coe_linearization_obj_ρ (X : Action (Type u) G) (g : G) :
    @DFunLike.coe (no_index G →* ((X.V →₀ k) →ₗ[k] (X.V →₀ k))) _
      (fun _ => (X.V →₀ k) →ₗ[k] (X.V →₀ k)) _
      ((linearization k G).obj X).ρ g = Finsupp.lmapDomain k k (X.ρ g) := rfl

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): helps fixing `linearizationTrivialIso` since change in behaviour of `ext`.
theorem linearization_single (X : Action (Type u) G) (g : G) (x : X.V) (r : k) :
    ((linearization k G).obj X).ρ g (Finsupp.single x r) = Finsupp.single (X.ρ g x) r := by
  simp

variable {X Y : Action (Type u) G} (f : X ⟶ Y)

@[simp]
theorem linearization_map_hom : ((linearization k G).map f).hom =
    ModuleCat.ofHom (Finsupp.lmapDomain k k f.hom) :=
  rfl

theorem linearization_map_hom_single (x : X.V) (r : k) :
    ((linearization k G).map f).hom (Finsupp.single x r) = Finsupp.single (f.hom x) r :=
  Finsupp.mapDomain_single

open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

@[simp]
theorem linearization_μ_hom (X Y : Action (Type u) G) :
    (μ (linearization k G) X Y).hom =
      ModuleCat.ofHom (finsuppTensorFinsupp' k X.V Y.V).toLinearMap :=
  rfl

@[simp]
theorem linearization_δ_hom (X Y : Action (Type u) G) :
    (δ (linearization k G) X Y).hom =
      ModuleCat.ofHom (finsuppTensorFinsupp' k X.V Y.V).symm.toLinearMap :=
  rfl

@[simp]
theorem linearization_ε_hom : (ε (linearization k G)).hom =
    ModuleCat.ofHom (Finsupp.lsingle PUnit.unit) :=
  rfl

theorem linearization_η_hom_apply (r : k) :
    (η (linearization k G)).hom (Finsupp.single PUnit.unit r) = r :=
  (εIso (linearization k G)).hom_inv_id_apply r

variable (k G)

/-- The linearization of a type `X` on which `G` acts trivially is the trivial `G`-representation
on `k[X]`. -/
@[simps! hom_hom inv_hom]
def linearizationTrivialIso (X : Type u) :
    (linearization k G).obj (Action.mk X 1) ≅ trivial k G (X →₀ k) :=
  Action.mkIso (Iso.refl _) fun _ => ModuleCat.hom_ext <| Finsupp.lhom_ext' fun _ => LinearMap.ext
    fun _ => linearization_single ..

/-- Given a `G`-action on `H`, this is `k[H]` bundled with the natural representation
`G →* End(k[H])` as a term of type `Rep k G`. -/
abbrev ofMulAction (H : Type u) [MulAction G H] : Rep k G :=
  of <| Representation.ofMulAction k G H

/-- The `k`-linear `G`-representation on `k[G]`, induced by left multiplication. -/
abbrev leftRegular : Rep k G :=
  ofMulAction k G G

/-- The `k`-linear `G`-representation on `k[Gⁿ]`, induced by left multiplication. -/
abbrev diagonal (n : ℕ) : Rep k G :=
  ofMulAction k G (Fin n → G)

/-- The natural isomorphism between the representations on `k[G¹]` and `k[G]` induced by left
multiplication in `G`. -/
@[simps! hom_hom inv_hom]
def diagonalOneIsoLeftRegular :
    diagonal k G 1 ≅ leftRegular k G :=
  Action.mkIso (Finsupp.domLCongr <| Equiv.funUnique (Fin 1) G).toModuleIso fun _ =>
    ModuleCat.hom_ext <| Finsupp.lhom_ext fun _ _ => by simp [diagonal, ModuleCat.endRingEquiv]

/-- When `H = {1}`, the `G`-representation on `k[H]` induced by an action of `G` on `H` is
isomorphic to the trivial representation on `k`. -/
@[simps! hom_hom inv_hom]
def ofMulActionSubsingletonIsoTrivial
    (H : Type u) [Subsingleton H] [MulOneClass H] [MulAction G H] :
    ofMulAction k G H ≅ trivial k G k :=
  letI : Unique H := uniqueOfSubsingleton 1
  Action.mkIso (Finsupp.LinearEquiv.finsuppUnique _ _ _).toModuleIso fun _ =>
    ModuleCat.hom_ext <| Finsupp.lhom_ext fun _ _ => by
      simp [Subsingleton.elim _ (1 : H), ModuleCat.endRingEquiv]

/-- The linearization of a type `H` with a `G`-action is definitionally isomorphic to the
`k`-linear `G`-representation on `k[H]` induced by the `G`-action on `H`. -/
def linearizationOfMulActionIso (H : Type u) [MulAction G H] :
    (linearization k G).obj (Action.ofMulAction G H) ≅ ofMulAction k G H :=
  Iso.refl _

section

variable (k G A : Type u) [CommRing k] [Monoid G] [AddCommGroup A]
  [Module k A] [DistribMulAction G A] [SMulCommClass G k A]

/-- Turns a `k`-module `A` with a compatible `DistribMulAction` of a monoid `G` into a
`k`-linear `G`-representation on `A`. -/
def ofDistribMulAction : Rep k G := Rep.of (Representation.ofDistribMulAction k G A)

@[simp] theorem ofDistribMulAction_ρ_apply_apply (g : G) (a : A) :
    (ofDistribMulAction k G A).ρ g a = g • a := rfl

/-- Given an `R`-algebra `S`, the `ℤ`-linear representation associated to the natural action of
`S ≃ₐ[R] S` on `S`. -/
@[simp] def ofAlgebraAut (R S : Type) [CommRing R] [CommRing S] [Algebra R S] :
    Rep ℤ (S ≃ₐ[R] S) := ofDistribMulAction ℤ (S ≃ₐ[R] S) S

end
section
variable (M G : Type) [Monoid M] [CommGroup G] [MulDistribMulAction M G]

/-- Turns a `CommGroup` `G` with a `MulDistribMulAction` of a monoid `M` into a
`ℤ`-linear `M`-representation on `Additive G`. -/
def ofMulDistribMulAction : Rep ℤ M := Rep.of (Representation.ofMulDistribMulAction M G)

variable {G M}

/-- Unfolds `ofMulDistribMulAction`; useful to keep track of additivity. -/
@[simps!]
def toAdditive : ofMulDistribMulAction M G ≃+ Additive G := AddEquiv.refl _

@[simp] theorem ofMulDistribMulAction_ρ_apply_apply (g : M) (a : Additive G) :
    (ofMulDistribMulAction M G).ρ g a = Additive.ofMul (g • a.toMul) := rfl

/-- Given an `R`-algebra `S`, the `ℤ`-linear representation associated to the natural action of
`S ≃ₐ[R] S` on `Sˣ`. -/
@[simp] def ofAlgebraAutOnUnits (R S : Type) [CommRing R] [CommRing S] [Algebra R S] :
    Rep ℤ (S ≃ₐ[R] S) := Rep.ofMulDistribMulAction (S ≃ₐ[R] S) Sˣ

end

variable {k G}

/-- Given an element `x : A`, there is a natural morphism of representations `k[G] ⟶ A` sending
`g ↦ A.ρ(g)(x).` -/
@[simps]
def leftRegularHom (A : Rep k G) (x : A) : leftRegular k G ⟶ A where
  hom := ModuleCat.ofHom <| Finsupp.lift A k G fun g => A.ρ g x
  comm _ := by ext; simp [ModuleCat.endRingEquiv]

theorem leftRegularHom_hom_single {A : Rep k G} (g : G) (x : A) (r : k) :
    (leftRegularHom A x).hom (Finsupp.single g r) = r • A.ρ g x := by simp

/-- Given a `k`-linear `G`-representation `A`, there is a `k`-linear isomorphism between
representation morphisms `Hom(k[G], A)` and `A`. -/
@[simps]
def leftRegularHomEquiv (A : Rep k G) : (leftRegular k G ⟶ A) ≃ₗ[k] A where
  toFun f := f.hom (Finsupp.single 1 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := leftRegularHom A x
  left_inv f := by ext; simp [← hom_comm_apply f]
  right_inv x := by simp

theorem leftRegularHomEquiv_symm_single {A : Rep k G} (x : A) (g : G) :
    ((leftRegularHomEquiv A).symm x).hom (Finsupp.single g 1) = A.ρ g x := by
  simp

end Linearization
section Finsupp

open Finsupp

variable (α : Type u) (A : Rep k G)

/-- The representation on `α →₀ A` defined pointwise by a representation on `A`. -/
abbrev finsupp : Rep k G :=
  Rep.of (Representation.finsupp A.ρ α)

variable (k G) in
/-- The representation on `α →₀ k[G]` defined pointwise by the left regular representation on
`k[G]`. -/
abbrev free : Rep k G :=
  Rep.of (V := (α →₀ G →₀ k)) (Representation.free k G α)

variable {α}

/-- Given `f : α → A`, the natural representation morphism `(α →₀ k[G]) ⟶ A` sending
`single a (single g r) ↦ r • A.ρ g (f a)`. -/
@[simps]
def freeLift (f : α → A) :
    free k G α ⟶ A where
  hom := ModuleCat.ofHom <| linearCombination k (fun x => A.ρ x.2 (f x.1)) ∘ₗ
    (curryLinearEquiv k).symm.toLinearMap
  comm _ := by
    ext; simp [ModuleCat.endRingEquiv]

variable {A} in
lemma freeLift_hom_single_single (f : α → A) (i : α) (g : G) (r : k) :
    (freeLift A f).hom (single i (single g r)) = r • A.ρ g (f i) := by
  simp

variable (α) in
/-- The natural linear equivalence between functions `α → A` and representation morphisms
`(α →₀ k[G]) ⟶ A`. -/
@[simps]
def freeLiftLEquiv :
    (free k G α ⟶ A) ≃ₗ[k] (α → A) where
  toFun f i := f.hom (single i (single 1 1))
  invFun := freeLift A
  left_inv x := by
      ext i j
      simpa [← map_smul] using (hom_comm_apply x j (single i (single 1 1))).symm
  right_inv _ := by ext; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {A}

@[ext]
lemma free_ext (f g : free k G α ⟶ A)
    (h : ∀ i : α, f.hom (single i (single 1 1)) = g.hom (single i (single 1 1))) : f = g := by
  classical exact (freeLiftLEquiv α A).injective (funext_iff.2 h)

section

open MonoidalCategory

variable (A B : Rep k G) (α : Type u) [DecidableEq α]

open ModuleCat.MonoidalCategory

-- the proof below can be simplified after https://github.com/leanprover-community/mathlib4/issues/24823 is merged
/-- Given representations `A, B` and a type `α`, this is the natural representation isomorphism
`(α →₀ A) ⊗ B ≅ (A ⊗ B) →₀ α` sending `single x a ⊗ₜ b ↦ single x (a ⊗ₜ b)`. -/
@[simps! hom_hom inv_hom]
def finsuppTensorLeft :
    A.finsupp α ⊗ B ≅ (A ⊗ B).finsupp α :=
  Action.mkIso (TensorProduct.finsuppLeft k _ A B α).toModuleIso
    fun _ => ModuleCat.hom_ext <| TensorProduct.ext <| lhom_ext fun _ _ => by
      ext
      simp [Action_ρ_eq_ρ, TensorProduct.finsuppLeft_apply_tmul,
        tensorObj_carrier, ModuleCat.endRingEquiv]

/-- Given representations `A, B` and a type `α`, this is the natural representation isomorphism
`A ⊗ (α →₀ B) ≅ (A ⊗ B) →₀ α` sending `a ⊗ₜ single x b ↦ single x (a ⊗ₜ b)`. -/
@[simps! hom_hom inv_hom]
def finsuppTensorRight :
    A ⊗ B.finsupp α ≅ (A ⊗ B).finsupp α :=
  Action.mkIso (TensorProduct.finsuppRight k _ A B α).toModuleIso fun _ => ModuleCat.hom_ext <|
      TensorProduct.ext <| LinearMap.ext fun _ => lhom_ext fun _ _ => by
      ext
      simp [Action_ρ_eq_ρ, TensorProduct.finsuppRight_apply_tmul, ModuleCat.endRingEquiv,
        tensorObj_carrier]

variable (k G) in
/-- The natural isomorphism sending `single g r₁ ⊗ single a r₂ ↦ single a (single g r₁r₂)`. -/
@[simps! -isSimp hom_hom inv_hom]
def leftRegularTensorTrivialIsoFree :
    leftRegular k G ⊗ trivial k G (α →₀ k) ≅ free k G α :=
  Action.mkIso (finsuppTensorFinsupp' k G α ≪≫ₗ Finsupp.domLCongr (Equiv.prodComm G α) ≪≫ₗ
    curryLinearEquiv k).toModuleIso fun _ =>
      ModuleCat.hom_ext <| TensorProduct.ext <| lhom_ext fun _ _ => lhom_ext fun _ _ => by
        ext
        simp [Action_ρ_eq_ρ, tensorObj_carrier, ModuleCat.endRingEquiv]

variable {α}

omit [DecidableEq α]

@[simp]
lemma leftRegularTensorTrivialIsoFree_hom_hom_single_tmul_single (i : α) (g : G) (r s : k) :
    DFunLike.coe (F := ↑(ModuleCat.of k (G →₀ k) ⊗ ModuleCat.of k (α →₀ k)) →ₗ[k] α →₀ G →₀ k)
    (leftRegularTensorTrivialIsoFree k G α).hom.hom.hom (single g r ⊗ₜ[k] single i s) =
      single i (single g (r * s)) := by
  simp [leftRegularTensorTrivialIsoFree, tensorObj_carrier]

@[simp]
lemma leftRegularTensorTrivialIsoFree_inv_hom_single_single (i : α) (g : G) (r : k) :
    DFunLike.coe (F := (α →₀ G →₀ k) →ₗ[k] ↑(ModuleCat.of k (G →₀ k) ⊗ ModuleCat.of k (α →₀ k)))
    (leftRegularTensorTrivialIsoFree k G α).inv.hom.hom (single i (single g r)) =
      single g r ⊗ₜ[k] single i 1 := by
  simp [leftRegularTensorTrivialIsoFree, finsuppTensorFinsupp'_symm_single_eq_tmul_single_one,
    tensorObj_carrier]

end
end Finsupp

end
section Group

open Finsupp MonoidalCategory ModuleCat.MonoidalCategory
open Representation (IsTrivial)

variable [Group G] {n : ℕ}

variable (k G n) in
/-- An isomorphism of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` (on
which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. The inverse sends `g₀ ⊗ (g₁, ..., gₙ)` to
`(g₀, g₀g₁, ..., g₀g₁...gₙ)`. -/
def diagonalSuccIsoTensorTrivial :
    diagonal k G (n + 1) ≅ leftRegular k G ⊗ trivial k G ((Fin n → G) →₀ k) :=
  (linearization k G).mapIso (Action.diagonalSuccIsoTensorTrivial G n) ≪≫
    (Functor.Monoidal.μIso (linearization k G) _ _).symm ≪≫
      tensorIso (Iso.refl _) (linearizationTrivialIso k G (Fin n → G))

@[simp]
theorem diagonalSuccIsoTensorTrivial_hom_hom_single (f : Fin (n + 1) → G) (a : k) :
    DFunLike.coe (F := ((Fin (n + 1) → G) →₀ k) →ₗ[k]
      ↑(ModuleCat.of k (G →₀ k) ⊗ ModuleCat.of k ((Fin n → G) →₀ k)))
    (diagonalSuccIsoTensorTrivial k G n).hom.hom.hom (single f a) =
      single (f 0) 1 ⊗ₜ single (fun i => (f (Fin.castSucc i))⁻¹ * f i.succ) a := by
  simp [diagonalSuccIsoTensorTrivial, whiskerLeft_def, tensorObj_carrier,
    types_tensorObj_def, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul,
    ModuleCat.hom_id (M := .of _ _), Action.ofMulAction_V]

theorem diagonalSuccIsoTensorTrivial_inv_hom_single_single (g : G) (f : Fin n → G) (a b : k) :
    (diagonalSuccIsoTensorTrivial k G n).inv.hom (single g a ⊗ₜ single f b) =
      single (g • Fin.partialProd f) (a * b) := by
  have := Action.diagonalSuccIsoTensorTrivial_inv_hom_apply (G := G) (n := n)
  simp_all [diagonalSuccIsoTensorTrivial, ModuleCat.MonoidalCategory.tensorHom_def,
    tensorObj_carrier, types_tensorObj_def, ModuleCat.hom_id (M := .of _ _), Action.ofMulAction_V]

theorem diagonalSuccIsoTensorTrivial_inv_hom_single_left (g : G) (f : (Fin n → G) →₀ k) (r : k) :
    (diagonalSuccIsoTensorTrivial k G n).inv.hom (single g r ⊗ₜ f) =
      Finsupp.lift ((Fin (n + 1) → G) →₀ k) k (Fin n → G)
      (fun f => single (g • Fin.partialProd f) r) f := by
  refine f.induction ?_ ?_
  · simp only [TensorProduct.tmul_zero, map_zero]
  · intro a b x _ _ hx
    simpa [-Action.tensorObj_V, TensorProduct.tmul_add, map_add, mul_comm b, hx] using
      diagonalSuccIsoTensorTrivial_inv_hom_single_single ..

theorem diagonalSuccIsoTensorTrivial_inv_hom_single_right (g : G →₀ k) (f : Fin n → G) (r : k) :
    (diagonalSuccIsoTensorTrivial k G n).inv.hom (g ⊗ₜ single f r) =
      Finsupp.lift _ k G (fun a => single (a • Fin.partialProd f) r) g := by
  refine g.induction ?_ ?_
  · simp only [TensorProduct.zero_tmul, map_zero]
  · intro a b x _ _ hx
    simpa [-Action.tensorObj_V, map_add, hx, TensorProduct.add_tmul] using
      diagonalSuccIsoTensorTrivial_inv_hom_single_single ..

variable (k G n) in
/-- Representation isomorphism `k[Gⁿ⁺¹] ≅ (Gⁿ →₀ k[G])`, where the right-hand representation is
defined pointwise by the left regular representation on `k[G]`. The map sends
`single (g₀, ..., gₙ) a ↦ single (g₀⁻¹g₁, ..., gₙ₋₁⁻¹gₙ) (single g₀ a)`. -/
def diagonalSuccIsoFree : diagonal k G (n + 1) ≅ free k G (Fin n → G) :=
  diagonalSuccIsoTensorTrivial k G n ≪≫ leftRegularTensorTrivialIsoFree k G (Fin n → G)

@[simp]
theorem diagonalSuccIsoFree_hom_hom_single (f : Fin (n + 1) → G) (a : k) :
    (diagonalSuccIsoFree k G n).hom.hom (single f a) =
      single (fun i => (f i.castSucc)⁻¹ * f i.succ) (single (f 0) a) := by
  simp [diagonalSuccIsoFree, leftRegularTensorTrivialIsoFree_hom_hom_single_tmul_single
    (k := k)]

@[simp]
theorem diagonalSuccIsoFree_inv_hom_single_single (g : G) (f : Fin n → G) (a : k) :
    (diagonalSuccIsoFree k G n).inv.hom (single f (single g a)) =
      single (g • Fin.partialProd f) a := by
  have := diagonalSuccIsoTensorTrivial_inv_hom_single_single g f a 1
  simp_all [diagonalSuccIsoFree, leftRegularTensorTrivialIsoFree_inv_hom_single_single (k := k)]

theorem diagonalSuccIsoFree_inv_hom_single (g : G →₀ k) (f : Fin n → G) :
    (diagonalSuccIsoFree k G n).inv.hom (single f g) =
      lift _ k G (fun a => single (a • Fin.partialProd f) 1) g :=
  g.induction (by simp) fun _ _ _ _ _ _ => by
    rw [single_add, map_add, diagonalSuccIsoFree_inv_hom_single_single]
    simp_all [sum_add_index']

variable (n) (A : Rep k G)

/-- Given a `k`-linear `G`-representation `A`, the set of representation morphisms
`Hom(k[Gⁿ⁺¹], A)` is `k`-linearly isomorphic to the set of functions `Gⁿ → A`. -/
def diagonalHomEquiv :
    (Rep.diagonal k G (n + 1) ⟶ A) ≃ₗ[k] (Fin n → G) → A :=
  Linear.homCongr k (diagonalSuccIsoFree k G n) (Iso.refl _) ≪≫ₗ
    freeLiftLEquiv (Fin n → G) A

variable {n A}

/-- Given a `k`-linear `G`-representation `A`, `diagonalHomEquiv` is a `k`-linear isomorphism of
the set of representation morphisms `Hom(k[Gⁿ⁺¹], A)` with `Fun(Gⁿ, A)`. This lemma says that this
sends a morphism of representations `f : k[Gⁿ⁺¹] ⟶ A` to the function
`(g₁, ..., gₙ) ↦ f(1, g₁, g₁g₂, ..., g₁g₂...gₙ).` -/
theorem diagonalHomEquiv_apply (f : Rep.diagonal k G (n + 1) ⟶ A) (x : Fin n → G) :
    diagonalHomEquiv n A f x = f.hom (Finsupp.single (Fin.partialProd x) 1) := by
  simp [diagonalHomEquiv, Linear.homCongr_apply,
    diagonalSuccIsoFree_inv_hom_single_single (k := k)]

/-- Given a `k`-linear `G`-representation `A`, `diagonalHomEquiv` is a `k`-linear isomorphism of
the set of representation morphisms `Hom(k[Gⁿ⁺¹], A)` with `Fun(Gⁿ, A)`. This lemma says that the
inverse map sends a function `f : Gⁿ → A` to the representation morphism sending
`(g₀, ... gₙ) ↦ ρ(g₀)(f(g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ))`, where `ρ` is the representation attached
to `A`. -/
theorem diagonalHomEquiv_symm_apply (f : (Fin n → G) → A) (x : Fin (n + 1) → G) :
    ((diagonalHomEquiv n A).symm f).hom (Finsupp.single x 1) =
      A.ρ (x 0) (f fun i : Fin n => (x (Fin.castSucc i))⁻¹ * x i.succ) := by
  simp [diagonalHomEquiv, Linear.homCongr_symm_apply, diagonalSuccIsoFree_hom_hom_single (k := k)]

section

variable [Fintype G] (A : Rep k G)

/-- Given a representation `A` of a finite group `G`, `norm A` is the representation morphism
`A ⟶ A` defined by `x ↦ ∑ A.ρ g x` for `g` in `G`. -/
@[simps]
def norm : End A where
  hom := ModuleCat.ofHom <| Representation.norm A.ρ
  comm g := by ext; simp

@[reassoc, elementwise]
lemma norm_comm {A B : Rep k G} (f : A ⟶ B) : f ≫ norm B = norm A ≫ f := by
  ext
  simp [Representation.norm, hom_comm_apply]

/-- Given a representation `A` of a finite group `G`, the norm map `A ⟶ A` defined by
`x ↦ ∑ A.ρ g x` for `g` in `G` defines a natural endomorphism of the identity functor. -/
@[simps]
def normNatTrans : End (𝟭 (Rep k G)) where
  app := norm
  naturality _ _ := norm_comm

end

section MonoidalClosed
open MonoidalCategory Action

variable (A B C : Rep k G)

/-- Given a `k`-linear `G`-representation `(A, ρ₁)`, this is the 'internal Hom' functor sending
`(B, ρ₂)` to the representation `Homₖ(A, B)` that maps `g : G` and `f : A →ₗ[k] B` to
`(ρ₂ g) ∘ₗ f ∘ₗ (ρ₁ g⁻¹)`. -/
@[simps]
protected noncomputable def ihom (A : Rep k G) : Rep k G ⥤ Rep k G where
  obj B := Rep.of (Representation.linHom A.ρ B.ρ)
  map := fun {X} {Y} f =>
    { hom := ModuleCat.ofHom (LinearMap.llcomp k _ _ _ f.hom.hom)
      comm g := by ext; simp [ModuleCat.endRingEquiv, hom_comm_apply] }
  map_id := fun _ => by ext; rfl
  map_comp := fun _ _ => by ext; rfl

@[simp] theorem ihom_obj_ρ_apply {A B : Rep k G} (g : G) (x : A →ₗ[k] B) :
    -- Hint to put this lemma into `simp`-normal form.
    DFunLike.coe (F := (Representation k G (↑A.V →ₗ[k] ↑B.V)))
    ((Rep.ihom A).obj B).ρ g x = B.ρ g ∘ₗ x ∘ₗ A.ρ g⁻¹ :=
  rfl

/-- Given a `k`-linear `G`-representation `A`, this is the Hom-set bijection in the adjunction
`A ⊗ - ⊣ ihom(A, -)`. It sends `f : A ⊗ B ⟶ C` to a `Rep k G` morphism defined by currying the
`k`-linear map underlying `f`, giving a map `A →ₗ[k] B →ₗ[k] C`, then flipping the arguments. -/
@[simps]
def homEquiv (A B C : Rep k G) : (A ⊗ B ⟶ C) ≃ (B ⟶ (Rep.ihom A).obj C) where
  toFun f :=
    { hom := ModuleCat.ofHom <| (TensorProduct.curry f.hom.hom).flip
      comm g := ModuleCat.hom_ext <| LinearMap.ext fun x => LinearMap.ext fun y => by
        simpa [tensorObj_carrier, ModuleCat.endRingEquiv] using
          hom_comm_apply f g (A.ρ g⁻¹ y ⊗ₜ[k] x) }
  invFun f :=
    { hom := ModuleCat.ofHom <| TensorProduct.uncurry (.id k) _ _ _ f.hom.hom.flip
      comm g := ModuleCat.hom_ext <| TensorProduct.ext' fun x y => by
        simpa using LinearMap.ext_iff.1 (hom_comm_apply f g y) (A.ρ g x) }
  left_inv _ := Action.Hom.ext (ModuleCat.hom_ext <| TensorProduct.ext' fun _ _ => rfl)

variable {A B C}

instance : MonoidalClosed (Rep k G) where
  closed A :=
    { rightAdj := Rep.ihom A
      adj := Adjunction.mkOfHomEquiv ({
        homEquiv := Rep.homEquiv A
        homEquiv_naturality_left_symm := fun _ _ => Action.Hom.ext
          (ModuleCat.hom_ext (TensorProduct.ext' fun _ _ => rfl))
        homEquiv_naturality_right := fun _ _ => Action.Hom.ext (ModuleCat.hom_ext (LinearMap.ext
          fun _ => LinearMap.ext fun _ => rfl)) }) }

@[simp]
theorem ihom_obj_ρ_def (A B : Rep k G) : ((ihom A).obj B).ρ = ((Rep.ihom A).obj B).ρ :=
  rfl

@[simp]
theorem homEquiv_def (A B C : Rep k G) : (ihom.adjunction A).homEquiv B C = Rep.homEquiv A B C :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _

@[simp]
theorem ihom_ev_app_hom (A B : Rep k G) :
    Action.Hom.hom ((ihom.ev A).app B) = ModuleCat.ofHom
      (TensorProduct.uncurry (.id k) A (A →ₗ[k] B) B LinearMap.id.flip) := by
  ext; rfl

@[simp] theorem ihom_coev_app_hom (A B : Rep k G) :
    Action.Hom.hom ((ihom.coev A).app B) = ModuleCat.ofHom (TensorProduct.mk k _ _).flip :=
  ModuleCat.hom_ext <| LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

variable (A B C)

/-- There is a `k`-linear isomorphism between the sets of representation morphisms `Hom(A ⊗ B, C)`
and `Hom(B, Homₖ(A, C))`. -/
def MonoidalClosed.linearHomEquiv : (A ⊗ B ⟶ C) ≃ₗ[k] B ⟶ A ⟶[Rep k G] C :=
  { (ihom.adjunction A).homEquiv _ _ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- There is a `k`-linear isomorphism between the sets of representation morphisms `Hom(A ⊗ B, C)`
and `Hom(A, Homₖ(B, C))`. -/
def MonoidalClosed.linearHomEquivComm : (A ⊗ B ⟶ C) ≃ₗ[k] A ⟶ B ⟶[Rep k G] C :=
  Linear.homCongr k (β_ A B) (Iso.refl _) ≪≫ₗ MonoidalClosed.linearHomEquiv _ _ _

variable {A B C}

@[simp]
theorem MonoidalClosed.linearHomEquiv_hom (f : A ⊗ B ⟶ C) :
    (MonoidalClosed.linearHomEquiv A B C f).hom =
      ModuleCat.ofHom (TensorProduct.curry f.hom.hom).flip :=
  rfl

@[simp]
theorem MonoidalClosed.linearHomEquivComm_hom (f : A ⊗ B ⟶ C) :
    (MonoidalClosed.linearHomEquivComm A B C f).hom =
      ModuleCat.ofHom (TensorProduct.curry f.hom.hom) :=
  rfl

theorem MonoidalClosed.linearHomEquiv_symm_hom (f : B ⟶ A ⟶[Rep k G] C) :
    ((MonoidalClosed.linearHomEquiv A B C).symm f).hom =
      ModuleCat.ofHom (TensorProduct.uncurry (.id k) A B C f.hom.hom.flip) := by
  simp [linearHomEquiv]
  rfl

theorem MonoidalClosed.linearHomEquivComm_symm_hom (f : A ⟶ B ⟶[Rep k G] C) :
    ((MonoidalClosed.linearHomEquivComm A B C).symm f).hom =
      ModuleCat.ofHom (TensorProduct.uncurry (.id k) A B C f.hom.hom) :=
  ModuleCat.hom_ext <| TensorProduct.ext' fun _ _ => rfl

end MonoidalClosed
end Group

end Rep

namespace Representation
open MonoidalCategory
variable {k G : Type u} [CommRing k] [Monoid G] {V W : Type u} [AddCommGroup V] [AddCommGroup W]
  [Module k V] [Module k W] (ρ : Representation k G V) (τ : Representation k G W)

/-- Tautological isomorphism to help Lean in typechecking. -/
def repOfTprodIso : Rep.of (ρ.tprod τ) ≅ Rep.of ρ ⊗ Rep.of τ :=
  Iso.refl _

theorem repOfTprodIso_apply (x : TensorProduct k V W) : (repOfTprodIso ρ τ).hom.hom x = x :=
  rfl

theorem repOfTprodIso_inv_apply (x : TensorProduct k V W) : (repOfTprodIso ρ τ).inv.hom x = x :=
  rfl

end Representation

/-!
### The categorical equivalence `Rep k G ≌ Module.{u} k[G]`.
-/


namespace Rep

variable {k G : Type u} [CommRing k] [Monoid G]

-- Verify that the symmetric monoidal structure is available.
example : SymmetricCategory (Rep k G) := by infer_instance

example : MonoidalPreadditive (Rep k G) := by infer_instance

example : MonoidalLinear k (Rep k G) := by infer_instance

/-- Auxiliary lemma for `toModuleMonoidAlgebra`. -/
theorem to_Module_monoidAlgebra_map_aux {k G : Type*} [CommRing k] [Monoid G] (V W : Type*)
    [AddCommGroup V] [AddCommGroup W] [Module k V] [Module k W] (ρ : G →* V →ₗ[k] V)
    (σ : G →* W →ₗ[k] W) (f : V →ₗ[k] W) (w : ∀ g : G, f.comp (ρ g) = (σ g).comp f)
    (r : k[G]) (x : V) :
    f (MonoidAlgebra.lift k (V →ₗ[k] V) G ρ r x) =
      MonoidAlgebra.lift k (W →ₗ[k] W) G σ r (f x) := by
  apply MonoidAlgebra.induction_on r
  · intro g
    simp only [one_smul, MonoidAlgebra.lift_single, MonoidAlgebra.of_apply]
    exact LinearMap.congr_fun (w g) x
  · intro g h gw hw; simp only [map_add, LinearMap.add_apply, hw, gw]
  · intro r g w
    simp only [map_smul, w, LinearMap.smul_apply]

/-- Auxiliary definition for `toModuleMonoidAlgebra`. -/
def toModuleMonoidAlgebraMap {V W : Rep k G} (f : V ⟶ W) :
    ModuleCat.of k[G] V.ρ.asModule ⟶ ModuleCat.of k[G] W.ρ.asModule :=
  ModuleCat.ofHom
    { f.hom.hom with
      map_smul' := fun r x => to_Module_monoidAlgebra_map_aux V.V W.V V.ρ W.ρ f.hom.hom
        (fun g => ModuleCat.hom_ext_iff.mp (f.comm g)) r x }

/-- Functorially convert a representation of `G` into a module over `k[G]`. -/
def toModuleMonoidAlgebra : Rep k G ⥤ ModuleCat.{u} k[G] where
  obj V := ModuleCat.of _ V.ρ.asModule
  map f := toModuleMonoidAlgebraMap f

/-- Functorially convert a module over `k[G]` into a representation of `G`. -/
def ofModuleMonoidAlgebra : ModuleCat.{u} k[G] ⥤ Rep k G where
  obj M := Rep.of (Representation.ofModule M)
  map f :=
    { hom := ModuleCat.ofHom
        { f.hom with
          map_smul' := fun r x => f.hom.map_smul (algebraMap k _ r) x }
      comm := fun g => by ext; apply f.hom.map_smul }

theorem ofModuleMonoidAlgebra_obj_coe (M : ModuleCat.{u} k[G]) :
    (ofModuleMonoidAlgebra.obj M : Type u) = RestrictScalars k k[G] M :=
  rfl

theorem ofModuleMonoidAlgebra_obj_ρ (M : ModuleCat.{u} k[G]) :
    (ofModuleMonoidAlgebra.obj M).ρ = Representation.ofModule M :=
  rfl

/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
def counitIsoAddEquiv {M : ModuleCat.{u} k[G]} :
    (ofModuleMonoidAlgebra ⋙ toModuleMonoidAlgebra).obj M ≃+ M := by
  dsimp [ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
  exact (Representation.ofModule M).asModuleEquiv.toAddEquiv.trans
    (RestrictScalars.addEquiv k k[G] _)

/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
def unitIsoAddEquiv {V : Rep k G} : V ≃+ (toModuleMonoidAlgebra ⋙ ofModuleMonoidAlgebra).obj V := by
  dsimp [ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
  exact V.ρ.asModuleEquiv.symm.toAddEquiv.trans (RestrictScalars.addEquiv _ _ _).symm

/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
def counitIso (M : ModuleCat.{u} k[G]) :
    (ofModuleMonoidAlgebra ⋙ toModuleMonoidAlgebra).obj M ≅ M :=
  LinearEquiv.toModuleIso
    { counitIsoAddEquiv with
      map_smul' := fun r x => by
        dsimp [counitIsoAddEquiv]
        simp }

theorem unit_iso_comm (V : Rep k G) (g : G) (x : V) :
    unitIsoAddEquiv ((V.ρ g).toFun x) = ((ofModuleMonoidAlgebra.obj
      (toModuleMonoidAlgebra.obj V)).ρ g).toFun (unitIsoAddEquiv x) := by
  simp [unitIsoAddEquiv, ofModuleMonoidAlgebra, toModuleMonoidAlgebra]

/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
def unitIso (V : Rep k G) : V ≅ (toModuleMonoidAlgebra ⋙ ofModuleMonoidAlgebra).obj V :=
  Action.mkIso
    (LinearEquiv.toModuleIso
      { unitIsoAddEquiv with
        map_smul' := fun r x => by
          change (RestrictScalars.addEquiv _ _ _).symm (V.ρ.asModuleEquiv.symm (r • x)) = _
          simp only [Representation.asModuleEquiv_symm_map_smul]
          rfl })
    fun g => by ext; apply unit_iso_comm

/-- The categorical equivalence `Rep k G ≌ ModuleCat k[G]`. -/
def equivalenceModuleMonoidAlgebra : Rep k G ≌ ModuleCat.{u} k[G] where
  functor := toModuleMonoidAlgebra
  inverse := ofModuleMonoidAlgebra
  unitIso := NatIso.ofComponents (fun V => unitIso V) (by cat_disch)
  counitIso := NatIso.ofComponents (fun M => counitIso M) (by cat_disch)

-- TODO Verify that the equivalence with `ModuleCat k[G]` is a monoidal functor.

instance : EnoughProjectives (Rep k G) :=
  equivalenceModuleMonoidAlgebra.enoughProjectives_iff.2 ModuleCat.enoughProjectives.{u}

instance free_projective {G α : Type u} [Group G] :
    Projective (free k G α) :=
  equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective _ <|
    @ModuleCat.projective_of_free.{u} _ _
      (ModuleCat.of k[G] (Representation.free k G α).asModule)
      _ (Representation.freeAsModuleBasis k G α)

section

variable {G : Type u} [Group G] {n : ℕ}

instance diagonal_succ_projective :
    Projective (diagonal k G (n + 1)) := by
  classical
  exact Projective.of_iso (diagonalSuccIsoFree k G n).symm inferInstance

instance leftRegular_projective :
    Projective (leftRegular k G) :=
  Projective.of_iso (diagonalOneIsoLeftRegular k G) inferInstance

instance trivial_projective_of_subsingleton [Subsingleton G] :
    Projective (trivial k G k) :=
  Projective.of_iso (ofMulActionSubsingletonIsoTrivial _ _ (Fin 1 → G)) diagonal_succ_projective

end
end Rep
