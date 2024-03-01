import Mathlib.Tactic
import Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.ProjectiveSpace.Independence



noncomputable section

variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V] (I : Type*) [Fintype I]
(r : ℕ) (hrI : Fintype.card I = r)

/- First definition of the Grassmannian, as the set of sub-vector spaces of V of
dimension r.-/

def Grassmannian :=
{W : Submodule K V | FiniteDimensional K W ∧ FiniteDimensional.finrank K W = r}


/- Second definition of the Grassmannian, as a quotient.-/

/-- The setoid whose quotient is the I-grassmannian of `V`. -/
def grassmannianSetoid : Setoid { v : I → V // LinearIndependent K v} :=
Setoid.comap (fun v => Submodule.span K (Set.range v.1))
⟨(· = ·), eq_equivalence⟩

/-- The I-grassmannian of the `K`-vector space `V`.-/
def QGrassmannian := Quotient (grassmannianSetoid K V I)

variable {V I}

/-- Construct an element of the grassmannian from a linearly independent family. -/
def QGrassmannian.mk (v : I → V) (hv : LinearIndependent K v) : QGrassmannian K V I :=
  Quotient.mk'' ⟨v, hv⟩


/-- A variant of `Grassmannian.mk` in terms of a subtype. `mk` is preferred. -/
def QGrassmannian.mk' (v : { v : I → V // LinearIndependent K v }) : QGrassmannian K V I :=
  Quotient.mk'' v

@[simp]
theorem QGrassmannian.mk'_eq_mk (v : { v : I → V // LinearIndependent K v}) :
QGrassmannian.mk' K v = QGrassmannian.mk K v.1 v.2 := rfl

variable {K}

/-- Choose a representative of `x : Grassmannian K V I` in `V`. -/
protected noncomputable def QGrassmannian.rep (x : QGrassmannian K V I) : I → V :=
  x.out'


theorem QGrassmannian.rep_linearIndependent (x : QGrassmannian K V I) :
LinearIndependent K x.rep  :=
  x.out'.2

@[simp]
theorem QGrassmannian.mk_rep (x : QGrassmannian K V I) :
QGrassmannian.mk K x.rep x.rep_linearIndependent = x := Quotient.out_eq' _

variable (K)

lemma QGrassmannian.mk_eq_mk_iff_span (v w : I → V) (hv : LinearIndependent K v)
(hw : LinearIndependent K w) :
QGrassmannian.mk K v hv = QGrassmannian.mk K w hw ↔
Submodule.span K (Set.range v) = Submodule.span K (Set.range w) := by
  unfold QGrassmannian.mk
  change (Setoid.ker (@Quotient.mk'' _ (grassmannianSetoid K V I))).r _ _  ↔ _
  rw [Setoid.ker_mk_eq]
  unfold grassmannianSetoid
  change Submodule.span K (Set.range v) = _ ↔ _
  simp only


def MatrixAction (f : (I → K) →ₗ[K] (I → K)) (v : I → V) : I -> V :=
  (Basis.constr (M' := V) (Pi.basisFun K I) ℤ).invFun
    ((Basis.constr (Pi.basisFun K I) ℤ  v).comp f)

lemma MatrixAction_vs_comp (f : (I → K) →ₗ[K] (I → K)) (v w : I → V) :
v = MatrixAction K f w ↔ Basis.constr (Pi.basisFun K I) ℤ v =
  (Basis.constr (Pi.basisFun K I) ℤ w).comp f := by
  unfold MatrixAction
  constructor
  . intro h
    rw [h]
    simp only [LinearEquiv.invFun_eq_symm, LinearEquiv.apply_symm_apply]
  . intro h
    apply_fun (Basis.constr (M' := V) (Pi.basisFun K I) ℤ).invFun at h
    simp only [LinearEquiv.invFun_eq_symm, LinearEquiv.symm_apply_apply] at h
    exact h


lemma MatrixAction_id (v : I → V) : MatrixAction K LinearMap.id v = v := by
  unfold MatrixAction
  simp only [LinearMap.comp_id, LinearEquiv.invFun_eq_symm, LinearEquiv.symm_apply_apply]

lemma MatrixAction_mul (f g : (I → K) →ₗ[K] (I → K)) (v : I → V) :
MatrixAction K (f.comp g) v = MatrixAction K g (MatrixAction K f v) := by
  unfold MatrixAction
  simp only [LinearEquiv.invFun_eq_symm, LinearEquiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq]
  apply LinearMap.comp_assoc

def MatrixAction_inv (f : (I → K) ≃ₗ[K] (I → K)) (v w : I → V) :
w = MatrixAction K f v ↔ v = MatrixAction K f.symm w := by
  constructor
  . intro h
    rw [h, ←MatrixAction_mul]
    simp only [LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap]
    rw [MatrixAction_id]
  . intro h
    rw [h, ←MatrixAction_mul]
    simp only [LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap]
    rw [MatrixAction_id]


lemma MatrixAction_apply (f : (I → K) →ₗ[K] (I → K)) (v : I → V) (i : I) :
MatrixAction K f v i = Finset.sum ⊤ (fun j => (f (Pi.basisFun K I i) j) • v j) := by
  unfold MatrixAction
  conv => lhs
          rw [←(Basis.constr_basis (Pi.basisFun K I) ℤ
            ((Basis.constr (M' := V) (Pi.basisFun K I) ℤ).invFun
            ((Basis.constr (Pi.basisFun K I) ℤ  v).comp f)) i)]
  simp only [LinearEquiv.invFun_eq_symm, LinearEquiv.apply_symm_apply, Pi.basisFun_apply, LinearMap.coe_comp,
    Function.comp_apply, Basis.constr_apply_fintype, Pi.basisFun_equivFun, LinearEquiv.refl_apply, Finset.top_eq_univ]


lemma MatrixAction_span (f : (I → K) →ₗ[K] (I → K)) (v : I → V) :
Submodule.span K (Set.range (MatrixAction K f v)) ≤ Submodule.span K (Set.range v) := by
  rw [Submodule.span_le]
  intro u
  simp only [Set.mem_range, SetLike.mem_coe, forall_exists_index]
  intro i heq
  rw [←heq, MatrixAction_apply]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  apply Submodule.subset_span
  simp only [Set.mem_range, exists_apply_eq_apply]


lemma MatrixAction_vs_SubmoduleSpan (v w : I → V) :
Submodule.span K (Set.range v) ≤ Submodule.span K (Set.range w) ↔
∃ (f : (I → K) →ₗ[K] (I → K)), v = MatrixAction K f w := by
  constructor
  . intro h
    set f := Basis.constr (Pi.basisFun K I) ℤ v with hfdef
    set g := Basis.constr (Pi.basisFun K I) ℤ w with hgdef
    have hsub : LinearMap.range f ≤ LinearMap.range g := by
      rw [Basis.constr_range, Basis.constr_range]
      exact h
    set f' := f.codRestrict (LinearMap.range g)
      (by intro u; apply hsub; simp only [Basis.constr_apply_fintype, Pi.basisFun_equivFun, LinearEquiv.refl_apply,
        LinearMap.mem_range, exists_apply_eq_apply])
    set g' := g.rangeRestrict
    have hsur : Function.Surjective g' := by rw [←LinearMap.range_eq_top]; apply LinearMap.range_rangeRestrict
    obtain ⟨h, prop⟩ := Module.projective_lifting_property g' f' hsur
    existsi h
    simp_rw [MatrixAction_vs_comp]
    rw [←hfdef, ←hgdef]
    have heq : g = (Submodule.subtype (LinearMap.range g)).comp g' := by
      simp only [LinearMap.subtype_comp_codRestrict]
    rw [heq, LinearMap.comp_assoc, prop]
    simp only [LinearMap.subtype_comp_codRestrict]
  . intro h
    obtain ⟨f, hf⟩ := h
    rw [hf]
    apply MatrixAction_span


lemma MatrixAction_uniqueness {v : I → V} (hv : LinearIndependent K v)
(f g : (I → K) →ₗ[K] (I → K)) (heq : MatrixAction K f v = MatrixAction K g v) :
f = g := by
  unfold MatrixAction at heq
  apply_fun (fun h => (Basis.constr (Pi.basisFun K I) ℤ) h) at heq
  simp only [LinearEquiv.invFun_eq_symm, LinearEquiv.apply_symm_apply] at heq
  have hinj : Function.Injective (Basis.constr (Pi.basisFun K I) ℤ v) := by
    rw [←LinearMap.ker_eq_bot]
    apply Basis.constr_ker
    exact hv
  apply LinearMap.ext
  intro u
  apply_fun (fun h => h u) at heq
  simp only [LinearMap.coe_comp, Function.comp_apply] at heq
  exact hinj heq




lemma QGrassmannian.mk_eq_mk_iff_matrixAction (v w : I → V) (hv : LinearIndependent K v)
(hw : LinearIndependent K w) :
QGrassmannian.mk K v hv = QGrassmannian.mk K w hw ↔ ∃ (f : (I → K) ≃ₗ[K] (I → K)),
w = MatrixAction K f v := by
  rw [QGrassmannian.mk_eq_mk_iff_span]
  constructor
  . intro heq
    obtain ⟨f, hf⟩ := (MatrixAction_vs_SubmoduleSpan K v w).mp (le_of_eq heq)
    obtain ⟨g, hg⟩ := (MatrixAction_vs_SubmoduleSpan K w v).mp (le_of_eq (Eq.symm heq))
    have hgf : LinearMap.comp g f = LinearMap.id := by
      rw [hg, ←MatrixAction_mul] at hf
      conv at hf => lhs
                    rw [←(MatrixAction_id K v)]
      apply Eq.symm
      exact MatrixAction_uniqueness K hv _ _ hf
    have hfg : LinearMap.comp f g = LinearMap.id := by
      rw [hf, ←MatrixAction_mul] at hg
      conv at hg => lhs
                    rw [←(MatrixAction_id K w)]
      apply Eq.symm
      exact MatrixAction_uniqueness K hw _ _ hg
    existsi LinearEquiv.ofLinear g f hgf hfg
    exact hg
  . intro h
    obtain ⟨f, hf⟩ := h
    apply le_antisymm
    . have heq : v = MatrixAction K f.symm.toLinearMap w := by
        rw [MatrixAction_inv] at hf
        exact hf
      rw [heq]
      apply MatrixAction_span
    . rw [hf]
      apply MatrixAction_span

lemma QGrassmannian.mk_eq_mk_iff_matrixAction' (v w : I → V) (hv : LinearIndependent K v)
(hw : LinearIndependent K w) :
QGrassmannian.mk K v hv = QGrassmannian.mk K w hw ↔ ∃ (f : (I → K) →ₗ[K] (I → K)),
w = MatrixAction K f v := by
  rw [QGrassmannian.mk_eq_mk_iff_matrixAction]
  constructor
  . exact fun h => by obtain ⟨f, hf⟩ := h; existsi f.toLinearMap; exact hf
  . intro h
    obtain ⟨f, hf⟩ := h
    have hf' := hf
    rw [MatrixAction_vs_comp] at hf
    apply_fun (fun f => f.toFun) at hf
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp] at hf
    have hinj : Function.Injective f := by
      apply Function.Injective.of_comp (f := (Basis.constr (Pi.basisFun K I) ℤ) v)
      rw [←hf, ←LinearMap.ker_eq_bot]
      apply Basis.constr_ker
      exact hw
    existsi LinearEquiv.ofInjectiveEndo f hinj
    exact hf'

lemma QGrassmannian.exists_matrixAction_eq_mk_rep (v : I → V) (hv : LinearIndependent K v) :
∃ (f : (I → K) ≃ₗ[K] (I → K)), MatrixAction K f v = QGrassmannian.rep (QGrassmannian.mk K v hv) := by
  have heq := Eq.symm (QGrassmannian.mk_rep (QGrassmannian.mk K v hv))
  rw [QGrassmannian.mk_eq_mk_iff_matrixAction] at heq
  obtain ⟨f, hf⟩ := heq
  existsi f
  exact Eq.symm hf

variable {K}

/-- An induction principle for `QGrassmannian`.
Use as `induction v using QGrassmannian.ind`. -/
@[elab_as_elim]
lemma QGrassmannian.ind {P : QGrassmannian K V I → Prop} (h : ∀ (v : I → V) (h : LinearIndependent K v),
P (QGrassmannian.mk K v h)) : ∀ p, P p :=
  Quotient.ind' <| Subtype.rec <| h


/-- Consider an element of the QGrassmannian as a submodule of `V`. -/
protected def QGrassmannian.submodule (x : QGrassmannian K V I) : Submodule K V :=
  (Quotient.liftOn' x fun v => Submodule.span K (Set.range v.1)) <| by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
    exact hvw

@[simp]
lemma QGrassmannian.submodule_mk (v : I → V) (hv : LinearIndependent K v) :
(QGrassmannian.mk K v hv).submodule = Submodule.span K (Set.range v) := rfl

lemma QGrassmannian.submodule_eq (x : QGrassmannian K V I) : x.submodule = Submodule.span K (Set.range x.rep) := by
  conv_lhs => rw [← x.mk_rep]

instance QGrassmannian.finiteDimensional_submodule (x : QGrassmannian K V I) : FiniteDimensional K x.submodule := by
  rw [QGrassmannian.submodule_eq]
  apply FiniteDimensional.span_of_finite
  apply Set.finite_range

lemma QGrassmannian.finrank_submodule (x : QGrassmannian K V I) : FiniteDimensional.finrank K x.submodule = Fintype.card I := by
  rw [QGrassmannian.submodule_eq]
  rw [finrank_span_eq_card (QGrassmannian.rep_linearIndependent x)]

variable {r}

lemma QGrassmannian.finrank_submodule' (x : QGrassmannian K V I) : FiniteDimensional.finrank K x.submodule = r := by
  rw [QGrassmannian.submodule_eq]
  rw [finrank_span_eq_card (QGrassmannian.rep_linearIndependent x)]
  exact hrI



/- Comparison of the two definitions.-/

variable (V K)

def QGrassmannianToGrassmannian : QGrassmannian K V I → Grassmannian K V r :=
fun x => ⟨QGrassmannian.submodule x, ⟨QGrassmannian.finiteDimensional_submodule x, QGrassmannian.finrank_submodule' hrI x⟩⟩

lemma QGrassmannianToGrassmannian_apply' {v : I → V} (hv : LinearIndependent K v) :
(QGrassmannianToGrassmannian K V hrI (QGrassmannian.mk K v hv)).1 = Submodule.span K (Set.range v) := by
  unfold QGrassmannianToGrassmannian QGrassmannian.mk
  simp only
  apply QGrassmannian.submodule_mk


lemma QGrassmannianToGrassmannian_apply (x : QGrassmannian K V I) :
QGrassmannianToGrassmannian K V hrI x = ⟨Submodule.span K (Set.range x.rep),
⟨FiniteDimensional.span_of_finite K (Set.finite_range x.rep),
by rw [finrank_span_eq_card (QGrassmannian.rep_linearIndependent x)]; exact hrI⟩⟩ := by
  conv => lhs
          rw [←(QGrassmannian.mk_rep x)]


def GrassmannianToQGrassmannian : Grassmannian K V r → QGrassmannian K V I := by
  intro W
  haveI := W.2.1
  have heq : Fintype.card (Fin r) = Fintype.card I := by
    rw [hrI]; simp only [Fintype.card_fin]
  set B :=  (Basis.reindex (FiniteDimensional.finBasisOfFinrankEq K W W.2.2)
    (Fintype.equivOfCardEq heq))
  refine QGrassmannian.mk K ((Submodule.subtype W.1) ∘ (fun i => B i)) ?_
  apply LinearIndependent.map' (Basis.linearIndependent B) _ (Submodule.ker_subtype W.1)


lemma QGrassmannianToGrassmannianToQGrassmannian (x : QGrassmannian K V I) :
GrassmannianToQGrassmannian K V hrI (QGrassmannianToGrassmannian K V hrI x) = x := by
  rw [QGrassmannianToGrassmannian_apply]
  unfold GrassmannianToQGrassmannian
  simp only [Submodule.coeSubtype]
  conv => rhs
          rw [←(QGrassmannian.mk_rep x)]
  rw [QGrassmannian.mk_eq_mk_iff_span]
  rw [Set.range_comp]
  conv => lhs
          erw [←(LinearMap.map_span (Submodule.subtype _))]
  simp only [Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

lemma GrassmannianToQGrassmannianToGrassmannian (W : Grassmannian K V r) :
QGrassmannianToGrassmannian K V hrI (GrassmannianToQGrassmannian K V hrI W) = W := by
  unfold GrassmannianToQGrassmannian
  simp only [Submodule.coeSubtype]
  rw [←SetCoe.ext_iff, QGrassmannianToGrassmannian_apply', Set.range_comp]
  erw [←(LinearMap.map_span (Submodule.subtype _))]
  simp only [Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

noncomputable def QGrassmannianEquivGrassmannian : QGrassmannian K V I ≃ Grassmannian K V r :=
{
  toFun := QGrassmannianToGrassmannian K V hrI
  invFun := GrassmannianToQGrassmannian K V hrI
  left_inv := QGrassmannianToGrassmannianToQGrassmannian K V hrI
  right_inv := GrassmannianToQGrassmannianToGrassmannian K V hrI
}

/- Since we have equivalence, we can define Grassmannian.mk and Grassmannian.rep by composing the QGrassmannian
versions with the equivalence.-/

variable {V}

def Grassmannian.mkI (v : I → V) (hv : LinearIndependent K v) : Grassmannian K V r :=
QGrassmannianEquivGrassmannian K V hrI (QGrassmannian.mk K v hv)

def Grassmannian.mkI' (v : { v : I → V // LinearIndependent K v }) : Grassmannian K V r :=
QGrassmannianEquivGrassmannian K V hrI (QGrassmannian.mk' K v)


abbrev Grassmannian.mk (v : Fin r → V) (hv : LinearIndependent K v) : Grassmannian K V r :=
Grassmannian.mkI K (Fintype.card_fin r) v hv

abbrev Grassmannian.mk' (v : { v : Fin r → V // LinearIndependent K v }) : Grassmannian K V r :=
Grassmannian.mkI' K (Fintype.card_fin r) v


@[simp]
theorem Grassmannian.mkI'_eq_mkI (v : { v : I → V // LinearIndependent K v}) :
Grassmannian.mkI' K hrI v = Grassmannian.mkI K hrI v.1 v.2 := rfl

@[simp]
theorem Grassmannian.mk'_eq_mk (v : { v : Fin r → V // LinearIndependent K v}) :
Grassmannian.mk' K v = Grassmannian.mk K v.1 v.2 := rfl

lemma Grassmannian.mkI_apply (v : I → V) (hv : LinearIndependent K v) :
(Grassmannian.mkI K hrI v hv).1 = Submodule.span K (Set.range v) := by
  unfold Grassmannian.mkI
  erw [QGrassmannianToGrassmannian_apply' K V hrI]

lemma Grassmannian.mk_apply (v : Fin r → V) (hv : LinearIndependent K v) :
(Grassmannian.mk K v hv).1 = Submodule.span K (Set.range v) :=
Grassmannian.mkI_apply K (Fintype.card_fin r) v hv

variable {K}

def Grassmannian.repI (x : Grassmannian K V r) : I → V :=
QGrassmannian.rep ((QGrassmannianEquivGrassmannian K V hrI).symm x)

def Grassmannian.rep (x : Grassmannian K V r) : Fin r → V :=
Grassmannian.repI (Fintype.card_fin r) x

lemma Grassmannian.repI_linearIndependent (x : Grassmannian K V r) :
LinearIndependent K (Grassmannian.repI hrI x) :=
QGrassmannian.rep_linearIndependent _

lemma Grassmannian.rep_linearIndependent (x : Grassmannian K V r) :
LinearIndependent K (Grassmannian.rep x) :=
QGrassmannian.rep_linearIndependent _

@[simp]
theorem Grassmannian.mkI_repI (x : Grassmannian K V r) :
Grassmannian.mkI K hrI (Grassmannian.repI hrI x) (Grassmannian.repI_linearIndependent hrI x) = x := by
  unfold Grassmannian.mkI Grassmannian.repI
  rw [QGrassmannian.mk_rep]
  simp only [Equiv.apply_symm_apply]


@[simp]
theorem Grassmannian.mk_rep (x : Grassmannian K V r) :
Grassmannian.mk K (Grassmannian.rep x) (Grassmannian.rep_linearIndependent x) = x :=
Grassmannian.mkI_repI (Fintype.card_fin r) x


variable (K)

lemma Grassmannian.mkI_eq_mkI_iff_span (v w : I → V) (hv : LinearIndependent K v)
(hw : LinearIndependent K w) :
Grassmannian.mkI K hrI v hv = Grassmannian.mkI K hrI w hw ↔
Submodule.span K (Set.range v) = Submodule.span K (Set.range w) := by
  unfold Grassmannian.mkI
  simp only [EmbeddingLike.apply_eq_iff_eq]
  rw [QGrassmannian.mk_eq_mk_iff_span]

lemma Grassmannian.mk_eq_mk_iff_span (v w : Fin r → V) (hv : LinearIndependent K v)
(hw : LinearIndependent K w) :
Grassmannian.mk K v hv = Grassmannian.mk K w hw ↔
Submodule.span K (Set.range v) = Submodule.span K (Set.range w) :=
Grassmannian.mkI_eq_mkI_iff_span K (Fintype.card_fin r) v w hv hw

lemma Grassmannian.mkI_eq_mkI_iff_matrixAction (v w : I → V) (hv : LinearIndependent K v)
(hw : LinearIndependent K w) :
Grassmannian.mkI K hrI v hv = Grassmannian.mkI K hrI w hw ↔ ∃ (f : (I → K) ≃ₗ[K] (I → K)),
w = MatrixAction K f v := by
  unfold Grassmannian.mkI
  simp only [EmbeddingLike.apply_eq_iff_eq]
  rw [QGrassmannian.mk_eq_mk_iff_matrixAction]

lemma Grassmannian.mk_eq_mk_iff_matrixAction (v w : Fin r → V) (hv : LinearIndependent K v)
(hw : LinearIndependent K w) :
Grassmannian.mk K v hv = Grassmannian.mk K w hw ↔ ∃ (f : (Fin r → K) ≃ₗ[K] (Fin r → K)),
w = MatrixAction K f v :=
Grassmannian.mkI_eq_mkI_iff_matrixAction K (Fintype.card_fin r) v w hv hw

lemma Grassmannian.mkI_eq_mkI_iff_matrixAction' (v w : I → V) (hv : LinearIndependent K v)
(hw : LinearIndependent K w) :
Grassmannian.mkI K hrI v hv = Grassmannian.mkI K hrI w hw ↔ ∃ (f : (I → K) →ₗ[K] (I → K)),
w = MatrixAction K f v := by
  unfold Grassmannian.mkI
  simp only [EmbeddingLike.apply_eq_iff_eq]
  rw [QGrassmannian.mk_eq_mk_iff_matrixAction']

lemma Grassmannian.mk_eq_mk_iff_matrixAction' (v w : Fin r → V) (hv : LinearIndependent K v)
(hw : LinearIndependent K w) :
Grassmannian.mk K v hv = Grassmannian.mk K w hw ↔ ∃ (f : (Fin r → K) →ₗ[K] (Fin r → K)),
w = MatrixAction K f v :=
Grassmannian.mkI_eq_mkI_iff_matrixAction' K (Fintype.card_fin r) v w hv hw

lemma Grassmannian.exists_matrixAction_eq_mkI_repI (v : I → V) (hv : LinearIndependent K v) :
∃ (f : (I → K) ≃ₗ[K] (I → K)), MatrixAction K f v = Grassmannian.repI hrI (Grassmannian.mkI K hrI v hv) := by
  unfold Grassmannian.repI Grassmannian.mkI
  simp only [Equiv.symm_apply_apply]
  exact QGrassmannian.exists_matrixAction_eq_mk_rep K v hv

lemma Grassmannian.exists_matrixAction_eq_mk_rep (v : Fin r → V) (hv : LinearIndependent K v) :
∃ (f : (Fin r → K) ≃ₗ[K] (Fin r → K)), MatrixAction K f v = Grassmannian.rep (Grassmannian.mk K v hv) :=
Grassmannian.exists_matrixAction_eq_mkI_repI K (Fintype.card_fin r) v hv

/- The case r = 1.-/
variable (V)

def Grassmannian.equivSubmodule (hr : r > 0) : Grassmannian K V r ≃
{W : Submodule K V // FiniteDimensional.finrank K W = r} :=
Equiv.ofBijective (fun W => ⟨W.1, W.2.2⟩)
(by constructor
    . intro W W'
      rw [←SetCoe.ext_iff, ←SetCoe.ext_iff]
      simp only [imp_self]
    . intro ⟨W, hW2⟩
      have hW1 : FiniteDimensional K W := by
        apply FiniteDimensional.finiteDimensional_of_finrank
        rw [hW2]; exact hr
      existsi ⟨W, hW1, hW2⟩
      simp only
)

noncomputable def Projectivization.equivGrassmannian : ℙ K V ≃ Grassmannian K V 1 :=
Equiv.trans (Projectivization.equivSubmodule K V) (Grassmannian.equivSubmodule K V Nat.zero_lt_one).symm


variable {K V}
variable (r I) {V' : Type*} [AddCommGroup V'] [Module K V']

/-- An injective linear map of vector spaces induces a map on QGrassmannians. -/
-- Less general than the version for projective spaces because LinearIndependent.map' requires the two rings to be equal.
def QGrassmannian.map (f : V →ₗ[K] V') (hf : Function.Injective f) : QGrassmannian K V I → QGrassmannian K V' I :=
  Quotient.map' (fun v => ⟨f ∘ v.1, by simp only; rw [←LinearMap.ker_eq_bot] at hf; exact LinearIndependent.map' v.2 f hf⟩)
    (by rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
        change Submodule.span K _ = _ at hvw
        change Submodule.span K _ = _
        simp only at hvw ⊢
        rw [Set.range_comp, Set.range_comp]
        rw [←LinearMap.map_span, ←LinearMap.map_span]
        rw [hvw])

lemma QGrassmannian.map_mk (f : V →ₗ[K] V') (hf : Function.Injective f) (v : I → V) (hv : LinearIndependent K v) :
    QGrassmannian.map I f hf (mk K v hv) = QGrassmannian.mk K (f ∘ v)
    (by rw [←LinearMap.ker_eq_bot] at hf; exact LinearIndependent.map' hv f hf) := rfl

/-- The map we have defined is injective. -/
theorem QGrassmannian.map_injective (f : V →ₗ[K] V') (hf : Function.Injective f) :
Function.Injective (QGrassmannian.map I f hf) := by
  intro x y hxy
  induction' x using QGrassmannian.ind with v hv
  induction' y using QGrassmannian.ind with w hw
  rw [QGrassmannian.mk_eq_mk_iff_span]
  rw [QGrassmannian.map_mk, QGrassmannian.map_mk, QGrassmannian.mk_eq_mk_iff_span, Set.range_comp, Set.range_comp,
    ←LinearMap.map_span, ←LinearMap.map_span] at hxy
  apply_fun (fun p => SetLike.coe p) at hxy
  rw [Submodule.map_coe, Submodule.map_coe] at hxy
  apply SetLike.coe_injective'
  exact Function.Injective.image_injective hf hxy


@[simp]
lemma QGrassmannian.map_id : QGrassmannian.map I (LinearMap.id : V →ₗ[K] V) (LinearEquiv.refl K V).injective = id := by
  ext ⟨v⟩
  rfl


lemma QGrassmannian.map_comp {U : Type*} [AddCommGroup U] [Module K U] (f : V →ₗ[K] V') (hf : Function.Injective f)
    (g : V' →ₗ[K] U) (hg : Function.Injective g) :
    QGrassmannian.map I (g.comp f) (hg.comp hf) = QGrassmannian.map I g hg ∘ QGrassmannian.map I f hf := by
  ext ⟨v⟩
  rfl


/- And the versions with Grassmannians.-/


def Grassmannian.map (f : V →ₗ[K] V') (hf : Function.Injective f) : Grassmannian K V r → Grassmannian K V' r := by
  intro W
  refine ⟨Submodule.map f W.1, ?_, ?_⟩
  . letI := W.2.1
    exact inferInstance
  . set f' := f.domRestrict W.1
    have heq : Submodule.map f W = LinearMap.range f' := by
      ext u
      simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.domRestrict_apply, Subtype.exists, exists_prop]
    have hinj : Function.Injective f' := by
      rw [←LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro u
      simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply]
      rw [←LinearMap.ker_eq_bot] at hf
      intro hu
      change u.1 ∈ LinearMap.ker f at hu
      rw [hf] at hu
      simp only [Submodule.mem_bot, ZeroMemClass.coe_eq_zero] at hu
      exact hu
    rw [heq, LinearMap.finrank_range_of_inj hinj, W.2.2]


lemma Grassmannian.map_apply (f : V →ₗ[K] V') (hf : Function.Injective f) (W : Grassmannian K V r) :
    (Grassmannian.map r f hf W).1 = Submodule.map f W := by
    unfold Grassmannian.map
    simp only


/-- The map we have defined is injective. -/
theorem Grassmannian.map_injective (f : V →ₗ[K] V') (hf : Function.Injective f) :
Function.Injective (Grassmannian.map r f hf) := by
  intro W W' hWW'
  rw [←SetCoe.ext_iff, Grassmannian.map_apply, Grassmannian.map_apply] at hWW'
  apply_fun (fun p => SetLike.coe p) at hWW'
  rw [Submodule.map_coe, Submodule.map_coe] at hWW'
  rw [←SetCoe.ext_iff, ←SetLike.coe_set_eq]
  exact Function.Injective.image_injective hf hWW'


@[simp]
lemma Grassmannian.map_id : Grassmannian.map r (LinearMap.id : V →ₗ[K] V) (LinearEquiv.refl K V).injective = id := by
  apply funext
  intro W
  rw [id_eq, ←SetCoe.ext_iff, Grassmannian.map_apply, Submodule.map_id]


lemma Grassmannian.map_comp {U : Type*} [AddCommGroup U] [Module K U] (f : V →ₗ[K] V') (hf : Function.Injective f)
    (g : V' →ₗ[K] U) (hg : Function.Injective g) :
    Grassmannian.map r (g.comp f) (hg.comp hf) = Grassmannian.map r g hg ∘ Grassmannian.map r f hf := by
  apply funext
  intro W
  rw [Function.comp_apply, ←SetCoe.ext_iff, Grassmannian.map_apply, Grassmannian.map_apply, Grassmannian.map_apply,
    Submodule.map_comp]



/- Nonemptiness of the Grassmannian.-/

variable (K V)
variable {r I}

lemma NonemptyGrassmannian_iff : Nonempty ({v : I → V // LinearIndependent K v}) ↔ Nonempty (Grassmannian K V r) := by
  rw [←(nonempty_quotient_iff (grassmannianSetoid K V I))]
  exact Equiv.nonempty_congr (QGrassmannianEquivGrassmannian K V hrI)

variable (r)

lemma NonemptyGrassmannian_iff' : Nonempty ({v : Fin r → V // LinearIndependent K v}) ↔ Nonempty (Grassmannian K V r) :=
NonemptyGrassmannian_iff K V (Fintype.card_fin r)

lemma NonemptyGrassmannian_of_finrank (hfinrank : r ≤ FiniteDimensional.finrank K V) : Nonempty (Grassmannian K V r) := by
  by_cases hr : r = 0
  . rw [hr]
    set W : Submodule K V := ⊥
    have hW1 : FiniteDimensional K W := inferInstance
    have hW2 : FiniteDimensional.finrank K W = 0 := finrank_bot K V
    exact Nonempty.intro ⟨W, hW1, hW2⟩
  . rw [←(Nat.succ_pred hr), Nat.succ_le_iff] at hfinrank
    have hrank := Order.succ_le_of_lt (FiniteDimensional.lt_rank_of_lt_finrank hfinrank)
    rw [←Cardinal.nat_succ, Nat.succ_pred hr, le_rank_iff_exists_linearIndependent_finset] at hrank
    obtain ⟨s, hsr, hslin⟩ := hrank
    set v : Fin r → V := fun i => (Finset.equivFinOfCardEq hsr).symm i
    have hv : LinearIndependent K v := by
      apply LinearIndependent.comp hslin
      apply Equiv.injective
    rw [←NonemptyGrassmannian_iff']
    exact Nonempty.intro ⟨v, hv⟩

variable {K V r}

/- Topologies. -/

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [BoundedSMul 𝕜 E]

/-- We equip the QGrassmannian with the "coinduced" topology from the natural map
`mk' : {v : Fin r → E // LinearIndependent 𝕜 v} → QGrassmannanian 𝕜 V r`. -/
instance : TopologicalSpace (QGrassmannian 𝕜 E I) :=
TopologicalSpace.coinduced (QGrassmannian.mk' 𝕜) instTopologicalSpaceSubtype

/- We equip the Grassmannian with the coinduced topology from the equivalence with the QGrassmannian. Note that this is also
an induced topology, see Equiv.induced_symm and Equiv.coinduced_symm.-/

instance : TopologicalSpace (Grassmannian 𝕜 E r) :=
TopologicalSpace.coinduced (Grassmannian.mk' 𝕜) instTopologicalSpaceSubtype

end
