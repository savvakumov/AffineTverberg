import AffineTverberg.PolytopalDeletedJoin
import AffineTverberg.Incidence

set_option linter.style.header false

/-!
# Part (I) of Lemma `Y` for the concrete polytopal model

This file proves the polytopal half of Lemma `Y`, for the concrete
coordinate model of the deleted join built in `PolytopalDeletedJoin.lean`
and a finite dimensional real target `V`.

The set under study is

`Y = {(z, y) ∈ D × S(V*) | z lies on the fiberwise upper envelope of λ_y}`,

where `D` is the concrete polytopal deleted join and `S(V*)` is the unit
sphere of the continuous dual.  The four assertions are:

* `(a)` every fiber `Y_y` is nonempty — this is
  `PolytopalJoinMap.deletedJoinTopLocus_nonempty`, already available;
* `(b)` `Y` is closed, hence compact.  The proof uses the finite face
  description of the join polytope: a top point always lies in the convex
  hull `F` of the vertices at which some affine upper support is tight, and
  that hull is contained in the top locus.  Consequently `Y` is the finite
  union of the products `(D ∩ F) × S_F`, where the parameter set
  `S_F = {y | F ⊆ topLocus λ_y}` is cut out by linear inequalities in `y`
  and therefore closed;
* `(c)` the projection `Y → S(V*)` is continuous and surjective;
* the geometric core of `(d)`: every point of `Y` lies on a genuine
  supporting face of the join on which the `y`-height is nonnegative.

The facewise incidence spaces at the end of this file are useful auxiliary
models.  The paper's actual deleted-cell incidence space `X`, and the
refinement of the supporting face inside a deleted cell, are formalized in
`PolytopalCellIncidence.lean`.
-/

noncomputable section

open Set

namespace AffineTverberg

namespace CompactConvexProjection

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (A : CompactConvexProjection E F)

/-- **Facewise description of the top locus of a polytope.**  Every top
point lies in the convex hull of the vertices at which one fixed affine
upper support is tight, and that hull is contained in the contact face of
that support. -/
theorem exists_tightVertexSubset_of_mem_topLocus
    (S : Finset E) (hS : A.carrier = convexHull ℝ (S : Set E))
    {w : E} (hw : w ∈ A.topLocus) :
    ∃ T : Finset E, T ⊆ S ∧ w ∈ convexHull ℝ (T : Set E) ∧
      ∃ c : UpperSupportCertificate A,
        convexHull ℝ (T : Set E) = c.contactSet := by
  classical
  obtain ⟨c, hc⟩ :=
    exists_upperSupportCertificate_mem_contactSet_of_convexHull A S hS hw
  let T := S.filter (fun v ↦ v ∈ c.contactSet)
  have hset : {v : E | v ∈ (S : Set E) ∧ v ∈ c.contactSet} = (T : Set E) := by
    ext v
    simp [T]
  refine ⟨T, Finset.filter_subset _ _, ?_, c, ?_⟩
  · have hmem := mem_convexHull_tight_vertices A S hS c hc
    rwa [hset] at hmem
  · apply Subset.antisymm
    · exact convexHull_min
        (fun v hv ↦ (Finset.mem_filter.1 (Finset.mem_coe.1 hv)).2)
        c.contactSet_convex
    · intro x hx
      have hmem := mem_convexHull_tight_vertices A S hS c hx
      rwa [hset] at hmem

/-- Every top point of a polytope lies in a face, spanned by vertices,
which is entirely contained in the top locus. -/
theorem exists_vertexSubset_face_of_mem_topLocus
    (S : Finset E) (hS : A.carrier = convexHull ℝ (S : Set E))
    {w : E} (hw : w ∈ A.topLocus) :
    ∃ T : Finset E, T ⊆ S ∧ w ∈ convexHull ℝ (T : Set E) ∧
      convexHull ℝ (T : Set E) ⊆ A.topLocus := by
  obtain ⟨T, hTS, hwT, c, hTc⟩ :=
    exists_tightVertexSubset_of_mem_topLocus A S hS hw
  exact ⟨T, hTS, hwT, hTc.le.trans c.contactSet_subset_topLocus⟩

/-- With the diagonal witness condition, the face through a top point is
moreover a face on which the height is everywhere nonnegative.  This is the
polytopal ingredient for the inclusion `Y ⊆ X`. -/
theorem exists_vertexSubset_nonnegative_face_of_mem_topLocus
    (S : Finset E) (hS : A.carrier = convexHull ℝ (S : Set E))
    (hfiber : A.HasNonnegativeFiberWitness)
    {w : E} (hw : w ∈ A.topLocus) :
    ∃ T : Finset E, T ⊆ S ∧ w ∈ convexHull ℝ (T : Set E) ∧
      convexHull ℝ (T : Set E) ⊆ A.topLocus ∧
      ∀ u ∈ convexHull ℝ (T : Set E), 0 ≤ A.height u := by
  obtain ⟨T, hTS, hwT, c, hTc⟩ :=
    exists_tightVertexSubset_of_mem_topLocus A S hS hw
  refine ⟨T, hTS, hwT, hTc.le.trans c.contactSet_subset_topLocus, fun u hu ↦ ?_⟩
  exact UpperSupportCertificate.height_nonnegative_on_contactSet A c hfiber u
    (hTc ▸ hu)

/-- The vertex-spanned face through a top point can be retained as an
actual exposed face of the polytope, rather than merely as a convex subset
of the top locus. -/
theorem exists_exposedVertexSubset_nonnegative_of_mem_topLocus
    (S : Finset E) (hS : A.carrier = convexHull ℝ (S : Set E))
    (hfiber : A.HasNonnegativeFiberWitness)
    {w : E} (hw : w ∈ A.topLocus) :
    ∃ T : Finset E, T ⊆ S ∧ w ∈ convexHull ℝ (T : Set E) ∧
      IsExposed ℝ A.carrier (convexHull ℝ (T : Set E)) ∧
      convexHull ℝ (T : Set E) ⊆ A.topLocus ∧
      (∀ u ∈ convexHull ℝ (T : Set E), 0 ≤ A.height u) := by
  obtain ⟨T, hTS, hwT, c, hTc⟩ :=
    exists_tightVertexSubset_of_mem_topLocus A S hS hw
  refine ⟨T, hTS, hwT, hTc ▸ c.contactSet_isExposed,
    hTc.le.trans c.contactSet_subset_topLocus, fun u hu ↦ ?_⟩
  exact UpperSupportCertificate.height_nonnegative_on_contactSet A c hfiber u
    (hTc ▸ hu)

end CompactConvexProjection

/-- The finite index set of candidate faces of the join polytope: subsets
of its Cayley vertex set. -/
abbrev PolytopalJoinFaceIndex {n : ℕ} (P : FullDimensionalPolytope n) (m : ℕ) :=
  {T : Finset (PolytopalJoinAmbient n m) // T ∈ (polytopalJoinVertices P m).powerset}

/-- The geometric carrier of a candidate face of the join polytope. -/
def polytopalJoinFaceCarrier {n m : ℕ} {P : FullDimensionalPolytope n}
    (T : PolytopalJoinFaceIndex P m) : Set (PolytopalJoinAmbient n m) :=
  convexHull ℝ (T.1 : Set (PolytopalJoinAmbient n m))

/-- The finite type of actual exposed faces of the join polytope, encoded by
the subset of Cayley vertices spanning them. -/
abbrev PolytopalJoinExposedFaceIndex {n : ℕ}
    (P : FullDimensionalPolytope n) (m : ℕ) :=
  {T : PolytopalJoinFaceIndex P m //
    IsExposed ℝ (polytopalJoinCarrier P m) (polytopalJoinFaceCarrier T)}

namespace PolytopalJoinFaceIndex

variable {n m : ℕ} {P : FullDimensionalPolytope n}

theorem compact (T : PolytopalJoinFaceIndex P m) :
    IsCompact (polytopalJoinFaceCarrier T) :=
  T.1.finite_toSet.isCompact_convexHull ℝ

theorem isClosed (T : PolytopalJoinFaceIndex P m) :
    IsClosed (polytopalJoinFaceCarrier T) :=
  (compact T).isClosed

theorem convex (T : PolytopalJoinFaceIndex P m) :
    Convex ℝ (polytopalJoinFaceCarrier T) :=
  convex_convexHull ℝ _

theorem subset_joinCarrier (T : PolytopalJoinFaceIndex P m) :
    polytopalJoinFaceCarrier T ⊆ polytopalJoinCarrier P m :=
  convexHull_mono (fun _v hv ↦ Finset.mem_coe.2
    (Finset.mem_powerset.1 T.2 (Finset.mem_coe.1 hv)))

end PolytopalJoinFaceIndex

namespace PolytopalJoinMap

variable {n m : ℕ} {P : FullDimensionalPolytope n}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (Φ : PolytopalJoinMap P m V)

/-!
### The facewise description of the fibers `Y_y`
-/

/-- Every point of the fiberwise upper envelope lies in a face of the join
polytope which is contained in the upper envelope and on which the
`y`-height is nonnegative. -/
theorem exists_joinFace_mem_of_mem_topLocus (y : StrongDual ℝ V)
    {z : PolytopalJoinAmbient n m}
    (hz : z ∈ (Φ.upperEnvelopeData y).topLocus) :
    ∃ T : PolytopalJoinFaceIndex P m,
      z ∈ polytopalJoinFaceCarrier T ∧
        polytopalJoinFaceCarrier T ⊆ (Φ.upperEnvelopeData y).topLocus ∧
        ∀ w ∈ polytopalJoinFaceCarrier T, 0 ≤ y (Φ.joinMap w) := by
  obtain ⟨T, hTS, hzT, htop, hnonneg⟩ :=
    CompactConvexProjection.exists_vertexSubset_nonnegative_face_of_mem_topLocus
      (Φ.upperEnvelopeData y) (polytopalJoinVertices P m) rfl
      (Φ.upperEnvelopeData_hasNonnegativeFiberWitness y) hz
  exact ⟨⟨T, Finset.mem_powerset.2 hTS⟩, hzT, htop, hnonneg⟩

/-- The supporting set in the preceding existence theorem may be chosen to
be an actual exposed face of the full join polytope. -/
theorem exists_exposedJoinFace_nonnegative_of_mem_topLocus
    (y : StrongDual ℝ V) {z : PolytopalJoinAmbient n m}
    (hz : z ∈ (Φ.upperEnvelopeData y).topLocus) :
    ∃ T : PolytopalJoinExposedFaceIndex P m,
      z ∈ polytopalJoinFaceCarrier T.val ∧
        polytopalJoinFaceCarrier T.val ⊆ (Φ.upperEnvelopeData y).topLocus ∧
        ∀ w ∈ polytopalJoinFaceCarrier T.val, 0 ≤ y (Φ.joinMap w) := by
  obtain ⟨T, hTS, hzT, hexposed, htop, hnonneg⟩ :=
    CompactConvexProjection.exists_exposedVertexSubset_nonnegative_of_mem_topLocus
      (Φ.upperEnvelopeData y) (polytopalJoinVertices P m) rfl
      (Φ.upperEnvelopeData_hasNonnegativeFiberWitness y) hz
  exact ⟨⟨⟨T, Finset.mem_powerset.2 hTS⟩, hexposed⟩, hzT, htop, hnonneg⟩

/-- The parameter set `S_F` of the paper: the dual functionals for which
the whole face `F` lies on the fiberwise upper envelope. -/
def faceParameterSet (T : PolytopalJoinFaceIndex P m) : Set (StrongDual ℝ V) :=
  {y | polytopalJoinFaceCarrier T ⊆ (Φ.upperEnvelopeData y).topLocus}

/-- `S_F` is cut out by the linear inequalities `y (Φ w) ≤ y (Φ u)`, one for
each pair of a point `u` of the face and a point `w` of the join polytope in
the same projection fiber. -/
theorem faceParameterSet_eq_iInter (T : PolytopalJoinFaceIndex P m) :
    Φ.faceParameterSet T =
      ⋂ u ∈ polytopalJoinFaceCarrier T, ⋂ w ∈ polytopalJoinCarrier P m,
        ⋂ _ : polytopalJoinProjection n m w = polytopalJoinProjection n m u,
          {y : StrongDual ℝ V | y (Φ.joinMap w) ≤ y (Φ.joinMap u)} := by
  ext y
  simp only [faceParameterSet, mem_ofPred_eq, mem_iInter]
  constructor
  · intro hy u hu w hw hproj
    have hutop := hy hu
    exact ((Φ.upperEnvelopeData y).mem_topLocus_iff.1 hutop).2 w hw hproj
  · intro hy u hu
    rw [CompactConvexProjection.mem_topLocus_iff]
    exact ⟨PolytopalJoinFaceIndex.subset_joinCarrier T hu,
      fun w hw hproj ↦ hy u hu w hw hproj⟩

/-- Each parameter set `S_F` is closed. -/
theorem faceParameterSet_isClosed (T : PolytopalJoinFaceIndex P m) :
    IsClosed (Φ.faceParameterSet T) := by
  rw [Φ.faceParameterSet_eq_iInter T]
  refine isClosed_iInter fun u ↦ isClosed_iInter fun _hu ↦
    isClosed_iInter fun w ↦ isClosed_iInter fun _hw ↦
      isClosed_iInter fun _hproj ↦ isClosed_le ?_ ?_
  · exact (ContinuousLinearMap.apply ℝ ℝ (Φ.joinMap w)).continuous
  · exact (ContinuousLinearMap.apply ℝ ℝ (Φ.joinMap u)).continuous

/-- The same parameter set restricted to actual exposed faces of the join. -/
def exposedFaceParameterSet (T : PolytopalJoinExposedFaceIndex P m) :
    Set (StrongDual ℝ V) :=
  Φ.faceParameterSet T.val

theorem exposedFaceParameterSet_isClosed (T : PolytopalJoinExposedFaceIndex P m) :
    IsClosed (Φ.exposedFaceParameterSet T) :=
  Φ.faceParameterSet_isClosed T.val

/-!
### The global set `Y` and its closedness
-/

/-- The set `Y` of the paper, as a subset of the ambient product. -/
def topIncidenceSet : Set (PolytopalJoinAmbient n m × StrongDual ℝ V) :=
  {p | p.1 ∈ polytopalDeletedJoinCarrier P m ∧ ‖p.2‖ = 1 ∧
    p.1 ∈ (Φ.upperEnvelopeData p.2).topLocus}

theorem mem_topIncidenceSet_iff (p : PolytopalJoinAmbient n m × StrongDual ℝ V) :
    p ∈ Φ.topIncidenceSet ↔
      p.1 ∈ polytopalDeletedJoinCarrier P m ∧ ‖p.2‖ = 1 ∧
        p.1 ∈ (Φ.upperEnvelopeData p.2).topLocus :=
  Iff.rfl

/-- The subtype used by the concrete join development is canonically the
same topological space as the ambient-set model of `Y`. -/
def topIncidenceSpaceHomeomorph :
    Φ.TopIncidenceSpace ≃ₜ
      {p : PolytopalJoinAmbient n m × StrongDual ℝ V // p ∈ Φ.topIncidenceSet} where
  toFun p :=
    ⟨(p.val.fst.val, p.val.snd.val),
      p.val.fst.property, p.val.snd.property, p.property⟩
  invFun p :=
    ⟨(⟨p.val.fst, p.property.1⟩, ⟨p.val.snd, p.property.2.1⟩),
      p.property.2.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl
  right_inv p := by
    apply Subtype.ext
    rfl
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop

/-- The fiber of `Y` over a unit dual functional is exactly the concrete
fiber `Y_y`. -/
theorem topIncidenceSet_fiber (y : StrongDual ℝ V) (hy : ‖y‖ = 1) :
    {z : PolytopalJoinAmbient n m | (z, y) ∈ Φ.topIncidenceSet} =
      Φ.deletedJoinTopLocus y := by
  ext z
  simp only [mem_ofPred_eq, mem_topIncidenceSet_iff, hy, true_and]
  exact Iff.rfl

/-- **The finite face description of `Y`.**  Up to the sphere condition on
`y`, the set `Y` is the finite union of the products `(D ∩ F) × S_F`. -/
theorem topIncidenceSet_eq_faceUnion :
    Φ.topIncidenceSet =
      {p : PolytopalJoinAmbient n m × StrongDual ℝ V | ‖p.2‖ = 1} ∩
        ⋃ T : PolytopalJoinFaceIndex P m,
          (polytopalDeletedJoinCarrier P m ∩ polytopalJoinFaceCarrier T) ×ˢ
            Φ.faceParameterSet T := by
  ext p
  constructor
  · rintro ⟨hD, hnorm, htop⟩
    refine ⟨hnorm, ?_⟩
    obtain ⟨T, hpT, hTtop, _hnonneg⟩ :=
      Φ.exists_joinFace_mem_of_mem_topLocus p.2 htop
    exact mem_iUnion.2 ⟨T, ⟨hD, hpT⟩, hTtop⟩
  · rintro ⟨hnorm, hunion⟩
    obtain ⟨T, ⟨hD, hpT⟩, hpS⟩ := mem_iUnion.1 hunion
    exact ⟨hD, hnorm, hpS hpT⟩

/-- The finite face description can be indexed only by genuine exposed
faces of the join polytope. -/
theorem topIncidenceSet_eq_exposedFaceUnion :
    Φ.topIncidenceSet =
      {p : PolytopalJoinAmbient n m × StrongDual ℝ V | ‖p.2‖ = 1} ∩
        ⋃ T : PolytopalJoinExposedFaceIndex P m,
          (polytopalDeletedJoinCarrier P m ∩ polytopalJoinFaceCarrier T.val) ×ˢ
            Φ.exposedFaceParameterSet T := by
  ext p
  constructor
  · rintro ⟨hD, hnorm, htop⟩
    refine ⟨hnorm, ?_⟩
    obtain ⟨T, hpT, hTtop, _hnonneg⟩ :=
      Φ.exists_exposedJoinFace_nonnegative_of_mem_topLocus p.2 htop
    exact mem_iUnion.2 ⟨T, ⟨hD, hpT⟩, hTtop⟩
  · rintro ⟨hnorm, hunion⟩
    obtain ⟨T, ⟨hD, hpT⟩, hpS⟩ := mem_iUnion.1 hunion
    exact ⟨hD, hnorm, hpS hpT⟩

/-- **Part (b) of Lemma `Y`: `Y` is closed.** -/
theorem topIncidenceSet_isClosed : IsClosed Φ.topIncidenceSet := by
  rw [Φ.topIncidenceSet_eq_faceUnion]
  refine IsClosed.inter ?_ (isClosed_iUnion_of_finite fun T ↦ ?_)
  · have hcont : Continuous
        (fun p : PolytopalJoinAmbient n m × StrongDual ℝ V ↦ ‖p.2‖) := by
      fun_prop
    have hpre : {p : PolytopalJoinAmbient n m × StrongDual ℝ V | ‖p.2‖ = 1} =
        (fun p : PolytopalJoinAmbient n m × StrongDual ℝ V ↦ ‖p.2‖) ⁻¹' {1} := by
      ext p
      simp
    rw [hpre]
    exact (isClosed_singleton (X := ℝ) (x := 1)).preimage hcont
  · exact IsClosed.prod
      ((polytopalDeletedJoinCarrier_compact P).isClosed.inter
        (PolytopalJoinFaceIndex.isClosed T))
      (Φ.faceParameterSet_isClosed T)

/-- **Part (b) of Lemma `Y`: `Y` is compact.** -/
theorem topIncidenceSet_isCompact [FiniteDimensional ℝ V] :
    IsCompact Φ.topIncidenceSet := by
  refine IsCompact.of_isClosed_subset
    ((polytopalDeletedJoinCarrier_compact P).prod
      (isCompact_sphere (0 : StrongDual ℝ V) 1))
    Φ.topIncidenceSet_isClosed ?_
  rintro p ⟨hD, hnorm, -⟩
  exact ⟨hD, mem_sphere_zero_iff_norm.2 hnorm⟩

/-- The topological space `Y` of the paper is compact. -/
theorem topIncidenceSpace_compactSpace [FiniteDimensional ℝ V] :
    CompactSpace Φ.TopIncidenceSpace := by
  have hsphere : IsCompact {y : StrongDual ℝ V | ‖y‖ = 1} := by
    have hset : {y : StrongDual ℝ V | ‖y‖ = 1} = Metric.sphere (0 : StrongDual ℝ V) 1 := by
      ext y
      simp
    rw [hset]
    exact isCompact_sphere _ _
  have _ : CompactSpace (DualUnitSphere V) := isCompact_iff_compactSpace.mp hsphere
  have hcont : Continuous
      (fun p : PolytopalDeletedJoinSpace P m × DualUnitSphere V ↦
        ((p.1 : PolytopalJoinAmbient n m), (p.2 : StrongDual ℝ V))) := by
    fun_prop
  have hclosed : IsClosed
      {p : PolytopalDeletedJoinSpace P m × DualUnitSphere V |
        (p.1 : PolytopalJoinAmbient n m) ∈
          (Φ.upperEnvelopeData (p.2 : StrongDual ℝ V)).topLocus} := by
    have hpre : {p : PolytopalDeletedJoinSpace P m × DualUnitSphere V |
        (p.1 : PolytopalJoinAmbient n m) ∈
          (Φ.upperEnvelopeData (p.2 : StrongDual ℝ V)).topLocus} =
        (fun p : PolytopalDeletedJoinSpace P m × DualUnitSphere V ↦
          ((p.1 : PolytopalJoinAmbient n m), (p.2 : StrongDual ℝ V))) ⁻¹'
            Φ.topIncidenceSet := by
      ext p
      constructor
      · intro hp
        exact ⟨p.1.2, p.2.2, hp⟩
      · rintro ⟨-, -, hp⟩
        exact hp
    rw [hpre]
    exact Φ.topIncidenceSet_isClosed.preimage hcont
  exact isCompact_iff_compactSpace.mp hclosed.isCompact

/-- **Part (c) of Lemma `Y`: the projection `Y → S(V*)` is continuous.** -/
theorem topIncidenceProjection_continuous :
    Continuous Φ.topIncidenceProjection :=
  continuous_snd.comp continuous_subtype_val

/-- **Part (a) of Lemma `Y`: every fiber of `Y` over the dual unit sphere is
nonempty.** -/
theorem topIncidenceSet_fiber_nonempty (y : DualUnitSphere V) :
    {z : PolytopalJoinAmbient n m |
      (z, (y : StrongDual ℝ V)) ∈ Φ.topIncidenceSet}.Nonempty := by
  rw [Φ.topIncidenceSet_fiber y.1 y.2]
  exact Φ.deletedJoinTopLocus_nonempty y.1

/-!
### Auxiliary facewise incidence inclusions
-/

/-- An auxiliary finite facewise incidence space, indexed by all convex
hulls of Cayley-vertex subsets.  The paper's actual deleted-cell incidence
space is `PolytopalJoinMap.DeletedCellIncidenceSpace`. -/
abbrev JoinFaceIncidenceSpace :=
  FaceIncidenceSpace (polytopalDeletedJoinCarrier P m)
    (polytopalJoinFaceCarrier (P := P) (m := m)) (fun z ↦ Φ.joinMap z)

/-- The smaller auxiliary incidence space indexed only by genuine exposed
faces of the full join polytope. -/
abbrev JoinExposedFaceIncidenceSpace :=
  FaceIncidenceSpace (polytopalDeletedJoinCarrier P m)
    (fun T : PolytopalJoinExposedFaceIndex P m ↦ polytopalJoinFaceCarrier T.val)
    (fun z ↦ Φ.joinMap z)

/-- Every point of `Y` lies on a genuine exposed face of the join polytope
on which the `y`-height is nonnegative; in particular it lies in the
auxiliary finite incidence space. -/
theorem exists_face_nonneg_of_mem_topIncidenceSet
    {p : PolytopalJoinAmbient n m × StrongDual ℝ V} (hp : p ∈ Φ.topIncidenceSet) :
    ∃ T : PolytopalJoinFaceIndex P m,
      p.1 ∈ polytopalJoinFaceCarrier T ∧
        ∀ w ∈ polytopalJoinFaceCarrier T, 0 ≤ p.2 (Φ.joinMap w) := by
  obtain ⟨T, hpT, -, hnonneg⟩ :=
    Φ.exists_joinFace_mem_of_mem_topLocus p.2 hp.2.2
  exact ⟨T, hpT, hnonneg⟩

/-- The inclusion of `Y` into the auxiliary finite incidence space. -/
def topIncidenceToFaceIncidence (p : Φ.TopIncidenceSpace) :
    Φ.JoinFaceIncidenceSpace := by
  refine ⟨(p.1.1, p.1.2.1), p.1.2.2, ?_⟩
  obtain ⟨T, hmem, -, hnonneg⟩ :=
    Φ.exists_joinFace_mem_of_mem_topLocus p.1.2.1 p.2
  exact ⟨T, hmem, hnonneg⟩

@[simp]
theorem topIncidenceToFaceIncidence_fst (p : Φ.TopIncidenceSpace) :
    (Φ.topIncidenceToFaceIncidence p).1.1 = p.1.1 :=
  rfl

@[simp]
theorem topIncidenceToFaceIncidence_snd (p : Φ.TopIncidenceSpace) :
    (Φ.topIncidenceToFaceIncidence p).1.2 = p.1.2.1 :=
  rfl

/-- The inclusion `Y ⊆ X` commutes with the projections to the deleted
join. -/
theorem faceIncidenceProjection_topIncidenceToFaceIncidence
    (p : Φ.TopIncidenceSpace) :
    faceIncidenceProjection (Φ.topIncidenceToFaceIncidence p) = p.1.1 :=
  rfl

theorem topIncidenceToFaceIncidence_injective :
    Function.Injective Φ.topIncidenceToFaceIncidence := by
  intro p q hpq
  have h1 : p.1.1 = q.1.1 := congrArg (fun r ↦ r.1.1) hpq
  have h2 : (p.1.2 : StrongDual ℝ V) = (q.1.2 : StrongDual ℝ V) :=
    congrArg (fun r ↦ r.1.2) hpq
  apply Subtype.ext
  exact Prod.ext h1 (Subtype.ext h2)

theorem topIncidenceToFaceIncidence_continuous :
    Continuous Φ.topIncidenceToFaceIncidence := by
  apply Continuous.subtype_mk
  exact (continuous_fst.comp continuous_subtype_val).prodMk
    (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))

/-- The stronger inclusion of `Y` into the incidence space indexed only by
actual exposed faces of the join. -/
noncomputable def topIncidenceToExposedFaceIncidence (p : Φ.TopIncidenceSpace) :
    Φ.JoinExposedFaceIncidenceSpace := by
  refine ⟨(p.val.fst, p.val.snd.val), p.val.snd.property, ?_⟩
  obtain ⟨T, hmem, _htop, hnonneg⟩ :=
    Φ.exists_exposedJoinFace_nonnegative_of_mem_topLocus p.val.snd.val p.property
  exact ⟨T, hmem, hnonneg⟩

theorem topIncidenceToExposedFaceIncidence_injective :
    Function.Injective Φ.topIncidenceToExposedFaceIncidence := by
  intro p q hpq
  have h1 : p.val.fst = q.val.fst := congrArg (fun r ↦ r.val.fst) hpq
  have h2 : p.val.snd.val = q.val.snd.val := congrArg (fun r ↦ r.val.snd) hpq
  apply Subtype.ext
  exact Prod.ext h1 (Subtype.ext h2)

theorem topIncidenceToExposedFaceIncidence_continuous :
    Continuous Φ.topIncidenceToExposedFaceIncidence := by
  apply Continuous.subtype_mk
  exact (continuous_fst.comp continuous_subtype_val).prodMk
    (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))

/-- The genuine-join-face auxiliary incidence space is compact. -/
theorem joinExposedFaceIncidenceSpace_compactSpace [FiniteDimensional ℝ V] :
    CompactSpace Φ.JoinExposedFaceIncidenceSpace :=
  faceIncidenceSpace_compactSpace (polytopalDeletedJoinCarrier_compact P)
    fun T ↦ PolytopalJoinFaceIndex.isClosed T.val

/-- The auxiliary facewise incidence space is compact. -/
theorem joinFaceIncidenceSpace_compactSpace [FiniteDimensional ℝ V] :
    CompactSpace Φ.JoinFaceIncidenceSpace :=
  faceIncidenceSpace_compactSpace (polytopalDeletedJoinCarrier_compact P)
    fun T ↦ PolytopalJoinFaceIndex.isClosed T

/-- The completed global-`Y` assertions from part (I), together with the
auxiliary finite-incidence inclusion: every fiber is nonempty; `Y` is closed
and compact; its sphere projection is continuous and surjective; and every
point lies on an exposed join face with nonnegative `y`-height.  The actual
cell-level inclusion used by the paper is proved in
`PolytopalCellIncidence.lean`. -/
theorem lemmaY_polytopal_part [FiniteDimensional ℝ V] :
    (∀ y : DualUnitSphere V,
        {z : PolytopalJoinAmbient n m |
          (z, (y : StrongDual ℝ V)) ∈ Φ.topIncidenceSet}.Nonempty) ∧
      IsClosed Φ.topIncidenceSet ∧
      IsCompact Φ.topIncidenceSet ∧
      Continuous Φ.topIncidenceProjection ∧
      Function.Surjective Φ.topIncidenceProjection ∧
      (∀ p ∈ Φ.topIncidenceSet, ∃ T : PolytopalJoinFaceIndex P m,
        p.1 ∈ polytopalJoinFaceCarrier T ∧
          ∀ w ∈ polytopalJoinFaceCarrier T, 0 ≤ p.2 (Φ.joinMap w)) :=
  ⟨Φ.topIncidenceSet_fiber_nonempty, Φ.topIncidenceSet_isClosed,
    Φ.topIncidenceSet_isCompact, Φ.topIncidenceProjection_continuous,
    Φ.topIncidenceProjection_surjective,
    fun _p hp ↦ Φ.exists_face_nonneg_of_mem_topIncidenceSet hp⟩

end PolytopalJoinMap

end AffineTverberg
