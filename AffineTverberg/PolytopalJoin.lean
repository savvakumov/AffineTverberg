import AffineTverberg.DeletedJoin
import AffineTverberg.RyFullDimensional
import AffineTverberg.PolyhedralTop
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option linter.style.header false

/-!
# The concrete polytopal join and its upper envelope

This file realizes the join `Q = P₁ * ⋯ * Pᵣ` as the convex hull of the
finite family of Cayley-embedded vertices.  A factorwise affine map extends
to a continuous linear map on this ambient vector space, while summing the
first coordinates gives the diagonal projection `π : Q → P`.

This supplies the concrete `CompactConvexProjection` to which the abstract
`R_y`, full-dimensionality, and finite-support-cover theorems apply.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg

/-- A vector-space realization of the `(m + 1)`-fold join.  The entry in
factor `i` is a homogenized pair `(tᵢ xᵢ, tᵢ)`. -/
abbrev PolytopalJoinAmbient (n m : ℕ) :=
  Fin (m + 1) → CoordinateSpace n × ℝ

/-- The copy of a point in one join factor. -/
def polytopalJoinCopy {n m : ℕ} (i : Fin (m + 1)) (x : CoordinateSpace n) :
    PolytopalJoinAmbient n m :=
  Pi.single i (x, 1)

/-- The linear diagonal projection, obtained by summing all first
coordinates. -/
def polytopalJoinProjectionLinear (n m : ℕ) :
    PolytopalJoinAmbient n m →ₗ[ℝ] CoordinateSpace n where
  toFun z := ∑ i, (z i).1
  map_add' z w := by
    simp only [Pi.add_apply, Prod.fst_add]
    exact Finset.sum_add_distrib
  map_smul' a z := by
    simp only [Pi.smul_apply, Prod.smul_fst]
    exact Finset.smul_sum.symm

/-- The continuous diagonal projection. -/
def polytopalJoinProjection (n m : ℕ) :
    PolytopalJoinAmbient n m →L[ℝ] CoordinateSpace n :=
  (polytopalJoinProjectionLinear n m).toContinuousLinearMap

@[simp]
theorem polytopalJoinProjection_copy {n m : ℕ}
    (i : Fin (m + 1)) (x : CoordinateSpace n) :
    polytopalJoinProjection n m (polytopalJoinCopy i x) = x := by
  classical
  change ∑ j : Fin (m + 1), ((polytopalJoinCopy i x) j).1 = x
  rw [Finset.sum_eq_single i]
  · simp [polytopalJoinCopy]
  · intro j _hj hji
    simp [polytopalJoinCopy, Pi.single_eq_of_ne hji]
  · simp

/-- The linear part of the inclusion of one join factor. -/
def polytopalJoinCopyLinear {n m : ℕ} (i : Fin (m + 1)) :
    CoordinateSpace n →ₗ[ℝ] PolytopalJoinAmbient n m where
  toFun x := Pi.single i (x, 0)
  map_add' x y := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Pi.single_eq_of_ne hji]
  map_smul' a x := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Pi.single_eq_of_ne hji]

/-- The affine inclusion of one copy of the original polytope into the
Cayley realization of the join. -/
def polytopalJoinCopyAffine {n m : ℕ} (i : Fin (m + 1)) :
    CoordinateSpace n →ᵃ[ℝ] PolytopalJoinAmbient n m where
  toFun := polytopalJoinCopy i
  linear := polytopalJoinCopyLinear i
  map_vadd' x v := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [polytopalJoinCopy, polytopalJoinCopyLinear]
    · simp [polytopalJoinCopy, polytopalJoinCopyLinear,
        Pi.single_eq_of_ne hji]

@[simp]
theorem polytopalJoinCopyAffine_apply {n m : ℕ}
    (i : Fin (m + 1)) (x : CoordinateSpace n) :
    polytopalJoinCopyAffine i x = polytopalJoinCopy i x :=
  rfl

/-- Indices for the finite set of copied vertices of the join. -/
abbrev PolytopalJoinVertexIndex {n : ℕ} (P : FullDimensionalPolytope n) (m : ℕ) :=
  Fin (m + 1) × {v // v ∈ P.vertices}

/-- The finite Cayley-embedded vertex set of `P₁ * ⋯ * Pᵣ`. -/
noncomputable def polytopalJoinVertices {n : ℕ}
    (P : FullDimensionalPolytope n) (m : ℕ) :
    Finset (PolytopalJoinAmbient n m) := by
  classical
  exact Finset.univ.image fun iv : PolytopalJoinVertexIndex P m ↦
    polytopalJoinCopy iv.1 iv.2.1

/-- The concrete polytopal join is the convex hull of all copied vertices. -/
def polytopalJoinCarrier {n : ℕ} (P : FullDimensionalPolytope n) (m : ℕ) :
    Set (PolytopalJoinAmbient n m) :=
  convexHull ℝ (polytopalJoinVertices P m : Set (PolytopalJoinAmbient n m))

theorem polytopalJoinCopy_vertex_mem_vertices {n m : ℕ}
    (P : FullDimensionalPolytope n) (i : Fin (m + 1))
    {v : CoordinateSpace n} (hv : v ∈ P.vertices) :
    polytopalJoinCopy i v ∈ polytopalJoinVertices P m := by
  classical
  rw [polytopalJoinVertices, Finset.mem_image]
  exact ⟨(i, ⟨v, hv⟩), Finset.mem_univ _, rfl⟩

/-- Every point of every copied factor lies in the convex hull of the
copied vertices. -/
theorem polytopalJoinCopy_mem_carrier {n m : ℕ}
    (P : FullDimensionalPolytope n) (i : Fin (m + 1)) (x : P.carrier) :
    polytopalJoinCopy i x.1 ∈ polytopalJoinCarrier P m := by
  have hx : x.1 ∈ convexHull ℝ (P.vertices : Set (CoordinateSpace n)) := x.2
  have hximage : polytopalJoinCopyAffine i x.1 ∈
      polytopalJoinCopyAffine i ''
        convexHull ℝ (P.vertices : Set (CoordinateSpace n)) := ⟨x.1, hx, rfl⟩
  rw [(polytopalJoinCopyAffine i).image_convexHull] at hximage
  apply convexHull_mono (𝕜 := ℝ) _ hximage
  rintro _ ⟨v, hv, rfl⟩
  exact Finset.mem_coe.mpr
    (polytopalJoinCopy_vertex_mem_vertices P i (Finset.mem_coe.mp hv))

/-- Projecting the copied join vertices recovers exactly the vertex set of
the original polytope. -/
theorem polytopalJoinProjection_image_vertices {n m : ℕ}
    (P : FullDimensionalPolytope n) :
    polytopalJoinProjection n m ''
        (polytopalJoinVertices P m : Set (PolytopalJoinAmbient n m)) =
      (P.vertices : Set (CoordinateSpace n)) := by
  classical
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Finset.mem_coe, polytopalJoinVertices, Finset.mem_image] at hz
    obtain ⟨⟨i, v⟩, _hiv, rfl⟩ := hz
    rw [polytopalJoinProjection_copy]
    exact Finset.mem_coe.mpr v.2
  · intro hx
    have hx' : x ∈ P.vertices := Finset.mem_coe.mp hx
    let i : Fin (m + 1) := Fin.last m
    refine ⟨polytopalJoinCopy i x, ?_, ?_⟩
    · exact Finset.mem_coe.mpr
        (polytopalJoinCopy_vertex_mem_vertices P i hx')
    · exact polytopalJoinProjection_copy i x

namespace PolytopeDeletedJoinPoint

variable {n m : ℕ} (P : FullDimensionalPolytope n)

/-- A point supported in a single join factor is automatically in the
deleted join: use the full polytope in that factor and the empty face in
all other factors. -/
noncomputable def singleFactor (i : Fin (m + 1)) (x : P.carrier) :
    PolytopeDeletedJoinPoint (m := m) P := by
  classical
  exact
    { weight := fun j ↦ if j = i then 1 else 0
      point := fun _ ↦ x
      face := fun j ↦ if j = i then P.carrier else ∅
      weight_nonneg := by
        intro j
        split <;> norm_num
      weight_sum := by simp
      face_isFace := by
        intro j
        by_cases hji : j = i
        · simp [hji, FullDimensionalPolytope.IsFace, IsExposed.refl]
        · simp [hji, FullDimensionalPolytope.IsFace, isExposed_empty]
      faces_pairwiseDisjoint := by
        intro j k hjk
        rw [Set.disjoint_left]
        intro z hzj hzk
        by_cases hji : j = i
        · have hki : k ≠ i := by
            intro h
            exact hjk (hji.trans h.symm)
          simp [hki] at hzk
        · simp [hji] at hzj
      point_mem_face := by
        intro j hj
        by_cases hji : j = i
        · simp [hji]
        · simp [hji] at hj }

/-- The Cayley realization of a represented deleted-join point. -/
def realization (z : PolytopeDeletedJoinPoint (m := m) P) :
    PolytopalJoinAmbient n m :=
  ∑ i, z.weight i • polytopalJoinCopy i (z.point i).1

@[simp]
theorem realization_singleFactor (i : Fin (m + 1)) (x : P.carrier) :
    (singleFactor P i x).realization = polytopalJoinCopy i x.1 := by
  classical
  rw [realization, Finset.sum_eq_single i]
  · simp [singleFactor]
  · intro j _hj hji
    simp [singleFactor, hji]
  · simp

/-- Every represented deleted-join point realizes to a point of the
concrete convex join. -/
theorem realization_mem_carrier (z : PolytopeDeletedJoinPoint (m := m) P) :
    z.realization ∈ polytopalJoinCarrier P m := by
  apply (convex_convexHull ℝ
    (polytopalJoinVertices P m : Set (PolytopalJoinAmbient n m))).sum_mem
      (fun i _hi ↦ z.weight_nonneg i) z.weight_sum
  intro i _hi
  exact polytopalJoinCopy_mem_carrier P i (z.point i)

/-- Every Cayley vertex has a canonical representative in the polytopal
deleted join, supported on just its own factor. -/
theorem exists_realization_eq_of_mem_vertices
    {v : PolytopalJoinAmbient n m} (hv : v ∈ polytopalJoinVertices P m) :
    ∃ z : PolytopeDeletedJoinPoint (m := m) P, z.realization = v := by
  classical
  rw [polytopalJoinVertices, Finset.mem_image] at hv
  obtain ⟨⟨i, p⟩, _hip, rfl⟩ := hv
  have hp : p.1 ∈ P.carrier := by
    exact subset_convexHull ℝ (P.vertices : Set (CoordinateSpace n))
      (Finset.mem_coe.mpr p.2)
  let x : P.carrier := ⟨p.1, hp⟩
  exact ⟨singleFactor P i x, realization_singleFactor P i x⟩

@[simp]
theorem projection_realization (z : PolytopeDeletedJoinPoint (m := m) P) :
    polytopalJoinProjection n m z.realization =
      ∑ i, z.weight i • (z.point i).1 := by
  rw [realization, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul, polytopalJoinProjection_copy]

end PolytopeDeletedJoinPoint

namespace PolytopalJoinMap

variable {n m : ℕ} {P : FullDimensionalPolytope n}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (Φ : PolytopalJoinMap P m V)

/-- A chosen ambient affine extension of a factor map. -/
noncomputable def affineExtension (i : Fin (m + 1)) :
    CoordinateSpace n →ᵃ[ℝ] V :=
  Classical.choose (Φ.factor_affine i)

theorem factor_eq_affineExtension (i : Fin (m + 1)) (x : P.carrier) :
    Φ.factor i x = Φ.affineExtension i x.1 :=
  Classical.choose_spec (Φ.factor_affine i) x

/-- The linear extension of the factorwise affine map to the homogenized
join ambient space. -/
noncomputable def joinMapLinear : PolytopalJoinAmbient n m →ₗ[ℝ] V where
  toFun z := ∑ i : Fin (m + 1),
    ((Φ.affineExtension i).linear (z i).1 + (z i).2 • Φ.affineExtension i 0)
  map_add' z w := by
    simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, map_add, add_smul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    abel
  map_smul' a z := by
    simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, map_smul]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    simp [smul_add, smul_smul]

/-- The continuous linear join map extending all factors. -/
noncomputable def joinMap : PolytopalJoinAmbient n m →L[ℝ] V :=
  Φ.joinMapLinear.toContinuousLinearMap

@[simp]
theorem joinMap_copy (i : Fin (m + 1)) (x : P.carrier) :
    Φ.joinMap (polytopalJoinCopy i x.1) = Φ.factor i x := by
  classical
  rw [Φ.factor_eq_affineExtension]
  change (∑ j : Fin (m + 1),
      ((Φ.affineExtension j).linear ((polytopalJoinCopy i x.1) j).1 +
      ((polytopalJoinCopy i x.1) j).2 • Φ.affineExtension j 0)) =
    Φ.affineExtension i x.1
  rw [Finset.sum_eq_single i]
  · simp only [polytopalJoinCopy, Pi.single_eq_same, one_smul]
    simpa using (congrFun (Φ.affineExtension i).decomp x.1).symm
  · intro j _hj hji
    simp [polytopalJoinCopy, Pi.single_eq_of_ne hji]
  · simp

/-- Evaluating the linear join map on the Cayley realization agrees with
the factorwise value used by `theorem:zero`. -/
theorem joinMap_realization (z : PolytopeDeletedJoinPoint (m := m) P) :
    Φ.joinMap z.realization = Φ.value z := by
  rw [PolytopeDeletedJoinPoint.realization, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul, Φ.joinMap_copy]

/-- The concrete compact convex projection behind `R_y` for a polytopal
join map and a dual functional `y`. -/
noncomputable def upperEnvelopeData (y : StrongDual ℝ V) :
    CompactConvexProjection (PolytopalJoinAmbient n m) (CoordinateSpace n) where
  carrier := polytopalJoinCarrier P m
  carrier_compact :=
    (polytopalJoinVertices P m).finite_toSet.isCompact_convexHull ℝ
  carrier_convex := convex_convexHull ℝ _
  projection := polytopalJoinProjection n m
  height := y.comp Φ.joinMap

/-- Height of a realized deleted-join witness is the dual evaluation of
the factorwise value appearing in `theorem:zero`. -/
@[simp]
theorem upperEnvelopeData_height_realization (y : StrongDual ℝ V)
    (z : PolytopeDeletedJoinPoint (m := m) P) :
    (Φ.upperEnvelopeData y).height z.realization = y (Φ.value z) := by
  change y (Φ.joinMap z.realization) = y (Φ.value z)
  rw [Φ.joinMap_realization]

@[simp]
theorem upperEnvelopeData_carrier (y : StrongDual ℝ V) :
    (Φ.upperEnvelopeData y).carrier = polytopalJoinCarrier P m :=
  rfl

@[simp]
theorem upperEnvelopeData_projection (y : StrongDual ℝ V) :
    (Φ.upperEnvelopeData y).projection = polytopalJoinProjection n m :=
  rfl

@[simp]
theorem upperEnvelopeData_height_copy (y : StrongDual ℝ V)
    (i : Fin (m + 1)) (x : P.carrier) :
    (Φ.upperEnvelopeData y).height (polytopalJoinCopy i x.1) =
      y (Φ.factor i x) := by
  simp [upperEnvelopeData]

/-- The base of the join projection is precisely the original polytope. -/
theorem upperEnvelopeData_base (y : StrongDual ℝ V) :
    (Φ.upperEnvelopeData y).base = P.carrier := by
  change polytopalJoinProjection n m '' polytopalJoinCarrier P m =
    convexHull ℝ (P.vertices : Set (CoordinateSpace n))
  rw [polytopalJoinCarrier]
  change (polytopalJoinProjection n m).toLinearMap ''
      convexHull ℝ (polytopalJoinVertices P m : Set (PolytopalJoinAmbient n m)) = _
  rw [LinearMap.image_convexHull]
  congr 1
  exact polytopalJoinProjection_image_vertices P

/-- Claim `R_y-full-dimensional` for the concrete polytopal join: if the
factor map is nondegenerate and `y` is nonzero, the lifted image affinely
spans `P` together with the full vertical direction. -/
theorem upperEnvelopeData_liftedImage_affineSpan_eq_top
    (y : StrongDual ℝ V) (hy : y ≠ 0)
    (hspan : FactorImagesAffinelySpan Φ.factor) :
    affineSpan ℝ (Φ.upperEnvelopeData y).liftedImage = ⊤ := by
  apply CompactConvexProjection.liftedImage_affineSpan_eq_top_of_diagonal_factors
    (Φ.upperEnvelopeData y)
    (fun x : P.carrier ↦ x.1) Φ.factor
    (fun i x ↦ polytopalJoinCopy i x.1) (y := y.toLinearMap)
  · intro i x
    exact polytopalJoinCopy_mem_carrier P i x
  · intro i x
    exact polytopalJoinProjection_copy i x.1
  · intro i x
    exact Φ.upperEnvelopeData_height_copy y i x
  · rw [show Set.range (fun x : P.carrier ↦ x.1) = P.carrier by
      ext x
      simp]
    rw [FullDimensionalPolytope.carrier, affineSpan_convexHull,
      P.affineSpan_vertices]
  · exact Φ.diagonal_relation
  · exact hspan
  · intro hzero
    apply hy
    ext v
    exact LinearMap.congr_fun hzero v

/-- The diagonal relation supplies a nonnegative-height point in every
projection fiber of the concrete join. -/
theorem upperEnvelopeData_hasNonnegativeFiberWitness
    (y : StrongDual ℝ V) :
    (Φ.upperEnvelopeData y).HasNonnegativeFiberWitness := by
  intro b hb
  have hbP : b ∈ P.carrier := by
    rw [← Φ.upperEnvelopeData_base y]
    exact hb
  let x : P.carrier := ⟨b, hbP⟩
  have hsum : ∑ i : Fin (m + 1),
      (Φ.upperEnvelopeData y).height (polytopalJoinCopy i b) = 0 := by
    calc
      ∑ i : Fin (m + 1),
          (Φ.upperEnvelopeData y).height (polytopalJoinCopy i b) =
          ∑ i : Fin (m + 1), y (Φ.factor i x) := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact Φ.upperEnvelopeData_height_copy y i x
      _ = y (∑ i : Fin (m + 1), Φ.factor i x) := by
        rw [map_sum]
      _ = 0 := by rw [Φ.diagonal_relation, map_zero]
  obtain ⟨i, hi⟩ := exists_nonnegative_of_sum_eq_zero
    (fun i : Fin (m + 1) ↦
      (Φ.upperEnvelopeData y).height (polytopalJoinCopy i b)) hsum
  refine ⟨polytopalJoinCopy i b, polytopalJoinCopy_mem_carrier P i x, ?_, hi⟩
  exact polytopalJoinProjection_copy i b

/-- The concrete polytopal join inherits the finite upper-support cover
constructed from its finite Cayley vertex set. -/
noncomputable def upperEnvelopeData_finiteUpperSupportCover
    (y : StrongDual ℝ V) :
    CompactConvexProjection.FiniteUpperSupportCover (Φ.upperEnvelopeData y) :=
  CompactConvexProjection.polytopeFiniteUpperSupportCover
    (Φ.upperEnvelopeData y) (polytopalJoinVertices P m) rfl

/-- The facewise support description of the top locus for the concrete
polytopal join. -/
theorem upperEnvelopeData_supportedTopLocus_eq_topLocus
    (y : StrongDual ℝ V) :
    (Φ.upperEnvelopeData y).supportedTopLocus =
      (Φ.upperEnvelopeData y).topLocus :=
  CompactConvexProjection.polytope_supportedTopLocus_eq_topLocus
    (Φ.upperEnvelopeData y) (polytopalJoinVertices P m) rfl

/-- The concrete top locus is compact. -/
theorem upperEnvelopeData_topLocus_compact (y : StrongDual ℝ V) :
    IsCompact (Φ.upperEnvelopeData y).topLocus :=
  CompactConvexProjection.polytope_topLocus_compact
    (Φ.upperEnvelopeData y) (polytopalJoinVertices P m) rfl

/-- The concrete top graph `Γ_y` is compact. -/
theorem upperEnvelopeData_topGraph_compact (y : StrongDual ℝ V) :
    IsCompact (Φ.upperEnvelopeData y).topGraph :=
  CompactConvexProjection.polytope_topGraph_compact
    (Φ.upperEnvelopeData y) (polytopalJoinVertices P m) rfl

/-- Concrete form of the paper's inclusion `Y ⊆ X`: every point on the
top locus has nonnegative `λ_y`-height. -/
theorem upperEnvelopeData_height_nonnegative_on_topLocus
    (y : StrongDual ℝ V) :
    ∀ z ∈ (Φ.upperEnvelopeData y).topLocus,
      0 ≤ (Φ.upperEnvelopeData y).height z :=
  CompactConvexProjection.polytope_height_nonnegative_on_topLocus
    (Φ.upperEnvelopeData y) (polytopalJoinVertices P m) rfl
    (Φ.upperEnvelopeData_hasNonnegativeFiberWitness y)

/-- A global height maximum can be chosen among the copied vertices, and
every such global maximum belongs to the fiberwise top locus.  This is the
geometric core of Claim `Yy-nonempty`. -/
theorem exists_joinVertex_mem_upperEnvelopeData_topLocus
    (y : StrongDual ℝ V) :
    ∃ v ∈ polytopalJoinVertices P m,
      v ∈ (Φ.upperEnvelopeData y).topLocus := by
  classical
  let A := Φ.upperEnvelopeData y
  have hvertices : (polytopalJoinVertices P m).Nonempty := by
    obtain ⟨p, hp⟩ := P.vertices_nonempty
    exact ⟨polytopalJoinCopy (Fin.last m) p,
      polytopalJoinCopy_vertex_mem_vertices P (Fin.last m) hp⟩
  obtain ⟨v, hv, hmax⟩ := (polytopalJoinVertices P m).exists_max_image A.height hvertices
  have hvcarrier : v ∈ A.carrier := by
    change v ∈ convexHull ℝ (polytopalJoinVertices P m : Set _)
    exact subset_convexHull ℝ
      (polytopalJoinVertices P m : Set (PolytopalJoinAmbient n m))
      (Finset.mem_coe.mpr hv)
  have hglobal : ∀ w ∈ A.carrier, A.height w ≤ A.height v := by
    intro w hw
    have hconv : Convex ℝ {z : PolytopalJoinAmbient n m | A.height z ≤ A.height v} :=
      convex_halfSpace_le A.height.toLinearMap.isLinear _
    have hsub : (polytopalJoinVertices P m : Set _) ⊆
        {z : PolytopalJoinAmbient n m | A.height z ≤ A.height v} := by
      intro z hz
      exact hmax z (Finset.mem_coe.mp hz)
    exact convexHull_min hsub hconv hw
  refine ⟨v, hv, ?_⟩
  rw [A.mem_topLocus_iff]
  exact ⟨hvcarrier, fun w hw _hprojection ↦ hglobal w hw⟩

/-- The witness-level fiber `Y_y` from the polytopal proof: represented
deleted-join points whose Cayley realizations lie on the upper envelope. -/
def deletedJoinTopFiber (y : StrongDual ℝ V) :
    Set (PolytopeDeletedJoinPoint (m := m) P) :=
  {z | z.realization ∈ (Φ.upperEnvelopeData y).topLocus}

/-- Claim `Yy-nonempty` for the concrete polytopal join.  A global maximum
may be chosen at a Cayley vertex, and a single-factor witness represents
that vertex in the deleted join. -/
theorem deletedJoinTopFiber_nonempty (y : StrongDual ℝ V) :
    (Φ.deletedJoinTopFiber y).Nonempty := by
  obtain ⟨v, hv, hvtop⟩ :=
    Φ.exists_joinVertex_mem_upperEnvelopeData_topLocus y
  obtain ⟨z, hz⟩ :=
    PolytopeDeletedJoinPoint.exists_realization_eq_of_mem_vertices P hv
  refine ⟨z, ?_⟩
  change z.realization ∈ (Φ.upperEnvelopeData y).topLocus
  rw [hz]
  exact hvtop

/-- Concrete witness-level form of `Y ⊆ X`: every point of `Y_y` has
nonnegative evaluation under the chosen dual functional. -/
theorem deletedJoinTopFiber_value_nonnegative (y : StrongDual ℝ V)
    {z : PolytopeDeletedJoinPoint (m := m) P}
    (hz : z ∈ Φ.deletedJoinTopFiber y) :
    0 ≤ y (Φ.value z) := by
  rw [← Φ.upperEnvelopeData_height_realization y z]
  exact Φ.upperEnvelopeData_height_nonnegative_on_topLocus y z.realization hz

/-- A copied vertex lies on a supporting contact face on which `λ_y` is
nonnegative everywhere.  This packages the nonemptiness and `Y ⊆ X`
ingredients in the facewise form used by the paper. -/
theorem exists_nonnegative_supportFace_containing_joinVertex
    (y : StrongDual ℝ V) :
    ∃ v ∈ polytopalJoinVertices P m,
      ∃ c : CompactConvexProjection.UpperSupportCertificate
          (Φ.upperEnvelopeData y),
        v ∈ c.contactSet ∧
          ∀ z ∈ c.contactSet, 0 ≤ (Φ.upperEnvelopeData y).height z := by
  obtain ⟨v, hv, hvtop⟩ :=
    Φ.exists_joinVertex_mem_upperEnvelopeData_topLocus y
  obtain ⟨c, hvc⟩ :=
    CompactConvexProjection.exists_upperSupportCertificate_mem_contactSet_of_convexHull
      (Φ.upperEnvelopeData y) (polytopalJoinVertices P m) rfl hvtop
  refine ⟨v, hv, c, hvc, ?_⟩
  exact CompactConvexProjection.UpperSupportCertificate.height_nonnegative_on_contactSet
    (Φ.upperEnvelopeData y) c
    (Φ.upperEnvelopeData_hasNonnegativeFiberWitness y)

end PolytopalJoinMap

end AffineTverberg
