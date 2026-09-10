import AffineTverberg.BoundaryJoinPairModel
import AffineTverberg.GeometricCoordinateTransport
import AffineTverberg.SphereLocalRestriction

set_option linter.style.header false

/-!
# The paper's boundary join as a finite geometric sphere in coordinate space

The previously constructed subdivision is converted to an actual geometric
simplicial complex in the coordinate spaces used by the local-star theory.
The good subcomplex is still the actual deleted join, and the dimensions,
sphere homeomorphism and relative pair identification are all derived from
the original ball hypothesis. This does not assume Alexander duality.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric

namespace AffineTverberg.BadEdge.BoundaryJoinVertexIndexing

open AffineTverberg.Simplicial AffineTverberg.AffChain

variable {e n m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
  (a : BoundaryJoinVertexIndexing n K m)

/-- The ambient dimension of the homogenized product, not the sphere dimension. -/
abbrev coordinateDimension (e m : ℕ) := Module.finrank ℝ (PolytopalJoinAmbient e m)

/-- A linear change of coordinates on the whole join ambient space. -/
def coordinateEquiv :
    PolytopalJoinAmbient e m ≃L[ℝ] CoordinateSpace (coordinateDimension e m) :=
  ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm

/-- The very same subdivision vertices, expressed in ordinary coordinates. -/
def coordinatePoints : Finset (Fin a.size) → CoordinateSpace (coordinateDimension e m) :=
  coordinateEquiv ∘ a.realizationPoints

theorem isGeometricRealization_coordinatePoints :
    IsGeometricRealization a.joinComplex a.coordinatePoints :=
  a.isGeometricRealization_joinComplex.linearEquiv coordinateEquiv

/-- The ambient sphere triangulation as a Mathlib geometric simplicial complex. -/
def geometricJoin : Geometry.SimplicialComplex ℝ (CoordinateSpace (coordinateDimension e m)) :=
  geometricComplex a.faceClosed_joinComplex a.isGeometricRealization_coordinatePoints

/-- The good induced subcomplex, in exactly the same coordinates. -/
def geometricDeleted : Geometry.SimplicialComplex ℝ (CoordinateSpace (coordinateDimension e m)) :=
  geometricComplex a.faceClosed_deletedComplex
    (a.isGeometricRealization_coordinatePoints.mono a.deletedComplex_subset)

theorem geometricJoin_faces_finite : a.geometricJoin.faces.Finite :=
  geometricComplex_faces_finite _ _

theorem geometricDeleted_faces_finite : a.geometricDeleted.faces.Finite :=
  geometricComplex_faces_finite _ _

theorem geometricDeleted_faces_subset : a.geometricDeleted.faces ⊆ a.geometricJoin.faces :=
  geometricComplex_faces_mono a.faceClosed_deletedComplex a.faceClosed_joinComplex
    a.deletedComplex_subset a.isGeometricRealization_coordinatePoints

theorem geometricJoin_space :
    a.geometricJoin.space = geometricCarrier a.joinComplex a.coordinatePoints :=
  geometricComplex_space _ _

theorem geometricDeleted_space :
    a.geometricDeleted.space = geometricCarrier a.deletedComplex a.coordinatePoints :=
  geometricComplex_space _ _

/-- The resulting carrier is the paper's literal boundary join. -/
def geometricJoinHomeomorph :
    ↥a.geometricJoin.space ≃ₜ ↥(simplicialBoundaryJoinCarrier K n m) :=
  (Homeomorph.setCongr a.geometricJoin_space).trans
    ((geometricCarrierLinearHomeomorph coordinateEquiv).symm.trans
      (Homeomorph.setCongr a.geometricCarrier_joinComplex))

/-- The subcomplex carrier is the paper's literal deleted join. -/
def geometricDeletedHomeomorph :
    ↥a.geometricDeleted.space ≃ₜ ↥(simplicialDeletedJoinCarrier n K m) :=
  (Homeomorph.setCongr a.geometricDeleted_space).trans
    ((geometricCarrierLinearHomeomorph coordinateEquiv).symm.trans
      (Homeomorph.setCongr a.geometricCarrier_deletedComplex))

/-- The constructed geometric complex is a topological sphere of exactly the required dimension. -/
def geometricJoinSphereHomeomorph (hball : IsSimplicialBall n K) (hn : 2 ≤ n) :
    ↥a.geometricJoin.space ≃ₜ sphere (0 : CoordinateSpace ((m + 1) * n)) 1 :=
  a.geometricJoinHomeomorph.trans (hball.fullBoundaryJoinHomeomorphSphere hn m)

/-- The original dimension bound holds for every actual geometric simplex. -/
theorem geometricJoin_card_le {S : Finset (CoordinateSpace (coordinateDimension e m))}
    (hS : S ∈ a.geometricJoin.faces) : S.card ≤ (m + 1) * n :=
  geometricComplex_card_le a.faceClosed_joinComplex a.isGeometricRealization_coordinatePoints
    (fun _ hs => a.card_joinComplex_le hs) hS

/-- Every face extends to the full sphere dimension; no purity assumption is added. -/
theorem geometricJoin_exists_top_extension (hball : IsSimplicialBall n K) (hn : 2 ≤ n)
    {S : Finset (CoordinateSpace (coordinateDimension e m))} (hS : S ∈ a.geometricJoin.faces) :
    ∃ T ∈ a.geometricJoin.faces, S ⊆ T ∧ T.card = (m + 1) * n :=
  geometricComplex_exists_top_extension a.faceClosed_joinComplex
    a.isGeometricRealization_coordinatePoints
    (fun _ hs => a.exists_top_simplex_extension hball hn hs) hS

theorem geometricJoin_card_facet (hball : IsSimplicialBall n K) (hn : 2 ≤ n)
    {S : Finset (CoordinateSpace (coordinateDimension e m))} (hS : S ∈ a.geometricJoin.facets) :
    S.card = (m + 1) * n :=
  geometricComplex_card_facet a.faceClosed_joinComplex a.isGeometricRealization_coordinatePoints
    (fun _ hs => a.exists_top_simplex_extension hball hn hs) hS

/-- The coordinate homeomorphism respects the literal inclusion of the deleted join. -/
theorem geometricJoinHomeomorph_mem_deleted (x : ↥a.geometricJoin.space) :
    x.val ∈ a.geometricDeleted.space ↔
      a.geometricJoinHomeomorph x ∈ deletedJoinInBoundaryJoin K n m := by
  change x.val ∈ a.geometricDeleted.space ↔
    (coordinateEquiv (e := e) (m := m)).symm x.val ∈ simplicialDeletedJoinCarrier n K m
  rw [a.geometricDeleted_space, ← a.geometricCarrier_deletedComplex]
  change x.val ∈ geometricCarrier a.deletedComplex (coordinateEquiv ∘ a.realizationPoints) ↔ _
  rw [← geometricCarrier_image_linearEquiv coordinateEquiv]
  constructor
  · rintro ⟨y, hy, hxy⟩
    simpa only [← hxy, ContinuousLinearEquiv.symm_apply_apply] using hy
  · intro hx
    exact ⟨_, hx, ContinuousLinearEquiv.apply_symm_apply _ _⟩

/-- The actual pair homology in the coordinate model is the actual paper pair homology. -/
def geometricPairHomologyIso (k : ℕ) :
    relativeHomology (X := TopCat.of ↥a.geometricJoin.space)
      (Subtype.val ⁻¹' a.geometricDeleted.space) k ≅
      relativeHomology (deletedJoinInBoundaryJoin K n m) k :=
  relativeHomologyIsoOfHomeomorph
    (X := TopCat.of ↥a.geometricJoin.space) (Y := boundaryJoinSpace K n m)
    a.geometricJoinHomeomorph a.geometricJoinHomeomorph_mem_deleted k

/-- The same map preserves the actual open complement. -/
theorem geometricJoinHomeomorph_mem_complement (x : ↥a.geometricJoin.space) :
    x.val ∈ a.geometricJoin.space \ a.geometricDeleted.space ↔
      a.geometricJoinHomeomorph x ∈ complementInBoundaryJoin K n m := by
  change (x.val ∈ a.geometricJoin.space ∧ x.val ∉ a.geometricDeleted.space) ↔
    ((a.geometricJoinHomeomorph x).val ∈ simplicialBoundaryJoinCarrier K n m ∧
      a.geometricJoinHomeomorph x ∉ deletedJoinInBoundaryJoin K n m)
  simp only [x.property, (a.geometricJoinHomeomorph x).property, true_and]
  exact not_congr (a.geometricJoinHomeomorph_mem_deleted x)

/-- The complement in the finite geometric sphere model is the literal
complement used in the paper. -/
def geometricComplementHomeomorph :
    ↥(a.geometricJoin.space \ a.geometricDeleted.space) ≃ₜ
      ↥(simplicialBoundaryJoinCarrier K n m \ simplicialDeletedJoinCarrier n K m) :=
  (subtypePreimageHomeomorph
    (S := a.geometricJoin.space \ a.geometricDeleted.space)
    (T := a.geometricJoin.space) (fun _ hx => hx.1)).symm.trans
    ((a.geometricJoinHomeomorph.subtype a.geometricJoinHomeomorph_mem_complement).trans
      (complementHomeomorph K))

/-- Relative homology with support on the deleted join is also the actual paper group. -/
def geometricComplementPairHomologyIso (k : ℕ) :
    relativeHomology (X := TopCat.of ↥a.geometricJoin.space)
      (Subtype.val ⁻¹' (a.geometricJoin.space \ a.geometricDeleted.space)) k ≅
      relativeHomology (complementInBoundaryJoin K n m) k :=
  relativeHomologyIsoOfHomeomorph
    (X := TopCat.of ↥a.geometricJoin.space) (Y := boundaryJoinSpace K n m)
    a.geometricJoinHomeomorph a.geometricJoinHomeomorph_mem_complement k

/-- The completed bad-complex argument supplies the complement vanishing in this geometric model. -/
theorem isZero_geometricComplement_homology (hfin : K.faces.Finite)
    (hm : 2 ≤ m) (hn : 0 < n) :
    IsZero ((realSingularHomology (m * n - 1)).obj
      (TopCat.of ↥(a.geometricJoin.space \ a.geometricDeleted.space))) := by
  have hzero := isZero_simplicialBoundaryJoinComplement_homology K hfin hm hn
  exact ModuleCat.isZero_iff_subsingleton.mpr
    ((realSingularHomology_subsingleton_iff_of_homotopyEquiv
      a.geometricComplementHomeomorph.toHomotopyEquiv (m * n - 1)).mpr
        (ModuleCat.subsingleton_of_isZero hzero))

/-- The already proved local restriction theorem now applies to every carrier face of the join. -/
def geometricJoinLocalHomologyIso (hball : IsSimplicialBall n K) (hn : 2 ≤ n)
    {S : Finset (CoordinateSpace (coordinateDimension e m))}
    {x : CoordinateSpace (coordinateDimension e m)}
    (hS : S ∈ a.geometricJoin.faces) (hx : IsCarrierPoint a.geometricJoin S x)
    (k : ℕ) (hk : k ≠ 0) :
    (realSingularHomology (k + 1)).obj (TopCat.of ↥a.geometricJoin.space) ≅
      (realSingularHomology k).obj (TopCat.of ↥(closedStarLink a.geometricJoin S)) :=
  sphereHomologyIsoClosedStarLink a.geometricJoin_faces_finite hS hx
    (a.geometricJoinSphereHomeomorph hball hn) k hk

end AffineTverberg.BadEdge.BoundaryJoinVertexIndexing
