import AffineTverberg.BoundaryIdentification
import AffineTverberg.DeletedJoinDualityReduction
import AffineTverberg.GeometricRelativeHomologyComparison

set_option linter.style.header false

/-!
# The actual boundary-join/deleted-join pair as a finite simplicial sphere pair

The already constructed bad-edge subdivision simultaneously triangulates the
boundary join and its deleted join. Here all indexing hypotheses are discharged
and the actual relative comparison is applied to this concrete pair. Thus a
duality theorem for a finite geometric simplicial sphere and subcomplex can be
used directly; no general triangulation theorem for arbitrary polyhedra is
needed. This file does not assume or claim Alexander duality.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric

namespace AffineTverberg.BadEdge.BoundaryJoinVertexIndexing

open AffineTverberg.Simplicial AffineTverberg.AffChain

variable {e n m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
  (a : BoundaryJoinVertexIndexing n K m)

/-- The existing subdivision, with every colored vertex explicitly indexed. -/
def joinComplex : Finset (Finset (Finset (Fin a.size))) :=
  sdJoinFaces n K a.factor a.vertex

/-- The good induced subcomplex, which realizes the actual deleted join. -/
def deletedComplex : Finset (Finset (Finset (Fin a.size))) :=
  inducedFaces a.joinComplex (goodSdVertices (Fin a.size))

/-- The actual Cayley vertices and inserted bad-edge midpoints. -/
def realizationPoints : Finset (Fin a.size) → PolytopalJoinAmbient e m :=
  sdPt (cayleyPt a.factor a.vertex)

theorem faceClosed_joinComplex : FaceClosed a.joinComplex :=
  faceClosed_sdJoinFaces a.factor a.vertex

theorem faceClosed_deletedComplex : FaceClosed a.deletedComplex :=
  faceClosed_inducedFaces a.faceClosed_joinComplex _

theorem deletedComplex_subset : a.deletedComplex ⊆ a.joinComplex :=
  fun _ hs => (mem_inducedFaces.mp hs).1

theorem isGeometricRealization_joinComplex :
    IsGeometricRealization a.joinComplex a.realizationPoints :=
  isGeometricRealization_sdJoinFaces a.factor a.vertex a.injective

theorem geometricCarrier_joinComplex :
    geometricCarrier a.joinComplex a.realizationPoints = simplicialBoundaryJoinCarrier K n m :=
  (geometricCarrier_sdJoinFaces a.factor a.vertex).trans
    (iUnion_joinFactor_eq_boundaryJoin K a.factor a.vertex a.covers)

theorem geometricCarrier_deletedComplex :
    geometricCarrier a.deletedComplex a.realizationPoints = simplicialDeletedJoinCarrier n K m :=
  geometricCarrier_good_sdJoinFaces a.factor a.vertex a.injective a.covers

/-- Every simplex has at most the number of vertices in a full ridge join. -/
theorem card_joinComplex_le {σ : Finset (Finset (Fin a.size))} (hσ : σ ∈ a.joinComplex) :
    σ.card ≤ (m + 1) * n := by
  obtain ⟨S, hS, hσS⟩ := (mem_sdJoinFaces a.factor a.vertex).mp hσ
  calc
    σ.card ≤ S.card := sdFaces_card_le a.vertex S hσS
    _ = ∑ i, (joinFactor a.factor a.vertex S i).card :=
      card_eq_sum_card_joinFactor a.factor a.vertex a.injective S
    _ ≤ ∑ _i : Fin (m + 1), n := by
      apply Finset.sum_le_sum
      intro i _
      rcases hS i with hemp | hface
      · simp [hemp]
      · obtain ⟨R, hR, hsub⟩ := hface.2
        exact (Finset.card_le_card hsub).trans hR.2.1.le
    _ = (m + 1) * n := by simp

/-- Every simplex extends to the full paper dimension, from the actual
boundary-ridge existence theorem and the existing subdivision purity. -/
theorem exists_top_simplex_extension (hball : IsSimplicialBall n K) (hn : 2 ≤ n)
    {σ : Finset (Finset (Fin a.size))} (hσ : σ ∈ a.joinComplex) :
    ∃ τ ∈ a.joinComplex, σ ⊆ τ ∧ τ.card = (m + 1) * n := by
  obtain ⟨S, hS, hσS⟩ := (mem_sdJoinFaces a.factor a.vertex).mp hσ
  obtain ⟨T, hT, hST⟩ := exists_ridgeJoinFace_extension a.factor a.vertex a.covers
    (hball.exists_isBoundaryRidge hn) hS
  have hσT : σ ∈ sdFaces a.vertex T := sdFaces_mono a.vertex hST hσS
  obtain ⟨τ, hτ, hστ, hcard⟩ := exists_full_simplex_extension a.vertex T hσT
  refine ⟨τ, (mem_sdJoinFaces a.factor a.vertex).mpr
    ⟨T, isJoinFace_of_mem_ridgeJoinFaces a.factor a.vertex hT, hτ⟩, hστ, ?_⟩
  exact hcard.trans (card_ridgeJoinFace a.factor a.vertex a.injective hT)

/-- All maximal simplices of the constructed sphere have the expected dimension. -/
theorem card_maximal_joinComplex (hball : IsSimplicialBall n K) (hn : 2 ≤ n)
    {σ : Finset (Finset (Fin a.size))} (hσ : σ ∈ a.joinComplex)
    (hmax : ∀ τ ∈ a.joinComplex, σ ⊆ τ → τ = σ) : σ.card = (m + 1) * n := by
  obtain ⟨τ, hτ, hστ, hcard⟩ := a.exists_top_simplex_extension hball hn hσ
  rwa [hmax τ hτ hστ] at hcard

/-- The subdivision's barycentric realization is the actual boundary join. -/
def joinBarycentricHomeomorph :
    ↥(barycentricCarrier a.joinComplex) ≃ₜ ↥(simplicialBoundaryJoinCarrier K n m) :=
  (geometricRealizationHomeomorph a.isGeometricRealization_joinComplex).trans
    (Homeomorph.setCongr a.geometricCarrier_joinComplex)

/-- The good subcomplex's barycentric realization is the actual deleted join. -/
def deletedBarycentricHomeomorph :
    ↥(barycentricCarrier a.deletedComplex) ≃ₜ ↥(simplicialDeletedJoinCarrier n K m) :=
  (geometricRealizationHomeomorph
    (a.isGeometricRealization_joinComplex.mono a.deletedComplex_subset)).trans
    (Homeomorph.setCongr a.geometricCarrier_deletedComplex)

/-- The exact sphere presentation for the triangulated ambient complex. -/
def joinBarycentricSphereHomeomorph (hball : IsSimplicialBall n K) (hn : 2 ≤ n) :
    ↥(barycentricCarrier a.joinComplex) ≃ₜ sphere (0 : CoordinateSpace ((m + 1) * n)) 1 :=
  a.joinBarycentricHomeomorph.trans (hball.fullBoundaryJoinHomeomorphSphere hn m)

/-- The affine realization identifies the literal subcomplex with the
deleted join as a subset of the boundary join. -/
theorem joinGeometricHomeomorph_mem_deleted
    (x : ↥(geometricCarrier a.joinComplex a.realizationPoints)) :
    x ∈ geometricSubcomplexRealization a.deletedComplex a.joinComplex a.realizationPoints ↔
      Homeomorph.setCongr a.geometricCarrier_joinComplex x ∈ deletedJoinInBoundaryJoin K n m := by
  change x.val ∈ geometricCarrier a.deletedComplex a.realizationPoints ↔
    x.val ∈ simplicialDeletedJoinCarrier n K m
  rw [a.geometricCarrier_deletedComplex]

/-- The actual relative singular pair agrees with the geometric model pair. -/
def geometricRelativeHomologyIso (k : ℕ) :
    relativeHomology (X := TopCat.of ↥(geometricCarrier a.joinComplex a.realizationPoints))
      (geometricSubcomplexRealization a.deletedComplex a.joinComplex a.realizationPoints) k ≅
      relativeHomology (deletedJoinInBoundaryJoin K n m) k :=
  relativeHomologyIsoOfHomeomorph
    (X := TopCat.of ↥(geometricCarrier a.joinComplex a.realizationPoints))
    (Y := boundaryJoinSpace K n m) (Homeomorph.setCongr a.geometricCarrier_joinComplex)
    a.joinGeometricHomeomorph_mem_deleted k

/-- The full relative comparison for the specific pair in the paper, with
all indexing and geometric hypotheses discharged. -/
def relativeSimplicialHomologyIso (k : ℕ) :
    letI := a.subdivisionOrder
    (simplicialRelativeCx a.faceClosed_deletedComplex a.faceClosed_joinComplex
      a.deletedComplex_subset).homology k ≅
      relativeHomology (deletedJoinInBoundaryJoin K n m) k := by
  letI := a.subdivisionOrder
  letI : DecidableEq (Finset (Fin a.size)) := a.subdivisionOrder.toDecidableEq
  have hgeom : IsGeometricRealization a.joinComplex a.realizationPoints := by
    convert a.isGeometricRealization_joinComplex using 1
  exact geometricRelativeComparisonHomologyIso a.faceClosed_deletedComplex
    a.faceClosed_joinComplex a.deletedComplex_subset hgeom k ≪≫
    a.geometricRelativeHomologyIso k

end AffineTverberg.BadEdge.BoundaryJoinVertexIndexing
