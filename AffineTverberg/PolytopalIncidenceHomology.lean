import AffineTverberg.BarycentricFaceIncidence
import AffineTverberg.SingularCohomologicalObstruction

set_option linter.style.header false

/-!
# The actual polytopal first projection is a homology equivalence

The verified good subdivision supplies barycentric coordinates on the actual
deleted join. Every deleted cell is an exposed face of the full Cayley join,
so membership in it is exactly a coordinate-support condition. The direct
open-star fiber theorem therefore applies to the actual incidence projection.
No general proper-map comparison theorem is assumed here.
-/

noncomputable section

open Set CategoryTheory HomologicalComplex

namespace AffineTverberg

namespace BadVertex

open AffineTverberg.Simplicial

variable {n : ℕ} (P : FullDimensionalPolytope n) (m : ℕ)

/-- The actual finite good subcomplex of the subdivided whole Cayley join. -/
def deletedJoinGoodComplex : Finset (Finset (Finset (JoinVertex P m))) :=
  inducedFaces (sdQ P m (topFace P m)) (goodJoinVertices P m)

theorem faceClosed_deletedJoinGoodComplex : FaceClosed (deletedJoinGoodComplex P m) :=
  faceClosed_inducedFaces (faceClosed_sdQ _) _

theorem geometricCarrier_deletedJoinGoodComplex :
    geometricCarrier (deletedJoinGoodComplex P m) (sdPoint P m) =
      polytopalDeletedJoinCarrier P m := by
  rw [deletedJoinGoodComplex, geometricCarrier_goodAssign, goodRealization_topFace]

/-- Barycentric coordinates on the actual polytopal deleted join. -/
def deletedJoinBarycentricHomeomorph :
    barycentricCarrier (deletedJoinGoodComplex P m) ≃ₜ PolytopalDeletedJoinSpace P m :=
  (geometricRealizationHomeomorph
    ((isGeometricRealization_sdQ (topFace P m)).induced (goodJoinVertices P m))).trans
      (Homeomorph.setCongr (geometricCarrier_deletedJoinGoodComplex P m))

@[simp]
theorem deletedJoinBarycentricHomeomorph_apply
    (x : barycentricCarrier (deletedJoinGoodComplex P m)) :
    (deletedJoinBarycentricHomeomorph P m x).val = barycentricEvaluation (sdPoint P m) x.val :=
  rfl

/-- The subdivision vertices lying in a particular deleted cell. -/
def deletedCellVertexSupport (C : PolytopalDeletedCellIndex P m) :
    Finset (Finset (JoinVertex P m)) := by
  classical
  exact Finset.univ.filter (fun v ↦ sdPoint P m v ∈ C.carrier)

/-- The actual cell support condition, not an additional compatibility assumption. -/
theorem deletedJoinBarycentricHomeomorph_mem_cell_iff
    (C : PolytopalDeletedCellIndex P m)
    (x : barycentricCarrier (deletedJoinGoodComplex P m)) :
    (deletedJoinBarycentricHomeomorph P m x).val ∈ C.carrier ↔
      ∀ v, v ∉ deletedCellVertexSupport P m C → x.val v = 0 := by
  classical
  have hface : IsExposed ℝ (polytopalJoinCarrier P m) C.carrier := by
    rw [CayleyJoin.cayleyJoin_cell, CayleyJoin.cayleyJoin_polytopalJoinCarrier]
    exact CayleyJoin.isExposed_cayleyJoin (fun i ↦ (C.1 i).isFace)
  have hp : ∀ v, x.val v ≠ 0 → sdPoint P m v ∈ polytopalJoinCarrier P m := by
    intro v hv
    obtain ⟨s, hs, hx⟩ := x.property.2.2
    have hvs : v ∈ s := by
      by_contra h
      exact hv (hx v h)
    apply polytopalDeletedJoinCarrier_subset_joinCarrier P
    rw [← geometricCarrier_deletedJoinGoodComplex P m]
    exact mem_iUnion₂.mpr ⟨s, hs, subset_convexHull ℝ _ ⟨v, hvs, rfl⟩⟩
  simpa [deletedCellVertexSupport] using
    (barycentricEvaluation_mem_exposed_iff (convex_convexHull ℝ _) hface
      (sdPoint P m) x.property.1 x.property.2.1 hp)

end BadVertex

namespace PolytopalJoinMap

open AffChain AffineTverberg.Simplicial BadVertex

variable {n m : ℕ} {P : FullDimensionalPolytope n}
  {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T]
  (Φ : PolytopalJoinMap P m T)

/-- **The actual first projection `X → D` is a singular homology equivalence**
under zero avoidance. Its triangulation compatibility and fiber contractions
are proved for the actual polytopal spaces, not supplied as extra hypotheses. -/
theorem quasiIso_cellIncidenceProjection
    (hzero : ∀ z ∈ polytopalDeletedJoinCarrier P m, Φ.joinMap z ≠ 0) :
    QuasiIso (singChainsMap Φ.cellIncidenceProjectionTopHom) := by
  exact quasiIso_faceIncidenceProjection_of_model
    (fun C : PolytopalDeletedCellIndex P m ↦ C.carrier) (fun z ↦ Φ.joinMap z)
    (deletedCellVertexSupport P m) (deletedJoinBarycentricHomeomorph P m)
    (deletedJoinBarycentricHomeomorph_mem_cell_iff P m)
    (faceClosed_deletedJoinGoodComplex P m) (Φ.cellIncidenceFiber_contractible hzero)

/-- The induced map on actual ordinary singular homology is an isomorphism
in every degree, including degree zero. -/
theorem isIso_cellIncidenceProjection_homology
    (hzero : ∀ z ∈ polytopalDeletedJoinCarrier P m, Φ.joinMap z ≠ 0) (k : ℕ) :
    IsIso ((realSingularHomology k).map Φ.cellIncidenceProjectionTopHom) := by
  exact (quasiIsoAt_iff_isIso_homologyMap _ _).mp
    ((quasiIso_iff _).mp (Φ.quasiIso_cellIncidenceProjection hzero) k)

/-- The polytopal zero deduction now needs only the actual sphere-projection
surjectivity. The first projection and deleted-join vanishing are discharged. -/
theorem exists_deletedJoinPoint_zero_of_singular_sphere_map
    {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m)
    {P : FullDimensionalPolytope ((d + 1) * m)}
    (Φ : PolytopalJoinMap P m (SarkariaTarget d m))
    (hYS : Function.Surjective ((realSingularHomology ((d + 1) * m - 1)).map
      Φ.topIncidenceProjectionTopHom)) :
    ∃ z : PolytopeDeletedJoinPoint (m := m) P, Φ.value z = 0 := by
  apply Φ.exists_deletedJoinPoint_zero_of_singular_homology_maps hd hm _ hYS
  intro hz
  have := Φ.isIso_cellIncidenceProjection_homology hz ((d + 1) * m - 1)
  exact (ConcreteCategory.bijective_of_isIso _).1

end PolytopalJoinMap

end AffineTverberg
