import AffineTverberg.PolytopalDeletedJoin
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.LocallyConvex.Separation

set_option linter.style.header false

/-!
# The actual polytopal boundary is a sphere

Proper exposed faces cover exactly the topological frontier of a closed
convex body. For a full-dimensional polytope this identifies the finite
boundary-face union with that frontier. A gauge homeomorphism then identifies
the polytope with a closed ball and its boundary with a sphere, compatibly
with their inclusions. No combinatorial boundary identification for an
arbitrary simplicial ball is asserted here.
-/

noncomputable section

open Set Metric

namespace AffineTverberg

section ConvexBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A F : Set E}

/-- A nonzero linear functional cannot attain a maximum at an interior point. -/
theorem notMem_interior_of_linear_max {l : E →L[ℝ] ℝ} (hl : l ≠ 0) {x : E}
    (hmax : ∀ y ∈ A, l y ≤ l x) : x ∉ interior A := by
  intro hx
  have hsub : l '' interior A ⊆ Iic (l x) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hmax y (interior_subset hy)
  have hlt := interior_maximal hsub (l.isOpenMap_of_ne_zero hl _ isOpen_interior)
    (mem_image_of_mem l hx)
  rw [interior_Iic] at hlt
  exact (lt_irrefl (l x)) hlt

theorem proper_exposed_subset_frontier (hclosed : IsClosed A)
    (hF : IsExposed ℝ A F) (hproper : F ≠ A) : F ⊆ frontier A := by
  intro x hx
  obtain ⟨l, hdef⟩ := hF ⟨x, hx⟩
  have hl : l ≠ 0 := by
    intro hz
    apply hproper
    rw [hdef]
    ext y
    simp [hz]
  have hx' : x ∈ A ∧ ∀ y ∈ A, l y ≤ l x := by rwa [hdef] at hx
  exact ⟨hclosed.closure_eq.symm ▸ hx'.1, notMem_interior_of_linear_max hl hx'.2⟩

theorem frontier_mem_proper_exposed (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hint : (interior A).Nonempty) {x : E} (hx : x ∈ frontier A) :
    ∃ F : Set E, IsExposed ℝ A F ∧ F ≠ A ∧ x ∈ F := by
  obtain ⟨l, hl, hmax⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point hconv hx.2 hint
  refine ⟨l.toExposed A, ContinuousLinearMap.toExposed.isExposed, ?_,
    hclosed.closure_eq ▸ hx.1, hmax⟩
  intro heq
  obtain ⟨y, hy⟩ := hint
  have hym : y ∈ l.toExposed A := heq.symm ▸ interior_subset hy
  exact notMem_interior_of_linear_max hl hym.2 hy

/-- The set-theoretic exposed-face boundary agrees with the topological one. -/
theorem frontier_eq_proper_exposed_union (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hint : (interior A).Nonempty) :
    frontier A = {x | ∃ F : Set E, IsExposed ℝ A F ∧ F ≠ A ∧ x ∈ F} := by
  ext x
  constructor
  · exact frontier_mem_proper_exposed hclosed hconv hint
  · rintro ⟨F, hF, hproper, hx⟩
    exact proper_exposed_subset_frontier hclosed hF hproper hx

end ConvexBoundary

namespace FullDimensionalPolytope

variable {n : ℕ} (P : FullDimensionalPolytope n)

/-- The finite union of all proper exposed faces. -/
def boundaryCarrier : Set (CoordinateSpace n) :=
  ⋃ (F : PolytopeFaceIndex P) (_ : F.carrier ≠ P.carrier), F.carrier

theorem carrier_interior_nonempty : (interior P.carrier).Nonempty := by
  have hconv : Convex ℝ P.carrier := convex_convexHull ℝ _
  apply hconv.interior_nonempty_iff_affineSpan_eq_top.mpr
  change affineSpan ℝ (convexHull ℝ (P.vertices : Set (CoordinateSpace n))) = ⊤
  rw [affineSpan_convexHull]
  exact P.affineSpan_vertices

theorem boundaryCarrier_eq_frontier : P.boundaryCarrier = frontier P.carrier := by
  have hclosed : IsClosed P.carrier :=
    (P.vertices.finite_toSet.isCompact_convexHull ℝ).isClosed
  apply Subset.antisymm
  · intro x hx
    obtain ⟨F, hproper, hx⟩ := Set.mem_iUnion₂.mp hx
    exact proper_exposed_subset_frontier hclosed F.isFace hproper hx
  · intro x hx
    obtain ⟨F, hF, hproper, hxF⟩ := frontier_mem_proper_exposed hclosed
      (convex_convexHull ℝ _) P.carrier_interior_nonempty hx
    have hFP : P.IsFace F := hF
    apply Set.mem_iUnion₂.mpr
    refine ⟨PolytopeFaceIndex.ofFace F hFP, ?_, ?_⟩
    · rwa [PolytopeFaceIndex.carrier_ofFace]
    · rwa [PolytopeFaceIndex.carrier_ofFace]

/-- One ambient homeomorphism identifies both the polytope and its actual
boundary with the closed ball and sphere, respectively. -/
theorem exists_ball_boundary_homeomorph :
    ∃ h : CoordinateSpace n ≃ₜ CoordinateSpace n,
      h '' P.carrier = closedBall 0 1 ∧ h '' P.boundaryCarrier = sphere 0 1 := by
  have hc : IsCompact P.carrier := P.vertices.finite_toSet.isCompact_convexHull ℝ
  obtain ⟨h, _, hball, hsphere⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (s := P.carrier) (convex_convexHull ℝ (P.vertices : Set (CoordinateSpace n)))
      P.carrier_interior_nonempty hc.isBounded
  exact ⟨h, by simpa only [hc.isClosed.closure_eq] using hball,
    by simpa only [P.boundaryCarrier_eq_frontier] using hsphere⟩

/-- The entire polytope is a closed ball. -/
def closedBallHomeomorph : P.carrier ≃ₜ closedBall (0 : CoordinateSpace n) 1 :=
  let h := P.exists_ball_boundary_homeomorph.choose
  (h.image P.carrier).trans (Homeomorph.setCongr
    P.exists_ball_boundary_homeomorph.choose_spec.1)

/-- The finite proper-face union is a sphere of dimension `n - 1`.
For `n = 0` both spaces are empty. -/
def boundarySphereHomeomorph : P.boundaryCarrier ≃ₜ sphere (0 : CoordinateSpace n) 1 :=
  let h := P.exists_ball_boundary_homeomorph.choose
  (h.image P.boundaryCarrier).trans (Homeomorph.setCongr
    P.exists_ball_boundary_homeomorph.choose_spec.2)

/-- Compatibility with the two boundary inclusions follows from the common
ambient homeomorphism; it is not an arbitrary pair of homeomorphisms. -/
theorem closedBall_boundarySphere_compatible (x : P.boundaryCarrier) :
    (P.closedBallHomeomorph ⟨x.1,
      (frontier_subset_closure.trans
        (P.vertices.finite_toSet.isCompact_convexHull ℝ).isClosed.closure_subset)
          (P.boundaryCarrier_eq_frontier ▸ x.2)⟩).1 =
      (P.boundarySphereHomeomorph x).1 := rfl

end FullDimensionalPolytope

end AffineTverberg
