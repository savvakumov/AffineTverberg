import AffineTverberg.HomologyBoundary
import AffineTverberg.BoundaryJoinSphere

set_option linter.style.header false

/-!
# The boundary-sphere deduction from boundary identification

`AffineTverberg.HomologyBoundary` proves, from the bare hypotheses of
`IsSimplicialBall n K` and `2 ≤ n`, that the *homologically detected* boundary
of the polyhedron,

`homologyBoundary ↥K.space (n - 1) = {p | H_{n-1}(K.space \ {p}) = 0}`,

is homeomorphic to the unit `(n-1)`-sphere.  `AffineTverberg.BoundaryJoinSphere`
turns a homeomorphism of the *combinatorial* boundary carrier with that sphere
into the join-of-spheres homeomorphism.

The identification required between the two is
identification of the two boundaries,

`Subtype.val ⁻¹' (simplicialBoundaryCarrier K n) = homologyBoundary ↥K.space (n - 1)`,

i.e. that a point of the polyhedron has vanishing punctured homology in degree
`n - 1` exactly when it lies in a face contained in a boundary ridge. It is
now proved in `BoundaryIdentification.lean` using the mod-two top cycle of
the actual closed-star link and the existing local geometry.

This file records what that identification implies: the boundary sphere,
the existence of a boundary ridge,
and the join-of-spheres identification of the full boundary join.  Every
statement here carries the identification as an explicit hypothesis; nothing is
assumed silently.
-/

noncomputable section

open Metric Set

namespace AffineTverberg

variable {e n : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-- The identification of the combinatorial boundary carrier with the homology
boundary yields the boundary sphere. -/
def boundaryCarrierHomeomorphSphere (hball : IsSimplicialBall n K) (hn : 2 ≤ n)
    (hEq : Subtype.val ⁻¹' (simplicialBoundaryCarrier K n) =
      homologyBoundary ↥K.space (n - 1)) :
    ↥(simplicialBoundaryCarrier K n) ≃ₜ ↥(sphere (0 : CoordinateSpace n) 1) :=
  (subsetSubtypeHomeomorph (T := K.space) (simplicialBoundaryCarrier_subset_space K)).symm.trans
    ((Homeomorph.setCongr hEq).trans (hball.homologyBoundaryHomeomorphSphere hn))

/-- With the identification, a simplicial ball has a boundary ridge. -/
theorem exists_isBoundaryRidge_of_boundary_eq (hball : IsSimplicialBall n K) (hn : 2 ≤ n)
    (hEq : Subtype.val ⁻¹' (simplicialBoundaryCarrier K n) =
      homologyBoundary ↥K.space (n - 1)) :
    ∃ L, IsBoundaryRidge n K L := by
  have hne : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨s, hs⟩ := (NormedSpace.sphere_nonempty (E := CoordinateSpace n) (x := 0)
    (r := 1)).mpr zero_le_one
  let p := (boundaryCarrierHomeomorphSphere hball hn hEq).symm ⟨s, hs⟩
  exact (simplicialBoundaryCarrier_nonempty_iff K (by omega)).mp ⟨p.1, p.2⟩

/-- With the identification, the actual boundary join of a simplicial ball is a
sphere of the expected dimension. -/
def boundaryJoinHomeomorphSphere (hball : IsSimplicialBall n K) (hn : 2 ≤ n)
    (hEq : Subtype.val ⁻¹' (simplicialBoundaryCarrier K n) =
      homologyBoundary ↥K.space (n - 1)) (m : ℕ) :
    ↥(simplicialBoundaryJoinCarrier K n m) ≃ₜ
      ↥(sphere (0 : CoordinateSpace ((m + 1) * n)) 1) :=
  boundaryJoinCoordinateSphereHomeomorph (boundaryCarrierHomeomorphSphere hball hn hEq)
    hball.finite_faces (by omega) m

end AffineTverberg
