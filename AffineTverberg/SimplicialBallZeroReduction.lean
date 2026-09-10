import AffineTverberg.SimplicialZeroReduction
import AffineTverberg.BoundaryRidgeExistence

set_option linter.style.header false

/-!
# The simplicial-ball zero theorem reduced to deleted-join homology

Boundary-ridge existence is now proved from the exact ball hypotheses.
Only the deleted-join vanishing remains as an input to the zero deduction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg

/-- The zero deduction for a simplicial ball, with boundary-ridge existence
and both incidence projection theorems discharged internally. -/
theorem exists_simplicialDeletedJoinPoint_zero_of_ball_deletedJoin_homology
    {e d m : ℕ} (hd : 1 ≤ d) (hm : 2 ≤ m)
    {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
    (hball : IsSimplicialBall ((d + 1) * m) K)
    (φ : K.space → CoordinateSpace d) (hφ : IsAffineOnSimplicialFaces K φ)
    (hD : IsZero ((realSingularHomology ((d + 1) * m - 1)).obj
      (TopCat.of (SimplicialDeletedJoinSpace ((d + 1) * m) K m)))) :
    ∃ w : SimplicialDeletedJoinPoint (n := (d + 1) * m) (m := m) K,
      SimplicialDeletedJoinPoint.sarkariaValue K w φ = 0 := by
  obtain ⟨L, hL⟩ := hball.exists_isBoundaryRidge (by nlinarith)
  exact exists_simplicialDeletedJoinPoint_zero_of_deletedJoin_homology
    hd hm hball.finite_faces φ hφ hL hD

end AffineTverberg
