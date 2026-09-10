import AffineTverberg.SimplicialIncidenceHomology
import AffineTverberg.RidgeIncidenceHomology
import AffineTverberg.SingularCohomologicalObstruction

set_option linter.style.header false

/-!
# Simplicial zero deduction with both projection theorems discharged

For a finite geometric complex with a boundary ridge, the actual incidence
maps now supply the homological obstruction. The only remaining homological
input is vanishing in degree `N - 1` of the actual deleted join. In the ball
application this is the paper's Alexander-duality argument. Existence of a
boundary ridge for the general topological-ball definition remains part of
that geometric/topological application, not an assumption hidden here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg

/-- The actual simplicial zero theorem reduced to deleted-join vanishing
and a boundary ridge. Both incidence-map conclusions are proved internally. -/
theorem exists_simplicialDeletedJoinPoint_zero_of_deletedJoin_homology
    {e d m : ℕ} (hd : 1 ≤ d) (hm : 2 ≤ m)
    {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
    (hfin : K.faces.Finite) (φ : K.space → CoordinateSpace d)
    (hφ : IsAffineOnSimplicialFaces K φ)
    {L : Finset (CoordinateSpace e)} (hL : IsBoundaryRidge ((d + 1) * m) K L)
    (hD : IsZero ((realSingularHomology ((d + 1) * m - 1)).obj
      (TopCat.of (SimplicialDeletedJoinSpace ((d + 1) * m) K m)))) :
    ∃ w : SimplicialDeletedJoinPoint (n := (d + 1) * m) (m := m) K,
      SimplicialDeletedJoinPoint.sarkariaValue K w φ = 0 := by
  obtain ⟨ψ, hψ⟩ := exists_ridge_affine_extension hφ hL
  apply exists_simplicialDeletedJoinPoint_zero_of_singular_inputs hd hm φ hφ ψ hψ hL hD
  · intro hz
    apply (realSingularCohomology_map_surjective_iff _ _).mpr
    have := isIso_simplicialCellIncidenceProjection_homology φ hfin hφ hz ((d + 1) * m - 1)
    exact (ConcreteCategory.bijective_of_isIso _).1
  · apply (realSingularCohomology_map_injective_iff _ _).mpr
    have hcard : 2 ≤ L.card := by
      rw [hL.2.1]
      nlinarith
    have hsurj :=
      surjective_ridgeIncidenceProjection_homology (m := m) L ψ (K.indep hL.1) hcard
    rw [hL.2.1] at hsurj
    exact hsurj

end AffineTverberg
