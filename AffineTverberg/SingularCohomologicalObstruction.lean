import AffineTverberg.SingularCohomologyDuality
import AffineTverberg.PolytopalCohomologicalObstruction
import AffineTverberg.SimplicialCohomologicalObstruction
import AffineTverberg.PolytopalCellGluing

set_option linter.style.header false

/-!
# The main obstruction with a concrete cohomology theory

The sphere-class input is now discharged for actual real singular cochains.
The remaining assumptions are explicitly the deleted-join homology vanishing
and the two proper-map pullback conclusions. This does not assert those
conclusions from fiber acyclicity alone; their topological hypotheses and
proofs still have to be supplied.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg

namespace PolytopalJoinMap

/-- The precise ordinary singular homology degree needed by the obstruction
vanishes on the actual polytopal deleted join. -/
theorem isZero_deletedJoin_sarkariaHomology
    {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m)
    (P : FullDimensionalPolytope ((d + 1) * m)) :
    IsZero ((realSingularHomology ((d + 1) * m - 1)).obj
      (TopCat.of (PolytopalDeletedJoinSpace P m))) := by
  have hN : 2 ≤ (d + 1) * m := by nlinarith
  exact (BadVertex.singular_acyclicity_polytopalDeletedJoin (P := P) (m := m)).2.2
    _ (by omega) (by omega)

/-- The polytopal zero deduction for actual singular cohomology, with the
nonzero sphere class proved and deleted-join vanishing supplied as homology. -/
theorem exists_deletedJoinPoint_zero_of_singular_inputs
    {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m)
    {P : FullDimensionalPolytope ((d + 1) * m)}
    (Φ : PolytopalJoinMap P m (SarkariaTarget d m))
    (hD : IsZero ((realSingularHomology ((d + 1) * m - 1)).obj
      (TopCat.of (PolytopalDeletedJoinSpace P m))))
    (hXD : (∀ z ∈ polytopalDeletedJoinCarrier P m, Φ.joinMap z ≠ 0) →
      Function.Surjective ((realSingularCohomology ((d + 1) * m - 1)).map
        Φ.cellIncidenceProjectionTopHom.op))
    (hYS : Function.Injective ((realSingularCohomology ((d + 1) * m - 1)).map
      Φ.topIncidenceProjectionTopHom.op)) :
    ∃ z : PolytopeDeletedJoinPoint (m := m) P, Φ.value z = 0 := by
  have hn := nontrivial_sarkariaDualSphereCohomology hd hm
  exact Φ.exists_deletedJoinPoint_zero_of_cohomological_inputs
    (realSingularCohomology ((d + 1) * m - 1))
    (ModuleCat.isZero_iff_subsingleton.mp
      ((isZero_realSingularCohomology_iff _ _).mpr hD)) hXD hYS

/-- For the polytopal case, the only remaining inputs are the two actual
proper-map pullback conclusions. Both the deleted-join vanishing and the
nonzero sphere cohomology have been proved. -/
theorem exists_deletedJoinPoint_zero_of_singular_pullbacks
    {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m)
    {P : FullDimensionalPolytope ((d + 1) * m)}
    (Φ : PolytopalJoinMap P m (SarkariaTarget d m))
    (hXD : (∀ z ∈ polytopalDeletedJoinCarrier P m, Φ.joinMap z ≠ 0) →
      Function.Surjective ((realSingularCohomology ((d + 1) * m - 1)).map
        Φ.cellIncidenceProjectionTopHom.op))
    (hYS : Function.Injective ((realSingularCohomology ((d + 1) * m - 1)).map
      Φ.topIncidenceProjectionTopHom.op)) :
    ∃ z : PolytopeDeletedJoinPoint (m := m) P, Φ.value z = 0 :=
  Φ.exists_deletedJoinPoint_zero_of_singular_inputs hd hm
    (isZero_deletedJoin_sarkariaHomology hd hm P) hXD hYS

/-- The remaining polytopal proper-map obligations can equivalently be
supplied on actual singular homology, with the variance proved by natural
field duality. -/
theorem exists_deletedJoinPoint_zero_of_singular_homology_maps
    {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m)
    {P : FullDimensionalPolytope ((d + 1) * m)}
    (Φ : PolytopalJoinMap P m (SarkariaTarget d m))
    (hXD : (∀ z ∈ polytopalDeletedJoinCarrier P m, Φ.joinMap z ≠ 0) →
      Function.Injective ((realSingularHomology ((d + 1) * m - 1)).map
        Φ.cellIncidenceProjectionTopHom))
    (hYS : Function.Surjective ((realSingularHomology ((d + 1) * m - 1)).map
      Φ.topIncidenceProjectionTopHom)) :
    ∃ z : PolytopeDeletedJoinPoint (m := m) P, Φ.value z = 0 :=
  Φ.exists_deletedJoinPoint_zero_of_singular_pullbacks hd hm
    (fun hz ↦ (realSingularCohomology_map_surjective_iff _ _).mpr (hXD hz))
    ((realSingularCohomology_map_injective_iff _ _).mpr hYS)

end PolytopalJoinMap

/-- The simplicial zero deduction on the actual global map, using the same
concrete cochain functor. The intended ball application has `m ≥ 2`. -/
theorem exists_simplicialDeletedJoinPoint_zero_of_singular_inputs
    {e d m : ℕ} (hd : 1 ≤ d) (hm : 2 ≤ m)
    {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
    {L : Finset (CoordinateSpace e)}
    (φ : K.space → CoordinateSpace d) (hφ : IsAffineOnSimplicialFaces K φ)
    (ψ : CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d)
    (hψ : ∀ y : K.space,
      y.val ∈ convexHull ℝ (L : Set (CoordinateSpace e)) → φ y = ψ y.val)
    (hL : IsBoundaryRidge ((d + 1) * m) K L)
    (hD : IsZero ((realSingularHomology ((d + 1) * m - 1)).obj
      (TopCat.of (SimplicialDeletedJoinSpace ((d + 1) * m) K m))))
    (hXD : (∀ z : SimplicialDeletedJoinSpace ((d + 1) * m) K m,
      simplicialGlobalSarkariaMap φ z ≠ 0) →
      Function.Surjective ((realSingularCohomology ((d + 1) * m - 1)).map
        (simplicialCellIncidenceProjectionTopHom
          (n := (d + 1) * m) (m := m) φ).op))
    (hYS : Function.Injective ((realSingularCohomology ((d + 1) * m - 1)).map
      (ridgeIncidenceDualProjectionTopHom (L := L) (m := m) ψ).op)) :
    ∃ w : SimplicialDeletedJoinPoint (n := (d + 1) * m) (m := m) K,
      SimplicialDeletedJoinPoint.sarkariaValue K w φ = 0 := by
  have hn := nontrivial_sarkariaDualSphereCohomology hd (show 1 ≤ m by omega)
  exact exists_simplicialDeletedJoinPoint_zero_of_cohomological_inputs
    φ hφ ψ hψ hL (realSingularCohomology ((d + 1) * m - 1))
    (ModuleCat.isZero_iff_subsingleton.mp
      ((isZero_realSingularCohomology_iff _ _).mpr hD)) hXD hYS

end AffineTverberg
