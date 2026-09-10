import AffineTverberg.CohomologicalObstruction
import AffineTverberg.PolytopalCellIncidence
import AffineTverberg.PolytopalDeletedJoinRealization

set_option linter.style.header false

/-!
# The polytopal incidence diagram in cohomology

This file packages the continuous maps already constructed for the polytopal
case as morphisms of `TopCat` and applies the abstract final obstruction from
`CohomologicalObstruction.lean`.

Under zero avoidance, the paper obtains vanishing of the relevant reduced
cohomology of the actual deleted-cell incidence space `X` from the deleted join, while
Leray--Vietoris--Begle makes the pullback along `Y → S` injective.  The theorem
below verifies that these two conclusions are formally contradictory because
the projection `Y → S` factors through `X`.
-/

noncomputable section

open CategoryTheory

namespace AffineTverberg
namespace PolytopalJoinMap

variable {n m : ℕ} {P : FullDimensionalPolytope n}
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (Φ : PolytopalJoinMap P m V)

/-- The first projection of the actual cell-incidence space as a morphism of
topological spaces. -/
def cellIncidenceProjectionTopHom :
    TopCat.of Φ.DeletedCellIncidenceSpace ⟶
      TopCat.of (PolytopalDeletedJoinSpace P m) :=
  TopCat.ofHom
    ⟨faceIncidenceProjection,
      continuous_faceIncidenceProjection⟩

/-- The second projection of the actual cell-incidence space as a morphism of
topological spaces. -/
def cellIncidenceDualTopHom :
    TopCat.of Φ.DeletedCellIncidenceSpace ⟶ TopCat.of (DualUnitSphere V) :=
  TopCat.ofHom
    ⟨Φ.cellIncidenceDual,
      Φ.cellIncidenceDual_continuous⟩

/-- The inclusion of the top-locus incidence space `Y` into the paper's
actual cell-incidence space `X`, as a morphism of topological spaces. -/
def topIncidenceToCellIncidenceTopHom :
    TopCat.of Φ.TopIncidenceSpace ⟶ TopCat.of Φ.DeletedCellIncidenceSpace :=
  TopCat.ofHom
    ⟨Φ.topIncidenceToCellIncidence,
      Φ.topIncidenceToCellIncidence_continuous⟩

/-- The projection `Y → S(V*)` as a morphism of topological spaces. -/
def topIncidenceProjectionTopHom :
    TopCat.of Φ.TopIncidenceSpace ⟶ TopCat.of (DualUnitSphere V) :=
  TopCat.ofHom ⟨Φ.topIncidenceProjection, Φ.topIncidenceProjection_continuous⟩

/-- The key commutative triangle from the end of the proof:
`pr_Y = (Y → X) ≫ pr_X`. -/
theorem topIncidenceProjectionTopHom_eq_comp :
    Φ.topIncidenceProjectionTopHom =
      Φ.topIncidenceToCellIncidenceTopHom ≫
        Φ.cellIncidenceDualTopHom := by
  ext p
  rfl

universe u

/-- The paper's final contradiction, specialized to the actual polytopal
incidence diagram.  This is ready to receive the two remaining topological
inputs: nontrivial sphere cohomology, vanishing cohomology of `X`, and the
fiber theorem giving injectivity for `Y → S`. -/
theorem not_injective_topIncidenceProjection_pullback
    {𝕜 : Type u} [Ring 𝕜]
    (H : TopCatᵒᵖ ⥤ ModuleCat 𝕜)
    [Nontrivial (H.obj (Opposite.op (TopCat.of (DualUnitSphere V))))]
    [Subsingleton
      (H.obj (Opposite.op (TopCat.of Φ.DeletedCellIncidenceSpace)))] :
    ¬ Function.Injective (H.map Φ.topIncidenceProjectionTopHom.op) := by
  rw [Φ.topIncidenceProjectionTopHom_eq_comp]
  exact cohomological_obstruction H
    Φ.topIncidenceToCellIncidenceTopHom
    Φ.cellIncidenceDualTopHom

/-- Explicit false-elimination form of the final contradiction. -/
theorem false_of_injective_topIncidenceProjection_pullback
    {𝕜 : Type u} [Ring 𝕜]
    (H : TopCatᵒᵖ ⥤ ModuleCat 𝕜)
    [Nontrivial (H.obj (Opposite.op (TopCat.of (DualUnitSphere V))))]
    [Subsingleton
      (H.obj (Opposite.op (TopCat.of Φ.DeletedCellIncidenceSpace)))]
    (hinjective : Function.Injective
      (H.map Φ.topIncidenceProjectionTopHom.op)) : False :=
  Φ.not_injective_topIncidenceProjection_pullback H hinjective

/-- The complete final diagram chase in the form used verbatim by the paper.
If reduced cohomology of the deleted join vanishes, the first projection
`X → D` induces a surjection (in the application, an isomorphism by the
acyclic-fiber part of Leray--Vietoris--Begle), and `Y → S` induces an
injection, then the nonzero sphere class gives a contradiction. -/
theorem false_of_deletedJoin_vanishing_and_lerayVietorisBegle
    {𝕜 : Type u} [Ring 𝕜]
    (H : TopCatᵒᵖ ⥤ ModuleCat 𝕜)
    [Nontrivial (H.obj (Opposite.op (TopCat.of (DualUnitSphere V))))]
    (hD : Subsingleton
      (H.obj (Opposite.op (TopCat.of (PolytopalDeletedJoinSpace P m)))))
    (hXD : Function.Surjective
      (H.map Φ.cellIncidenceProjectionTopHom.op))
    (hYS : Function.Injective
      (H.map Φ.topIncidenceProjectionTopHom.op)) : False := by
  let _ : Subsingleton
      (H.obj (Opposite.op (TopCat.of (PolytopalDeletedJoinSpace P m)))) := hD
  let _ : Subsingleton
      (H.obj (Opposite.op (TopCat.of Φ.DeletedCellIncidenceSpace))) :=
    ⟨fun a b ↦ by
      obtain ⟨a', rfl⟩ := hXD a
      obtain ⟨b', rfl⟩ := hXD b
      exact congrArg (H.map Φ.cellIncidenceProjectionTopHom.op)
        (Subsingleton.elim a' b')⟩
  exact Φ.false_of_injective_topIncidenceProjection_pullback H hYS

/-- Zero-existence form of the preceding contradiction.  It exposes exactly
the three topological conclusions still to be supplied in degree `N - 1`:
deleted-join vanishing, the surjective pullback for `X → D`, and the injective
pullback for `Y → S`. -/
theorem exists_zero_on_deletedJoin_of_cohomological_inputs
    {𝕜 : Type u} [Ring 𝕜]
    (H : TopCatᵒᵖ ⥤ ModuleCat 𝕜)
    [Nontrivial (H.obj (Opposite.op (TopCat.of (DualUnitSphere V))))]
    (hD : Subsingleton
      (H.obj (Opposite.op (TopCat.of (PolytopalDeletedJoinSpace P m)))))
    (hXD : (∀ z ∈ polytopalDeletedJoinCarrier P m, Φ.joinMap z ≠ 0) →
      Function.Surjective (H.map Φ.cellIncidenceProjectionTopHom.op))
    (hYS : Function.Injective
      (H.map Φ.topIncidenceProjectionTopHom.op)) :
    ∃ z ∈ polytopalDeletedJoinCarrier P m, Φ.joinMap z = 0 := by
  by_contra hzero
  push Not at hzero
  exact Φ.false_of_deletedJoin_vanishing_and_lerayVietorisBegle
    H hD (hXD hzero) hYS

/-- Witness-level version, matching the conclusion of
`polytopalZeroTheoremStatement`. -/
theorem exists_deletedJoinPoint_zero_of_cohomological_inputs
    {𝕜 : Type u} [Ring 𝕜]
    (H : TopCatᵒᵖ ⥤ ModuleCat 𝕜)
    [Nontrivial (H.obj (Opposite.op (TopCat.of (DualUnitSphere V))))]
    (hD : Subsingleton
      (H.obj (Opposite.op (TopCat.of (PolytopalDeletedJoinSpace P m)))))
    (hXD : (∀ z ∈ polytopalDeletedJoinCarrier P m, Φ.joinMap z ≠ 0) →
      Function.Surjective (H.map Φ.cellIncidenceProjectionTopHom.op))
    (hYS : Function.Injective
      (H.map Φ.topIncidenceProjectionTopHom.op)) :
    ∃ z : PolytopeDeletedJoinPoint (m := m) P, Φ.value z = 0 := by
  obtain ⟨w, hwD, hw0⟩ :=
    Φ.exists_zero_on_deletedJoin_of_cohomological_inputs H hD hXD hYS
  exact Φ.exists_value_eq_zero_of_joinMap_eq_zero hwD hw0

end PolytopalJoinMap
end AffineTverberg
