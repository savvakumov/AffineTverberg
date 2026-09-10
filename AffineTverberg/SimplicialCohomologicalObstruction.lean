import AffineTverberg.CohomologicalObstruction
import AffineTverberg.SimplicialCellIncidence

set_option linter.style.header false

/-!
# The simplicial-ball incidence diagram in cohomology

This file packages the actual piecewise-affine simplicial Sarkaria map and its
cell incidence space as morphisms of `TopCat`.  It then performs the final
diagram chase: deleted-join cohomology vanishing, the acyclic-fiber conclusion
for `X → D`, and injectivity for the ridge projection `Y → S` force a zero of
the global Sarkaria map and hence a witness for the simplicial zero theorem.
-/

noncomputable section

open CategoryTheory

namespace AffineTverberg

variable {e n d m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
  {L : Finset (CoordinateSpace e)}

/-- The first projection `X → D` for the actual simplicial cell-incidence
space. -/
def simplicialCellIncidenceProjectionTopHom
    (φ : K.space → CoordinateSpace d) :
    TopCat.of (SimplicialDeletedCellIncidenceSpace (n := n) (m := m) φ) ⟶
      TopCat.of (SimplicialDeletedJoinSpace n K m) :=
  TopCat.ofHom ⟨faceIncidenceProjection, continuous_faceIncidenceProjection⟩

/-- The second projection `X → S`. -/
def simplicialCellIncidenceDualTopHom
    (φ : K.space → CoordinateSpace d) :
    TopCat.of (SimplicialDeletedCellIncidenceSpace (n := n) (m := m) φ) ⟶
      TopCat.of (DualUnitSphere (SarkariaTarget d m)) :=
  TopCat.ofHom
    ⟨simplicialCellIncidenceDual φ,
      continuous_simplicialCellIncidenceDual φ⟩

/-- The ridge inclusion `Y → X` as a morphism of topological spaces. -/
def ridgeToSimplicialCellIncidenceTopHom
    (φ : K.space → CoordinateSpace d)
    (ψ : CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d)
    (hψ : ∀ y : K.space,
      y.val ∈ convexHull ℝ (L : Set (CoordinateSpace e)) → φ y = ψ y.val)
    (hL : IsBoundaryRidge n K L) :
    TopCat.of (RidgeIncidenceSpace L
      (simplicialSarkariaMap (m := m) fun _ : Fin (m + 1) ↦ ψ)) ⟶
      TopCat.of (SimplicialDeletedCellIncidenceSpace (n := n) (m := m) φ) :=
  TopCat.ofHom
    ⟨ridgeToSimplicialCellIncidence φ ψ hψ hL,
      continuous_ridgeToSimplicialCellIncidence φ ψ hψ hL⟩

/-- The ridge projection `Y → S`. -/
def ridgeIncidenceDualProjectionTopHom
    (ψ : CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d) :
    TopCat.of (RidgeIncidenceSpace L
      (simplicialSarkariaMap (m := m) fun _ : Fin (m + 1) ↦ ψ)) ⟶
      TopCat.of (DualUnitSphere (SarkariaTarget d m)) :=
  TopCat.ofHom
    ⟨ridgeIncidenceDualProjection L
        (simplicialSarkariaMap (m := m) fun _ : Fin (m + 1) ↦ ψ),
      continuous_ridgeIncidenceDualProjection L
        (simplicialSarkariaMap (m := m) fun _ : Fin (m + 1) ↦ ψ)⟩

/-- The commutative triangle `pr_Y = (Y → X) ≫ pr_X`. -/
theorem ridgeIncidenceDualProjectionTopHom_eq_comp
    (φ : K.space → CoordinateSpace d)
    (ψ : CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d)
    (hψ : ∀ y : K.space,
      y.val ∈ convexHull ℝ (L : Set (CoordinateSpace e)) → φ y = ψ y.val)
    (hL : IsBoundaryRidge n K L) :
    ridgeIncidenceDualProjectionTopHom (L := L) (m := m) ψ =
      ridgeToSimplicialCellIncidenceTopHom φ ψ hψ hL ≫
        simplicialCellIncidenceDualTopHom φ := by
  ext p
  rfl

universe u

/-- The final cohomological contradiction for the actual simplicial
incidence diagram. -/
theorem false_of_simplicial_deletedJoin_vanishing_and_lerayVietorisBegle
    {𝕜 : Type u} [Ring 𝕜]
    (φ : K.space → CoordinateSpace d)
    (ψ : CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d)
    (hψ : ∀ y : K.space,
      y.val ∈ convexHull ℝ (L : Set (CoordinateSpace e)) → φ y = ψ y.val)
    (hL : IsBoundaryRidge n K L)
    (H : TopCatᵒᵖ ⥤ ModuleCat 𝕜)
    [Nontrivial
      (H.obj (Opposite.op (TopCat.of (DualUnitSphere (SarkariaTarget d m)))))]
    (hD : Subsingleton
      (H.obj (Opposite.op (TopCat.of (SimplicialDeletedJoinSpace n K m)))))
    (hXD : Function.Surjective
      (H.map (simplicialCellIncidenceProjectionTopHom
        (n := n) (m := m) φ).op))
    (hYS : Function.Injective
      (H.map (ridgeIncidenceDualProjectionTopHom (L := L) (m := m) ψ).op)) :
    False := by
  let _ : Subsingleton
      (H.obj (Opposite.op (TopCat.of (SimplicialDeletedJoinSpace n K m)))) := hD
  let _ : Subsingleton
      (H.obj (Opposite.op (TopCat.of
        (SimplicialDeletedCellIncidenceSpace (n := n) (m := m) φ)))) :=
    ⟨fun a b ↦ by
      obtain ⟨a', rfl⟩ := hXD a
      obtain ⟨b', rfl⟩ := hXD b
      exact congrArg (H.map (simplicialCellIncidenceProjectionTopHom
        (n := n) (m := m) φ).op)
        (Subsingleton.elim a' b')⟩
  rw [ridgeIncidenceDualProjectionTopHom_eq_comp φ ψ hψ hL] at hYS
  exact cohomological_obstruction H
    (ridgeToSimplicialCellIncidenceTopHom (m := m) φ ψ hψ hL)
    (simplicialCellIncidenceDualTopHom (n := n) (m := m) φ) hYS

/-- Zero-existence form, exposing the three substantive cohomological inputs
which remain to be supplied in the target degree. -/
theorem exists_zero_on_simplicialDeletedJoin_of_cohomological_inputs
    {𝕜 : Type u} [Ring 𝕜]
    (φ : K.space → CoordinateSpace d)
    (ψ : CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d)
    (hψ : ∀ y : K.space,
      y.val ∈ convexHull ℝ (L : Set (CoordinateSpace e)) → φ y = ψ y.val)
    (hL : IsBoundaryRidge n K L)
    (H : TopCatᵒᵖ ⥤ ModuleCat 𝕜)
    [Nontrivial
      (H.obj (Opposite.op (TopCat.of (DualUnitSphere (SarkariaTarget d m)))))]
    (hD : Subsingleton
      (H.obj (Opposite.op (TopCat.of (SimplicialDeletedJoinSpace n K m)))))
    (hXD : (∀ z : SimplicialDeletedJoinSpace n K m,
      simplicialGlobalSarkariaMap φ z ≠ 0) →
      Function.Surjective
        (H.map (simplicialCellIncidenceProjectionTopHom
          (n := n) (m := m) φ).op))
    (hYS : Function.Injective
      (H.map (ridgeIncidenceDualProjectionTopHom (L := L) (m := m) ψ).op)) :
    ∃ z : SimplicialDeletedJoinSpace n K m,
      simplicialGlobalSarkariaMap φ z = 0 := by
  by_contra hzero
  push Not at hzero
  exact false_of_simplicial_deletedJoin_vanishing_and_lerayVietorisBegle
    φ ψ hψ hL H hD (hXD hzero) hYS

/-- Witness-level form matching the conclusion required by
`simplicialBallZeroTheoremStatement`. -/
theorem exists_simplicialDeletedJoinPoint_zero_of_cohomological_inputs
    {𝕜 : Type u} [Ring 𝕜]
    (φ : K.space → CoordinateSpace d)
    (hφ : IsAffineOnSimplicialFaces K φ)
    (ψ : CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d)
    (hψ : ∀ y : K.space,
      y.val ∈ convexHull ℝ (L : Set (CoordinateSpace e)) → φ y = ψ y.val)
    (hL : IsBoundaryRidge n K L)
    (H : TopCatᵒᵖ ⥤ ModuleCat 𝕜)
    [Nontrivial
      (H.obj (Opposite.op (TopCat.of (DualUnitSphere (SarkariaTarget d m)))))]
    (hD : Subsingleton
      (H.obj (Opposite.op (TopCat.of (SimplicialDeletedJoinSpace n K m)))))
    (hXD : (∀ z : SimplicialDeletedJoinSpace n K m,
      simplicialGlobalSarkariaMap φ z ≠ 0) →
      Function.Surjective
        (H.map (simplicialCellIncidenceProjectionTopHom
          (n := n) (m := m) φ).op))
    (hYS : Function.Injective
      (H.map (ridgeIncidenceDualProjectionTopHom (L := L) (m := m) ψ).op)) :
    ∃ w : SimplicialDeletedJoinPoint (n := n) (m := m) K,
      SimplicialDeletedJoinPoint.sarkariaValue K w φ = 0 := by
  obtain ⟨z, hz⟩ :=
    exists_zero_on_simplicialDeletedJoin_of_cohomological_inputs
      φ ψ hψ hL H hD hXD hYS
  exact exists_sarkariaValue_eq_zero_of_globalMap_eq_zero φ hφ z hz

end AffineTverberg
