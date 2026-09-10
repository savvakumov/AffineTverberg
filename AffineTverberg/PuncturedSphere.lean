import AffineTverberg.PuncturedBall
import AffineTverberg.BoundaryJoinSphere
import Mathlib.Geometry.Manifold.Instances.Sphere

set_option linter.style.header false

/-!
# Punctured finite-dimensional norm spheres are contractible

The existing affine-simplex boundary parametrizations identify norm spheres
of equal dimension. We transport stereographic projection from a Euclidean
sphere through this identification. This applies to the paper's coordinate
spaces with their existing norm, without changing their definitions.
-/

noncomputable section

open Metric

namespace AffineTverberg

/-- Stereographic projection is a homeomorphism on the literal punctured sphere. -/
def puncturedInnerProductSphereHomeomorph {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (p : sphere (0 : E) 1) :
    ↥({q : sphere (0 : E) 1 | q ≠ p}) ≃ₜ ↥(ℝ ∙ (p : E))ᗮ := by
  have hp : ‖(p : E)‖ = 1 := by simp
  exact (stereographic hp).toHomeomorphSourceTarget.trans (Homeomorph.Set.univ _)

theorem contractibleSpace_puncturedInnerProductSphere {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (p : sphere (0 : E) 1) :
    ContractibleSpace ↥({q : sphere (0 : E) 1 | q ≠ p}) :=
  (puncturedInnerProductSphereHomeomorph p).toHomotopyEquiv.contractibleSpace

/-- Removing any point from any finite-dimensional real norm sphere leaves a
contractible space. The norm need not come from an inner product. -/
theorem contractibleSpace_puncturedNormSphere {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : sphere (0 : E) 1) :
    ContractibleSpace ↥({q : sphere (0 : E) 1 | q ≠ p}) := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let e : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1 :=
    normSphereHomeomorphOfFinrankEq (by simp [F])
  have := contractibleSpace_puncturedInnerProductSphere (e p)
  exact (puncturedHomeomorph e p).toHomotopyEquiv.contractibleSpace

/-- This contractibility is invariant under the actual sphere homeomorphism. -/
theorem contractibleSpace_punctured_of_homeomorph_normSphere {X E : Type}
    [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : X ≃ₜ sphere (0 : E) 1) (p : X) : ContractibleSpace ↥({q : X | q ≠ p}) := by
  have := contractibleSpace_puncturedNormSphere (e p)
  exact (puncturedHomeomorph e p).toHomotopyEquiv.contractibleSpace

end AffineTverberg
