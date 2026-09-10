import AffineTverberg.BarycentricRealization
import AffineTverberg.SimplicialFiberAcyclicity
import AffineTverberg.SimplicialCohomology

set_option linter.style.header false

/-!
# The ridge fiber in barycentric coordinates

This connects the newly verified join homology and geometric fiber description
to the standard finite realization. The resulting homeomorphisms use the
actual colored Cayley vertices and the actual fiber of the projection in
Lemma Y. The cohomology statement below is still simplicial cohomology;
comparison with topological cohomology remains separate.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg

open Simplicial

variable {e m : ℕ} {L : Finset (CoordinateSpace e)}
  {eval : CoordinateSpace e → Fin (m + 1) → ℝ}

/-- The finite colored-face family satisfies the standard geometric
realization conditions with its actual Cayley vertex map. -/
theorem isGeometricRealization_colorChoiceFamily
    [Fintype (NonnegativeColoredVertex L eval)]
    (hL : AffineIndependent ℝ ((↑) : L → CoordinateSpace e)) :
    IsGeometricRealization (colorChoiceFamily L eval) coloredCayleyVertex := by
  classical
  apply isGeometricRealization_of_simplicialComplex (coloredCayleyComplex hL eval)
    coloredCayleyVertex_injective
  intro s hs hne
  exact ⟨hne.image _, s, (mem_colorChoiceFamily_iff L eval s).mp hs, rfl⟩

section Ridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (L : Finset (CoordinateSpace e)) (Φ : PolytopalJoinAmbient e m →L[ℝ] E)
  (y : StrongDual ℝ E)
  [Fintype (NonnegativeColoredVertex L (ridgeEval Φ y))]

/-- The geometric carrier of the finite family is exactly the previously
defined nonnegative ridge locus. -/
theorem geometricCarrier_colorChoiceFamily_eq_ridgeNonnegLocus :
    geometricCarrier (colorChoiceFamily L (ridgeEval Φ y)) coloredCayleyVertex =
      ridgeNonnegLocus L Φ y := by
  rw [ridgeNonnegLocus_eq_iUnion_colorChoiceFamily]
  simp only [geometricCarrier, Finset.coe_image]

/-- The standard barycentric realization of the colored family is
homeomorphic to the actual nonnegative ridge locus. -/
def ridgeBarycentricHomeomorph
    (hL : AffineIndependent ℝ ((↑) : L → CoordinateSpace e)) :
    barycentricCarrier (colorChoiceFamily L (ridgeEval Φ y)) ≃ₜ
      ridgeNonnegLocus L Φ y :=
  (geometricRealizationHomeomorph (isGeometricRealization_colorChoiceFamily hL)).trans
    (Homeomorph.setCongr (geometricCarrier_colorChoiceFamily_eq_ridgeNonnegLocus L Φ y))

/-- The required degree range also holds for the actual dual simplicial
cochain complex, by the verified field-coefficient homology comparison. -/
theorem cohomology_ridgeColorChoiceFamily_subsingleton (𝕜 : Type*) [Field 𝕜]
    [LinearOrder (NonnegativeColoredVertex L (ridgeEval Φ y))]
    (hdiag : ∀ x : CoordinateSpace e, ∑ i : Fin (m + 1), Φ (polytopalJoinCopy i x) = 0)
    {k : ℕ} (hk : k < L.card) :
    Subsingleton (cohomology 𝕜 (faceClosed_colorChoiceFamily L (ridgeEval Φ y)) k) :=
  (cohomology_subsingleton_iff_isReducedAcyclicAt _ _).mpr
    (isReducedAcyclicAt_ridgeColorChoiceFamily 𝕜 L Φ y hdiag hk)

end Ridge

/-- Direct identification of a fiber of `Y → S` with the finite barycentric
model whose simplicial homology has been computed. -/
def ridgeIncidenceFiberBarycentricHomeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Finset (CoordinateSpace e)) (Φ : PolytopalJoinAmbient e m →L[ℝ] E)
    (y : DualUnitSphere E)
    [Fintype (NonnegativeColoredVertex L (ridgeEval Φ y.val))]
    (hL : AffineIndependent ℝ ((↑) : L → CoordinateSpace e)) :
    RidgeIncidenceFiber L Φ y ≃ₜ barycentricCarrier (colorChoiceFamily L (ridgeEval Φ y.val)) :=
  (ridgeIncidenceFiberHomeomorph L Φ y).trans (ridgeBarycentricHomeomorph L Φ y.val hL).symm

end AffineTverberg
