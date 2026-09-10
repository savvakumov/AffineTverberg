import AffineTverberg.SimplicialToSingular
import AffineTverberg.ComparisonInduction
import AffineTverberg.SimplicialFiberRealization

set_option linter.style.header false

/-!
# The comparison map on the actual ridge incidence fiber

`AffineTverberg/SimplicialFiberRealization.lean` identifies the fiber
`RidgeIncidenceFiber L Φ y` of the projection `Y → S` with the standard
barycentric realization of the finite colored family
`colorChoiceFamily L (ridgeEval Φ y)`, and
`AffineTverberg/SimplicialJoinAcyclicity.lean` computes the reduced simplicial
homology of that family.  This file transports the explicit comparison map of
`AffineTverberg/SimplicialToSingular.lean` along that homeomorphism, so that
the computed simplicial homology of the combinatorial model is mapped into the
*actual* singular homology of the *actual* fiber.

The comparison map itself is the honest chain-level map, and by the general
comparison theorem `Simplicial.isIso_comparisonHomologyMap` it is an
isomorphism.  This turns the computed vanishing of the simplicial homology of
the combinatorial model into the *actual* vanishing of the singular homology
of the *actual* fiber.
-/

noncomputable section

open CategoryTheory

namespace AffineTverberg

open _root_.AffineTverberg.Simplicial

variable {e m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (L : Finset (CoordinateSpace e)) (Φ : PolytopalJoinAmbient e m →L[ℝ] E)
  (y : DualUnitSphere E)
  [Fintype (NonnegativeColoredVertex L (ridgeEval Φ y.val))]
  [LinearOrder (NonnegativeColoredVertex L (ridgeEval Φ y.val))]

/-- The finite colored family whose reduced simplicial homology models the
ridge fiber. -/
abbrev ridgeColorFamily : Finset (Finset (NonnegativeColoredVertex L (ridgeEval Φ y.val))) :=
  colorChoiceFamily L (ridgeEval Φ y.val)

/-- Singular homology of the barycentric model of the fiber is the singular
homology of the actual fiber, via the verified homeomorphism. -/
def ridgeFiberSingularIso (hL : AffineIndependent ℝ ((↑) : L → CoordinateSpace e)) (n : ℕ) :
    (realSingularHomology n).obj (barySpace (ridgeColorFamily L Φ y)) ≅
      (realSingularHomology n).obj (TopCat.of (RidgeIncidenceFiber L Φ y)) :=
  realSingularHomologyIsoOfHomotopyEquiv
    (ridgeIncidenceFiberBarycentricHomeomorph L Φ y hL).symm.toHomotopyEquiv n

/-- **The comparison map for the actual ridge fiber**: from ordinary
simplicial homology of the colored family to Mathlib's ordinary singular
homology of the fiber of `Y → S` over `y`. In positive degrees the source
agrees with the reduced computation in `SimplicialJoinAcyclicity`. -/
def ridgeComparisonHomologyMap
    (hL : AffineIndependent ℝ ((↑) : L → CoordinateSpace e)) (n : ℕ) :
    (simplicialChains (faceClosed_colorChoiceFamily L (ridgeEval Φ y.val))).homology n ⟶
      (realSingularHomology n).obj (TopCat.of (RidgeIncidenceFiber L Φ y)) :=
  comparisonHomologyMap (faceClosed_colorChoiceFamily L (ridgeEval Φ y.val)) n ≫
    (ridgeFiberSingularIso L Φ y hL n).hom

/-- The source of the ridge comparison map vanishes in every degree below the
top one, by the verified join acyclicity of the colored family. -/
theorem isZero_ridgeSimplicialHomology
    (hdiag : ∀ x : CoordinateSpace e, ∑ i : Fin (m + 1), Φ (polytopalJoinCopy i x) = 0)
    {n : ℕ} (hn : n + 2 < L.card) :
    Limits.IsZero
      ((simplicialChains (faceClosed_colorChoiceFamily L (ridgeEval Φ y.val))).homology (n + 1)) :=
  isZero_simplicialChains_homology _ n
    (isReducedAcyclicAt_ridgeColorChoiceFamily ℝ L Φ y.val hdiag hn)

/-- The ridge comparison map is an isomorphism in every degree, by the general
comparison theorem. -/
theorem isIso_ridgeComparisonHomologyMap
    (hL : AffineIndependent ℝ ((↑) : L → CoordinateSpace e)) (n : ℕ) :
    IsIso (ridgeComparisonHomologyMap L Φ y hL n) := by
  have := isIso_comparisonHomologyMap (faceClosed_colorChoiceFamily L (ridgeEval Φ y.val)) n
  rw [ridgeComparisonHomologyMap]
  infer_instance

omit [Fintype (NonnegativeColoredVertex L (ridgeEval Φ y.val))] in
/-- **The actual singular homology of the actual ridge fiber vanishes** in
every degree `n + 1` with `n + 2 < L.card`.  This is no longer conditional on
any assumed comparison: it combines the verified join acyclicity of the
colored family with the general comparison theorem and the verified
homeomorphism between the fiber and the barycentric realization. -/
theorem isZero_ridgeFiberSingularHomology
    (hL : AffineIndependent ℝ ((↑) : L → CoordinateSpace e))
    (hdiag : ∀ x : CoordinateSpace e, ∑ i : Fin (m + 1), Φ (polytopalJoinCopy i x) = 0)
    {n : ℕ} (hn : n + 2 < L.card) :
    Limits.IsZero
      ((realSingularHomology (n + 1)).obj (TopCat.of (RidgeIncidenceFiber L Φ y))) := by
  let := Fintype.ofFinite (NonnegativeColoredVertex L (ridgeEval Φ y.val))
  have hsrc := isZero_ridgeSimplicialHomology L Φ y hdiag hn
  have hiso := isIso_ridgeComparisonHomologyMap L Φ y hL (n + 1)
  exact Limits.IsZero.of_iso hsrc
    (@asIso _ _ _ _ (ridgeComparisonHomologyMap L Φ y hL (n + 1)) hiso).symm

omit [Fintype (NonnegativeColoredVertex L (ridgeEval Φ y.val))] in
/-- **The actual singular homology of the concrete geometric fiber
`ridgeNonnegLocus` vanishes** in every degree `n + 1` with `n + 2 < L.card`.
This is the statement flagged as the one remaining gap at the end of
`AffineTverberg/SimplicialFiberAcyclicity.lean`. -/
theorem isZero_ridgeNonnegLocusSingularHomology
    (hL : AffineIndependent ℝ ((↑) : L → CoordinateSpace e))
    (hdiag : ∀ x : CoordinateSpace e, ∑ i : Fin (m + 1), Φ (polytopalJoinCopy i x) = 0)
    {n : ℕ} (hn : n + 2 < L.card) :
    Limits.IsZero
      ((realSingularHomology (n + 1)).obj (TopCat.of ↥(ridgeNonnegLocus L Φ y.1))) :=
  Limits.IsZero.of_iso (isZero_ridgeFiberSingularHomology L Φ y hL hdiag hn)
    (realSingularHomologyIsoOfHomotopyEquiv
      (ridgeIncidenceFiberHomeomorph L Φ y).toHomotopyEquiv (n + 1)).symm

end AffineTverberg
