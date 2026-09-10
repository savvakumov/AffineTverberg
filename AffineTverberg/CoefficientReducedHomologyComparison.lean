import AffineTverberg.CoefficientComparisonInduction
import AffineTverberg.AffineSpanRealization

set_option linter.style.header false

/-!
# Positive reduced exactness from actual singular homology over any field

The augmented simplicial degree `k + 2` is the ordinary geometric degree
`k + 1`. The comparison is the actual quasi-isomorphism, not an alternative
definition of acyclicity. In particular contractible real geometric realizations
are acyclic over characteristic two as well as over the reals.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AffineTverberg.Simplicial

namespace AffineTverberg.Coefficients

variable (𝕜 : Type) [Field 𝕜]
variable {V : Type} [Fintype V] [LinearOrder V] {K : Finset (Finset V)}

theorem isReducedAcyclicAt_of_isZero_simplicialHomology (hK : FaceClosed K) (k : ℕ)
    (h : IsZero ((simplicialChains 𝕜 hK).homology (k + 1))) :
    IsReducedAcyclicAt 𝕜 K (k + 2) :=
  (simplicialChains_exactAt_iff 𝕜 hK k).mp
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr h)

/-- Actual positive singular vanishing gives exactness in the shifted augmented
simplicial degree, over the same coefficient field. -/
theorem isReducedAcyclicAt_of_subsingleton_singularHomology (hK : FaceClosed K) (k : ℕ)
    (h : Subsingleton ((singularHomology 𝕜 (k + 1)).obj (barySpace K))) :
    IsReducedAcyclicAt 𝕜 K (k + 2) := by
  let := h
  have hz : IsZero ((singularHomology 𝕜 (k + 1)).obj (barySpace K)) :=
    ModuleCat.isZero_of_subsingleton _
  have hi := isIso_comparisonHomologyMap 𝕜 hK (k + 1)
  exact isReducedAcyclicAt_of_isZero_simplicialHomology 𝕜 hK k
    (IsZero.of_iso hz (@asIso _ _ _ _ (comparisonHomologyMap 𝕜 hK (k + 1)) hi))

/-- Contractibility of the actual barycentric realization implies positive
reduced exactness over every field. -/
theorem isReducedAcyclicAt_of_contractible_realization (hK : FaceClosed K)
    [ContractibleSpace ↥(barycentricCarrier K)] (k : ℕ) :
    IsReducedAcyclicAt 𝕜 K (k + 2) :=
  isReducedAcyclicAt_of_subsingleton_singularHomology 𝕜 hK k
    (singularHomology_subsingleton_of_contractible 𝕜
      ↥(barycentricCarrier K) (k + 1) (by omega))

/-- The same conclusion for any genuine real geometric realization of the
finite face family. Only its chain coefficients change. -/
theorem isReducedAcyclicAt_of_contractible_geometricRealization
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : V → E} (hK : FaceClosed K) (hgeom : IsGeometricRealization K q)
    [ContractibleSpace ↥(geometricCarrier K q)] (k : ℕ) :
    IsReducedAcyclicAt 𝕜 K (k + 2) := by
  have : ContractibleSpace ↥(barycentricCarrier K) :=
    (geometricRealizationHomeomorph hgeom).toHomotopyEquiv.contractibleSpace
  exact isReducedAcyclicAt_of_contractible_realization 𝕜 hK k

end AffineTverberg.Coefficients
