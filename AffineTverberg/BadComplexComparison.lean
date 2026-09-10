import AffineTverberg.SimplicialBadTopology
import AffineTverberg.SimplicialToSingular
import AffineTverberg.ComparisonInduction

set_option linter.style.header false

/-!
# The comparison map for the geometric bad subcomplex

The source has zero homology in the required degree, by the constructed
private facets.  The map targets Mathlib's singular homology of the actual
bad polyhedron, and by the general comparison theorem
`Simplicial.isIso_comparisonHomologyMap` it is an isomorphism, so the actual
singular homology of the actual bad polyhedron vanishes in that degree.
-/

noncomputable section

open CategoryTheory AffineTverberg.Simplicial

namespace AffineTverberg.BadEdge

variable {e n m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
variable {W : Type} [Fintype W] [LinearOrder W] [LinearOrder (Finset W)]
variable (idx : W → Fin (m + 1)) (vert : W → CoordinateSpace e)

/-- The comparison map lands in the actual singular homology of the
geometric bad subcomplex, via its verified realization homeomorphism. -/
def badComparisonHomologyMap
    (hinj : Function.Injective fun w ↦ (idx w, vert w)) (k : ℕ) :
    (simplicialChains (faceClosed_badJoinFaces (n := n) (K := K) idx vert)).homology k ⟶
      (realSingularHomology k).obj (TopCat.of ↥(badJoinPartCarrier n K idx vert)) :=
  comparisonHomologyMap (faceClosed_badJoinFaces idx vert) k ≫
    (realSingularHomologyIsoOfHomotopyEquiv
      (badJoinBarycentricHomeomorph idx vert hinj).toHomotopyEquiv k).hom

/-- The ordinary simplicial chain complex has zero homology in geometric
degree `(r - 1) * n - 1`, by the proved bad-complex calculation. -/
theorem isZero_badSimplicialHomology (hm : 2 ≤ m) (hn : 0 < n)
    (hinj : Function.Injective fun w ↦ (idx w, vert w))
    (hcover : ∀ (i : Fin (m + 1)) (s : Finset (CoordinateSpace e)),
      IsBoundarySimplicialFace n K s → ∀ v ∈ s, ∃ w, idx w = i ∧ vert w = v) :
    Limits.IsZero
      ((simplicialChains (faceClosed_badJoinFaces (n := n) (K := K) idx vert)).homology
        (m * n - 1)) := by
  have hprod : 2 ≤ m * n := by nlinarith
  have hacyclic : IsReducedAcyclicAt ℝ (badJoinFaces (n := n) (K := K) idx vert) (m * n) :=
    (homology_subsingleton_iff _ _).mp
      (homology_badJoinFaces_subsingleton idx vert ℝ hm hn hinj hcover)
  have hshift : m * n - 2 + 2 = m * n := by omega
  have hresult := isZero_simplicialChains_homology (faceClosed_badJoinFaces idx vert)
    (m * n - 2) (by simpa only [hshift] using hacyclic)
  have hdegree : m * n - 2 + 1 = m * n - 1 := by omega
  simpa only [hdegree] using hresult

/-- The bad-complex comparison map is an isomorphism in every degree, by the
general comparison theorem. -/
theorem isIso_badComparisonHomologyMap
    (hinj : Function.Injective fun w ↦ (idx w, vert w)) (k : ℕ) :
    IsIso (badComparisonHomologyMap (n := n) (K := K) idx vert hinj k) := by
  have h1 : IsIso (comparisonHomologyMap (faceClosed_badJoinFaces (n := n) (K := K) idx vert) k) :=
    isIso_comparisonHomologyMap _ k
  have h2 : IsIso (realSingularHomologyIsoOfHomotopyEquiv
      (badJoinBarycentricHomeomorph (n := n) (K := K) idx vert hinj).toHomotopyEquiv k).hom :=
    Iso.isIso_hom _
  rw [badComparisonHomologyMap]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

/-- **The actual singular homology of the actual geometric bad subcomplex
vanishes** in geometric degree `m * n - 1`.  This combines the proved
bad-complex calculation with the general comparison theorem and the verified
realization homeomorphism; no comparison is assumed. -/
theorem isZero_badSingularHomology (hm : 2 ≤ m) (hn : 0 < n)
    (hinj : Function.Injective fun w ↦ (idx w, vert w))
    (hcover : ∀ (i : Fin (m + 1)) (s : Finset (CoordinateSpace e)),
      IsBoundarySimplicialFace n K s → ∀ v ∈ s, ∃ w, idx w = i ∧ vert w = v) :
    Limits.IsZero
      ((realSingularHomology (m * n - 1)).obj
        (TopCat.of ↥(badJoinPartCarrier n K idx vert))) := by
  have hsrc := isZero_badSimplicialHomology idx vert hm hn hinj hcover
  have hiso := isIso_badComparisonHomologyMap (n := n) (K := K) idx vert hinj (m * n - 1)
  exact Limits.IsZero.of_iso hsrc
    (@asIso _ _ _ _ (badComparisonHomologyMap (n := n) (K := K) idx vert hinj (m * n - 1))
      hiso).symm

omit [Fintype W] in
/-- **The actual singular homology of the complement of the deleted join in
the boundary join vanishes** in degree `m * n - 1`.  This is the
Alexander-duality input, obtained from the vanishing for the bad subcomplex
through the verified homotopy equivalence
`deletedJoinComplementToBadHomotopyEquiv`. -/
theorem isZero_deletedJoinComplementSingularHomology [Finite W] (hm : 2 ≤ m) (hn : 0 < n)
    (hinj : Function.Injective fun w ↦ (idx w, vert w))
    (hcover : ∀ (i : Fin (m + 1)) (s : Finset (CoordinateSpace e)),
      IsBoundarySimplicialFace n K s → ∀ v ∈ s, ∃ w, idx w = i ∧ vert w = v) :
    Limits.IsZero
      ((realSingularHomology (m * n - 1)).obj
        (TopCat.of ↥((⋃ S ∈ {S : Finset W | IsJoinFace n K idx vert S},
            joinCellCarrier (joinFactor idx vert S)) \
          simplicialDeletedJoinCarrier n K m))) := by
  let := Fintype.ofFinite W
  exact Limits.IsZero.of_iso (isZero_badSingularHomology idx vert hm hn hinj hcover)
    (singularHomologyIso_deletedJoinComplementBad idx vert hinj hcover (m * n - 1))

end AffineTverberg.BadEdge
