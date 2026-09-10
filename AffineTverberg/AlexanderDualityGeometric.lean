import AffineTverberg.AlexanderDuality
import AffineTverberg.ComparisonInduction

set_option linter.style.header false

/-!
# Alexander duality for the actual geometric realizations

Combining the combinatorial Alexander duality of
`AffineTverberg/AlexanderDuality.lean` with the general simplicial-to-singular
comparison theorem of `AffineTverberg/ComparisonInduction.lean` gives a genuine
statement about the ordinary real singular homology of actual polyhedra:

`isZero_realSingularHomology_alexanderDual_iff` — for a face-closed family `K`
on a vertex type with `q` vertices and positive degrees `i`, `j` with
`i + j + 3 = q`, the singular homology of the barycentric realization of the
Alexander dual `alexanderDual K` vanishes in degree `i` if and only if the
singular homology of the barycentric realization of `K` vanishes in degree `j`.

This is duality between the two *polyhedra* `|K^∨|` and `|K|`, obtained from the
actual oriented chain complexes; it is **not** yet a statement about the
geometric complement `|∂Δ| \ |K|`, whose identification with `|K^∨|` needs the
barycentric subdivision of the boundary of the simplex and is not proved here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg
namespace Simplicial

variable {V : Type} [Fintype V] [LinearOrder V]

/-- The actual singular homology of the barycentric realization vanishes in a
positive degree exactly when the oriented simplicial complex is exact in the
corresponding cardinality-degree. -/
theorem isZero_realSingularHomology_barySpace_iff {K : Finset (Finset V)}
    (hK : FaceClosed K) (m : ℕ) :
    IsZero ((realSingularHomology (m + 1)).obj (barySpace K)) ↔
      IsReducedAcyclicAt ℝ K (m + 2) := by
  have hiso : IsIso (comparisonHomologyMap hK (m + 1)) :=
    isIso_comparisonHomologyMap hK (m + 1)
  have e : (simplicialChains hK).homology (m + 1) ≅
      (realSingularHomology (m + 1)).obj (barySpace K) :=
    asIso (comparisonHomologyMap hK (m + 1))
  rw [show IsReducedAcyclicAt ℝ K (m + 2) ↔ (simplicialChains hK).ExactAt (m + 1) from
    (simplicialChains_exactAt_iff hK m).symm,
    HomologicalComplex.exactAt_iff_isZero_homology]
  exact ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

/-- **Alexander duality for the actual realizations.**  For a face-closed family
`K` on a vertex type with `i + j + 3` vertices and positive degrees `i` and `j`,
the real singular homology of the polyhedron of the Alexander dual vanishes in
degree `i` if and only if the real singular homology of the polyhedron of `K`
vanishes in degree `j`. -/
theorem isZero_realSingularHomology_alexanderDual_iff {K : Finset (Finset V)}
    (hK : FaceClosed K) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hij : i + j + 3 = Fintype.card V) :
    IsZero ((realSingularHomology i).obj (barySpace (alexanderDual K))) ↔
      IsZero ((realSingularHomology j).obj (barySpace K)) := by
  obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, j = b + 1 := ⟨j - 1, by omega⟩
  rw [isZero_realSingularHomology_barySpace_iff (faceClosed_alexanderDual hK) a,
    isZero_realSingularHomology_barySpace_iff hK b]
  exact isReducedAcyclicAt_alexanderDual_iff_isReducedAcyclicAt hK (by omega)

end Simplicial
end AffineTverberg
