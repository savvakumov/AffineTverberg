import AffineTverberg.RelativeLineShelling

set_option linter.style.header false

/-!
# Intersections of faces of a `V`-polytope

The cell data of a shelling certificate is an intersection-preserving
assignment (see `ShellableGluing.lean`), so the combinatorics of a polytopal
cell family must satisfy `A (c ⊓ d) = A c ∩ A d`.  This file proves the
corresponding geometric statement for the genuine facet system:

* `facetFace_inter_eq_convexHull_inter` — the intersection of two facets is the
  convex hull of the generators lying on both, i.e. the face indexed by the
  intersection of the two canonical contact generator sets;
* `contactGens_add_eq_inter` — the underlying combinatorial statement about the
  contact generators of the sum of the two facet inequalities.

Both are proved from the fact that a face of a `V`-polytope is the hull of the
generators it contains, applied to the sum of the two supporting functionals,
which exposes precisely the intersection.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace PolytopeFace

open CayleyJoin RelInt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [DecidableEq E]

omit [FiniteDimensional ℝ E] in
open Classical in
/-- If the two facets meet, the generators maximizing the sum of their
functionals are exactly those lying on both. -/
theorem contactGens_add_eq_inter {s : Finset E} (j k : FacetIdx s) {x : E}
    (hxj : x ∈ facetFace j) (hxk : x ∈ facetFace k) :
    (s.filter fun v ↦ ∀ w ∈ s,
        (facetForm j + facetForm k) w ≤ (facetForm j + facetForm k) v)
      = j.1.1 ∩ k.1.1 := by
  classical
  have hvj := facetIdx_isFacetIneq j
  have hvk := facetIdx_isFacetIneq k
  have hxP : x ∈ convexHull ℝ (s : Set E) := facetFace_subset j hxj
  have hx1 : facetForm j x = facetRhs j := ((mem_facetFace_iff j).1 hxj).2
  have hx2 : facetForm k x = facetRhs k := ((mem_facetFace_iff k).1 hxk).2
  ext v
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨hv, hmax⟩
    have h1 := hvj.valid v (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))
    have h2 := hvk.valid v (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))
    have hexp : v ∈ exposedBy (convexHull ℝ (s : Set E)) (facetForm j + facetForm k) :=
      mem_exposedBy_of_forall_le (Finset.mem_coe.mpr hv)
        (fun w hw ↦ hmax w (Finset.mem_coe.mp hw))
    have hxle := hexp.2 x hxP
    simp only [add_apply, hx1, hx2] at hxle
    have hj : facetForm j v = facetRhs j := by linarith
    have hk : facetForm k v = facetRhs k := by linarith
    refine ⟨?_, ?_⟩
    · rw [facetIdx_index_eq_contactGens j]
      exact mem_contactGens.mpr ⟨hv, hj⟩
    · rw [facetIdx_index_eq_contactGens k]
      exact mem_contactGens.mpr ⟨hv, hk⟩
  · rintro ⟨hvj', hvk'⟩
    have hvs : v ∈ s := Finset.mem_powerset.mp j.1.2 hvj'
    have h1 : facetForm j v = facetRhs j := by
      rw [facetIdx_index_eq_contactGens j] at hvj'
      exact (mem_contactGens.mp hvj').2
    have h2 : facetForm k v = facetRhs k := by
      rw [facetIdx_index_eq_contactGens k] at hvk'
      exact (mem_contactGens.mp hvk').2
    refine ⟨hvs, fun w hw ↦ ?_⟩
    have hw1 := hvj.valid w (subset_convexHull ℝ _ (Finset.mem_coe.mpr hw))
    have hw2 := hvk.valid w (subset_convexHull ℝ _ (Finset.mem_coe.mpr hw))
    simp only [add_apply, h1, h2]
    linarith

omit [FiniteDimensional ℝ E] in
open Classical in
/-- **The intersection of two facets is the face spanned by the generators on
both.** -/
theorem facetFace_inter_eq_convexHull_inter {s : Finset E} (j k : FacetIdx s) :
    facetFace j ∩ facetFace k
      = convexHull ℝ (((j.1.1 ∩ k.1.1 : Finset E) : Finset E) : Set E) := by
  classical
  refine Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxj, hxk⟩ := hx
    have hxP : x ∈ convexHull ℝ (s : Set E) := facetFace_subset j hxj
    have h1 : facetForm j x = facetRhs j := ((mem_facetFace_iff j).1 hxj).2
    have h2 : facetForm k x = facetRhs k := ((mem_facetFace_iff k).1 hxk).2
    have hexp : x ∈ exposedBy (convexHull ℝ (s : Set E)) (facetForm j + facetForm k) := by
      refine ⟨hxP, fun y hy ↦ ?_⟩
      have hy1 := (facetIdx_isFacetIneq j).valid y hy
      have hy2 := (facetIdx_isFacetIneq k).valid y hy
      simp only [add_apply, h1, h2]
      linarith
    rw [exposedBy_convexHull s (facetForm j + facetForm k),
      contactGens_add_eq_inter j k hxj hxk] at hexp
    exact hexp
  · have h1 : (((j.1.1 ∩ k.1.1 : Finset E)) : Set E) ⊆ ((j.1.1 : Finset E) : Set E) := by
      intro v hv
      exact Finset.mem_coe.mpr (Finset.mem_of_mem_inter_left (Finset.mem_coe.mp hv))
    have h2 : (((j.1.1 ∩ k.1.1 : Finset E)) : Set E) ⊆ ((k.1.1 : Finset E) : Set E) := by
      intro v hv
      exact Finset.mem_coe.mpr (Finset.mem_of_mem_inter_right (Finset.mem_coe.mp hv))
    exact Set.subset_inter (convexHull_mono h1) (convexHull_mono h2)

end PolytopeFace
end AffineTverberg
