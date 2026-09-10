import AffineTverberg.GenericDirection

set_option linter.style.header false

/-!
# The crossing order and the attaching overlap of a line shelling

Fix a polytope `conv s`, a relative interior point `w` and a direction `d`
inside the affine span.  Along the ray `τ ↦ w + τ • d` a facet inequality can
only ever be violated if the direction increases it, and then exactly after the
crossing parameter (`facetForm_lt_line_iff`).  Thus the facets become visible in
the order of their crossing parameters, and at the crossing point `q_j` of a
facet `j` the visible facets are exactly those crossed strictly earlier
(`isVisible_at_crossPoint_iff`).

Combining this with the overlap identification of `FacetVisibleOverlap.lean`
gives the **attaching data of a line shelling**
(`overlap_at_crossPoint_eq_iUnion_visible_ridge`):

> the intersection of the newly crossed facet with the union of the previously
> crossed ones is exactly the union of its own ridges that are visible from the
> crossing point inside the affine hull of the facet.

This is the geometric input a recursive `CellShelling` certificate needs at
every attaching step.  The induction on dimension itself — turning these
statements into a certificate for the whole visible initial segment — is not
carried out here.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace PolytopeFace

open CayleyJoin RelInt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable {s : Finset E} {w d : E}

omit [FiniteDimensional ℝ E] in
/-- The facet functional is affine along the ray. -/
theorem facetForm_line (j : FacetIdx s) (τ : ℝ) :
    facetForm j (w + τ • d) = facetForm j w + τ * facetForm j d := by
  simp only [map_add, map_smul, smul_eq_mul]

omit [FiniteDimensional ℝ E] in
/-- **The crossing criterion.**  Starting at a relative interior point, the ray
violates the `j`-th facet inequality at parameter `τ ≥ 0` exactly when the
direction increases the functional and the crossing parameter has been
passed. -/
theorem facetForm_lt_line_iff (hw : IsRelInt (convexHull ℝ (s : Set E)) w)
    (j : FacetIdx s) {τ : ℝ} (hτ : 0 ≤ τ) :
    facetRhs j < facetForm j (w + τ • d) ↔
      0 < facetForm j d ∧ crossParamF j w d < τ := by
  have hδ : 0 < facetRhs j - facetForm j w := by
    have := facetForm_lt_facetRhs_of_isRelInt j hw
    linarith
  rw [facetForm_line]
  constructor
  · intro hviol
    have hpos : 0 < τ * facetForm j d := by linarith
    have hd : 0 < facetForm j d := by
      rcases le_or_gt (facetForm j d) 0 with hle | hgt
      · exact absurd hpos (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hτ hle))
      · exact hgt
    refine ⟨hd, ?_⟩
    rw [crossParamF, div_lt_iff₀ hd]
    linarith
  · rintro ⟨hd, hlt⟩
    rw [crossParamF, div_lt_iff₀ hd] at hlt
    linarith

omit [FiniteDimensional ℝ E] in
/-- The crossing parameter of a crossed facet is positive. -/
theorem crossParamF_pos (hw : IsRelInt (convexHull ℝ (s : Set E)) w)
    (j : FacetIdx s) (hd : 0 < facetForm j d) : 0 < crossParamF j w d := by
  have hδ : 0 < facetRhs j - facetForm j w := by
    have := facetForm_lt_facetRhs_of_isRelInt j hw
    linarith
  exact div_pos hδ hd

omit [FiniteDimensional ℝ E] in
/-- The ray stays inside the affine span. -/
theorem mem_affineSpan_line (hw : w ∈ affineSpan ℝ (s : Set E))
    (hd : d ∈ vectorSpan ℝ (s : Set E)) (τ : ℝ) :
    w + τ • d ∈ affineSpan ℝ (s : Set E) := by
  have hdir : τ • d ∈ (affineSpan ℝ (s : Set E)).direction := by
    rw [direction_affineSpan]
    exact Submodule.smul_mem _ τ hd
  have := AffineSubspace.vadd_mem_of_mem_direction hdir hw
  simpa [add_comm] using this

/-- The point at which the ray crosses the hyperplane of the facet `j`. -/
def crossPoint (j : FacetIdx s) (w d : E) : E := w + (crossParamF j w d) • d

omit [FiniteDimensional ℝ E] in
/-- The crossing point lies on the hyperplane of the crossed facet. -/
theorem facetForm_crossPoint (j : FacetIdx s) (hd : facetForm j d ≠ 0) :
    facetForm j (crossPoint j w d) = facetRhs j := by
  rw [crossPoint, facetForm_line, crossParamF, div_mul_cancel₀ _ hd]
  ring

omit [FiniteDimensional ℝ E] in
/-- **At the crossing point of a facet exactly the earlier facets are
visible.** -/
theorem isVisible_at_crossPoint_iff (hw : IsRelInt (convexHull ℝ (s : Set E)) w)
    {j : FacetIdx s} (hjd : 0 < facetForm j d) (k : FacetIdx s) :
    facetRhs k < facetForm k (crossPoint j w d) ↔
      0 < facetForm k d ∧ crossParamF k w d < crossParamF j w d :=
  facetForm_lt_line_iff hw k (le_of_lt (crossParamF_pos hw j hjd))

/-- **The attaching overlap of a line shelling.**  At the crossing point of the
facet `j`, the union of the intersections of `j` with the facets crossed
strictly earlier is exactly the union of the ridges of `j` that are visible
from the crossing point. -/
theorem overlap_at_crossPoint_eq_iUnion_visible_ridge (hs : s.Nonempty)
    (hw : IsRelInt (convexHull ℝ (s : Set E)) w)
    (hd : d ∈ vectorSpan ℝ (s : Set E))
    {j : FacetIdx s} (hjd : 0 < facetForm j d) :
    (⋃ (k : FacetIdx s) (_ : 0 < facetForm k d ∧
          crossParamF k w d < crossParamF j w d), facetFace j ∩ facetFace k)
      = ⋃ (i : FacetIdx j.1.1)
          (_ : facetRhs i < facetForm i (crossPoint j w d)), facetFace i := by
  have hwspan : w ∈ affineSpan ℝ (s : Set E) :=
    convexHull_subset_affineSpan (𝕜 := ℝ) (s : Set E) hw.mem
  have hqspan : crossPoint j w d ∈ affineSpan ℝ (s : Set E) :=
    mem_affineSpan_line hwspan hd _
  have hqj : facetForm j (crossPoint j w d) = facetRhs j :=
    facetForm_crossPoint j (ne_of_gt hjd)
  have hmain := iUnion_facetFace_inter_eq_iUnion_visible_ridge hs j hqspan hqj
  rw [← hmain]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨k, hk, hx⟩
    exact ⟨k, (isVisible_at_crossPoint_iff hw hjd k).2 hk, hx⟩
  · rintro ⟨k, hk, hx⟩
    exact ⟨k, (isVisible_at_crossPoint_iff hw hjd k).1 hk, hx⟩

end PolytopeFace
end AffineTverberg
