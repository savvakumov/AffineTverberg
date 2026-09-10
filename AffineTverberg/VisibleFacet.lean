import AffineTverberg.RelativeFacet

set_option linter.style.header false

/-!
# Visible facets through a face

This file proves the elementary geometric sublemma needed to identify the
overlap of a newly attached facet in a line shelling:

> **Every proper face on which a valid inequality is tight, with that inequality
> violated at a point `q` of the affine span, is contained in a facet which is
> also violated at `q`.**

No normal-cone theory is used.  The proof takes a relative interior point `z`
of the face; any facet tight at `z` contains the whole face
(`IsRelInt.eq_of_valid`), and if *every* facet tight at `z` were satisfied at
`q`, then a short segment from `z` towards `q` would satisfy every facet
inequality — the active ones because they do not increase, the inactive ones by
finite positive slack — hence would lie in the polytope by the relative facet
description, while violating the inequality exposing the face.

## Main results

* `mem_facetFace_iff` — a point lies on a genuine facet iff it lies in the
  polytope and its inequality is tight there.
* `exists_facetIdx_active_violated` — from a point where a valid inequality is
  tight and a point of the affine span where it is violated, there is a genuine
  facet tight at the first point and violated at the second.
* `exists_facetIdx_face_subset_violated` — the sublemma above, in the form
  "the contact face is contained in a visible facet".
-/

noncomputable section

open Set

namespace AffineTverberg
namespace PolytopeFace

open CayleyJoin RelInt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The (closed) face of the polytope carried by a genuine facet. -/
def facetFace {s : Finset E} (j : FacetIdx s) : Set E :=
  convexHull ℝ ((j.1.1 : Finset E) : Set E)

omit [FiniteDimensional ℝ E] in
theorem facetFace_subset {s : Finset E} (j : FacetIdx s) :
    facetFace j ⊆ convexHull ℝ (s : Set E) :=
  convexHull_mono (by exact_mod_cast Finset.mem_powerset.mp j.1.2)

omit [FiniteDimensional ℝ E] in
/-- **A point lies on a facet exactly when its inequality is tight there.** -/
theorem mem_facetFace_iff {s : Finset E} (j : FacetIdx s) {x : E} :
    x ∈ facetFace j ↔
      x ∈ convexHull ℝ (s : Set E) ∧ facetForm j x = facetRhs j := by
  have h := facetIdx_isFacetIneq j
  constructor
  · intro hx
    exact ⟨facetFace_subset j hx, h.tight x hx⟩
  · rintro ⟨hxP, hxt⟩
    have : x ∈ exposedBy (convexHull ℝ (s : Set E)) (facetForm j) := by
      refine ⟨hxP, fun y hy ↦ ?_⟩
      rw [hxt]
      exact h.valid y hy
    rw [facetFace, h.face]
    exact this

/-- **The short-segment lemma.**  If every facet inequality active at a point
`z` of the polytope is still satisfied at a point `q` of the affine span, then a
short segment from `z` towards `q` stays inside the polytope: the active
inequalities do not increase, and the inactive ones have positive slack. -/
theorem exists_pos_segment_mem {s : Finset E} (hs : s.Nonempty) {z : E}
    (hz : z ∈ convexHull ℝ (s : Set E)) {q : E} (hq : q ∈ affineSpan ℝ (s : Set E))
    (hactive : ∀ j : FacetIdx s, facetForm j z = facetRhs j →
      facetForm j q ≤ facetRhs j) :
    ∃ θ : ℝ, 0 < θ ∧ z + θ • (q - z) ∈ convexHull ℝ (s : Set E) := by
  classical
  have hfin : Fintype (FacetIdx s) := Fintype.ofFinite _
  have hzspan : z ∈ affineSpan ℝ (s : Set E) :=
    convexHull_subset_affineSpan (𝕜 := ℝ) (s : Set E) hz
  have hale : ∀ j : FacetIdx s, facetForm j z ≤ facetRhs j :=
    fun j ↦ facetForm_le_facetRhs j hz
  have hslack : ∀ j : FacetIdx s, facetForm j z < facetForm j q →
      facetForm j z < facetRhs j := by
    intro j hlt
    rcases lt_or_eq_of_le (hale j) with h | h
    · exact h
    · exact absurd (hactive j h) (by linarith)
  set f : FacetIdx s → ℝ := fun j ↦
    if facetForm j z < facetForm j q then
      (facetRhs j - facetForm j z) / (facetForm j q - facetForm j z)
    else 1 with hf
  have hfpos : ∀ j, 0 < f j := by
    intro j
    by_cases hlt : facetForm j z < facetForm j q
    · have hfj : f j = (facetRhs j - facetForm j z) / (facetForm j q - facetForm j z) := by
        simp [hf, hlt]
      rw [hfj]
      exact div_pos (by linarith [hslack j hlt]) (by linarith)
    · have hfj : f j = 1 := by simp [hf, hlt]
      rw [hfj]; exact one_pos
  obtain ⟨θ, hθpos, hθle⟩ : ∃ θ : ℝ, 0 < θ ∧ ∀ j, θ ≤ f j := by
    by_cases hempty : IsEmpty (FacetIdx s)
    · exact ⟨1, one_pos, fun j ↦ (hempty.false j).elim⟩
    · have hne : Nonempty (FacetIdx s) := not_isEmpty_iff.mp hempty
      obtain ⟨j₀, -, hmin⟩ :=
        Finset.exists_min_image (Finset.univ : Finset (FacetIdx s)) f
          ⟨Classical.arbitrary _, Finset.mem_univ _⟩
      exact ⟨f j₀, hfpos j₀, fun j ↦ hmin j (Finset.mem_univ j)⟩
  refine ⟨θ, hθpos, ?_⟩
  set x : E := z + θ • (q - z) with hx
  have hxspan : x ∈ affineSpan ℝ (s : Set E) := by
    have := AffineSubspace.smul_vsub_vadd_mem (affineSpan ℝ (s : Set E)) θ hq hzspan hzspan
    simpa [hx, vsub_eq_sub, vadd_eq_add, add_comm] using this
  rw [mem_convexHull_iff_forall_facetIdx hs hxspan]
  intro j
  have hval : facetForm j x
      = facetForm j z + θ * (facetForm j q - facetForm j z) := by
    simp only [hx, map_add, map_smul, map_sub, smul_eq_mul]
  rw [hval]
  by_cases hlt : facetForm j z < facetForm j q
  · have hfj : f j = (facetRhs j - facetForm j z) / (facetForm j q - facetForm j z) := by
      simp [hf, hlt]
    have hθj : θ ≤ (facetRhs j - facetForm j z) / (facetForm j q - facetForm j z) := by
      rw [← hfj]; exact hθle j
    have hmul : θ * (facetForm j q - facetForm j z) ≤ facetRhs j - facetForm j z :=
      (le_div_iff₀ (by linarith)).1 hθj
    linarith
  · push Not at hlt
    have hnp : θ * (facetForm j q - facetForm j z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hθpos.le (by linarith)
    linarith [hale j]

/-- **A tight valid inequality violated at a point of the affine span extends
to a genuine facet tight at the same point and violated there.** -/
theorem exists_facetIdx_active_violated {s : Finset E} (hs : s.Nonempty)
    {g : E →L[ℝ] ℝ} {c : ℝ}
    (hvalid : ∀ y ∈ convexHull ℝ (s : Set E), g y ≤ c)
    {z : E} (hz : z ∈ convexHull ℝ (s : Set E)) (hzt : g z = c)
    {q : E} (hq : q ∈ affineSpan ℝ (s : Set E)) (hqv : c < g q) :
    ∃ j : FacetIdx s, facetForm j z = facetRhs j ∧ facetRhs j < facetForm j q := by
  by_contra hcon
  push Not at hcon
  obtain ⟨θ, hθpos, hmem⟩ := exists_pos_segment_mem hs hz hq hcon
  have hgx : g (z + θ • (q - z)) = c + θ * (g q - c) := by
    simp only [map_add, map_smul, map_sub, smul_eq_mul, hzt]
  have hxle := hvalid _ hmem
  rw [hgx] at hxle
  nlinarith

/-- **Sublemma (a): a face exposed by a violated valid inequality is contained
in a violated facet.** -/
theorem exists_facetIdx_face_subset_violated {s : Finset E} (hs : s.Nonempty)
    {g : E →L[ℝ] ℝ} {c : ℝ}
    (hvalid : ∀ y ∈ convexHull ℝ (s : Set E), g y ≤ c)
    (hne : (contactGens s g c).Nonempty)
    {q : E} (hq : q ∈ affineSpan ℝ (s : Set E)) (hqv : c < g q) :
    ∃ j : FacetIdx s,
      convexHull ℝ ((contactGens s g c : Finset E) : Set E) ⊆ facetFace j ∧
        facetRhs j < facetForm j q := by
  classical
  set G : Set E := convexHull ℝ ((contactGens s g c : Finset E) : Set E) with hG
  have hGP : G ⊆ convexHull ℝ (s : Set E) := by
    rw [hG]
    exact convexHull_mono (by exact_mod_cast contactGens_subset s g c)
  have hGtight : ∀ y ∈ G, g y = c := by
    intro y hy
    refine eq_of_mem_affineSpan_of_forall_eq (S := ((contactGens s g c : Finset E) : Set E))
      (fun v hv ↦ (mem_contactGens.mp (Finset.mem_coe.mp hv)).2) ?_
    exact convexHull_subset_affineSpan _ hy
  obtain ⟨z, hz⟩ := exists_isRelInt_convexHull hne
  have hzG : z ∈ G := hz.mem
  obtain ⟨j, hjz, hjq⟩ :=
    exists_facetIdx_active_violated hs hvalid (hGP hzG) (hGtight z hzG) hq hqv
  refine ⟨j, fun y hy ↦ ?_, hjq⟩
  have htight : ∀ y ∈ G, facetForm j y = facetRhs j :=
    hz.eq_of_valid (fun u hu ↦ facetForm_le_facetRhs j (hGP hu)) hjz
  exact (mem_facetFace_iff j).2 ⟨hGP hy, htight y hy⟩

end PolytopeFace
end AffineTverberg
