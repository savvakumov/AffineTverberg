import AffineTverberg.VisibleFacet

set_option linter.style.header false

/-!
# Ridges: the facets of a facet are the intersections with the other facets

This is sublemma (b) of the line-shelling route.  For a genuine facet `F` of a
polytope `P = conv s` and a genuine facet `H` of the polytope `F` (a *ridge* of
`P`), there is another ambient facet `F'` with

* `H = F ∩ F'`, and
* the restriction of the inequality of `F'` to the affine span of `F` is
  *oriented like* the inequality of `H`: it is violated at exactly the same
  points of `aff F`.

No normal-cone theory is used.  A relative interior point `z` of the ridge and
a point `q` of `aff F` just beyond the ridge are chosen; `q` lies outside `P`
but on the hyperplane of `F`, so the short-segment lemma of `VisibleFacet.lean`
produces an ambient facet active at `z` and violated at `q`, which cannot be
`F` itself.  A rank comparison then identifies `F ∩ F'` with the ridge, and the
uniqueness of the supporting hyperplane of a facet
(`lt_iff_lt_of_same_contact`) gives the orientation.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace PolytopeFace

open CayleyJoin RelInt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A facet functional is constant on the whole affine span of its facet. -/
theorem facetForm_eq_of_mem_affineSpan {s : Finset E} (j : FacetIdx s) {x : E}
    (hx : x ∈ affineSpan ℝ ((j.1.1 : Finset E) : Set E)) :
    facetForm j x = facetRhs j := by
  refine eq_of_mem_affineSpan_of_forall_eq
    (S := ((j.1.1 : Finset E) : Set E)) (fun v hv ↦ ?_) hx
  exact (facetIdx_isFacetIneq j).tight v (subset_convexHull ℝ _ hv)

/-- **The facets of a facet are its intersections with the other facets.**
For a genuine facet `j` of `conv s` and a genuine facet `i` of the facet
polytope, there is a second ambient facet `j'` cutting out exactly `i`, with the
same orientation on the affine span of the facet. -/
theorem exists_ambient_facet_of_ridge {s : Finset E} (hs : s.Nonempty)
    (j : FacetIdx s) (i : FacetIdx j.1.1) :
    ∃ j' : FacetIdx s, j' ≠ j ∧
      facetFace i = facetFace j ∩ facetFace j' ∧
      ∀ x ∈ affineSpan ℝ ((j.1.1 : Finset E) : Set E),
        (facetRhs i < facetForm i x ↔ facetRhs j' < facetForm j' x) := by
  classical
  have ht : (j.1.1).Nonempty := facetIdx_nonempty j
  have htsub : j.1.1 ⊆ s := Finset.mem_powerset.mp j.1.2
  have hFP : convexHull ℝ ((j.1.1 : Finset E) : Set E) ⊆ convexHull ℝ (s : Set E) :=
    convexHull_mono (by exact_mod_cast htsub)
  have hi := facetIdx_isFacetIneq i
  have hH : (i.1.1).Nonempty := facetIdx_nonempty i
  -- a relative interior point of the ridge and of the facet
  obtain ⟨z, hz⟩ := exists_isRelInt_convexHull hH
  obtain ⟨y, hy⟩ := exists_isRelInt_convexHull ht
  have hzH : z ∈ facetFace i := hz.mem
  have hzt : z ∈ convexHull ℝ ((j.1.1 : Finset E) : Set E) := facetFace_subset i hzH
  have hzform : facetForm i z = facetRhs i := ((mem_facetFace_iff i).1 hzH).2
  have hyform : facetForm i y < facetRhs i := facetForm_lt_facetRhs_of_isRelInt i hy
  -- the point just beyond the ridge inside the affine span of the facet
  set q : E := z + (z - y) with hq
  have hzspan : z ∈ affineSpan ℝ ((j.1.1 : Finset E) : Set E) :=
    convexHull_subset_affineSpan (𝕜 := ℝ) ((j.1.1 : Finset E) : Set E) hzt
  have hyspan : y ∈ affineSpan ℝ ((j.1.1 : Finset E) : Set E) :=
    convexHull_subset_affineSpan (𝕜 := ℝ) ((j.1.1 : Finset E) : Set E) hy.mem
  have hqspan : q ∈ affineSpan ℝ ((j.1.1 : Finset E) : Set E) := by
    have := AffineSubspace.smul_vsub_vadd_mem (affineSpan ℝ ((j.1.1 : Finset E) : Set E)) (1 : ℝ)
      hzspan hyspan hzspan
    simpa [hq, vsub_eq_sub, vadd_eq_add, add_comm] using this
  have hqi : facetRhs i < facetForm i q := by
    have : facetForm i q = facetForm i z + (facetForm i z - facetForm i y) := by
      simp only [hq, map_add, map_sub]
    rw [this, hzform]
    linarith
  have hqnt : q ∉ convexHull ℝ ((j.1.1 : Finset E) : Set E) := fun hmem ↦
    absurd (facetForm_le_facetRhs i hmem) (not_le.mpr hqi)
  -- `q` lies on the hyperplane of `j`, hence outside the polytope
  have hspan_le : affineSpan ℝ ((j.1.1 : Finset E) : Set E) ≤ affineSpan ℝ (s : Set E) :=
    affineSpan_mono ℝ (by exact_mod_cast htsub)
  have hqspans : q ∈ affineSpan ℝ (s : Set E) := hspan_le hqspan
  have hqj : facetForm j q = facetRhs j := facetForm_eq_of_mem_affineSpan j hqspan
  have hqns : q ∉ convexHull ℝ (s : Set E) := by
    intro hmem
    exact hqnt ((mem_facetFace_iff j).2 ⟨hmem, hqj⟩)
  have hzs : z ∈ convexHull ℝ (s : Set E) := hFP hzt
  -- an ambient facet active at `z` and violated at `q`
  obtain ⟨j', hj'z, hj'q⟩ :
      ∃ j' : FacetIdx s, facetForm j' z = facetRhs j' ∧ facetRhs j' < facetForm j' q := by
    by_contra hcon
    push Not at hcon
    obtain ⟨θ, hθpos, hmem⟩ := exists_pos_segment_mem hs hzs hqspans hcon
    have hxspan : z + θ • (q - z) ∈ affineSpan ℝ ((j.1.1 : Finset E) : Set E) := by
      have := AffineSubspace.smul_vsub_vadd_mem (affineSpan ℝ ((j.1.1 : Finset E) : Set E)) θ
        hqspan hzspan hzspan
      simpa [vsub_eq_sub, vadd_eq_add, add_comm] using this
    have hxt : z + θ • (q - z) ∈ convexHull ℝ ((j.1.1 : Finset E) : Set E) :=
      (mem_facetFace_iff j).2 ⟨hmem, facetForm_eq_of_mem_affineSpan j hxspan⟩
    have hxi : facetForm i (z + θ • (q - z))
        = facetRhs i + θ * (facetForm i q - facetRhs i) := by
      simp only [map_add, map_smul, map_sub, smul_eq_mul, hzform]
    have := facetForm_le_facetRhs i hxt
    rw [hxi] at this
    nlinarith
  have hj'ne : j' ≠ j := by
    intro h
    rw [h] at hj'q
    linarith [hqj]
  -- the ridge is contained in the intersection
  have hj'valid : ∀ x ∈ convexHull ℝ ((j.1.1 : Finset E) : Set E), facetForm j' x ≤ facetRhs j' :=
    fun x hx ↦ facetForm_le_facetRhs j' (hFP hx)
  have hj'tightH : ∀ x ∈ facetFace i, facetForm j' x = facetRhs j' := by
    intro x hx
    exact hz.eq_of_valid (fun u hu ↦ hj'valid u (facetFace_subset i hu)) hj'z x hx
  have hHsub : facetFace i ⊆ convexHull ℝ ((j.1.1 : Finset E) : Set E) ∩ facetFace j' := by
    intro x hx
    exact ⟨facetFace_subset i hx,
      (mem_facetFace_iff j').2 ⟨hFP (facetFace_subset i hx), hj'tightH x hx⟩⟩
  -- the intersection is a proper subset of the facet
  set K : Set E := convexHull ℝ ((j.1.1 : Finset E) : Set E) ∩ facetFace j' with hK
  have hKsub : K ⊆ convexHull ℝ ((j.1.1 : Finset E) : Set E) := fun x hx ↦ hx.1
  have hKtight : ∀ x ∈ K, facetForm j' x = facetRhs j' :=
    fun x hx ↦ ((mem_facetFace_iff j').1 hx.2).2
  have hKne : K.Nonempty := ⟨z, hHsub hzH⟩
  have hKproper : ∃ x ∈ convexHull ℝ ((j.1.1 : Finset E) : Set E),
      facetForm j' x < facetRhs j' := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ x ∈ convexHull ℝ ((j.1.1 : Finset E) : Set E),
        facetForm j' x = facetRhs j' :=
      fun x hx ↦ le_antisymm (hj'valid x hx) (hcon x hx)
    have hqeq : facetForm j' q = facetRhs j' := by
      refine eq_of_mem_affineSpan_of_forall_eq (S := ((j.1.1 : Finset E) : Set E))
        (fun v hv ↦ ?_) hqspan
      exact hall v (subset_convexHull ℝ _ hv)
    linarith
  -- the intersection is exactly the ridge
  have hKeq : K = facetFace i := by
    refine Subset.antisymm ?_ hHsub
    -- `K` is a face of `conv t` of rank at most that of the ridge
    have hrankK : arank K ≤ arank (facetFace i) := by
      by_contra hcon
      push Not at hcon
      have hle : arank (convexHull ℝ ((j.1.1 : Finset E) : Set E)) ≤ arank K := by
        have hcodim : arank (facetFace i) + 1
            = arank (convexHull ℝ ((j.1.1 : Finset E) : Set E)) := facetIdx_codim i
        have hmono : arank K ≤ arank (convexHull ℝ ((j.1.1 : Finset E) : Set E)) := arank_mono hKsub
        have hHK : arank (facetFace i) ≤ arank K := le_of_lt hcon
        omega
      have hspanK : affineSpan ℝ K = affineSpan ℝ (convexHull ℝ ((j.1.1 : Finset E) : Set E)) :=
        affineSpan_eq_of_subset_of_arank_le hKne hKsub hle
      have hconst : ∀ x ∈ convexHull ℝ ((j.1.1 : Finset E) : Set E),
          facetForm j' x = facetRhs j' := by
        intro x hx
        refine eq_of_mem_affineSpan_of_forall_eq (S := K) hKtight ?_
        rw [hspanK]
        exact subset_affineSpan ℝ _ hx
      obtain ⟨x, hx, hxlt⟩ := hKproper
      exact absurd (hconst x hx) (ne_of_lt hxlt)
    have hHne : (facetFace i).Nonempty := by
      obtain ⟨v, hv⟩ := hH
      exact ⟨v, subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)⟩
    have hspanKH : affineSpan ℝ K = affineSpan ℝ (facetFace i) :=
      (affineSpan_eq_of_subset_of_arank_le hHne hHsub hrankK).symm
    intro x hx
    have hxspanH : x ∈ affineSpan ℝ (facetFace i) := by
      rw [← hspanKH]
      exact subset_affineSpan ℝ _ hx
    have hxi : facetForm i x = facetRhs i := by
      refine eq_of_mem_affineSpan_of_forall_eq (S := facetFace i) (fun u hu ↦ ?_) hxspanH
      exact ((mem_facetFace_iff i).1 hu).2
    exact (mem_facetFace_iff i).2 ⟨hKsub hx, hxi⟩
  refine ⟨j', hj'ne, hKeq.symm, ?_⟩
  -- the restricted inequality is a facet inequality of the facet with the same
  -- contact face, hence has the same orientation
  have hj'facet : IsFacetIneq j.1.1 (i.1.1) (facetForm j') (facetRhs j') := by
    refine ⟨hj'valid, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact hj'tightH x hx
    · obtain ⟨x, hx, hxlt⟩ := hKproper
      exact ⟨x, hx, hxlt⟩
    · refine Subset.antisymm ?_ ?_
      · intro x hx
        refine ⟨facetFace_subset i hx, fun u hu ↦ ?_⟩
        rw [hj'tightH x hx]
        exact hj'valid u hu
      · intro x hx
        have hxK : x ∈ K := by
          refine ⟨hx.1, (mem_facetFace_iff j').2 ⟨hFP hx.1, ?_⟩⟩
          have hzK : facetForm j' z = facetRhs j' := hj'z
          exact le_antisymm (hj'valid x hx.1) (by
            have := hx.2 z hzt
            rw [hzK] at this
            exact this)
        rw [hKeq] at hxK
        exact hxK
    · exact facetIdx_codim i
  intro x hx
  exact lt_iff_lt_of_same_contact ht (facetIdx_isFacetIneq i) hj'facet hx

end PolytopeFace
end AffineTverberg
