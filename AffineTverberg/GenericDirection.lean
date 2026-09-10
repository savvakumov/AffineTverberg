import Mathlib.Algebra.Module.Submodule.Union
import AffineTverberg.FacetVisibleOverlap

set_option linter.style.header false

/-!
# A generic direction for a line shelling

For a line shelling one starts at a relative interior point `w` of the polytope
and travels along a ray `w + t • d` inside the affine span.  The order in which
the facets become visible is the order of the *crossing parameters*
`crossParamF j w d = (c_j - g_j w) / g_j d`, and the argument needs this order
to be strict: no two facets may be crossed at the same parameter, and no facet
hyperplane may be parallel to `d`.

This file proves that such a direction exists.

* `facetIdx_eq_of_facetFace_subset` — distinct genuine facets have incomparable
  faces, so distinct indices really are distinct supporting hyperplanes.
* `exists_forall_apply_ne_zero` — a finite family of nonzero functionals is
  simultaneously nonzero somewhere (a vector space over an infinite field is
  not a finite union of proper subspaces).
* `exists_generic_direction` — **there is a direction inside the affine span
  which is not parallel to any facet hyperplane and for which all crossing
  parameters are pairwise distinct.**  The equality of two crossing parameters
  is the vanishing of the linear form `δ_i · g_j - δ_j · g_i`, which is a
  genuinely nonzero form on the direction space precisely because distinct
  facets have distinct supporting hyperplanes.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace PolytopeFace

open CayleyJoin RelInt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Distinct facets have distinct faces -/

omit [FiniteDimensional ℝ E] in
/-- The canonical index of a genuine facet is the set of generators on it. -/
theorem facetIdx_index_eq_contactGens {s : Finset E} (j : FacetIdx s) :
    j.1.1 = contactGens s (facetForm j) (facetRhs j) :=
  contactGens_eq_of_isFacetGens j.2 (facetIdx_isFacetIneq j)

/-- **Facets are determined by their faces**: one facet contained in another
forces the two indices to be equal. -/
theorem facetIdx_eq_of_facetFace_subset {s : Finset E} {i j : FacetIdx s}
    (h : facetFace i ⊆ facetFace j) : i = j := by
  classical
  have hine : (facetFace i).Nonempty := by
    obtain ⟨v, hv⟩ := facetIdx_nonempty i
    exact ⟨v, subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)⟩
  have hci := facetIdx_codim i
  have hcj := facetIdx_codim j
  have hrank : arank (facetFace j) ≤ arank (facetFace i) := by
    have h1 : arank (facetFace i) + 1 = arank (convexHull ℝ (s : Set E)) := hci
    have h2 : arank (facetFace j) + 1 = arank (convexHull ℝ (s : Set E)) := hcj
    omega
  have hspan : affineSpan ℝ (facetFace i) = affineSpan ℝ (facetFace j) :=
    affineSpan_eq_of_subset_of_arank_le hine h hrank
  have hsubset : facetFace j ⊆ facetFace i := by
    intro x hx
    have hxspan : x ∈ affineSpan ℝ (facetFace i) := by
      rw [hspan]
      exact subset_affineSpan ℝ _ hx
    have hxi : facetForm i x = facetRhs i := by
      refine eq_of_mem_affineSpan_of_forall_eq (S := facetFace i) (fun u hu ↦ ?_) hxspan
      exact ((mem_facetFace_iff i).1 hu).2
    exact (mem_facetFace_iff i).2 ⟨facetFace_subset j hx, hxi⟩
  have hfaces : facetFace i = facetFace j := Subset.antisymm h hsubset
  have hindex : i.1.1 = j.1.1 := by
    rw [facetIdx_index_eq_contactGens i, facetIdx_index_eq_contactGens j]
    ext v
    simp only [mem_contactGens]
    constructor
    · rintro ⟨hv, hgv⟩
      have hvi : v ∈ facetFace i :=
        (mem_facetFace_iff i).2 ⟨subset_convexHull ℝ _ (Finset.mem_coe.mpr hv), hgv⟩
      rw [hfaces] at hvi
      exact ⟨hv, ((mem_facetFace_iff j).1 hvi).2⟩
    · rintro ⟨hv, hgv⟩
      have hvj : v ∈ facetFace j :=
        (mem_facetFace_iff j).2 ⟨subset_convexHull ℝ _ (Finset.mem_coe.mpr hv), hgv⟩
      rw [← hfaces] at hvj
      exact ⟨hv, ((mem_facetFace_iff i).1 hvj).2⟩
  exact Subtype.ext (Subtype.ext hindex)

/-! ### A point where finitely many nonzero functionals are all nonzero -/

/-- A finite family of nonzero linear functionals on a real vector space is
simultaneously nonzero at some point. -/
theorem exists_forall_apply_ne_zero {W : Type*} [AddCommGroup W] [Module ℝ W]
    {ι : Type*} [Finite ι] (L : ι → W →ₗ[ℝ] ℝ) (hL : ∀ k, L k ≠ 0) :
    ∃ d : W, ∀ k, L k d ≠ 0 := by
  have hker : ∀ k, LinearMap.ker (L k) ≠ ⊤ := by
    intro k hk
    exact hL k (LinearMap.ker_eq_top.mp hk)
  obtain ⟨d, hd⟩ :=
    Submodule.exists_forall_notMem_of_forall_ne_top (fun k ↦ LinearMap.ker (L k)) hker
  exact ⟨d, fun k hk ↦ hd k (LinearMap.mem_ker.mpr hk)⟩

/-! ### Crossing parameters and the generic direction -/

/-- The parameter at which the ray `w + t • d` crosses the hyperplane of the
facet `j`. -/
def crossParamF {s : Finset E} (j : FacetIdx s) (w d : E) : ℝ :=
  (facetRhs j - facetForm j w) / facetForm j d

/-- A facet functional is nonconstant along the affine span. -/
theorem exists_mem_vectorSpan_facetForm_ne_zero {s : Finset E} (hs : s.Nonempty)
    (j : FacetIdx s) : ∃ u ∈ vectorSpan ℝ (s : Set E), facetForm j u ≠ 0 := by
  obtain ⟨p, hp⟩ := exists_isRelInt_convexHull hs
  have hplt : facetForm j p < facetRhs j := facetForm_lt_facetRhs_of_isRelInt j hp
  obtain ⟨v, hv⟩ := facetIdx_nonempty j
  have hvform : facetForm j v = facetRhs j :=
    (facetIdx_isFacetIneq j).tight v (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))
  have hvs : v ∈ s := Finset.mem_powerset.mp j.1.2 hv
  have hvspan : v ∈ affineSpan ℝ (s : Set E) :=
    subset_affineSpan ℝ _ (Finset.mem_coe.mpr hvs)
  have hpspan : p ∈ affineSpan ℝ (s : Set E) :=
    convexHull_subset_affineSpan (𝕜 := ℝ) (s : Set E) hp.mem
  refine ⟨v - p, ?_, ?_⟩
  · have := AffineSubspace.vsub_mem_direction hvspan hpspan
    rw [direction_affineSpan] at this
    simpa using this
  · rw [map_sub, hvform]
    intro hzero
    have : facetForm j p = facetRhs j := by linarith
    linarith

/-- **Distinct facets are not proportional along the affine span.**  The linear
form governing the equality of two crossing parameters is nonzero on the
direction space. -/
theorem exists_mem_vectorSpan_pair_ne_zero {s : Finset E}
    {w : E} (hw : IsRelInt (convexHull ℝ (s : Set E)) w) {i j : FacetIdx s}
    (hij : i ≠ j) :
    ∃ u ∈ vectorSpan ℝ (s : Set E),
      (facetRhs i - facetForm i w) * facetForm j u
        - (facetRhs j - facetForm j w) * facetForm i u ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set di : ℝ := facetRhs i - facetForm i w with hdi
  set dj : ℝ := facetRhs j - facetForm j w with hdj
  have hdipos : 0 < di := by
    have := facetForm_lt_facetRhs_of_isRelInt i hw
    simp only [hdi]; linarith
  have hdjpos : 0 < dj := by
    have := facetForm_lt_facetRhs_of_isRelInt j hw
    simp only [hdj]; linarith
  have hwspan : w ∈ affineSpan ℝ (s : Set E) :=
    convexHull_subset_affineSpan (𝕜 := ℝ) (s : Set E) hw.mem
  -- the affine function `di • g_j - dj • g_i` is constant on the affine span
  have hconst : ∀ x ∈ affineSpan ℝ (s : Set E),
      di * facetForm j x - dj * facetForm i x
        = di * facetForm j w - dj * facetForm i w := by
    intro x hx
    have hu : x - w ∈ vectorSpan ℝ (s : Set E) := by
      have := AffineSubspace.vsub_mem_direction hx hwspan
      rw [direction_affineSpan] at this
      simpa using this
    have := hcon _ hu
    rw [map_sub, map_sub] at this
    nlinarith [this]
  -- hence the face of `i` is contained in the face of `j`
  have hsub : facetFace i ⊆ facetFace j := by
    intro x hx
    have hxP : x ∈ convexHull ℝ (s : Set E) := facetFace_subset i hx
    have hxspan : x ∈ affineSpan ℝ (s : Set E) :=
      convexHull_subset_affineSpan (𝕜 := ℝ) (s : Set E) hxP
    have hxi : facetForm i x = facetRhs i := ((mem_facetFace_iff i).1 hx).2
    have h1 := hconst x hxspan
    have hxj : facetForm j x = facetRhs j := by
      rw [hxi] at h1
      have : di * facetForm j x = di * facetRhs j := by
        simp only [hdi, hdj] at h1 ⊢
        nlinarith [h1]
      exact mul_left_cancel₀ (ne_of_gt hdipos) this
    exact (mem_facetFace_iff j).2 ⟨hxP, hxj⟩
  exact hij (facetIdx_eq_of_facetFace_subset hsub)

/-- **A generic direction exists.**  Inside the affine span of the polytope
there is a direction which is not parallel to any facet hyperplane and for
which all crossing parameters from a relative interior point are pairwise
distinct. -/
theorem exists_generic_direction {s : Finset E} (hs : s.Nonempty) {w : E}
    (hw : IsRelInt (convexHull ℝ (s : Set E)) w) :
    ∃ d ∈ vectorSpan ℝ (s : Set E), (∀ j : FacetIdx s, facetForm j d ≠ 0) ∧
      ∀ i j : FacetIdx s, i ≠ j → crossParamF i w d ≠ crossParamF j w d := by
  classical
  set W : Submodule ℝ E := vectorSpan ℝ (s : Set E) with hW
  set L : (FacetIdx s ⊕ {p : FacetIdx s × FacetIdx s // p.1 ≠ p.2}) → W →ₗ[ℝ] ℝ := fun k ↦
    match k with
    | Sum.inl j => (facetForm j).toLinearMap.comp W.subtype
    | Sum.inr p =>
        ((facetRhs p.1.1 - facetForm p.1.1 w) •
            (facetForm p.1.2).toLinearMap
          - (facetRhs p.1.2 - facetForm p.1.2 w) •
            (facetForm p.1.1).toLinearMap).comp W.subtype with hL
  have hLne : ∀ k, L k ≠ 0 := by
    rintro (j | ⟨⟨i, j⟩, hij⟩)
    · obtain ⟨u, huW, hu⟩ := exists_mem_vectorSpan_facetForm_ne_zero hs j
      intro hzero
      apply hu
      have := congrArg (fun (f : W →ₗ[ℝ] ℝ) ↦ f ⟨u, huW⟩) hzero
      simpa [hL] using this
    · obtain ⟨u, huW, hu⟩ := exists_mem_vectorSpan_pair_ne_zero hw hij
      intro hzero
      apply hu
      have := congrArg (fun (f : W →ₗ[ℝ] ℝ) ↦ f ⟨u, huW⟩) hzero
      simpa [hL] using this
  obtain ⟨d, hd⟩ := exists_forall_apply_ne_zero L hLne
  refine ⟨(d : E), d.2, ?_, ?_⟩
  · intro j
    have := hd (Sum.inl j)
    simpa [hL] using this
  · intro i j hij
    have hne := hd (Sum.inr ⟨(i, j), hij⟩)
    have hdi : facetForm i (d : E) ≠ 0 := by
      have := hd (Sum.inl i); simpa [hL] using this
    have hdj : facetForm j (d : E) ≠ 0 := by
      have := hd (Sum.inl j); simpa [hL] using this
    intro heq
    apply hne
    have hkey : (facetRhs i - facetForm i w) * facetForm j (d : E)
        - (facetRhs j - facetForm j w) * facetForm i (d : E) = 0 := by
      rw [crossParamF, crossParamF, div_eq_div_iff hdi hdj] at heq
      linarith [heq]
    simpa [hL] using hkey

end PolytopeFace
end AffineTverberg
