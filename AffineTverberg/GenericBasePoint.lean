import AffineTverberg.GenericDirection

set_option linter.style.header false

/-!
# A generic base point for the ray towards a fixed external point

In the recursive step of a line shelling the external point `q` is *given* (it
is the crossing point produced one level up), so the direction of the ray can no
longer be chosen freely: only the base point `w` in the relative interior is
free.  This file proves that a good base point exists:

> **`exists_generic_basePoint`** — for every `q` in the affine span there is a
> relative interior point `w` such that the crossing parameters along the
> segment from `w` to `q` are pairwise distinct for the facets visible from
> `q`.

The equality of two crossing parameters is the vanishing of the *affine*
function
`w ↦ (c_i - g_i w)(g_k q - g_k w) - (c_k - g_k w)(g_i q - g_i w)`
(the quadratic terms cancel), which is not identically zero on the affine span
because distinct facets have distinct faces.  Moving from an arbitrary relative
interior point in a direction on which all the relevant linear parts are nonzero
turns each condition into a single forbidden value of the step length, and only
finitely many values have to be avoided.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace PolytopeFace

open CayleyJoin RelInt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The affine function whose vanishing expresses equality of the crossing
parameters of the facets `i` and `k` along the segment from `w` to `q`. -/
def crossEq {s : Finset E} (i k : FacetIdx s) (q w : E) : ℝ :=
  (facetRhs i - facetForm i w) * (facetForm k q - facetForm k w)
    - (facetRhs k - facetForm k w) * (facetForm i q - facetForm i w)

/-- The linear part of `crossEq`. -/
def crossEqLin {s : Finset E} (i k : FacetIdx s) (q : E) : E →L[ℝ] ℝ :=
  (facetRhs k - facetForm k q) • facetForm i - (facetRhs i - facetForm i q) • facetForm k

omit [FiniteDimensional ℝ E] in
/-- `crossEq` is affine: it is a constant plus its linear part. -/
theorem crossEq_eq_add {s : Finset E} (i k : FacetIdx s) (q w : E) :
    crossEq i k q w
      = (facetRhs i * facetForm k q - facetRhs k * facetForm i q)
        + crossEqLin i k q w := by
  simp only [crossEq, crossEqLin, sub_apply, smul_apply, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] in
/-- Two crossing parameters agree exactly when `crossEq` vanishes, provided both
facets are visible from `q` and `w` is a relative interior point. -/
theorem crossParamF_eq_iff_crossEq_eq_zero {s : Finset E} {i k : FacetIdx s}
    {q w : E} (hw : IsRelInt (convexHull ℝ (s : Set E)) w)
    (hi : facetRhs i < facetForm i q) (hk : facetRhs k < facetForm k q) :
    crossParamF i w (q - w) = crossParamF k w (q - w) ↔ crossEq i k q w = 0 := by
  have hwi : facetForm i w < facetRhs i := facetForm_lt_facetRhs_of_isRelInt i hw
  have hwk : facetForm k w < facetRhs k := facetForm_lt_facetRhs_of_isRelInt k hw
  have hdi : facetForm i (q - w) = facetForm i q - facetForm i w := by rw [map_sub]
  have hdk : facetForm k (q - w) = facetForm k q - facetForm k w := by rw [map_sub]
  have hdipos : 0 < facetForm i q - facetForm i w := by linarith
  have hdkpos : 0 < facetForm k q - facetForm k w := by linarith
  rw [crossParamF, crossParamF, hdi, hdk,
    div_eq_div_iff (ne_of_gt hdipos) (ne_of_gt hdkpos)]
  constructor
  · intro h
    simp only [crossEq]
    linarith
  · intro h
    simp only [crossEq] at h
    linarith

/-- **`crossEq` is not identically zero on the affine span** for two distinct
facets visible from `q`. -/
theorem exists_crossEq_ne_zero {s : Finset E} {i k : FacetIdx s} (hik : i ≠ k)
    {q : E} (hi : facetRhs i < facetForm i q) :
    ∃ z ∈ convexHull ℝ (s : Set E), crossEq i k q z ≠ 0 := by
  -- a point of the face of `i` off the hyperplane of `k`
  have hex : ∃ z ∈ facetFace i, facetForm k z ≠ facetRhs k := by
    by_contra hcon
    push Not at hcon
    exact hik (facetIdx_eq_of_facetFace_subset (fun z hz ↦
      (mem_facetFace_iff k).2 ⟨facetFace_subset i hz, hcon z hz⟩))
  obtain ⟨z, hzi, hzk⟩ := hex
  refine ⟨z, facetFace_subset i hzi, ?_⟩
  have hzform : facetForm i z = facetRhs i := ((mem_facetFace_iff i).1 hzi).2
  have hval : crossEq i k q z
      = -(facetRhs k - facetForm k z) * (facetForm i q - facetRhs i) := by
    simp only [crossEq, hzform]
    ring
  rw [hval]
  have h1 : facetRhs k - facetForm k z ≠ 0 := fun h ↦ hzk (by linarith)
  have h2 : facetForm i q - facetRhs i ≠ 0 := by
    intro h
    have : facetForm i q = facetRhs i := by linarith
    linarith
  exact mul_ne_zero (neg_ne_zero.mpr h1) h2

/-- **A generic base point exists.**  For a fixed point `q` of the affine span
there is a relative interior point from which the facets visible from `q` are
crossed at pairwise distinct parameters. -/
theorem exists_generic_basePoint {s : Finset E} (hs : s.Nonempty) (q : E) :
    ∃ w, IsRelInt (convexHull ℝ (s : Set E)) w ∧
      ∀ i k : FacetIdx s, i ≠ k →
        facetRhs i < facetForm i q → facetRhs k < facetForm k q →
        crossParamF i w (q - w) ≠ crossParamF k w (q - w) := by
  classical
  have hfin : Fintype (FacetIdx s) := Fintype.ofFinite _
  obtain ⟨w₀, hw₀, hmove⟩ := exists_isRelInt_move hs
  have hw₀span : w₀ ∈ affineSpan ℝ (s : Set E) :=
    convexHull_subset_affineSpan (𝕜 := ℝ) (s : Set E) hw₀.mem
  -- the pairs whose linear part is nontrivial on the direction space
  set W : Submodule ℝ E := vectorSpan ℝ (s : Set E) with hW
  set Bad : Type _ := {p : FacetIdx s × FacetIdx s //
    ((crossEqLin p.1 p.2 q).toLinearMap.comp W.subtype) ≠ 0} with hBad
  set L : Bad → W →ₗ[ℝ] ℝ := fun p ↦
    (crossEqLin p.1.1 p.1.2 q).toLinearMap.comp W.subtype with hL
  obtain ⟨u, hu⟩ := exists_forall_apply_ne_zero L (fun p ↦ p.2)
  obtain ⟨ε₀, hε₀, hεmem⟩ := hmove (u : E) u.2
  -- the finitely many forbidden step lengths
  set bad : Finset ℝ := Finset.univ.image fun p : FacetIdx s × FacetIdx s ↦
    -(crossEq p.1 p.2 q w₀) / (crossEqLin p.1 p.2 q (u : E)) with hbad
  have hinf : (Set.Ioo (0 : ℝ) ε₀).Infinite := Set.Ioo_infinite hε₀
  obtain ⟨ε, hεIoo, hεbad⟩ := (hinf.exists_notMem_finset bad)
  refine ⟨w₀ + ε • (u : E), hεmem ε (by rw [abs_of_pos hεIoo.1]; exact hεIoo.2), ?_⟩
  intro i k hik hi hk
  have hwrel : IsRelInt (convexHull ℝ (s : Set E)) (w₀ + ε • (u : E)) :=
    hεmem ε (by rw [abs_of_pos hεIoo.1]; exact hεIoo.2)
  rw [Ne, crossParamF_eq_iff_crossEq_eq_zero hwrel hi hk]
  -- evaluate the affine function along the chosen step
  have hval : crossEq i k q (w₀ + ε • (u : E))
      = crossEq i k q w₀ + ε * crossEqLin i k q (u : E) := by
    rw [crossEq_eq_add i k q, crossEq_eq_add i k q w₀, map_add, map_smul]
    simp only [smul_eq_mul]
    ring
  rw [hval]
  by_cases hlin : ((crossEqLin i k q).toLinearMap.comp W.subtype) ≠ 0
  · -- the linear part is nontrivial: only one step length is forbidden
    have hune : crossEqLin i k q (u : E) ≠ 0 := by
      have := hu ⟨(i, k), hlin⟩
      simpa [hL] using this
    intro hzero
    apply hεbad
    have hεeq : ε = -(crossEq i k q w₀) / (crossEqLin i k q (u : E)) := by
      field_simp at hzero ⊢
      linarith
    rw [hbad]
    refine Finset.mem_image.mpr ⟨(i, k), Finset.mem_univ _, ?_⟩
    exact hεeq.symm
  · -- the linear part vanishes: the function is constant and nonzero
    push Not at hlin
    have hune : crossEqLin i k q (u : E) = 0 := by
      have := congrArg (fun f : W →ₗ[ℝ] ℝ ↦ f u) hlin
      simpa using this
    have hconst : ∀ x ∈ affineSpan ℝ (s : Set E),
        crossEq i k q x = crossEq i k q w₀ := by
      intro x hx
      have hxu : x - w₀ ∈ W := by
        have := AffineSubspace.vsub_mem_direction hx hw₀span
        rw [direction_affineSpan] at this
        simpa [hW] using this
      have hzero : crossEqLin i k q (x - w₀) = 0 := by
        have := congrArg (fun f : W →ₗ[ℝ] ℝ ↦ f ⟨x - w₀, hxu⟩) hlin
        simpa using this
      rw [crossEq_eq_add i k q, crossEq_eq_add i k q w₀]
      have : crossEqLin i k q x - crossEqLin i k q w₀ = 0 := by
        rw [← map_sub]; exact hzero
      linarith
    obtain ⟨z, hz, hzne⟩ := exists_crossEq_ne_zero hik hi
    have hzspan : z ∈ affineSpan ℝ (s : Set E) :=
      convexHull_subset_affineSpan (𝕜 := ℝ) (s : Set E) hz
    have hw₀ne : crossEq i k q w₀ ≠ 0 := by
      rw [← hconst z hzspan]; exact hzne
    rw [hune]
    simpa using hw₀ne

end PolytopeFace
end AffineTverberg
