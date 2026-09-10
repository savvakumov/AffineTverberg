import AffineTverberg.CanonicalVisibleShelling
import AffineTverberg.UpperSubdivision

set_option linter.style.header false

/-!
# Upper facets of a lifted polytope and their visibility from above

Let `R = conv s` be a polytope in `F × ℝ`, thought of as the lifted image of a
compact convex projection.  A genuine facet of `R` (in the sense of
`RelativeFacet.lean`, so that its index carries an actual supporting
inequality) is an **upper facet** when the vertical coefficient of its
supporting functional is positive.  This file proves the three geometric facts
about upper facets used by the polytopal shelling:

* `isUpperFacet_of_isVisible` / `isVisible_of_isUpperFacet` and
  `exists_visible_eq_upper` — from a point `(x₀, T)` high above the polytope
  the visible facets are *exactly* the upper facets, and that point is outside
  the polytope;
* `exists_upperFacet_of_mem_topGraph` — every point of the upper graph lies on
  an upper facet; the proof is the short-segment lemma of `VisibleFacet.lean`
  applied to the vertical direction, so no limiting argument is needed;
* `facetFace_subset_topGraph` and `arank_fst_image_of_forall_tight` — an upper
  facet lies in the upper graph, and the first-coordinate projection preserves
  the affine rank of any subset of an upper facet hyperplane, because the
  hyperplane is an affine graph over the base.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace UpperFacet

open PolytopeFace CayleyJoin AffineTverberg.CompactConvexProjection

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The vertical coefficient of a continuous linear form on `F × ℝ`. -/
def vcoeff (g : (F × ℝ) →L[ℝ] ℝ) : ℝ := g (0, 1)

omit [FiniteDimensional ℝ F] in
theorem apply_eq_add_vcoeff (g : (F × ℝ) →L[ℝ] ℝ) (p : F × ℝ) :
    g p = g (p.1, 0) + p.2 * vcoeff g := by
  have h : ((p.1, 0) : F × ℝ) + p.2 • ((0 : F), (1 : ℝ)) = p := by
    apply Prod.ext <;> simp
  calc g p = g (((p.1, 0) : F × ℝ) + p.2 • ((0 : F), (1 : ℝ))) := by rw [h]
    _ = g (p.1, 0) + p.2 * vcoeff g := by
        rw [map_add, map_smul, smul_eq_mul, vcoeff]

omit [FiniteDimensional ℝ F] in
theorem apply_vertical_shift (g : (F × ℝ) →L[ℝ] ℝ) (p : F × ℝ) (t : ℝ) :
    g (p.1, p.2 + t) = g p + t * vcoeff g := by
  rw [apply_eq_add_vcoeff g (p.1, p.2 + t), apply_eq_add_vcoeff g p]
  ring

omit [FiniteDimensional ℝ F] in
/-- Two points with the same base differ by their heights only. -/
theorem apply_sub_of_fst_eq (g : (F × ℝ) →L[ℝ] ℝ) {p q : F × ℝ} (h : q.1 = p.1) :
    g q - g p = (q.2 - p.2) * vcoeff g := by
  rw [apply_eq_add_vcoeff g q, apply_eq_add_vcoeff g p, h]
  ring

section Facets

variable {s : Finset (F × ℝ)}

/-- A genuine facet is an *upper* facet when its vertical coefficient is
positive. -/
def IsUpperFacet (j : FacetIdx s) : Prop := 0 < vcoeff (facetForm j)

omit [FiniteDimensional ℝ F] in
/-- **A facet visible from a point high above a base point is an upper
facet.** -/
theorem isUpperFacet_of_isVisible {j : FacetIdx s} {x₀ : F} {T h₀ : ℝ}
    (hmem : ((x₀, h₀) : F × ℝ) ∈ convexHull ℝ (s : Set (F × ℝ))) (hlt : h₀ < T)
    (hvis : facetRhs j < facetForm j (x₀, T)) : IsUpperFacet j := by
  have hle : facetForm j (x₀, h₀) ≤ facetRhs j := facetForm_le_facetRhs j hmem
  have hdiff : facetForm j (x₀, T) - facetForm j (x₀, h₀) =
      (T - h₀) * vcoeff (facetForm j) :=
    apply_sub_of_fst_eq (facetForm j) (p := ((x₀, h₀) : F × ℝ)) (q := ((x₀, T) : F × ℝ)) rfl
  have hpos : 0 < (T - h₀) * vcoeff (facetForm j) := by linarith
  have hT : 0 < T - h₀ := by linarith
  change 0 < vcoeff (facetForm j)
  by_contra hv
  push Not at hv
  nlinarith

omit [FiniteDimensional ℝ F] in
/-- **An upper facet is visible from every sufficiently high point.** -/
theorem isVisible_of_isUpperFacet {j : FacetIdx s} (hj : IsUpperFacet j) {x₀ : F} {T : ℝ}
    (hT : (facetRhs j - facetForm j (x₀, 0)) / vcoeff (facetForm j) < T) :
    facetRhs j < facetForm j (x₀, T) := by
  rw [apply_eq_add_vcoeff (facetForm j) ((x₀, T) : F × ℝ)]
  have := (div_lt_iff₀ hj).mp hT
  simp only at this ⊢
  linarith

omit [FiniteDimensional ℝ F] in
/-- The second coordinate is bounded on the polytope by its value on the
generators. -/
theorem exists_snd_bound (s : Finset (F × ℝ)) :
    ∃ M : ℝ, ∀ p ∈ convexHull ℝ (s : Set (F × ℝ)), p.2 ≤ M := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨0, by simp⟩
  · obtain ⟨v₀, -, hmax⟩ := Finset.exists_max_image s (fun v ↦ v.2) hs
    refine ⟨v₀.2, ?_⟩
    have hconv : Convex ℝ {p : F × ℝ | p.2 ≤ v₀.2} := by
      have : {p : F × ℝ | p.2 ≤ v₀.2} =
          {p : F × ℝ | (ContinuousLinearMap.snd ℝ F ℝ) p ≤ v₀.2} := rfl
      rw [this]
      exact convex_halfSpace_le (LinearMap.isLinear _) _
    exact convexHull_min (fun v hv ↦ hmax v (Finset.mem_coe.mp hv)) hconv

omit [FiniteDimensional ℝ F] in
/-- **From a point high above a base point the visible facets are exactly the
upper facets**, and that point lies outside the polytope. -/
theorem exists_visible_eq_upper {x₀ : F} {h₀ : ℝ}
    (hmem : ((x₀, h₀) : F × ℝ) ∈ convexHull ℝ (s : Set (F × ℝ))) :
    ∃ T : ℝ, ((x₀, T) : F × ℝ) ∉ convexHull ℝ (s : Set (F × ℝ)) ∧
      ∀ j : FacetIdx s,
        (facetRhs j < facetForm j (x₀, T) ↔ IsUpperFacet j) := by
  classical
  obtain ⟨M, hM⟩ := exists_snd_bound s
  let _ : Fintype (FacetIdx s) := Fintype.ofFinite _
  -- a threshold making every upper facet visible
  set thr : FacetIdx s → ℝ := fun j ↦
    if IsUpperFacet j then (facetRhs j - facetForm j (x₀, 0)) / vcoeff (facetForm j) + 1
    else 0 with hthr
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : ℝ, ∀ j : FacetIdx s, thr j ≤ T₀ := by
    rcases isEmpty_or_nonempty (FacetIdx s) with hem | hne
    · exact ⟨0, fun j ↦ (hem.false j).elim⟩
    · obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image (Finset.univ : Finset (FacetIdx s)) thr
        ⟨Classical.arbitrary _, Finset.mem_univ _⟩
      exact ⟨thr j₀, fun j ↦ hj₀ j (Finset.mem_univ j)⟩
  have hh₀ : h₀ ≤ M := hM _ hmem
  refine ⟨max (M + 1) T₀, ?_, fun j ↦ ?_⟩
  · intro hcon
    have := hM _ hcon
    simp only at this
    have : M + 1 ≤ max (M + 1) T₀ := le_max_left _ _
    linarith [hM ((x₀, max (M + 1) T₀) : F × ℝ) hcon]
  · constructor
    · intro hvis
      refine isUpperFacet_of_isVisible hmem ?_ hvis
      have h1 : M + 1 ≤ max (M + 1) T₀ := le_max_left _ _
      linarith
    · intro hj
      refine isVisible_of_isUpperFacet hj ?_
      have h1 : thr j ≤ max (M + 1) T₀ := le_trans (hT₀ j) (le_max_right _ _)
      rw [hthr] at h1
      simp only [hj, ite_eq_left] at h1
      linarith

omit [FiniteDimensional ℝ F] in
/-- **An upper facet lies in the upper graph**: no point of the polytope over
the same base point is higher. -/
theorem le_of_mem_facetFace_of_isUpperFacet {j : FacetIdx s} (hj : IsUpperFacet j)
    {x : F × ℝ} (hx : x ∈ facetFace j) {z : F × ℝ}
    (hz : z ∈ convexHull ℝ (s : Set (F × ℝ))) (hfst : z.1 = x.1) : z.2 ≤ x.2 := by
  have hxt : facetForm j x = facetRhs j := ((mem_facetFace_iff j).1 hx).2
  have hzle : facetForm j z ≤ facetRhs j := facetForm_le_facetRhs j hz
  have hdiff := apply_sub_of_fst_eq (facetForm j) (p := x) (q := z) hfst
  have hv : 0 < vcoeff (facetForm j) := hj
  nlinarith

/-- **Every point of the upper graph lies on an upper facet.**  The proof uses
the short-segment lemma in the vertical direction. -/
theorem exists_upperFacet_of_top (hs : s.Nonempty)
    (hspan : affineSpan ℝ (s : Set (F × ℝ)) = ⊤)
    {p : F × ℝ} (hp : p ∈ convexHull ℝ (s : Set (F × ℝ)))
    (htop : ∀ z ∈ convexHull ℝ (s : Set (F × ℝ)), z.1 = p.1 → z.2 ≤ p.2) :
    ∃ j : FacetIdx s, IsUpperFacet j ∧ p ∈ facetFace j := by
  classical
  by_contra hcon
  push Not at hcon
  -- no facet active at `p` is violated at `p + (0,1)`
  set q : F × ℝ := (p.1, p.2 + 1) with hq
  have hqspan : q ∈ affineSpan ℝ (s : Set (F × ℝ)) := by rw [hspan]; trivial
  have hactive : ∀ j : FacetIdx s, facetForm j p = facetRhs j →
      facetForm j q ≤ facetRhs j := by
    intro j hjp
    by_contra hlt
    push Not at hlt
    have hjface : p ∈ facetFace j := (mem_facetFace_iff j).2 ⟨hp, hjp⟩
    have hupper : IsUpperFacet j := by
      have hval : facetForm j q = facetForm j p + 1 * vcoeff (facetForm j) := by
        rw [hq]
        exact apply_vertical_shift (facetForm j) p 1
      rw [hval, hjp] at hlt
      have : 0 < vcoeff (facetForm j) := by linarith
      exact this
    exact absurd hjface (hcon j hupper)
  obtain ⟨θ, hθpos, hθmem⟩ := exists_pos_segment_mem hs hp hqspan hactive
  have hfst : (p + θ • (q - p)).1 = p.1 := by
    simp [hq]
  have hsnd : (p + θ • (q - p)).2 = p.2 + θ := by
    simp [hq]
  have := htop _ hθmem hfst
  rw [hsnd] at this
  linarith

/-! ### The projection preserves the rank of an upper face -/

/-- The affine graph lift determined by an upper supporting hyperplane. -/
def graphLiftOfForm (g : (F × ℝ) →L[ℝ] ℝ) (c : ℝ) : F →ᵃ[ℝ] F × ℝ :=
  (AffineMap.id ℝ F).prod
    ((vcoeff g)⁻¹ •
      (AffineMap.const ℝ F c -
        (g.comp (ContinuousLinearMap.inl ℝ F ℝ)).toLinearMap.toAffineMap))

omit [FiniteDimensional ℝ F] in
theorem graphLiftOfForm_apply (g : (F × ℝ) →L[ℝ] ℝ) (c : ℝ) (x : F) :
    graphLiftOfForm g c x = (x, (c - g (x, 0)) / vcoeff g) := by
  simp [graphLiftOfForm, div_eq_inv_mul]

omit [FiniteDimensional ℝ F] in
theorem graphLiftOfForm_eq_self {g : (F × ℝ) →L[ℝ] ℝ} {c : ℝ} (hg : vcoeff g ≠ 0)
    {p : F × ℝ} (hp : g p = c) : graphLiftOfForm g c p.1 = p := by
  rw [graphLiftOfForm_apply]
  apply Prod.ext
  · rfl
  · have hval : g (p.1, 0) + p.2 * vcoeff g = c := by
      rw [← apply_eq_add_vcoeff g p]; exact hp
    change (c - g (p.1, 0)) / vcoeff g = p.2
    field_simp
    linarith

/-- **The first-coordinate projection preserves the affine rank of any set on an
upper supporting hyperplane.** -/
theorem arank_fst_image_of_forall_tight {g : (F × ℝ) →L[ℝ] ℝ} {c : ℝ} (hg : vcoeff g ≠ 0)
    {X : Set (F × ℝ)} (hX : ∀ p ∈ X, g p = c) :
    arank (Prod.fst '' X) = arank X := by
  refine arank_image_eq_of_leftInvOn (AffineMap.fst : (F × ℝ) →ᵃ[ℝ] F) (graphLiftOfForm g c) ?_
  intro p hp
  exact graphLiftOfForm_eq_self hg (hX p hp)

end Facets

end UpperFacet
end AffineTverberg
