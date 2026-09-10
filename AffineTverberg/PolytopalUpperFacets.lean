import AffineTverberg.PolytopeHDescription
import AffineTverberg.PolyhedralTop

set_option linter.style.header false

/-!
# The actual facet presentation of a polytopal lifted image, and its top facets

For a compact convex projection `A` whose carrier is an honest `V`-polytope
`conv S`, the lifted image `R = (π, height)(Q)` is again a `V`-polytope, namely
the hull of the finitely many lifted generators.  Combining this with the exact
facet description `PolytopeFace.mem_convexHull_iff_forall_powerset` produces a
genuine `FiniteHalfspacePresentation`: no facet system is assumed anywhere.

Every inequality `a(x) + b t ≤ c` of the presentation is then classified as

* **top** if `b > 0`,
* **bottom** if `b < 0`,
* **vertical** if `b = 0`,

and the two main geometric statements of the upper subdivision are proved:

* `mem_topGraph_iff_exists_top_active` / `topGraph_eq_iUnion_topFacet` — the
  union of the top facets is *exactly* the upper graph of `R`.  The forward
  direction is that a top inequality prevents moving upwards; the reverse
  direction is the fact that if every active inequality has `b ≤ 0` then a
  sufficiently small upward move stays inside all the finitely many
  inequalities, contradicting maximality.
* `exists_visibility_threshold` — from a point `(x₀, T)` with `x₀` in the base
  and `T` large, *precisely* the top inequalities are violated, i.e. precisely
  the top facets are visible.  This is the geometric input for a line shelling
  of the upper faces from a point high above the base.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace CompactConvexProjection

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Splitting a functional on `F × ℝ` into its base part and its vertical
coefficient. -/
theorem apply_prod_eq (g : (F × ℝ) →L[ℝ] ℝ) (x : F) (t : ℝ) :
    g (x, t) = g (x, 0) + t * g (0, 1) := by
  have h : ((x, t) : F × ℝ) = ((x, 0) : F × ℝ) + t • ((0, 1) : F × ℝ) := by
    ext <;> simp
  rw [h, map_add, map_smul]
  simp

/-! ### The lifted image of a polytope is a polytope -/

variable (A : CompactConvexProjection E F)

open Classical in
/-- The lifted generators of a polytopal carrier. -/
def liftedGenerators (S : Finset E) : Finset (F × ℝ) := S.image A.liftedMap

theorem coe_liftedGenerators (S : Finset E) :
    ((A.liftedGenerators S : Finset (F × ℝ)) : Set (F × ℝ)) = A.liftedMap '' (S : Set E) := by
  ext x
  simp [liftedGenerators]

theorem liftedImage_eq_convexHull {S : Finset E}
    (hS : A.carrier = convexHull ℝ (S : Set E)) :
    A.liftedImage = convexHull ℝ ((A.liftedGenerators S : Finset (F × ℝ)) : Set (F × ℝ)) := by
  rw [liftedImage, hS, A.coe_liftedGenerators S]
  exact A.liftedMap.toLinearMap.image_convexHull _

/-! ### The genuine finite halfspace presentation -/

section Presentation

variable [FiniteDimensional ℝ F] {S : Finset E}

/-- The index type of the inequality presentation: all subsets of the lifted
generators. Non-facet subsets contribute the dummy inequality `0 ≤ 0`.
This index type must be filtered before requiring every inequality to be
strict at an interior point in a line-shelling argument. -/
abbrev FacetIndex (S : Finset E) : Type _ :=
  {t : Finset (F × ℝ) // t ∈ (A.liftedGenerators S).powerset}

instance instNonemptyFacetIndex : Nonempty (A.FacetIndex S) :=
  ⟨⟨∅, Finset.empty_mem_powerset _⟩⟩

/-- **The actual facet presentation of a polytopal lifted image.**  The
inequalities are the facet inequalities of `PolytopeHDescription.lean` applied
to the finite generating set of `R`; the only hypotheses are that the carrier
is a `V`-polytope and that `R` is full dimensional. -/
def polytopalPresentation (hS : A.carrier = convexHull ℝ (S : Set E))
    (hfull : affineSpan ℝ A.liftedImage = ⊤) :
    FiniteHalfspacePresentation A (J := A.FacetIndex S) where
  baseNormal j :=
    (PolytopeFace.facetNormal (A.liftedGenerators S) j.1).comp
      (ContinuousLinearMap.inl ℝ F ℝ)
  verticalCoeff j :=
    PolytopeFace.facetNormal (A.liftedGenerators S) j.1 (0, 1)
  bound j := PolytopeFace.facetBound (A.liftedGenerators S) j.1
  mem_liftedImage_iff := by
    intro p
    have hint : (interior (convexHull ℝ
        ((A.liftedGenerators S : Finset (F × ℝ)) : Set (F × ℝ)))).Nonempty := by
      rw [← A.liftedImage_eq_convexHull hS]
      exact (A.liftedImage_convex.interior_nonempty_iff_affineSpan_eq_top).2 hfull
    rw [A.liftedImage_eq_convexHull hS,
      PolytopeFace.mem_convexHull_iff_forall_powerset hint p]
    have key : ∀ t : Finset (F × ℝ),
        PolytopeFace.facetNormal (A.liftedGenerators S) t p =
          PolytopeFace.facetNormal (A.liftedGenerators S) t (p.1, 0) +
            PolytopeFace.facetNormal (A.liftedGenerators S) t (0, 1) * p.2 := by
      intro t
      have h := apply_prod_eq (PolytopeFace.facetNormal (A.liftedGenerators S) t) p.1 p.2
      rw [mul_comm] at h
      simpa using h
    constructor
    · intro h j
      have hj := h j.1 j.2
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.inl_apply]
      rw [← key j.1]
      exact hj
    · intro h t ht
      have hj := h ⟨t, ht⟩
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.inl_apply] at hj
      rw [← key t] at hj
      exact hj

end Presentation

/-! ### Top, bottom and vertical inequalities -/

namespace FiniteHalfspacePresentation

variable {J : Type*} [Finite J] {A : CompactConvexProjection E F}
  (H : FiniteHalfspacePresentation A (J := J))

/-- The value of the `j`-th affine form at a point of `F × ℝ`. -/
def form (j : J) (p : F × ℝ) : ℝ := H.baseNormal j p.1 + H.verticalCoeff j * p.2

/-- A *top* inequality: the vertical coefficient is positive. -/
def IsTopIndex (j : J) : Prop := 0 < H.verticalCoeff j

/-- A *bottom* inequality: the vertical coefficient is negative. -/
def IsBottomIndex (j : J) : Prop := H.verticalCoeff j < 0

/-- A *vertical* inequality: the vertical coefficient vanishes. -/
def IsVerticalIndex (j : J) : Prop := H.verticalCoeff j = 0

/-- The inequality is tight at `p`. -/
def IsActiveAt (j : J) (p : F × ℝ) : Prop := H.form j p = H.bound j

/-- The inequality is violated at `p`, i.e. `p` is *beyond* the corresponding
facet. -/
def IsViolatedAt (j : J) (p : F × ℝ) : Prop := H.bound j < H.form j p

omit [Finite J] in
/-- Every index is of exactly one of the three kinds. -/
theorem isTop_or_isBottom_or_isVertical (j : J) :
    H.IsTopIndex j ∨ H.IsBottomIndex j ∨ H.IsVerticalIndex j := by
  rcases lt_trichotomy (H.verticalCoeff j) 0 with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact Or.inl h

/-- The contact set cut out by the `j`-th inequality. For a dummy inequality
this is the entire polytope, not a genuine facet. -/
def facetSet (j : J) : Set (F × ℝ) := {p ∈ A.liftedImage | H.IsActiveAt j p}

omit [Finite J] in
include H in
theorem le_bound_of_mem_liftedImage {p : F × ℝ} (hp : p ∈ A.liftedImage) (j : J) :
    H.form j p ≤ H.bound j := (H.mem_liftedImage_iff p).1 hp j

variable [Nonempty J]

/-- **The union of the top facets is exactly the upper graph.**  A point of `R`
is on the upper envelope if and only if some inequality with positive vertical
coefficient is tight at it. -/
theorem mem_topGraph_iff_exists_top_active (p : F × ℝ) :
    p ∈ A.topGraph ↔ p ∈ A.liftedImage ∧ ∃ j, H.IsTopIndex j ∧ H.IsActiveAt j p := by
  constructor
  · intro hp
    refine ⟨A.topGraph_subset_liftedImage hp, ?_⟩
    obtain ⟨j, hj, hactive⟩ := H.exists_positive_active p hp
    exact ⟨j, hj, hactive⟩
  · rintro ⟨hpR, j, hj, hactive⟩
    rw [A.mem_topGraph_iff]
    refine ⟨hpR, ?_⟩
    intro q hq hq1
    by_contra hlt
    push Not at hlt
    have hqle : H.form j q ≤ H.bound j := H.le_bound_of_mem_liftedImage hq j
    have hform : H.form j q = H.bound j + H.verticalCoeff j * (q.2 - p.2) := by
      have h1 : H.form j q = H.baseNormal j p.1 + H.verticalCoeff j * q.2 := by
        simp only [form, hq1]
      have h2 : H.bound j = H.baseNormal j p.1 + H.verticalCoeff j * p.2 := by
        simpa only [form] using hactive.symm
      rw [h1, h2]; ring
    nlinarith [mul_pos hj (sub_pos.mpr hlt)]

/-- The same statement as an equality of sets: the upper graph is the union of
the top facets. -/
theorem topGraph_eq_iUnion_topFacet :
    A.topGraph = ⋃ (j : J) (_ : H.IsTopIndex j), H.facetSet j := by
  ext p
  rw [H.mem_topGraph_iff_exists_top_active p]
  simp only [mem_iUnion, facetSet, Set.mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨hpR, j, hj, ha⟩
    exact ⟨j, hj, hpR, ha⟩
  · rintro ⟨j, hj, hpR, ha⟩
    exact ⟨hpR, j, hj, ha⟩

/-! ### Visibility from a point high above the base -/

/-- The threshold beyond which the `j`-th inequality has settled into its
asymptotic behaviour on the vertical line over `x₀`. -/
private def visThreshold (x₀ : F) (j : J) : ℝ :=
  if 0 < H.verticalCoeff j then
    (H.bound j - H.baseNormal j x₀) / H.verticalCoeff j + 1
  else if H.verticalCoeff j < 0 then
    (H.bound j - H.baseNormal j x₀) / H.verticalCoeff j
  else 0

omit [Nonempty J] in
/-- **From a point high above the base, precisely the top facets are
visible.**  For `x₀` in the base of `R` and all sufficiently large heights `T`,
the inequalities violated at `(x₀, T)` are exactly the top ones: the `b > 0`
inequalities fail, the `b < 0` ones hold, and the vertical ones hold because
they already hold over `x₀`. -/
theorem exists_visibility_threshold {x₀ : F} (hx₀ : x₀ ∈ A.base) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ j : J, (H.IsViolatedAt j (x₀, T) ↔ H.IsTopIndex j) := by
  classical
  have : Fintype J := Fintype.ofFinite J
  refine ⟨1 + ∑ j : J, |H.visThreshold x₀ j|, ?_⟩
  intro T hT j
  have hle : |H.visThreshold x₀ j| ≤ ∑ k : J, |H.visThreshold x₀ k| :=
    Finset.single_le_sum (f := fun k ↦ |H.visThreshold x₀ k|)
      (fun k _ ↦ abs_nonneg _) (Finset.mem_univ j)
  have habs : H.visThreshold x₀ j ≤ |H.visThreshold x₀ j| := le_abs_self _
  have hTj : H.visThreshold x₀ j < T := by linarith
  -- the base point lifts into `R`
  obtain ⟨w, hw, hwx⟩ := hx₀
  have hmem : ((x₀, A.height w) : F × ℝ) ∈ A.liftedImage := by
    refine ⟨w, hw, ?_⟩
    apply Prod.ext
    · simpa [liftedMap] using hwx
    · rfl
  have hbase : H.baseNormal j x₀ + H.verticalCoeff j * A.height w ≤ H.bound j :=
    H.le_bound_of_mem_liftedImage hmem j
  simp only [IsViolatedAt, IsTopIndex, form]
  rcases lt_trichotomy (H.verticalCoeff j) 0 with hb | hb | hb
  · -- bottom inequality: satisfied for large `T`
    have hthr : H.visThreshold x₀ j =
        (H.bound j - H.baseNormal j x₀) / H.verticalCoeff j := by
      simp [visThreshold, hb, not_lt.mpr hb.le]
    rw [hthr] at hTj
    have := (div_lt_iff_of_neg hb).1 hTj
    constructor
    · intro hviol; linarith
    · intro hpos; exact absurd hpos (not_lt.mpr hb.le)
  · -- vertical inequality: already satisfied over `x₀`
    have hthr : H.visThreshold x₀ j = 0 := by simp [visThreshold, hb]
    rw [hb] at hbase ⊢
    constructor
    · intro hviol
      simp only [zero_mul, add_zero] at hviol hbase
      linarith
    · intro hpos
      exact absurd hpos (lt_irrefl 0)
  · -- top inequality: violated for large `T`
    have hthr : H.visThreshold x₀ j =
        (H.bound j - H.baseNormal j x₀) / H.verticalCoeff j + 1 := by
      simp [visThreshold, hb]
    rw [hthr] at hTj
    have hdiv : (H.bound j - H.baseNormal j x₀) / H.verticalCoeff j < T := by linarith
    have := (div_lt_iff₀ hb).1 hdiv
    constructor
    · intro _; exact hb
    · intro _; linarith

end FiniteHalfspacePresentation

end CompactConvexProjection
end AffineTverberg
