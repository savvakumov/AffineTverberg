import AffineTverberg.RelativeInterior

set_option linter.style.header false

/-!
# A genuine facet system of a polytope inside its affine span

`PolytopeHDescription.lean` describes a `V`-polytope by its facet inequalities
under the hypothesis that the polytope is *full dimensional*.  A face of a
polytope is never full dimensional, so an inductive (recursive shelling)
argument needs the same description relative to the affine span.  Using the
flattening chart of `RelativeInterior.lean` this file proves:

* `exists_facetIneq_violated_of_notMem` — a point of the affine span which is
  not in the polytope violates an actual facet inequality;
* `mem_convexHull_iff_forall_facetIdx` — **the polytope is exactly the
  intersection of its facet halfspaces with its affine span**, the facets being
  indexed by the finite type `FacetIdx s` of *genuine* facets: no dummy
  inequality `0 ≤ 0` occurs, every index carries an actual supporting
  inequality with nonempty contact face of codimension one;
* `facetForm_lt_facetRhs_of_isRelInt` — every facet inequality is *strict* at
  every relative interior point, so the strictness hypothesis of a line
  shelling is satisfiable, which it is not for the unfiltered index type;
* `contactGens` — the canonical index of a facet: **all** generators lying on
  it.  `contactGens_eq_of_isFacetIneq` shows this depends only on the contact
  face, so distinct indices really are distinct facets, and
  `lt_iff_lt_of_same_contactGens` shows two facet inequalities with the same
  contact face are violated at exactly the same points of the affine span:
  duplicate supporting hyperplanes are identified.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace PolytopeFace

open CayleyJoin RelInt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Affine level sets -/

omit [FiniteDimensional ℝ E] in
/-- An affine functional which is constant on a set is constant on its affine
span. -/
theorem eq_of_mem_affineSpan_of_forall_eq {S : Set E} {L : E →L[ℝ] ℝ} {k : ℝ}
    (h : ∀ y ∈ S, L y = k) {x : E} (hx : x ∈ affineSpan ℝ S) : L x = k := by
  set Q : AffineSubspace ℝ E :=
    { carrier := {y | L y = k}
      smul_vsub_vadd_mem' := by
        rintro c p₁ p₂ p₃ h₁ h₂ h₃
        simp only [Set.mem_ofPred_eq, vsub_eq_sub, vadd_eq_add, map_add, map_smul,
          map_sub, smul_eq_mul] at *
        rw [h₁, h₂, h₃]; ring } with hQ
  have hle : affineSpan ℝ S ≤ Q := affineSpan_le.mpr (fun y hy ↦ h y hy)
  exact hle hx

/-! ### The canonical contact generator set -/

open Classical in
/-- All generators lying on the hyperplane `g = c`.  This is the canonical
index of a facet. -/
def contactGens (s : Finset E) (g : E →L[ℝ] ℝ) (c : ℝ) : Finset E :=
  s.filter fun v ↦ g v = c

omit [FiniteDimensional ℝ E] in
theorem mem_contactGens {s : Finset E} {g : E →L[ℝ] ℝ} {c : ℝ} {v : E} :
    v ∈ contactGens s g c ↔ v ∈ s ∧ g v = c := by
  classical
  simp [contactGens]

omit [FiniteDimensional ℝ E] in
theorem contactGens_subset (s : Finset E) (g : E →L[ℝ] ℝ) (c : ℝ) :
    contactGens s g c ⊆ s := by
  classical
  exact Finset.filter_subset _ _

omit [FiniteDimensional ℝ E] in
/-- The contact generators are exactly the generators of the exposed face. -/
theorem contactGens_eq_filter_exposed {s : Finset E} {t : Finset E}
    {g : E →L[ℝ] ℝ} {c : ℝ} (h : IsFacetIneq s t g c) :
    contactGens s g c = s.filter fun v ↦ ∀ w ∈ s, g w ≤ g v := by
  classical
  ext v
  simp only [mem_contactGens, Finset.mem_filter]
  constructor
  · rintro ⟨hv, hgv⟩
    refine ⟨hv, fun w hw ↦ ?_⟩
    rw [hgv]
    exact h.valid w (subset_convexHull ℝ _ (Finset.mem_coe.mpr hw))
  · rintro ⟨hv, hmax⟩
    refine ⟨hv, ?_⟩
    have hexp : v ∈ exposedBy (convexHull ℝ (s : Set E)) g :=
      mem_exposedBy_of_forall_le (Finset.mem_coe.mpr hv)
        (fun w hw ↦ hmax w (Finset.mem_coe.mp hw))
    have hvt : v ∈ convexHull ℝ (t : Set E) := by rw [h.face]; exact hexp
    exact h.tight v hvt

omit [FiniteDimensional ℝ E] in
/-- The convex hull of the contact generators is the contact face. -/
theorem convexHull_contactGens {s t : Finset E} {g : E →L[ℝ] ℝ} {c : ℝ}
    (h : IsFacetIneq s t g c) :
    convexHull ℝ ((contactGens s g c : Finset E) : Set E) =
      convexHull ℝ (t : Set E) := by
  classical
  rw [contactGens_eq_filter_exposed h, ← exposedBy_convexHull s g, h.face]

omit [FiniteDimensional ℝ E] in
/-- A facet inequality is also a facet inequality with its canonical contact
generator set. -/
theorem isFacetIneq_contactGens {s t : Finset E} {g : E →L[ℝ] ℝ} {c : ℝ}
    (h : IsFacetIneq s t g c) : IsFacetIneq s (contactGens s g c) g c := by
  have hhull := convexHull_contactGens h
  exact
    { valid := h.valid
      tight := by rw [hhull]; exact h.tight
      proper := h.proper
      face := by rw [hhull]; exact h.face
      facet := by rw [hhull]; exact h.facet }

/-! ### Transport of facet inequalities along the flattening chart -/

section Transport

variable {W : Submodule ℝ E}

/-- A functional on a submodule extends to an affine inequality on the whole
space with the same values along the chart. -/
theorem exists_chart_extension (W : Submodule ℝ E) (p₀ : E) (g' : W →L[ℝ] ℝ)
    (c' : ℝ) : ∃ (g : E →L[ℝ] ℝ) (c : ℝ),
      ∀ w : W, g (p₀ + (w : E)) - c = g' w - c' := by
  obtain ⟨K, hK⟩ := Submodule.exists_isCompl W
  set π : E →ₗ[ℝ] W := W.projectionOnto K hK with hπ
  set πL : E →L[ℝ] W := LinearMap.toContinuousLinearMap π with hπL
  refine ⟨g'.comp πL, c' + g' (π p₀), fun w ↦ ?_⟩
  have hπw : π (w : E) = w := Submodule.projectionOnto_apply_left hK w
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    hπL, LinearMap.coe_toContinuousLinearMap', map_add, hπw]
  ring

variable {p₀ : E}

omit [FiniteDimensional ℝ E] in
/-- The chart image of an exposed face is the exposed face of the transported
functional. -/
theorem image_exposedBy_chart {g : E →L[ℝ] ℝ} {c : ℝ} {g' : W →L[ℝ] ℝ} {c' : ℝ}
    (hrel : ∀ w : W, g (p₀ + (w : E)) - c = g' w - c') (A : Set W) :
    (chartIncl p₀ W) '' (exposedBy A g') =
      exposedBy ((chartIncl p₀ W) '' A) g := by
  ext x
  constructor
  · rintro ⟨w, ⟨hwA, hwmax⟩, rfl⟩
    refine ⟨⟨w, hwA, rfl⟩, ?_⟩
    rintro y ⟨u, huA, rfl⟩
    have h1 := hrel u
    have h2 := hrel w
    have := hwmax u huA
    simp only [chartIncl_apply] at *
    linarith
  · rintro ⟨⟨w, hwA, rfl⟩, hmax⟩
    refine ⟨w, ⟨hwA, fun u huA ↦ ?_⟩, rfl⟩
    have h1 := hrel u
    have h2 := hrel w
    have := hmax _ ⟨u, huA, rfl⟩
    simp only [chartIncl_apply] at *
    linarith

variable [DecidableEq E]

/-- **Transport of a facet inequality along the flattening chart.** -/
theorem isFacetIneq_chart {s : Finset E} {s' t' : Finset W}
    (himg : (chartIncl p₀ W) '' ((s' : Finset W) : Set W) = (s : Set E))
    {g' : W →L[ℝ] ℝ} {c' : ℝ} (h : IsFacetIneq s' t' g' c')
    {g : E →L[ℝ] ℝ} {c : ℝ}
    (hrel : ∀ w : W, g (p₀ + (w : E)) - c = g' w - c') :
    IsFacetIneq s (t'.image fun w : W ↦ p₀ + (w : E)) g c := by
  have himgt : ((t'.image fun w : W ↦ p₀ + (w : E) : Finset E) : Set E) =
      (chartIncl p₀ W) '' ((t' : Finset W) : Set W) := by
    simp [Finset.coe_image, chartIncl]
  have hhulls : convexHull ℝ (s : Set E) =
      (chartIncl p₀ W) '' convexHull ℝ ((s' : Finset W) : Set W) := by
    rw [AffineMap.image_convexHull, himg]
  have hhullt : convexHull ℝ ((t'.image fun w : W ↦ p₀ + (w : E) : Finset E) : Set E) =
      (chartIncl p₀ W) '' convexHull ℝ ((t' : Finset W) : Set W) := by
    rw [AffineMap.image_convexHull, himgt]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [hhulls] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    have := hrel w
    have hle := h.valid w hw
    simp only [chartIncl_apply] at *
    linarith
  · intro y hy
    rw [hhullt] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    have := hrel w
    have heq := h.tight w hw
    simp only [chartIncl_apply] at *
    linarith
  · obtain ⟨w, hw, hlt⟩ := h.proper
    refine ⟨chartIncl p₀ W w, ?_, ?_⟩
    · rw [hhulls]; exact ⟨w, hw, rfl⟩
    · have := hrel w
      simp only [chartIncl_apply] at *
      linarith
  · rw [hhullt, h.face, image_exposedBy_chart hrel, ← hhulls]
  · rw [hhullt, hhulls, arank_image_chartIncl, arank_image_chartIncl]
    exact h.facet

end Transport

/-! ### Facet inequalities relative to the affine span -/

/-- **A point of the affine span outside the polytope violates an actual facet
inequality**, with canonical contact generator set. -/
theorem exists_facetIneq_violated_of_notMem {s : Finset E} (hs : s.Nonempty)
    {x : E} (hx : x ∈ affineSpan ℝ (s : Set E))
    (hxn : x ∉ convexHull ℝ (s : Set E)) :
    ∃ (g : E →L[ℝ] ℝ) (c : ℝ), IsFacetIneq s (contactGens s g c) g c ∧ c < g x := by
  classical
  obtain ⟨W, p₀, s', himg, hint, hsurj, -⟩ := exists_chart_data hs
  obtain ⟨w, hw⟩ := hsurj x hx
  have hhulls : convexHull ℝ (s : Set E) =
      (chartIncl p₀ W) '' convexHull ℝ ((s' : Finset W) : Set W) := by
    rw [AffineMap.image_convexHull, himg]
  have hwn : w ∉ convexHull ℝ ((s' : Finset W) : Set W) := by
    intro hmem
    apply hxn
    rw [hhulls]
    exact ⟨w, hmem, hw⟩
  have hint' : (interior (convexHull ℝ ((s' : Finset W) : Set W))).Nonempty := hint
  have := (mem_convexHull_iff_forall_isFacetIneq hint' w).not
  simp only [not_forall, not_le] at this
  obtain ⟨t', g', c', hfacet, hviol⟩ := this.1 hwn
  obtain ⟨g, c, hrel⟩ := exists_chart_extension W p₀ g' c'
  have hE : IsFacetIneq s (t'.image fun u : W ↦ p₀ + (u : E)) g c :=
    isFacetIneq_chart himg hfacet hrel
  refine ⟨g, c, isFacetIneq_contactGens hE, ?_⟩
  have := hrel w
  rw [hw] at this
  linarith

/-! ### The finite type of genuine facets -/

/-- `t` is the canonical generator index of an actual facet of `conv s`. -/
def IsFacetGens (s t : Finset E) : Prop :=
  ∃ p : (E →L[ℝ] ℝ) × ℝ, IsFacetIneq s t p.1 p.2 ∧ t = contactGens s p.1 p.2

/-- **The genuine facets of a polytope**, indexed by their canonical contact
generator sets.  Unlike the powerset index used in `PolytopalUpperFacets`, every
index of this type carries an actual facet inequality. -/
def FacetIdx (s : Finset E) : Type _ :=
  {t : {u : Finset E // u ∈ s.powerset} // IsFacetGens s t.1}

instance instFiniteFacetIdx (s : Finset E) : Finite (FacetIdx s) := by
  unfold FacetIdx
  infer_instance

/-- The supporting functional of a genuine facet. -/
def facetForm {s : Finset E} (j : FacetIdx s) : E →L[ℝ] ℝ := facetNormal s j.1.1

/-- The right-hand side of the supporting inequality of a genuine facet. -/
def facetRhs {s : Finset E} (j : FacetIdx s) : ℝ := facetBound s j.1.1

omit [FiniteDimensional ℝ E] in
theorem facetIdx_isFacetIneq {s : Finset E} (j : FacetIdx s) :
    IsFacetIneq s j.1.1 (facetForm j) (facetRhs j) := by
  obtain ⟨p, hp, -⟩ := j.2
  exact facetData_spec ⟨p, hp⟩

omit [FiniteDimensional ℝ E] in
theorem facetForm_le_facetRhs {s : Finset E} (j : FacetIdx s) {x : E}
    (hx : x ∈ convexHull ℝ (s : Set E)) : facetForm j x ≤ facetRhs j :=
  (facetIdx_isFacetIneq j).valid x hx

omit [FiniteDimensional ℝ E] in
/-- The contact face of a genuine facet is nonempty. -/
theorem facetIdx_nonempty {s : Finset E} (j : FacetIdx s) : (j.1.1).Nonempty := by
  classical
  have h := facetIdx_isFacetIneq j
  obtain ⟨y, hy, -⟩ := h.proper
  have hsne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with rfl | hne
    · simp at hy
    · exact hne
  obtain ⟨v, hv, hvmax⟩ := Finset.exists_max_image s (facetForm j) hsne
  have hvexp : v ∈ exposedBy (convexHull ℝ (s : Set E)) (facetForm j) :=
    mem_exposedBy_of_forall_le (Finset.mem_coe.mpr hv)
      (fun w hw ↦ hvmax w (Finset.mem_coe.mp hw))
  have hvt : v ∈ convexHull ℝ ((j.1.1 : Finset E) : Set E) := by
    rw [h.face]; exact hvexp
  rcases Finset.eq_empty_or_nonempty j.1.1 with he | hne
  · rw [he] at hvt; simp at hvt
  · exact hne

omit [FiniteDimensional ℝ E] in
/-- The contact face of a genuine facet has codimension one. -/
theorem facetIdx_codim {s : Finset E} (j : FacetIdx s) :
    arank (convexHull ℝ ((j.1.1 : Finset E) : Set E)) + 1 =
      arank (convexHull ℝ (s : Set E)) := (facetIdx_isFacetIneq j).facet

omit [FiniteDimensional ℝ E] in
/-- **Every facet inequality is strict at every relative interior point.** -/
theorem facetForm_lt_facetRhs_of_isRelInt {s : Finset E} (j : FacetIdx s) {p : E}
    (hp : IsRelInt (convexHull ℝ (s : Set E)) p) : facetForm j p < facetRhs j :=
  hp.lt_of_valid (facetIdx_isFacetIneq j).valid (facetIdx_isFacetIneq j).proper

/-! ### Uniqueness of the supporting hyperplane of a facet -/

omit [FiniteDimensional ℝ E] in
/-- The canonical contact generator set only depends on the contact face:
whenever a set of generators indexes a facet, it is the canonical index of
*every* facet inequality it carries. -/
theorem contactGens_eq_of_isFacetGens {s t : Finset E} (ht : IsFacetGens s t)
    {g : E →L[ℝ] ℝ} {c : ℝ} (h : IsFacetIneq s t g c) : t = contactGens s g c := by
  classical
  obtain ⟨p, hp, hpt⟩ := ht
  ext v
  rw [mem_contactGens]
  constructor
  · intro hv
    have hvs : v ∈ s := by
      rw [hpt] at hv
      exact contactGens_subset _ _ _ hv
    exact ⟨hvs, h.tight v (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))⟩
  · rintro ⟨hvs, hgv⟩
    have hvcontact : v ∈ contactGens s g c := mem_contactGens.mpr ⟨hvs, hgv⟩
    have hvhull : v ∈ convexHull ℝ (t : Set E) := by
      rw [← convexHull_contactGens h]
      exact subset_convexHull ℝ _ (Finset.mem_coe.mpr hvcontact)
    -- `v` is a generator lying on the face, hence a contact generator of `p`
    have hvp : p.1 v = p.2 := hp.tight v hvhull
    rw [hpt]
    exact mem_contactGens.mpr ⟨hvs, hvp⟩

/-- **Two facet inequalities with the same contact face are violated at exactly
the same points of the affine span.**  This identifies duplicate supporting
hyperplanes: the supporting hyperplane of a facet is unique inside the affine
span of the polytope. -/
theorem lt_iff_lt_of_same_contact {s t : Finset E} (hs : s.Nonempty)
    {g₁ g₂ : E →L[ℝ] ℝ} {c₁ c₂ : ℝ}
    (h₁ : IsFacetIneq s t g₁ c₁) (h₂ : IsFacetIneq s t g₂ c₂)
    {x : E} (hx : x ∈ affineSpan ℝ (s : Set E)) :
    (c₁ < g₁ x ↔ c₂ < g₂ x) := by
  classical
  obtain ⟨p, hp⟩ := exists_isRelInt_convexHull hs
  have hp1 : g₁ p < c₁ := hp.lt_of_valid h₁.valid h₁.proper
  have hp2 : g₂ p < c₂ := hp.lt_of_valid h₂.valid h₂.proper
  set G : Set E := convexHull ℝ (t : Set E) with hG
  set S : Set E := convexHull ℝ (s : Set E) with hS
  have hGS : G ⊆ S := by
    rw [hG, h₁.face]
    exact exposedBy_subset _ _
  have hpG : p ∉ affineSpan ℝ G := by
    intro hmem
    have := eq_of_mem_affineSpan_of_forall_eq (L := g₁) (k := c₁)
      (fun y hy ↦ h₁.tight y hy) hmem
    linarith
  have hspan : affineSpan ℝ (insert p G) = affineSpan ℝ S :=
    affineSpan_insert_eq_of_arank_step hGS h₁.facet hp.mem hpG
  -- the affine functional vanishing on the facet and at `p`
  set L : E →L[ℝ] ℝ := (g₂ p - c₂) • g₁ - (g₁ p - c₁) • g₂ with hL
  set k : ℝ := (g₂ p - c₂) * c₁ - (g₁ p - c₁) * c₂ with hk
  have hLconst : ∀ y ∈ insert p G, L y = k := by
    rintro y (rfl | hy)
    · simp only [hL, hk, sub_apply,
        smul_apply, smul_eq_mul]
      ring
    · have hy1 : g₁ y = c₁ := h₁.tight y hy
      have hy2 : g₂ y = c₂ := h₂.tight y hy
      simp only [hL, hk, sub_apply,
        smul_apply, smul_eq_mul, hy1, hy2]
  have hxS : x ∈ affineSpan ℝ S := by
    rw [hS, affineSpan_convexHull]
    exact hx
  have hLx : L x = k :=
    eq_of_mem_affineSpan_of_forall_eq hLconst (by rw [hspan]; exact hxS)
  have hexpand : (g₂ p - c₂) * (g₁ x - c₁) = (g₁ p - c₁) * (g₂ x - c₂) := by
    have := hLx
    simp only [hL, hk, sub_apply,
      smul_apply, smul_eq_mul] at this
    nlinarith [this]
  constructor
  · intro hlt
    nlinarith
  · intro hlt
    nlinarith

/-! ### The exact facet description inside the affine span -/

/-- **The polytope is exactly the intersection of the halfspaces of its genuine
facets with its affine span.**  No dummy inequality occurs: the index type
`FacetIdx s` consists of actual facets. -/
theorem mem_convexHull_iff_forall_facetIdx {s : Finset E} (hs : s.Nonempty) {x : E}
    (hx : x ∈ affineSpan ℝ (s : Set E)) :
    x ∈ convexHull ℝ (s : Set E) ↔ ∀ j : FacetIdx s, facetForm j x ≤ facetRhs j := by
  classical
  constructor
  · intro hmem j
    exact facetForm_le_facetRhs j hmem
  · intro hall
    by_contra hnot
    obtain ⟨g, c, hfacet, hviol⟩ := exists_facetIneq_violated_of_notMem hs hx hnot
    set t : Finset E := contactGens s g c with ht
    have htgens : IsFacetGens s t := ⟨(g, c), hfacet, rfl⟩
    have htsub : t ∈ s.powerset := Finset.mem_powerset.mpr (contactGens_subset s g c)
    set j : FacetIdx s := ⟨⟨t, htsub⟩, htgens⟩ with hj
    have hjineq : IsFacetIneq s t (facetForm j) (facetRhs j) := facetIdx_isFacetIneq j
    have := (lt_iff_lt_of_same_contact hs hfacet hjineq hx).1 hviol
    exact absurd (hall j) (not_le.mpr this)

end PolytopeFace
end AffineTverberg
