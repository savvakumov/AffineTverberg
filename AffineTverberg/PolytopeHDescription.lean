import AffineTverberg.PolytopeFacet

set_option linter.style.header false

/-!
# The exact facet description of a full-dimensional `V`-polytope

This file proves the Minkowski half of the Weyl--Minkowski theorem for the
`V`-polytopes used throughout this development:

> a full-dimensional polytope `conv s` (`s` a finite set) is exactly the
> intersection of the finitely many halfspaces determined by its facets.

Nothing is assumed: the facet inequalities are produced from the actual finite
convex hull by combining

* a supporting functional at a boundary point (Hahn--Banach for the open
  convex interior),
* the facet-enlargement theorem `exists_facet_exposed_avoiding` of
  `PolytopeFacet.lean`, and
* the description `exposedBy_convexHull` of a face of a `V`-polytope as the
  hull of the generators it contains, which makes the family of facets finite:
  every facet is indexed by a subset of the generating set `s`.

## Main definitions and results

* `IsFacetIneq s t g c` — `g ≤ c` is a valid inequality for `conv s`, tight
  exactly on the exposed face `conv t`, which is a facet (affine rank one less
  than the polytope).
* `lt_of_mem_interior_of_isFacetIneq` — a facet inequality is strict at every
  interior point.
* `exists_isFacetIneq_of_mem_frontier` — every boundary point of a
  full-dimensional polytope lies on a facet.
* `mem_convexHull_iff_forall_isFacetIneq` — the exact facet description.
* `facetNormal`, `facetBound`, `mem_convexHull_iff_forall_powerset` — the same
  statement with a *finite* index set: the facet inequalities may be indexed by
  the subsets of `s`.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace PolytopeFace

open CayleyJoin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- `g ≤ c` is a facet inequality of the `V`-polytope `conv s` with contact
face the hull of the generator subset `t`. -/
structure IsFacetIneq (s t : Finset E) (g : E →L[ℝ] ℝ) (c : ℝ) : Prop where
  /-- The inequality is valid on the polytope. -/
  valid : ∀ y ∈ convexHull ℝ (s : Set E), g y ≤ c
  /-- It is tight on the contact face. -/
  tight : ∀ y ∈ convexHull ℝ (t : Set E), g y = c
  /-- It is not valid with equality everywhere, i.e. the contact face is proper. -/
  proper : ∃ y ∈ convexHull ℝ (s : Set E), g y < c
  /-- The contact face is the exposed face determined by `g`. -/
  face : convexHull ℝ (t : Set E) = exposedBy (convexHull ℝ (s : Set E)) g
  /-- The contact face has codimension one. -/
  facet : arank (convexHull ℝ (t : Set E)) + 1 = arank (convexHull ℝ (s : Set E))

omit [FiniteDimensional ℝ E] in
/-- A valid inequality which is strict somewhere is strict at every interior
point of a convex set. -/
theorem lt_of_mem_interior_of_valid {A : Set E} {g : E →L[ℝ] ℝ} {c : ℝ}
    (hvalid : ∀ y ∈ A, g y ≤ c) (hproper : ∃ y ∈ A, g y < c)
    {p : E} (hp : p ∈ interior A) : g p < c := by
  obtain ⟨y, hyA, hy⟩ := hproper
  rcases lt_or_eq_of_le (hvalid p (interior_subset hp)) with h | h
  · exact h
  · exfalso
    have hcont : ContinuousAt (fun d : ℝ ↦ p + d • (p - y)) 0 := by fun_prop
    have h0 : interior A ∈ nhds ((fun d : ℝ ↦ p + d • (p - y)) 0) := by
      simpa using IsOpen.mem_nhds isOpen_interior hp
    have hmem : ∀ᶠ d in nhds (0 : ℝ), p + d • (p - y) ∈ interior A :=
      hcont.preimage_mem_nhds h0
    have hmem' : ∀ᶠ d in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        p + d • (p - y) ∈ interior A := hmem.filter_mono nhdsWithin_le_nhds
    obtain ⟨d, hdmem, hdpos⟩ := (hmem'.and self_mem_nhdsWithin).exists
    have hd : g (p + d • (p - y)) ≤ c := hvalid _ (interior_subset hdmem)
    have hexp : g (p + d • (p - y)) = g p + d * (g p - g y) := by
      simp only [map_add, map_smul, map_sub, smul_eq_mul]
    rw [hexp, h] at hd
    nlinarith [mul_pos hdpos (sub_pos.mpr hy)]

omit [FiniteDimensional ℝ E] in
/-- A facet inequality is strict at every interior point. -/
theorem lt_of_mem_interior_of_isFacetIneq {s t : Finset E} {g : E →L[ℝ] ℝ} {c : ℝ}
    (h : IsFacetIneq s t g c) {p : E} (hp : p ∈ interior (convexHull ℝ (s : Set E))) :
    g p < c :=
  lt_of_mem_interior_of_valid h.valid h.proper hp

omit [FiniteDimensional ℝ E] in
/-- Travelling from an interior point towards an outside point one leaves a
compact convex set at a boundary point. -/
theorem exists_crossing {A : Set E} (hA : IsCompact A) {p x : E}
    (hp : p ∈ interior A) (hx : x ∉ A) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ p + θ • (x - p) ∈ A ∧ p + θ • (x - p) ∉ interior A := by
  classical
  set f : ℝ → E := fun u ↦ p + u • (x - p) with hf
  have hfcont : Continuous f := by fun_prop
  set S : Set ℝ := Set.Icc 0 1 ∩ f ⁻¹' A with hS
  have hScompact : IsCompact S :=
    (isCompact_Icc).inter_right ((hA.isClosed.preimage hfcont))
  have hSne : S.Nonempty := ⟨0, by
    refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
    simp [hf, interior_subset hp]⟩
  set θ := sSup S with hθ
  have hθS : θ ∈ S := hScompact.sSup_mem hSne
  have hθ01 : θ ∈ Set.Icc (0 : ℝ) 1 := hθS.1
  have hθA : f θ ∈ A := hθS.2
  have hθne1 : θ ≠ 1 := by
    intro h
    apply hx
    have : f 1 = x := by simp [hf]
    rw [h, this] at hθA
    exact hθA
  have hθlt1 : θ < 1 := lt_of_le_of_ne hθ01.2 hθne1
  have hθnotint : f θ ∉ interior A := by
    intro hint
    -- points slightly further along the ray remain in `A`, contradicting maximality
    have hcont : ContinuousAt (fun u : ℝ ↦ f (θ + u)) 0 := by fun_prop
    have h0 : interior A ∈ nhds ((fun u : ℝ ↦ f (θ + u)) 0) := by
      simpa using IsOpen.mem_nhds isOpen_interior hint
    have hmem : ∀ᶠ u in nhds (0 : ℝ), f (θ + u) ∈ interior A :=
      hcont.preimage_mem_nhds h0
    have hsmall : ∀ᶠ u in nhds (0 : ℝ), u < 1 - θ := Iio_mem_nhds (by linarith)
    have hmem' : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        f (θ + u) ∈ interior A ∧ u < 1 - θ :=
      ((hmem.and hsmall)).filter_mono nhdsWithin_le_nhds
    obtain ⟨u, ⟨humem, hulen⟩, hupos⟩ := (hmem'.and self_mem_nhdsWithin).exists
    have hmemS : θ + u ∈ S := by
      exact ⟨⟨by linarith [hθ01.1], by linarith⟩, (interior_subset humem : f (θ + u) ∈ A)⟩
    have hle : θ + u ≤ θ := le_csSup hScompact.bddAbove hmemS
    linarith
  have hθpos : 0 < θ := by
    rcases lt_or_eq_of_le hθ01.1 with h | h
    · exact h
    · exfalso
      apply hθnotint
      rw [← h]
      simpa [hf] using hp
  exact ⟨θ, hθpos, hθlt1, hθA, hθnotint⟩

omit [FiniteDimensional ℝ E] in
/-- A supporting functional at a point of a closed convex body which is not
interior. -/
theorem exists_supporting_of_notMem_interior {A : Set E} (hconv : Convex ℝ A)
    (hclosed : IsClosed A) (hint : (interior A).Nonempty)
    {z : E} (hzi : z ∉ interior A) :
    ∃ g : E →L[ℝ] ℝ, (∀ y ∈ A, g y ≤ g z) ∧ ∃ y ∈ A, g y < g z := by
  obtain ⟨g, hg⟩ := geometric_hahn_banach_open_point hconv.interior isOpen_interior hzi
  refine ⟨g, ?_, ?_⟩
  · intro y hy
    have hclosedset : IsClosed {w : E | g w ≤ g z} :=
      isClosed_le (by fun_prop) continuous_const
    have hsub : closure (interior A) ⊆ {w : E | g w ≤ g z} :=
      hclosedset.closure_subset_iff.mpr fun w hw ↦ le_of_lt (hg w hw)
    have : y ∈ closure (interior A) := by
      rw [hconv.closure_interior_eq_closure_of_nonempty_interior hint, hclosed.closure_eq]
      exact hy
    exact hsub this
  · obtain ⟨y, hy⟩ := hint
    exact ⟨y, interior_subset hy, hg y hy⟩

/-- **Every boundary point of a full-dimensional `V`-polytope lies on a
facet.** -/
theorem exists_isFacetIneq_of_notMem_interior {s : Finset E}
    (hint : (interior (convexHull ℝ (s : Set E))).Nonempty)
    {z : E} (hz : z ∈ convexHull ℝ (s : Set E))
    (hzi : z ∉ interior (convexHull ℝ (s : Set E))) :
    ∃ t ⊆ s, ∃ g : E →L[ℝ] ℝ, ∃ c : ℝ,
      IsFacetIneq s t g c ∧ z ∈ convexHull ℝ (t : Set E) := by
  classical
  set A := convexHull ℝ (s : Set E) with hA
  have hAcompact : IsCompact A := s.finite_toSet.isCompact_convexHull ℝ
  have hAconv : Convex ℝ A := convex_convexHull ℝ _
  obtain ⟨g₀, hg₀le, y₀, hy₀A, hy₀lt⟩ :=
    exists_supporting_of_notMem_interior hAconv hAcompact.isClosed hint hzi
  have hzF₀ : z ∈ exposedBy A g₀ := ⟨hz, hg₀le⟩
  have hy₀F₀ : y₀ ∉ exposedBy A g₀ := by
    rintro ⟨-, hmax⟩
    exact absurd (hmax z hz) (not_le.mpr hy₀lt)
  obtain ⟨F, hFexp, hsub, hy₀F, hrank⟩ :=
    exists_facet_exposed_avoiding (s := s) (isExposed_exposedBy A g₀) hy₀A hy₀F₀
  have hzF : z ∈ F := hsub hzF₀
  obtain ⟨l, hl0⟩ := hFexp ⟨z, hzF⟩
  have hl : F = exposedBy A l := hl0
  set t : Finset E := s.filter fun v ↦ ∀ w ∈ s, l w ≤ l v with ht
  have hFt : F = convexHull ℝ (t : Set E) := by
    rw [hl, ht, hA]
    exact exposedBy_convexHull s l
  have hzt : z ∈ convexHull ℝ (t : Set E) := hFt ▸ hzF
  have hzexp : z ∈ exposedBy A l := by rw [← hl]; exact hzF
  refine ⟨t, Finset.filter_subset _ _, l, l z, ?_, hzt⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun y hy ↦ hzexp.2 y hy
  · intro y hy
    have : y ∈ exposedBy A l := by rw [← hl, hFt]; exact hy
    exact eq_of_mem_exposedBy this hzexp
  · refine ⟨y₀, hy₀A, ?_⟩
    have hy₀nexp : y₀ ∉ exposedBy A l := by rw [← hl]; exact hy₀F
    rcases lt_or_eq_of_le (hzexp.2 y₀ hy₀A) with h | h
    · exact h
    · exact absurd (⟨hy₀A, fun y hy ↦ h ▸ hzexp.2 y hy⟩ : y₀ ∈ exposedBy A l) hy₀nexp
  · rw [← hFt, hl, hA]
  · rw [← hFt]; exact hrank

omit [FiniteDimensional ℝ E] in
/-- If a facet inequality is tight at a point of the open segment from an
interior point `p` to `x`, then `x` violates it. -/
theorem lt_of_isFacetIneq_of_segment {s t : Finset E} {g : E →L[ℝ] ℝ} {c : ℝ}
    (h : IsFacetIneq s t g c) {p x : E}
    (hp : p ∈ interior (convexHull ℝ (s : Set E)))
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hzt : p + θ • (x - p) ∈ convexHull ℝ (t : Set E)) : c < g x := by
  have hgp : g p < c := lt_of_mem_interior_of_isFacetIneq h hp
  have hgz : g (p + θ • (x - p)) = c := h.tight _ hzt
  have hexp : g (p + θ • (x - p)) = g p + θ * (g x - g p) := by
    simp only [map_add, map_smul, map_sub, smul_eq_mul]
  rw [hexp] at hgz
  nlinarith

/-- **The exact facet description of a full-dimensional `V`-polytope.** -/
theorem mem_convexHull_iff_forall_isFacetIneq {s : Finset E}
    (hint : (interior (convexHull ℝ (s : Set E))).Nonempty) (x : E) :
    x ∈ convexHull ℝ (s : Set E) ↔
      ∀ (t : Finset E) (g : E →L[ℝ] ℝ) (c : ℝ), IsFacetIneq s t g c → g x ≤ c := by
  constructor
  · intro hx t g c h
    exact h.valid x hx
  · intro hx
    by_contra hnot
    obtain ⟨p, hp⟩ := id hint
    have hAcompact : IsCompact (convexHull ℝ (s : Set E)) := s.finite_toSet.isCompact_convexHull ℝ
    obtain ⟨θ, hθ0, hθ1, hzA, hznot⟩ :=
      exists_crossing hAcompact hp hnot
    obtain ⟨t, -, g, c, hfacet, hzt⟩ :=
      exists_isFacetIneq_of_notMem_interior hint hzA hznot
    exact absurd (hx t g c hfacet)
      (not_le.mpr (lt_of_isFacetIneq_of_segment hfacet hp hθ0 hθ1 hzt))

/-! ### A finite index set for the facet inequalities -/

open Classical in
/-- A chosen facet inequality with contact vertex set `t`, if one exists, and
the trivial inequality `0 ≤ 0` otherwise. -/
def facetData (s t : Finset E) : (E →L[ℝ] ℝ) × ℝ :=
  if h : ∃ p : (E →L[ℝ] ℝ) × ℝ, IsFacetIneq s t p.1 p.2 then h.choose else (0, 0)

/-- The normal vector of the chosen facet inequality. -/
def facetNormal (s t : Finset E) : E →L[ℝ] ℝ := (facetData s t).1

/-- The right-hand side of the chosen facet inequality. -/
def facetBound (s t : Finset E) : ℝ := (facetData s t).2

omit [FiniteDimensional ℝ E] in
theorem facetData_spec {s t : Finset E} (h : ∃ p : (E →L[ℝ] ℝ) × ℝ, IsFacetIneq s t p.1 p.2) :
    IsFacetIneq s t (facetNormal s t) (facetBound s t) := by
  classical
  have hd : facetData s t = h.choose := by
    rw [facetData]
    split
    · rfl
    · exact absurd h (by assumption)
  rw [facetNormal, facetBound, hd]
  exact h.choose_spec

omit [FiniteDimensional ℝ E] in
/-- Every chosen inequality is valid on the polytope. -/
theorem facetNormal_le_facetBound (s t : Finset E) {x : E}
    (hx : x ∈ convexHull ℝ (s : Set E)) : facetNormal s t x ≤ facetBound s t := by
  classical
  by_cases h : ∃ p : (E →L[ℝ] ℝ) × ℝ, IsFacetIneq s t p.1 p.2
  · exact (facetData_spec h).valid x hx
  · have hd : facetData s t = (0, 0) := by
      rw [facetData]
      split
      · exact absurd (by assumption) h
      · rfl
    rw [facetNormal, facetBound, hd]
    simp

/-- **The facet description with a finite index set**: a full-dimensional
`V`-polytope is cut out by the inequalities indexed by the subsets of its
generating set. -/
theorem mem_convexHull_iff_forall_powerset {s : Finset E}
    (hint : (interior (convexHull ℝ (s : Set E))).Nonempty) (x : E) :
    x ∈ convexHull ℝ (s : Set E) ↔
      ∀ t ∈ s.powerset, facetNormal s t x ≤ facetBound s t := by
  classical
  constructor
  · intro hx t _
    exact facetNormal_le_facetBound s t hx
  · intro hx
    by_contra hnot
    obtain ⟨p, hp⟩ := id hint
    have hAcompact : IsCompact (convexHull ℝ (s : Set E)) := s.finite_toSet.isCompact_convexHull ℝ
    obtain ⟨θ, hθ0, hθ1, hzA, hznot⟩ :=
      exists_crossing hAcompact hp hnot
    obtain ⟨t, hts, g, c, hfacet, hzt⟩ :=
      exists_isFacetIneq_of_notMem_interior hint hzA hznot
    have hex : ∃ q : (E →L[ℝ] ℝ) × ℝ, IsFacetIneq s t q.1 q.2 := ⟨(g, c), hfacet⟩
    have hchosen := facetData_spec hex
    have := lt_of_isFacetIneq_of_segment hchosen hp hθ0 hθ1 hzt
    exact absurd (hx t (Finset.mem_powerset.mpr hts)) (not_le.mpr this)

end PolytopeFace
end AffineTverberg
