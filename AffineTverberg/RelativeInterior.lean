import AffineTverberg.UpperSubdivision

set_option linter.style.header false

/-!
# Relative interior points and the affine chart of a finite point set

A polytope which is not full dimensional has empty interior, so the
full-dimensional facet theory of `PolytopeHDescription.lean` cannot be applied
to it directly.  This file supplies the two tools needed to work *inside the
affine span*:

* `IsRelInt A p` — a *relative interior point* of a set `A`: a point of `A`
  from which one can move a positive distance directly away from any point of
  `A` and stay inside `A`.  This elementary segment formulation is exactly what
  the supporting-inequality arguments need:
  - `IsRelInt.eq_of_valid` — a valid inequality tight at a relative interior
    point is tight on all of `A`;
  - `IsRelInt.lt_of_valid` — a valid inequality which is somewhere strict is
    strict at every relative interior point.
* the *affine chart* `chartIncl p₀ W : W →ᵃ[ℝ] E`, `w ↦ p₀ + w`, of the
  direction submodule `W` of a finite set, with its affine retraction
  `chartRetr`, preservation of affine rank, and the resulting existence
  theorem `exists_isRelInt_convexHull`: **the convex hull of a nonempty finite
  set has a relative interior point.**

Nothing here is specific to the Tverberg development; these are the general
tools used by `RelativeFacet.lean` to produce a genuine facet system of a
polytope inside its own affine span.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace RelInt

open CayleyJoin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `p` is a *relative interior point* of `A`: it lies in `A`, and for every
`y ∈ A` the segment from `y` through `p` continues inside `A`. -/
def IsRelInt (A : Set E) (p : E) : Prop :=
  p ∈ A ∧ ∀ y ∈ A, ∃ ε : ℝ, 0 < ε ∧ p + ε • (p - y) ∈ A

theorem IsRelInt.mem {A : Set E} {p : E} (h : IsRelInt A p) : p ∈ A := h.1

/-- Interior points are relative interior points. -/
theorem isRelInt_of_mem_interior {A : Set E} {p : E} (hp : p ∈ interior A) :
    IsRelInt A p := by
  refine ⟨interior_subset hp, fun y _ ↦ ?_⟩
  have hcont : ContinuousAt (fun d : ℝ ↦ p + d • (p - y)) 0 := by fun_prop
  have h0 : interior A ∈ nhds ((fun d : ℝ ↦ p + d • (p - y)) 0) := by
    simpa using IsOpen.mem_nhds isOpen_interior hp
  have hmem : ∀ᶠ d in nhds (0 : ℝ), p + d • (p - y) ∈ interior A :=
    hcont.preimage_mem_nhds h0
  have hmem' : ∀ᶠ d in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      p + d • (p - y) ∈ interior A := hmem.filter_mono nhdsWithin_le_nhds
  obtain ⟨d, hdmem, hdpos⟩ := (hmem'.and self_mem_nhdsWithin).exists
  exact ⟨d, hdpos, interior_subset hdmem⟩

/-- **A valid inequality tight at a relative interior point is tight
everywhere.** -/
theorem IsRelInt.eq_of_valid {A : Set E} {p : E} (h : IsRelInt A p)
    {g : E →L[ℝ] ℝ} {c : ℝ} (hvalid : ∀ y ∈ A, g y ≤ c) (htight : g p = c) :
    ∀ y ∈ A, g y = c := by
  intro y hy
  obtain ⟨ε, hε, hmem⟩ := h.2 y hy
  have hle := hvalid _ hmem
  have hval : g (p + ε • (p - y)) = c + ε * (c - g y) := by
    simp only [map_add, map_smul, map_sub, smul_eq_mul, htight]
  rw [hval] at hle
  have hgy : c ≤ g y := by nlinarith
  exact le_antisymm (hvalid y hy) hgy

/-- **A valid inequality which is somewhere strict is strict at every relative
interior point.** -/
theorem IsRelInt.lt_of_valid {A : Set E} {p : E} (h : IsRelInt A p)
    {g : E →L[ℝ] ℝ} {c : ℝ} (hvalid : ∀ y ∈ A, g y ≤ c)
    (hproper : ∃ y ∈ A, g y < c) : g p < c := by
  rcases lt_or_eq_of_le (hvalid p h.1) with hlt | heq
  · exact hlt
  · obtain ⟨y, hy, hylt⟩ := hproper
    exact absurd (h.eq_of_valid hvalid heq y hy) (ne_of_lt hylt)

/-- Relative interior points are preserved by affine maps, provided the target
set is the image. -/
theorem IsRelInt.image_affine {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : W →ᵃ[ℝ] E) {A : Set W} {w : W} (h : IsRelInt A w) :
    IsRelInt (f '' A) (f w) := by
  refine ⟨⟨w, h.1, rfl⟩, ?_⟩
  rintro y ⟨u, hu, rfl⟩
  obtain ⟨ε, hε, hmem⟩ := h.2 u hu
  refine ⟨ε, hε, ⟨w + ε • (w - u), hmem, ?_⟩⟩
  have hsub : ∀ a b : W, f a - f b = f.linear (a - b) := by
    intro a b
    have := f.linearMap_vsub a b
    simpa using this.symm
  have h1 : f (w + ε • (w - u)) = f w + f.linear (ε • (w - u)) := by
    have := f.map_vadd w (ε • (w - u))
    simpa [add_comm] using this
  rw [h1, map_smul, ← hsub w u]

/-! ### The affine chart of a direction submodule -/

section Chart

variable [FiniteDimensional ℝ E]

/-- The affine chart `w ↦ p₀ + w` of a submodule `W` of `E`. -/
def chartIncl (p₀ : E) (W : Submodule ℝ E) : W →ᵃ[ℝ] E where
  toFun w := p₀ + (w : E)
  linear := W.subtype
  map_vadd' := by
    intro p v
    simp only [Submodule.coe_subtype, Submodule.coe_add, vadd_eq_add]
    abel

omit [FiniteDimensional ℝ E] in
@[simp]
theorem chartIncl_apply (p₀ : E) (W : Submodule ℝ E) (w : W) :
    chartIncl p₀ W w = p₀ + (w : E) := rfl

omit [FiniteDimensional ℝ E] in
@[simp]
theorem chartIncl_linear (p₀ : E) (W : Submodule ℝ E) :
    (chartIncl p₀ W).linear = W.subtype := rfl

/-- The affine retraction `x ↦ π (x - p₀)` associated with a complement of `W`. -/
def chartRetr (p₀ : E) (W K : Submodule ℝ E) (h : IsCompl W K) : E →ᵃ[ℝ] W where
  toFun x := W.projectionOnto K h (x - p₀)
  linear := W.projectionOnto K h
  map_vadd' := by
    intro p v
    have : v + p - p₀ = v + (p - p₀) := by abel
    simp [this]

omit [FiniteDimensional ℝ E] in
theorem chartRetr_chartIncl (p₀ : E) (W K : Submodule ℝ E) (h : IsCompl W K)
    (w : W) : chartRetr p₀ W K h (chartIncl p₀ W w) = w := by
  simp [chartRetr, chartIncl, Submodule.projectionOnto_apply_left]

/-- The chart preserves affine rank. -/
theorem arank_image_chartIncl (p₀ : E) (W : Submodule ℝ E) (A : Set W) :
    arank ((chartIncl p₀ W) '' A) = arank A := by
  obtain ⟨K, hK⟩ := Submodule.exists_isCompl W
  exact CompactConvexProjection.arank_image_eq_of_leftInvOn (chartIncl p₀ W)
    (chartRetr p₀ W K hK) (fun w _ ↦ chartRetr_chartIncl p₀ W K hK w)

open Classical in
/-- The chart of a finite set: the translated generators, viewed in the
direction submodule. -/
def chartFinset (p₀ : E) (W : Submodule ℝ E) (s : Finset E)
    (h : ∀ v ∈ s, v - p₀ ∈ W) : Finset W :=
  s.attach.image (fun v : {x : E // x ∈ s} ↦ (⟨(v.1 : E) - p₀, h v.1 v.2⟩ : W))

omit [FiniteDimensional ℝ E] in
theorem chartFinset_nonempty (p₀ : E) (W : Submodule ℝ E) {s : Finset E}
    (h : ∀ v ∈ s, v - p₀ ∈ W) (hs : s.Nonempty) :
    (chartFinset p₀ W s h).Nonempty := by
  classical
  obtain ⟨v, hv⟩ := hs
  exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨v, hv⟩)⟩

omit [FiniteDimensional ℝ E] in
/-- The image of the chart of a finite set is the original set. -/
theorem chartIncl_image_chartFinset (p₀ : E) (W : Submodule ℝ E) (s : Finset E)
    (h : ∀ v ∈ s, v - p₀ ∈ W) :
    (chartIncl p₀ W) '' ((chartFinset p₀ W s h : Finset W) : Set W) = (s : Set E) := by
  classical
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    simp only [chartFinset, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      Finset.mem_attach, true_and, Subtype.exists] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    have hxv : p₀ + ((v : E) - p₀) = v := by abel
    simpa [chartIncl, hxv] using hv
  · intro hx
    refine ⟨⟨x - p₀, h x hx⟩, ?_, ?_⟩
    · simp only [chartFinset, Finset.coe_image, Set.mem_image, Finset.mem_coe,
        Finset.mem_attach, true_and, Subtype.exists]
      exact ⟨x, hx, rfl⟩
    · simp [chartIncl]

end Chart

section RelIntExists

variable [FiniteDimensional ℝ E]

/-- **The flattening chart of a nonempty finite set.**  Every nonempty finite
set `s` becomes a *full-dimensional* finite set `s'` inside the direction
submodule of its affine span, via the affine chart `w ↦ p₀ + w`; moreover every
point of the affine span of `s` is in the image of the chart.  This is the
device that reduces the relative facet theory to the full-dimensional theory of
`PolytopeHDescription.lean`. -/
theorem exists_chart_data {s : Finset E} (hs : s.Nonempty) :
    ∃ (W : Submodule ℝ E) (p₀ : E) (s' : Finset W),
      (chartIncl p₀ W) '' ((s' : Finset W) : Set W) = (s : Set E) ∧
      (interior (convexHull ℝ ((s' : Finset W) : Set W))).Nonempty ∧
      (∀ x ∈ affineSpan ℝ (s : Set E), ∃ w : W, p₀ + (w : E) = x) ∧
      (∀ u ∈ vectorSpan ℝ (s : Set E), u ∈ W) := by
  classical
  obtain ⟨p₀, hp₀⟩ := hs
  set W : Submodule ℝ E := vectorSpan ℝ (s : Set E) with hW
  have hmemW : ∀ v ∈ s, v - p₀ ∈ W := by
    intro v hv
    have := vsub_mem_vectorSpan ℝ (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hp₀)
    simpa [hW] using this
  set s' : Finset W := chartFinset p₀ W s hmemW with hs'
  have himg : (chartIncl p₀ W) '' ((s' : Finset W) : Set W) = (s : Set E) :=
    chartIncl_image_chartFinset p₀ W s hmemW
  -- the chart of `s` spans the direction submodule
  have hspan : vectorSpan ℝ ((s' : Finset W) : Set W) = ⊤ := by
    have hmap : Submodule.map W.subtype (vectorSpan ℝ ((s' : Finset W) : Set W)) = W := by
      have := AffineMap.map_vectorSpan (chartIncl p₀ W)
        (s := ((s' : Finset W) : Set W))
      rw [chartIncl_linear] at this
      rw [this, himg, ← hW]
    have hinj : Function.Injective W.subtype := Submodule.injective_subtype W
    have htop : Submodule.map W.subtype (⊤ : Submodule ℝ W) = W := by
      simp [Submodule.map_top]
    exact Submodule.map_injective_of_injective hinj (by rw [hmap, htop])
  have hspanTop : affineSpan ℝ ((s' : Finset W) : Set W) = ⊤ := by
    have hne : (((s' : Finset W) : Set W)).Nonempty := by
      have hne' : (s' : Finset W).Nonempty := chartFinset_nonempty p₀ W hmemW ⟨p₀, hp₀⟩
      exact_mod_cast hne'
    have := AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ W W hne
    exact this.mpr hspan
  have hconv : Convex ℝ (convexHull ℝ ((s' : Finset W) : Set W)) := convex_convexHull ℝ _
  have hspanhull : affineSpan ℝ (convexHull ℝ ((s' : Finset W) : Set W)) = ⊤ := by
    rw [affineSpan_convexHull]; exact hspanTop
  refine ⟨W, p₀, s', himg, (hconv.interior_nonempty_iff_affineSpan_eq_top).2 hspanhull,
    ?_, fun u hu ↦ by simpa [hW] using hu⟩
  intro x hx
  have hdir : x -ᵥ p₀ ∈ (affineSpan ℝ (s : Set E)).direction :=
    AffineSubspace.vsub_mem_direction hx (subset_affineSpan ℝ _ (Finset.mem_coe.mpr hp₀))
  rw [direction_affineSpan] at hdir
  exact ⟨⟨x - p₀, by simpa [hW] using hdir⟩, by simp⟩

/-- **The convex hull of a nonempty finite set has a relative interior
point.** -/
theorem exists_isRelInt_convexHull {s : Finset E} (hs : s.Nonempty) :
    ∃ p, IsRelInt (convexHull ℝ (s : Set E)) p := by
  obtain ⟨W, p₀, s', himg, ⟨w, hw⟩, -, -⟩ := exists_chart_data hs
  refine ⟨chartIncl p₀ W w, ?_⟩
  have hrel : IsRelInt (convexHull ℝ ((s' : Finset W) : Set W)) w :=
    isRelInt_of_mem_interior hw
  have := hrel.image_affine (chartIncl p₀ W)
  rwa [AffineMap.image_convexHull, himg] at this

/-- **A relative interior point from which every direction of the affine span
can be followed for a while.**  This strengthening of
`exists_isRelInt_convexHull` is what a genericity argument needs: the relative
interior is not contained in finitely many proper affine subspaces because one
can move a little in an arbitrary direction of the span. -/
theorem exists_isRelInt_move {s : Finset E} (hs : s.Nonempty) :
    ∃ p, IsRelInt (convexHull ℝ (s : Set E)) p ∧
      ∀ u ∈ vectorSpan ℝ (s : Set E), ∃ ε₀ : ℝ, 0 < ε₀ ∧
        ∀ ε : ℝ, |ε| < ε₀ → IsRelInt (convexHull ℝ (s : Set E)) (p + ε • u) := by
  classical
  obtain ⟨W, p₀, s', himg, ⟨w, hw⟩, -, hWsub⟩ := exists_chart_data hs
  have hhull : (chartIncl p₀ W) '' convexHull ℝ ((s' : Finset W) : Set W)
      = convexHull ℝ (s : Set E) := by
    rw [AffineMap.image_convexHull, himg]
  refine ⟨chartIncl p₀ W w, ?_, ?_⟩
  · have hrel : IsRelInt (convexHull ℝ ((s' : Finset W) : Set W)) w :=
      isRelInt_of_mem_interior hw
    have := hrel.image_affine (chartIncl p₀ W)
    rwa [hhull] at this
  · intro u hu
    set u' : W := ⟨u, hWsub u hu⟩ with hu'
    have hcont : Continuous fun ε : ℝ ↦ w + ε • u' := by fun_prop
    have hpre : IsOpen ((fun ε : ℝ ↦ w + ε • u') ⁻¹'
        interior (convexHull ℝ ((s' : Finset W) : Set W))) :=
      hcont.isOpen_preimage _ isOpen_interior
    have hzero : (0 : ℝ) ∈ (fun ε : ℝ ↦ w + ε • u') ⁻¹'
        interior (convexHull ℝ ((s' : Finset W) : Set W)) := by
      simpa using hw
    obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.1 hpre 0 hzero
    refine ⟨ε₀, hε₀, fun ε hε ↦ ?_⟩
    have hmem : w + ε • u' ∈ interior (convexHull ℝ ((s' : Finset W) : Set W)) := by
      apply hball
      simpa [Real.dist_eq] using hε
    have hrel : IsRelInt (convexHull ℝ (s : Set E))
        (chartIncl p₀ W (w + ε • u')) := by
      have := (isRelInt_of_mem_interior hmem).image_affine (chartIncl p₀ W)
      rwa [hhull] at this
    simpa [chartIncl, hu', add_assoc] using hrel

end RelIntExists

end RelInt
end AffineTverberg
