import AffineTverberg.RidgeLocalStar

set_option linter.style.header false

/-!
# The closed star is a cone with apex a carrier point

Let `L` be a face of a finite geometric simplicial complex `K` and let `p` be a
carrier point of `L` (a point of the relative interior of the closed simplex of
`L`).  The *link* of the star

`closedStarLink K L = ⋃ F ∈ facetsThrough K L, ⋃ u ∈ L, convexHull (F.erase u)`

is a compact set avoiding `p`, and the closed star `closedStar K L` is exactly
the cone over it with apex `p`:

* `exists_link_decomposition` — every point of the closed star other than `p`
  is `p + t • (y - p)` for some `y` in the link and some `t ∈ (0, 1]`;
* `notMem_closedStarLink_smul` — a ray from `p` meets the link at most once, so
  in particular `p ∉ closedStarLink K L`;
* `link_ray_injective` — the resulting parameterisation is injective.

Everything is proved with explicit barycentric weights inside a single facet;
the only global input is the intersection axiom of a simplicial complex.
-/

noncomputable section

open Metric Set

namespace AffineTverberg

variable {e : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-! ### Barycentric weights -/

/-- The convex hull of a finset, described by weights. -/
theorem mem_convexHull_finset_iff {S : Finset (CoordinateSpace e)} {x : CoordinateSpace e} :
    x ∈ convexHull ℝ (S : Set (CoordinateSpace e)) ↔
      ∃ w : CoordinateSpace e → ℝ, (∀ y ∈ S, 0 ≤ w y) ∧ ∑ y ∈ S, w y = 1 ∧
        ∑ y ∈ S, w y • y = x := by
  rw [Finset.convexHull_eq]
  constructor
  · rintro ⟨w, hw, hsum, hx⟩
    refine ⟨w, hw, hsum, ?_⟩
    rw [Finset.centerMass_eq_of_sum_1 _ _ hsum] at hx
    simpa using hx
  · rintro ⟨w, hw, hsum, hx⟩
    refine ⟨w, hw, hsum, ?_⟩
    rw [Finset.centerMass_eq_of_sum_1 _ _ hsum]
    simpa using hx

/-- Weights on a subset extend by zero to weights on a larger finset. -/
theorem exists_extend_weights {S T : Finset (CoordinateSpace e)} (hST : S ⊆ T)
    {c : CoordinateSpace e → ℝ} {q : CoordinateSpace e}
    (hpos : ∀ u ∈ S, 0 ≤ c u) (hsum : ∑ u ∈ S, c u = 1) (hq : ∑ u ∈ S, c u • u = q) :
    ∃ c' : CoordinateSpace e → ℝ, (∀ u ∈ S, c' u = c u) ∧ (∀ w, w ∉ S → c' w = 0) ∧
      (∀ w, 0 ≤ c' w) ∧ ∑ w ∈ T, c' w = 1 ∧ ∑ w ∈ T, c' w • w = q := by
  classical
  refine ⟨fun w => if w ∈ S then c w else 0, fun u hu => by simp [hu],
    fun w hw => by simp [hw], fun w => ?_, ?_, ?_⟩
  · by_cases h : w ∈ S
    · simpa [h] using hpos w h
    · simp [h]
  · have h1 : ∑ w ∈ S, (if w ∈ S then c w else 0) =
        ∑ w ∈ T, (if w ∈ S then c w else 0) :=
      Finset.sum_subset hST fun w _ hw => by simp [hw]
    rw [← h1, ← hsum]
    exact Finset.sum_congr rfl fun u hu => by simp [hu]
  · have h1 : ∑ w ∈ S, (if w ∈ S then c w else 0) • w =
        ∑ w ∈ T, (if w ∈ S then c w else 0) • w :=
      Finset.sum_subset hST fun w _ hw => by simp [hw]
    rw [← h1, ← hq]
    exact Finset.sum_congr rfl fun u hu => by simp [hu]

/-- The barycentric coordinate functional of a vertex of an affinely independent
finset: it is `1` at the vertex and `0` at all the others. -/
theorem exists_baryCoord {F : Finset (CoordinateSpace e)}
    (hind : AffineIndependent ℝ ((↑) : ↑F → CoordinateSpace e))
    {u : CoordinateSpace e} (hu : u ∈ F) :
    ∃ lam : CoordinateSpace e →ᵃ[ℝ] ℝ, lam u = 1 ∧ ∀ w ∈ F.erase u, lam w = 0 := by
  obtain ⟨lam, h1, -, h0⟩ :=
    exists_vertexCoord hind hu (Finset.notMem_erase u F) (Finset.erase_subset u F)
  exact ⟨lam, h1, fun w hw => h0 w (subset_convexHull ℝ _ (by exact_mod_cast hw))⟩

/-- An affine functional evaluated on an affine combination. -/
theorem affineMap_sum_smul (lam : CoordinateSpace e →ᵃ[ℝ] ℝ)
    {S : Finset (CoordinateSpace e)} {w : CoordinateSpace e → ℝ}
    (hsum : ∑ y ∈ S, w y = 1) :
    lam (∑ y ∈ S, w y • y) = ∑ y ∈ S, w y * lam y := by
  have hdec : ∀ z : CoordinateSpace e, lam z = lam.linear z + lam 0 := by
    intro z
    have h := lam.map_vadd 0 z
    simpa [vadd_eq_add] using h
  calc lam (∑ y ∈ S, w y • y) = lam.linear (∑ y ∈ S, w y • y) + lam 0 := hdec _
    _ = (∑ y ∈ S, w y * lam.linear y) + lam 0 := by rw [map_sum]; simp
    _ = (∑ y ∈ S, w y * lam.linear y) + (∑ y ∈ S, w y) * lam 0 := by rw [hsum]; ring
    _ = ∑ y ∈ S, (w y * lam.linear y + w y * lam 0) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    _ = ∑ y ∈ S, w y * lam y :=
          Finset.sum_congr rfl fun y _ => by rw [hdec y]; ring

/-- An affine functional vanishing on a set vanishes on its convex hull. -/
theorem affineMap_eq_zero_of_mem_convexHull (lam : CoordinateSpace e →ᵃ[ℝ] ℝ)
    {S : Set (CoordinateSpace e)} (hS : ∀ w ∈ S, lam w = 0)
    {z : CoordinateSpace e} (hz : z ∈ convexHull ℝ S) : lam z = 0 := by
  have hconv : Convex ℝ (lam ⁻¹' ({0} : Set ℝ)) := (convex_singleton (0 : ℝ)).affine_preimage lam
  exact convexHull_min (fun w hw => hS w hw) hconv hz

/-! ### Positive weights at a carrier point -/

variable {L : Finset (CoordinateSpace e)} {p : CoordinateSpace e}

/-- At a carrier point all barycentric weights of the carrier face are
positive. -/
theorem IsCarrierPoint.exists_pos_weights (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p) :
    ∃ c : CoordinateSpace e → ℝ, (∀ u ∈ L, 0 < c u) ∧ ∑ u ∈ L, c u = 1 ∧
      ∑ u ∈ L, c u • u = p := by
  obtain ⟨c, hc0, hsum, hx⟩ := mem_convexHull_finset_iff.mp hp.1
  refine ⟨c, fun u hu => lt_of_le_of_ne (hc0 u hu) (fun h => ?_), hsum, hx⟩
  have hcu : c u = 0 := h.symm
  have hsum' : ∑ y ∈ L.erase u, c y = 1 := by
    rw [Finset.sum_erase _ hcu]; exact hsum
  have hpt : ∑ y ∈ L.erase u, c y • y = p := by
    rw [Finset.sum_erase _ (by rw [hcu]; simp)]; exact hx
  have hne : (L.erase u).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (L.erase u) with hemp | hne
    · rw [hemp] at hsum'; simp at hsum'
    · exact hne
  exact IsCarrierPoint.notMem_convexHull_erase hL hp hu hne
    (mem_convexHull_finset_iff.mpr ⟨c, fun y hy => hc0 y (Finset.mem_of_mem_erase hy),
      hsum', hpt⟩)

/-! ### The link of the closed star -/

/-- The link of the closed star of `L`: the union of the codimension one faces
of the facets through `L` obtained by deleting a vertex of `L`. -/
def closedStarLink (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))
    (L : Finset (CoordinateSpace e)) : Set (CoordinateSpace e) :=
  ⋃ F ∈ facetsThrough K L, ⋃ u ∈ L,
    convexHull ℝ ((F.erase u : Finset (CoordinateSpace e)) : Set (CoordinateSpace e))

theorem mem_closedStarLink_iff {x : CoordinateSpace e} :
    x ∈ closedStarLink K L ↔ ∃ F ∈ facetsThrough K L, ∃ u ∈ L,
      x ∈ convexHull ℝ ((F.erase u : Finset (CoordinateSpace e)) :
        Set (CoordinateSpace e)) := by
  simp [closedStarLink]

theorem closedStarLink_subset_closedStar :
    closedStarLink K L ⊆ closedStar K L := by
  intro x hx
  obtain ⟨F, hF, u, -, hxu⟩ := mem_closedStarLink_iff.mp hx
  exact convexHull_subset_closedStar hF
    (convexHull_mono (by exact_mod_cast Finset.erase_subset u F) hxu)

theorem isCompact_closedStarLink (hfin : K.faces.Finite) (L : Finset (CoordinateSpace e)) :
    IsCompact (closedStarLink K L) := by
  refine (facetsThrough_finite hfin L).isCompact_biUnion fun F _ => ?_
  refine L.finite_toSet.isCompact_biUnion fun u _ => ?_
  exact (F.erase u).finite_toSet.isCompact_convexHull ℝ

theorem isClosed_closedStarLink (hfin : K.faces.Finite) (L : Finset (CoordinateSpace e)) :
    IsClosed (closedStarLink K L) :=
  (isCompact_closedStarLink hfin L).isClosed

/-! ### A ray from the apex meets the link at most once -/

/-- **The ray uniqueness lemma.**  If `y` is in the link and `0 ≤ s < 1` then
the interior point `p + s • (y - p)` of the segment is not in the link. -/
theorem notMem_closedStarLink_smul (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p)
    {y : CoordinateSpace e} (hy : y ∈ closedStarLink K L) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    p + s • (y - p) ∉ closedStarLink K L := by
  classical
  obtain ⟨c, hcpos, hcsum, hcp⟩ := hp.exists_pos_weights hL
  obtain ⟨F, hF, u₀, hu₀, hyF⟩ := mem_closedStarLink_iff.mp hy
  have hLF : L ⊆ F := hF.2
  have hFfaces : F ∈ K.faces := Geometry.SimplicialComplex.facets_subset hF.1
  obtain ⟨c', hc'L, hc'out, hc'nonneg, hc'sum, hc'p⟩ :=
    exists_extend_weights hLF (fun u hu => (hcpos u hu).le) hcsum hcp
  obtain ⟨b0, hb00, hb0sum, hb0y⟩ := mem_convexHull_finset_iff.mp hyF
  obtain ⟨b, -, hbout, hbnonneg, hbsum, hby⟩ :=
    exists_extend_weights (Finset.erase_subset u₀ F) hb00 hb0sum hb0y
  obtain ⟨d, hddef⟩ : ∃ d : CoordinateSpace e → ℝ,
      ∀ w, d w = (1 - s) * c' w + s * b w := ⟨_, fun _ => rfl⟩
  have hdsum : ∑ w ∈ F, d w = 1 := by
    have h1 : ∑ w ∈ F, d w = (1 - s) * (∑ w ∈ F, c' w) + s * (∑ w ∈ F, b w) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun w _ => hddef w
    rw [h1, hc'sum, hbsum]; ring
  have hdz : ∑ w ∈ F, d w • w = p + s • (y - p) := by
    have h1 : ∑ w ∈ F, d w • w =
        (1 - s) • (∑ w ∈ F, c' w • w) + s • (∑ w ∈ F, b w • w) := by
      rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun w _ => by rw [hddef w]; module
    rw [h1, hc'p, hby]; module
  have hdpos : ∀ u ∈ L, 0 < d u := by
    intro u hu
    have h1 : 0 < (1 - s) * c' u := by
      rw [hc'L u hu]
      exact mul_pos (by linarith) (hcpos u hu)
    have h2 : 0 ≤ s * b u := mul_nonneg hs0 (hbnonneg u)
    rw [hddef u]; linarith
  have hdnonneg : ∀ w ∈ F, 0 ≤ d w := by
    intro w _
    have h1 : 0 ≤ (1 - s) * c' w := mul_nonneg (by linarith) (hc'nonneg w)
    have h2 : 0 ≤ s * b w := mul_nonneg hs0 (hbnonneg w)
    rw [hddef w]; linarith
  have hzF : p + s • (y - p) ∈ convexHull ℝ (F : Set (CoordinateSpace e)) :=
    mem_convexHull_finset_iff.mpr ⟨d, hdnonneg, hdsum, hdz⟩
  intro hzlink
  obtain ⟨G, hG, u₁, hu₁, hzG⟩ := mem_closedStarLink_iff.mp hzlink
  have hGfaces : G ∈ K.faces := Geometry.SimplicialComplex.facets_subset hG.1
  rcases Finset.eq_empty_or_nonempty (G.erase u₁) with hemp | hGne
  · rw [hemp] at hzG; simp at hzG
  have hGerase : G.erase u₁ ∈ K.faces :=
    K.down_closed hGfaces (Finset.erase_subset u₁ G) hGne
  have hint : p + s • (y - p) ∈ convexHull ℝ ((F : Set (CoordinateSpace e)) ∩
      ((G.erase u₁ : Finset (CoordinateSpace e)) : Set (CoordinateSpace e))) :=
    K.inter_subset_convexHull hFfaces hGerase ⟨hzF, hzG⟩
  obtain ⟨lam, hlam1, hlam0⟩ := exists_baryCoord (K.indep hFfaces) (hLF hu₁)
  have hlamz : lam (p + s • (y - p)) = d u₁ := by
    rw [← hdz, affineMap_sum_smul lam hdsum]
    rw [Finset.sum_eq_single u₁]
    · rw [hlam1, mul_one]
    · intro w hw hwne
      rw [hlam0 w (Finset.mem_erase.mpr ⟨hwne, hw⟩), mul_zero]
    · intro h
      exact absurd (hLF hu₁) h
  have hlamz0 : lam (p + s • (y - p)) = 0 := by
    refine affineMap_eq_zero_of_mem_convexHull lam ?_ hint
    rintro w ⟨hwF, hwG⟩
    have hwne : w ≠ u₁ := (Finset.mem_erase.mp (by exact_mod_cast hwG)).1
    exact hlam0 w (Finset.mem_erase.mpr ⟨hwne, by exact_mod_cast hwF⟩)
  have hpos := hdpos u₁ hu₁
  rw [hlamz] at hlamz0
  linarith

/-- The apex is not in the link. -/
theorem notMem_closedStarLink (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p) :
    p ∉ closedStarLink K L := by
  intro h
  have hcon := notMem_closedStarLink_smul hL hp h (le_refl (0 : ℝ)) (by norm_num)
  simp only [zero_smul, add_zero] at hcon
  exact hcon h

/-- **Injectivity of the cone parameterisation.** -/
theorem link_ray_injective (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p)
    {y y' : CoordinateSpace e} (hy : y ∈ closedStarLink K L) (hy' : y' ∈ closedStarLink K L)
    {t t' : ℝ} (ht : 0 < t) (ht' : 0 < t')
    (heq : p + t • (y - p) = p + t' • (y' - p)) : y = y' ∧ t = t' := by
  have key : ∀ (a b : CoordinateSpace e) (r r' : ℝ), a ∈ closedStarLink K L →
      b ∈ closedStarLink K L → 0 < r → 0 < r' → r ≤ r' →
      p + r • (a - p) = p + r' • (b - p) → a = b ∧ r = r' := by
    intro a b r r' ha hb hr hr' hrr heq'
    have hvec : r • (a - p) = r' • (b - p) := add_left_cancel heq'
    have hstep : (r / r') • (a - p) = b - p := by
      have hrw : (r / r') • (a - p) = r'⁻¹ • (r • (a - p)) := by
        rw [smul_smul]; congr 1; field_simp
      rw [hrw, hvec, smul_smul, inv_mul_cancel₀ (ne_of_gt hr'), one_smul]
    have hb' : b = p + (r / r') • (a - p) := by rw [hstep]; abel
    have hs0 : 0 ≤ r / r' := le_of_lt (div_pos hr hr')
    have hs1 : r / r' ≤ 1 := (div_le_one hr').mpr hrr
    have hone : r / r' = 1 := by
      by_contra hne
      have hlt : r / r' < 1 := lt_of_le_of_ne hs1 hne
      have hmem : p + (r / r') • (a - p) ∈ closedStarLink K L := by rw [← hb']; exact hb
      exact notMem_closedStarLink_smul hL hp ha hs0 hlt hmem
    refine ⟨?_, (div_eq_one_iff_eq (ne_of_gt hr')).mp hone⟩
    rw [hb', hone, one_smul]; abel
  rcases le_total t t' with h | h
  · exact key y y' t t' hy hy' ht ht' h heq
  · obtain ⟨h1, h2⟩ := key y' y t' t hy' hy ht' ht h heq.symm
    exact ⟨h1.symm, h2.symm⟩

/-! ### The cone decomposition -/

/-- **Every point of the closed star other than the apex lies on a ray to the
link.** -/
theorem exists_link_decomposition (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p)
    {x : CoordinateSpace e} (hx : x ∈ closedStar K L) (hxp : x ≠ p) :
    ∃ y ∈ closedStarLink K L, ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ x = p + t • (y - p) := by
  classical
  obtain ⟨c, hcpos, hcsum, hcp⟩ := hp.exists_pos_weights hL
  obtain ⟨F, hF, hxF⟩ := mem_closedStar_iff.mp hx
  have hLF : L ⊆ F := hF.2
  have hLne : L.Nonempty := K.nonempty_of_mem_faces hL
  obtain ⟨a, ha0, hasum, hax⟩ := mem_convexHull_finset_iff.mp hxF
  obtain ⟨c', hc'L, hc'out, hc'nonneg, hc'sum, hc'p⟩ :=
    exists_extend_weights hLF (fun u hu => (hcpos u hu).le) hcsum hcp
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = L.sup' hLne (fun u => 1 - a u / c u) := ⟨_, rfl⟩
  obtain ⟨u₀, hu₀L, hu₀⟩ := Finset.exists_mem_eq_sup' hLne (fun u => 1 - a u / c u)
  have hsuple : ∀ u ∈ L, 1 - a u / c u ≤ t := by
    intro u hu
    rw [htdef]
    exact Finset.le_sup' (f := fun u => 1 - a u / c u) hu
  have htle : t ≤ 1 := by
    rw [htdef]
    refine Finset.sup'_le hLne _ fun u hu => ?_
    have : 0 ≤ a u / c u := div_nonneg (ha0 u (hLF hu)) (hcpos u hu).le
    linarith
  have htpos : 0 < t := by
    by_contra hcon0
    have hcon : t ≤ 0 := not_lt.mp hcon0
    have hge : ∀ u ∈ L, c u ≤ a u := by
      intro u hu
      have h1 : 1 - a u / c u ≤ 0 := le_trans (hsuple u hu) hcon
      have h2 : 1 ≤ a u / c u := by linarith
      have := (le_div_iff₀ (hcpos u hu)).mp h2
      linarith
    have hLsum : ∑ u ∈ L, a u ≤ 1 := by
      rw [← hasum]
      exact Finset.sum_le_sum_of_subset_of_nonneg hLF fun w hw _ => ha0 w hw
    have hcle : ∑ u ∈ L, c u ≤ ∑ u ∈ L, a u := Finset.sum_le_sum hge
    have heqsum : ∑ u ∈ L, a u = 1 := le_antisymm hLsum (by rw [← hcsum]; exact hcle)
    have haeq : ∀ u ∈ L, a u = c u := by
      have h := (Finset.sum_eq_sum_iff_of_le hge).mp (by rw [heqsum, hcsum])
      exact fun u hu => (h u hu).symm
    have hzero : ∀ w ∈ F, w ∉ L → a w = 0 := by
      have hsplit : ∑ w ∈ F, a w = ∑ u ∈ L, a u + ∑ w ∈ F \ L, a w := by
        rw [← Finset.sum_union Finset.disjoint_sdiff]
        congr 1
        exact (Finset.union_sdiff_of_subset hLF).symm
      have hrest : ∑ w ∈ F \ L, a w = 0 := by
        rw [hasum, heqsum] at hsplit; linarith
      intro w hw hwL
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun v hv => ha0 v (Finset.mem_sdiff.mp hv).1)).mp hrest w
          (Finset.mem_sdiff.mpr ⟨hw, hwL⟩)
    apply hxp
    rw [← hax, ← hcp]
    rw [← Finset.sum_subset hLF (fun w hw hwL => by rw [hzero w hw hwL]; simp)]
    exact Finset.sum_congr rfl fun u hu => by rw [haeq u hu]
  have htne : t ≠ 0 := ne_of_gt htpos
  obtain ⟨b, hbdef⟩ : ∃ b : CoordinateSpace e → ℝ,
      ∀ w, b w = c' w + (a w - c' w) / t := ⟨_, fun _ => rfl⟩
  have hbsum : ∑ w ∈ F, b w = 1 := by
    have h1 : ∑ w ∈ F, b w = ∑ w ∈ F, (c' w + (a w - c' w) / t) :=
      Finset.sum_congr rfl fun w _ => hbdef w
    rw [h1, Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib,
      hasum, hc'sum]
    norm_num
  have hbnonneg : ∀ w ∈ F, 0 ≤ b w := by
    intro w hw
    by_cases hwL : w ∈ L
    · have hcw : c' w = c w := hc'L w hwL
      have hcwpos : 0 < c w := hcpos w hwL
      have hkey : (c w - a w) / c w ≤ t := by
        have hrw : (c w - a w) / c w = 1 - a w / c w := by field_simp
        rw [hrw]; exact hsuple w hwL
      have h1 : c w - a w ≤ t * c w := (div_le_iff₀ hcwpos).mp hkey
      have h2 : -(c w) ≤ (a w - c w) / t := by
        rw [le_div_iff₀ htpos]
        nlinarith
      rw [hbdef w, hcw]
      linarith
    · have hcw : c' w = 0 := hc'out w hwL
      rw [hbdef w, hcw, sub_zero, zero_add]
      exact div_nonneg (ha0 w hw) htpos.le
  have hbu₀ : b u₀ = 0 := by
    have hcw : c' u₀ = c u₀ := hc'L u₀ hu₀L
    have hcne : c u₀ ≠ 0 := ne_of_gt (hcpos u₀ hu₀L)
    have hteq : t = 1 - a u₀ / c u₀ := by rw [htdef]; exact hu₀
    have hval : (a u₀ - c u₀) / t = -(c u₀) := by
      rw [div_eq_iff htne, hteq]
      field_simp
      ring
    rw [hbdef u₀, hcw, hval]
    ring
  obtain ⟨y, hydef⟩ : ∃ y : CoordinateSpace e, y = ∑ w ∈ F, b w • w := ⟨_, rfl⟩
  have hylink : y ∈ closedStarLink K L := by
    refine mem_closedStarLink_iff.mpr ⟨F, hF, u₀, hu₀L, ?_⟩
    refine mem_convexHull_finset_iff.mpr
      ⟨b, fun w hw => hbnonneg w (Finset.mem_of_mem_erase hw), ?_, ?_⟩
    · rw [Finset.sum_erase _ hbu₀]; exact hbsum
    · rw [Finset.sum_erase _ (by rw [hbu₀]; simp)]; exact hydef.symm
  refine ⟨y, hylink, t, htpos, htle, ?_⟩
  have hyp : y - p = ∑ w ∈ F, (b w - c' w) • w := by
    rw [hydef, ← hc'p, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ => (sub_smul _ _ _).symm
  have hscale : t • (y - p) = ∑ w ∈ F, (a w - c' w) • w := by
    rw [hyp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [smul_smul]
    congr 1
    rw [hbdef w]
    field_simp
    ring
  rw [hscale, ← hax, ← hc'p, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun w _ => by module

/-- Conversely every point of a ray from the apex to the link is in the closed
star. -/
theorem mem_closedStar_of_ray
    (hpL : p ∈ convexHull ℝ (L : Set (CoordinateSpace e)))
    {y : CoordinateSpace e} (hy : y ∈ closedStarLink K L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    p + t • (y - p) ∈ closedStar K L := by
  have hstar := starConvex_closedStar (K := K) (L := L) hpL
  have hyS : y ∈ closedStar K L := closedStarLink_subset_closedStar hy
  have hmem := hstar hyS (a := 1 - t) (b := t) (by linarith) ht0 (by ring)
  have hEq : (1 - t) • p + t • y = p + t • (y - p) := by module
  rwa [hEq] at hmem

end AffineTverberg
