import AffineTverberg.BadEdgeSubdivisionGeometry

set_option linter.style.header false

/-!
# The bad-edge subdivision covers the join face

The recursive construction cones a face from the midpoint of its earliest bad
edge (or from its earliest vertex, when the face is deleted).  Geometrically
this splits the face into the two cones over the two facets opposite the
endpoints of that bad edge, which is why the subdivision covers the face.

## Main results

* `convexHull_eq_iUnion_sdRealize` : the realizations of the simplices of the
  subdivision of `S` cover exactly `conv (ρ '' S)`;
* `iUnion_good_sdRealize_eq` : the realizations of the *good* simplices cover
  exactly the deleted part of the face, i.e. the union of `conv (ρ '' T)` over
  the deleted subfaces `T ⊆ S`.  Together with `sdRealize_inter` and
  `affineIndependent_sdPt` this says that the good induced subcomplex of the
  subdivision triangulates the deleted join.
-/

open scoped BigOperators
open Set

namespace AffineTverberg
namespace BadEdge

variable {W V E : Type*} [Fintype W] [DecidableEq W] [LinearOrder W] [DecidableEq V]
variable [AddCommGroup E] [Module ℝ E]

omit [LinearOrder W] in
/-- Splitting a sum over the whole vertex type at two distinct vertices. -/
theorem sum_pair_split {M : Type*} [AddCommMonoid M] (f : W → M) {p q : W} (hpq : p ≠ q) :
    ∑ w, f w = f p + (f q + ∑ w ∈ (Finset.univ.erase p).erase q, f w) := by
  classical
  rw [← Finset.add_sum_erase _ f (Finset.mem_univ p),
    ← Finset.add_sum_erase _ f (Finset.mem_erase.mpr ⟨Ne.symm hpq, Finset.mem_univ q⟩)]

omit [LinearOrder W] in
/-- The convex combination `c` is rewritten as a combination of the midpoint of
the bad edge `{p, q}` and the vertices other than `p`, when `c p ≤ c q`. -/
theorem exists_cone_weights_pair (ρ : W → E) {S : Finset W} {c : W → ℝ}
    (hc : ConvexWeights S c) {p q : W} (hpq : p ≠ q) (hle : c p ≤ c q) :
    ∃ d : W → ℝ, (∀ w, 0 ≤ d w) ∧ (∀ w, w ∉ S.erase p → d w = 0) ∧
      2 * c p + ∑ w, d w = 1 ∧
      (2 * c p) • ((2 : ℝ)⁻¹ • ρ p + (2 : ℝ)⁻¹ • ρ q) + ∑ w, d w • ρ w
        = ∑ w, c w • ρ w := by
  classical
  set d : W → ℝ := fun w ↦ if w = p then 0 else if w = q then c q - c p else c w with hddef
  have hdp : d p = 0 := by simp [hddef]
  have hdq : d q = c q - c p := by simp [hddef, Ne.symm hpq]
  have hdother : ∀ w, w ≠ p → w ≠ q → d w = c w := by
    intro w h1 h2
    simp [hddef, h1, h2]
  have hcsum : c p + (c q + ∑ w ∈ (Finset.univ.erase p).erase q, c w) = 1 := by
    rw [← sum_pair_split c hpq]
    exact hc.sum_one
  have hrest : ∑ w ∈ (Finset.univ.erase p).erase q, d w =
      ∑ w ∈ (Finset.univ.erase p).erase q, c w := by
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    obtain ⟨hwq, hw'⟩ := Finset.mem_erase.mp hw
    obtain ⟨hwp, -⟩ := Finset.mem_erase.mp hw'
    exact hdother w hwp hwq
  have hrest' : ∑ w ∈ (Finset.univ.erase p).erase q, d w • ρ w =
      ∑ w ∈ (Finset.univ.erase p).erase q, c w • ρ w := by
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    obtain ⟨hwq, hw'⟩ := Finset.mem_erase.mp hw
    obtain ⟨hwp, -⟩ := Finset.mem_erase.mp hw'
    rw [hdother w hwp hwq]
  refine ⟨d, ?_, ?_, ?_, ?_⟩
  · intro w
    by_cases hwp : w = p
    · rw [hwp, hdp]
    · by_cases hwq : w = q
      · rw [hwq, hdq]; linarith
      · rw [hdother w hwp hwq]; exact hc.nonneg w
  · intro w hw
    by_cases hwp : w = p
    · rw [hwp, hdp]
    · have hwS : w ∉ S := fun hcon ↦ hw (Finset.mem_erase.mpr ⟨hwp, hcon⟩)
      by_cases hwq : w = q
      · have hcq : c q = 0 := hc.support q (by rwa [hwq] at hwS)
        have hcp : c p = 0 := le_antisymm (by rw [← hcq]; exact hle) (hc.nonneg p)
        rw [hwq, hdq, hcq, hcp, sub_zero]
      · rw [hdother w hwp hwq]
        exact hc.support w hwS
  · rw [sum_pair_split d hpq, hdp, hdq, hrest]
    linarith
  · rw [sum_pair_split (fun w ↦ d w • ρ w) hpq, sum_pair_split (fun w ↦ c w • ρ w) hpq]
    rw [hdp, hdq, hrest', zero_smul, smul_add, smul_smul, smul_smul,
      show (2 * c p) * (2 : ℝ)⁻¹ = c p by ring, sub_smul]
    abel

/-- Every point of a nonempty join face is a convex combination of the apex
realization and the vertices of one of the two facets opposite the apex. -/
theorem exists_cone_decomposition (orig : W → V) (ρ : W → E) {S : Finset W}
    (hS : S.Nonempty) {x : E} (hx : x ∈ convexHull ℝ (ρ '' (S : Set W))) :
    ∃ u ∈ apexSet orig S, ∃ t : ℝ, ∃ d : W → ℝ,
      0 ≤ t ∧ (∀ w, 0 ≤ d w) ∧ (∀ w, w ∉ S.erase u → d w = 0) ∧
        t + ∑ w, d w = 1 ∧
        t • sdPt ρ (apexSet orig S) + ∑ w, d w • ρ w = x := by
  classical
  obtain ⟨c, hc, rfl⟩ := (mem_convexHull_image_iff ρ S _).mp hx
  by_cases hbad : (badElts orig S).Nonempty
  · obtain ⟨p, q, hpair, hpq, -, hpS, hqS⟩ := exists_apexSet_pair hbad
    rcases le_total (c p) (c q) with hle | hle
    · obtain ⟨d, hd0, hdsupp, hdsum, hdcomb⟩ := exists_cone_weights_pair ρ hc hpq hle
      refine ⟨p, by rw [hpair]; simp, 2 * c p, d, by linarith [hc.nonneg p],
        hd0, hdsupp, hdsum, ?_⟩
      rw [hpair, sdPt_pair ρ hpq]
      exact hdcomb
    · obtain ⟨d, hd0, hdsupp, hdsum, hdcomb⟩ :=
        exists_cone_weights_pair ρ hc (Ne.symm hpq) hle
      refine ⟨q, by rw [hpair]; simp, 2 * c q, d, by linarith [hc.nonneg q],
        hd0, hdsupp, hdsum, ?_⟩
      rw [hpair, Finset.pair_comm p q, sdPt_pair ρ (Ne.symm hpq)]
      exact hdcomb
  · rw [Finset.not_nonempty_iff_eq_empty] at hbad
    set v := S.min' hS with hv
    have hvS : v ∈ S := Finset.min'_mem _ _
    have hapex : apexSet orig S = {v} := apexSet_of_deleted hbad hS
    refine ⟨v, by rw [hapex]; simp, c v, fun w ↦ if w = v then 0 else c w,
      hc.nonneg v, ?_, ?_, ?_, ?_⟩
    · intro w
      by_cases hwv : w = v
      · simp [hwv]
      · simp only [hwv, ↓reduceIte]
        exact hc.nonneg w
    · intro w hw
      by_cases hwv : w = v
      · simp [hwv]
      · simp only [hwv, ↓reduceIte]
        exact hc.support w fun hcon ↦ hw (Finset.mem_erase.mpr ⟨hwv, hcon⟩)
    · rw [← Finset.add_sum_erase _ (fun w ↦ if w = v then (0 : ℝ) else c w) (Finset.mem_univ v),
        ite_eq_left rfl, zero_add]
      have hrest : ∑ w ∈ Finset.univ.erase v, (if w = v then (0 : ℝ) else c w) =
          ∑ w ∈ Finset.univ.erase v, c w :=
        Finset.sum_congr rfl fun w hw ↦ by rw [ite_eq_right (Finset.ne_of_mem_erase hw)]
      rw [hrest]
      have := hc.sum_one
      rw [← Finset.add_sum_erase _ c (Finset.mem_univ v)] at this
      linarith
    · rw [hapex, sdPt_singleton]
      rw [← Finset.add_sum_erase _ (fun w ↦ (if w = v then (0 : ℝ) else c w) • ρ w)
        (Finset.mem_univ v), ite_eq_left rfl, zero_smul, zero_add]
      have hrest : ∑ w ∈ Finset.univ.erase v, (if w = v then (0 : ℝ) else c w) • ρ w =
          ∑ w ∈ Finset.univ.erase v, c w • ρ w :=
        Finset.sum_congr rfl fun w hw ↦ by rw [ite_eq_right (Finset.ne_of_mem_erase hw)]
      rw [hrest, ← Finset.add_sum_erase _ (fun w ↦ c w • ρ w) (Finset.mem_univ v)]

/-- **The subdivision covers the face.** -/
theorem convexHull_subset_iUnion_sdRealize (orig : W → V) (ρ : W → E) (S : Finset W) :
    convexHull ℝ (ρ '' (S : Set W)) ⊆ ⋃ σ ∈ sdFaces orig S, sdRealize ρ σ := by
  classical
  induction S using Finset.strongInduction with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simp
    · intro x hx
      obtain ⟨u, hu, t, d, ht0, hd0, hdsupp, hsum, hcomb⟩ :=
        exists_cone_decomposition orig ρ hS hx
      set a := apexSet orig S with ha
      have huS : u ∈ S := apexSet_subset orig S hu
      have hlt : S.erase u ⊂ S := Finset.erase_ssubset huS
      have hempty : (∅ : Finset (Finset W)) ∈ sdBase orig S :=
        mem_sdBase.mpr ⟨u, hu, empty_mem_sdFaces orig _⟩
      by_cases ht1 : t = 1
      · have hd : ∀ w, d w = 0 := by
          intro w
          have hsum0 : ∑ w, d w = 0 := by rw [ht1] at hsum; linarith
          exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ hd0 i)).mp hsum0 w
            (Finset.mem_univ w)
        have hxa : x = sdPt ρ a := by
          rw [← hcomb, ht1, one_smul, Finset.sum_congr rfl (fun w _ ↦ by
            rw [hd w, zero_smul]), Finset.sum_const_zero, add_zero]
        refine Set.mem_iUnion₂.mpr ⟨({a} : Finset (Finset W)), ?_, ?_⟩
        · exact (mem_sdFaces_iff hS).mpr (Or.inr ⟨∅, hempty, rfl⟩)
        · rw [hxa]
          exact sdPt_mem_sdRealize (Finset.mem_singleton_self a)
      · have htlt : t < 1 := by
          have : 0 ≤ ∑ w, d w := Finset.sum_nonneg fun i _ ↦ hd0 i
          rcases lt_or_eq_of_le (by linarith : t ≤ 1) with h | h
          · exact h
          · exact absurd h ht1
        have hpos : 0 < 1 - t := by linarith
        set y := (1 - t)⁻¹ • ∑ w, d w • ρ w with hy
        have hymem : y ∈ convexHull ℝ (ρ '' ((S.erase u : Finset W) : Set W)) := by
          rw [hy, Finset.smul_sum]
          have : ∀ w, (1 - t)⁻¹ • (d w • ρ w) = ((1 - t)⁻¹ * d w) • ρ w :=
            fun w ↦ by rw [smul_smul]
          rw [Finset.sum_congr rfl (fun w _ ↦ this w)]
          refine sum_smul_mem_convexHull_image ρ ⟨fun w ↦ ?_, fun w hw ↦ ?_, ?_⟩
          · exact mul_nonneg (le_of_lt (inv_pos.mpr hpos)) (hd0 w)
          · rw [hdsupp w hw, mul_zero]
          · rw [← Finset.mul_sum, show ∑ w, d w = 1 - t by linarith,
              inv_mul_cancel₀ (ne_of_gt hpos)]
        obtain ⟨τ, hτ, hy'⟩ := Set.mem_iUnion₂.mp (ih _ hlt hymem)
        refine Set.mem_iUnion₂.mpr ⟨insert a τ, ?_, ?_⟩
        · exact (mem_sdFaces_iff hS).mpr (Or.inr ⟨τ, mem_sdBase.mpr ⟨u, hu, hτ⟩, rfl⟩)
        · have hby : sdPt ρ a ∈ sdRealize ρ (insert a τ) :=
            sdPt_mem_sdRealize (Finset.mem_insert_self _ _)
          have hyy : y ∈ sdRealize ρ (insert a τ) :=
            sdRealize_mono (Finset.subset_insert _ _) hy'
          have hx' : x = t • sdPt ρ a + (1 - t) • y := by
            rw [hy, smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul, hcomb]
          rw [hx']
          exact (sdRealize_convex ρ (insert a τ)) hby hyy ht0 (le_of_lt hpos) (by ring)

/-- **The subdivision is a subdivision of the face.** -/
theorem convexHull_eq_iUnion_sdRealize (orig : W → V) (ρ : W → E) (S : Finset W) :
    (⋃ σ ∈ sdFaces orig S, sdRealize ρ σ) = convexHull ℝ (ρ '' (S : Set W)) := by
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun σ hσ ↦ sdRealize_subset_convexHull orig hσ
  · exact convexHull_subset_iUnion_sdRealize orig ρ S

omit [LinearOrder W] in
/-- The realization of an undivided simplex is the convex hull of its
vertices. -/
theorem sdRealize_sdSimplexOf (ρ : W → E) (T : Finset W) :
    sdRealize ρ (sdSimplexOf T) = convexHull ℝ (ρ '' (T : Set W)) := by
  have himg : sdPt ρ '' ((sdSimplexOf T : Finset (Finset W)) : Set (Finset W)) =
      ρ '' (T : Set W) := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hs)
      exact ⟨u, hu, (sdPt_singleton ρ u).symm⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨{u}, by exact_mod_cast Finset.mem_image_of_mem _ hu, sdPt_singleton ρ u⟩
  rw [sdRealize, himg]

/-- **The good induced subcomplex triangulates the deleted join.**  The
realizations of the simplices of the subdivision of `S` all of whose vertices
are good cover exactly the union of the deleted subfaces of `S`. -/
theorem iUnion_good_sdRealize_eq (orig : W → V) (ρ : W → E) (S : Finset W) :
    (⋃ σ ∈ {σ : Finset (Finset W) | σ ∈ sdFaces orig S ∧ ∀ s ∈ σ, IsGoodSdVertex s},
        sdRealize ρ σ) =
      ⋃ T ∈ {T : Finset W | T ⊆ S ∧ IsDeletedFace orig T},
        convexHull ℝ (ρ '' (T : Set W)) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨σ, hσ, hxσ⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨T, hTS, hTdel, rfl⟩ := (good_mem_sdFaces_iff orig S).mp hσ
    exact Set.mem_iUnion₂.mpr ⟨T, ⟨hTS, hTdel⟩, by rwa [sdRealize_sdSimplexOf] at hxσ⟩
  · intro hx
    obtain ⟨T, ⟨hTS, hTdel⟩, hxT⟩ := Set.mem_iUnion₂.mp hx
    refine Set.mem_iUnion₂.mpr ⟨sdSimplexOf T,
      (good_mem_sdFaces_iff orig S).mpr ⟨T, hTS, hTdel, rfl⟩, ?_⟩
    rwa [sdRealize_sdSimplexOf]

end BadEdge
end AffineTverberg
