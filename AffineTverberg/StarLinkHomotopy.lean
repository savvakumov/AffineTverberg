import AffineTverberg.StarLinkRetract

set_option linter.style.header false

/-!
# The punctured open star is homotopy equivalent to its link

This completes the existing ray retraction to a homotopy equivalence, using
the straight segment along each ray. The geometry, projection and inclusion
are the previously constructed ones. This identifies all local homology
groups with the actual closed-star link, not just a retract summand, for
the geometric duality argument.
-/

noncomputable section

open Set unitInterval

namespace AffineTverberg

variable {e : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
  {L : Finset (CoordinateSpace e)} {p : CoordinateSpace e}

private theorem half_ray_coeff_pos {s t : ℝ} (hs : 0 < s) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < (1 - t) * s + t / 2 := by
  rcases lt_or_eq_of_le ht.2 with h | h
  · have h1 : 0 < (1 - t) * s := mul_pos (by linarith) hs
    linarith [ht.1]
  · rw [h]
    norm_num

/-- The segment from a point of the punctured star to its half-radius link
projection never meets the apex or exits the open star. -/
theorem linkSegment_mem (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p)
    (x : ↥(puncturedOpenStar K L p)) (t : I) :
    (1 - (t : ℝ)) • (x : CoordinateSpace e) +
      (t : ℝ) • (linkInclusion hL hp (linkRetraction hL hp x) : CoordinateSpace e) ∈
        puncturedOpenStar K L p := by
  obtain ⟨y, hy, s, hs0, hs1, hxs⟩ :=
    exists_link_decomposition hL hp x.property.1.1 (fun h => x.property.2 h)
  have hslt : s < 1 := by
    apply lt_of_le_of_ne hs1
    intro hs
    have hxy : (x : CoordinateSpace e) = y := by rw [hxs, hs]; simp
    exact x.property.1.2 (hxy ▸ hy)
  have hproj : linkProj K L p (x : CoordinateSpace e) = y := by
    rw [hxs]
    exact linkProj_eq hL hp hy hs0 hs1
  have hincl : (linkInclusion hL hp (linkRetraction hL hp x) : CoordinateSpace e) =
      p + (1 / 2 : ℝ) • (y - p) := by
    change p + (1 / 2 : ℝ) • (linkProj K L p (x : CoordinateSpace e) - p) = _
    rw [hproj]
  let a : ℝ := (1 - (t : ℝ)) * s + (t : ℝ) / 2
  have ha0 : 0 < a := half_ray_coeff_pos hs0 t.property
  have ha1 : a < 1 := by
    have hgap := half_ray_coeff_pos (s := 1 - s) (by linarith) t.property
    dsimp [a]
    nlinarith
  have heq : (1 - (t : ℝ)) • (x : CoordinateSpace e) +
      (t : ℝ) • (linkInclusion hL hp (linkRetraction hL hp x) : CoordinateSpace e) =
      p + a • (y - p) := by
    rw [hxs, hincl]
    dsimp [a]
    module
  rw [heq]
  refine ⟨⟨mem_closedStar_of_ray hp.1 hy ha0.le ha1.le,
    notMem_closedStarLink_smul hL hp hy ha0.le ha1⟩, ?_⟩
  intro h
  have hvec : a • (y - p) = 0 := by
    have heq' : p + a • (y - p) = p := h
    exact add_left_cancel (heq'.trans (add_zero p).symm)
  have hyp : y = p := sub_eq_zero.mp ((smul_eq_zero.mp hvec).resolve_left ha0.ne')
  exact notMem_closedStarLink hL hp (hyp ▸ hy)

/-- The existing projection and half-radius inclusion compose to a map
homotopic to the identity through points of the punctured open star. -/
def linkRayHomotopy (hfin : K.faces.Finite) (hL : L ∈ K.faces)
    (hp : IsCarrierPoint K L p) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(puncturedOpenStar K L p))
      ((⟨linkInclusion hL hp, continuous_linkInclusion hL hp⟩ :
        C(↥(closedStarLink K L), ↥(puncturedOpenStar K L p))).comp
        ⟨linkRetraction hL hp, continuous_linkRetraction hfin hL hp⟩) where
  toFun z := ⟨(1 - (z.1 : ℝ)) • (z.2 : CoordinateSpace e) +
    (z.1 : ℝ) • (linkInclusion hL hp (linkRetraction hL hp z.2) : CoordinateSpace e),
      linkSegment_mem hL hp z.2 z.1⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.add
    · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp continuous_snd)
    · exact (continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp ((continuous_linkInclusion hL hp).comp
          ((continuous_linkRetraction hfin hL hp).comp continuous_snd)))
  map_zero_left x := by apply Subtype.ext; simp
  map_one_left x := by apply Subtype.ext; simp

/-- The actual closed-star link is homotopy equivalent to the punctured
open star, using exactly the previously constructed maps. -/
def puncturedOpenStarLinkHomotopyEquiv (hfin : K.faces.Finite) (hL : L ∈ K.faces)
    (hp : IsCarrierPoint K L p) :
    ContinuousMap.HomotopyEquiv ↥(puncturedOpenStar K L p) ↥(closedStarLink K L) where
  toFun := ⟨linkRetraction hL hp, continuous_linkRetraction hfin hL hp⟩
  invFun := ⟨linkInclusion hL hp, continuous_linkInclusion hL hp⟩
  left_inv := ⟨(linkRayHomotopy hfin hL hp).symm⟩
  right_inv := by
    have heq : (⟨linkRetraction hL hp, continuous_linkRetraction hfin hL hp⟩ :
        C(↥(puncturedOpenStar K L p), ↥(closedStarLink K L))).comp
        ⟨linkInclusion hL hp, continuous_linkInclusion hL hp⟩ = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro x
      exact linkRetraction_linkInclusion hL hp x
    rw [heq]

end AffineTverberg
