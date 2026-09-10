import AffineTverberg.StarBoundaryCycle
import AffineTverberg.ModTwoBoundaryHomology
import AffineTverberg.BoundaryCarrierClosure
import AffineTverberg.BoundaryRidgeExistence
import AffineTverberg.BoundarySphereReduction

set_option linter.style.header false

/-!
# The combinatorial boundary of a simplicial ball is a sphere

The forward inclusion is already proved. For the reverse inclusion, a point
not in a boundary ridge has a carrier face with no boundary-ridge coface.
The mod-two boundary of the sum of its incident facets gives a nonzero top
cycle on the actual closed-star link, contradicting the local vanishing at
a topological boundary point. No PL or orientability assumption is added.
-/

noncomputable section

open Set Metric

namespace AffineTverberg

variable {e n : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-- Every point of a finite geometric complex has a carrier face. -/
theorem exists_carrierPoint (hfin : K.faces.Finite) {p : CoordinateSpace e}
    (hp : p ∈ K.space) : ∃ L ∈ K.faces, IsCarrierPoint K L p := by
  classical
  obtain ⟨s, hs, hps⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hp
  obtain ⟨L, hL, hmin⟩ := Set.exists_min_image
    {t | t ∈ K.faces ∧ p ∈ convexHull ℝ (t : Set (CoordinateSpace e))}
    (fun t : Finset (CoordinateSpace e) => t.card)
    (hfin.subset fun t ht => ht.1) ⟨s, hs, hps⟩
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro t ht hpt
  have hinter : p ∈ convexHull ℝ ((L ∩ t : Finset (CoordinateSpace e)) :
      Set (CoordinateSpace e)) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull hL.1 ht]
    exact ⟨hL.2, hpt⟩
  have hne : (L ∩ t).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hinter
    simp at hinter
  have hface := K.down_closed hL.1 (Finset.inter_subset_left (s₂ := t)) hne
  have heq : L ∩ t = L := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
    (hmin (L ∩ t) ⟨hface, hinter⟩)
  rw [← heq]
  exact Finset.inter_subset_right

namespace Simplicial

variable {W : Type} [Fintype W] [LinearOrder W] {q : W → CoordinateSpace e}
  {A : Finset (Finset W)}

omit [Fintype W] in
/-- The abstract boundary of a closed star realizes exactly the previously
constructed geometric closed-star link. -/
theorem geometricCarrier_starBoundaryFamily (hfin : K.faces.Finite)
    (hq : Function.Injective q) (hA : FaceClosed A)
    (hmem : ∀ s, s ∈ A ↔ s = ∅ ∨ Finset.image q s ∈ K.faces)
    (hpre : ∀ F ∈ K.faces, ∃ s ∈ A, Finset.image q s = F)
    {L : Finset W} (hL : L.Nonempty) :
    geometricCarrier (starBoundaryFamily A L) q = closedStarLink K (Finset.image q L) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨hsA, hsL, hnot⟩ := mem_starBoundaryFamily.mp hs
    have hne : (s ∪ L).Nonempty := hL.mono Finset.subset_union_right
    have hUL : Finset.image q (s ∪ L) ∈ K.faces :=
      ((hmem _).mp hsL).resolve_left hne.ne_empty
    obtain ⟨F, hF, hUF⟩ := exists_facet_superset hfin hUL
    obtain ⟨u, huL, hus⟩ := Finset.not_subset.mp hnot
    have hLsF : Finset.image q L ⊆ F :=
      (Finset.image_subset_image Finset.subset_union_right).trans hUF
    have hsF : Finset.image q s ⊆ F :=
      (Finset.image_subset_image Finset.subset_union_left).trans hUF
    have hsu : Finset.image q s ⊆ F.erase (q u) := by
      intro y hy
      refine Finset.mem_erase.mpr ⟨?_, hsF hy⟩
      intro hyu
      obtain ⟨v, hv, hvy⟩ := Finset.mem_image.mp hy
      exact hus ((hq (hvy.trans hyu)) ▸ hv)
    exact mem_closedStarLink_iff.mpr
      ⟨F, ⟨hF, hLsF⟩, q u, Finset.mem_image_of_mem q huL,
        convexHull_mono (by exact_mod_cast hsu) (by
          simpa only [Finset.coe_image] using hxs)⟩
  · intro hx
    obtain ⟨F, hF, u, hu, hxF⟩ := mem_closedStarLink_iff.mp hx
    obtain ⟨T, hT, hTF⟩ := hpre F (Geometry.SimplicialComplex.facets_subset hF.1)
    obtain ⟨v, hvL, rfl⟩ := Finset.mem_image.mp hu
    have hLT : L ⊆ T := (Finset.image_subset_image_iff hq).mp (hTF ▸ hF.2)
    have hvT := hLT hvL
    have hunion : T.erase v ∪ L = T := by
      apply Finset.Subset.antisymm
      · exact Finset.union_subset (Finset.erase_subset _ _) hLT
      · intro w hw
        by_cases h : w = v
        · exact Finset.mem_union_right _ (h ▸ hvL)
        · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩)
    refine Set.mem_iUnion₂.mpr ⟨T.erase v, ?_, ?_⟩
    · exact mem_starBoundaryFamily.mpr
        ⟨hA T hT _ (Finset.erase_subset _ _), by rwa [hunion],
          fun h => (Finset.notMem_erase v T) (h hvL)⟩
    · rw [← Finset.coe_image, Finset.image_erase hq, hTF]
      exact hxF

omit [Fintype W] in
/-- Cofacet counts of a faithful abstract presentation are exactly the
cardinalities of the actual geometric facet sets. -/
theorem facetCount_eq_ncard_facetsThrough (hfin : K.faces.Finite)
    (hpure : ∀ F ∈ K.facets, F.card = n + 1)
    (hq : Function.Injective q)
    (hmem : ∀ s, s ∈ A ↔ s = ∅ ∨ Finset.image q s ∈ K.faces)
    (hpre : ∀ F ∈ K.faces, ∃ s ∈ A, Finset.image q s = F)
    {f : Finset W} (hfcard : f.card = n) :
    facetCount A (n + 1) f = (facetsThrough K (Finset.image q f)).ncard := by
  classical
  have hcard (s : Finset W) : (Finset.image q s).card = s.card :=
    Finset.card_image_of_injective s hq
  have htop (s : Finset W) : s ∈ topSimplices A (n + 1) ↔
      Finset.image q s ∈ K.facets := by
    rw [mem_topSimplices, mem_facets_iff_card hfin hpure, hcard]
    constructor
    · rintro ⟨hs, hsz⟩
      rcases (hmem s).mp hs with rfl | hsK
      · simp at hsz
      · exact ⟨hsK, hsz⟩
    · rintro ⟨hsK, hsz⟩
      exact ⟨(hmem s).mpr (Or.inr hsK), hsz⟩
  rw [facetCount, Set.ncard_eq_toFinset_card _
    (facetsThrough_finite hfin (Finset.image q f))]
  refine Finset.card_bij (fun s _ => Finset.image q s) ?_ ?_ ?_
  · intro s hs
    obtain ⟨hs, hfs, -⟩ := Finset.mem_filter.mp hs
    exact (facetsThrough_finite hfin _).mem_toFinset.mpr
      ⟨(htop s).mp hs, Finset.image_subset_image hfs⟩
  · intro s hs t ht hst
    exact Finset.image_injective hq hst
  · intro F hF
    have hF' : F ∈ facetsThrough K (Finset.image q f) :=
      (facetsThrough_finite hfin _).mem_toFinset.mp hF
    obtain ⟨s, hs, himg⟩ := hpre F (Geometry.SimplicialComplex.facets_subset hF'.1)
    refine ⟨s, Finset.mem_filter.mpr ⟨(htop s).mpr (himg ▸ hF'.1), ?_, ?_⟩, himg⟩
    · apply (Finset.image_subset_image_iff hq).mp
      rw [himg]
      exact hF'.2
    · have hsz : s.card = n + 1 := by rw [← hcard s, himg]; exact hpure F hF'.1
      omega

end Simplicial

namespace IsSimplicialBall

open AffineTverberg.Simplicial AffineTverberg.Coefficients

/-- The reverse inclusion: a topological boundary point must lie in a
combinatorial boundary ridge, including points with lower-dimensional carriers. -/
theorem homologyBoundary_subset_boundaryCarrier (hball : IsSimplicialBall n K) (hn : 2 ≤ n) :
    homologyBoundary ↥K.space (n - 1) ⊆
      Subtype.val ⁻¹' (simplicialBoundaryCarrier K n) := by
  classical
  intro P hP
  by_contra hnot
  obtain ⟨G, hG, hpG⟩ := exists_carrierPoint hball.finite_faces P.property
  have hno : ∀ R, IsBoundaryRidge n K R → ¬ G ⊆ R := by
    intro R hR hGR
    apply hnot
    exact Set.mem_iUnion₂.mpr ⟨G, ⟨hG, R, hR, hGR⟩, hpG.1⟩
  obtain ⟨W, _, _, q, A, hq, hclosed, hgeom, hcarrier, hmem, hpre⟩ :=
    exists_finite_face_presentation hball.finite_faces
  obtain ⟨L, hL, hLG⟩ := hpre G hG
  have hLne : L.Nonempty := by
    have himgne : (Finset.image q L).Nonempty := by
      rw [hLG]
      exact K.nonempty_of_mem_faces hG
    exact Finset.image_nonempty.mp himgne
  have hcard (s : Finset W) : (Finset.image q s).card = s.card :=
    Finset.card_image_of_injective s hq
  have hmax : ∀ s ∈ A, s.card ≤ n + 1 := by
    intro s hs
    rcases (hmem s).mp hs with rfl | hsK
    · simp
    · rw [← hcard s]
      exact card_le_of_mem_faces hball.finite_faces hball.pure hsK
  have hface : ∃ F ∈ A, L ⊆ F ∧ F.card = n + 1 := by
    obtain ⟨F, hF, hGF⟩ := exists_facet_superset hball.finite_faces hG
    obtain ⟨T, hT, hTF⟩ := hpre F (Geometry.SimplicialComplex.facets_subset hF)
    refine ⟨T, hT, ?_, ?_⟩
    · apply (Finset.image_subset_image_iff hq).mp
      rw [hTF, hLG]
      exact hGF
    · rw [← hcard T, hTF]
      exact hball.pure F hF
  have heven : ∀ f ∈ A, L ⊆ f → f.card + 1 = n + 1 → Even (facetCount A (n + 1) f) := by
    intro f hf hLf hfc
    have hfn : f.card = n := by omega
    have hfne : f.Nonempty := Finset.card_pos.mp (by omega)
    have hfK : Finset.image q f ∈ K.faces :=
      ((hmem f).mp hf).resolve_left hfne.ne_empty
    have hfcard : (Finset.image q f).card = n := (hcard f).trans hfn
    rw [facetCount_eq_ncard_facetsThrough hball.finite_faces hball.pure hq hmem hpre hfn]
    rcases Nat.even_or_odd (facetsThrough K (Finset.image q f)).ncard with h | h
    · exact h
    · exfalso
      have hle := hball.ncard_facetsThrough_le_two hn hfK hfcard
      obtain ⟨k, hk⟩ := h
      have hone : (facetsThrough K (Finset.image q f)).ncard = 1 := by omega
      have hbr := (isBoundaryRidge_iff_ncard_eq_one hfK hfcard).mpr hone
      apply hno _ hbr
      rw [← hLG]
      exact Finset.image_subset_image hLf
  have hnonzero := not_isReducedAcyclicAt_starBoundaryFamily hclosed hmax hLne hface heven
  have hgeomLink : IsGeometricRealization (starBoundaryFamily A L) q :=
    isGeometricRealization_of_image_mem_faces hq (fun s hs hne =>
      ((hmem s).mp (mem_starBoundaryFamily.mp hs).1).resolve_left hne.ne_empty)
  have hlink : geometricCarrier (starBoundaryFamily A L) q = closedStarLink K G := by
    rw [geometricCarrier_starBoundaryFamily hball.finite_faces hq hclosed hmem hpre hLne, hLG]
  have hhomeo : ↥(barycentricCarrier (starBoundaryFamily A L)) ≃ₜ ↥(closedStarLink K G) :=
    (geometricRealizationHomeomorph hgeomLink).trans (Homeomorph.setCongr hlink)
  have hsub := hball.subsingleton_modTwo_homology_closedStarLink_of_mem_homologyBoundary
    hn hG hpG hP (n - 1) (by omega)
  have hbary : Subsingleton ((singularHomology (ZMod 2) (n - 1)).obj
      (barySpace (starBoundaryFamily A L))) :=
    (singularHomology_subsingleton_iff_of_homotopyEquiv
      (ZMod 2) hhomeo.toHomotopyEquiv (n - 1)).mpr hsub
  have hacyc : IsReducedAcyclicAt (ZMod 2) (starBoundaryFamily A L) n := by
    have hdeg : (n - 2) + 1 = n - 1 := by omega
    have h := Coefficients.isReducedAcyclicAt_of_subsingleton_singularHomology
      (ZMod 2) (faceClosed_starBoundaryFamily hclosed L) (n - 2) (hdeg ▸ hbary)
    convert h using 1; omega
  exact hnonzero (by simpa using hacyc)

/-- The boundary generated by ridges is exactly the boundary detected by
punctured homology, under the original topological-ball assumptions. -/
theorem boundaryCarrier_eq_homologyBoundary (hball : IsSimplicialBall n K) (hn : 2 ≤ n) :
    Subtype.val ⁻¹' (simplicialBoundaryCarrier K n) = homologyBoundary ↥K.space (n - 1) :=
  Set.Subset.antisymm (hball.boundaryCarrier_subset_homologyBoundary hn)
    (hball.homologyBoundary_subset_boundaryCarrier hn)

/-- The actual combinatorial boundary of a simplicial ball is a sphere. -/
def boundaryHomeomorphSphere (hball : IsSimplicialBall n K) (hn : 2 ≤ n) :
    ↥(simplicialBoundaryCarrier K n) ≃ₜ ↥(sphere (0 : CoordinateSpace n) 1) :=
  boundaryCarrierHomeomorphSphere hball hn (hball.boundaryCarrier_eq_homologyBoundary hn)

/-- The actual full boundary join has the sphere dimension used in the paper. -/
def fullBoundaryJoinHomeomorphSphere (hball : IsSimplicialBall n K) (hn : 2 ≤ n) (m : ℕ) :
    ↥(simplicialBoundaryJoinCarrier K n m) ≃ₜ
      ↥(sphere (0 : CoordinateSpace ((m + 1) * n)) 1) :=
  boundaryJoinHomeomorphSphere hball hn (hball.boundaryCarrier_eq_homologyBoundary hn) m

end IsSimplicialBall

end AffineTverberg
