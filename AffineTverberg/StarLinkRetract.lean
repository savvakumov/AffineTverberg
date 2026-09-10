import AffineTverberg.StarConeStructure

set_option linter.style.header false

/-!
# The link is a retract of the punctured open star

Continuing `AffineTverberg.StarConeStructure`, let `p` be a carrier point of a
face `L` of a finite geometric simplicial complex.  The *open star*

`openStarCone K L = closedStar K L \ closedStarLink K L`

is an open, star convex (hence contractible) neighbourhood of `p` inside the
polyhedron, and the punctured open star retracts continuously onto the link:
`linkProj` sends a point to the unique link point on its ray from `p`, and its
continuity is proved by compactness of the cone parameter space.

Consequently, for a simplicial ball of dimension `n ≥ 2`, the link of any
carrier point has homology of rank at most one in degree `n - 1`
(`IsSimplicialBall.finrank_homology_closedStarLink_le_one`).  Combined with the
combinatorial lower bound of `LinkJoinRank` this is the local homology
computation at a ridge.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric Set

namespace AffineTverberg

variable {e : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
  {L : Finset (CoordinateSpace e)} {p : CoordinateSpace e}

/-! ### Retracts and singular homology -/

/-- If `X` is a retract of `Y` then singular homology of `X` injects into that
of `Y`. -/
theorem injective_realSingularHomology_of_retract {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (i : C(X, Y)) (r : C(Y, X)) (hri : ∀ x, r (i x) = x) (n : ℕ) :
    Function.Injective ((realSingularHomology n).map (TopCat.ofHom i)).hom := by
  have hcomp : (TopCat.ofHom i ≫ TopCat.ofHom r) = 𝟙 (TopCat.of X) := by
    apply TopCat.hom_ext
    ext x
    exact hri x
  have hmap : (realSingularHomology n).map (TopCat.ofHom i) ≫
      (realSingularHomology n).map (TopCat.ofHom r) = 𝟙 _ := by
    rw [← Functor.map_comp, hcomp]
    exact (realSingularHomology n).map_id _
  intro a b hab
  have h1 := congrArg (fun z => ((realSingularHomology n).map (TopCat.ofHom r)).hom z) hab
  have h2 : ∀ z, ((realSingularHomology n).map (TopCat.ofHom r)).hom
      (((realSingularHomology n).map (TopCat.ofHom i)).hom z) = z := by
    intro z
    have := congrArg (fun (g : (realSingularHomology n).obj (TopCat.of X) ⟶
      (realSingularHomology n).obj (TopCat.of X)) => g.hom z) hmap
    simpa using this
  rw [h2 a, h2 b] at h1
  exact h1

/-! ### The cone map -/

/-- The cone map from the parameter space: `(y, t) ↦ p + t • (y - p)`. -/
def coneMap (p : CoordinateSpace e) : CoordinateSpace e × ℝ → CoordinateSpace e :=
  fun z => p + z.2 • (z.1 - p)

theorem continuous_coneMap (p : CoordinateSpace e) : Continuous (coneMap p) := by
  unfold coneMap
  fun_prop

theorem isCompact_coneMap_image {Z : Set (CoordinateSpace e)} (hZ : IsCompact Z)
    (p : CoordinateSpace e) :
    IsCompact (coneMap p '' (Z ×ˢ Set.Icc (0 : ℝ) 1)) :=
  (hZ.prod isCompact_Icc).image (continuous_coneMap p)

/-! ### The open star -/

/-- The open star of `L`: the closed star with its link removed. -/
def openStarCone (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))
    (L : Finset (CoordinateSpace e)) : Set (CoordinateSpace e) :=
  closedStar K L \ closedStarLink K L

theorem openStarCone_subset_space : openStarCone K L ⊆ K.space :=
  fun _ hx => closedStar_subset_space L hx.1

/-- A point of the open star lies only in faces containing `L`. -/
theorem faces_subset_of_mem_openStarCone {x : CoordinateSpace e} (hx : x ∈ openStarCone K L)
    {G : Finset (CoordinateSpace e)} (hG : G ∈ K.faces)
    (hxG : x ∈ convexHull ℝ (G : Set (CoordinateSpace e))) : L ⊆ G := by
  obtain ⟨F, hF, hxF⟩ := mem_closedStar_iff.mp hx.1
  have hFfaces : F ∈ K.faces := Geometry.SimplicialComplex.facets_subset hF.1
  intro u hu
  by_contra huG
  have hint : x ∈ convexHull ℝ ((F : Set (CoordinateSpace e)) ∩
      (G : Set (CoordinateSpace e))) := K.inter_subset_convexHull hFfaces hG ⟨hxF, hxG⟩
  have hsub : (F : Set (CoordinateSpace e)) ∩ (G : Set (CoordinateSpace e)) ⊆
      ((F.erase u : Finset (CoordinateSpace e)) : Set (CoordinateSpace e)) := by
    rintro w ⟨hwF, hwG⟩
    have hwu : w ≠ u := fun h => huG (h ▸ hwG)
    exact_mod_cast Finset.mem_erase.mpr ⟨hwu, by exact_mod_cast hwF⟩
  exact hx.2 (mem_closedStarLink_iff.mpr ⟨F, hF, u, hu, convexHull_mono hsub hint⟩)

/-- The open star is open in the polyhedron. -/
theorem isOpen_preimage_openStarCone (hfin : K.faces.Finite) :
    IsOpen (Subtype.val ⁻¹' (openStarCone K L) : Set ↥K.space) := by
  rw [Metric.isOpen_iff]
  intro q hq
  have hq' : (q : CoordinateSpace e) ∈ openStarCone K L := hq
  obtain ⟨ε₁, hε₁, h1⟩ := exists_localRadius hfin (q : CoordinateSpace e)
  have hΛclosed : IsClosed (closedStarLink K L) := isClosed_closedStarLink hfin L
  obtain ⟨ε₂, hε₂, h2⟩ :=
    Metric.isOpen_iff.mp hΛclosed.isOpen_compl (q : CoordinateSpace e) hq'.2
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun z hz => ?_⟩
  have hzd : dist (z : CoordinateSpace e) (q : CoordinateSpace e) < min ε₁ ε₂ := by
    have := Metric.mem_ball.mp hz
    simpa [Subtype.dist_eq] using this
  obtain ⟨s, hs, hqs, hzs⟩ := h1 (z : CoordinateSpace e) z.property
    (by rw [← dist_eq_norm]; exact lt_of_lt_of_le hzd (min_le_left _ _))
  have hLs : L ⊆ s := faces_subset_of_mem_openStarCone hq' hs hqs
  obtain ⟨F, hF, hsF⟩ := exists_facet_superset hfin hs
  refine ⟨mem_closedStar_iff.mpr ⟨F, ⟨hF, hLs.trans hsF⟩,
    convexHull_mono (by exact_mod_cast hsF) hzs⟩, ?_⟩
  exact h2 (Metric.mem_ball.mpr (lt_of_lt_of_le hzd (min_le_right _ _)))

/-- The open star is star convex about the carrier point. -/
theorem starConvex_openStarCone (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p) :
    StarConvex ℝ p (openStarCone K L) := by
  intro y hy a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  have hrw : a • p + b • y = p + b • (y - p) := by
    have : a = 1 - b := by linarith
    rw [this]; module
  rw [hrw]
  by_cases hyp : y = p
  · subst hyp
    simpa using hy
  · obtain ⟨z, hz, t, ht0, ht1, hxz⟩ := exists_link_decomposition hL hp hy.1 hyp
    have htne : t ≠ 1 := by
      intro h
      subst h
      simp only [one_smul] at hxz
      have : y = z := by rw [hxz]; abel
      exact hy.2 (this ▸ hz)
    have htlt : t < 1 := lt_of_le_of_ne ht1 htne
    have hrw2 : p + b • (y - p) = p + (b * t) • (z - p) := by
      rw [hxz]
      module
    rw [hrw2]
    refine ⟨mem_closedStar_of_ray hp.1 hz (mul_nonneg hb ht0.le) ?_, ?_⟩
    · calc b * t ≤ 1 * t := by nlinarith
        _ ≤ 1 := by linarith
    · refine notMem_closedStarLink_smul hL hp hz (mul_nonneg hb ht0.le) ?_
      calc b * t ≤ 1 * t := by nlinarith
        _ = t := one_mul t
        _ < 1 := htlt

theorem mem_openStarCone_apex (hfin : K.faces.Finite) (hL : L ∈ K.faces)
    (hp : IsCarrierPoint K L p) : p ∈ openStarCone K L :=
  ⟨mem_closedStar_of_isCarrierPoint hfin hL hp, notMem_closedStarLink hL hp⟩

/-! ### The link projection -/

open Classical in
/-- The projection of a point of the punctured star onto the link, along the ray
from the apex `p`. -/
def linkProj (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))
    (L : Finset (CoordinateSpace e)) (p x : CoordinateSpace e) : CoordinateSpace e :=
  Classical.epsilon fun y =>
    y ∈ closedStarLink K L ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ x = p + t • (y - p)

theorem linkProj_spec {x : CoordinateSpace e}
    (h : ∃ y, y ∈ closedStarLink K L ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ x = p + t • (y - p)) :
    linkProj K L p x ∈ closedStarLink K L ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ x = p + t • (linkProj K L p x - p) :=
  Classical.epsilon_spec h

/-- Uniqueness of the ray decomposition identifies the projection. -/
theorem linkProj_eq (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p)
    {y : CoordinateSpace e} (hy : y ∈ closedStarLink K L) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    linkProj K L p (p + t • (y - p)) = y := by
  have h : ∃ z, z ∈ closedStarLink K L ∧
      ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ p + t • (y - p) = p + s • (z - p) := ⟨y, hy, t, ht0, ht1, rfl⟩
  obtain ⟨hmem, s, hs0, -, hs⟩ := linkProj_spec (K := K) (L := L) (p := p) h
  exact (link_ray_injective hL hp hmem hy hs0 ht0 hs.symm).1

/-- Membership in the image of the cone map detects the projection. -/
theorem mem_coneMap_image_iff (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p)
    {Z : Set (CoordinateSpace e)} (hZ : Z ⊆ closedStarLink K L)
    {x : CoordinateSpace e} (hx : x ∈ closedStar K L) (hxp : x ≠ p) :
    x ∈ coneMap p '' (Z ×ˢ Set.Icc (0 : ℝ) 1) ↔ linkProj K L p x ∈ Z := by
  constructor
  · rintro ⟨⟨z, s⟩, hzs, hzx⟩
    have hz : z ∈ Z := hzs.1
    have hs : (0 : ℝ) ≤ s ∧ s ≤ 1 := hzs.2
    have hzx' : x = p + s • (z - p) := hzx.symm
    have hs0 : 0 < s := by
      rcases lt_or_eq_of_le hs.1 with h | h
      · exact h
      · exact absurd (by rw [hzx', ← h]; simp) hxp
    rw [hzx', linkProj_eq hL hp (hZ hz) hs0 hs.2]
    exact hz
  · intro hmem
    obtain ⟨y, hy, t, ht0, ht1, hxt⟩ := exists_link_decomposition hL hp hx hxp
    have hproj : linkProj K L p x = y := by rw [hxt]; exact linkProj_eq hL hp hy ht0 ht1
    exact ⟨(y, t), ⟨hproj ▸ hmem, ⟨ht0.le, ht1⟩⟩, hxt.symm⟩

/-! ### Continuity of the projection -/

/-- The punctured open star. -/
def puncturedOpenStar (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))
    (L : Finset (CoordinateSpace e)) (p : CoordinateSpace e) : Set (CoordinateSpace e) :=
  openStarCone K L \ {p}

theorem puncturedOpenStar_subset_space : puncturedOpenStar K L p ⊆ K.space :=
  fun _ hx => openStarCone_subset_space hx.1

/-- The link projection, as a map of the punctured open star to the link. -/
def linkRetraction (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p)
    (x : ↥(puncturedOpenStar K L p)) : ↥(closedStarLink K L) := by
  refine ⟨linkProj K L p (x : CoordinateSpace e), ?_⟩
  obtain ⟨y, hy, t, ht0, ht1, hxt⟩ :=
    exists_link_decomposition hL hp x.property.1.1 (fun h => x.property.2 h)
  have hval : linkProj K L p (x : CoordinateSpace e) = y := by
    rw [hxt]; exact linkProj_eq hL hp hy ht0 ht1
  rw [hval]
  exact hy

theorem continuous_linkRetraction (hfin : K.faces.Finite) (hL : L ∈ K.faces)
    (hp : IsCarrierPoint K L p) : Continuous (linkRetraction hL hp) := by
  rw [continuous_iff_isClosed]
  intro S hS
  obtain ⟨Z', hZ'closed, hZ'⟩ := isClosed_induced_iff.mp hS
  have hZcompact : IsCompact (Z' ∩ closedStarLink K L) :=
    (isCompact_closedStarLink hfin L).inter_left hZ'closed
  have himg : IsClosed (coneMap p '' ((Z' ∩ closedStarLink K L) ×ˢ Set.Icc (0 : ℝ) 1)) :=
    (isCompact_coneMap_image hZcompact p).isClosed
  have hpre : linkRetraction hL hp ⁻¹' S =
      Subtype.val ⁻¹' (coneMap p '' ((Z' ∩ closedStarLink K L) ×ˢ Set.Icc (0 : ℝ) 1)) := by
    ext x
    have hxstar : (x : CoordinateSpace e) ∈ closedStar K L := x.property.1.1
    have hxp : (x : CoordinateSpace e) ≠ p := fun h => x.property.2 h
    have hiff := mem_coneMap_image_iff (K := K) (L := L) (p := p) hL hp
      (Z := Z' ∩ closedStarLink K L) Set.inter_subset_right hxstar hxp
    constructor
    · intro hxS
      have h1 : linkRetraction hL hp x ∈ S := hxS
      rw [← hZ'] at h1
      have h2 : linkProj K L p (x : CoordinateSpace e) ∈ Z' ∩ closedStarLink K L :=
        ⟨h1, (linkRetraction hL hp x).property⟩
      exact hiff.mpr h2
    · intro hxim
      have h2 := hiff.mp hxim
      change linkRetraction hL hp x ∈ S
      rw [← hZ']
      exact h2.1
  rw [hpre]
  exact himg.preimage continuous_subtype_val

/-! ### The link is a retract of the punctured open star -/

/-- The inclusion of the link into the punctured open star, at half the radius. -/
def linkInclusion (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p)
    (y : ↥(closedStarLink K L)) : ↥(puncturedOpenStar K L p) := by
  refine ⟨p + (1 / 2 : ℝ) • ((y : CoordinateSpace e) - p), ⟨⟨?_, ?_⟩, ?_⟩⟩
  · exact mem_closedStar_of_ray hp.1 y.property (by norm_num) (by norm_num)
  · exact notMem_closedStarLink_smul hL hp y.property (by norm_num) (by norm_num)
  · intro hmem
    have h : p + (1 / 2 : ℝ) • ((y : CoordinateSpace e) - p) = p := hmem
    have hy : (y : CoordinateSpace e) = p := by
      have h2 : (1 / 2 : ℝ) • ((y : CoordinateSpace e) - p) = 0 := by
        have hc := congrArg (fun z => z - p) h
        simpa using hc
      have h3 : (y : CoordinateSpace e) - p = 0 := by
        rcases smul_eq_zero.mp h2 with h4 | h4
        · norm_num at h4
        · exact h4
      exact sub_eq_zero.mp h3
    exact notMem_closedStarLink hL hp (hy ▸ y.property)

theorem continuous_linkInclusion (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p) :
    Continuous (linkInclusion hL hp) := by
  apply Continuous.subtype_mk
  fun_prop

theorem linkRetraction_linkInclusion (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p)
    (y : ↥(closedStarLink K L)) :
    linkRetraction hL hp (linkInclusion hL hp y) = y := by
  apply Subtype.ext
  exact linkProj_eq hL hp y.property (by norm_num) (by norm_num)

/-! ### The local homology bound for the link -/

namespace IsSimplicialBall

variable {n : ℕ}

/-- **The link of a carrier point of a simplicial ball has homology of rank at
most one in degree `n - 1`.**  The punctured open star is an open punctured
neighbourhood, so Mayer-Vietoris bounds its rank by that of the punctured ball;
and the link is a retract of the punctured open star. -/
theorem finrank_homology_closedStarLink_le_one
    (hball : IsSimplicialBall n K) (hn : 2 ≤ n) (hL : L ∈ K.faces)
    (hp : IsCarrierPoint K L p) :
    Module.finrank ℝ ((realSingularHomology (n - 1)).obj
      (TopCat.of ↥(closedStarLink K L))) ≤ 1 := by
  classical
  have hpspace : p ∈ K.space := hp.mem_space hL
  have hBopen : IsOpen (Subtype.val ⁻¹' (openStarCone K L) : Set ↥K.space) :=
    isOpen_preimage_openStarCone hball.finite_faces
  have hapex : p ∈ openStarCone K L := mem_openStarCone_apex hball.finite_faces hL hp
  have hPB : (⟨p, hpspace⟩ : ↥K.space) ∈
      (Subtype.val ⁻¹' (openStarCone K L) : Set ↥K.space) := hapex
  have hBcontr : ContractibleSpace ↥(Subtype.val ⁻¹' (openStarCone K L) : Set ↥K.space) := by
    have h0 : ContractibleSpace ↥(openStarCone K L) :=
      (starConvex_openStarCone hL hp).contractibleSpace ⟨p, hapex⟩
    exact (subsetSubtypeHomeomorph
      (openStarCone_subset_space (K := K) (L := L))).toHomotopyEquiv.contractibleSpace
  obtain ⟨hfd, hle⟩ := hball.finrank_homology_punctured_open_le_one hn hBopen hPB hBcontr
  -- the intersection is the punctured open star
  have hinter : ({q : ↥K.space | q ≠ (⟨p, hpspace⟩ : ↥K.space)} ∩
      (Subtype.val ⁻¹' (openStarCone K L))) =
      Subtype.val ⁻¹' (puncturedOpenStar K L p) := by
    ext q
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, fun h => h1 (Subtype.ext h)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h2 (by simp [h]), h1⟩
  have hWhomeo : ↥({q : ↥K.space | q ≠ (⟨p, hpspace⟩ : ↥K.space)} ∩
      (Subtype.val ⁻¹' (openStarCone K L))) ≃ₜ ↥(puncturedOpenStar K L p) :=
    (Homeomorph.setCongr hinter).trans
      (subsetSubtypeHomeomorph (puncturedOpenStar_subset_space (K := K) (L := L) (p := p)))
  have hiso := (realSingularHomologyIsoOfHomotopyEquiv
    hWhomeo.toHomotopyEquiv (n - 1)).toLinearEquiv
  have hfdW : FiniteDimensional ℝ ((realSingularHomology (n - 1)).obj
      (TopCat.of ↥(puncturedOpenStar K L p))) :=
    @LinearEquiv.finiteDimensional ℝ _ _ _ _ _ _ _ hiso hfd
  have hleW : Module.finrank ℝ ((realSingularHomology (n - 1)).obj
      (TopCat.of ↥(puncturedOpenStar K L p))) ≤ 1 := by
    rw [← hiso.finrank_eq]
    exact hle
  have hinj := injective_realSingularHomology_of_retract
    (⟨linkInclusion hL hp, continuous_linkInclusion hL hp⟩ :
      C(↥(closedStarLink K L), ↥(puncturedOpenStar K L p)))
    (⟨linkRetraction hL hp, continuous_linkRetraction hball.finite_faces hL hp⟩)
    (linkRetraction_linkInclusion hL hp) (n - 1)
  exact le_trans (LinearMap.finrank_le_finrank_of_injective hinj) hleW

/-- **At a homology boundary point the link is acyclic in degree `n - 1`.** -/
theorem subsingleton_homology_closedStarLink_of_mem_homologyBoundary
    (hball : IsSimplicialBall n K) (hn : 2 ≤ n) (hL : L ∈ K.faces)
    (hp : IsCarrierPoint K L p)
    (hmem : (⟨p, hp.mem_space hL⟩ : ↥K.space) ∈ homologyBoundary ↥K.space (n - 1)) :
    Subsingleton ((realSingularHomology (n - 1)).obj
      (TopCat.of ↥(closedStarLink K L))) := by
  classical
  have hpspace : p ∈ K.space := hp.mem_space hL
  have hBopen : IsOpen (Subtype.val ⁻¹' (openStarCone K L) : Set ↥K.space) :=
    isOpen_preimage_openStarCone hball.finite_faces
  have hapex : p ∈ openStarCone K L := mem_openStarCone_apex hball.finite_faces hL hp
  have hPB : (⟨p, hpspace⟩ : ↥K.space) ∈
      (Subtype.val ⁻¹' (openStarCone K L) : Set ↥K.space) := hapex
  have hBcontr : ContractibleSpace ↥(Subtype.val ⁻¹' (openStarCone K L) : Set ↥K.space) := by
    have h0 : ContractibleSpace ↥(openStarCone K L) :=
      (starConvex_openStarCone hL hp).contractibleSpace ⟨p, hapex⟩
    exact (subsetSubtypeHomeomorph
      (openStarCone_subset_space (K := K) (L := L))).toHomotopyEquiv.contractibleSpace
  have hsub := hball.subsingleton_homology_punctured_open_of_mem_homologyBoundary hn
    hBopen hPB hBcontr hmem
  have hinter : ({q : ↥K.space | q ≠ (⟨p, hpspace⟩ : ↥K.space)} ∩
      (Subtype.val ⁻¹' (openStarCone K L))) =
      Subtype.val ⁻¹' (puncturedOpenStar K L p) := by
    ext q
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, fun h => h1 (Subtype.ext h)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h2 (by simp [h]), h1⟩
  have hWhomeo : ↥({q : ↥K.space | q ≠ (⟨p, hpspace⟩ : ↥K.space)} ∩
      (Subtype.val ⁻¹' (openStarCone K L))) ≃ₜ ↥(puncturedOpenStar K L p) :=
    (Homeomorph.setCongr hinter).trans
      (subsetSubtypeHomeomorph (puncturedOpenStar_subset_space (K := K) (L := L) (p := p)))
  have hiso := (realSingularHomologyIsoOfHomotopyEquiv
    hWhomeo.toHomotopyEquiv (n - 1)).toLinearEquiv
  have hsubW : Subsingleton ((realSingularHomology (n - 1)).obj
      (TopCat.of ↥(puncturedOpenStar K L p))) :=
    hiso.toEquiv.symm.subsingleton_congr.mpr hsub
  have hinj := injective_realSingularHomology_of_retract
    (⟨linkInclusion hL hp, continuous_linkInclusion hL hp⟩ :
      C(↥(closedStarLink K L), ↥(puncturedOpenStar K L p)))
    (⟨linkRetraction hL hp, continuous_linkRetraction hball.finite_faces hL hp⟩)
    (linkRetraction_linkInclusion hL hp) (n - 1)
  exact ⟨fun x y => hinj (Subsingleton.elim _ _)⟩

end IsSimplicialBall

end AffineTverberg
