import AffineTverberg.StarLinkRetract
import AffineTverberg.LinkJoinRank

set_option linter.style.header false

/-!
# The link of a ridge is the join of a simplex boundary with the apex set

For a codimension one face `L` of a finite pure geometric simplicial complex,
each facet through `L` is `insert v L` for a vertex `v` outside `L`.  The link
of the closed star, `closedStarLink K L`, is then exactly the geometric
realization of the abstract complex `boundaryJoinPoints L V` of
`AffineTverberg.LinkJoinRank`, where `V` is the set of apexes.

Combining the resulting rank lower bound `V.card - 1` with the local upper
bound of `StarLinkRetract` shows that in a simplicial ball of dimension
`n ≥ 2` every codimension one face lies in at most two facets.
-/

noncomputable section

open Set CategoryTheory

namespace AffineTverberg.Simplicial

variable {e : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-- If the images of all members of an abstract face family are faces of a
geometric simplicial complex, then the family is geometrically realized by the
(injective) vertex map. -/
theorem isGeometricRealization_of_image_mem_faces {W : Type} [DecidableEq W]
    {A : Finset (Finset W)} {q : W → CoordinateSpace e} (hq : Function.Injective q)
    (hfaces : ∀ s ∈ A, s.Nonempty → Finset.image q s ∈ K.faces) :
    IsGeometricRealization A q := by
  classical
  constructor
  · intro s hs
    rcases Finset.eq_empty_or_nonempty s with rfl | hne
    · exact affineIndependent_of_subsingleton ℝ _
    · have hF := hfaces s hs hne
      have hind := K.indep hF
      let emb : ↥s ↪ ↥(Finset.image q s) :=
        ⟨fun w => ⟨q w.val, Finset.mem_image_of_mem q w.property⟩, by
          intro a b hab
          exact Subtype.ext (hq (congrArg Subtype.val hab))⟩
      exact hind.comp_embedding emb
  · intro s hs t ht
    rcases Finset.eq_empty_or_nonempty s with rfl | hsne
    · simp
    rcases Finset.eq_empty_or_nonempty t with rfl | htne
    · simp
    have h := K.inter_subset_convexHull (hfaces s hs hsne) (hfaces t ht htne)
    have himg : (Finset.image q (s ∩ t) : Finset (CoordinateSpace e)) =
        Finset.image q s ∩ Finset.image q t := Finset.image_inter s t hq
    intro x hx
    have hx' : x ∈ convexHull ℝ ((Finset.image q s : Set (CoordinateSpace e)) ∩
        (Finset.image q t : Set (CoordinateSpace e))) := by
      apply h
      rw [Finset.coe_image, Finset.coe_image]
      exact hx
    rw [← Finset.coe_inter, ← himg, Finset.coe_image] at hx'
    exact hx'

/-- A finite set of points is the injective image of a finite linearly ordered
abstract vertex type. -/
theorem exists_abstract_vertexType (M : Finset (CoordinateSpace e)) :
    ∃ (W : Type) (_ : Fintype W) (_ : LinearOrder W) (q : W → CoordinateSpace e),
      Function.Injective q ∧ ∀ x, x ∈ M ↔ ∃ w, q w = x := by
  classical
  refine ⟨↥M, inferInstance,
    LinearOrder.lift' (fun w => Fintype.equivFin ↥M w) (Equiv.injective _),
    Subtype.val, Subtype.val_injective, fun x => ?_⟩
  constructor
  · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨w, rfl⟩; exact w.property

end AffineTverberg.Simplicial

namespace AffineTverberg

variable {e n : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
  {L V : Finset (CoordinateSpace e)}

/-- The hypotheses describing the apex set of a codimension one face: the
facets through `L` are exactly the sets `insert v L` for `v ∈ V`. -/
structure IsApexSet (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))
    (L V : Finset (CoordinateSpace e)) : Prop where
  disjoint : Disjoint L V
  facet : ∀ v ∈ V, insert v L ∈ facetsThrough K L
  surj : ∀ F ∈ facetsThrough K L, ∃ v ∈ V, F = insert v L

theorem IsApexSet.nonempty (hfin : K.faces.Finite) (hL : L ∈ K.faces)
    (hV : IsApexSet K L V) : V.Nonempty := by
  obtain ⟨F, hF⟩ := facetsThrough_nonempty hfin hL
  obtain ⟨v, hv, -⟩ := hV.surj F hF
  exact ⟨v, hv⟩

/-- **The link of a codimension one face is the join of the boundary of `L`
with the apex set.**  Consequently its homology in degree `n - 1` has rank at
least `V.card - 1`. -/
theorem card_sub_one_le_finrank_homology_closedStarLink
    (hfin : K.faces.Finite) (hL : L ∈ K.faces) (hcard : L.card = n) (hn : 2 ≤ n)
    (hV : IsApexSet K L V) :
    V.card - 1 ≤ Module.finrank ℝ ((realSingularHomology (n - 1)).obj
      (TopCat.of ↥(closedStarLink K L))) := by
  classical
  obtain ⟨v₀, hv₀⟩ := hV.nonempty hfin hL
  obtain ⟨W, _, _, q, hqinj, hqsurj⟩ :=
    Simplicial.exists_abstract_vertexType (e := e) (L ∪ V)
  set L' : Finset W := Finset.univ.filter (fun w => q w ∈ L) with hL'def
  set V' : Finset W := Finset.univ.filter (fun w => q w ∈ V) with hV'def
  have hmemL' : ∀ w : W, w ∈ L' ↔ q w ∈ L := by intro w; simp [hL'def]
  have hmemV' : ∀ w : W, w ∈ V' ↔ q w ∈ V := by intro w; simp [hV'def]
  have hpreL : ∀ x ∈ L, ∃ w : W, q w = x := fun x hx =>
    (hqsurj x).mp (Finset.mem_union_left _ hx)
  have hpreV : ∀ x ∈ V, ∃ w : W, q w = x := fun x hx =>
    (hqsurj x).mp (Finset.mem_union_right _ hx)
  have himageL : Finset.image q L' = L := by
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact (hmemL' w).mp hw
    · intro hx
      obtain ⟨w, rfl⟩ := hpreL x hx
      exact ⟨w, (hmemL' w).mpr hx, rfl⟩
  have himageV : Finset.image q V' = V := by
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact (hmemV' w).mp hw
    · intro hx
      obtain ⟨w, rfl⟩ := hpreV x hx
      exact ⟨w, (hmemV' w).mpr hx, rfl⟩
  have hcardL' : L'.card = L.card := by
    rw [← himageL, Finset.card_image_of_injective _ hqinj]
  have hcardV' : V'.card = V.card := by
    rw [← himageV, Finset.card_image_of_injective _ hqinj]
  have hdisj' : Disjoint L' V' := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    exact (Finset.disjoint_left.mp hV.disjoint) ((hmemL' w).mp hw) ((hmemV' w).mp hw')
  -- every abstract face is carried into a facet with a vertex of `L` deleted
  have hsubset : ∀ s ∈ Simplicial.boundaryJoinPoints L' V', ∃ u ∈ L, ∃ v ∈ V,
      Finset.image q s ⊆ (insert v L).erase u := by
    intro s hs
    obtain ⟨hsub, hnot, hcard1⟩ := Simplicial.mem_boundaryJoinPoints.mp hs
    obtain ⟨u', hu'L, hu's⟩ : ∃ u' ∈ L', u' ∉ s := Finset.not_subset.mp hnot
    have huL : q u' ∈ L := (hmemL' u').mp hu'L
    have hnotimg : q u' ∉ Finset.image q s := by
      intro hmem
      obtain ⟨w, hw, hwq⟩ := Finset.mem_image.mp hmem
      exact hu's ((hqinj hwq) ▸ hw)
    have huniq := Finset.card_le_one.mp hcard1
    by_cases hex : ∃ z, z ∈ s ∧ z ∈ V'
    · obtain ⟨v', hv's, hv'V'⟩ := hex
      have hv'V : q v' ∈ V := (hmemV' v').mp hv'V'
      refine ⟨q u', huL, q v', hv'V, ?_⟩
      intro x hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
      refine Finset.mem_erase.mpr ⟨fun h => hnotimg (h ▸ hx), ?_⟩
      rcases Finset.mem_union.mp (hsub hw) with h | h
      · exact Finset.mem_insert_of_mem ((hmemL' w).mp h)
      · have hwv : w = v' :=
          huniq w (Finset.mem_inter.mpr ⟨hw, h⟩) v' (Finset.mem_inter.mpr ⟨hv's, hv'V'⟩)
        rw [hwv]
        exact Finset.mem_insert_self _ _
    · push Not at hex
      refine ⟨q u', huL, v₀, hv₀, ?_⟩
      intro x hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
      refine Finset.mem_erase.mpr ⟨fun h => hnotimg (h ▸ hx), ?_⟩
      rcases Finset.mem_union.mp (hsub hw) with h | h
      · exact Finset.mem_insert_of_mem ((hmemL' w).mp h)
      · exact absurd h (hex w hw)
  -- the abstract faces are realized by faces of `K`
  have hfacesK : ∀ s ∈ Simplicial.boundaryJoinPoints L' V', s.Nonempty →
      Finset.image q s ∈ K.faces := by
    intro s hs hne
    obtain ⟨u, hu, v, hv, hsub⟩ := hsubset s hs
    have hFfaces : insert v L ∈ K.faces :=
      Geometry.SimplicialComplex.facets_subset (hV.facet v hv).1
    exact K.down_closed hFfaces
      (hsub.trans (Finset.erase_subset u (insert v L))) (hne.image q)
  have hgeom : Simplicial.IsGeometricRealization (Simplicial.boundaryJoinPoints L' V') q :=
    Simplicial.isGeometricRealization_of_image_mem_faces hqinj hfacesK
  -- the geometric carrier is the link
  have hcarrier : Simplicial.geometricCarrier (Simplicial.boundaryJoinPoints L' V') q =
      closedStarLink K L := by
    apply Set.Subset.antisymm
    · rw [Simplicial.geometricCarrier]
      refine Set.iUnion₂_subset fun s hs => ?_
      obtain ⟨u, hu, v, hv, hsub⟩ := hsubset s hs
      have hsub' : q '' (s : Set W) ⊆ (((insert v L).erase u : Finset (CoordinateSpace e)) :
          Set (CoordinateSpace e)) := by
        rw [← Finset.coe_image]
        exact_mod_cast hsub
      refine subset_trans (convexHull_mono hsub') ?_
      exact fun x hx => mem_closedStarLink_iff.mpr ⟨insert v L, hV.facet v hv, u, hu, hx⟩
    · intro x hx
      obtain ⟨F, hF, u, hu, hxu⟩ := mem_closedStarLink_iff.mp hx
      obtain ⟨v, hv, rfl⟩ := hV.surj F hF
      have hvL : v ∉ L := Finset.disjoint_right.mp hV.disjoint hv
      obtain ⟨u', hu'⟩ := hpreL u hu
      obtain ⟨v', hv'⟩ := hpreV v hv
      have huv : u' ≠ v' := by
        intro h
        apply hvL
        rw [← hv', ← h, hu']
        exact hu
      rw [Simplicial.geometricCarrier]
      refine Set.mem_iUnion₂.mpr ⟨insert v' (L'.erase u'), ?_, ?_⟩
      · refine Simplicial.mem_boundaryJoinPoints.mpr ⟨?_, ?_, ?_⟩
        · intro w hw
          rcases Finset.mem_insert.mp hw with h1 | h1
          · exact Finset.mem_union_right _ ((hmemV' w).mpr (by rw [h1, hv']; exact hv))
          · exact Finset.mem_union_left _ (Finset.mem_of_mem_erase h1)
        · intro hcon
          have hmem : u' ∈ insert v' (L'.erase u') :=
            hcon ((hmemL' u').mpr (by rw [hu']; exact hu))
          rcases Finset.mem_insert.mp hmem with h | h
          · exact huv h
          · exact (Finset.notMem_erase _ L') h
        · refine le_trans (Finset.card_le_card (?_ : _ ⊆ ({v'} : Finset W))) (by simp)
          intro w hw
          obtain ⟨hw1, hw2⟩ := Finset.mem_inter.mp hw
          rcases Finset.mem_insert.mp hw1 with h1 | h1
          · exact Finset.mem_singleton.mpr h1
          · exact absurd hw2 (Finset.disjoint_left.mp hdisj' (Finset.mem_of_mem_erase h1))
      · have himg : q '' ((insert v' (L'.erase u') : Finset W) : Set W) =
            (((insert v L).erase u : Finset (CoordinateSpace e)) : Set (CoordinateSpace e)) := by
          rw [← Finset.coe_image]
          congr 1
          ext y
          simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro ⟨w, hw, rfl⟩
            rcases hw with h1 | ⟨hw1, hw2⟩
            · refine ⟨?_, Or.inl ?_⟩
              · rw [h1, hv']
                exact fun hc => hvL (hc ▸ hu)
              · rw [h1, hv']
            · exact ⟨fun hc => hw1 (hqinj (by rw [hc, hu'])), Or.inr ((hmemL' w).mp hw2)⟩
          · rintro ⟨hyu, hymem⟩
            rcases hymem with h1 | h1
            · exact ⟨v', Or.inl rfl, by rw [hv', h1]⟩
            · obtain ⟨w, rfl⟩ := hpreL y h1
              refine ⟨w, Or.inr ⟨?_, (hmemL' w).mpr h1⟩, rfl⟩
              intro hc
              exact hyu (by rw [← hu', hc])
        rw [himg]
        exact hxu
  -- transport the abstract lower bound
  have hdeg : (n - 2) + 1 = n - 1 := by omega
  have hLcard : L'.card = (n - 2) + 2 := by rw [hcardL', hcard]; omega
  have hbound := Simplicial.card_sub_one_le_finrank_realSingularHomology_boundaryJoinPoints
    hdisj' hLcard
  rw [hdeg] at hbound
  have hhomeo : ↥(Simplicial.barycentricCarrier (Simplicial.boundaryJoinPoints L' V')) ≃ₜ
      ↥(closedStarLink K L) :=
    (Simplicial.geometricRealizationHomeomorph hgeom).trans (Homeomorph.setCongr hcarrier)
  have hiso := (realSingularHomologyIsoOfHomotopyEquiv
    hhomeo.toHomotopyEquiv (n - 1)).toLinearEquiv
  rw [← hiso.finrank_eq, ← hcardV']
  exact hbound

/-! ### At most two facets through a codimension one face -/

/-- The apex set of a codimension one face of a finite pure complex. -/
def apexSet (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))
    (L : Finset (CoordinateSpace e)) (hfin : K.faces.Finite) :
    Finset (CoordinateSpace e) := by
  classical
  exact (facetsThrough_finite hfin L).toFinset.biUnion fun F => F \ L

theorem isApexSet_apexSet (hfin : K.faces.Finite) (hpure : ∀ F ∈ K.facets, F.card = n + 1)
    (hcard : L.card = n) : IsApexSet K L (apexSet K L hfin) := by
  classical
  have hmem : ∀ v, v ∈ apexSet K L hfin ↔ ∃ F ∈ facetsThrough K L, v ∈ F ∧ v ∉ L := by
    intro v
    simp only [apexSet, Finset.mem_biUnion, Set.Finite.mem_toFinset, Finset.mem_sdiff]
  have hins : ∀ F ∈ facetsThrough K L, ∀ v ∈ F, v ∉ L → F = insert v L := by
    intro F hF v hvF hvL
    refine (Finset.eq_of_subset_of_card_le (Finset.insert_subset hvF hF.2) ?_).symm
    rw [hpure F hF.1, Finset.card_insert_of_notMem hvL, hcard]
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.disjoint_right]
    intro v hv
    obtain ⟨F, -, -, hvL⟩ := (hmem v).mp hv
    exact hvL
  · intro v hv
    obtain ⟨F, hF, hvF, hvL⟩ := (hmem v).mp hv
    exact (hins F hF v hvF hvL) ▸ hF
  · intro F hF
    have hlt : L.card < F.card := by rw [hpure F hF.1, hcard]; omega
    obtain ⟨v, hvF, hvL⟩ := Finset.exists_of_ssubset
      (Finset.ssubset_iff_subset_ne.mpr ⟨hF.2, fun h => by rw [h] at hlt; omega⟩)
    exact ⟨v, (hmem v).mpr ⟨F, hF, hvF, hvL⟩, hins F hF v hvF hvL⟩

theorem card_apexSet (hfin : K.faces.Finite) (hpure : ∀ F ∈ K.facets, F.card = n + 1)
    (hcard : L.card = n) : (apexSet K L hfin).card = (facetsThrough K L).ncard := by
  classical
  have hV := isApexSet_apexSet (K := K) (L := L) (n := n) hfin hpure hcard
  have himg : (apexSet K L hfin).image (fun v => insert v L) =
      (facetsThrough_finite hfin L).toFinset := by
    ext F
    simp only [Finset.mem_image, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hV.facet v hv
    · intro hF
      obtain ⟨v, hv, rfl⟩ := hV.surj F hF
      exact ⟨v, hv, rfl⟩
  have hinj : Set.InjOn (fun v => insert v L) (apexSet K L hfin) := by
    intro a ha b hb hab
    have hbL : b ∉ L := Finset.disjoint_right.mp hV.disjoint hb
    have hab' : insert a L = insert b L := hab
    have : a ∈ insert b L := by rw [← hab']; exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp this with h | h
    · exact h
    · exact absurd h (Finset.disjoint_right.mp hV.disjoint ha)
  rw [Set.ncard_eq_toFinset_card _ (facetsThrough_finite hfin L), ← himg,
    Finset.card_image_of_injOn hinj]

namespace IsSimplicialBall

/-- **In a simplicial ball of dimension `n ≥ 2` every codimension one face lies
in at most two facets.**  The local homology of the link is at least
`(number of facets) - 1` by the join computation and at most one by the
punctured-ball comparison. -/
theorem ncard_facetsThrough_le_two (hball : IsSimplicialBall n K) (hn : 2 ≤ n)
    (hL : L ∈ K.faces) (hcard : L.card = n) :
    (facetsThrough K L).ncard ≤ 2 := by
  classical
  have hV := isApexSet_apexSet (K := K) (L := L) (n := n) hball.finite_faces hball.pure hcard
  have hcardV := card_apexSet (K := K) (L := L) (n := n) hball.finite_faces hball.pure hcard
  have hlow := card_sub_one_le_finrank_homology_closedStarLink
    hball.finite_faces hL hcard hn hV
  have hup := hball.finrank_homology_closedStarLink_le_one hn hL (isCarrierPoint_centroid hL)
  rw [hcardV] at hlow
  omega

/-- **A codimension one face carrying a homology boundary point is a boundary
ridge.**  Its link is then acyclic in degree `n - 1`, so the join computation
forces exactly one facet through it. -/
theorem isBoundaryRidge_of_carrierPoint_mem_homologyBoundary
    (hball : IsSimplicialBall n K) (hn : 2 ≤ n) (hL : L ∈ K.faces) (hcard : L.card = n)
    {p : CoordinateSpace e} (hp : IsCarrierPoint K L p)
    (hmem : (⟨p, hp.mem_space hL⟩ : ↥K.space) ∈ homologyBoundary ↥K.space (n - 1)) :
    IsBoundaryRidge n K L := by
  classical
  have hV := isApexSet_apexSet (K := K) (L := L) (n := n) hball.finite_faces hball.pure hcard
  have hcardV := card_apexSet (K := K) (L := L) (n := n) hball.finite_faces hball.pure hcard
  have hlow := card_sub_one_le_finrank_homology_closedStarLink
    hball.finite_faces hL hcard hn hV
  have hsub := hball.subsingleton_homology_closedStarLink_of_mem_homologyBoundary hn hL hp hmem
  have hzero : Module.finrank ℝ ((realSingularHomology (n - 1)).obj
      (TopCat.of ↥(closedStarLink K L))) = 0 := Module.finrank_zero_of_subsingleton
  rw [hzero] at hlow
  have hne : 0 < (apexSet K L hball.finite_faces).card :=
    Finset.card_pos.mpr (hV.nonempty hball.finite_faces hL)
  have hone : (apexSet K L hball.finite_faces).card = 1 := by omega
  rw [isBoundaryRidge_iff_ncard_eq_one hL hcard, ← hcardV, hone]

/-- **From an odd cofacet count to a boundary ridge.**  With the local bound of
`ncard_facetsThrough_le_two`, the only remaining input for a boundary ridge of a
simplicial ball is a codimension one face lying in an odd number of facets. -/
theorem exists_isBoundaryRidge_of_odd (hball : IsSimplicialBall n K) (hn : 2 ≤ n)
    (hodd : ∃ L ∈ K.faces, L.card = n ∧ Odd (facetsThrough K L).ncard) :
    ∃ L, IsBoundaryRidge n K L :=
  exists_isBoundaryRidge_of_odd_of_le_two hodd
    fun _ hL hcard => hball.ncard_facetsThrough_le_two hn hL hcard

end IsSimplicialBall

end AffineTverberg
