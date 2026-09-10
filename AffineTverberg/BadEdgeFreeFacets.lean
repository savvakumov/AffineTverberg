import AffineTverberg.BadEdgeSubdivisionPurity
import AffineTverberg.BadEdgeSubdivisionGluing
import AffineTverberg.SimplicialHomology

set_option linter.style.header false

/-!
# Private facets of top bad simplices

This is the counting and free-facet argument of the simplicial-ball case.
The cells are finite sets of colored copies, with at most `r * N` vertices
and at least `N` distinct original vertices. The subdivision is the actual
recursive bad-edge subdivision, not an assumed triangulation certificate.

For `r = m + 1 ≥ 3`, every bad simplex of cardinality `m * N` has a private
facet in the assembled bad subcomplex. The conclusion is then applied to
the genuine oriented simplicial homology. No duality theorem is assumed here.
-/

noncomputable section

namespace AffineTverberg.BadEdge

variable {W V : Type*} [LinearOrder W] [DecidableEq V]

omit [LinearOrder W] in
/-- There are at most `m + 1` different copies of each original vertex. -/
theorem card_le_copies_mul_image {m : ℕ} (idx : W → Fin (m + 1)) (orig : W → V)
    (hinj : Function.Injective fun w ↦ (idx w, orig w)) (S : Finset W) :
    S.card ≤ (m + 1) * (S.image orig).card := by
  have hsub : S.image (fun w ↦ (idx w, orig w)) ⊆
      (Finset.univ : Finset (Fin (m + 1))) ×ˢ S.image orig := by
    intro p hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_image_of_mem _ hw⟩
  have := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_product,
    Finset.card_univ, Fintype.card_fin] using this

/-- Saturating the bad dimension bound forces the original face to have
exactly `N` original vertices and all `(m + 1) * N` copies. -/
theorem saturated_bad_face_counts {m N : ℕ} {orig : W → V} {S : Finset W}
    (hsize : S.card ≤ (m + 1) * N) (horig : N ≤ (S.image orig).card)
    {τ : Finset (Finset W)} (hτ : τ ∈ sdFaces orig S)
    (hbad : ∀ s ∈ τ, ¬ IsGoodSdVertex s) (hcard : τ.card = m * N) :
    S.card = (m + 1) * N ∧ (S.image orig).card = N := by
  have hbound := card_le_of_all_bad orig S hτ hbad
  have himage : (S.image orig).card ≤ S.card := Finset.card_image_le
  have hexp : (m + 1) * N = m * N + N := by ring
  omega

/-- Two saturated faces with the same original vertices contain exactly the
same colored copies. -/
theorem eq_of_saturated_image_eq {m N : ℕ} (idx : W → Fin (m + 1)) (orig : W → V)
    (hinj : Function.Injective fun w ↦ (idx w, orig w)) {S T : Finset W}
    (hS : S.card = (m + 1) * N) (hT : T.card = (m + 1) * N)
    (hSN : (S.image orig).card = N) (heq : S.image orig = T.image orig) : S = T := by
  have hbound := card_le_copies_mul_image idx orig hinj (S ∪ T)
  rw [Finset.image_union, ← heq, Finset.union_self, hSN] at hbound
  have hSU : S = S ∪ T := Finset.eq_of_subset_of_card_le Finset.subset_union_left
    (by omega)
  have hTU : T = S ∪ T := Finset.eq_of_subset_of_card_le Finset.subset_union_right
    (by omega)
  exact hSU.trans hTU.symm

/-- Distinct saturated cells share fewer than `N` original vertices. -/
theorem card_image_inter_lt_of_saturated_ne {m N : ℕ}
    (idx : W → Fin (m + 1)) (orig : W → V)
    (hinj : Function.Injective fun w ↦ (idx w, orig w)) {S T : Finset W}
    (hS : S.card = (m + 1) * N) (hT : T.card = (m + 1) * N)
    (hSN : (S.image orig).card = N) (hTN : (T.image orig).card = N)
    (hne : S ≠ T) : ((S ∩ T).image orig).card < N := by
  by_contra hnot
  have hle : N ≤ ((S ∩ T).image orig).card := by omega
  have hIS : (S ∩ T).image orig = S.image orig :=
    Finset.eq_of_subset_of_card_le (Finset.image_subset_image Finset.inter_subset_left)
      (by omega)
  have hIT : (S ∩ T).image orig = T.image orig :=
    Finset.eq_of_subset_of_card_le (Finset.image_subset_image Finset.inter_subset_right)
      (by omega)
  exact hne (eq_of_saturated_image_eq idx orig hinj hS hT hSN (hIS.symm.trans hIT))

/-- A simplex occurring in two subdivisions occurs in the subdivision of
their common original face. -/
theorem mem_sdFaces_inter {orig : W → V} {S T : Finset W} {σ : Finset (Finset W)}
    (hS : σ ∈ sdFaces orig S) (hT : σ ∈ sdFaces orig T) :
    σ ∈ sdFaces orig (S ∩ T) := by
  apply mem_sdFaces_of_subset (S := S) (R := S ∩ T) _ Finset.inter_subset_left hS
  intro s hs w hw
  exact Finset.mem_inter.mpr
    ⟨(sdFaces_vertex orig S hS s hs).2.1 hw, (sdFaces_vertex orig T hT s hs).2.1 hw⟩

/-- The actual assembled bad subcomplex of a finite family of original cells. -/
def badFacesOfFamily (orig : W → V) (M : Finset (Finset W)) : Finset (Finset (Finset W)) :=
  (M.biUnion (sdFaces orig)).filter fun σ ↦ ∀ s ∈ σ, ¬ IsGoodSdVertex s

@[simp]
theorem mem_badFacesOfFamily {orig : W → V} {M : Finset (Finset W)}
    {σ : Finset (Finset W)} :
    σ ∈ badFacesOfFamily orig M ↔
      (∃ S ∈ M, σ ∈ sdFaces orig S) ∧ (∀ s ∈ σ, ¬ IsGoodSdVertex s) := by
  simp [badFacesOfFamily]

theorem faceClosed_badFacesOfFamily (orig : W → V) (M : Finset (Finset W)) :
    Simplicial.FaceClosed (badFacesOfFamily orig M) := by
  intro σ hσ τ hτσ
  obtain ⟨⟨S, hSM, hσS⟩, hbad⟩ := mem_badFacesOfFamily.mp hσ
  exact mem_badFacesOfFamily.mpr
    ⟨⟨S, hSM, sdFaces_faceClosed orig S hσS hτσ⟩, fun s hs ↦ hbad s (hτσ hs)⟩

/-- All bad simplices lie in the cardinality-degree bound `m * N`. -/
theorem card_le_badFacesOfFamily {m N : ℕ} (orig : W → V) (M : Finset (Finset W))
    (hsize : ∀ S ∈ M, S.card ≤ (m + 1) * N)
    (horig : ∀ S ∈ M, N ≤ (S.image orig).card)
    {τ : Finset (Finset W)} (hτ : τ ∈ badFacesOfFamily orig M) : τ.card ≤ m * N := by
  obtain ⟨⟨S, hSM, hτS⟩, hbad⟩ := mem_badFacesOfFamily.mp hτ
  have hbound := card_le_of_all_bad orig S hτS hbad
  have h1 := hsize S hSM
  have h2 := horig S hSM
  have hexp : (m + 1) * N = m * N + N := by ring
  omega

/-- The paper's free-facet construction. A top bad simplex has a private
facet obtained by erasing the apex of its saturated original cell. -/
theorem hasFreeFacets_badFacesOfFamily {m N : ℕ} (hm : 2 ≤ m) (hN : 0 < N)
    (idx : W → Fin (m + 1)) (orig : W → V)
    (hinj : Function.Injective fun w ↦ (idx w, orig w)) (M : Finset (Finset W))
    (hsize : ∀ S ∈ M, S.card ≤ (m + 1) * N)
    (horig : ∀ S ∈ M, N ≤ (S.image orig).card) :
    HasFreeFacets (Simplicial.topSimplices (badFacesOfFamily orig M) (m * N)) := by
  intro τ
  obtain ⟨hτmem, hτcard⟩ := Simplicial.mem_topSimplices.mp τ.property
  obtain ⟨⟨S, hSM, hτS⟩, hτbad⟩ := mem_badFacesOfFamily.mp hτmem
  obtain ⟨hSsize, hSorig⟩ := saturated_bad_face_counts (hsize S hSM) (horig S hSM)
    hτS hτbad hτcard
  have hSnonempty : S.Nonempty := Finset.card_pos.mp (by rw [hSsize]; positivity)
  have hnotdel : ¬ IsDeletedFace orig S := by
    intro hdel
    have hc : (S.image orig).card = S.card :=
      Finset.card_image_iff.mpr (fun u hu w hw h ↦ hdel u hu w hw h)
    rw [hSsize, hSorig] at hc
    nlinarith
  have hbadapex : ¬ IsGoodSdVertex (apexSet orig S) := not_isGoodSdVertex_apexSet
    (Finset.nonempty_iff_ne_empty.mpr fun h ↦ hnotdel (badElts_eq_empty_iff.mp h))
  have hcapS : S.card - (S.image orig).card = m * N := by
    rw [hSsize, hSorig, add_mul, one_mul, Nat.add_sub_cancel]
  have hapex : apexSet orig S ∈ τ.val := apex_mem_of_bad_card_eq hSnonempty hbadapex
    hτS hτbad (hτcard.trans hcapS.symm)
  have hfacetτ : IsSimplexFacet (τ.val.erase (apexSet orig S)) τ.val := by
    refine ⟨Finset.erase_subset _ _, ?_⟩
    rw [Finset.card_erase_of_mem hapex]
    have := Finset.card_pos.mpr (show τ.val.Nonempty from ⟨_, hapex⟩)
    omega
  refine ⟨τ.val.erase (apexSet orig S), hfacetτ, ?_⟩
  intro τ' hfacet
  obtain ⟨hτ'mem, hτ'card⟩ := Simplicial.mem_topSimplices.mp τ'.property
  obtain ⟨⟨T, hTM, hτ'T⟩, hτ'bad⟩ := mem_badFacesOfFamily.mp hτ'mem
  obtain ⟨hTsize, hTorig⟩ := saturated_bad_face_counts (hsize T hTM) (horig T hTM)
    hτ'T hτ'bad hτ'card
  have hST : S = T := by
    by_contra hne
    have hinter := mem_sdFaces_inter
      (sdFaces_faceClosed orig S hτS (Finset.erase_subset _ _))
      (sdFaces_faceClosed orig T hτ'T hfacet.1)
    have hbound := card_le_of_all_bad orig (S ∩ T) hinter
      (fun s hs ↦ hτbad s (Finset.mem_of_mem_erase hs))
    have hcopies := card_le_copies_mul_image idx orig hinj (S ∩ T)
    have hlt := card_image_inter_lt_of_saturated_ne idx orig hinj
      hSsize hTsize hSorig hTorig hne
    have hdim := bad_facet_dimension_lt (m + 1) N ((S ∩ T).image orig).card
      (by omega) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at hdim
    have hcap : (S ∩ T).card - ((S ∩ T).image orig).card ≤
        m * ((S ∩ T).image orig).card := by
      rw [add_mul, one_mul] at hcopies
      omega
    rw [Finset.card_erase_of_mem hapex, hτcard] at hbound
    rw [Nat.mul_comm ((S ∩ T).image orig).card m] at hdim
    omega
  subst T
  have hapex' : apexSet orig S ∈ τ'.val := apex_mem_of_bad_card_eq hSnonempty hbadapex
    hτ'T hτ'bad (hτ'card.trans hcapS.symm)
  apply Subtype.ext
  symm
  apply Finset.eq_of_subset_of_card_le
  · rw [← Finset.insert_erase hapex]
    exact Finset.insert_subset hapex' hfacet.1
  · omega

end AffineTverberg.BadEdge
