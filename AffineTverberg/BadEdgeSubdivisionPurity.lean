import AffineTverberg.BadEdgeSubdivision

set_option linter.style.header false

/-!
# Purity and bad-simplex dimension bounds for the midpoint subdivision

Every simplex extends to one with as many vertices as the original face.
Consequently the good-vertex count bounds every bad simplex, not just the
bad part of a simplex already known to be full-dimensional. These are the
extension and dimension steps used in the paper's deleted-join argument.
-/

namespace AffineTverberg.BadEdge

variable {W V : Type*} [DecidableEq W] [LinearOrder W] [DecidableEq V]

/-- Every simplex of a nonempty subdivided face can be coned to its apex. -/
theorem insert_apex_mem_sdFaces {orig : W → V} {S : Finset W}
    (hS : S.Nonempty) {σ : Finset (Finset W)} (hσ : σ ∈ sdFaces orig S) :
    insert (apexSet orig S) σ ∈ sdFaces orig S := by
  rcases (mem_sdFaces_iff hS).mp hσ with h | ⟨τ, hτ, rfl⟩
  · exact (mem_sdFaces_iff hS).mpr (Or.inr ⟨σ, h, rfl⟩)
  · simpa only [Finset.insert_idem] using
      (mem_sdFaces_iff hS).mpr (Or.inr ⟨τ, hτ, rfl⟩)

/-- Purity, in its useful extension form; the empty face is included. -/
theorem exists_full_simplex_extension (orig : W → V) (S : Finset W)
    {σ : Finset (Finset W)} (hσ : σ ∈ sdFaces orig S) :
    ∃ τ ∈ sdFaces orig S, σ ⊆ τ ∧ τ.card = S.card := by
  induction S using Finset.strongInduction generalizing σ with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · have hσempty : σ = ∅ := by simpa only [sdFaces_empty, Finset.mem_singleton] using hσ
      exact ⟨∅, empty_mem_sdFaces orig ∅, by simp [hσempty], rfl⟩
    · obtain ⟨u, hu, hbase⟩ := exists_erase_apex_mem hS hσ
      have huS : u ∈ S := apexSet_subset orig S hu
      obtain ⟨τ, hτ, hsub, hcard⟩ := ih (S.erase u) (Finset.erase_ssubset huS) hbase
      have hanot : apexSet orig S ∉ τ := by
        intro ha
        have := (sdFaces_vertex orig (S.erase u) hτ _ ha).2.1 hu
        exact (Finset.mem_erase.mp this).1 rfl
      refine ⟨insert (apexSet orig S) τ,
        (mem_sdFaces_iff hS).mpr
          (Or.inr ⟨τ, mem_sdBase.mpr ⟨u, hu, hτ⟩, rfl⟩), ?_, ?_⟩
      · intro s hs
        by_cases hsa : s = apexSet orig S
        · exact Finset.mem_insert.mpr (Or.inl hsa)
        · exact Finset.mem_insert_of_mem (hsub (Finset.mem_erase.mpr ⟨hsa, hs⟩))
      · rw [Finset.card_insert_of_notMem hanot, hcard, Finset.card_erase_of_mem huS]
        have := Finset.card_pos.mpr hS
        omega

/-- Thus every inclusion-maximal simplex has the expected dimension. -/
theorem card_eq_of_maximal_sdFaces (orig : W → V) (S : Finset W)
    {σ : Finset (Finset W)} (hσ : σ ∈ sdFaces orig S)
    (hmax : ∀ τ ∈ sdFaces orig S, σ ⊆ τ → τ = σ) :
    σ.card = S.card := by
  obtain ⟨τ, hτ, hsub, hcard⟩ := exists_full_simplex_extension orig S hσ
  rwa [hmax τ hτ hsub] at hcard

/-- A full-dimensional simplex contains the chosen apex. -/
theorem apex_mem_of_full_card {orig : W → V} {S : Finset W}
    (hS : S.Nonempty) {σ : Finset (Finset W)} (hσ : σ ∈ sdFaces orig S)
    (hcard : σ.card = S.card) : apexSet orig S ∈ σ := by
  by_contra ha
  have hbound := sdFaces_card_le orig S (insert_apex_mem_sdFaces hS hσ)
  rw [Finset.card_insert_of_notMem ha, hcard] at hbound
  omega

/-- The number of bad vertices in any simplex is bounded by the number of
repeated original vertices of the original face. -/
theorem card_bad_filter_le (orig : W → V) (S : Finset W)
    {σ : Finset (Finset W)} (hσ : σ ∈ sdFaces orig S) :
    (σ.filter fun s ↦ ¬ IsGoodSdVertex s).card ≤ S.card - (S.image orig).card := by
  obtain ⟨τ, hτ, hsub, hcard⟩ := exists_full_simplex_extension orig S hσ
  have hgood := card_image_orig_le_card_good orig S hτ hcard
  have hpartition := Finset.card_filter_add_card_filter_not (s := τ) IsGoodSdVertex
  have hmono : (σ.filter fun s ↦ ¬ IsGoodSdVertex s).card ≤
      (τ.filter fun s ↦ ¬ IsGoodSdVertex s).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ hsub)
  omega

/-- The bad induced subcomplex has the required dimension bound on all its
simplices, including simplices on the boundary of an original face. -/
theorem card_le_of_all_bad (orig : W → V) (S : Finset W)
    {σ : Finset (Finset W)} (hσ : σ ∈ sdFaces orig S)
    (hbad : ∀ s ∈ σ, ¬ IsGoodSdVertex s) :
    σ.card ≤ S.card - (S.image orig).card := by
  have hf : σ.filter (fun s ↦ ¬ IsGoodSdVertex s) = σ := Finset.filter_true_of_mem hbad
  simpa only [hf] using card_bad_filter_le orig S hσ

/-- A bad simplex saturating the dimension bound contains the bad apex.
This will give its candidate private facet by erasing that apex. -/
theorem apex_mem_of_bad_card_eq {orig : W → V} {S : Finset W}
    (hS : S.Nonempty) (ha : ¬ IsGoodSdVertex (apexSet orig S))
    {σ : Finset (Finset W)} (hσ : σ ∈ sdFaces orig S)
    (hbad : ∀ s ∈ σ, ¬ IsGoodSdVertex s)
    (hcard : σ.card = S.card - (S.image orig).card) : apexSet orig S ∈ σ := by
  by_contra hnot
  have hbound := card_le_of_all_bad orig S (insert_apex_mem_sdFaces hS hσ)
    (fun s hs ↦ by
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact ha
      · exact hbad s hs)
  rw [Finset.card_insert_of_notMem hnot, hcard] at hbound
  omega

end AffineTverberg.BadEdge
