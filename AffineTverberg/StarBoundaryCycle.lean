import AffineTverberg.PseudomanifoldCycle
import Mathlib.Algebra.Field.ZMod

set_option linter.style.header false

/-!
# The mod-two cycle on the boundary of a closed star

The family here realizes the existing geometric `closedStarLink`: faces of
the closed star which do not contain the carrier face. If no boundary ridge
contains the carrier, take the sum of the top simplices through it. Its
boundary is a nonzero cycle supported on this link. Coefficients on ridges
containing the carrier cancel in pairs. This avoids a join Kunneth theorem
and avoids imposing orientability or combinatorial-manifold links.
-/

noncomputable section

namespace AffineTverberg.Simplicial

variable {V : Type} [Fintype V] [LinearOrder V]

/-- The boundary of the closed star, as an abstract face family. -/
def starBoundaryFamily (A : Finset (Finset V)) (L : Finset V) : Finset (Finset V) :=
  A.filter (fun s => s ∪ L ∈ A ∧ ¬ L ⊆ s)

omit [Fintype V] in
@[simp]
theorem mem_starBoundaryFamily {A : Finset (Finset V)} {L s : Finset V} :
    s ∈ starBoundaryFamily A L ↔ s ∈ A ∧ s ∪ L ∈ A ∧ ¬ L ⊆ s :=
  Finset.mem_filter

omit [Fintype V] in
theorem faceClosed_starBoundaryFamily {A : Finset (Finset V)}
    (hA : FaceClosed A) (L : Finset V) : FaceClosed (starBoundaryFamily A L) := by
  intro s hs t hts
  obtain ⟨hsA, hsL, hnot⟩ := mem_starBoundaryFamily.mp hs
  exact mem_starBoundaryFamily.mpr ⟨hA s hsA t hts,
    hA _ hsL _ (Finset.union_subset_union_left hts), fun h => hnot (h.trans hts)⟩

omit [Fintype V] in
theorem card_le_starBoundaryFamily {A : Finset (Finset V)} {L : Finset V} {N : ℕ}
    (hmax : ∀ s ∈ A, s.card ≤ N) {s : Finset V}
    (hs : s ∈ starBoundaryFamily A L) : s.card ≤ N - 1 := by
  obtain ⟨hsA, hsL, hnot⟩ := mem_starBoundaryFamily.mp hs
  have hle := hmax s hsA
  have hle' := hmax (s ∪ L) hsL
  have hlt : s.card < N := by
    by_contra h
    have heq : s = s ∪ L :=
      Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
    exact hnot (heq.symm ▸ Finset.subset_union_right)
  omega

omit [Fintype V] in
/-- Restricting top simplices to cofaces of `L` does not change the count
above any face which already contains `L`. -/
theorem facetCount_filter_cofaces {A : Finset (Finset V)} {L s : Finset V}
    (hLs : L ⊆ s) (N : ℕ) :
    facetCount (A.filter (fun F => L ⊆ F)) N s = facetCount A N s := by
  unfold facetCount
  congr 1
  ext F
  simp only [Finset.mem_filter, mem_topSimplices]
  constructor
  · rintro ⟨⟨⟨hF, -⟩, hc⟩, hsub, hcard⟩
    exact ⟨⟨hF, hc⟩, hsub, hcard⟩
  · rintro ⟨⟨hF, hc⟩, hsub, hcard⟩
    exact ⟨⟨⟨hF, hLs.trans hsub⟩, hc⟩, hsub, hcard⟩

omit [Fintype V] in
/-- A top simplex through `L`, with one vertex of `L` removed, belongs to
exactly that one top simplex of the restricted coface family. -/
theorem facetCount_filter_cofaces_erase {A : Finset (Finset V)}
    {L F : Finset V} {N : ℕ} (hF : F ∈ A) (hLF : L ⊆ F) (hcard : F.card = N)
    {u : V} (hu : u ∈ L) :
    facetCount (A.filter (fun G => L ⊆ G)) N (F.erase u) = 1 := by
  have huF := hLF hu
  have hc : (F.erase u).card + 1 = N := by
    rw [Finset.card_erase_of_mem huF]
    have hpos := Finset.card_pos.mpr ⟨u, huF⟩
    omega
  have hsingle : ((topSimplices (A.filter (fun G => L ⊆ G)) N).filter
      (fun G => F.erase u ⊆ G ∧ (F.erase u).card + 1 = G.card)) = {F} := by
    ext G
    simp only [Finset.mem_filter, mem_topSimplices, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨⟨-, hLG⟩, hGc⟩, hsub, -⟩
      have hFG : F ⊆ G := by
        rw [← Finset.insert_erase huF]
        exact Finset.insert_subset (hLG hu) hsub
      exact (Finset.eq_of_subset_of_card_le hFG (by omega)).symm
    · rintro rfl
      exact ⟨⟨⟨hF, hLF⟩, hcard⟩, Finset.erase_subset _ _, hc.trans hcard.symm⟩
  rw [facetCount, hsingle, Finset.card_singleton]

/-- If every codimension-one coface of a nonempty face lies in an even
number of top simplices, the boundary of its closed star has a nonzero top
mod-two cycle. This is exactly the obstruction needed for boundary detection. -/
theorem not_isReducedAcyclicAt_starBoundaryFamily {A : Finset (Finset V)}
    (hA : FaceClosed A) {L : Finset V} {N : ℕ}
    (hmax : ∀ s ∈ A, s.card ≤ N) (hne : L.Nonempty)
    (hface : ∃ F ∈ A, L ⊆ F ∧ F.card = N)
    (heven : ∀ s ∈ A, L ⊆ s → s.card + 1 = N → Even (facetCount A N s)) :
    ¬ IsReducedAcyclicAt (ZMod 2) (starBoundaryFamily A L) (N - 1) := by
  classical
  let B := A.filter (fun F => L ⊆ F)
  let c := boundary (ZMod 2) V (fundamentalChain (ZMod 2) B N)
  have hcoeff (s : Finset V) : c s = (facetCount B N s : ZMod 2) :=
    boundary_fundamentalChain_apply (ZMod.natCast_self 2) B N s
  have hc : c ∈ chains (ZMod 2) (starBoundaryFamily A L) (N - 1) := by
    intro s hs
    have hcount : 0 < facetCount B N s := Nat.pos_of_ne_zero (by
      intro hzero
      exact hs (by rw [hcoeff, hzero]; rfl))
    obtain ⟨F, hF⟩ := Finset.card_pos.mp hcount
    obtain ⟨hFtop, hsF, hsc⟩ := Finset.mem_filter.mp hF
    obtain ⟨hFB, hFc⟩ := mem_topSimplices.mp hFtop
    obtain ⟨hFA, hLF⟩ := Finset.mem_filter.mp hFB
    have hsA : s ∈ A := hA F hFA s hsF
    have hsL : s ∪ L ∈ A := hA F hFA _ (Finset.union_subset hsF hLF)
    have hsnot : ¬ L ⊆ s := by
      intro hLs
      have hcnt : facetCount B N s = facetCount A N s :=
        facetCount_filter_cofaces hLs N
      have hparity := heven s hsA hLs (hsc.trans hFc)
      exact hs (by rw [hcoeff, hcnt]; exact hparity.natCast_zmod_two)
    exact ⟨mem_starBoundaryFamily.mpr ⟨hsA, hsL, hsnot⟩, by omega⟩
  have hcycle : c ∈ cycles (ZMod 2) (starBoundaryFamily A L) (N - 1) :=
    ⟨hc, boundary_boundary_apply _⟩
  have hcne : c ≠ 0 := by
    obtain ⟨F, hF, hLF, hFc⟩ := hface
    obtain ⟨u, hu⟩ := hne
    intro hzero
    have hcu : c (F.erase u) = 1 := by
      rw [hcoeff, facetCount_filter_cofaces_erase hF hLF hFc hu]
      rfl
    have hz := congrFun hzero (F.erase u)
    rw [hcu] at hz
    exact one_ne_zero hz
  intro hacyc
  have hb := hacyc hcycle
  rw [boundaries_top_eq_bot (fun s hs => card_le_starBoundaryFamily hmax hs),
    Submodule.mem_bot] at hb
  exact hcne hb

end AffineTverberg.Simplicial
