import Mathlib.Data.Set.Card
import AffineTverberg.MainTheorem

set_option linter.style.header false

/-!
# Facets and ridges of a finite pure geometric complex

Elementary combinatorial glue for the boundary-ridge argument of the
simplicial-ball half of the main theorem.  For a geometric simplicial complex
with finitely many faces every face is contained in a facet; if moreover all
facets have `n + 1` vertices then the facets are exactly the faces with
`n + 1` vertices, and every face has at most `n + 1` vertices.

The set of facets through a face is finite, and `IsBoundaryRidge n K L` says
precisely that this set is a singleton, i.e. has `ncard` equal to one.  These
statements convert the topological input "some codimension one face lies in an
odd (hence exactly one) number of facets" into the definition used by
`simplicialBallMainTheoremStatement`.
-/

noncomputable section

open Set

namespace AffineTverberg

variable {e n : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-- The set of facets of `K` containing a given face. -/
def facetsThrough (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))
    (s : Finset (CoordinateSpace e)) : Set (Finset (CoordinateSpace e)) :=
  {F | F ∈ K.facets ∧ s ⊆ F}

theorem mem_facetsThrough {s F : Finset (CoordinateSpace e)} :
    F ∈ facetsThrough K s ↔ F ∈ K.facets ∧ s ⊆ F := Iff.rfl

/-- In a complex with finitely many faces every face extends to a facet. -/
theorem exists_facet_superset (hfin : K.faces.Finite) {s : Finset (CoordinateSpace e)}
    (hs : s ∈ K.faces) : ∃ F ∈ K.facets, s ⊆ F := by
  obtain ⟨F, hF, hmax⟩ := Set.exists_max_image {t | t ∈ K.faces ∧ s ⊆ t}
    (fun t : Finset (CoordinateSpace e) => t.card)
    (hfin.subset fun t ht => ht.1) ⟨s, hs, subset_rfl⟩
  refine ⟨F, ?_, hF.2⟩
  rw [Geometry.SimplicialComplex.mem_facets]
  refine ⟨hF.1, fun t ht hFt => ?_⟩
  exact Finset.eq_of_subset_of_card_le hFt (hmax t ⟨ht, hF.2.trans hFt⟩)

/-- The set of facets through a face of a finite complex is nonempty. -/
theorem facetsThrough_nonempty (hfin : K.faces.Finite) {s : Finset (CoordinateSpace e)}
    (hs : s ∈ K.faces) : (facetsThrough K s).Nonempty := by
  obtain ⟨F, hF, hsF⟩ := exists_facet_superset hfin hs
  exact ⟨F, hF, hsF⟩

theorem facetsThrough_finite (hfin : K.faces.Finite) (s : Finset (CoordinateSpace e)) :
    (facetsThrough K s).Finite :=
  hfin.subset fun _ hF => Geometry.SimplicialComplex.facets_subset hF.1

/-- In a finite pure complex every face has at most `n + 1` vertices. -/
theorem card_le_of_mem_faces (hfin : K.faces.Finite)
    (hpure : ∀ s ∈ K.facets, s.card = n + 1) {s : Finset (CoordinateSpace e)}
    (hs : s ∈ K.faces) : s.card ≤ n + 1 := by
  obtain ⟨F, hF, hsF⟩ := exists_facet_superset hfin hs
  calc s.card ≤ F.card := Finset.card_le_card hsF
    _ = n + 1 := hpure F hF

/-- In a finite pure complex the facets are exactly the faces with `n + 1`
vertices. -/
theorem mem_facets_iff_card (hfin : K.faces.Finite)
    (hpure : ∀ s ∈ K.facets, s.card = n + 1) {s : Finset (CoordinateSpace e)} :
    s ∈ K.facets ↔ s ∈ K.faces ∧ s.card = n + 1 := by
  constructor
  · exact fun hs => ⟨Geometry.SimplicialComplex.facets_subset hs, hpure s hs⟩
  · rintro ⟨hs, hcard⟩
    obtain ⟨F, hF, hsF⟩ := exists_facet_superset hfin hs
    have : s = F := Finset.eq_of_subset_of_card_le hsF (by rw [hpure F hF, hcard])
    exact this ▸ hF

/-- `IsBoundaryRidge` says exactly that the set of facets through the face is a
singleton. -/
theorem isBoundaryRidge_iff_facetsThrough_eq_singleton {L : Finset (CoordinateSpace e)} :
    IsBoundaryRidge n K L ↔
      L ∈ K.faces ∧ L.card = n ∧ ∃ F, facetsThrough K L = {F} := by
  refine and_congr_right fun hL => and_congr_right fun hcard => ?_
  constructor
  · rintro ⟨F, hF, huniq⟩
    exact ⟨F, Set.eq_singleton_iff_unique_mem.mpr ⟨hF, fun G hG => huniq G hG⟩⟩
  · rintro ⟨F, hFeq⟩
    have hmem := Set.eq_singleton_iff_unique_mem.mp hFeq
    exact ⟨F, hmem.1, fun G hG => hmem.2 G hG⟩

/-- **The counting criterion for a boundary ridge.**  A codimension one face
of a finite complex is a boundary ridge exactly when it lies in exactly one
facet. -/
theorem isBoundaryRidge_iff_ncard_eq_one {L : Finset (CoordinateSpace e)}
    (hL : L ∈ K.faces) (hcard : L.card = n) :
    IsBoundaryRidge n K L ↔ (facetsThrough K L).ncard = 1 := by
  rw [isBoundaryRidge_iff_facetsThrough_eq_singleton, Set.ncard_eq_one]
  simp [hL, hcard]

/-- **From counting to a boundary ridge.**  If some codimension one face lies in
an odd number of facets, and no codimension one face lies in more than two
facets, then `K` has a boundary ridge.  The first hypothesis is what a mod two
fundamental-cycle argument provides, the second is the local homology bound at a
ridge point of a ball. -/
theorem exists_isBoundaryRidge_of_odd_of_le_two
    (hodd : ∃ L ∈ K.faces, L.card = n ∧ Odd (facetsThrough K L).ncard)
    (hle : ∀ L ∈ K.faces, L.card = n → (facetsThrough K L).ncard ≤ 2) :
    ∃ L, IsBoundaryRidge n K L := by
  obtain ⟨L, hL, hcard, hoddL⟩ := hodd
  refine ⟨L, (isBoundaryRidge_iff_ncard_eq_one hL hcard).mpr ?_⟩
  have hle2 := hle L hL hcard
  obtain ⟨k, hk⟩ := hoddL
  omega

/-- A boundary ridge of a finite pure complex from a unique facet. -/
theorem isBoundaryRidge_of_unique_facet {L F : Finset (CoordinateSpace e)}
    (hL : L ∈ K.faces) (hcard : L.card = n) (hF : F ∈ K.facets) (hLF : L ⊆ F)
    (huniq : ∀ G ∈ K.facets, L ⊆ G → G = F) : IsBoundaryRidge n K L :=
  ⟨hL, hcard, F, ⟨hF, hLF⟩, fun G hG => huniq G hG.1 hG.2⟩

end AffineTverberg
