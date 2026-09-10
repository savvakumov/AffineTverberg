import AffineTverberg.BadEdgeSubdivision

set_option linter.style.header false

/-!
# The bad-vertex pulling subdivision over an arbitrary face family

`AffineTverberg/BadEdgeSubdivision.lean` constructs the bad-edge subdivision of a
*simplex*, where the faces of the face being subdivided are exactly the subsets
of its vertex set.  For a general (nonsimplicial) polytope this is false: the
faces form a proper subfamily of the subsets of the vertex set.  This file
redoes the construction over an arbitrary finite family

`F : Finset (Finset W)`

of "faces", each recorded by its set of vertices, using the same apex rule
`apexSet` (earliest vertex of a deleted face, earliest bad pair otherwise) and
hence inheriting its hereditary behaviour `apexSet_mono`.

`sdPoset orig F S` is defined by recursion on the number of vertices:

`sdPoset orig F S = {∅} ∪ ⋃ (G ∈ F, G ⊆ S, apex S ⊄ G) apexCone (apex S) (sdPoset orig F G)`,

i.e. the faces of `S` not containing the apex are subdivided recursively and
coned from the apex; faces containing the apex need no separate treatment,
because by `apexSet_mono` they carry the *same* apex and their subdivisions are
therefore already contained in that of `S` (`sdPoset_mono`).

## Main results

* `sdPoset_mono` — compatibility of the subdivisions along the face family.
* `sdPoset_faceClosed` — the subdivision is a simplicial (abstract) complex.
* `sdPoset_vertex_eq_apexSet` — every vertex of the subdivision is the apex of
  some face contained in `S`; in particular it is a singleton (an original
  vertex, *good*) or a bad pair (an edge midpoint, *bad*).
* `sdPoset_good_exists_deleted_face` — a simplex all of whose vertices are good
  lies in a *deleted* face of the family; this is the combinatorial half of the
  identification of the good subcomplex with the deleted join.
* `sdPoset_card_eq_one_of_deleted` — conversely all simplices of a deleted face
  are good.
* `IsApexFlag.card_eq_rank` — a flag simplex has exactly `rank S` vertices.
* `IsApexFlag` and `card_goodVertices_ge` — the good-vertex count of a full
  simplex: a simplex carried by an apex flag of ranks `0, 1, …, k` has at least
  `mm S + 1` good vertices, for any `mm` which drops by at most one along a rank
  step and does not grow along a rank step with a bad apex.
-/

open scoped BigOperators

namespace AffineTverberg
namespace BadEdge

variable {W V : Type*} [DecidableEq W] [LinearOrder W] [DecidableEq V]

/-- The cone with apex `a` over a family of simplices. -/
def apexCone (a : Finset W) (X : Finset (Finset (Finset W))) :
    Finset (Finset (Finset W)) := X ∪ X.image (insert a)

omit [LinearOrder W] in
theorem mem_apexCone {a : Finset W} {X : Finset (Finset (Finset W))}
    {σ : Finset (Finset W)} :
    σ ∈ apexCone a X ↔ σ ∈ X ∨ ∃ τ ∈ X, σ = insert a τ := by
  simp [apexCone, eq_comm]

/-- **The bad-vertex pulling subdivision of the face `S` over the face family
`F`.** -/
def sdPoset (orig : W → V) (F : Finset (Finset W)) (S : Finset W) :
    Finset (Finset (Finset W)) :=
  insert ∅ ((F.filter fun G ↦ G ⊆ S ∧ ¬ apexSet orig S ⊆ G).attach.biUnion
    fun G ↦ apexCone (apexSet orig S) (sdPoset orig F G.1))
termination_by S.card
decreasing_by
  obtain ⟨-, hGS, hna⟩ := Finset.mem_filter.mp G.2
  obtain ⟨u, hu, hu'⟩ := Finset.not_subset.mp hna
  exact Finset.card_lt_card
    ((Finset.ssubset_iff_of_subset hGS).mpr ⟨u, apexSet_subset orig S hu, hu'⟩)

theorem sdPoset_eq (orig : W → V) (F : Finset (Finset W)) (S : Finset W) :
    sdPoset orig F S =
      insert ∅ ((F.filter fun G ↦ G ⊆ S ∧ ¬ apexSet orig S ⊆ G).attach.biUnion
        fun G ↦ apexCone (apexSet orig S) (sdPoset orig F G.1)) := by
  rw [sdPoset]

theorem empty_mem_sdPoset (orig : W → V) (F : Finset (Finset W)) (S : Finset W) :
    ∅ ∈ sdPoset orig F S := by
  rw [sdPoset_eq]; exact Finset.mem_insert_self _ _

/-- Membership in the subdivision, unfolded one step. -/
theorem mem_sdPoset_iff {orig : W → V} {F : Finset (Finset W)} {S : Finset W}
    {σ : Finset (Finset W)} :
    σ ∈ sdPoset orig F S ↔
      σ = ∅ ∨ ∃ G ∈ F, G ⊆ S ∧ ¬ apexSet orig S ⊆ G ∧
        (σ ∈ sdPoset orig F G ∨ ∃ τ ∈ sdPoset orig F G, σ = insert (apexSet orig S) τ) := by
  rw [sdPoset_eq]
  simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_attach, true_and,
    Subtype.exists, Finset.mem_filter, mem_apexCone, exists_prop]
  constructor
  · rintro (h | ⟨G, hG, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨G, hG.1, hG.2.1, hG.2.2, h⟩
  · rintro (h | ⟨G, hG, hGS, hna, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨G, ⟨hG, hGS, hna⟩, h⟩

/-- A face of the family not containing the apex of `S` has strictly fewer
vertices than `S`; this is what makes the recursion terminate. -/
theorem card_lt_of_apexSet_not_subset {orig : W → V} {S G : Finset W} (hGS : G ⊆ S)
    (hna : ¬ apexSet orig S ⊆ G) : G.card < S.card := by
  obtain ⟨u, hu, hu'⟩ := Finset.not_subset.mp hna
  exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hGS).mpr
    ⟨u, apexSet_subset orig S hu, hu'⟩)

theorem apexSet_nonempty_of_not_subset {orig : W → V} {S G : Finset W}
    (hna : ¬ apexSet orig S ⊆ G) : (apexSet orig S).Nonempty := by
  obtain ⟨u, hu, -⟩ := Finset.not_subset.mp hna
  exact ⟨u, hu⟩

/-- Every vertex of the subdivision of `S` is the apex of a nonempty face of the
family contained in `S`. -/
theorem sdPoset_vertex_eq_apexSet {orig : W → V} {F : Finset (Finset W)}
    {S : Finset W} {σ : Finset (Finset W)} (hσ : σ ∈ sdPoset orig F S)
    {a : Finset W} (ha : a ∈ σ) :
    ∃ G, (G ∈ F ∨ G = S) ∧ G ⊆ S ∧ G.Nonempty ∧ a = apexSet orig G := by
  induction hk : S.card using Nat.strong_induction_on generalizing S σ with
  | _ k ih =>
    subst hk
    rcases mem_sdPoset_iff.mp hσ with rfl | ⟨G, hGF, hGS, hna, hcase⟩
    · simp at ha
    · have hlt := card_lt_of_apexSet_not_subset (orig := orig) hGS hna
      rcases hcase with h | ⟨τ, hτ, rfl⟩
      · obtain ⟨H, hH, hHG, hHne, rfl⟩ := ih G.card hlt h ha rfl
        exact ⟨H, Or.inl (hH.elim id fun h ↦ h ▸ hGF), hHG.trans hGS, hHne, rfl⟩
      · rcases Finset.mem_insert.mp ha with rfl | ha'
        · exact ⟨S, Or.inr rfl, Finset.Subset.refl _,
            (apexSet_nonempty_of_not_subset (orig := orig) hna).mono
              (apexSet_subset orig S), rfl⟩
        · obtain ⟨H, hH, hHG, hHne, rfl⟩ := ih G.card hlt hτ ha' rfl
          exact ⟨H, Or.inl (hH.elim id fun h ↦ h ▸ hGF), hHG.trans hGS, hHne, rfl⟩

theorem sdPoset_vertex_subset {orig : W → V} {F : Finset (Finset W)}
    {S : Finset W} {σ : Finset (Finset W)} (hσ : σ ∈ sdPoset orig F S)
    {a : Finset W} (ha : a ∈ σ) : a ⊆ S := by
  obtain ⟨G, -, hGS, -, rfl⟩ := sdPoset_vertex_eq_apexSet hσ ha
  exact (apexSet_subset orig G).trans hGS

theorem sdPoset_vertex_card_le_two {orig : W → V} {F : Finset (Finset W)}
    {S : Finset W} {σ : Finset (Finset W)} (hσ : σ ∈ sdPoset orig F S)
    {a : Finset W} (ha : a ∈ σ) : a.card ≤ 2 := by
  obtain ⟨G, -, -, hGne, rfl⟩ := sdPoset_vertex_eq_apexSet hσ ha
  by_cases h : (badElts orig G).Nonempty
  · exact le_of_eq (apexSet_card_eq_two h)
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [apexSet_card_eq_one h hGne]
    norm_num

theorem sdPoset_vertex_nonempty {orig : W → V} {F : Finset (Finset W)}
    {S : Finset W} {σ : Finset (Finset W)} (hσ : σ ∈ sdPoset orig F S)
    {a : Finset W} (ha : a ∈ σ) : a.Nonempty := by
  obtain ⟨G, -, -, hGne, rfl⟩ := sdPoset_vertex_eq_apexSet hσ ha
  exact apexSet_nonempty hGne

/-- **Compatibility along the face family**: the subdivision of a face of the
family contained in `S` is part of the subdivision of `S`. -/
theorem sdPoset_mono {orig : W → V} {F : Finset (Finset W)} {S G : Finset W}
    (hG : G ∈ F) (hGS : G ⊆ S) : sdPoset orig F G ⊆ sdPoset orig F S := by
  intro σ hσ
  by_cases hna : ¬ apexSet orig S ⊆ G
  · rw [mem_sdPoset_iff]
    exact Or.inr ⟨G, hG, hGS, hna, Or.inl hσ⟩
  · rw [not_not] at hna
    rcases G.eq_empty_or_nonempty with rfl | hGne
    · rw [mem_sdPoset_iff] at hσ
      rcases hσ with rfl | ⟨H, -, hHS, hna', -⟩
      · exact empty_mem_sdPoset _ _ _
      · rw [apexSet_empty] at hna'
        exact absurd (Finset.empty_subset H) hna'
    · have hap : apexSet orig G = apexSet orig S := apexSet_mono hGS hGne hna
      rw [mem_sdPoset_iff] at hσ ⊢
      rcases hσ with rfl | ⟨H, hHF, hHG, hnaH, hcase⟩
      · exact Or.inl rfl
      · rw [hap] at hnaH hcase
        exact Or.inr ⟨H, hHF, hHG.trans hGS, hnaH, hcase⟩

/-- The subdivision is an abstract simplicial complex. -/
theorem sdPoset_faceClosed {orig : W → V} {F : Finset (Finset W)} {S : Finset W}
    {σ τ : Finset (Finset W)} (hσ : σ ∈ sdPoset orig F S) (hτσ : τ ⊆ σ) :
    τ ∈ sdPoset orig F S := by
  induction hk : S.card using Nat.strong_induction_on generalizing S σ τ with
  | _ k ih =>
    subst hk
    rcases mem_sdPoset_iff.mp hσ with rfl | ⟨G, hGF, hGS, hna, hcase⟩
    · rw [Finset.subset_empty] at hτσ
      exact hτσ ▸ empty_mem_sdPoset _ _ _
    · have hlt := card_lt_of_apexSet_not_subset (orig := orig) hGS hna
      rw [mem_sdPoset_iff]
      rcases hcase with h | ⟨ρ, hρ, rfl⟩
      · exact Or.inr ⟨G, hGF, hGS, hna, Or.inl (ih G.card hlt h hτσ rfl)⟩
      · by_cases ha : apexSet orig S ∈ τ
        · refine Or.inr ⟨G, hGF, hGS, hna, Or.inr ⟨τ.erase (apexSet orig S), ?_, ?_⟩⟩
          · refine ih G.card hlt hρ ?_ rfl
            intro x hx
            rcases Finset.mem_insert.mp (hτσ (Finset.mem_of_mem_erase hx)) with rfl | h'
            · exact absurd rfl (Finset.ne_of_mem_erase hx)
            · exact h'
          · rw [Finset.insert_erase ha]
        · refine Or.inr ⟨G, hGF, hGS, hna, Or.inl (ih G.card hlt hρ ?_ rfl)⟩
          intro x hx
          rcases Finset.mem_insert.mp (hτσ hx) with rfl | h'
          · exact absurd hx ha
          · exact h'

/-- All vertices of the subdivision of a deleted face are good (singletons):
a deleted face is not subdivided at all in the bad directions. -/
theorem sdPoset_card_eq_one_of_deleted {orig : W → V} {F : Finset (Finset W)}
    {S : Finset W} (hS : IsDeletedFace orig S) {σ : Finset (Finset W)}
    (hσ : σ ∈ sdPoset orig F S) {a : Finset W} (ha : a ∈ σ) : a.card = 1 := by
  obtain ⟨G, -, hGS, hGne, rfl⟩ := sdPoset_vertex_eq_apexSet hσ ha
  exact apexSet_card_eq_one (badElts_eq_empty_iff.mpr (hS.mono hGS)) hGne

/-- **A simplex with only good vertices lies in a deleted face of the family.**
This is the combinatorial content of the identification of the good induced
subcomplex with the deleted join. -/
theorem sdPoset_good_exists_deleted_face {orig : W → V} {F : Finset (Finset W)}
    (hF : ∅ ∈ F) {S : Finset W} {σ : Finset (Finset W)}
    (hσ : σ ∈ sdPoset orig F S) (hgood : ∀ a ∈ σ, a.card = 1) :
    ∃ G, (G ∈ F ∨ G = S) ∧ G ⊆ S ∧ IsDeletedFace orig G ∧ ∀ a ∈ σ, a ⊆ G := by
  induction hk : S.card using Nat.strong_induction_on generalizing S σ with
  | _ k ih =>
    subst hk
    rcases mem_sdPoset_iff.mp hσ with rfl | ⟨G, hGF, hGS, hna, hcase⟩
    · exact ⟨∅, Or.inl hF, Finset.empty_subset _, fun u hu ↦ absurd hu (by simp), by simp⟩
    · have hlt := card_lt_of_apexSet_not_subset (orig := orig) hGS hna
      rcases hcase with h | ⟨τ, hτ, rfl⟩
      · obtain ⟨H, hH, hHG, hdel, hsub⟩ := ih G.card hlt h hgood rfl
        exact ⟨H, Or.inl (hH.elim id fun h ↦ h ▸ hGF), hHG.trans hGS, hdel, hsub⟩
      · have hcard : (apexSet orig S).card = 1 := hgood _ (Finset.mem_insert_self _ _)
        have hdel : IsDeletedFace orig S := by
          by_contra hcon
          have hb : (badElts orig S).Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            exact fun h ↦ hcon (badElts_eq_empty_iff.mp h)
          rw [apexSet_card_eq_two hb] at hcard
          omega
        exact ⟨S, Or.inr rfl, Finset.Subset.refl _, hdel,
          fun a ha ↦ sdPoset_vertex_subset hσ ha⟩

/-! ### Full simplices and the good-vertex count -/

/-- The good (original, non-midpoint) vertices of a simplex. -/
def goodVertices (σ : Finset (Finset W)) : Finset (Finset W) :=
  σ.filter fun a ↦ a.card = 1

omit [DecidableEq W] [LinearOrder W] in
theorem mem_goodVertices {σ : Finset (Finset W)} {a : Finset W} :
    a ∈ goodVertices σ ↔ a ∈ σ ∧ a.card = 1 := by
  simp [goodVertices]

/-- A simplex of the subdivision of `S` carried by an *apex flag*
`F₀ ⊊ F₁ ⊊ ⋯ ⊊ F_k = S` of faces of the family whose ranks are `0, 1, …, k`:
this is the general form of a full-dimensional simplex of a pulling
subdivision. -/
inductive IsApexFlag (orig : W → V) (F : Finset (Finset W)) (rank : Finset W → ℕ) :
    Finset W → Finset (Finset W) → Prop
  | base {S : Finset W} (h : rank S = 0) : IsApexFlag orig F rank S ∅
  | step {S G : Finset W} {τ : Finset (Finset W)} (hG : G ∈ F) (hGS : G ⊆ S)
      (hapex : ¬ apexSet orig S ⊆ G) (hrank : rank G + 1 = rank S)
      (hτ : IsApexFlag orig F rank G τ) :
      IsApexFlag orig F rank S (insert (apexSet orig S) τ)

/-- A flag simplex really is a simplex of the subdivision. -/
theorem IsApexFlag.mem_sdPoset {orig : W → V} {F : Finset (Finset W)}
    {rank : Finset W → ℕ} {S : Finset W} {σ : Finset (Finset W)}
    (h : IsApexFlag orig F rank S σ) : σ ∈ sdPoset orig F S := by
  induction h with
  | base h => exact empty_mem_sdPoset _ _ _
  | step hG hGS hapex hrank hτ ih =>
      exact mem_sdPoset_iff.mpr (Or.inr ⟨_, hG, hGS, hapex, Or.inr ⟨_, ih, rfl⟩⟩)

/-- **A flag simplex has exactly `rank S` vertices**, so it is a
top-dimensional simplex of the subdivision of `S`. -/
theorem IsApexFlag.card_eq_rank {orig : W → V} {F : Finset (Finset W)}
    {rank : Finset W → ℕ} {S : Finset W} {σ : Finset (Finset W)}
    (h : IsApexFlag orig F rank S σ) : σ.card = rank S := by
  induction h with
  | base h => simpa using h.symm
  | @step S G τ hG hGS hapex hrank hτ ih =>
      have hanotmem : apexSet orig S ∉ τ := fun hmem ↦
        hapex (sdPoset_vertex_subset hτ.mem_sdPoset hmem)
      rw [Finset.card_insert_of_notMem hanotmem, ih]
      omega

/-- **The good-vertex count of a full simplex.**  If the "projected dimension"
`mm` drops by at most one along a rank step and does not grow along a rank step
whose apex is bad, then every full simplex of the subdivision of `S` has at
least `mm S + 1` good vertices. -/
theorem card_goodVertices_ge {orig : W → V} {F : Finset (Finset W)}
    {rank mm : Finset W → ℕ}
    (hdrop : ∀ S ∈ F, ∀ G ∈ F, G ⊆ S → rank G + 1 = rank S → mm S ≤ mm G + 1)
    (hbad : ∀ S ∈ F, ∀ G ∈ F, G ⊆ S → rank G + 1 = rank S →
      ¬ apexSet orig S ⊆ G → (apexSet orig S).card = 2 → mm S ≤ mm G)
    (hrank1 : ∀ S ∈ F, rank S = 1 → mm S = 0 ∧ (apexSet orig S).card = 1)
    {S : Finset W} (hS : S ∈ F) (hS1 : 1 ≤ rank S)
    {σ : Finset (Finset W)} (hσ : IsApexFlag orig F rank S σ) :
    mm S + 1 ≤ (goodVertices σ).card := by
  induction hσ with
  | base h => omega
  | @step S G τ hG hGS hapex hrank hτ ih =>
      have hane : (apexSet orig S).Nonempty := apexSet_nonempty_of_not_subset hapex
      have hSne : S.Nonempty := hane.mono (apexSet_subset orig S)
      have hcard : (apexSet orig S).card = 1 ∨ (apexSet orig S).card = 2 := by
        by_cases hb : (badElts orig S).Nonempty
        · exact Or.inr (apexSet_card_eq_two hb)
        · rw [Finset.not_nonempty_iff_eq_empty] at hb
          exact Or.inl (apexSet_card_eq_one hb hSne)
      have hanotmem : apexSet orig S ∉ τ := fun hmem ↦
        hapex (sdPoset_vertex_subset hτ.mem_sdPoset hmem)
      have hnotgood : apexSet orig S ∉ goodVertices τ := fun h ↦
        hanotmem (mem_goodVertices.mp h).1
      rcases Nat.eq_zero_or_pos (rank G) with h0 | hpos
      · have hr1 : rank S = 1 := by omega
        obtain ⟨hmm0, hac⟩ := hrank1 S hS hr1
        have hmem : apexSet orig S ∈ goodVertices (insert (apexSet orig S) τ) :=
          mem_goodVertices.mpr ⟨Finset.mem_insert_self _ _, hac⟩
        have hpos' : 0 < (goodVertices (insert (apexSet orig S) τ)).card :=
          Finset.card_pos.mpr ⟨_, hmem⟩
        omega
      · have ihv := ih hG hpos
        rcases hcard with hac | hac
        · have heq : goodVertices (insert (apexSet orig S) τ)
              = insert (apexSet orig S) (goodVertices τ) := by
            simp [goodVertices, Finset.filter_insert, hac]
          rw [heq, Finset.card_insert_of_notMem hnotgood]
          have := hdrop S hS G hG hGS hrank
          omega
        · have hsub : goodVertices τ ⊆ goodVertices (insert (apexSet orig S) τ) := by
            intro x hx
            rw [mem_goodVertices] at hx ⊢
            exact ⟨Finset.mem_insert_of_mem hx.1, hx.2⟩
          have hle := Finset.card_le_card hsub
          have := hbad S hS G hG hGS hrank hapex hac
          omega

end BadEdge
end AffineTverberg
