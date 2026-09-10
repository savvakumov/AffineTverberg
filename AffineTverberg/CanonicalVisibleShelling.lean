import AffineTverberg.CanonicalFace

set_option linter.style.header false

/-!
# The recursive visible shelling inside the canonical face lattice

`VisibleShelling.lean` proves that the facets of `conv s` visible from a point
`q` carry a `CellShelling` certificate in the poset of *all* finite subsets of
`s`.  For the transport to another indexing of the faces — for instance to the
faces of a Cayley join lying above them — that poset is too big: the convex
hull does not preserve intersections of arbitrary subsets, while it does
preserve intersections of canonical faces.

This file reruns the same double induction inside the canonical face lattice
`CanonFace s` of `CanonicalFace.lean`, using that

* every visible facet of a canonical face `u` of `s` is again a canonical face
  of `s` (`IsExposedGens.trans`, a face of a face is a face), so that all cells
  occurring in the certificate — including those of the recursive overlap
  families — are genuine faces of the ambient polytope;
* cell supports transfer between the two posets
  (`mem_cellSupport_canonCells`), so the attaching identity proved in
  `FacetCellOverlap.lean` gives the attaching identity in the canonical face
  lattice.

The geometric content is exactly the one already proved; only the indexing
poset changes.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace PolytopeFace

open CayleyJoin RelInt AffineTverberg.Simplicial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [DecidableEq E]

/-- The dimension function of the canonical face lattice: the affine rank of
the face spanned by the cell. -/
def canonDim (s : Finset E) (c : CanonFace s) : ℕ := hullDim c.1

omit [FiniteDimensional ℝ E] [DecidableEq E] in
/-- Visible facets of a canonical face of `s` are canonical faces of `s`. -/
theorem isExposedGens_of_mem_visibleCells {s u : Finset E} (hu : IsExposedGens s u)
    {q : E} {t : Finset E} (ht : t ∈ visibleCells u q) : IsExposedGens s t := by
  obtain ⟨k, -, rfl⟩ := mem_visibleCells.mp ht
  exact hu.trans (isExposedGens_facetIdx k)

omit [FiniteDimensional ℝ E] in
/-- Meets with a fixed canonical face commute with the passage to the
canonical face lattice. -/
theorem canonCells_image_inf {s : Finset E} {X : Finset (Finset E)}
    (hX : ∀ t ∈ X, IsExposedGens s t) (c : CanonFace s) :
    (canonCells s X).image (fun e ↦ c ⊓ e) = canonCells s (X.image fun e ↦ c.1 ∩ e) := by
  ext t
  constructor
  · intro ht
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ht
    exact mem_canonCells.mpr (Finset.mem_image.mpr ⟨e.1, mem_canonCells.mp he, rfl⟩)
  · intro ht
    obtain ⟨e, he, hte⟩ := Finset.mem_image.mp (mem_canonCells.mp ht)
    exact Finset.mem_image.mpr
      ⟨CanonFace.mk' e (hX e he), mem_canonCells.mpr he, Subtype.ext hte⟩

/-! ### The recursive shelling -/

private theorem cellShelling_visible_canon_aux {s : Finset E} :
    ∀ n m : ℕ, ∀ (u : Finset E) (q : E), IsExposedGens s u →
      arank (convexHull ℝ (u : Set E)) ≤ n →
      (visibleCells u q).card ≤ m →
      u.Nonempty → q ∈ affineSpan ℝ (u : Set E) → (visibleCells u q).Nonempty →
      CellShelling (canonDim s) (arank (convexHull ℝ (u : Set E)) - 1)
        (canonCells s (visibleCells u q)) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro m
    induction m with
    | zero =>
        intro u q _ _ hcard _ _ hne
        exact absurd (Finset.card_pos.mpr hne) (by omega)
    | succ m ihm =>
        intro u q hu hrank hcard hs hq hne
        -- all displayed cells are canonical faces of `s`
        have hcanon : ∀ t ∈ visibleCells u q, IsExposedGens s t :=
          fun t ht ↦ isExposedGens_of_mem_visibleCells hu ht
        -- a generic relative interior base point and the outward direction
        obtain ⟨w, hw, hgen⟩ := exists_generic_basePoint hs q
        set d : E := q - w with hdq
        have hwspan : w ∈ affineSpan ℝ (u : Set E) :=
          convexHull_subset_affineSpan (𝕜 := ℝ) (u : Set E) hw.mem
        have hdmem : d ∈ vectorSpan ℝ (u : Set E) := by
          have := AffineSubspace.vsub_mem_direction hq hwspan
          rwa [direction_affineSpan, vsub_eq_sub] at this
        have hqd : w + (1 : ℝ) • d = q := by rw [hdq, one_smul]; abel
        have hvis : ∀ k : FacetIdx u, facetRhs k < facetForm k q ↔
            0 < facetForm k d ∧ crossParamF k w d < 1 := by
          intro k
          rw [← hqd]
          exact isVisible_endpoint_iff hw k
        -- the visible facet crossed last
        let _ : Fintype (FacetIdx u) := Fintype.ofFinite _
        have hVne : (Finset.univ.filter
            fun k : FacetIdx u ↦ facetRhs k < facetForm k q).Nonempty := by
          obtain ⟨c, hc⟩ := hne
          obtain ⟨k, hk, -⟩ := mem_visibleCells.mp hc
          exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
        obtain ⟨c₀, hc₀mem, hc₀max⟩ :=
          Finset.exists_max_image _ (fun k : FacetIdx u ↦ crossParamF k w d) hVne
        have hc₀vis : facetRhs c₀ < facetForm c₀ q :=
          (Finset.mem_filter.mp hc₀mem).2
        have hmax : ∀ k : FacetIdx u, facetRhs k < facetForm k q →
            crossParamF k w d ≤ crossParamF c₀ w d :=
          fun k hk ↦ hc₀max k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩)
        have hc₀d : 0 < facetForm c₀ d := ((hvis c₀).1 hc₀vis).1
        set q₀ : E := crossPoint c₀ w d with hq₀def
        -- the peeling identity
        have hpeel : visibleCells u q₀ = (visibleCells u q).erase c₀.1.1 :=
          visibleCells_crossPoint hw hgen hc₀vis hmax
        have hc₀in : c₀.1.1 ∈ visibleCells u q := mem_visibleCells_self c₀ hc₀vis
        have hc₀canon : IsExposedGens s c₀.1.1 := hcanon _ hc₀in
        -- basic geometry of the crossing point
        have hq₀span : q₀ ∈ affineSpan ℝ (u : Set E) :=
          mem_affineSpan_line hwspan hdmem _
        have hq₀tight : facetForm c₀ q₀ = facetRhs c₀ :=
          facetForm_crossPoint c₀ (ne_of_gt hc₀d)
        have hq₀facetspan : q₀ ∈ affineSpan ℝ ((c₀.1.1 : Finset E) : Set E) := by
          have hmem : q₀ ∈ {x : E | x ∈ affineSpan ℝ (u : Set E) ∧
              facetForm c₀ x = facetRhs c₀} := ⟨hq₀span, hq₀tight⟩
          rwa [affineSpan_facet_eq hs c₀] at hmem
        -- the dimension of the new cell
        have hcodim : arank (convexHull ℝ ((c₀.1.1 : Finset E) : Set E)) + 1 =
            arank (convexHull ℝ (u : Set E)) := facetIdx_codim c₀
        have hc₀ne : (CanonFace.mk' c₀.1.1 hc₀canon) ≠ ⊥ := by
          rw [CanonFace.ne_bot_iff]
          exact facetIdx_nonempty c₀
        rcases Finset.eq_empty_or_nonempty (visibleCells u q₀) with hemp | hSne
        · -- only one visible facet: the base case of the shelling
          have hsingle : visibleCells u q = {c₀.1.1} := by
            rw [hpeel] at hemp
            ext c
            simp only [Finset.mem_singleton]
            constructor
            · intro hc
              by_contra hcc
              have : c ∈ (visibleCells u q).erase c₀.1.1 :=
                Finset.mem_erase.mpr ⟨hcc, hc⟩
              rw [hemp] at this
              exact absurd this (Finset.notMem_empty c)
            · rintro rfl
              exact hc₀in
          have hcells : canonCells s (visibleCells u q) =
              {(CanonFace.mk' c₀.1.1 hc₀canon)} := by
            rw [hsingle, show ({c₀.1.1} : Finset (Finset E)) = insert c₀.1.1 ∅ from rfl,
              canonCells_insert hc₀canon, canonCells_empty]
            rfl
          rw [hcells]
          have hdim : canonDim s (CanonFace.mk' c₀.1.1 hc₀canon) =
              arank (convexHull ℝ (u : Set E)) - 1 := by
            simp only [canonDim, hullDim, CanonFace.coe_mk']; omega
          rw [← hdim]
          exact CellShelling.single _ hc₀ne
        · -- attach the last facet along its visible ridges
          obtain ⟨c, hc⟩ := hSne
          obtain ⟨k, hkvis, -⟩ := mem_visibleCells.mp hc
          have hq₀out : q₀ ∉ convexHull ℝ (u : Set E) := by
            intro hmem
            exact absurd (facetForm_le_facetRhs k hmem) (not_le.mpr hkvis)
          have hq₀outF : q₀ ∉ convexHull ℝ ((c₀.1.1 : Finset E) : Set E) := by
            intro hmem
            exact hq₀out (facetFace_subset c₀ hmem)
          obtain ⟨i, hi⟩ : ∃ i : FacetIdx (c₀.1.1 : Finset E),
              ¬ facetForm i q₀ ≤ facetRhs i := by
            by_contra hcon
            push Not at hcon
            exact hq₀outF ((mem_convexHull_iff_forall_facetIdx
              (facetIdx_nonempty c₀) hq₀facetspan).2 fun i ↦ hcon i)
          have hivis : facetRhs i < facetForm i q₀ := not_le.mp hi
          have hTne : (visibleCells (c₀.1.1 : Finset E) q₀).Nonempty :=
            ⟨i.1.1, mem_visibleCells_self i hivis⟩
          -- the ambient dimension is at least two
          have hridge := facetIdx_codim i
          have hA2 : 2 ≤ arank (convexHull ℝ (u : Set E)) := by omega
          have hn1 : 1 ≤ n := by omega
          -- the recursive shelling of the ridges, by the outer induction
          have hT : CellShelling (canonDim s)
              (arank (convexHull ℝ ((c₀.1.1 : Finset E) : Set E)) - 1)
              (canonCells s (visibleCells (c₀.1.1 : Finset E) q₀)) :=
            ihn (n - 1) (by omega) (visibleCells (c₀.1.1 : Finset E) q₀).card
              (c₀.1.1) q₀ hc₀canon (by omega) le_rfl (facetIdx_nonempty c₀)
              hq₀facetspan hTne
          -- the shelling of the remaining visible facets, by the inner induction
          have hcard₀ : (visibleCells u q₀).card ≤ m := by
            rw [hpeel, Finset.card_erase_of_mem hc₀in]
            have : 1 ≤ (visibleCells u q).card := Finset.card_pos.mpr hne
            omega
          have hS : CellShelling (canonDim s) (arank (convexHull ℝ (u : Set E)) - 1)
              (canonCells s (visibleCells u q₀)) :=
            ihm u q₀ hu hrank hcard₀ hs hq₀span ⟨c, hc⟩
          -- the canonicity of the two recursive families
          have hcanon₀ : ∀ t ∈ visibleCells u q₀, IsExposedGens s t :=
            fun t ht ↦ isExposedGens_of_mem_visibleCells hu ht
          have hcanonT : ∀ t ∈ visibleCells (c₀.1.1 : Finset E) q₀, IsExposedGens s t :=
            fun t ht ↦ isExposedGens_of_mem_visibleCells hc₀canon ht
          have hcanonI : ∀ t ∈ (visibleCells u q₀).image (fun e ↦ (c₀.1.1 : Finset E) ∩ e),
              IsExposedGens s t := by
            intro t ht
            obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ht
            exact hc₀canon.inter (hcanon₀ e he)
          -- the attaching identity, transported to the canonical face lattice
          have hoverlapAmb : cellSupport ((visibleCells u q₀).image
              fun e ↦ (c₀.1.1 : Finset E) ∩ e) =
              cellSupport (visibleCells (c₀.1.1 : Finset E) q₀) := by
            have := cellSupport_visible_overlap hs c₀ hq₀span hq₀tight
            rwa [visibleOverlapCells_eq_image] at this
          have hoverlap : cellSupport ((canonCells s (visibleCells u q₀)).image
              fun e ↦ (CanonFace.mk' c₀.1.1 hc₀canon) ⊓ e) =
              cellSupport (canonCells s (visibleCells (c₀.1.1 : Finset E) q₀)) := by
            rw [canonCells_image_inf hcanon₀ (CanonFace.mk' c₀.1.1 hc₀canon)]
            exact cellSupport_canonCells_congr hcanonI hcanonT hoverlapAmb
          have hnew : (CanonFace.mk' c₀.1.1 hc₀canon) ∉
              canonCells s (visibleCells u q₀) := by
            rw [mem_canonCells, hpeel]
            exact fun h ↦ (Finset.mem_erase.mp h).1 rfl
          have hdimc : canonDim s (CanonFace.mk' c₀.1.1 hc₀canon) =
              (arank (convexHull ℝ (u : Set E)) - 2) + 1 := by
            simp only [canonDim, hullDim, CanonFace.coe_mk']; omega
          have hkey := CellShelling.attach (dim := canonDim s)
            (n := arank (convexHull ℝ (u : Set E)) - 2)
            (S := canonCells s (visibleCells u q₀))
            (T := canonCells s (visibleCells (c₀.1.1 : Finset E) q₀))
            (CanonFace.mk' c₀.1.1 hc₀canon)
            (by
              have : arank (convexHull ℝ (u : Set E)) - 2 + 1 =
                  arank (convexHull ℝ (u : Set E)) - 1 := by omega
              rw [this]; exact hS)
            hc₀ne hdimc hnew
            (by
              have : arank (convexHull ℝ (u : Set E)) - 2 =
                  arank (convexHull ℝ ((c₀.1.1 : Finset E) : Set E)) - 1 := by omega
              rw [this]; exact hT)
            hoverlap
          have hins : insert (CanonFace.mk' c₀.1.1 hc₀canon)
              (canonCells s (visibleCells u q₀)) = canonCells s (visibleCells u q) := by
            rw [← canonCells_insert hc₀canon, hpeel, Finset.insert_erase hc₀in]
          have hdegree : arank (convexHull ℝ (u : Set E)) - 2 + 1 =
              arank (convexHull ℝ (u : Set E)) - 1 := by omega
          rw [hins, hdegree] at hkey
          exact hkey

/-- **The visible part of the boundary of a polytope is recursively shelled, in
the canonical face lattice.**  Every cell of the certificate is a genuine
exposed face of `conv s`. -/
theorem cellShelling_visibleCells_canon {s : Finset E} (hs : s.Nonempty) {q : E}
    (hq : q ∈ affineSpan ℝ (s : Set E)) (hne : (visibleCells s q).Nonempty) :
    CellShelling (canonDim s) (arank (convexHull ℝ (s : Set E)) - 1)
      (canonCells s (visibleCells s q)) :=
  cellShelling_visible_canon_aux (arank (convexHull ℝ (s : Set E)))
    (visibleCells s q).card s q (isExposedGens_self s) le_rfl le_rfl hs hq hne

/-- The same certificate for a point of the affine span outside the
polytope. -/
theorem cellShelling_visibleCells_canon_of_notMem {s : Finset E} (hs : s.Nonempty) {q : E}
    (hq : q ∈ affineSpan ℝ (s : Set E)) (hqout : q ∉ convexHull ℝ (s : Set E)) :
    CellShelling (canonDim s) (arank (convexHull ℝ (s : Set E)) - 1)
      (canonCells s (visibleCells s q)) :=
  cellShelling_visibleCells_canon hs hq (visibleCells_nonempty_of_notMem hs hq hqout)

end PolytopeFace
end AffineTverberg
