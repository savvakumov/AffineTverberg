import AffineTverberg.FacetCellOverlap
import AffineTverberg.RelativeLineShelling
import AffineTverberg.GenericBasePoint

set_option linter.style.header false

/-!
# The recursive visible shelling of a polytope

Fix a finite generating set `s` and a point `q` of its affine span.  The facets
of `conv s` *visible from* `q` are those whose inequality is violated at `q`;
their canonical generator sets form the finite family `visibleCells s q`.

This file proves that this family always carries a
`ShellableGluing.CellShelling` certificate, by a double induction:

* an outer induction on the affine dimension of `conv s`, which supplies the
  recursive shelling of the ridges of a facet (one dimension lower), and
* an inner induction on the number of visible facets, which peels off the
  *last* facet crossed by an outward ray.

The ray is chosen through a generic relative interior point `w`
(`exists_generic_basePoint`), so that all crossing parameters of the visible
facets are distinct.  Its last crossing point `q₀` sees exactly the remaining
visible facets (`visibleCells_crossPoint`), while inside the affine hull of the
new facet it sees exactly the ridges along which that facet is attached
(`cellSupport_visible_overlap`).  This is precisely the data of
`CellShelling.attach`; the first crossing gives `CellShelling.single`.

Only the visible part of the boundary is shelled — no claim is made about the
whole boundary sphere, and a point (dimension zero) is never given a second
visible cell along an outward ray.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace PolytopeFace

open CayleyJoin RelInt AffineTverberg.Simplicial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [DecidableEq E]

/-- The dimension of a cell: the affine dimension of the face it spans. -/
def hullDim (c : Finset E) : ℕ := arank (convexHull ℝ (c : Set E))

omit [FiniteDimensional ℝ E] [DecidableEq E] in
/-- The canonical generator set determines the facet. -/
theorem facetIdx_eq_of_index_eq {s : Finset E} {i k : FacetIdx s}
    (h : i.1.1 = k.1.1) : i = k :=
  Subtype.ext (Subtype.ext h)

omit [FiniteDimensional ℝ E] [DecidableEq E] in
/-- A facet visible from `q` contributes its generator set to `visibleCells`. -/
theorem mem_visibleCells_self {s : Finset E} {q : E} (k : FacetIdx s)
    (hk : facetRhs k < facetForm k q) : k.1.1 ∈ visibleCells s q :=
  mem_visibleCells.mpr ⟨k, hk, rfl⟩

/-! ### The last crossing point of an outward ray -/

section Ray

variable {s : Finset E} {w d : E}

omit [FiniteDimensional ℝ E] [DecidableEq E] in
/-- Visibility from the endpoint of the ray, in terms of crossing parameters. -/
theorem isVisible_endpoint_iff (hw : IsRelInt (convexHull ℝ (s : Set E)) w)
    (k : FacetIdx s) :
    facetRhs k < facetForm k (w + (1 : ℝ) • d) ↔
      0 < facetForm k d ∧ crossParamF k w d < 1 :=
  facetForm_lt_line_iff hw k zero_le_one

end Ray

omit [FiniteDimensional ℝ E] in
/-- **The visible facets at the last crossing point.**  If `c₀` is the visible
facet crossed last by the ray from a relative interior point `w` towards `q`,
then the facets visible from its crossing point are exactly the remaining
visible facets. -/
theorem visibleCells_crossPoint {s : Finset E} {q w : E}
    (hw : IsRelInt (convexHull ℝ (s : Set E)) w)
    (hgen : ∀ i k : FacetIdx s, i ≠ k →
      facetRhs i < facetForm i q → facetRhs k < facetForm k q →
      crossParamF i w (q - w) ≠ crossParamF k w (q - w))
    {c₀ : FacetIdx s} (hc₀vis : facetRhs c₀ < facetForm c₀ q)
    (hmax : ∀ k : FacetIdx s, facetRhs k < facetForm k q →
      crossParamF k w (q - w) ≤ crossParamF c₀ w (q - w)) :
    visibleCells s (crossPoint c₀ w (q - w)) =
      (visibleCells s q).erase c₀.1.1 := by
  classical
  set d : E := q - w with hdq
  have hqd : w + (1 : ℝ) • d = q := by
    rw [hdq, one_smul]; abel
  have hvis : ∀ k : FacetIdx s, facetRhs k < facetForm k q ↔
      0 < facetForm k d ∧ crossParamF k w d < 1 := by
    intro k
    rw [← hqd]
    exact isVisible_endpoint_iff hw k
  have hc₀d : 0 < facetForm c₀ d := ((hvis c₀).1 hc₀vis).1
  have hcross : ∀ k : FacetIdx s,
      facetRhs k < facetForm k (crossPoint c₀ w d) ↔
        0 < facetForm k d ∧ crossParamF k w d < crossParamF c₀ w d :=
    fun k ↦ isVisible_at_crossPoint_iff hw hc₀d k
  ext c
  rw [Finset.mem_erase, mem_visibleCells, mem_visibleCells]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨hkd, hklt⟩ := (hcross k).1 hk
    have hkvis : facetRhs k < facetForm k q :=
      (hvis k).2 ⟨hkd, lt_trans hklt ((hvis c₀).1 hc₀vis).2⟩
    refine ⟨?_, k, hkvis, rfl⟩
    intro hcc
    have : k = c₀ := facetIdx_eq_of_index_eq hcc
    subst this
    exact lt_irrefl _ hklt
  · rintro ⟨hne, k, hkvis, rfl⟩
    have hkc : k ≠ c₀ := fun h ↦ hne (by rw [h])
    refine ⟨k, (hcross k).2 ⟨((hvis k).1 hkvis).1, ?_⟩, rfl⟩
    exact lt_of_le_of_ne (hmax k hkvis) (hgen k c₀ hkc hkvis hc₀vis)

/-! ### The recursive shelling -/

private theorem cellShelling_visible_aux :
    ∀ n m : ℕ, ∀ (s : Finset E) (q : E),
      arank (convexHull ℝ (s : Set E)) ≤ n →
      (visibleCells s q).card ≤ m →
      s.Nonempty → q ∈ affineSpan ℝ (s : Set E) → (visibleCells s q).Nonempty →
      CellShelling hullDim (arank (convexHull ℝ (s : Set E)) - 1)
        (visibleCells s q) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro m
    induction m with
    | zero =>
        intro s q _ hcard _ _ hne
        exact absurd (Finset.card_pos.mpr hne) (by omega)
    | succ m ihm =>
        intro s q hrank hcard hs hq hne
        -- a generic relative interior base point and the outward direction
        obtain ⟨w, hw, hgen⟩ := exists_generic_basePoint hs q
        set d : E := q - w with hdq
        have hwspan : w ∈ affineSpan ℝ (s : Set E) :=
          convexHull_subset_affineSpan (𝕜 := ℝ) (s : Set E) hw.mem
        have hdmem : d ∈ vectorSpan ℝ (s : Set E) := by
          have := AffineSubspace.vsub_mem_direction hq hwspan
          rwa [direction_affineSpan, vsub_eq_sub] at this
        have hqd : w + (1 : ℝ) • d = q := by rw [hdq, one_smul]; abel
        have hvis : ∀ k : FacetIdx s, facetRhs k < facetForm k q ↔
            0 < facetForm k d ∧ crossParamF k w d < 1 := by
          intro k
          rw [← hqd]
          exact isVisible_endpoint_iff hw k
        -- the visible facet crossed last
        let _ : Fintype (FacetIdx s) := Fintype.ofFinite _
        have hVne : (Finset.univ.filter
            fun k : FacetIdx s ↦ facetRhs k < facetForm k q).Nonempty := by
          obtain ⟨c, hc⟩ := hne
          obtain ⟨k, hk, -⟩ := mem_visibleCells.mp hc
          exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
        obtain ⟨c₀, hc₀mem, hc₀max⟩ :=
          Finset.exists_max_image _ (fun k : FacetIdx s ↦ crossParamF k w d) hVne
        have hc₀vis : facetRhs c₀ < facetForm c₀ q :=
          (Finset.mem_filter.mp hc₀mem).2
        have hmax : ∀ k : FacetIdx s, facetRhs k < facetForm k q →
            crossParamF k w d ≤ crossParamF c₀ w d :=
          fun k hk ↦ hc₀max k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩)
        have hc₀d : 0 < facetForm c₀ d := ((hvis c₀).1 hc₀vis).1
        set q₀ : E := crossPoint c₀ w d with hq₀def
        -- the peeling identity
        have hpeel : visibleCells s q₀ = (visibleCells s q).erase c₀.1.1 :=
          visibleCells_crossPoint hw hgen hc₀vis hmax
        have hc₀in : c₀.1.1 ∈ visibleCells s q := mem_visibleCells_self c₀ hc₀vis
        -- basic geometry of the crossing point
        have hq₀span : q₀ ∈ affineSpan ℝ (s : Set E) :=
          mem_affineSpan_line hwspan hdmem _
        have hq₀tight : facetForm c₀ q₀ = facetRhs c₀ :=
          facetForm_crossPoint c₀ (ne_of_gt hc₀d)
        have hq₀facetspan : q₀ ∈ affineSpan ℝ ((c₀.1.1 : Finset E) : Set E) := by
          have hmem : q₀ ∈ {x : E | x ∈ affineSpan ℝ (s : Set E) ∧
              facetForm c₀ x = facetRhs c₀} := ⟨hq₀span, hq₀tight⟩
          rwa [affineSpan_facet_eq hs c₀] at hmem
        -- the dimension of the new cell
        have hcodim : arank (convexHull ℝ ((c₀.1.1 : Finset E) : Set E)) + 1 =
            arank (convexHull ℝ (s : Set E)) := facetIdx_codim c₀
        have hc₀ne : (c₀.1.1 : Finset E) ≠ ⊥ := by
          rw [Finset.bot_eq_empty, ← Finset.nonempty_iff_ne_empty]
          exact facetIdx_nonempty c₀
        rcases Finset.eq_empty_or_nonempty (visibleCells s q₀) with hemp | hSne
        · -- only one visible facet: the base case of the shelling
          have hsingle : visibleCells s q = {c₀.1.1} := by
            rw [hpeel] at hemp
            ext c
            simp only [Finset.mem_singleton]
            constructor
            · intro hc
              by_contra hcc
              have : c ∈ (visibleCells s q).erase c₀.1.1 :=
                Finset.mem_erase.mpr ⟨hcc, hc⟩
              rw [hemp] at this
              exact absurd this (Finset.notMem_empty c)
            · rintro rfl
              exact hc₀in
          rw [hsingle]
          have hdim : hullDim (c₀.1.1 : Finset E) =
              arank (convexHull ℝ (s : Set E)) - 1 := by
            rw [hullDim]; omega
          rw [← hdim]
          exact CellShelling.single _ hc₀ne
        · -- attach the last facet along its visible ridges
          -- `q₀` lies outside the polytope, hence outside the facet
          obtain ⟨c, hc⟩ := hSne
          obtain ⟨k, hkvis, -⟩ := mem_visibleCells.mp hc
          have hq₀out : q₀ ∉ convexHull ℝ (s : Set E) := by
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
          have hA2 : 2 ≤ arank (convexHull ℝ (s : Set E)) := by omega
          have hn1 : 1 ≤ n := by omega
          -- the recursive shelling of the ridges, by the outer induction
          have hT : CellShelling hullDim
              (arank (convexHull ℝ ((c₀.1.1 : Finset E) : Set E)) - 1)
              (visibleCells (c₀.1.1 : Finset E) q₀) :=
            ihn (n - 1) (by omega) (visibleCells (c₀.1.1 : Finset E) q₀).card
              (c₀.1.1) q₀ (by omega) le_rfl (facetIdx_nonempty c₀)
              hq₀facetspan hTne
          -- the shelling of the remaining visible facets, by the inner induction
          have hcard₀ : (visibleCells s q₀).card ≤ m := by
            rw [hpeel, Finset.card_erase_of_mem hc₀in]
            have : 1 ≤ (visibleCells s q).card := Finset.card_pos.mpr hne
            omega
          have hS : CellShelling hullDim (arank (convexHull ℝ (s : Set E)) - 1)
              (visibleCells s q₀) :=
            ihm s q₀ hrank hcard₀ hs hq₀span ⟨c, hc⟩
          -- assemble
          have hoverlap : cellSupport ((visibleCells s q₀).image
              fun e ↦ (c₀.1.1 : Finset E) ⊓ e) =
              cellSupport (visibleCells (c₀.1.1 : Finset E) q₀) := by
            have := cellSupport_visible_overlap hs c₀ hq₀span hq₀tight
            rwa [visibleOverlapCells_eq_image] at this
          have hnew : (c₀.1.1 : Finset E) ∉ visibleCells s q₀ := by
            rw [hpeel]
            exact fun h ↦ (Finset.mem_erase.mp h).1 rfl
          have hdimc : hullDim (c₀.1.1 : Finset E) =
              (arank (convexHull ℝ (s : Set E)) - 2) + 1 := by
            rw [hullDim]; omega
          have hkey := CellShelling.attach (dim := hullDim)
            (n := arank (convexHull ℝ (s : Set E)) - 2)
            (S := visibleCells s q₀)
            (T := visibleCells (c₀.1.1 : Finset E) q₀) (c₀.1.1)
            (by
              have : arank (convexHull ℝ (s : Set E)) - 2 + 1 =
                  arank (convexHull ℝ (s : Set E)) - 1 := by omega
              rw [this]; exact hS)
            hc₀ne hdimc hnew
            (by
              have : arank (convexHull ℝ (s : Set E)) - 2 =
                  arank (convexHull ℝ ((c₀.1.1 : Finset E) : Set E)) - 1 := by omega
              rw [this]; exact hT)
            hoverlap
          have hins : insert (c₀.1.1 : Finset E) (visibleCells s q₀) =
              visibleCells s q := by
            rw [hpeel, Finset.insert_erase hc₀in]
          have hdegree : arank (convexHull ℝ (s : Set E)) - 2 + 1 =
              arank (convexHull ℝ (s : Set E)) - 1 := by omega
          rw [hins, hdegree] at hkey
          exact hkey

/-- **The visible part of the boundary of a polytope is recursively shelled.**
For a finite generating set `s` and any point `q` of its affine span from which
some facet is visible, the canonical generator sets of the visible facets carry
a `CellShelling` certificate in the dimension of the facets. -/
theorem cellShelling_visibleCells {s : Finset E} (hs : s.Nonempty) {q : E}
    (hq : q ∈ affineSpan ℝ (s : Set E)) (hne : (visibleCells s q).Nonempty) :
    CellShelling hullDim (arank (convexHull ℝ (s : Set E)) - 1)
      (visibleCells s q) :=
  cellShelling_visible_aux (arank (convexHull ℝ (s : Set E)))
    (visibleCells s q).card s q le_rfl le_rfl hs hq hne

omit [DecidableEq E] in
/-- **Nonvacuity of the visible family.**  A point of the affine span outside
the polytope sees at least one facet. -/
theorem visibleCells_nonempty_of_notMem {s : Finset E} (hs : s.Nonempty) {q : E}
    (hq : q ∈ affineSpan ℝ (s : Set E)) (hqout : q ∉ convexHull ℝ (s : Set E)) :
    (visibleCells s q).Nonempty := by
  classical
  by_contra hcon
  rw [Finset.not_nonempty_iff_eq_empty] at hcon
  refine hqout ((mem_convexHull_iff_forall_facetIdx hs hq).2 fun j ↦ ?_)
  by_contra hj
  have : j.1.1 ∈ visibleCells s q := mem_visibleCells_self j (not_le.mp hj)
  rw [hcon] at this
  exact absurd this (Finset.notMem_empty _)

/-- **The visible boundary seen from an exterior point of the affine span is
recursively shelled.** -/
theorem cellShelling_visibleCells_of_notMem {s : Finset E} (hs : s.Nonempty) {q : E}
    (hq : q ∈ affineSpan ℝ (s : Set E)) (hqout : q ∉ convexHull ℝ (s : Set E)) :
    CellShelling hullDim (arank (convexHull ℝ (s : Set E)) - 1)
      (visibleCells s q) :=
  cellShelling_visibleCells hs hq (visibleCells_nonempty_of_notMem hs hq hqout)

end PolytopeFace
end AffineTverberg
