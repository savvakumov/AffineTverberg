import AffineTverberg.FacetIntersection
import AffineTverberg.ShellableGluing

set_option linter.style.header false

/-!
# The attaching overlap in the combinatorial form of a cell shelling

`ShellableGluing.CellShelling` records an attaching step by the equality of two
*cell supports*: the faces below the intersections of the new cell with the
previously attached ones, and the faces below a recursively shelled family one
dimension lower.  This file proves exactly that equality for a polytope,
with cells taken to be the canonical generator sets of its faces:

* `visibleCells s q` — the generator sets of the facets of `conv s` visible from
  a point `q`, and `visibleOverlapCells s j q` — their intersections with the
  facet `j`;
* `subset_of_convexHull_subset` — for canonical face index sets, containment of
  faces is containment of generator sets;
* `exists_visible_ridge_supset` — the intersection of the facet `j` with a
  visible facet `k` (when nonempty) is contained in a ridge of `j` visible from
  the same point;
* `exists_visible_facet_inter_eq_ridge` — conversely every visible ridge of `j`
  *is* such an intersection;
* `cellSupport_visible_overlap` — **the two cell supports coincide**: the
  nonempty generator sets below some `j ∩ k` with `k` visible are exactly the
  nonempty generator sets below some ridge of `j` visible from the same point.

This is the attaching hypothesis of `CellShelling.attach` for the visible part
of the boundary.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace PolytopeFace

open CayleyJoin RelInt AffineTverberg.Simplicial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A generator of the polytope lying on a facet belongs to the canonical index
of that facet. -/
theorem mem_index_of_mem_facetFace {s : Finset E} (j : FacetIdx s) {v : E}
    (hv : v ∈ s) (hvF : v ∈ facetFace j) : v ∈ j.1.1 := by
  rw [facetIdx_index_eq_contactGens j]
  exact mem_contactGens.mpr ⟨hv, ((mem_facetFace_iff j).1 hvF).2⟩

omit [FiniteDimensional ℝ E] in
/-- For canonical index sets of faces, containment of faces is containment of
generator sets. -/
theorem subset_of_convexHull_subset {s : Finset E} {a : Finset E} (has : a ⊆ s)
    (j : FacetIdx s) (h : convexHull ℝ (a : Set E) ⊆ facetFace j) : a ⊆ j.1.1 := by
  intro v hv
  exact mem_index_of_mem_facetFace j (has hv)
    (h (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)))

/-! ### The two directions of the overlap, per facet -/

/-- **A nonempty intersection with a visible facet lies in a visible ridge.** -/
theorem exists_visible_ridge_supset {s : Finset E} (hs : s.Nonempty)
    (j : FacetIdx s) {q : E} (hq : q ∈ affineSpan ℝ (s : Set E))
    (hqj : facetForm j q = facetRhs j) {k : FacetIdx s}
    (hkvis : facetRhs k < facetForm k q)
    {x : E} (hx : x ∈ facetFace j ∩ facetFace k) :
    ∃ i : FacetIdx j.1.1, facetRhs i < facetForm i q ∧
      facetFace j ∩ facetFace k ⊆ facetFace i := by
  classical
  have ht : (j.1.1).Nonempty := facetIdx_nonempty j
  have htsub : j.1.1 ⊆ s := Finset.mem_powerset.mp j.1.2
  have hFP : convexHull ℝ ((j.1.1 : Finset E) : Set E) ⊆ convexHull ℝ (s : Set E) :=
    convexHull_mono (by exact_mod_cast htsub)
  have hqt : q ∈ affineSpan ℝ ((j.1.1 : Finset E) : Set E) := by
    have hmem : q ∈ {y : E | y ∈ affineSpan ℝ (s : Set E) ∧ facetForm j y = facetRhs j} :=
      ⟨hq, hqj⟩
    rw [affineSpan_facet_eq hs j] at hmem
    exact hmem
  have hvalid : ∀ y ∈ convexHull ℝ ((j.1.1 : Finset E) : Set E),
      facetForm k y ≤ facetRhs k := fun y hy ↦ facetForm_le_facetRhs k (hFP hy)
  have hxt : x ∈ convexHull ℝ ((j.1.1 : Finset E) : Set E) := hx.1
  have hxform : facetForm k x = facetRhs k := ((mem_facetFace_iff k).1 hx.2).2
  have hcontact := convexHull_contactGens_of_attained hvalid hxt hxform
  have hne : (contactGens (j.1.1) (facetForm k) (facetRhs k)).Nonempty := by
    by_contra hcon
    have hempty : contactGens (j.1.1) (facetForm k) (facetRhs k) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hcon
    have hxexp : x ∈ exposedBy (convexHull ℝ ((j.1.1 : Finset E) : Set E))
        (facetForm k) := ⟨hxt, fun y hy ↦ by rw [hxform]; exact hvalid y hy⟩
    rw [← hcontact, hempty] at hxexp
    simp at hxexp
  obtain ⟨i, hisub, hivis⟩ :=
    exists_facetIdx_face_subset_violated ht hvalid hne hqt hkvis
  refine ⟨i, hivis, ?_⟩
  intro y hy
  apply hisub
  rw [hcontact]
  exact ⟨hy.1, fun z hz ↦ by
    rw [((mem_facetFace_iff k).1 hy.2).2]
    exact hvalid z hz⟩

/-- **Every visible ridge is the intersection with a visible facet.** -/
theorem exists_visible_facet_inter_eq_ridge {s : Finset E} (hs : s.Nonempty)
    (j : FacetIdx s) {q : E} (hq : q ∈ affineSpan ℝ (s : Set E))
    (hqj : facetForm j q = facetRhs j) (i : FacetIdx j.1.1)
    (hivis : facetRhs i < facetForm i q) :
    ∃ k : FacetIdx s, facetRhs k < facetForm k q ∧
      facetFace j ∩ facetFace k = facetFace i := by
  have hqt : q ∈ affineSpan ℝ ((j.1.1 : Finset E) : Set E) := by
    have hmem : q ∈ {y : E | y ∈ affineSpan ℝ (s : Set E) ∧ facetForm j y = facetRhs j} :=
      ⟨hq, hqj⟩
    rw [affineSpan_facet_eq hs j] at hmem
    exact hmem
  obtain ⟨k, -, hinter, horient⟩ := exists_ambient_facet_of_ridge hs j i
  exact ⟨k, (horient q hqt).1 hivis, hinter.symm⟩

/-! ### The visible cells and their overlaps -/

variable [DecidableEq E]

open Classical in
/-- The canonical generator sets of the facets of `conv s` visible from `q`. -/
def visibleCells (s : Finset E) (q : E) : Finset (Finset E) :=
  s.powerset.filter fun t ↦ ∃ k : FacetIdx s, k.1.1 = t ∧ facetRhs k < facetForm k q

omit [FiniteDimensional ℝ E] [DecidableEq E] in
theorem mem_visibleCells {s : Finset E} {q : E} {c : Finset E} :
    c ∈ visibleCells s q ↔
      ∃ k : FacetIdx s, facetRhs k < facetForm k q ∧ k.1.1 = c := by
  classical
  unfold visibleCells
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, k, hk, hvis⟩
    exact ⟨k, hvis, hk⟩
  · rintro ⟨k, hvis, rfl⟩
    exact ⟨k.1.2, k, rfl, hvis⟩

/-- The generator sets of the intersections of the facet `j` with the facets
visible from `q`. -/
def visibleOverlapCells (s : Finset E) (j : FacetIdx s) (q : E) :
    Finset (Finset E) :=
  (visibleCells s q).image fun e ↦ j.1.1 ∩ e

omit [FiniteDimensional ℝ E] in
theorem visibleOverlapCells_eq_image {s : Finset E} (j : FacetIdx s) (q : E) :
    visibleOverlapCells s j q = (visibleCells s q).image fun e ↦ j.1.1 ∩ e :=
  rfl

omit [FiniteDimensional ℝ E] in
theorem mem_visibleOverlapCells {s : Finset E} {j : FacetIdx s} {q : E}
    {c : Finset E} :
    c ∈ visibleOverlapCells s j q ↔
      ∃ k : FacetIdx s, facetRhs k < facetForm k q ∧ j.1.1 ∩ k.1.1 = c := by
  rw [visibleOverlapCells, Finset.mem_image]
  constructor
  · rintro ⟨e, he, rfl⟩
    obtain ⟨k, hk, rfl⟩ := mem_visibleCells.mp he
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.1.1, mem_visibleCells.mpr ⟨k, hk, rfl⟩, rfl⟩

/-- **The attaching hypothesis of a cell shelling, in the geometric case.**
The nonempty generator sets below an intersection of the facet `j` with a facet
visible from `q` are exactly those below a ridge of `j` visible from `q`. -/
theorem cellSupport_visible_overlap {s : Finset E} (hs : s.Nonempty)
    (j : FacetIdx s) {q : E} (hq : q ∈ affineSpan ℝ (s : Set E))
    (hqj : facetForm j q = facetRhs j) :
    cellSupport (visibleOverlapCells s j q) = cellSupport (visibleCells j.1.1 q) := by
  have htsub : j.1.1 ⊆ s := Finset.mem_powerset.mp j.1.2
  ext e
  simp only [cellSupport, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hene, c, hc, hec⟩
    obtain ⟨k, hkvis, rfl⟩ := mem_visibleOverlapCells.mp hc
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hene
    have hvj : v ∈ j.1.1 := Finset.mem_of_mem_inter_left (hec hv)
    have hvk : v ∈ k.1.1 := Finset.mem_of_mem_inter_right (hec hv)
    have hxmem : v ∈ facetFace j ∩ facetFace k :=
      ⟨subset_convexHull ℝ _ (Finset.mem_coe.mpr hvj),
        subset_convexHull ℝ _ (Finset.mem_coe.mpr hvk)⟩
    obtain ⟨i, hivis, hisub⟩ :=
      exists_visible_ridge_supset hs j hq hqj hkvis hxmem
    refine ⟨hene, i.1.1, mem_visibleCells.mpr ⟨i, hivis, rfl⟩, ?_⟩
    have hsub : ((j.1.1 ∩ k.1.1 : Finset E)) ⊆ i.1.1 := by
      refine subset_of_convexHull_subset (a := j.1.1 ∩ k.1.1)
        (fun v hv ↦ Finset.mem_of_mem_inter_left hv) i ?_
      rw [← facetFace_inter_eq_convexHull_inter j k]
      exact hisub
    exact hec.trans hsub
  · rintro ⟨hene, c, hc, hec⟩
    obtain ⟨i, hivis, rfl⟩ := mem_visibleCells.mp hc
    obtain ⟨k, hkvis, hinter⟩ :=
      exists_visible_facet_inter_eq_ridge hs j hq hqj i hivis
    refine ⟨hene, j.1.1 ∩ k.1.1, mem_visibleOverlapCells.mpr ⟨k, hkvis, rfl⟩, ?_⟩
    have hsub : (i.1.1 : Finset E) ⊆ j.1.1 ∩ k.1.1 := by
      intro v hv
      have hvj : v ∈ j.1.1 := Finset.mem_powerset.mp i.1.2 hv
      have hvF : v ∈ facetFace i := subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)
      rw [← hinter] at hvF
      exact Finset.mem_inter.mpr ⟨hvj,
        mem_index_of_mem_facetFace k (htsub hvj) hvF.2⟩
    exact hec.trans hsub

end PolytopeFace
end AffineTverberg
