import AffineTverberg.BadEdgeSubdivisionCover
import AffineTverberg.SimplicialJoinCell

set_option linter.style.header false

/-!
# The bad-edge subdivision on the Cayley points of a join

This file instantiates the bad-edge subdivision at the *actual Cayley points*
of the join model used in the rest of the development.

A join vertex is an element `w` of a finite linearly ordered type `W`, placed in
the join factor `idx w` and being the copy of the original vertex `vert w` of
the ambient coordinate space.  Its Cayley realization is
`cayleyPt idx vert w = polytopalJoinCopy (idx w) (vert w)`.  Two join vertices
form a *bad edge* exactly when they are distinct copies of the same original
vertex, and the subdivision inserts the midpoint of that edge, which here is
literally the midpoint of the two Cayley points (`sdPt_bad_edge`).

## Main results

* `convexHull_cayleyPt_eq_joinCellCarrier` : the convex hull of the Cayley
  points of a join face is the corresponding join cell;
* `affIndepOn_cayleyPt` : the Cayley points of a join face are affinely
  independent as soon as they are in each factor separately;
* `iUnion_sdRealize_eq_joinCellCarrier` : the subdivision of a join face
  triangulates the corresponding join cell;
* `iUnion_good_sdRealize_eq_joinCells` : its good part covers exactly the
  deleted join inside that cell — the union of the join cells of the deleted
  subfaces.

Combined with `affineIndependent_sdPt` and `sdRealize_inter` (from
`BadEdgeSubdivisionGeometry`), these say that on the actual Cayley points the
bad-edge-midpoint subdivision is a genuine geometric triangulation of the join
cell whose good induced subcomplex triangulates the deleted join.
-/

open scoped BigOperators
open Set

namespace AffineTverberg
namespace BadEdge

variable {e m : ℕ} {W : Type*} [Fintype W] [DecidableEq W] [LinearOrder W]

/-- The Cayley realization of a join vertex. -/
noncomputable def cayleyPt (idx : W → Fin (m + 1)) (vert : W → CoordinateSpace e) (w : W) :
    PolytopalJoinAmbient e m :=
  polytopalJoinCopy (idx w) (vert w)

/-- The set of original vertices of a join face lying in a given factor. -/
noncomputable def joinFactor (idx : W → Fin (m + 1)) (vert : W → CoordinateSpace e)
    (S : Finset W) (i : Fin (m + 1)) : Finset (CoordinateSpace e) := by
  classical
  exact (S.filter fun w ↦ idx w = i).image vert

omit [Fintype W] [DecidableEq W] [LinearOrder W] in
theorem mem_joinFactor {idx : W → Fin (m + 1)} {vert : W → CoordinateSpace e}
    {S : Finset W} {i : Fin (m + 1)} {x : CoordinateSpace e} :
    x ∈ joinFactor idx vert S i ↔ ∃ w ∈ S, idx w = i ∧ vert w = x := by
  classical
  simp [joinFactor, Finset.mem_image, Finset.mem_filter, and_assoc]

omit [Fintype W] [DecidableEq W] [LinearOrder W] in
theorem joinFactor_mono {idx : W → Fin (m + 1)} {vert : W → CoordinateSpace e}
    {S T : Finset W} (h : T ⊆ S) (i : Fin (m + 1)) :
    joinFactor idx vert T i ⊆ joinFactor idx vert S i := by
  intro x hx
  obtain ⟨w, hw, hwi, hwx⟩ := mem_joinFactor.mp hx
  exact mem_joinFactor.mpr ⟨w, h hw, hwi, hwx⟩

omit [Fintype W] [DecidableEq W] [LinearOrder W] in
/-- The Cayley points of a join face are exactly the Cayley vertices of the
corresponding join cell. -/
theorem image_cayleyPt_eq (idx : W → Fin (m + 1)) (vert : W → CoordinateSpace e)
    (S : Finset W) :
    cayleyPt idx vert '' (S : Set W) =
      (joinCellVertices (joinFactor idx vert S) : Set (PolytopalJoinAmbient e m)) := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact Finset.mem_coe.mpr (copy_mem_joinCellVertices (idx w)
      (mem_joinFactor.mpr ⟨w, hw, rfl, rfl⟩))
  · intro hy
    obtain ⟨i, x, hx, rfl⟩ := mem_joinCellVertices.mp (Finset.mem_coe.mp hy)
    obtain ⟨w, hw, hwi, hwx⟩ := mem_joinFactor.mp hx
    exact ⟨w, hw, by rw [cayleyPt, hwi, hwx]⟩

omit [Fintype W] [DecidableEq W] [LinearOrder W] in
/-- The convex hull of the Cayley points of a join face is the join cell of the
factorwise vertex sets. -/
theorem convexHull_cayleyPt_eq_joinCellCarrier (idx : W → Fin (m + 1))
    (vert : W → CoordinateSpace e) (S : Finset W) :
    convexHull ℝ (cayleyPt idx vert '' (S : Set W)) =
      joinCellCarrier (joinFactor idx vert S) := by
  rw [joinCellCarrier, image_cayleyPt_eq]

omit [LinearOrder W] in
/-- The realization of a bad-edge vertex of the subdivision is the midpoint of
the two Cayley copies of the same original vertex. -/
theorem sdPt_bad_edge (idx : W → Fin (m + 1)) (vert : W → CoordinateSpace e)
    {u w : W} (huw : u ≠ w) :
    sdPt (cayleyPt idx vert) {u, w} =
      (2 : ℝ)⁻¹ • polytopalJoinCopy (idx u) (vert u) +
        (2 : ℝ)⁻¹ • polytopalJoinCopy (idx w) (vert w) :=
  sdPt_pair _ huw

omit [Fintype W] [DecidableEq W] [LinearOrder W] in
/-- A deleted face gives pairwise disjoint factorwise vertex sets, i.e. a cell
of the deleted join. -/
theorem pairwise_disjoint_joinFactor {idx : W → Fin (m + 1)} {vert : W → CoordinateSpace e}
    {T : Finset W} (hdel : IsDeletedFace vert T) :
    Pairwise fun i j ↦ Disjoint (joinFactor idx vert T i) (joinFactor idx vert T j) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro x hxi hxj
  obtain ⟨w, hw, hwi, hwx⟩ := mem_joinFactor.mp hxi
  obtain ⟨w', hw', hwj, hwx'⟩ := mem_joinFactor.mp hxj
  have : w = w' := hdel w hw w' hw' (by rw [hwx, hwx'])
  rw [this, hwj] at hwi
  exact hij hwi.symm

/-! ### Affine independence of the Cayley points -/

omit [DecidableEq W] [LinearOrder W] in
/-- The `j`-th Cayley coordinate of a linear combination of Cayley points. -/
theorem sum_smul_cayleyPt_apply (idx : W → Fin (m + 1)) (vert : W → CoordinateSpace e)
    (c : W → ℝ) (j : Fin (m + 1)) :
    (∑ w, c w • cayleyPt idx vert w) j =
      (∑ w, (if idx w = j then c w else 0) • vert w, ∑ w, if idx w = j then c w else 0) := by
  classical
  rw [Finset.sum_apply]
  have hterm : ∀ w : W, (c w • cayleyPt idx vert w) j =
      ((if idx w = j then c w else 0) • vert w, if idx w = j then c w else 0) := by
    intro w
    by_cases hw : idx w = j
    · subst hw
      simp [cayleyPt, polytopalJoinCopy, Prod.smul_mk]
    · simp [cayleyPt, polytopalJoinCopy, hw, Prod.ext_iff]
  rw [Finset.sum_congr rfl fun w _ ↦ hterm w]
  rw [← prod_mk_sum]

omit [DecidableEq W] [LinearOrder W] in
/-- **Affine independence of the Cayley points of a join face.**  It suffices
that the join vertices of each factor are placed affinely independently. -/
theorem affIndepOn_cayleyPt (idx : W → Fin (m + 1)) (vert : W → CoordinateSpace e)
    {S : Finset W}
    (hfib : ∀ j, AffIndepOn vert (S.filter fun w ↦ idx w = j)) :
    AffIndepOn (cayleyPt idx vert) S := by
  classical
  intro c hsupp hsum hcomb w
  set j := idx w with hj
  set cj : W → ℝ := fun x ↦ if idx x = j then c x else 0 with hcj
  have hcomp := congrFun hcomb j
  rw [sum_smul_cayleyPt_apply] at hcomp
  have hzero : ((0 : PolytopalJoinAmbient e m) j) = (0, 0) := rfl
  rw [hzero] at hcomp
  have h1 : ∑ x, cj x • vert x = 0 := congrArg Prod.fst hcomp
  have h2 : ∑ x, cj x = 0 := congrArg Prod.snd hcomp
  have hcjsupp : ∀ x, x ∉ S.filter (fun x ↦ idx x = j) → cj x = 0 := by
    intro x hx
    rw [Finset.mem_filter] at hx
    push Not at hx
    by_cases hxj : idx x = j
    · rw [hcj]
      simp only [hxj, ↓reduceIte]
      exact hsupp x (fun hxS ↦ absurd (hx hxS) (fun h ↦ h hxj))
    · rw [hcj]
      simp [hxj]
  have := hfib j cj hcjsupp h2 h1 w
  rw [hcj] at this
  simpa [hj] using this

/-! ### The subdivision of a join cell -/

variable (idx : W → Fin (m + 1)) (vert : W → CoordinateSpace e)

/-- **The bad-edge subdivision triangulates the join cell.**  Its simplices are
spanned by Cayley points and midpoints of bad edges, and their realizations
cover exactly the cell. -/
theorem iUnion_sdRealize_eq_joinCellCarrier (S : Finset W) :
    (⋃ σ ∈ sdFaces vert S, sdRealize (cayleyPt idx vert) σ) =
      joinCellCarrier (joinFactor idx vert S) := by
  rw [convexHull_eq_iUnion_sdRealize vert (cayleyPt idx vert) S,
    convexHull_cayleyPt_eq_joinCellCarrier]

/-- **The good induced subcomplex triangulates the deleted join inside the
cell.** -/
theorem iUnion_good_sdRealize_eq_joinCells (S : Finset W) :
    (⋃ σ ∈ {σ : Finset (Finset W) | σ ∈ sdFaces vert S ∧ ∀ s ∈ σ, IsGoodSdVertex s},
        sdRealize (cayleyPt idx vert) σ) =
      ⋃ T ∈ {T : Finset W | T ⊆ S ∧ IsDeletedFace vert T},
        joinCellCarrier (joinFactor idx vert T) := by
  rw [iUnion_good_sdRealize_eq vert (cayleyPt idx vert) S]
  exact Set.iUnion₂_congr fun T _ ↦ convexHull_cayleyPt_eq_joinCellCarrier idx vert T

omit [Fintype W] in
/-- **Good-vertex count in the Cayley model.**  Here `(S.image vert).card` is the
number of distinct original vertices occurring in the join face `S`, i.e.
`m(S) + 1` in the notation of the paper. -/
theorem card_originalVertices_le_card_good (S : Finset W) {σ : Finset (Finset W)}
    (hσ : σ ∈ sdFaces vert S) (hcard : σ.card = S.card) :
    (S.image vert).card ≤ (σ.filter IsGoodSdVertex).card :=
  card_image_orig_le_card_good vert S hσ hcard

/-- **Summary: the bad-edge-midpoint subdivision of a join cell.**  On the
actual Cayley points of a join face `S` whose vertices are affinely independent
in each factor, the bad-edge subdivision is a geometric triangulation of the
join cell of `S`:

1. the realized vertices of each of its simplices are affinely independent;
2. two simplices meet exactly in the realization of their common face;
3. the simplices cover the join cell;
4. the simplices with only good (original Cayley) vertices cover exactly the
   deleted join inside the cell, i.e. the join cells of the deleted subfaces;
5. every top-dimensional simplex has at least `m(S) + 1` good vertices, where
   `m(S) + 1` is the number of distinct original vertices occurring in `S`. -/
theorem badEdgeSubdivision_triangulates_joinCell (S : Finset W)
    (hfib : ∀ j, AffIndepOn vert (S.filter fun w ↦ idx w = j)) :
    (∀ σ ∈ sdFaces vert S,
        AffineIndependent ℝ fun s : (σ : Set (Finset W)) ↦ sdPt (cayleyPt idx vert) s) ∧
      (∀ σ ∈ sdFaces vert S, ∀ τ ∈ sdFaces vert S,
        sdRealize (cayleyPt idx vert) σ ∩ sdRealize (cayleyPt idx vert) τ =
          sdRealize (cayleyPt idx vert) (σ ∩ τ)) ∧
      ((⋃ σ ∈ sdFaces vert S, sdRealize (cayleyPt idx vert) σ) =
        joinCellCarrier (joinFactor idx vert S)) ∧
      ((⋃ σ ∈ {σ : Finset (Finset W) | σ ∈ sdFaces vert S ∧ ∀ s ∈ σ, IsGoodSdVertex s},
          sdRealize (cayleyPt idx vert) σ) =
        ⋃ T ∈ {T : Finset W | T ⊆ S ∧ IsDeletedFace vert T},
          joinCellCarrier (joinFactor idx vert T)) ∧
      (∀ σ ∈ sdFaces vert S, σ.card = S.card →
        (S.image vert).card ≤ (σ.filter IsGoodSdVertex).card) := by
  have hindep : AffIndepOn (cayleyPt idx vert) S := affIndepOn_cayleyPt idx vert hfib
  exact ⟨fun σ hσ ↦ affineIndependent_sdPt vert hindep hσ,
    fun σ hσ τ hτ ↦ sdRealize_inter vert hindep hσ hτ,
    iUnion_sdRealize_eq_joinCellCarrier idx vert S,
    iUnion_good_sdRealize_eq_joinCells idx vert S,
    fun σ hσ hcard ↦ card_originalVertices_le_card_good vert S hσ hcard⟩

end BadEdge
end AffineTverberg
