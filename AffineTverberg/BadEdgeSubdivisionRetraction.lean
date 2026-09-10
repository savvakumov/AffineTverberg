import AffineTverberg.BadEdgeSubdivisionCayley
import AffineTverberg.BarycentricRealization

set_option linter.style.header false

/-!
# The bad-edge subdivision as a geometric realization, and its good part

This file connects the bad-edge-midpoint subdivision of a join cell with the
general machinery of `BarycentricRealization` and `InducedComplement`.

The subdivision `sdFaces vert S` of a join face `S`, realized on the Cayley
points by `sdPt (cayleyPt idx vert)`, satisfies the standard geometric
simplicial-complex hypotheses `IsGeometricRealization` (affine independence on
each simplex and the convex-hull intersection condition).  Its geometric
carrier is the join cell of `S`, and the carrier of the subcomplex induced by
the good vertices is exactly the deleted join inside that cell.

Feeding this into `geometricInducedComplementHomotopyEquiv` gives the paper's
local statement: *the complement of the bad induced subcomplex inside a join
cell is homotopy equivalent to the deleted join part of that cell*, via the
explicit deformation retraction that discards the bad barycentric coordinates.

## Main results

* `isGeometricRealization_sdFaces` : the subdivision is a geometric simplicial
  complex on the Cayley points;
* `geometricCarrier_sdFaces` : its carrier is the join cell;
* `geometricCarrier_good_sdFaces` : the carrier of the good induced subcomplex
  is the union of the join cells of the deleted subfaces;
* `joinCellComplementHomotopyEquiv` : the homotopy equivalence between the
  complement of the bad induced subcomplex in the join cell and the deleted
  join inside the cell.
-/

noncomputable section

open scoped BigOperators
open Set
open AffineTverberg.Simplicial

namespace AffineTverberg
namespace BadEdge

variable {e m : ℕ} {W : Type*} [Fintype W] [DecidableEq W] [LinearOrder W]

/-- The set of good vertices of the subdivision: the singletons, i.e. the
original join vertices. -/
def goodSdVertices (W : Type*) [Fintype W] [DecidableEq W] : Finset (Finset W) :=
  Finset.univ.filter IsGoodSdVertex

omit [LinearOrder W] in
@[simp]
theorem mem_goodSdVertices {s : Finset W} : s ∈ goodSdVertices W ↔ IsGoodSdVertex s := by
  simp [goodSdVertices]

omit [LinearOrder W] in
theorem subset_goodSdVertices {σ : Finset (Finset W)} :
    σ ⊆ goodSdVertices W ↔ ∀ s ∈ σ, IsGoodSdVertex s := by
  constructor
  · intro h s hs
    exact mem_goodSdVertices.mp (h hs)
  · intro h s hs
    exact mem_goodSdVertices.mpr (h s hs)

variable (idx : W → Fin (m + 1)) (vert : W → CoordinateSpace e)

/-- **The bad-edge subdivision is a geometric simplicial complex.**  On the
Cayley points of a join face whose vertices are affinely independent in each
factor, its simplices are affinely independent and meet in common faces. -/
theorem isGeometricRealization_sdFaces {S : Finset W}
    (hfib : ∀ j, AffIndepOn vert (S.filter fun w ↦ idx w = j)) :
    IsGeometricRealization (sdFaces vert S) (sdPt (cayleyPt idx vert)) where
  independent := fun _ hσ ↦
    affineIndependent_sdPt vert (affIndepOn_cayleyPt idx vert hfib) hσ
  intersection := fun _ hσ _ hτ ↦
    (sdRealize_inter vert (affIndepOn_cayleyPt idx vert hfib) hσ hτ).subset

/-- The geometric carrier of the subdivision is the join cell. -/
theorem geometricCarrier_sdFaces (S : Finset W) :
    geometricCarrier (sdFaces vert S) (sdPt (cayleyPt idx vert)) =
      joinCellCarrier (joinFactor idx vert S) :=
  iUnion_sdRealize_eq_joinCellCarrier idx vert S

/-- The geometric carrier of the good induced subcomplex is the deleted join
inside the cell: the union of the join cells of the deleted subfaces. -/
theorem geometricCarrier_good_sdFaces (S : Finset W) :
    geometricCarrier (inducedFaces (sdFaces vert S) (goodSdVertices W))
        (sdPt (cayleyPt idx vert)) =
      ⋃ T ∈ {T : Finset W | T ⊆ S ∧ IsDeletedFace vert T},
        joinCellCarrier (joinFactor idx vert T) := by
  rw [← iUnion_good_sdRealize_eq_joinCells idx vert S]
  ext x
  simp only [geometricCarrier, Set.mem_iUnion, mem_inducedFaces, subset_goodSdVertices,
    Set.mem_ofPred_eq, sdRealize, exists_prop]

/-- The bad part of the join cell: the carrier of the subcomplex induced by the
bad vertices, i.e. by the inserted bad-edge midpoints. -/
def badPartCarrier (S : Finset W) : Set (PolytopalJoinAmbient e m) :=
  geometricCarrier (inducedFaces (sdFaces vert S) (goodSdVertices W)ᶜ)
    (sdPt (cayleyPt idx vert))

/-- **The complement of the bad subcomplex retracts onto the deleted join.**
Inside a join cell, the complement of the bad induced subcomplex of the
bad-edge subdivision is homotopy equivalent to the union of the join cells of
the deleted subfaces, i.e. to the deleted join inside that cell. -/
def joinCellComplementHomotopyEquiv {S : Finset W}
    (hfib : ∀ j, AffIndepOn vert (S.filter fun w ↦ idx w = j)) :
    ContinuousMap.HomotopyEquiv
      ↥(joinCellCarrier (joinFactor idx vert S) \ badPartCarrier idx vert S)
      ↥(⋃ T ∈ {T : Finset W | T ⊆ S ∧ IsDeletedFace vert T},
          joinCellCarrier (joinFactor idx vert T)) := by
  rw [← geometricCarrier_sdFaces idx vert S, ← geometricCarrier_good_sdFaces idx vert S]
  exact geometricInducedComplementHomotopyEquiv
    (fun _ hσ _ hτσ ↦ sdFaces_faceClosed vert S hσ hτσ)
    (isGeometricRealization_sdFaces idx vert hfib) (goodSdVertices W)

end BadEdge
end AffineTverberg
