import AffineTverberg.BadEdgeSubdivisionGluing
import AffineTverberg.BadEdgeSubdivisionGlobal

set_option linter.style.header false

/-!
# The bad-edge subdivision of the whole join complex as a geometric complex

This file assembles the per-face results.  The subdivisions of the individual
join faces glue to a finite simplicial complex `sdJoinFaces` on the Cayley
points, which satisfies the geometric realization hypotheses: simplices coming
from *different* join faces still meet in a common face.  The proof combines

* `joinCellCarrier_inter_subset` (two join cells meet in the cell of their
  factorwise intersection),
* `mem_sdFaces_of_subset` and `sdRealize_inter_joinCell` (restriction of a
  simplex to a subface),
* `sdRealize_inter` (the intersection property inside one face).

Consequently the general induced-complement machinery applies globally: the
complement of the bad induced subcomplex inside the join complex is homotopy
equivalent to the deleted join `simplicialDeletedJoinCarrier n K m`.

## Main results

* `isGeometricRealization_sdJoinFaces` : the assembled subdivision is a
  geometric simplicial complex on the Cayley points;
* `geometricCarrier_sdJoinFaces` : its carrier is the join complex;
* `geometricCarrier_good_sdJoinFaces` : the carrier of its good induced
  subcomplex is exactly the deleted join;
* `deletedJoinComplementHomotopyEquiv` : **the complement of the bad induced
  subcomplex in the join complex is homotopy equivalent to the deleted join.**
-/

noncomputable section

open scoped BigOperators
open Set
open AffineTverberg.Simplicial

namespace AffineTverberg
namespace BadEdge

variable {e n m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
variable {W : Type*} [Fintype W] [DecidableEq W] [LinearOrder W]
variable (idx : W → Fin (m + 1)) (vert : W → CoordinateSpace e)

/-! ### Factorwise intersections of join faces -/

omit [Fintype W] [LinearOrder W] in
/-- Distinct join vertices being distinct copies, the component faces of two
join faces intersect in the component faces of their intersection. -/
theorem joinFactor_inter (hinj : Function.Injective fun w ↦ (idx w, vert w))
    (S T : Finset W) (i : Fin (m + 1)) :
    joinFactor idx vert S i ∩ joinFactor idx vert T i = joinFactor idx vert (S ∩ T) i := by
  classical
  ext x
  simp only [Finset.mem_inter, mem_joinFactor]
  constructor
  · rintro ⟨⟨w, hwS, hwi, hwx⟩, ⟨w', hw'T, hw'i, hw'x⟩⟩
    have : w = w' := hinj (show (idx w, vert w) = (idx w', vert w') by
      rw [hwi, hw'i, hwx, hw'x])
    exact ⟨w, ⟨hwS, by rw [this]; exact hw'T⟩, hwi, hwx⟩
  · rintro ⟨w, ⟨hwS, hwT⟩, hwi, hwx⟩
    exact ⟨⟨w, hwS, hwi, hwx⟩, ⟨w, hwT, hwi, hwx⟩⟩

/-! ### Affine independence of the Cayley points of a join face -/

omit [DecidableEq W] [LinearOrder W] in
/-- The original vertices of a join face lying in one factor are affinely
independent, because they form a face of the simplicial complex `K`. -/
theorem affIndepOn_vert_filter (hinj : Function.Injective fun w ↦ (idx w, vert w))
    {S : Finset W} (hS : IsJoinFace n K idx vert S) (j : Fin (m + 1)) :
    AffIndepOn vert (S.filter fun w ↦ idx w = j) := by
  classical
  rcases hS j with hemp | hface
  · have hfil : (S.filter fun w ↦ idx w = j) = ∅ := by
      rw [joinFactor, Finset.image_eq_empty] at hemp
      exact hemp
    intro c hsupp _ _ w
    exact hsupp w (by rw [hfil]; exact Finset.notMem_empty w)
  · refine affIndepOn_of_affineIndependent ?_
    have hmem : ∀ w : {x // x ∈ S.filter fun w ↦ idx w = j},
        vert w.val ∈ joinFactor idx vert S j := by
      intro w
      obtain ⟨hwS, hwj⟩ := Finset.mem_filter.mp w.property
      exact mem_joinFactor.mpr ⟨w.val, hwS, hwj, rfl⟩
    have hinjfil : Function.Injective
        (fun w : {x // x ∈ S.filter fun w ↦ idx w = j} ↦
          (⟨vert w.val, hmem w⟩ : {x // x ∈ joinFactor idx vert S j})) := by
      intro u w huw
      have hv : vert u.val = vert w.val := congrArg Subtype.val huw
      have hu := (Finset.mem_filter.mp u.property).2
      have hw := (Finset.mem_filter.mp w.property).2
      exact Subtype.ext (hinj (show (idx u.val, vert u.val) = (idx w.val, vert w.val) by
        rw [hu, hw, hv]))
    exact (K.indep hface.1).comp_embedding ⟨_, hinjfil⟩

omit [DecidableEq W] [LinearOrder W] in
/-- The Cayley points of a join face are affinely independent. -/
theorem affIndepOn_cayleyPt_of_isJoinFace (hinj : Function.Injective fun w ↦ (idx w, vert w))
    {S : Finset W} (hS : IsJoinFace n K idx vert S) :
    AffIndepOn (cayleyPt idx vert) S :=
  affIndepOn_cayleyPt idx vert (affIndepOn_vert_filter (n := n) (K := K) idx vert hinj hS)

/-! ### Intersections of the cells of two join faces -/

omit [Fintype W] [LinearOrder W] in
/-- Two join cells of the join complex meet inside the join cell of the
intersection of the two join faces. -/
theorem joinCellCarrier_joinFactor_inter_subset
    (hinj : Function.Injective fun w ↦ (idx w, vert w))
    {S T : Finset W} (hS : IsJoinFace n K idx vert S) (hT : IsJoinFace n K idx vert T) :
    joinCellCarrier (joinFactor idx vert S) ∩ joinCellCarrier (joinFactor idx vert T) ⊆
      joinCellCarrier (joinFactor idx vert (S ∩ T)) := by
  classical
  have hsub := joinCellCarrier_inter_subset (joinFactor idx vert S) (joinFactor idx vert T)
    (fun i ↦ ?_)
  · have hfun : (fun i ↦ joinFactor idx vert S i ∩ joinFactor idx vert T i) =
        joinFactor idx vert (S ∩ T) :=
      funext fun i ↦ joinFactor_inter idx vert hinj S T i
    rwa [hfun] at hsub
  · rcases hS i with hemp | hfaceS
    · rw [hemp]
      simp
    · rcases hT i with hemp | hfaceT
      · rw [hemp]
        simp
      · intro x hx
        have := K.inter_subset_convexHull hfaceS.1 hfaceT.1 hx
        rwa [Finset.coe_inter]

/-! ### The intersection property across two join faces -/

/-- **Simplices of the subdivisions of two different join faces meet in a
common face.** -/
theorem sdRealize_inter_of_isJoinFace (hinj : Function.Injective fun w ↦ (idx w, vert w))
    {S T : Finset W} (hS : IsJoinFace n K idx vert S) (hT : IsJoinFace n K idx vert T)
    {σ τ : Finset (Finset W)} (hσ : σ ∈ sdFaces vert S) (hτ : τ ∈ sdFaces vert T) :
    sdRealize (cayleyPt idx vert) σ ∩ sdRealize (cayleyPt idx vert) τ ⊆
      sdRealize (cayleyPt idx vert) (σ ∩ τ) := by
  classical
  set R : Finset W := S ∩ T with hR
  have hindepS : AffIndepOn (cayleyPt idx vert) S :=
    affIndepOn_cayleyPt_of_isJoinFace (n := n) (K := K) idx vert hinj hS
  have hindepT : AffIndepOn (cayleyPt idx vert) T :=
    affIndepOn_cayleyPt_of_isJoinFace (n := n) (K := K) idx vert hinj hT
  have hRS : R ⊆ S := Finset.inter_subset_left
  have hRT : R ⊆ T := Finset.inter_subset_right
  rintro x ⟨hxσ, hxτ⟩
  have hxS : x ∈ joinCellCarrier (joinFactor idx vert S) := by
    have := sdRealize_subset_convexHull vert (ρ := cayleyPt idx vert) hσ hxσ
    rwa [convexHull_cayleyPt_eq_joinCellCarrier] at this
  have hxT : x ∈ joinCellCarrier (joinFactor idx vert T) := by
    have := sdRealize_subset_convexHull vert (ρ := cayleyPt idx vert) hτ hxτ
    rwa [convexHull_cayleyPt_eq_joinCellCarrier] at this
  have hxR : x ∈ joinCellCarrier (joinFactor idx vert R) :=
    joinCellCarrier_joinFactor_inter_subset (n := n) (K := K) idx vert hinj hS hT ⟨hxS, hxT⟩
  have hxσR : x ∈ sdRealize (cayleyPt idx vert) (σ.filter fun s ↦ s ⊆ R) :=
    sdRealize_inter_joinCell idx vert hRS hindepS hσ ⟨hxσ, hxR⟩
  have hxτR : x ∈ sdRealize (cayleyPt idx vert) (τ.filter fun s ↦ s ⊆ R) :=
    sdRealize_inter_joinCell idx vert hRT hindepT hτ ⟨hxτ, hxR⟩
  have hσR : (σ.filter fun s ↦ s ⊆ R) ∈ sdFaces vert R :=
    mem_sdFaces_of_subset (fun s hs ↦ (Finset.mem_filter.mp hs).2) hRS
      (sdFaces_faceClosed vert S hσ (Finset.filter_subset _ _))
  have hτR : (τ.filter fun s ↦ s ⊆ R) ∈ sdFaces vert R :=
    mem_sdFaces_of_subset (fun s hs ↦ (Finset.mem_filter.mp hs).2) hRT
      (sdFaces_faceClosed vert T hτ (Finset.filter_subset _ _))
  have hindepR : AffIndepOn (cayleyPt idx vert) R := affIndepOn_mono hindepS hRS
  have hinter := sdRealize_inter vert hindepR hσR hτR
  have hx : x ∈ sdRealize (cayleyPt idx vert)
      ((σ.filter fun s ↦ s ⊆ R) ∩ (τ.filter fun s ↦ s ⊆ R)) := by
    rw [← hinter]; exact ⟨hxσR, hxτR⟩
  refine sdRealize_mono ?_ hx
  intro s hs
  obtain ⟨hsσ, hsτ⟩ := Finset.mem_inter.mp hs
  exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hsσ).1, (Finset.mem_filter.mp hsτ).1⟩

/-! ### The assembled subdivision of the join complex -/

open scoped Classical in
/-- The bad-edge subdivision of the whole join complex, as a finite complex on
the subdivision vertices. -/
def sdJoinFaces (n : ℕ) (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))
    (idx : W → Fin (m + 1)) (vert : W → CoordinateSpace e) :
    Finset (Finset (Finset W)) :=
  (Finset.univ.filter fun S : Finset W ↦ IsJoinFace n K idx vert S).biUnion (sdFaces vert)

theorem mem_sdJoinFaces {σ : Finset (Finset W)} :
    σ ∈ sdJoinFaces n K idx vert ↔ ∃ S, IsJoinFace n K idx vert S ∧ σ ∈ sdFaces vert S := by
  classical
  simp [sdJoinFaces, Finset.mem_biUnion, Finset.mem_filter]

/-- The finite complex `sdJoinFaces` is the complex `sdJoinComplex`. -/
theorem coe_sdJoinFaces :
    (sdJoinFaces n K idx vert : Set (Finset (Finset W))) = sdJoinComplex n K idx vert := by
  ext σ
  simpa [sdJoinComplex] using mem_sdJoinFaces idx vert (n := n) (K := K)

theorem faceClosed_sdJoinFaces : FaceClosed (sdJoinFaces n K idx vert) := by
  intro σ hσ τ hτσ
  obtain ⟨S, hS, hσS⟩ := mem_sdJoinFaces idx vert |>.mp hσ
  exact mem_sdJoinFaces idx vert |>.mpr ⟨S, hS, sdFaces_faceClosed vert S hσS hτσ⟩

/-- **The assembled subdivision is a geometric simplicial complex** on the
Cayley points. -/
theorem isGeometricRealization_sdJoinFaces
    (hinj : Function.Injective fun w ↦ (idx w, vert w)) :
    IsGeometricRealization (sdJoinFaces n K idx vert) (sdPt (cayleyPt idx vert)) where
  independent := by
    intro σ hσ
    obtain ⟨S, hS, hσS⟩ := mem_sdJoinFaces idx vert |>.mp hσ
    exact affineIndependent_sdPt vert
      (affIndepOn_cayleyPt_of_isJoinFace (n := n) (K := K) idx vert hinj hS) hσS
  intersection := by
    intro σ hσ τ hτ
    obtain ⟨S, hS, hσS⟩ := mem_sdJoinFaces idx vert |>.mp hσ
    obtain ⟨T, hT, hτT⟩ := mem_sdJoinFaces idx vert |>.mp hτ
    exact sdRealize_inter_of_isJoinFace (n := n) (K := K) idx vert hinj hS hT hσS hτT

/-- The carrier of the assembled subdivision is the join complex. -/
theorem geometricCarrier_sdJoinFaces :
    geometricCarrier (sdJoinFaces n K idx vert) (sdPt (cayleyPt idx vert)) =
      ⋃ S ∈ {S : Finset W | IsJoinFace n K idx vert S},
        joinCellCarrier (joinFactor idx vert S) := by
  rw [← iUnion_sdRealize_sdJoinComplex idx vert]
  ext x
  simp only [geometricCarrier, Set.mem_iUnion, sdRealize, exists_prop, sdJoinComplex,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨σ, hσ, hx⟩
    exact ⟨σ, (mem_sdJoinFaces idx vert).mp hσ, hx⟩
  · rintro ⟨σ, hσ, hx⟩
    exact ⟨σ, (mem_sdJoinFaces idx vert).mpr hσ, hx⟩

/-- **The good induced subcomplex of the assembled subdivision triangulates the
deleted join.** -/
theorem geometricCarrier_good_sdJoinFaces
    (hinj : Function.Injective fun w ↦ (idx w, vert w))
    (hcover : ∀ (i : Fin (m + 1)) (s : Finset (CoordinateSpace e)),
      IsBoundarySimplicialFace n K s → ∀ v ∈ s, ∃ w, idx w = i ∧ vert w = v) :
    geometricCarrier (inducedFaces (sdJoinFaces n K idx vert) (goodSdVertices W))
        (sdPt (cayleyPt idx vert)) = simplicialDeletedJoinCarrier n K m := by
  rw [← iUnion_good_sdRealize_eq_deletedJoin idx vert hinj hcover]
  ext x
  simp only [geometricCarrier, Set.mem_iUnion, mem_inducedFaces, subset_goodSdVertices,
    sdRealize, exists_prop, sdJoinComplex, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨σ, ⟨hσ, hgood⟩, hx⟩
    exact ⟨σ, ⟨(mem_sdJoinFaces idx vert).mp hσ, hgood⟩, hx⟩
  · rintro ⟨σ, ⟨hσ, hgood⟩, hx⟩
    exact ⟨σ, ⟨(mem_sdJoinFaces idx vert).mpr hσ, hgood⟩, hx⟩

/-- The bad part of the join complex: the carrier of the subcomplex induced by
the inserted bad-edge midpoints. -/
def badJoinPartCarrier (n : ℕ) (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))
    (idx : W → Fin (m + 1)) (vert : W → CoordinateSpace e) : Set (PolytopalJoinAmbient e m) :=
  geometricCarrier (inducedFaces (sdJoinFaces n K idx vert) (goodSdVertices W)ᶜ)
    (sdPt (cayleyPt idx vert))

/-- **The complement of the bad subcomplex retracts onto the deleted join.**
The complement, inside the join complex, of the induced subcomplex on the
inserted bad-edge midpoints is homotopy equivalent to the deleted join. -/
def deletedJoinComplementHomotopyEquiv
    (hinj : Function.Injective fun w ↦ (idx w, vert w))
    (hcover : ∀ (i : Fin (m + 1)) (s : Finset (CoordinateSpace e)),
      IsBoundarySimplicialFace n K s → ∀ v ∈ s, ∃ w, idx w = i ∧ vert w = v) :
    ContinuousMap.HomotopyEquiv
      ↥((⋃ S ∈ {S : Finset W | IsJoinFace n K idx vert S},
            joinCellCarrier (joinFactor idx vert S)) \ badJoinPartCarrier n K idx vert)
      ↥(simplicialDeletedJoinCarrier n K m) := by
  rw [← geometricCarrier_sdJoinFaces idx vert,
    ← geometricCarrier_good_sdJoinFaces idx vert hinj hcover]
  exact geometricInducedComplementHomotopyEquiv (faceClosed_sdJoinFaces idx vert)
    (isGeometricRealization_sdJoinFaces idx vert hinj) (goodSdVertices W)

end BadEdge
end AffineTverberg
