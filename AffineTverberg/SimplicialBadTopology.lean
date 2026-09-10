import AffineTverberg.SimplicialBadHomology
import AffineTverberg.SingularHomology

set_option linter.style.header false

/-!
# The bad complex and the complement of the deleted join

The direction needed for Alexander duality is the complement of the *good*
complex retracting onto the bad one. This file identifies that complement
with the complement of the actual deleted join and transfers the homotopy
equivalence to Mathlib's singular homology.

It also constructs the finite colored-vertex indexing from a finite geometric
simplicial complex, discharging the indexing assumptions in the subdivision
and bad-homology theorems. No homology-comparison or duality input is assumed.
-/

noncomputable section

open AffineTverberg.Simplicial CategoryTheory

namespace AffineTverberg.BadEdge

section Topology

variable {e n m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
variable {W : Type} [Fintype W] [LinearOrder W]
variable (idx : W → Fin (m + 1)) (vert : W → CoordinateSpace e)

/-- The barycentric realization whose homology was computed is homeomorphic
to the actual geometric bad subcomplex in the join. -/
def badJoinBarycentricHomeomorph
    (hinj : Function.Injective fun w ↦ (idx w, vert w)) :
    barycentricCarrier (badJoinFaces (n := n) (K := K) idx vert) ≃ₜ
      badJoinPartCarrier n K idx vert :=
  geometricRealizationHomeomorph
    ((isGeometricRealization_sdJoinFaces (n := n) (K := K) idx vert hinj).induced
      (goodSdVertices W)ᶜ)

/-- The Alexander-duality direction: the complement of the deleted join in
the boundary join is homotopy equivalent to the geometric bad subcomplex. -/
def deletedJoinComplementToBadHomotopyEquiv
    (hinj : Function.Injective fun w ↦ (idx w, vert w))
    (hcover : ∀ (i : Fin (m + 1)) (s : Finset (CoordinateSpace e)),
      IsBoundarySimplicialFace n K s → ∀ v ∈ s, ∃ w, idx w = i ∧ vert w = v) :
    ContinuousMap.HomotopyEquiv
      ↥((⋃ S ∈ {S : Finset W | IsJoinFace n K idx vert S},
            joinCellCarrier (joinFactor idx vert S)) \ simplicialDeletedJoinCarrier n K m)
      ↥(badJoinPartCarrier n K idx vert) := by
  classical
  have hcc : ((goodSdVertices W)ᶜ)ᶜ = goodSdVertices W := by
    ext s
    simp only [Finset.mem_compl, not_not]
  have hdomain :
      (⋃ S ∈ {S : Finset W | IsJoinFace n K idx vert S},
          joinCellCarrier (joinFactor idx vert S)) \ simplicialDeletedJoinCarrier n K m =
      geometricCarrier (sdJoinFaces n K idx vert) (sdPt (cayleyPt idx vert)) \
        geometricCarrier (inducedFaces (sdJoinFaces n K idx vert) ((goodSdVertices W)ᶜ)ᶜ)
          (sdPt (cayleyPt idx vert)) := by
    rw [hcc, geometricCarrier_sdJoinFaces idx vert,
      geometricCarrier_good_sdJoinFaces idx vert hinj hcover]
  exact (Homeomorph.setCongr hdomain).toHomotopyEquiv.trans (geometricInducedComplementHomotopyEquiv
    (faceClosed_sdJoinFaces (n := n) (K := K) idx vert)
    (isGeometricRealization_sdJoinFaces idx vert hinj) (goodSdVertices W)ᶜ)

/-- The corresponding isomorphism of actual ordinary singular homology
groups.  The resulting vanishing in degree `m * n - 1` is
`AffineTverberg.BadEdge.isZero_deletedJoinComplementSingularHomology` in
`AffineTverberg/BadComplexComparison.lean`. -/
def singularHomologyIso_deletedJoinComplementBad
    (hinj : Function.Injective fun w ↦ (idx w, vert w))
    (hcover : ∀ (i : Fin (m + 1)) (s : Finset (CoordinateSpace e)),
      IsBoundarySimplicialFace n K s → ∀ v ∈ s, ∃ w, idx w = i ∧ vert w = v) (k : ℕ) :
    (realSingularHomology k).obj
      (TopCat.of ↥((⋃ S ∈ {S : Finset W | IsJoinFace n K idx vert S},
          joinCellCarrier (joinFactor idx vert S)) \ simplicialDeletedJoinCarrier n K m)) ≅
    (realSingularHomology k).obj (TopCat.of ↥(badJoinPartCarrier n K idx vert)) :=
  realSingularHomologyIsoOfHomotopyEquiv
    (deletedJoinComplementToBadHomotopyEquiv idx vert hinj hcover) k

end Topology

section FiniteIndexing

variable {e n m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-- Finite labels for the colored copies of all boundary vertices. These are
only enumeration data, not assumptions about homology or triangulation. -/
structure BoundaryJoinVertexIndexing (n : ℕ)
    (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)) (m : ℕ) where
  size : ℕ
  factor : Fin size → Fin (m + 1)
  vertex : Fin size → CoordinateSpace e
  injective : Function.Injective fun w ↦ (factor w, vertex w)
  covers : ∀ (i : Fin (m + 1)) (s : Finset (CoordinateSpace e)),
    IsBoundarySimplicialFace n K s → ∀ v ∈ s, ∃ w, factor w = i ∧ vertex w = v

/-- A finite geometric complex has the required indexing, including when
there are no vertices. No nonemptiness or topological-boundary premise is used. -/
def boundaryJoinVertexIndexing (hfinite : K.faces.Finite) : BoundaryJoinVertexIndexing n K m := by
  classical
  let A : Finset (CoordinateSpace e) := hfinite.toFinset.biUnion id
  let C := Fin (m + 1) × {v // v ∈ A}
  let enc : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
  refine ⟨Fintype.card C, (fun w ↦ (enc.symm w).1), (fun w ↦ (enc.symm w).2.val), ?_, ?_⟩
  · intro w w' h
    apply enc.symm.injective
    apply Prod.ext
    · exact congrArg (fun p : Fin (m + 1) × CoordinateSpace e ↦ p.1) h
    · exact Subtype.ext (congrArg (fun p : Fin (m + 1) × CoordinateSpace e ↦ p.2) h)
  · intro i s hs v hv
    have hvA : v ∈ A := Finset.mem_biUnion.mpr ⟨s, hfinite.mem_toFinset.mpr hs.1, hv⟩
    refine ⟨enc (i, ⟨v, hvA⟩), ?_, ?_⟩ <;> simp

namespace BoundaryJoinVertexIndexing

variable (a : BoundaryJoinVertexIndexing n K m)

/-- An explicit orientation order for the finite subdivision vertices. -/
@[instance_reducible]
def subdivisionOrder : LinearOrder (Finset (Fin a.size)) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-- The bad complex in the concrete indexing. -/
def badComplex : Finset (Finset (Finset (Fin a.size))) :=
  badJoinFaces (n := n) (K := K) a.factor a.vertex

/-- The private-facet result with the indexing hypotheses discharged. -/
theorem hasFreeFacets (hm : 2 ≤ m) (hn : 0 < n) :
    AffineTverberg.HasFreeFacets (topSimplices a.badComplex (m * n)) :=
  hasFreeFacets_badJoinFaces a.factor a.vertex hm hn a.injective a.covers

/-- The top homology of the explicitly indexed bad complex is zero. -/
theorem homology_subsingleton (𝕜 : Type*) [Field 𝕜] (hm : 2 ≤ m) (hn : 0 < n) :
    letI := a.subdivisionOrder
    Subsingleton (homology 𝕜 a.badComplex (m * n)) := by
  let := a.subdivisionOrder
  exact homology_top_subsingleton_of_hasFreeFacets (a.hasFreeFacets hm hn)

end BoundaryJoinVertexIndexing

/-- For every finite geometric complex, the constructed bad complex has
zero homology in the exact degree used in the paper. -/
theorem homology_constructed_badComplex_subsingleton (hfinite : K.faces.Finite)
    (𝕜 : Type*) [Field 𝕜] (hm : 2 ≤ m) (hn : 0 < n) :
    let a := boundaryJoinVertexIndexing (n := n) (m := m) hfinite
    letI := a.subdivisionOrder
    Subsingleton (homology 𝕜 a.badComplex (m * n)) :=
  (boundaryJoinVertexIndexing hfinite).homology_subsingleton 𝕜 hm hn

end FiniteIndexing

end AffineTverberg.BadEdge
