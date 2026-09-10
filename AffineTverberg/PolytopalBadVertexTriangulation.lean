import AffineTverberg.CayleyJoinFaces
import AffineTverberg.PullingSubdivision

set_option linter.style.header false

/-!
# The general polytopal bad-vertex triangulation

Let `P` be a polytope and `Q = P * ⋯ * P` the Cayley join of `m + 1` copies of
`P`.  A *bad edge* of `Q` joins two copies of one and the same actual vertex of
`P`; a face of `Q` is *deleted* when it contains no bad edge, and the deleted
faces are exactly the cells of the polytopal deleted join.

This file constructs the bad-vertex triangulation of `Q` in the general,
nonsimplicial case, by instantiating the abstract pulling subdivision
`AffineTverberg.BadEdge.sdPoset` at the actual face lattice of `Q`:

* `JoinVertex P m` is the (finite, linearly ordered) type of Cayley vertices,
  a copy index together with an *actual* vertex of `P` (an extreme point, from
  `PolytopalVertices.lean`, not merely a chosen generator);
* `faceVertexSet` records a tuple of exposed faces of `P` by the Cayley vertices
  it contains, and `faceFamily` is the resulting finite family of faces of `Q`;
* `sdCarrier S` is the actual geometric carrier of a face, and it agrees with
  the Cayley join of the factors (`sdCarrier_faceVertexSet`), hence with the
  carriers used by `PolytopalJoin`, `PolytopalDeletedJoin` and
  `PolytopalCellStructure`;
* `sdQ S` is the triangulation of the face `S`, and `realization S` its
  geometric realization.

## Main results

* `realization_eq_sdCarrier` — **the triangulation covers exactly the face**,
  for every exposed face of `Q`, in particular for `Q` itself.
* `sdQ_mono` — **compatibility on every exposed face**: the triangulation of a
  face is the restriction of the triangulation of any larger face.
* `goodRealization_eq_deletedJoin` — **the good induced subcomplex is exactly
  the polytopal deleted join** `polytopalDeletedJoinCarrier P m`.

These results construct an abstract face-closed subdivision and identify its
geometric carrier. `PolytopalPurity` proves purity; `PolytopalIntersection`
proves `Simplicial.IsGeometricRealization`, including affine independence and
exact simplex intersections. These are separate proofs, not consequences of
coverage and monotonicity alone.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg
namespace BadVertex

open CayleyJoin PolytopeFace BadEdge

variable {n : ℕ} (P : FullDimensionalPolytope n) (m : ℕ)

/-! ### Cayley vertices -/

/-- A Cayley vertex of the join `Q`: a copy index and an actual vertex of `P`,
the latter encoded by its position in the finite set of extreme points. -/
def JoinVertex : Type := Fin (m + 1) × Fin P.actualVertices.card

instance : Fintype (JoinVertex P m) :=
  inferInstanceAs (Fintype (Fin (m + 1) × Fin P.actualVertices.card))

instance : DecidableEq (JoinVertex P m) :=
  inferInstanceAs (DecidableEq (Fin (m + 1) × Fin P.actualVertices.card))

instance : LinearOrder (JoinVertex P m) :=
  LinearOrder.lift'
    (fun w : JoinVertex P m ↦
      finProdFinEquiv (show Fin (m + 1) × Fin P.actualVertices.card from w))
    finProdFinEquiv.injective

/-- The actual vertex of `P` with a given index. -/
def vtx (k : Fin P.actualVertices.card) : CoordinateSpace n :=
  (P.actualVertices.equivFin.symm k : CoordinateSpace n)

theorem vtx_mem (k : Fin P.actualVertices.card) : vtx P k ∈ P.actualVertices :=
  (P.actualVertices.equivFin.symm k).2

theorem vtx_injective : Function.Injective (vtx P) := by
  intro k l h
  exact P.actualVertices.equivFin.symm.injective (Subtype.ext h)

theorem exists_vtx {v : CoordinateSpace n} (hv : v ∈ P.actualVertices) :
    ∃ k, vtx P k = v :=
  ⟨P.actualVertices.equivFin ⟨v, hv⟩, by simp [vtx]⟩

/-- Two Cayley vertices form a bad edge when they are copies of the same actual
vertex of `P`; this is recorded by the second component. -/
def origIndex (w : JoinVertex P m) : Fin P.actualVertices.card := w.2

/-- The Cayley point of a join vertex. -/
def pt (w : JoinVertex P m) : PolytopalJoinAmbient n m :=
  polytopalJoinCopy w.1 (vtx P w.2)

/-! ### Faces of the join -/

/-- The Cayley vertices lying in a tuple of exposed faces of `P`. -/
def faceVertexSet (C : Fin (m + 1) → PolytopeFaceIndex P) : Finset (JoinVertex P m) := by
  classical
  exact Finset.univ.filter fun w ↦ vtx P w.2 ∈ (C w.1).carrier

/-- The finite family of faces of the Cayley join, each recorded by its set of
Cayley vertices. -/
def faceFamily : Finset (Finset (JoinVertex P m)) :=
  Finset.univ.image (faceVertexSet P m)

/-- The geometric carrier of a set of Cayley vertices. -/
def sdCarrier (S : Finset (JoinVertex P m)) : Set (PolytopalJoinAmbient n m) :=
  convexHull ℝ (pt P m '' S)

/-- The barycentre of a vertex of the subdivision: an original Cayley vertex, or
the midpoint of a bad edge. -/
def sdPoint (a : Finset (JoinVertex P m)) : PolytopalJoinAmbient n m :=
  (a.card : ℝ)⁻¹ • ∑ w ∈ a, pt P m w

/-- The carrier of one simplex of the subdivision. -/
def simplexCarrier (σ : Finset (Finset (JoinVertex P m))) :
    Set (PolytopalJoinAmbient n m) :=
  convexHull ℝ (sdPoint P m '' σ)

/-- **The bad-vertex triangulation of the face `S` of the Cayley join.** -/
def sdQ (S : Finset (JoinVertex P m)) :
    Finset (Finset (Finset (JoinVertex P m))) :=
  BadEdge.sdPoset (origIndex P m) (faceFamily P m) S

/-- The geometric realization of the triangulation of a face. -/
def realization (S : Finset (JoinVertex P m)) : Set (PolytopalJoinAmbient n m) :=
  ⋃ σ ∈ sdQ P m S, simplexCarrier P m σ

/-- The whole Cayley join, as a face of itself. -/
def topFace : Finset (JoinVertex P m) := Finset.univ

/-! ### Basic properties of the face family and the carriers -/

theorem mem_faceVertexSet {C : Fin (m + 1) → PolytopeFaceIndex P} {w : JoinVertex P m} :
    w ∈ faceVertexSet P m C ↔ vtx P w.2 ∈ (C w.1).carrier := by
  classical
  simp [faceVertexSet]

theorem mem_faceFamily_iff {S : Finset (JoinVertex P m)} :
    S ∈ faceFamily P m ↔ ∃ C, faceVertexSet P m C = S := by
  simp [faceFamily]

theorem empty_mem_faceFamily : (∅ : Finset (JoinVertex P m)) ∈ faceFamily P m := by
  rw [mem_faceFamily_iff]
  have hface : P.IsFace (∅ : Set (CoordinateSpace n)) := isExposed_empty
  refine ⟨fun _ ↦ PolytopeFaceIndex.ofFace (∅ : Set (CoordinateSpace n)) hface, ?_⟩
  ext w
  rw [mem_faceVertexSet, PolytopeFaceIndex.carrier_ofFace]
  simp

theorem sdCarrier_mono {S T : Finset (JoinVertex P m)} (h : S ⊆ T) :
    sdCarrier P m S ⊆ sdCarrier P m T :=
  convexHull_mono (image_mono (by exact_mod_cast h))

theorem sdCarrier_convex (S : Finset (JoinVertex P m)) : Convex ℝ (sdCarrier P m S) :=
  convex_convexHull ℝ _

theorem sdCarrier_compact (S : Finset (JoinVertex P m)) : IsCompact (sdCarrier P m S) :=
  ((S.finite_toSet).image _).isCompact_convexHull ℝ

theorem sdPoint_mem_sdCarrier {a S : Finset (JoinVertex P m)} (hsub : a ⊆ S)
    (hne : a.Nonempty) : sdPoint P m a ∈ sdCarrier P m S := by
  have hmem := Finset.centerMass_mem_convexHull (R := ℝ) a (w := fun _ ↦ (1 : ℝ))
    (fun i _ ↦ zero_le_one) (by simpa using Finset.card_pos.mpr hne) (z := pt P m)
    (fun i hi ↦ mem_image_of_mem _ (hsub hi))
  simpa [Finset.centerMass, sdPoint, sdCarrier] using hmem

/-- **The carrier of a face of the Cayley join is the Cayley join of its
factors**, so the model used here is the one of `PolytopalJoin`,
`PolytopalDeletedJoin` and `PolytopalCellStructure`. -/
theorem sdCarrier_faceVertexSet (C : Fin (m + 1) → PolytopeFaceIndex P) :
    sdCarrier P m (faceVertexSet P m C) = cayleyJoin (fun i ↦ (C i).carrier) := by
  classical
  rw [cayleyJoin_eq_convexHull fun i ↦ (C i).convex, sdCarrier]
  apply Subset.antisymm
  · apply convexHull_mono
    rintro _ ⟨w, hw, rfl⟩
    exact mem_iUnion.mpr ⟨w.1, ⟨vtx P w.2, (mem_faceVertexSet P m).mp hw, rfl⟩⟩
  · apply convexHull_min _ (convex_convexHull ℝ _)
    rintro z hz
    obtain ⟨i, x, hx, rfl⟩ := mem_iUnion.mp hz
    have hxhull : x ∈ convexHull ℝ
        ((C i).carrier ∩ (P.actualVertices : Set (CoordinateSpace n))) := by
      rw [← P.face_eq_convexHull_actualVertices (C i).isFace]
      exact hx
    have himg : polytopalJoinCopy i x ∈
        convexHull ℝ (polytopalJoinCopy i ''
          ((C i).carrier ∩ (P.actualVertices : Set (CoordinateSpace n)))) := by
      have hhull := (polytopalJoinCopyAffine (m := m) i).image_convexHull
        ((C i).carrier ∩ (P.actualVertices : Set (CoordinateSpace n)))
      have hmem : polytopalJoinCopyAffine (m := m) i x ∈
          polytopalJoinCopyAffine i '' convexHull ℝ
            ((C i).carrier ∩ (P.actualVertices : Set (CoordinateSpace n))) := ⟨x, hxhull, rfl⟩
      rw [hhull] at hmem
      exact hmem
    refine convexHull_mono ?_ himg
    rintro _ ⟨v, ⟨hvface, hvvert⟩, rfl⟩
    obtain ⟨k, rfl⟩ := exists_vtx P (Finset.mem_coe.mp hvvert)
    exact ⟨(i, k), (mem_faceVertexSet P m).mpr hvface, rfl⟩

/-- **Every exposed face of a face of the Cayley join belongs to the family.**
This uses that an exposed face of an exposed face of a polytope is again an
exposed face (`isExposed_trans_convexHull`) and the classification of the faces
of a Cayley join. -/
theorem exists_faceFamily_exposedBy (C : Fin (m + 1) → PolytopeFaceIndex P)
    (l : PolytopalJoinAmbient n m →L[ℝ] ℝ) :
    ∃ G ∈ faceFamily P m, G ⊆ faceVertexSet P m C ∧
      sdCarrier P m G = exposedBy (sdCarrier P m (faceVertexSet P m C)) l := by
  rw [sdCarrier_faceVertexSet]
  obtain ⟨Gs, hGsexp, hGseq⟩ := exists_exposed_factors_exposedBy
    (fun i ↦ (C i).convex) (fun i ↦ (C i).compact) l
  have hface : ∀ i, P.IsFace (Gs i) := by
    intro i
    have h1 : IsExposed ℝ (convexHull ℝ (P.vertices : Set (CoordinateSpace n)))
        (C i).carrier := (C i).isFace
    exact isExposed_trans_convexHull h1 (hGsexp i)
  refine ⟨faceVertexSet P m (fun i ↦ PolytopeFaceIndex.ofFace (Gs i) (hface i)),
    (mem_faceFamily_iff P m).mpr ⟨_, rfl⟩, ?_, ?_⟩
  · intro w hw
    rw [mem_faceVertexSet] at hw ⊢
    rw [PolytopeFaceIndex.carrier_ofFace] at hw
    exact (hGsexp w.1).subset hw
  · rw [sdCarrier_faceVertexSet, hGseq]
    congr 1
    funext i
    exact PolytopeFaceIndex.carrier_ofFace _ _

theorem mem_sdQ_iff {S : Finset (JoinVertex P m)} {σ : Finset (Finset (JoinVertex P m))} :
    σ ∈ sdQ P m S ↔
      σ = ∅ ∨ ∃ G ∈ faceFamily P m, G ⊆ S ∧ ¬ apexSet (origIndex P m) S ⊆ G ∧
        (σ ∈ sdQ P m G ∨ ∃ τ ∈ sdQ P m G, σ = insert (apexSet (origIndex P m) S) τ) :=
  mem_sdPoset_iff

/-- **Compatibility on every exposed face**: the triangulation of a face of the
Cayley join is contained in the triangulation of any larger face. -/
theorem sdQ_mono {S G : Finset (JoinVertex P m)} (hG : G ∈ faceFamily P m)
    (hGS : G ⊆ S) : sdQ P m G ⊆ sdQ P m S :=
  sdPoset_mono hG hGS

/-- The triangulation is an abstract simplicial complex. -/
theorem sdQ_faceClosed {S : Finset (JoinVertex P m)}
    {σ τ : Finset (Finset (JoinVertex P m))} (hσ : σ ∈ sdQ P m S) (hτ : τ ⊆ σ) :
    τ ∈ sdQ P m S :=
  sdPoset_faceClosed hσ hτ

/-! ### The triangulation covers the face -/

/-- **The bad-vertex triangulation of a face of the Cayley join covers exactly
that face.** -/
theorem realization_eq_sdCarrier {S : Finset (JoinVertex P m)} (hS : S ∈ faceFamily P m) :
    realization P m S = sdCarrier P m S := by
  induction hk : S.card using Nat.strong_induction_on generalizing S with
  | _ k ih =>
    subst hk
    apply Subset.antisymm
    · apply iUnion₂_subset
      intro σ hσ
      apply convexHull_min _ (sdCarrier_convex P m S)
      rintro _ ⟨a, ha, rfl⟩
      exact sdPoint_mem_sdCarrier P m (sdPoset_vertex_subset hσ ha)
        (sdPoset_vertex_nonempty hσ ha)
    · intro x hx
      rcases S.eq_empty_or_nonempty with rfl | hSne
      · simp [sdCarrier] at hx
      · set a := apexSet (origIndex P m) S with ha_def
        have hane : a.Nonempty := apexSet_nonempty hSne
        have hasub : a ⊆ S := apexSet_subset _ _
        have hp : sdPoint P m a ∈ sdCarrier P m S := sdPoint_mem_sdCarrier P m hasub hane
        rcases exists_proper_exposedBy_mem_segment (sdCarrier_compact P m S)
          (sdCarrier_convex P m S) hp hx with heq | ⟨l, y, hy, hproper, hseg⟩
        · have hmem : ({a} : Finset (Finset (JoinVertex P m))) ∈ sdQ P m S := by
            rw [mem_sdQ_iff]
            refine Or.inr ⟨∅, empty_mem_faceFamily P m, Finset.empty_subset _, ?_,
              Or.inr ⟨∅, empty_mem_sdPoset _ _ _, by simp [ha_def]⟩⟩
            rw [← ha_def]
            intro hcon
            obtain ⟨u, hu⟩ := hane
            exact absurd (hcon hu) (by simp)
          refine mem_iUnion₂.mpr ⟨{a}, hmem, ?_⟩
          rw [heq]
          exact subset_convexHull ℝ _ ⟨a, by simp, rfl⟩
        · obtain ⟨C, hC⟩ := (mem_faceFamily_iff P m).mp hS
          subst hC
          obtain ⟨G, hGfam, hGsub, hGeq⟩ := exists_faceFamily_exposedBy P m C l
          have hyG : y ∈ sdCarrier P m G := by rw [hGeq]; exact hy
          have hGne : G ≠ faceVertexSet P m C := by
            intro hcon
            rw [hcon] at hGeq
            exact hproper hGeq.symm
          have hcard : G.card < (faceVertexSet P m C).card :=
            Finset.card_lt_card ((Finset.ssubset_iff_of_subset hGsub).mpr (by
              by_contra hcon
              rw [not_exists] at hcon
              refine hGne (Finset.Subset.antisymm hGsub fun z hz ↦ ?_)
              by_contra hzG
              exact (hcon z) ⟨hz, hzG⟩))
          have hIH : realization P m G = sdCarrier P m G := ih G.card hcard hGfam rfl
          rw [← hIH] at hyG
          obtain ⟨τ, hτ, hyτ⟩ := mem_iUnion₂.mp hyG
          by_cases hna : ¬ a ⊆ G
          · refine mem_iUnion₂.mpr ⟨insert a τ, ?_, ?_⟩
            · rw [mem_sdQ_iff]
              exact Or.inr ⟨G, hGfam, hGsub, hna, Or.inr ⟨τ, hτ, rfl⟩⟩
            · have hpm : sdPoint P m a ∈ simplexCarrier P m (insert a τ) :=
                subset_convexHull ℝ _ ⟨a, by simp, rfl⟩
              have hym : y ∈ simplexCarrier P m (insert a τ) := by
                refine convexHull_mono ?_ hyτ
                exact image_mono (by exact_mod_cast Finset.subset_insert a τ)
              exact (convex_convexHull ℝ _).segment_subset hpm hym hseg
          · rw [not_not] at hna
            have hpG : sdPoint P m a ∈ sdCarrier P m G :=
              sdPoint_mem_sdCarrier P m hna hane
            have hxG : x ∈ sdCarrier P m G :=
              (sdCarrier_convex P m G).segment_subset hpG (by rw [← hIH]; exact hyG) hseg
            rw [← hIH] at hxG
            obtain ⟨ρ, hρ, hxρ⟩ := mem_iUnion₂.mp hxG
            exact mem_iUnion₂.mpr ⟨ρ, sdPoset_mono hGfam hGsub hρ, hxρ⟩


/-! ### The whole join, deleted faces, and the good subcomplex -/

theorem carrier_isFace : P.IsFace P.carrier := IsExposed.refl _

theorem topFace_eq_faceVertexSet :
    topFace P m
      = faceVertexSet P m (fun _ ↦ PolytopeFaceIndex.ofFace P.carrier (carrier_isFace P)) := by
  ext w
  rw [mem_faceVertexSet, PolytopeFaceIndex.carrier_ofFace]
  simp only [topFace, Finset.mem_univ, true_iff]
  exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (P.actualVertices_subset (vtx_mem P w.2)))

theorem topFace_mem_faceFamily : topFace P m ∈ faceFamily P m :=
  (mem_faceFamily_iff P m).mpr ⟨_, (topFace_eq_faceVertexSet P m).symm⟩

/-- The top face is the whole polytopal join. -/
theorem sdCarrier_topFace : sdCarrier P m (topFace P m) = polytopalJoinCarrier P m := by
  rw [topFace_eq_faceVertexSet, sdCarrier_faceVertexSet, cayleyJoin_polytopalJoinCarrier]
  congr 1
  funext i
  exact PolytopeFaceIndex.carrier_ofFace _ _

/-- **The bad-vertex triangulation triangulates the whole Cayley join.** -/
theorem realization_topFace : realization P m (topFace P m) = polytopalJoinCarrier P m := by
  rw [realization_eq_sdCarrier P m (topFace_mem_faceFamily P m), sdCarrier_topFace]

/-- A face of the Cayley join contains no bad edge exactly when its factors are
pairwise disjoint, i.e. exactly when it is a cell of the polytopal deleted
join.  This uses the actual-vertex criterion `pairwise_disjoint_faces_iff`. -/
theorem isDeletedFace_faceVertexSet_iff (C : Fin (m + 1) → PolytopeFaceIndex P) :
    IsDeletedFace (origIndex P m) (faceVertexSet P m C) ↔
      Pairwise fun i j ↦ Disjoint (C i).carrier (C j).carrier := by
  constructor
  · intro hdel
    rw [P.pairwise_disjoint_faces_iff (fun i ↦ (C i).carrier) (fun i ↦ (C i).isFace)]
    intro i j hij v hv hvi hvj
    obtain ⟨k, rfl⟩ := exists_vtx P hv
    have h1 : ((i, k) : JoinVertex P m) ∈ faceVertexSet P m C := (mem_faceVertexSet P m).mpr hvi
    have h2 : ((j, k) : JoinVertex P m) ∈ faceVertexSet P m C := (mem_faceVertexSet P m).mpr hvj
    exact hij (congrArg Prod.fst (hdel _ h1 _ h2 rfl))
  · intro hpair u hu w hw horig
    have hui : vtx P u.2 ∈ (C u.1).carrier := (mem_faceVertexSet P m).mp hu
    have hwi : vtx P w.2 ∈ (C w.1).carrier := (mem_faceVertexSet P m).mp hw
    have hsnd : u.2 = w.2 := horig
    have hfst : u.1 = w.1 := by
      by_contra hne
      exact Set.disjoint_left.mp (hpair hne) hui (hsnd ▸ hwi)
    exact Prod.ext hfst hsnd

/-- The good simplices of the triangulation: those all of whose vertices are
original Cayley vertices (rather than bad-edge midpoints). -/
def goodSimplices (S : Finset (JoinVertex P m)) :
    Finset (Finset (Finset (JoinVertex P m))) :=
  (sdQ P m S).filter fun σ ↦ ∀ a ∈ σ, a.card = 1

/-- The geometric realization of the good induced subcomplex. -/
def goodRealization (S : Finset (JoinVertex P m)) : Set (PolytopalJoinAmbient n m) :=
  ⋃ σ ∈ goodSimplices P m S, simplexCarrier P m σ

/-- **The good induced subcomplex is exactly the polytopal deleted join.** -/
theorem goodRealization_topFace :
    goodRealization P m (topFace P m) = polytopalDeletedJoinCarrier P m := by
  apply Subset.antisymm
  · apply iUnion₂_subset
    intro σ hσ
    obtain ⟨hσQ, hgood⟩ := Finset.mem_filter.mp hσ
    obtain ⟨G, hGmem, hGsub, hGdel, hvert⟩ :=
      sdPoset_good_exists_deleted_face (empty_mem_faceFamily P m) hσQ hgood
    have hGfam : G ∈ faceFamily P m := by
      rcases hGmem with h | h
      · exact h
      · exact h ▸ topFace_mem_faceFamily P m
    obtain ⟨C, rfl⟩ := (mem_faceFamily_iff P m).mp hGfam
    have hpair : Pairwise fun i j ↦ Disjoint (C i).carrier (C j).carrier :=
      (isDeletedFace_faceVertexSet_iff P m C).mp hGdel
    have hcell : PolytopalDeletedCellIndex.carrier (⟨C, hpair⟩ : PolytopalDeletedCellIndex P m)
        = sdCarrier P m (faceVertexSet P m C) := by
      rw [sdCarrier_faceVertexSet]
      exact cayleyJoin_cell _
    refine le_trans ?_ (le_trans (le_of_eq hcell.symm)
      (PolytopalDeletedCellIndex.carrier_subset_deletedJoinCarrier _))
    apply convexHull_min _ (sdCarrier_convex P m _)
    rintro _ ⟨a, ha, rfl⟩
    exact sdPoint_mem_sdCarrier P m (hvert a ha) (sdPoset_vertex_nonempty hσQ ha)
  · intro z hz
    obtain ⟨D, hzD⟩ := mem_iUnion.mp hz
    have hpair : Pairwise fun i j ↦ Disjoint ((D.1 i)).carrier ((D.1 j)).carrier := D.2
    have hSfam : faceVertexSet P m D.1 ∈ faceFamily P m :=
      (mem_faceFamily_iff P m).mpr ⟨_, rfl⟩
    have hzc : z ∈ sdCarrier P m (faceVertexSet P m D.1) := by
      rw [sdCarrier_faceVertexSet, ← cayleyJoin_cell D]
      exact hzD
    rw [← realization_eq_sdCarrier P m hSfam] at hzc
    obtain ⟨σ, hσ, hzσ⟩ := mem_iUnion₂.mp hzc
    have hdel : IsDeletedFace (origIndex P m) (faceVertexSet P m D.1) :=
      (isDeletedFace_faceVertexSet_iff P m D.1).mpr hpair
    refine mem_iUnion₂.mpr ⟨σ, Finset.mem_filter.mpr ⟨?_, ?_⟩, hzσ⟩
    · exact sdQ_mono P m hSfam (Finset.subset_univ _) hσ
    · exact fun a ha ↦ sdPoset_card_eq_one_of_deleted hdel hσ ha

/-- **The midpoint of a bad edge really is outside the deleted join**, so the
good/bad distinction of the triangulation is the geometric one: a simplex lies
in the deleted join if and only if all of its vertices are good. -/
theorem sdPoint_notMem_deletedJoin {u w : JoinVertex P m} (huw : u ≠ w)
    (horig : origIndex P m u = origIndex P m w) :
    sdPoint P m {u, w} ∉ polytopalDeletedJoinCarrier P m := by
  have hsnd : u.2 = w.2 := horig
  have hfst : u.1 ≠ w.1 := fun h ↦ huw (Prod.ext h hsnd)
  set v := vtx P u.2 with hv
  have hcard : ({u, w} : Finset (JoinVertex P m)).card = 2 := Finset.card_pair huw
  have hpoint : sdPoint P m {u, w} = (2 : ℝ)⁻¹ • (pt P m u + pt P m w) := by
    rw [sdPoint, hcard, Finset.sum_pair huw]
    norm_num
  intro hmem
  obtain ⟨C, hzC⟩ := mem_iUnion.mp hmem
  rw [cayleyJoin_cell C] at hzC
  have hcomp : ∀ i : Fin (m + 1), (sdPoint P m {u, w}) i
      = (2 : ℝ)⁻¹ • ((pt P m u) i + (pt P m w) i) := by
    intro i
    rw [hpoint]
    rfl
  have hu1 : (sdPoint P m {u, w}) u.1 = ((2 : ℝ)⁻¹ • v, (2 : ℝ)⁻¹) := by
    rw [hcomp, show (pt P m u) u.1 = (v, (1 : ℝ)) from polytopalJoinCopy_apply_self _ _,
      show (pt P m w) u.1 = 0 from polytopalJoinCopy_apply_of_ne hfst _]
    simp [Prod.smul_mk]
  have hw1 : (sdPoint P m {u, w}) w.1 = ((2 : ℝ)⁻¹ • v, (2 : ℝ)⁻¹) := by
    rw [hcomp, show (pt P m w) w.1 = (v, (1 : ℝ)) by
        rw [pt, ← hsnd, ← hv]; exact polytopalJoinCopy_apply_self _ _,
      show (pt P m u) w.1 = 0 from polytopalJoinCopy_apply_of_ne (Ne.symm hfst) _]
    simp [Prod.smul_mk]
  have hmemu : v ∈ (C.1 u.1).carrier := by
    have h := hzC.1 u.1
    rw [hu1] at h
    simpa using h.2.2 (by norm_num)
  have hmemw : v ∈ (C.1 w.1).carrier := by
    have h := hzC.1 w.1
    rw [hw1] at h
    simpa using h.2.2 (by norm_num)
  exact Set.disjoint_left.mp (C.2 hfst) hmemu hmemw

end BadVertex
end AffineTverberg
