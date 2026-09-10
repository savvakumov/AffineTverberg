import AffineTverberg.SphereLocalHomology
import AffineTverberg.StarLinkHomotopy
import AffineTverberg.BoundaryIdentification

set_option linter.style.header false

/-!
# Links in a triangulated topological sphere are homology spheres

Let `K` be a finite geometric simplicial complex whose polyhedron carries an
*actual* homeomorphism with a norm sphere of dimension `N` (for the boundary of
a simplicial ball this is `IsSimplicialBall.boundaryHomeomorphSphere`, and for
the boundary join `IsSimplicialBall.fullBoundaryJoinHomeomorphSphere`).  No
piecewise-linear or combinatorial sphere hypothesis is made.

Combining

* the local homology isomorphism of `AffineTverberg.SphereLocalHomology`
  (`H_{k+1}(X) ≅ H_k(B ∖ {P})` for an open contractible neighbourhood `B`), with
* the open star as such a neighbourhood (`StarLinkRetract`), and
* the homotopy equivalence between the punctured open star and the actual link
  (`StarLinkHomotopy.puncturedOpenStarLinkHomotopyEquiv`),

gives the local structure result used by a dual-cell duality argument:

`isZero_realSingularHomology_closedStarLink_of_sphere` — the link of a carrier
point is acyclic in all degrees `k` with `0 < k` and `k + 1 < N`, and
`nontrivial_realSingularHomology_closedStarLink_of_sphere` — it has nontrivial
homology in the top degree `N - 1`.  In other words the links are homology
`(N-1)`-spheres, derived purely from the topological sphere structure.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric Set

namespace AffineTverberg

variable {e : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
  {L : Finset (CoordinateSpace e)} {p : CoordinateSpace e}

/-- The punctured open star is the intersection of the punctured polyhedron
with the open star, as spaces. -/
def puncturedOpenStarHomeomorph (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p) :
    ↥({q : ↥K.space | q ≠ (⟨p, hp.mem_space hL⟩ : ↥K.space)} ∩
        (Subtype.val ⁻¹' (openStarCone K L))) ≃ₜ ↥(puncturedOpenStar K L p) := by
  have hinter : ({q : ↥K.space | q ≠ (⟨p, hp.mem_space hL⟩ : ↥K.space)} ∩
      (Subtype.val ⁻¹' (openStarCone K L))) =
      Subtype.val ⁻¹' (puncturedOpenStar K L p) := by
    ext q
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, fun h => h1 (Subtype.ext h)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h2 (by simp [h]), h1⟩
  exact (Homeomorph.setCongr hinter).trans
    (subsetSubtypeHomeomorph (puncturedOpenStar_subset_space (K := K) (L := L) (p := p)))

/-- The homology of the actual link agrees with the homology of the punctured
neighbourhood of the carrier point cut out by the open star. -/
def closedStarLinkHomologyIso (hfin : K.faces.Finite) (hL : L ∈ K.faces)
    (hp : IsCarrierPoint K L p) (k : ℕ) :
    (realSingularHomology k).obj (TopCat.of ↥(closedStarLink K L)) ≅
      (realSingularHomology k).obj
        (AffChain.subSpace (X := TopCat.of ↥K.space)
          ({q : ↥K.space | q ≠ (⟨p, hp.mem_space hL⟩ : ↥K.space)} ∩
            (Subtype.val ⁻¹' (openStarCone K L)))) :=
  (realSingularHomologyIsoOfHomotopyEquiv
      (puncturedOpenStarLinkHomotopyEquiv hfin hL hp).symm k).trans
    (realSingularHomologyIsoOfHomotopyEquiv
      (puncturedOpenStarHomeomorph hL hp).symm.toHomotopyEquiv k)

/-- The open star, as a subset of the polyhedron, is an open contractible
neighbourhood of the carrier point. -/
theorem openStar_isOpen_contractible (hfin : K.faces.Finite) (hL : L ∈ K.faces)
    (hp : IsCarrierPoint K L p) :
    IsOpen (Subtype.val ⁻¹' (openStarCone K L) : Set ↥K.space) ∧
      (⟨p, hp.mem_space hL⟩ : ↥K.space) ∈ (Subtype.val ⁻¹' (openStarCone K L) : Set ↥K.space) ∧
      ContractibleSpace ↥(Subtype.val ⁻¹' (openStarCone K L) : Set ↥K.space) := by
  have hapex : p ∈ openStarCone K L := mem_openStarCone_apex hfin hL hp
  refine ⟨isOpen_preimage_openStarCone hfin, hapex, ?_⟩
  have h0 : ContractibleSpace ↥(openStarCone K L) :=
    (starConvex_openStarCone hL hp).contractibleSpace ⟨p, hapex⟩
  exact (subsetSubtypeHomeomorph
    (openStarCone_subset_space (K := K) (L := L))).toHomotopyEquiv.contractibleSpace

/-- The link of a face, as an actual subcomplex: the faces of `K` contained in
a codimension-one face `F.erase u` of a facet `F` through `L`, for a vertex
`u` of `L`. -/
def starLinkSubcomplex (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))
    (L : Finset (CoordinateSpace e)) : Geometry.SimplicialComplex ℝ (CoordinateSpace e) where
  faces := {s | s ∈ K.faces ∧ ∃ F ∈ facetsThrough K L, ∃ u ∈ L, s ⊆ F.erase u}
  isRelLowerSet_faces := by
    rintro s ⟨hsK, F, hF, u, hu, hsF⟩
    refine ⟨(K.isRelLowerSet_faces hsK).1, ?_⟩
    rintro t hts htne
    exact ⟨(K.isRelLowerSet_faces hsK).2 hts htne, F, hF, u, hu, hts.trans hsF⟩
  indep hs := K.indep hs.1
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1

/-- The polyhedron of the link subcomplex is the actual `closedStarLink`. -/
theorem starLinkSubcomplex_space (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))
    (L : Finset (CoordinateSpace e)) :
    (starLinkSubcomplex K L).space = closedStarLink K L := by
  apply Set.Subset.antisymm
  · refine Set.iUnion₂_subset fun s hs => ?_
    obtain ⟨hsK, F, hF, u, hu, hsF⟩ := hs
    refine subset_trans (convexHull_mono (by exact_mod_cast hsF)) ?_
    exact fun x hx => mem_closedStarLink_iff.mpr ⟨F, hF, u, hu, hx⟩
  · intro x hx
    obtain ⟨F, hF, u, hu, hxF⟩ := mem_closedStarLink_iff.mp hx
    have hne : (F.erase u).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h] at hxF
      simp at hxF
    have hFK : F ∈ K.faces := Geometry.SimplicialComplex.facets_subset hF.1
    have hmem : F.erase u ∈ (starLinkSubcomplex K L).faces :=
      ⟨(K.isRelLowerSet_faces hFK).2 (Finset.erase_subset _ _) hne,
        F, hF, u, hu, Finset.Subset.refl _⟩
    exact Set.mem_biUnion hmem hxF

theorem starLinkSubcomplex_faces_finite {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
    (hfin : K.faces.Finite) (L : Finset (CoordinateSpace e)) :
    (starLinkSubcomplex K L).faces.Finite :=
  hfin.subset fun _ hs => hs.1

/-- **Links in a triangulated topological sphere are acyclic below the top
degree.**  If the polyhedron of a finite geometric simplicial complex is
homeomorphic to an `N`-sphere, the link of any carrier point has vanishing real
singular homology in every degree `k` with `0 < k` and `k + 1 < N`. -/
theorem isZero_realSingularHomology_closedStarLink_of_sphere
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {N : ℕ}
    (hfin : K.faces.Finite) (hdim : Module.finrank ℝ E = N + 1)
    (hsph : ↥K.space ≃ₜ sphere (0 : E) 1)
    (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p)
    (k : ℕ) (hk : 0 < k) (hkN : k + 1 < N) :
    IsZero ((realSingularHomology k).obj (TopCat.of ↥(closedStarLink K L))) := by
  obtain ⟨hopen, hmem, hcontr⟩ := openStar_isOpen_contractible hfin hL hp
  have hzero := isZero_realSingularHomology_puncturedNbhd_of_sphere hdim hsph
    (P := (⟨p, hp.mem_space hL⟩ : ↥K.space))
    (B := (Subtype.val ⁻¹' (openStarCone K L) : Set ↥K.space)) hopen hmem hcontr k hk hkN
  exact IsZero.of_iso hzero (closedStarLinkHomologyIso hfin hL hp k)

/-- **Links in a triangulated topological sphere are acyclic above the top
degree.** -/
theorem isZero_realSingularHomology_closedStarLink_of_sphere_of_gt
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {N : ℕ}
    (hfin : K.faces.Finite) (hdim : Module.finrank ℝ E = N + 1)
    (hsph : ↥K.space ≃ₜ sphere (0 : E) 1)
    (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p)
    (k : ℕ) (hk : 0 < k) (hkN : N < k + 1) :
    IsZero ((realSingularHomology k).obj (TopCat.of ↥(closedStarLink K L))) := by
  obtain ⟨hopen, hmem, hcontr⟩ := openStar_isOpen_contractible hfin hL hp
  have hzero := isZero_realSingularHomology_puncturedNbhd_of_sphere_of_gt hdim hsph
    (P := (⟨p, hp.mem_space hL⟩ : ↥K.space))
    (B := (Subtype.val ⁻¹' (openStarCone K L) : Set ↥K.space)) hopen hmem hcontr k hk hkN
  exact IsZero.of_iso hzero (closedStarLinkHomologyIso hfin hL hp k)

/-- **Links in a triangulated topological sphere are homology spheres.**  The
link of a carrier point of a face has vanishing real singular homology in every
positive degree except `N - 1`. -/
theorem isZero_realSingularHomology_closedStarLink_of_sphere_of_ne
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {N : ℕ}
    (hfin : K.faces.Finite) (hdim : Module.finrank ℝ E = N + 1)
    (hsph : ↥K.space ≃ₜ sphere (0 : E) 1)
    (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p)
    (k : ℕ) (hk : 0 < k) (hkN : k + 1 ≠ N) :
    IsZero ((realSingularHomology k).obj (TopCat.of ↥(closedStarLink K L))) := by
  rcases lt_or_gt_of_ne hkN with h | h
  · exact isZero_realSingularHomology_closedStarLink_of_sphere hfin hdim hsph hL hp k hk h
  · exact isZero_realSingularHomology_closedStarLink_of_sphere_of_gt hfin hdim hsph hL hp k hk h

/-- **Links in a triangulated topological sphere are nontrivial in the top
degree.**  If the polyhedron is homeomorphic to a `(k+1)`-sphere, the link of
any carrier point has nontrivial real singular homology in degree `k`. -/
theorem nontrivial_realSingularHomology_closedStarLink_of_sphere
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {k : ℕ}
    (hfin : K.faces.Finite) (hdim : Module.finrank ℝ E = k + 2)
    (hsph : ↥K.space ≃ₜ sphere (0 : E) 1)
    (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p) (hk : 0 < k) :
    Nontrivial ((realSingularHomology k).obj (TopCat.of ↥(closedStarLink K L))) := by
  obtain ⟨hopen, hmem, hcontr⟩ := openStar_isOpen_contractible hfin hL hp
  have hnt := nontrivial_realSingularHomology_puncturedNbhd_of_sphere hdim hsph
    (P := (⟨p, hp.mem_space hL⟩ : ↥K.space))
    (B := (Subtype.val ⁻¹' (openStarCone K L) : Set ↥K.space)) hopen hmem hcontr hk
  apply not_subsingleton_iff_nontrivial.mp
  intro hs
  have hzero : IsZero ((realSingularHomology k).obj (TopCat.of ↥(closedStarLink K L))) := by
    have := hs
    exact ModuleCat.isZero_of_subsingleton _
  have hzero' := IsZero.of_iso hzero (closedStarLinkHomologyIso hfin hL hp k).symm
  exact not_subsingleton _ (ModuleCat.subsingleton_of_isZero hzero')


/-- **Every point of a triangulated topological sphere has a homology-sphere
link.**  Packaging the two statements above with the existence of a carrier
face, which shows they are not vacuous: for every point of the polyhedron
there is a face carrying it, and the link of that face is acyclic in every
positive degree other than `N - 1` and nontrivial in degree `N - 1`. -/
theorem exists_carrierFace_link_homologySphere
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {N : ℕ}
    (hfin : K.faces.Finite) (hdim : Module.finrank ℝ E = N + 2)
    (hsph : ↥K.space ≃ₜ sphere (0 : E) 1) (hN : 0 < N)
    {x : CoordinateSpace e} (hx : x ∈ K.space) :
    ∃ L ∈ K.faces, IsCarrierPoint K L x ∧
      (∀ k : ℕ, 0 < k → k ≠ N →
        IsZero ((realSingularHomology k).obj (TopCat.of ↥(closedStarLink K L)))) ∧
      Nontrivial ((realSingularHomology N).obj (TopCat.of ↥(closedStarLink K L))) := by
  obtain ⟨L, hL, hp⟩ := exists_carrierPoint hfin hx
  refine ⟨L, hL, hp, ?_, ?_⟩
  · intro k hk hkN
    exact isZero_realSingularHomology_closedStarLink_of_sphere_of_ne
      (N := N + 1) hfin hdim hsph hL hp k hk (by omega)
  · exact nontrivial_realSingularHomology_closedStarLink_of_sphere
      (k := N) hfin hdim hsph hL hp hN

/-! ### The link as a subcomplex is a homology sphere -/

/-- **The link subcomplex of a triangulated topological sphere is a homology
`(N-1)`-sphere: vanishing part.** -/
theorem isZero_realSingularHomology_starLinkSubcomplex_of_sphere
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {N : ℕ}
    (hfin : K.faces.Finite) (hdim : Module.finrank ℝ E = N + 1)
    (hsph : ↥K.space ≃ₜ sphere (0 : E) 1)
    (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p)
    (k : ℕ) (hk : 0 < k) (hkN : k + 1 ≠ N) :
    IsZero ((realSingularHomology k).obj (TopCat.of ↥(starLinkSubcomplex K L).space)) := by
  rw [starLinkSubcomplex_space]
  exact isZero_realSingularHomology_closedStarLink_of_sphere_of_ne hfin hdim hsph hL hp k hk hkN

/-- **The link subcomplex of a triangulated topological sphere is a homology
`(N-1)`-sphere: nontriviality part.** -/
theorem nontrivial_realSingularHomology_starLinkSubcomplex_of_sphere
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {k : ℕ}
    (hfin : K.faces.Finite) (hdim : Module.finrank ℝ E = k + 2)
    (hsph : ↥K.space ≃ₜ sphere (0 : E) 1)
    (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p) (hk : 0 < k) :
    Nontrivial ((realSingularHomology k).obj
      (TopCat.of ↥(starLinkSubcomplex K L).space)) := by
  rw [starLinkSubcomplex_space]
  exact nontrivial_realSingularHomology_closedStarLink_of_sphere hfin hdim hsph hL hp hk

/-! ### The actual boundary sphere of a simplicial ball -/

section BoundaryComplex

variable {n : ℕ}

/-- The subcomplex of the boundary faces of a complex.  Its polyhedron is the
actual boundary carrier `simplicialBoundaryCarrier`. -/
def boundarySubcomplex (n : ℕ) (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)) :
    Geometry.SimplicialComplex ℝ (CoordinateSpace e) where
  faces := {s | IsBoundarySimplicialFace n K s}
  isRelLowerSet_faces := by
    rintro s ⟨hsK, ridge, hridge, hsr⟩
    refine ⟨(K.isRelLowerSet_faces hsK).1, ?_⟩
    rintro t hts htne
    exact ⟨(K.isRelLowerSet_faces hsK).2 hts htne, ridge, hridge, hts.trans hsr⟩
  indep hs := K.indep hs.1
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1

@[simp] theorem boundarySubcomplex_faces
    (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)) :
    (boundarySubcomplex n K).faces = {s | IsBoundarySimplicialFace n K s} := rfl

/-- The polyhedron of the boundary subcomplex is the boundary carrier. -/
theorem boundarySubcomplex_space (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)) :
    (boundarySubcomplex n K).space = simplicialBoundaryCarrier K n := rfl

theorem boundarySubcomplex_faces_finite {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
    (hfin : K.faces.Finite) : (boundarySubcomplex n K).faces.Finite :=
  hfin.subset fun _ hs => hs.1

namespace IsSimplicialBall

/-- The sphere presentation of the polyhedron of the boundary subcomplex. -/
def boundarySubcomplexHomeomorphSphere {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
    (hball : IsSimplicialBall n K) (hn : 2 ≤ n) :
    ↥(boundarySubcomplex n K).space ≃ₜ ↥(sphere (0 : CoordinateSpace n) 1) :=
  Homeomorph.setCongr (boundarySubcomplex_space K) |>.trans
    (hball.boundaryHomeomorphSphere hn)

/-- **Links in the boundary sphere of a simplicial ball are acyclic below the
top degree.**  The boundary of an `n`-ball is an `(n-1)`-sphere, so the link of
a carrier point of a boundary face is acyclic in every degree `k` with
`0 < k` and `k + 2 < n`. -/
theorem isZero_realSingularHomology_closedStarLink_boundary
    {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
    (hball : IsSimplicialBall n K) (hn : 2 ≤ n)
    {L : Finset (CoordinateSpace e)} {p : CoordinateSpace e}
    (hL : L ∈ (boundarySubcomplex n K).faces)
    (hp : IsCarrierPoint (boundarySubcomplex n K) L p)
    (k : ℕ) (hk : 0 < k) (hkn : k + 2 < n) :
    IsZero ((realSingularHomology k).obj
      (TopCat.of ↥(closedStarLink (boundarySubcomplex n K) L))) := by
  refine isZero_realSingularHomology_closedStarLink_of_sphere
    (E := CoordinateSpace n) (N := n - 1)
    (boundarySubcomplex_faces_finite hball.finite_faces) ?_
    (hball.boundarySubcomplexHomeomorphSphere hn) hL hp k hk (by omega)
  simp only [CoordinateSpace, Module.finrank_pi, Fintype.card_fin]
  omega

/-- **Links in the boundary sphere of a simplicial ball are nontrivial in the
top degree `n - 2`.** -/
theorem nontrivial_realSingularHomology_closedStarLink_boundary
    {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
    (hball : IsSimplicialBall n K) (hn : 3 ≤ n)
    {L : Finset (CoordinateSpace e)} {p : CoordinateSpace e}
    (hL : L ∈ (boundarySubcomplex n K).faces)
    (hp : IsCarrierPoint (boundarySubcomplex n K) L p) :
    Nontrivial ((realSingularHomology (n - 2)).obj
      (TopCat.of ↥(closedStarLink (boundarySubcomplex n K) L))) := by
  refine nontrivial_realSingularHomology_closedStarLink_of_sphere
    (E := CoordinateSpace n) (k := n - 2)
    (boundarySubcomplex_faces_finite hball.finite_faces) ?_
    (hball.boundarySubcomplexHomeomorphSphere (by omega)) hL hp (by omega)
  simp only [CoordinateSpace, Module.finrank_pi, Fintype.card_fin]
  omega

end IsSimplicialBall

end BoundaryComplex

end AffineTverberg
