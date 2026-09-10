import AffineTverberg.DualBlockLink
import AffineTverberg.OrdinaryLinkHomology

set_option linter.style.header false

/-!
# The boundary of a dual block is a homology sphere

`DualBlockLink` identifies the boundary of the dual block of `s` with the
barycentric subdivision of the *ordinary* combinatorial link of `s`, realized
by placing the link face `t` at the barycenter of the coface `t ∪ s`.  That
placement is not the standard barycentric placement of the link, so the
identification is upgraded here to an actual homeomorphism with the standard
polyhedron of the link:

* `IsGeometricRealization.of_injOn` — transport of a geometric realization
  along a relabelling of the vertices which is injective on the faces;
* `isGeometricRealization_single` — the barycentric model itself is a
  geometric realization, so `|sd L|` is homeomorphic to `|L|`
  (`barycentricSubdivisionHomeomorph`);
* `dualBlockBoundaryHomeomorph` — `∂D(s) ≃ₜ |link K s|`;
* `isZero_realSingularHomology_dualBlockBoundary_of_sphere` and
  `not_isZero_realSingularHomology_dualBlockBoundary_of_sphere` — combining
  with `OrdinaryLinkHomology`, the boundary of the dual block of a nonempty
  face `s` of a triangulated topological `N`-sphere is a homology
  `(N - #s)`-sphere.

Nothing here assumes that a dual block is a ball, nor any PL or shellability
hypothesis.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric Set

namespace AffineTverberg.Simplicial

section Transport

variable {W : Type*} [DecidableEq W] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A geometric realization of a relabelled family gives a geometric
realization of the original family, provided the relabelling is injective on
pairs of faces. -/
theorem IsGeometricRealization.of_injOn {F : Finset (Finset W)} {φ : W → W} {pb : W → E}
    (hinj : ∀ C ∈ F, ∀ D ∈ F, Set.InjOn φ ((C : Set W) ∪ (D : Set W)))
    (h : IsGeometricRealization (F.image (Finset.image φ)) pb) :
    IsGeometricRealization F (fun w ↦ pb (φ w)) := by
  classical
  constructor
  · intro C hC
    have hmem : C.image φ ∈ F.image (Finset.image φ) := Finset.mem_image_of_mem _ hC
    have hind := h.independent _ hmem
    have hinjC : Set.InjOn φ (C : Set W) :=
      (hinj C hC C hC).mono (Set.subset_union_left)
    let emb : (C : Finset W) ↪ (C.image φ : Finset W) :=
      ⟨fun w ↦ ⟨φ w.val, Finset.mem_image_of_mem _ w.property⟩, by
        intro w w' hww'
        exact Subtype.ext (hinjC w.property w'.property (congrArg Subtype.val hww'))⟩
    exact hind.comp_embedding emb
  · intro C hC D hD
    have hCD : (C.image φ) ∩ (D.image φ) ⊆ (C ∩ D).image φ := by
      intro u hu
      obtain ⟨huC, huD⟩ := Finset.mem_inter.mp hu
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp huC
      obtain ⟨w', hw', hww'⟩ := Finset.mem_image.mp huD
      have hweq : w' = w := hinj C hC D hD (Or.inr hw') (Or.inl hw) hww'
      exact Finset.mem_image_of_mem _ (Finset.mem_inter.mpr ⟨hw, hweq ▸ hw'⟩)
    have himg : ∀ A : Finset W, (fun w ↦ pb (φ w)) '' (A : Set W) = pb '' (A.image φ : Set W) := by
      intro A
      rw [Finset.coe_image, Set.image_image]
    rw [himg C, himg D, himg (C ∩ D)]
    refine (h.intersection _ (Finset.mem_image_of_mem _ hC) _
      (Finset.mem_image_of_mem _ hD)).trans ?_
    exact convexHull_mono (Set.image_mono (by exact_mod_cast hCD))

end Transport

section Standard

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The barycentric model is itself a geometric realization, with the standard
basis vectors as vertices. -/
theorem isGeometricRealization_single (L : Finset (Finset V)) :
    IsGeometricRealization L (fun v ↦ Pi.single v (1 : ℝ)) := by
  constructor
  · intro s _
    have hli : LinearIndependent ℝ (fun v : s ↦ (Pi.single v.val (1 : ℝ) : V → ℝ)) := by
      rw [linearIndependent_iff']
      intro t g hg i hi
      have heval := congrFun hg i.val
      rw [Finset.sum_apply, Finset.sum_eq_single i] at heval
      · simpa using heval
      · intro j _ hji
        have hne : j.val ≠ i.val := fun h ↦ hji (Subtype.ext h)
        simp [hne]
      · intro hcon
        exact absurd hi hcon
    exact hli.affineIndependent
  · intro s _ t _
    rw [← barycentricFace_eq_convexHull, ← barycentricFace_eq_convexHull,
      ← barycentricFace_eq_convexHull]
    rintro x ⟨hxs, hxt⟩
    refine ⟨hxs.1, hxs.2.1, ?_⟩
    intro v hv
    rw [Finset.mem_inter, not_and_or] at hv
    rcases hv with hv | hv
    · exact hxs.2.2 v hv
    · exact hxt.2.2 v hv

theorem geometricCarrier_single (L : Finset (Finset V)) :
    geometricCarrier L (fun v ↦ Pi.single v (1 : ℝ)) = barycentricCarrier L := by
  rw [barycentricCarrier_eq_union, geometricCarrier]
  exact Set.iUnion₂_congr fun s _ ↦ (barycentricFace_eq_convexHull s).symm

/-- The polyhedron of the barycentric subdivision is homeomorphic to the
polyhedron of the original family. -/
def barycentricSubdivisionHomeomorph {L : Finset (Finset V)} (hL : FaceClosed L) :
    ↥(barycentricCarrier (subdivisionFaces L)) ≃ₜ ↥(barycentricCarrier L) :=
  (geometricRealizationHomeomorph
    (isGeometricRealization_subdivisionFaces (isGeometricRealization_single L))).trans
      (Homeomorph.setCongr
        ((geometricCarrier_subdivisionFaces hL).trans (geometricCarrier_single L)))

end Standard

section LinkRealization

variable {V : Type} [Finite V] [LinearOrder V]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Finset (Finset V)} {p : V → E}

/-- Placing the link face `t` at the barycenter of the coface `t ∪ s` is an
actual geometric realization of the subdivided link. -/
theorem isGeometricRealization_subdivisionFaces_link (hgeom : IsGeometricRealization K p)
    (s : Finset V) :
    IsGeometricRealization (subdivisionFaces (link K s))
      (fun t ↦ faceBarycenter p (t ∪ s)) := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  refine IsGeometricRealization.of_injOn (φ := fun t ↦ t ∪ s) ?_ ?_
  · intro C hC D hD t ht t' ht' hunion
    have hdisj : ∀ u : Finset V, u ∈ (C : Set (Finset V)) ∪ (D : Set (Finset V)) →
        Disjoint u s := by
      intro u hu
      rcases hu with hu | hu
      · exact (mem_link_iff.mp ((mem_subdivisionFaces.mp hC).1 hu)).2
      · exact (mem_link_iff.mp ((mem_subdivisionFaces.mp hD).1 hu)).2
    have hunion' : t ∪ s = t' ∪ s := hunion
    have h1 : (t ∪ s) \ s = t := by
      rw [Finset.union_sdiff_right, Finset.sdiff_eq_self_of_disjoint (hdisj t ht)]
    have h2 : (t' ∪ s) \ s = t' := by
      rw [Finset.union_sdiff_right, Finset.sdiff_eq_self_of_disjoint (hdisj t' ht')]
    rw [← h1, ← h2, hunion']
  · rw [← dualBlockBoundaryFaces_eq_image]
    exact (isGeometricRealization_subdivisionFaces hgeom).mono
      ((dualBlockBoundaryFaces_subset K s).trans (dualBlockFaces_subset K s))

end LinkRealization

section DualBlock

variable {V : Type} [Fintype V] [LinearOrder V]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Finset (Finset V)} {p : V → E} {s : Finset V}

/-- **The boundary of the dual block of `s` is the polyhedron of the ordinary
link of `s`.**  This is an actual homeomorphism, not just an equality of face
families with a nonstandard vertex placement. -/
def dualBlockBoundaryHomeomorph (hgeom : IsGeometricRealization K p) (hK : FaceClosed K)
    (s : Finset V) :
    ↥(dualBlockBoundarySpace K p s) ≃ₜ ↥(barycentricCarrier (link K s)) :=
  (Homeomorph.setCongr (dualBlockBoundarySpace_eq_geometricCarrier K p s)).trans
    (((geometricRealizationHomeomorph
      (isGeometricRealization_subdivisionFaces_link hgeom s)).symm).trans
        (barycentricSubdivisionHomeomorph (faceClosed_link hK s)))

section Sphere

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The boundary of a dual block of a triangulated topological sphere is a
homology sphere: the vanishing half.**  Its real singular homology vanishes in
every positive degree `j` with `j + 1 + #s ≠ N + 1`, i.e. in every positive
degree other than `N - #s`. -/
theorem isZero_realSingularHomology_dualBlockBoundary_of_sphere
    (hgeom : IsGeometricRealization K p) (hK : FaceClosed K) (hsK : s ∈ K) (hs : s.Nonempty)
    {N : ℕ} (hdim : Module.finrank ℝ F = N + 1) (hN : 1 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : F) 1) (j : ℕ) (hj : 0 < j)
    (hne : j + 1 + s.card ≠ N + 1) :
    IsZero ((realSingularHomology j).obj
      (TopCat.of ↥(dualBlockBoundarySpace K p s))) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hacyc : IsReducedAcyclicAt ℝ (link K s) (m + 2) :=
    isReducedAcyclicAt_link_of_sphere hK hsK hs hdim hN e (m + 2) (by omega)
  have hzero : IsZero ((realSingularHomology (m + 1)).obj (barySpace (link K s))) :=
    (isZero_realSingularHomology_barySpace_iff (faceClosed_link hK s) m).mpr hacyc
  have hsub : Subsingleton ((realSingularHomology (m + 1)).obj
      (TopCat.of ↥(dualBlockBoundarySpace K p s))) :=
    (realSingularHomology_subsingleton_iff_of_homotopyEquiv
      (dualBlockBoundaryHomeomorph hgeom hK s).toHomotopyEquiv (m + 1)).mpr
        (ModuleCat.subsingleton_of_isZero hzero)
  exact ModuleCat.isZero_of_subsingleton _

/-- **The boundary of a dual block of a triangulated topological sphere is a
homology sphere: the nonvanishing half.**  In the degree `N - #s` its real
singular homology does not vanish. -/
theorem not_isZero_realSingularHomology_dualBlockBoundary_of_sphere
    (hgeom : IsGeometricRealization K p) (hK : FaceClosed K) (hsK : s ∈ K) (hs : s.Nonempty)
    {N : ℕ} (hdim : Module.finrank ℝ F = N + 1) (hN : 2 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : F) 1) (j : ℕ) (hj : 0 < j)
    (heq : j + 1 + s.card = N + 1) :
    ¬ IsZero ((realSingularHomology j).obj
      (TopCat.of ↥(dualBlockBoundarySpace K p s))) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  intro hzero
  have hsub : Subsingleton ((realSingularHomology (m + 1)).obj (barySpace (link K s))) :=
    (realSingularHomology_subsingleton_iff_of_homotopyEquiv
      (dualBlockBoundaryHomeomorph hgeom hK s).toHomotopyEquiv (m + 1)).mp
        (ModuleCat.subsingleton_of_isZero hzero)
  have hacyc : IsReducedAcyclicAt ℝ (link K s) (m + 2) :=
    (isZero_realSingularHomology_barySpace_iff (faceClosed_link hK s) m).mp
      (ModuleCat.isZero_of_subsingleton _)
  exact not_isReducedAcyclicAt_link_of_sphere hK hsK hs hdim e (m + 2) hN (by omega) hacyc

end Sphere

end DualBlock

end AffineTverberg.Simplicial
