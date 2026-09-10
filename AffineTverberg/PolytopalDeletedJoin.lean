import AffineTverberg.PolytopalJoin

set_option linter.style.header false

/-!
# The finite polytopal deleted join

This file realizes the deleted join `D = P^{*r}_Δ` as the finite union of
the Cayley joins of pairwise disjoint faces of `P`.  Unlike the represented
points in `DeletedJoin.lean`, this is an actual compact subset of the finite
dimensional join ambient space and can therefore serve as the domain of the
incidence and proper-map argument.
-/

noncomputable section

open Set

namespace AffineTverberg

namespace FullDimensionalPolytope

variable {n : ℕ} (P : FullDimensionalPolytope n)

/-- The chosen finite generators of `P` which lie in `F`. -/
noncomputable def faceVertices (F : Set (CoordinateSpace n)) :
    Finset (CoordinateSpace n) := by
  classical
  exact P.vertices.filter fun v ↦ v ∈ F

@[simp]
theorem mem_faceVertices {F : Set (CoordinateSpace n)} {v : CoordinateSpace n} :
    v ∈ P.faceVertices F ↔ v ∈ P.vertices ∧ v ∈ F := by
  classical
  simp [faceVertices]

/-- An exposed face of a finitely generated polytope is the convex hull of
exactly those chosen generators which lie in the face. -/
theorem face_eq_convexHull_filter_vertices {F : Set (CoordinateSpace n)}
    (hF : P.IsFace F) :
    F = convexHull ℝ (P.faceVertices F : Set (CoordinateSpace n)) := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | hFne
  · simp [faceVertices]
  obtain ⟨l, hl⟩ := hF hFne
  obtain ⟨w, hwF⟩ := hFne
  have hw : w ∈ P.carrier ∧ ∀ y ∈ P.carrier, l y ≤ l w := by
    rw [hl] at hwF
    exact hwF
  let A : CompactConvexProjection (CoordinateSpace n) (CoordinateSpace 0) :=
    { carrier := P.carrier
      carrier_compact := P.vertices.finite_toSet.isCompact_convexHull ℝ
      carrier_convex := convex_convexHull ℝ _
      projection := 0
      height := l }
  let c : CompactConvexProjection.UpperSupportCertificate A :=
    { slope := 0
      intercept := l w
      upper_bound := by
        intro x hx
        simpa [A] using hw.2 x hx
      contact_nonempty := by
        refine ⟨w, hw.1, ?_⟩
        simp [A] }
  have hcF : c.contactSet = F := by
    ext x
    constructor
    · rintro ⟨hxP, hxeq⟩
      rw [hl]
      refine ⟨hxP, fun y hy ↦ ?_⟩
      have hxy : l x = l w := by
        simpa [c, CompactConvexProjection.UpperSupportCertificate.eval, A] using hxeq
      exact (hw.2 y hy).trans_eq hxy.symm
    · intro hxF
      have hx : x ∈ P.carrier ∧ ∀ y ∈ P.carrier, l y ≤ l x := by
        rw [hl] at hxF
        exact hxF
      refine ⟨hx.1, ?_⟩
      have hle₁ : l w ≤ l x := hx.2 w hw.1
      have hle₂ : l x ≤ l w := hw.2 x hx.1
      have heq : l x = l w := le_antisymm hle₂ hle₁
      simpa [c, CompactConvexProjection.UpperSupportCertificate.eval, A] using heq
  apply Subset.antisymm
  · intro x hxF
    have hxc : x ∈ c.contactSet := hcF.symm ▸ hxF
    have hxHull :=
      CompactConvexProjection.mem_convexHull_tight_vertices
        A P.vertices rfl c hxc
    have hvertexSet :
        {v : CoordinateSpace n |
            v ∈ (P.vertices : Set (CoordinateSpace n)) ∧ v ∈ c.contactSet} =
          (P.faceVertices F : Set (CoordinateSpace n)) := by
      ext v
      simp [hcF, FullDimensionalPolytope.faceVertices]
    rwa [hvertexSet] at hxHull
  · apply convexHull_min
    · intro v hv
      exact (P.mem_faceVertices.mp (Finset.mem_coe.mp hv)).2
    · exact hF.convex (convex_convexHull ℝ _)

end FullDimensionalPolytope

/-- A subset of the fixed finite generating set of `P`. -/
abbrev PolytopeVertexSubset {n : ℕ} (P : FullDimensionalPolytope n) :=
  {s : Finset (CoordinateSpace n) // s ∈ P.vertices.powerset}

/-- The finite type of exposed faces, encoded by their generating vertices. -/
abbrev PolytopeFaceIndex {n : ℕ} (P : FullDimensionalPolytope n) :=
  {s : PolytopeVertexSubset P //
    P.IsFace (convexHull ℝ (s.1 : Set (CoordinateSpace n)))}

namespace PolytopeFaceIndex

variable {n : ℕ} {P : FullDimensionalPolytope n}

noncomputable instance : Fintype (PolytopeFaceIndex P) :=
  Fintype.ofFinite (PolytopeFaceIndex P)

/-- The geometric carrier of a finitely indexed face. -/
def carrier (F : PolytopeFaceIndex P) : Set (CoordinateSpace n) :=
  convexHull ℝ (F.1.1 : Set (CoordinateSpace n))

theorem isFace (F : PolytopeFaceIndex P) : P.IsFace F.carrier :=
  F.2

theorem compact (F : PolytopeFaceIndex P) : IsCompact F.carrier :=
  F.1.1.finite_toSet.isCompact_convexHull ℝ

theorem convex (F : PolytopeFaceIndex P) : Convex ℝ F.carrier :=
  convex_convexHull ℝ _

/-- Every set-theoretic face has a canonical finite face index. -/
def ofFace (F : Set (CoordinateSpace n)) (hF : P.IsFace F) :
    PolytopeFaceIndex P := by
  classical
  let s := P.faceVertices F
  refine ⟨⟨s, Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩, ?_⟩
  rw [← P.face_eq_convexHull_filter_vertices hF]
  exact hF

@[simp]
theorem carrier_ofFace (F : Set (CoordinateSpace n)) (hF : P.IsFace F) :
    (ofFace F hF).carrier = F := by
  exact (P.face_eq_convexHull_filter_vertices hF).symm

end PolytopeFaceIndex

/-- A tuple of pairwise disjoint faces, hence a cell of the deleted join. -/
abbrev PolytopalDeletedCellIndex {n : ℕ} (P : FullDimensionalPolytope n) (m : ℕ) :=
  {f : Fin (m + 1) → PolytopeFaceIndex P //
    Pairwise fun i j ↦ Disjoint (f i).carrier (f j).carrier}

namespace PolytopalDeletedCellIndex

variable {n m : ℕ} {P : FullDimensionalPolytope n}

noncomputable instance : Fintype (PolytopalDeletedCellIndex P m) :=
  Fintype.ofFinite (PolytopalDeletedCellIndex P m)

/-- The finite Cayley vertex set of one deleted-join cell. -/
noncomputable def vertices (C : PolytopalDeletedCellIndex P m) :
    Finset (PolytopalJoinAmbient n m) := by
  classical
  exact Finset.univ.biUnion fun i ↦
    (C.1 i).1.1.image fun v ↦ polytopalJoinCopy i v

/-- The Cayley join of the faces in a deleted cell. -/
def carrier (C : PolytopalDeletedCellIndex P m) :
    Set (PolytopalJoinAmbient n m) :=
  convexHull ℝ (C.vertices : Set (PolytopalJoinAmbient n m))

theorem compact (C : PolytopalDeletedCellIndex P m) : IsCompact C.carrier :=
  C.vertices.finite_toSet.isCompact_convexHull ℝ

theorem convex (C : PolytopalDeletedCellIndex P m) : Convex ℝ C.carrier :=
  convex_convexHull ℝ _

theorem copy_vertex_mem_vertices (C : PolytopalDeletedCellIndex P m)
    (i : Fin (m + 1)) {v : CoordinateSpace n}
    (hv : v ∈ (C.1 i).1.1) :
    polytopalJoinCopy i v ∈ C.vertices := by
  classical
  rw [vertices, Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩

/-- The copy of every point of a component face lies in its Cayley cell. -/
theorem copy_mem_carrier (C : PolytopalDeletedCellIndex P m)
    (i : Fin (m + 1)) {x : CoordinateSpace n}
    (hx : x ∈ (C.1 i).carrier) :
    polytopalJoinCopy i x ∈ C.carrier := by
  have hximage : polytopalJoinCopyAffine i x ∈
      polytopalJoinCopyAffine i ''
        convexHull ℝ ((C.1 i).1.1 : Set (CoordinateSpace n)) :=
    ⟨x, hx, rfl⟩
  rw [(polytopalJoinCopyAffine i).image_convexHull] at hximage
  apply convexHull_mono (𝕜 := ℝ) _ hximage
  rintro _ ⟨v, hv, rfl⟩
  exact Finset.mem_coe.mpr
    (C.copy_vertex_mem_vertices i (Finset.mem_coe.mp hv))

end PolytopalDeletedCellIndex

/-- The concrete deleted join is the finite union of all Cayley joins of
pairwise disjoint face tuples. -/
def polytopalDeletedJoinCarrier {n : ℕ} (P : FullDimensionalPolytope n) (m : ℕ) :
    Set (PolytopalJoinAmbient n m) :=
  ⋃ C : PolytopalDeletedCellIndex P m, C.carrier

/-- The concrete polytopal deleted join is compact. -/
theorem polytopalDeletedJoinCarrier_compact {n m : ℕ}
    (P : FullDimensionalPolytope n) :
    IsCompact (polytopalDeletedJoinCarrier P m) :=
  isCompact_iUnion fun C : PolytopalDeletedCellIndex P m ↦ C.compact

/-- Every deleted-join witness determines a cell in the finite face model. -/
noncomputable def PolytopeDeletedJoinPoint.cellIndex {n m : ℕ}
    {P : FullDimensionalPolytope n}
    (z : PolytopeDeletedJoinPoint (m := m) P) :
    PolytopalDeletedCellIndex P m := by
  classical
  refine ⟨fun i ↦ PolytopeFaceIndex.ofFace (z.face i) (z.face_isFace i), ?_⟩
  intro i j hij
  simpa only [PolytopeFaceIndex.carrier_ofFace] using
    z.faces_pairwiseDisjoint hij

/-- Every represented deleted-join point realizes into the corresponding
finite Cayley face cell. -/
theorem PolytopeDeletedJoinPoint.realization_mem_cellCarrier {n m : ℕ}
    {P : FullDimensionalPolytope n}
    (z : PolytopeDeletedJoinPoint (m := m) P) :
    z.realization ∈ z.cellIndex.carrier := by
  classical
  have hsum_ne : (∑ i : Fin (m + 1), z.weight i) ≠ 0 := by
    rw [z.weight_sum]
    norm_num
  obtain ⟨i₀, _hi₀, hi₀ne⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  have hi₀pos : 0 < z.weight i₀ :=
    lt_of_le_of_ne (z.weight_nonneg i₀) hi₀ne.symm
  let q₀ : PolytopalJoinAmbient n m :=
    polytopalJoinCopy i₀ (z.point i₀).1
  have hq₀ : q₀ ∈ z.cellIndex.carrier := by
    apply z.cellIndex.copy_mem_carrier i₀
    change (z.point i₀).1 ∈
      (PolytopeFaceIndex.ofFace (z.face i₀) (z.face_isFace i₀)).carrier
    rw [PolytopeFaceIndex.carrier_ofFace]
    exact z.point_mem_face i₀ hi₀pos
  let q : Fin (m + 1) → PolytopalJoinAmbient n m := fun i ↦
    if z.weight i = 0 then q₀ else polytopalJoinCopy i (z.point i).1
  have hq : ∀ i, q i ∈ z.cellIndex.carrier := by
    intro i
    by_cases hi : z.weight i = 0
    · simpa [q, hi] using hq₀
    · rw [show q i = polytopalJoinCopy i (z.point i).1 by simp [q, hi]]
      apply z.cellIndex.copy_mem_carrier i
      change (z.point i).1 ∈
        (PolytopeFaceIndex.ofFace (z.face i) (z.face_isFace i)).carrier
      rw [PolytopeFaceIndex.carrier_ofFace]
      exact z.point_mem_face i
        (lt_of_le_of_ne (z.weight_nonneg i) (fun h ↦ hi h.symm))
  have hmem := z.cellIndex.convex.sum_mem
    (s := z.cellIndex.carrier) (t := Finset.univ) (w := z.weight) (z := q)
    (fun i _hi ↦ z.weight_nonneg i) z.weight_sum
    (fun i _hi ↦ hq i)
  have heq : ∑ i, z.weight i • q i = z.realization := by
    rw [PolytopeDeletedJoinPoint.realization]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hi : z.weight i = 0
    · simp [q, hi]
    · simp [q, hi]
  rwa [heq] at hmem

/-- The witness-level model used in the zero theorem maps into the concrete
compact deleted join. -/
theorem PolytopeDeletedJoinPoint.realization_mem_deletedJoinCarrier {n m : ℕ}
    {P : FullDimensionalPolytope n}
    (z : PolytopeDeletedJoinPoint (m := m) P) :
    z.realization ∈ polytopalDeletedJoinCarrier P m := by
  rw [polytopalDeletedJoinCarrier]
  exact Set.mem_iUnion.mpr ⟨z.cellIndex, z.realization_mem_cellCarrier⟩

/-- The concrete deleted join is a subset of the full polytopal join. -/
theorem polytopalDeletedJoinCarrier_subset_joinCarrier {n m : ℕ}
    (P : FullDimensionalPolytope n) :
    polytopalDeletedJoinCarrier P m ⊆ polytopalJoinCarrier P m := by
  intro z hz
  rw [polytopalDeletedJoinCarrier] at hz
  obtain ⟨C, hzC⟩ := Set.mem_iUnion.mp hz
  apply convexHull_mono (𝕜 := ℝ) _ hzC
  intro v hv
  rw [Finset.mem_coe, PolytopalDeletedCellIndex.vertices,
    Finset.mem_biUnion] at hv
  obtain ⟨i, _hi, hv⟩ := hv
  rw [Finset.mem_image] at hv
  obtain ⟨p, hp, rfl⟩ := hv
  apply Finset.mem_coe.mpr
  apply polytopalJoinCopy_vertex_mem_vertices P i
  exact Finset.mem_powerset.mp (C.1 i).1.2 hp

/-- In particular the concrete deleted join is nonempty. -/
theorem polytopalDeletedJoinCarrier_nonempty {n m : ℕ}
    (P : FullDimensionalPolytope n) :
    (polytopalDeletedJoinCarrier P m).Nonempty := by
  obtain ⟨v, hv⟩ := P.vertices_nonempty
  have hvP : v ∈ P.carrier :=
    subset_convexHull ℝ (P.vertices : Set (CoordinateSpace n))
      (Finset.mem_coe.mpr hv)
  let x : P.carrier := ⟨v, hvP⟩
  let z := PolytopeDeletedJoinPoint.singleFactor P (Fin.last m) x
  exact ⟨z.realization, z.realization_mem_deletedJoinCarrier⟩

/-- The compact topological space underlying the concrete deleted join. -/
abbrev PolytopalDeletedJoinSpace {n : ℕ}
    (P : FullDimensionalPolytope n) (m : ℕ) :=
  {z : PolytopalJoinAmbient n m // z ∈ polytopalDeletedJoinCarrier P m}

noncomputable instance {n m : ℕ} (P : FullDimensionalPolytope n) :
    CompactSpace (PolytopalDeletedJoinSpace P m) :=
  isCompact_iff_compactSpace.mp (polytopalDeletedJoinCarrier_compact P)

/-- The unit sphere in the continuous dual, used to parametrize the
functionals `λ_y`. -/
abbrev DualUnitSphere (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  {y : StrongDual ℝ V // ‖y‖ = 1}

namespace PolytopalJoinMap

variable {n m : ℕ} {P : FullDimensionalPolytope n}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (Φ : PolytopalJoinMap P m V)

/-- Equation `(Y_y-formula)` in the paper, now as a subset of the concrete
finite-dimensional deleted join. -/
def deletedJoinTopLocus (y : StrongDual ℝ V) :
    Set (PolytopalJoinAmbient n m) :=
  polytopalDeletedJoinCarrier P m ∩ (Φ.upperEnvelopeData y).topLocus

theorem mem_deletedJoinTopLocus_iff (y : StrongDual ℝ V)
    (z : PolytopalJoinAmbient n m) :
    z ∈ Φ.deletedJoinTopLocus y ↔
      z ∈ polytopalDeletedJoinCarrier P m ∧
        z ∈ (Φ.upperEnvelopeData y).topLocus :=
  Iff.rfl

/-- Every concrete fiber `Y_y` is compact. -/
theorem deletedJoinTopLocus_compact (y : StrongDual ℝ V) :
    IsCompact (Φ.deletedJoinTopLocus y) :=
  (polytopalDeletedJoinCarrier_compact P).inter_right
    (Φ.upperEnvelopeData_topLocus_compact y).isClosed

/-- The witness-level `Y_y` realization lands in the concrete geometric
fiber. -/
theorem realization_mem_deletedJoinTopLocus
    (y : StrongDual ℝ V) {z : PolytopeDeletedJoinPoint (m := m) P}
    (hz : z ∈ Φ.deletedJoinTopFiber y) :
    z.realization ∈ Φ.deletedJoinTopLocus y :=
  ⟨z.realization_mem_deletedJoinCarrier, hz⟩

/-- Claim `Yy-nonempty` for the actual compact geometric fiber. -/
theorem deletedJoinTopLocus_nonempty (y : StrongDual ℝ V) :
    (Φ.deletedJoinTopLocus y).Nonempty := by
  obtain ⟨z, hz⟩ := Φ.deletedJoinTopFiber_nonempty y
  exact ⟨z.realization, Φ.realization_mem_deletedJoinTopLocus y hz⟩

/-- Concrete form of `Y ⊆ X` at the level of height: `λ_y` is
nonnegative at every point of `Y_y`. -/
theorem height_nonnegative_on_deletedJoinTopLocus
    (y : StrongDual ℝ V) {z : PolytopalJoinAmbient n m}
    (hz : z ∈ Φ.deletedJoinTopLocus y) :
    0 ≤ (Φ.upperEnvelopeData y).height z :=
  Φ.upperEnvelopeData_height_nonnegative_on_topLocus y z hz.2

/-- The global set `Y` from the polytopal proof, prior to proving its
closedness: its points are deleted-join points paired with a unit dual
functional for which they lie on the upper envelope. -/
abbrev TopIncidenceSpace :=
  {p : PolytopalDeletedJoinSpace P m × DualUnitSphere V //
    p.fst.val ∈ (Φ.upperEnvelopeData p.snd.val).topLocus}

/-- Projection `Y → S^{N-1}`. -/
def topIncidenceProjection : Φ.TopIncidenceSpace → DualUnitSphere V :=
  fun p ↦ p.val.snd

theorem continuous_topIncidenceProjection :
    Continuous Φ.topIncidenceProjection := by
  exact continuous_snd.comp continuous_subtype_val

/-- The fiber of the global incidence projection over a dual direction. -/
abbrev TopIncidenceFiber (y : DualUnitSphere V) :=
  {p : Φ.TopIncidenceSpace // Φ.topIncidenceProjection p = y}

/-- The compact geometric fiber `Y_y`, packaged as a topological space. -/
abbrev DeletedJoinTopLocusSpace (y : DualUnitSphere V) :=
  {z : PolytopalJoinAmbient n m // z ∈ Φ.deletedJoinTopLocus y.val}

/-- The abstract projection fiber of `Y → S^{N-1}` is canonically
homeomorphic to the concrete deleted-join top locus `Y_y`. -/
def topIncidenceFiberHomeomorph (y : DualUnitSphere V) :
    Φ.TopIncidenceFiber y ≃ₜ Φ.DeletedJoinTopLocusSpace y where
  toFun p :=
    ⟨p.val.val.fst.val, p.val.val.fst.property, by
      have htop := p.val.property
      have hy : p.val.val.snd = y := p.property
      rw [hy] at htop
      exact htop⟩
  invFun z :=
    ⟨⟨(⟨z.val, z.property.1⟩, y), z.property.2⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · exact p.property.symm
  right_inv z := by
    apply Subtype.ext
    rfl
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop

noncomputable instance deletedJoinTopLocusCompactSpace (y : DualUnitSphere V) :
    CompactSpace (Φ.DeletedJoinTopLocusSpace y) :=
  isCompact_iff_compactSpace.mp (Φ.deletedJoinTopLocus_compact y.val)

noncomputable instance topIncidenceFiberCompactSpace (y : DualUnitSphere V) :
    CompactSpace (Φ.TopIncidenceFiber y) :=
  (Φ.topIncidenceFiberHomeomorph y).symm.compactSpace

/-- Part (I) of polytopal Lemma `Y`, surjectivity of the second projection. -/
theorem topIncidenceProjection_surjective :
    Function.Surjective Φ.topIncidenceProjection := by
  intro y
  obtain ⟨z, hzD, hztop⟩ := Φ.deletedJoinTopLocus_nonempty y.1
  exact ⟨⟨(⟨z, hzD⟩, y), hztop⟩, rfl⟩

end PolytopalJoinMap

end AffineTverberg
