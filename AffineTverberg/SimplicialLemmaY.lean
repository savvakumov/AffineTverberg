import AffineTverberg.SimplicialRidgeJoin
import AffineTverberg.Incidence

set_option linter.style.header false

/-!
# The space `Y` of the simplicial-ball Lemma Y

Fix a boundary ridge `L` of the simplicial ball and a linear map `Φ` on the join
ambient space (in the application, the Sarkaria join map of the paper).  The
space `Y` of `lemma:Y` consists of the pairs `(z, y)` where `z` lies in the
deleted join `L^{*(m+1)}_Δ`, `y` is a unit dual functional, and `y ∘ Φ` is
nonnegative on some cell of `L^{*(m+1)}_Δ` containing `z`.  This is exactly the
incidence space `FaceIncidenceSpace` of `AffineTverberg/Incidence.lean` for the
finite family of cells of `L^{*(m+1)}_Δ`.

This file proves, in the concrete finite-dimensional model:

* `RidgeIncidenceSpace` is compact and its projection to the unit dual sphere is
  continuous;
* the inclusion `Y → X` into the incidence space of the full deleted join of the
  boundary of `K`, which exists because every cell of `L^{*(m+1)}_Δ` is a cell of
  the full deleted join;
* the projection `Y → S^{N-1}` is surjective (using the diagonal relation, which
  supplies an allowed colour for every vertex of `L`);
* the fiber over `y` is canonically homeomorphic to the compact geometric fiber
  `ridgeNonnegLocus`, the union of the cells on which `y ∘ Φ` is nonnegative,
  which is the join of the allowed colour sets `W_v(y)`;
* the strongest connectivity statement available here: every such fiber is path
  connected as soon as the ridge has at least two vertices.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg

section IncidenceSpace

variable {e m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The space `Y` of the simplicial-ball Lemma Y: incidences between the deleted
join of the ridge `L` and unit functionals which are nonnegative on a cell
containing the point. -/
abbrev RidgeIncidenceSpace (L : Finset (CoordinateSpace e))
    (Φ : PolytopalJoinAmbient e m →L[ℝ] E) :=
  FaceIncidenceSpace (ridgeDeletedJoinCarrier L m)
    (fun F : RidgeDeletedCellIndex L m ↦ F.carrier) (fun z ↦ Φ z)

variable (L : Finset (CoordinateSpace e)) (Φ : PolytopalJoinAmbient e m →L[ℝ] E)

/-- Claim (2) of Lemma Y: `Y` is compact in the concrete finite-dimensional
model. -/
instance ridgeIncidenceSpace_compactSpace [FiniteDimensional ℝ E] :
    CompactSpace (RidgeIncidenceSpace L Φ) :=
  faceIncidenceSpace_compactSpace (ridgeDeletedJoinCarrier_compact L)
    fun F ↦ F.carrier_isClosed

/-- The second projection `Y → S^{N-1}`. -/
def ridgeIncidenceDualProjection : RidgeIncidenceSpace L Φ → DualUnitSphere E :=
  fun p ↦ ⟨p.1.2, p.2.1⟩

/-- Claim (2) of Lemma Y: the second projection is continuous. -/
theorem continuous_ridgeIncidenceDualProjection :
    Continuous (ridgeIncidenceDualProjection L Φ) := by
  apply Continuous.subtype_mk
  exact continuous_snd.comp continuous_subtype_val

end IncidenceSpace

section ToFullIncidence

variable {e n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)} {L : Finset (CoordinateSpace e)}

/-- The finite index type of the cells of the deleted join of the boundary of
`K`. -/
abbrev BoundaryDeletedCellIndex (n : ℕ) (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))
    (m : ℕ) :=
  {f : Fin (m + 1) → Finset (CoordinateSpace e) // IsBoundaryDeletedJoinCell n K f}

/-- The incidence space `X` over the full deleted join of the boundary of `K`. -/
abbrev FullIncidenceSpace (n : ℕ) (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))
    (m : ℕ) (Φ : PolytopalJoinAmbient e m →L[ℝ] E) :=
  FaceIncidenceSpace (simplicialDeletedJoinCarrier n K m)
    (fun F : BoundaryDeletedCellIndex n K m ↦ joinCellCarrier F.1) (fun z ↦ Φ z)

variable (Φ : PolytopalJoinAmbient e m →L[ℝ] E)

/-- Claim (1) of Lemma Y: since every cell of `L^{*(m+1)}_Δ` is a cell of the
full deleted join, the incidence space `Y` maps to the incidence space `X`. -/
def ridgeToFullIncidence (hL : IsBoundaryRidge n K L) :
    RidgeIncidenceSpace L Φ → FullIncidenceSpace n K m Φ :=
  fun p ↦ ⟨(⟨p.1.1.1, ridgeDeletedJoinCarrier_subset hL p.1.1.2⟩, p.1.2),
    p.2.1, by
      obtain ⟨F, hzF, hnonneg⟩ := p.2.2
      exact ⟨⟨F.faces, isBoundaryDeletedJoinCell_of_ridgeCell hL F⟩, hzF, hnonneg⟩⟩

theorem continuous_ridgeToFullIncidence (hL : IsBoundaryRidge n K L) :
    Continuous (ridgeToFullIncidence Φ hL) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · exact Continuous.subtype_mk
      (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)) _
  · exact continuous_snd.comp continuous_subtype_val

/-- The map `Y → X` is compatible with the projections to the unit dual
sphere. -/
theorem ridgeToFullIncidence_snd (hL : IsBoundaryRidge n K L)
    (p : RidgeIncidenceSpace L Φ) :
    (ridgeToFullIncidence Φ hL p).1.2 = (ridgeIncidenceDualProjection L Φ p).1 :=
  rfl

end ToFullIncidence

section Fiber

variable {e m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (L : Finset (CoordinateSpace e)) (Φ : PolytopalJoinAmbient e m →L[ℝ] E)

/-- The geometric fiber of `Y → S^{N-1}` over `y`: the union of the cells of
`L^{*(m+1)}_Δ` on which `y ∘ Φ` is nonnegative. -/
def ridgeNonnegLocus (y : StrongDual ℝ E) : Set (PolytopalJoinAmbient e m) :=
  {z | ∃ F : RidgeDeletedCellIndex L m, z ∈ F.carrier ∧ ∀ w ∈ F.carrier, 0 ≤ y (Φ w)}

theorem ridgeNonnegLocus_subset (y : StrongDual ℝ E) :
    ridgeNonnegLocus L Φ y ⊆ ridgeDeletedJoinCarrier L m := by
  rintro z ⟨F, hzF, -⟩
  exact carrier_subset_ridgeDeletedJoinCarrier F hzF

theorem cell_carrier_subset_ridgeNonnegLocus {y : StrongDual ℝ E}
    {F : RidgeDeletedCellIndex L m} (hF : ∀ w ∈ F.carrier, 0 ≤ y (Φ w)) :
    F.carrier ⊆ ridgeNonnegLocus L Φ y :=
  fun _z hz ↦ ⟨F, hz, hF⟩

/-- The geometric fiber is a finite union of compact cells, hence compact. -/
theorem ridgeNonnegLocus_compact (y : StrongDual ℝ E) :
    IsCompact (ridgeNonnegLocus L Φ y) := by
  classical
  have hrw : ridgeNonnegLocus L Φ y =
      ⋃ F ∈ {F : RidgeDeletedCellIndex L m | ∀ w ∈ F.carrier, 0 ≤ y (Φ w)}, F.carrier := by
    ext z
    simp only [ridgeNonnegLocus, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    exact ⟨fun ⟨F, hz, hF⟩ ↦ ⟨F, hF, hz⟩, fun ⟨F, hF, hz⟩ ↦ ⟨F, hz, hF⟩⟩
  rw [hrw]
  exact Set.Finite.isCompact_biUnion (Set.toFinite _) fun F _hF ↦ F.carrier_compact

/-- The fiber of the second projection of `Y` over a unit functional. -/
abbrev RidgeIncidenceFiber (y : DualUnitSphere E) :=
  {p : RidgeIncidenceSpace L Φ // ridgeIncidenceDualProjection L Φ p = y}

/-- The abstract fiber of `Y → S^{N-1}` is canonically homeomorphic to the
concrete geometric fiber. -/
def ridgeIncidenceFiberHomeomorph (y : DualUnitSphere E) :
    RidgeIncidenceFiber L Φ y ≃ₜ
      {z : PolytopalJoinAmbient e m // z ∈ ridgeNonnegLocus L Φ y.1} where
  toFun p :=
    ⟨p.1.1.1.1, by
      obtain ⟨F, hzF, hnonneg⟩ := p.1.2.2
      have hy : p.1.1.2 = y.1 := congrArg Subtype.val p.2
      exact ⟨F, hzF, by rw [← hy]; exact hnonneg⟩⟩
  invFun z :=
    ⟨⟨(⟨z.1, ridgeNonnegLocus_subset L Φ y.1 z.2⟩, y.1), y.2, by
        obtain ⟨F, hzF, hnonneg⟩ := z.2
        exact ⟨F, hzF, hnonneg⟩⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · exact (congrArg Subtype.val p.2).symm
  right_inv z := by
    apply Subtype.ext
    rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end Fiber

section GeometricFiberCombinatorics

variable {e m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (L : Finset (CoordinateSpace e)) (Φ : PolytopalJoinAmbient e m →L[ℝ] E)

/-- The geometric fiber over `y` is exactly the union of the cells whose
component vertex sets carry only allowed colours: the geometric realization of
the join `W_{v₁}(y) * ⋯ * W_{v_N}(y)` of the allowed colour sets. -/
theorem mem_ridgeNonnegLocus_iff (y : StrongDual ℝ E) (z : PolytopalJoinAmbient e m) :
    z ∈ ridgeNonnegLocus L Φ y ↔
      ∃ f : NonnegRidgeCell L (ridgeEval Φ y), z ∈ joinCellCarrier f.1 := by
  constructor
  · rintro ⟨F, hzF, hnonneg⟩
    exact ⟨⟨F.faces, F.faces_subset, F.faces_pairwiseDisjoint,
      (nonneg_on_ridgeCell_iff y Φ F).mp hnonneg⟩, hzF⟩
  · rintro ⟨⟨f, hsub, hdisj, hnn⟩, hzf⟩
    refine ⟨⟨fun i ↦ ⟨f i, Finset.mem_powerset.mpr (hsub i)⟩, hdisj⟩, hzf, ?_⟩
    exact (nonneg_on_joinCellCarrier_iff y Φ f).mpr hnn

/-- Restated through the identification of nonnegative cells with the faces of
the join complex of the allowed colour sets. -/
theorem mem_ridgeNonnegLocus_iff_colorChoiceFace (y : StrongDual ℝ E)
    (z : PolytopalJoinAmbient e m) :
    z ∈ ridgeNonnegLocus L Φ y ↔
      ∃ s : ColorChoiceFace L (ridgeEval Φ y),
        z ∈ joinCellCarrier (cellOfColorFace s.1) := by
  rw [mem_ridgeNonnegLocus_iff]
  constructor
  · rintro ⟨f, hzf⟩
    refine ⟨nonnegRidgeCellEquivColorChoiceFace L (ridgeEval Φ y) f, ?_⟩
    have := congrArg Subtype.val
      ((nonnegRidgeCellEquivColorChoiceFace L (ridgeEval Φ y)).left_inv f)
    rw [show cellOfColorFace (nonnegRidgeCellEquivColorChoiceFace L (ridgeEval Φ y) f).1 =
      f.1 from this]
    exact hzf
  · rintro ⟨s, hzs⟩
    exact ⟨(nonnegRidgeCellEquivColorChoiceFace L (ridgeEval Φ y)).symm s, hzs⟩

end GeometricFiberCombinatorics

section Surjectivity

variable {e m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (L : Finset (CoordinateSpace e)) (Φ : PolytopalJoinAmbient e m →L[ℝ] E)

/-- The cell supported on a single coloured vertex is nonnegative for `y` as
soon as that colour is allowed. -/
theorem singleVertexCell_nonneg {y : StrongDual ℝ E} {v : CoordinateSpace e}
    (hv : v ∈ L) {i : Fin (m + 1)} (hi : 0 ≤ y (Φ (polytopalJoinCopy i v))) :
    ∀ w ∈ (colorRidgeCell (m := m) {v} (Finset.singleton_subset_iff.mpr hv)
      (fun _ ↦ i)).carrier, 0 ≤ y (Φ w) := by
  classical
  rw [nonneg_on_ridgeCell_iff]
  intro k u hu
  rw [colorRidgeCell_faces, mem_colorCell] at hu
  obtain ⟨huv, hki⟩ := hu
  rw [Finset.mem_singleton] at huv
  subst huv
  subst hki
  exact hi

theorem copy_mem_ridgeNonnegLocus {y : StrongDual ℝ E} {v : CoordinateSpace e}
    (hv : v ∈ L) {i : Fin (m + 1)} (hi : 0 ≤ y (Φ (polytopalJoinCopy i v))) :
    polytopalJoinCopy i v ∈ ridgeNonnegLocus L Φ y := by
  classical
  refine ⟨colorRidgeCell {v} (Finset.singleton_subset_iff.mpr hv) (fun _ ↦ i), ?_,
    singleVertexCell_nonneg L Φ hv hi⟩
  exact copy_mem_colorRidgeCell_carrier _ _ (Finset.mem_singleton_self v)

/-- The geometric fiber is nonempty for every functional, by the diagonal
relation. -/
theorem ridgeNonnegLocus_nonempty
    (hdiag : ∀ x : CoordinateSpace e, ∑ i : Fin (m + 1), Φ (polytopalJoinCopy i x) = 0)
    (y : StrongDual ℝ E) (hL : L.Nonempty) :
    (ridgeNonnegLocus L Φ y).Nonempty := by
  obtain ⟨v, hv⟩ := hL
  exact ⟨_, copy_mem_ridgeNonnegLocus L Φ hv (chosenAllowedColor_nonneg hdiag y v)⟩

/-- Claim (6) of Lemma Y: the second projection `Y → S^{N-1}` is surjective. -/
theorem ridgeIncidenceDualProjection_surjective
    (hdiag : ∀ x : CoordinateSpace e, ∑ i : Fin (m + 1), Φ (polytopalJoinCopy i x) = 0)
    (hL : L.Nonempty) :
    Function.Surjective (ridgeIncidenceDualProjection L Φ) := by
  intro y
  obtain ⟨z, hz⟩ := ridgeNonnegLocus_nonempty L Φ hdiag y.1 hL
  obtain ⟨F, hzF, hnonneg⟩ := hz
  exact ⟨⟨(⟨z, carrier_subset_ridgeDeletedJoinCarrier F hzF⟩, y.1), y.2, F, hzF, hnonneg⟩,
    Subtype.ext rfl⟩

end Surjectivity

section FullCells

variable {e m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (L : Finset (CoordinateSpace e)) (Φ : PolytopalJoinAmbient e m →L[ℝ] E)

/-- A colouring of all of `L` by allowed colours gives a nonnegative cell. -/
theorem fullColorCell_nonneg {y : StrongDual ℝ E} {c : CoordinateSpace e → Fin (m + 1)}
    (hc : ∀ v ∈ L, 0 ≤ y (Φ (polytopalJoinCopy (c v) v))) :
    ∀ w ∈ joinCellCarrier (colorCell L c), 0 ≤ y (Φ w) := by
  rw [nonneg_on_joinCellCarrier_iff]
  intro i v hv
  obtain ⟨hvL, hvi⟩ := mem_colorCell.mp hv
  rw [← hvi]
  exact hc v hvL

/-- Geometric purity of the fiber: every point of the fiber lies in a cell in
which *every* vertex of the ridge carries an allowed colour.  This is the
geometric counterpart of the maximality statements of
`AffineTverberg/SimplicialFiber.lean`. -/
theorem exists_fullColoring_of_mem_ridgeNonnegLocus
    (hdiag : ∀ x : CoordinateSpace e, ∑ i : Fin (m + 1), Φ (polytopalJoinCopy i x) = 0)
    (y : StrongDual ℝ E) {z : PolytopalJoinAmbient e m}
    (hz : z ∈ ridgeNonnegLocus L Φ y) :
    ∃ c : CoordinateSpace e → Fin (m + 1),
      (∀ v ∈ L, 0 ≤ y (Φ (polytopalJoinCopy (c v) v))) ∧
        z ∈ joinCellCarrier (colorCell L c) := by
  classical
  obtain ⟨F, hzF, hnonneg⟩ := hz
  set c : CoordinateSpace e → Fin (m + 1) := fun v ↦
    if h : ∃ i, v ∈ F.faces i then h.choose else chosenAllowedColor hdiag y v with hcdef
  have hcmem : ∀ i, ∀ v ∈ F.faces i, c v = i := by
    intro i v hv
    have h : ∃ j, v ∈ F.faces j := ⟨i, hv⟩
    have hchoose : v ∈ F.faces h.choose := h.choose_spec
    have hji : h.choose = i := by
      by_contra hne
      exact (Finset.disjoint_left.mp (F.faces_pairwiseDisjoint hne) hchoose) hv
    rw [hcdef]
    simp only [dite_eq_left h]
    exact hji
  refine ⟨c, ?_, joinCellCarrier_mono (fun i v hv ↦
    mem_colorCell.mpr ⟨F.faces_subset i hv, hcmem i v hv⟩) hzF⟩
  intro v hv
  by_cases h : ∃ i, v ∈ F.faces i
  · obtain ⟨i, hi⟩ := h
    rw [hcmem i v hi]
    exact (nonneg_on_ridgeCell_iff y Φ F).mp hnonneg i v hi
  · have hcv : c v = chosenAllowedColor hdiag y v := by
      rw [hcdef]
      simp only [dite_eq_right h]
    rw [hcv]
    exact chosenAllowedColor_nonneg hdiag y v

/-- The fiber is exactly the union of the cells given by colourings of the whole
ridge by allowed colours — the geometric join of the sets `W_v(y)`. -/
theorem ridgeNonnegLocus_eq_iUnion_fullColorCells
    (hdiag : ∀ x : CoordinateSpace e, ∑ i : Fin (m + 1), Φ (polytopalJoinCopy i x) = 0)
    (y : StrongDual ℝ E) :
    ridgeNonnegLocus L Φ y =
      ⋃ c ∈ {c : CoordinateSpace e → Fin (m + 1) |
          ∀ v ∈ L, 0 ≤ y (Φ (polytopalJoinCopy (c v) v))},
        joinCellCarrier (colorCell L c) := by
  ext z
  constructor
  · intro hz
    obtain ⟨c, hc, hzc⟩ := exists_fullColoring_of_mem_ridgeNonnegLocus L Φ hdiag y hz
    exact Set.mem_biUnion hc hzc
  · intro hz
    obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.mp hz
    refine ⟨colorRidgeCell L (Finset.Subset.refl L) c, hzc, ?_⟩
    exact fullColorCell_nonneg L Φ hc

end FullCells

section Connectivity

variable {e m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (L : Finset (CoordinateSpace e)) (Φ : PolytopalJoinAmbient e m →L[ℝ] E)

/-- Two points of one nonnegative cell are joined inside the geometric fiber. -/
theorem joinedIn_of_mem_cell {y : StrongDual ℝ E} {F : RidgeDeletedCellIndex L m}
    (hF : ∀ w ∈ F.carrier, 0 ≤ y (Φ w)) {z w : PolytopalJoinAmbient e m}
    (hz : z ∈ F.carrier) (hw : w ∈ F.carrier) :
    JoinedIn (ridgeNonnegLocus L Φ y) z w :=
  ((F.carrier_convex.isPathConnected ⟨z, hz⟩).joinedIn z hz w hw).mono
    (cell_carrier_subset_ridgeNonnegLocus L Φ hF)

/-- The two-vertex cell carrying two differently coloured vertices is
nonnegative when both colours are allowed. -/
theorem joinedIn_copy_copy {y : StrongDual ℝ E} {u w : CoordinateSpace e}
    (hu : u ∈ L) (hw : w ∈ L) (huw : u ≠ w) {i j : Fin (m + 1)}
    (hi : 0 ≤ y (Φ (polytopalJoinCopy i u))) (hj : 0 ≤ y (Φ (polytopalJoinCopy j w))) :
    JoinedIn (ridgeNonnegLocus L Φ y) (polytopalJoinCopy i u) (polytopalJoinCopy j w) := by
  classical
  set c : CoordinateSpace e → Fin (m + 1) := fun x ↦ if x = u then i else j with hcdef
  have hS : ({u, w} : Finset (CoordinateSpace e)) ⊆ L := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hu
    · rw [Finset.mem_singleton] at hx
      subst hx
      exact hw
  set F : RidgeDeletedCellIndex L m := colorRidgeCell {u, w} hS c with hFdef
  have hcu : c u = i := by simp [hcdef]
  have hcw : c w = j := by simp [hcdef, huw.symm]
  have hnonneg : ∀ q ∈ F.carrier, 0 ≤ y (Φ q) := by
    rw [hFdef, nonneg_on_ridgeCell_iff]
    intro k x hx
    rw [colorRidgeCell_faces, mem_colorCell] at hx
    obtain ⟨hxS, hxk⟩ := hx
    rcases Finset.mem_insert.mp hxS with rfl | hxw
    · rw [← hxk, hcu]; exact hi
    · rw [Finset.mem_singleton] at hxw
      subst hxw
      rw [← hxk, hcw]; exact hj
  have hmemu : polytopalJoinCopy i u ∈ F.carrier := by
    have := copy_mem_colorRidgeCell_carrier (L := L) hS c
      (Finset.mem_insert_self u {w})
    rwa [hcu] at this
  have hmemw : polytopalJoinCopy j w ∈ F.carrier := by
    have := copy_mem_colorRidgeCell_carrier (L := L) hS c
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self w))
    rwa [hcw] at this
  exact joinedIn_of_mem_cell L Φ hnonneg hmemu hmemw

/-- Two allowed colours of the same vertex are joined through any other vertex
of the ridge. -/
theorem joinedIn_copy_copy_same_vertex {y : StrongDual ℝ E} {u w : CoordinateSpace e}
    (hu : u ∈ L) (hw : w ∈ L) (huw : u ≠ w) {i i' j : Fin (m + 1)}
    (hi : 0 ≤ y (Φ (polytopalJoinCopy i u))) (hi' : 0 ≤ y (Φ (polytopalJoinCopy i' u)))
    (hj : 0 ≤ y (Φ (polytopalJoinCopy j w))) :
    JoinedIn (ridgeNonnegLocus L Φ y) (polytopalJoinCopy i u) (polytopalJoinCopy i' u) :=
  (joinedIn_copy_copy L Φ hu hw huw hi hj).trans
    ((joinedIn_copy_copy L Φ hu hw huw hi' hj).symm)

/-- Every point of the geometric fiber is joined to the copy of a vertex. -/
theorem exists_joinedIn_copy {y : StrongDual ℝ E} {z : PolytopalJoinAmbient e m}
    (hz : z ∈ ridgeNonnegLocus L Φ y) :
    ∃ v ∈ L, ∃ i : Fin (m + 1), 0 ≤ y (Φ (polytopalJoinCopy i v)) ∧
      JoinedIn (ridgeNonnegLocus L Φ y) z (polytopalJoinCopy i v) := by
  obtain ⟨F, hzF, hnonneg⟩ := hz
  have hne : ∃ i, (F.faces i).Nonempty := by
    by_contra h
    push Not at h
    rw [RidgeDeletedCellIndex.carrier, joinCellCarrier_eq_empty h] at hzF
    exact hzF
  obtain ⟨i, v, hv⟩ := hne
  refine ⟨v, F.faces_subset i hv, i, ?_, ?_⟩
  · exact (nonneg_on_ridgeCell_iff y Φ F |>.mp hnonneg) i v hv
  · exact joinedIn_of_mem_cell L Φ hnonneg hzF (copy_mem_joinCellCarrier i hv)

/-- The strongest connectivity statement available in the concrete model: the
geometric fiber over any functional — the join of the allowed colour sets
`W_v(y)` — is path connected as soon as the ridge has at least two vertices. -/
theorem isPathConnected_ridgeNonnegLocus
    (hdiag : ∀ x : CoordinateSpace e, ∑ i : Fin (m + 1), Φ (polytopalJoinCopy i x) = 0)
    (y : StrongDual ℝ E) (hcard : 2 ≤ L.card) :
    IsPathConnected (ridgeNonnegLocus L Φ y) := by
  classical
  obtain ⟨v₁, hv₁, v₂, hv₂, hne⟩ := Finset.one_lt_card.mp hcard
  set i₁ : Fin (m + 1) := chosenAllowedColor hdiag y v₁ with hi₁def
  have hi₁ : 0 ≤ y (Φ (polytopalJoinCopy i₁ v₁)) := chosenAllowedColor_nonneg hdiag y v₁
  set i₂ : Fin (m + 1) := chosenAllowedColor hdiag y v₂ with hi₂def
  have hi₂ : 0 ≤ y (Φ (polytopalJoinCopy i₂ v₂)) := chosenAllowedColor_nonneg hdiag y v₂
  refine ⟨polytopalJoinCopy i₁ v₁, copy_mem_ridgeNonnegLocus L Φ hv₁ hi₁, ?_⟩
  intro z hz
  obtain ⟨v, hv, i, hi, hjoin⟩ := exists_joinedIn_copy L Φ hz
  refine (hjoin.trans ?_).symm
  by_cases hvv₁ : v = v₁
  · subst hvv₁
    exact joinedIn_copy_copy_same_vertex L Φ hv hv₂ hne hi hi₁ hi₂
  · exact joinedIn_copy_copy L Φ hv hv₁ hvv₁ hi hi₁

/-- Consequently the fiber is connected. -/
theorem isConnected_ridgeNonnegLocus
    (hdiag : ∀ x : CoordinateSpace e, ∑ i : Fin (m + 1), Φ (polytopalJoinCopy i x) = 0)
    (y : StrongDual ℝ E) (hcard : 2 ≤ L.card) :
    IsConnected (ridgeNonnegLocus L Φ y) :=
  (isPathConnected_ridgeNonnegLocus L Φ hdiag y hcard).isConnected

/-- The abstract fiber of `Y → S^{N-1}` is a path-connected space. -/
theorem pathConnectedSpace_ridgeIncidenceFiber
    (hdiag : ∀ x : CoordinateSpace e, ∑ i : Fin (m + 1), Φ (polytopalJoinCopy i x) = 0)
    (y : DualUnitSphere E) (hcard : 2 ≤ L.card) :
    PathConnectedSpace (RidgeIncidenceFiber L Φ y) := by
  have h := isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_ridgeNonnegLocus L Φ hdiag y.1 hcard)
  exact (ridgeIncidenceFiberHomeomorph L Φ y).symm.pathConnectedSpace

end Connectivity

section SarkariaInstance

variable {e d m : ℕ}

/-- The diagonal relation for the concrete simplicial Sarkaria join map, in the
form required by Lemma Y. -/
theorem sum_simplicialSarkariaMap_copy_eq_zero
    (ψ : CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d) (x : CoordinateSpace e) :
    ∑ i : Fin (m + 1), simplicialSarkariaMap (fun _ ↦ ψ) (polytopalJoinCopy i x) = 0 :=
  sum_simplicialSarkariaLinear_copy ψ x

/-- Lemma Y for the concrete Sarkaria map of a ridge: the projection to the unit
dual sphere is surjective and all of its fibers are path connected. -/
theorem ridgeIncidence_sarkaria_surjective_and_fibers_pathConnected
    (L : Finset (CoordinateSpace e)) (ψ : CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d)
    (hcard : 2 ≤ L.card) :
    Function.Surjective
        (ridgeIncidenceDualProjection L (simplicialSarkariaMap (m := m) (fun _ ↦ ψ))) ∧
      ∀ y : DualUnitSphere (SarkariaTarget d m),
        PathConnectedSpace
          (RidgeIncidenceFiber L (simplicialSarkariaMap (m := m) (fun _ ↦ ψ)) y) := by
  have hL : L.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨ridgeIncidenceDualProjection_surjective L _
      (sum_simplicialSarkariaMap_copy_eq_zero ψ) hL, fun y ↦ ?_⟩
  exact pathConnectedSpace_ridgeIncidenceFiber L _ (sum_simplicialSarkariaMap_copy_eq_zero ψ)
    y hcard

end SarkariaInstance

section ZeroOnRidge

variable {e n d m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
  {L : Finset (CoordinateSpace e)}

/-- A zero of the concrete Sarkaria join map at a point of the deleted join of a
boundary ridge produces a represented deleted-join point of `DeletedJoin.lean`
with vanishing Sarkaria value. -/
theorem exists_sarkariaValue_eq_zero_of_mem_ridgeDeletedJoinCarrier
    (hL : IsBoundaryRidge n K L) {φ : K.space → CoordinateSpace d}
    {ψ : CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d}
    (hψ : ∀ x : K.space, x.1 ∈ convexHull ℝ (L : Set (CoordinateSpace e)) → φ x = ψ x.1)
    {z : PolytopalJoinAmbient e m} (hz : z ∈ ridgeDeletedJoinCarrier L m)
    (hzero : simplicialSarkariaMap (fun _ ↦ ψ) z = 0) :
    ∃ w : SimplicialDeletedJoinPoint (n := n) (m := m) K,
      SimplicialDeletedJoinPoint.sarkariaValue K w φ = 0 := by
  obtain ⟨F, hzF⟩ := Set.mem_iUnion.mp hz
  refine exists_sarkariaValue_eq_zero_of_simplicialSarkariaLinear_eq_zero
    (isBoundaryDeletedJoinCell_of_ridgeCell hL F) (fun i x hx ↦ ?_) hzF hzero
  exact hψ x (convexHull_mono (by exact_mod_cast F.faces_subset i) hx)

/-- The chosen ambient affine representative of `φ` on the ridge always
exists. -/
theorem exists_ridge_affine_extension {φ : K.space → CoordinateSpace d}
    (hφ : IsAffineOnSimplicialFaces K φ) (hL : IsBoundaryRidge n K L) :
    ∃ ψ : CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d,
      ∀ x : K.space, x.1 ∈ convexHull ℝ (L : Set (CoordinateSpace e)) → φ x = ψ x.1 :=
  hφ L hL.1

end ZeroOnRidge

end AffineTverberg

