import AffineTverberg.PolytopalCellStructure
import AffineTverberg.PolytopalTopIncidence

set_option linter.style.header false

/-!
# The face incidence space `X` of the polytopal deleted join

This file replaces the auxiliary family of convex hulls of arbitrary subsets
of Cayley vertices by the actual cell family of the deleted join: the finite
family `C.carrier`, `C : PolytopalDeletedCellIndex P m`, of Cayley joins of
tuples of pairwise disjoint exposed faces of `P`.  The incidence space is

`X = {(z, y) ∈ D × S(V*) | ∃ a deleted cell G ∋ z with y ∘ Φ ≥ 0 on G}`.

The two main results are:

* `PolytopalJoinMap.exists_cell_carrier_eq_inter_contactSet`: the
  intersection of a deleted-join cell with an upper-support contact face of
  the join polytope is again a deleted-join cell.
* `PolytopalJoinMap.exists_deletedCell_nonneg_of_mem_topLocus`: every point
  of `Y` lies in a deleted-join cell on which the `y`-height is nonnegative.
  The geometry is the one of the paper: pick a deleted cell `C` containing
  `z`, pick the upper-support contact face `F` of the join polytope `Q`
  containing `z`; `F` is exactly the set of points of `Q` on which the
  exposing functional is tight, so `C ∩ F` is the convex hull of the tight
  Cayley vertices of `C`, and it decomposes factorwise into the exposed
  subfaces `F i ∩ {ℓ_i = max}` of the component faces of `C`, which are
  again pairwise disjoint.  Hence `C ∩ F` is another deleted cell, it
  contains `z`, and the height is nonnegative on it.  This produces the
  continuous inclusion `Y → X` commuting with both projections.
* `PolytopalJoinMap.cellIncidenceFiberData`: assuming `Φ.joinMap` avoids
  zero on `D`, each fiber of the first projection `X → D` is contractible,
  via the minimal deleted cell through a point provided by
  `PolytopalCellStructure.lean`.  This is the geometric input for the
  Leray--Vietoris--Begle step.
-/

noncomputable section

open Set

namespace AffineTverberg

/-! ## Two elementary convexity lemmas -/

section Elementary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The level set of an affine functional at its maximum is an exposed face. -/
theorem isExposed_of_affine_eq_max {A : Set E} (g : E →L[ℝ] ℝ) (k c : ℝ)
    (hle : ∀ v ∈ A, g v + k ≤ c) :
    IsExposed ℝ A {v | v ∈ A ∧ g v + k = c} := by
  rintro ⟨w, hwA, hwc⟩
  refine ⟨g, ?_⟩
  ext v
  constructor
  · rintro ⟨hv, hveq⟩
    refine ⟨hv, fun u hu ↦ ?_⟩
    have := hle u hu
    linarith
  · rintro ⟨hv, hmax⟩
    refine ⟨hv, le_antisymm (hle v hv) ?_⟩
    have := hmax w hwA
    linarith

/-- **Tight vertices.**  If a linear functional is bounded by `c` on a finite
set and takes the value `c` at a convex combination of that set, the
combination only involves points at which the functional equals `c`. -/
theorem mem_convexHull_filter_of_eq_max (S : Finset E) (l : E →L[ℝ] ℝ) (c : ℝ)
    (hle : ∀ v ∈ S, l v ≤ c) {w : E} (hw : w ∈ convexHull ℝ (S : Set E))
    (hwc : l w = c) :
    w ∈ convexHull ℝ ((S.filter fun v ↦ l v = c : Finset E) : Set E) := by
  classical
  rw [Finset.convexHull_eq] at hw
  obtain ⟨lam, hlam0, hlam1, hlamw⟩ := hw
  rw [Finset.centerMass_eq_of_sum_1 S id hlam1] at hlamw
  have hwsum : ∑ v ∈ S, lam v • v = w := hlamw
  have hlsum : ∑ v ∈ S, lam v * l v = c := by
    rw [← hwc, ← hwsum, map_sum]
    exact Finset.sum_congr rfl fun v _ ↦ by rw [map_smul, smul_eq_mul]
  have hgap : ∑ v ∈ S, lam v * (c - l v) = 0 := by
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hlam1, hlsum, one_mul,
      sub_self]
  have hterm : ∀ v ∈ S, lam v * (c - l v) = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).1 hgap
    intro v hv
    exact mul_nonneg (hlam0 v hv) (by linarith [hle v hv])
  have hzero : ∀ v ∈ S, l v ≠ c → lam v = 0 := by
    intro v hv hne
    rcases mul_eq_zero.1 (hterm v hv) with h | h
    · exact h
    · exact absurd (by linarith : l v = c) hne
  set T : Finset E := S.filter fun v ↦ l v = c with hT
  have hTS : T ⊆ S := Finset.filter_subset _ _
  have hsumT : ∑ v ∈ T, lam v = 1 := by
    rw [← hlam1]
    refine Finset.sum_subset hTS ?_
    intro v hv hvT
    exact hzero v hv fun hlv ↦ hvT (Finset.mem_filter.2 ⟨hv, hlv⟩)
  have hwT : ∑ v ∈ T, lam v • v = w := by
    rw [← hwsum]
    refine Finset.sum_subset hTS ?_
    intro v hv hvT
    rw [hzero v hv fun hlv ↦ hvT (Finset.mem_filter.2 ⟨hv, hlv⟩), zero_smul]
  have hmem := T.centerMass_mem_convexHull (fun v hv ↦ hlam0 v (hTS hv))
    (by rw [hsumT]; norm_num) (fun v hv ↦ Finset.mem_coe.2 hv)
  rwa [Finset.centerMass_eq_of_sum_1 T (fun v ↦ v) hsumT, hwT] at hmem

end Elementary

/-! ## Cells as candidate Cayley-vertex subsets -/

section CellFaces

variable {n m : ℕ} {P : FullDimensionalPolytope n}

theorem PolytopalDeletedCellIndex.vertices_subset
    (C : PolytopalDeletedCellIndex P m) :
    C.vertices ⊆ polytopalJoinVertices P m := by
  classical
  intro s hs
  rw [PolytopalDeletedCellIndex.vertices, Finset.mem_biUnion] at hs
  obtain ⟨i, _hi, hs⟩ := hs
  rw [Finset.mem_image] at hs
  obtain ⟨v, hv, rfl⟩ := hs
  exact polytopalJoinCopy_vertex_mem_vertices P i
    (Finset.mem_powerset.mp (C.1 i).1.2 hv)

/-- A cell of the deleted join is in particular one of the candidate hulls of
subsets of Cayley vertices. -/
def PolytopalDeletedCellIndex.toJoinFaceIndex
    (C : PolytopalDeletedCellIndex P m) : PolytopalJoinFaceIndex P m :=
  ⟨C.vertices, Finset.mem_powerset.2 C.vertices_subset⟩

@[simp]
theorem PolytopalDeletedCellIndex.polytopalJoinFaceCarrier_toJoinFaceIndex
    (C : PolytopalDeletedCellIndex P m) :
    polytopalJoinFaceCarrier C.toJoinFaceIndex = C.carrier :=
  rfl

end CellFaces

/-! ## The incidence space of the actual cell family -/

namespace PolytopalJoinMap

variable {n m : ℕ} {P : FullDimensionalPolytope n}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (Φ : PolytopalJoinMap P m V)

/-- The `i`-th factor of the exposing functional of an upper support, as a
continuous linear functional on the coordinate space. -/
def factorFunctional (l : StrongDual ℝ (PolytopalJoinAmbient n m))
    (i : Fin (m + 1)) : StrongDual ℝ (CoordinateSpace n) :=
  l.comp (polytopalJoinCopyLinear i).toContinuousLinearMap

theorem apply_polytopalJoinCopy (l : StrongDual ℝ (PolytopalJoinAmbient n m))
    (i : Fin (m + 1)) (v : CoordinateSpace n) :
    l (polytopalJoinCopy i v) =
      factorFunctional l i v + l (polytopalJoinCopy (m := m) i 0) := by
  have hsplit : polytopalJoinCopy (m := m) i v
      = polytopalJoinCopyLinear i v + polytopalJoinCopy (m := m) i 0 := by
    funext j
    by_cases hji : j = i
    · subst hji
      simp [polytopalJoinCopy, polytopalJoinCopyLinear]
    · simp [polytopalJoinCopy, polytopalJoinCopyLinear, Pi.single_eq_of_ne hji]
  rw [hsplit, map_add]
  rfl

variable {Φ}

/-- **The intersection of a deleted cell with an upper-support contact face
is again a deleted cell.**  The contact face `F` of the join polytope `Q` is
exactly the set of points of `Q` at which the exposing functional of the
support is tight, so its intersection with the Cayley cell `C₀` is the convex
hull of the tight Cayley vertices of `C₀`.  These decompose factorwise into
the exposed subfaces `F i ∩ {ℓ_i = max}` of the component faces of `C₀`,
which are again pairwise disjoint faces of `P`; hence the intersection is the
Cayley cell of that tuple of faces. -/
theorem exists_cell_carrier_eq_inter_contactSet (y : StrongDual ℝ V)
    (C₀ : PolytopalDeletedCellIndex P m)
    (c : CompactConvexProjection.UpperSupportCertificate
      (Φ.upperEnvelopeData y)) :
    ∃ C : PolytopalDeletedCellIndex P m,
      C.carrier = C₀.carrier ∩ c.contactSet := by
  classical
  set l : StrongDual ℝ (PolytopalJoinAmbient n m) := c.exposingFunctional with hl
  set M : ℝ := c.intercept with hM
  have hQ : ∀ w ∈ polytopalJoinCarrier P m, l w ≤ M := fun w hw ↦
    c.exposingFunctional_le_intercept hw
  have hcontact : ∀ w : PolytopalJoinAmbient n m,
      w ∈ c.contactSet ↔ w ∈ polytopalJoinCarrier P m ∧ l w = M := by
    intro w
    constructor
    · intro hw
      exact ⟨hw.1, c.exposingFunctional_eq_intercept hw⟩
    · rintro ⟨hwQ, hwl⟩
      refine ⟨hwQ, ?_⟩
      have hlw : (Φ.upperEnvelopeData y).height w
          - c.slope ((Φ.upperEnvelopeData y).projection w) = c.intercept := hwl
      change (Φ.upperEnvelopeData y).height w
        = c.slope ((Φ.upperEnvelopeData y).projection w) + c.intercept
      linarith
  -- the tight exposed subface of each component face
  set k : Fin (m + 1) → ℝ := fun i ↦ l (polytopalJoinCopy (m := m) i 0) with hk
  set g : Fin (m + 1) → StrongDual ℝ (CoordinateSpace n) :=
    fun i ↦ factorFunctional l i with hg
  have hcopy : ∀ (i : Fin (m + 1)) (v : CoordinateSpace n),
      l (polytopalJoinCopy i v) = g i v + k i := fun i v ↦
    apply_polytopalJoinCopy l i v
  have hcopyQ : ∀ (i : Fin (m + 1)) (v : CoordinateSpace n), v ∈ P.carrier →
      polytopalJoinCopy i v ∈ polytopalJoinCarrier P m := fun i v hv ↦
    polytopalJoinCopy_mem_carrier P i ⟨v, hv⟩
  set H : Fin (m + 1) → Set (CoordinateSpace n) :=
    fun i ↦ {v | v ∈ P.carrier ∧ g i v + k i = M} with hH
  have hHface : ∀ i, P.IsFace (H i) := by
    intro i
    exact isExposed_of_affine_eq_max (g i) (k i) M fun v hv ↦ by
      rw [← hcopy i v]
      exact hQ _ (hcopyQ i v hv)
  set G : Fin (m + 1) → Set (CoordinateSpace n) :=
    fun i ↦ (C₀.1 i).carrier ∩ H i with hG
  have hGface : ∀ i, P.IsFace (G i) := fun i ↦ (C₀.1 i).isFace.inter (hHface i)
  -- the resulting deleted cell
  set C : PolytopalDeletedCellIndex P m :=
    ⟨fun i ↦ PolytopeFaceIndex.ofFace (G i) (hGface i), by
      intro i j hij
      rw [PolytopeFaceIndex.carrier_ofFace, PolytopeFaceIndex.carrier_ofFace]
      exact Disjoint.mono inter_subset_left inter_subset_left (C₀.2 hij)⟩ with hC
  have hCvertices : ∀ i, (C.1 i).1.1 = P.faceVertices (G i) := fun _ ↦ rfl
  have hCface : ∀ i, (C.1 i).carrier = G i := fun i ↦
    PolytopeFaceIndex.carrier_ofFace (G i) (hGface i)
  -- the cell is contained in the contact face
  have hCcontact : C.carrier ⊆ c.contactSet := by
    refine convexHull_min ?_ c.contactSet_convex
    intro s hs
    rw [Finset.mem_coe, PolytopalDeletedCellIndex.vertices,
      Finset.mem_biUnion] at hs
    obtain ⟨i, _hi, hs⟩ := hs
    rw [Finset.mem_image] at hs
    obtain ⟨v, hv, rfl⟩ := hs
    rw [hCvertices i, P.mem_faceVertices] at hv
    have hvP : v ∈ P.carrier := hv.2.2.1
    refine (hcontact _).2 ⟨hcopyQ i v hvP, ?_⟩
    rw [hcopy i v]
    exact hv.2.2.2
  refine ⟨C, Subset.antisymm (subset_inter ?_ hCcontact) ?_⟩
  · refine PolytopalDeletedCellIndex.carrier_mono fun i ↦ ?_
    rw [hCface i]
    exact inter_subset_left
  · rintro z ⟨hzC₀, hzc⟩
    have hzl : l z = M := ((hcontact z).1 hzc).2
    have hverticesQ : ∀ s ∈ C₀.vertices, l s ≤ M := by
      intro s hs
      refine hQ s ?_
      apply polytopalDeletedJoinCarrier_subset_joinCarrier P
      apply C₀.carrier_subset_deletedJoinCarrier
      exact subset_convexHull ℝ (C₀.vertices : Set (PolytopalJoinAmbient n m))
        (Finset.mem_coe.2 hs)
    have hfilter := mem_convexHull_filter_of_eq_max C₀.vertices l M hverticesQ
      hzC₀ hzl
    refine convexHull_min ?_ C.convex hfilter
    intro s hs
    rw [Finset.mem_coe, Finset.mem_filter] at hs
    obtain ⟨hsV, hsl⟩ := hs
    rw [PolytopalDeletedCellIndex.vertices, Finset.mem_biUnion] at hsV
    obtain ⟨i, _hi, hsV⟩ := hsV
    rw [Finset.mem_image] at hsV
    obtain ⟨v, hv, rfl⟩ := hsV
    have hvvert : v ∈ P.vertices := Finset.mem_powerset.1 (C₀.1 i).1.2 hv
    have hvP : v ∈ P.carrier :=
      subset_convexHull ℝ (P.vertices : Set (CoordinateSpace n))
        (Finset.mem_coe.2 hvvert)
    have hvface : v ∈ (C₀.1 i).carrier :=
      subset_convexHull ℝ ((C₀.1 i).1.1 : Set (CoordinateSpace n))
        (Finset.mem_coe.2 hv)
    have hvG : v ∈ G i := by
      refine ⟨hvface, hvP, ?_⟩
      rw [← hcopy i v]
      exact hsl
    have hvmem : v ∈ (C.1 i).1.1 := by
      rw [hCvertices i, P.mem_faceVertices]
      exact ⟨hvvert, hvG⟩
    exact subset_convexHull ℝ (C.vertices : Set (PolytopalJoinAmbient n m))
      (Finset.mem_coe.2 (C.copy_vertex_mem_vertices i hvmem))

/-- **The deleted cell through a top point.**  Every point of the deleted
join which lies on the fiberwise upper envelope of `λ_y` lies in a cell of
the deleted join on which the `y`-height is nonnegative everywhere. -/
theorem exists_deletedCell_nonneg_of_mem_topLocus (y : StrongDual ℝ V)
    {z : PolytopalJoinAmbient n m} (hzD : z ∈ polytopalDeletedJoinCarrier P m)
    (hztop : z ∈ (Φ.upperEnvelopeData y).topLocus) :
    ∃ C : PolytopalDeletedCellIndex P m, z ∈ C.carrier ∧
      ∀ w ∈ C.carrier, 0 ≤ y (Φ.joinMap w) := by
  -- a deleted cell containing `z`
  obtain ⟨C₀, hzC₀⟩ := mem_iUnion.1 hzD
  -- the upper support contact face containing `z`
  obtain ⟨c, hzc⟩ :=
    CompactConvexProjection.exists_upperSupportCertificate_mem_contactSet_of_convexHull
      (Φ.upperEnvelopeData y) (polytopalJoinVertices P m) rfl hztop
  obtain ⟨C, hC⟩ := exists_cell_carrier_eq_inter_contactSet (Φ := Φ) y C₀ c
  refine ⟨C, by rw [hC]; exact ⟨hzC₀, hzc⟩, fun w hw ↦ ?_⟩
  have hwc : w ∈ C₀.carrier ∩ c.contactSet := by rw [← hC]; exact hw
  exact CompactConvexProjection.UpperSupportCertificate.height_nonnegative_on_contactSet
    (Φ.upperEnvelopeData y) c (Φ.upperEnvelopeData_hasNonnegativeFiberWitness y)
    w hwc.2

variable (Φ)

/-- **The incidence space `X` of the paper**, for the actual cell family of
the polytopal deleted join. -/
abbrev DeletedCellIncidenceSpace :=
  FaceIncidenceSpace (polytopalDeletedJoinCarrier P m)
    (fun C : PolytopalDeletedCellIndex P m ↦ C.carrier) (fun z ↦ Φ.joinMap z)

/-- The second projection `X → S(V*)`. -/
def cellIncidenceDual (p : Φ.DeletedCellIncidenceSpace) : DualUnitSphere V :=
  ⟨p.1.2, p.2.1⟩

theorem cellIncidenceDual_continuous : Continuous Φ.cellIncidenceDual := by
  apply Continuous.subtype_mk
  exact continuous_snd.comp continuous_subtype_val

/-- **The inclusion `Y → X`** into the actual cell incidence space. -/
def topIncidenceToCellIncidence (p : Φ.TopIncidenceSpace) :
    Φ.DeletedCellIncidenceSpace := by
  refine ⟨(p.1.1, p.1.2.1), p.1.2.2, ?_⟩
  obtain ⟨C, hmem, hnonneg⟩ :=
    exists_deletedCell_nonneg_of_mem_topLocus (Φ := Φ) p.1.2.1 p.1.1.2 p.2
  exact ⟨C, hmem, hnonneg⟩

theorem topIncidenceToCellIncidence_continuous :
    Continuous Φ.topIncidenceToCellIncidence := by
  apply Continuous.subtype_mk
  exact (continuous_fst.comp continuous_subtype_val).prodMk
    (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))

theorem topIncidenceToCellIncidence_injective :
    Function.Injective Φ.topIncidenceToCellIncidence := by
  intro p q hpq
  have h1 : p.1.1 = q.1.1 := congrArg (fun r ↦ r.1.1) hpq
  have h2 : (p.1.2 : StrongDual ℝ V) = (q.1.2 : StrongDual ℝ V) :=
    congrArg (fun r ↦ r.1.2) hpq
  exact Subtype.ext (Prod.ext h1 (Subtype.ext h2))

/-- The inclusion `Y → X` commutes with the projections to the deleted
join. -/
theorem faceIncidenceProjection_topIncidenceToCellIncidence
    (p : Φ.TopIncidenceSpace) :
    faceIncidenceProjection (Φ.topIncidenceToCellIncidence p) = p.1.1 :=
  rfl

/-- The inclusion `Y → X` commutes with the projections to the dual unit
sphere. -/
theorem cellIncidenceDual_topIncidenceToCellIncidence (p : Φ.TopIncidenceSpace) :
    Φ.cellIncidenceDual (Φ.topIncidenceToCellIncidence p) =
      Φ.topIncidenceProjection p :=
  rfl

/-- The cell incidence space `X` is compact. -/
theorem deletedCellIncidenceSpace_compactSpace [FiniteDimensional ℝ V] :
    CompactSpace Φ.DeletedCellIncidenceSpace :=
  faceIncidenceSpace_compactSpace (polytopalDeletedJoinCarrier_compact P)
    fun C ↦ C.compact.isClosed

/-! ### Comparison with the auxiliary candidate-subset incidence space -/

/-- The cell incidence space maps to the auxiliary candidate-subset incidence
space of `PolytopalTopIncidence.lean`. -/
def cellIncidenceToJoinFaceIncidence (p : Φ.DeletedCellIncidenceSpace) :
    Φ.JoinFaceIncidenceSpace := by
  refine ⟨p.1, p.2.1, ?_⟩
  obtain ⟨C, hmem, hnonneg⟩ := p.2.2
  exact ⟨C.toJoinFaceIndex, hmem, hnonneg⟩

theorem cellIncidenceToJoinFaceIncidence_continuous :
    Continuous Φ.cellIncidenceToJoinFaceIncidence :=
  Continuous.subtype_mk continuous_subtype_val _

/-- The strengthened inclusion `Y → X` refines the previous inclusion of `Y`
into the auxiliary candidate-subset incidence space. -/
theorem cellIncidenceToJoinFaceIncidence_topIncidenceToCellIncidence
    (p : Φ.TopIncidenceSpace) :
    Φ.cellIncidenceToJoinFaceIncidence (Φ.topIncidenceToCellIncidence p) =
      Φ.topIncidenceToFaceIncidence p :=
  rfl

/-! ### Contractibility of the fibers of `X → D` -/

/-- **The minimal-cell fiber data.**  If `Φ.joinMap` does not vanish on the
deleted join, every point of `D` has a minimal deleted cell whose image is a
nonempty compact convex set avoiding the origin. -/
def cellIncidenceFiberData
    (hzero : ∀ z ∈ polytopalDeletedJoinCarrier P m, Φ.joinMap z ≠ 0)
    (x : polytopalDeletedJoinCarrier P m) :
    FaceIncidenceFiberData (fun C : PolytopalDeletedCellIndex P m ↦ C.carrier)
      (fun z ↦ Φ.joinMap z) (x : PolytopalJoinAmbient n m) where
  index := minimalCell P x.2
  mem_face := mem_minimalCell x.2
  minimal := fun C hC ↦ minimalCell_subset x.2 C hC
  image_convex :=
    (minimalCell P x.2).convex.is_linear_image Φ.joinMap.toLinearMap.isLinear
  image_compact := (minimalCell P x.2).compact.image Φ.joinMap.continuous
  image_nonempty := ⟨Φ.joinMap x, ⟨x, mem_minimalCell x.2, rfl⟩⟩
  image_avoids_zero := by
    rintro ⟨w, hw, hw0⟩
    exact hzero w ((minimalCell P x.2).carrier_subset_deletedJoinCarrier hw) hw0

/-- **Contractible fibers of the first projection `X → D`.** -/
theorem cellIncidenceFiber_contractible
    (hzero : ∀ z ∈ polytopalDeletedJoinCarrier P m, Φ.joinMap z ≠ 0)
    (x : polytopalDeletedJoinCarrier P m) :
    ContractibleSpace
      (FaceIncidenceFiber (polytopalDeletedJoinCarrier P m)
        (fun C : PolytopalDeletedCellIndex P m ↦ C.carrier)
        (fun z ↦ Φ.joinMap z) x) :=
  faceIncidenceFiber_contractible_of_data x (Φ.cellIncidenceFiberData hzero x)

/-- The first projection `X → D` is surjective. -/
theorem cellIncidenceProjection_surjective
    (hzero : ∀ z ∈ polytopalDeletedJoinCarrier P m, Φ.joinMap z ≠ 0) :
    Function.Surjective
      (faceIncidenceProjection (D := polytopalDeletedJoinCarrier P m)
        (G := fun C : PolytopalDeletedCellIndex P m ↦ C.carrier)
        (Φ := fun z ↦ Φ.joinMap z)) :=
  faceIncidenceProjection_surjective (Φ.cellIncidenceFiberData hzero)

/-- **The polytopal incidence package.**  `Y` includes continuously into the
cell incidence space `X` compatibly with both projections, `X` is compact,
and — as soon as `Φ.joinMap` avoids zero on the deleted join — the first
projection `X → D` is surjective with contractible fibers. -/
theorem lemmaY_cellIncidence [FiniteDimensional ℝ V]
    (hzero : ∀ z ∈ polytopalDeletedJoinCarrier P m, Φ.joinMap z ≠ 0) :
    Continuous Φ.topIncidenceToCellIncidence ∧
      Function.Injective Φ.topIncidenceToCellIncidence ∧
      (∀ p, faceIncidenceProjection (Φ.topIncidenceToCellIncidence p) = p.1.1) ∧
      (∀ p, Φ.cellIncidenceDual (Φ.topIncidenceToCellIncidence p) =
        Φ.topIncidenceProjection p) ∧
      CompactSpace Φ.DeletedCellIncidenceSpace ∧
      Function.Surjective
        (faceIncidenceProjection (D := polytopalDeletedJoinCarrier P m)
          (G := fun C : PolytopalDeletedCellIndex P m ↦ C.carrier)
          (Φ := fun z ↦ Φ.joinMap z)) ∧
      ∀ x : polytopalDeletedJoinCarrier P m,
        ContractibleSpace
          (FaceIncidenceFiber (polytopalDeletedJoinCarrier P m)
            (fun C : PolytopalDeletedCellIndex P m ↦ C.carrier)
            (fun z ↦ Φ.joinMap z) x) :=
  ⟨Φ.topIncidenceToCellIncidence_continuous,
    Φ.topIncidenceToCellIncidence_injective,
    Φ.faceIncidenceProjection_topIncidenceToCellIncidence,
    Φ.cellIncidenceDual_topIncidenceToCellIncidence,
    Φ.deletedCellIncidenceSpace_compactSpace,
    Φ.cellIncidenceProjection_surjective hzero,
    Φ.cellIncidenceFiber_contractible hzero⟩

end PolytopalJoinMap

end AffineTverberg

