import AffineTverberg.BadComplexComparison

set_option linter.style.header false

/-!
# The actual boundary join, independently of vertex labels

The boundary carrier is the union of the simplicial boundary faces. Its
join is a finite union of actual Cayley cells. This file identifies that
intrinsic carrier with the labeled carrier used by the bad-complex proof,
discharges all enumeration hypotheses in the complement homology theorem,
and records compactness and the closed deleted-join inclusion.

No sphere identification or Alexander duality is assumed or claimed here.
-/

noncomputable section

open Set CategoryTheory

namespace AffineTverberg

variable {e n m : ℕ} (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))

/-- The actual geometric carrier of the combinatorial boundary. -/
def simplicialBoundaryCarrier (n : ℕ) : Set (CoordinateSpace e) :=
  ⋃ s ∈ {s | IsBoundarySimplicialFace n K s}, convexHull ℝ (s : Set (CoordinateSpace e))

theorem simplicialBoundaryCarrier_subset_space : simplicialBoundaryCarrier K n ⊆ K.space := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := mem_iUnion₂.mp hx
  exact convexHull_subset_space hs.1 hx

theorem simplicialBoundaryCarrier_compact (hfin : K.faces.Finite) :
    IsCompact (simplicialBoundaryCarrier K n) := by
  apply Set.Finite.isCompact_biUnion (hfin.subset (fun _ hs ↦ hs.1))
  exact fun s _ ↦ s.finite_toSet.isCompact_convexHull ℝ

/-- Nonemptiness of the boundary gives an actual boundary ridge; conversely,
a positive-dimensional boundary ridge has a nonempty realization. -/
theorem simplicialBoundaryCarrier_nonempty_iff (hn : 0 < n) :
    (simplicialBoundaryCarrier K n).Nonempty ↔ ∃ L, IsBoundaryRidge n K L := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨s, hs, _⟩ := mem_iUnion₂.mp hx
    obtain ⟨L, hL, _⟩ := hs.2
    exact ⟨L, hL⟩
  · rintro ⟨L, hL⟩
    have hne : L.Nonempty := Finset.card_pos.mp (by rw [hL.2.1]; exact hn)
    obtain ⟨v, hv⟩ := hne
    refine ⟨v, mem_iUnion₂.mpr ⟨L, ⟨hL.1, L, hL, Finset.Subset.refl L⟩, ?_⟩⟩
    exact subset_convexHull ℝ _ hv

/-- All tuples of boundary faces, including empty join factors. -/
def BoundaryJoinCells (n m : ℕ) : Set (Fin (m + 1) → Finset (CoordinateSpace e)) :=
  {f | ∀ i, f i = ∅ ∨ IsBoundarySimplicialFace n K (f i)}

/-- The full boundary join, with no vertex-indexing choices in its definition. -/
def simplicialBoundaryJoinCarrier (n m : ℕ) : Set (PolytopalJoinAmbient e m) :=
  ⋃ f ∈ BoundaryJoinCells K n m, joinCellCarrier f

theorem boundaryJoinCells_finite (hfin : K.faces.Finite) :
    (BoundaryJoinCells K n m).Finite := by
  apply Set.Finite.subset (Set.Finite.pi (t := fun _ : Fin (m + 1) ↦ insert ∅ K.faces)
    fun _ ↦ hfin.insert ∅)
  intro f hf i _
  exact (hf i).imp_right (fun h ↦ h.1)

theorem simplicialBoundaryJoinCarrier_compact (hfin : K.faces.Finite) :
    IsCompact (simplicialBoundaryJoinCarrier K n m) :=
  Set.Finite.isCompact_biUnion (boundaryJoinCells_finite K hfin)
    (fun f _ ↦ joinCellCarrier_compact f)

theorem simplicialBoundaryJoinCarrier_isClosed (hfin : K.faces.Finite) :
    IsClosed (simplicialBoundaryJoinCarrier K n m) :=
  (simplicialBoundaryJoinCarrier_compact K hfin).isClosed

theorem simplicialDeletedJoinCarrier_subset_boundaryJoin :
    simplicialDeletedJoinCarrier n K m ⊆ simplicialBoundaryJoinCarrier K n m := by
  intro z hz
  obtain ⟨f, hf, hz⟩ := (mem_simplicialDeletedJoinCarrier_iff K z).mp hz
  exact mem_iUnion₂.mpr ⟨f, hf.1, hz⟩

/-- The deleted join is closed as a subspace of the actual full boundary join. -/
theorem isClosed_deletedJoin_in_boundaryJoin (hfin : K.faces.Finite) :
    IsClosed {z : simplicialBoundaryJoinCarrier K n m |
      z.val ∈ simplicialDeletedJoinCarrier n K m} :=
  (simplicialDeletedJoinCarrier_isClosed K hfin).preimage continuous_subtype_val

/-- A boundary join is nonempty exactly when its underlying boundary is. -/
theorem simplicialBoundaryJoinCarrier_nonempty_iff :
    (simplicialBoundaryJoinCarrier K n m).Nonempty ↔
      (simplicialBoundaryCarrier K n).Nonempty := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨f, hf, hz⟩ := mem_iUnion₂.mp hz
    obtain ⟨w, hw⟩ := (convexHull_nonempty_iff.mp ⟨z, hz⟩)
    obtain ⟨i, v, hv, _⟩ := mem_joinCellVertices.mp hw
    rcases hf i with hi | hi
    · simp [hi] at hv
    · exact ⟨v, mem_iUnion₂.mpr ⟨f i, hi, subset_convexHull ℝ _ hv⟩⟩
  · rintro ⟨x, hx⟩
    obtain ⟨s, hs, hx⟩ := mem_iUnion₂.mp hx
    exact ⟨polytopalJoinCopy 0 x, mem_iUnion₂.mpr
      ⟨fun _ ↦ s, fun _ ↦ Or.inr hs, copy_convexHull_mem_joinCellCarrier 0 hx⟩⟩

/-- Weights and independently chosen points in the boundary. Zero-weight
coordinates will be collapsed by the join map. -/
def BoundaryJoinParameters (n m : ℕ) :=
  (stdSimplex ℝ (Fin (m + 1))) × (Fin (m + 1) → simplicialBoundaryCarrier K n)
  deriving TopologicalSpace

/-- The concrete weighted-point parameterization of the full boundary join. -/
def boundaryJoinParameterMap (p : BoundaryJoinParameters K n m) : PolytopalJoinAmbient e m :=
  ∑ i, p.1.val i • polytopalJoinCopy i (p.2 i).val

theorem boundaryJoinParameterMap_mem (p : BoundaryJoinParameters K n m) :
    boundaryJoinParameterMap K p ∈ simplicialBoundaryJoinCarrier K n m := by
  classical
  have hx : ∀ i, ∃ s, IsBoundarySimplicialFace n K s ∧
      (p.2 i).val ∈ convexHull ℝ (s : Set (CoordinateSpace e)) := by
    intro i
    obtain ⟨s, hs, hx⟩ := mem_iUnion₂.mp (p.2 i).property
    exact ⟨s, hs, hx⟩
  choose f hf hx using hx
  refine mem_iUnion₂.mpr ⟨f, fun i ↦ Or.inr (hf i), ?_⟩
  exact sum_smul_copy_mem_joinCellCarrier p.1.val (fun i ↦ (p.2 i).val)
    p.1.property.1 p.1.property.2 (fun i _ ↦ hx i)

theorem continuous_boundaryJoinParameterMap :
    Continuous (boundaryJoinParameterMap K (n := n) (m := m)) := by
  unfold boundaryJoinParameterMap
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).smul
    (((polytopalJoinCopyAffine i).continuous_of_finiteDimensional).comp
      (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)))

/-- The parameter map into the actual carrier. -/
def boundaryJoinParameterProjection :
    C(BoundaryJoinParameters K n m, simplicialBoundaryJoinCarrier K n m) :=
  ⟨fun p ↦ ⟨boundaryJoinParameterMap K p, boundaryJoinParameterMap_mem K p⟩,
    (continuous_boundaryJoinParameterMap K).subtype_mk _⟩

/-- Every actual join point has a weighted-boundary-point representation,
including when some weights vanish. No boundary nonemptiness is assumed:
an actual join point itself supplies a point for the zero-weight factors. -/
theorem surjective_boundaryJoinParameterProjection :
    Function.Surjective (boundaryJoinParameterProjection K (n := n) (m := m)) := by
  classical
  intro z
  obtain ⟨b, hb⟩ := (simplicialBoundaryJoinCarrier_nonempty_iff K).mp ⟨z.val, z.property⟩
  obtain ⟨f, hf, hz⟩ := mem_iUnion₂.mp z.property
  obtain ⟨t, x, ht0, ht1, hx, heq⟩ := exists_repr_of_mem_joinCellCarrier hz
  have hxp : ∀ i, 0 < t i → x i ∈ simplicialBoundaryCarrier K n := by
    intro i hi
    rcases hf i with hfi | hfi
    · have hh := hx i hi
      simp [hfi] at hh
    · exact mem_iUnion₂.mpr ⟨f i, hfi, hx i hi⟩
  let y : Fin (m + 1) → simplicialBoundaryCarrier K n :=
    fun i ↦ if hi : 0 < t i then ⟨x i, hxp i hi⟩ else ⟨b, hb⟩
  refine ⟨(⟨t, ht0, ht1⟩, y), Subtype.ext ?_⟩
  change (∑ i, t i • polytopalJoinCopy i (y i).val) = z.val
  rw [heq]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : 0 < t i
  · simp [y, hi]
  · have hti : t i = 0 := le_antisymm (le_of_not_gt hi) (ht0 i)
    simp [hti]

/-- The usual weighted-point description has exactly the quotient topology.
This supplies the topological, not just set-theoretic, join model. -/
theorem isQuotientMap_boundaryJoinParameterProjection (hfin : K.faces.Finite) :
    Topology.IsQuotientMap (boundaryJoinParameterProjection K (n := n) (m := m)) := by
  let := isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ (Fin (m + 1)))
  let := isCompact_iff_compactSpace.mp (simplicialBoundaryCarrier_compact K (n := n) hfin)
  have : CompactSpace (BoundaryJoinParameters K n m) :=
    inferInstanceAs (CompactSpace
      ((stdSimplex ℝ (Fin (m + 1))) × (Fin (m + 1) → simplicialBoundaryCarrier K n)))
  exact Topology.IsQuotientMap.of_surjective_continuous
    (surjective_boundaryJoinParameterProjection K) (boundaryJoinParameterProjection K).continuous

/-- The fibers identify only the points in zero-weight coordinates. -/
theorem boundaryJoinParameterMap_eq_iff (p q : BoundaryJoinParameters K n m) :
    boundaryJoinParameterMap K p = boundaryJoinParameterMap K q ↔
      p.1 = q.1 ∧ ∀ i, p.1.val i ≠ 0 → p.2 i = q.2 i := by
  constructor
  · intro h
    have hc (i) := congrFun h i
    simp only [boundaryJoinParameterMap, sum_smul_copy_apply] at hc
    have ht : p.1 = q.1 := Subtype.ext (funext (fun i ↦ congrArg Prod.snd (hc i)))
    refine ⟨ht, fun i hi ↦ Subtype.ext ?_⟩
    have hi' := congrArg Prod.fst (hc i)
    change p.1.val i • (p.2 i).val = q.1.val i • (q.2 i).val at hi'
    rw [← ht] at hi'
    exact (smul_right_injective _ hi) hi'
  · rintro ⟨ht, hx⟩
    unfold boundaryJoinParameterMap
    apply Finset.sum_congr rfl
    intro i _
    rw [← ht]
    by_cases hi : p.1.val i = 0
    · simp [hi]
    · rw [hx i hi]

namespace BadEdge

variable {W : Type} [Fintype W] (idx : W → Fin (m + 1)) (vert : W → CoordinateSpace e)

omit [Fintype W] in
/-- Every complete labeling realizes exactly the intrinsic boundary join.
Injectivity of the labels is unnecessary for this equality of carriers. -/
theorem iUnion_joinFactor_eq_boundaryJoin
    [Finite W]
    (hcover : ∀ (i : Fin (m + 1)) (s : Finset (CoordinateSpace e)),
      IsBoundarySimplicialFace n K s → ∀ v ∈ s, ∃ w, idx w = i ∧ vert w = v) :
    (⋃ S ∈ {S : Finset W | IsJoinFace n K idx vert S},
      joinCellCarrier (joinFactor idx vert S)) = simplicialBoundaryJoinCarrier K n m := by
  classical
  let := Fintype.ofFinite W
  ext z
  constructor
  · intro hz
    obtain ⟨S, hS, hz⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨joinFactor idx vert S, hS, hz⟩
  · intro hz
    obtain ⟨f, hf, hz⟩ := mem_iUnion₂.mp hz
    have hcovered : ∀ i v, v ∈ f i → ∃ w, idx w = i ∧ vert w = v := by
      intro i v hv
      rcases hf i with hi | hi
      · simp [hi] at hv
      · exact hcover i (f i) hi v hv
    have heq : joinFactor idx vert (preimageJoinFace idx vert f) = f :=
      funext (joinFactor_preimageJoinFace idx vert hcovered)
    refine mem_iUnion₂.mpr ⟨preimageJoinFace idx vert f, ?_, ?_⟩
    · change ∀ i, _
      rw [heq]
      exact hf
    · rw [heq]
      exact hz

end BadEdge

/-- **The complement homology input to Alexander duality**, now for the
intrinsic boundary join with all finite-labeling hypotheses discharged. -/
theorem isZero_simplicialBoundaryJoinComplement_homology (hfin : K.faces.Finite)
    (hm : 2 ≤ m) (hn : 0 < n) :
    Limits.IsZero ((realSingularHomology (m * n - 1)).obj
      (TopCat.of ↥(simplicialBoundaryJoinCarrier K n m \ simplicialDeletedJoinCarrier n K m))) := by
  let a := BadEdge.boundaryJoinVertexIndexing (n := n) (m := m) hfin
  let := a.subdivisionOrder
  have h := BadEdge.isZero_deletedJoinComplementSingularHomology
    a.factor a.vertex hm hn a.injective a.covers
  rw [BadEdge.iUnion_joinFactor_eq_boundaryJoin K a.factor a.vertex a.covers] at h
  exact h

end AffineTverberg
