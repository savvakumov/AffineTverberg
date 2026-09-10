import AffineTverberg.SimplicialDeletedJoinModel
import AffineTverberg.SimplicialFiber

set_option linter.style.header false

/-!
# The deleted join over a boundary ridge

In the simplicial-ball case of `lemma:Y` one fixes a boundary ridge `L` (an
`(N-1)`-simplex of the boundary of the ball) and works with the deleted join
`L^{*(m+1)}_Δ` of that single simplex.  This file provides:

* the finite index type `RidgeDeletedCellIndex L m` of the cells of
  `L^{*(m+1)}_Δ`, its geometric carrier `ridgeDeletedJoinCarrier`, and the fact
  that every such cell is a cell of the full deleted join of the boundary of
  `K` (`isBoundaryDeletedJoinCell_of_ridgeCell`);
* the criterion `nonneg_on_joinCellCarrier_iff`: for a fixed functional,
  nonnegativity on a join cell is equivalent to nonnegativity at its vertices;
* the allowed colour sets `W_v(y)` and the proof, from the diagonal relation,
  that they are nonempty;
* the combinatorial identification of the cells of `L^{*(m+1)}_Δ` on which the
  functional is nonnegative with the faces of the join complex
  `W_{v₁}(y) * ⋯ * W_{v_N}(y)` of `AffineTverberg/SimplicialFiber.lean`.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg

section Cells

variable {e m : ℕ}

/-- A subset of the vertex set of the chosen ridge. -/
abbrev RidgeSubset (L : Finset (CoordinateSpace e)) :=
  {s : Finset (CoordinateSpace e) // s ∈ L.powerset}

/-- The finite index type of the cells of the deleted join `L^{*(m+1)}_Δ`:
tuples of pairwise disjoint subsets of the ridge `L`. -/
abbrev RidgeDeletedCellIndex (L : Finset (CoordinateSpace e)) (m : ℕ) :=
  {f : Fin (m + 1) → RidgeSubset L //
    Pairwise fun i j ↦ Disjoint (f i).1 (f j).1}

namespace RidgeDeletedCellIndex

variable {L : Finset (CoordinateSpace e)}

instance : Finite (RidgeDeletedCellIndex L m) := Subtype.finite

noncomputable instance : Fintype (RidgeDeletedCellIndex L m) :=
  Fintype.ofFinite (RidgeDeletedCellIndex L m)

/-- The tuple of vertex sets of a cell. -/
def faces (F : RidgeDeletedCellIndex L m) : Fin (m + 1) → Finset (CoordinateSpace e) :=
  fun i ↦ (F.1 i).1

theorem faces_subset (F : RidgeDeletedCellIndex L m) (i : Fin (m + 1)) : F.faces i ⊆ L :=
  Finset.mem_powerset.mp (F.1 i).2

theorem faces_pairwiseDisjoint (F : RidgeDeletedCellIndex L m) :
    Pairwise fun i j ↦ Disjoint (F.faces i) (F.faces j) :=
  F.2

/-- The geometric carrier of a cell of `L^{*(m+1)}_Δ`. -/
def carrier (F : RidgeDeletedCellIndex L m) : Set (PolytopalJoinAmbient e m) :=
  joinCellCarrier F.faces

theorem carrier_convex (F : RidgeDeletedCellIndex L m) : Convex ℝ F.carrier :=
  joinCellCarrier_convex _

theorem carrier_compact (F : RidgeDeletedCellIndex L m) : IsCompact F.carrier :=
  joinCellCarrier_compact _

theorem carrier_isClosed (F : RidgeDeletedCellIndex L m) : IsClosed F.carrier :=
  joinCellCarrier_isClosed _

end RidgeDeletedCellIndex

/-- The concrete deleted join `L^{*(m+1)}_Δ` of a single simplex. -/
def ridgeDeletedJoinCarrier (L : Finset (CoordinateSpace e)) (m : ℕ) :
    Set (PolytopalJoinAmbient e m) :=
  ⋃ F : RidgeDeletedCellIndex L m, F.carrier

theorem ridgeDeletedJoinCarrier_compact (L : Finset (CoordinateSpace e)) :
    IsCompact (ridgeDeletedJoinCarrier L m) :=
  isCompact_iUnion fun F ↦ F.carrier_compact

theorem carrier_subset_ridgeDeletedJoinCarrier {L : Finset (CoordinateSpace e)}
    (F : RidgeDeletedCellIndex L m) : F.carrier ⊆ ridgeDeletedJoinCarrier L m :=
  Set.subset_iUnion (fun F : RidgeDeletedCellIndex L m ↦ F.carrier) F

/-- Colour a finite set of vertices by a colour function; the resulting tuple of
fibres is a cell of `L^{*(m+1)}_Δ`. -/
def colorCell (S : Finset (CoordinateSpace e)) (c : CoordinateSpace e → Fin (m + 1)) :
    Fin (m + 1) → Finset (CoordinateSpace e) := by
  classical
  exact fun i ↦ S.filter fun v ↦ c v = i

theorem mem_colorCell {S : Finset (CoordinateSpace e)} {c : CoordinateSpace e → Fin (m + 1)}
    {i : Fin (m + 1)} {v : CoordinateSpace e} :
    v ∈ colorCell S c i ↔ v ∈ S ∧ c v = i := by
  classical
  simp [colorCell]

theorem colorCell_subset {S : Finset (CoordinateSpace e)} {c : CoordinateSpace e → Fin (m + 1)}
    (i : Fin (m + 1)) : colorCell S c i ⊆ S := by
  intro v hv
  exact (mem_colorCell.mp hv).1

theorem colorCell_pairwiseDisjoint (S : Finset (CoordinateSpace e))
    (c : CoordinateSpace e → Fin (m + 1)) :
    Pairwise fun i j ↦ Disjoint (colorCell S c i) (colorCell S c j) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro v hi hj
  exact hij (((mem_colorCell.mp hi).2).symm.trans (mem_colorCell.mp hj).2)

/-- The cell of `L^{*(m+1)}_Δ` determined by a colouring of a subset of `L`. -/
def colorRidgeCell {L : Finset (CoordinateSpace e)} (S : Finset (CoordinateSpace e))
    (hS : S ⊆ L) (c : CoordinateSpace e → Fin (m + 1)) : RidgeDeletedCellIndex L m :=
  ⟨fun i ↦ ⟨colorCell S c i, Finset.mem_powerset.mpr ((colorCell_subset i).trans hS)⟩,
    colorCell_pairwiseDisjoint S c⟩

@[simp]
theorem colorRidgeCell_faces {L : Finset (CoordinateSpace e)}
    (S : Finset (CoordinateSpace e)) (hS : S ⊆ L) (c : CoordinateSpace e → Fin (m + 1)) :
    (colorRidgeCell (m := m) S hS c).faces = colorCell S c :=
  rfl

theorem copy_mem_colorRidgeCell_carrier {L : Finset (CoordinateSpace e)}
    {S : Finset (CoordinateSpace e)} (hS : S ⊆ L) (c : CoordinateSpace e → Fin (m + 1))
    {v : CoordinateSpace e} (hv : v ∈ S) :
    polytopalJoinCopy (c v) v ∈ (colorRidgeCell (m := m) S hS c).carrier :=
  copy_mem_joinCellCarrier (c v) (mem_colorCell.mpr ⟨hv, rfl⟩)

end Cells

section RidgeInFullDeletedJoin

variable {e n m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
  {L : Finset (CoordinateSpace e)}

/-- Every nonempty subset of a boundary ridge is a boundary face. -/
theorem isBoundarySimplicialFace_of_subset_ridge (hL : IsBoundaryRidge n K L)
    {s : Finset (CoordinateSpace e)} (hs : s ⊆ L) (hne : s.Nonempty) :
    IsBoundarySimplicialFace n K s :=
  ⟨K.down_closed hL.1 hs hne, L, hL, hs⟩

/-- Every cell of `L^{*(m+1)}_Δ` is a cell of the deleted join of the boundary
of `K`.  This is the first half of `Y ⊆ X`. -/
theorem isBoundaryDeletedJoinCell_of_ridgeCell (hL : IsBoundaryRidge n K L)
    (F : RidgeDeletedCellIndex L m) :
    IsBoundaryDeletedJoinCell n K F.faces := by
  refine ⟨fun i ↦ ?_, F.faces_pairwiseDisjoint⟩
  rcases (F.faces i).eq_empty_or_nonempty with h | h
  · exact Or.inl h
  · exact Or.inr (isBoundarySimplicialFace_of_subset_ridge hL (F.faces_subset i) h)

/-- The deleted join of the ridge sits inside the deleted join of the whole
boundary complex. -/
theorem ridgeDeletedJoinCarrier_subset (hL : IsBoundaryRidge n K L) :
    ridgeDeletedJoinCarrier L m ⊆ simplicialDeletedJoinCarrier n K m := by
  intro z hz
  obtain ⟨F, hzF⟩ := Set.mem_iUnion.mp hz
  exact joinCellCarrier_subset_simplicialDeletedJoinCarrier K
    (isBoundaryDeletedJoinCell_of_ridgeCell hL F) hzF

end RidgeInFullDeletedJoin

section Nonnegativity

variable {e m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For a fixed functional, nonnegativity on a join cell is equivalent to
nonnegativity at the Cayley vertices of the cell. -/
theorem nonneg_on_joinCellCarrier_iff (y : StrongDual ℝ E)
    (Φ : PolytopalJoinAmbient e m →L[ℝ] E)
    (f : Fin (m + 1) → Finset (CoordinateSpace e)) :
    (∀ z ∈ joinCellCarrier f, 0 ≤ y (Φ z)) ↔
      ∀ i, ∀ v ∈ f i, 0 ≤ y (Φ (polytopalJoinCopy i v)) := by
  constructor
  · intro h i v hv
    exact h _ (copy_mem_joinCellCarrier i hv)
  · intro h
    have hconv : Convex ℝ {z : PolytopalJoinAmbient e m | 0 ≤ y (Φ z)} := by
      have hpre : {z : PolytopalJoinAmbient e m | 0 ≤ y (Φ z)} =
          (y.comp Φ).toLinearMap ⁻¹' Set.Ici (0 : ℝ) := by
        ext z; simp [Set.mem_Ici]
      rw [hpre]
      exact (convex_Ici (0 : ℝ)).linear_preimage _
    have hsub : joinCellCarrier f ⊆ {z : PolytopalJoinAmbient e m | 0 ≤ y (Φ z)} := by
      apply convexHull_min _ hconv
      intro w hw
      obtain ⟨i, v, hv, rfl⟩ := mem_joinCellVertices.mp (Finset.mem_coe.mp hw)
      exact h i v hv
    exact fun z hz ↦ hsub hz

/-- Vertexwise form of nonnegativity on a cell of the ridge deleted join. -/
theorem nonneg_on_ridgeCell_iff {L : Finset (CoordinateSpace e)} (y : StrongDual ℝ E)
    (Φ : PolytopalJoinAmbient e m →L[ℝ] E) (F : RidgeDeletedCellIndex L m) :
    (∀ z ∈ F.carrier, 0 ≤ y (Φ z)) ↔
      ∀ i, ∀ v ∈ F.faces i, 0 ≤ y (Φ (polytopalJoinCopy i v)) :=
  nonneg_on_joinCellCarrier_iff y Φ F.faces

end Nonnegativity

section AllowedColors

variable {e m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The value of the functional `y` on the `i`-th copy of the vertex `v`; the
allowed colours of `v` are the indices where this is nonnegative. -/
def ridgeEval (Φ : PolytopalJoinAmbient e m →L[ℝ] E) (y : StrongDual ℝ E) :
    CoordinateSpace e → Fin (m + 1) → ℝ :=
  fun v i ↦ y (Φ (polytopalJoinCopy i v))

/-- The diagonal relation `∑ᵢ Φ(vᵢ) = 0` makes the values of `y` on the copies
of a vertex sum to zero. -/
theorem sum_ridgeEval_eq_zero {Φ : PolytopalJoinAmbient e m →L[ℝ] E}
    (hdiag : ∀ x : CoordinateSpace e, ∑ i : Fin (m + 1), Φ (polytopalJoinCopy i x) = 0)
    (y : StrongDual ℝ E) (v : CoordinateSpace e) :
    ∑ i, ridgeEval Φ y v i = 0 := by
  have := congrArg y (hdiag v)
  rw [map_sum, map_zero] at this
  exact this

/-- Claim (4) of the paper: the diagonal relation makes the allowed colour set
`W_v(y)` nonempty for every vertex `v`. -/
theorem nonempty_allowedColors {Φ : PolytopalJoinAmbient e m →L[ℝ] E}
    (hdiag : ∀ x : CoordinateSpace e, ∑ i : Fin (m + 1), Φ (polytopalJoinCopy i x) = 0)
    (y : StrongDual ℝ E) (v : CoordinateSpace e) :
    Nonempty (NonnegativeColor (ridgeEval Φ y v)) :=
  nonempty_nonnegativeColor _ (sum_ridgeEval_eq_zero hdiag y v)

/-- A chosen allowed colour for every vertex. -/
def chosenAllowedColor {Φ : PolytopalJoinAmbient e m →L[ℝ] E}
    (hdiag : ∀ x : CoordinateSpace e, ∑ i : Fin (m + 1), Φ (polytopalJoinCopy i x) = 0)
    (y : StrongDual ℝ E) (v : CoordinateSpace e) : Fin (m + 1) :=
  (Classical.choice (nonempty_allowedColors hdiag y v)).1

theorem chosenAllowedColor_nonneg {Φ : PolytopalJoinAmbient e m →L[ℝ] E}
    (hdiag : ∀ x : CoordinateSpace e, ∑ i : Fin (m + 1), Φ (polytopalJoinCopy i x) = 0)
    (y : StrongDual ℝ E) (v : CoordinateSpace e) :
    0 ≤ y (Φ (polytopalJoinCopy (chosenAllowedColor hdiag y v) v)) :=
  (Classical.choice (nonempty_allowedColors hdiag y v)).2

end AllowedColors

section CombinatorialFiber

variable {e m : ℕ} (L : Finset (CoordinateSpace e))
  (eval : CoordinateSpace e → Fin (m + 1) → ℝ)

/-- The cells of `L^{*(m+1)}_Δ` on which the functional is nonnegative, as a
subtype of tuples of vertex sets. -/
abbrev NonnegRidgeCell :=
  {f : Fin (m + 1) → Finset (CoordinateSpace e) //
    (∀ i, f i ⊆ L) ∧ (Pairwise fun i j ↦ Disjoint (f i) (f j)) ∧
      (∀ i, ∀ v ∈ f i, 0 ≤ eval v i)}

/-- The faces of the join complex `W_{v₁} * ⋯ * W_{v_N}` of colour choices. -/
abbrev ColorChoiceFace :=
  {s : Finset (NonnegativeColoredVertex L eval) // IsColorChoiceFace L eval s}

variable {L eval}

/-- Two coloured vertices agreeing on the underlying vertex and colour are
equal. -/
theorem coloredVertex_ext {a b : NonnegativeColoredVertex L eval}
    (h₁ : (a.1 : CoordinateSpace e) = (b.1 : CoordinateSpace e))
    (h₂ : (a.2 : Fin (m + 1)) = (b.2 : Fin (m + 1))) : a = b := by
  obtain ⟨⟨v, hv⟩, ⟨i, hi⟩⟩ := a
  obtain ⟨⟨w, hw⟩, ⟨j, hj⟩⟩ := b
  simp only at h₁ h₂
  subst h₁
  subst h₂
  rfl

/-- The coloured copy of a vertex of a nonnegative cell. -/
def coloredVertexOfCell {f : Fin (m + 1) → Finset (CoordinateSpace e)}
    (hsub : ∀ i, f i ⊆ L) (hnn : ∀ i, ∀ v ∈ f i, 0 ≤ eval v i)
    (i : Fin (m + 1)) (v : {v // v ∈ f i}) : NonnegativeColoredVertex L eval :=
  ⟨⟨v.1, hsub i v.2⟩, ⟨i, hnn i v.1 v.2⟩⟩

/-- The colour-choice face associated with a nonnegative cell. -/
def colorFaceOfCell {f : Fin (m + 1) → Finset (CoordinateSpace e)}
    (hsub : ∀ i, f i ⊆ L) (hnn : ∀ i, ∀ v ∈ f i, 0 ≤ eval v i) :
    Finset (NonnegativeColoredVertex L eval) := by
  classical
  exact Finset.univ.biUnion fun i ↦ (f i).attach.image (coloredVertexOfCell hsub hnn i)

theorem mem_colorFaceOfCell {f : Fin (m + 1) → Finset (CoordinateSpace e)}
    (hsub : ∀ i, f i ⊆ L) (hnn : ∀ i, ∀ v ∈ f i, 0 ≤ eval v i)
    (a : NonnegativeColoredVertex L eval) :
    a ∈ colorFaceOfCell hsub hnn ↔ (a.1 : CoordinateSpace e) ∈ f (a.2 : Fin (m + 1)) := by
  classical
  constructor
  · intro ha
    rw [colorFaceOfCell, Finset.mem_biUnion] at ha
    obtain ⟨i, _hi, ha⟩ := ha
    rw [Finset.mem_image] at ha
    obtain ⟨v, _hv, rfl⟩ := ha
    exact v.2
  · intro ha
    rw [colorFaceOfCell, Finset.mem_biUnion]
    refine ⟨(a.2 : Fin (m + 1)), Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    exact ⟨⟨(a.1 : CoordinateSpace e), ha⟩, Finset.mem_attach _ _, rfl⟩

/-- The nonnegative cell associated with a finite set of coloured vertices. -/
def cellOfColorFace (s : Finset (NonnegativeColoredVertex L eval)) :
    Fin (m + 1) → Finset (CoordinateSpace e) := by
  classical
  exact fun i ↦ (s.filter fun a ↦ (a.2 : Fin (m + 1)) = i).image
    fun a ↦ (a.1 : CoordinateSpace e)

theorem mem_cellOfColorFace {s : Finset (NonnegativeColoredVertex L eval)}
    {i : Fin (m + 1)} {v : CoordinateSpace e} :
    v ∈ cellOfColorFace s i ↔
      ∃ a ∈ s, (a.2 : Fin (m + 1)) = i ∧ (a.1 : CoordinateSpace e) = v := by
  classical
  simp [cellOfColorFace, Finset.mem_image, Finset.mem_filter, and_assoc]

theorem cellOfColorFace_subset (s : Finset (NonnegativeColoredVertex L eval))
    (i : Fin (m + 1)) : cellOfColorFace s i ⊆ L := by
  intro v hv
  obtain ⟨a, _ha, _hai, rfl⟩ := mem_cellOfColorFace.mp hv
  exact a.1.2

theorem cellOfColorFace_nonneg (s : Finset (NonnegativeColoredVertex L eval))
    (i : Fin (m + 1)) : ∀ v ∈ cellOfColorFace s i, 0 ≤ eval v i := by
  intro v hv
  obtain ⟨a, _ha, hai, rfl⟩ := mem_cellOfColorFace.mp hv
  rw [← hai]
  exact a.2.2

theorem cellOfColorFace_pairwiseDisjoint {s : Finset (NonnegativeColoredVertex L eval)}
    (hs : IsColorChoiceFace L eval s) :
    Pairwise fun i j ↦ Disjoint (cellOfColorFace s i) (cellOfColorFace s j) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro v hi hj
  obtain ⟨a, ha, hai, hav⟩ := mem_cellOfColorFace.mp hi
  obtain ⟨b, hb, hbj, hbv⟩ := mem_cellOfColorFace.mp hj
  have hab : a = b := hs a ha b hb (Subtype.ext (hav.trans hbv.symm))
  exact hij (hai.symm.trans (by rw [hab]; exact hbj))

theorem isColorChoiceFace_colorFaceOfCell
    {f : Fin (m + 1) → Finset (CoordinateSpace e)}
    (hsub : ∀ i, f i ⊆ L) (hnn : ∀ i, ∀ v ∈ f i, 0 ≤ eval v i)
    (hdisj : Pairwise fun i j ↦ Disjoint (f i) (f j)) :
    IsColorChoiceFace L eval (colorFaceOfCell hsub hnn) := by
  intro a ha b hb hab
  have ha' := (mem_colorFaceOfCell hsub hnn a).mp ha
  have hb' := (mem_colorFaceOfCell hsub hnn b).mp hb
  have hvertex : (a.1 : CoordinateSpace e) = (b.1 : CoordinateSpace e) := congrArg Subtype.val hab
  have hcolor : (a.2 : Fin (m + 1)) = (b.2 : Fin (m + 1)) := by
    by_contra hne
    have := Finset.disjoint_left.mp (hdisj hne) ha'
    rw [hvertex] at this
    exact this hb'
  exact coloredVertex_ext hvertex hcolor

/-- Round trip: the cell of the colour face of a cell is the original cell. -/
theorem cellOfColorFace_colorFaceOfCell
    {f : Fin (m + 1) → Finset (CoordinateSpace e)}
    (hsub : ∀ i, f i ⊆ L) (hnn : ∀ i, ∀ v ∈ f i, 0 ≤ eval v i) :
    cellOfColorFace (colorFaceOfCell hsub hnn) = f := by
  funext i
  ext v
  constructor
  · intro hv
    obtain ⟨a, ha, hai, hav⟩ := mem_cellOfColorFace.mp hv
    have := (mem_colorFaceOfCell hsub hnn a).mp ha
    rw [hai, hav] at this
    exact this
  · intro hv
    refine mem_cellOfColorFace.mpr ⟨coloredVertexOfCell hsub hnn i ⟨v, hv⟩, ?_, rfl, rfl⟩
    exact (mem_colorFaceOfCell hsub hnn _).mpr hv

/-- Round trip: the colour face of the cell of a colour face is the original
colour face. -/
theorem colorFaceOfCell_cellOfColorFace (s : Finset (NonnegativeColoredVertex L eval)) :
    colorFaceOfCell (cellOfColorFace_subset s) (cellOfColorFace_nonneg s) = s := by
  ext a
  rw [mem_colorFaceOfCell]
  constructor
  · intro ha
    obtain ⟨b, hb, hbi, hbv⟩ := mem_cellOfColorFace.mp ha
    have : b = a := coloredVertex_ext hbv hbi
    rwa [this] at hb
  · intro ha
    exact mem_cellOfColorFace.mpr ⟨a, ha, rfl, rfl⟩

variable (L eval)

/-- Claim (5) of the paper: the cells of `L^{*(m+1)}_Δ` on which `y` is
nonnegative are exactly the faces of the join complex
`W_{v₁}(y) * ⋯ * W_{v_N}(y)` of the allowed colour sets. -/
def nonnegRidgeCellEquivColorChoiceFace :
    NonnegRidgeCell L eval ≃ ColorChoiceFace L eval where
  toFun f := ⟨colorFaceOfCell f.2.1 f.2.2.2,
    isColorChoiceFace_colorFaceOfCell f.2.1 f.2.2.2 f.2.2.1⟩
  invFun s := ⟨cellOfColorFace s.1, cellOfColorFace_subset s.1,
    cellOfColorFace_pairwiseDisjoint s.2, cellOfColorFace_nonneg s.1⟩
  left_inv f := Subtype.ext (cellOfColorFace_colorFaceOfCell f.2.1 f.2.2.2)
  right_inv s := Subtype.ext (colorFaceOfCell_cellOfColorFace s.1)

/-- Under the identification, the nonempty nonnegative cells correspond to the
faces of the join complex. -/
theorem mem_nonnegativeJoinComplex_iff_exists_nonempty (f : NonnegRidgeCell L eval) :
    (nonnegRidgeCellEquivColorChoiceFace L eval f).1 ∈ nonnegativeJoinComplex L eval ↔
      ∃ i, (f.1 i).Nonempty := by
  classical
  rw [mem_nonnegativeJoinComplex_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, _⟩
    exact ⟨(a.2 : Fin (m + 1)), ⟨(a.1 : CoordinateSpace e),
      (mem_colorFaceOfCell f.2.1 f.2.2.2 a).mp ha⟩⟩
  · rintro ⟨i, v, hv⟩
    refine ⟨⟨coloredVertexOfCell f.2.1 f.2.2.2 i ⟨v, hv⟩, ?_⟩,
      isColorChoiceFace_colorFaceOfCell f.2.1 f.2.2.2 f.2.2.1⟩
    exact (mem_colorFaceOfCell f.2.1 f.2.2.2 _).mpr hv

end CombinatorialFiber

end AffineTverberg

