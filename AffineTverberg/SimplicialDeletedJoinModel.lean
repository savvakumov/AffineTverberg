import AffineTverberg.SimplicialJoinCell

set_option linter.style.header false

/-!
# The concrete deleted join of the boundary of a simplicial ball

Using the join cells of `AffineTverberg/SimplicialJoinCell.lean`, this file
realizes the `(m + 1)`-fold deleted join `(∂K)^{*(m+1)}_Δ` of the boundary of a
finite pure simplicial ball `K` as an actual compact subset

`simplicialDeletedJoinCarrier n K m ⊆ PolytopalJoinAmbient e m`,

namely the union of the join cells indexed by tuples of pairwise disjoint
boundary faces (some of which may be empty).  This is the simplicial counterpart
of `polytopalDeletedJoinCarrier`.

The file also builds the *Sarkaria join map* in this model.  On a single cell
the map `φ` of the paper is affine, given by an ambient affine map `ψ i` on the
`i`-th component face, and the resulting Sarkaria map is the restriction of a
genuine linear map `simplicialSarkariaLinear ψ` of the ambient join space.  The
two compatibility theorems with the witness-level model of `DeletedJoin.lean`
are

* `SimplicialDeletedJoinPoint.realization_mem_simplicialDeletedJoinCarrier`;
* `exists_sarkariaValue_eq_zero_of_simplicialSarkariaLinear_eq_zero`,

the latter turning a concrete zero on a cell into a zero of
`SimplicialDeletedJoinPoint.sarkariaValue`, exactly as
`PolytopalDeletedJoinRealization.lean` does in the polytopal case.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg

section Space

variable {e : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-- The geometric realization of a face is contained in the realization of the
complex. -/
theorem convexHull_subset_space {s : Finset (CoordinateSpace e)} (hs : s ∈ K.faces) :
    convexHull ℝ (s : Set (CoordinateSpace e)) ⊆ K.space := by
  intro x hx
  exact Set.mem_biUnion hs hx

end Space

section Cells

variable {e n m : ℕ} (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))

/-- A cell of the `(m + 1)`-fold deleted join of the boundary complex: a tuple of
pairwise disjoint boundary faces, where empty entries are allowed. -/
def IsBoundaryDeletedJoinCell (n : ℕ) (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))
    (f : Fin (m + 1) → Finset (CoordinateSpace e)) : Prop :=
  (∀ i, f i = ∅ ∨ IsBoundarySimplicialFace n K (f i)) ∧
    Pairwise fun i j ↦ Disjoint (f i) (f j)

/-- The set of cells of the deleted join of the boundary complex. -/
def BoundaryDeletedJoinCells (n : ℕ) (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))
    (m : ℕ) : Set (Fin (m + 1) → Finset (CoordinateSpace e)) :=
  {f | IsBoundaryDeletedJoinCell n K f}

/-- Every component of a deleted-join cell is a face of `K` or empty. -/
theorem face_mem_faces_of_isBoundaryDeletedJoinCell
    {f : Fin (m + 1) → Finset (CoordinateSpace e)}
    (hf : IsBoundaryDeletedJoinCell n K f) (i : Fin (m + 1)) :
    f i = ∅ ∨ f i ∈ K.faces := by
  rcases hf.1 i with h | h
  · exact Or.inl h
  · exact Or.inr h.1

/-- There are only finitely many cells in the deleted join of a finite complex. -/
theorem boundaryDeletedJoinCells_finite (hfin : K.faces.Finite) :
    (BoundaryDeletedJoinCells n K m).Finite := by
  apply Set.Finite.subset (Set.Finite.pi (t := fun _ : Fin (m + 1) ↦ insert ∅ K.faces)
    fun _ ↦ hfin.insert ∅)
  intro f hf i _hi
  rcases face_mem_faces_of_isBoundaryDeletedJoinCell K hf i with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- The concrete `(m + 1)`-fold deleted join of the boundary of `K`. -/
def simplicialDeletedJoinCarrier (n : ℕ)
    (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)) (m : ℕ) :
    Set (PolytopalJoinAmbient e m) :=
  ⋃ f ∈ BoundaryDeletedJoinCells n K m, joinCellCarrier f

theorem joinCellCarrier_subset_simplicialDeletedJoinCarrier
    {f : Fin (m + 1) → Finset (CoordinateSpace e)}
    (hf : IsBoundaryDeletedJoinCell n K f) :
    joinCellCarrier f ⊆ simplicialDeletedJoinCarrier n K m :=
  Set.subset_biUnion_of_mem (u := fun f ↦ joinCellCarrier f) hf

theorem mem_simplicialDeletedJoinCarrier_iff (z : PolytopalJoinAmbient e m) :
    z ∈ simplicialDeletedJoinCarrier n K m ↔
      ∃ f, IsBoundaryDeletedJoinCell n K f ∧ z ∈ joinCellCarrier f := by
  simp [simplicialDeletedJoinCarrier, BoundaryDeletedJoinCells]

/-- The concrete deleted join of a finite complex is compact. -/
theorem simplicialDeletedJoinCarrier_compact (hfin : K.faces.Finite) :
    IsCompact (simplicialDeletedJoinCarrier n K m) :=
  Set.Finite.isCompact_biUnion (boundaryDeletedJoinCells_finite K hfin)
    fun f _hf ↦ joinCellCarrier_compact f

theorem simplicialDeletedJoinCarrier_isClosed (hfin : K.faces.Finite) :
    IsClosed (simplicialDeletedJoinCarrier (n := n) (m := m) K) :=
  (simplicialDeletedJoinCarrier_compact K hfin).isClosed

end Cells

section Realization

variable {e n m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-- The Cayley realization of a represented deleted-join point of the boundary
of a simplicial ball. -/
def SimplicialDeletedJoinPoint.realization
    (z : SimplicialDeletedJoinPoint (n := n) (m := m) K) : PolytopalJoinAmbient e m :=
  ∑ i, z.weight i • polytopalJoinCopy i (z.point i).1

/-- The tuple of supporting faces of a represented point is a deleted-join cell. -/
theorem SimplicialDeletedJoinPoint.isBoundaryDeletedJoinCell
    (z : SimplicialDeletedJoinPoint (n := n) (m := m) K) :
    IsBoundaryDeletedJoinCell n K z.face :=
  ⟨fun i ↦ Or.inr (z.face_isBoundary i), z.faces_pairwiseDisjoint⟩

/-- Every represented deleted-join point realizes into its own cell. -/
theorem SimplicialDeletedJoinPoint.realization_mem_joinCellCarrier
    (z : SimplicialDeletedJoinPoint (n := n) (m := m) K) :
    z.realization ∈ joinCellCarrier z.face := by
  apply sum_smul_copy_mem_joinCellCarrier _ _ z.weight_nonneg z.weight_sum
  intro i hi
  exact z.point_mem_face i hi

/-- Every represented deleted-join point realizes into the concrete compact
deleted join. -/
theorem SimplicialDeletedJoinPoint.realization_mem_simplicialDeletedJoinCarrier
    (z : SimplicialDeletedJoinPoint (n := n) (m := m) K) :
    z.realization ∈ simplicialDeletedJoinCarrier n K m :=
  joinCellCarrier_subset_simplicialDeletedJoinCarrier K z.isBoundaryDeletedJoinCell
    z.realization_mem_joinCellCarrier

/-- In particular the concrete deleted join is nonempty as soon as `K` has a
boundary face. -/
theorem simplicialDeletedJoinCarrier_nonempty
    {s : Finset (CoordinateSpace e)} (hs : IsBoundarySimplicialFace n K s)
    (v : CoordinateSpace e) (hv : v ∈ s) :
    (simplicialDeletedJoinCarrier n K m).Nonempty := by
  classical
  set f : Fin (m + 1) → Finset (CoordinateSpace e) :=
    fun i ↦ if i = Fin.last m then s else ∅ with hfdef
  have hcell : IsBoundaryDeletedJoinCell n K f := by
    constructor
    · intro i
      by_cases hi : i = Fin.last m
      · exact Or.inr (by simpa [hfdef, hi] using hs)
      · exact Or.inl (by simp [hfdef, hi])
    · intro i j hij
      by_cases hi : i = Fin.last m
      · have hj : j ≠ Fin.last m := fun h ↦ hij (hi.trans h.symm)
        simp [hfdef, hj]
      · simp [hfdef, hi]
  refine ⟨polytopalJoinCopy (Fin.last m) v,
    joinCellCarrier_subset_simplicialDeletedJoinCarrier K hcell ?_⟩
  exact copy_mem_joinCellCarrier (Fin.last m) (by simp [hfdef, hv])

end Realization

section SarkariaLinear

variable {e d m : ℕ}

/-- The linear extension of an ambient affine map to homogenized coordinates:
`(u, t) ↦ (ψ.linear u + t • ψ 0, t)`. -/
def homogenizedAffineLinear (ψ : CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d) :
    (CoordinateSpace e × ℝ) →ₗ[ℝ] CoordinateSpace d × ℝ where
  toFun p := (ψ.linear p.1 + p.2 • ψ 0, p.2)
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul, Prod.mk_add_mk]
    congr 1
    abel
  map_smul' a p := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply, Prod.smul_mk]
    congr 1
    rw [smul_add, smul_smul, smul_eq_mul]

@[simp]
theorem homogenizedAffineLinear_apply (ψ : CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d)
    (p : CoordinateSpace e × ℝ) :
    homogenizedAffineLinear ψ p = (ψ.linear p.1 + p.2 • ψ 0, p.2) :=
  rfl

/-- On homogenized points `t • (x, 1)` the linear extension computes the
homogenized affine image. -/
theorem homogenizedAffineLinear_smul_homogenize
    (ψ : CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d) (t : ℝ) (x : CoordinateSpace e) :
    homogenizedAffineLinear ψ (t • x, t) = t • homogenize (ψ x) := by
  have hdecomp : ψ x = ψ.linear x + ψ 0 := by
    conv_lhs => rw [AffineMap.decomp ψ]
    simp
  rw [homogenizedAffineLinear_apply]
  simp only [homogenize, Prod.smul_mk, smul_eq_mul, mul_one, map_smul]
  rw [hdecomp, smul_add]

/-- The Sarkaria join map of a family of ambient affine maps, one per join
factor.  It is genuinely linear on the ambient join space. -/
def simplicialSarkariaLinear (ψ : Fin (m + 1) → (CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d)) :
    PolytopalJoinAmbient e m →ₗ[ℝ] SarkariaTarget d m where
  toFun z := sarkariaMap fun i ↦ homogenizedAffineLinear (ψ i) (z i)
  map_add' z w := by
    funext j
    simp only [sarkariaMap, Pi.add_apply, map_add, Pi.add_apply]
    abel
  map_smul' a z := by
    funext j
    simp only [sarkariaMap, Pi.smul_apply, map_smul, RingHom.id_apply, Pi.smul_apply]
    rw [smul_sub]

@[simp]
theorem simplicialSarkariaLinear_apply
    (ψ : Fin (m + 1) → (CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d))
    (z : PolytopalJoinAmbient e m) :
    simplicialSarkariaLinear ψ z = sarkariaMap fun i ↦ homogenizedAffineLinear (ψ i) (z i) :=
  rfl

/-- The continuous Sarkaria join map. -/
def simplicialSarkariaMap (ψ : Fin (m + 1) → (CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d)) :
    PolytopalJoinAmbient e m →L[ℝ] SarkariaTarget d m :=
  (simplicialSarkariaLinear ψ).toContinuousLinearMap

@[simp]
theorem simplicialSarkariaMap_apply
    (ψ : Fin (m + 1) → (CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d))
    (z : PolytopalJoinAmbient e m) :
    simplicialSarkariaMap ψ z = simplicialSarkariaLinear ψ z :=
  rfl

/-- The Sarkaria join map on a weighted sum of Cayley copies is the Sarkaria map
of the weighted homogenized image points. -/
theorem simplicialSarkariaLinear_sum_smul_copy
    (ψ : Fin (m + 1) → (CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d))
    (t : Fin (m + 1) → ℝ) (x : Fin (m + 1) → CoordinateSpace e) :
    simplicialSarkariaLinear ψ (∑ i, t i • polytopalJoinCopy i (x i)) =
      sarkariaMap (weightedHomogenized t fun i ↦ ψ i (x i)) := by
  rw [simplicialSarkariaLinear_apply]
  congr 1
  funext i
  rw [sum_smul_copy_apply, homogenizedAffineLinear_smul_homogenize]
  rfl

/-- Equation (3) of the paper for the simplicial Sarkaria map: the copies of a
fixed point in the `m + 1` join factors sum to zero. -/
theorem sum_simplicialSarkariaLinear_copy
    (ψ : CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d) (x : CoordinateSpace e) :
    ∑ i : Fin (m + 1), simplicialSarkariaLinear (fun _ ↦ ψ) (polytopalJoinCopy i x) = 0 := by
  classical
  funext j
  simp only [Finset.sum_apply, simplicialSarkariaLinear_apply, sarkariaMap, Pi.zero_apply]
  rw [Finset.sum_sub_distrib]
  have key : ∀ k : Fin (m + 1),
      ∑ i : Fin (m + 1),
          homogenizedAffineLinear ψ ((polytopalJoinCopy (m := m) i x) k) =
        homogenizedAffineLinear ψ (x, 1) := by
    intro k
    rw [Finset.sum_eq_single k]
    · simp [polytopalJoinCopy]
    · intro i _hi hik
      simp [polytopalJoinCopy, Pi.single_eq_of_ne (Ne.symm hik)]
    · simp
  rw [key, key, sub_self]

end SarkariaLinear

section ZeroTransfer

variable {e n d m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-- Weighted homogenized data only depends on the points in the factors of
positive weight. -/
theorem weightedHomogenized_congr {V : Type*} [AddCommGroup V] [Module ℝ V]
    (t : Fin (m + 1) → ℝ) (a b : Fin (m + 1) → V)
    (h : ∀ i, 0 < t i → a i = b i) (ht : ∀ i, 0 ≤ t i) :
    weightedHomogenized t a = weightedHomogenized t b := by
  funext i
  rcases eq_or_lt_of_le (ht i) with hi | hi
  · simp [weightedHomogenized, ← hi]
  · rw [weightedHomogenized, weightedHomogenized, h i hi]

/-- The Sarkaria value of a represented point is the value of the linear
Sarkaria join map at its realization, provided the ambient affine maps agree
with `φ` on the supporting faces. -/
theorem SimplicialDeletedJoinPoint.sarkariaValue_eq_simplicialSarkariaLinear
    (φ : K.space → CoordinateSpace d)
    (ψ : Fin (m + 1) → (CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d))
    (w : SimplicialDeletedJoinPoint (n := n) (m := m) K)
    (hψ : ∀ i, 0 < w.weight i → φ (w.point i) = ψ i (w.point i).1) :
    SimplicialDeletedJoinPoint.sarkariaValue K w φ =
      simplicialSarkariaLinear ψ w.realization := by
  rw [SimplicialDeletedJoinPoint.realization, simplicialSarkariaLinear_sum_smul_copy]
  rw [SimplicialDeletedJoinPoint.sarkariaValue]
  congr 1
  exact weightedHomogenized_congr _ _ _ (fun i hi ↦ hψ i hi) w.weight_nonneg

/-- A zero of the linear Sarkaria join map at a point of a deleted-join cell
produces a represented deleted-join point with vanishing Sarkaria value: the
concrete form of `theorem:zero` in the simplicial-ball case. -/
theorem exists_sarkariaValue_eq_zero_of_simplicialSarkariaLinear_eq_zero
    {φ : K.space → CoordinateSpace d}
    {ψ : Fin (m + 1) → (CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d)}
    {f : Fin (m + 1) → Finset (CoordinateSpace e)}
    (hf : IsBoundaryDeletedJoinCell n K f)
    (hψ : ∀ i, ∀ y : K.space, y.1 ∈ convexHull ℝ (f i : Set (CoordinateSpace e)) →
      φ y = ψ i y.1)
    {z : PolytopalJoinAmbient e m} (hz : z ∈ joinCellCarrier f)
    (hzero : simplicialSarkariaLinear ψ z = 0) :
    ∃ w : SimplicialDeletedJoinPoint (n := n) (m := m) K,
      SimplicialDeletedJoinPoint.sarkariaValue K w φ = 0 := by
  classical
  obtain ⟨t, x, ht0, ht1, hx, rfl⟩ := exists_repr_of_mem_joinCellCarrier hz
  rw [simplicialSarkariaLinear_sum_smul_copy] at hzero
  -- All join weights are equal, hence all equal to `1 / (m + 1)`.
  have hweq : ∀ i, t i = t (Fin.last m) :=
    weights_eq_last_of_sarkariaMap_eq_zero t _ hzero
  have hsum : ((m : ℝ) + 1) * t (Fin.last m) = 1 := by
    have : ∑ i : Fin (m + 1), t i = ∑ _i : Fin (m + 1), t (Fin.last m) :=
      Finset.sum_congr rfl fun i _hi ↦ hweq i
    rw [ht1] at this
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    push_cast at this
    linarith
  have hlastpos : 0 < t (Fin.last m) := by
    rcases eq_or_lt_of_le (ht0 (Fin.last m)) with h | h
    · rw [← h] at hsum; simp at hsum
    · exact h
  have hpos : ∀ i, 0 < t i := fun i ↦ by rw [hweq i]; exact hlastpos
  -- Hence every component face is nonempty, so it is a boundary face.
  have hxface : ∀ i, x i ∈ convexHull ℝ (f i : Set (CoordinateSpace e)) :=
    fun i ↦ hx i (hpos i)
  have hfne : ∀ i, f i ≠ ∅ := by
    intro i hfi
    have := hxface i
    rw [hfi] at this
    simp at this
  have hbdry : ∀ i, IsBoundarySimplicialFace n K (f i) := by
    intro i
    rcases hf.1 i with h | h
    · exact absurd h (hfne i)
    · exact h
  have hmemspace : ∀ i, x i ∈ K.space := fun i ↦
    convexHull_subset_space (hbdry i).1 (hxface i)
  refine ⟨{ weight := t
            point := fun i ↦ ⟨x i, hmemspace i⟩
            face := f
            weight_nonneg := ht0
            weight_sum := ht1
            face_isBoundary := hbdry
            faces_pairwiseDisjoint := hf.2
            point_mem_face := fun i _hi ↦ hxface i }, ?_⟩
  rw [SimplicialDeletedJoinPoint.sarkariaValue]
  refine Eq.trans ?_ hzero
  congr 1
  refine weightedHomogenized_congr _ _ _ (fun i _hi ↦ ?_) ht0
  exact hψ i ⟨x i, hmemspace i⟩ (hxface i)

/-- On any deleted-join cell, a map which is affine on the simplices of `K` is
given factorwise by ambient affine maps. -/
theorem exists_cellwise_affine_extension
    {φ : K.space → CoordinateSpace d} (hφ : IsAffineOnSimplicialFaces K φ)
    {f : Fin (m + 1) → Finset (CoordinateSpace e)}
    (hf : IsBoundaryDeletedJoinCell n K f) :
    ∃ ψ : Fin (m + 1) → (CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d),
      ∀ i, ∀ y : K.space, y.1 ∈ convexHull ℝ (f i : Set (CoordinateSpace e)) →
        φ y = ψ i y.1 := by
  classical
  have hchoice : ∀ i, ∃ ψ : CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d,
      ∀ y : K.space, y.1 ∈ convexHull ℝ (f i : Set (CoordinateSpace e)) → φ y = ψ y.1 := by
    intro i
    rcases hf.1 i with hempty | hbdry
    · exact ⟨AffineMap.const ℝ (CoordinateSpace e) 0, by
        intro y hy
        rw [hempty] at hy
        simp at hy⟩
    · exact hφ (f i) hbdry.1
  choose ψ hψ using hchoice
  exact ⟨ψ, hψ⟩

end ZeroTransfer

end AffineTverberg

