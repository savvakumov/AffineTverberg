import AffineTverberg.PolytopalDeletedJoinRealization

set_option linter.style.header false

/-!
# Cells of a join of finite vertex sets

This file builds the concrete finite/cellular model used for the deleted join of
a simplicial complex.  A *join cell* is indexed by a tuple `f : Fin (m + 1) →
Finset (CoordinateSpace e)` of vertex sets, one per join factor.  Its geometric
carrier is the convex hull of the Cayley copies `polytopalJoinCopy i v` of the
vertices `v ∈ f i`, inside the same ambient space `PolytopalJoinAmbient e m`
already used for the polytopal join.

The main results are the basic geometric facts about a cell (compactness,
convexity, monotonicity, the total-weight identity) and the two directions
relating a point of a cell with its barycentric data:

* `sum_smul_copy_mem_joinCellCarrier` : weights and points in the component
  faces assemble to a point of the cell;
* `exists_repr_of_mem_joinCellCarrier` : every point of a cell arises this way.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg

variable {e m : ℕ}

/-- The Cayley vertex set of the join cell determined by the tuple `f`. -/
def joinCellVertices (f : Fin (m + 1) → Finset (CoordinateSpace e)) :
    Finset (PolytopalJoinAmbient e m) := by
  classical
  exact Finset.univ.biUnion fun i ↦ (f i).image (polytopalJoinCopy i)

/-- The geometric carrier of the join cell determined by the tuple `f`. -/
def joinCellCarrier (f : Fin (m + 1) → Finset (CoordinateSpace e)) :
    Set (PolytopalJoinAmbient e m) :=
  convexHull ℝ (joinCellVertices f : Set (PolytopalJoinAmbient e m))

theorem mem_joinCellVertices {f : Fin (m + 1) → Finset (CoordinateSpace e)}
    {w : PolytopalJoinAmbient e m} :
    w ∈ joinCellVertices f ↔ ∃ i, ∃ v ∈ f i, polytopalJoinCopy i v = w := by
  classical
  simp [joinCellVertices, Finset.mem_biUnion, Finset.mem_image]

theorem copy_mem_joinCellVertices {f : Fin (m + 1) → Finset (CoordinateSpace e)}
    (i : Fin (m + 1)) {v : CoordinateSpace e} (hv : v ∈ f i) :
    polytopalJoinCopy i v ∈ joinCellVertices f :=
  mem_joinCellVertices.mpr ⟨i, v, hv, rfl⟩

theorem joinCellVertices_mono {f g : Fin (m + 1) → Finset (CoordinateSpace e)}
    (h : ∀ i, f i ⊆ g i) : joinCellVertices f ⊆ joinCellVertices g := by
  intro w hw
  obtain ⟨i, v, hv, rfl⟩ := mem_joinCellVertices.mp hw
  exact copy_mem_joinCellVertices i (h i hv)

theorem joinCellCarrier_mono {f g : Fin (m + 1) → Finset (CoordinateSpace e)}
    (h : ∀ i, f i ⊆ g i) : joinCellCarrier f ⊆ joinCellCarrier g :=
  convexHull_mono (by exact_mod_cast joinCellVertices_mono h)

theorem joinCellCarrier_convex (f : Fin (m + 1) → Finset (CoordinateSpace e)) :
    Convex ℝ (joinCellCarrier f) :=
  convex_convexHull ℝ _

theorem joinCellCarrier_compact (f : Fin (m + 1) → Finset (CoordinateSpace e)) :
    IsCompact (joinCellCarrier f) :=
  (joinCellVertices f).finite_toSet.isCompact_convexHull ℝ

theorem joinCellCarrier_isClosed (f : Fin (m + 1) → Finset (CoordinateSpace e)) :
    IsClosed (joinCellCarrier f) :=
  (joinCellCarrier_compact f).isClosed

theorem copy_mem_joinCellCarrier {f : Fin (m + 1) → Finset (CoordinateSpace e)}
    (i : Fin (m + 1)) {v : CoordinateSpace e} (hv : v ∈ f i) :
    polytopalJoinCopy i v ∈ joinCellCarrier f :=
  subset_convexHull ℝ _ (Finset.mem_coe.mpr (copy_mem_joinCellVertices i hv))

/-- The copy of any point of a component face lies in the cell. -/
theorem copy_convexHull_mem_joinCellCarrier
    {f : Fin (m + 1) → Finset (CoordinateSpace e)} (i : Fin (m + 1))
    {x : CoordinateSpace e}
    (hx : x ∈ convexHull ℝ (f i : Set (CoordinateSpace e))) :
    polytopalJoinCopy i x ∈ joinCellCarrier f := by
  have hximage : polytopalJoinCopyAffine i x ∈
      polytopalJoinCopyAffine i '' convexHull ℝ (f i : Set (CoordinateSpace e)) :=
    ⟨x, hx, rfl⟩
  rw [(polytopalJoinCopyAffine i).image_convexHull] at hximage
  apply convexHull_mono (𝕜 := ℝ) _ hximage
  rintro _ ⟨v, hv, rfl⟩
  exact Finset.mem_coe.mpr (copy_mem_joinCellVertices i (Finset.mem_coe.mp hv))

theorem joinCellCarrier_eq_empty {f : Fin (m + 1) → Finset (CoordinateSpace e)}
    (hf : ∀ i, f i = ∅) : joinCellCarrier f = ∅ := by
  have : joinCellVertices f = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨i, v, hv, _⟩ := mem_joinCellVertices.mp hw
    rw [hf i] at hv
    exact absurd hv (Finset.notMem_empty v)
  rw [joinCellCarrier, this]
  simp

theorem joinCellCarrier_nonempty {f : Fin (m + 1) → Finset (CoordinateSpace e)}
    {i : Fin (m + 1)} (hi : (f i).Nonempty) : (joinCellCarrier f).Nonempty := by
  obtain ⟨v, hv⟩ := hi
  exact ⟨_, copy_mem_joinCellCarrier i hv⟩

section TotalWeight

/-- The total join weight of an ambient point, i.e. the sum of the homogenizing
coordinates of all factors. -/
def joinTotalWeight : PolytopalJoinAmbient e m →ₗ[ℝ] ℝ where
  toFun z := ∑ i, (z i).2
  map_add' z w := by
    simp only [Pi.add_apply, Prod.snd_add]
    exact Finset.sum_add_distrib
  map_smul' a z := by
    simp only [Pi.smul_apply, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]

@[simp]
theorem joinTotalWeight_apply (z : PolytopalJoinAmbient e m) :
    joinTotalWeight z = ∑ i, (z i).2 :=
  rfl

@[simp]
theorem joinTotalWeight_copy (i : Fin (m + 1)) (x : CoordinateSpace e) :
    joinTotalWeight (polytopalJoinCopy (m := m) i x) = 1 := by
  classical
  rw [joinTotalWeight_apply, Finset.sum_eq_single i]
  · simp [polytopalJoinCopy]
  · intro j _hj hji
    simp [polytopalJoinCopy, Pi.single_eq_of_ne hji]
  · simp

/-- Every point of a join cell has total weight one. -/
theorem joinTotalWeight_eq_one_of_mem_joinCellCarrier
    {f : Fin (m + 1) → Finset (CoordinateSpace e)}
    {z : PolytopalJoinAmbient e m} (hz : z ∈ joinCellCarrier f) :
    joinTotalWeight z = 1 := by
  have hsub : joinCellCarrier f ⊆ {z : PolytopalJoinAmbient e m | joinTotalWeight z = 1} := by
    apply convexHull_min
    · intro w hw
      obtain ⟨i, v, _hv, rfl⟩ := mem_joinCellVertices.mp (Finset.mem_coe.mp hw)
      exact joinTotalWeight_copy i v
    · intro u hu v hv a b _ha _hb hab
      have hu' : joinTotalWeight u = 1 := hu
      have hv' : joinTotalWeight v = 1 := hv
      change joinTotalWeight (a • u + b • v) = 1
      rw [map_add, map_smul, map_smul, hu', hv']
      simp [smul_eq_mul, hab]
  exact hsub hz

end TotalWeight

section Assembly

/-- The `j`-th coordinate of a weighted sum of Cayley copies. -/
theorem sum_smul_copy_apply (t : Fin (m + 1) → ℝ) (x : Fin (m + 1) → CoordinateSpace e)
    (j : Fin (m + 1)) :
    (∑ i, t i • polytopalJoinCopy i (x i)) j = (t j • x j, t j) := by
  classical
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp [polytopalJoinCopy, Prod.smul_mk]
  · intro i _hi hij
    simp [polytopalJoinCopy, Pi.single_eq_of_ne (Ne.symm hij)]
  · simp

/-- Barycentric data with points in the component faces assembles to a point of
the cell. -/
theorem sum_smul_copy_mem_joinCellCarrier {f : Fin (m + 1) → Finset (CoordinateSpace e)}
    (t : Fin (m + 1) → ℝ) (x : Fin (m + 1) → CoordinateSpace e)
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∑ i, t i = 1)
    (hx : ∀ i, 0 < t i → x i ∈ convexHull ℝ (f i : Set (CoordinateSpace e))) :
    (∑ i, t i • polytopalJoinCopy i (x i)) ∈ joinCellCarrier f := by
  classical
  have hsum_ne : (∑ i : Fin (m + 1), t i) ≠ 0 := by
    rw [ht1]; norm_num
  obtain ⟨i₀, _hi₀, hi₀ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  have hi₀pos : 0 < t i₀ := lt_of_le_of_ne (ht0 i₀) (Ne.symm hi₀ne)
  set q₀ : PolytopalJoinAmbient e m := polytopalJoinCopy i₀ (x i₀) with hq₀def
  have hq₀ : q₀ ∈ joinCellCarrier f :=
    copy_convexHull_mem_joinCellCarrier i₀ (hx i₀ hi₀pos)
  set q : Fin (m + 1) → PolytopalJoinAmbient e m := fun i ↦
    if t i = 0 then q₀ else polytopalJoinCopy i (x i) with hqdef
  have hq : ∀ i, q i ∈ joinCellCarrier f := by
    intro i
    by_cases hi : t i = 0
    · simpa [hqdef, hi] using hq₀
    · have hpos : 0 < t i := lt_of_le_of_ne (ht0 i) (fun h ↦ hi h.symm)
      rw [show q i = polytopalJoinCopy i (x i) by simp [hqdef, hi]]
      exact copy_convexHull_mem_joinCellCarrier i (hx i hpos)
  have hmem := (joinCellCarrier_convex f).sum_mem
    (t := Finset.univ) (w := t) (z := q) (fun i _hi ↦ ht0 i) ht1 (fun i _hi ↦ hq i)
  have heq : ∑ i, t i • q i = ∑ i, t i • polytopalJoinCopy i (x i) := by
    refine Finset.sum_congr rfl fun i _hi ↦ ?_
    by_cases hi : t i = 0
    · simp [hqdef, hi]
    · simp [hqdef, hi]
  rwa [heq] at hmem

end Assembly

section Decomposition

variable {f : Fin (m + 1) → Finset (CoordinateSpace e)}

/-- The Cayley vertex images of distinct factors of a cell are disjoint. -/
theorem joinCell_pairwiseDisjoint_vertexImages (f : Fin (m + 1) → Finset (CoordinateSpace e)) :
    ((Finset.univ : Finset (Fin (m + 1))) : Set (Fin (m + 1))).PairwiseDisjoint
      fun i ↦ (f i).image (polytopalJoinCopy (m := m) i) := by
  classical
  intro i _hi j _hj hij
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  rintro y hy hy'
  rw [Finset.mem_image] at hy hy'
  obtain ⟨u, _hu, rfl⟩ := hy
  obtain ⟨v, _hv, hv'⟩ := hy'
  exact polytopalJoinCopy_ne_of_index_ne hij u v hv'.symm

/-- A sum over the Cayley vertices of a cell splits into a sum over the factors. -/
theorem sum_joinCellVertices_eq {M : Type*} [AddCommMonoid M]
    (f : Fin (m + 1) → Finset (CoordinateSpace e)) (g : PolytopalJoinAmbient e m → M) :
    ∑ y ∈ joinCellVertices f, g y = ∑ i, ∑ v ∈ f i, g (polytopalJoinCopy i v) := by
  classical
  rw [joinCellVertices, Finset.sum_biUnion (joinCell_pairwiseDisjoint_vertexImages f)]
  exact Finset.sum_congr rfl fun i _hi ↦
    Finset.sum_image fun _u _hu _v _hv h ↦ polytopalJoinCopy_injective i h

/-- Every point of a join cell has barycentric data: nonnegative factor weights
summing to one, together with a point of the corresponding component face in
each factor of positive weight. -/
theorem exists_repr_of_mem_joinCellCarrier {z : PolytopalJoinAmbient e m}
    (hz : z ∈ joinCellCarrier f) :
    ∃ t : Fin (m + 1) → ℝ, ∃ x : Fin (m + 1) → CoordinateSpace e,
      (∀ i, 0 ≤ t i) ∧ (∑ i, t i = 1) ∧
      (∀ i, 0 < t i → x i ∈ convexHull ℝ (f i : Set (CoordinateSpace e))) ∧
      z = ∑ i, t i • polytopalJoinCopy i (x i) := by
  classical
  rw [joinCellCarrier, Finset.convexHull_eq] at hz
  obtain ⟨a, ha0, ha1, hacm⟩ := hz
  rw [Finset.centerMass_eq_of_sum_1 _ _ ha1] at hacm
  simp only [id_eq] at hacm
  set b : Fin (m + 1) → CoordinateSpace e → ℝ := fun i v ↦ a (polytopalJoinCopy i v) with hbdef
  set t : Fin (m + 1) → ℝ := fun i ↦ ∑ v ∈ f i, b i v with htdef
  have hb0 : ∀ i, ∀ v ∈ f i, 0 ≤ b i v := fun i v hv ↦
    ha0 _ (copy_mem_joinCellVertices i hv)
  have ht0 : ∀ i, 0 ≤ t i := fun i ↦ Finset.sum_nonneg (hb0 i)
  have ht1 : ∑ i, t i = 1 := by
    rw [htdef, ← sum_joinCellVertices_eq f a]
    exact ha1
  set x : Fin (m + 1) → CoordinateSpace e :=
    fun i ↦ if t i = 0 then 0 else (f i).centerMass (b i) id with hxdef
  have hxface : ∀ i, 0 < t i → x i ∈ convexHull ℝ (f i : Set (CoordinateSpace e)) := by
    intro i hi
    rw [hxdef]
    simp only [hi.ne', ↓reduceIte]
    exact Finset.centerMass_mem_convexHull _ (hb0 i) hi (fun v hv ↦ Finset.mem_coe.mpr hv)
  refine ⟨t, x, ht0, ht1, hxface, ?_⟩
  rw [← hacm, sum_joinCellVertices_eq f fun y ↦ a y • y]
  refine Finset.sum_congr rfl fun i _hi ↦ ?_
  have hgroup : ∑ v ∈ f i, a (polytopalJoinCopy i v) • polytopalJoinCopy i v =
      Pi.single i ((∑ v ∈ f i, b i v • v), t i) := by
    rw [htdef]
    exact sum_smul_polytopalJoinCopy i _ (b i)
  rw [hgroup, smul_polytopalJoinCopy]
  by_cases hi : t i = 0
  · have hsz : ∑ v ∈ f i, b i v • v = 0 := by
      refine Finset.sum_eq_zero fun v hv ↦ ?_
      rw [(Finset.sum_eq_zero_iff_of_nonneg (hb0 i)).mp hi v hv, zero_smul]
    rw [hi, hsz, zero_smul]
  · have hnorm : t i • x i = ∑ v ∈ f i, b i v • v := by
      rw [hxdef]
      simp only [hi, ↓reduceIte, Finset.centerMass, smul_smul, id_eq]
      rw [mul_inv_cancel₀ hi, one_smul]
    rw [hnorm]

end Decomposition

end AffineTverberg

