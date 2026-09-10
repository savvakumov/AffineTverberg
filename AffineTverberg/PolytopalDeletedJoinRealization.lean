import AffineTverberg.PolytopalDeletedJoin

set_option linter.style.header false

/-!
# Realizing points of the concrete polytopal deleted join

`AffineTverberg/PolytopalDeletedJoin.lean` shows that every represented
deleted-join point `z : PolytopeDeletedJoinPoint P` realizes to a point of
the concrete compact set `polytopalDeletedJoinCarrier P m`.  This file proves
the converse: every point of a Cayley cell `C.carrier` is the realization of
some `PolytopeDeletedJoinPoint` whose supporting faces are exactly the
component faces of `C`, and hence every point of
`polytopalDeletedJoinCarrier P m` admits a witness.

The argument writes a point of the cell as a finite convex combination of the
Cayley vertices of the cell, groups the coefficients by join factor, and
normalizes each group of positive total weight to a point of the corresponding
component face.  An arbitrary vertex of `P` is used in the factors whose total
weight vanishes; the deleted-join witness structure only constrains the chosen
point in factors of positive weight.

As a consequence, a zero of the linear join map `Φ.joinMap` on the concrete
deleted join produces a witness `w` with `Φ.value w = 0`, which is the form in
which `theorem:zero` is stated.
-/

noncomputable section

open Set

namespace AffineTverberg

section CopyLemmas

variable {n m : ℕ}

/-- The Cayley inclusion of a single join factor is injective. -/
theorem polytopalJoinCopy_injective (i : Fin (m + 1)) :
    Function.Injective (polytopalJoinCopy (n := n) (m := m) i) := by
  intro x y h
  have hi := congrFun h i
  rw [polytopalJoinCopy, polytopalJoinCopy, Pi.single_eq_same, Pi.single_eq_same] at hi
  exact congrArg Prod.fst hi

/-- Copies of points in different join factors are different. -/
theorem polytopalJoinCopy_ne_of_index_ne {i j : Fin (m + 1)} (hij : i ≠ j)
    (x y : CoordinateSpace n) :
    polytopalJoinCopy (m := m) i x ≠ polytopalJoinCopy j y := by
  intro h
  have hi := congrFun h i
  rw [polytopalJoinCopy, polytopalJoinCopy, Pi.single_eq_same,
    Pi.single_eq_of_ne hij] at hi
  exact one_ne_zero (congrArg Prod.snd hi)

/-- A weighted sum of copies inside one join factor is the copy determined by
the weighted sum of the points and the total weight. -/
theorem sum_smul_polytopalJoinCopy (i : Fin (m + 1))
    (s : Finset (CoordinateSpace n)) (b : CoordinateSpace n → ℝ) :
    ∑ v ∈ s, b v • polytopalJoinCopy (m := m) i v =
      Pi.single i ((∑ v ∈ s, b v • v), (∑ v ∈ s, b v)) := by
  classical
  induction s using Finset.induction with
  | empty => simp [Prod.mk_zero_zero]
  | insert v s hv ih =>
      rw [Finset.sum_insert hv, Finset.sum_insert hv, Finset.sum_insert hv, ih,
        polytopalJoinCopy, ← Pi.single_smul, ← Pi.single_add]
      congr 1
      simp

/-- Scaling a copy of a point. -/
theorem smul_polytopalJoinCopy (i : Fin (m + 1)) (c : ℝ) (x : CoordinateSpace n) :
    c • polytopalJoinCopy (m := m) i x = Pi.single i (c • x, c) := by
  rw [polytopalJoinCopy, ← Pi.single_smul]
  congr 1
  simp

end CopyLemmas

namespace PolytopeFaceIndex

variable {n : ℕ} {P : FullDimensionalPolytope n}

/-- A face of `P` is contained in `P`. -/
theorem carrier_subset (F : PolytopeFaceIndex P) : F.carrier ⊆ P.carrier := by
  apply convexHull_mono
  intro v hv
  exact Finset.mem_coe.mpr (Finset.mem_powerset.mp F.1.2 (Finset.mem_coe.mp hv))

end PolytopeFaceIndex

namespace PolytopalDeletedCellIndex

variable {n m : ℕ} {P : FullDimensionalPolytope n}

/-- The Cayley vertex images of distinct factors of a cell are disjoint. -/
theorem pairwiseDisjoint_vertexImages (C : PolytopalDeletedCellIndex P m) :
    ((Finset.univ : Finset (Fin (m + 1))) : Set (Fin (m + 1))).PairwiseDisjoint
      fun i ↦ (C.1 i).1.1.image (polytopalJoinCopy (m := m) i) := by
  classical
  intro i _hi j _hj hij
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  rintro y hy hy'
  rw [Finset.mem_image] at hy hy'
  obtain ⟨u, _hu, rfl⟩ := hy
  obtain ⟨v, _hv, hv'⟩ := hy'
  exact polytopalJoinCopy_ne_of_index_ne hij u v hv'.symm

/-- A sum over the Cayley vertices of a cell splits as an iterated sum over the
component faces. -/
theorem sum_vertices_eq (C : PolytopalDeletedCellIndex P m) {M : Type*}
    [AddCommMonoid M] (f : PolytopalJoinAmbient n m → M) :
    ∑ y ∈ C.vertices, f y = ∑ i, ∑ v ∈ (C.1 i).1.1, f (polytopalJoinCopy i v) := by
  classical
  rw [PolytopalDeletedCellIndex.vertices,
    Finset.sum_biUnion C.pairwiseDisjoint_vertexImages]
  exact Finset.sum_congr rfl fun i _hi ↦
    Finset.sum_image fun _u _hu _v _hv h ↦ polytopalJoinCopy_injective i h

/-- Every point of a Cayley cell is the realization of a deleted-join witness
whose supporting faces are the component faces of the cell. -/
theorem exists_realization_eq_of_mem_carrier (C : PolytopalDeletedCellIndex P m)
    {z : PolytopalJoinAmbient n m} (hz : z ∈ C.carrier) :
    ∃ w : PolytopeDeletedJoinPoint (m := m) P,
      (∀ i, w.face i = (C.1 i).carrier) ∧ w.realization = z := by
  classical
  obtain ⟨p₀, hp₀v⟩ := P.vertices_nonempty
  have hp₀ : p₀ ∈ P.carrier :=
    subset_convexHull ℝ (P.vertices : Set (CoordinateSpace n)) (Finset.mem_coe.mpr hp₀v)
  rw [PolytopalDeletedCellIndex.carrier, Finset.convexHull_eq] at hz
  obtain ⟨a, ha0, ha1, hacm⟩ := hz
  rw [Finset.centerMass_eq_of_sum_1 _ _ ha1] at hacm
  simp only [id_eq] at hacm
  -- Coefficients grouped by join factor.
  set b : Fin (m + 1) → CoordinateSpace n → ℝ :=
    fun i v ↦ a (polytopalJoinCopy i v)
  set t : Fin (m + 1) → ℝ := fun i ↦ ∑ v ∈ (C.1 i).1.1, b i v with htdef
  have hb0 : ∀ i, ∀ v ∈ (C.1 i).1.1, 0 ≤ b i v := by
    intro i v hv
    exact ha0 _ (C.copy_vertex_mem_vertices i hv)
  have ht0 : ∀ i, 0 ≤ t i := fun i ↦ Finset.sum_nonneg (hb0 i)
  have hsumt : ∑ i, t i = 1 := by
    rw [htdef, ← C.sum_vertices_eq a]
    exact ha1
  -- The normalized point of each factor.
  set x : Fin (m + 1) → CoordinateSpace n :=
    fun i ↦ if t i = 0 then p₀ else (C.1 i).1.1.centerMass (b i) id with hxdef
  have hxface : ∀ i, 0 < t i → x i ∈ (C.1 i).carrier := by
    intro i hi
    rw [hxdef]
    simp only [hi.ne', ↓reduceIte]
    exact Finset.centerMass_mem_convexHull _ (hb0 i) hi
      (fun v hv ↦ Finset.mem_coe.mpr hv)
  have hxP : ∀ i, x i ∈ P.carrier := by
    intro i
    by_cases hi : t i = 0
    · rw [hxdef]
      simpa only [hi, ↓reduceIte] using hp₀
    · exact (C.1 i).carrier_subset (hxface i (lt_of_le_of_ne (ht0 i) (Ne.symm hi)))
  refine ⟨{ weight := t
            point := fun i ↦ ⟨x i, hxP i⟩
            face := fun i ↦ (C.1 i).carrier
            weight_nonneg := ht0
            weight_sum := hsumt
            face_isFace := fun i ↦ (C.1 i).isFace
            faces_pairwiseDisjoint := C.2
            point_mem_face := fun i hi ↦ hxface i hi }, fun _ ↦ rfl, ?_⟩
  -- The realization identity.
  change ∑ i, t i • polytopalJoinCopy i (x i) = z
  rw [← hacm, C.sum_vertices_eq fun y ↦ a y • y]
  refine Finset.sum_congr rfl fun i _hi ↦ ?_
  have hgroup : ∑ v ∈ (C.1 i).1.1, a (polytopalJoinCopy i v) • polytopalJoinCopy i v =
      Pi.single i ((∑ v ∈ (C.1 i).1.1, b i v • v), t i) := by
    rw [htdef]
    exact sum_smul_polytopalJoinCopy i _ (b i)
  rw [hgroup, smul_polytopalJoinCopy]
  by_cases hi : t i = 0
  · have hsz : ∑ v ∈ (C.1 i).1.1, b i v • v = 0 := by
      refine Finset.sum_eq_zero fun v hv ↦ ?_
      rw [(Finset.sum_eq_zero_iff_of_nonneg (hb0 i)).mp hi v hv, zero_smul]
    rw [hi, hsz, zero_smul]
  · have hnorm : t i • x i = ∑ v ∈ (C.1 i).1.1, b i v • v := by
      rw [hxdef]
      simp only [hi, ↓reduceIte, Finset.centerMass, smul_smul, id_eq]
      rw [mul_inv_cancel₀ hi, one_smul]
    rw [hnorm]

end PolytopalDeletedCellIndex

variable {n m : ℕ} {P : FullDimensionalPolytope n}

/-- Every point of the concrete polytopal deleted join is the realization of a
represented deleted-join point. -/
theorem exists_realization_eq_of_mem_polytopalDeletedJoinCarrier
    {z : PolytopalJoinAmbient n m} (hz : z ∈ polytopalDeletedJoinCarrier P m) :
    ∃ w : PolytopeDeletedJoinPoint (m := m) P, w.realization = z := by
  rw [polytopalDeletedJoinCarrier] at hz
  obtain ⟨C, hzC⟩ := Set.mem_iUnion.mp hz
  obtain ⟨w, _hface, hw⟩ := C.exists_realization_eq_of_mem_carrier hzC
  exact ⟨w, hw⟩

/-- The concrete polytopal deleted join is exactly the set of realizations of
represented deleted-join points. -/
theorem mem_polytopalDeletedJoinCarrier_iff_exists_realization
    (z : PolytopalJoinAmbient n m) :
    z ∈ polytopalDeletedJoinCarrier P m ↔
      ∃ w : PolytopeDeletedJoinPoint (m := m) P, w.realization = z := by
  constructor
  · exact exists_realization_eq_of_mem_polytopalDeletedJoinCarrier
  · rintro ⟨w, rfl⟩
    exact w.realization_mem_deletedJoinCarrier

/-- The concrete deleted join is the image of the witness-level model under
realization. -/
theorem polytopalDeletedJoinCarrier_eq_range_realization :
    polytopalDeletedJoinCarrier P m =
      Set.range (PolytopeDeletedJoinPoint.realization (m := m) P) := by
  ext z
  rw [mem_polytopalDeletedJoinCarrier_iff_exists_realization]
  exact ⟨fun ⟨w, hw⟩ ↦ ⟨w, hw⟩, fun ⟨w, hw⟩ ↦ ⟨w, hw⟩⟩

namespace PolytopalJoinMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (Φ : PolytopalJoinMap P m V)

/-- A zero of the linear join map on the concrete deleted join yields a
represented deleted-join witness of value zero. -/
theorem exists_value_eq_zero_of_joinMap_eq_zero
    {z : PolytopalJoinAmbient n m} (hz : z ∈ polytopalDeletedJoinCarrier P m)
    (hzero : Φ.joinMap z = 0) :
    ∃ w : PolytopeDeletedJoinPoint (m := m) P, Φ.value w = 0 := by
  obtain ⟨w, hw⟩ := exists_realization_eq_of_mem_polytopalDeletedJoinCarrier hz
  refine ⟨w, ?_⟩
  rw [← Φ.joinMap_realization, hw, hzero]

/-- The witness-level zero statement of `theorem:zero` is equivalent to the
existence of a zero of the linear join map on the concrete compact deleted
join. -/
theorem exists_mem_deletedJoinCarrier_joinMap_eq_zero_iff :
    (∃ z ∈ polytopalDeletedJoinCarrier P m, Φ.joinMap z = 0) ↔
      ∃ w : PolytopeDeletedJoinPoint (m := m) P, Φ.value w = 0 := by
  constructor
  · rintro ⟨z, hz, hzero⟩
    exact Φ.exists_value_eq_zero_of_joinMap_eq_zero hz hzero
  · rintro ⟨w, hw⟩
    refine ⟨w.realization, w.realization_mem_deletedJoinCarrier, ?_⟩
    rw [Φ.joinMap_realization, hw]

end PolytopalJoinMap

/-- The concrete compact-space formulation of the polytopal zero theorem. -/
def polytopalConcreteZeroTheoremStatement : Prop :=
  ∀ (d m : ℕ), 1 ≤ d → 1 ≤ m →
    ∀ (P : FullDimensionalPolytope ((d + 1) * m))
      (Φ : PolytopalJoinMap P m (SarkariaTarget d m)),
      ∃ z ∈ polytopalDeletedJoinCarrier P m, Φ.joinMap z = 0

/-- The concrete compact-space zero theorem is exactly the witness-level
statement used by the Sarkaria deduction. -/
theorem polytopalZeroTheoremStatement_iff_concrete :
    polytopalZeroTheoremStatement ↔ polytopalConcreteZeroTheoremStatement := by
  constructor
  · intro hzero d m hd hm P Φ
    obtain ⟨w, hw⟩ := hzero d m hd hm P Φ
    exact ⟨w.realization, w.realization_mem_deletedJoinCarrier, by
      rw [Φ.joinMap_realization, hw]⟩
  · intro hzero d m hd hm P Φ
    obtain ⟨z, hzD, hz⟩ := hzero d m hd hm P Φ
    exact Φ.exists_value_eq_zero_of_joinMap_eq_zero hzD hz

/-- A proof of the zero theorem on the compact concrete deleted join gives
the polytopal conclusion of the paper's main theorem. -/
theorem polytopalMainTheoremStatement_of_concrete_zero
    (hzero : polytopalConcreteZeroTheoremStatement) :
    polytopalMainTheoremStatement :=
  polytopalMainTheoremStatement_of_zero
    (polytopalZeroTheoremStatement_iff_concrete.mpr hzero)

end AffineTverberg
