import AffineTverberg.PolytopalDeletedJoin

set_option linter.style.header false

/-!
# The cell structure of the polytopal deleted join

The deleted join `D` of `PolytopalDeletedJoin.lean` is the finite union of
the Cayley cells `C.carrier`, one for each tuple `C` of pairwise disjoint
exposed faces of `P`.  This file establishes the combinatorial structure of
that family, which is what turns it into an honest cell complex:

* `homogenizedCone K` is the cone of pairs `(t x, t)` with `t ≥ 0`, `x ∈ K`
  (together with the origin), the homogenization used by the Cayley trick;
* `PolytopalDeletedCellIndex.carrier_eq_cellSet` describes a Cayley cell
  factorwise: `z` lies in the cell of the faces `F i` if and only if every
  component `z i` lies in the homogenized cone of `F i` and the homogenizing
  coordinates sum to one;
* consequently the family of cells is closed under intersection
  (`interCell_carrier`), the intersection of the cells through a point being
  again a cell;
* hence every point of `D` lies in a unique smallest cell,
  `minimalCell`, which is contained in every cell containing the point.

The last statement is the finite-choice minimality input required by
`FaceIncidenceFiberData`.
-/

noncomputable section

open Set

namespace AffineTverberg

/-! ## Homogenized cones -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The homogenization of a set `K`: all pairs `(t x, t)` with `t ≥ 0` and
`x ∈ K`, together with the origin. -/
def homogenizedCone (K : Set E) : Set (E × ℝ) :=
  {p | 0 ≤ p.2 ∧ (p.2 = 0 → p.1 = 0) ∧ (0 < p.2 → p.2⁻¹ • p.1 ∈ K)}

theorem mem_homogenizedCone_iff {K : Set E} {p : E × ℝ} :
    p ∈ homogenizedCone K ↔
      0 ≤ p.2 ∧ (p.2 = 0 → p.1 = 0) ∧ (0 < p.2 → p.2⁻¹ • p.1 ∈ K) :=
  Iff.rfl

theorem zero_mem_homogenizedCone (K : Set E) :
    (0 : E × ℝ) ∈ homogenizedCone K :=
  ⟨le_refl 0, fun _ ↦ rfl, fun h ↦ absurd h (lt_irrefl 0)⟩

theorem mem_homogenizedCone_smul {K : Set E} {x : E} (hx : x ∈ K) {t : ℝ}
    (ht : 0 ≤ t) : ((t • x, t) : E × ℝ) ∈ homogenizedCone K := by
  refine ⟨ht, fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only at h ⊢
    simp [h]
  · simp only
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt h), one_smul]
    exact hx

theorem mem_homogenizedCone_one {K : Set E} {x : E} (hx : x ∈ K) :
    ((x, (1 : ℝ)) : E × ℝ) ∈ homogenizedCone K := by
  simpa using mem_homogenizedCone_smul hx zero_le_one

theorem homogenizedCone_mono {K L : Set E} (h : K ⊆ L) :
    homogenizedCone K ⊆ homogenizedCone L :=
  fun _p hp ↦ ⟨hp.1, hp.2.1, fun hpos ↦ h (hp.2.2 hpos)⟩

theorem homogenizedCone_convex {K : Set E} (hK : Convex ℝ K) :
    Convex ℝ (homogenizedCone K) := by
  rintro p ⟨hp2, hp0, hppos⟩ q ⟨hq2, hq0, hqpos⟩ a b ha hb hab
  have hap : 0 ≤ a * p.2 := mul_nonneg ha hp2
  have hbq : 0 ≤ b * q.2 := mul_nonneg hb hq2
  have hs2 : (a • p + b • q).2 = a * p.2 + b * q.2 := by simp [smul_eq_mul]
  have hs1 : (a • p + b • q).1 = a • p.1 + b • q.1 := by simp
  have hzero1 : a * p.2 = 0 → a • p.1 = 0 := by
    intro h
    rcases mul_eq_zero.1 h with h' | h'
    · simp [h']
    · simp [hp0 h']
  have hzero2 : b * q.2 = 0 → b • q.1 = 0 := by
    intro h
    rcases mul_eq_zero.1 h with h' | h'
    · simp [h']
    · simp [hq0 h']
  refine ⟨by rw [hs2]; positivity, ?_, ?_⟩
  · intro h
    rw [hs2] at h
    have h1 : a * p.2 = 0 := by linarith
    have h2 : b * q.2 = 0 := by linarith
    rw [hs1, hzero1 h1, hzero2 h2, add_zero]
  · intro h
    rw [hs2] at h
    rw [hs1, hs2]
    rcases eq_or_lt_of_le hap with h1 | h1
    · have hbpos : 0 < b * q.2 := by linarith
      have hbpos' : 0 < b := by nlinarith
      have hqp : 0 < q.2 := by nlinarith
      rw [hzero1 h1.symm, zero_add, smul_smul]
      have hcoef : (a * p.2 + b * q.2)⁻¹ * b = q.2⁻¹ := by
        rw [← h1, zero_add]
        field_simp
      rw [hcoef]
      exact hqpos hqp
    · rcases eq_or_lt_of_le hbq with h2 | h2
      · have hppos2 : 0 < p.2 := by nlinarith
        rw [hzero2 h2.symm, add_zero, smul_smul]
        have hcoef : (a * p.2 + b * q.2)⁻¹ * a = p.2⁻¹ := by
          rw [← h2, add_zero]
          have ha0 : a ≠ 0 := by nlinarith
          field_simp
        rw [hcoef]
        exact hppos hppos2
      · have hp2pos : 0 < p.2 := by nlinarith
        have hq2pos : 0 < q.2 := by nlinarith
        have hapos : 0 < a := by nlinarith
        have hbpos : 0 < b := by nlinarith
        have hx := hppos hp2pos
        have hy := hqpos hq2pos
        have hspos : 0 < a * p.2 + b * q.2 := by linarith
        have key := hK hx hy (a := (a * p.2 + b * q.2)⁻¹ * (a * p.2))
          (b := (a * p.2 + b * q.2)⁻¹ * (b * q.2))
          (by positivity) (by positivity) (by field_simp)
        have e1 : ((a * p.2 + b * q.2)⁻¹ * (a * p.2)) • (p.2⁻¹ • p.1)
            = (a * p.2 + b * q.2)⁻¹ • (a • p.1) := by
          rw [smul_smul, smul_smul]
          congr 1
          field_simp
        have e2 : ((a * p.2 + b * q.2)⁻¹ * (b * q.2)) • (q.2⁻¹ • q.1)
            = (a * p.2 + b * q.2)⁻¹ • (b • q.1) := by
          rw [smul_smul, smul_smul]
          congr 1
          field_simp
        rw [e1, e2, ← smul_add] at key
        exact key

/-! ## The factorwise description of a Cayley cell -/

section Cells

variable {n m : ℕ} {P : FullDimensionalPolytope n}

@[simp]
theorem polytopalJoinCopy_apply_self (i : Fin (m + 1)) (x : CoordinateSpace n) :
    (polytopalJoinCopy (m := m) i x) i = (x, 1) := by
  simp [polytopalJoinCopy]

theorem polytopalJoinCopy_apply_of_ne {i j : Fin (m + 1)} (hij : j ≠ i)
    (x : CoordinateSpace n) : (polytopalJoinCopy (m := m) i x) j = 0 := by
  simp [polytopalJoinCopy, Pi.single_eq_of_ne hij]

theorem sum_snd_polytopalJoinCopy (i : Fin (m + 1)) (x : CoordinateSpace n) :
    ∑ j : Fin (m + 1), ((polytopalJoinCopy (m := m) i x) j).2 = 1 := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [polytopalJoinCopy_apply_of_ne hji]
  · simp

namespace PolytopalDeletedCellIndex

variable (C : PolytopalDeletedCellIndex P m)

/-- The factorwise description of a Cayley cell: componentwise membership in
the homogenized cones of the component faces, with homogenizing coordinates
summing to one. -/
def cellSet : Set (PolytopalJoinAmbient n m) :=
  {z | (∀ i, z i ∈ homogenizedCone (C.1 i).carrier) ∧ ∑ i, (z i).2 = 1}

theorem cellSet_convex : Convex ℝ C.cellSet := by
  rintro z ⟨hz, hz1⟩ w ⟨hw, hw1⟩ a b ha hb hab
  constructor
  · intro i
    have hzi : z i ∈ homogenizedCone (C.1 i).carrier := hz i
    have hwi : w i ∈ homogenizedCone (C.1 i).carrier := hw i
    have := homogenizedCone_convex (C.1 i).convex hzi hwi ha hb hab
    simpa using this
  · have : ∀ i : Fin (m + 1), ((a • z + b • w) i).2 = a * (z i).2 + b * (w i).2 := by
      intro i
      simp [smul_eq_mul]
    rw [Finset.sum_congr rfl fun i _ ↦ this i, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hz1, hw1, mul_one, mul_one, hab]

theorem vertices_subset_cellSet :
    (C.vertices : Set (PolytopalJoinAmbient n m)) ⊆ C.cellSet := by
  classical
  intro v hv
  rw [Finset.mem_coe, vertices, Finset.mem_biUnion] at hv
  obtain ⟨i, _hi, hv⟩ := hv
  rw [Finset.mem_image] at hv
  obtain ⟨x, hx, rfl⟩ := hv
  have hxface : x ∈ (C.1 i).carrier :=
    subset_convexHull ℝ ((C.1 i).1.1 : Set (CoordinateSpace n))
      (Finset.mem_coe.mpr hx)
  refine ⟨fun j ↦ ?_, sum_snd_polytopalJoinCopy i x⟩
  by_cases hji : j = i
  · subst hji
    rw [polytopalJoinCopy_apply_self]
    exact mem_homogenizedCone_one hxface
  · rw [polytopalJoinCopy_apply_of_ne hji]
    exact zero_mem_homogenizedCone _

/-- **The factorwise description of a Cayley cell.** -/
theorem carrier_eq_cellSet : C.carrier = C.cellSet := by
  classical
  apply Subset.antisymm
  · exact convexHull_min C.vertices_subset_cellSet C.cellSet_convex
  · rintro z ⟨hcone, hsum⟩
    -- some homogenizing coordinate is positive
    have hexists : ∃ i, 0 < (z i).2 := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      have hzero : ∀ i : Fin (m + 1), (z i).2 = 0 := fun i ↦
        le_antisymm (hcon i) (hcone i).1
      rw [Finset.sum_congr rfl fun i _ ↦ hzero i] at hsum
      simp at hsum
    obtain ⟨i₀, hi₀⟩ := hexists
    have hx₀ : (z i₀).2⁻¹ • (z i₀).1 ∈ (C.1 i₀).carrier := (hcone i₀).2.2 hi₀
    set q : Fin (m + 1) → PolytopalJoinAmbient n m := fun i ↦
      if 0 < (z i).2 then polytopalJoinCopy i ((z i).2⁻¹ • (z i).1)
      else polytopalJoinCopy i₀ ((z i₀).2⁻¹ • (z i₀).1) with hq_def
    have hq : ∀ i, q i ∈ C.carrier := by
      intro i
      by_cases hi : 0 < (z i).2
      · rw [hq_def]
        simp only [hi, ite_true]
        exact C.copy_mem_carrier i ((hcone i).2.2 hi)
      · rw [hq_def]
        simp only [hi, ite_false]
        exact C.copy_mem_carrier i₀ hx₀
    have hrepr : ∑ i, (z i).2 • q i = z := by
      funext j
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single j]
      · by_cases hj : 0 < (z j).2
        · rw [hq_def]
          simp only [hj, ite_true, Pi.smul_apply, polytopalJoinCopy_apply_self]
          rw [Prod.smul_mk, smul_smul, mul_inv_cancel₀ (ne_of_gt hj), one_smul,
            smul_eq_mul, mul_one]
        · have hj0 : (z j).2 = 0 := le_antisymm (not_lt.1 hj) (hcone j).1
          have hj1 : (z j).1 = 0 := (hcone j).2.1 hj0
          rw [hj0, zero_smul]
          exact (Prod.ext hj1 hj0).symm
      · intro i _hi hij
        by_cases hi : 0 < (z i).2
        · rw [hq_def]
          simp only [hi, ite_true, Pi.smul_apply,
            polytopalJoinCopy_apply_of_ne hij.symm, smul_zero]
        · have hi0 : (z i).2 = 0 := le_antisymm (not_lt.1 hi) (hcone i).1
          rw [hi0, zero_smul]
          rfl
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [← hrepr]
    exact C.convex.sum_mem (fun i _hi ↦ (hcone i).1) hsum (fun i _hi ↦ hq i)

theorem mem_carrier_iff {z : PolytopalJoinAmbient n m} :
    z ∈ C.carrier ↔
      (∀ i, z i ∈ homogenizedCone (C.1 i).carrier) ∧ ∑ i, (z i).2 = 1 := by
  rw [C.carrier_eq_cellSet]
  exact Iff.rfl

theorem carrier_subset_deletedJoinCarrier :
    C.carrier ⊆ polytopalDeletedJoinCarrier P m :=
  subset_iUnion (fun C : PolytopalDeletedCellIndex P m ↦ C.carrier) C

/-- Cayley cells are monotone in their component faces. -/
theorem carrier_mono {C D : PolytopalDeletedCellIndex P m}
    (h : ∀ i, (C.1 i).carrier ⊆ (D.1 i).carrier) : C.carrier ⊆ D.carrier := by
  intro z hz
  rw [mem_carrier_iff] at hz ⊢
  exact ⟨fun i ↦ homogenizedCone_mono (h i) (hz.1 i), hz.2⟩

end PolytopalDeletedCellIndex

/-! ## Faces of `P` are closed under finite intersection -/

theorem PolytopeFaceIndex.carrier_subset_polytope (F : PolytopeFaceIndex P) :
    F.carrier ⊆ P.carrier := by
  refine convexHull_mono ?_
  intro v hv
  exact Finset.mem_coe.mpr (Finset.mem_powerset.mp F.1.2 (Finset.mem_coe.mp hv))

variable (P) in
/-- The intersection of the `i`-th component faces of a finite family of
cells (intersected with `P` so that the empty family gives `P` itself). -/
def interFaces (S : Finset (PolytopalDeletedCellIndex P m)) (i : Fin (m + 1)) :
    Set (CoordinateSpace n) :=
  P.carrier ∩ ⋂ C ∈ S, (C.1 i).carrier

theorem interFaces_isFace (S : Finset (PolytopalDeletedCellIndex P m))
    (i : Fin (m + 1)) : P.IsFace (interFaces P S i) := by
  classical
  induction S using Finset.induction with
  | empty =>
      have h : interFaces P (∅ : Finset (PolytopalDeletedCellIndex P m)) i
          = P.carrier := by
        simp [interFaces]
      rw [h]
      exact IsExposed.refl _
  | insert C S _hC ih =>
      have h : interFaces P (insert C S) i
          = (C.1 i).carrier ∩ interFaces P S i := by
        rw [interFaces, interFaces]
        ext x
        simp only [mem_inter_iff, mem_iInter, Finset.mem_insert]
        constructor
        · rintro ⟨hxP, hx⟩
          exact ⟨hx C (Or.inl rfl), hxP, fun D hD ↦ hx D (Or.inr hD)⟩
        · rintro ⟨hxC, hxP, hx⟩
          refine ⟨hxP, ?_⟩
          rintro D (rfl | hD)
          · exact hxC
          · exact hx D hD
      rw [h]
      exact (C.1 i).isFace.inter ih

theorem interFaces_subset {S : Finset (PolytopalDeletedCellIndex P m)}
    {C : PolytopalDeletedCellIndex P m} (hC : C ∈ S) (i : Fin (m + 1)) :
    interFaces P S i ⊆ (C.1 i).carrier := by
  intro x hx
  exact (mem_iInter₂.1 hx.2) C hC

/-- The intersection of a nonempty finite family of Cayley cells, again a
Cayley cell. -/
def interCell {S : Finset (PolytopalDeletedCellIndex P m)} (hS : S.Nonempty) :
    PolytopalDeletedCellIndex P m := by
  refine ⟨fun i ↦ PolytopeFaceIndex.ofFace (interFaces P S i)
    (interFaces_isFace S i), ?_⟩
  obtain ⟨C, hC⟩ := hS
  intro i j hij
  rw [PolytopeFaceIndex.carrier_ofFace, PolytopeFaceIndex.carrier_ofFace]
  exact Disjoint.mono (interFaces_subset hC i) (interFaces_subset hC j)
    (C.2 hij)

theorem interCell_face {S : Finset (PolytopalDeletedCellIndex P m)}
    (hS : S.Nonempty) (i : Fin (m + 1)) :
    ((interCell hS).1 i).carrier = interFaces P S i := by
  change (PolytopeFaceIndex.ofFace (interFaces P S i)
    (interFaces_isFace S i)).carrier = interFaces P S i
  exact PolytopeFaceIndex.carrier_ofFace _ _

/-- **The family of Cayley cells is closed under intersection.** -/
theorem interCell_carrier {S : Finset (PolytopalDeletedCellIndex P m)}
    (hS : S.Nonempty) : (interCell hS).carrier = ⋂ C ∈ S, C.carrier := by
  have hex : ∃ C, C ∈ S := hS
  have hface : ∀ i : Fin (m + 1),
      ((interCell hS).1 i).carrier = interFaces P S i := interCell_face hS
  obtain ⟨C₀, hC₀⟩ := hex
  ext z
  rw [PolytopalDeletedCellIndex.mem_carrier_iff]
  simp only [mem_iInter, hface]
  constructor
  · rintro ⟨hcone, hsum⟩ C hC
    rw [PolytopalDeletedCellIndex.mem_carrier_iff]
    exact ⟨fun i ↦ homogenizedCone_mono (interFaces_subset hC i) (hcone i), hsum⟩
  · intro h
    have h₀ := h C₀ hC₀
    rw [PolytopalDeletedCellIndex.mem_carrier_iff] at h₀
    refine ⟨fun i ↦ ⟨(h₀.1 i).1, (h₀.1 i).2.1, fun hpos ↦ ?_⟩, h₀.2⟩
    refine ⟨PolytopeFaceIndex.carrier_subset_polytope _ ((h₀.1 i).2.2 hpos), ?_⟩
    refine mem_iInter₂.2 fun C hC ↦ ?_
    have hC' := h C hC
    rw [PolytopalDeletedCellIndex.mem_carrier_iff] at hC'
    exact (hC'.1 i).2.2 hpos

/-! ## The minimal cell through a point -/

variable (P) in
/-- The finite set of Cayley cells containing a given point. -/
def cellsThrough (z : PolytopalJoinAmbient n m) :
    Finset (PolytopalDeletedCellIndex P m) := by
  classical
  exact Finset.univ.filter fun C ↦ z ∈ C.carrier

theorem mem_cellsThrough_iff {z : PolytopalJoinAmbient n m}
    {C : PolytopalDeletedCellIndex P m} :
    C ∈ cellsThrough P z ↔ z ∈ C.carrier := by
  classical
  simp [cellsThrough]

theorem cellsThrough_nonempty {z : PolytopalJoinAmbient n m}
    (hz : z ∈ polytopalDeletedJoinCarrier P m) : (cellsThrough P z).Nonempty := by
  obtain ⟨C, hC⟩ := mem_iUnion.1 hz
  exact ⟨C, mem_cellsThrough_iff.2 hC⟩

variable (P) in
/-- **The minimal Cayley cell containing a point of the deleted join**: the
intersection of all cells through the point, which is again a cell. -/
def minimalCell {z : PolytopalJoinAmbient n m}
    (hz : z ∈ polytopalDeletedJoinCarrier P m) :
    PolytopalDeletedCellIndex P m :=
  interCell (cellsThrough_nonempty hz)

theorem minimalCell_carrier {z : PolytopalJoinAmbient n m}
    (hz : z ∈ polytopalDeletedJoinCarrier P m) :
    (minimalCell P hz).carrier = ⋂ C ∈ cellsThrough P z, C.carrier :=
  interCell_carrier _

theorem mem_minimalCell {z : PolytopalJoinAmbient n m}
    (hz : z ∈ polytopalDeletedJoinCarrier P m) :
    z ∈ (minimalCell P hz).carrier := by
  rw [minimalCell_carrier]
  exact mem_iInter₂.2 fun C hC ↦ mem_cellsThrough_iff.1 hC

theorem minimalCell_subset {z : PolytopalJoinAmbient n m}
    (hz : z ∈ polytopalDeletedJoinCarrier P m)
    (C : PolytopalDeletedCellIndex P m) (hC : z ∈ C.carrier) :
    (minimalCell P hz).carrier ⊆ C.carrier := by
  rw [minimalCell_carrier]
  exact biInter_subset_of_mem (mem_cellsThrough_iff.2 hC)

end Cells

end AffineTverberg

