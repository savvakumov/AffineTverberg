import AffineTverberg.PolytopalCellStructure
import AffineTverberg.PolytopeFaceTheory

set_option linter.style.header false

/-!
# The Cayley join of an arbitrary tuple of factors and its faces

The cells of `PolytopalDeletedJoin.lean` are Cayley joins of tuples of
*pairwise disjoint* faces.  For the bad-vertex triangulation one needs the
Cayley join of an arbitrary tuple of faces (the faces of the Cayley polytope
`Q = P₁ * ⋯ * P_r` are exactly these), together with a description of *its*
exposed faces.

* `cayleyJoin Fs` is the factorwise homogenized description already used by
  `PolytopalDeletedCellIndex.cellSet`, here for an arbitrary tuple; empty
  factors are allowed and contribute only the zero component.
* `cayleyJoin_eq_convexHull` identifies it with the convex hull of the copied
  factors, so it agrees with all the carriers already in use
  (`cayleyJoin_polytopalJoinCarrier`, `PolytopalDeletedCellIndex.carrier`).
* `exists_exposed_factors_exposedBy` is the **face classification**: every
  exposed face of a Cayley join is the Cayley join of exposed faces of the
  factors (the empty face in the factors which do not attain the maximum).
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg
namespace CayleyJoin

open PolytopeFace

variable {n m : ℕ}

/-- The Cayley join of an arbitrary tuple of factors. -/
def cayleyJoin (Fs : Fin (m + 1) → Set (CoordinateSpace n)) :
    Set (PolytopalJoinAmbient n m) :=
  {z | (∀ i, z i ∈ homogenizedCone (Fs i)) ∧ ∑ i, (z i).2 = 1}

theorem mem_cayleyJoin_iff {Fs : Fin (m + 1) → Set (CoordinateSpace n)}
    {z : PolytopalJoinAmbient n m} :
    z ∈ cayleyJoin Fs ↔
      (∀ i, z i ∈ homogenizedCone (Fs i)) ∧ ∑ i, (z i).2 = 1 := Iff.rfl

theorem cayleyJoin_mono {Fs Gs : Fin (m + 1) → Set (CoordinateSpace n)}
    (h : ∀ i, Fs i ⊆ Gs i) : cayleyJoin Fs ⊆ cayleyJoin Gs :=
  fun _ hz ↦ ⟨fun i ↦ homogenizedCone_mono (h i) (hz.1 i), hz.2⟩

theorem cayleyJoin_convex {Fs : Fin (m + 1) → Set (CoordinateSpace n)}
    (h : ∀ i, Convex ℝ (Fs i)) : Convex ℝ (cayleyJoin Fs) := by
  rintro z ⟨hz, hz1⟩ w ⟨hw, hw1⟩ a b ha hb hab
  constructor
  · intro i
    have := homogenizedCone_convex (h i) (hz i) (hw i) ha hb hab
    simpa using this
  · have hcomp : ∀ i : Fin (m + 1), ((a • z + b • w) i).2 = a * (z i).2 + b * (w i).2 := by
      intro i; simp [smul_eq_mul]
    rw [Finset.sum_congr rfl fun i _ ↦ hcomp i, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hz1, hw1, mul_one, mul_one, hab]

/-- A copied point of a factor lies in the Cayley join, and only there. -/
theorem copy_mem_cayleyJoin_iff {Fs : Fin (m + 1) → Set (CoordinateSpace n)}
    {i : Fin (m + 1)} {x : CoordinateSpace n} :
    polytopalJoinCopy i x ∈ cayleyJoin Fs ↔ x ∈ Fs i := by
  constructor
  · intro hz
    have h := hz.1 i
    rw [polytopalJoinCopy_apply_self] at h
    simpa using h.2.2 (by norm_num)
  · intro hx
    refine ⟨fun j ↦ ?_, sum_snd_polytopalJoinCopy i x⟩
    by_cases hji : j = i
    · subst hji
      rw [polytopalJoinCopy_apply_self]
      exact mem_homogenizedCone_one hx
    · rw [polytopalJoinCopy_apply_of_ne hji]
      exact zero_mem_homogenizedCone _

/-- **The Cayley join is the convex hull of the copied factors.** -/
theorem cayleyJoin_eq_convexHull {Fs : Fin (m + 1) → Set (CoordinateSpace n)}
    (h : ∀ i, Convex ℝ (Fs i)) :
    cayleyJoin Fs = convexHull ℝ (⋃ i, polytopalJoinCopy i '' Fs i) := by
  apply Subset.antisymm
  · rintro z ⟨hcone, hsum⟩
    set A := convexHull ℝ (⋃ i, polytopalJoinCopy i '' Fs i) with hA
    have hAconv : Convex ℝ A := convex_convexHull _ _
    have hmemA : ∀ (i : Fin (m + 1)) {x : CoordinateSpace n}, x ∈ Fs i →
        polytopalJoinCopy i x ∈ A := fun i x hx ↦
      subset_convexHull ℝ _ (mem_iUnion.mpr ⟨i, mem_image_of_mem _ hx⟩)
    have hexists : ∃ i, 0 < (z i).2 := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      have hzero : ∀ i : Fin (m + 1), (z i).2 = 0 := fun i ↦
        le_antisymm (hcon i) (hcone i).1
      rw [Finset.sum_congr rfl fun i _ ↦ hzero i] at hsum
      simp at hsum
    obtain ⟨i₀, hi₀⟩ := hexists
    have hx₀ : (z i₀).2⁻¹ • (z i₀).1 ∈ Fs i₀ := (hcone i₀).2.2 hi₀
    set q : Fin (m + 1) → PolytopalJoinAmbient n m := fun i ↦
      if 0 < (z i).2 then polytopalJoinCopy i ((z i).2⁻¹ • (z i).1)
      else polytopalJoinCopy i₀ ((z i₀).2⁻¹ • (z i₀).1) with hq_def
    have hq : ∀ i, q i ∈ A := by
      intro i
      by_cases hi : 0 < (z i).2
      · rw [hq_def]; simp only [hi, ite_true]
        exact hmemA i ((hcone i).2.2 hi)
      · rw [hq_def]; simp only [hi, ite_false]
        exact hmemA i₀ hx₀
    have hrepr : ∑ i, (z i).2 • q i = z := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
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
          rw [hi0, zero_smul]; rfl
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [← hrepr]
    exact hAconv.sum_mem (fun i _hi ↦ (hcone i).1) hsum (fun i _hi ↦ hq i)
  · apply convexHull_min _ (cayleyJoin_convex h)
    rintro _ hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    obtain ⟨x, hx, rfl⟩ := hi
    exact copy_mem_cayleyJoin_iff.mpr hx

/-- Hull form: the Cayley join of hulls of finite sets is the hull of all
copied generators. -/
theorem cayleyJoin_convexHull_finset (s : Fin (m + 1) → Finset (CoordinateSpace n)) :
    cayleyJoin (fun i ↦ convexHull ℝ (s i : Set (CoordinateSpace n))) =
      convexHull ℝ (⋃ i, polytopalJoinCopy i '' (s i : Set (CoordinateSpace n))) := by
  rw [cayleyJoin_eq_convexHull fun i ↦ convex_convexHull ℝ _]
  apply Subset.antisymm
  · apply convexHull_min _ (convex_convexHull ℝ _)
    rintro x hx
    obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp hx
    have himg : polytopalJoinCopyAffine i '' (convexHull ℝ (s i : Set (CoordinateSpace n)))
        = convexHull ℝ (polytopalJoinCopy i '' (s i : Set (CoordinateSpace n))) := by
      rw [(polytopalJoinCopyAffine i).image_convexHull]
      rfl
    have hmem : polytopalJoinCopy i y ∈
        convexHull ℝ (polytopalJoinCopy i '' (s i : Set (CoordinateSpace n))) := by
      rw [← himg]; exact ⟨y, hy, rfl⟩
    exact convexHull_mono (subset_iUnion _ i) hmem
  · exact convexHull_mono (iUnion_mono fun i ↦ image_mono (subset_convexHull ℝ _))

theorem cayleyJoin_eq_empty_iff {Fs : Fin (m + 1) → Set (CoordinateSpace n)} :
    cayleyJoin Fs = ∅ ↔ ∀ i, Fs i = ∅ := by
  constructor
  · intro h i
    rw [eq_empty_iff_forall_notMem]
    intro x hx
    have hmem : polytopalJoinCopy i x ∈ cayleyJoin Fs := copy_mem_cayleyJoin_iff.mpr hx
    rw [h] at hmem
    exact hmem
  · intro h
    rw [eq_empty_iff_forall_notMem]
    rintro z ⟨hz, hz1⟩
    have hzero : ∀ i : Fin (m + 1), (z i).2 = 0 := by
      intro i
      have hi := hz i
      rw [h i] at hi
      by_contra hne
      exact absurd (hi.2.2 (lt_of_le_of_ne hi.1 (Ne.symm hne))) (by simp)
    rw [Finset.sum_congr rfl fun i _ ↦ hzero i] at hz1
    simp at hz1

/-- Compatibility with the deleted-join cells. -/
theorem cayleyJoin_cell {P : FullDimensionalPolytope n}
    (C : PolytopalDeletedCellIndex P m) :
    C.carrier = cayleyJoin (fun i ↦ (C.1 i).carrier) :=
  C.carrier_eq_cellSet

/-- Compatibility with the full polytopal join. -/
theorem cayleyJoin_polytopalJoinCarrier (P : FullDimensionalPolytope n) :
    polytopalJoinCarrier P m = cayleyJoin (fun _ ↦ P.carrier) := by
  have hvert : (polytopalJoinVertices P m : Set (PolytopalJoinAmbient n m))
      = ⋃ i : Fin (m + 1), polytopalJoinCopy i '' (P.vertices : Set (CoordinateSpace n)) := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_coe, polytopalJoinVertices, Finset.mem_image] at hx
      obtain ⟨⟨i, v⟩, -, rfl⟩ := hx
      exact mem_iUnion.mpr ⟨i, ⟨v.1, Finset.mem_coe.mpr v.2, rfl⟩⟩
    · intro hx
      obtain ⟨i, v, hv, rfl⟩ := mem_iUnion.mp hx
      exact Finset.mem_coe.mpr
        (polytopalJoinCopy_vertex_mem_vertices P i (Finset.mem_coe.mp hv))
  rw [show (fun _ : Fin (m + 1) ↦ P.carrier)
      = fun _ : Fin (m + 1) ↦ convexHull ℝ (P.vertices : Set (CoordinateSpace n)) from rfl,
    cayleyJoin_convexHull_finset, polytopalJoinCarrier, hvert]

/-- The copy map into one join factor is continuous. -/
theorem continuous_polytopalJoinCopy (i : Fin (m + 1)) :
    Continuous (polytopalJoinCopy (n := n) (m := m) i) := by
  have hsplit : polytopalJoinCopy (n := n) (m := m) i
      = fun x ↦ (polytopalJoinCopyLinear (m := m) i x) + Pi.single i (0, 1) := by
    funext x
    simp [polytopalJoinCopy, polytopalJoinCopyLinear, ← Pi.single_add]
  rw [hsplit]
  exact ((polytopalJoinCopyLinear (m := m) i).continuous_of_finiteDimensional).add
    continuous_const

/-- Evaluating a linear functional on a point of a Cayley join: the value is the
convex combination, with the homogenizing weights, of its values at the copied
factor points. -/
theorem l_eval_cayleyJoin (l : PolytopalJoinAmbient n m →L[ℝ] ℝ)
    {Fs : Fin (m + 1) → Set (CoordinateSpace n)} {z : PolytopalJoinAmbient n m}
    (hz : z ∈ cayleyJoin Fs) :
    l z = ∑ i, (z i).2 *
      (if 0 < (z i).2 then l (polytopalJoinCopy i ((z i).2⁻¹ • (z i).1)) else 0) := by
  have hsplit : z = ∑ i, Pi.single i (z i) := (Finset.univ_sum_single z).symm
  calc l z = ∑ i, l (Pi.single i (z i)) := by
        conv_lhs => rw [hsplit]
        rw [map_sum]
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        by_cases hi : 0 < (z i).2
        · have hzi : Pi.single i (z i)
              = (z i).2 • polytopalJoinCopy i ((z i).2⁻¹ • (z i).1) := by
            rw [polytopalJoinCopy, ← Pi.single_smul]
            congr 1
            rw [Prod.smul_mk, smul_smul, mul_inv_cancel₀ (ne_of_gt hi), one_smul,
              smul_eq_mul, mul_one]
          rw [hzi, map_smul, ite_eq_left hi]
          simp [smul_eq_mul]
        · have hi0 : (z i).2 = 0 := le_antisymm (not_lt.1 hi) (hz.1 i).1
          have hi1 : (z i).1 = 0 := (hz.1 i).2.1 hi0
          have hzi : z i = 0 := Prod.ext hi1 hi0
          rw [hzi]
          simp

/-- **Classification of the exposed faces of a Cayley join**: the maximizer set
of a functional is the Cayley join of the maximizer sets in those factors which
attain the global maximum, the other factors being empty. -/
theorem exists_exposed_factors_exposedBy
    {Fs : Fin (m + 1) → Set (CoordinateSpace n)} (hconv : ∀ i, Convex ℝ (Fs i))
    (hcomp : ∀ i, IsCompact (Fs i)) (l : PolytopalJoinAmbient n m →L[ℝ] ℝ) :
    ∃ Gs : Fin (m + 1) → Set (CoordinateSpace n),
      (∀ i, IsExposed ℝ (Fs i) (Gs i)) ∧
        exposedBy (cayleyJoin Fs) l = cayleyJoin Gs := by
  by_cases hempty : ∀ i, Fs i = ∅
  · refine ⟨Fs, fun i ↦ IsExposed.refl _, ?_⟩
    rw [cayleyJoin_eq_empty_iff.mpr hempty]
    exact Subset.antisymm (fun x hx ↦ hx.1) fun x hx ↦ absurd hx (by simp)
  · rw [not_forall] at hempty
    obtain ⟨i₀, hi₀⟩ := hempty
    rw [← ne_eq, ← nonempty_iff_ne_empty] at hi₀
    set U : Set (PolytopalJoinAmbient n m) := ⋃ i, polytopalJoinCopy i '' Fs i with hU_def
    have hUcomp : IsCompact U :=
      isCompact_iUnion fun i ↦ (hcomp i).image (continuous_polytopalJoinCopy i)
    have hUne : U.Nonempty := by
      obtain ⟨x, hx⟩ := hi₀
      exact ⟨polytopalJoinCopy i₀ x, mem_iUnion.mpr ⟨i₀, ⟨x, hx, rfl⟩⟩⟩
    obtain ⟨w, hwU, hwmax⟩ := hUcomp.exists_isMaxOn hUne l.continuous.continuousOn
    set M := l w with hM
    have hleU : ∀ u ∈ U, l u ≤ M := fun u hu ↦ hwmax hu
    have hleJ : ∀ z ∈ cayleyJoin Fs, l z ≤ M := by
      intro z hz
      rw [cayleyJoin_eq_convexHull hconv] at hz
      exact convexHull_min hleU (convex_halfSpace_le l.toLinearMap.isLinear M) hz
    have hlecopy : ∀ (i : Fin (m + 1)), ∀ x ∈ Fs i, l (polytopalJoinCopy i x) ≤ M :=
      fun i x hx ↦ hleU _ (mem_iUnion.mpr ⟨i, ⟨x, hx, rfl⟩⟩)
    refine ⟨fun i ↦ {x ∈ Fs i | l (polytopalJoinCopy i x) = M}, ?_, ?_⟩
    · intro i hne
      obtain ⟨x₀, hx₀F, hx₀M⟩ := hne
      refine ⟨l.comp (polytopalJoinCopyLinear i).toContinuousLinearMap, ?_⟩
      have hkey : ∀ x : CoordinateSpace n,
          l (polytopalJoinCopy i x)
            = (l.comp (polytopalJoinCopyLinear i).toContinuousLinearMap) x
              + l (Pi.single i (0, 1)) := by
        intro x
        rw [ContinuousLinearMap.comp_apply, ← map_add]
        congr 1
        simp [polytopalJoinCopy, polytopalJoinCopyLinear, ← Pi.single_add]
      ext x
      simp only [mem_ofPred_eq]
      constructor
      · rintro ⟨hxF, hxM⟩
        refine ⟨hxF, fun y hy ↦ ?_⟩
        have h1 := hlecopy i y hy
        rw [hkey y, hkey x] at *
        linarith [h1, hxM.ge, hxM.le]
      · rintro ⟨hxF, hxmax⟩
        refine ⟨hxF, le_antisymm (hlecopy i x hxF) ?_⟩
        have h2 := hxmax x₀ hx₀F
        rw [hkey x₀, hkey x] at *
        linarith [hx₀M.ge, hx₀M.le]
    · ext z
      constructor
      · rintro ⟨hzJ, hzmax⟩
        have hzM : l z = M := le_antisymm (hleJ z hzJ) (hzmax w (by
          rw [cayleyJoin_eq_convexHull hconv]; exact subset_convexHull ℝ _ hwU))
        refine ⟨fun i ↦ ⟨(hzJ.1 i).1, (hzJ.1 i).2.1, fun hpos ↦ ?_⟩, hzJ.2⟩
        refine ⟨(hzJ.1 i).2.2 hpos, ?_⟩
        by_contra hne
        have hlt : l (polytopalJoinCopy i ((z i).2⁻¹ • (z i).1)) < M :=
          lt_of_le_of_ne (hlecopy i _ ((hzJ.1 i).2.2 hpos)) hne
        have heval := l_eval_cayleyJoin l hzJ
        have hterm : ∀ j ∈ Finset.univ, (z j).2 *
            (if 0 < (z j).2 then l (polytopalJoinCopy j ((z j).2⁻¹ • (z j).1)) else 0)
              ≤ (z j).2 * M := by
          intro j _
          by_cases hj : 0 < (z j).2
          · rw [ite_eq_left hj]
            exact mul_le_mul_of_nonneg_left (hlecopy j _ ((hzJ.1 j).2.2 hj)) (le_of_lt hj)
          · have hj0 : (z j).2 = 0 := le_antisymm (not_lt.1 hj) (hzJ.1 j).1
            rw [hj0]; simp
        have hstrict : (z i).2 *
            (if 0 < (z i).2 then l (polytopalJoinCopy i ((z i).2⁻¹ • (z i).1)) else 0)
              < (z i).2 * M := by
          rw [ite_eq_left hpos]
          exact mul_lt_mul_of_pos_left hlt hpos
        have hsum := Finset.sum_lt_sum hterm ⟨i, Finset.mem_univ i, hstrict⟩
        rw [← heval, ← Finset.sum_mul, hzJ.2, one_mul] at hsum
        exact absurd hzM (ne_of_lt hsum)
      · intro hz
        have hzJ : z ∈ cayleyJoin Fs := cayleyJoin_mono (fun i x hx ↦ hx.1) hz
        refine ⟨hzJ, fun y hy ↦ ?_⟩
        have heval := l_eval_cayleyJoin l hzJ
        have hzM : l z = M := by
          rw [heval]
          have hterm : ∀ j ∈ Finset.univ, (z j).2 *
              (if 0 < (z j).2 then l (polytopalJoinCopy j ((z j).2⁻¹ • (z j).1)) else 0)
                = (z j).2 * M := by
            intro j _
            by_cases hj : 0 < (z j).2
            · rw [ite_eq_left hj, ((hz.1 j).2.2 hj).2]
            · have hj0 : (z j).2 = 0 := le_antisymm (not_lt.1 hj) (hzJ.1 j).1
              rw [hj0]; simp
          rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, hzJ.2, one_mul]
        rw [hzM]
        exact hleJ y hy

end CayleyJoin
end AffineTverberg
