import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.Prod
import Mathlib.Data.Real.Basic

set_option linter.style.header false

/-!
# The algebraic Sarkaria reduction

This file formalizes the linear-algebra step in the deduction of the main theorem from
Theorem `theorem:zero` in `affine-tverberg17.tex`, lines 238--280.

With `m + 1` join factors, the usual centered-simplex tensor map is linearly equivalent
to recording the differences between the first `m` vectors and the last vector.  The
definition `sarkariaMap` uses those coordinates.  Its kernel is therefore exactly the
diagonal.  Applying this to the weighted homogenized points `(tᵢ • xᵢ, tᵢ)` proves that
a zero of the Sarkaria map has uniform positive join weights and coincident points.
-/

namespace AffineTverberg

section DiagonalKernel

variable {m : ℕ} {A : Type*} [AddGroup A]

/-- Coordinates for the centered-simplex tensor map on `m + 1` vectors.

For centered-simplex vertices `u₀, ..., uₘ`, chosen as the standard basis followed by
minus their sum, `∑ i, a i ⊗ uᵢ` has coordinates `a j - a (Fin.last m)`.
-/
def sarkariaMap (a : Fin (m + 1) → A) : Fin m → A :=
  fun j ↦ a j.castSucc - a (Fin.last m)

@[simp]
theorem sarkariaMap_apply (a : Fin (m + 1) → A) (j : Fin m) :
    sarkariaMap a j = a j.castSucc - a (Fin.last m) :=
  rfl

/-- The kernel of the centered-simplex Sarkaria map is the diagonal subspace. -/
theorem sarkariaMap_eq_zero_iff (a : Fin (m + 1) → A) :
    sarkariaMap a = 0 ↔ ∀ i, a i = a (Fin.last m) := by
  constructor
  · intro h i
    refine Fin.lastCases rfl (fun j ↦ ?_) i
    have hj := congrFun h j
    simpa [sarkariaMap] using sub_eq_zero.mp hj
  · intro h
    funext j
    simp [sarkariaMap, h j.castSucc]

/-- Pairwise formulation of `sarkariaMap_eq_zero_iff`. -/
theorem sarkariaMap_eq_zero_iff_pairwise (a : Fin (m + 1) → A) :
    sarkariaMap a = 0 ↔ ∀ i j, a i = a j := by
  rw [sarkariaMap_eq_zero_iff]
  constructor
  · intro h i j
    exact (h i).trans (h j).symm
  · intro h i
    exact h i (Fin.last m)

end DiagonalKernel

section CenteredSimplex

variable {m : ℕ}

/-- A concrete centered simplex in `ℝ^m`: the first `m` vertices are the standard
basis and the last vertex is minus their sum. -/
def centeredSimplexVertex (i : Fin (m + 1)) : Fin m → ℝ :=
  Fin.lastCases (fun _ ↦ -1) (fun k j ↦ if k = j then 1 else 0) i

@[simp]
theorem centeredSimplexVertex_last (j : Fin m) :
    centeredSimplexVertex (Fin.last m) j = -1 := by
  simp [centeredSimplexVertex]

@[simp]
theorem centeredSimplexVertex_castSucc (i j : Fin m) :
    centeredSimplexVertex i.castSucc j = if i = j then 1 else 0 := by
  simp [centeredSimplexVertex]

/-- The chosen simplex vertices have barycenter zero, as required in lines 203--207. -/
theorem sum_centeredSimplexVertex (j : Fin m) :
    ∑ i : Fin (m + 1), centeredSimplexVertex i j = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The coordinate form of `∑ i, aᵢ ⊗ uᵢ` for the concrete centered simplex. -/
def centeredSimplexCombination (a : Fin (m + 1) → E) : Fin m → E :=
  fun j ↦ ∑ i, centeredSimplexVertex i j • a i

/-- The tensor construction in the paper is exactly `sarkariaMap` in our coordinates. -/
theorem centeredSimplexCombination_eq_sarkariaMap (a : Fin (m + 1) → E) :
    centeredSimplexCombination a = sarkariaMap a := by
  funext j
  simp only [centeredSimplexCombination, sarkariaMap]
  rw [Fin.sum_univ_castSucc]
  simp [sub_eq_add_neg]

/-- The displayed relation among the simplex vertices spans every linear dependency. -/
theorem centeredSimplexCombination_eq_zero_iff (a : Fin (m + 1) → E) :
    centeredSimplexCombination a = 0 ↔ ∀ i, a i = a (Fin.last m) := by
  rw [centeredSimplexCombination_eq_sarkariaMap, sarkariaMap_eq_zero_iff]

end CenteredSimplex

section WeightedPoints

variable {m : ℕ} {E : Type*}

/-- The affine homogenization `x ↦ (x, 1)`. -/
def homogenize (x : E) : E × ℝ :=
  (x, 1)

@[simp]
theorem homogenize_fst (x : E) : (homogenize x).1 = x :=
  rfl

@[simp]
theorem homogenize_snd (x : E) : (homogenize x).2 = 1 :=
  rfl

variable [AddCommGroup E] [Module ℝ E]

/-- The vectors `tᵢ (xᵢ, 1)` occurring in the Sarkaria construction. -/
def weightedHomogenized (t : Fin (m + 1) → ℝ) (x : Fin (m + 1) → E) :
    Fin (m + 1) → E × ℝ :=
  fun i ↦ t i • homogenize (x i)

/-- A zero of the Sarkaria map forces all join weights to agree. -/
theorem weights_eq_last_of_sarkariaMap_eq_zero
    (t : Fin (m + 1) → ℝ) (x : Fin (m + 1) → E)
    (hzero : sarkariaMap (weightedHomogenized t x) = 0) :
    ∀ i, t i = t (Fin.last m) := by
  intro i
  have hi := (sarkariaMap_eq_zero_iff (weightedHomogenized t x)).mp hzero i
  simpa [weightedHomogenized, homogenize] using congrArg Prod.snd hi

/-- If the join weights sum to one, their common value is `1 / (m + 1)`. -/
theorem weights_eq_uniform_of_sarkariaMap_eq_zero
    (t : Fin (m + 1) → ℝ) (x : Fin (m + 1) → E)
    (hsum : ∑ i, t i = 1)
    (hzero : sarkariaMap (weightedHomogenized t x) = 0) :
    ∀ i, t i = (((m + 1 : ℕ) : ℝ)⁻¹) := by
  have hweights := weights_eq_last_of_sarkariaMap_eq_zero t x hzero
  have hcard : ((m + 1 : ℕ) : ℝ) * t (Fin.last m) = 1 := by
    calc
      ((m + 1 : ℕ) : ℝ) * t (Fin.last m) = ∑ _i : Fin (m + 1), t (Fin.last m) := by
        simp
      _ = ∑ i, t i := by
        apply Finset.sum_congr rfl
        intro i _
        exact (hweights i).symm
      _ = 1 := hsum
  have hcard_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.zero_lt_succ m)
  have hcard_ne : ((m + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hlast : t (Fin.last m) = 1 / ((m + 1 : ℕ) : ℝ) := by
    apply (eq_div_iff hcard_ne).2
    simpa [mul_comm] using hcard
  intro i
  simpa [one_div] using (hweights i).trans hlast

/-- Under the barycentric sum condition, a zero also forces all original points to agree. -/
theorem points_eq_of_sarkariaMap_eq_zero
    (t : Fin (m + 1) → ℝ) (x : Fin (m + 1) → E)
    (hsum : ∑ i, t i = 1)
    (hzero : sarkariaMap (weightedHomogenized t x) = 0) :
    ∀ i j, x i = x j := by
  have hdiag := (sarkariaMap_eq_zero_iff (weightedHomogenized t x)).mp hzero
  have hweights := weights_eq_last_of_sarkariaMap_eq_zero t x hzero
  have hlast_ne : t (Fin.last m) ≠ 0 := by
    intro hlast_zero
    have hsum_zero : ∑ i, t i = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hweights i, hlast_zero]
    exact one_ne_zero (hsum.symm.trans hsum_zero)
  intro i j
  have hij : weightedHomogenized t x i = weightedHomogenized t x j :=
    (hdiag i).trans (hdiag j).symm
  have hscaled : t (Fin.last m) • x i = t (Fin.last m) • x j := by
    simpa [weightedHomogenized, homogenize, hweights i, hweights j] using
      congrArg Prod.fst hij
  apply_fun ((t (Fin.last m))⁻¹ • ·) at hscaled
  simpa [smul_smul, hlast_ne] using hscaled

/-- The complete algebraic conclusion used in the paper's Tverberg deduction. -/
theorem zero_implies_uniform_weights_and_coincident_points
    (t : Fin (m + 1) → ℝ) (x : Fin (m + 1) → E)
    (hsum : ∑ i, t i = 1)
    (hzero : sarkariaMap (weightedHomogenized t x) = 0) :
    (∀ i, t i = (((m + 1 : ℕ) : ℝ)⁻¹)) ∧ ∃ y, ∀ i, x i = y := by
  refine ⟨weights_eq_uniform_of_sarkariaMap_eq_zero t x hsum hzero, ?_⟩
  exact ⟨x (Fin.last m), fun i ↦ points_eq_of_sarkariaMap_eq_zero t x hsum hzero i _⟩

/-- Exact zero characterization under the barycentric sum condition. -/
theorem sarkariaMap_weighted_eq_zero_iff
    (t : Fin (m + 1) → ℝ) (x : Fin (m + 1) → E)
    (hsum : ∑ i, t i = 1) :
    sarkariaMap (weightedHomogenized t x) = 0 ↔
      (∀ i, t i = (((m + 1 : ℕ) : ℝ)⁻¹)) ∧ ∀ i j, x i = x j := by
  constructor
  · intro hzero
    exact ⟨weights_eq_uniform_of_sarkariaMap_eq_zero t x hsum hzero,
      points_eq_of_sarkariaMap_eq_zero t x hsum hzero⟩
  · rintro ⟨hweights, hpoints⟩
    apply (sarkariaMap_eq_zero_iff (weightedHomogenized t x)).2
    intro i
    simp only [weightedHomogenized]
    rw [hweights i, hweights (Fin.last m), hpoints i (Fin.last m)]

/-- In particular, every join coefficient at a Sarkaria zero is positive. -/
theorem weights_pos_of_sarkariaMap_eq_zero
    (t : Fin (m + 1) → ℝ) (x : Fin (m + 1) → E)
    (hsum : ∑ i, t i = 1)
    (hzero : sarkariaMap (weightedHomogenized t x) = 0) :
    ∀ i, 0 < t i := by
  intro i
  rw [weights_eq_uniform_of_sarkariaMap_eq_zero t x hsum hzero i]
  apply inv_pos.mpr
  exact Nat.cast_pos.mpr (Nat.zero_lt_succ m)

end WeightedPoints

section DeletedJoinDeduction

variable {m : ℕ} {X E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The data about a deleted-join point used in the deduction of `theorem:main` from
`theorem:zero`.  Faces attached to zero-weight factors may be empty; positive factors
must carry a point of their face. -/
structure DeletedJoinWitness (m : ℕ) (X : Type*) where
  weight : Fin (m + 1) → ℝ
  point : Fin (m + 1) → X
  face : Fin (m + 1) → Set X
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : ∑ i, weight i = 1
  point_mem_face : ∀ i, 0 < weight i → point i ∈ face i
  faces_pairwiseDisjoint : Pairwise fun i j ↦ Disjoint (face i) (face j)

/-- The conclusion of the affine Tverberg theorem, expressed for an abstract face
system on the type `X` of points of the domain.  `face_ne_univ` says that every chosen
face is proper, hence belongs to the boundary. -/
structure TverbergPartition (m : ℕ) (X E : Type*) (φ : X → E) where
  face : Fin (m + 1) → Set X
  faces_pairwiseDisjoint : Pairwise fun i j ↦ Disjoint (face i) (face j)
  face_ne_univ : ∀ i, face i ≠ Set.univ
  commonPoint : E
  commonPoint_mem_image : ∀ i, commonPoint ∈ φ '' face i

/-- The Sarkaria value of a point represented by deleted-join data. -/
def DeletedJoinWitness.sarkariaValue (z : DeletedJoinWitness m X) (φ : X → E) :
    Fin m → E × ℝ :=
  sarkariaMap (weightedHomogenized z.weight (fun i ↦ φ (z.point i)))

/-- Lines 238--280 of the paper: a zero of the deleted-join Sarkaria map gives
pairwise disjoint proper faces whose images have a common point. -/
theorem tverbergPartition_of_sarkariaValue_eq_zero
    (hm : 1 ≤ m) (φ : X → E) (z : DeletedJoinWitness m X)
    (hzero : z.sarkariaValue φ = 0) :
    Nonempty (TverbergPartition m X E φ) := by
  have hpos : ∀ i, 0 < z.weight i :=
    weights_pos_of_sarkariaMap_eq_zero z.weight (fun i ↦ φ (z.point i)) z.weight_sum hzero
  have hpoints : ∀ i j, φ (z.point i) = φ (z.point j) :=
    points_eq_of_sarkariaMap_eq_zero z.weight (fun i ↦ φ (z.point i)) z.weight_sum hzero
  have htwo : 2 ≤ m + 1 := by
    exact Nat.succ_le_succ hm
  let _ : Nontrivial (Fin (m + 1)) := Fin.nontrivial_iff_two_le.mpr htwo
  refine ⟨?_⟩
  refine
    { face := z.face
      faces_pairwiseDisjoint := z.faces_pairwiseDisjoint
      face_ne_univ := ?_
      commonPoint := φ (z.point (Fin.last m))
      commonPoint_mem_image := ?_ }
  · intro i hface
    obtain ⟨j, hji⟩ := exists_ne i
    have hjmem : z.point j ∈ z.face j := z.point_mem_face j (hpos j)
    have himem : z.point j ∈ z.face i := by simp [hface]
    exact (Set.disjoint_left.mp (z.faces_pairwiseDisjoint hji.symm)) himem hjmem
  · intro i
    exact ⟨z.point i, z.point_mem_face i (hpos i), hpoints i (Fin.last m)⟩

end DeletedJoinDeduction

end AffineTverberg
