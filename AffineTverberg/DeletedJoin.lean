import AffineTverberg.MainTheorem
import AffineTverberg.Sarkaria

set_option linter.style.header false

/-!
# Deleted joins and the zero-theorem interface

This file gives a witness-level model of the deleted joins used in
`affine-tverberg17.tex`.  It records exactly the data needed at a zero: barycentric
weights, one point in each positive-weight factor, and pairwise disjoint supporting
faces.  It also states `theorem:zero` for both domain classes and proves the complete
deduction from those zero statements to `theorem:main` in the requested range.  The
separately known two-fold simplicial-ball case is intentionally omitted.
-/

open Set

namespace AffineTverberg

section SetLemmas

variable {α : Type*} {S F G : Set α}

/-- Disjoint ambient sets remain disjoint after restriction to a common subtype. -/
theorem disjoint_setWithin (h : Disjoint F G) :
    Disjoint (setWithin S F) (setWithin S G) := by
  rw [Set.disjoint_left]
  intro x hxF hxG
  exact (Set.disjoint_left.mp h) hxF hxG

end SetLemmas

section PolytopalDeletedJoin

variable {n m d : ℕ} (P : FullDimensionalPolytope n)

/-- A represented point of the `m + 1`-fold deleted join of a polytope. -/
structure PolytopeDeletedJoinPoint where
  weight : Fin (m + 1) → ℝ
  point : Fin (m + 1) → P.carrier
  face : Fin (m + 1) → Set (CoordinateSpace n)
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : ∑ i, weight i = 1
  face_isFace : ∀ i, P.IsFace (face i)
  faces_pairwiseDisjoint : Pairwise fun i j ↦ Disjoint (face i) (face j)
  point_mem_face : ∀ i, 0 < weight i → (point i).1 ∈ face i

/-- Forget the ambient polytope while retaining the deleted-join data. -/
def PolytopeDeletedJoinPoint.toDeletedJoinWitness
    (z : PolytopeDeletedJoinPoint (m := m) P) :
    DeletedJoinWitness m P.carrier where
  weight := z.weight
  point := z.point
  face i := setWithin P.carrier (z.face i)
  weight_nonneg := z.weight_nonneg
  weight_sum := z.weight_sum
  point_mem_face := z.point_mem_face
  faces_pairwiseDisjoint := by
    intro i j hij
    exact disjoint_setWithin (z.faces_pairwiseDisjoint hij)

/-- The Sarkaria value of a represented point in the polytopal deleted join. -/
def PolytopeDeletedJoinPoint.sarkariaValue
    (z : PolytopeDeletedJoinPoint (m := m) P)
    (φ : P.carrier → CoordinateSpace d) : Fin m → CoordinateSpace d × ℝ :=
  z.toDeletedJoinWitness.sarkariaValue φ

/-- A Sarkaria zero in the polytopal deleted join gives the concrete polytopal
conclusion of `theorem:main`. -/
theorem polytopalConclusion_of_sarkariaValue_eq_zero
    (hm : 1 ≤ m) (φ : P.carrier → CoordinateSpace d)
    (z : PolytopeDeletedJoinPoint (m := m) P)
    (hzero : PolytopeDeletedJoinPoint.sarkariaValue P z φ = 0) :
    ∃ F : Fin (m + 1) → Set (CoordinateSpace n),
      (∀ i, P.IsBoundaryFace (F i)) ∧
      Pairwise (fun i j ↦ Disjoint (F i) (F j)) ∧
      ∃ y, ∀ i, y ∈ φ '' setWithin P.carrier (F i) := by
  have hpos : ∀ i, 0 < z.weight i :=
    weights_pos_of_sarkariaMap_eq_zero z.weight (fun i ↦ φ (z.point i)) z.weight_sum hzero
  have hpoints : ∀ i j, φ (z.point i) = φ (z.point j) :=
    points_eq_of_sarkariaMap_eq_zero z.weight (fun i ↦ φ (z.point i)) z.weight_sum hzero
  have htwo : 2 ≤ m + 1 := Nat.succ_le_succ hm
  let _ : Nontrivial (Fin (m + 1)) := Fin.nontrivial_iff_two_le.mpr htwo
  refine ⟨z.face, ?_, z.faces_pairwiseDisjoint, ?_⟩
  · intro i
    refine ⟨z.face_isFace i, ?_⟩
    intro hface
    obtain ⟨j, hji⟩ := exists_ne i
    have hjmem : (z.point j).1 ∈ z.face j := z.point_mem_face j (hpos j)
    have himem : (z.point j).1 ∈ z.face i := by
      rw [hface]
      exact (z.point j).2
    exact (Set.disjoint_left.mp (z.faces_pairwiseDisjoint hji.symm)) himem hjmem
  · exact ⟨φ (z.point (Fin.last m)), fun i ↦
      ⟨z.point i, z.point_mem_face i (hpos i), hpoints i (Fin.last m)⟩⟩

end PolytopalDeletedJoin

section SimplicialDeletedJoin

variable {n m d e : ℕ} (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))

/-- A represented point of the `m + 1`-fold deleted join of the boundary of a
simplicial ball. -/
structure SimplicialDeletedJoinPoint where
  weight : Fin (m + 1) → ℝ
  point : Fin (m + 1) → K.space
  face : Fin (m + 1) → Finset (CoordinateSpace e)
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : ∑ i, weight i = 1
  face_isBoundary : ∀ i, IsBoundarySimplicialFace n K (face i)
  faces_pairwiseDisjoint : Pairwise fun i j ↦ Disjoint (face i) (face j)
  point_mem_face : ∀ i, 0 < weight i → point i ∈ simplicialFaceCarrier K (face i)

/-- The Sarkaria value of a represented point in the simplicial deleted join. -/
def SimplicialDeletedJoinPoint.sarkariaValue
    (z : SimplicialDeletedJoinPoint (n := n) (m := m) K)
    (φ : K.space → CoordinateSpace d) : Fin m → CoordinateSpace d × ℝ :=
  sarkariaMap (weightedHomogenized z.weight (fun i ↦ φ (z.point i)))

/-- A Sarkaria zero in the simplicial deleted join gives the concrete simplicial-ball
conclusion of `theorem:main`. -/
theorem simplicialConclusion_of_sarkariaValue_eq_zero
    (φ : K.space → CoordinateSpace d)
    (z : SimplicialDeletedJoinPoint (n := n) (m := m) K)
    (hzero : SimplicialDeletedJoinPoint.sarkariaValue K z φ = 0) :
    ∃ F : Fin (m + 1) → Finset (CoordinateSpace e),
      (∀ i, IsBoundarySimplicialFace n K (F i)) ∧
      Pairwise (fun i j ↦ Disjoint (F i) (F j)) ∧
      ∃ y, ∀ i, y ∈ φ '' simplicialFaceCarrier K (F i) := by
  have hpos : ∀ i, 0 < z.weight i :=
    weights_pos_of_sarkariaMap_eq_zero z.weight (fun i ↦ φ (z.point i)) z.weight_sum hzero
  have hpoints : ∀ i j, φ (z.point i) = φ (z.point j) :=
    points_eq_of_sarkariaMap_eq_zero z.weight (fun i ↦ φ (z.point i)) z.weight_sum hzero
  exact ⟨z.face, z.face_isBoundary, z.faces_pairwiseDisjoint,
    φ (z.point (Fin.last m)), fun i ↦
      ⟨z.point i, z.point_mem_face i (hpos i), hpoints i (Fin.last m)⟩⟩

end SimplicialDeletedJoin

section ZeroTheorem

/-- The coordinate realization of `ℝ^(d+1) ⊗ ℝ^m` used for `r = m + 1` factors. -/
abbrev SarkariaTarget (d m : ℕ) := Fin m → CoordinateSpace d × ℝ

variable {n m d : ℕ} {P : FullDimensionalPolytope n}

/-- Affineness on a polytope with an arbitrary real-module target. -/
def isAffineMapOnInto (P : FullDimensionalPolytope n) {V : Type*}
    [AddCommGroup V] [Module ℝ V] (f : P.carrier → V) : Prop :=
  ∃ ψ : CoordinateSpace n →ᵃ[ℝ] V, ∀ x, f x = ψ x.1

/-- An affine map on the join is recorded by its restrictions to the join factors.
The diagonal relation is equation (3) of the paper. -/
structure PolytopalJoinMap (P : FullDimensionalPolytope n) (m : ℕ) (V : Type*)
    [AddCommGroup V] [Module ℝ V] where
  factor : Fin (m + 1) → P.carrier → V
  factor_affine : ∀ i, isAffineMapOnInto P (factor i)
  diagonal_relation : ∀ x, ∑ i, factor i x = 0

/-- Evaluation of a factorwise map on a represented deleted-join point. -/
def PolytopalJoinMap.value {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Φ : PolytopalJoinMap P m V) (z : PolytopeDeletedJoinPoint (m := m) P) : V :=
  ∑ i, z.weight i • Φ.factor i (z.point i)

/-- The standard factor map `x ↦ (φ(x), 1) ⊗ uᵢ` from equation (2). -/
def standardSarkariaFactor (φ : P.carrier → CoordinateSpace d) (i : Fin (m + 1)) :
    P.carrier → SarkariaTarget d m :=
  fun x j ↦ centeredSimplexVertex i j • homogenize (φ x)

/-- Each standard Sarkaria factor is affine when `φ` is affine on the polytope. -/
theorem standardSarkariaFactor_affine (φ : P.carrier → CoordinateSpace d)
    (hφ : P.IsAffineMapOn φ) (i : Fin (m + 1)) :
    isAffineMapOnInto P (standardSarkariaFactor φ i) := by
  obtain ⟨ψ, hψ⟩ := hφ
  let homogenizedMap : CoordinateSpace n →ᵃ[ℝ] CoordinateSpace d × ℝ :=
    ψ.prod (AffineMap.const ℝ (CoordinateSpace n) 1)
  let Ψ : CoordinateSpace n →ᵃ[ℝ] SarkariaTarget d m :=
    AffineMap.pi fun j ↦ centeredSimplexVertex i j • homogenizedMap
  refine ⟨Ψ, fun x ↦ ?_⟩
  funext j
  simp [standardSarkariaFactor, Ψ, homogenizedMap, hψ, homogenize]

/-- The standard factors sum to zero on the diagonal. -/
theorem sum_standardSarkariaFactor (φ : P.carrier → CoordinateSpace d) (x : P.carrier) :
    ∑ i : Fin (m + 1), standardSarkariaFactor φ i x = 0 := by
  funext j
  simp only [standardSarkariaFactor, Finset.sum_apply, Pi.zero_apply]
  rw [← Finset.sum_smul]
  simp [sum_centeredSimplexVertex]

/-- The standard Sarkaria join map, packaged as an admissible map for `theorem:zero`. -/
def standardSarkariaJoinMap (φ : P.carrier → CoordinateSpace d)
    (hφ : P.IsAffineMapOn φ) : PolytopalJoinMap P m (SarkariaTarget d m) where
  factor := standardSarkariaFactor φ
  factor_affine := standardSarkariaFactor_affine φ hφ
  diagonal_relation := sum_standardSarkariaFactor φ

/-- Evaluating the standard factorwise join map is the coordinate Sarkaria value. -/
theorem standardSarkariaJoinMap_value
    (φ : P.carrier → CoordinateSpace d) (hφ : P.IsAffineMapOn φ)
    (z : PolytopeDeletedJoinPoint (m := m) P) :
    (standardSarkariaJoinMap φ hφ).value z =
      PolytopeDeletedJoinPoint.sarkariaValue P z φ := by
  unfold PolytopeDeletedJoinPoint.sarkariaValue DeletedJoinWitness.sarkariaValue
  rw [← centeredSimplexCombination_eq_sarkariaMap]
  funext j
  simp [PolytopalJoinMap.value, standardSarkariaJoinMap, standardSarkariaFactor,
    PolytopeDeletedJoinPoint.toDeletedJoinWitness, centeredSimplexCombination,
    weightedHomogenized, smul_smul, mul_comm]

/-- The polytopal case of `theorem:zero`, in the coordinate target used by the paper. -/
def polytopalZeroTheoremStatement : Prop :=
  ∀ (d m : ℕ), 1 ≤ d → 1 ≤ m →
    ∀ (P : FullDimensionalPolytope ((d + 1) * m))
      (Φ : PolytopalJoinMap P m (SarkariaTarget d m)),
      ∃ z : PolytopeDeletedJoinPoint (m := m) P, Φ.value z = 0

/-- The simplicial-ball case of `theorem:zero`.  As in the paper, this case assumes
`r ≥ 3`, equivalently `m ≥ 2`. -/
def simplicialBallZeroTheoremStatement : Prop :=
  ∀ (d m e : ℕ), 1 ≤ d → 2 ≤ m →
    ∀ (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)),
      IsSimplicialBall ((d + 1) * m) K →
      ∀ (φ : K.space → CoordinateSpace d),
        Continuous φ → IsAffineOnSimplicialFaces K φ →
        ∃ z : SimplicialDeletedJoinPoint (n := (d + 1) * m) (m := m) K,
          SimplicialDeletedJoinPoint.sarkariaValue K z φ = 0

/-- The polytopal zero theorem implies the polytopal half of `theorem:main`. -/
theorem polytopalMainTheoremStatement_of_zero
    (hzero : polytopalZeroTheoremStatement) : polytopalMainTheoremStatement := by
  intro d m hd hm P φ _hcontinuous hφ
  let Φ := standardSarkariaJoinMap (P := P) (m := m) φ hφ
  obtain ⟨z, hz⟩ := hzero d m hd hm P Φ
  apply polytopalConclusion_of_sarkariaValue_eq_zero P hm φ z
  rw [← standardSarkariaJoinMap_value φ hφ]
  exact hz

/-- The simplicial zero theorem implies the simplicial-ball half of `theorem:main`
in the requested range `r ≥ 3`. -/
theorem simplicialBallMainTheoremStatement_of_zero
    (hzero : simplicialBallZeroTheoremStatement) :
    simplicialBallMainTheoremStatement := by
  intro d m e hd hm K hK φ hcontinuous hφ
  obtain ⟨z, hz⟩ := hzero d m e hd hm K hK φ hcontinuous hφ
  exact simplicialConclusion_of_sarkariaValue_eq_zero K φ z hz

/-- The deduction of `theorem:main` in the requested range from the two cases of
`theorem:zero`. -/
theorem mainTheoremStatement_of_zero
    (hzeroPolytope : polytopalZeroTheoremStatement)
    (hzeroSimplicialBall : simplicialBallZeroTheoremStatement) :
    mainTheoremStatement :=
  ⟨polytopalMainTheoremStatement_of_zero hzeroPolytope,
    simplicialBallMainTheoremStatement_of_zero hzeroSimplicialBall⟩

end ZeroTheorem

end AffineTverberg
