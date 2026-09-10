import AffineTverberg.SimplicialBoundaryJoin
import AffineTverberg.RelativeSingularHomology
import AffineTverberg.SphereMiddleHomology

set_option linter.style.header false

/-!
# Reduction of the geometric-complement step to one duality isomorphism

Let `D = simplicialDeletedJoinCarrier n K m` be the actual deleted join and
`J = simplicialBoundaryJoinCarrier K n m` the actual boundary join, which is
a compact polyhedron containing `D` as a closed subset. The project already
proves, with no duality input,

`isZero_simplicialBoundaryJoinComplement_homology :  H_{m·n-1}(J \ D) = 0`

and the target of the simplicial half of the main theorem is

`H_{n-1}(D) = 0`.

The classical bridge between these two is Alexander duality in the sphere `J`
(equivalently Poincaré–Lefschetz duality for the pair). This file supplies
*everything except that one duality isomorphism*, using the genuine relative
singular chain complex of the pair and its long exact sequence:

* `isZero_relativeHomology_boundaryJoin_complement` — unconditionally, with
  only the geometric sphere presentation of `J` as input,
  `H_{m·n}(J, J \ D) = 0`;
* `isZero_singularHomology_deletedJoin_of_isZero_relative` — unconditionally,
  with the same input, `H_n(J, D) = 0` implies `H_{n-1}(D) = 0`.

Under the duality isomorphism these are exactly the two ends of the classical
argument: `H_{m·n}(J, J∖D) ≅ H^{n-1}(D)` (the Alexander form) and
`H_n(J, D) ≅ H^{m·n-1}(J∖D)` (the Lefschetz form); over the real field a
cohomology group vanishes exactly when the corresponding homology group does
(`isZero_realSingularCohomology_iff`), so either form of the duality
isomorphism, combined with the two theorems below, yields the desired
`H_{n-1}(D) = 0`. The two duality statements are recorded as explicit
predicates `AlexanderFormDualityInput` and `LefschetzFormDualityInput`, and
the corresponding conclusions are proved from them; neither the conclusion
nor any acyclicity of `D` is assumed anywhere.

The sphere presentation of `J` is taken as a hypothesis: it is the geometric
identification of the boundary join with a coordinate sphere, developed
separately.
-/

noncomputable section

open Set Metric CategoryTheory CategoryTheory.Limits

namespace AffineTverberg

/-! ### A subspace of a subspace -/

/-- For `S ⊆ T`, the preimage of `S` in the subspace `T` is homeomorphic to
`S` itself. -/
def subtypePreimageHomeomorph {X : Type*} [TopologicalSpace X] {S T : Set X} (h : S ⊆ T) :
    ↥(Subtype.val ⁻¹' S : Set ↥T) ≃ₜ ↥S where
  toFun z := ⟨z.val.val, z.property⟩
  invFun x := ⟨⟨x.val, h x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

variable {e n m : ℕ} (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))

/-- The boundary join as a space. -/
abbrev boundaryJoinSpace (n m : ℕ) : TopCat.{0} :=
  TopCat.of ↥(simplicialBoundaryJoinCarrier K n m)

/-- The deleted join, as a subset of the boundary join. -/
def deletedJoinInBoundaryJoin (n m : ℕ) : Set ↥(boundaryJoinSpace K n m) :=
  Subtype.val ⁻¹' (simplicialDeletedJoinCarrier n K m)

/-- The complement of the deleted join inside the boundary join. -/
def complementInBoundaryJoin (n m : ℕ) : Set ↥(boundaryJoinSpace K n m) :=
  Subtype.val ⁻¹' (simplicialBoundaryJoinCarrier K n m \ simplicialDeletedJoinCarrier n K m)

/-- The deleted join sits inside the boundary join as a topological subspace. -/
def deletedJoinHomeomorph :
    ↥(deletedJoinInBoundaryJoin K n m) ≃ₜ ↥(simplicialDeletedJoinCarrier n K m) :=
  subtypePreimageHomeomorph (simplicialDeletedJoinCarrier_subset_boundaryJoin K)

/-- The complement inside the boundary join is the actual set difference. -/
def complementHomeomorph :
    ↥(complementInBoundaryJoin K n m) ≃ₜ
      ↥(simplicialBoundaryJoinCarrier K n m \ simplicialDeletedJoinCarrier n K m) :=
  subtypePreimageHomeomorph fun _ hx ↦ hx.1

/-! ### The homology of the boundary join from its sphere presentation -/

/-- The sphere presentation of the boundary join: an explicit homeomorphism
with the unit sphere of the coordinate space of dimension `(m+1)·n`, whose
sphere dimension is therefore `(m+1)·n - 1`. -/
abbrev BoundaryJoinSpherePresentation (n m : ℕ) : Type :=
  ↥(simplicialBoundaryJoinCarrier K n m) ≃ₜ sphere (0 : CoordinateSpace ((m + 1) * n)) 1

theorem finrank_coordinateSpace (k : ℕ) : Module.finrank ℝ (CoordinateSpace k) = k := by
  simp [CoordinateSpace]

/-- Middle-degree vanishing for the boundary join, from its sphere
presentation. -/
theorem isZero_boundaryJoin_homology (hsph : BoundaryJoinSpherePresentation K n m)
    (j : ℕ) (hj : 0 < j) (hjN : j < (m + 1) * n - 1) :
    IsZero ((realSingularHomology j).obj (boundaryJoinSpace K n m)) := by
  obtain ⟨N, hN⟩ : ∃ N, (m + 1) * n = N + 1 := by
    rcases Nat.eq_zero_or_pos ((m + 1) * n) with h | h
    · omega
    · exact ⟨(m + 1) * n - 1, by omega⟩
  have hdim : Module.finrank ℝ (CoordinateSpace ((m + 1) * n)) = N + 1 := by
    rw [finrank_coordinateSpace]; omega
  have hsub := Simplicial.subsingleton_singularHomology_of_homeomorph_sphere
    (X := ↥(simplicialBoundaryJoinCarrier K n m)) hdim hsph j hj (by omega)
  exact ModuleCat.isZero_iff_subsingleton.mpr hsub

/-! ### The complement side: relative homology in the complementary degree -/

/-- **Unconditional relative vanishing on the complement side.** With the
sphere presentation of the boundary join as the only geometric input, the
relative homology of the pair `(J, J \ D)` vanishes in degree `m·n`. -/
theorem isZero_relativeHomology_boundaryJoin_complement
    (hfin : K.faces.Finite) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hsph : BoundaryJoinSpherePresentation K n m) :
    IsZero (AffChain.relativeHomology (complementInBoundaryJoin K n m) (m * n)) := by
  obtain ⟨p, hp⟩ : ∃ p, m * n = p + 1 := ⟨m * n - 1, by
    have : 0 < m * n := Nat.mul_pos (by omega) (by omega)
    omega⟩
  have hX : IsZero ((realSingularHomology (p + 1)).obj (boundaryJoinSpace K n m)) := by
    refine isZero_boundaryJoin_homology K hsph (p + 1) (by omega) ?_
    have h1 : (m + 1) * n = m * n + n := by ring
    rw [h1, hp]
    omega
  have hcompl : IsZero ((realSingularHomology p).obj
      (TopCat.of ↥(simplicialBoundaryJoinCarrier K n m \ simplicialDeletedJoinCarrier n K m))) := by
    have h := isZero_simplicialBoundaryJoinComplement_homology (K := K) (n := n) (m := m)
      hfin hm (by omega)
    rwa [show m * n - 1 = p by omega] at h
  have hA : IsZero ((realSingularHomology p).obj
      (TopCat.of ↥(complementInBoundaryJoin K n m))) :=
    ModuleCat.isZero_iff_subsingleton.mpr
      ((realSingularHomology_subsingleton_iff_of_homotopyEquiv
        (complementHomeomorph K).toHomotopyEquiv p).mpr
          (ModuleCat.subsingleton_of_isZero hcompl))
  rw [hp]
  exact AffChain.isZero_relativeHomology (complementInBoundaryJoin K n m) p hX hA

/-! ### The target side: from relative vanishing to the deleted join -/

/-- **Unconditional reduction of the target.** With the sphere presentation of
the boundary join as the only geometric input, vanishing of the relative
homology of the pair `(J, D)` in degree `n` implies the desired vanishing
`H_{n-1}(D) = 0`. -/
theorem isZero_singularHomology_deletedJoin_of_isZero_relative
    (hn : 2 ≤ n) (hsph : BoundaryJoinSpherePresentation K n m) (hm : 1 ≤ m)
    (hrel : IsZero (AffChain.relativeHomology (deletedJoinInBoundaryJoin K n m) n)) :
    IsZero ((realSingularHomology (n - 1)).obj
      (TopCat.of ↥(simplicialDeletedJoinCarrier n K m))) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hX : IsZero ((realSingularHomology k).obj (boundaryJoinSpace K (k + 1) m)) := by
    refine isZero_boundaryJoin_homology K hsph k (by omega) ?_
    have h1 : (m + 1) * (k + 1) = m * (k + 1) + (k + 1) := by ring
    have h2 : k + 1 ≤ m * (k + 1) := Nat.le_mul_of_pos_left (k + 1) (by omega)
    rw [h1]
    omega
  have hsub := AffChain.isZero_homology_sub_of_isZero_relative
    (deletedJoinInBoundaryJoin K (k + 1) m) k hrel hX
  exact ModuleCat.isZero_iff_subsingleton.mpr
    ((realSingularHomology_subsingleton_iff_of_homotopyEquiv
      (deletedJoinHomeomorph K).toHomotopyEquiv k).mp (ModuleCat.subsingleton_of_isZero hsub))

/-- The reduction above loses nothing: for these parameters the relative
vanishing `H_n(J, D) = 0` is *equivalent* to the desired
`H_{n-1}(D) = 0`, again with only the sphere presentation as input. -/
theorem isZero_relativeHomology_deletedJoin_iff
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hsph : BoundaryJoinSpherePresentation K n m) :
    IsZero (AffChain.relativeHomology (deletedJoinInBoundaryJoin K n m) n) ↔
      IsZero ((realSingularHomology (n - 1)).obj
        (TopCat.of ↥(simplicialDeletedJoinCarrier n K m))) := by
  refine ⟨isZero_singularHomology_deletedJoin_of_isZero_relative K hn hsph (by omega), ?_⟩
  intro hD
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hmn : k + 1 ≤ m * (k + 1) := Nat.le_mul_of_pos_left (k + 1) (by omega)
  have hX : IsZero ((realSingularHomology (k + 1)).obj (boundaryJoinSpace K (k + 1) m)) := by
    refine isZero_boundaryJoin_homology K hsph (k + 1) (by omega) ?_
    have h1 : (m + 1) * (k + 1) = m * (k + 1) + (k + 1) := by ring
    rw [h1]
    omega
  have hA : IsZero ((realSingularHomology k).obj
      (TopCat.of ↥(deletedJoinInBoundaryJoin K (k + 1) m))) :=
    ModuleCat.isZero_iff_subsingleton.mpr
      ((realSingularHomology_subsingleton_iff_of_homotopyEquiv
        (deletedJoinHomeomorph K).toHomotopyEquiv k).mpr
          (ModuleCat.subsingleton_of_isZero hD))
  exact AffChain.isZero_relativeHomology (deletedJoinInBoundaryJoin K (k + 1) m) k hX hA

/-! ### The remaining duality inputs, stated explicitly -/

/-- **The Alexander form of the missing duality**: for the compact pair
`(J, D)` inside the boundary join, vanishing of the relative homology
`H_{m·n}(J, J∖D)` implies vanishing of the real singular homology of `D` in
the complementary degree `n - 1`. This is the statement
`H_{m·n}(J, J∖D) ≅ H^{n-1}(D)` in vanishing form (over the real field
cohomology vanishes exactly when homology does). It is *not* proved here. -/
def AlexanderFormDualityInput (n m : ℕ) : Prop :=
  IsZero (AffChain.relativeHomology (complementInBoundaryJoin K n m) (m * n)) →
    IsZero ((realSingularHomology (n - 1)).obj
      (TopCat.of ↥(simplicialDeletedJoinCarrier n K m)))

/-- **The Lefschetz form of the missing duality**: vanishing of the singular
homology of the open complement `J∖D` in degree `m·n-1` implies vanishing of
the relative homology `H_n(J, D)`, which is the statement
`H_n(J, D) ≅ H^{m·n-1}(J∖D)` in vanishing form. It is *not* proved here. -/
def LefschetzFormDualityInput (n m : ℕ) : Prop :=
  IsZero ((realSingularHomology (m * n - 1)).obj
      (TopCat.of ↥(simplicialBoundaryJoinCarrier K n m \ simplicialDeletedJoinCarrier n K m))) →
    IsZero (AffChain.relativeHomology (deletedJoinInBoundaryJoin K n m) n)

/-- The Alexander form of duality gives the deleted-join vanishing, using the
unconditional complement computation of this file. -/
theorem isZero_deletedJoin_homology_of_alexanderForm
    (hfin : K.faces.Finite) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hsph : BoundaryJoinSpherePresentation K n m)
    (hdual : AlexanderFormDualityInput K n m) :
    IsZero ((realSingularHomology (n - 1)).obj
      (TopCat.of ↥(simplicialDeletedJoinCarrier n K m))) :=
  hdual (isZero_relativeHomology_boundaryJoin_complement K hfin hm hn hsph)

/-- The Lefschetz form of duality gives the deleted-join vanishing, using the
unconditional exact-sequence reduction of this file and the already proved
complement homology theorem. -/
theorem isZero_deletedJoin_homology_of_lefschetzForm
    (hfin : K.faces.Finite) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hsph : BoundaryJoinSpherePresentation K n m)
    (hdual : LefschetzFormDualityInput K n m) :
    IsZero ((realSingularHomology (n - 1)).obj
      (TopCat.of ↥(simplicialDeletedJoinCarrier n K m))) :=
  isZero_singularHomology_deletedJoin_of_isZero_relative K hn hsph (by omega)
    (hdual (isZero_simplicialBoundaryJoinComplement_homology K hfin hm (by omega)))

/-! ### The single general theorem that is still missing

The two predicates above are tailored to the pair at hand. It is better to
isolate the general statement they are instances of, so that a future proof
is a proof of one standard theorem rather than of a bespoke implication. -/

/-- A finite polyhedron: a finite union of convex hulls of finite point sets.
Both the boundary join and the deleted join are of this form. -/
def IsFinitePolyhedron {E : Type} [AddCommGroup E] [Module ℝ E] (S : Set E) : Prop :=
  ∃ C : Set (Finset E), C.Finite ∧ S = ⋃ v ∈ C, convexHull ℝ (v : Set E)

/-- **Alexander duality for a subpolyhedron of a polyhedral topological
sphere, in vanishing form over the real field.** For a finite polyhedron `X`
homeomorphic to the unit sphere of an `(N+1)`-dimensional normed space and a
subpolyhedron `A ⊆ X`, vanishing of the real singular homology of the open
complement `X \ A` in a positive degree `i` implies vanishing of the real
singular homology of `A` in the complementary positive degree `j`, where
`i + j + 1 = N`.

This is the one classical theorem that the geometric-complement step still
needs, and it is **not** proved in this project. It is stated here as a
predicate so that the instance used by the deleted join is a genuine
specialization of a standard result rather than an assumption about the
deleted join itself. -/
def FinitePolyhedralAlexanderDualityStatement : Prop :=
  ∀ (N : ℕ) (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (X A : Set E), IsFinitePolyhedron X → IsFinitePolyhedron A → A ⊆ X →
    (↑X ≃ₜ sphere (0 : F) 1) → Module.finrank ℝ F = N + 1 →
    ∀ i j : ℕ, 0 < i → 0 < j → i + j + 1 = N →
      IsZero ((realSingularHomology i).obj (TopCat.of ↑(X \ A))) →
      IsZero ((realSingularHomology j).obj (TopCat.of ↑A))

theorem isFinitePolyhedron_simplicialBoundaryJoinCarrier (hfin : K.faces.Finite) :
    IsFinitePolyhedron (simplicialBoundaryJoinCarrier K n m) := by
  refine ⟨joinCellVertices '' BoundaryJoinCells K n m,
    (boundaryJoinCells_finite K hfin).image _, ?_⟩
  rw [Set.biUnion_image]
  rfl

theorem isFinitePolyhedron_simplicialDeletedJoinCarrier (hfin : K.faces.Finite) :
    IsFinitePolyhedron (simplicialDeletedJoinCarrier n K m) := by
  refine ⟨joinCellVertices '' BoundaryDeletedJoinCells n K m,
    (boundaryDeletedJoinCells_finite K hfin).image _, ?_⟩
  rw [Set.biUnion_image]
  rfl

/-- **The deleted-join vanishing from the general duality theorem.** Every
other ingredient is discharged here: the complement homology theorem of the
project, the polyhedrality of both sets, the dimension count and the
positivity of both degrees. The sphere presentation of the boundary join is
the separately developed geometric input. -/
theorem isZero_deletedJoin_homology_of_polyhedralAlexanderDuality
    (hdual : FinitePolyhedralAlexanderDualityStatement)
    (hfin : K.faces.Finite) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hsph : BoundaryJoinSpherePresentation K n m) :
    IsZero ((realSingularHomology (n - 1)).obj
      (TopCat.of ↥(simplicialDeletedJoinCarrier n K m))) := by
  have hmn : 2 ≤ m * n := by
    calc 2 = 1 * 2 := by norm_num
      _ ≤ m * n := Nat.mul_le_mul (by omega) (by omega)
  have hprod : (m + 1) * n = m * n + n := by ring
  refine hdual ((m + 1) * n - 1) (PolytopalJoinAmbient e m) (CoordinateSpace ((m + 1) * n))
    (simplicialBoundaryJoinCarrier K n m) (simplicialDeletedJoinCarrier n K m)
    (isFinitePolyhedron_simplicialBoundaryJoinCarrier K hfin)
    (isFinitePolyhedron_simplicialDeletedJoinCarrier K hfin)
    (simplicialDeletedJoinCarrier_subset_boundaryJoin K) hsph ?_
    (m * n - 1) (n - 1) (by omega) (by omega) (by omega)
    (isZero_simplicialBoundaryJoinComplement_homology (K := K) (n := n) (m := m)
      hfin hm (by omega))
  rw [finrank_coordinateSpace]
  omega

end AffineTverberg
