import AffineTverberg.PolytopalTopIncidence

set_option linter.style.header false

/-!
# The paper's affine-support face description of `Y`

Claim 5.2 uses the parameter set `S_F` defined by existence of one affine
majorant on the base, tight on the whole face `F`. This file states that
definition literally, including the unit-sphere condition, and proves the
claimed union over nonempty exposed faces. No facewise-support equivalence,
polyhedral presentation, or cohomological assertion is assumed.
-/

noncomputable section

open Set

namespace AffineTverberg

namespace PolytopalJoinMap

variable {n m : ℕ} {P : FullDimensionalPolytope n}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (Φ : PolytopalJoinMap P m V)

/-- Exactly the paper's `S_F`: a unit functional with an affine upper
support on `P` that is tight on every point of `F`. -/
def paperFaceParameterSet (F : Set (PolytopalJoinAmbient n m)) :
    Set (StrongDual ℝ V) :=
  {y | ‖y‖ = 1 ∧ ∃ γ : CoordinateSpace n →ᵃ[ℝ] ℝ,
    (∀ w ∈ polytopalJoinCarrier P m,
      y (Φ.joinMap w) ≤ γ (polytopalJoinProjection n m w)) ∧
    ∀ z ∈ F, y (Φ.joinMap z) = γ (polytopalJoinProjection n m z)}

/-- An actual affine upper-support certificate supplies the paper's
parameter condition on its entire contact face. -/
theorem mem_paperFaceParameterSet_contactSet
    (y : StrongDual ℝ V) (hy : ‖y‖ = 1)
    (c : CompactConvexProjection.UpperSupportCertificate (Φ.upperEnvelopeData y)) :
    y ∈ Φ.paperFaceParameterSet c.contactSet := by
  refine ⟨hy, c.slope.toLinearMap.toAffineMap +
    AffineMap.const ℝ (CoordinateSpace n) c.intercept, ?_, ?_⟩
  · intro w hw
    exact c.upper_bound w hw
  · intro z hz
    exact hz.2

/-- Tightness of an affine majorant implies fiberwise maximality. -/
theorem subset_topLocus_of_mem_paperFaceParameterSet
    {F : Set (PolytopalJoinAmbient n m)}
    (hF : F ⊆ polytopalJoinCarrier P m) {y : StrongDual ℝ V}
    (hy : y ∈ Φ.paperFaceParameterSet F) :
    F ⊆ (Φ.upperEnvelopeData y).topLocus := by
  obtain ⟨_, γ, hupper, htight⟩ := hy
  intro z hz
  rw [CompactConvexProjection.mem_topLocus_iff]
  refine ⟨hF hz, ?_⟩
  intro w hw hproj
  change y (Φ.joinMap w) ≤ y (Φ.joinMap z)
  calc
    y (Φ.joinMap w) ≤ γ (polytopalJoinProjection n m w) := hupper w hw
    _ = γ (polytopalJoinProjection n m z) := congrArg γ hproj
    _ = y (Φ.joinMap z) := (htight z hz).symm

/-- **Claim 5.2 (`Y-face-description`), with the paper's actual parameter
definition.** The union ranges over all nonempty exposed faces of `Q`. -/
theorem deletedJoinTopLocus_eq_paperFaceUnion
    (y : StrongDual ℝ V) (hy : ‖y‖ = 1) :
    Φ.deletedJoinTopLocus y =
      ⋃ F : {F : Set (PolytopalJoinAmbient n m) //
        IsExposed ℝ (polytopalJoinCarrier P m) F ∧ F.Nonempty},
        ⋃ (_ : y ∈ Φ.paperFaceParameterSet F.val),
          polytopalDeletedJoinCarrier P m ∩ F.val := by
  ext z
  constructor
  · rintro ⟨hzD, hztop⟩
    obtain ⟨c, hzc⟩ :=
      CompactConvexProjection.exists_upperSupportCertificate_mem_contactSet_of_convexHull
        (Φ.upperEnvelopeData y) (polytopalJoinVertices P m) rfl hztop
    exact mem_iUnion.2 ⟨⟨c.contactSet, c.contactSet_isExposed, c.contactSet_nonempty⟩,
      mem_iUnion.2 ⟨Φ.mem_paperFaceParameterSet_contactSet y hy c, hzD, hzc⟩⟩
  · intro hz
    obtain ⟨F, hz⟩ := mem_iUnion.1 hz
    obtain ⟨hFy, hzD, hzF⟩ := mem_iUnion.1 hz
    exact ⟨hzD, Φ.subset_topLocus_of_mem_paperFaceParameterSet F.2.1.subset hFy hzF⟩

/-- The same description with a finite index set of genuine exposed faces,
retaining precisely the paper's affine-support condition. -/
theorem topIncidenceSet_eq_finite_paperFaceUnion :
    Φ.topIncidenceSet =
      ⋃ T : PolytopalJoinExposedFaceIndex P m,
        ⋃ (_ : (polytopalJoinFaceCarrier T.val).Nonempty),
          (polytopalDeletedJoinCarrier P m ∩ polytopalJoinFaceCarrier T.val) ×ˢ
            Φ.paperFaceParameterSet (polytopalJoinFaceCarrier T.val) := by
  ext p
  constructor
  · rintro ⟨hpD, hynorm, hptop⟩
    obtain ⟨T, hTS, hpT, c, hTc⟩ :=
      CompactConvexProjection.exists_tightVertexSubset_of_mem_topLocus
        (Φ.upperEnvelopeData p.2) (polytopalJoinVertices P m) rfl hptop
    let T' : PolytopalJoinFaceIndex P m := ⟨T, Finset.mem_powerset.2 hTS⟩
    have hTc' : polytopalJoinFaceCarrier T' = c.contactSet := hTc
    have hTexposed : IsExposed ℝ (polytopalJoinCarrier P m)
        (polytopalJoinFaceCarrier T') := hTc' ▸ c.contactSet_isExposed
    refine mem_iUnion.2 ⟨⟨T', hTexposed⟩, mem_iUnion.2 ⟨⟨p.1, hpT⟩, ⟨hpD, hpT⟩, ?_⟩⟩
    rw [hTc']
    exact Φ.mem_paperFaceParameterSet_contactSet p.2 hynorm c
  · intro hp
    obtain ⟨T, hp⟩ := mem_iUnion.1 hp
    obtain ⟨_, ⟨hpD, hpT⟩, hpS⟩ := mem_iUnion.1 hp
    exact ⟨hpD, hpS.1,
      Φ.subset_topLocus_of_mem_paperFaceParameterSet T.2.subset hpS hpT⟩

end PolytopalJoinMap

end AffineTverberg
