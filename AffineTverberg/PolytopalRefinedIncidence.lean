import AffineTverberg.PolytopalTopIncidence

set_option linter.style.header false

/-!
# A finite refined incidence space for the polytopal zero theorem

The paper's incidence space `X` needs a finite face family on the deleted
join which both contains the supporting piece through every point of `Y` and
has a minimal member through every point of `D`.  We obtain such a family by
taking all finite intersections of deleted-join cells and exposed faces of
the full join, requiring at least one deleted cell in every intersection.

These refined pieces are compact and convex, cover `D`, and are closed under
the relevant intersections.  The intersection of all generators containing
a point is consequently a canonical minimal piece.  If the join map avoids
zero on `D`, its image has the compact-convex zero-avoidance properties used
in `Incidence.lean`, so every fiber of `X → D` is contractible.
-/

noncomputable section

open Set

namespace AffineTverberg

/-- Generators for the common finite refinement: deleted cells and exposed
faces of the full join. -/
abbrev PolytopalIncidenceGenerator {n : ℕ}
    (P : FullDimensionalPolytope n) (m : ℕ) :=
  PolytopalDeletedCellIndex P m ⊕ PolytopalJoinExposedFaceIndex P m

/-- The carrier of one generator of the common refinement. -/
def polytopalIncidenceGeneratorCarrier {n m : ℕ}
    {P : FullDimensionalPolytope n} (g : PolytopalIncidenceGenerator P m) :
    Set (PolytopalJoinAmbient n m) :=
  match g with
  | Sum.inl C => C.carrier
  | Sum.inr T => polytopalJoinFaceCarrier T.val

namespace PolytopalIncidenceGenerator

variable {n m : ℕ} {P : FullDimensionalPolytope n}

theorem compact (g : PolytopalIncidenceGenerator P m) :
    IsCompact (polytopalIncidenceGeneratorCarrier g) := by
  cases g with
  | inl C => exact C.compact
  | inr T => exact PolytopalJoinFaceIndex.compact T.val

theorem isClosed (g : PolytopalIncidenceGenerator P m) :
    IsClosed (polytopalIncidenceGeneratorCarrier g) :=
  g.compact.isClosed

theorem convex (g : PolytopalIncidenceGenerator P m) :
    Convex ℝ (polytopalIncidenceGeneratorCarrier g) := by
  cases g with
  | inl C => exact C.convex
  | inr T => exact PolytopalJoinFaceIndex.convex T.val

end PolytopalIncidenceGenerator

/-- A refined face is a finite intersection of generators which includes at
least one deleted cell.  The latter condition ensures that its carrier lies
in `D`. -/
abbrev PolytopalRefinedFaceIndex {n : ℕ}
    (P : FullDimensionalPolytope n) (m : ℕ) :=
  {S : Finset (PolytopalIncidenceGenerator P m) //
    ∃ C : PolytopalDeletedCellIndex P m, Sum.inl C ∈ S}

namespace PolytopalRefinedFaceIndex

variable {n m : ℕ} {P : FullDimensionalPolytope n}

noncomputable instance : Fintype (PolytopalJoinExposedFaceIndex P m) :=
  Fintype.ofFinite _

noncomputable instance : Fintype (PolytopalRefinedFaceIndex P m) :=
  Fintype.ofFinite _

/-- The intersection represented by a refined face. -/
def carrier (F : PolytopalRefinedFaceIndex P m) :
    Set (PolytopalJoinAmbient n m) :=
  ⋂ g ∈ F.val, polytopalIncidenceGeneratorCarrier g

theorem mem_carrier_iff (F : PolytopalRefinedFaceIndex P m)
    (z : PolytopalJoinAmbient n m) :
    z ∈ F.carrier ↔
      ∀ g ∈ F.val, z ∈ polytopalIncidenceGeneratorCarrier g := by
  simp [carrier]

theorem isClosed (F : PolytopalRefinedFaceIndex P m) : IsClosed F.carrier := by
  rw [carrier]
  exact isClosed_biInter fun g _hg ↦ g.isClosed

theorem convex (F : PolytopalRefinedFaceIndex P m) : Convex ℝ F.carrier := by
  rw [carrier]
  exact convex_iInter₂ fun g _hg ↦ g.convex

theorem compact (F : PolytopalRefinedFaceIndex P m) : IsCompact F.carrier := by
  obtain ⟨C, hC⟩ := F.property
  refine C.compact.of_isClosed_subset F.isClosed ?_
  intro z hz
  exact (F.mem_carrier_iff z).mp hz (Sum.inl C) hC

theorem subset_deletedJoinCarrier (F : PolytopalRefinedFaceIndex P m) :
    F.carrier ⊆ polytopalDeletedJoinCarrier P m := by
  obtain ⟨C, hC⟩ := F.property
  intro z hz
  rw [polytopalDeletedJoinCarrier]
  exact Set.mem_iUnion.mpr
    ⟨C, (F.mem_carrier_iff z).mp hz (Sum.inl C) hC⟩

/-- The two-generator refinement piece cut out by a deleted cell and an
exposed join face. -/
def ofCellAndExposedFace (C : PolytopalDeletedCellIndex P m)
    (T : PolytopalJoinExposedFaceIndex P m) : PolytopalRefinedFaceIndex P m := by
  classical
  exact ⟨{Sum.inl C, Sum.inr T}, C, by simp⟩

theorem mem_ofCellAndExposedFace_iff
    (C : PolytopalDeletedCellIndex P m)
    (T : PolytopalJoinExposedFaceIndex P m)
    (z : PolytopalJoinAmbient n m) :
    z ∈ (ofCellAndExposedFace C T).carrier ↔
      z ∈ C.carrier ∧ z ∈ polytopalJoinFaceCarrier T.val := by
  simp [carrier, ofCellAndExposedFace, polytopalIncidenceGeneratorCarrier]

end PolytopalRefinedFaceIndex

/-- The generators which contain a given point. -/
def polytopalIncidenceGeneratorsAt {n m : ℕ}
    {P : FullDimensionalPolytope n} (z : PolytopalJoinAmbient n m) :
    Finset (PolytopalIncidenceGenerator P m) := by
  classical
  exact Finset.univ.filter fun g ↦ z ∈ polytopalIncidenceGeneratorCarrier g

/-- The canonical minimal refined face through a point of the deleted join:
intersect every generator which contains the point. -/
def minimalPolytopalRefinedFace {n m : ℕ}
    {P : FullDimensionalPolytope n}
    (z : PolytopalDeletedJoinSpace P m) : PolytopalRefinedFaceIndex P m := by
  classical
  refine ⟨polytopalIncidenceGeneratorsAt z.val, ?_⟩
  have hzD := z.property
  change z.val ∈ ⋃ C : PolytopalDeletedCellIndex P m, C.carrier at hzD
  obtain ⟨C, hzC⟩ := Set.mem_iUnion.mp hzD
  refine ⟨C, ?_⟩
  simp only [polytopalIncidenceGeneratorsAt, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change z.val ∈ C.carrier
  exact hzC

namespace PolytopalRefinedFaceIndex

variable {n m : ℕ} {P : FullDimensionalPolytope n}

theorem mem_minimal (z : PolytopalDeletedJoinSpace P m) :
    z.val ∈ (minimalPolytopalRefinedFace z).carrier := by
  rw [mem_carrier_iff]
  intro g hg
  simpa [minimalPolytopalRefinedFace, polytopalIncidenceGeneratorsAt] using hg

theorem minimal_subset (z : PolytopalDeletedJoinSpace P m)
    (F : PolytopalRefinedFaceIndex P m) (hzF : z.val ∈ F.carrier) :
    (minimalPolytopalRefinedFace z).carrier ⊆ F.carrier := by
  intro w hw
  rw [mem_carrier_iff] at hw ⊢
  intro g hg
  apply hw g
  simp only [minimalPolytopalRefinedFace, polytopalIncidenceGeneratorsAt,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact (F.mem_carrier_iff z.val).mp hzF g hg

end PolytopalRefinedFaceIndex

namespace PolytopalJoinMap

variable {n m : ℕ} {P : FullDimensionalPolytope n}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (Φ : PolytopalJoinMap P m V)

/-- The refined finite incidence space `X`. -/
abbrev RefinedFaceIncidenceSpace :=
  FaceIncidenceSpace (polytopalDeletedJoinCarrier P m)
    (PolytopalRefinedFaceIndex.carrier (P := P) (m := m))
    (fun z ↦ Φ.joinMap z)

/-- First projection `X → D`. -/
def refinedFaceIncidenceProjection :
    Φ.RefinedFaceIncidenceSpace → PolytopalDeletedJoinSpace P m :=
  faceIncidenceProjection

theorem refinedFaceIncidenceProjection_continuous :
    Continuous Φ.refinedFaceIncidenceProjection :=
  continuous_faceIncidenceProjection

/-- Second projection `X → S(V*)`. -/
def refinedFaceIncidenceDualProjection :
    Φ.RefinedFaceIncidenceSpace → DualUnitSphere V :=
  fun p ↦ ⟨p.val.snd, p.property.1⟩

theorem refinedFaceIncidenceDualProjection_continuous :
    Continuous Φ.refinedFaceIncidenceDualProjection := by
  apply Continuous.subtype_mk
  exact continuous_snd.comp continuous_subtype_val

/-- Every point of `Y` belongs to a refined deleted-join piece on which its
dual height is nonnegative. -/
noncomputable def topIncidenceToRefinedFaceIncidence
    (p : Φ.TopIncidenceSpace) : Φ.RefinedFaceIncidenceSpace := by
  have hzD := p.val.fst.property
  change p.val.fst.val ∈ ⋃ C : PolytopalDeletedCellIndex P m, C.carrier at hzD
  let C := Classical.choose (Set.mem_iUnion.mp hzD)
  have hzC := Classical.choose_spec (Set.mem_iUnion.mp hzD)
  have hT :=
    Φ.exists_exposedJoinFace_nonnegative_of_mem_topLocus
      p.val.snd.val p.property
  let T := Classical.choose hT
  have hTspec := Classical.choose_spec hT
  have hzT := hTspec.1
  have hnonneg := hTspec.2.2
  let F := PolytopalRefinedFaceIndex.ofCellAndExposedFace C T
  refine ⟨(p.val.fst, p.val.snd.val), p.val.snd.property, F, ?_, ?_⟩
  · exact (PolytopalRefinedFaceIndex.mem_ofCellAndExposedFace_iff C T _).mpr
      ⟨hzC, hzT⟩
  · intro w hw
    apply hnonneg w
    exact (PolytopalRefinedFaceIndex.mem_ofCellAndExposedFace_iff C T w).mp hw |>.2

@[simp]
theorem topIncidenceToRefinedFaceIncidence_fst (p : Φ.TopIncidenceSpace) :
    (Φ.topIncidenceToRefinedFaceIncidence p).val.fst = p.val.fst := by
  rfl

@[simp]
theorem topIncidenceToRefinedFaceIncidence_snd (p : Φ.TopIncidenceSpace) :
    (Φ.topIncidenceToRefinedFaceIncidence p).val.snd = p.val.snd.val := by
  rfl

theorem topIncidenceToRefinedFaceIncidence_injective :
    Function.Injective Φ.topIncidenceToRefinedFaceIncidence := by
  intro p q hpq
  have h1 := congrArg (fun r : Φ.RefinedFaceIncidenceSpace ↦ r.val.fst) hpq
  have h2 := congrArg (fun r : Φ.RefinedFaceIncidenceSpace ↦ r.val.snd) hpq
  simp only [Φ.topIncidenceToRefinedFaceIncidence_fst] at h1
  simp only [Φ.topIncidenceToRefinedFaceIncidence_snd] at h2
  apply Subtype.ext
  exact Prod.ext h1 (Subtype.ext h2)

theorem topIncidenceToRefinedFaceIncidence_continuous :
    Continuous Φ.topIncidenceToRefinedFaceIncidence := by
  apply Continuous.subtype_mk
  change Continuous (fun p ↦ (Φ.topIncidenceToRefinedFaceIncidence p).val)
  convert (continuous_fst.comp
      (continuous_subtype_val : Continuous (fun p : Φ.TopIncidenceSpace ↦ p.val))).prodMk
    ((continuous_subtype_val : Continuous (fun y : DualUnitSphere V ↦ y.val)).comp
      (continuous_snd.comp
        (continuous_subtype_val : Continuous (fun p : Φ.TopIncidenceSpace ↦ p.val)))) using 1
  funext p
  exact Prod.ext (Φ.topIncidenceToRefinedFaceIncidence_fst p)
    (Φ.topIncidenceToRefinedFaceIncidence_snd p)

@[simp]
theorem refinedFaceIncidenceProjection_topIncidenceToRefinedFaceIncidence
    (p : Φ.TopIncidenceSpace) :
    Φ.refinedFaceIncidenceProjection (Φ.topIncidenceToRefinedFaceIncidence p) =
      p.val.fst := by
  exact Φ.topIncidenceToRefinedFaceIncidence_fst p

@[simp]
theorem refinedFaceIncidenceDualProjection_topIncidenceToRefinedFaceIncidence
    (p : Φ.TopIncidenceSpace) :
    Φ.refinedFaceIncidenceDualProjection (Φ.topIncidenceToRefinedFaceIncidence p) =
      Φ.topIncidenceProjection p := by
  apply Subtype.ext
  exact Φ.topIncidenceToRefinedFaceIncidence_snd p

/-- The refined incidence space is compact. -/
theorem refinedFaceIncidenceSpace_compactSpace [FiniteDimensional ℝ V] :
    CompactSpace Φ.RefinedFaceIncidenceSpace :=
  faceIncidenceSpace_compactSpace (polytopalDeletedJoinCarrier_compact P)
    fun F ↦ F.isClosed

/-- Minimal-face data for the refined family, assuming the join map avoids
zero on the whole deleted join. -/
def refinedFaceIncidenceFiberData
    (havoid : (0 : V) ∉ Φ.joinMap '' polytopalDeletedJoinCarrier P m)
    (z : PolytopalDeletedJoinSpace P m) :
    FaceIncidenceFiberData
      (PolytopalRefinedFaceIndex.carrier (P := P) (m := m))
      (fun w ↦ Φ.joinMap w) z.val where
  index := minimalPolytopalRefinedFace z
  mem_face := PolytopalRefinedFaceIndex.mem_minimal z
  minimal := fun F hzF ↦ PolytopalRefinedFaceIndex.minimal_subset z F hzF
  image_convex :=
    (minimalPolytopalRefinedFace z).convex.linear_image Φ.joinMap.toLinearMap
  image_compact :=
    (minimalPolytopalRefinedFace z).compact.image Φ.joinMap.continuous
  image_nonempty :=
    ⟨Φ.joinMap z.val, z.val,
      PolytopalRefinedFaceIndex.mem_minimal z, rfl⟩
  image_avoids_zero := by
    rintro ⟨w, hw, hzero⟩
    exact havoid ⟨w,
      (minimalPolytopalRefinedFace z).subset_deletedJoinCarrier hw, hzero⟩

/-- Under zero avoidance, every fiber of the first projection `X → D` is
contractible. -/
theorem refinedFaceIncidenceFiber_contractible
    (havoid : (0 : V) ∉ Φ.joinMap '' polytopalDeletedJoinCarrier P m)
    (z : PolytopalDeletedJoinSpace P m) :
    ContractibleSpace
      (FaceIncidenceFiber (polytopalDeletedJoinCarrier P m)
        (PolytopalRefinedFaceIndex.carrier (P := P) (m := m))
        (fun w ↦ Φ.joinMap w) z) :=
  faceIncidenceFiber_contractible_of_data z
    (Φ.refinedFaceIncidenceFiberData havoid z)

/-- Under zero avoidance, the first projection `X → D` is surjective. -/
theorem refinedFaceIncidenceProjection_surjective
    (havoid : (0 : V) ∉ Φ.joinMap '' polytopalDeletedJoinCarrier P m) :
    Function.Surjective Φ.refinedFaceIncidenceProjection :=
  faceIncidenceProjection_surjective fun z ↦
    Φ.refinedFaceIncidenceFiberData havoid z

end PolytopalJoinMap

end AffineTverberg
