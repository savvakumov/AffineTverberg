import AffineTverberg.CofaceLinkEndpoints
import AffineTverberg.GeometricRelativeHomologyComparison
import AffineTverberg.DualBlockLinkHomology

set_option linter.style.header false

/-!
# A concrete relative chain model for a dual block

The boundary of a dual block is exactly the costar of its cone apex. Thus
the existing coface comparison gives an actual quasi-isomorphism to the
singular chains of the dual-block pair. Its homology is the reduced homology
of the block boundary in the shifted degree, including ordinary degree zero.
No assertion that the block is a topological ball is needed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.Simplicial

open AffineTverberg.AffChain

section GeometricCoface

variable {V E : Type} [Fintype V] [LinearOrder V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Finset (Finset V)} {p : V → E}

/-- The actual coface-to-relative comparison followed by the actual
geometric realization map of the pair. -/
def geometricCofaceComparisonChainMap (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (L : Finset V) :
    cofaceComplex hK L ⟶ relCx (X := TopCat.of ↥(geometricCarrier K p))
      (geometricSubcomplexRealization (costarFamily K L) K p) :=
  cofaceComparisonChainMap hK L ≫
    geometricRelativeRealizationMap hgeom (costarFamily_subset K L)

theorem quasiIso_geometricCofaceComparisonChainMap (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (L : Finset V) :
    QuasiIso (geometricCofaceComparisonChainMap hK hgeom L) := by
  have := quasiIso_cofaceComparisonChainMap hK L
  have := quasiIso_geometricRelativeRealizationMap hgeom (costarFamily_subset K L)
  dsimp only [geometricCofaceComparisonChainMap]
  infer_instance

def geometricCofaceHomologyIso (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (L : Finset V) (q : ℕ) :
    (cofaceComplex hK L).homology q ≅
      relativeHomology (X := TopCat.of ↥(geometricCarrier K p))
        (geometricSubcomplexRealization (costarFamily K L) K p) q := by
  have := quasiIso_geometricCofaceComparisonChainMap hK hgeom L
  exact asIso (HomologicalComplex.homologyMap
    (geometricCofaceComparisonChainMap hK hgeom L) q)

theorem isZero_geometricCostarHomology_iff_link (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) {L : Finset V} (hL : L.Nonempty)
    (q n : ℕ) (hn : n + L.card = q + 1) :
    IsZero (relativeHomology (X := TopCat.of ↥(geometricCarrier K p))
      (geometricSubcomplexRealization (costarFamily K L) K p) q) ↔
      IsReducedAcyclicAt ℝ (link K L) n := by
  constructor
  · intro h
    exact (isZero_cofaceHomology_iff_link_all hK hL q n hn).mp
      (h.of_iso (geometricCofaceHomologyIso hK hgeom L q))
  · intro h
    exact ((isZero_cofaceHomology_iff_link_all hK hL q n hn).mpr h).of_iso
      (geometricCofaceHomologyIso hK hgeom L q).symm

end GeometricCoface

section Block

variable {V : Type} [Fintype V] [LinearOrder V] [inst : LinearOrder (Finset V)]
  {K : Finset (Finset V)} {s : Finset V}

local instance : DecidableEq (Finset V) := inst.toDecidableEq

/-- Removing the cofaces of the cone apex leaves exactly the block boundary. -/
theorem costar_dualBlock_apex (K : Finset (Finset V)) (s : Finset V) :
    costarFamily (dualBlockFaces K s) {s} = dualBlockBoundaryFaces K s := by
  ext C
  simp only [mem_costarFamily, mem_dualBlockFaces, mem_dualBlockBoundaryFaces,
    Finset.singleton_subset_iff]
  constructor
  · rintro ⟨⟨hC, hsub⟩, hnot⟩
    refine ⟨hC, fun t ht => Finset.ssubset_iff_subset_ne.mpr ⟨hsub t ht, ?_⟩⟩
    intro heq
    exact hnot (heq ▸ ht)
  · rintro ⟨hC, hstrict⟩
    refine ⟨⟨hC, fun t ht => (hstrict t ht).subset⟩, ?_⟩
    intro hsC
    exact (Finset.ssubset_iff_subset_ne.mp (hstrict s hsC)).2 rfl

/-- The link of the cone apex is literally the boundary face family. -/
theorem link_dualBlock_apex (hsK : s ∈ K) (hs : s.Nonempty) :
    link (dualBlockFaces K s) {s} = dualBlockBoundaryFaces K s := by
  rw [← costar_dualBlock_apex]
  ext C
  rw [mem_link_iff, mem_costarFamily]
  constructor
  · rintro ⟨hunion, hdisj⟩
    have hB : FaceClosed (dualBlockFaces K s) := by
      convert faceClosed_dualBlockFaces K s using 1
    refine ⟨hB _ hunion C Finset.subset_union_left, ?_⟩
    simpa only [Finset.singleton_subset_iff] using Finset.disjoint_singleton_right.mp hdisj
  · rintro ⟨hC, hnot⟩
    refine ⟨?_, Finset.disjoint_singleton_right.mpr ?_⟩
    · rw [Finset.union_singleton]
      convert insert_mem_dualBlockFaces hsK hs hC using 1
      ext t
      simp
    · simpa only [Finset.singleton_subset_iff] using hnot

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : V → E}

/-- The actual relative singular homology of the dual-block pair is reduced
boundary homology in the shifted degree, with no restriction on q. -/
theorem isZero_dualBlockRelativeHomology_iff_boundary_acyclic
    (hgeom : IsGeometricRealization K p) (hsK : s ∈ K) (hs : s.Nonempty) (q : ℕ) :
    IsZero (relativeHomology (X := TopCat.of ↥(dualBlockSpace K p s))
      (Subtype.val ⁻¹' dualBlockBoundarySpace K p s) q) ↔
      IsReducedAcyclicAt ℝ (dualBlockBoundaryFaces K s) q := by
  have hB : FaceClosed (dualBlockFaces K s) := by
    convert faceClosed_dualBlockFaces K s using 1
  have hBg : IsGeometricRealization (dualBlockFaces K s) (faceBarycenter p) := by
    have h := @IsGeometricRealization.mono (Finset V) (fun a b => a.decidableEq b)
      E _ _ _ _ _ (isGeometricRealization_subdivisionFaces hgeom) (dualBlockFaces_subset K s)
    convert h using 1
  have h := isZero_geometricCostarHomology_iff_link hB hBg
    (Finset.singleton_nonempty s) q q (by simp)
  rw [link_dualBlock_apex hsK hs] at h
  change IsZero (relativeHomology
    (X := TopCat.of ↥(geometricCarrier (dualBlockFaces K s) (faceBarycenter p)))
    (Subtype.val ⁻¹' geometricCarrier (costarFamily (dualBlockFaces K s) {s})
      (faceBarycenter p)) q) ↔ _ at h
  rw [costar_dualBlock_apex] at h
  exact h

end Block

end AffineTverberg.Simplicial
