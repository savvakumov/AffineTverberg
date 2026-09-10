import AffineTverberg.CofaceRelativeChains
import AffineTverberg.RelativeHomologyShift

set_option linter.style.header false

/-!
# Puncturing an arbitrary face retracts onto its costar

The radial formula already used for a maximal simplex works for every
nonempty face: its image omits at least one vertex of that face, and hence
lands in the costar. The actual inclusion is a homotopy equivalence.
Consequently every costar in a triangulated topological sphere is
contractible, without a PL hypothesis. This gives the local relative
homology calculation directly in the coface chain model.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric

namespace AffineTverberg.Simplicial

variable {V : Type} [Fintype V] [LinearOrder V]
  {K : Finset (Finset V)} {s : Finset V}

theorem faceCenter_notMem_costar : faceCenter s ∉ barycentricCarrier (costarFamily K s) := by
  rintro ⟨-, -, t, ht, hsupp⟩
  apply (mem_costarFamily.mp ht).2
  intro v hv
  by_contra hvt
  exact (ne_of_gt (faceCenter_pos hv)) (hsupp v hvt)

/-- The radial formula deletes a vertex of the face, even when the face is not maximal. -/
theorem radialRetract_mem_costar (hK : FaceClosed K) (hs : s.Nonempty)
    {x : V → ℝ} (hx : x ∈ barycentricCarrier K) (hne : x ≠ faceCenter s) :
    radialRetract s hs x ∈ barycentricCarrier (costarFamily K s) := by
  obtain ⟨h0, h1, t, htK, hsupp⟩ := hx
  have hlt := card_mul_minOn_lt_one hs h0 h1 hne
  obtain ⟨w, hws, hwval⟩ := exists_eq_minOn hs x
  have hzero := radialRetract_eq_zero_of_eq_minOn hs hws hwval
  refine ⟨fun v => radialRetract_nonneg hs h0 hlt v, radialRetract_sum hs h1 hlt,
    t.erase w, mem_costarFamily.mpr ⟨hK t htK _ (Finset.erase_subset _ _), ?_⟩, ?_⟩
  · intro hsub
    exact Finset.notMem_erase w t (hsub hws)
  · intro v hv
    by_cases hvw : v = w
    · exact hvw ▸ hzero
    · apply radialRetract_eq_zero_of_notMem hs h0
      apply hsupp
      intro hvt
      exact hv (Finset.mem_erase.mpr ⟨hvw, hvt⟩)

theorem radialRetract_eq_self_on_costar (hs : s.Nonempty)
    {x : V → ℝ} (hx : x ∈ barycentricCarrier (costarFamily K s)) :
    radialRetract s hs x = x := by
  obtain ⟨h0, -, t, ht, hsupp⟩ := hx
  have hzero : minOn s hs x = 0 := by
    by_contra hne
    have hpos := lt_of_le_of_ne (minOn_nonneg hs h0) (Ne.symm hne)
    apply (mem_costarFamily.mp ht).2
    intro v hv
    by_contra hvt
    have hvzero := hsupp v hvt
    have hle := minOn_le hs hv x
    linarith
  have hscale : radialScale s hs x = 1 := by simp [radialScale, hzero]
  funext v
  by_cases hv : v ∈ s <;> simp [radialRetract, hscale, hzero, hv]

def costarPuncturedRetract (hK : FaceClosed K) (hs : s.Nonempty) :
    C(↥(punctured K s), ↥(barycentricCarrier (costarFamily K s))) where
  toFun x := ⟨radialRetract s hs x.val.val,
    radialRetract_mem_costar hK hs x.val.property x.property⟩
  continuous_toFun := (continuous_radialRetract_punctured hs).subtype_mk _

def costarPuncturedInclusion :
    C(↥(barycentricCarrier (costarFamily K s)), ↥(punctured K s)) where
  toFun x := ⟨⟨x.val, barycentricCarrier_mono (costarFamily_subset K s) x.property⟩,
    fun h => faceCenter_notMem_costar (h ▸ x.property)⟩
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem costarPuncturedRetract_comp_inclusion (hK : FaceClosed K) (hs : s.Nonempty) :
    (costarPuncturedRetract hK hs).comp costarPuncturedInclusion = ContinuousMap.id _ := by
  ext x
  exact congrFun (radialRetract_eq_self_on_costar hs x.property) _

def costarPuncturedHomotopy (hK : FaceClosed K) (hs : s.Nonempty) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(punctured K s))
      (costarPuncturedInclusion.comp (costarPuncturedRetract hK hs)) where
  toFun p := ⟨⟨puncturedHomotopyMap hs p, puncturedHomotopyMap_mem hs p⟩,
    puncturedHomotopyMap_ne hs p⟩
  continuous_toFun :=
    ((continuous_puncturedHomotopyMap hs).subtype_mk _).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    change (1 - (0 : ℝ)) * x.val.val v + (0 : ℝ) * radialRetract s hs x.val.val v = x.val.val v
    ring
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    change (1 - (1 : ℝ)) * x.val.val v + (1 : ℝ) * radialRetract s hs x.val.val v =
      radialRetract s hs x.val.val v
    ring

/-- The actual costar inclusion is a homotopy inverse to radial projection. -/
def costarPuncturedHomotopyEquiv (hK : FaceClosed K) (hs : s.Nonempty) :
    ContinuousMap.HomotopyEquiv ↥(punctured K s) ↥(barycentricCarrier (costarFamily K s)) where
  toFun := costarPuncturedRetract hK hs
  invFun := costarPuncturedInclusion
  left_inv := ⟨(costarPuncturedHomotopy hK hs).symm⟩
  right_inv := by rw [costarPuncturedRetract_comp_inclusion hK hs]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- This holds for every nonempty face of a topological sphere, not only its facets. -/
theorem contractibleSpace_costar_of_homeomorph_sphere (hK : FaceClosed K)
    (hsK : s ∈ K) (hs : s.Nonempty)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1) :
    ContractibleSpace ↥(barycentricCarrier (costarFamily K s)) := by
  let p : ↥(barycentricCarrier K) :=
    ⟨faceCenter s, barycentricFace_subset_carrier hsK (faceCenter_mem_barycentricFace hs)⟩
  have hpun : punctured K s = {x : ↥(barycentricCarrier K) | x ≠ p} := by
    ext x
    change (x.val ≠ p.val) ↔ x ≠ p
    exact not_congr Subtype.ext_iff.symm
  have : ContractibleSpace ↥(punctured K s) := by
    rw [hpun]
    exact contractibleSpace_punctured_of_homeomorph_normSphere e p
  exact (costarPuncturedHomotopyEquiv hK hs).symm.contractibleSpace

/-- Global-to-costar-relative restriction is the actual projection and is an isomorphism. -/
theorem isIso_costar_relPi_of_homeomorph_sphere (hK : FaceClosed K)
    (hsK : s ∈ K) (hs : s.Nonempty)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1) (k : ℕ) (hk : k ≠ 0) :
    IsIso (AffChain.relPi (subcomplexRealization (costarFamily K s) K) (k + 1)) := by
  have : ContractibleSpace (barySpace (costarFamily K s)) :=
    contractibleSpace_costar_of_homeomorph_sphere hK hsK hs e
  have : ContractibleSpace ↥(subcomplexRealization (costarFamily K s) K) :=
    (subcomplexRealizationHomeomorph
      (costarFamily_subset K s)).symm.toHomotopyEquiv.contractibleSpace
  exact AffChain.isIso_relPi_of_contractible _ k hk

/-- In the concrete simplicial model the isomorphism is induced by literal coface restriction. -/
theorem isIso_cofaceProjection_homology_of_homeomorph_sphere (hK : FaceClosed K)
    (hsK : s ∈ K) (hs : s.Nonempty)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1) (k : ℕ) (hk : k ≠ 0) :
    IsIso (HomologicalComplex.homologyMap (cofaceProjection hK s) (k + 1)) := by
  have : IsIso (HomologicalComplex.homologyMap (comparisonChainMap hK) (k + 1)) :=
    isIso_comparisonHomologyMap hK (k + 1)
  have : IsIso (HomologicalComplex.homologyMap
      (AffChain.relProj (subcomplexRealization (costarFamily K s) K)) (k + 1)) :=
    isIso_costar_relPi_of_homeomorph_sphere hK hsK hs e k hk
  have := quasiIso_cofaceComparisonChainMap hK s
  have hcomm := congrArg (fun f => HomologicalComplex.homologyMap f (k + 1))
    (cofaceComparisonChainMap_proj hK s)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hcomm
  have : IsIso (HomologicalComplex.homologyMap (cofaceProjection hK s) (k + 1) ≫
      HomologicalComplex.homologyMap (cofaceComparisonChainMap hK s) (k + 1)) := by
    rw [hcomm]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (HomologicalComplex.homologyMap (cofaceComparisonChainMap hK s) (k + 1))

/-- The explicit coface complex has the homology of the ambient sphere in degrees at least two. -/
def sphereHomologyIsoCoface (hK : FaceClosed K) (hsK : s ∈ K) (hs : s.Nonempty)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1) (k : ℕ) (hk : k ≠ 0) :
    (realSingularHomology (k + 1)).obj (barySpace K) ≅ (cofaceComplex hK s).homology (k + 1) := by
  have := isIso_costar_relPi_of_homeomorph_sphere hK hsK hs e k hk
  let eπ := asIso (AffChain.relPi (X := barySpace K)
    (subcomplexRealization (costarFamily K s) K) (k + 1))
  exact eπ ≪≫ (cofaceRelativeHomologyIso hK s (k + 1)).symm

end AffineTverberg.Simplicial
