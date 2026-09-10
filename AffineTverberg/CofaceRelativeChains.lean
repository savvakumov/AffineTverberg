import AffineTverberg.StarOrientationCycle
import AffineTverberg.RelativeHomologyComparison

set_option linter.style.header false

/-!
# The actual relative chain complex at a face

The costar consists of faces not containing L. The quotient by its chain
complex is represented concretely by chains supported on cofaces of L,
with differential given by the oriented boundary followed by restriction.
The identification below is an isomorphism with the actual categorical
cokernel used by relative simplicial homology, not a new homology definition.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.Simplicial

variable {V : Type} [LinearOrder V] {K : Finset (Finset V)}

/-- The subcomplex of faces which do not contain L. -/
def costarFamily (K : Finset (Finset V)) (L : Finset V) : Finset (Finset V) :=
  K.filter fun s => ¬ L ⊆ s

@[simp]
theorem mem_costarFamily {L s : Finset V} :
    s ∈ costarFamily K L ↔ s ∈ K ∧ ¬ L ⊆ s := Finset.mem_filter

theorem costarFamily_subset (K : Finset (Finset V)) (L : Finset V) : costarFamily K L ⊆ K :=
  fun _ hs => (mem_costarFamily.mp hs).1

theorem faceClosed_costarFamily (hK : FaceClosed K) (L : Finset V) :
    FaceClosed (costarFamily K L) := by
  intro s hs t hts
  obtain ⟨hsK, hLs⟩ := mem_costarFamily.mp hs
  exact mem_costarFamily.mpr ⟨hK s hsK t hts, fun hLt => hLs (hLt.trans hts)⟩

/-- Coefficient functions supported on cofaces of L of the specified cardinality. -/
def cofaceChains (K : Finset (Finset V)) (L : Finset V) (n : ℕ) :
    Submodule ℝ (Finset V → ℝ) := chains ℝ (K.filter fun s => L ⊆ s) n

theorem cofaceChains_le (L : Finset V) (n : ℕ) : cofaceChains K L n ≤ chains ℝ K n :=
  chains_mono (Finset.filter_subset _ _) n

theorem cofaceRestriction_mem_cofaceChains {n : ℕ} {c : Finset V → ℝ}
    (hc : c ∈ chains ℝ K n) (L : Finset V) :
    cofaceRestriction L c ∈ cofaceChains K L n := by
  intro s hs
  have hLs : L ⊆ s := by
    by_contra h
    exact hs (by simp only [cofaceRestriction_apply, h, ite_false])
  have hcs : c s ≠ 0 := by simpa only [cofaceRestriction_apply, hLs, ite_true] using hs
  obtain ⟨hsK, hcard⟩ := hc s hcs
  exact ⟨Finset.mem_filter.mpr ⟨hsK, hLs⟩, hcard⟩

theorem cofaceRestriction_eq_self {L : Finset V} {n : ℕ} {c : Finset V → ℝ}
    (hc : c ∈ cofaceChains K L n) : cofaceRestriction L c = c := by
  funext s
  by_cases hLs : L ⊆ s
  · simp only [cofaceRestriction_apply, hLs, ite_true]
  · have hcs : c s = 0 := by
      by_contra h
      exact hLs (Finset.mem_filter.mp (hc s h).1).2
    simp only [cofaceRestriction_apply, hLs, ite_false, hcs]

theorem cofaceRestriction_eq_zero_iff_costar {L : Finset V} {n : ℕ} {c : Finset V → ℝ}
    (hc : c ∈ chains ℝ K n) :
    cofaceRestriction L c = 0 ↔ c ∈ chains ℝ (costarFamily K L) n := by
  constructor
  · intro hzero s hcs
    obtain ⟨hsK, hcard⟩ := hc s hcs
    refine ⟨mem_costarFamily.mpr ⟨hsK, ?_⟩, hcard⟩
    intro hLs
    have h := congrFun hzero s
    simp only [cofaceRestriction_apply, hLs, ite_true, Pi.zero_apply] at h
    exact hcs h
  · intro hcostar
    funext s
    by_cases hLs : L ⊆ s
    · have hcs : c s = 0 := by
        by_contra h
        exact (mem_costarFamily.mp (hcostar s h).1).2 hLs
      simp only [cofaceRestriction_apply, hLs, ite_true, hcs, Pi.zero_apply]
    · simp only [cofaceRestriction_apply, hLs, ite_false, Pi.zero_apply]

variable [Fintype V]

/-- Projection after taking the boundary is insensitive to a prior coface projection. -/
theorem cofaceRestriction_boundary_cofaceRestriction (L : Finset V) (c : Finset V → ℝ) :
    cofaceRestriction L (boundary ℝ V (cofaceRestriction L c)) =
      cofaceRestriction L (boundary ℝ V c) := by
  funext s
  by_cases hLs : L ⊆ s
  · simpa only [cofaceRestriction_apply, hLs, ite_true] using
      boundary_cofaceRestriction_of_subset hLs c
  · simp only [cofaceRestriction_apply, hLs, ite_false]

/-- The concrete relative differential. -/
def cofaceBoundary (L : Finset V) : (Finset V → ℝ) →ₗ[ℝ] (Finset V → ℝ) :=
  (cofaceRestriction L).comp (boundary ℝ V)

theorem cofaceBoundary_squared (L : Finset V) (c : Finset V → ℝ) :
    cofaceBoundary L (cofaceBoundary L c) = 0 := by
  change cofaceRestriction L (boundary ℝ V (cofaceRestriction L (boundary ℝ V c))) = 0
  rw [cofaceRestriction_boundary_cofaceRestriction, boundary_boundary_apply, map_zero]

theorem cofaceBoundary_mem (hK : FaceClosed K) (L : Finset V) (n : ℕ)
    {c : Finset V → ℝ} (hc : c ∈ cofaceChains K L (n + 1)) :
    cofaceBoundary L c ∈ cofaceChains K L n :=
  cofaceRestriction_mem_cofaceChains (boundary_mem_chains hK (cofaceChains_le L (n + 1) hc)) L

def cofaceDifferential (hK : FaceClosed K) (L : Finset V) (n : ℕ) :
    cofaceChains K L (n + 1) →ₗ[ℝ] cofaceChains K L n :=
  LinearMap.codRestrict _ ((cofaceBoundary L).comp (cofaceChains K L (n + 1)).subtype)
    (fun c => cofaceBoundary_mem hK L n c.property)

/-- The coface chain complex, in ordinary geometric degrees. -/
def cofaceComplex (hK : FaceClosed K) (L : Finset V) :
    ChainComplex (ModuleCat.{0} ℝ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of ℝ ↥(cofaceChains K L (n + 1)))
    (fun n => ModuleCat.ofHom (cofaceDifferential hK L (n + 1)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact Subtype.ext (cofaceBoundary_squared L c.val))

theorem cofaceComplex_d (hK : FaceClosed K) (L : Finset V) (n : ℕ) :
    (cofaceComplex hK L).d (n + 1) n = ModuleCat.ofHom (cofaceDifferential hK L (n + 1)) := by
  simp [cofaceComplex]

def cofaceProjectionLinear (L : Finset V) (n : ℕ) :
    chains ℝ K n →ₗ[ℝ] cofaceChains K L n :=
  LinearMap.codRestrict _ ((cofaceRestriction L).comp (chains ℝ K n).subtype)
    (fun c => cofaceRestriction_mem_cofaceChains c.property L)

/-- The actual projection of the original simplicial complex to its relative coface model. -/
def cofaceProjection (hK : FaceClosed K) (L : Finset V) :
    simplicialChains hK ⟶ cofaceComplex hK L :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (cofaceProjectionLinear L (n + 1)))
    (fun n => by
      rw [simplicialChains_d, cofaceComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact Subtype.ext (cofaceRestriction_boundary_cofaceRestriction L c.val))

theorem cofaceProjection_surjective (hK : FaceClosed K) (L : Finset V) (n : ℕ) :
    Function.Surjective ((cofaceProjection hK L).f n).hom := by
  intro c
  exact ⟨⟨c.val, cofaceChains_le L (n + 1) c.property⟩,
    Subtype.ext (cofaceRestriction_eq_self c.property)⟩

theorem costarInclusion_comp_cofaceProjection (hK : FaceClosed K) (L : Finset V) :
    simplicialChainsInclusion (faceClosed_costarFamily hK L) hK (costarFamily_subset K L) ≫
      cofaceProjection hK L = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  exact (cofaceRestriction_eq_zero_iff_costar
    (chains_mono (costarFamily_subset K L) (n + 1) c.property)).mpr c.property

def cofaceShortComplex (hK : FaceClosed K) (L : Finset V) :
    ShortComplex (ChainComplex (ModuleCat.{0} ℝ) ℕ) :=
  ShortComplex.mk
    (simplicialChainsInclusion (faceClosed_costarFamily hK L) hK (costarFamily_subset K L))
    (cofaceProjection hK L) (costarInclusion_comp_cofaceProjection hK L)

/-- The kernel of the projection is precisely the costar chain complex, in every degree. -/
theorem cofaceShortExact (hK : FaceClosed K) (L : Finset V) :
    (cofaceShortComplex hK L).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have hexact : ((cofaceShortComplex hK L).map
      (HomologicalComplex.eval (ModuleCat.{0} ℝ) (ComplexShape.down ℕ) n)).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro c hc
    have hzero : cofaceRestriction L c.val = 0 := congrArg Subtype.val hc
    have hcostar : c.val ∈ chains ℝ (costarFamily K L) (n + 1) :=
      (cofaceRestriction_eq_zero_iff_costar c.property).mp hzero
    exact ⟨⟨c.val, hcostar⟩, rfl⟩
  exact ShortComplex.ShortExact.mk' hexact
    ((ModuleCat.mono_iff_injective _).mpr
      (Submodule.inclusion_injective (chains_mono (𝕜 := ℝ) (costarFamily_subset K L) (n + 1))))
    ((ModuleCat.epi_iff_surjective _).mpr (cofaceProjection_surjective hK L n))

/-- The concrete coface complex is the actual relative simplicial chain complex. -/
def relativeCofaceIso (hK : FaceClosed K) (L : Finset V) :
    simplicialRelativeCx (faceClosed_costarFamily hK L) hK (costarFamily_subset K L) ≅
      cofaceComplex hK L := by
  have hSES := cofaceShortExact hK L
  have := hSES.epi_g
  exact (cokernelIsCokernel _).coconePointUniqueUpToIso hSES.exact.gIsCokernel

@[reassoc (attr := simp)]
theorem relativeCofaceIso_proj (hK : FaceClosed K) (L : Finset V) :
    cokernel.π (simplicialChainsInclusion (faceClosed_costarFamily hK L) hK
        (costarFamily_subset K L)) ≫ (relativeCofaceIso hK L).hom =
      cofaceProjection hK L := by
  have hSES := cofaceShortExact hK L
  have := hSES.epi_g
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
    hSES.exact.gIsCokernel WalkingParallelPair.one

/-- The coface model maps to the genuine relative singular chain complex. -/
def cofaceComparisonChainMap (hK : FaceClosed K) (L : Finset V) :
    cofaceComplex hK L ⟶ AffChain.relCx (subcomplexRealization (costarFamily K L) K) :=
  (relativeCofaceIso hK L).inv ≫
    relativeComparisonChainMap (faceClosed_costarFamily hK L) hK (costarFamily_subset K L)

/-- The comparison agrees with the original absolute comparison followed by quotient. -/
theorem cofaceComparisonChainMap_proj (hK : FaceClosed K) (L : Finset V) :
    cofaceProjection hK L ≫ cofaceComparisonChainMap hK L =
      comparisonChainMap hK ≫ AffChain.relProj (subcomplexRealization (costarFamily K L) K) := by
  have hcancel : (relativeCofaceIso hK L).hom ≫ cofaceComparisonChainMap hK L =
      relativeComparisonChainMap (faceClosed_costarFamily hK L) hK
        (costarFamily_subset K L) :=
    (relativeCofaceIso hK L).hom_inv_id_assoc _
  calc
    _ = (cokernel.π (simplicialChainsInclusion (faceClosed_costarFamily hK L) hK
        (costarFamily_subset K L)) ≫ (relativeCofaceIso hK L).hom) ≫
          cofaceComparisonChainMap hK L := by rw [relativeCofaceIso_proj]
    _ = cokernel.π (simplicialChainsInclusion (faceClosed_costarFamily hK L) hK
        (costarFamily_subset K L)) ≫
          relativeComparisonChainMap (faceClosed_costarFamily hK L) hK
            (costarFamily_subset K L) :=
      (Category.assoc _ _ _).trans (congrArg (fun f =>
        cokernel.π (simplicialChainsInclusion (faceClosed_costarFamily hK L) hK
          (costarFamily_subset K L)) ≫ f) hcancel)
    _ = _ := relativeComparisonChainMap_proj (faceClosed_costarFamily hK L) hK
      (costarFamily_subset K L)

/-- The explicit coface chain complex computes actual relative singular homology. -/
theorem quasiIso_cofaceComparisonChainMap (hK : FaceClosed K) (L : Finset V) :
    QuasiIso (cofaceComparisonChainMap hK L) := by
  have := quasiIso_relativeComparisonChainMap
    (faceClosed_costarFamily hK L) hK (costarFamily_subset K L)
  dsimp only [cofaceComparisonChainMap]
  infer_instance

def cofaceRelativeHomologyIso (hK : FaceClosed K) (L : Finset V) (k : ℕ) :
    (cofaceComplex hK L).homology k ≅
      AffChain.relativeHomology (subcomplexRealization (costarFamily K L) K) k := by
  have := quasiIso_cofaceComparisonChainMap hK L
  exact asIso (HomologicalComplex.homologyMap (cofaceComparisonChainMap hK L) k)

end AffineTverberg.Simplicial
