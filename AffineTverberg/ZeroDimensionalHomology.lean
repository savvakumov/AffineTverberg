import AffineTverberg.ReducedHomologyInvariance

set_option linter.style.header false

/-!
# The augmentation kernel of a zero-dimensional realization

For a finite complex with no edges, ordinary H0 is the vertex chain module.
This identification commutes with the actual augmentation. Consequently the
kernel of the genuine singular H0 augmentation is the reduced vertex cycle
space. This is used for the one-dimensional relative dual-block endpoint.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.Simplicial

variable {V : Type} [Fintype V] [LinearOrder V] {K : Finset (Finset V)}

theorem isZero_simplicialChains_one_of_card_le_one (hK : FaceClosed K)
    (htop : ∀ t ∈ K, t.card ≤ 1) : IsZero ((simplicialChains hK).X 1) := by
  have hzero : ∀ c ∈ chains ℝ K 2, c = 0 := by
    intro c hc
    funext t
    by_contra h
    obtain ⟨ht, hcard⟩ := hc t h
    have := htop t ht
    omega
  have : Subsingleton ↥(chains ℝ K 2) :=
    ⟨fun c d => Subtype.ext ((hzero c.val c.property).trans (hzero d.val d.property).symm)⟩
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of ℝ ↥(chains ℝ K 2))

theorem isIso_simplicial_pOpcycles_zero (hK : FaceClosed K)
    (htop : ∀ t ∈ K, t.card ≤ 1) : IsIso ((simplicialChains hK).pOpcycles 0) :=
  (simplicialChains hK).isIso_pOpcycles 1 0 (by simp)
    ((isZero_simplicialChains_one_of_card_le_one hK htop).eq_zero_of_src _)

/-- The canonical identification of H0 with vertex chains when there are no edges. -/
def simplicialHomologyZeroChainIso (hK : FaceClosed K)
    (htop : ∀ t ∈ K, t.card ≤ 1) :
    (simplicialChains hK).homology 0 ≅ ModuleCat.of ℝ ↥(chains ℝ K 1) := by
  have := isIso_simplicial_pOpcycles_zero hK htop
  exact (simplicialChains hK).isoHomologyι₀ ≪≫ (asIso ((simplicialChains hK).pOpcycles 0)).symm

theorem simplicialHomologyZeroChainIso_augmentation (hK : FaceClosed K)
    (htop : ∀ t ∈ K, t.card ≤ 1) :
    (simplicialHomologyZeroChainIso hK htop).hom ≫ simplicialAug hK =
      augHomology (simplicialChains hK) (simplicialAug hK) (d_simplicialAug hK) := by
  let C := simplicialChains hK
  have := isIso_simplicial_pOpcycles_zero hK htop
  let desc := C.descOpcycles (simplicialAug hK) 1 (by simp) (d_simplicialAug hK)
  have hp : C.pOpcycles 0 ≫ desc = simplicialAug hK :=
    C.p_descOpcycles (simplicialAug hK) 1 (by simp) (d_simplicialAug hK)
  have hcancel : inv (C.pOpcycles 0) ≫ simplicialAug hK = desc := by
    rw [← hp]
    simp
  change (C.isoHomologyι₀.hom ≫ inv (C.pOpcycles 0)) ≫ simplicialAug hK =
    C.isoHomologyι₀.hom ≫ desc
  rw [Category.assoc, hcancel]

/-- The chain augmentation kernel is precisely the reduced vertex cycle space. -/
def simplicialAugmentationKernelCyclesEquiv (hK : FaceClosed K) :
    ↥(kernel (simplicialAug hK)) ≃ₗ[ℝ] ↥(cycles ℝ K 1) := by
  have hker : LinearMap.ker (simplicialAug hK).hom =
      Submodule.comap (chains ℝ K 1).subtype (cycles ℝ K 1) := by
    ext c
    change augmentation ℝ V c.val = 0 ↔ c.val ∈ cycles ℝ K 1
    constructor
    · intro h
      exact ⟨c.property, (boundary_eq_zero_iff_augmentation_of_mem_chains_one c.property).mpr h⟩
    · intro h
      exact (boundary_eq_zero_iff_augmentation_of_mem_chains_one c.property).mp h.2
  have eqv : ↥(LinearMap.ker (simplicialAug hK).hom) ≃ₗ[ℝ] ↥(cycles ℝ K 1) := by
    rw [hker]
    exact Submodule.comapSubtypeEquivOfLe (fun c hc => hc.1)
  exact (ModuleCat.kernelIsoKer (simplicialAug hK)).toLinearEquiv.trans eqv

/-- The actual singular augmentation kernel is the reduced vertex cycle
space when the finite complex has no edges. -/
def singularAugmentationKernelTopEquiv (hK : FaceClosed K)
    (htop : ∀ t ∈ K, t.card ≤ 1) :
    ↥(kernel (realSingularAugmentation (barySpace K))) ≃ₗ[ℝ] ↥(cycles ℝ K 1) := by
  have := isIso_comparisonHomologyMap hK 0
  let e₁ := (kernelIsIsoComp (comparisonHomologyMap hK 0)
    (realSingularAugmentation (barySpace K))).symm ≪≫
    kernelIsoOfEq (comparisonHomologyMap_zero_realSingularAugmentation hK)
  let e₂ := (kernelIsoOfEq (simplicialHomologyZeroChainIso_augmentation hK htop)).symm ≪≫
    kernelIsIsoComp (simplicialHomologyZeroChainIso hK htop).hom (simplicialAug hK)
  exact (e₁ ≪≫ e₂).toLinearEquiv.trans (simplicialAugmentationKernelCyclesEquiv hK)

end AffineTverberg.Simplicial
