import AffineTverberg.CofaceNaturality
import AffineTverberg.RelativeHomologyMaps

set_option linter.style.header false

/-!
# Face restrictions agree with the actual maps of relative pairs

The explicit coface transition is identified, through the actual comparison
maps, with the relative singular map induced by the identity of the carrier
and the inclusion of costars. For a triangulated sphere both costars are
contractible, so this relative map and the coface transition are
quasi-isomorphisms in ALL degrees, including zero and one. This statement
does not assert that ordinary degree-zero homology of a contractible space
vanishes.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric

namespace AffineTverberg.Simplicial

open AffChain

/-- Maps to a contractible space are homotopic to one another. -/
theorem homotopic_maps_to_contractible {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace Y] (f g : C(X, Y)) : f.Homotopic g := by
  obtain ⟨y, hy⟩ := id_nullhomotopic Y
  have hf : f.Homotopic (ContinuousMap.const X y) := hy.comp (.refl f)
  have hg : g.Homotopic (ContinuousMap.const X y) := hy.comp (.refl g)
  exact hf.trans hg.symm

/-- Any given map between contractible spaces is itself a homotopy equivalence. -/
def homotopyEquiv_of_contractible_map {X Y : TopCat.{0}}
    [ContractibleSpace X] [ContractibleSpace Y] (f : X ⟶ Y) :
    ContinuousMap.HomotopyEquiv X Y where
  toFun := f.hom
  invFun := (Classical.choice (ContractibleSpace.hequiv X Y)).invFun
  left_inv := homotopic_maps_to_contractible _ _
  right_inv := homotopic_maps_to_contractible _ _

theorem quasiIso_singChainsMap_of_contractible_map {X Y : TopCat.{0}}
    [ContractibleSpace X] [ContractibleSpace Y] (f : X ⟶ Y) :
    QuasiIso (singChainsMap f) :=
  quasiIso_singChainsMap_of_homotopyEquiv (homotopyEquiv_of_contractible_map f)

variable {V : Type} [Fintype V] [LinearOrder V]
  {K : Finset (Finset V)} {L M : Finset V}

theorem costarRealization_mono_face (hLM : L ⊆ M) :
    subcomplexRealization (costarFamily K L) K ⊆ subcomplexRealization (costarFamily K M) K :=
  fun _ hx => barycentricCarrier_mono (costarFamily_mono_face hLM) hx

/-- The actual relative pair map, induced by the identity of the ambient carrier. -/
def cofaceSingularTransition (hLM : L ⊆ M) :
    relCx (subcomplexRealization (costarFamily K L) K) ⟶
      relCx (subcomplexRealization (costarFamily K M) K) :=
  relativeMap (𝟙 (barySpace K)) (fun _ hx => costarRealization_mono_face hLM hx)

theorem cofaceSingularTransition_proj (hLM : L ⊆ M) :
    relProj (subcomplexRealization (costarFamily K L) K) ≫ cofaceSingularTransition hLM =
      relProj (subcomplexRealization (costarFamily K M) K) := by
  have hid : singChainsMap (𝟙 (barySpace K)) = 𝟙 (singChains (barySpace K)) :=
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℝ)).obj
      (ModuleCat.of ℝ ℝ)).map_id (barySpace K)
  exact (relativeMap_proj (𝟙 (barySpace K))
    (fun _ hx => costarRealization_mono_face hLM hx)).trans (by rw [hid, Category.id_comp])

/-- The whole comparison square commutes at the level of actual chain maps. -/
theorem cofaceComparisonChainMap_transition (hK : FaceClosed K) (hLM : L ⊆ M) :
    cofaceTransition hK hLM ≫ cofaceComparisonChainMap hK M =
      cofaceComparisonChainMap hK L ≫ cofaceSingularTransition hLM := by
  have : Epi (cofaceProjection hK L) := (cofaceShortExact hK L).epi_g
  apply (cancel_epi (cofaceProjection hK L)).mp
  calc
    _ = cofaceProjection hK M ≫ cofaceComparisonChainMap hK M := by
      rw [← Category.assoc, cofaceProjection_transition]
    _ = comparisonChainMap hK ≫ relProj (subcomplexRealization (costarFamily K M) K) :=
      cofaceComparisonChainMap_proj hK M
    _ = (cofaceProjection hK L ≫ cofaceComparisonChainMap hK L) ≫
        cofaceSingularTransition hLM := by
      rw [cofaceComparisonChainMap_proj, Category.assoc, cofaceSingularTransition_proj]
    _ = _ := Category.assoc _ _ _

/-- Consequently the relative homology identifications respect face restriction. -/
theorem cofaceRelativeHomologyIso_naturality (hK : FaceClosed K) (hLM : L ⊆ M) (k : ℕ) :
    HomologicalComplex.homologyMap (cofaceTransition hK hLM) k ≫
      (cofaceRelativeHomologyIso hK M k).hom =
        (cofaceRelativeHomologyIso hK L k).hom ≫
          HomologicalComplex.homologyMap (cofaceSingularTransition hLM) k := by
  change HomologicalComplex.homologyMap (cofaceTransition hK hLM) k ≫
      HomologicalComplex.homologyMap (cofaceComparisonChainMap hK M) k =
    HomologicalComplex.homologyMap (cofaceComparisonChainMap hK L) k ≫
      HomologicalComplex.homologyMap (cofaceSingularTransition hLM) k
  rw [← HomologicalComplex.homologyMap_comp, cofaceComparisonChainMap_transition,
    HomologicalComplex.homologyMap_comp]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The actual relative singular transition is a quasi-isomorphism, without dropping low degrees. -/
theorem quasiIso_cofaceSingularTransition_of_homeomorph_sphere (hK : FaceClosed K)
    (hLM : L ⊆ M) (hM : M ∈ K) (hLne : L.Nonempty)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1) :
    QuasiIso (cofaceSingularTransition (K := K) hLM) := by
  have : ContractibleSpace (barySpace (costarFamily K L)) :=
    contractibleSpace_costar_of_homeomorph_sphere hK (hK M hM L hLM) hLne e
  have : ContractibleSpace (barySpace (costarFamily K M)) :=
    contractibleSpace_costar_of_homeomorph_sphere hK hM (hLne.mono hLM) e
  have : ContractibleSpace (subSpace (subcomplexRealization (costarFamily K L) K)) :=
    (subcomplexRealizationHomeomorph
      (costarFamily_subset K L)).symm.toHomotopyEquiv.contractibleSpace
  have : ContractibleSpace (subSpace (subcomplexRealization (costarFamily K M) K)) :=
    (subcomplexRealizationHomeomorph
      (costarFamily_subset K M)).symm.toHomotopyEquiv.contractibleSpace
  apply quasiIso_relativeMap
  · exact quasiIso_singChainsMap_of_contractible_map _
  · have hid : singChainsMap (𝟙 (barySpace K)) = 𝟙 (singChains (barySpace K)) :=
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℝ)).obj
        (ModuleCat.of ℝ ℝ)).map_id (barySpace K)
    rw [hid]
    infer_instance

/-- Face-inclusion coface transitions induce isomorphisms in every ordinary degree. -/
theorem quasiIso_cofaceTransition_of_homeomorph_sphere (hK : FaceClosed K)
    (hLM : L ⊆ M) (hM : M ∈ K) (hLne : L.Nonempty)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1) :
    QuasiIso (cofaceTransition hK hLM) := by
  have := quasiIso_cofaceComparisonChainMap hK L
  have := quasiIso_cofaceComparisonChainMap hK M
  have := quasiIso_cofaceSingularTransition_of_homeomorph_sphere hK hLM hM hLne e
  have : QuasiIso (cofaceTransition hK hLM ≫ cofaceComparisonChainMap hK M) := by
    rw [cofaceComparisonChainMap_transition]
    infer_instance
  exact quasiIso_of_comp_right
    (cofaceTransition hK hLM) (cofaceComparisonChainMap hK M)

end AffineTverberg.Simplicial
