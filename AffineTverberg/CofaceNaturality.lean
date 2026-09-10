import AffineTverberg.CostarRetraction

set_option linter.style.header false

/-!
# Natural restriction maps between the actual coface complexes

For L contained in M, restriction to cofaces of M is a chain map from
the coface model at L to the model at M. These maps compose strictly and
intertwine the projections from the original chain complex. For a
triangulated topological sphere they induce isomorphisms in degrees >=2.
The global-to-local isomorphisms trivialize this entire diagram, rather
than independently identifying its objects with one-dimensional spaces.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric

namespace AffineTverberg.Simplicial

variable {V : Type} [LinearOrder V] {K : Finset (Finset V)}
  {L M N : Finset V}

theorem costarFamily_mono_face (hLM : L ⊆ M) : costarFamily K L ⊆ costarFamily K M := by
  intro s hs
  obtain ⟨hsK, hLs⟩ := mem_costarFamily.mp hs
  exact mem_costarFamily.mpr ⟨hsK, fun hMs => hLs (hLM.trans hMs)⟩

theorem cofaceChains_antitone_face (hLM : L ⊆ M) (n : ℕ) :
    cofaceChains K M n ≤ cofaceChains K L n := by
  apply chains_mono
  intro s hs
  obtain ⟨hsK, hMs⟩ := Finset.mem_filter.mp hs
  exact Finset.mem_filter.mpr ⟨hsK, hLM.trans hMs⟩

theorem cofaceRestriction_nested (hLM : L ⊆ M) (c : Finset V → ℝ) :
    cofaceRestriction M (cofaceRestriction L c) = cofaceRestriction M c := by
  rw [cofaceRestriction_cofaceRestriction, Finset.union_eq_right.mpr hLM]

/-- The linear map is literal restriction of coefficient functions. -/
def cofaceTransitionLinear (L M : Finset V) (n : ℕ) :
    cofaceChains K L n →ₗ[ℝ] cofaceChains K M n :=
  LinearMap.codRestrict _ ((cofaceRestriction M).comp (cofaceChains K L n).subtype)
    (fun c => cofaceRestriction_mem_cofaceChains (cofaceChains_le L n c.property) M)

theorem cofaceTransitionLinear_surjective (hLM : L ⊆ M) (n : ℕ) :
    Function.Surjective (cofaceTransitionLinear (K := K) L M n) := by
  intro c
  exact ⟨⟨c.val, cofaceChains_antitone_face hLM n c.property⟩,
    Subtype.ext (cofaceRestriction_eq_self c.property)⟩

variable [Fintype V]

theorem cofaceBoundary_transition (hLM : L ⊆ M) (c : Finset V → ℝ) :
    cofaceBoundary M (cofaceRestriction M c) = cofaceRestriction M (cofaceBoundary L c) := by
  change cofaceRestriction M (boundary ℝ V (cofaceRestriction M c)) =
    cofaceRestriction M (cofaceRestriction L (boundary ℝ V c))
  rw [cofaceRestriction_boundary_cofaceRestriction, cofaceRestriction_nested hLM]

/-- Restriction along face inclusion, as an actual chain map. -/
def cofaceTransition (hK : FaceClosed K) (hLM : L ⊆ M) :
    cofaceComplex hK L ⟶ cofaceComplex hK M :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (cofaceTransitionLinear L M (n + 1)))
    (fun n => by
      rw [cofaceComplex_d, cofaceComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact Subtype.ext (cofaceBoundary_transition hLM c.val))

theorem cofaceTransition_apply (hK : FaceClosed K) (hLM : L ⊆ M) (n : ℕ)
    (c : (cofaceComplex hK L).X n) :
    (((cofaceTransition hK hLM).f n).hom c).val = cofaceRestriction M c.val := rfl

@[simp]
theorem cofaceTransition_refl (hK : FaceClosed K) (L : Finset V) :
    cofaceTransition hK (Finset.Subset.refl L) = 𝟙 (cofaceComplex hK L) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact Subtype.ext (cofaceRestriction_eq_self c.property)

@[reassoc (attr := simp)]
theorem cofaceTransition_comp (hK : FaceClosed K) (hLM : L ⊆ M) (hMN : M ⊆ N) :
    cofaceTransition hK hLM ≫ cofaceTransition hK hMN = cofaceTransition hK (hLM.trans hMN) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact Subtype.ext (cofaceRestriction_nested hMN c.val)

@[reassoc (attr := simp)]
theorem cofaceProjection_transition (hK : FaceClosed K) (hLM : L ⊆ M) :
    cofaceProjection hK L ≫ cofaceTransition hK hLM = cofaceProjection hK M := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact Subtype.ext (cofaceRestriction_nested hLM c.val)

theorem epi_cofaceTransition (hK : FaceClosed K) (hLM : L ⊆ M) :
    Epi (cofaceTransition hK hLM) := by
  apply HomologicalComplex.epi_of_epi_f
  intro n
  exact (ModuleCat.epi_iff_surjective _).mpr (cofaceTransitionLinear_surjective hLM (n + 1))

theorem cofaceProjection_homology_transition (hK : FaceClosed K) (hLM : L ⊆ M) (k : ℕ) :
    HomologicalComplex.homologyMap (cofaceProjection hK L) k ≫
      HomologicalComplex.homologyMap (cofaceTransition hK hLM) k =
        HomologicalComplex.homologyMap (cofaceProjection hK M) k := by
  rw [← HomologicalComplex.homologyMap_comp, cofaceProjection_transition]

/-- Restriction of a single global homology class gives compatible local classes. -/
theorem cofaceTransition_global_class (hK : FaceClosed K) (hLM : L ⊆ M) (k : ℕ)
    (z : (simplicialChains hK).homology k) :
    (HomologicalComplex.homologyMap (cofaceTransition hK hLM) k).hom
        ((HomologicalComplex.homologyMap (cofaceProjection hK L) k).hom z) =
      (HomologicalComplex.homologyMap (cofaceProjection hK M) k).hom z :=
  congrArg (fun f => f.hom z) (cofaceProjection_homology_transition hK hLM k)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Every local transition in this diagram is an isomorphism for a topological sphere. -/
theorem isIso_cofaceTransition_homology_of_homeomorph_sphere (hK : FaceClosed K)
    (hLM : L ⊆ M) (hM : M ∈ K) (hLne : L.Nonempty)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1) (k : ℕ) (hk : k ≠ 0) :
    IsIso (HomologicalComplex.homologyMap (cofaceTransition hK hLM) (k + 1)) := by
  have := isIso_cofaceProjection_homology_of_homeomorph_sphere hK
    (hK M hM L hLM) hLne e k hk
  have := isIso_cofaceProjection_homology_of_homeomorph_sphere hK
    hM (hLne.mono hLM) e k hk
  have : IsIso (HomologicalComplex.homologyMap (cofaceProjection hK L) (k + 1) ≫
      HomologicalComplex.homologyMap (cofaceTransition hK hLM) (k + 1)) := by
    rw [cofaceProjection_homology_transition]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (HomologicalComplex.homologyMap (cofaceProjection hK L) (k + 1)) _

/-- The actual global restriction gives a simultaneous trivialization of local homology. -/
def globalCofaceHomologyIso (hK : FaceClosed K) (hL : L ∈ K) (hLne : L.Nonempty)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1) (k : ℕ) (hk : k ≠ 0) :
    (simplicialChains hK).homology (k + 1) ≅ (cofaceComplex hK L).homology (k + 1) := by
  have := isIso_cofaceProjection_homology_of_homeomorph_sphere hK hL hLne e k hk
  exact asIso (HomologicalComplex.homologyMap (cofaceProjection hK L) (k + 1))

/-- These isomorphisms commute with all face-inclusion transitions. -/
theorem globalCofaceHomologyIso_naturality (hK : FaceClosed K)
    (hLM : L ⊆ M) (hM : M ∈ K) (hLne : L.Nonempty)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1) (k : ℕ) (hk : k ≠ 0) :
    (globalCofaceHomologyIso hK (hK M hM L hLM) hLne e k hk).hom ≫
      HomologicalComplex.homologyMap (cofaceTransition hK hLM) (k + 1) =
        (globalCofaceHomologyIso hK hM (hLne.mono hLM) e k hk).hom :=
  cofaceProjection_homology_transition hK hLM (k + 1)

theorem coface_global_class_ne_zero (hK : FaceClosed K) (hL : L ∈ K) (hLne : L.Nonempty)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1) (k : ℕ) (hk : k ≠ 0)
    {z : (simplicialChains hK).homology (k + 1)} (hz : z ≠ 0) :
    (HomologicalComplex.homologyMap (cofaceProjection hK L) (k + 1)).hom z ≠ 0 := by
  have := isIso_cofaceProjection_homology_of_homeomorph_sphere hK hL hLne e k hk
  intro hzero
  exact hz ((ModuleCat.mono_iff_injective _).mp inferInstance (hzero.trans (map_zero _).symm))

end AffineTverberg.Simplicial
