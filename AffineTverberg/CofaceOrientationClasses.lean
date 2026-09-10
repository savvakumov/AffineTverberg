import AffineTverberg.CofaceNaturality
import AffineTverberg.HomologyClassCalculus

set_option linter.style.header false

/-!
# Compatible generators of local relative homology

An actual nonzero top cycle of a triangulated sphere determines a nonzero
homology class in every coface complex. These are generators, not merely
nonzero elements: every local class is a unique real multiple of the chosen
class. The actual face-inclusion maps carry each chosen generator to the
next, so the scalar coordinates are compatible. The choice is made once
globally, without separate local orientations or an orientability premise.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric

namespace AffineTverberg.Simplicial

variable {V : Type} [Fintype V] [LinearOrder V]
  {K : Finset (Finset V)} {k : ℕ} {c : Finset V → ℝ}

theorem simplicialCycle_isCycleAt (hK : FaceClosed K) (hc : c ∈ cycles ℝ K (k + 2)) :
    AffChain.IsCycleAt (simplicialChains hK) (k + 1)
      (⟨c, hc.1⟩ : ↥(chains ℝ K (k + 2))) := by
  apply AffChain.isCycleAt_succ
  rw [simplicialChains_d]
  exact Subtype.ext hc.2

/-- The homology class of the original coefficient cycle. -/
def simplicialCycleClass (hK : FaceClosed K) (hc : c ∈ cycles ℝ K (k + 2)) :
    (simplicialChains hK).homology (k + 1) :=
  AffChain.homClass (⟨c, hc.1⟩ : ↥(chains ℝ K (k + 2))) (simplicialCycle_isCycleAt hK hc)

/-- The local class is represented by the literal coface restriction of the cycle. -/
def cofaceCycleClass (hK : FaceClosed K) (L : Finset V) (hc : c ∈ cycles ℝ K (k + 2)) :
    (cofaceComplex hK L).homology (k + 1) :=
  AffChain.homClass (((cofaceProjection hK L).f (k + 1)).hom
      (⟨c, hc.1⟩ : ↥(chains ℝ K (k + 2))))
    ((simplicialCycle_isCycleAt hK hc).map (cofaceProjection hK L))

theorem cofaceCycleClass_eq_map (hK : FaceClosed K) (L : Finset V)
    (hc : c ∈ cycles ℝ K (k + 2)) :
    cofaceCycleClass hK L hc =
      (HomologicalComplex.homologyMap (cofaceProjection hK L) (k + 1)).hom
        (simplicialCycleClass hK hc) :=
  (AffChain.homClass_map (cofaceProjection hK L) _ (simplicialCycle_isCycleAt hK hc)).symm

/-- The lack of higher simplices makes the actual nonzero top cycle nonzero in homology. -/
theorem simplicialCycleClass_ne_zero (hK : FaceClosed K)
    (htop : ∀ t ∈ K, t.card ≤ k + 2) (hc : c ∈ cycles ℝ K (k + 2)) (hc0 : c ≠ 0) :
    simplicialCycleClass hK hc ≠ 0 := by
  intro hzero
  obtain ⟨b, hb⟩ := (AffChain.homClass_eq_zero_iff (C := simplicialChains hK) (k := k + 1)
    (⟨c, hc.1⟩ : ↥(chains ℝ K (k + 2))) (simplicialCycle_isCycleAt hK hc)).mp hzero
  rw [simplicialChains_d] at hb
  have hboundary : c ∈ boundaries ℝ K (k + 2) :=
    ⟨b.val, b.property, congrArg Subtype.val hb⟩
  rw [boundaries_top_eq_bot htop, Submodule.mem_bot] at hboundary
  exact hc0 hboundary

/-- Compatibility holds for actual cycle classes under every face inclusion. -/
theorem cofaceCycleClass_transition (hK : FaceClosed K) {L M : Finset V} (hLM : L ⊆ M)
    (hc : c ∈ cycles ℝ K (k + 2)) :
    (HomologicalComplex.homologyMap (cofaceTransition hK hLM) (k + 1)).hom
      (cofaceCycleClass hK L hc) = cofaceCycleClass hK M hc := by
  rw [cofaceCycleClass_eq_map, cofaceCycleClass_eq_map]
  exact cofaceTransition_global_class hK hLM (k + 1) (simplicialCycleClass hK hc)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cofaceCycleClass_ne_zero (hK : FaceClosed K)
    (htop : ∀ t ∈ K, t.card ≤ k + 2) (hc : c ∈ cycles ℝ K (k + 2)) (hc0 : c ≠ 0)
    {L : Finset V} (hL : L ∈ K) (hLne : L.Nonempty)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1) (hk : k ≠ 0) :
    cofaceCycleClass hK L hc ≠ 0 := by
  rw [cofaceCycleClass_eq_map]
  exact coface_global_class_ne_zero hK hL hLne e k hk
    (simplicialCycleClass_ne_zero hK htop hc hc0)

/-- Top local homology is a line, with no local manifold hypothesis beyond the global sphere. -/
theorem finrank_coface_top_homology (hK : FaceClosed K)
    (htop : ∀ t ∈ K, t.card ≤ k + 2) {L : Finset V} (hL : L ∈ K) (hLne : L.Nonempty)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1)
    (hdim : Module.finrank ℝ E = k + 2) (hk : k ≠ 0) :
    Module.finrank ℝ ((cofaceComplex hK L).homology (k + 1)) = 1 := by
  calc
    _ = Module.finrank ℝ ((simplicialChains hK).homology (k + 1)) :=
      (globalCofaceHomologyIso hK hL hLne e k hk).toLinearEquiv.finrank_eq.symm
    _ = Module.finrank ℝ ↥(cycles ℝ K (k + 2)) :=
      (simplicialChainsHomologyTopEquiv hK k htop).finrank_eq
    _ = 1 := finrank_top_cycles_of_homeomorph_sphere hK k htop e hdim

/-- The restricted global cycle spans the complete local relative homology. -/
theorem span_cofaceCycleClass (hK : FaceClosed K)
    (htop : ∀ t ∈ K, t.card ≤ k + 2) (hc : c ∈ cycles ℝ K (k + 2)) (hc0 : c ≠ 0)
    {L : Finset V} (hL : L ∈ K) (hLne : L.Nonempty)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1)
    (hdim : Module.finrank ℝ E = k + 2) (hk : k ≠ 0) :
    Submodule.span ℝ {cofaceCycleClass hK L hc} = ⊤ :=
  (finrank_eq_one_iff_of_nonzero _
    (cofaceCycleClass_ne_zero hK htop hc hc0 hL hLne e hk)).mp
      (finrank_coface_top_homology hK htop hL hLne e hdim hk)

/-- Scalar coordinates of local classes exist uniquely once the one global cycle is fixed. -/
theorem existsUnique_smul_cofaceCycleClass (hK : FaceClosed K)
    (htop : ∀ t ∈ K, t.card ≤ k + 2) (hc : c ∈ cycles ℝ K (k + 2)) (hc0 : c ≠ 0)
    {L : Finset V} (hL : L ∈ K) (hLne : L.Nonempty)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1)
    (hdim : Module.finrank ℝ E = k + 2) (hk : k ≠ 0)
    (z : (cofaceComplex hK L).homology (k + 1)) :
    ∃! a : ℝ, a • cofaceCycleClass hK L hc = z := by
  have hne := cofaceCycleClass_ne_zero hK htop hc hc0 hL hLne e hk
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp
    (finrank_coface_top_homology hK htop hL hLne e hdim hk) z
  refine ⟨a, ha, fun b hb => ?_⟩
  exact (smul_left_injective ℝ hne) (hb.trans ha.symm)

/-- Local transition maps preserve these scalar coordinates exactly. -/
theorem cofaceCycleClass_transition_smul (hK : FaceClosed K) {L M : Finset V} (hLM : L ⊆ M)
    (hc : c ∈ cycles ℝ K (k + 2)) (a : ℝ) :
    (HomologicalComplex.homologyMap (cofaceTransition hK hLM) (k + 1)).hom
      (a • cofaceCycleClass hK L hc) = a • cofaceCycleClass hK M hc := by
  rw [map_smul, cofaceCycleClass_transition]

/-- The chosen global cycle identifies each local homology line with the real coefficients. -/
def cofaceOrientationEquiv (hK : FaceClosed K)
    (htop : ∀ t ∈ K, t.card ≤ k + 2) (hc : c ∈ cycles ℝ K (k + 2)) (hc0 : c ≠ 0)
    {L : Finset V} (hL : L ∈ K) (hLne : L.Nonempty)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1)
    (hdim : Module.finrank ℝ E = k + 2) (hk : k ≠ 0) :
    ℝ ≃ₗ[ℝ] ((cofaceComplex hK L).homology (k + 1)) :=
  LinearEquiv.ofBijective ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (cofaceCycleClass hK L hc))
    ⟨smul_left_injective ℝ (cofaceCycleClass_ne_zero hK htop hc hc0 hL hLne e hk),
      fun z => (existsUnique_smul_cofaceCycleClass hK htop hc hc0 hL hLne e hdim hk z).exists⟩

theorem cofaceOrientationEquiv_apply (hK : FaceClosed K)
    (htop : ∀ t ∈ K, t.card ≤ k + 2) (hc : c ∈ cycles ℝ K (k + 2)) (hc0 : c ≠ 0)
    {L : Finset V} (hL : L ∈ K) (hLne : L.Nonempty)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1)
    (hdim : Module.finrank ℝ E = k + 2) (hk : k ≠ 0) (a : ℝ) :
    cofaceOrientationEquiv hK htop hc hc0 hL hLne e hdim hk a =
      a • cofaceCycleClass hK L hc := rfl

/-- With these actual scalar identifications, all transition maps become the identity. -/
theorem cofaceOrientationEquiv_naturality (hK : FaceClosed K)
    (htop : ∀ t ∈ K, t.card ≤ k + 2) (hc : c ∈ cycles ℝ K (k + 2)) (hc0 : c ≠ 0)
    {L M : Finset V} (hLM : L ⊆ M) (hM : M ∈ K) (hLne : L.Nonempty)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1)
    (hdim : Module.finrank ℝ E = k + 2) (hk : k ≠ 0) (a : ℝ) :
    (HomologicalComplex.homologyMap (cofaceTransition hK hLM) (k + 1)).hom
        (cofaceOrientationEquiv hK htop hc hc0 (hK M hM L hLM) hLne e hdim hk a) =
      cofaceOrientationEquiv hK htop hc hc0 hM (hLne.mono hLM) e hdim hk a :=
  cofaceCycleClass_transition_smul hK hLM hc a

/-- A single global choice supplies generators, with explicit representatives,
for all local homology groups at once. -/
theorem exists_compatible_coface_generators (hK : FaceClosed K) (k : ℕ)
    (htop : ∀ t ∈ K, t.card ≤ k + 2)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1)
    (hdim : Module.finrank ℝ E = k + 2) (hk : k ≠ 0) :
    ∃ c : Finset V → ℝ, ∃ hc : c ∈ cycles ℝ K (k + 2), c ≠ 0 ∧
      (∀ t ∈ K, t.card = k + 2 → c t ≠ 0) ∧
      (∀ L ∈ K, L.Nonempty → Submodule.span ℝ {cofaceCycleClass hK L hc} = ⊤) ∧
      (∀ (L M : Finset V) (hLM : L ⊆ M),
        (HomologicalComplex.homologyMap (cofaceTransition hK hLM) (k + 1)).hom
          (cofaceCycleClass hK L hc) = cofaceCycleClass hK M hc) := by
  obtain ⟨c, hc, hc0, hcfull⟩ := exists_fundamental_sphere_cycle hK k htop e hdim
  exact ⟨c, hc, hc0, hcfull,
    fun L hL hLne => span_cofaceCycleClass hK htop hc hc0 hL hLne e hdim hk,
    fun _ _ hLM => cofaceCycleClass_transition hK hLM hc⟩

end AffineTverberg.Simplicial
