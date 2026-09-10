import AffineTverberg.SimplexBoundaryRank
import AffineTverberg.PuncturedSphere

set_option linter.style.header false

/-!
# Fundamental cycles of a finite triangulated topological sphere

Deleting a maximal simplex leaves a contractible realization: the existing
radial retraction identifies it with the sphere punctured at that simplex's
barycenter. Consequently a top cycle whose coefficient on a top simplex is
zero must be zero. A nonzero top cycle therefore has nonzero coefficients on
every top simplex, and can be uniquely normalized on any chosen one.

This supplies orientation data for a dual-chain construction without adding
an orientability, PL-sphere or combinatorial-manifold assumption. The existing
real-coefficient comparison and sphere homology are reused unchanged.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric

namespace AffineTverberg.Simplicial

variable {V E : Type} [Fintype V] [LinearOrder V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K : Finset (Finset V)} {s : Finset V}

/-- The facet-deletion realization is contractible, even for a non-PL triangulated sphere. -/
theorem contractibleSpace_erase_of_homeomorph_sphere (hK : FaceClosed K)
    (hsK : s ∈ K) (hs : s.Nonempty) (hmax : ∀ t ∈ K, s ⊆ t → t = s)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1) :
    ContractibleSpace ↥(barycentricCarrier (K.erase s)) := by
  let p : ↥(barycentricCarrier K) :=
    ⟨faceCenter s, barycentricFace_subset_carrier hsK (faceCenter_mem_barycentricFace hs)⟩
  have hpun : punctured K s = {x : ↥(barycentricCarrier K) | x ≠ p} := by
    ext x
    change (x.val ≠ p.val) ↔ x ≠ p
    exact not_congr Subtype.ext_iff.symm
  have : ContractibleSpace ↥(punctured K s) := by
    rw [hpun]
    exact contractibleSpace_punctured_of_homeomorph_normSphere e p
  exact (puncturedHomotopyEquiv hK hs hmax).symm.contractibleSpace

/-- A top cycle is determined by its coefficient on any top-dimensional simplex. -/
theorem top_cycle_eq_zero_of_coefficient_eq_zero (hK : FaceClosed K) (k : ℕ)
    (htop : ∀ t ∈ K, t.card ≤ k + 2)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1)
    (hsK : s ∈ K) (hscard : s.card = k + 2)
    {c : Finset V → ℝ} (hc : c ∈ cycles ℝ K (k + 2)) (hcs : c s = 0) : c = 0 := by
  have hmax : ∀ t ∈ K, s ⊆ t → t = s := by
    intro t ht hst
    exact (Finset.eq_of_subset_of_card_le hst (by rw [hscard]; exact htop t ht)).symm
  have hs : s.Nonempty := Finset.card_pos.mp (by omega)
  have hErase : FaceClosed (K.erase s) := faceClosed_erase_of_max hK hmax
  have hEraseTop : ∀ t ∈ K.erase s, t.card ≤ k + 2 :=
    fun t ht => htop t (Finset.mem_erase.mp ht).2
  have : ContractibleSpace ↥(barycentricCarrier (K.erase s)) :=
    contractibleSpace_erase_of_homeomorph_sphere hK hsK hs hmax e
  have : Subsingleton ((realSingularHomology (k + 1)).obj (barySpace (K.erase s))) :=
    realSingularHomology_subsingleton_of_contractible _ (k + 1) (by omega)
  have hsub : Subsingleton ↥(cycles ℝ (K.erase s) (k + 2)) :=
    (realSingularHomologyTopEquiv hErase k hEraseTop).symm.injective.subsingleton
  have hcErase : c ∈ cycles ℝ (K.erase s) (k + 2) := by
    refine ⟨?_, hc.2⟩
    intro t hct
    obtain ⟨htK, htcard⟩ := hc.1 t hct
    refine ⟨Finset.mem_erase.mpr ⟨?_, htK⟩, htcard⟩
    intro hts
    exact hct (by simpa only [hts] using hcs)
  exact congrArg Subtype.val (hsub.elim (⟨c, hcErase⟩ : ↥(cycles ℝ (K.erase s) (k + 2))) 0)

/-- Every nonzero top cycle is nonzero on every top simplex. -/
theorem top_cycle_coefficient_ne_zero (hK : FaceClosed K) (k : ℕ)
    (htop : ∀ t ∈ K, t.card ≤ k + 2)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1)
    {c : Finset V → ℝ} (hc : c ∈ cycles ℝ K (k + 2)) (hc0 : c ≠ 0)
    (hsK : s ∈ K) (hscard : s.card = k + 2) : c s ≠ 0 :=
  fun hcs => hc0 (top_cycle_eq_zero_of_coefficient_eq_zero hK k htop e hsK hscard hc hcs)

/-- The top cycle space is the one-dimensional top homology of the actual sphere. -/
theorem finrank_top_cycles_of_homeomorph_sphere (hK : FaceClosed K) (k : ℕ)
    (htop : ∀ t ∈ K, t.card ≤ k + 2)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1)
    (hdim : Module.finrank ℝ E = k + 2) :
    Module.finrank ℝ ↥(cycles ℝ K (k + 2)) = 1 := by
  calc
    Module.finrank ℝ ↥(cycles ℝ K (k + 2)) =
        Module.finrank ℝ ((realSingularHomology (k + 1)).obj (barySpace K)) :=
      (realSingularHomologyTopEquiv hK k htop).finrank_eq.symm
    _ = Module.finrank ℝ ((realSingularHomology (k + 1)).obj
        (TopCat.of (sphere (0 : E) 1))) :=
      (realSingularHomologyIsoOfHomotopyEquiv e.toHomotopyEquiv (k + 1)).toLinearEquiv.finrank_eq
    _ = 1 := finrank_realSingularHomology_sphere hdim

/-- A genuine fundamental cycle exists and has full top-dimensional support. -/
theorem exists_fundamental_sphere_cycle (hK : FaceClosed K) (k : ℕ)
    (htop : ∀ t ∈ K, t.card ≤ k + 2)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1)
    (hdim : Module.finrank ℝ E = k + 2) :
    ∃ c : Finset V → ℝ, c ∈ cycles ℝ K (k + 2) ∧ c ≠ 0 ∧
      ∀ t ∈ K, t.card = k + 2 → c t ≠ 0 := by
  have hdimC := finrank_top_cycles_of_homeomorph_sphere hK k htop e hdim
  have : Nontrivial ↥(cycles ℝ K (k + 2)) :=
    Module.nontrivial_of_finrank_pos (by rw [hdimC]; norm_num)
  obtain ⟨z, hz⟩ := exists_ne (0 : ↥(cycles ℝ K (k + 2)))
  have hz0 : (z : Finset V → ℝ) ≠ 0 := fun h => hz (Subtype.ext h)
  exact ⟨z.val, z.property, hz0,
    fun _ ht hcard => top_cycle_coefficient_ne_zero hK k htop e z.property hz0 ht hcard⟩

/-- A fundamental cycle can be normalized to have coefficient one on any selected top simplex. -/
theorem exists_normalized_sphere_cycle (hK : FaceClosed K) (k : ℕ)
    (htop : ∀ t ∈ K, t.card ≤ k + 2)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1)
    (hdim : Module.finrank ℝ E = k + 2) (hsK : s ∈ K) (hscard : s.card = k + 2) :
    ∃ c : Finset V → ℝ, c ∈ cycles ℝ K (k + 2) ∧ c s = 1 ∧
      ∀ t ∈ K, t.card = k + 2 → c t ≠ 0 := by
  obtain ⟨z, hz, -, hzall⟩ := exists_fundamental_sphere_cycle hK k htop e hdim
  have hzs : z s ≠ 0 := hzall s hsK hscard
  refine ⟨(z s)⁻¹ • z, (cycles ℝ K (k + 2)).smul_mem _ hz, ?_, ?_⟩
  · change (z s)⁻¹ * z s = 1
    exact inv_mul_cancel₀ hzs
  · intro t ht hcard
    change (z s)⁻¹ * z t ≠ 0
    exact mul_ne_zero (inv_ne_zero hzs)
      (hzall t ht hcard)

/-- Normalizing one coefficient determines the entire fundamental cycle uniquely. -/
theorem normalized_sphere_cycle_unique (hK : FaceClosed K) (k : ℕ)
    (htop : ∀ t ∈ K, t.card ≤ k + 2)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1)
    (hsK : s ∈ K) (hscard : s.card = k + 2)
    {c d : Finset V → ℝ} (hc : c ∈ cycles ℝ K (k + 2))
    (hd : d ∈ cycles ℝ K (k + 2)) (hcs : c s = d s) : c = d := by
  apply sub_eq_zero.mp
  exact top_cycle_eq_zero_of_coefficient_eq_zero hK k htop e hsK hscard
    ((cycles ℝ K (k + 2)).sub_mem hc hd) (by change c s - d s = 0; exact sub_eq_zero.mpr hcs)

end AffineTverberg.Simplicial
