import AffineTverberg.SimplicialBoundaryJoin
import AffineTverberg.SphereHomology
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.Homeomorph.Quotient

set_option linter.style.header false

/-!
# The boundary join of a sphere is a sphere

Given a homeomorphism from the actual simplicial boundary to a norm sphere,
we construct the homeomorphism from its actual Cayley join to the unit
sphere of the L1 product. The two parameter maps have exactly the same
fibers and the quotient topology. Zero-weight factors are treated explicitly.

The boundary-sphere homeomorphism is an explicit input here, not a claimed
consequence of IsSimplicialBall. That distinct topological step remains open.
-/

noncomputable section

open Set Metric Topology

namespace AffineTverberg

section Quotient

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y}

/-- A quotient map identifies its codomain with the quotient by its fibers. -/
def quotientKerHomeomorph (hf : IsQuotientMap f) : Quotient (Setoid.ker f) ≃ₜ Y where
  toEquiv := Setoid.quotientKerEquivOfSurjective f hf.surjective
  continuous_toFun := hf.continuous.quotient_lift (fun _ _ h ↦ h)
  continuous_invFun := hf.continuous_iff.mpr (by
    have heq : (Setoid.quotientKerEquivOfSurjective f hf.surjective).symm ∘ f =
        @Quotient.mk' X (Setoid.ker f) := by
      funext x
      apply Quotient.sound
      exact Function.rightInverse_surjInv hf.surjective (f x)
    change Continuous ((Setoid.quotientKerEquivOfSurjective f hf.surjective).symm ∘ f)
    rw [heq]
    exact continuous_quotient_mk')

/-- Two quotient maps with the same fibers have homeomorphic codomains. -/
def homeomorphOfQuotientMaps {Z : Type*} [TopologicalSpace Z] {g : X → Z}
    (hf : IsQuotientMap f) (hg : IsQuotientMap g)
    (hker : ∀ p q, f p = f q ↔ g p = g q) : Y ≃ₜ Z :=
  (quotientKerHomeomorph hf).symm.trans
    ((Homeomorph.Quotient.congrRight hker).trans (quotientKerHomeomorph hg))

end Quotient

variable {e n m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (hB : simplicialBoundaryCarrier K n ≃ₜ sphere (0 : E) 1)

/-- The L1 product of the vector spaces underlying the factor spheres. -/
abbrev BoundaryJoinSphereAmbient (E : Type*) (m : ℕ) :=
  PiLp 1 (fun _ : Fin (m + 1) ↦ E)

/-- Scale each unit vector by its join weight. -/
def boundarySphereParameterMap (p : BoundaryJoinParameters K n m) :
    BoundaryJoinSphereAmbient E m :=
  WithLp.toLp 1 (fun i ↦ p.1.val i • (hB (p.2 i)).val)

theorem norm_boundarySphereParameterMap (p : BoundaryJoinParameters K n m) :
    ‖boundarySphereParameterMap hB p‖ = 1 := by
  rw [PiLp.norm_eq_of_L1]
  calc
    ∑ i, ‖boundarySphereParameterMap hB p i‖ = ∑ i, p.1.val i := by
      apply Finset.sum_congr rfl
      intro i _
      have hn : ‖(hB (p.2 i)).val‖ = 1 := by
        simpa only [mem_sphere, dist_zero_right] using (hB (p.2 i)).property
      change ‖p.1.val i • (hB (p.2 i)).val‖ = p.1.val i
      rw [norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_nonneg (p.1.property.1 i)]
    _ = 1 := p.1.property.2

theorem continuous_boundarySphereParameterMap :
    Continuous (boundarySphereParameterMap hB (m := m)) := by
  apply (PiLp.continuous_toLp 1 _).comp
  apply continuous_pi
  intro i
  exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).smul
    (continuous_subtype_val.comp (hB.continuous.comp
      ((continuous_apply i).comp continuous_snd)))

/-- The weighted parameter map lands on the L1 unit sphere. -/
def boundarySphereParameterProjection (m : ℕ) :
    C(BoundaryJoinParameters K n m, sphere (0 : BoundaryJoinSphereAmbient E m) 1) := by
  let f : BoundaryJoinParameters K n m → sphere (0 : BoundaryJoinSphereAmbient E m) 1 :=
    fun p ↦ ⟨boundarySphereParameterMap hB p,
      mem_sphere_zero_iff_norm.mpr (norm_boundarySphereParameterMap hB p)⟩
  exact ⟨f, (continuous_boundarySphereParameterMap hB (m := m)).subtype_mk _⟩

theorem surjective_boundarySphereParameterProjection [Nontrivial E] :
    Function.Surjective (boundarySphereParameterProjection hB m) := by
  classical
  intro z
  obtain ⟨b, hb⟩ := (NormedSpace.sphere_nonempty (E := E) (x := 0)).mpr zero_le_one
  have ht1 : ∑ i, ‖z.val i‖ = 1 := by
    rw [← PiLp.norm_eq_of_L1]
    simpa only [mem_sphere, dist_zero_right] using z.property
  have hunit (i) (hi : z.val i ≠ 0) :
      ‖z.val i‖⁻¹ • z.val i ∈ sphere (0 : E) 1 := by
    rw [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hi)]
  let u : Fin (m + 1) → sphere (0 : E) 1 :=
    fun i ↦ if hi : z.val i = 0 then ⟨b, hb⟩
      else ⟨‖z.val i‖⁻¹ • z.val i, hunit i hi⟩
  let p : BoundaryJoinParameters K n m :=
    (⟨fun i ↦ ‖z.val i‖, fun i ↦ norm_nonneg _, ht1⟩, fun i ↦ hB.symm (u i))
  refine ⟨p, Subtype.ext ?_⟩
  apply (WithLp.equiv 1 _).injective
  funext i
  change ‖z.val i‖ • (hB (hB.symm (u i))).val = z.val i
  rw [hB.apply_symm_apply]
  by_cases hi : z.val i = 0
  · simp [hi]
  · simp only [u, hi, ↓reduceDIte]
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hi), one_smul]

theorem isQuotientMap_boundarySphereParameterProjection (hfin : K.faces.Finite)
    [Nontrivial E] : IsQuotientMap (boundarySphereParameterProjection hB m) := by
  let := isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ (Fin (m + 1)))
  let := isCompact_iff_compactSpace.mp (simplicialBoundaryCarrier_compact K (n := n) hfin)
  have : CompactSpace (BoundaryJoinParameters K n m) :=
    inferInstanceAs (CompactSpace
      ((stdSimplex ℝ (Fin (m + 1))) × (Fin (m + 1) → simplicialBoundaryCarrier K n)))
  exact IsQuotientMap.of_surjective_continuous
    (surjective_boundarySphereParameterProjection hB)
    (boundarySphereParameterProjection hB m).continuous

theorem boundarySphereParameterMap_eq_iff (p q : BoundaryJoinParameters K n m) :
    boundarySphereParameterMap hB p = boundarySphereParameterMap hB q ↔
      p.1 = q.1 ∧ ∀ i, p.1.val i ≠ 0 → p.2 i = q.2 i := by
  have hn (x : simplicialBoundaryCarrier K n) : ‖(hB x).val‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using (hB x).property
  constructor
  · intro h
    have hc (i) : p.1.val i • (hB (p.2 i)).val = q.1.val i • (hB (q.2 i)).val :=
      congrArg (fun v : BoundaryJoinSphereAmbient E m ↦ v i) h
    have ht : p.1 = q.1 := by
      apply Subtype.ext
      funext i
      have hh := congrArg norm (hc i)
      simpa only [norm_smul, hn, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (p.1.property.1 i), abs_of_nonneg (q.1.property.1 i)] using hh
    refine ⟨ht, fun i hi ↦ hB.injective (Subtype.ext ?_)⟩
    have hh := hc i
    rw [← ht] at hh
    exact (smul_right_injective _ hi) hh
  · rintro ⟨ht, hx⟩
    apply (WithLp.equiv 1 _).injective
    funext i
    change p.1.val i • (hB (p.2 i)).val = q.1.val i • (hB (q.2 i)).val
    rw [← ht]
    by_cases hi : p.1.val i = 0
    · simp [hi]
    · rw [hx i hi]

/-- **The actual Cayley join of a sphere is a sphere.** All topology of the
join construction is proved; only the factor's sphere identification is an
input. The ambient vector space has (m+1) times the factor dimension. -/
def boundaryJoinSphereHomeomorph (hfin : K.faces.Finite) [Nontrivial E] :
    simplicialBoundaryJoinCarrier K n m ≃ₜ sphere (0 : BoundaryJoinSphereAmbient E m) 1 :=
  homeomorphOfQuotientMaps (isQuotientMap_boundaryJoinParameterProjection K hfin)
    (isQuotientMap_boundarySphereParameterProjection hB hfin) (fun p q ↦ by
      rw [Subtype.ext_iff, Subtype.ext_iff]
      exact (boundaryJoinParameterMap_eq_iff K p q).trans
        (boundarySphereParameterMap_eq_iff hB p q).symm)

/-- The L1 join ambient space has the expected vector-space dimension. -/
theorem finrank_boundaryJoinSphereAmbient [FiniteDimensional ℝ E] :
    Module.finrank ℝ (BoundaryJoinSphereAmbient E m) = (m + 1) * Module.finrank ℝ E := by
  rw [(WithLp.linearEquiv 1 ℝ (Fin (m + 1) → E)).finrank_eq,
    Module.finrank_pi_fintype]
  simp

/-- Unit spheres in finite-dimensional real normed spaces of equal dimension
are homeomorphic, using their common affine-simplex boundary model. -/
def normSphereHomeomorphOfFinrankEq {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1 := by
  classical
  let bE := Classical.choice (AffineBasis.exists_affineBasis_of_finiteDimensional
    (ι := Fin (Module.finrank ℝ E + 1)) (k := ℝ) (V := E) (P := E) (by simp))
  let bF := Classical.choice (AffineBasis.exists_affineBasis_of_finiteDimensional
    (ι := Fin (Module.finrank ℝ E + 1)) (k := ℝ) (V := F) (P := F) (by simp [hdim]))
  exact (Simplicial.affineBasisBoundarySphereHomeomorph bE).symm.trans
    (Simplicial.affineBasisBoundarySphereHomeomorph bF)

/-- The sphere identification in precisely the coordinate dimension used by
the paper: the join of m+1 copies of S^(n-1) is S^((m+1)*n-1). -/
def boundaryJoinCoordinateSphereHomeomorph
    (hB : simplicialBoundaryCarrier K n ≃ₜ sphere (0 : CoordinateSpace n) 1)
    (hfin : K.faces.Finite) (hn : 0 < n) (m : ℕ) :
    simplicialBoundaryJoinCarrier K n m ≃ₜ sphere (0 : CoordinateSpace ((m + 1) * n)) 1 := by
  let : NeZero n := ⟨by omega⟩
  exact (boundaryJoinSphereHomeomorph hB hfin).trans
    (normSphereHomeomorphOfFinrankEq (by
      rw [finrank_boundaryJoinSphereAmbient]
      simp [CoordinateSpace]))

end AffineTverberg
