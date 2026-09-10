import AffineTverberg.MayerVietorisRank
import AffineTverberg.SimplexBoundaryRank

set_option linter.style.header false

/-!
# The local homology of a closed ball

For every point `x` of the closed unit ball `B` of a finite dimensional normed
space of dimension `n + 2`, the singular homology of the punctured ball
`B \ {x}` in degree `n + 1` has rank at most one.

Two cases are treated with the actual geometry:

* if `‖x‖ = 1` the punctured ball is star convex about the origin, hence
  contractible, and the homology vanishes;
* if `‖x‖ < 1` a small punctured ball around `x` is a deformation retract of a
  sphere, and Mayer-Vietoris for the cover of `B` by `B \ {x}` and that small
  ball bounds the rank by the rank of the sphere, which is one.

This is the topological half of the statement that a ridge of a simplicial
ball lies in at most two facets: the local homology of a ball is at most one
dimensional, while a ridge in `k` facets contributes rank `k - 1`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric Set

namespace AffineTverberg

section SubtypeHelpers

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- A subset of a subtype is homeomorphic to the corresponding subset of the
ambient space. -/
def subsetSubtypeHomeomorph {S T : Set X} (h : S ⊆ T) :
    ↥(Subtype.val ⁻¹' S : Set ↥T) ≃ₜ ↥S where
  toFun p := ⟨p.1.1, p.2⟩
  invFun p := ⟨⟨p.1, h p.2⟩, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- A homeomorphism of spaces restricts to a homeomorphism of the complements
of a point and its image. -/
def puncturedHomeomorph (e : X ≃ₜ Y) (p : X) :
    ↥({q : X | q ≠ p}) ≃ₜ ↥({q : Y | q ≠ e p}) where
  toFun q := ⟨e q.1, fun h => q.2 (e.injective h)⟩
  invFun q := ⟨e.symm q.1,
    fun h => q.2 ((e.apply_symm_apply q.1).symm.trans (congrArg e h))⟩
  left_inv q := by ext; simp
  right_inv q := by ext; simp
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

end SubtypeHelpers

section PuncturedNeighborhood

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A punctured ball around `x` of radius `ε`. -/
def puncturedNbhd (x : E) (ε : ℝ) : Set E := {z | z ≠ x ∧ ‖z - x‖ < ε}

omit [NormedSpace ℝ E] in
theorem mem_puncturedNbhd {x z : E} {ε : ℝ} :
    z ∈ puncturedNbhd x ε ↔ z ≠ x ∧ ‖z - x‖ < ε := Iff.rfl

omit [NormedSpace ℝ E] in
theorem norm_sub_pos_of_mem_puncturedNbhd {x z : E} {ε : ℝ} (hz : z ∈ puncturedNbhd x ε) :
    0 < ‖z - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz.1)

variable (x : E) (ε : ℝ) (hε : 0 < ε)

/-- The radial projection of the punctured ball to the unit sphere. -/
def puncturedToSphere : C(↥(puncturedNbhd x ε), ↥(sphere (0 : E) 1)) where
  toFun z := ⟨‖(z : E) - x‖⁻¹ • ((z : E) - x), by
    have hpos := norm_sub_pos_of_mem_puncturedNbhd z.2
    simp only [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm]
    field_simp⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.smul
    · exact (continuous_norm.comp ((continuous_subtype_val).sub continuous_const)).inv₀
        (fun z => ne_of_gt (norm_sub_pos_of_mem_puncturedNbhd z.2))
    · exact (continuous_subtype_val).sub continuous_const

include hε in
theorem sphereMap_mem_puncturedNbhd (u : ↥(sphere (0 : E) 1)) :
    x + (ε / 2) • (u : E) ∈ puncturedNbhd x ε := by
  have hu : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
  constructor
  · intro h
    have : (ε / 2) • (u : E) = 0 := by
      have := congrArg (fun z => z - x) h
      simpa using this
    rw [smul_eq_zero] at this
    rcases this with h1 | h2
    · linarith [h1 ▸ hε]
    · rw [h2] at hu; simp at hu
  · have : x + (ε / 2) • (u : E) - x = (ε / 2) • (u : E) := by abel
    rw [this, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith

/-- The inclusion of the unit sphere into the punctured ball, at radius
`ε / 2`. -/
def sphereToPunctured : C(↥(sphere (0 : E) 1), ↥(puncturedNbhd x ε)) where
  toFun u := ⟨x + (ε / 2) • (u : E), sphereMap_mem_puncturedNbhd x ε hε u⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.add (continuous_const.smul continuous_subtype_val)

include hε in
theorem puncturedToSphere_comp_sphereToPunctured :
    (puncturedToSphere x ε).comp (sphereToPunctured x ε hε) = ContinuousMap.id _ := by
  ext u
  have hu : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
  have hsub : x + (ε / 2) • (u : E) - x = (ε / 2) • (u : E) := by abel
  change ‖x + (ε / 2) • (u : E) - x‖⁻¹ • (x + (ε / 2) • (u : E) - x) = (u : E)
  rw [hsub, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith), smul_smul]
  rw [inv_mul_cancel₀ (by linarith), one_smul]

/-- The straight line homotopy from the identity of the punctured ball to the
radial retraction onto the sphere of radius `ε / 2`. -/
def puncturedHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(puncturedNbhd x ε))
      ((sphereToPunctured x ε hε).comp (puncturedToSphere x ε)) where
  toFun p := ⟨x + ((1 - (p.1 : ℝ)) + (p.1 : ℝ) * (ε / 2) * ‖(p.2 : E) - x‖⁻¹) •
      ((p.2 : E) - x), by
    set t : ℝ := (p.1 : ℝ) with ht
    have ht0 : 0 ≤ t := p.1.2.1
    have ht1 : t ≤ 1 := p.1.2.2
    have hpos := norm_sub_pos_of_mem_puncturedNbhd p.2.2
    have hlt := p.2.2.2
    set c : ℝ := (1 - t) + t * (ε / 2) * ‖(p.2 : E) - x‖⁻¹ with hc
    have hcpos : 0 < c := by
      rcases eq_or_lt_of_le ht1 with h | h
      · rw [hc, ← h]
        simp only [sub_self, zero_add]
        positivity
      · have h1 : 0 < 1 - t := by linarith
        have h2 : 0 ≤ t * (ε / 2) * ‖(p.2 : E) - x‖⁻¹ := by positivity
        linarith
    have hnorm : c * ‖(p.2 : E) - x‖ = (1 - t) * ‖(p.2 : E) - x‖ + t * (ε / 2) := by
      have hN : ‖(p.2 : E) - x‖ ≠ 0 := ne_of_gt hpos
      rw [hc]
      field_simp
    constructor
    · intro h
      have hz : c • ((p.2 : E) - x) = 0 := by
        have := congrArg (fun z => z - x) h
        simpa using this
      rcases smul_eq_zero.mp hz with h1 | h2
      · exact absurd h1 (ne_of_gt hcpos)
      · rw [h2] at hpos; simp at hpos
    · have hsub : x + c • ((p.2 : E) - x) - x = c • ((p.2 : E) - x) := by abel
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, hnorm]
      nlinarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.add continuous_const
    apply Continuous.smul
    · apply Continuous.add
      · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst))
      · apply Continuous.mul
        · exact (continuous_subtype_val.comp continuous_fst).mul continuous_const
        · exact (continuous_norm.comp
            ((continuous_subtype_val.comp continuous_snd).sub continuous_const)).inv₀
            (fun p => ne_of_gt (norm_sub_pos_of_mem_puncturedNbhd p.2.2))
    · exact (continuous_subtype_val.comp continuous_snd).sub continuous_const
  map_zero_left z := by
    apply Subtype.ext
    change x + ((1 - (0 : ℝ)) + (0 : ℝ) * (ε / 2) * ‖(z : E) - x‖⁻¹) • ((z : E) - x) = (z : E)
    simp
  map_one_left z := by
    apply Subtype.ext
    change x + ((1 - (1 : ℝ)) + (1 : ℝ) * (ε / 2) * ‖(z : E) - x‖⁻¹) • ((z : E) - x) =
      x + (ε / 2) • (‖(z : E) - x‖⁻¹ • ((z : E) - x))
    rw [smul_smul]
    norm_num

/-- **The punctured ball is homotopy equivalent to the unit sphere.** -/
def puncturedNbhdHomotopyEquiv :
    ContinuousMap.HomotopyEquiv ↥(puncturedNbhd x ε) ↥(sphere (0 : E) 1) where
  toFun := puncturedToSphere x ε
  invFun := sphereToPunctured x ε hε
  left_inv := ⟨(puncturedHomotopy x ε hε).symm⟩
  right_inv := by
    rw [puncturedToSphere_comp_sphereToPunctured x ε hε]

end PuncturedNeighborhood

section Ball

open AffineTverberg.Simplicial

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The closed unit ball with one point removed, as a subset of the subtype. -/
def ballPunctured (p : ↥(closedBall (0 : E) 1)) : Set ↥(closedBall (0 : E) 1) :=
  {q | q ≠ p}

omit [NormedSpace ℝ E] in
theorem isOpen_ballPunctured (p : ↥(closedBall (0 : E) 1)) : IsOpen (ballPunctured p) :=
  isOpen_compl_singleton

omit [NormedSpace ℝ E] in
theorem ballPunctured_eq_preimage (p : ↥(closedBall (0 : E) 1)) :
    ballPunctured p = Subtype.val ⁻¹' (closedBall (0 : E) 1 \ {(p : E)}) := by
  ext q
  simp only [ballPunctured, Set.mem_ofPred_eq, mem_preimage, Set.mem_sdiff, mem_singleton_iff]
  exact ⟨fun h => ⟨q.2, fun hq => h (Subtype.ext hq)⟩,
    fun h hq => h.2 (congrArg Subtype.val hq)⟩

/-- Removing a boundary point of the closed unit ball leaves a star convex set. -/
theorem starConvex_closedBall_sdiff (x : E) (hx : ‖x‖ = 1) :
    StarConvex ℝ (0 : E) (closedBall (0 : E) 1 \ {x}) := by
  rintro y ⟨hy, hyx⟩ a b ha hb hab
  have hy1 : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
  have hb1 : b ≤ 1 := by linarith
  have hzero : a • (0 : E) + b • y = b • y := by simp
  rw [hzero]
  constructor
  · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    nlinarith
  · intro hmem
    have h : b • y = x := hmem
    have hnorm : b * ‖y‖ = 1 := by
      have hcongr := congrArg norm h
      rwa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb, hx] at hcongr
    have hmul : b * ‖y‖ ≤ b * 1 := mul_le_mul_of_nonneg_left hy1 hb
    rw [hnorm] at hmul
    have hb' : b = 1 := le_antisymm hb1 (by linarith)
    exact hyx (mem_singleton_iff.mpr (by rw [← h, hb', one_smul]))

/-- The punctured closed ball at a boundary point is contractible. -/
theorem contractibleSpace_ballPunctured_of_norm_eq_one (p : ↥(closedBall (0 : E) 1))
    (hp : ‖(p : E)‖ = 1) : ContractibleSpace ↥(ballPunctured p) := by
  have hne : (closedBall (0 : E) 1 \ {(p : E)}).Nonempty := by
    refine ⟨0, by simp, ?_⟩
    intro h0
    have : ‖(p : E)‖ = 0 := by
      rw [← mem_singleton_iff.mp h0, norm_zero]
    rw [hp] at this
    norm_num at this
  have hcontr : ContractibleSpace ↥(closedBall (0 : E) 1 \ {(p : E)}) :=
    (starConvex_closedBall_sdiff (p : E) hp).contractibleSpace hne
  have hhomeo : ↥(ballPunctured p) ≃ₜ ↥(closedBall (0 : E) 1 \ {(p : E)}) :=
    (Homeomorph.setCongr (ballPunctured_eq_preimage p)).trans
      (subsetSubtypeHomeomorph Set.sdiff_subset)
  exact hhomeo.toHomotopyEquiv.contractibleSpace

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- **The local homology at a boundary point of the ball vanishes.** -/
theorem finrank_homology_ballPunctured_of_norm_eq_one {n : ℕ}
    (p : ↥(closedBall (0 : E) 1)) (hp : ‖(p : E)‖ = 1) :
    Module.finrank ℝ ((realSingularHomology (n + 1)).obj
      (TopCat.of ↥(ballPunctured p))) = 0 := by
  have := contractibleSpace_ballPunctured_of_norm_eq_one p hp
  have hsub : Subsingleton
      ((realSingularHomology (n + 1)).obj (TopCat.of ↥(ballPunctured p))) :=
    realSingularHomology_subsingleton_of_contractible (↥(ballPunctured p)) (n + 1) (by omega)
  exact Module.finrank_zero_of_subsingleton

/-- The punctured ball has finite-dimensional homology of rank at most one
at an interior point. Finiteness is explicit: a `finrank` bound alone would
not exclude infinite-dimensional vector spaces. -/
theorem finiteDimensional_and_finrank_homology_ballPunctured_of_norm_lt_one {n : ℕ}
    (hdim : Module.finrank ℝ E = n + 2)
    (p : ↥(closedBall (0 : E) 1)) (hp : ‖(p : E)‖ < 1) :
    FiniteDimensional ℝ ((realSingularHomology (n + 1)).obj
      (TopCat.of ↥(ballPunctured p))) ∧
    Module.finrank ℝ ((realSingularHomology (n + 1)).obj
      (TopCat.of ↥(ballPunctured p))) ≤ 1 := by
  classical
  set x : E := (p : E) with hx
  set ε : ℝ := (1 - ‖x‖) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hsubset : puncturedNbhd x ε ⊆ closedBall (0 : E) 1 := by
    rintro z ⟨-, hz⟩
    have htri : ‖z‖ ≤ ‖z - x‖ + ‖x‖ := by
      have := norm_add_le (z - x) x
      simpa using this
    rw [hεdef] at hz
    rw [mem_closedBall_zero_iff]
    linarith
  set A : Set ↥(closedBall (0 : E) 1) := ballPunctured p with hA
  set B : Set ↥(closedBall (0 : E) 1) := {q | ‖(q : E) - x‖ < ε} with hB
  have hAopen : IsOpen A := isOpen_ballPunctured p
  have hBopen : IsOpen B := by
    have hcont : Continuous fun q : ↥(closedBall (0 : E) 1) => ‖(q : E) - x‖ :=
      continuous_norm.comp (continuous_subtype_val.sub continuous_const)
    exact isOpen_lt hcont continuous_const
  have hcov : ∀ q : ↥(closedBall (0 : E) 1), q ∈ A ∨ q ∈ B := by
    intro q
    by_cases h : q = p
    · refine Or.inr ?_
      change ‖(q : E) - x‖ < ε
      rw [h, ← hx, sub_self, norm_zero]
      exact hε
    · exact Or.inl h
  have hballne : (closedBall (0 : E) 1).Nonempty := ⟨0, by simp⟩
  have : ContractibleSpace ↥(closedBall (0 : E) 1) :=
    (convex_closedBall (0 : E) 1).contractibleSpace hballne
  have hXsub : Subsingleton ((realSingularHomology (n + 1)).obj
      (TopCat.of ↥(closedBall (0 : E) 1))) :=
    realSingularHomology_subsingleton_of_contractible
      (↥(closedBall (0 : E) 1)) (n + 1) (by omega)
  have hXzero : IsZero ((realSingularHomology (n + 1)).obj
      (TopCat.of ↥(closedBall (0 : E) 1))) :=
    ModuleCat.isZero_of_subsingleton _
  have hinter : A ∩ B = Subtype.val ⁻¹' (puncturedNbhd x ε) := by
    ext q
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun hq => h1 (Subtype.ext (by rw [hq, hx])), h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun hq => h1 (by rw [hq, hx]), h2⟩
  have hhomeo : ↥(A ∩ B) ≃ₜ ↥(puncturedNbhd x ε) :=
    (Homeomorph.setCongr hinter).trans (subsetSubtypeHomeomorph hsubset)
  have hequiv : ContinuousMap.HomotopyEquiv ↥(A ∩ B) ↥(sphere (0 : E) 1) :=
    hhomeo.toHomotopyEquiv.trans (puncturedNbhdHomotopyEquiv x ε hε)
  have hiso := (realSingularHomologyIsoOfHomotopyEquiv hequiv (n + 1)).toLinearEquiv
  have hsph := Simplicial.finrank_realSingularHomology_sphere (E := E) (n := n) hdim
  have hfdsph := Simplicial.finiteDimensional_realSingularHomology_sphere (E := E) (n := n) hdim
  have hfd : FiniteDimensional ℝ ((realSingularHomology (n + 1)).obj
      (TopCat.of ↥(A ∩ B))) := hiso.symm.finiteDimensional
  have hrank : Module.finrank ℝ ((realSingularHomology (n + 1)).obj
      (TopCat.of ↥(A ∩ B))) = 1 := by
    rw [hiso.finrank_eq]
    exact hsph
  have hle := AffChain.finrank_homology_le_of_cover (X := TopCat.of ↥(closedBall (0 : E) 1))
    A B hAopen hBopen hcov (n + 1) hXzero
  rw [hrank] at hle
  exact ⟨AffChain.finiteDimensional_homology_of_cover
    (X := TopCat.of ↥(closedBall (0 : E) 1)) A B hAopen hBopen hcov (n + 1) hXzero, hle⟩

/-- **The local homology at an interior point of the ball has rank at most
one**, by Mayer-Vietoris and the rank of the sphere. -/
theorem finrank_homology_ballPunctured_of_norm_lt_one {n : ℕ}
    (hdim : Module.finrank ℝ E = n + 2)
    (p : ↥(closedBall (0 : E) 1)) (hp : ‖(p : E)‖ < 1) :
    Module.finrank ℝ ((realSingularHomology (n + 1)).obj
      (TopCat.of ↥(ballPunctured p))) ≤ 1 :=
  (finiteDimensional_and_finrank_homology_ballPunctured_of_norm_lt_one hdim p hp).2

/-- Actual finiteness of the punctured ball's top homology, at every point. -/
theorem finiteDimensional_homology_ballPunctured {n : ℕ}
    (hdim : Module.finrank ℝ E = n + 2) (p : ↥(closedBall (0 : E) 1)) :
    FiniteDimensional ℝ ((realSingularHomology (n + 1)).obj
      (TopCat.of ↥(ballPunctured p))) := by
  rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp p.property) with h | h
  · exact (finiteDimensional_and_finrank_homology_ballPunctured_of_norm_lt_one hdim p h).1
  · have := contractibleSpace_ballPunctured_of_norm_eq_one p h
    have := realSingularHomology_subsingleton_of_contractible
      (↥(ballPunctured p)) (n + 1) (by omega)
    infer_instance

/-- **The local homology of a closed ball has rank at most one at every
point.**  This is the topological input for the ridge degree bound. -/
theorem finrank_homology_ballPunctured_le_one {n : ℕ}
    (hdim : Module.finrank ℝ E = n + 2) (p : ↥(closedBall (0 : E) 1)) :
    Module.finrank ℝ ((realSingularHomology (n + 1)).obj
      (TopCat.of ↥(ballPunctured p))) ≤ 1 := by
  have hp : ‖(p : E)‖ ≤ 1 := mem_closedBall_zero_iff.mp p.2
  rcases lt_or_eq_of_le hp with h | h
  · exact finrank_homology_ballPunctured_of_norm_lt_one hdim p h
  · rw [finrank_homology_ballPunctured_of_norm_eq_one (n := n) p h]
    norm_num

end Ball

end AffineTverberg
