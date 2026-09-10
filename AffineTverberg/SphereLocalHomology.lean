import AffineTverberg.SphereMiddleHomology
import AffineTverberg.SphereTopHomology
import AffineTverberg.PuncturedBall
import AffineTverberg.RelativeSingularHomology
import AffineTverberg.RelativeHomologyShift
import AffineTverberg.MayerVietorisRank

set_option linter.style.header false

/-!
# Local homology of a space presented as a sphere

This file is the local part of the geometric duality argument.  Its input is
the *actual* sphere homeomorphism of a space `X` (for the boundary join this is
`IsSimplicialBall.fullBoundaryJoinHomeomorphSphere`), and its output is the
local homology of `X` at a point, in the shape in which a dual-cell argument
uses it: for every open contractible neighbourhood `B` of a point `P`,

`H_{k+1}(X) ≅ H_k(B ∖ {P})`,

so a punctured neighbourhood is a homology `(N-1)`-sphere.  Nothing about
combinatorial or piecewise-linear structure is used: the only inputs are the
homeomorphism with a norm sphere and Mayer-Vietoris.

The two ingredients are:

* `contractibleSpace_sphere_sdiff_singleton` — the unit sphere of *any* real
  normed space with one point removed is contractible.  The contraction is the
  explicit normalized segment `t ↦ ‖(1-t)x - tv‖⁻¹ • ((1-t)x - tv)`, which
  never meets the origin and never returns to the deleted point; no inner
  product, stereographic projection or finite dimensionality is needed.
* `AffChain.isIso_mvDelta_of_isZero` — the Mayer-Vietoris connecting map is an
  isomorphism whenever both pieces of the cover are acyclic in the two relevant
  degrees.  This upgrades the existing injectivity and surjectivity statements
  to an actual isomorphism of homology modules.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric Set

namespace AffineTverberg

/-! ### The punctured norm sphere is contractible -/

section PuncturedSphere

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The segment from a point of the punctured sphere to the antipode of the
deleted point never passes through the origin. -/
theorem punctured_sphere_segment_ne_zero {v x : E} (hv : ‖v‖ = 1) (hx : ‖x‖ = 1)
    (hxv : x ≠ v) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) • x - t • v ≠ 0 := by
  intro h
  have hEq : (1 - t) • x = t • v := sub_eq_zero.mp h
  have hnorm : |1 - t| = |t| := by
    have := congrArg norm hEq
    rwa [norm_smul, norm_smul, hx, hv, Real.norm_eq_abs, Real.norm_eq_abs,
      mul_one, mul_one] at this
  have ht : t = 1 / 2 := by
    rw [abs_of_nonneg (by linarith), abs_of_nonneg ht0] at hnorm
    linarith
  apply hxv
  rw [ht] at hEq
  have h4 : (1 / 2 : ℝ) • x = (1 / 2 : ℝ) • v := by
    rw [← hEq]; norm_num
  exact smul_right_injective E (by norm_num : (1 / 2 : ℝ) ≠ 0) h4

/-- The normalized segment stays on the sphere and never returns to the deleted
point. -/
theorem punctured_sphere_segment_mem {v x : E} (hv : ‖v‖ = 1) (hx : ‖x‖ = 1)
    (hxv : x ≠ v) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(1 - t) • x - t • v‖⁻¹ • ((1 - t) • x - t • v) ∈ sphere (0 : E) 1 \ {v} := by
  set w : E := (1 - t) • x - t • v with hw
  have hwne : w ≠ 0 := punctured_sphere_segment_ne_zero hv hx hxv ht0 ht1
  have hnorm : ‖‖w‖⁻¹ • w‖ = 1 := norm_smul_inv_norm hwne
  refine ⟨by simpa [mem_sphere_iff_norm] using hnorm, ?_⟩
  simp only [mem_singleton_iff]
  intro hEq
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  have hwv : w = ‖w‖ • v := by
    have := congrArg (fun z => (‖w‖ : ℝ) • z) hEq
    simpa [smul_smul, mul_inv_cancel₀ (ne_of_gt hwpos)] using this
  have hxvEq : (1 - t) • x = (‖w‖ + t) • v := by
    have hb : (1 - t) • x - t • v = ‖w‖ • v := by rw [← hw]; exact hwv
    have h2 : (1 - t) • x = ‖w‖ • v + t • v := by rw [← hb]; abel
    rw [h2, add_smul]
  rcases eq_or_lt_of_le ht1 with ht | ht
  · -- `t = 1` : the left side is zero but the right side has positive norm
    have hzero : ((‖w‖ + t) • v : E) = 0 := by
      rw [← hxvEq, ← ht]
      simp
    have hnv : ‖((‖w‖ + t) • v : E)‖ = 0 := by rw [hzero]; simp
    rw [norm_smul, hv, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)] at hnv
    linarith
  · have h1t : 0 < 1 - t := by linarith
    have hcoef : x = ((‖w‖ + t) / (1 - t)) • v := by
      have hs := congrArg (fun z => (1 - t)⁻¹ • z) hxvEq
      simp only [smul_smul, inv_mul_cancel₀ (ne_of_gt h1t), one_smul] at hs
      rw [hs, div_eq_inv_mul]
    have hnx : |(‖w‖ + t) / (1 - t)| = 1 := by
      have hs := congrArg norm hcoef
      rw [hx, norm_smul, hv, mul_one, Real.norm_eq_abs] at hs
      exact hs.symm
    have hpos : 0 < (‖w‖ + t) / (1 - t) := by positivity
    rw [abs_of_pos hpos] at hnx
    exact hxv (by rw [hcoef, hnx, one_smul])

/-- **The unit sphere of a real normed space with one point removed is
contractible.**  The contraction is the explicit normalized segment towards the
antipode of the deleted point. -/
theorem contractibleSpace_sphere_sdiff_singleton {v : E} (hv : ‖v‖ = 1) :
    ContractibleSpace ↥(sphere (0 : E) 1 \ {v}) := by
  classical
  have hvne : v ≠ 0 := by
    intro h; rw [h] at hv; simp at hv
  have hneg : (-v) ∈ sphere (0 : E) 1 \ {v} := by
    refine ⟨by simpa [mem_sphere_iff_norm] using hv, ?_⟩
    simp only [mem_singleton_iff]
    intro h
    have h2 : (2 : ℝ) • v = 0 := by
      rw [two_smul]
      have := congrArg (fun z => z + v) h
      simpa [neg_add_cancel] using this.symm
    simp only [smul_eq_zero] at h2
    rcases h2 with h2 | h2
    · norm_num at h2
    · exact hvne h2
  have hmap : ∀ (p : unitInterval × ↥(sphere (0 : E) 1 \ {v})),
      ‖(1 - (p.1 : ℝ)) • (p.2 : E) - (p.1 : ℝ) • v‖⁻¹ •
        ((1 - (p.1 : ℝ)) • (p.2 : E) - (p.1 : ℝ) • v) ∈ sphere (0 : E) 1 \ {v} := by
    rintro ⟨⟨t, ht0, ht1⟩, ⟨x, hx1, hx2⟩⟩
    exact punctured_sphere_segment_mem hv (by simpa [mem_sphere_iff_norm] using hx1)
      (by simpa using hx2) ht0 ht1
  have hne : ∀ (p : unitInterval × ↥(sphere (0 : E) 1 \ {v})),
      (1 - (p.1 : ℝ)) • (p.2 : E) - (p.1 : ℝ) • v ≠ 0 := by
    rintro ⟨⟨t, ht0, ht1⟩, ⟨x, hx1, hx2⟩⟩
    exact punctured_sphere_segment_ne_zero hv (by simpa [mem_sphere_iff_norm] using hx1)
      (by simpa using hx2) ht0 ht1
  have hcontw : Continuous fun p : unitInterval × ↥(sphere (0 : E) 1 \ {v}) =>
      (1 - (p.1 : ℝ)) • (p.2 : E) - (p.1 : ℝ) • v :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp continuous_snd)).sub
      ((continuous_subtype_val.comp continuous_fst).smul continuous_const)
  let H : ContinuousMap.Homotopy (ContinuousMap.id ↥(sphere (0 : E) 1 \ {v}))
      (ContinuousMap.const _ (⟨-v, hneg⟩ : ↥(sphere (0 : E) 1 \ {v}))) :=
    { toFun := fun p => ⟨‖(1 - (p.1 : ℝ)) • (p.2 : E) - (p.1 : ℝ) • v‖⁻¹ •
        ((1 - (p.1 : ℝ)) • (p.2 : E) - (p.1 : ℝ) • v), hmap p⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact ((hcontw.norm.inv₀ (fun p => norm_ne_zero_iff.mpr (hne p)))).smul hcontw
      map_zero_left := by
        rintro ⟨x, hx1, hx2⟩
        apply Subtype.ext
        have hx : ‖x‖ = 1 := by simpa [mem_sphere_iff_norm] using hx1
        simp [hx]
      map_one_left := by
        rintro ⟨x, hx1, hx2⟩
        apply Subtype.ext
        simp [hv] }
  rw [contractible_iff_id_nullhomotopic]
  exact ⟨⟨-v, hneg⟩, ⟨H⟩⟩

end PuncturedSphere

/-- A space presented as a norm sphere is contractible after removing a
point. -/
theorem contractibleSpace_punctured_of_homeomorph_sphere {X : Type} [TopologicalSpace X]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : X ≃ₜ sphere (0 : E) 1) (P : X) :
    ContractibleSpace ↥{q : X | q ≠ P} := by
  classical
  have hv : ‖((h P : ↥(sphere (0 : E) 1)) : E)‖ = 1 := by
    simp
  have hcontr : ContractibleSpace ↥(sphere (0 : E) 1 \ {((h P : ↥(sphere (0 : E) 1)) : E)}) :=
    contractibleSpace_sphere_sdiff_singleton hv
  have hhom : ↥{q : X | q ≠ P} ≃ₜ ↥{q : ↥(sphere (0 : E) 1) | q ≠ h P} :=
    puncturedHomeomorph h P
  have hset : {q : ↥(sphere (0 : E) 1) | q ≠ h P} =
      Subtype.val ⁻¹' (sphere (0 : E) 1 \ {((h P : ↥(sphere (0 : E) 1)) : E)}) := by
    ext q
    constructor
    · intro hq
      exact ⟨q.property, fun hcon => hq (Subtype.ext hcon)⟩
    · rintro ⟨-, hq⟩
      exact fun hcon => hq (by rw [hcon]; exact rfl)
  have hhom2 : ↥{q : ↥(sphere (0 : E) 1) | q ≠ h P} ≃ₜ
      ↥(sphere (0 : E) 1 \ {((h P : ↥(sphere (0 : E) 1)) : E)}) :=
    (Homeomorph.setCongr hset).trans (subsetSubtypeHomeomorph (fun _ hx => hx.1))
  exact (hhom.trans hhom2).toHomotopyEquiv.contractibleSpace

/-! ### The Mayer-Vietoris connecting map as an isomorphism -/

namespace AffChain

variable {X : TopCat.{0}} (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
  (hcov : ∀ x, x ∈ A ∨ x ∈ B)

/-- If both pieces of the cover are acyclic in degrees `n` and `n + 1`, the
Mayer-Vietoris connecting map `H_{n+1}(X) → H_n(A ∩ B)` is an isomorphism. -/
theorem isIso_mvDelta_of_isZero (n : ℕ)
    (hA1 : IsZero ((realSingularHomology (n + 1)).obj (subSpace A)))
    (hB1 : IsZero ((realSingularHomology (n + 1)).obj (subSpace B)))
    (hA0 : IsZero ((realSingularHomology n).obj (subSpace A)))
    (hB0 : IsZero ((realSingularHomology n).obj (subSpace B))) :
    IsIso (mvDelta A B hA hB hcov n) := by
  have hbip : ∀ (Y Z : ModuleCat.{0} ℝ), IsZero Y → IsZero Z → IsZero (Y ⊞ Z) := by
    intro Y Z hY hZ
    rw [IsZero.iff_id_eq_zero]
    apply biprod.hom_ext' <;> [exact hY.eq_of_src _ _; exact hZ.eq_of_src _ _]
  have hpair1 : IsZero ((pairCx (singChains (subSpace A)) (singChains (subSpace B))).homology
      (n + 1)) :=
    IsZero.of_iso (hbip _ _ hA1 hB1)
      (homologyPairIso (singChains (subSpace A)) (singChains (subSpace B)) (n + 1))
  have hpair0 : IsZero ((pairCx (singChains (subSpace A)) (singChains (subSpace B))).homology n) :=
    IsZero.of_iso (hbip _ _ hA0 hB0)
      (homologyPairIso (singChains (subSpace A)) (singChains (subSpace B)) n)
  have hmono : Mono (mvDelta A B hA hB hcov n) := by
    have hbeta : mvBeta A B (n + 1) = 0 := hpair1.eq_zero_of_src _
    exact (ShortComplex.exact_iff_mono
      (ShortComplex.mk (mvBeta A B (n + 1)) (mvDelta A B hA hB hcov n)
        (mvBeta_comp_mvDelta A B hA hB hcov n)) hbeta).mp (mv_exact_space A B hA hB hcov n)
  have hepi : Epi (mvDelta A B hA hB hcov n) := by
    have halpha : mvAlpha A B n = 0 := hpair0.eq_zero_of_tgt _
    exact (ShortComplex.exact_iff_epi
      (ShortComplex.mk (mvDelta A B hA hB hcov n) (mvAlpha A B n)
        (mvDelta_comp_mvAlpha A B hA hB hcov n)) halpha).mp (mv_exact_inter A B hA hB hcov n)
  exact isIso_of_mono_of_epi _

/-- The resulting isomorphism `H_{n+1}(X) ≅ H_n(A ∩ B)` of homology modules. -/
def mvDeltaIso (n : ℕ)
    (hA1 : IsZero ((realSingularHomology (n + 1)).obj (subSpace A)))
    (hB1 : IsZero ((realSingularHomology (n + 1)).obj (subSpace B)))
    (hA0 : IsZero ((realSingularHomology n).obj (subSpace A)))
    (hB0 : IsZero ((realSingularHomology n).obj (subSpace B))) :
    (realSingularHomology (n + 1)).obj X ≅
      (realSingularHomology n).obj (subSpace (A ∩ B)) :=
  @asIso _ _ _ _ (mvDelta A B hA hB hcov n)
    (isIso_mvDelta_of_isZero A B hA hB hcov n hA1 hB1 hA0 hB0)

end AffChain

/-! ### Local homology of a space presented as a sphere -/

section SphereLocal

variable {X : Type} [TopologicalSpace X] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Positive-degree acyclicity of the punctured space, from the sphere
presentation. -/
theorem isZero_realSingularHomology_punctured_of_sphere (hsph : X ≃ₜ sphere (0 : E) 1)
    (P : X) (j : ℕ) (hj : 0 < j) :
    IsZero ((realSingularHomology j).obj
      (AffChain.subSpace (X := TopCat.of X) {q : X | q ≠ P})) := by
  have : ContractibleSpace ↥{q : X | q ≠ P} :=
    contractibleSpace_punctured_of_homeomorph_sphere hsph P
  have := realSingularHomology_subsingleton_of_contractible ↥{q : X | q ≠ P} j (by omega)
  exact ModuleCat.isZero_of_subsingleton _

/-- **The local homology isomorphism.**  If `X` is homeomorphic to a norm
sphere and `B` is an open contractible neighbourhood of a point `P`, then the
punctured neighbourhood `B ∖ {P}` carries the homology of `X`, shifted by one:
`H_{k+1}(X) ≅ H_k(B ∖ {P})` for every `k ≥ 1`.

This is the local input of the dual-cell duality argument, derived from the
actual sphere homeomorphism only. -/
def puncturedNbhdHomologyIso (hsph : X ≃ₜ sphere (0 : E) 1) {P : X} {B : Set X}
    (hBopen : IsOpen B) (hPB : P ∈ B) (hBcontr : ContractibleSpace ↥B) (k : ℕ) (hk : 0 < k) :
    (realSingularHomology (k + 1)).obj (TopCat.of X) ≅
      (realSingularHomology k).obj
        (AffChain.subSpace (X := TopCat.of X) ({q : X | q ≠ P} ∩ B)) := by
  classical
  haveI : T1Space X := Homeomorph.t1Space hsph.symm
  have hAopen : IsOpen {q : X | q ≠ P} := isOpen_compl_singleton
  have hcov : ∀ q : X, q ∈ {q : X | q ≠ P} ∨ q ∈ B := by
    intro q
    by_cases h : q = P
    · exact Or.inr (h ▸ hPB)
    · exact Or.inl h
  have hBzero : ∀ j : ℕ, 0 < j →
      IsZero ((realSingularHomology j).obj (AffChain.subSpace (X := TopCat.of X) B)) := by
    intro j hj
    have := realSingularHomology_subsingleton_of_contractible ↥B j (by omega : j ≠ 0)
    exact ModuleCat.isZero_of_subsingleton _
  exact AffChain.mvDeltaIso (X := TopCat.of X) {q : X | q ≠ P} B hAopen hBopen hcov k
    (isZero_realSingularHomology_punctured_of_sphere hsph P (k + 1) (by omega))
    (hBzero (k + 1) (by omega))
    (isZero_realSingularHomology_punctured_of_sphere hsph P k hk)
    (hBzero k hk)

variable [FiniteDimensional ℝ E]

/-- **Local acyclicity below the top degree.**  For a space presented as an
`N`-sphere, every open contractible punctured neighbourhood is acyclic in all
degrees `k` with `0 < k` and `k + 1 < N`. -/
theorem isZero_realSingularHomology_puncturedNbhd_of_sphere {N : ℕ}
    (hdim : Module.finrank ℝ E = N + 1) (hsph : X ≃ₜ sphere (0 : E) 1)
    {P : X} {B : Set X} (hBopen : IsOpen B) (hPB : P ∈ B) (hBcontr : ContractibleSpace ↥B)
    (k : ℕ) (hk : 0 < k) (hkN : k + 1 < N) :
    IsZero ((realSingularHomology k).obj
      (AffChain.subSpace (X := TopCat.of X) ({q : X | q ≠ P} ∩ B))) := by
  have hX : IsZero ((realSingularHomology (k + 1)).obj (TopCat.of X)) := by
    have := Simplicial.subsingleton_singularHomology_of_homeomorph_sphere hdim hsph (k + 1)
      (by omega) hkN
    exact ModuleCat.isZero_of_subsingleton _
  exact IsZero.of_iso hX
    (puncturedNbhdHomologyIso hsph hBopen hPB hBcontr k hk).symm

/-- **Local acyclicity above the sphere dimension.**  For a space presented as
an `N`-sphere, every open contractible punctured neighbourhood is acyclic in
all degrees `k > N - 1`, i.e. with `N < k + 1`. -/
theorem isZero_realSingularHomology_puncturedNbhd_of_sphere_of_gt {N : ℕ}
    (hdim : Module.finrank ℝ E = N + 1) (hsph : X ≃ₜ sphere (0 : E) 1)
    {P : X} {B : Set X} (hBopen : IsOpen B) (hPB : P ∈ B) (hBcontr : ContractibleSpace ↥B)
    (k : ℕ) (hk : 0 < k) (hkN : N < k + 1) :
    IsZero ((realSingularHomology k).obj
      (AffChain.subSpace (X := TopCat.of X) ({q : X | q ≠ P} ∩ B))) := by
  have hX : IsZero ((realSingularHomology (k + 1)).obj (TopCat.of X)) := by
    have := Simplicial.subsingleton_singularHomology_of_homeomorph_sphere_of_gt hdim hsph (k + 1)
      (by omega)
    exact ModuleCat.isZero_of_subsingleton _
  exact IsZero.of_iso hX (puncturedNbhdHomologyIso hsph hBopen hPB hBcontr k hk).symm

/-- **Local nontriviality in the top degree.**  For a space presented as an
`N`-sphere with `N = k + 1 ≥ 2`, every open contractible punctured
neighbourhood has nontrivial homology in degree `k`: the punctured
neighbourhood is a homology `(N-1)`-sphere. -/
theorem nontrivial_realSingularHomology_puncturedNbhd_of_sphere {k : ℕ}
    (hdim : Module.finrank ℝ E = k + 2) (hsph : X ≃ₜ sphere (0 : E) 1)
    {P : X} {B : Set X} (hBopen : IsOpen B) (hPB : P ∈ B) (hBcontr : ContractibleSpace ↥B)
    (hk : 0 < k) :
    Nontrivial ((realSingularHomology k).obj
      (AffChain.subSpace (X := TopCat.of X) ({q : X | q ≠ P} ∩ B))) := by
  have hsphere : Nontrivial ((realSingularHomology (k + 1)).obj
      (TopCat.of (sphere (0 : E) 1))) := Simplicial.nontrivial_singularHomology_sphere hdim
  apply not_subsingleton_iff_nontrivial.mp
  intro hs
  have hzero : IsZero ((realSingularHomology k).obj
      (AffChain.subSpace (X := TopCat.of X) ({q : X | q ≠ P} ∩ B))) := by
    have := hs
    exact ModuleCat.isZero_of_subsingleton _
  have hX : IsZero ((realSingularHomology (k + 1)).obj (TopCat.of X)) :=
    IsZero.of_iso hzero (puncturedNbhdHomologyIso hsph hBopen hPB hBcontr k hk)
  have hsph0 : Subsingleton ((realSingularHomology (k + 1)).obj
      (TopCat.of (sphere (0 : E) 1))) :=
    (realSingularHomology_subsingleton_iff_of_homotopyEquiv hsph.toHomotopyEquiv (k + 1)).mp
      (ModuleCat.subsingleton_of_isZero hX)
  exact not_subsingleton _ hsph0

end SphereLocal


/-! ### Local homology of the pair `(X, X ∖ {P})` -/

namespace AffChain

variable {X : TopCat.{0}}

-- The actual projection-isomorphism lemma is already proved in RelativeHomologyShift.

/-- The induced isomorphism `H_{k+1}(X) ≅ H_{k+1}(X, A)`. -/
def relPiIso (A : Set X) (k : ℕ)
    (hA1 : IsZero ((singChains (subSpace A)).homology (k + 1)))
    (hA0 : IsZero ((singChains (subSpace A)).homology k)) :
    (singChains X).homology (k + 1) ≅ relativeHomology A (k + 1) :=
  @asIso _ _ _ _ (relPi A (k + 1)) (isIso_relPi_of_isZero A k hA1 hA0)

end AffChain

section LocalHomology

variable {X : Type} [TopologicalSpace X] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Local homology of a space presented as a sphere.**  For every point `P`
of a space homeomorphic to a norm sphere, the local homology of the pair
`(X, X ∖ {P})` in degree `k + 1 ≥ 2` is the homology of `X` itself. -/
def localHomologyIso_of_sphere (hsph : X ≃ₜ sphere (0 : E) 1) (P : X) (k : ℕ) (hk : 0 < k) :
    (realSingularHomology (k + 1)).obj (TopCat.of X) ≅
      AffChain.relativeHomology (X := TopCat.of X) {q : X | q ≠ P} (k + 1) :=
  AffChain.relPiIso (X := TopCat.of X) {q : X | q ≠ P} k
    (isZero_realSingularHomology_punctured_of_sphere hsph P (k + 1) (by omega))
    (isZero_realSingularHomology_punctured_of_sphere hsph P k hk)

variable [FiniteDimensional ℝ E]

/-- Local homology of a sphere-space vanishes away from the sphere dimension. -/
theorem isZero_localHomology_of_sphere {N : ℕ} (hdim : Module.finrank ℝ E = N + 1)
    (hsph : X ≃ₜ sphere (0 : E) 1) (P : X) (k : ℕ) (hk : 0 < k) (hkN : k + 1 < N) :
    IsZero (AffChain.relativeHomology (X := TopCat.of X) {q : X | q ≠ P} (k + 1)) := by
  have hX : IsZero ((realSingularHomology (k + 1)).obj (TopCat.of X)) := by
    have := Simplicial.subsingleton_singularHomology_of_homeomorph_sphere hdim hsph (k + 1)
      (by omega) hkN
    exact ModuleCat.isZero_of_subsingleton _
  exact IsZero.of_iso hX (localHomologyIso_of_sphere hsph P k hk).symm

/-- **The local fundamental class.**  In the sphere dimension the local
homology of a sphere-space at a point is nontrivial. -/
theorem nontrivial_localHomology_of_sphere {k : ℕ} (hdim : Module.finrank ℝ E = k + 2)
    (hsph : X ≃ₜ sphere (0 : E) 1) (P : X) (hk : 0 < k) :
    Nontrivial (AffChain.relativeHomology (X := TopCat.of X) {q : X | q ≠ P} (k + 1)) := by
  have hsphere : Nontrivial ((realSingularHomology (k + 1)).obj
      (TopCat.of (sphere (0 : E) 1))) := Simplicial.nontrivial_singularHomology_sphere hdim
  apply not_subsingleton_iff_nontrivial.mp
  intro hs
  have hzero : IsZero (AffChain.relativeHomology (X := TopCat.of X)
      {q : X | q ≠ P} (k + 1)) := by
    have := hs
    exact ModuleCat.isZero_of_subsingleton _
  have hX : IsZero ((realSingularHomology (k + 1)).obj (TopCat.of X)) :=
    IsZero.of_iso hzero (localHomologyIso_of_sphere hsph P k hk)
  have hsph0 : Subsingleton ((realSingularHomology (k + 1)).obj
      (TopCat.of (sphere (0 : E) 1))) :=
    (realSingularHomology_subsingleton_iff_of_homotopyEquiv hsph.toHomotopyEquiv (k + 1)).mp
      (ModuleCat.subsingleton_of_isZero hX)
  exact not_subsingleton _ hsph0

end LocalHomology

end AffineTverberg
