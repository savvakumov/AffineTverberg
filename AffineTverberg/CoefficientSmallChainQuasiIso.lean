import AffineTverberg.CoefficientSmallChainTheorem
import AffineTverberg.SmallChainQuasiIso

set_option linter.style.header false

/-!
# The small-chain theorem with arbitrary field coefficients

This is the actual small-chain argument over any field. All cycles, boundaries
and induced homology maps refer to Mathlib's singular chain complex; no
vanishing or comparison premise is built into the definitions.
-/

noncomputable section

open CategoryTheory Limits Simplicial Metric AffineTverberg.AffChain
open scoped BigOperators

namespace AffineTverberg.Coefficients.AffChain

variable (𝕜 : Type) [Field 𝕜]
variable {X : TopCat.{0}} {ι : Type}


/-- The restriction of the singular boundary to the small chains. -/
def smallCxD (U : ι → Set X) (n : ℕ) :
    ModuleCat.of 𝕜 (smallChains 𝕜 U (n + 1)) ⟶ ModuleCat.of 𝕜 (smallChains 𝕜 U n) :=
  ModuleCat.ofHom (LinearMap.restrict ((singChains 𝕜 X).d (n + 1) n).hom
    (fun _ hx => smallChains_d 𝕜 U n hx))

/-- The subcomplex of `U`-small singular chains. -/
def smallCx (U : ι → Set X) : ChainComplex (ModuleCat.{0} 𝕜) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of 𝕜 (smallChains 𝕜 U n)) (smallCxD 𝕜 U)
    (fun n => by
      ext x
      change ((singChains 𝕜 X).d (n + 1) n).hom
        (((singChains 𝕜 X).d (n + 2) (n + 1)).hom (x : (singChains 𝕜 X).X (n + 2))) = 0
      have h := congrArg
        (fun (g : (singChains 𝕜 X).X (n + 2) ⟶ (singChains 𝕜 X).X n) =>
          g.hom (x : (singChains 𝕜 X).X (n + 2)))
        (HomologicalComplex.d_comp_d (singChains 𝕜 X) (n + 2) (n + 1) n)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] using h)

lemma smallCx_d_eq (U : ι → Set X) (n : ℕ) : (smallCx 𝕜 U).d (n + 1) n = smallCxD 𝕜 U n :=
  ChainComplex.of_d (fun n => ModuleCat.of 𝕜 (smallChains 𝕜 U n)) (smallCxD 𝕜 U) n

/-- The inclusion of the complex of small chains into the singular chain
complex. -/
def smallInc (U : ι → Set X) : smallCx 𝕜 U ⟶ singChains 𝕜 X where
  f n := ModuleCat.ofHom (smallChains 𝕜 U n).subtype
  comm' i j hij := by
    obtain ⟨rfl⟩ : j + 1 = i := hij
    rw [smallCx_d_eq 𝕜]
    ext x
    rfl

lemma smallInc_injective (U : ι → Set X) (n : ℕ) :
    Function.Injective ((smallInc 𝕜 U).f n).hom := Subtype.val_injective

lemma smallInc_mem (U : ι → Set X) (n : ℕ) (x : (smallCx 𝕜 U).X n) :
    ((smallInc 𝕜 U).f n).hom x ∈ smallChains 𝕜 U n := x.2

lemma smallInc_d_apply (U : ι → Set X) (n j : ℕ) (x : (smallCx 𝕜 U).X n) :
    ((smallInc 𝕜 U).f j).hom (((smallCx 𝕜 U).d n j).hom x) =
      ((singChains 𝕜 X).d n j).hom (((smallInc 𝕜 U).f n).hom x) := by
  have h := congrArg (fun (g : (smallCx 𝕜 U).X n ⟶ (singChains 𝕜 X).X j) => g.hom x)
    ((smallInc 𝕜 U).comm n j)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h.symm

lemma smallCx_d_eq_zero (U : ι → Set X) (n j : ℕ) (x : (smallCx 𝕜 U).X n)
    (h : ((singChains 𝕜 X).d n j).hom (((smallInc 𝕜 U).f n).hom x) = 0) :
    ((smallCx 𝕜 U).d n j).hom x = 0 := by
  apply smallInc_injective 𝕜 U j
  rw [smallInc_d_apply 𝕜, h, map_zero]

/-! ### Homology classes vanish exactly on boundaries -/

/-- In a chain complex of modules, a cycle whose homology class vanishes is a
boundary at the level of cycles. -/
lemma exists_toCycles_of_homologyπ_eq_zero (K : ChainComplex (ModuleCat.{0} 𝕜) ℕ) (n : ℕ)
    (c : K.cycles n) (h : (K.homologyπ n).hom c = 0) :
    ∃ w : K.X (n + 1), (K.toCycles (n + 1) n).hom w = c := by
  have hexact : (ShortComplex.mk (K.toCycles (n + 1) n) (K.homologyπ n)
      (K.toCycles_comp_homologyπ (n + 1) n)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _
      (K.homologyIsCokernel (n + 1) n (by simp))
  exact (ShortComplex.exact_iff_of_hasForget _).1 hexact c h

/-! ### The inclusion of small chains is a quasi-isomorphism -/

/-- Surjectivity on homology: every class is represented by a small cycle. -/
theorem epi_homologyMap_smallInc (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    Epi (HomologicalComplex.homologyMap (smallInc 𝕜 U) n) := by
  rw [ModuleCat.epi_iff_surjective]
  intro h
  obtain ⟨c, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((singChains 𝕜 X).homologyπ n)).1 inferInstance h
  have hz : ∀ j, ((singChains 𝕜 X).d n j).hom (((singChains 𝕜 X).iCycles n).hom c) = 0 := by
    intro j
    have h2 := congrArg (fun (g : (singChains 𝕜 X).cycles n ⟶ (singChains 𝕜 X).X j) => g.hom c)
      ((singChains 𝕜 X).iCycles_d n j)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h2
  obtain ⟨z', hz'small, hz'cyc, w, hw⟩ :=
    exists_small_cycle_homologous 𝕜 U hU hcov (((singChains 𝕜 X).iCycles n).hom c) hz
  set xs : (smallCx 𝕜 U).X n := (⟨z', hz'small⟩ : smallChains 𝕜 U n) with hxs
  have hxsval : ((smallInc 𝕜 U).f n).hom xs = z' := rfl
  have hcyc : ((smallCx 𝕜 U).d n ((ComplexShape.down ℕ).next n)).hom xs = 0 := by
    refine smallCx_d_eq_zero 𝕜 U n _ xs ?_
    rw [hxsval]
    exact hz'cyc _
  set c' := HomologicalComplex.cyclesMk (smallCx 𝕜 U) xs ((ComplexShape.down ℕ).next n) rfl hcyc
    with hc'
  have hic' : ((smallCx 𝕜 U).iCycles n).hom c' = xs :=
    HomologicalComplex.i_cyclesMk (smallCx 𝕜 U) xs _ rfl hcyc
  refine ⟨((smallCx 𝕜 U).homologyπ n).hom c', ?_⟩
  have hnat := congrArg (fun (g : (smallCx 𝕜 U).cycles n ⟶ (singChains 𝕜 X).homology n) => g.hom c')
    (HomologicalComplex.homologyπ_naturality (smallInc 𝕜 U) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  rw [hnat]
  have hdiff : c - (HomologicalComplex.cyclesMap (smallInc 𝕜 U) n).hom c' =
      ((singChains 𝕜 X).toCycles (n + 1) n).hom w := by
    apply (ModuleCat.mono_iff_injective ((singChains 𝕜 X).iCycles n)).1 inferInstance
    have h1 := congrArg (fun (g : (smallCx 𝕜 U).cycles n ⟶ (singChains 𝕜 X).X n) => g.hom c')
      (HomologicalComplex.cyclesMap_i (smallInc 𝕜 U) n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    have h2 := congrArg (fun (g : (singChains 𝕜 X).X (n + 1) ⟶ (singChains 𝕜 X).X n) => g.hom w)
      ((singChains 𝕜 X).toCycles_i (n + 1) n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    rw [map_sub, h1, h2, hic', hxsval, ← hw]
  have hzero : ((singChains 𝕜 X).homologyπ n).hom
      (((singChains 𝕜 X).toCycles (n + 1) n).hom w) = 0 := by
    have h3 := congrArg
      (fun (g : (singChains 𝕜 X).X (n + 1) ⟶ (singChains 𝕜 X).homology n) => g.hom w)
      ((singChains 𝕜 X).toCycles_comp_homologyπ (n + 1) n)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h3
  have hfin := congrArg (fun y => ((singChains 𝕜 X).homologyπ n).hom y) hdiff
  simp only [map_sub, hzero] at hfin
  exact (sub_eq_zero.1 hfin).symm

/-- Injectivity on homology: a small cycle bounding in the singular complex
bounds a small chain. -/
theorem mono_homologyMap_smallInc (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    Mono (HomologicalComplex.homologyMap (smallInc 𝕜 U) n) := by
  rw [ModuleCat.mono_iff_injective]
  refine (injective_iff_map_eq_zero _).2 fun h hh => ?_
  obtain ⟨c', rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((smallCx 𝕜 U).homologyπ n)).1 inferInstance h
  -- the class of the image cycle vanishes
  have hnat := congrArg (fun (g : (smallCx 𝕜 U).cycles n ⟶ (singChains 𝕜 X).homology n) => g.hom c')
    (HomologicalComplex.homologyπ_naturality (smallInc 𝕜 U) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  rw [hnat] at hh
  obtain ⟨w, hwc⟩ := exists_toCycles_of_homologyπ_eq_zero 𝕜 (singChains 𝕜 X) n
    ((HomologicalComplex.cyclesMap (smallInc 𝕜 U) n).hom c') hh
  -- the underlying small cycle
  set zs : (smallCx 𝕜 U).X n := ((smallCx 𝕜 U).iCycles n).hom c' with hzs
  have himg : ((singChains 𝕜 X).d (n + 1) n).hom w = ((smallInc 𝕜 U).f n).hom zs := by
    have h1 := congrArg (fun (g : (smallCx 𝕜 U).cycles n ⟶ (singChains 𝕜 X).X n) => g.hom c')
      (HomologicalComplex.cyclesMap_i (smallInc 𝕜 U) n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    have h2 := congrArg (fun (g : (singChains 𝕜 X).X (n + 1) ⟶ (singChains 𝕜 X).X n) => g.hom w)
      ((singChains 𝕜 X).toCycles_i (n + 1) n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    rw [← h2, hwc, h1]
  obtain ⟨w', hw'small, hw'⟩ := small_boundary_of_boundary 𝕜 U hU hcov
    (((smallInc 𝕜 U).f n).hom zs) (smallInc_mem 𝕜 U n zs) w himg
  -- lift the bounding chain to the subcomplex
  set ws : (smallCx 𝕜 U).X (n + 1) := (⟨w', hw'small⟩ : smallChains 𝕜 U (n + 1)) with hws
  have hwsval : ((smallInc 𝕜 U).f (n + 1)).hom ws = w' := rfl
  have hdws : ((smallCx 𝕜 U).d (n + 1) n).hom ws = zs := by
    apply smallInc_injective 𝕜 U n
    rw [smallInc_d_apply 𝕜, hwsval, hw']
  have hcyc : ((smallCx 𝕜 U).toCycles (n + 1) n).hom ws = c' := by
    apply (ModuleCat.mono_iff_injective ((smallCx 𝕜 U).iCycles n)).1 inferInstance
    have h2 := congrArg (fun (g : (smallCx 𝕜 U).X (n + 1) ⟶ (smallCx 𝕜 U).X n) => g.hom ws)
      ((smallCx 𝕜 U).toCycles_i (n + 1) n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    rw [h2, hdws, hzs]
  rw [← hcyc]
  have h3 := congrArg (fun (g : (smallCx 𝕜 U).X (n + 1) ⟶ (smallCx 𝕜 U).homology n) => g.hom ws)
    ((smallCx 𝕜 U).toCycles_comp_homologyπ (n + 1) n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h3

/-- **The small chain theorem.** For an open cover `U` of `X`, the inclusion of
the complex of `U`-small singular chains into the singular chain complex is a
quasi-isomorphism. -/
theorem quasiIso_smallInc (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : ∀ x : X, ∃ i, x ∈ U i) : QuasiIso (smallInc 𝕜 U) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have := mono_homologyMap_smallInc 𝕜 U hU hcov n
  have := epi_homologyMap_smallInc 𝕜 U hU hcov n
  exact isIso_of_mono_of_epi _

end AffineTverberg.Coefficients.AffChain

