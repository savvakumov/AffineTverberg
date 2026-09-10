import AffineTverberg.SmallChainTheorem
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.QuasiIso

set_option linter.style.header false

/-!
# The complex of small chains and the small chain quasi-isomorphism

For an open cover `U : ι → Set X` this file packages the submodules
`smallChains U n` of `AffineTverberg.SmallSingular` into an actual chain
complex `smallCx U : ChainComplex (ModuleCat ℝ) ℕ`, constructs the inclusion
chain map `smallInc U : smallCx U ⟶ singChains X`, and proves that it is a
**quasi-isomorphism** (`quasiIso_smallInc`).

The two halves of the small chain theorem proved in
`AffineTverberg.SmallChainTheorem` are exactly what is needed:
`exists_small_cycle_homologous` gives surjectivity of the induced map on
homology and `small_boundary_of_boundary` gives injectivity; the categorical
work here is the translation between elements of the abstract homology objects
and cycles and boundaries.

This settles the first of the remaining obligations listed in
`AffineTverberg.SmallChainTheorem`; singular Mayer-Vietoris, the general
simplicial-to-singular comparison and its specialisations remain open.
-/

noncomputable section

open CategoryTheory Limits

namespace AffineTverberg

namespace AffChain

variable {X : TopCat.{0}} {ι : Type}

/-! ### The complex of small chains -/

/-- The restriction of the singular boundary to the small chains. -/
def smallCxD (U : ι → Set X) (n : ℕ) :
    ModuleCat.of ℝ (smallChains U (n + 1)) ⟶ ModuleCat.of ℝ (smallChains U n) :=
  ModuleCat.ofHom (LinearMap.restrict ((singChains X).d (n + 1) n).hom
    (fun _ hx => smallChains_d U n hx))

/-- The subcomplex of `U`-small singular chains. -/
def smallCx (U : ι → Set X) : ChainComplex (ModuleCat.{0} ℝ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of ℝ (smallChains U n)) (smallCxD U)
    (fun n => by
      ext x
      change ((singChains X).d (n + 1) n).hom
        (((singChains X).d (n + 2) (n + 1)).hom (x : (singChains X).X (n + 2))) = 0
      have h := congrArg
        (fun (g : (singChains X).X (n + 2) ⟶ (singChains X).X n) =>
          g.hom (x : (singChains X).X (n + 2)))
        (HomologicalComplex.d_comp_d (singChains X) (n + 2) (n + 1) n)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] using h)

lemma smallCx_d_eq (U : ι → Set X) (n : ℕ) : (smallCx U).d (n + 1) n = smallCxD U n :=
  ChainComplex.of_d (fun n => ModuleCat.of ℝ (smallChains U n)) (smallCxD U) n

/-- The inclusion of the complex of small chains into the singular chain
complex. -/
def smallInc (U : ι → Set X) : smallCx U ⟶ singChains X where
  f n := ModuleCat.ofHom (smallChains U n).subtype
  comm' i j hij := by
    obtain ⟨rfl⟩ : j + 1 = i := hij
    rw [smallCx_d_eq]
    ext x
    rfl

lemma smallInc_injective (U : ι → Set X) (n : ℕ) :
    Function.Injective ((smallInc U).f n).hom := Subtype.val_injective

lemma smallInc_mem (U : ι → Set X) (n : ℕ) (x : (smallCx U).X n) :
    ((smallInc U).f n).hom x ∈ smallChains U n := x.2

lemma smallInc_d_apply (U : ι → Set X) (n j : ℕ) (x : (smallCx U).X n) :
    ((smallInc U).f j).hom (((smallCx U).d n j).hom x) =
      ((singChains X).d n j).hom (((smallInc U).f n).hom x) := by
  have h := congrArg (fun (g : (smallCx U).X n ⟶ (singChains X).X j) => g.hom x)
    ((smallInc U).comm n j)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h.symm

lemma smallCx_d_eq_zero (U : ι → Set X) (n j : ℕ) (x : (smallCx U).X n)
    (h : ((singChains X).d n j).hom (((smallInc U).f n).hom x) = 0) :
    ((smallCx U).d n j).hom x = 0 := by
  apply smallInc_injective U j
  rw [smallInc_d_apply, h, map_zero]

/-! ### Homology classes vanish exactly on boundaries -/

/-- In a chain complex of modules, a cycle whose homology class vanishes is a
boundary at the level of cycles. -/
lemma exists_toCycles_of_homologyπ_eq_zero (K : ChainComplex (ModuleCat.{0} ℝ) ℕ) (n : ℕ)
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
    Epi (HomologicalComplex.homologyMap (smallInc U) n) := by
  rw [ModuleCat.epi_iff_surjective]
  intro h
  obtain ⟨c, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((singChains X).homologyπ n)).1 inferInstance h
  have hz : ∀ j, ((singChains X).d n j).hom (((singChains X).iCycles n).hom c) = 0 := by
    intro j
    have h2 := congrArg (fun (g : (singChains X).cycles n ⟶ (singChains X).X j) => g.hom c)
      ((singChains X).iCycles_d n j)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h2
  obtain ⟨z', hz'small, hz'cyc, w, hw⟩ :=
    exists_small_cycle_homologous U hU hcov (((singChains X).iCycles n).hom c) hz
  set xs : (smallCx U).X n := (⟨z', hz'small⟩ : smallChains U n) with hxs
  have hxsval : ((smallInc U).f n).hom xs = z' := rfl
  have hcyc : ((smallCx U).d n ((ComplexShape.down ℕ).next n)).hom xs = 0 := by
    refine smallCx_d_eq_zero U n _ xs ?_
    rw [hxsval]
    exact hz'cyc _
  set c' := HomologicalComplex.cyclesMk (smallCx U) xs ((ComplexShape.down ℕ).next n) rfl hcyc
    with hc'
  have hic' : ((smallCx U).iCycles n).hom c' = xs :=
    HomologicalComplex.i_cyclesMk (smallCx U) xs _ rfl hcyc
  refine ⟨((smallCx U).homologyπ n).hom c', ?_⟩
  have hnat := congrArg (fun (g : (smallCx U).cycles n ⟶ (singChains X).homology n) => g.hom c')
    (HomologicalComplex.homologyπ_naturality (smallInc U) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  rw [hnat]
  have hdiff : c - (HomologicalComplex.cyclesMap (smallInc U) n).hom c' =
      ((singChains X).toCycles (n + 1) n).hom w := by
    apply (ModuleCat.mono_iff_injective ((singChains X).iCycles n)).1 inferInstance
    have h1 := congrArg (fun (g : (smallCx U).cycles n ⟶ (singChains X).X n) => g.hom c')
      (HomologicalComplex.cyclesMap_i (smallInc U) n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    have h2 := congrArg (fun (g : (singChains X).X (n + 1) ⟶ (singChains X).X n) => g.hom w)
      ((singChains X).toCycles_i (n + 1) n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    rw [map_sub, h1, h2, hic', hxsval, ← hw]
  have hzero : ((singChains X).homologyπ n).hom
      (((singChains X).toCycles (n + 1) n).hom w) = 0 := by
    have h3 := congrArg
      (fun (g : (singChains X).X (n + 1) ⟶ (singChains X).homology n) => g.hom w)
      ((singChains X).toCycles_comp_homologyπ (n + 1) n)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h3
  have hfin := congrArg (fun y => ((singChains X).homologyπ n).hom y) hdiff
  simp only [map_sub, hzero] at hfin
  exact (sub_eq_zero.1 hfin).symm

/-- Injectivity on homology: a small cycle bounding in the singular complex
bounds a small chain. -/
theorem mono_homologyMap_smallInc (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    Mono (HomologicalComplex.homologyMap (smallInc U) n) := by
  rw [ModuleCat.mono_iff_injective]
  refine (injective_iff_map_eq_zero _).2 fun h hh => ?_
  obtain ⟨c', rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((smallCx U).homologyπ n)).1 inferInstance h
  -- the class of the image cycle vanishes
  have hnat := congrArg (fun (g : (smallCx U).cycles n ⟶ (singChains X).homology n) => g.hom c')
    (HomologicalComplex.homologyπ_naturality (smallInc U) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  rw [hnat] at hh
  obtain ⟨w, hwc⟩ := exists_toCycles_of_homologyπ_eq_zero (singChains X) n
    ((HomologicalComplex.cyclesMap (smallInc U) n).hom c') hh
  -- the underlying small cycle
  set zs : (smallCx U).X n := ((smallCx U).iCycles n).hom c' with hzs
  have himg : ((singChains X).d (n + 1) n).hom w = ((smallInc U).f n).hom zs := by
    have h1 := congrArg (fun (g : (smallCx U).cycles n ⟶ (singChains X).X n) => g.hom c')
      (HomologicalComplex.cyclesMap_i (smallInc U) n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    have h2 := congrArg (fun (g : (singChains X).X (n + 1) ⟶ (singChains X).X n) => g.hom w)
      ((singChains X).toCycles_i (n + 1) n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    rw [← h2, hwc, h1]
  obtain ⟨w', hw'small, hw'⟩ := small_boundary_of_boundary U hU hcov
    (((smallInc U).f n).hom zs) (smallInc_mem U n zs) w himg
  -- lift the bounding chain to the subcomplex
  set ws : (smallCx U).X (n + 1) := (⟨w', hw'small⟩ : smallChains U (n + 1)) with hws
  have hwsval : ((smallInc U).f (n + 1)).hom ws = w' := rfl
  have hdws : ((smallCx U).d (n + 1) n).hom ws = zs := by
    apply smallInc_injective U n
    rw [smallInc_d_apply, hwsval, hw']
  have hcyc : ((smallCx U).toCycles (n + 1) n).hom ws = c' := by
    apply (ModuleCat.mono_iff_injective ((smallCx U).iCycles n)).1 inferInstance
    have h2 := congrArg (fun (g : (smallCx U).X (n + 1) ⟶ (smallCx U).X n) => g.hom ws)
      ((smallCx U).toCycles_i (n + 1) n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    rw [h2, hdws, hzs]
  rw [← hcyc]
  have h3 := congrArg (fun (g : (smallCx U).X (n + 1) ⟶ (smallCx U).homology n) => g.hom ws)
    ((smallCx U).toCycles_comp_homologyπ (n + 1) n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h3

/-- **The small chain theorem.** For an open cover `U` of `X`, the inclusion of
the complex of `U`-small singular chains into the singular chain complex is a
quasi-isomorphism. -/
theorem quasiIso_smallInc (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : ∀ x : X, ∃ i, x ∈ U i) : QuasiIso (smallInc U) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have := mono_homologyMap_smallInc U hU hcov n
  have := epi_homologyMap_smallInc U hU hcov n
  exact isIso_of_mono_of_epi _

end AffChain

end AffineTverberg
