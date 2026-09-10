import AffineTverberg.CoefficientHomology
import AffineTverberg.SimplicialToSingular

set_option linter.style.header false

/-!
# The simplicial-to-singular chain map over an arbitrary field

The affine singular simplices and all geometric realizations are the existing
REAL geometric constructions. Only their chain coefficients are generalized.
This file proves the actual chain comparison, its naturality, injectivity,
augmentation compatibility, and the cone base case over every field.

The general comparison quasi-isomorphism is proved in
`CoefficientComparisonInduction.lean` using small chains and Mayer–Vietoris.
It is applied over `ZMod 2` to the fundamental-cycle argument for a ball.
-/

noncomputable section

open CategoryTheory Limits Simplicial AffineTverberg.Simplicial
open scoped BigOperators

namespace AffineTverberg.Coefficients

variable (𝕜 : Type) [Field 𝕜]
variable {V : Type} [Fintype V] [LinearOrder V]

/-- Mathlib's singular chain complex (with arbitrary field coefficients) of the
barycentric realization of `K`. -/
abbrev singularChains (K : Finset (Finset V)) : ChainComplex (ModuleCat.{0} 𝕜) ℕ :=
  (TopCat.toSSet.obj (barySpace K)).chainComplex (ModuleCat.of 𝕜 𝕜)

omit [LinearOrder V] in
/-- The singular chain complex used here is literally the one produced by
Mathlib's `singularChainComplexFunctor`. -/
theorem singularChains_eq (K : Finset (Finset V)) :
    singularChains 𝕜 K =
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} 𝕜)).obj
        (ModuleCat.of 𝕜 𝕜)).obj (barySpace K) := rfl

/-- The oriented simplicial chain complex of `K`, shifted so that degree `m`
is spanned by the simplices with `m + 1` vertices, i.e. by the geometric
`m`-dimensional simplices. This complex omits the augmentation term, so its
degree-zero homology is ordinary, not reduced. The augmentation is constructed
separately below. In positive degrees it agrees with the augmented complex. -/
def simplicialChains {K : Finset (Finset V)} (hK : FaceClosed K) :
    ChainComplex (ModuleCat.{0} 𝕜) ℕ :=
  ChainComplex.of (fun m ↦ ModuleCat.of 𝕜 ↥(chains 𝕜 K (m + 1)))
    (fun m ↦ ModuleCat.ofHom (chainBoundary 𝕜 hK (m + 1)))
    (fun m ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact Subtype.ext (boundary_boundary_apply (c : Finset V → 𝕜)))

@[simp]
theorem simplicialChains_X {K : Finset (Finset V)} (hK : FaceClosed K) (m : ℕ) :
    (simplicialChains 𝕜 hK).X m = ModuleCat.of 𝕜 ↥(chains 𝕜 K (m + 1)) := rfl

theorem simplicialChains_d {K : Finset (Finset V)} (hK : FaceClosed K) (m : ℕ) :
    (simplicialChains 𝕜 hK).d (m + 1) m = ModuleCat.ofHom (chainBoundary 𝕜 hK (m + 1)) := by
  simp [simplicialChains]

/-! ### The comparison chain map -/

/-- The inclusion of the summand of the singular chains corresponding to the
affine simplex of `s`, and zero if `s` is not a simplex of `K` of the right
cardinality. -/
def iotaAffine (K : Finset (Finset V)) (s : Finset V) (m : ℕ) :
    ModuleCat.of 𝕜 𝕜 ⟶ (singularChains 𝕜 K).X m :=
  if h : s ∈ K ∧ s.card = m + 1 then
    (TopCat.toSSet.obj (barySpace K)).ιChainComplex (affineSimplex h.1 h.2)
  else 0

theorem iotaAffine_of_mem {K : Finset (Finset V)} {s : Finset V} {m : ℕ}
    (hs : s ∈ K) (hc : s.card = m + 1) :
    iotaAffine 𝕜 K s m =
      (TopCat.toSSet.obj (barySpace K)).ιChainComplex (affineSimplex hs hc) := by
  rw [iotaAffine, dite_eq_left_of_eq_true (eq_true (⟨hs, hc⟩ : s ∈ K ∧ s.card = m + 1))]

theorem iotaAffine_of_not {K : Finset (Finset V)} {s : Finset V} {m : ℕ}
    (h : ¬ (s ∈ K ∧ s.card = m + 1)) : iotaAffine 𝕜 K s m = 0 := by
  rw [iotaAffine, dite_eq_right_of_eq_false (eq_false h)]

/-- The comparison map on chains, as a linear map defined on all coefficient
functions. -/
def comparisonAux (K : Finset (Finset V)) (m : ℕ) :
    (Finset V → 𝕜) →ₗ[𝕜] (singularChains 𝕜 K).X m :=
  ∑ s : Finset V, (iotaAffine 𝕜 K s m).hom ∘ₗ (LinearMap.proj s)

theorem comparisonAux_apply (K : Finset (Finset V)) (m : ℕ) (c : Finset V → 𝕜) :
    comparisonAux 𝕜 K m c = ∑ s : Finset V, (iotaAffine 𝕜 K s m).hom (c s) := by
  simp [comparisonAux]

/-- The comparison morphism in degree `m`: an oriented simplicial chain is sent
to the corresponding combination of affine singular simplices. -/
def comparisonHom (K : Finset (Finset V)) (m : ℕ) :
    ModuleCat.of 𝕜 ↥(chains 𝕜 K (m + 1)) ⟶ (singularChains 𝕜 K).X m :=
  ModuleCat.ofHom (comparisonAux 𝕜 K m ∘ₗ (chains 𝕜 K (m + 1)).subtype)

theorem comparisonHom_apply (K : Finset (Finset V)) (m : ℕ) (c : ↥(chains 𝕜 K (m + 1))) :
    (comparisonHom 𝕜 K m).hom c = ∑ s : Finset V, (iotaAffine 𝕜 K s m).hom ((c : Finset V → 𝕜) s) :=
  comparisonAux_apply 𝕜 K m _

/-- **The oriented boundary of a single simplex maps to the alternating
singular boundary of its affine simplex.** -/
theorem iotaAffine_comp_d {K : Finset (Finset V)} (hK : FaceClosed K) {s : Finset V} {m : ℕ}
    (hs : s ∈ K) (hc : s.card = m + 2) :
    iotaAffine 𝕜 K s (m + 1) ≫ (singularChains 𝕜 K).d (m + 1) m =
      ∑ v ∈ s, (orientedSign 𝕜 (s.erase v) v) • iotaAffine 𝕜 K (s.erase v) m := by
  classical
  rw [iotaAffine_of_mem 𝕜 hs hc, SSet.ιChainComplex_d]
  refine Finset.sum_bij (fun (i : Fin (m + 2)) _ ↦ s.orderEmbOfFin hc i)
    (fun i _ ↦ s.orderEmbOfFin_mem hc i)
    (fun i _ j _ h ↦ (s.orderEmbOfFin hc).injective h) (fun v hv ↦ ?_) (fun i _ ↦ ?_)
  · have hv' : v ∈ Set.range (s.orderEmbOfFin hc) := by
      rw [s.range_orderEmbOfFin hc]; exact hv
    obtain ⟨i, hi⟩ := hv'
    exact ⟨i, Finset.mem_univ i, hi⟩
  set v := s.orderEmbOfFin hc i with hv
  have hvs : v ∈ s := s.orderEmbOfFin_mem hc i
  have hs' : s.erase v ∈ K := hK s hs _ (Finset.erase_subset _ _)
  have h' : (s.erase v).card = m + 1 := by
    rw [Finset.card_erase_of_mem hvs, hc]
    omega
  rw [delta_affineSimplex hs hc i hs' h', iotaAffine_of_mem 𝕜 hs' h',
    orientedSign_erase_orderEmbOfFin 𝕜 s hc i, ← Int.cast_smul_eq_zsmul 𝕜 ((-1) ^ i.val)]
  push_cast
  rfl

/-- **The comparison map is a chain map**: it intertwines the oriented
simplicial boundary with the alternating singular differential. -/
theorem comparison_comm {K : Finset (Finset V)} (hK : FaceClosed K) (m : ℕ) :
    comparisonHom 𝕜 K (m + 1) ≫ (singularChains 𝕜 K).d (m + 1) m =
      (simplicialChains 𝕜 hK).d (m + 1) m ≫ comparisonHom 𝕜 K m := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change ((singularChains 𝕜 K).d (m + 1) m).hom ((comparisonHom 𝕜 K (m + 1)).hom c) =
    (comparisonHom 𝕜 K m).hom (((simplicialChains 𝕜 hK).d (m + 1) m).hom c)
  set F : Finset V → V → ((singularChains 𝕜 K).X m) := fun s v ↦
    orientedSign 𝕜 (s.erase v) v • (iotaAffine 𝕜 K (s.erase v) m).hom ((c : Finset V → 𝕜) s)
    with hFdef
  have hLHS : ((singularChains 𝕜 K).d (m + 1) m).hom ((comparisonHom 𝕜 K (m + 1)).hom c)
      = ∑ s : Finset V, ∑ v ∈ s, F s v := by
    rw [comparisonHom_apply 𝕜, map_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    by_cases hcs : (c : Finset V → 𝕜) s = 0
    · simp [hFdef, hcs]
    · obtain ⟨hsK, hscard⟩ := c.2 s hcs
      have hmor := iotaAffine_comp_d 𝕜 hK hsK (m := m) hscard
      have := congrArg (fun (g : ModuleCat.of 𝕜 𝕜 ⟶ (singularChains 𝕜 K).X m) ↦
        g.hom ((c : Finset V → 𝕜) s)) hmor
      simpa [hFdef] using this
  have hRHS : (comparisonHom 𝕜 K m).hom (((simplicialChains 𝕜 hK).d (m + 1) m).hom c)
      = ∑ f : Finset V, ∑ v ∈ fᶜ, F (insert v f) v := by
    rw [simplicialChains_d 𝕜]
    change (comparisonHom 𝕜 K m).hom (chainBoundary 𝕜 hK (m + 1) c) = _
    rw [comparisonHom_apply 𝕜]
    refine Finset.sum_congr rfl fun f _ ↦ ?_
    rw [chainBoundary_coe, boundary_apply, map_sum]
    refine Finset.sum_congr rfl fun v hv ↦ ?_
    have hvf : v ∉ f := by simpa using hv
    have hins : (insert v f).erase v = f := Finset.erase_insert hvf
    rw [hFdef]
    simp only [hins]
    rw [← smul_eq_mul, map_smul]
  rw [hLHS, hRHS, Finset.sum_sigma', Finset.sum_sigma']
  refine (Finset.sum_nbij' (i := fun p ↦ (⟨insert p.2 p.1, p.2⟩ : Σ _ : Finset V, V))
    (j := fun q ↦ (⟨q.1.erase q.2, q.2⟩ : Σ _ : Finset V, V)) ?_ ?_ ?_ ?_ ?_).symm
  · rintro ⟨f, v⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_compl, true_and] at hp ⊢
    exact Finset.mem_insert_self v f
  · rintro ⟨s, v⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_compl, true_and] at hq ⊢
    exact Finset.notMem_erase v s
  · rintro ⟨f, v⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_compl, true_and] at hp
    simp [Finset.erase_insert hp]
  · rintro ⟨s, v⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at hq
    simp [Finset.insert_erase hq]
  · rintro ⟨f, v⟩ _
    rfl

/-- The comparison chain map from the oriented simplicial chain complex of `K`
to Mathlib's singular chain complex of the barycentric realization of `K`. -/
def comparisonChainMap {K : Finset (Finset V)} (hK : FaceClosed K) :
    simplicialChains 𝕜 hK ⟶ singularChains 𝕜 K :=
  ChainComplex.ofHom (fun m ↦ comparisonHom 𝕜 K m) (fun m ↦ comparison_comm 𝕜 hK m)

@[simp]
theorem comparisonChainMap_f {K : Finset (Finset V)} (hK : FaceClosed K) (m : ℕ) :
    (comparisonChainMap 𝕜 hK).f m = comparisonHom 𝕜 K m := rfl

/-! ### Identification of the shifted complex with reduced simplicial homology -/

/-- In every positive degree, exactness of the shifted simplicial chain complex
is exactly the reduced acyclicity predicate of `SimplicialHomology`, in the
corresponding augmented degree. -/
theorem ker_chainBoundary_le_range_iff {K : Finset (Finset V)} (hK : FaceClosed K) (m : ℕ) :
    (LinearMap.ker (chainBoundary 𝕜 hK (m + 1)) ≤
      LinearMap.range (chainBoundary 𝕜 hK (m + 2))) ↔ IsReducedAcyclicAt 𝕜 K (m + 2) := by
  constructor
  · intro h c hc
    obtain ⟨hcmem, hcbd⟩ := hc
    obtain ⟨b, hb⟩ := h (show (⟨c, hcmem⟩ : ↥(chains 𝕜 K (m + 2))) ∈
      LinearMap.ker (chainBoundary 𝕜 hK (m + 1)) from Subtype.ext hcbd)
    exact ⟨b, b.2, congrArg Subtype.val hb⟩
  · intro h c hc
    have hc0 : boundary 𝕜 V (c : Finset V → 𝕜) = 0 := congrArg Subtype.val hc
    obtain ⟨b, hb, hbc⟩ := h (show (c : Finset V → 𝕜) ∈ cycles 𝕜 K (m + 2) from ⟨c.2, hc0⟩)
    exact ⟨⟨b, hb⟩, Subtype.ext hbc⟩

theorem simplicialChains_exactAt_iff {K : Finset (Finset V)} (hK : FaceClosed K) (m : ℕ) :
    (simplicialChains 𝕜 hK).ExactAt (m + 1) ↔ IsReducedAcyclicAt 𝕜 K (m + 2) := by
  rw [HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_ker_sub_range]
  have hg : (HomologicalComplex.sc' (simplicialChains 𝕜 hK) (m + 2) (m + 1) m).g
      = ModuleCat.ofHom (chainBoundary 𝕜 hK (m + 1)) := simplicialChains_d 𝕜 hK m
  have hf : (HomologicalComplex.sc' (simplicialChains 𝕜 hK) (m + 2) (m + 1) m).f
      = ModuleCat.ofHom (chainBoundary 𝕜 hK (m + 2)) := simplicialChains_d 𝕜 hK (m + 1)
  rw [hf, hg]
  exact ker_chainBoundary_le_range_iff 𝕜 hK m

/-- Vanishing of the reduced simplicial homology of `K` in augmented degree
`m + 2` makes the shifted chain complex have zero homology in degree `m + 1`. -/
theorem isZero_simplicialChains_homology {K : Finset (Finset V)} (hK : FaceClosed K) (m : ℕ)
    (h : IsReducedAcyclicAt 𝕜 K (m + 2)) :
    Limits.IsZero ((simplicialChains 𝕜 hK).homology (m + 1)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    ((simplicialChains_exactAt_iff 𝕜 hK m).mpr h)

/-! ### The induced map on homology -/

/-- The map induced by the comparison chain map on homology: from the (shifted)
simplicial homology of `K` to Mathlib's singular homology of the barycentric
realization of `K`. -/
def comparisonHomologyMap {K : Finset (Finset V)} (hK : FaceClosed K) (m : ℕ) :
    (simplicialChains 𝕜 hK).homology m ⟶ (singularHomology 𝕜 m).obj (barySpace K) :=
  HomologicalComplex.homologyMap (comparisonChainMap 𝕜 hK) m

/-- Ordinary singular homology of the realization of a nonempty cone vanishes
in every positive degree. -/
theorem isZero_singularHomology_of_cone {K : Finset (Finset V)} {a : V}
    (hcone : IsConeWithApex K a) (hKne : K.Nonempty) (m : ℕ) (hm : m ≠ 0) :
    Limits.IsZero ((singularHomology 𝕜 m).obj (barySpace K)) := by
  have : ContractibleSpace ↥(barycentricCarrier K) :=
    contractibleSpace_barycentricCarrier_of_cone hcone hKne
  have hsub : Subsingleton ((singularHomology 𝕜 m).obj
      (TopCat.of ↥(barycentricCarrier K))) :=
    singularHomology_subsingleton_of_contractible 𝕜 _ m hm
  change Limits.IsZero ((singularHomology 𝕜 m).obj (TopCat.of ↥(barycentricCarrier K)))
  exact ModuleCat.isZero_of_subsingleton _

/-- **The comparison map is an isomorphism in all positive degrees for a
cone.**  Both sides vanish: the simplicial side by the cone homotopy, the
singular side by contractibility of the star-shaped realization. -/
theorem isIso_comparisonHomologyMap_of_cone {K : Finset (Finset V)} (hK : FaceClosed K) {a : V}
    (hcone : IsConeWithApex K a) (hKne : K.Nonempty) (m : ℕ) :
    IsIso (comparisonHomologyMap 𝕜 hK (m + 1)) := by
  have h1 : Limits.IsZero ((simplicialChains 𝕜 hK).homology (m + 1)) :=
    isZero_simplicialChains_homology 𝕜 hK m (isReducedAcyclic_of_cone hcone (m + 2))
  have h2 : Limits.IsZero ((singularHomology 𝕜 (m + 1)).obj (barySpace K)) :=
    isZero_singularHomology_of_cone 𝕜 hcone hKne (m + 1) (Nat.succ_ne_zero m)
  exact ⟨⟨0, h1.eq_of_src _ _, h2.eq_of_tgt _ _⟩⟩

/-- The chain map of singular complexes induced by an inclusion of families. -/
def singularChainsMap {K L : Finset (Finset V)} (h : K ⊆ L) :
    singularChains 𝕜 K ⟶ singularChains 𝕜 L :=
  SSet.chainComplexMap (TopCat.toSSet.map (baryInclusion h)) (ModuleCat.of 𝕜 𝕜)

theorem iotaAffine_naturality {K L : Finset (Finset V)} (h : K ⊆ L) {s : Finset V} {m : ℕ}
    (hs : s ∈ K) (hc : s.card = m + 1) :
    iotaAffine 𝕜 K s m ≫ (singularChainsMap 𝕜 h).f m = iotaAffine 𝕜 L s m := by
  rw [iotaAffine_of_mem 𝕜 hs hc, iotaAffine_of_mem 𝕜 (h hs) hc, singularChainsMap,
    SSet.ι_chainComplexMap_f, affineSimplex_naturality h hs hc]

/-- The inclusion of simplicial chain complexes induced by an inclusion of
face-closed families. -/
def simplicialChainsInclusion {K L : Finset (Finset V)} (hK : FaceClosed K) (hL : FaceClosed L)
    (h : K ⊆ L) : simplicialChains 𝕜 hK ⟶ simplicialChains 𝕜 hL :=
  ChainComplex.ofHom (fun m ↦ ModuleCat.ofHom (Submodule.inclusion (chains_mono h (m + 1))))
    (fun m ↦ by
      rw [simplicialChains_d 𝕜, simplicialChains_d 𝕜]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      rfl)

/-- Degreewise naturality of the comparison map. -/
theorem comparisonHom_naturality {K L : Finset (Finset V)} (h : K ⊆ L) (m : ℕ) :
    comparisonHom 𝕜 K m ≫ (singularChainsMap 𝕜 h).f m =
      ModuleCat.ofHom (Submodule.inclusion (chains_mono h (m + 1))) ≫ comparisonHom 𝕜 L m := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change ((singularChainsMap 𝕜 h).f m).hom ((comparisonHom 𝕜 K m).hom c) =
    (comparisonHom 𝕜 L m).hom (Submodule.inclusion (chains_mono h (m + 1)) c)
  rw [comparisonHom_apply 𝕜 K m c, comparisonHom_apply 𝕜 L m, map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  by_cases hcs : (c : Finset V → 𝕜) s = 0
  · simp [hcs]
  · obtain ⟨hsK, hscard⟩ := c.2 s hcs
    exact congrArg (fun (g : ModuleCat.of 𝕜 𝕜 ⟶ (singularChains 𝕜 L).X m) ↦
      g.hom ((c : Finset V → 𝕜) s)) (iotaAffine_naturality 𝕜 h hsK hscard)

/-- **Naturality of the comparison chain map** in the face-closed family. -/
theorem comparisonChainMap_naturality {K L : Finset (Finset V)} (hK : FaceClosed K)
    (hL : FaceClosed L) (h : K ⊆ L) :
    comparisonChainMap 𝕜 hK ≫ singularChainsMap 𝕜 h =
      simplicialChainsInclusion 𝕜 hK hL h ≫ comparisonChainMap 𝕜 hL := by
  apply HomologicalComplex.hom_ext
  intro m
  exact comparisonHom_naturality 𝕜 h m

/-- Naturality of the induced map on homology. -/
theorem comparisonHomologyMap_naturality {K L : Finset (Finset V)} (hK : FaceClosed K)
    (hL : FaceClosed L) (h : K ⊆ L) (m : ℕ) :
    HomologicalComplex.homologyMap (comparisonChainMap 𝕜 hK) m ≫
        HomologicalComplex.homologyMap (singularChainsMap 𝕜 h) m =
      HomologicalComplex.homologyMap (simplicialChainsInclusion 𝕜 hK hL h) m ≫
        HomologicalComplex.homologyMap (comparisonChainMap 𝕜 hL) m := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    comparisonChainMap_naturality 𝕜 hK hL h]

/-! ### The augmentation endpoint

The augmentation of the augmented simplicial chain complex (the boundary map
out of the vertex degree) corresponds to the singular augmentation sending
every singular `0`-simplex to `1`; this is the chain-level statement, proved
for the actual coproduct description of Mathlib's singular `0`-chains. -/

/-- The chain-level singular augmentation: every singular `0`-simplex is sent
to `1`. -/
def singularAugmentationChain (K : Finset (Finset V)) :
    (singularChains 𝕜 K).X 0 ⟶ ModuleCat.of 𝕜 𝕜 :=
  Limits.Sigma.desc (fun _ ↦ 𝟙 (ModuleCat.of 𝕜 𝕜))

omit [LinearOrder V] in
@[reassoc (attr := simp)]
theorem ιChainComplex_singularAugmentationChain (K : Finset (Finset V))
    (x : (TopCat.toSSet.obj (barySpace K)) _⦋0⦌) :
    (TopCat.toSSet.obj (barySpace K)).ιChainComplex (R := ModuleCat.of 𝕜 𝕜) x ≫
      singularAugmentationChain 𝕜 K = 𝟙 (ModuleCat.of 𝕜 𝕜) :=
  Limits.Sigma.ι_desc _ _

omit [LinearOrder V] in
/-- The singular augmentation kills the boundaries of singular `1`-chains. -/
theorem d_singularAugmentationChain (K : Finset (Finset V)) :
    (singularChains 𝕜 K).d 1 0 ≫ singularAugmentationChain 𝕜 K = 0 := by
  apply SSet.chainComplex_hom_ext
  intro x
  rw [SSet.ιChainComplex_d_assoc]
  simp [Fin.sum_univ_two]

/-- **The augmentation endpoint of the comparison.**  Composing the comparison
map in degree `0` with the singular augmentation gives exactly the simplicial
augmentation `c ↦ ∑ v, c {v}` of `SimplicialHomology`. -/
theorem comparisonHom_singularAugmentationChain (K : Finset (Finset V)) :
    comparisonHom 𝕜 K 0 ≫ singularAugmentationChain 𝕜 K =
      ModuleCat.ofHom ((augmentation 𝕜 V).comp (chains 𝕜 K 1).subtype) := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change (singularAugmentationChain 𝕜 K).hom ((comparisonHom 𝕜 K 0).hom c) =
    augmentation 𝕜 V (c : Finset V → 𝕜)
  rw [comparisonHom_apply 𝕜, map_sum, augmentation_apply]
  have hterm : ∀ s : Finset V, (singularAugmentationChain 𝕜 K).hom
      ((iotaAffine 𝕜 K s 0).hom ((c : Finset V → 𝕜) s))
      = if s ∈ K ∧ s.card = 1 then (c : Finset V → 𝕜) s else 0 := by
    intro s
    by_cases hs : s ∈ K ∧ s.card = 1
    · rw [iotaAffine_of_mem 𝕜 hs.1 hs.2]
      simp only [hs, and_self, ite_true]
      exact congrArg (fun (g : ModuleCat.of 𝕜 𝕜 ⟶ ModuleCat.of 𝕜 𝕜) ↦
        g.hom ((c : Finset V → 𝕜) s))
        (ιChainComplex_singularAugmentationChain 𝕜 K (affineSimplex hs.1 hs.2))
    · rw [iotaAffine_of_not 𝕜 hs]
      simp only [hs, ite_false]
      simp
  have hall : ∀ s : Finset V, (if s ∈ K ∧ s.card = 1 then (c : Finset V → 𝕜) s else 0)
      = (c : Finset V → 𝕜) s := by
    intro s
    by_cases hs : s ∈ K ∧ s.card = 1
    · simp only [hs, and_self, ite_true]
    · simp only [hs, ite_false]
      by_contra hne
      exact hs (c.2 s (Ne.symm hne))
  rw [Finset.sum_congr rfl (fun s _ ↦ (hterm s).trans (hall s))]
  have himg : (Finset.univ.image (fun v : V ↦ ({v} : Finset V))) ⊆ Finset.univ :=
    Finset.subset_univ _
  rw [← Finset.sum_subset himg (fun s _ hs ↦ ?_)]
  · exact Finset.sum_image (fun a _ b _ hab ↦ by simpa using hab)
  · by_contra hne
    obtain ⟨_, hcard⟩ := c.2 s hne
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
    exact hs (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩)

/-! ### Degree zero: the comparison against the two augmentations -/

/-- The map induced on `H₀` by an augmentation of a chain complex, i.e. by a
morphism out of the degree-zero chains killing the boundaries. -/
def augHomology (C : ChainComplex (ModuleCat.{0} 𝕜) ℕ) (ε : C.X 0 ⟶ ModuleCat.of 𝕜 𝕜)
    (hε : C.d 1 0 ≫ ε = 0) : C.homology 0 ⟶ ModuleCat.of 𝕜 𝕜 :=
  (C.isoHomologyι₀).hom ≫ C.descOpcycles ε 1 (by simp) hε

theorem homologyπ_augHomology (C : ChainComplex (ModuleCat.{0} 𝕜) ℕ)
    (ε : C.X 0 ⟶ ModuleCat.of 𝕜 𝕜) (hε : C.d 1 0 ≫ ε = 0) :
    C.homologyπ 0 ≫ augHomology 𝕜 C ε hε = C.iCycles 0 ≫ C.pOpcycles 0 ≫
      C.descOpcycles ε 1 (by simp) hε := by
  rw [augHomology, ← Category.assoc, ← Category.assoc]
  congr 1
  simp

/-- Naturality of the induced map on `H₀` with respect to augmented chain
maps. -/
theorem homologyMap_augHomology {C D : ChainComplex (ModuleCat.{0} 𝕜) ℕ} (φ : C ⟶ D)
    (εC : C.X 0 ⟶ ModuleCat.of 𝕜 𝕜) (εD : D.X 0 ⟶ ModuleCat.of 𝕜 𝕜)
    (hC : C.d 1 0 ≫ εC = 0) (hD : D.d 1 0 ≫ εD = 0) (hφ : φ.f 0 ≫ εD = εC) :
    HomologicalComplex.homologyMap φ 0 ≫ augHomology 𝕜 D εD hD = augHomology 𝕜 C εC hC := by
  rw [augHomology, augHomology, ← Category.assoc]
  have h1 : HomologicalComplex.homologyMap φ 0 ≫ (D.isoHomologyι₀).hom =
      (C.isoHomologyι₀).hom ≫ HomologicalComplex.opcyclesMap φ 0 := by
    simp
  rw [h1, Category.assoc]
  congr 1
  rw [← cancel_epi (C.pOpcycles 0), HomologicalComplex.p_opcyclesMap_assoc,
    HomologicalComplex.p_descOpcycles, HomologicalComplex.p_descOpcycles, hφ]

/-- The simplicial augmentation as an augmentation of the shifted chain
complex. -/
def simplicialAug {K : Finset (Finset V)} (hK : FaceClosed K) :
    (simplicialChains 𝕜 hK).X 0 ⟶ ModuleCat.of 𝕜 𝕜 :=
  ModuleCat.ofHom ((augmentation 𝕜 V).comp (chains 𝕜 K 1).subtype)

theorem simplicialAug_apply {K : Finset (Finset V)} (hK : FaceClosed K)
    (c : ↥(chains 𝕜 K 1)) :
    (simplicialAug 𝕜 hK).hom c = augmentation 𝕜 V (c : Finset V → 𝕜) := rfl

theorem simplicialChains_d_apply {K : Finset (Finset V)} (hK : FaceClosed K) (m : ℕ)
    (c : ↥(chains 𝕜 K (m + 2))) :
    ((((simplicialChains 𝕜 hK).d (m + 1) m).hom c : ↥(chains 𝕜 K (m + 1))).val) =
      boundary 𝕜 V (c : Finset V → 𝕜) := by
  rw [simplicialChains_d 𝕜]
  rfl

theorem d_simplicialAug {K : Finset (Finset V)} (hK : FaceClosed K) :
    (simplicialChains 𝕜 hK).d 1 0 ≫ simplicialAug 𝕜 hK = 0 := by
  have key : ∀ c : ↥(chains 𝕜 K 2),
      augmentation 𝕜 V (boundary 𝕜 V (c : Finset V → 𝕜)) = 0 := by
    intro c
    rw [← boundary_apply_empty, boundary_boundary_apply]
    rfl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact key (c : ↥(chains 𝕜 K 2))

/-- Compatibility of the comparison chain map with the two augmentations. -/
theorem comparisonChainMap_f_zero_singularAugmentationChain {K : Finset (Finset V)}
    (hK : FaceClosed K) :
    (comparisonChainMap 𝕜 hK).f 0 ≫ singularAugmentationChain 𝕜 K = simplicialAug 𝕜 hK :=
  comparisonHom_singularAugmentationChain 𝕜 K

/-- **The comparison map in degree `0` is compatible with the augmentations**,
at the level of homology. -/
theorem comparisonHomologyMap_zero_augHomology {K : Finset (Finset V)} (hK : FaceClosed K) :
    HomologicalComplex.homologyMap (comparisonChainMap 𝕜 hK) 0 ≫
        augHomology 𝕜 (singularChains 𝕜 K) (singularAugmentationChain 𝕜 K)
          (d_singularAugmentationChain 𝕜 K) =
      augHomology 𝕜 (simplicialChains 𝕜 hK) (simplicialAug 𝕜 hK) (d_simplicialAug 𝕜 hK) :=
  homologyMap_augHomology 𝕜 _ _ _ (d_simplicialAug 𝕜 hK) (d_singularAugmentationChain 𝕜 K)
    (comparisonChainMap_f_zero_singularAugmentationChain 𝕜 hK)

/-- For a nonempty cone the simplicial augmentation induces an isomorphism on
`H₀`: this is reduced acyclicity in the vertex degree together with the
existence of a vertex. -/
theorem isIso_augHomology_simplicial {K : Finset (Finset V)} (hK : FaceClosed K) {a : V}
    (hcone : IsConeWithApex K a) (hKne : K.Nonempty) :
    IsIso (augHomology 𝕜 (simplicialChains 𝕜 hK) (simplicialAug 𝕜 hK) (d_simplicialAug 𝕜 hK)) := by
  classical
  have hempty : (∅ : Finset V) ∈ K := by
    obtain ⟨s, hs⟩ := hKne
    exact hK s hs ∅ (Finset.empty_subset s)
  have hvertex : ({a} : Finset V) ∈ K := by
    simpa using hcone ∅ hempty
  set D := simplicialChains 𝕜 hK with hD
  set desc := D.descOpcycles (simplicialAug 𝕜 hK) 1 (by simp) (d_simplicialAug 𝕜 hK) with hdescdef
  have hpd : D.pOpcycles 0 ≫ desc = simplicialAug 𝕜 hK :=
    D.p_descOpcycles (simplicialAug 𝕜 hK) 1 (by simp) (d_simplicialAug 𝕜 hK)
  have hpd' : ∀ c : ↥(chains 𝕜 K 1),
      desc.hom ((D.pOpcycles 0).hom c) = augmentation 𝕜 V (c : Finset V → 𝕜) :=
    fun c ↦ congrArg (fun (g : D.X 0 ⟶ ModuleCat.of 𝕜 𝕜) ↦ g.hom c) hpd
  have hsurj_p : ∀ z, ∃ c : ↥(chains 𝕜 K 1), (D.pOpcycles 0).hom c = z := by
    intro z
    obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective (D.pOpcycles 0)).mp inferInstance z
    exact ⟨(c : ↥(chains 𝕜 K 1)), hc⟩
  have hiso : IsIso desc := by
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨c, rfl⟩ := hsurj_p z
      have hcz : augmentation 𝕜 V (c : Finset V → 𝕜) = 0 := (hpd' c).symm.trans hz
      have hcycle : ((c : Finset V → 𝕜)) ∈ cycles 𝕜 K 1 :=
        ⟨c.2, (boundary_eq_zero_iff_augmentation_of_mem_chains_one c.2).mpr hcz⟩
      obtain ⟨b, hb, hbc⟩ := isReducedAcyclic_of_cone hcone 1 hcycle
      have hbeq : ((D.d 1 0).hom (⟨b, hb⟩ : ↥(chains 𝕜 K 2)) : ↥(chains 𝕜 K 1)) = c :=
        Subtype.ext (by rw [simplicialChains_d_apply 𝕜 hK 0 ⟨b, hb⟩]; exact hbc)
      have hzero : (D.pOpcycles 0).hom ((D.d 1 0).hom (⟨b, hb⟩ : ↥(chains 𝕜 K 2))) = 0 :=
        congrArg (fun (g : D.X 1 ⟶ D.opcycles 0) ↦ g.hom (⟨b, hb⟩ : ↥(chains 𝕜 K 2)))
          (D.d_pOpcycles 1 0)
      rw [← hbeq]
      exact hzero
    · intro r
      have hmem : (fun s ↦ if s = ({a} : Finset V) then r else 0) ∈ chains 𝕜 K 1 := by
        intro s hs
        by_cases hsa : s = {a}
        · exact ⟨hsa ▸ hvertex, by simp [hsa]⟩
        · simp [hsa] at hs
      refine ⟨(D.pOpcycles 0).hom ⟨_, hmem⟩, ?_⟩
      rw [hpd' ⟨_, hmem⟩]
      change ∑ v : V, (if ({v} : Finset V) = {a} then r else 0) = r
      rw [Finset.sum_eq_single a]
      · simp
      · intro v _ hv
        have hva : ({v} : Finset V) ≠ {a} := by simpa using hv
        simp [hva]
      · intro h
        exact absurd (Finset.mem_univ a) h
  rw [augHomology]
  infer_instance

omit [LinearOrder V] in
/-- The chain-level singular augmentation induces exactly Mathlib's
augmentation on degree-zero singular homology. -/
theorem augHomology_singular_eq (K : Finset (Finset V)) :
    augHomology 𝕜 (singularChains 𝕜 K) (singularAugmentationChain 𝕜 K)
        (d_singularAugmentationChain 𝕜 K) =
      (singularAugmentation 𝕜 (barySpace K) :
        (singularChains 𝕜 K).homology 0 ⟶ ModuleCat.of 𝕜 𝕜) := by
  have hlift : ∀ x : (TopCat.toSSet.obj (barySpace K)) _⦋0⦌,
      (TopCat.toSSet.obj (barySpace K)).ιChainComplex (R := ModuleCat.of 𝕜 𝕜) x ≫
          ((singularChains 𝕜 K).cycles₀Iso).inv =
        (singularChains 𝕜 K).liftCycles
          ((TopCat.toSSet.obj (barySpace K)).ιChainComplex x) 0 (by simp) (by simp) := by
    intro x
    rw [← cancel_mono ((singularChains 𝕜 K).iCycles 0)]
    simp
  have h1 : (singularChains 𝕜 K).homologyπ 0 ≫ ((singularChains 𝕜 K).isoHomologyι₀).hom =
      (singularChains 𝕜 K).iCycles 0 ≫ (singularChains 𝕜 K).pOpcycles 0 := by
    simp
  refine (cancel_epi ((singularChains 𝕜 K).homologyπ 0)).mp ?_
  refine (cancel_epi (((singularChains 𝕜 K).cycles₀Iso).inv)).mp ?_
  apply SSet.chainComplex_hom_ext
  intro x
  have hL : (singularChains 𝕜 K).liftCycles
        ((TopCat.toSSet.obj (barySpace K)).ιChainComplex (R := ModuleCat.of 𝕜 𝕜) x) 0
        (by simp) (by simp) ≫ (singularChains 𝕜 K).homologyπ 0 ≫
        augHomology 𝕜 (singularChains 𝕜 K) (singularAugmentationChain 𝕜 K)
          (d_singularAugmentationChain 𝕜 K) = 𝟙 (ModuleCat.of 𝕜 𝕜) := by
    rw [augHomology, ← Category.assoc ((singularChains 𝕜 K).homologyπ 0), h1, Category.assoc,
      ← Category.assoc ((singularChains 𝕜 K).liftCycles _ _ _ _),
      HomologicalComplex.liftCycles_i, HomologicalComplex.p_descOpcycles,
      ιChainComplex_singularAugmentationChain 𝕜]
  have hL' : (TopCat.toSSet.obj (barySpace K)).ιChainComplex (R := ModuleCat.of 𝕜 𝕜) x ≫
      ((singularChains 𝕜 K).cycles₀Iso).inv ≫ (singularChains 𝕜 K).homologyπ 0 ≫
        augHomology 𝕜 (singularChains 𝕜 K) (singularAugmentationChain 𝕜 K)
          (d_singularAugmentationChain 𝕜 K) = 𝟙 (ModuleCat.of 𝕜 𝕜) := by
    rw [← Category.assoc, hlift x]
    exact hL
  have hR : (TopCat.toSSet.obj (barySpace K)).ιChainComplex (R := ModuleCat.of 𝕜 𝕜) x ≫
      ((singularChains 𝕜 K).cycles₀Iso).inv ≫ (singularChains 𝕜 K).homologyπ 0 ≫
        singularAugmentation 𝕜 (barySpace K) = 𝟙 (ModuleCat.of 𝕜 𝕜) := by
    rw [← Category.assoc, hlift x]
    exact SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε _ _ x
  exact hL'.trans hR.symm

/-- **The comparison map is an isomorphism in degree `0` for a nonempty
cone.**  Together with `isIso_comparisonHomologyMap_of_cone 𝕜` this settles the
base case of the comparison in *every* degree. -/
theorem isIso_comparisonHomologyMap_zero_of_cone {K : Finset (Finset V)} (hK : FaceClosed K)
    {a : V} (hcone : IsConeWithApex K a) (hKne : K.Nonempty) :
    IsIso (comparisonHomologyMap 𝕜 hK 0) := by
  have hcontr : ContractibleSpace ↥(barycentricCarrier K) :=
    contractibleSpace_barycentricCarrier_of_cone hcone hKne
  have hsing : IsIso (singularAugmentation 𝕜 (barySpace K)) := by
    have hpc0 : PathConnectedSpace ↥(barycentricCarrier K) := by
      have := hcontr
      infer_instance
    let _hpc : PathConnectedSpace ↥(barySpace K) := hpc0
    infer_instance
  have h1 : IsIso (augHomology 𝕜 (singularChains 𝕜 K) (singularAugmentationChain 𝕜 K)
      (d_singularAugmentationChain 𝕜 K)) := by
    rw [augHomology_singular_eq 𝕜]
    exact hsing
  have h2 : IsIso (augHomology 𝕜 (simplicialChains 𝕜 hK)
      (simplicialAug 𝕜 hK) (d_simplicialAug 𝕜 hK)) :=
    isIso_augHomology_simplicial 𝕜 hK hcone hKne
  have h4 : IsIso (HomologicalComplex.homologyMap (comparisonChainMap 𝕜 hK) 0 ≫
      augHomology 𝕜 (singularChains 𝕜 K) (singularAugmentationChain 𝕜 K)
        (d_singularAugmentationChain 𝕜 K)) := by
    rw [comparisonHomologyMap_zero_augHomology 𝕜 hK]
    exact h2
  exact IsIso.of_isIso_comp_right (HomologicalComplex.homologyMap (comparisonChainMap 𝕜 hK) 0)
    (augHomology 𝕜 (singularChains 𝕜 K) (singularAugmentationChain 𝕜 K)
      (d_singularAugmentationChain 𝕜 K))

/-- **Acyclic-models base case.**  For a nonempty cone the comparison map from
the oriented simplicial homology to Mathlib's singular homology of the
barycentric realization is an isomorphism in *every* ordinary degree, including
degree `0`, with its compatibility with the augmentations proved above. -/
theorem isIso_comparisonHomologyMap_of_cone_all {K : Finset (Finset V)} (hK : FaceClosed K)
    {a : V} (hcone : IsConeWithApex K a) (hKne : K.Nonempty) (m : ℕ) :
    IsIso (comparisonHomologyMap 𝕜 hK m) := by
  cases m with
  | zero => exact isIso_comparisonHomologyMap_zero_of_cone 𝕜 hK hcone hKne
  | succ n => exact isIso_comparisonHomologyMap_of_cone 𝕜 hK hcone hKne n

/-- The full simplex on a nonempty vertex set: the comparison map is an
isomorphism in every degree. -/
theorem isIso_comparisonHomologyMap_powerset {S : Finset V} {a : V} (ha : a ∈ S) (m : ℕ) :
    IsIso (comparisonHomologyMap 𝕜
      (show FaceClosed S.powerset from fun _ hs _ hts ↦
        Finset.mem_powerset.mpr (hts.trans (Finset.mem_powerset.mp hs))) m) :=
  isIso_comparisonHomologyMap_of_cone_all 𝕜 _
    (fun _ hs ↦ Finset.mem_powerset.mpr (Finset.insert_subset ha (Finset.mem_powerset.mp hs)))
    ⟨∅, Finset.empty_mem_powerset S⟩ m

/-- The coefficient functional of a singular simplex on the free module of
singular chains. -/
def singularCoeff (K : Finset (Finset V)) {m : ℕ}
    (x : (TopCat.toSSet.obj (barySpace K)) _⦋m⦌) :
    (singularChains 𝕜 K).X m ⟶ ModuleCat.of 𝕜 𝕜 := by
  classical
  exact Limits.Sigma.desc (fun y ↦ if y = x then 𝟙 (ModuleCat.of 𝕜 𝕜) else 0)

omit [LinearOrder V] in
open Classical in
theorem ιChainComplex_singularCoeff (K : Finset (Finset V)) {m : ℕ}
    (x y : (TopCat.toSSet.obj (barySpace K)) _⦋m⦌) :
    (TopCat.toSSet.obj (barySpace K)).ιChainComplex (R := ModuleCat.of 𝕜 𝕜) y ≫
        singularCoeff 𝕜 K x =
      if y = x then 𝟙 (ModuleCat.of 𝕜 𝕜) else 0 := by
  classical
  simp [singularCoeff, SSet.ιChainComplex]

/-- **The comparison map is injective in every degree.** -/
theorem comparisonHom_injective (K : Finset (Finset V)) (m : ℕ) :
    Function.Injective (comparisonHom 𝕜 K m).hom := by
  classical
  rw [injective_iff_map_eq_zero]
  intro c hc
  apply Subtype.ext
  funext s
  simp only [Submodule.coe_zero, Pi.zero_apply]
  by_contra hcs
  obtain ⟨hsK, hscard⟩ := c.2 s hcs
  set x := affineSimplex hsK hscard with hx
  have hzero := congrArg (fun z ↦ (singularCoeff 𝕜 K x).hom z) hc
  rw [comparisonHom_apply 𝕜] at hzero
  simp only [map_zero, map_sum] at hzero
  have hterm : ∀ t ∈ (Finset.univ : Finset (Finset V)),
      (singularCoeff 𝕜 K x).hom ((iotaAffine 𝕜 K t m).hom ((c : Finset V → 𝕜) t)) =
        if t = s then (c : Finset V → 𝕜) t else 0 := by
    intro t _
    by_cases hmem : t ∈ K ∧ t.card = m + 1
    · have hcomp : iotaAffine 𝕜 K t m ≫ singularCoeff 𝕜 K x =
          if affineSimplex hmem.1 hmem.2 = x then 𝟙 (ModuleCat.of 𝕜 𝕜) else 0 := by
        rw [iotaAffine_of_mem 𝕜 hmem.1 hmem.2, ιChainComplex_singularCoeff]
      have hval := congrArg (fun g : ModuleCat.of 𝕜 𝕜 ⟶ ModuleCat.of 𝕜 𝕜 ↦
        g.hom ((c : Finset V → 𝕜) t)) hcomp
      by_cases hts : t = s
      · subst hts
        have hxx : affineSimplex hmem.1 hmem.2 = x := by
          rw [hx]
        simp only [hxx, ite_true] at hval
        simpa using hval
      · have hne : affineSimplex hmem.1 hmem.2 ≠ x := by
          intro hEq
          exact hts (affineSimplex_inj hmem.1 hmem.2 hsK hscard hEq)
        simp only [hne, ite_false] at hval
        simp only [hts, ite_false]
        simpa using hval
    · have hct : (c : Finset V → 𝕜) t = 0 := by
        by_contra hct
        exact hmem (c.2 t hct)
      have hts : t ≠ s := by
        intro h; exact hmem (h ▸ ⟨hsK, hscard⟩)
      simp [hct, hts]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' Finset.univ s ((c : Finset V → 𝕜))] at hzero
  simp only [Finset.mem_univ, ite_true] at hzero
  exact hcs hzero

instance mono_comparisonHom (K : Finset (Finset V)) (m : ℕ) : Mono (comparisonHom 𝕜 K m) :=
  (ModuleCat.mono_iff_injective _).mpr (comparisonHom_injective 𝕜 K m)

/-- **The oriented simplicial chain complex embeds in the singular chain
complex** of the barycentric realization, via the comparison chain map. -/
instance mono_comparisonChainMap {K : Finset (Finset V)} (hK : FaceClosed K) :
    Mono (comparisonChainMap 𝕜 hK) :=
  HomologicalComplex.mono_of_mono_f _ (fun m ↦ mono_comparisonHom 𝕜 K m)

end AffineTverberg.Coefficients
