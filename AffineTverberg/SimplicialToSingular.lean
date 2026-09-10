import AffineTverberg.SingularHomology
import AffineTverberg.MayerVietoris
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Analysis.Convex.Contractible

set_option linter.style.header false

/-!
# The comparison chain map from simplicial to singular chains

This file constructs the *explicit* comparison map from the finite oriented
simplicial chain complex of a face-closed family `K : Finset (Finset V)` to
Mathlib's singular chain complex of the standard barycentric realization
`barycentricCarrier K`.

The construction is the classical one: an ordered simplex `s ∈ K` with
`s.card = m + 1` is sent to the affine singular `m`-simplex obtained by
spreading the barycentric coordinates of a point of the standard `m`-simplex
over the increasing enumeration of `s`.

Nothing in this file assumes any comparison theorem; the compatibility of the
oriented simplicial boundary with the alternating singular differential is
proved from the actual incidence signs.
-/

noncomputable section

open CategoryTheory Limits Simplicial
open scoped BigOperators

namespace AffineTverberg

namespace Simplicial

variable {V : Type} [Fintype V] [LinearOrder V]

/-! ### Combinatorial lemmas about increasing enumerations -/

omit [Fintype V] in
/-- The number of elements of `s` below its `i`-th element is `i`. -/
theorem card_filter_lt_orderEmbOfFin (s : Finset V) {k : ℕ} (h : s.card = k) (i : Fin k) :
    (s.filter (· < s.orderEmbOfFin h i)).card = i.val := by
  classical
  have hs : s.filter (· < s.orderEmbOfFin h i) =
      (Finset.univ.filter (· < i)).image (s.orderEmbOfFin h) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hxs, hlt⟩
      obtain ⟨j, rfl⟩ : ∃ j, s.orderEmbOfFin h j = x := by
        have hx : x ∈ Set.range (s.orderEmbOfFin h) := by
          rw [s.range_orderEmbOfFin h]; exact hxs
        exact hx
      exact ⟨j, by simpa using (OrderEmbedding.lt_iff_lt _).mp hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨s.orderEmbOfFin_mem h j, (OrderEmbedding.lt_iff_lt _).mpr hj⟩
  rw [hs, Finset.card_image_of_injective _ (s.orderEmbOfFin h).injective]
  have hIio : Finset.univ.filter (fun j : Fin k => j < i) = Finset.Iio i := by
    ext j; simp
  rw [hIio]
  exact Fin.card_Iio i

omit [Fintype V] in
/-- Erasing the `i`-th vertex of `s` corresponds to precomposition with
`Fin.succAbove i` on the increasing enumerations. -/
theorem orderEmbOfFin_erase (s : Finset V) {m : ℕ} (h : s.card = m + 2) (i : Fin (m + 2))
    (h' : (s.erase (s.orderEmbOfFin h i)).card = m + 1) :
    ⇑((s.erase (s.orderEmbOfFin h i)).orderEmbOfFin h') =
      (s.orderEmbOfFin h) ∘ i.succAbove := by
  classical
  symm
  apply Finset.orderEmbOfFin_unique
  · intro j
    refine Finset.mem_erase.mpr ⟨?_, s.orderEmbOfFin_mem h _⟩
    simp only [Function.comp_apply]
    intro hEq
    exact (Fin.succAbove_ne i j) ((s.orderEmbOfFin h).injective hEq)
  · exact (s.orderEmbOfFin h).strictMono.comp (Fin.strictMono_succAbove i)

omit [Fintype V] in
/-- The oriented incidence sign of the `i`-th vertex of `s` is `(-1) ^ i`. -/
theorem orientedSign_erase_orderEmbOfFin (𝕜 : Type*) [Field 𝕜] (s : Finset V) {k : ℕ}
    (h : s.card = k) (i : Fin k) :
    orientedSign 𝕜 (s.erase (s.orderEmbOfFin h i)) (s.orderEmbOfFin h i) = (-1) ^ i.val := by
  classical
  unfold orientedSign
  congr 1
  have : (s.erase (s.orderEmbOfFin h i)).filter (· < s.orderEmbOfFin h i) =
      s.filter (· < s.orderEmbOfFin h i) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    exact ⟨fun hx ↦ ⟨hx.1.2, hx.2⟩, fun hx ↦ ⟨⟨ne_of_lt hx.2, hx.1⟩, hx.2⟩⟩
  rw [this, card_filter_lt_orderEmbOfFin s h i]

/-! ### The affine singular simplex of an ordered face -/

/-- The topological space realizing `K`: the standard barycentric carrier. -/
def barySpace (K : Finset (Finset V)) : TopCat.{0} := TopCat.of ↥(barycentricCarrier K)

/-- Spreading the coordinates of a point of the standard `m`-simplex over the
increasing enumeration of a face `s` lands in the barycentric face of `s`. -/
theorem stdSimplexMap_mem_barycentricFace (s : Finset V) {m : ℕ} (h : s.card = m + 1)
    (t : stdSimplex ℝ (Fin (m + 1))) :
    (stdSimplex.map (s.orderEmbOfFin h) t : V → ℝ) ∈ barycentricFace s := by
  classical
  refine ⟨fun v ↦ (stdSimplex.map (s.orderEmbOfFin h) t).2.1 v,
    (stdSimplex.map (s.orderEmbOfFin h) t).2.2, ?_⟩
  intro v hv
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Finset.mem_filter] at hi
  exact absurd (hi.2 ▸ s.orderEmbOfFin_mem h i) hv

/-- The affine singular simplex attached to a face `s ∈ K` with `s.card = m + 1`,
as a point of `barycentricCarrier K`-valued continuous map on the standard
`m`-simplex. -/
def affineSimplexMap {K : Finset (Finset V)} {s : Finset V} {m : ℕ}
    (hs : s ∈ K) (h : s.card = m + 1) :
    C(stdSimplex ℝ (Fin (m + 1)), ↥(barycentricCarrier K)) where
  toFun t := ⟨(stdSimplex.map (s.orderEmbOfFin h) t : V → ℝ), by
    obtain ⟨h0, h1, h2⟩ := stdSimplexMap_mem_barycentricFace s h t
    exact ⟨h0, h1, s, hs, h2⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp (stdSimplex.continuous_map _))

@[simp]
theorem affineSimplexMap_apply {K : Finset (Finset V)} {s : Finset V} {m : ℕ}
    (hs : s ∈ K) (h : s.card = m + 1) (t : stdSimplex ℝ (Fin (m + 1))) :
    ((affineSimplexMap hs h t : ↥(barycentricCarrier K)) : V → ℝ) =
      (stdSimplex.map (s.orderEmbOfFin h) t : V → ℝ) := rfl

/-- The affine singular simplex of a face, as a simplex of the singular
simplicial set of the barycentric realization. -/
def affineSimplex {K : Finset (Finset V)} {s : Finset V} {m : ℕ}
    (hs : s ∈ K) (h : s.card = m + 1) :
    (TopCat.toSSet.obj (barySpace K)) _⦋m⦌ :=
  ((barySpace K).toSSetObjEquiv (Opposite.op ⦋m⦌)).symm (affineSimplexMap hs h)

theorem toSSetObjEquiv_affineSimplex {K : Finset (Finset V)} {s : Finset V} {m : ℕ}
    (hs : s ∈ K) (h : s.card = m + 1) :
    (barySpace K).toSSetObjEquiv (Opposite.op ⦋m⦌) (affineSimplex hs h) =
      affineSimplexMap hs h :=
  Equiv.apply_symm_apply _ _

/-- Precomposing the affine simplex of `s` with the `i`-th face inclusion of the
standard simplex gives the affine simplex of `s` with its `i`-th vertex erased. -/
theorem affineSimplexMap_succAbove {K : Finset (Finset V)} {s : Finset V} {m : ℕ}
    (hs : s ∈ K) (h : s.card = m + 2) (i : Fin (m + 2))
    (hs' : s.erase (s.orderEmbOfFin h i) ∈ K)
    (h' : (s.erase (s.orderEmbOfFin h i)).card = m + 1)
    (t : stdSimplex ℝ (Fin (m + 1))) :
    affineSimplexMap hs h (stdSimplex.map i.succAbove t) = affineSimplexMap hs' h' t := by
  have h1 : stdSimplex.map (⇑(s.orderEmbOfFin h)) (stdSimplex.map i.succAbove t)
      = stdSimplex.map ((⇑(s.orderEmbOfFin h)) ∘ i.succAbove) t :=
    stdSimplex.map_comp_apply _ _ t
  have h2 : ((⇑(s.orderEmbOfFin h)) ∘ i.succAbove)
      = ⇑((s.erase (s.orderEmbOfFin h i)).orderEmbOfFin h') :=
    (orderEmbOfFin_erase s h i h').symm
  rw [h2] at h1
  have h3 : ((stdSimplex.map (⇑(s.orderEmbOfFin h))
        (stdSimplex.map i.succAbove t) : stdSimplex ℝ V) : V → ℝ)
      = ((stdSimplex.map (⇑((s.erase (s.orderEmbOfFin h i)).orderEmbOfFin h'))
        t : stdSimplex ℝ V) : V → ℝ) := congrArg _ h1
  exact Subtype.ext h3

/-- **Face compatibility**: the `i`-th face of the affine simplex of `s` is the
affine simplex of `s` with its `i`-th vertex erased. -/
theorem delta_affineSimplex {K : Finset (Finset V)} {s : Finset V} {m : ℕ}
    (hs : s ∈ K) (h : s.card = m + 2) (i : Fin (m + 2))
    (hs' : s.erase (s.orderEmbOfFin h i) ∈ K)
    (h' : (s.erase (s.orderEmbOfFin h i)).card = m + 1) :
    (TopCat.toSSet.obj (barySpace K)).δ i (affineSimplex hs h) = affineSimplex hs' h' := by
  apply ((barySpace K).toSSetObjEquiv (Opposite.op ⦋m⦌)).injective
  rw [toSSetObjEquiv_affineSimplex]
  ext t
  have hδ := TopCat.toSSetObjEquiv_δ_apply (X := barySpace K) (affineSimplex hs h) i t
  rw [show ((barySpace K).toSSetObjEquiv (Opposite.op ⦋m⦌))
      ((TopCat.toSSet.obj (barySpace K)).δ i (affineSimplex hs h)) t =
      ((barySpace K).toSSetObjEquiv (Opposite.op ⦋m + 1⦌)) (affineSimplex hs h)
        (stdSimplex.map i.succAbove t) from hδ]
  rw [toSSetObjEquiv_affineSimplex]
  exact affineSimplexMap_succAbove hs h i hs' h' t

/-! ### The two chain complexes -/

/-- Mathlib's singular chain complex (with real coefficients) of the
barycentric realization of `K`. -/
abbrev singularChains (K : Finset (Finset V)) : ChainComplex (ModuleCat.{0} ℝ) ℕ :=
  (TopCat.toSSet.obj (barySpace K)).chainComplex (ModuleCat.of ℝ ℝ)

omit [LinearOrder V] in
/-- The singular chain complex used here is literally the one produced by
Mathlib's `singularChainComplexFunctor`. -/
theorem singularChains_eq (K : Finset (Finset V)) :
    singularChains K =
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℝ)).obj
        (ModuleCat.of ℝ ℝ)).obj (barySpace K) := rfl

/-- The oriented simplicial chain complex of `K`, shifted so that degree `m`
is spanned by the simplices with `m + 1` vertices, i.e. by the geometric
`m`-dimensional simplices. This complex omits the augmentation term, so its
degree-zero homology is ordinary, not reduced. The augmentation is constructed
separately below. In positive degrees it agrees with the augmented complex. -/
def simplicialChains {K : Finset (Finset V)} (hK : FaceClosed K) :
    ChainComplex (ModuleCat.{0} ℝ) ℕ :=
  ChainComplex.of (fun m ↦ ModuleCat.of ℝ ↥(chains ℝ K (m + 1)))
    (fun m ↦ ModuleCat.ofHom (chainBoundary ℝ hK (m + 1)))
    (fun m ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact Subtype.ext (boundary_boundary_apply (c : Finset V → ℝ)))

@[simp]
theorem simplicialChains_X {K : Finset (Finset V)} (hK : FaceClosed K) (m : ℕ) :
    (simplicialChains hK).X m = ModuleCat.of ℝ ↥(chains ℝ K (m + 1)) := rfl

theorem simplicialChains_d {K : Finset (Finset V)} (hK : FaceClosed K) (m : ℕ) :
    (simplicialChains hK).d (m + 1) m = ModuleCat.ofHom (chainBoundary ℝ hK (m + 1)) := by
  simp [simplicialChains]

/-! ### The comparison chain map -/

/-- The inclusion of the summand of the singular chains corresponding to the
affine simplex of `s`, and zero if `s` is not a simplex of `K` of the right
cardinality. -/
def iotaAffine (K : Finset (Finset V)) (s : Finset V) (m : ℕ) :
    ModuleCat.of ℝ ℝ ⟶ (singularChains K).X m :=
  if h : s ∈ K ∧ s.card = m + 1 then
    (TopCat.toSSet.obj (barySpace K)).ιChainComplex (affineSimplex h.1 h.2)
  else 0

theorem iotaAffine_of_mem {K : Finset (Finset V)} {s : Finset V} {m : ℕ}
    (hs : s ∈ K) (hc : s.card = m + 1) :
    iotaAffine K s m =
      (TopCat.toSSet.obj (barySpace K)).ιChainComplex (affineSimplex hs hc) := by
  rw [iotaAffine, dite_eq_left_of_eq_true (eq_true (⟨hs, hc⟩ : s ∈ K ∧ s.card = m + 1))]

theorem iotaAffine_of_not {K : Finset (Finset V)} {s : Finset V} {m : ℕ}
    (h : ¬ (s ∈ K ∧ s.card = m + 1)) : iotaAffine K s m = 0 := by
  rw [iotaAffine, dite_eq_right_of_eq_false (eq_false h)]

/-- The comparison map on chains, as a linear map defined on all coefficient
functions. -/
def comparisonAux (K : Finset (Finset V)) (m : ℕ) :
    (Finset V → ℝ) →ₗ[ℝ] (singularChains K).X m :=
  ∑ s : Finset V, (iotaAffine K s m).hom ∘ₗ (LinearMap.proj s)

theorem comparisonAux_apply (K : Finset (Finset V)) (m : ℕ) (c : Finset V → ℝ) :
    comparisonAux K m c = ∑ s : Finset V, (iotaAffine K s m).hom (c s) := by
  simp [comparisonAux]

/-- The comparison morphism in degree `m`: an oriented simplicial chain is sent
to the corresponding combination of affine singular simplices. -/
def comparisonHom (K : Finset (Finset V)) (m : ℕ) :
    ModuleCat.of ℝ ↥(chains ℝ K (m + 1)) ⟶ (singularChains K).X m :=
  ModuleCat.ofHom (comparisonAux K m ∘ₗ (chains ℝ K (m + 1)).subtype)

theorem comparisonHom_apply (K : Finset (Finset V)) (m : ℕ) (c : ↥(chains ℝ K (m + 1))) :
    (comparisonHom K m).hom c = ∑ s : Finset V, (iotaAffine K s m).hom ((c : Finset V → ℝ) s) :=
  comparisonAux_apply K m _

/-- **The oriented boundary of a single simplex maps to the alternating
singular boundary of its affine simplex.** -/
theorem iotaAffine_comp_d {K : Finset (Finset V)} (hK : FaceClosed K) {s : Finset V} {m : ℕ}
    (hs : s ∈ K) (hc : s.card = m + 2) :
    iotaAffine K s (m + 1) ≫ (singularChains K).d (m + 1) m =
      ∑ v ∈ s, (orientedSign ℝ (s.erase v) v) • iotaAffine K (s.erase v) m := by
  classical
  rw [iotaAffine_of_mem hs hc, SSet.ιChainComplex_d]
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
  rw [delta_affineSimplex hs hc i hs' h', iotaAffine_of_mem hs' h',
    orientedSign_erase_orderEmbOfFin ℝ s hc i, ← Int.cast_smul_eq_zsmul ℝ ((-1) ^ i.val)]
  push_cast
  rfl

/-- **The comparison map is a chain map**: it intertwines the oriented
simplicial boundary with the alternating singular differential. -/
theorem comparison_comm {K : Finset (Finset V)} (hK : FaceClosed K) (m : ℕ) :
    comparisonHom K (m + 1) ≫ (singularChains K).d (m + 1) m =
      (simplicialChains hK).d (m + 1) m ≫ comparisonHom K m := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change ((singularChains K).d (m + 1) m).hom ((comparisonHom K (m + 1)).hom c) =
    (comparisonHom K m).hom (((simplicialChains hK).d (m + 1) m).hom c)
  set F : Finset V → V → ((singularChains K).X m) := fun s v ↦
    orientedSign ℝ (s.erase v) v • (iotaAffine K (s.erase v) m).hom ((c : Finset V → ℝ) s)
    with hFdef
  have hLHS : ((singularChains K).d (m + 1) m).hom ((comparisonHom K (m + 1)).hom c)
      = ∑ s : Finset V, ∑ v ∈ s, F s v := by
    rw [comparisonHom_apply, map_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    by_cases hcs : (c : Finset V → ℝ) s = 0
    · simp [hFdef, hcs]
    · obtain ⟨hsK, hscard⟩ := c.2 s hcs
      have hmor := iotaAffine_comp_d hK hsK (m := m) hscard
      have := congrArg (fun (g : ModuleCat.of ℝ ℝ ⟶ (singularChains K).X m) ↦
        g.hom ((c : Finset V → ℝ) s)) hmor
      simpa [hFdef] using this
  have hRHS : (comparisonHom K m).hom (((simplicialChains hK).d (m + 1) m).hom c)
      = ∑ f : Finset V, ∑ v ∈ fᶜ, F (insert v f) v := by
    rw [simplicialChains_d]
    change (comparisonHom K m).hom (chainBoundary ℝ hK (m + 1) c) = _
    rw [comparisonHom_apply]
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
    simplicialChains hK ⟶ singularChains K :=
  ChainComplex.ofHom (fun m ↦ comparisonHom K m) (fun m ↦ comparison_comm hK m)

@[simp]
theorem comparisonChainMap_f {K : Finset (Finset V)} (hK : FaceClosed K) (m : ℕ) :
    (comparisonChainMap hK).f m = comparisonHom K m := rfl

/-! ### Identification of the shifted complex with reduced simplicial homology -/

/-- In every positive degree, exactness of the shifted simplicial chain complex
is exactly the reduced acyclicity predicate of `SimplicialHomology`, in the
corresponding augmented degree. -/
theorem ker_chainBoundary_le_range_iff {K : Finset (Finset V)} (hK : FaceClosed K) (m : ℕ) :
    (LinearMap.ker (chainBoundary ℝ hK (m + 1)) ≤
      LinearMap.range (chainBoundary ℝ hK (m + 2))) ↔ IsReducedAcyclicAt ℝ K (m + 2) := by
  constructor
  · intro h c hc
    obtain ⟨hcmem, hcbd⟩ := hc
    obtain ⟨b, hb⟩ := h (show (⟨c, hcmem⟩ : ↥(chains ℝ K (m + 2))) ∈
      LinearMap.ker (chainBoundary ℝ hK (m + 1)) from Subtype.ext hcbd)
    exact ⟨b, b.2, congrArg Subtype.val hb⟩
  · intro h c hc
    have hc0 : boundary ℝ V (c : Finset V → ℝ) = 0 := congrArg Subtype.val hc
    obtain ⟨b, hb, hbc⟩ := h (show (c : Finset V → ℝ) ∈ cycles ℝ K (m + 2) from ⟨c.2, hc0⟩)
    exact ⟨⟨b, hb⟩, Subtype.ext hbc⟩

theorem simplicialChains_exactAt_iff {K : Finset (Finset V)} (hK : FaceClosed K) (m : ℕ) :
    (simplicialChains hK).ExactAt (m + 1) ↔ IsReducedAcyclicAt ℝ K (m + 2) := by
  rw [HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_ker_sub_range]
  have hg : (HomologicalComplex.sc' (simplicialChains hK) (m + 2) (m + 1) m).g
      = ModuleCat.ofHom (chainBoundary ℝ hK (m + 1)) := simplicialChains_d hK m
  have hf : (HomologicalComplex.sc' (simplicialChains hK) (m + 2) (m + 1) m).f
      = ModuleCat.ofHom (chainBoundary ℝ hK (m + 2)) := simplicialChains_d hK (m + 1)
  rw [hf, hg]
  exact ker_chainBoundary_le_range_iff hK m

/-- Vanishing of the reduced simplicial homology of `K` in augmented degree
`m + 2` makes the shifted chain complex have zero homology in degree `m + 1`. -/
theorem isZero_simplicialChains_homology {K : Finset (Finset V)} (hK : FaceClosed K) (m : ℕ)
    (h : IsReducedAcyclicAt ℝ K (m + 2)) :
    Limits.IsZero ((simplicialChains hK).homology (m + 1)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    ((simplicialChains_exactAt_iff hK m).mpr h)

/-! ### The induced map on homology -/

/-- The map induced by the comparison chain map on homology: from the (shifted)
simplicial homology of `K` to Mathlib's singular homology of the barycentric
realization of `K`. -/
def comparisonHomologyMap {K : Finset (Finset V)} (hK : FaceClosed K) (m : ℕ) :
    (simplicialChains hK).homology m ⟶ (realSingularHomology m).obj (barySpace K) :=
  HomologicalComplex.homologyMap (comparisonChainMap hK) m

/-! ### The comparison is an isomorphism for cones

This is the base case of the acyclic-models argument, proved here for the
actual singular homology of the actual barycentric realization: the
realization of a cone is star-shaped, hence contractible, so its singular
homology vanishes in positive degrees, while the oriented simplicial complex
of a cone is reduced acyclic. -/

/-- The apex vertex of a cone, as a point of the barycentric realization. -/
theorem apex_mem_barycentricCarrier {K : Finset (Finset V)} {a : V}
    (hcone : IsConeWithApex K a) (hKne : K.Nonempty) :
    (Pi.single a (1 : ℝ)) ∈ barycentricCarrier K := by
  classical
  obtain ⟨s₀, hs₀⟩ := hKne
  refine ⟨fun v ↦ ?_, ?_, insert a s₀, hcone s₀ hs₀, ?_⟩
  · by_cases h : v = a <;> simp [h]
  · simp [Pi.single_apply, eq_comm]
  · intro v hv
    have hva : v ≠ a := fun h ↦ hv (h ▸ Finset.mem_insert_self a s₀)
    simp [hva]

/-- **The barycentric realization of a cone is star-shaped** around the apex
vertex. -/
theorem starConvex_barycentricCarrier_of_cone {K : Finset (Finset V)} {a : V}
    (hcone : IsConeWithApex K a) :
    StarConvex ℝ (Pi.single a (1 : ℝ)) (barycentricCarrier K) := by
  classical
  rintro y ⟨hy0, hy1, t, htK, hyt⟩ p q hp hq hpq
  refine ⟨fun v ↦ ?_, ?_, insert a t, hcone t htK, ?_⟩
  · have h1 : 0 ≤ p * (Pi.single a (1 : ℝ) : V → ℝ) v := by
      by_cases h : v = a <;> simp [h, hp]
    exact add_nonneg h1 (mul_nonneg hq (hy0 v))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hy1, mul_one]
    have : ∑ v : V, (Pi.single a (1 : ℝ)) v = 1 := by simp [Pi.single_apply, eq_comm]
    rw [this, mul_one, hpq]
  · intro v hv
    have hva : v ≠ a := fun h ↦ hv (h ▸ Finset.mem_insert_self a t)
    have hvt : v ∉ t := fun h ↦ hv (Finset.mem_insert_of_mem h)
    simp [hva, hyt v hvt]

/-- The barycentric realization of a nonempty cone is contractible. -/
theorem contractibleSpace_barycentricCarrier_of_cone {K : Finset (Finset V)} {a : V}
    (hcone : IsConeWithApex K a) (hKne : K.Nonempty) :
    ContractibleSpace ↥(barycentricCarrier K) :=
  StarConvex.contractibleSpace (starConvex_barycentricCarrier_of_cone hcone)
    ⟨_, apex_mem_barycentricCarrier hcone hKne⟩

/-- Ordinary singular homology of the realization of a nonempty cone vanishes
in every positive degree. -/
theorem isZero_realSingularHomology_of_cone {K : Finset (Finset V)} {a : V}
    (hcone : IsConeWithApex K a) (hKne : K.Nonempty) (m : ℕ) (hm : m ≠ 0) :
    Limits.IsZero ((realSingularHomology m).obj (barySpace K)) := by
  have : ContractibleSpace ↥(barycentricCarrier K) :=
    contractibleSpace_barycentricCarrier_of_cone hcone hKne
  have hsub : Subsingleton ((realSingularHomology m).obj
      (TopCat.of ↥(barycentricCarrier K))) :=
    realSingularHomology_subsingleton_of_contractible _ m hm
  change Limits.IsZero ((realSingularHomology m).obj (TopCat.of ↥(barycentricCarrier K)))
  exact ModuleCat.isZero_of_subsingleton _

/-- **The comparison map is an isomorphism in all positive degrees for a
cone.**  Both sides vanish: the simplicial side by the cone homotopy, the
singular side by contractibility of the star-shaped realization. -/
theorem isIso_comparisonHomologyMap_of_cone {K : Finset (Finset V)} (hK : FaceClosed K) {a : V}
    (hcone : IsConeWithApex K a) (hKne : K.Nonempty) (m : ℕ) :
    IsIso (comparisonHomologyMap hK (m + 1)) := by
  have h1 : Limits.IsZero ((simplicialChains hK).homology (m + 1)) :=
    isZero_simplicialChains_homology hK m (isReducedAcyclic_of_cone hcone (m + 2))
  have h2 : Limits.IsZero ((realSingularHomology (m + 1)).obj (barySpace K)) :=
    isZero_realSingularHomology_of_cone hcone hKne (m + 1) (Nat.succ_ne_zero m)
  exact ⟨⟨0, h1.eq_of_src _ _, h2.eq_of_tgt _ _⟩⟩

/-! ### Naturality in the family

The comparison map is compatible with inclusions of face-closed families and
the corresponding inclusions of realizations.  This is what makes it usable in
an induction over subcomplexes (Mayer–Vietoris or acyclic models). -/

/-- The inclusion of barycentric realizations induced by an inclusion of
families. -/
def baryInclusion {K L : Finset (Finset V)} (h : K ⊆ L) : barySpace K ⟶ barySpace L :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.1, barycentricCarrier_mono h x.2⟩, by fun_prop⟩

/-- The affine singular simplex of a face does not depend on the ambient
family. -/
theorem affineSimplex_naturality {K L : Finset (Finset V)} (h : K ⊆ L) {s : Finset V} {m : ℕ}
    (hs : s ∈ K) (hc : s.card = m + 1) :
    (TopCat.toSSet.map (baryInclusion h)).app (Opposite.op ⦋m⦌) (affineSimplex hs hc) =
      affineSimplex (h hs) hc := by
  apply ((barySpace L).toSSetObjEquiv (Opposite.op ⦋m⦌)).injective
  rw [toSSetObjEquiv_affineSimplex]
  ext t
  rfl

/-- The chain map of singular complexes induced by an inclusion of families. -/
def singularChainsMap {K L : Finset (Finset V)} (h : K ⊆ L) :
    singularChains K ⟶ singularChains L :=
  SSet.chainComplexMap (TopCat.toSSet.map (baryInclusion h)) (ModuleCat.of ℝ ℝ)

theorem iotaAffine_naturality {K L : Finset (Finset V)} (h : K ⊆ L) {s : Finset V} {m : ℕ}
    (hs : s ∈ K) (hc : s.card = m + 1) :
    iotaAffine K s m ≫ (singularChainsMap h).f m = iotaAffine L s m := by
  rw [iotaAffine_of_mem hs hc, iotaAffine_of_mem (h hs) hc, singularChainsMap,
    SSet.ι_chainComplexMap_f, affineSimplex_naturality h hs hc]

/-- The inclusion of simplicial chain complexes induced by an inclusion of
face-closed families. -/
def simplicialChainsInclusion {K L : Finset (Finset V)} (hK : FaceClosed K) (hL : FaceClosed L)
    (h : K ⊆ L) : simplicialChains hK ⟶ simplicialChains hL :=
  ChainComplex.ofHom (fun m ↦ ModuleCat.ofHom (Submodule.inclusion (chains_mono h (m + 1))))
    (fun m ↦ by
      rw [simplicialChains_d, simplicialChains_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      rfl)

/-- Degreewise naturality of the comparison map. -/
theorem comparisonHom_naturality {K L : Finset (Finset V)} (h : K ⊆ L) (m : ℕ) :
    comparisonHom K m ≫ (singularChainsMap h).f m =
      ModuleCat.ofHom (Submodule.inclusion (chains_mono h (m + 1))) ≫ comparisonHom L m := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change ((singularChainsMap h).f m).hom ((comparisonHom K m).hom c) =
    (comparisonHom L m).hom (Submodule.inclusion (chains_mono h (m + 1)) c)
  rw [comparisonHom_apply K m c, comparisonHom_apply L m, map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  by_cases hcs : (c : Finset V → ℝ) s = 0
  · simp [hcs]
  · obtain ⟨hsK, hscard⟩ := c.2 s hcs
    exact congrArg (fun (g : ModuleCat.of ℝ ℝ ⟶ (singularChains L).X m) ↦
      g.hom ((c : Finset V → ℝ) s)) (iotaAffine_naturality h hsK hscard)

/-- **Naturality of the comparison chain map** in the face-closed family. -/
theorem comparisonChainMap_naturality {K L : Finset (Finset V)} (hK : FaceClosed K)
    (hL : FaceClosed L) (h : K ⊆ L) :
    comparisonChainMap hK ≫ singularChainsMap h =
      simplicialChainsInclusion hK hL h ≫ comparisonChainMap hL := by
  apply HomologicalComplex.hom_ext
  intro m
  exact comparisonHom_naturality h m

/-- Naturality of the induced map on homology. -/
theorem comparisonHomologyMap_naturality {K L : Finset (Finset V)} (hK : FaceClosed K)
    (hL : FaceClosed L) (h : K ⊆ L) (m : ℕ) :
    HomologicalComplex.homologyMap (comparisonChainMap hK) m ≫
        HomologicalComplex.homologyMap (singularChainsMap h) m =
      HomologicalComplex.homologyMap (simplicialChainsInclusion hK hL h) m ≫
        HomologicalComplex.homologyMap (comparisonChainMap hL) m := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    comparisonChainMap_naturality hK hL h]

/-! ### The augmentation endpoint

The augmentation of the augmented simplicial chain complex (the boundary map
out of the vertex degree) corresponds to the singular augmentation sending
every singular `0`-simplex to `1`; this is the chain-level statement, proved
for the actual coproduct description of Mathlib's singular `0`-chains. -/

/-- The chain-level singular augmentation: every singular `0`-simplex is sent
to `1`. -/
def singularAugmentationChain (K : Finset (Finset V)) :
    (singularChains K).X 0 ⟶ ModuleCat.of ℝ ℝ :=
  Limits.Sigma.desc (fun _ ↦ 𝟙 (ModuleCat.of ℝ ℝ))

omit [LinearOrder V] in
@[reassoc (attr := simp)]
theorem ιChainComplex_singularAugmentationChain (K : Finset (Finset V))
    (x : (TopCat.toSSet.obj (barySpace K)) _⦋0⦌) :
    (TopCat.toSSet.obj (barySpace K)).ιChainComplex (R := ModuleCat.of ℝ ℝ) x ≫
      singularAugmentationChain K = 𝟙 (ModuleCat.of ℝ ℝ) :=
  Limits.Sigma.ι_desc _ _

omit [LinearOrder V] in
/-- The singular augmentation kills the boundaries of singular `1`-chains. -/
theorem d_singularAugmentationChain (K : Finset (Finset V)) :
    (singularChains K).d 1 0 ≫ singularAugmentationChain K = 0 := by
  apply SSet.chainComplex_hom_ext
  intro x
  rw [SSet.ιChainComplex_d_assoc]
  simp [Fin.sum_univ_two]

/-- **The augmentation endpoint of the comparison.**  Composing the comparison
map in degree `0` with the singular augmentation gives exactly the simplicial
augmentation `c ↦ ∑ v, c {v}` of `SimplicialHomology`. -/
theorem comparisonHom_singularAugmentationChain (K : Finset (Finset V)) :
    comparisonHom K 0 ≫ singularAugmentationChain K =
      ModuleCat.ofHom ((augmentation ℝ V).comp (chains ℝ K 1).subtype) := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change (singularAugmentationChain K).hom ((comparisonHom K 0).hom c) =
    augmentation ℝ V (c : Finset V → ℝ)
  rw [comparisonHom_apply, map_sum, augmentation_apply]
  have hterm : ∀ s : Finset V, (singularAugmentationChain K).hom
      ((iotaAffine K s 0).hom ((c : Finset V → ℝ) s))
      = if s ∈ K ∧ s.card = 1 then (c : Finset V → ℝ) s else 0 := by
    intro s
    by_cases hs : s ∈ K ∧ s.card = 1
    · rw [iotaAffine_of_mem hs.1 hs.2]
      simp only [hs, and_self, ite_true]
      exact congrArg (fun (g : ModuleCat.of ℝ ℝ ⟶ ModuleCat.of ℝ ℝ) ↦
        g.hom ((c : Finset V → ℝ) s))
        (ιChainComplex_singularAugmentationChain K (affineSimplex hs.1 hs.2))
    · rw [iotaAffine_of_not hs]
      simp only [hs, ite_false]
      simp
  have hall : ∀ s : Finset V, (if s ∈ K ∧ s.card = 1 then (c : Finset V → ℝ) s else 0)
      = (c : Finset V → ℝ) s := by
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
def augHomology (C : ChainComplex (ModuleCat.{0} ℝ) ℕ) (ε : C.X 0 ⟶ ModuleCat.of ℝ ℝ)
    (hε : C.d 1 0 ≫ ε = 0) : C.homology 0 ⟶ ModuleCat.of ℝ ℝ :=
  (C.isoHomologyι₀).hom ≫ C.descOpcycles ε 1 (by simp) hε

theorem homologyπ_augHomology (C : ChainComplex (ModuleCat.{0} ℝ) ℕ)
    (ε : C.X 0 ⟶ ModuleCat.of ℝ ℝ) (hε : C.d 1 0 ≫ ε = 0) :
    C.homologyπ 0 ≫ augHomology C ε hε = C.iCycles 0 ≫ C.pOpcycles 0 ≫
      C.descOpcycles ε 1 (by simp) hε := by
  rw [augHomology, ← Category.assoc, ← Category.assoc]
  congr 1
  simp

/-- Naturality of the induced map on `H₀` with respect to augmented chain
maps. -/
theorem homologyMap_augHomology {C D : ChainComplex (ModuleCat.{0} ℝ) ℕ} (φ : C ⟶ D)
    (εC : C.X 0 ⟶ ModuleCat.of ℝ ℝ) (εD : D.X 0 ⟶ ModuleCat.of ℝ ℝ)
    (hC : C.d 1 0 ≫ εC = 0) (hD : D.d 1 0 ≫ εD = 0) (hφ : φ.f 0 ≫ εD = εC) :
    HomologicalComplex.homologyMap φ 0 ≫ augHomology D εD hD = augHomology C εC hC := by
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
    (simplicialChains hK).X 0 ⟶ ModuleCat.of ℝ ℝ :=
  ModuleCat.ofHom ((augmentation ℝ V).comp (chains ℝ K 1).subtype)

theorem simplicialAug_apply {K : Finset (Finset V)} (hK : FaceClosed K)
    (c : ↥(chains ℝ K 1)) :
    (simplicialAug hK).hom c = augmentation ℝ V (c : Finset V → ℝ) := rfl

theorem simplicialChains_d_apply {K : Finset (Finset V)} (hK : FaceClosed K) (m : ℕ)
    (c : ↥(chains ℝ K (m + 2))) :
    ((((simplicialChains hK).d (m + 1) m).hom c : ↥(chains ℝ K (m + 1))).val) =
      boundary ℝ V (c : Finset V → ℝ) := by
  rw [simplicialChains_d]
  rfl

theorem d_simplicialAug {K : Finset (Finset V)} (hK : FaceClosed K) :
    (simplicialChains hK).d 1 0 ≫ simplicialAug hK = 0 := by
  have key : ∀ c : ↥(chains ℝ K 2),
      augmentation ℝ V (boundary ℝ V (c : Finset V → ℝ)) = 0 := by
    intro c
    rw [← boundary_apply_empty, boundary_boundary_apply]
    rfl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact key (c : ↥(chains ℝ K 2))

/-- Compatibility of the comparison chain map with the two augmentations. -/
theorem comparisonChainMap_f_zero_singularAugmentationChain {K : Finset (Finset V)}
    (hK : FaceClosed K) :
    (comparisonChainMap hK).f 0 ≫ singularAugmentationChain K = simplicialAug hK :=
  comparisonHom_singularAugmentationChain K

/-- **The comparison map in degree `0` is compatible with the augmentations**,
at the level of homology. -/
theorem comparisonHomologyMap_zero_augHomology {K : Finset (Finset V)} (hK : FaceClosed K) :
    HomologicalComplex.homologyMap (comparisonChainMap hK) 0 ≫
        augHomology (singularChains K) (singularAugmentationChain K)
          (d_singularAugmentationChain K) =
      augHomology (simplicialChains hK) (simplicialAug hK) (d_simplicialAug hK) :=
  homologyMap_augHomology _ _ _ (d_simplicialAug hK) (d_singularAugmentationChain K)
    (comparisonChainMap_f_zero_singularAugmentationChain hK)

/-- For a nonempty cone the simplicial augmentation induces an isomorphism on
`H₀`: this is reduced acyclicity in the vertex degree together with the
existence of a vertex. -/
theorem isIso_augHomology_simplicial {K : Finset (Finset V)} (hK : FaceClosed K) {a : V}
    (hcone : IsConeWithApex K a) (hKne : K.Nonempty) :
    IsIso (augHomology (simplicialChains hK) (simplicialAug hK) (d_simplicialAug hK)) := by
  classical
  have hempty : (∅ : Finset V) ∈ K := by
    obtain ⟨s, hs⟩ := hKne
    exact hK s hs ∅ (Finset.empty_subset s)
  have hvertex : ({a} : Finset V) ∈ K := by
    simpa using hcone ∅ hempty
  set D := simplicialChains hK with hD
  set desc := D.descOpcycles (simplicialAug hK) 1 (by simp) (d_simplicialAug hK) with hdescdef
  have hpd : D.pOpcycles 0 ≫ desc = simplicialAug hK :=
    D.p_descOpcycles (simplicialAug hK) 1 (by simp) (d_simplicialAug hK)
  have hpd' : ∀ c : ↥(chains ℝ K 1),
      desc.hom ((D.pOpcycles 0).hom c) = augmentation ℝ V (c : Finset V → ℝ) :=
    fun c ↦ congrArg (fun (g : D.X 0 ⟶ ModuleCat.of ℝ ℝ) ↦ g.hom c) hpd
  have hsurj_p : ∀ z, ∃ c : ↥(chains ℝ K 1), (D.pOpcycles 0).hom c = z := by
    intro z
    obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective (D.pOpcycles 0)).mp inferInstance z
    exact ⟨(c : ↥(chains ℝ K 1)), hc⟩
  have hiso : IsIso desc := by
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨c, rfl⟩ := hsurj_p z
      have hcz : augmentation ℝ V (c : Finset V → ℝ) = 0 := (hpd' c).symm.trans hz
      have hcycle : ((c : Finset V → ℝ)) ∈ cycles ℝ K 1 :=
        ⟨c.2, (boundary_eq_zero_iff_augmentation_of_mem_chains_one c.2).mpr hcz⟩
      obtain ⟨b, hb, hbc⟩ := isReducedAcyclic_of_cone hcone 1 hcycle
      have hbeq : ((D.d 1 0).hom (⟨b, hb⟩ : ↥(chains ℝ K 2)) : ↥(chains ℝ K 1)) = c :=
        Subtype.ext (by rw [simplicialChains_d_apply hK 0 ⟨b, hb⟩]; exact hbc)
      have hzero : (D.pOpcycles 0).hom ((D.d 1 0).hom (⟨b, hb⟩ : ↥(chains ℝ K 2))) = 0 :=
        congrArg (fun (g : D.X 1 ⟶ D.opcycles 0) ↦ g.hom (⟨b, hb⟩ : ↥(chains ℝ K 2)))
          (D.d_pOpcycles 1 0)
      rw [← hbeq]
      exact hzero
    · intro r
      have hmem : (fun s ↦ if s = ({a} : Finset V) then r else 0) ∈ chains ℝ K 1 := by
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
    augHomology (singularChains K) (singularAugmentationChain K)
        (d_singularAugmentationChain K) =
      (realSingularAugmentation (barySpace K) :
        (singularChains K).homology 0 ⟶ ModuleCat.of ℝ ℝ) := by
  have hlift : ∀ x : (TopCat.toSSet.obj (barySpace K)) _⦋0⦌,
      (TopCat.toSSet.obj (barySpace K)).ιChainComplex (R := ModuleCat.of ℝ ℝ) x ≫
          ((singularChains K).cycles₀Iso).inv =
        (singularChains K).liftCycles
          ((TopCat.toSSet.obj (barySpace K)).ιChainComplex x) 0 (by simp) (by simp) := by
    intro x
    rw [← cancel_mono ((singularChains K).iCycles 0)]
    simp
  have h1 : (singularChains K).homologyπ 0 ≫ ((singularChains K).isoHomologyι₀).hom =
      (singularChains K).iCycles 0 ≫ (singularChains K).pOpcycles 0 := by
    simp
  refine (cancel_epi ((singularChains K).homologyπ 0)).mp ?_
  refine (cancel_epi (((singularChains K).cycles₀Iso).inv)).mp ?_
  apply SSet.chainComplex_hom_ext
  intro x
  have hL : (singularChains K).liftCycles
        ((TopCat.toSSet.obj (barySpace K)).ιChainComplex (R := ModuleCat.of ℝ ℝ) x) 0
        (by simp) (by simp) ≫ (singularChains K).homologyπ 0 ≫
        augHomology (singularChains K) (singularAugmentationChain K)
          (d_singularAugmentationChain K) = 𝟙 (ModuleCat.of ℝ ℝ) := by
    rw [augHomology, ← Category.assoc ((singularChains K).homologyπ 0), h1, Category.assoc,
      ← Category.assoc ((singularChains K).liftCycles _ _ _ _),
      HomologicalComplex.liftCycles_i, HomologicalComplex.p_descOpcycles,
      ιChainComplex_singularAugmentationChain]
  have hL' : (TopCat.toSSet.obj (barySpace K)).ιChainComplex (R := ModuleCat.of ℝ ℝ) x ≫
      ((singularChains K).cycles₀Iso).inv ≫ (singularChains K).homologyπ 0 ≫
        augHomology (singularChains K) (singularAugmentationChain K)
          (d_singularAugmentationChain K) = 𝟙 (ModuleCat.of ℝ ℝ) := by
    rw [← Category.assoc, hlift x]
    exact hL
  have hR : (TopCat.toSSet.obj (barySpace K)).ιChainComplex (R := ModuleCat.of ℝ ℝ) x ≫
      ((singularChains K).cycles₀Iso).inv ≫ (singularChains K).homologyπ 0 ≫
        realSingularAugmentation (barySpace K) = 𝟙 (ModuleCat.of ℝ ℝ) := by
    rw [← Category.assoc, hlift x]
    exact SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε _ _ x
  exact hL'.trans hR.symm

/-- **The comparison map is an isomorphism in degree `0` for a nonempty
cone.**  Together with `isIso_comparisonHomologyMap_of_cone` this settles the
base case of the comparison in *every* degree. -/
theorem isIso_comparisonHomologyMap_zero_of_cone {K : Finset (Finset V)} (hK : FaceClosed K)
    {a : V} (hcone : IsConeWithApex K a) (hKne : K.Nonempty) :
    IsIso (comparisonHomologyMap hK 0) := by
  have hcontr : ContractibleSpace ↥(barycentricCarrier K) :=
    contractibleSpace_barycentricCarrier_of_cone hcone hKne
  have hsing : IsIso (realSingularAugmentation (barySpace K)) := by
    have hpc0 : PathConnectedSpace ↥(barycentricCarrier K) := by
      have := hcontr
      infer_instance
    let _hpc : PathConnectedSpace ↥(barySpace K) := hpc0
    infer_instance
  have h1 : IsIso (augHomology (singularChains K) (singularAugmentationChain K)
      (d_singularAugmentationChain K)) := by
    rw [augHomology_singular_eq]
    exact hsing
  have h2 : IsIso (augHomology (simplicialChains hK) (simplicialAug hK) (d_simplicialAug hK)) :=
    isIso_augHomology_simplicial hK hcone hKne
  have h4 : IsIso (HomologicalComplex.homologyMap (comparisonChainMap hK) 0 ≫
      augHomology (singularChains K) (singularAugmentationChain K)
        (d_singularAugmentationChain K)) := by
    rw [comparisonHomologyMap_zero_augHomology hK]
    exact h2
  exact IsIso.of_isIso_comp_right (HomologicalComplex.homologyMap (comparisonChainMap hK) 0)
    (augHomology (singularChains K) (singularAugmentationChain K)
      (d_singularAugmentationChain K))

/-- **Acyclic-models base case.**  For a nonempty cone the comparison map from
the oriented simplicial homology to Mathlib's singular homology of the
barycentric realization is an isomorphism in *every* ordinary degree, including
degree `0`, with its compatibility with the augmentations proved above. -/
theorem isIso_comparisonHomologyMap_of_cone_all {K : Finset (Finset V)} (hK : FaceClosed K)
    {a : V} (hcone : IsConeWithApex K a) (hKne : K.Nonempty) (m : ℕ) :
    IsIso (comparisonHomologyMap hK m) := by
  cases m with
  | zero => exact isIso_comparisonHomologyMap_zero_of_cone hK hcone hKne
  | succ n => exact isIso_comparisonHomologyMap_of_cone hK hcone hKne n

/-- The full simplex on a nonempty vertex set: the comparison map is an
isomorphism in every degree. -/
theorem isIso_comparisonHomologyMap_powerset {S : Finset V} {a : V} (ha : a ∈ S) (m : ℕ) :
    IsIso (comparisonHomologyMap
      (show FaceClosed S.powerset from fun _ hs _ hts ↦
        Finset.mem_powerset.mpr (hts.trans (Finset.mem_powerset.mp hs))) m) :=
  isIso_comparisonHomologyMap_of_cone_all _
    (fun _ hs ↦ Finset.mem_powerset.mpr (Finset.insert_subset ha (Finset.mem_powerset.mp hs)))
    ⟨∅, Finset.empty_mem_powerset S⟩ m

/-! ### The comparison chain map is degreewise injective

The affine singular simplices attached to distinct faces of `K` are distinct
singular simplices, hence distinct members of the basis of the free module of
singular chains.  Consequently the comparison map realizes the oriented
simplicial chain complex as a *subcomplex* of the singular chain complex. -/

/-- Distinct faces of `K` have distinct affine singular simplices. -/
theorem affineSimplex_inj {K : Finset (Finset V)} {s t : Finset V} {m : ℕ}
    (hs : s ∈ K) (h : s.card = m + 1) (ht : t ∈ K) (h' : t.card = m + 1)
    (heq : affineSimplex hs h = affineSimplex ht h') : s = t := by
  classical
  have hmap : affineSimplexMap hs h = affineSimplexMap ht h' := by
    rw [← toSSetObjEquiv_affineSimplex hs h, ← toSSetObjEquiv_affineSimplex ht h', heq]
  have hemb : ∀ i : Fin (m + 1), s.orderEmbOfFin h i = t.orderEmbOfFin h' i := by
    intro i
    have hval := congrArg
      (fun f : C(stdSimplex ℝ (Fin (m + 1)), ↥(barycentricCarrier K)) ↦
        ((f (stdSimplex.vertex i) : ↥(barycentricCarrier K)) : V → ℝ)) hmap
    simp only [affineSimplexMap_apply, stdSimplex.map_vertex] at hval
    exact stdSimplex.vertex_injective (S := ℝ) (Subtype.ext hval)
  apply Finset.coe_injective
  rw [← s.range_orderEmbOfFin h, ← t.range_orderEmbOfFin h']
  exact congrArg Set.range (funext hemb)

open Classical in
/-- The coefficient functional of a singular simplex on the free module of
singular chains. -/
def singularCoeff (K : Finset (Finset V)) {m : ℕ}
    (x : (TopCat.toSSet.obj (barySpace K)) _⦋m⦌) :
    (singularChains K).X m ⟶ ModuleCat.of ℝ ℝ :=
  Limits.Sigma.desc (fun y ↦ if y = x then 𝟙 (ModuleCat.of ℝ ℝ) else 0)

omit [LinearOrder V] in
open Classical in
theorem ιChainComplex_singularCoeff (K : Finset (Finset V)) {m : ℕ}
    (x y : (TopCat.toSSet.obj (barySpace K)) _⦋m⦌) :
    (TopCat.toSSet.obj (barySpace K)).ιChainComplex (R := ModuleCat.of ℝ ℝ) y ≫
        singularCoeff K x =
      if y = x then 𝟙 (ModuleCat.of ℝ ℝ) else 0 := by
  classical
  simp [singularCoeff, SSet.ιChainComplex]

/-- **The comparison map is injective in every degree.** -/
theorem comparisonHom_injective (K : Finset (Finset V)) (m : ℕ) :
    Function.Injective (comparisonHom K m).hom := by
  classical
  rw [injective_iff_map_eq_zero]
  intro c hc
  apply Subtype.ext
  funext s
  simp only [Submodule.coe_zero, Pi.zero_apply]
  by_contra hcs
  obtain ⟨hsK, hscard⟩ := c.2 s hcs
  set x := affineSimplex hsK hscard with hx
  have hzero := congrArg (fun z ↦ (singularCoeff K x).hom z) hc
  rw [comparisonHom_apply] at hzero
  simp only [map_zero, map_sum] at hzero
  have hterm : ∀ t ∈ (Finset.univ : Finset (Finset V)),
      (singularCoeff K x).hom ((iotaAffine K t m).hom ((c : Finset V → ℝ) t)) =
        if t = s then (c : Finset V → ℝ) t else 0 := by
    intro t _
    by_cases hmem : t ∈ K ∧ t.card = m + 1
    · have hcomp : iotaAffine K t m ≫ singularCoeff K x =
          if affineSimplex hmem.1 hmem.2 = x then 𝟙 (ModuleCat.of ℝ ℝ) else 0 := by
        rw [iotaAffine_of_mem hmem.1 hmem.2, ιChainComplex_singularCoeff]
      have hval := congrArg (fun g : ModuleCat.of ℝ ℝ ⟶ ModuleCat.of ℝ ℝ ↦
        g.hom ((c : Finset V → ℝ) t)) hcomp
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
    · have hct : (c : Finset V → ℝ) t = 0 := by
        by_contra hct
        exact hmem (c.2 t hct)
      have hts : t ≠ s := by
        intro h; exact hmem (h ▸ ⟨hsK, hscard⟩)
      simp [hct, hts]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' Finset.univ s ((c : Finset V → ℝ))] at hzero
  simp only [Finset.mem_univ, ite_true] at hzero
  exact hcs hzero

instance mono_comparisonHom (K : Finset (Finset V)) (m : ℕ) : Mono (comparisonHom K m) :=
  (ModuleCat.mono_iff_injective _).mpr (comparisonHom_injective K m)

/-- **The oriented simplicial chain complex embeds in the singular chain
complex** of the barycentric realization, via the comparison chain map. -/
instance mono_comparisonChainMap {K : Finset (Finset V)} (hK : FaceClosed K) :
    Mono (comparisonChainMap hK) :=
  HomologicalComplex.mono_of_mono_f _ (fun m ↦ mono_comparisonHom K m)

/-! ### The void family versus the family containing only the empty simplex

Both have empty geometric realization, and the comparison map is an
isomorphism in every degree `m` in the range of the comparison (which is
geometric degree `m`, i.e. augmented degree `m + 1`).  They are nevertheless
distinguished by the *augmented* degree `0`, which lies outside that range:
the reduced homology of the void family vanishes there while that of `{∅}`
does not.  This is the usual `H̃_{-1}` of the empty space. -/

omit [LinearOrder V] in
@[simp]
theorem barycentricCarrier_void : barycentricCarrier (∅ : Finset (Finset V)) = ∅ := by
  ext x
  simp [barycentricCarrier]

omit [LinearOrder V] in
@[simp]
theorem barycentricCarrier_singleton_empty :
    barycentricCarrier ({∅} : Finset (Finset V)) = ∅ := by
  ext x
  simp only [barycentricCarrier, Set.mem_ofPred_eq, Finset.mem_singleton, Set.mem_empty_iff_false,
    iff_false, not_and]
  rintro _ hsum ⟨s, rfl, hs⟩
  rw [Finset.sum_congr rfl (fun v _ ↦ hs v (Finset.notMem_empty v))] at hsum
  simp at hsum

/-- The void family is reduced acyclic in every degree, including the
augmented degree `0`. -/
theorem isReducedAcyclic_void : IsReducedAcyclic ℝ (∅ : Finset (Finset V)) := by
  intro n c hc
  have hc0 : c = 0 := by
    funext s
    by_contra h
    exact absurd (hc.1 s h).1 (Finset.notMem_empty s)
  exact hc0 ▸ Submodule.zero_mem _

/-- The family consisting of the empty simplex alone is *not* reduced acyclic
in augmented degree `0`: its reduced homology there is the usual `H̃_{-1}` of
the empty space. -/
theorem not_isReducedAcyclicAt_singleton_empty_zero :
    ¬ IsReducedAcyclicAt ℝ ({∅} : Finset (Finset V)) 0 := by
  classical
  intro h
  set c : Finset V → ℝ := fun s ↦ if s = ∅ then 1 else 0 with hc
  have hmem : c ∈ cycles ℝ ({∅} : Finset (Finset V)) 0 := by
    refine ⟨fun s hs ↦ ?_, ?_⟩
    · have : s = ∅ := by
        by_contra hne
        exact hs (by simp [hc, hne])
      subst this
      simp
    · funext f
      rw [boundary_apply]
      apply Finset.sum_eq_zero
      intro v _
      have : insert v f ≠ ∅ := Finset.insert_ne_empty v f
      simp [hc, this]
  obtain ⟨b, hb, hbc⟩ := h hmem
  have hb0 : b = 0 := by
    funext s
    by_contra hne
    obtain ⟨hs1, hs2⟩ := hb s hne
    rw [Finset.mem_singleton] at hs1
    rw [hs1] at hs2
    simp at hs2
  rw [hb0, map_zero] at hbc
  have := congrFun hbc (∅ : Finset V)
  simp [hc] at this

end Simplicial

end AffineTverberg

/-!
## Remaining comparison obligations

The comparison chain map is injective in every degree and natural for
subcomplex inclusions. It commutes with the actual augmentations, and induces
an isomorphism on homology for nonempty cones (including ordinary degree zero).
It is NOT yet proved to induce an isomorphism for arbitrary finite complexes.
Chain-level injectivity alone does not imply injectivity or surjectivity on
homology. The missing step is an actual small-chain/subdivision or equivalent
comparison argument. Reduced degree zero must be handled through the kernels
of the augmentations; ordinary H₀ is not the reduced group.
-/
