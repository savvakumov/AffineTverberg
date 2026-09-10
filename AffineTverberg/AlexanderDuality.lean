import AffineTverberg.AlexanderDualChains

set_option linter.style.header false

/-!
# Combinatorial Alexander duality over a field

Let `V` be a finite linearly ordered vertex type with `q = |V|` vertices and let
`K ⊆ Finset V` be a face-closed family (an abstract simplicial complex in the
augmented convention, so `∅` may or may not belong to `K`).  Its Alexander dual
is `alexanderDual K = {s | sᶜ ∉ K}`.

The theorem proved here is the exact combinatorial Alexander duality in the
vanishing form which is what a duality argument actually uses:

`alexanderDual_isReducedAcyclicAt_iff` :
  for `c + d + 1 = q`, the reduced simplicial homology of `alexanderDual K`
  vanishes in cardinality-degree `c` **iff** the reduced simplicial homology of
  `K` vanishes in cardinality-degree `d`.

Equivalently `H̃_{c-1}(K^∨) = 0 ↔ H̃_{d-1}(K) = 0` in geometric degrees, with
`(c - 1) + (d - 1) = q - 3`, the classical Alexander duality relation for the
boundary of the `(q-1)`-simplex.

The proof is entirely at the level of the actual oriented chain complexes:

* complementation `dualize` identifies the chains of `alexanderDual K` with the
  *relative cochains* `relCochains K` — coefficient functions supported on the
  non-faces of `K` — turning the boundary into the coboundary
  (`AffineTverberg/AlexanderDualChains.lean`);
* the cochain complex of the full simplex is exact, since the full simplex is a
  cone (`exists_cochainDelta_eq`, `eq_zero_of_cochainDelta_eq_zero`);
* the short exact sequence of cochain complexes
  `0 → relCochains K → (all cochains) → (cochains of K) → 0`
  therefore shifts exactness by one degree (`relCochainExactAt_iff`), which is
  an explicit diagram chase, not an appeal to a long exact sequence;
* finally the concrete cochain complex of `K` is exact exactly where its
  homology vanishes.  This is the universal coefficient statement over a field;
  it is obtained from the dual-annihilator form already proved in
  `AffineTverberg/SimplicialCohomology.lean` through the explicit pairing
  `⟨x, y⟩ = ∑ s, x s * y s`, which is proved to identify the concrete cochain
  complex with the linear dual of the chain complex.

No geometric realization statement is claimed here: this is the combinatorial
engine, and the passage to the singular homology of a geometric complement is a
separate (and still missing) step, discussed in the final section.
-/

noncomputable section

open scoped BigOperators

namespace AffineTverberg
namespace Simplicial

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder V] [Fintype V]

/-! ### Restriction of a coefficient function to a family -/

/-- Restriction of a coefficient function to the simplices of `K`. -/
def restrictFaces (𝕜 : Type*) [Field 𝕜] (K : Finset (Finset V)) :
    (Finset V → 𝕜) →ₗ[𝕜] (Finset V → 𝕜) where
  toFun f := fun t ↦ if t ∈ K then f t else 0
  map_add' f g := by funext t; by_cases h : t ∈ K <;> simp [h]
  map_smul' a f := by funext t; by_cases h : t ∈ K <;> simp [h]

omit [Fintype V] in
@[simp]
theorem restrictFaces_apply (K : Finset (Finset V)) (f : Finset V → 𝕜) (t : Finset V) :
    restrictFaces 𝕜 K f t = if t ∈ K then f t else 0 := rfl

omit [Fintype V] in
theorem restrictFaces_eq_zero_iff {K : Finset (Finset V)} {f : Finset V → 𝕜} :
    restrictFaces 𝕜 K f = 0 ↔ ∀ t ∈ K, f t = 0 := by
  constructor
  · intro h t ht
    have := congrFun h t
    simpa [ht] using this
  · intro h
    funext t
    by_cases ht : t ∈ K <;> simp [ht, h t]

omit [Fintype V] in
theorem restrictFaces_eq_self {K : Finset (Finset V)} {f : Finset V → 𝕜}
    (hf : ∀ t, f t ≠ 0 → t ∈ K) : restrictFaces 𝕜 K f = f := by
  funext t
  by_cases ht : t ∈ K
  · simp [ht]
  · simp only [restrictFaces_apply, ht, ite_false]
    by_contra h
    exact ht (hf t (Ne.symm h))

omit [Fintype V] in
theorem restrictFaces_of_mem_chains {K : Finset (Finset V)} {d : ℕ} {f : Finset V → 𝕜}
    (hf : f ∈ chains 𝕜 K d) : restrictFaces 𝕜 K f = f :=
  restrictFaces_eq_self fun t ht ↦ (hf t ht).1

omit [Fintype V] in
theorem restrictFaces_of_mem_relCochains {K : Finset (Finset V)} {d : ℕ} {f : Finset V → 𝕜}
    (hf : f ∈ relCochains 𝕜 K d) : restrictFaces 𝕜 K f = 0 := by
  rw [restrictFaces_eq_zero_iff]
  intro t ht
  by_contra h
  exact (hf t h).1 ht

/-- Only the values on faces matter for the restricted coboundary. -/
theorem restrictFaces_cochainDelta_restrictFaces {K : Finset (Finset V)}
    (hK : FaceClosed K) (f : Finset V → 𝕜) :
    restrictFaces 𝕜 K (cochainDelta 𝕜 V (restrictFaces 𝕜 K f))
      = restrictFaces 𝕜 K (cochainDelta 𝕜 V f) := by
  funext t
  by_cases ht : t ∈ K
  · simp only [restrictFaces_apply, ht, ite_true, cochainDelta_apply]
    refine Finset.sum_congr rfl fun v hv ↦ ?_
    have hmem : t.erase v ∈ K := hK t ht _ (Finset.erase_subset _ _)
    simp [hmem]
  · simp [ht]

/-! ### Supports of the coboundary -/

theorem cochainDelta_mem_relCochains {K : Finset (Finset V)} (hK : FaceClosed K)
    {d : ℕ} {f : Finset V → 𝕜} (hf : f ∈ relCochains 𝕜 K d) :
    cochainDelta 𝕜 V f ∈ relCochains 𝕜 K (d + 1) := by
  intro t ht
  rw [cochainDelta_apply] at ht
  obtain ⟨v, hv, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
  have hfv : f (t.erase v) ≠ 0 := fun h ↦ hne (by rw [h, mul_zero])
  obtain ⟨hnot, hcard⟩ := hf _ hfv
  constructor
  · intro htK
    exact hnot (hK t htK _ (Finset.erase_subset _ _))
  · rw [Finset.card_erase_of_mem hv] at hcard
    have hpos : 0 < t.card := Finset.card_pos.mpr ⟨v, hv⟩
    omega

theorem cochainDelta_card {d : ℕ} {f : Finset V → 𝕜}
    (hf : ∀ t, f t ≠ 0 → t.card = d) (t : Finset V) :
    cochainDelta 𝕜 V f t ≠ 0 → t.card = d + 1 := by
  intro ht
  rw [cochainDelta_apply] at ht
  obtain ⟨v, hv, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
  have hfv : f (t.erase v) ≠ 0 := fun h ↦ hne (by rw [h, mul_zero])
  have hcard := hf _ hfv
  rw [Finset.card_erase_of_mem hv] at hcard
  have hpos : 0 < t.card := Finset.card_pos.mpr ⟨v, hv⟩
  omega

theorem restrictFaces_cochainDelta_mem_chains {K : Finset (Finset V)} {d : ℕ}
    {f : Finset V → 𝕜} (hf : f ∈ chains 𝕜 K d) :
    restrictFaces 𝕜 K (cochainDelta 𝕜 V f) ∈ chains 𝕜 K (d + 1) := by
  intro t ht
  by_cases htK : t ∈ K
  · refine ⟨htK, ?_⟩
    apply cochainDelta_card (fun s hs ↦ (hf s hs).2)
    simpa [htK] using ht
  · simp [htK] at ht

/-! ### Exactness of the cochain complex of the full simplex -/

/-- The cochain complex of the full simplex is exact in the vertex degree. -/
theorem eq_zero_of_cochainDelta_eq_zero (hne : Nonempty V) {f : Finset V → 𝕜}
    (hf : ∀ t, f t ≠ 0 → t.card = 0) (hδ : cochainDelta 𝕜 V f = 0) : f = 0 := by
  obtain ⟨v⟩ := hne
  have hempty : f ∅ = 0 := by
    have := congrFun hδ {v}
    rw [cochainDelta_apply] at this
    simpa using this
  funext t
  by_cases ht : f t = 0
  · simp [ht]
  · have := hf t ht
    rw [Finset.card_eq_zero] at this
    subst this
    simp [hempty]

/-- The cochain complex of the full simplex is exact in every positive degree.
This is the dual of the acyclicity of the full simplex, which is a cone. -/
theorem exists_cochainDelta_eq (hne : Nonempty V) {d : ℕ} {f : Finset V → 𝕜}
    (hf : ∀ t, f t ≠ 0 → t.card = d + 1) (hδ : cochainDelta 𝕜 V f = 0) :
    ∃ g : Finset V → 𝕜, (∀ t, g t ≠ 0 → t.card = d) ∧ cochainDelta 𝕜 V g = f := by
  classical
  obtain ⟨a⟩ := hne
  by_cases hdq : d + 1 ≤ Fintype.card V
  · set x : Finset V → 𝕜 :=
      compSign 𝕜 (Finset.univ : Finset V) • dualize 𝕜 V f with hx
    have hdx : dualize 𝕜 V x = f := dualize_leftInverse f
    have hxmem : x ∈ chains 𝕜 (Finset.univ : Finset V).powerset (Fintype.card V - (d + 1)) := by
      intro s hs
      refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ s), ?_⟩
      have hne' : f sᶜ ≠ 0 := by
        intro h
        rw [hx] at hs
        simp only [Pi.smul_apply, dualize_apply, h, mul_zero, smul_zero] at hs
        exact hs rfl
      have hcard := hf _ hne'
      have hcc : sᶜ.card = Fintype.card V - s.card := card_compl_eq s
      have hle : s.card ≤ Fintype.card V := Finset.card_le_univ s
      omega
    have hcyc : boundary 𝕜 V x = 0 := by
      apply dualize_injective (𝕜 := 𝕜) (V := V)
      rw [← cochainDelta_dualize, hdx, hδ, map_zero]
    obtain ⟨b, hb, hbx⟩ :=
      isReducedAcyclic_powerset (𝕜 := 𝕜) (S := (Finset.univ : Finset V))
        (a := a) (Finset.mem_univ a) _ ⟨hxmem, hcyc⟩
    refine ⟨dualize 𝕜 V b, ?_, ?_⟩
    · intro t ht
      have hbne : b tᶜ ≠ 0 := by
        intro h
        simp only [dualize_apply, h, mul_zero] at ht
        exact ht rfl
      have hcard := (hb _ hbne).2
      have hcc : tᶜ.card = Fintype.card V - t.card := card_compl_eq t
      have hle : t.card ≤ Fintype.card V := Finset.card_le_univ t
      omega
    · rw [cochainDelta_dualize, hbx, hdx]
  · have hf0 : f = 0 := by
      funext t
      by_contra h
      have hcard := hf t h
      have hle : t.card ≤ Fintype.card V := Finset.card_le_univ t
      omega
    exact ⟨0, by simp, by simp [hf0]⟩

/-! ### The two exactness predicates -/

/-- The chains of `K` in the degree preceding `d`; in degree `0` there is
nothing incoming. -/
def predChains (𝕜 : Type*) [Field 𝕜] (K : Finset (Finset V)) : ℕ → Submodule 𝕜 (Finset V → 𝕜)
  | 0 => ⊥
  | (e + 1) => chains 𝕜 K e

omit [LinearOrder V] [Fintype V] in
theorem mem_predChains_iff {K : Finset (Finset V)} {d : ℕ} {g : Finset V → 𝕜} :
    g ∈ predChains 𝕜 K d ↔ ∀ t, g t ≠ 0 → t ∈ K ∧ t.card + 1 = d := by
  cases d with
  | zero =>
      constructor
      · intro hg t ht
        change g ∈ (⊥ : Submodule 𝕜 (Finset V → 𝕜)) at hg
        rw [Submodule.mem_bot] at hg
        exact absurd (congrFun hg t) ht
      · intro hg
        change g ∈ (⊥ : Submodule 𝕜 (Finset V → 𝕜))
        rw [Submodule.mem_bot]
        funext t
        by_contra h
        exact absurd (hg t h).2 (by omega)
  | succ e =>
      constructor
      · intro hg t ht
        exact ⟨(hg t ht).1, by rw [(hg t ht).2]⟩
      · intro hg t ht
        have := (hg t ht).2
        exact ⟨(hg t ht).1, by omega⟩

/-- Exactness of the concrete cochain complex of `K` in cardinality-degree `d`. -/
def CochainExactAt (𝕜 : Type*) [Field 𝕜] (K : Finset (Finset V)) (d : ℕ) : Prop :=
  ∀ f ∈ chains 𝕜 K d, restrictFaces 𝕜 K (cochainDelta 𝕜 V f) = 0 →
    ∃ g ∈ predChains 𝕜 K d, restrictFaces 𝕜 K (cochainDelta 𝕜 V g) = f

/-- Exactness of the relative cochain complex of `K` in cardinality-degree
`d + 1`. -/
def RelCochainExactAt (𝕜 : Type*) [Field 𝕜] (K : Finset (Finset V)) (d : ℕ) : Prop :=
  ∀ f ∈ relCochains 𝕜 K (d + 1), cochainDelta 𝕜 V f = 0 →
    ∃ g ∈ relCochains 𝕜 K d, cochainDelta 𝕜 V g = f

/-- **The degree shift of the short exact sequence of cochain complexes.**
The relative cochain complex of `K` is exact in degree `d + 1` exactly when the
cochain complex of `K` is exact in degree `d`. -/
theorem relCochainExactAt_iff (hne : Nonempty V) {K : Finset (Finset V)}
    (hK : FaceClosed K) (d : ℕ) :
    RelCochainExactAt 𝕜 K d ↔ CochainExactAt 𝕜 K d := by
  constructor
  · -- from the relative complex to the complex of `K`
    intro hrel u hu hdu
    have hupp : ∀ t, u t ≠ 0 → t.card = d := fun t ht ↦ (hu t ht).2
    have hamem : cochainDelta 𝕜 V u ∈ relCochains 𝕜 K (d + 1) := by
      intro t ht
      refine ⟨?_, cochainDelta_card hupp t ht⟩
      intro htK
      rw [restrictFaces_eq_zero_iff] at hdu
      exact ht (hdu t htK)
    obtain ⟨b, hb, hbu⟩ := hrel _ hamem (cochainDelta_cochainDelta u)
    -- `u - b` is a cocycle of the full complex
    have hwsupp : ∀ t, (u - b) t ≠ 0 → t.card = d := by
      intro t ht
      by_cases h : u t = 0
      · have hbt : b t ≠ 0 := by
          intro hb0
          exact ht (by simp [Pi.sub_apply, h, hb0])
        exact (hb t hbt).2
      · exact hupp t h
    have hwd : cochainDelta 𝕜 V (u - b) = 0 := by
      rw [map_sub, hbu, sub_self]
    cases d with
    | zero =>
        have hw0 : u - b = 0 := eq_zero_of_cochainDelta_eq_zero hne hwsupp hwd
        have hub : u = b := sub_eq_zero.mp hw0
        have hu0 : u = 0 :=
          calc u = restrictFaces 𝕜 K u := (restrictFaces_of_mem_chains hu).symm
            _ = restrictFaces 𝕜 K b := by rw [hub]
            _ = 0 := restrictFaces_of_mem_relCochains hb
        exact ⟨0, Submodule.zero_mem _, by simp [hu0]⟩
    | succ e =>
        obtain ⟨z, hz, hzw⟩ := exists_cochainDelta_eq hne hwsupp hwd
        refine ⟨restrictFaces 𝕜 K z, ?_, ?_⟩
        · rw [mem_predChains_iff]
          intro t ht
          by_cases htK : t ∈ K
          · refine ⟨htK, ?_⟩
            have : z t ≠ 0 := by
              simpa [htK] using ht
            rw [hz t this]
          · simp [htK] at ht
        · rw [restrictFaces_cochainDelta_restrictFaces hK, hzw]
          rw [map_sub, restrictFaces_of_mem_chains hu, restrictFaces_of_mem_relCochains hb,
            sub_zero]
  · -- from the complex of `K` to the relative complex
    intro hex a ha hda
    have hasupp : ∀ t, a t ≠ 0 → t.card = d + 1 := fun t ht ↦ (ha t ht).2
    obtain ⟨b, hb, hba⟩ := exists_cochainDelta_eq hne hasupp hda
    set u : Finset V → 𝕜 := restrictFaces 𝕜 K b with hu
    have humem : u ∈ chains 𝕜 K d := by
      intro t ht
      by_cases htK : t ∈ K
      · refine ⟨htK, hb t (by simpa [hu, htK] using ht)⟩
      · simp [hu, htK] at ht
    have hdu : restrictFaces 𝕜 K (cochainDelta 𝕜 V u) = 0 := by
      rw [hu, restrictFaces_cochainDelta_restrictFaces hK, hba]
      exact restrictFaces_of_mem_relCochains ha
    obtain ⟨g, hg, hgu⟩ := hex u humem hdu
    rw [mem_predChains_iff] at hg
    refine ⟨b - cochainDelta 𝕜 V g, ?_, ?_⟩
    · intro t ht
      have hgsupp : ∀ s, g s ≠ 0 → s.card + 1 = d := fun s hs ↦ (hg s hs).2
      have hdsupp : ∀ s, cochainDelta 𝕜 V g s ≠ 0 → s.card = d := by
        intro s hs
        cases d with
        | zero =>
            exfalso
            rw [cochainDelta_apply] at hs
            obtain ⟨v, hv, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
            have : g (s.erase v) ≠ 0 := fun h ↦ hne' (by rw [h, mul_zero])
            exact absurd (hgsupp _ this) (by omega)
        | succ e =>
            have : ∀ s, g s ≠ 0 → s.card = e := fun s hs ↦ by
              have := hgsupp s hs; omega
            exact cochainDelta_card this s hs
      have hcard : t.card = d := by
        by_cases h : b t = 0
        · have : cochainDelta 𝕜 V g t ≠ 0 := by
            intro h0
            exact ht (by simp [Pi.sub_apply, h, h0])
          exact hdsupp t this
        · exact hb t h
      refine ⟨?_, hcard⟩
      intro htK
      have hbt : b t = u t := by simp [hu, htK]
      have hgt : cochainDelta 𝕜 V g t = u t := by
        have := congrFun hgu t
        simpa [htK] using this
      exact ht (by simp [Pi.sub_apply, hbt, hgt])
    · rw [map_sub, hba, cochainDelta_cochainDelta, sub_zero]

/-! ### The chains of the Alexander dual and the relative cochain complex -/

/-- Complementation turns reduced acyclicity of the Alexander dual into
exactness of the relative cochain complex, and back. -/
theorem isReducedAcyclicAt_alexanderDual_iff {K : Finset (Finset V)} {c d : ℕ}
    (hcd : c + d + 1 = Fintype.card V) :
    IsReducedAcyclicAt 𝕜 (alexanderDual K) c ↔ RelCochainExactAt 𝕜 K d := by
  have hcd1 : c + (d + 1) = Fintype.card V := by omega
  have hcd2 : (c + 1) + d = Fintype.card V := by omega
  constructor
  · intro hac a ha hda
    set x : Finset V → 𝕜 :=
      compSign 𝕜 (Finset.univ : Finset V) • dualize 𝕜 V a with hx
    have hdx : dualize 𝕜 V x = a := dualize_leftInverse a
    have hxmem : x ∈ chains 𝕜 (alexanderDual K) c := by
      rw [hx]
      exact Submodule.smul_mem _ _ (dualize_mem_chains_alexanderDual hcd1 ha)
    have hxcyc : boundary 𝕜 V x = 0 := by
      apply dualize_injective (𝕜 := 𝕜) (V := V)
      rw [← cochainDelta_dualize, hdx, hda, map_zero]
    obtain ⟨y, hy, hyx⟩ := hac ⟨hxmem, hxcyc⟩
    refine ⟨dualize 𝕜 V y, dualize_mem_relCochains hcd2 hy, ?_⟩
    rw [cochainDelta_dualize, hyx, hdx]
  · intro hrel x hx
    obtain ⟨hxmem, hxcyc⟩ := hx
    have hamem : dualize 𝕜 V x ∈ relCochains 𝕜 K (d + 1) :=
      dualize_mem_relCochains hcd1 hxmem
    have hda : cochainDelta 𝕜 V (dualize 𝕜 V x) = 0 := by
      rw [cochainDelta_dualize, hxcyc, map_zero]
    obtain ⟨b, hb, hbx⟩ := hrel _ hamem hda
    refine ⟨compSign 𝕜 (Finset.univ : Finset V) • dualize 𝕜 V b, ?_, ?_⟩
    · exact Submodule.smul_mem _ _ (dualize_mem_chains_alexanderDual hcd2 hb)
    · apply dualize_injective (𝕜 := 𝕜) (V := V)
      rw [← cochainDelta_dualize, dualize_leftInverse b, hbx]

/-! ### The pairing identifying the concrete cochains with the linear dual -/

/-- The indicator coefficient function of a simplex. -/
def indicatorChain (𝕜 : Type*) [Field 𝕜] (s : Finset V) : Finset V → 𝕜 :=
  fun t ↦ if t = s then 1 else 0

omit [Fintype V] in
theorem indicatorChain_mem_chains {K : Finset (Finset V)} {d : ℕ} {s : Finset V}
    (hs : s ∈ K) (hcard : s.card = d) : indicatorChain 𝕜 s ∈ chains 𝕜 K d := by
  intro t ht
  by_cases h : t = s
  · exact ⟨h ▸ hs, by rw [h, hcard]⟩
  · simp only [indicatorChain, h, ite_false] at ht
    exact absurd rfl ht

theorem sum_mul_indicatorChain (u : Finset V → 𝕜) (s : Finset V) :
    ∑ t : Finset V, u t * indicatorChain 𝕜 s t = u s := by
  simp [indicatorChain]

/-- **Adjointness of the oriented boundary and coboundary** for the standard
pairing of coefficient functions. -/
theorem sum_mul_boundary (x y : Finset V → 𝕜) :
    ∑ s : Finset V, x s * boundary 𝕜 V y s
      = ∑ t : Finset V, cochainDelta 𝕜 V x t * y t := by
  classical
  have hmem : ∀ (s : Finset V) (F : V → 𝕜),
      ∑ v ∈ s, F v = ∑ v : V, if v ∈ s then F v else 0 := by
    intro s F
    rw [Finset.sum_ite_mem]
    simp
  have hL : ∑ s : Finset V, x s * boundary 𝕜 V y s
      = ∑ v : V, ∑ s : Finset V,
          (if v ∈ sᶜ then x s * (orientedSign 𝕜 s v * y (insert v s)) else 0) := by
    rw [← Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [boundary_apply, Finset.mul_sum, hmem]
  have hR : ∑ t : Finset V, cochainDelta 𝕜 V x t * y t
      = ∑ v : V, ∑ t : Finset V,
          (if v ∈ t then orientedSign 𝕜 (t.erase v) v * x (t.erase v) * y t else 0) := by
    rw [← Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [cochainDelta_apply, Finset.sum_mul, hmem]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  -- for a fixed vertex, adding or deleting `v` is an involution of the simplices
  set φ : Finset V → Finset V := fun s ↦ if v ∈ s then s.erase v else insert v s with hφ
  have hinv : Function.Involutive φ := by
    intro s
    by_cases hv : v ∈ s
    · have h1 : φ s = s.erase v := by simp only [hφ, ite_eq_left hv]
      have h2 : v ∉ s.erase v := by simp
      calc φ (φ s) = φ (s.erase v) := by rw [h1]
        _ = insert v (s.erase v) := by simp only [hφ, ite_eq_right h2]
        _ = s := Finset.insert_erase hv
    · have h1 : φ s = insert v s := by simp only [hφ, ite_eq_right hv]
      have h2 : v ∈ insert v s := Finset.mem_insert_self v s
      calc φ (φ s) = φ (insert v s) := by rw [h1]
        _ = (insert v s).erase v := by simp only [hφ, ite_eq_left h2]
        _ = s := Finset.erase_insert hv
  refine (Fintype.sum_bijective φ hinv.bijective _ _ ?_).symm
  intro s
  by_cases hv : v ∈ s
  · have hφs : φ s = s.erase v := by simp only [hφ, ite_eq_left hv]
    have h2 : v ∈ (φ s)ᶜ := by simp [hφs]
    rw [ite_eq_left hv, ite_eq_left h2, hφs, Finset.insert_erase hv]
    ring
  · have hφs : φ s = insert v s := by simp only [hφ, ite_eq_right hv]
    have h2 : v ∉ (φ s)ᶜ := by simp [hφs]
    rw [ite_eq_right hv, ite_eq_right h2]

/-- The standard pairing of the chain group with itself, which identifies the
concrete cochains with the linear dual of the chains. -/
def pairingHom (𝕜 : Type*) [Field 𝕜] (K : Finset (Finset V)) (d : ℕ) :
    chains 𝕜 K d →ₗ[𝕜] Module.Dual 𝕜 (chains 𝕜 K d) :=
  LinearMap.mk₂ 𝕜
    (fun x y : chains 𝕜 K d ↦ ∑ s : Finset V, (x : Finset V → 𝕜) s * (y : Finset V → 𝕜) s)
    (fun x₁ x₂ y ↦ by
      simp only [Submodule.coe_add, Pi.add_apply, add_mul]
      exact Finset.sum_add_distrib)
    (fun a x y ↦ by
      simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum])
    (fun x y₁ y₂ ↦ by
      simp only [Submodule.coe_add, Pi.add_apply, mul_add]
      exact Finset.sum_add_distrib)
    (fun a x y ↦ by
      simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ ↦ by ring)

omit [LinearOrder V] in
theorem pairingHom_apply {K : Finset (Finset V)} {d : ℕ} (x y : chains 𝕜 K d) :
    pairingHom 𝕜 K d x y = ∑ s : Finset V, (x : Finset V → 𝕜) s * (y : Finset V → 𝕜) s := rfl

theorem pairingHom_injective (K : Finset (Finset V)) (d : ℕ) :
    Function.Injective (pairingHom 𝕜 K d) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  apply Subtype.ext
  funext s
  by_cases hs : (x : Finset V → 𝕜) s = 0
  · simp [hs]
  · obtain ⟨hmem, hcard⟩ := x.2 s hs
    have := LinearMap.congr_fun hx ⟨indicatorChain 𝕜 s, indicatorChain_mem_chains hmem hcard⟩
    rw [pairingHom_apply] at this
    simpa [sum_mul_indicatorChain] using this

theorem pairingHom_surjective (K : Finset (Finset V)) (d : ℕ) :
    Function.Surjective (pairingHom 𝕜 K d) := by
  have hdim : Module.finrank 𝕜 (chains 𝕜 K d)
      = Module.finrank 𝕜 (Module.Dual 𝕜 (chains 𝕜 K d)) := Subspace.dual_finrank_eq.symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    (pairingHom_injective K d)

/-- Testing against the indicator chains: a coefficient function whose values on
faces are concentrated in cardinality `d` pairs to zero with all `d`-chains of
`K` exactly when it vanishes on the faces of `K`. -/
theorem forall_sum_eq_zero_iff {K : Finset (Finset V)} {d : ℕ} {u : Finset V → 𝕜}
    (hu : ∀ t ∈ K, u t ≠ 0 → t.card = d) :
    (∀ y ∈ chains 𝕜 K d, ∑ t : Finset V, u t * y t = 0) ↔ restrictFaces 𝕜 K u = 0 := by
  constructor
  · intro h
    rw [restrictFaces_eq_zero_iff]
    intro t ht
    by_cases hut : u t = 0
    · exact hut
    · have hcard := hu t ht hut
      have := h (indicatorChain 𝕜 t) (indicatorChain_mem_chains ht hcard)
      rwa [sum_mul_indicatorChain] at this
  · intro h y hy
    rw [restrictFaces_eq_zero_iff] at h
    refine Finset.sum_eq_zero fun t _ ↦ ?_
    by_cases hyt : y t = 0
    · rw [hyt, mul_zero]
    · rw [h t (hy t hyt).1, zero_mul]

/-! ### The concrete cochain complex computes the reduced cohomology -/

/-- Under the pairing, the concrete cocycle condition is the abstract one. -/
theorem pairingHom_mem_cocycles_iff {K : Finset (Finset V)} (hK : FaceClosed K) {d : ℕ}
    (x : chains 𝕜 K d) :
    pairingHom 𝕜 K d x ∈ cocycles 𝕜 hK d ↔
      restrictFaces 𝕜 K (cochainDelta 𝕜 V (x : Finset V → 𝕜)) = 0 := by
  have hsupp : ∀ t ∈ K, cochainDelta 𝕜 V (x : Finset V → 𝕜) t ≠ 0 → t.card = d + 1 :=
    fun t _ ht ↦ cochainDelta_card (fun s hs ↦ (x.2 s hs).2) t ht
  rw [cocycles, LinearMap.mem_ker, coboundary]
  rw [show ((chainBoundary 𝕜 hK d).dualMap (pairingHom 𝕜 K d x) = 0) ↔
      ∀ y : chains 𝕜 K (d + 1), pairingHom 𝕜 K d x (chainBoundary 𝕜 hK d y) = 0 from
    ⟨fun h y ↦ by
        have := LinearMap.congr_fun h y
        simpa using this,
      fun h ↦ by
        ext y
        simpa using h y⟩]
  rw [← forall_sum_eq_zero_iff (d := d + 1) hsupp]
  constructor
  · intro h y hy
    have := h ⟨y, hy⟩
    rw [pairingHom_apply, chainBoundary_coe] at this
    rw [← sum_mul_boundary]
    exact this
  · intro h y
    rw [pairingHom_apply, chainBoundary_coe, sum_mul_boundary]
    exact h y.1 y.2

/-- Under the pairing, the abstract coboundary condition is the concrete one. -/
theorem pairingHom_mem_coboundaries_iff {K : Finset (Finset V)} (hK : FaceClosed K) {d : ℕ}
    (x : chains 𝕜 K d) :
    pairingHom 𝕜 K d x ∈ coboundaries 𝕜 hK d ↔
      ∃ g ∈ predChains 𝕜 K d, restrictFaces 𝕜 K (cochainDelta 𝕜 V g) = (x : Finset V → 𝕜) := by
  cases d with
  | zero =>
      constructor
      · intro hmem
        obtain ⟨ψ, hψ⟩ := hmem
        have hx0 : pairingHom 𝕜 K 0 x = 0 := by
          rw [← hψ]
          ext y
          change ψ (chainDifferential 𝕜 hK 0 y) = 0
          rw [show chainDifferential 𝕜 hK 0 = 0 from rfl]
          simp
        have : x = 0 := pairingHom_injective K 0 (by rw [hx0, map_zero])
        refine ⟨0, Submodule.zero_mem _, ?_⟩
        rw [map_zero, map_zero, this]
        rfl
      · rintro ⟨g, hg, hgx⟩
        change g ∈ (⊥ : Submodule 𝕜 (Finset V → 𝕜)) at hg
        rw [Submodule.mem_bot] at hg
        subst hg
        rw [map_zero, map_zero] at hgx
        have : x = 0 := Subtype.ext hgx.symm
        rw [this, map_zero]
        exact Submodule.zero_mem _
  | succ e =>
      constructor
      · rintro ⟨ψ, hψ⟩
        obtain ⟨g, rfl⟩ := pairingHom_surjective (𝕜 := 𝕜) K e ψ
        refine ⟨(g : Finset V → 𝕜), (by exact g.2 : (g : Finset V → 𝕜) ∈ chains 𝕜 K e), ?_⟩
        have hsupp : ∀ t ∈ K,
            (cochainDelta 𝕜 V (g : Finset V → 𝕜) - (x : Finset V → 𝕜)) t ≠ 0 → t.card = e + 1 := by
          intro t _ ht
          by_cases h : cochainDelta 𝕜 V (g : Finset V → 𝕜) t = 0
          · have hxt : (x : Finset V → 𝕜) t ≠ 0 := by
              intro h0
              exact ht (by simp [Pi.sub_apply, h, h0])
            exact (x.2 t hxt).2
          · exact cochainDelta_card (fun s hs ↦ (g.2 s hs).2) t h
        have hzero : restrictFaces 𝕜 K
            (cochainDelta 𝕜 V (g : Finset V → 𝕜) - (x : Finset V → 𝕜)) = 0 := by
          rw [← forall_sum_eq_zero_iff hsupp]
          intro y hy
          have hcomp : pairingHom 𝕜 K e g (chainBoundary 𝕜 hK e ⟨y, hy⟩)
              = pairingHom 𝕜 K (e + 1) x ⟨y, hy⟩ := LinearMap.congr_fun hψ ⟨y, hy⟩
          rw [pairingHom_apply, pairingHom_apply, chainBoundary_coe, sum_mul_boundary] at hcomp
          have : ∑ t : Finset V,
              (cochainDelta 𝕜 V (g : Finset V → 𝕜) t - (x : Finset V → 𝕜) t) * y t = 0 := by
            rw [Finset.sum_congr rfl (fun t _ ↦ sub_mul _ _ _), Finset.sum_sub_distrib, hcomp,
              sub_self]
          simpa [Pi.sub_apply] using this
        rw [map_sub, restrictFaces_of_mem_chains x.2, sub_eq_zero] at hzero
        exact hzero
      · rintro ⟨g, hg, hgx⟩
        rw [mem_predChains_iff] at hg
        have hgmem : g ∈ chains 𝕜 K e := fun t ht ↦ ⟨(hg t ht).1, by have := (hg t ht).2; omega⟩
        refine ⟨pairingHom 𝕜 K e ⟨g, hgmem⟩, ?_⟩
        ext y
        change pairingHom 𝕜 K e ⟨g, hgmem⟩ (chainDifferential 𝕜 hK (e + 1) y)
          = pairingHom 𝕜 K (e + 1) x y
        rw [show chainDifferential 𝕜 hK (e + 1) = chainBoundary 𝕜 hK e from rfl]
        rw [pairingHom_apply, pairingHom_apply, chainBoundary_coe, sum_mul_boundary]
        refine Finset.sum_congr rfl fun t _ ↦ ?_
        by_cases hyt : (y : Finset V → 𝕜) t = 0
        · rw [hyt, mul_zero, mul_zero]
        · have htK : t ∈ K := (y.2 t hyt).1
          have := congrFun hgx t
          simp only [restrictFaces_apply, htK, ite_true] at this
          rw [this]

/-- **The concrete cochain complex is exact exactly where the reduced homology
vanishes** (the universal coefficient statement over a field). -/
theorem cochainExactAt_iff_isReducedAcyclicAt {K : Finset (Finset V)} (hK : FaceClosed K)
    (d : ℕ) : CochainExactAt 𝕜 K d ↔ IsReducedAcyclicAt 𝕜 K d := by
  rw [← cohomology_subsingleton_iff_isReducedAcyclicAt (𝕜 := 𝕜) hK d,
    cohomology_subsingleton_iff_cocycles_le]
  constructor
  · intro hex φ hφ
    obtain ⟨x, rfl⟩ := pairingHom_surjective (𝕜 := 𝕜) K d φ
    rw [pairingHom_mem_cocycles_iff hK] at hφ
    obtain ⟨g, hg, hgx⟩ := hex (x : Finset V → 𝕜) x.2 hφ
    exact (pairingHom_mem_coboundaries_iff hK x).mpr ⟨g, hg, hgx⟩
  · intro hle f hf hdf
    have hmem : pairingHom 𝕜 K d ⟨f, hf⟩ ∈ cocycles 𝕜 hK d :=
      (pairingHom_mem_cocycles_iff hK ⟨f, hf⟩).mpr hdf
    exact (pairingHom_mem_coboundaries_iff hK ⟨f, hf⟩).mp (hle hmem)

/-! ### Combinatorial Alexander duality -/

/-- **Combinatorial Alexander duality over a field.**  For a face-closed family
`K` on a vertex type with `q = c + d + 1` vertices, the reduced simplicial
homology of the Alexander dual `alexanderDual K` vanishes in cardinality-degree
`c` if and only if the reduced simplicial homology of `K` vanishes in
cardinality-degree `d`.  In geometric degrees this is the classical relation
`H̃_{c-1}(K^∨) = 0 ↔ H̃_{q-c-2}(K) = 0`. -/
theorem isReducedAcyclicAt_alexanderDual_iff_isReducedAcyclicAt
    {K : Finset (Finset V)} (hK : FaceClosed K) {c d : ℕ}
    (hcd : c + d + 1 = Fintype.card V) :
    IsReducedAcyclicAt 𝕜 (alexanderDual K) c ↔ IsReducedAcyclicAt 𝕜 K d := by
  have hne : Nonempty V := by
    rw [← Fintype.card_pos_iff]
    omega
  rw [isReducedAcyclicAt_alexanderDual_iff hcd, relCochainExactAt_iff hne hK,
    cochainExactAt_iff_isReducedAcyclicAt hK]

/-- The same statement for the reduced homology modules. -/
theorem homology_alexanderDual_subsingleton_iff
    {K : Finset (Finset V)} (hK : FaceClosed K) {c d : ℕ}
    (hcd : c + d + 1 = Fintype.card V) :
    Subsingleton (homology 𝕜 (alexanderDual K) c) ↔ Subsingleton (homology 𝕜 K d) := by
  rw [homology_subsingleton_iff, homology_subsingleton_iff]
  exact isReducedAcyclicAt_alexanderDual_iff_isReducedAcyclicAt hK hcd

end Simplicial
end AffineTverberg
