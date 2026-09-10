import AffineTverberg.CofaceDoubleComplex
import AffineTverberg.InducedComplement

set_option linter.style.header false

/-!
# Duality from the coface double complex

The two staircase theorems of `CofaceDoubleComplex` are combined here into the
algebraic core of Alexander duality.

Two explicit maps identify the two degenerate pages of the double complex:

* `psiMap x`, the chain `x` of the induced subcomplex on the *bad* vertices,
  placed in the first column.  It identifies the reduced chain complex of the
  bad subcomplex with the first column of the double complex, and turns the
  simplicial boundary into (minus) the total differential.
* `phiMap z a`, the relative cochain `a` multiplied by the restrictions of a
  fixed global top cycle `z`.  Because *one* global cycle is used for every
  face, no orientation has to be chosen face by face, and the total
  differential becomes literally the oriented simplicial coboundary.

The main theorem `exists_relCoboundary_of_relCocycle` states: if the bad
subcomplex is reduced acyclic in cardinality degree `k + 1`, then the relative
cochain complex of the pair `(K, K[G])` is exact in cardinality degree
`Q - k`.  The companion `isReducedAcyclicAt_inducedFaces_of_relExact` runs the
(explicit, elementary) long exact sequence of the pair and converts this into
reduced acyclicity of the induced subcomplex `K[G]`.
-/

noncomputable section

namespace AffineTverberg.Simplicial

variable {V : Type} [Fintype V] [LinearOrder V]

/-! ### Oriented signs on singletons -/

omit [Fintype V] in
theorem orientedSign_singleton_of_lt {v u : V} (h : v < u) :
    orientedSign ℝ ({u} : Finset V) v = 1 := by
  simp [orientedSign, Finset.filter_singleton, asymm h]

omit [Fintype V] in
theorem orientedSign_singleton_of_gt {v u : V} (h : v < u) :
    orientedSign ℝ ({v} : Finset V) u = -1 := by
  simp [orientedSign, Finset.filter_singleton, h]

omit [Fintype V] in
/-- The two oriented signs of an edge cancel. -/
theorem sum_orientedSign_card_two {s : Finset V} (hs : s.card = 2) :
    ∑ u ∈ s, orientedSign ℝ (s.erase u) u = 0 := by
  classical
  obtain ⟨v, u, hvu, rfl⟩ := Finset.card_eq_two.mp hs
  have hev : ({v, u} : Finset V).erase v = {u} := by
    rw [Finset.erase_insert (by simpa using hvu)]
  have heu : ({v, u} : Finset V).erase u = {v} := by
    rw [Finset.pair_comm, Finset.erase_insert (by simpa using hvu.symm)]
  rw [Finset.sum_pair hvu, hev, heu]
  rcases lt_or_gt_of_ne hvu with h | h
  · rw [orientedSign_singleton_of_lt h, orientedSign_singleton_of_gt h]
    ring
  · rw [orientedSign_singleton_of_gt h, orientedSign_singleton_of_lt h]
    ring

/-! ### The bad faces and the two comparison maps -/

/-- The faces of `K` which are not contained in `G`. -/
def badFaces (K : Finset (Finset V)) (G : Finset V) : Finset (Finset V) :=
  K.filter (fun s => ¬ s ⊆ G)

omit [Fintype V] in
theorem mem_badFaces {K : Finset (Finset V)} {G s : Finset V} :
    s ∈ badFaces K G ↔ s ∈ K ∧ ¬ s ⊆ G := Finset.mem_filter

/-- The relative coboundary of the pair `(K, K[G])`. -/
def relCoboundary (K : Finset (Finset V)) (G : Finset V) :
    (Finset V → ℝ) →ₗ[ℝ] (Finset V → ℝ) :=
  coboundaryOn ℝ (badFaces K G)

/-- The first-column comparison map: a chain of the bad subcomplex, placed in
the column of one-element faces. -/
def psiMap (V : Type) [Fintype V] [LinearOrder V] :
    (Finset V → ℝ) →ₗ[ℝ] (Finset V → Finset V → ℝ) where
  toFun x := fun s t => if s ⊆ t ∧ s.card = 1 then x t else 0
  map_add' x y := by
    funext s t
    by_cases h : s ⊆ t ∧ s.card = 1 <;> simp [h]
  map_smul' r x := by
    funext s t
    by_cases h : s ⊆ t ∧ s.card = 1 <;> simp [h]

theorem psiMap_apply (x : Finset V → ℝ) (s t : Finset V) :
    psiMap V x s t = if s ⊆ t ∧ s.card = 1 then x t else 0 := rfl

/-- The top-row comparison map: a relative cochain times the restrictions of a
fixed global top cycle. -/
def phiMap (z : Finset V → ℝ) :
    (Finset V → ℝ) →ₗ[ℝ] (Finset V → Finset V → ℝ) where
  toFun a := fun s t => a s * cofaceRestriction s z t
  map_add' a b := by
    funext s t
    by_cases h : s ⊆ t <;> simp [cofaceRestriction, h, add_mul]
  map_smul' r a := by
    funext s t
    by_cases h : s ⊆ t <;> simp [cofaceRestriction, h, mul_assoc]

omit [Fintype V] in
theorem phiMap_apply (z a : Finset V → ℝ) (s t : Finset V) :
    phiMap z a s t = a s * (if s ⊆ t then z t else 0) := rfl

/-! ### The first column is the chain complex of the bad subcomplex -/

theorem dhMap_psiMap (x : Finset V → ℝ) : dhMap V (psiMap V x) = 0 := by
  classical
  funext s t
  by_cases hst : s ⊆ t
  · rw [dhMap_apply_of_subset hst]
    by_cases hcard : s.card = 2
    · have hterm : ∀ v ∈ s, orientedSign ℝ (s.erase v) v * psiMap V x (s.erase v) t
          = orientedSign ℝ (s.erase v) v * x t := by
        intro v hv
        have h1 : (s.erase v).card = 1 := by rw [Finset.card_erase_of_mem hv, hcard]
        have h2 : s.erase v ⊆ t := (Finset.erase_subset v s).trans hst
        rw [psiMap_apply]
        simp [h1, h2]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, sum_orientedSign_card_two hcard,
        zero_mul]
      rfl
    · refine Finset.sum_eq_zero fun v hv => ?_
      have h1 : (s.erase v).card ≠ 1 := by
        rw [Finset.card_erase_of_mem hv]
        have hpos : 1 ≤ s.card := Finset.card_pos.mpr ⟨v, hv⟩
        omega
      rw [psiMap_apply]
      simp [h1]
  · exact dhMap_apply_of_not_subset hst

theorem dvMap_psiMap (x : Finset V → ℝ) :
    dvMap V (psiMap V x) = psiMap V (boundary ℝ V x) := by
  classical
  funext s t
  have hlhs : dvMap V (psiMap V x) s t
      = if s ⊆ t then ∑ v ∈ tᶜ, orientedSign ℝ t v * psiMap V x s (insert v t) else 0 := rfl
  have hrhs : psiMap V (boundary ℝ V x) s t
      = if s ⊆ t ∧ s.card = 1 then boundary ℝ V x t else 0 := rfl
  by_cases hcard : s.card = 1
  · by_cases hst : s ⊆ t
    · rw [hlhs, hrhs]
      simp only [hst, hcard, and_self, ↓reduceIte, boundary_apply]
      refine Finset.sum_congr rfl fun v _ => ?_
      have hsub : s ⊆ insert v t := hst.trans (Finset.subset_insert v t)
      rw [psiMap_apply]
      simp [hsub, hcard]
    · rw [hlhs, hrhs]
      simp [hst]
  · have hz : ∀ v : V, psiMap V x s (insert v t) = 0 := by
      intro v
      rw [psiMap_apply]
      simp [hcard]
    rw [hlhs, hrhs]
    simp [hz, hcard]

theorem dtotMap_psiMap (x : Finset V → ℝ) :
    dtotMap V (psiMap V x) = - psiMap V (boundary ℝ V x) := by
  classical
  funext s t
  have hdv : cofaceBoundary s (psiMap V x s) t = psiMap V (boundary ℝ V x) s t :=
    congrFun (congrFun (dvMap_psiMap x) s) t
  have hdh : dhMap V (psiMap V x) s t = 0 := congrFun (congrFun (dhMap_psiMap x) s) t
  have hgoal : dtotMap V (psiMap V x) s t
      = ((-1 : ℝ) ^ s.card) * psiMap V (boundary ℝ V x) s t := by
    rw [dtotMap_apply, hdv, hdh, add_zero]
  have hrhs : (- psiMap V (boundary ℝ V x)) s t = - psiMap V (boundary ℝ V x) s t := rfl
  rw [hgoal, hrhs]
  by_cases hcard : s.card = 1
  · rw [hcard]
    ring
  · have hzero : psiMap V (boundary ℝ V x) s t = 0 := by
      rw [psiMap_apply]
      simp [hcard]
    rw [hzero]
    ring

theorem psiMap_mem_rowChains {K : Finset (Finset V)} (hK : FaceClosed K) {G : Finset V}
    {L : Finset (Finset V)} (hL : ∀ s, s ∈ L ↔ s ∈ K ∧ ∀ v ∈ s, v ∉ G) {k : ℕ}
    {x : Finset V → ℝ} (hx : x ∈ chains ℝ L (k + 1)) :
    psiMap V x ∈ rowChains K G k := by
  classical
  refine ⟨fun s t hst => ?_, LinearMap.mem_ker.mpr (dhMap_psiMap x)⟩
  rw [psiMap_apply] at hst
  by_cases hc : s ⊆ t ∧ s.card = 1
  · simp only [hc, and_self, ↓reduceIte] at hst
    obtain ⟨htmem, htcard⟩ := hx t hst
    obtain ⟨htK, htsub⟩ := (hL t).mp htmem
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc.2
    have hc2 := hc.2
    refine ⟨⟨hK t htK s hc.1, ?_, htK, hc.1, by omega⟩, hc.2⟩
    intro hsG
    have hvG : v ∈ G := hsG (by rw [hv]; exact Finset.mem_singleton_self v)
    have hvt : v ∈ t := hc.1 (by rw [hv]; exact Finset.mem_singleton_self v)
    exact htsub v hvt hvG
  · simp only [hc, ↓reduceIte] at hst
    exact absurd rfl hst

theorem eq_zero_of_psiMap_eq_zero {x : Finset V → ℝ}
    (hx : ∀ t, x t ≠ 0 → t.Nonempty) (h : psiMap V x = 0) : x = 0 := by
  funext t
  by_contra hne
  obtain ⟨v, hv⟩ := hx t hne
  have h0 : psiMap V x {v} t = 0 := congrFun (congrFun h {v}) t
  rw [psiMap_apply] at h0
  simp only [Finset.singleton_subset_iff, hv, Finset.card_singleton, and_self,
    ↓reduceIte] at h0
  exact hne h0

/-- Every element of the first column with vanishing horizontal differential
comes from a chain of the bad subcomplex. -/
theorem exists_psiMap_of_mem_rowChains {K : Finset (Finset V)} {G : Finset V}
    {L : Finset (Finset V)} (hL : ∀ s, s ∈ L ↔ s ∈ K ∧ ∀ v ∈ s, v ∉ G) {k : ℕ}
    {w : Finset V → Finset V → ℝ} (hw : w ∈ rowChains K G k) :
    ∃ x ∈ chains ℝ L (k + 1), w = psiMap V x := by
  classical
  have hdh : dhMap V w = 0 := LinearMap.mem_ker.mp hw.2
  -- the value of `w` on a singleton inside `t` does not depend on the singleton
  have hconst : ∀ (t : Finset V) (v u : V), v ∈ t → u ∈ t → w {v} t = w {u} t := by
    intro t v u hv hu
    rcases eq_or_ne v u with rfl | hvu
    · rfl
    · have hst : ({v, u} : Finset V) ⊆ t := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl <;> assumption
      have h0 : dhMap V w {v, u} t = 0 := congrFun (congrFun hdh _) t
      rw [dhMap_apply_of_subset hst] at h0
      have hev : ({v, u} : Finset V).erase v = {u} := by
        rw [Finset.erase_insert (by simpa using hvu)]
      have heu : ({v, u} : Finset V).erase u = {v} := by
        rw [Finset.pair_comm, Finset.erase_insert (by simpa using hvu.symm)]
      rw [Finset.sum_pair hvu, hev, heu] at h0
      rcases lt_or_gt_of_ne hvu with h | h
      · rw [orientedSign_singleton_of_lt h, orientedSign_singleton_of_gt h] at h0
        linarith
      · rw [orientedSign_singleton_of_gt h, orientedSign_singleton_of_lt h] at h0
        linarith
  refine ⟨fun t => if h : t.Nonempty then w {t.min' h} t else 0, ?_, ?_⟩
  · intro t ht
    by_cases hne : t.Nonempty
    · simp only [hne, ↓reduceDIte] at ht
      obtain ⟨⟨_, _, htK, _, hcard⟩, _⟩ := hw.1 _ t ht
      refine ⟨(hL t).mpr ⟨htK, ?_⟩,
        by simp only [Finset.card_singleton] at hcard; omega⟩
      intro v hv hvG
      have hwv : w {v} t ≠ 0 := by
        rw [hconst t v (t.min' hne) hv (t.min'_mem hne)]
        exact ht
      obtain ⟨⟨_, hsG, _, _, _⟩, _⟩ := hw.1 _ t hwv
      exact hsG (by simpa using hvG)
    · simp only [hne, ↓reduceDIte] at ht
      exact absurd rfl ht
  · funext s t
    rw [psiMap_apply]
    by_cases hc : s ⊆ t ∧ s.card = 1
    · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc.2
      have hvt : v ∈ t := hc.1 (by rw [hv]; exact Finset.mem_singleton_self v)
      have hne : t.Nonempty := ⟨v, hvt⟩
      simp only [hc, and_self, ↓reduceIte, hne, ↓reduceDIte]
      rw [hv, hconst t v (t.min' hne) hvt (t.min'_mem hne)]
    · simp only [hc, ↓reduceIte]
      by_contra hne
      exact hc (⟨(hw.1 s t hne).1.2.2.2.1, (hw.1 s t hne).2⟩)

/-! ### The top row is the relative cochain complex -/

theorem phiMap_mem_topChains {K : Finset (Finset V)} {G : Finset V} {Q k p : ℕ}
    (hpk : p + k = Q) {z : Finset V → ℝ} (hz : z ∈ cycles ℝ K Q)
    {a : Finset V → ℝ} (ha : a ∈ chains ℝ (badFaces K G) p) :
    phiMap z a ∈ topChains K G Q k := by
  classical
  constructor
  · intro s t hst
    rw [phiMap_apply] at hst
    have has : a s ≠ 0 := fun h => hst (by rw [h, zero_mul])
    obtain ⟨hsK, hsG⟩ := mem_badFaces.mp (ha s has).1
    have hcard := (ha s has).2
    have hsub : s ⊆ t := by
      by_contra h
      simp only [h, ↓reduceIte, mul_zero] at hst
      exact hst rfl
    have hzt : z t ≠ 0 := by
      intro h
      apply hst
      simp only [hsub, ↓reduceIte, h, mul_zero]
    obtain ⟨htK, htcard⟩ := hz.1 t hzt
    exact ⟨⟨hsK, hsG, htK, hsub, by omega⟩, htcard⟩
  · refine LinearMap.mem_ker.mpr ?_
    funext s
    change cofaceBoundary s (phiMap z a s) = 0
    have hs : phiMap z a s = a s • cofaceRestriction s z := by
      funext t
      rw [phiMap_apply]
      simp [cofaceRestriction_apply, smul_eq_mul]
    rw [hs, map_smul]
    have : cofaceBoundary s (cofaceRestriction s z) = 0 := by
      change cofaceRestriction s (boundary ℝ V (cofaceRestriction s z)) = 0
      rw [cofaceRestriction_boundary_cofaceRestriction, hz.2, map_zero]
    rw [this, smul_zero]

theorem dtotMap_phiMap {K : Finset (Finset V)} {Q : ℕ}
    {z : Finset V → ℝ} (hz : z ∈ cycles ℝ K Q) (a : Finset V → ℝ) :
    dtotMap V (phiMap z a) = phiMap z (coboundaryFun ℝ V a) := by
  classical
  funext s t
  rw [dtotMap_apply]
  have hdv : cofaceBoundary s (phiMap z a s) t = 0 := by
    have hs : phiMap z a s = a s • cofaceRestriction s z := by
      funext u
      rw [phiMap_apply]
      simp [cofaceRestriction_apply, smul_eq_mul]
    have h0 : cofaceBoundary s (cofaceRestriction s z) = 0 := by
      change cofaceRestriction s (boundary ℝ V (cofaceRestriction s z)) = 0
      rw [cofaceRestriction_boundary_cofaceRestriction, hz.2, map_zero]
    rw [hs, map_smul, h0, smul_zero]
    rfl
  rw [hdv, mul_zero, zero_add, phiMap_apply, coboundaryFun_apply]
  by_cases hst : s ⊆ t
  · rw [dhMap_apply_of_subset hst]
    simp only [hst, ↓reduceIte, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hsub : s.erase v ⊆ t := (Finset.erase_subset v s).trans hst
    rw [phiMap_apply]
    simp only [hsub, ↓reduceIte]
    ring
  · rw [dhMap_apply_of_not_subset hst]
    simp [hst]

/-- On relative cochains, the total differential of the top row is literally
the relative coboundary. -/
theorem dtotMap_phiMap_relCoboundary {K : Finset (Finset V)} (hK : FaceClosed K)
    {G : Finset V} {Q p : ℕ} {z : Finset V → ℝ} (hz : z ∈ cycles ℝ K Q)
    {a : Finset V → ℝ} (ha : a ∈ chains ℝ (badFaces K G) p) :
    dtotMap V (phiMap z a) = phiMap z (relCoboundary K G a) := by
  classical
  rw [dtotMap_phiMap hz]
  funext s t
  rw [phiMap_apply, phiMap_apply]
  by_cases hzt : (if s ⊆ t then z t else 0) = 0
  · rw [hzt, mul_zero, mul_zero]
  · have hst : s ⊆ t := by
      by_contra h
      exact hzt (by simp [h])
    have hztne : z t ≠ 0 := by
      intro h
      exact hzt (by simp [hst, h])
    have hsK : s ∈ K := hK t (hz.1 t hztne).1 s hst
    have heq : relCoboundary K G a s = coboundaryFun ℝ V a s := by
      rw [relCoboundary, coboundaryOn_apply]
      by_cases hbad : s ∈ badFaces K G
      · simp only [hbad, ↓reduceIte]
      · simp only [hbad, ↓reduceIte, coboundaryFun_apply]
        have hsG : s ⊆ G := by
          by_contra h
          exact hbad (mem_badFaces.mpr ⟨hsK, h⟩)
        refine (Finset.sum_eq_zero fun v hv => ?_).symm
        have hav : a (s.erase v) = 0 := by
          by_contra hne
          exact (mem_badFaces.mp (ha _ hne).1).2 ((Finset.erase_subset v s).trans hsG)
        rw [hav, mul_zero]
    rw [heq]

omit [Fintype V] in
/-- Assuming the restrictions of the global cycle are nonzero at every face of
`K`, the top-row comparison map is injective on chains of `K`. -/
theorem phiMap_injective_on {K : Finset (Finset V)} {p : ℕ} {z : Finset V → ℝ}
    (hgen : ∀ s ∈ K, s.Nonempty → cofaceRestriction s z ≠ 0)
    {a b : Finset V → ℝ} (ha : a ∈ chains ℝ K p) (hb : b ∈ chains ℝ K p) (hp : p ≠ 0)
    (h : phiMap z a = phiMap z b) : a = b := by
  classical
  funext s
  by_contra hne
  have hor : a s ≠ 0 ∨ b s ≠ 0 := by
    by_cases h1 : a s = 0
    · exact Or.inr fun h2 => hne (by rw [h1, h2])
    · exact Or.inl h1
  have hsK : s ∈ K ∧ s.card = p := by
    rcases hor with h1 | h1
    · exact ha s h1
    · exact hb s h1
  have hs : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨t, ht⟩ : ∃ t, cofaceRestriction s z t ≠ 0 := by
    by_contra hcon
    refine hgen s hsK.1 hs (funext fun t => ?_)
    by_contra hne2
    exact hcon ⟨t, hne2⟩
  have h0 : a s * cofaceRestriction s z t = b s * cofaceRestriction s z t :=
    congrFun (congrFun h s) t
  exact hne (mul_right_cancel₀ ht h0)

/-- Assuming that the top cycles of every coface complex are spanned by the
restriction of the global cycle, every element of the top row is the image of a
relative cochain. -/
theorem exists_phiMap_of_mem_topChains {K : Finset (Finset V)} {G : Finset V} {Q k p : ℕ}
    (hpk : p + k = Q) {z : Finset V → ℝ}
    (hgen : ∀ s ∈ K, s.Nonempty → cofaceRestriction s z ≠ 0)
    (hspan : ∀ s ∈ K, s.Nonempty → ∀ x ∈ cofaceChains K s Q, cofaceBoundary s x = 0 →
      ∃ r : ℝ, x = r • cofaceRestriction s z)
    {y : Finset V → Finset V → ℝ} (hy : y ∈ topChains K G Q k) :
    ∃ a ∈ chains ℝ (badFaces K G) p, y = phiMap z a := by
  classical
  have hdv : ∀ s, cofaceBoundary s (y s) = 0 := fun s =>
    congrFun (LinearMap.mem_ker.mp hy.2) s
  have hmem : ∀ s, y s ∈ cofaceChains K s Q := by
    intro s t ht
    obtain ⟨⟨_, _, htK, hsub, _⟩, htcard⟩ := hy.1 s t ht
    exact ⟨Finset.mem_filter.mpr ⟨htK, hsub⟩, htcard⟩
  have hex : ∀ s, s ∈ K → s.Nonempty → ∃ r : ℝ, y s = r • cofaceRestriction s z :=
    fun s hsK hs => hspan s hsK hs (y s) (hmem s) (hdv s)
  refine ⟨fun s => if h : s ∈ K ∧ s.Nonempty then (hex s h.1 h.2).choose else 0, ?_, ?_⟩
  · intro s hs
    by_cases h : s ∈ K ∧ s.Nonempty
    · simp only [h, and_self, ↓reduceDIte] at hs
      have hys : y s ≠ 0 := by
        intro h0
        have hspec := (hex s h.1 h.2).choose_spec
        have hzz : (hex s h.1 h.2).choose • cofaceRestriction s z = 0 := by
          rw [← hspec]
          exact h0
        exact hgen s h.1 h.2 ((smul_eq_zero.mp hzz).resolve_left hs)
      obtain ⟨t, ht⟩ : ∃ t, y s t ≠ 0 := by
        by_contra hcon
        refine hys (funext fun t => ?_)
        by_contra hne
        exact hcon ⟨t, hne⟩
      obtain ⟨⟨hsK, hsG, _, _, hcard⟩, htcard⟩ := hy.1 s t ht
      exact ⟨mem_badFaces.mpr ⟨hsK, hsG⟩, by omega⟩
    · simp only [h, ↓reduceDIte] at hs
      exact absurd rfl hs
  · funext s t
    rw [phiMap_apply]
    by_cases h : s ∈ K ∧ s.Nonempty
    · simp only [h, and_self, ↓reduceDIte]
      have hspec := (hex s h.1 h.2).choose_spec
      have := congrFun hspec t
      simpa [cofaceRestriction_apply, smul_eq_mul] using this
    · simp only [h, ↓reduceDIte, zero_mul]
      by_contra hne
      obtain ⟨⟨hsK, hsG, _, hsub, _⟩, _⟩ := hy.1 s t hne
      refine h ⟨hsK, ?_⟩
      rcases Finset.eq_empty_or_nonempty s with rfl | hs
      · exact absurd (Finset.empty_subset G) hsG
      · exact hs

/-! ### The relative cochain complex is exact -/

/-- **Algebraic Alexander duality.**  If the induced subcomplex on the bad
vertices is reduced acyclic in cardinality degree `k + 1`, then the relative
cochain complex of the pair `(K, K[G])` is exact in cardinality degree
`q + 1 = Q - k`. -/
theorem exists_relCoboundary_of_relCocycle {K : Finset (Finset V)}
    (hK : FaceClosed K) {G : Finset V} {Q k q : ℕ} (hk : 1 ≤ k) (hpk : q + 1 + k = Q)
    (htop : ∀ t ∈ K, t.card ≤ Q)
    (hcol : ∀ s ∈ K, ∀ j, j ≠ Q → IsCofaceAcyclicAt K s j)
    {z : Finset V → ℝ} (hz : z ∈ cycles ℝ K Q)
    (hgen : ∀ s ∈ K, s.Nonempty → cofaceRestriction s z ≠ 0)
    (hspan : ∀ s ∈ K, s.Nonempty → ∀ x ∈ cofaceChains K s Q, cofaceBoundary s x = 0 →
      ∃ r : ℝ, x = r • cofaceRestriction s z)
    {L : Finset (Finset V)} (hL : ∀ s, s ∈ L ↔ s ∈ K ∧ ∀ v ∈ s, v ∉ G)
    (hbad : IsReducedAcyclicAt ℝ L (k + 1))
    {a : Finset V → ℝ} (ha : a ∈ chains ℝ (badFaces K G) (q + 1))
    (hcoc : relCoboundary K G a = 0) :
    ∃ b ∈ chains ℝ (badFaces K G) q, relCoboundary K G b = a := by
  classical
  set y := phiMap z a with hydef
  have hytop : y ∈ topChains K G Q k := phiMap_mem_topChains hpk hz ha
  have hycyc : dtotMap V y = 0 := by
    rw [hydef, dtotMap_phiMap_relCoboundary hK hz ha, hcoc, map_zero]
  -- first staircase
  obtain ⟨w, hw, b₁, hb₁, hyeq⟩ :=
    exists_rowChains_of_cycle hK (topChains_le_dblChains K G Q k hytop) hycyc
  have hLclosed : FaceClosed L := by
    intro u hu t hts
    obtain ⟨huK, huG⟩ := (hL u).mp hu
    exact (hL t).mpr ⟨hK u huK t hts, fun v hv => huG v (hts hv)⟩
  obtain ⟨x, hx, hwx⟩ := exists_psiMap_of_mem_rowChains hL hw
  -- `x` is a cycle of the bad subcomplex
  have hdtw : dtotMap V w = 0 := by
    have : dtotMap V w = dtotMap V y - dtotMap V (dtotMap V b₁) := by
      rw [hyeq, map_add]
      abel
    rw [this, hycyc, dtotMap_dtotMap, sub_zero]
  have hxcyc : boundary ℝ V x = 0 := by
    have h1 : psiMap V (boundary ℝ V x) = 0 := by
      have := hdtw
      rw [hwx, dtotMap_psiMap] at this
      simpa using this
    refine eq_zero_of_psiMap_eq_zero (fun t ht => ?_) h1
    have hb : boundary ℝ V x ∈ chains ℝ L k := boundary_mem_chains hLclosed hx
    have := (hb t ht).2
    exact Finset.card_pos.mp (by omega)
  -- fill it in using the acyclicity of the bad subcomplex
  obtain ⟨u, hu, hux⟩ := hbad ⟨hx, LinearMap.mem_ker.mpr hxcyc⟩
  have hpsiu : psiMap V u ∈ rowChains K G (k + 1) := psiMap_mem_rowChains hK hL hu
  have hyb : y = dtotMap V (b₁ - psiMap V u) := by
    rw [map_sub, dtotMap_psiMap, hux, ← hwx, hyeq]
    abel
  -- second staircase
  obtain ⟨y', hy', hyy'⟩ := dtotMap_topChains_of_mem hK htop hcol hytop
    (Submodule.sub_mem _ hb₁ (rowChains_le_dblChains K G (k + 1) hpsiu)) hyb
  obtain ⟨b, hb, hby⟩ := exists_phiMap_of_mem_topChains (p := q) (by omega) hgen hspan hy'
  refine ⟨b, hb, ?_⟩
  have hchain : ∀ c : Finset V → ℝ, c ∈ chains ℝ (badFaces K G) (q + 1) → c ∈ chains ℝ K (q + 1) :=
    fun c hc s hs => ⟨(mem_badFaces.mp (hc s hs).1).1, (hc s hs).2⟩
  refine phiMap_injective_on (p := q + 1) hgen
    (coboundaryOn_mem_chains hb |> hchain _) (hchain _ ha) (by omega) ?_
  rw [← dtotMap_phiMap_relCoboundary hK hz hb, ← hby, ← hyy', hydef]

/-- **The long exact sequence of the pair, made explicit.**  Relative
exactness in cardinality degree `q + 2`, together with acyclicity of `K` in
cardinality degree `q + 1`, gives reduced acyclicity of the induced subcomplex
`K[G]` in cardinality degree `q + 1`. -/
theorem isReducedAcyclicAt_inducedFaces_of_relExact {K : Finset (Finset V)}
    (hK : FaceClosed K) {G : Finset V} {q : ℕ}
    (hKac : IsReducedAcyclicAt ℝ K (q + 1))
    (hrel : ∀ a ∈ chains ℝ (badFaces K G) (q + 2), relCoboundary K G a = 0 →
      ∃ b ∈ chains ℝ (badFaces K G) (q + 1), relCoboundary K G b = a) :
    IsReducedAcyclicAt ℝ (inducedFaces K G) (q + 1) := by
  classical
  have hA : FaceClosed (inducedFaces K G) := faceClosed_inducedFaces hK G
  rw [← isCoacyclicAt_iff_isReducedAcyclicAt hA q]
  intro α hα hαco
  -- `δα` is a relative cocycle
  have hαK : α ∈ chains ℝ K (q + 1) := fun s hs =>
    ⟨(mem_inducedFaces.mp (hα s hs).1).1, (hα s hs).2⟩
  have hAsub : ∀ s ∈ inducedFaces K G, ∀ v ∈ s, s.erase v ∈ inducedFaces K G := by
    intro s hs v _
    obtain ⟨hsK, hsG⟩ := mem_inducedFaces.mp hs
    exact mem_inducedFaces.mpr ⟨hK s hsK _ (Finset.erase_subset v s),
      (Finset.erase_subset v s).trans hsG⟩
  have hr : coboundaryOn ℝ K α ∈ chains ℝ (badFaces K G) (q + 2) := by
    intro s hs
    have hsK : s ∈ K := by
      by_contra h
      rw [coboundaryOn_apply] at hs
      simp only [h, ↓reduceIte] at hs
      exact hs rfl
    have hcard := (coboundaryOn_mem_chains hαK s hs).2
    refine ⟨mem_badFaces.mpr ⟨hsK, ?_⟩, hcard⟩
    intro hsG
    have hsA : s ∈ inducedFaces K G := mem_inducedFaces.mpr ⟨hsK, hsG⟩
    have h0 : coboundaryOn ℝ (inducedFaces K G) α s = 0 := by rw [hαco]; rfl
    rw [coboundaryOn_apply] at h0 hs
    simp only [hsA, ↓reduceIte] at h0
    simp only [hsK, ↓reduceIte] at hs
    exact hs h0
  have hrco : relCoboundary K G (coboundaryOn ℝ K α) = 0 := by
    funext g
    rw [relCoboundary, coboundaryOn_apply]
    by_cases hg : g ∈ badFaces K G
    · simp only [hg, ↓reduceIte, coboundaryFun_apply]
      have hgK : g ∈ K := (mem_badFaces.mp hg).1
      have hstep : ∀ v ∈ g, orientedSign ℝ (g.erase v) v * coboundaryOn ℝ K α (g.erase v)
          = orientedSign ℝ (g.erase v) v * coboundaryFun ℝ V α (g.erase v) := by
        intro v hv
        rw [coboundaryOn_apply]
        simp only [hK g hgK _ (Finset.erase_subset v g), ↓reduceIte]
      rw [Finset.sum_congr rfl hstep]
      have := congrFun (coboundaryFun_coboundaryFun (𝕜 := ℝ) (V := V) α) g
      rw [coboundaryFun_apply] at this
      simpa using this
    · simp [hg]
  obtain ⟨b, hb, hbeq⟩ := hrel _ hr hrco
  -- `δ b` and `δ α` agree on all of `K`
  have hbK : b ∈ chains ℝ K (q + 1) := fun s hs =>
    ⟨(mem_badFaces.mp (hb s hs).1).1, (hb s hs).2⟩
  have hbrel : coboundaryOn ℝ K b = relCoboundary K G b := by
    funext g
    rw [relCoboundary, coboundaryOn_apply, coboundaryOn_apply]
    by_cases hg : g ∈ badFaces K G
    · simp only [hg, ↓reduceIte, (mem_badFaces.mp hg).1]
    · simp only [hg, ↓reduceIte]
      by_cases hgK : g ∈ K
      · simp only [hgK, ↓reduceIte, coboundaryFun_apply]
        have hgG : g ⊆ G := by
          by_contra h
          exact hg (mem_badFaces.mpr ⟨hgK, h⟩)
        refine Finset.sum_eq_zero fun v hv => ?_
        have hbv : b (g.erase v) = 0 := by
          by_contra hne
          exact (mem_badFaces.mp (hb _ hne).1).2 ((Finset.erase_subset v g).trans hgG)
        rw [hbv, mul_zero]
      · simp only [hgK, ↓reduceIte]
    -- `α - b` is a cocycle of `K`
  have hdiff : coboundaryOn ℝ K (α - b) = 0 := by
    rw [map_sub, hbrel, hbeq, sub_self]
  obtain ⟨γ, hγ, hγeq⟩ := (isCoacyclicAt_iff_isReducedAcyclicAt hK q).mpr hKac (α - b)
    (Submodule.sub_mem _ hαK hbK) hdiff
  refine ⟨restrictFamily (inducedFaces K G) γ, ?_, ?_⟩
  · intro s hs
    rw [restrictFamily_apply] at hs
    by_cases hsA : s ∈ inducedFaces K G
    · simp only [hsA, ↓reduceIte] at hs
      exact ⟨hsA, (hγ s hs).2⟩
    · simp only [hsA, ↓reduceIte] at hs
      exact absurd rfl hs
  · funext g
    rw [coboundaryOn_apply]
    by_cases hg : g ∈ inducedFaces K G
    · simp only [hg, ↓reduceIte, coboundaryFun_apply]
      have hstep : ∀ v ∈ g,
          orientedSign ℝ (g.erase v) v * restrictFamily (inducedFaces K G) γ (g.erase v)
            = orientedSign ℝ (g.erase v) v * γ (g.erase v) := by
        intro v hv
        rw [restrictFamily_apply]
        simp only [hAsub g hg v hv, ↓reduceIte]
      rw [Finset.sum_congr rfl hstep]
      have hval : coboundaryOn ℝ K γ g = (α - b) g := by rw [hγeq]
      rw [coboundaryOn_apply, coboundaryFun_apply] at hval
      simp only [(mem_inducedFaces.mp hg).1, ↓reduceIte] at hval
      have hbg : b g = 0 := by
        by_contra hne
        exact (mem_badFaces.mp (hb g hne).1).2 (mem_inducedFaces.mp hg).2
      rw [hval]
      simp only [Pi.sub_apply, hbg, sub_zero]
    · simp only [hg, ↓reduceIte]
      by_contra hne
      exact hg (hα g (Ne.symm hne)).1

end AffineTverberg.Simplicial
