import AffineTverberg.GeometricComplex

set_option linter.style.header false

/-!
# The general barycentric subdivision of a finite geometric complex

For an arbitrary finite face family `K : Finset (Finset V)` the *barycentric
subdivision* has as vertices the nonempty faces of `K` and as faces the chains
of nonempty faces of `K`.  Geometrically a face `s` is placed at the barycenter
`faceBarycenter p s` of its geometric vertices.

The main results are:

* `faceClosed_subdivisionFaces`, `subdivisionFaces_mono` — the subdivision is a
  face family, monotone in the complex;
* `isGeometricRealization_subdivisionFaces` — the barycenters realize the
  subdivision as an actual geometric simplicial complex, whenever `p` realizes
  `K`;
* `geometricCarrier_subdivisionFaces` — `|sd K| = |K|`, and the same for every
  face-closed subfamily, so subdivision is compatible with subcomplexes.

The combinatorial heart is the fact that a point of `|sd K|` remembers the chain
carrying it: for a chain with strictly positive weights the resulting
barycentric coordinate vector has the chain as its family of superlevel sets
(`levelSets_eq_of_chainCombination`).
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg.Simplicial

variable {V : Type*} [DecidableEq V]

/-! ### Chains of faces -/

/-- A finite family of nonempty faces which is totally ordered by inclusion. -/
def IsFaceChain (C : Finset (Finset V)) : Prop :=
  (∀ s ∈ C, s.Nonempty) ∧ ∀ s ∈ C, ∀ t ∈ C, s ⊆ t ∨ t ⊆ s

instance (C : Finset (Finset V)) : Decidable (IsFaceChain C) := by
  unfold IsFaceChain; infer_instance

omit [DecidableEq V] in
theorem IsFaceChain.mono {C D : Finset (Finset V)} (hC : IsFaceChain C) (hDC : D ⊆ C) :
    IsFaceChain D :=
  ⟨fun s hs ↦ hC.1 s (hDC hs), fun s hs t ht ↦ hC.2 s (hDC hs) t (hDC ht)⟩

omit [DecidableEq V] in
/-- A nonempty chain has a greatest element. -/
theorem IsFaceChain.exists_max {C : Finset (Finset V)} (hC : IsFaceChain C)
    (hne : C.Nonempty) : ∃ t ∈ C, ∀ s ∈ C, s ⊆ t := by
  obtain ⟨t, hmax⟩ := C.exists_maximal hne
  refine ⟨t, hmax.1, fun s hs ↦ ?_⟩
  rcases hC.2 s hs t hmax.1 with h | h
  · exact h
  · exact hmax.2 hs h

omit [DecidableEq V] in
/-- A nonempty chain has a least element. -/
theorem IsFaceChain.exists_min {C : Finset (Finset V)} (hC : IsFaceChain C)
    (hne : C.Nonempty) : ∃ t ∈ C, ∀ s ∈ C, t ⊆ s := by
  obtain ⟨t, hmin⟩ := C.exists_minimal hne
  refine ⟨t, hmin.1, fun s hs ↦ ?_⟩
  rcases hC.2 s hs t hmin.1 with h | h
  · exact hmin.2 hs h
  · exact h

/-- The faces of the barycentric subdivision: the chains of nonempty faces. -/
def subdivisionFaces (K : Finset (Finset V)) : Finset (Finset (Finset V)) :=
  K.powerset.filter IsFaceChain

@[simp]
theorem mem_subdivisionFaces {K : Finset (Finset V)} {C : Finset (Finset V)} :
    C ∈ subdivisionFaces K ↔ C ⊆ K ∧ IsFaceChain C := by
  simp [subdivisionFaces, Finset.mem_powerset]

theorem faceClosed_subdivisionFaces (K : Finset (Finset V)) :
    FaceClosed (subdivisionFaces K) := by
  intro C hC D hDC
  obtain ⟨hCK, hchain⟩ := mem_subdivisionFaces.mp hC
  exact mem_subdivisionFaces.mpr ⟨hDC.trans hCK, hchain.mono hDC⟩

theorem subdivisionFaces_mono {K L : Finset (Finset V)} (hLK : L ⊆ K) :
    subdivisionFaces L ⊆ subdivisionFaces K := by
  intro C hC
  obtain ⟨hCK, hchain⟩ := mem_subdivisionFaces.mp hC
  exact mem_subdivisionFaces.mpr ⟨hCK.trans hLK, hchain⟩

/-! ### Barycenters -/

/-- The uniform barycentric coordinate vector of a face. -/
def uniformCoord (s : Finset V) : V → ℝ := fun v ↦ if v ∈ s then ((s.card : ℝ))⁻¹ else 0

theorem uniformCoord_nonneg (s : Finset V) (v : V) : 0 ≤ uniformCoord s v := by
  unfold uniformCoord; split <;> positivity

theorem uniformCoord_eq_zero {s : Finset V} {v : V} (hv : v ∉ s) : uniformCoord s v = 0 := by
  simp [uniformCoord, hv]

theorem uniformCoord_pos {s : Finset V} {v : V} (hv : v ∈ s) : 0 < uniformCoord s v := by
  have : 0 < s.card := Finset.card_pos.mpr ⟨v, hv⟩
  simp only [uniformCoord, ite_eq_left hv]
  positivity

theorem sum_uniformCoord_face {s : Finset V} (hs : s.Nonempty) :
    ∑ v ∈ s, uniformCoord s v = 1 := by
  have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem hs.choose_spec)
  simp only [uniformCoord]
  rw [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem sum_uniformCoord_subset {t T : Finset V} (htT : t ⊆ T) (ht : t.Nonempty) :
    ∑ v ∈ T, uniformCoord t v = 1 := by
  rw [← Finset.sum_subset htT (fun v _ hv ↦ uniformCoord_eq_zero hv)]
  exact sum_uniformCoord_face ht

/-- The convex combination of the uniform coordinate vectors of a chain. -/
def chainCombination (C : Finset (Finset V)) (a : Finset V → ℝ) : V → ℝ :=
  ∑ t ∈ C, a t • uniformCoord t

theorem chainCombination_apply (C : Finset (Finset V)) (a : Finset V → ℝ) (v : V) :
    chainCombination C a v = ∑ t ∈ C, a t * uniformCoord t v := by
  simp [chainCombination, Finset.sum_apply]

theorem chainCombination_nonneg {C : Finset (Finset V)} {a : Finset V → ℝ}
    (ha : ∀ t ∈ C, 0 ≤ a t) (v : V) : 0 ≤ chainCombination C a v := by
  rw [chainCombination_apply]
  exact Finset.sum_nonneg fun t ht ↦ mul_nonneg (ha t ht) (uniformCoord_nonneg t v)

theorem chainCombination_eq_zero {C : Finset (Finset V)} {a : Finset V → ℝ} {v : V}
    (hv : ∀ t ∈ C, v ∉ t) : chainCombination C a v = 0 := by
  rw [chainCombination_apply]
  exact Finset.sum_eq_zero fun t ht ↦ by rw [uniformCoord_eq_zero (hv t ht), mul_zero]

/-- Strict separation: a coordinate inside a member of the chain strictly
dominates every coordinate outside it. -/
theorem chainCombination_lt {C : Finset (Finset V)} (hC : IsFaceChain C)
    {a : Finset V → ℝ} (hpos : ∀ t ∈ C, 0 < a t)
    {s : Finset V} (hs : s ∈ C) {v u : V} (hv : v ∈ s) (hu : u ∉ s) :
    chainCombination C a u < chainCombination C a v := by
  rw [chainCombination_apply, chainCombination_apply]
  refine Finset.sum_lt_sum (fun t ht ↦ ?_) ⟨s, hs, ?_⟩
  · by_cases hut : u ∈ t
    · have hvt : v ∈ t := by
        rcases hC.2 t ht s hs with h | h
        · exact absurd (h hut) hu
        · exact h hv
      rw [show uniformCoord t u = uniformCoord t v by simp [uniformCoord, hut, hvt]]
    · rw [uniformCoord_eq_zero hut, mul_zero]
      exact mul_nonneg (hpos t ht).le (uniformCoord_nonneg t v)
  · rw [uniformCoord_eq_zero hu, mul_zero]
    exact mul_pos (hpos s hs) (uniformCoord_pos hv)

/-- Membership in a member of the chain is monotone for the coordinate values. -/
theorem chainCombination_le {C : Finset (Finset V)}
    {a : Finset V → ℝ} (ha : ∀ t ∈ C, 0 ≤ a t) {u v : V}
    (huv : ∀ t ∈ C, u ∈ t → v ∈ t) :
    chainCombination C a u ≤ chainCombination C a v := by
  rw [chainCombination_apply, chainCombination_apply]
  refine Finset.sum_le_sum fun t ht ↦ ?_
  by_cases hut : u ∈ t
  · rw [show uniformCoord t u = uniformCoord t v by
      simp [uniformCoord, hut, huv t ht hut]]
  · rw [uniformCoord_eq_zero hut, mul_zero]
    exact mul_nonneg (ha t ht) (uniformCoord_nonneg t v)

section Geometric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The barycenter of the geometric vertices of a face. -/
def faceBarycenter (p : V → E) (s : Finset V) : E := ((s.card : ℝ))⁻¹ • ∑ v ∈ s, p v

omit [DecidableEq V] in
theorem faceBarycenter_mem_convexHull (p : V → E) {s : Finset V} (hs : s.Nonempty) :
    faceBarycenter p s ∈ convexHull ℝ (p '' (s : Set V)) := by
  have := Finset.centerMass_mem_convexHull (R := ℝ) (s := p '' (s : Set V)) s
    (w := fun _ ↦ (1 : ℝ)) (fun i _ ↦ zero_le_one) (by simpa using Finset.card_pos.mpr hs)
    (z := p) (fun i hi ↦ Set.mem_image_of_mem p hi)
  simpa [Finset.centerMass, faceBarycenter] using this

end Geometric

section Fintype

variable [Fintype V]

theorem sum_uniformCoord {s : Finset V} (hs : s.Nonempty) : ∑ v, uniformCoord s v = 1 := by
  rw [← sum_uniformCoord_face hs]
  exact (Finset.sum_subset (Finset.subset_univ s)
    (fun v _ hv ↦ uniformCoord_eq_zero hv)).symm

theorem uniformCoord_mem_barycentricFace (s : Finset V) (hs : s.Nonempty) :
    uniformCoord s ∈ barycentricFace s :=
  ⟨uniformCoord_nonneg s, sum_uniformCoord hs, fun _ hv ↦ uniformCoord_eq_zero hv⟩

theorem sum_chainCombination {C : Finset (Finset V)} {a : Finset V → ℝ}
    (hC : IsFaceChain C) (hsum : ∑ t ∈ C, a t = 1) :
    ∑ v, chainCombination C a v = 1 := by
  simp only [chainCombination_apply]
  rw [Finset.sum_comm]
  rw [← hsum]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  rw [← Finset.mul_sum, sum_uniformCoord (hC.1 t ht), mul_one]

/-- The superlevel set of `mu` at the value `mu w`. -/
def levelSet (mu : V → ℝ) (w : V) : Finset V := Finset.univ.filter fun v ↦ mu w ≤ mu v

/-- All positive superlevel sets of a coordinate vector. -/
def levelSets (mu : V → ℝ) : Finset (Finset V) :=
  (Finset.univ.filter fun w ↦ 0 < mu w).image (levelSet mu)

omit [Fintype V] in
/-- The chain is recovered from the coordinate vector as its family of
positive superlevel sets. -/
theorem chainCombination_pos {C : Finset (Finset V)} {a : Finset V → ℝ}
    (hpos : ∀ t ∈ C, 0 < a t) {s : Finset V} (hs : s ∈ C) {v : V} (hv : v ∈ s) :
    0 < chainCombination C a v := by
  classical
  rw [chainCombination_apply, ← Finset.add_sum_erase C (fun t ↦ a t * uniformCoord t v) hs]
  refine add_pos_of_pos_of_nonneg (mul_pos (hpos s hs) (uniformCoord_pos hv))
    (Finset.sum_nonneg fun t ht ↦
      mul_nonneg (hpos t (Finset.mem_of_mem_erase ht)).le (uniformCoord_nonneg t v))

theorem levelSets_eq_of_chainCombination {C : Finset (Finset V)} (hC : IsFaceChain C)
    {a : Finset V → ℝ} (hpos : ∀ t ∈ C, 0 < a t) :
    levelSets (chainCombination C a) = C := by
  classical
  set mu := chainCombination C a with hmu
  have hposmu : ∀ s ∈ C, ∀ v ∈ s, 0 < mu v := fun s hs v hv ↦
    chainCombination_pos hpos hs hv
  apply Finset.ext
  intro s
  constructor
  · intro hs
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hs
    have hwpos : 0 < mu w := (Finset.mem_filter.mp hw).2
    -- `w` lies in some member of the chain
    have hex : ∃ t ∈ C, w ∈ t := by
      by_contra hcon
      push Not at hcon
      exact absurd (chainCombination_eq_zero (C := C) (a := a) hcon) (ne_of_gt hwpos)
    obtain ⟨t₀, ht₀, hwt₀⟩ := hex
    have hCwne : (C.filter fun t ↦ w ∈ t).Nonempty := ⟨t₀, Finset.mem_filter.mpr ⟨ht₀, hwt₀⟩⟩
    obtain ⟨s₀, hs₀, hmin⟩ := (hC.mono (Finset.filter_subset _ _)).exists_min hCwne
    have hs₀C : s₀ ∈ C := (Finset.mem_filter.mp hs₀).1
    have hws₀ : w ∈ s₀ := (Finset.mem_filter.mp hs₀).2
    have : levelSet mu w = s₀ := by
      apply Finset.ext
      intro v
      simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hle
        by_contra hv
        exact absurd hle (not_le.mpr (chainCombination_lt hC hpos hs₀C hws₀ hv))
      · intro hv
        refine chainCombination_le (fun t ht ↦ (hpos t ht).le) ?_
        intro t ht hwt
        exact hmin t (Finset.mem_filter.mpr ⟨ht, hwt⟩) hv
    rw [this]
    exact hs₀C
  · intro hs
    obtain ⟨w, hws, hwmin⟩ := Finset.exists_min_image s mu (hC.1 s hs)
    refine Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hposmu s hs w hws⟩, ?_⟩
    apply Finset.ext
    intro v
    simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hle
      by_contra hv
      exact absurd hle (not_le.mpr (chainCombination_lt hC hpos hs hws hv))
    · intro hv
      exact hwmin v hv

/-- The vertices carrying a strictly positive coordinate. -/
def posSupport (lam : V → ℝ) : Finset V := Finset.univ.filter fun v ↦ 0 < lam v

omit [DecidableEq V] in
@[simp]
theorem mem_posSupport {lam : V → ℝ} {v : V} : v ∈ posSupport lam ↔ 0 < lam v := by
  simp [posSupport]

omit [DecidableEq V] in
theorem eq_zero_of_notMem_posSupport {lam : V → ℝ} (h0 : ∀ v, 0 ≤ lam v) {v : V}
    (hv : v ∉ posSupport lam) : lam v = 0 :=
  le_antisymm (not_lt.mp fun h ↦ hv (mem_posSupport.mpr h)) (h0 v)

omit [DecidableEq V] in
theorem sum_posSupport {lam : V → ℝ} (h0 : ∀ v, 0 ≤ lam v) :
    ∑ v ∈ posSupport lam, lam v = ∑ v, lam v :=
  Finset.sum_subset (Finset.subset_univ _)
    (fun _ _ hv ↦ eq_zero_of_notMem_posSupport h0 hv)

private theorem exists_chain_decomposition_aux (n : ℕ) : ∀ lam : V → ℝ, (∀ v, 0 ≤ lam v) →
    (∑ v, lam v = 1) → (posSupport lam).card ≤ n →
    ∃ (C : Finset (Finset V)) (a : Finset V → ℝ), IsFaceChain C ∧
      (∀ t ∈ C, t ⊆ posSupport lam) ∧ (∀ t ∈ C, 0 ≤ a t) ∧ (∑ t ∈ C, a t = 1) ∧
      chainCombination C a = lam := by
  induction n with
  | zero =>
      intro lam h0 h1 hcard
      exfalso
      have hempty : posSupport lam = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      have hzero : ∑ v, lam v = 0 := Finset.sum_eq_zero fun v _ ↦
        eq_zero_of_notMem_posSupport h0 (by rw [hempty]; exact Finset.notMem_empty v)
      rw [h1] at hzero
      exact one_ne_zero hzero
  | succ n ih =>
      intro lam h0 h1 hcard
      set T := posSupport lam with hT
      have hTne : T.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hempty
        have hzero : ∑ v, lam v = 0 := Finset.sum_eq_zero fun v _ ↦
          eq_zero_of_notMem_posSupport h0 (by rw [← hT, hempty]; exact Finset.notMem_empty v)
        rw [h1] at hzero; exact one_ne_zero hzero
      obtain ⟨w, hwT, hwmin⟩ := Finset.exists_min_image T lam hTne
      have hmpos : 0 < lam w := mem_posSupport.mp hwT
      have hsumT : ∑ v ∈ T, lam v = 1 := by rw [hT, sum_posSupport h0, h1]
      have hcardpos : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hTne
      have hconstsum : (T.card : ℝ) * lam w = ∑ _v ∈ T, lam w := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have hcardm : (T.card : ℝ) * lam w ≤ 1 := by
        rw [hconstsum, ← hsumT]
        exact Finset.sum_le_sum fun v hv ↦ hwmin v hv
      by_cases hc : (T.card : ℝ) * lam w = 1
      · -- the coordinates are constant on their support
        have hconst : ∀ v ∈ T, lam v = lam w := by
          by_contra hcon
          push Not at hcon
          obtain ⟨v₀, hv₀T, hv₀⟩ := hcon
          have hlt : (T.card : ℝ) * lam w < ∑ v ∈ T, lam v := by
            rw [hconstsum]
            exact Finset.sum_lt_sum (fun v hv ↦ hwmin v hv)
              ⟨v₀, hv₀T, lt_of_le_of_ne (hwmin v₀ hv₀T) (Ne.symm hv₀)⟩
          rw [hsumT, hc] at hlt
          exact lt_irrefl _ hlt
        have hmval : lam w = ((T.card : ℝ))⁻¹ := by
          field_simp
          linarith [hc]
        refine ⟨{T}, fun _ ↦ 1, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
        · intro u hu; rw [Finset.mem_singleton.mp hu]; exact hTne
        · intro u hu v hv
          rw [Finset.mem_singleton.mp hu, Finset.mem_singleton.mp hv]
          exact Or.inl Finset.Subset.rfl
        · intro u hu; rw [Finset.mem_singleton.mp hu]
        · intro u _; exact zero_le_one
        · simp
        · funext v
          rw [chainCombination, Finset.sum_singleton, Pi.smul_apply, one_smul]
          by_cases hv : v ∈ T
          · rw [uniformCoord, ite_eq_left hv, ← hmval, hconst v hv]
          · rw [uniformCoord_eq_zero hv, eq_zero_of_notMem_posSupport h0 (hT ▸ hv)]
      · -- strip off the uniform vector of the support and recurse
        have hcpos : 0 < 1 - (T.card : ℝ) * lam w := by
          rcases lt_or_eq_of_le hcardm with h | h
          · linarith
          · exact absurd h hc
        set c := 1 - (T.card : ℝ) * lam w with hcdef
        have hcne : c ≠ 0 := ne_of_gt hcpos
        set lam' : V → ℝ := fun v ↦ c⁻¹ * (lam v - if v ∈ T then lam w else 0) with hlam'
        have hlam'apply : ∀ v, lam' v = c⁻¹ * (lam v - if v ∈ T then lam w else 0) :=
          fun v ↦ rfl
        have hlam'0 : ∀ v, 0 ≤ lam' v := by
          intro v
          rw [hlam'apply v]
          by_cases hv : v ∈ T
          · rw [ite_eq_left hv]
            exact mul_nonneg (by positivity) (by linarith [hwmin v hv])
          · rw [ite_eq_right hv, sub_zero]
            exact mul_nonneg (by positivity) (h0 v)
        have hlam'1 : ∑ v, lam' v = 1 := by
          have hstep : ∀ v, lam' v = c⁻¹ * lam v - c⁻¹ * (if v ∈ T then lam w else 0) :=
            fun v ↦ by rw [hlam'apply v]; ring
          rw [Finset.sum_congr rfl (fun v _ ↦ hstep v), Finset.sum_sub_distrib,
            ← Finset.mul_sum, h1, ← Finset.mul_sum,
            show (∑ v, if v ∈ T then lam w else 0) = (T.card : ℝ) * lam w by
              rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul],
            show c⁻¹ * 1 - c⁻¹ * ((T.card : ℝ) * lam w) = c⁻¹ * c by rw [hcdef]; ring,
            inv_mul_cancel₀ hcne]
        have hlam'w : lam' w = 0 := by
          rw [hlam'apply w, ite_eq_left hwT, sub_self, mul_zero]
        have hsub : posSupport lam' ⊆ T.erase w := by
          intro v hv
          have hpos : 0 < lam' v := mem_posSupport.mp hv
          have hvT : v ∈ T := by
            by_contra hvT
            rw [hlam'apply v, ite_eq_right hvT, sub_zero,
              eq_zero_of_notMem_posSupport h0 (hT ▸ hvT), mul_zero] at hpos
            exact lt_irrefl _ hpos
          refine Finset.mem_erase.mpr ⟨?_, hvT⟩
          intro hvw
          rw [hvw, hlam'w] at hpos
          exact lt_irrefl _ hpos
        have hcard' : (posSupport lam').card ≤ n := by
          have h1' := Finset.card_le_card hsub
          have h2' : (T.erase w).card = T.card - 1 := Finset.card_erase_of_mem hwT
          have h3' : 1 ≤ T.card := Finset.card_pos.mpr hTne
          have h4' : T.card ≤ n + 1 := hcard
          omega
        obtain ⟨C', a', hchain', hsub', ha'0, ha'1, hcomb'⟩ := ih lam' hlam'0 hlam'1 hcard'
        have hsubT : ∀ x ∈ C', x ⊆ T.erase w := fun x hx ↦ (hsub' x hx).trans hsub
        have hTnotmem : T ∉ C' := fun hTC' ↦
          (Finset.notMem_erase w T) (hsubT T hTC' hwT)
        set A : Finset V → ℝ := fun t ↦ if t = T then (T.card : ℝ) * lam w else c * a' t
          with hA
        have hAT : A T = (T.card : ℝ) * lam w := by rw [hA]; simp
        have hAC : ∀ t ∈ C', A t = c * a' t := by
          intro t ht
          have hne : t ≠ T := fun he ↦ hTnotmem (he ▸ ht)
          rw [hA]; simp [hne]
        refine ⟨insert T C', A, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
        · intro u hu
          rcases Finset.mem_insert.mp hu with hu | hu
          · exact hu ▸ hTne
          · exact hchain'.1 u hu
        · intro u hu v hv
          have hle : ∀ x ∈ C', x ⊆ T := fun x hx ↦ (hsubT x hx).trans (T.erase_subset w)
          rcases Finset.mem_insert.mp hu with hu | hu
          · rcases Finset.mem_insert.mp hv with hv | hv
            · exact Or.inl (hu.trans hv.symm).subset
            · exact Or.inr (hu ▸ hle v hv)
          · rcases Finset.mem_insert.mp hv with hv | hv
            · exact Or.inl (hv ▸ hle u hu)
            · exact hchain'.2 u hu v hv
        · intro u hu
          rcases Finset.mem_insert.mp hu with hu | hu
          · exact hu ▸ Finset.Subset.rfl
          · exact (hsubT u hu).trans (T.erase_subset w)
        · intro u hu
          rcases Finset.mem_insert.mp hu with hu | hu
          · rw [hu, hAT]; positivity
          · rw [hAC u hu]
            exact mul_nonneg hcpos.le (ha'0 u hu)
        · rw [Finset.sum_insert hTnotmem, hAT, Finset.sum_congr rfl hAC, ← Finset.mul_sum,
            ha'1, mul_one, hcdef]
          ring
        · funext v
          rw [chainCombination, Finset.sum_apply, Finset.sum_insert hTnotmem]
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [hAT, Finset.sum_congr rfl (fun t ht ↦ by rw [hAC t ht])]
          have hrest : ∑ t ∈ C', c * a' t * uniformCoord t v = c * lam' v := by
            rw [← hcomb', chainCombination_apply, Finset.mul_sum]
            exact Finset.sum_congr rfl fun t _ ↦ by ring
          rw [hrest, hlam'apply v]
          have hcardne : (T.card : ℝ) ≠ 0 := ne_of_gt hcardpos
          by_cases hv : v ∈ T
          · rw [uniformCoord, ite_eq_left hv, ite_eq_left hv]
            rw [show (T.card : ℝ) * lam w * ((T.card : ℝ))⁻¹ = lam w by field_simp,
              show c * (c⁻¹ * (lam v - lam w)) = lam v - lam w by field_simp]
            ring
          · rw [uniformCoord_eq_zero hv, ite_eq_right hv]
            rw [show c * (c⁻¹ * (lam v - 0)) = lam v by
              rw [sub_zero, ← mul_assoc, mul_inv_cancel₀ hcne, one_mul]]
            ring

/-- Every barycentric coordinate vector supported on a face is a convex
combination of the uniform vectors of a chain of subsets of that face. -/
theorem exists_chain_decomposition {s : Finset V} {lam : V → ℝ}
    (h0 : ∀ v, 0 ≤ lam v) (h1 : ∑ v, lam v = 1) (hsupp : ∀ v, v ∉ s → lam v = 0) :
    ∃ (C : Finset (Finset V)) (a : Finset V → ℝ), IsFaceChain C ∧ (∀ t ∈ C, t ⊆ s) ∧
      (∀ t ∈ C, 0 ≤ a t) ∧ (∑ t ∈ C, a t = 1) ∧ chainCombination C a = lam := by
  obtain ⟨C, a, hchain, hsub, ha0, ha1, hcomb⟩ :=
    exists_chain_decomposition_aux (posSupport lam).card lam h0 h1 le_rfl
  refine ⟨C, a, hchain, fun t ht ↦ (hsub t ht).trans ?_, ha0, ha1, hcomb⟩
  intro v hv
  by_contra hvs
  exact absurd (hsupp v hvs) (ne_of_gt (mem_posSupport.mp hv))

section Geometric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem barycentricEvaluation_uniformCoord (p : V → E) (s : Finset V) :
    barycentricEvaluation p (uniformCoord s) = faceBarycenter p s := by
  change ∑ v, uniformCoord s v • p v = faceBarycenter p s
  rw [← Finset.sum_subset (Finset.subset_univ s)
    (fun v _ hv ↦ by rw [uniformCoord_eq_zero hv, zero_smul])]
  simp only [faceBarycenter, Finset.smul_sum, uniformCoord]
  exact Finset.sum_congr rfl fun v hv ↦ by rw [ite_eq_left hv]

end Geometric

end Fintype

/-- Two chains with strictly positive weights producing the same point coincide. -/
theorem eq_of_chainCombination_eq [Finite V] {C D : Finset (Finset V)} (hC : IsFaceChain C)
    (hD : IsFaceChain D) {a b : Finset V → ℝ} (hposa : ∀ t ∈ C, 0 < a t)
    (hposb : ∀ t ∈ D, 0 < b t)
    (heq : chainCombination C a = chainCombination D b) : C = D := by
  let _ : Fintype V := Fintype.ofFinite V
  rw [← levelSets_eq_of_chainCombination hC hposa,
    ← levelSets_eq_of_chainCombination hD hposb, heq]

end AffineTverberg.Simplicial

end
