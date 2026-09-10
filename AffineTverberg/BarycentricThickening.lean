import AffineTverberg.BarycentricOpenCover
import Mathlib.Topology.Homotopy.Equiv

set_option linter.style.header false

/-!
# Puncturing a maximal face: the open thickening of a subcomplex

Let `K` be a finite face-closed family and let `s ∈ K` be a nonempty *maximal*
face. Deleting the barycenter `faceCenter s` from the barycentric realization
of `K` produces an open subset which deformation retracts onto the realization
of `K.erase s`, by radial projection away from the barycenter inside the closed
simplex of `s`.

This is the thickening step needed to run a Mayer-Vietoris induction over the
faces of `K`: together with the (contractible) open star of `s`, the punctured
realization is an *open* cover of the realization of `K`.

Everything is proved for the actual barycentric realization; no comparison or
excision statement is assumed.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg.Simplicial

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The minimal coordinate on a face -/

/-- The smallest barycentric coordinate of `x` among the vertices of `s`. -/
def minOn (s : Finset V) (hs : s.Nonempty) (x : V → ℝ) : ℝ := s.inf' hs x

omit [Fintype V] [DecidableEq V] in
theorem continuous_minOn (s : Finset V) (hs : s.Nonempty) :
    Continuous (fun x : V → ℝ => minOn s hs x) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa [minOn] using continuous_apply a
  | cons a t ha ht ih =>
    have key : ∀ x : V → ℝ,
        minOn (Finset.cons a t ha) (by simp) x = min (x a) (minOn t ht x) :=
      fun x => Finset.inf'_cons ht x
    simp only [key]
    exact (continuous_apply a).min ih

omit [Fintype V] [DecidableEq V] in
theorem minOn_le {s : Finset V} (hs : s.Nonempty) {v : V} (hv : v ∈ s) (x : V → ℝ) :
    minOn s hs x ≤ x v := Finset.inf'_le _ hv

omit [Fintype V] [DecidableEq V] in
theorem exists_eq_minOn {s : Finset V} (hs : s.Nonempty) (x : V → ℝ) :
    ∃ v ∈ s, x v = minOn s hs x := by
  obtain ⟨v, hv, h⟩ := Finset.exists_mem_eq_inf' hs x
  exact ⟨v, hv, h.symm⟩

omit [Fintype V] [DecidableEq V] in
theorem minOn_nonneg {s : Finset V} (hs : s.Nonempty) {x : V → ℝ} (h0 : ∀ v, 0 ≤ x v) :
    0 ≤ minOn s hs x := by
  obtain ⟨v, _, hv⟩ := exists_eq_minOn hs x
  rw [← hv]
  exact h0 v

omit [DecidableEq V] in
theorem card_mul_minOn_le_one {s : Finset V} (hs : s.Nonempty) {x : V → ℝ}
    (h0 : ∀ v, 0 ≤ x v) (h1 : (∑ v, x v) = 1) : (s.card : ℝ) * minOn s hs x ≤ 1 := by
  have hsum : ∑ v ∈ s, minOn s hs x ≤ ∑ v ∈ s, x v :=
    Finset.sum_le_sum fun v hv => minOn_le hs hv x
  have hle : ∑ v ∈ s, x v ≤ ∑ v, x v :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun v _ _ => h0 v
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  linarith [h1 ▸ hle]

/-- If the minimal coordinate on `s` is as large as possible, the point is the
barycenter of `s`. -/
theorem eq_faceCenter_of_card_mul_minOn {s : Finset V} (hs : s.Nonempty) {x : V → ℝ}
    (h0 : ∀ v, 0 ≤ x v) (h1 : (∑ v, x v) = 1) (h : (s.card : ℝ) * minOn s hs x = 1) :
    x = faceCenter s := by
  classical
  set m := minOn s hs x with hm
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  have hmval : m = (s.card : ℝ)⁻¹ := by
    field_simp at h ⊢
    linarith [h]
  have hsum_s : ∑ v ∈ s, x v = 1 := by
    have hge : ∑ v ∈ s, m ≤ ∑ v ∈ s, x v :=
      Finset.sum_le_sum fun v hv => minOn_le hs hv x
    have hle : ∑ v ∈ s, x v ≤ ∑ v, x v :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun v _ _ => h0 v
    simp only [Finset.sum_const, nsmul_eq_mul] at hge
    rw [h1] at hle
    linarith [h ▸ hge]
  have houtside : ∀ v ∉ s, x v = 0 := by
    intro v hv
    have hsplit : ∑ w ∈ s, x w + ∑ w ∈ Finset.univ \ s, x w = ∑ w, x w :=
      Finset.sum_add_sum_compl s x
    have hrest : ∑ w ∈ Finset.univ \ s, x w = 0 := by
      rw [h1] at hsplit; linarith [hsum_s ▸ hsplit]
    have hmemc : v ∈ Finset.univ \ s := by simp [hv]
    have hnonneg : ∀ w ∈ Finset.univ \ s, 0 ≤ x w := fun w _ => h0 w
    exact le_antisymm ((Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hrest v hmemc).le (h0 v)
  have hinside : ∀ v ∈ s, x v = m := by
    intro v hv
    by_contra hne
    have hlt : m < x v := lt_of_le_of_ne (minOn_le hs hv x) (Ne.symm hne)
    have hstrict : ∑ w ∈ s, m < ∑ w ∈ s, x w :=
      Finset.sum_lt_sum (fun w hw => minOn_le hs hw x) ⟨v, hv, hlt⟩
    simp only [Finset.sum_const, nsmul_eq_mul] at hstrict
    rw [h, hsum_s] at hstrict
    exact lt_irrefl 1 hstrict
  funext v
  by_cases hv : v ∈ s
  · rw [hinside v hv, hmval]
    simp [faceCenter, hv]
  · rw [houtside v hv]
    simp [faceCenter, hv]

theorem card_mul_minOn_lt_one {s : Finset V} (hs : s.Nonempty) {x : V → ℝ}
    (h0 : ∀ v, 0 ≤ x v) (h1 : (∑ v, x v) = 1) (hne : x ≠ faceCenter s) :
    (s.card : ℝ) * minOn s hs x < 1 :=
  lt_of_le_of_ne (card_mul_minOn_le_one hs h0 h1) fun h =>
    hne (eq_faceCenter_of_card_mul_minOn hs h0 h1 h)

/-! ### The radial retraction away from the barycenter -/

/-- The scaling factor of the radial projection away from the barycenter of `s`. -/
def radialScale (s : Finset V) (hs : s.Nonempty) (x : V → ℝ) : ℝ :=
  (1 - s.card * minOn s hs x)⁻¹

/-- The radial projection of `x` away from the barycenter of `s` onto the part
of the realization not meeting the open simplex of `s`. -/
def radialRetract (s : Finset V) (hs : s.Nonempty) (x : V → ℝ) : V → ℝ :=
  fun v => radialScale s hs x * (x v - if v ∈ s then minOn s hs x else 0)

omit [Fintype V] [DecidableEq V] in
theorem radialScale_pos {s : Finset V} (hs : s.Nonempty) {x : V → ℝ}
    (hlt : (s.card : ℝ) * minOn s hs x < 1) : 0 < radialScale s hs x :=
  inv_pos.mpr (by linarith)

omit [Fintype V] [DecidableEq V] in
theorem radialScale_mul {s : Finset V} (hs : s.Nonempty) {x : V → ℝ}
    (hlt : (s.card : ℝ) * minOn s hs x < 1) :
    radialScale s hs x * (1 - s.card * minOn s hs x) = 1 :=
  inv_mul_cancel₀ (by linarith)

omit [Fintype V] in
theorem radialRetract_nonneg {s : Finset V} (hs : s.Nonempty) {x : V → ℝ}
    (h0 : ∀ v, 0 ≤ x v) (hlt : (s.card : ℝ) * minOn s hs x < 1) (v : V) :
    0 ≤ radialRetract s hs x v := by
  have hpos := (radialScale_pos hs hlt).le
  by_cases hv : v ∈ s
  · simp only [radialRetract, hv, ite_true]
    exact mul_nonneg hpos (by linarith [minOn_le hs hv x])
  · simp only [radialRetract, hv, ite_false, sub_zero]
    exact mul_nonneg hpos (h0 v)

theorem radialRetract_sum {s : Finset V} (hs : s.Nonempty) {x : V → ℝ}
    (h1 : (∑ v, x v) = 1) (hlt : (s.card : ℝ) * minOn s hs x < 1) :
    (∑ v, radialRetract s hs x v) = 1 := by
  classical
  have hsplit : (∑ v, radialRetract s hs x v)
      = radialScale s hs x * ((∑ v, x v) - ∑ v, (if v ∈ s then minOn s hs x else 0)) := by
    calc (∑ v, radialRetract s hs x v)
        = ∑ v, (radialScale s hs x * x v -
            radialScale s hs x * (if v ∈ s then minOn s hs x else 0)) :=
          Finset.sum_congr rfl fun v _ => by rw [radialRetract, mul_sub]
      _ = (∑ v, radialScale s hs x * x v) -
            ∑ v, radialScale s hs x * (if v ∈ s then minOn s hs x else 0) :=
          Finset.sum_sub_distrib _ _
      _ = radialScale s hs x * ((∑ v, x v) - ∑ v, (if v ∈ s then minOn s hs x else 0)) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, mul_sub]
  have hind : (∑ v, (if v ∈ s then minOn s hs x else 0)) = s.card * minOn s hs x := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rw [hsplit, h1, hind]
  exact radialScale_mul hs hlt

omit [Fintype V] in
theorem radialRetract_eq_zero_of_eq_minOn {s : Finset V} (hs : s.Nonempty) {x : V → ℝ}
    {v : V} (hv : v ∈ s) (hval : x v = minOn s hs x) : radialRetract s hs x v = 0 := by
  simp [radialRetract, hv, hval]

omit [Fintype V] in
theorem radialRetract_eq_zero_of_notMem {s : Finset V} (hs : s.Nonempty) {x : V → ℝ}
    (h0 : ∀ w, 0 ≤ x w) {v : V} (hzero : x v = 0) : radialRetract s hs x v = 0 := by
  by_cases hv : v ∈ s
  · have hm : minOn s hs x = 0 :=
      le_antisymm (by rw [← hzero]; exact minOn_le hs hv x) (minOn_nonneg hs h0)
    simp [radialRetract, hv, hm, hzero]
  · simp [radialRetract, hv, hzero]

/-- The radial projection stays inside the closed simplex carrying `x`. -/
theorem radialRetract_mem_barycentricFace {s t : Finset V} (hs : s.Nonempty) {x : V → ℝ}
    (hx : x ∈ barycentricFace t) (hlt : (s.card : ℝ) * minOn s hs x < 1) :
    radialRetract s hs x ∈ barycentricFace t :=
  ⟨fun v => radialRetract_nonneg hs hx.1 hlt v, radialRetract_sum hs hx.2.1 hlt,
    fun v hv => radialRetract_eq_zero_of_notMem hs hx.1 (hx.2.2 v hv)⟩

/-- The radial projection lands in the realization of the family with the
maximal face `s` removed. -/
theorem radialRetract_mem_erase {K : Finset (Finset V)} (hK : FaceClosed K) {s : Finset V}
    (hs : s.Nonempty) {x : V → ℝ} (hx : x ∈ barycentricCarrier K) (hne : x ≠ faceCenter s) :
    radialRetract s hs x ∈ barycentricCarrier (K.erase s) := by
  classical
  obtain ⟨h0, h1, t, htK, hsupp⟩ := hx
  have hlt := card_mul_minOn_lt_one hs h0 h1 hne
  obtain ⟨w, hws, hwval⟩ := exists_eq_minOn hs x
  have hzero : radialRetract s hs x w = 0 := radialRetract_eq_zero_of_eq_minOn hs hws hwval
  refine ⟨fun v => radialRetract_nonneg hs h0 hlt v, radialRetract_sum hs h1 hlt, ?_⟩
  by_cases hwt : w ∈ t
  · refine ⟨t.erase w, Finset.mem_erase.mpr ⟨?_, hK t htK _ (Finset.erase_subset _ _)⟩, ?_⟩
    · intro hEq
      exact (Finset.notMem_erase w t) (hEq ▸ hws)
    · intro v hv
      rw [Finset.mem_erase] at hv
      push Not at hv
      by_cases hvw : v = w
      · exact hvw ▸ hzero
      · exact radialRetract_eq_zero_of_notMem hs h0 (hsupp v (hv hvw))
  · refine ⟨t, Finset.mem_erase.mpr ⟨fun hEq => hwt (hEq ▸ hws), htK⟩, ?_⟩
    intro v hv
    exact radialRetract_eq_zero_of_notMem hs h0 (hsupp v hv)

/-- On the realization of the smaller family the radial projection is the
identity: this uses maximality of `s`. -/
theorem radialRetract_eq_self {K : Finset (Finset V)} {s : Finset V} (hs : s.Nonempty)
    (hmax : ∀ t ∈ K, s ⊆ t → t = s) {x : V → ℝ} (hx : x ∈ barycentricCarrier (K.erase s)) :
    radialRetract s hs x = x := by
  classical
  obtain ⟨h0, h1, t, htK, hsupp⟩ := hx
  obtain ⟨htne, htK⟩ := Finset.mem_erase.1 htK
  have hzero : minOn s hs x = 0 := by
    by_contra hne
    have hpos : 0 < minOn s hs x := lt_of_le_of_ne (minOn_nonneg hs h0) (Ne.symm hne)
    have hsub : s ⊆ t := by
      intro v hv
      by_contra hvt
      have := hsupp v hvt
      have := minOn_le hs hv x
      linarith
    exact htne (hmax t htK hsub)
  have hscale : radialScale s hs x = 1 := by simp [radialScale, hzero]
  funext v
  by_cases hv : v ∈ s <;> simp [radialRetract, hscale, hzero, hv]

/-! ### The punctured realization -/

/-- The realization of `K` with the barycenter of the face `s` removed. -/
def punctured (K : Finset (Finset V)) (s : Finset V) : Set ↥(barycentricCarrier K) :=
  {x | x.val ≠ faceCenter s}

theorem isOpen_punctured (K : Finset (Finset V)) (s : Finset V) : IsOpen (punctured K s) := by
  have : punctured K s = (fun x : ↥(barycentricCarrier K) => x.val) ⁻¹' {faceCenter s}ᶜ := rfl
  rw [this]
  exact (isClosed_singleton.isOpen_compl).preimage continuous_subtype_val

/-- The punctured realization and the open star of `s` cover the realization. -/
theorem punctured_union_openStar (K : Finset (Finset V)) (s : Finset V) :
    punctured K s ∪ openStar K s = univ := by
  apply eq_univ_of_forall
  intro x
  by_cases h : x.val = faceCenter s
  · refine Or.inr fun v hv => ?_
    rw [h]
    exact faceCenter_pos hv
  · exact Or.inl h

theorem carrier_erase_subset {K : Finset (Finset V)} (s : Finset V) :
    barycentricCarrier (K.erase s) ⊆ barycentricCarrier K :=
  barycentricCarrier_mono (Finset.erase_subset _ _)

theorem faceCenter_notMem_carrier_erase {K : Finset (Finset V)} {s : Finset V}
    (hmax : ∀ t ∈ K, s ⊆ t → t = s) : faceCenter s ∉ barycentricCarrier (K.erase s) := by
  classical
  rintro ⟨-, -, t, htK, hsupp⟩
  obtain ⟨htne, htK⟩ := Finset.mem_erase.1 htK
  refine htne (hmax t htK fun v hv => ?_)
  by_contra hvt
  exact absurd (hsupp v hvt) (ne_of_gt (faceCenter_pos hv))


/-! ### The deformation retraction -/

section Retraction

variable {K : Finset (Finset V)} {s : Finset V}

theorem card_mul_minOn_lt_one_of_mem_punctured (hs : s.Nonempty) (x : ↥(punctured K s)) :
    (s.card : ℝ) * minOn s hs x.val.val < 1 :=
  card_mul_minOn_lt_one hs x.val.property.1 x.val.property.2.1 x.property

theorem continuous_radialRetract_punctured (hs : s.Nonempty) :
    Continuous (fun x : ↥(punctured K s) => radialRetract s hs x.val.val) := by
  have hval : Continuous fun x : ↥(punctured K s) => (x.val.val : V → ℝ) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hmin : Continuous fun x : ↥(punctured K s) => minOn s hs x.val.val :=
    (continuous_minOn s hs).comp hval
  have hden : Continuous fun x : ↥(punctured K s) =>
      1 - (s.card : ℝ) * minOn s hs x.val.val := by
    exact continuous_const.sub (continuous_const.mul hmin)
  have hne : ∀ x : ↥(punctured K s), 1 - (s.card : ℝ) * minOn s hs x.val.val ≠ 0 := fun x => by
    have := card_mul_minOn_lt_one_of_mem_punctured hs x
    intro h
    linarith
  have hscale : Continuous fun x : ↥(punctured K s) => radialScale s hs x.val.val :=
    hden.inv₀ hne
  refine continuous_pi fun v => hscale.mul (((continuous_apply v).comp hval).sub ?_)
  by_cases hv : v ∈ s
  · simpa only [hv, ite_true] using hmin
  · simpa only [hv, ite_false] using continuous_const

/-- The radial retraction of the punctured realization onto the realization of
the family with the maximal face removed. -/
def puncturedRetract (hK : FaceClosed K) (hs : s.Nonempty) :
    C(↥(punctured K s), ↥(barycentricCarrier (K.erase s))) where
  toFun x := ⟨radialRetract s hs x.val.val,
    radialRetract_mem_erase hK hs x.val.property x.property⟩
  continuous_toFun := (continuous_radialRetract_punctured hs).subtype_mk _

/-- The inclusion of the realization of the smaller family into the punctured
realization. -/
def puncturedInclusion (hmax : ∀ t ∈ K, s ⊆ t → t = s) :
    C(↥(barycentricCarrier (K.erase s)), ↥(punctured K s)) where
  toFun y := ⟨⟨y.val, carrier_erase_subset s y.property⟩, fun h =>
    faceCenter_notMem_carrier_erase hmax (h ▸ y.property)⟩
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem puncturedRetract_comp_inclusion (hK : FaceClosed K) (hs : s.Nonempty)
    (hmax : ∀ t ∈ K, s ⊆ t → t = s) :
    (puncturedRetract hK hs).comp (puncturedInclusion hmax) = ContinuousMap.id _ := by
  ext y
  exact congrFun (radialRetract_eq_self hs hmax y.property) _

/-- The straight-line homotopy from the identity to the radial retraction. -/
def puncturedHomotopyMap (hs : s.Nonempty) (p : unitInterval × ↥(punctured K s)) : V → ℝ :=
  fun v => (1 - p.1.val) * p.2.val.val v + p.1.val * radialRetract s hs p.2.val.val v

theorem puncturedHomotopyMap_mem (hs : s.Nonempty) (p : unitInterval × ↥(punctured K s)) :
    puncturedHomotopyMap hs p ∈ barycentricCarrier K := by
  obtain ⟨h0, h1, t, htK, hsupp⟩ := p.2.val.property
  have hlt := card_mul_minOn_lt_one_of_mem_punctured hs p.2
  have hxface : (p.2.val.val : V → ℝ) ∈ barycentricFace t := ⟨h0, h1, hsupp⟩
  have hrface : radialRetract s hs p.2.val.val ∈ barycentricFace t :=
    radialRetract_mem_barycentricFace hs hxface hlt
  have hconv := barycentricFace_convex t hxface hrface
    (by linarith [p.1.2.2] : (0:ℝ) ≤ 1 - p.1.val) p.1.2.1 (by ring)
  obtain ⟨hc0, hc1, hcsupp⟩ := hconv
  exact ⟨hc0, hc1, t, htK, hcsupp⟩

theorem puncturedHomotopyMap_ne (hs : s.Nonempty) (p : unitInterval × ↥(punctured K s)) :
    puncturedHomotopyMap hs p ≠ faceCenter s := by
  obtain ⟨h0, h1, -⟩ := p.2.val.property
  have hlt := card_mul_minOn_lt_one_of_mem_punctured hs p.2
  obtain ⟨w, hws, hwval⟩ := exists_eq_minOn hs (p.2.val.val : V → ℝ)
  have hzero : radialRetract s hs p.2.val.val w = 0 :=
    radialRetract_eq_zero_of_eq_minOn hs hws hwval
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  have hmlt : minOn s hs (p.2.val.val : V → ℝ) < (s.card : ℝ)⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hcard]
    linarith [hlt]
  intro hEq
  have hval := congrFun hEq w
  rw [puncturedHomotopyMap] at hval
  simp only [hzero, mul_zero, add_zero, faceCenter, hws, ite_true] at hval
  have hm0 : 0 ≤ minOn s hs (p.2.val.val : V → ℝ) := minOn_nonneg hs h0
  have ht1 : p.1.val ≤ 1 := p.1.2.2
  have ht0 : 0 ≤ p.1.val := p.1.2.1
  nlinarith [hval, hwval, hmlt, hm0, ht0, ht1]

theorem continuous_puncturedHomotopyMap (hs : s.Nonempty) :
    Continuous (fun p : unitInterval × ↥(punctured K s) => puncturedHomotopyMap hs p) := by
  have hval : Continuous fun p : unitInterval × ↥(punctured K s) => (p.2.val.val : V → ℝ) :=
    (continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd
  have hret : Continuous fun p : unitInterval × ↥(punctured K s) =>
      radialRetract s hs p.2.val.val :=
    (continuous_radialRetract_punctured hs).comp continuous_snd
  have ht : Continuous fun p : unitInterval × ↥(punctured K s) => (p.1.val : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  exact continuous_pi fun v =>
    ((continuous_const.sub ht).mul ((continuous_apply v).comp hval)).add
      (ht.mul ((continuous_apply v).comp hret))

/-- The straight-line homotopy from the identity of the punctured realization
to the radial retraction. -/
def puncturedHomotopy (hK : FaceClosed K) (hs : s.Nonempty)
    (hmax : ∀ t ∈ K, s ⊆ t → t = s) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(punctured K s))
      ((puncturedInclusion hmax).comp (puncturedRetract hK hs)) where
  toFun p := ⟨⟨puncturedHomotopyMap hs p, puncturedHomotopyMap_mem hs p⟩,
    puncturedHomotopyMap_ne hs p⟩
  continuous_toFun :=
    ((continuous_puncturedHomotopyMap hs).subtype_mk _).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    change (1 - (0 : ℝ)) * x.val.val v + (0 : ℝ) * radialRetract s hs x.val.val v = x.val.val v
    ring
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    change (1 - (1 : ℝ)) * x.val.val v + (1 : ℝ) * radialRetract s hs x.val.val v
      = radialRetract s hs x.val.val v
    ring

/-- **The punctured realization deformation retracts onto the realization of
the family with the maximal face removed.** -/
def puncturedHomotopyEquiv (hK : FaceClosed K) (hs : s.Nonempty)
    (hmax : ∀ t ∈ K, s ⊆ t → t = s) :
    ContinuousMap.HomotopyEquiv ↥(punctured K s) ↥(barycentricCarrier (K.erase s)) where
  toFun := puncturedRetract hK hs
  invFun := puncturedInclusion hmax
  left_inv := ⟨(puncturedHomotopy hK hs hmax).symm⟩
  right_inv := by
    rw [puncturedRetract_comp_inclusion hK hs hmax]

end Retraction

end AffineTverberg.Simplicial
