import AffineTverberg.BarycentricThickening

set_option linter.style.header false

/-!
# The intersection piece of the Mayer-Vietoris cover along a maximal face

For a nonempty maximal face `s` of a finite family `K`, the intersection of the
punctured realization with the open star of `s` is the open simplex of `s` with
its barycenter removed. This file constructs an explicit homotopy equivalence
between that intersection and the realization of the boundary of `s`, i.e. of
the family `boundaryFamily s` of proper faces of `s`.

Together with `BarycentricThickening` this identifies all three pieces of the
open Mayer-Vietoris cover `{punctured K s, openStar K s}` of the realization of
`K`: the punctured realization retracts onto the realization of `K.erase s`,
the open star is contractible, and the intersection is the boundary of `s`.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg.Simplicial

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The boundary of a face -/

/-- The family of proper faces of `s`. -/
def boundaryFamily (s : Finset V) : Finset (Finset V) := s.powerset.erase s

omit [Fintype V] in
theorem mem_boundaryFamily {s u : Finset V} : u ∈ boundaryFamily s ↔ u ⊆ s ∧ u ≠ s := by
  simp [boundaryFamily, Finset.mem_erase, Finset.mem_powerset, and_comm]

/-! ### The intersection piece -/

variable {K : Finset (Finset V)} {s : Finset V}

/-- The intersection of the punctured realization with the open star of `s`. -/
def linkSet (K : Finset (Finset V)) (s : Finset V) : Set ↥(barycentricCarrier K) :=
  punctured K s ∩ openStar K s

omit [DecidableEq V] in
/-- A point of the open star of a maximal face lies in the closed simplex of
that face. -/
theorem mem_barycentricFace_of_mem_openStar (hmax : ∀ t ∈ K, s ⊆ t → t = s)
    {x : ↥(barycentricCarrier K)} (hx : x ∈ openStar K s) : x.val ∈ barycentricFace s := by
  obtain ⟨h0, h1, t, htK, hsupp⟩ := x.property
  have hsub : s ⊆ t := by
    intro v hv
    by_contra hvt
    exact absurd (hsupp v hvt) (ne_of_gt (hx v hv))
  refine ⟨h0, h1, ?_⟩
  rw [← hmax t htK hsub]
  exact hsupp

/-! ### From the intersection to the boundary -/

theorem radialRetract_mem_boundaryFamily (hs : s.Nonempty)
    (hmax : ∀ t ∈ K, s ⊆ t → t = s) {x : ↥(barycentricCarrier K)} (hx : x ∈ linkSet K s) :
    radialRetract s hs x.val ∈ barycentricCarrier (boundaryFamily s) := by
  classical
  obtain ⟨h0, h1, -⟩ := x.property
  have hlt := card_mul_minOn_lt_one hs h0 h1 hx.1
  have hface := mem_barycentricFace_of_mem_openStar hmax hx.2
  obtain ⟨w, hws, hwval⟩ := exists_eq_minOn hs (x.val : V → ℝ)
  have hzero : radialRetract s hs x.val w = 0 := radialRetract_eq_zero_of_eq_minOn hs hws hwval
  have hr := radialRetract_mem_barycentricFace hs hface hlt
  refine ⟨hr.1, hr.2.1, s.erase w, mem_boundaryFamily.2 ⟨Finset.erase_subset _ _, ?_⟩, ?_⟩
  · intro hEq
    exact (Finset.notMem_erase w s) (by rw [hEq]; exact hws)
  · intro v hv
    rw [Finset.mem_erase] at hv
    push Not at hv
    by_cases hvw : v = w
    · exact hvw ▸ hzero
    · exact hr.2.2 v (hv hvw)

/-- The inclusion of the intersection into the punctured realization. -/
def linkToPunctured (K : Finset (Finset V)) (s : Finset V) :
    C(↥(linkSet K s), ↥(punctured K s)) where
  toFun x := ⟨x.val, x.property.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The radial projection of the intersection onto the boundary of `s`. -/
def linkRetract (hs : s.Nonempty) (hmax : ∀ t ∈ K, s ⊆ t → t = s) :
    C(↥(linkSet K s), ↥(barycentricCarrier (boundaryFamily s))) where
  toFun x := ⟨radialRetract s hs x.val, radialRetract_mem_boundaryFamily hs hmax x.property⟩
  continuous_toFun :=
    (((continuous_radialRetract_punctured (K := K) hs).comp
      (linkToPunctured K s).continuous).subtype_mk _)

/-! ### From the boundary to the intersection -/

/-- The midpoint of a point of the boundary of `s` and the barycenter of `s`. -/
def halfCenter (s : Finset V) (y : V → ℝ) : V → ℝ := fun v => (y v + faceCenter s v) / 2

theorem halfCenter_mem_barycentricFace (hs : s.Nonempty) {y : V → ℝ}
    (hy : y ∈ barycentricFace s) : halfCenter s y ∈ barycentricFace s := by
  have hc := faceCenter_mem_barycentricFace hs
  have := barycentricFace_convex s hy hc (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num)
  refine ⟨fun v => ?_, ?_, fun v hv => ?_⟩
  · have := this.1 v
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    simpa [halfCenter, div_eq_mul_inv] using by linarith [this]
  · have := this.2.1
    have heq : ∀ v, halfCenter s y v = (1/2 : ℝ) * y v + (1/2 : ℝ) * faceCenter s v := by
      intro v; simp [halfCenter]; ring
    calc ∑ v, halfCenter s y v = ∑ v, ((1/2 : ℝ) * y v + (1/2 : ℝ) * faceCenter s v) :=
          Finset.sum_congr rfl fun v _ => heq v
      _ = 1 := by simpa using this
  · simp [halfCenter, hy.2.2 v hv, faceCenter, hv]

omit [Fintype V] in
theorem halfCenter_pos {y : V → ℝ} (hy : ∀ v, 0 ≤ y v) {v : V} (hv : v ∈ s) :
    0 < halfCenter s y v := by
  have := faceCenter_pos (s := s) hv
  have := hy v
  simp only [halfCenter]
  positivity

theorem halfCenter_ne_faceCenter (hs : s.Nonempty) {y : V → ℝ}
    (hy : y ∈ barycentricCarrier (boundaryFamily s)) : halfCenter s y ≠ faceCenter s := by
  classical
  obtain ⟨h0, h1, u, huB, hsupp⟩ := hy
  obtain ⟨husub, hune⟩ := mem_boundaryFamily.1 huB
  obtain ⟨w, hws, hwu⟩ : ∃ w ∈ s, w ∉ u := by
    by_contra hcon
    push Not at hcon
    exact hune (Finset.Subset.antisymm husub hcon)
  intro hEq
  have hval := congrFun hEq w
  have hy0 : y w = 0 := hsupp w hwu
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  simp only [halfCenter, hy0, faceCenter, hws, ite_true, zero_add] at hval
  field_simp at hval
  linarith

theorem halfCenter_mem_linkSet (hs : s.Nonempty) (hsK : s ∈ K) {y : V → ℝ}
    (hy : y ∈ barycentricCarrier (boundaryFamily s)) :
    ∃ h : halfCenter s y ∈ barycentricCarrier K,
      (⟨halfCenter s y, h⟩ : ↥(barycentricCarrier K)) ∈ linkSet K s := by
  classical
  obtain ⟨h0, h1, u, huB, hsupp⟩ := hy
  obtain ⟨husub, -⟩ := mem_boundaryFamily.1 huB
  have hyface : y ∈ barycentricFace s :=
    ⟨h0, h1, fun v hv => hsupp v fun hvu => hv (husub hvu)⟩
  have hface := halfCenter_mem_barycentricFace hs hyface
  refine ⟨⟨hface.1, hface.2.1, s, hsK, hface.2.2⟩, ?_, ?_⟩
  · exact halfCenter_ne_faceCenter hs ⟨h0, h1, u, huB, hsupp⟩
  · exact fun v hv => halfCenter_pos h0 hv

/-- The map from the boundary of `s` into the intersection, halfway towards the
barycenter. -/
def linkInclusion (hs : s.Nonempty) (hsK : s ∈ K) :
    C(↥(barycentricCarrier (boundaryFamily s)), ↥(linkSet K s)) where
  toFun y := ⟨⟨halfCenter s y.val, (halfCenter_mem_linkSet hs hsK y.property).choose⟩,
    (halfCenter_mem_linkSet hs hsK y.property).choose_spec⟩
  continuous_toFun := by
    refine ((continuous_pi fun v => ?_).subtype_mk _).subtype_mk _
    exact (((continuous_apply v).comp continuous_subtype_val).add continuous_const).div_const 2

/-! ### The two compositions -/

theorem minOn_halfCenter (hs : s.Nonempty) {y : V → ℝ}
    (hy : y ∈ barycentricCarrier (boundaryFamily s)) :
    minOn s hs (halfCenter s y) = (2 * s.card : ℝ)⁻¹ := by
  classical
  obtain ⟨h0, h1, u, huB, hsupp⟩ := hy
  obtain ⟨husub, hune⟩ := mem_boundaryFamily.1 huB
  obtain ⟨w, hws, hwu⟩ : ∃ w ∈ s, w ∉ u := by
    by_contra hcon
    push Not at hcon
    exact hune (Finset.Subset.antisymm husub hcon)
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  refine le_antisymm ?_ ?_
  · have hle := minOn_le hs hws (halfCenter s y)
    have : halfCenter s y w = (2 * s.card : ℝ)⁻¹ := by
      simp only [halfCenter, hsupp w hwu, faceCenter, hws, ite_true, zero_add]
      field_simp
    linarith [this ▸ hle]
  · obtain ⟨v, hvs, hveq⟩ := exists_eq_minOn hs (halfCenter s y)
    rw [← hveq]
    have hy0 : 0 ≤ y v := h0 v
    have hfc : faceCenter s v = (s.card : ℝ)⁻¹ := by simp [faceCenter, hvs]
    simp only [halfCenter, hfc]
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    have : (2 * (s.card : ℝ))⁻¹ * 2 = (s.card : ℝ)⁻¹ := by field_simp
    rw [this]
    linarith

theorem linkRetract_halfCenter (hs : s.Nonempty)
    (y : ↥(barycentricCarrier (boundaryFamily s))) :
    radialRetract s hs (halfCenter s y.val) = y.val := by
  classical
  obtain ⟨h0, h1, u, huB, hsupp⟩ := y.property
  obtain ⟨husub, -⟩ := mem_boundaryFamily.1 huB
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  have hmin := minOn_halfCenter hs y.property
  have hscale : radialScale s hs (halfCenter s y.val) = 2 := by
    rw [radialScale, hmin]
    rw [show (s.card : ℝ) * (2 * s.card : ℝ)⁻¹ = 2⁻¹ by field_simp]
    norm_num
  funext v
  rw [radialRetract, hscale, hmin]
  by_cases hv : v ∈ s
  · have hfc : faceCenter s v = (s.card : ℝ)⁻¹ := by simp [faceCenter, hv]
    simp only [hv, ite_true, halfCenter, hfc]
    field_simp
    ring
  · have hy0 : y.val v = 0 := hsupp v fun hvu => hv (husub hvu)
    simp [hv, halfCenter, faceCenter, hy0]

theorem linkRetract_comp_inclusion (hs : s.Nonempty) (hsK : s ∈ K)
    (hmax : ∀ t ∈ K, s ⊆ t → t = s) :
    (linkRetract hs hmax).comp (linkInclusion hs hsK) = ContinuousMap.id _ := by
  ext y
  exact congrFun (linkRetract_halfCenter hs y) _

/-! ### The homotopy -/

/-- The straight-line homotopy from the identity of the intersection to the
composition through the boundary of `s`. -/
def linkHomotopyMap (hs : s.Nonempty) (p : unitInterval × ↥(linkSet K s)) : V → ℝ :=
  fun v => (1 - p.1.val) * p.2.val.val v +
    p.1.val * halfCenter s (radialRetract s hs p.2.val.val) v

theorem linkHomotopyMap_mem (hs : s.Nonempty) (hsK : s ∈ K) (hmax : ∀ t ∈ K, s ⊆ t → t = s)
    (p : unitInterval × ↥(linkSet K s)) :
    ∃ h : linkHomotopyMap hs p ∈ barycentricCarrier K,
      (⟨linkHomotopyMap hs p, h⟩ : ↥(barycentricCarrier K)) ∈ linkSet K s := by
  classical
  obtain ⟨h0, h1, -⟩ := p.2.val.property
  have hlt := card_mul_minOn_lt_one hs h0 h1 p.2.property.1
  have hface := mem_barycentricFace_of_mem_openStar hmax p.2.property.2
  have hrface : radialRetract s hs p.2.val.val ∈ barycentricFace s :=
    radialRetract_mem_barycentricFace hs hface hlt
  have hhalf : halfCenter s (radialRetract s hs p.2.val.val) ∈ barycentricFace s :=
    halfCenter_mem_barycentricFace hs hrface
  have hconv := barycentricFace_convex s hface hhalf
    (by linarith [p.1.2.2] : (0:ℝ) ≤ 1 - p.1.val) p.1.2.1 (by ring)
  have hmemK : linkHomotopyMap hs p ∈ barycentricCarrier K :=
    ⟨hconv.1, hconv.2.1, s, hsK, hconv.2.2⟩
  refine ⟨hmemK, ?_, ?_⟩
  · -- the homotopy never passes through the barycenter
    obtain ⟨w, hws, hwval⟩ := exists_eq_minOn hs (p.2.val.val : V → ℝ)
    have hzero : radialRetract s hs p.2.val.val w = 0 :=
      radialRetract_eq_zero_of_eq_minOn hs hws hwval
    have hcard : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
    have hmlt : minOn s hs (p.2.val.val : V → ℝ) < (s.card : ℝ)⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ hcard]
      linarith [hlt]
    have hm0 : 0 ≤ minOn s hs (p.2.val.val : V → ℝ) := minOn_nonneg hs h0
    intro hEq
    have hval := congrFun hEq w
    have hfc : faceCenter s w = (s.card : ℝ)⁻¹ := by simp [faceCenter, hws]
    simp only [linkHomotopyMap, halfCenter, hzero, hfc, zero_add] at hval
    have ht0 : 0 ≤ p.1.val := p.1.2.1
    have ht1 : p.1.val ≤ 1 := p.1.2.2
    have hxw : (p.2.val.val : V → ℝ) w = minOn s hs (p.2.val.val : V → ℝ) := hwval
    rw [hxw] at hval
    have hinv : (0 : ℝ) < (s.card : ℝ)⁻¹ := inv_pos.mpr hcard
    nlinarith [hval, hmlt, hm0, ht0, ht1, hinv]
  · -- the homotopy stays in the open star
    intro v hv
    have hxpos : 0 < p.2.val.val v := p.2.property.2 v hv
    have hhpos : 0 < halfCenter s (radialRetract s hs p.2.val.val) v :=
      halfCenter_pos hrface.1 hv
    have ht0 : 0 ≤ p.1.val := p.1.2.1
    have ht1 : p.1.val ≤ 1 := p.1.2.2
    change 0 < (1 - p.1.val) * p.2.val.val v +
      p.1.val * halfCenter s (radialRetract s hs p.2.val.val) v
    rcases eq_or_lt_of_le ht0 with h | h
    · rw [← h]
      simpa using hxpos
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) hxpos.le) (mul_pos h hhpos)

theorem continuous_linkHomotopyMap (hs : s.Nonempty) :
    Continuous (fun p : unitInterval × ↥(linkSet K s) => linkHomotopyMap hs p) := by
  have hval : Continuous fun p : unitInterval × ↥(linkSet K s) => (p.2.val.val : V → ℝ) :=
    (continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd
  have hret : Continuous fun p : unitInterval × ↥(linkSet K s) =>
      radialRetract s hs p.2.val.val :=
    ((continuous_radialRetract_punctured (K := K) hs).comp
      (linkToPunctured K s).continuous).comp continuous_snd
  have ht : Continuous fun p : unitInterval × ↥(linkSet K s) => (p.1.val : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  refine continuous_pi fun v => ((continuous_const.sub ht).mul
    ((continuous_apply v).comp hval)).add (ht.mul ?_)
  exact (((continuous_apply v).comp hret).add continuous_const).div_const 2

/-- The homotopy from the identity of the intersection to the composition
through the boundary of `s`. -/
def linkHomotopy (hs : s.Nonempty) (hsK : s ∈ K) (hmax : ∀ t ∈ K, s ⊆ t → t = s) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(linkSet K s))
      ((linkInclusion hs hsK).comp (linkRetract hs hmax)) where
  toFun p := ⟨⟨linkHomotopyMap hs p, (linkHomotopyMap_mem hs hsK hmax p).choose⟩,
    (linkHomotopyMap_mem hs hsK hmax p).choose_spec⟩
  continuous_toFun :=
    (((continuous_linkHomotopyMap hs).subtype_mk _).subtype_mk _)
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    change (1 - (0 : ℝ)) * x.val.val v +
      (0 : ℝ) * halfCenter s (radialRetract s hs x.val.val) v = x.val.val v
    ring
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    change (1 - (1 : ℝ)) * x.val.val v +
        (1 : ℝ) * halfCenter s (radialRetract s hs x.val.val) v =
      halfCenter s (radialRetract s hs x.val.val) v
    ring

/-- **The intersection of the punctured realization with the open star of a
maximal face is homotopy equivalent to the realization of the boundary of that
face.** -/
def linkHomotopyEquiv (hs : s.Nonempty) (hsK : s ∈ K) (hmax : ∀ t ∈ K, s ⊆ t → t = s) :
    ContinuousMap.HomotopyEquiv ↥(linkSet K s) ↥(barycentricCarrier (boundaryFamily s)) where
  toFun := linkRetract hs hmax
  invFun := linkInclusion hs hsK
  left_inv := ⟨(linkHomotopy hs hsK hmax).symm⟩
  right_inv := by rw [linkRetract_comp_inclusion hs hsK hmax]

end AffineTverberg.Simplicial
