import AffineTverberg.BarycentricLink
import AffineTverberg.MayerVietoris

set_option linter.style.header false

/-!
# The open star thickening of a maximal face

For a maximal nonempty face `s` of a finite face-closed family `K` this file
constructs the second member of the open cover of the barycentric realization
used in the simplicial-to-singular comparison:

`faceStar K s = {x | 0 < ∑_{v ∈ s} x v}`,

the union of the open stars of the vertices of `s`.  Unlike the open star of
the face `s` itself, this open set *contains the whole closed simplex* of `s`,
which is what makes the comparison chain map land in the complex of small
chains of the cover `{punctured K s, faceStar K s}`.

The three geometric facts proved here are

* `starHomotopyEquiv` — `faceStar K s` deformation retracts onto the closed
  simplex of `s`, i.e. onto the realization of `s.powerset`;
* `starPuncturedBoundaryHomotopyEquiv` — the intersection
  `punctured K s ∩ faceStar K s` deformation retracts onto the realization of
  the boundary `boundaryFamily s`;
* `isOpen_faceStar`, `mem_punctured_or_faceStar` — the two sets form an open
  cover.

The retraction is the normalization `x ↦ x|_s / (∑_{v ∈ s} x v)`; maximality of
`s` enters through `exists_eq_zero_of_notMem_barycentricFace`, which is what
makes the normalization avoid the barycenter of `s`.
-/

noncomputable section

open Set

namespace AffineTverberg.Simplicial

variable {V : Type} [Fintype V] [DecidableEq V]
variable {K : Finset (Finset V)} {s : Finset V}

/-! ### The mass carried by a face and the normalization retraction -/

/-- The total barycentric mass a point puts on the vertices of `s`. -/
def starMass (s : Finset V) (x : V → ℝ) : ℝ := ∑ v ∈ s, x v

omit [Fintype V] [DecidableEq V] in
theorem continuous_starMass (s : Finset V) : Continuous (starMass (V := V) s) :=
  continuous_finsetSum _ fun v _ => continuous_apply v

omit [DecidableEq V] in
theorem starMass_eq_one_of_mem_barycentricFace {x : V → ℝ} (hx : x ∈ barycentricFace s) :
    starMass s x = 1 := by
  obtain ⟨-, h1, hsupp⟩ := hx
  rw [starMass, ← h1]
  exact Finset.sum_subset (Finset.subset_univ s) fun v _ hv => hsupp v hv

omit [Fintype V] [DecidableEq V] in
theorem starMass_nonneg {x : V → ℝ} (h0 : ∀ v, 0 ≤ x v) : 0 ≤ starMass s x :=
  Finset.sum_nonneg fun v _ => h0 v

omit [Fintype V] [DecidableEq V] in
theorem starMass_pos_of_mem {x : V → ℝ} (h0 : ∀ v, 0 ≤ x v) {v : V} (hv : v ∈ s)
    (hpos : 0 < x v) : 0 < starMass s x :=
  lt_of_lt_of_le hpos (Finset.single_le_sum (f := x) (fun w _ => h0 w) hv)

/-- The union of the open stars of the vertices of `s`. -/
def faceStar (K : Finset (Finset V)) (s : Finset V) : Set ↥(barycentricCarrier K) :=
  {x | 0 < starMass s x.val}

omit [DecidableEq V] in
theorem mem_faceStar_iff {x : ↥(barycentricCarrier K)} :
    x ∈ faceStar K s ↔ 0 < starMass s x.val := Iff.rfl

omit [DecidableEq V] in
theorem isOpen_faceStar (K : Finset (Finset V)) (s : Finset V) : IsOpen (faceStar K s) := by
  have hpre : faceStar K s =
      (fun x : ↥(barycentricCarrier K) => starMass s x.val) ⁻¹' (Ioi 0) := rfl
  rw [hpre]
  exact (isOpen_Ioi).preimage ((continuous_starMass s).comp continuous_subtype_val)

omit [DecidableEq V] in
/-- The realization of the full powerset of `s` is the closed simplex of `s`. -/
theorem barycentricCarrier_powerset (s : Finset V) :
    barycentricCarrier (s.powerset) = barycentricFace s := by
  ext x
  constructor
  · rintro ⟨h0, h1, t, htmem, hsupp⟩
    exact ⟨h0, h1, fun v hv => hsupp v fun hvt => hv (Finset.mem_powerset.1 htmem hvt)⟩
  · rintro ⟨h0, h1, hsupp⟩
    exact ⟨h0, h1, s, Finset.mem_powerset_self s, hsupp⟩

omit [DecidableEq V] in
theorem barycentricFace_subset_carrier (hsK : s ∈ K) :
    barycentricFace s ⊆ barycentricCarrier K := by
  rintro x ⟨h0, h1, hsupp⟩
  exact ⟨h0, h1, s, hsK, hsupp⟩

/-- The normalization of a point onto the face `s`. -/
def starRetract (s : Finset V) (x : V → ℝ) : V → ℝ :=
  fun v => if v ∈ s then x v / starMass s x else 0

theorem starRetract_mem_barycentricFace_of_mem {t : Finset V} {x : V → ℝ}
    (hx : x ∈ barycentricFace t) (hpos : 0 < starMass s x) :
    starRetract s x ∈ barycentricFace t ∩ barycentricFace s := by
  obtain ⟨h0, h1, hsupp⟩ := hx
  have hsum : ∑ v, starRetract s x v = 1 := by
    have hs : ∑ v, starRetract s x v = ∑ v ∈ s, x v / starMass s x := by
      rw [← Finset.sum_subset (Finset.subset_univ s) (fun v _ hv => by simp [starRetract, hv])]
      exact Finset.sum_congr rfl fun v hv => by simp [starRetract, hv]
    rw [hs, ← Finset.sum_div]
    exact div_self (ne_of_gt hpos)
  have hnonneg : ∀ v, 0 ≤ starRetract s x v := by
    intro v
    by_cases hv : v ∈ s
    · simpa [starRetract, hv] using div_nonneg (h0 v) (le_of_lt hpos)
    · simp [starRetract, hv]
  refine ⟨⟨hnonneg, hsum, fun v hv => ?_⟩, hnonneg, hsum, fun v hv => by simp [starRetract, hv]⟩
  by_cases hvs : v ∈ s
  · simp [starRetract, hvs, hsupp v hv]
  · simp [starRetract, hvs]

theorem starRetract_mem_barycentricFace {x : V → ℝ} (hx : x ∈ barycentricCarrier K)
    (hpos : 0 < starMass s x) : starRetract s x ∈ barycentricFace s := by
  obtain ⟨h0, h1, t, -, hsupp⟩ := hx
  exact (starRetract_mem_barycentricFace_of_mem (t := t) ⟨h0, h1, hsupp⟩ hpos).2

theorem starRetract_mem_carrier_powerset {x : V → ℝ} (hx : x ∈ barycentricCarrier K)
    (hpos : 0 < starMass s x) : starRetract s x ∈ barycentricCarrier (s.powerset) := by
  rw [barycentricCarrier_powerset]
  exact starRetract_mem_barycentricFace hx hpos

theorem starRetract_eq_self {x : V → ℝ} (hx : x ∈ barycentricFace s) :
    starRetract s x = x := by
  have hmass := starMass_eq_one_of_mem_barycentricFace hx
  funext v
  by_cases hv : v ∈ s
  · simp [starRetract, hv, hmass]
  · simp [starRetract, hv, hx.2.2 v hv]

omit [DecidableEq V] in
/-- **Maximality of `s`**: a point of the realization which is not in the closed
simplex of `s` must have a zero coordinate at some vertex of `s`. -/
theorem exists_eq_zero_of_notMem_barycentricFace (hmax : ∀ t ∈ K, s ⊆ t → t = s)
    {x : V → ℝ} (hx : x ∈ barycentricCarrier K) (hnot : x ∉ barycentricFace s) :
    ∃ v ∈ s, x v = 0 := by
  classical
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  obtain ⟨h0, h1, t, htK, hsupp⟩ := hx
  have hst : s ⊆ t := by
    intro v hv
    by_contra hvt
    exact hcon v hv (hsupp v hvt)
  have hts : t = s := hmax t htK hst
  exact hnot ⟨h0, h1, fun v hv => hsupp v (fun hvt => hv (hts ▸ hvt))⟩

omit [DecidableEq V] in
theorem starMass_pos_of_mem_barycentricFace {x : V → ℝ} (hx : x ∈ barycentricFace s) :
    0 < starMass s x := by
  rw [starMass_eq_one_of_mem_barycentricFace hx]; norm_num

theorem starRetract_ne_faceCenter (hmax : ∀ t ∈ K, s ⊆ t → t = s)
    {x : V → ℝ} (hx : x ∈ barycentricCarrier K) (hne : x ≠ faceCenter s) :
    starRetract s x ≠ faceCenter s := by
  by_cases hface : x ∈ barycentricFace s
  · rwa [starRetract_eq_self hface]
  · obtain ⟨v, hv, hxv⟩ := exists_eq_zero_of_notMem_barycentricFace hmax hx hface
    intro hEq
    have h1 := congrFun hEq v
    rw [starRetract, ite_eq_left_of_eq_true _ _ (eq_true hv), hxv, zero_div] at h1
    exact absurd h1.symm (ne_of_gt (faceCenter_pos hv))

theorem continuous_starRetract_faceStar (s : Finset V) :
    Continuous (fun x : ↥(faceStar K s) => starRetract s x.val.val) := by
  have hval : Continuous fun x : ↥(faceStar K s) => (x.val.val : V → ℝ) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hmass : Continuous fun x : ↥(faceStar K s) => starMass s x.val.val :=
    (continuous_starMass s).comp hval
  have hne : ∀ x : ↥(faceStar K s), starMass s x.val.val ≠ 0 := fun x => ne_of_gt x.property
  refine continuous_pi fun v => ?_
  by_cases hv : v ∈ s
  · simp only [starRetract, hv, ite_true]
    exact ((continuous_apply v).comp hval).div hmass hne
  · simpa only [starRetract, hv, ite_false] using continuous_const

/-! ### The deformation retraction of the star onto the closed simplex -/

section Retraction

/-- The normalization retraction of the star onto the closed simplex of `s`. -/
def starRetractMap (K : Finset (Finset V)) (s : Finset V) :
    C(↥(faceStar K s), ↥(barycentricCarrier (s.powerset))) where
  toFun x := ⟨starRetract s x.val.val,
    starRetract_mem_carrier_powerset x.val.property x.property⟩
  continuous_toFun := (continuous_starRetract_faceStar s).subtype_mk _

omit [DecidableEq V] in
theorem barycentricCarrier_powerset_subset (hsK : s ∈ K) :
    barycentricCarrier (s.powerset) ⊆ barycentricCarrier K := by
  rw [barycentricCarrier_powerset]
  exact barycentricFace_subset_carrier hsK

/-- The inclusion of the closed simplex of `s` into the star. -/
def starInclusion (hsK : s ∈ K) :
    C(↥(barycentricCarrier (s.powerset)), ↥(faceStar K s)) where
  toFun y := ⟨⟨y.val, barycentricCarrier_powerset_subset hsK y.property⟩,
    starMass_pos_of_mem_barycentricFace
      (by rw [← barycentricCarrier_powerset]; exact y.property)⟩
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem starRetractMap_comp_inclusion (hsK : s ∈ K) :
    (starRetractMap K s).comp (starInclusion hsK) = ContinuousMap.id _ := by
  ext y
  have hy : y.val ∈ barycentricFace s := by
    rw [← barycentricCarrier_powerset]; exact y.property
  exact congrFun (starRetract_eq_self hy) _

/-- The straight-line homotopy from the identity of the star to the
normalization retraction. -/
def starHomotopyMap (p : unitInterval × ↥(faceStar K s)) : V → ℝ :=
  fun v => (1 - p.1.val) * p.2.val.val v + p.1.val * starRetract s p.2.val.val v

theorem starHomotopyMap_mem (p : unitInterval × ↥(faceStar K s)) :
    starHomotopyMap p ∈ barycentricCarrier K := by
  obtain ⟨h0, h1, t, htK, hsupp⟩ := p.2.val.property
  have hxface : (p.2.val.val : V → ℝ) ∈ barycentricFace t := ⟨h0, h1, hsupp⟩
  have hrface : starRetract s p.2.val.val ∈ barycentricFace t :=
    (starRetract_mem_barycentricFace_of_mem hxface p.2.property).1
  have hconv := barycentricFace_convex t hxface hrface
    (by linarith [p.1.2.2] : (0:ℝ) ≤ 1 - p.1.val) p.1.2.1 (by ring)
  obtain ⟨hc0, hc1, hcsupp⟩ := hconv
  exact ⟨hc0, hc1, t, htK, hcsupp⟩

theorem starMass_starHomotopyMap (p : unitInterval × ↥(faceStar K s)) :
    starMass s (starHomotopyMap p) =
      (1 - p.1.val) * starMass s p.2.val.val +
        p.1.val * starMass s (starRetract s p.2.val.val) := by
  simp only [starMass, starHomotopyMap, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]

theorem starHomotopyMap_mem_faceStar (p : unitInterval × ↥(faceStar K s)) :
    0 < starMass s (starHomotopyMap p) := by
  have hrs : starMass s (starRetract s p.2.val.val) = 1 :=
    starMass_eq_one_of_mem_barycentricFace
      (starRetract_mem_barycentricFace p.2.val.property p.2.property)
  have hx : 0 < starMass s p.2.val.val := p.2.property
  have ht0 : (0:ℝ) ≤ p.1.val := p.1.2.1
  have ht1 : p.1.val ≤ 1 := p.1.2.2
  rw [starMass_starHomotopyMap, hrs, mul_one]
  rcases eq_or_lt_of_le ht1 with h | h
  · rw [h]; norm_num
  · nlinarith

theorem continuous_starHomotopyMap :
    Continuous (fun p : unitInterval × ↥(faceStar K s) => starHomotopyMap p) := by
  have hval : Continuous fun p : unitInterval × ↥(faceStar K s) => (p.2.val.val : V → ℝ) :=
    (continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd
  have hret : Continuous fun p : unitInterval × ↥(faceStar K s) =>
      starRetract s p.2.val.val :=
    (continuous_starRetract_faceStar s).comp continuous_snd
  have ht : Continuous fun p : unitInterval × ↥(faceStar K s) => (p.1.val : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  exact continuous_pi fun v =>
    ((continuous_const.sub ht).mul ((continuous_apply v).comp hval)).add
      (ht.mul ((continuous_apply v).comp hret))

/-- The straight-line homotopy from the identity of the star to the
normalization retraction. -/
def starHomotopy (hsK : s ∈ K) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(faceStar K s))
      ((starInclusion hsK).comp (starRetractMap K s)) where
  toFun p := ⟨⟨starHomotopyMap p, starHomotopyMap_mem p⟩, starHomotopyMap_mem_faceStar p⟩
  continuous_toFun := (continuous_starHomotopyMap.subtype_mk _).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    change (1 - (0 : ℝ)) * x.val.val v + (0 : ℝ) * starRetract s x.val.val v = x.val.val v
    ring
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    change (1 - (1 : ℝ)) * x.val.val v + (1 : ℝ) * starRetract s x.val.val v
      = starRetract s x.val.val v
    ring

/-- **The star of a face deformation retracts onto the closed simplex of that
face.** -/
def starHomotopyEquiv (hsK : s ∈ K) :
    ContinuousMap.HomotopyEquiv ↥(faceStar K s) ↥(barycentricCarrier (s.powerset)) where
  toFun := starRetractMap K s
  invFun := starInclusion hsK
  left_inv := ⟨(starHomotopy hsK).symm⟩
  right_inv := by rw [starRetractMap_comp_inclusion hsK]

end Retraction

/-! ### The punctured star -/

/-- The intersection of the two members of the cover. -/
def starPunctured (K : Finset (Finset V)) (s : Finset V) : Set ↥(barycentricCarrier K) :=
  punctured K s ∩ faceStar K s

/-- The punctured realization and the star of `s` cover the realization. -/
theorem mem_punctured_or_faceStar (hs : s.Nonempty) (x : ↥(barycentricCarrier K)) :
    x ∈ punctured K s ∨ x ∈ faceStar K s := by
  by_cases h : x.val = faceCenter s
  · refine Or.inr ?_
    obtain ⟨v, hv⟩ := hs
    exact mem_faceStar_iff.2
      (starMass_pos_of_mem (h ▸ x.property.1) hv (by rw [h]; exact faceCenter_pos hv))
  · exact Or.inl h

section PuncturedRetraction

theorem continuous_starRetract_starPunctured :
    Continuous (fun x : ↥(starPunctured K s) => starRetract s x.val.val) := by
  have hval : Continuous fun x : ↥(starPunctured K s) => (x.val.val : V → ℝ) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hmass : Continuous fun x : ↥(starPunctured K s) => starMass s x.val.val :=
    (continuous_starMass s).comp hval
  have hnz : ∀ x : ↥(starPunctured K s), starMass s x.val.val ≠ 0 :=
    fun x => ne_of_gt x.property.2
  refine continuous_pi fun v => ?_
  by_cases hv : v ∈ s
  · simp only [starRetract, hv, ite_true]
    exact ((continuous_apply v).comp hval).div hmass hnz
  · simpa only [starRetract, hv, ite_false] using continuous_const

/-- The normalization retraction of the punctured star. -/
def starPuncturedRetract (hmax : ∀ t ∈ K, s ⊆ t → t = s) :
    C(↥(starPunctured K s), ↥(punctured (s.powerset) s)) where
  toFun x := ⟨⟨starRetract s x.val.val,
      starRetract_mem_carrier_powerset x.val.property x.property.2⟩,
    starRetract_ne_faceCenter hmax x.val.property x.property.1⟩
  continuous_toFun :=
    ((continuous_starRetract_starPunctured).subtype_mk _).subtype_mk _

/-- The inclusion of the punctured closed simplex into the punctured star. -/
def starPuncturedInclusion (hsK : s ∈ K) :
    C(↥(punctured (s.powerset) s), ↥(starPunctured K s)) where
  toFun y := ⟨⟨y.val.val, barycentricCarrier_powerset_subset hsK y.val.property⟩,
    y.property,
    starMass_pos_of_mem_barycentricFace (by
      rw [← barycentricCarrier_powerset]; exact y.val.property)⟩
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

theorem starPuncturedRetract_comp_inclusion (hsK : s ∈ K) (hmax : ∀ t ∈ K, s ⊆ t → t = s) :
    (starPuncturedRetract hmax).comp (starPuncturedInclusion hsK) = ContinuousMap.id _ := by
  ext y
  have hy : y.val.val ∈ barycentricFace s := by
    rw [← barycentricCarrier_powerset]; exact y.val.property
  exact congrFun (starRetract_eq_self hy) _

theorem starHomotopyMap_ne_faceCenter (hmax : ∀ t ∈ K, s ⊆ t → t = s)
    (p : unitInterval × ↥(faceStar K s))
    (hne : p.2.val.val ≠ faceCenter s) : starHomotopyMap p ≠ faceCenter s := by
  by_cases hface : (p.2.val.val : V → ℝ) ∈ barycentricFace s
  · have hself : starRetract s p.2.val.val = p.2.val.val := starRetract_eq_self hface
    intro hEq
    refine hne ?_
    rw [← hEq]
    funext v
    simp only [starHomotopyMap, hself]
    ring
  · obtain ⟨v, hv, hxv⟩ :=
      exists_eq_zero_of_notMem_barycentricFace hmax p.2.val.property hface
    intro hEq
    have h1 := congrFun hEq v
    rw [starHomotopyMap] at h1
    simp only [hxv, mul_zero, zero_add, starRetract, ite_eq_left_of_eq_true _ _ (eq_true hv),
      zero_div] at h1
    exact absurd h1.symm (ne_of_gt (faceCenter_pos hv))

/-- The straight-line homotopy on the punctured star. -/
def starPuncturedHomotopy (hsK : s ∈ K) (hmax : ∀ t ∈ K, s ⊆ t → t = s) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(starPunctured K s))
      ((starPuncturedInclusion hsK).comp (starPuncturedRetract hmax)) where
  toFun p := ⟨⟨starHomotopyMap (⟨p.1, ⟨p.2.val, p.2.property.2⟩⟩), starHomotopyMap_mem _⟩,
    starHomotopyMap_ne_faceCenter hmax _ p.2.property.1,
    starHomotopyMap_mem_faceStar _⟩
  continuous_toFun := by
    have hsub : Continuous fun p : unitInterval × ↥(starPunctured K s) =>
        (⟨p.2.val, p.2.property.2⟩ : ↥(faceStar K s)) :=
      Continuous.subtype_mk (continuous_subtype_val.comp continuous_snd) _
    have hpair : Continuous fun p : unitInterval × ↥(starPunctured K s) =>
        ((p.1, (⟨p.2.val, p.2.property.2⟩ : ↥(faceStar K s))) :
          unitInterval × ↥(faceStar K s)) :=
      continuous_fst.prodMk hsub
    exact (((continuous_starHomotopyMap.comp hpair).subtype_mk _).subtype_mk _)
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    change (1 - (0 : ℝ)) * x.val.val v + (0 : ℝ) * starRetract s x.val.val v = x.val.val v
    ring
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    change (1 - (1 : ℝ)) * x.val.val v + (1 : ℝ) * starRetract s x.val.val v
      = starRetract s x.val.val v
    ring

/-- **The punctured star deformation retracts onto the punctured closed
simplex.** -/
def starPuncturedHomotopyEquiv (hsK : s ∈ K) (hmax : ∀ t ∈ K, s ⊆ t → t = s) :
    ContinuousMap.HomotopyEquiv ↥(starPunctured K s) ↥(punctured (s.powerset) s) where
  toFun := starPuncturedRetract hmax
  invFun := starPuncturedInclusion hsK
  left_inv := ⟨(starPuncturedHomotopy hsK hmax).symm⟩
  right_inv := by rw [starPuncturedRetract_comp_inclusion hsK hmax]

/-- **The intersection of the two members of the cover deformation retracts
onto the realization of the boundary of `s`.** -/
def starPuncturedBoundaryHomotopyEquiv (hs : s.Nonempty) (hsK : s ∈ K)
    (hmax : ∀ t ∈ K, s ⊆ t → t = s) :
    ContinuousMap.HomotopyEquiv ↥(starPunctured K s)
      ↥(barycentricCarrier (boundaryFamily s)) :=
  (starPuncturedHomotopyEquiv hsK hmax).trans
    (puncturedHomotopyEquiv (faceClosed_powerset s) hs
      (fun _ ht hst => Finset.Subset.antisymm (Finset.mem_powerset.1 ht) hst))

end PuncturedRetraction

end AffineTverberg.Simplicial
