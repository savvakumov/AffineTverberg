import AffineTverberg.LinkCofaceShift
import AffineTverberg.SimplicialCoboundary

set_option linter.style.header false

/-!
# The coface double complex

Fix a finite face-closed family `K` on a finite linearly ordered vertex type and
a set `G` of "good" vertices.  The *coface double complex* has, in bidegree
`(p, q)`, the coefficient functions supported on pairs `(s, t)` where `s` is a
face of `K` with `p` vertices which is **not** contained in `G`, and `t` is a
coface of `s` in `K` with `q` vertices.

* the vertical differential `dvMap` is the coface differential
  `cofaceBoundary s` in the second variable — the differential of the relative
  chain complex `C(K, K ∖ star s)` already used in `CofaceRelativeChains`;
* the horizontal differential `dhMap` is the oriented simplicial coboundary in
  the first variable, followed by restriction to cofaces — the natural
  transition maps of the coface complexes.

The two differentials commute, and `dtotMap`, the total differential with the
column sign, squares to zero.  Everything here is elementary linear algebra on
explicit coefficient functions; no homological algebra package is used.

The two "staircase" theorems of this file are the degeneration statements for
the two filtrations of the double complex:

* `exists_rowChains_of_cycle` — every total cycle is homologous to a cycle
  concentrated in the column `#s = 1`.  This uses only the explicit contracting
  homotopy of the rows (relative cochain complexes of simplices), so it is
  unconditional.
* `dtotMap_topChains_of_mem` — a total boundary which lies in the top row
  `#t = Q` is already a horizontal boundary inside the top row.  This uses the
  exactness of the coface complexes below the top degree, which is supplied by
  the caller.
-/

noncomputable section

namespace AffineTverberg.Simplicial

variable {V : Type} [Fintype V] [LinearOrder V]

/-! ### The two differentials -/

/-- Vertical differential: the coface differential in the coface variable. -/
def dvMap (V : Type) [Fintype V] [LinearOrder V] :
    (Finset V → Finset V → ℝ) →ₗ[ℝ] (Finset V → Finset V → ℝ) where
  toFun c := fun s => cofaceBoundary s (c s)
  map_add' c d := by funext s; simp only [Pi.add_apply, map_add]
  map_smul' r c := by funext s; simp only [Pi.smul_apply, RingHom.id_apply, map_smul]

/-- Horizontal differential: the oriented coboundary in the face variable,
followed by restriction to cofaces. -/
def dhMap (V : Type) [Fintype V] [LinearOrder V] :
    (Finset V → Finset V → ℝ) →ₗ[ℝ] (Finset V → Finset V → ℝ) where
  toFun c := fun s => cofaceRestriction s
    (fun t => ∑ v ∈ s, orientedSign ℝ (s.erase v) v * c (s.erase v) t)
  map_add' c d := by
    funext s t
    by_cases h : s ⊆ t <;>
      simp [cofaceRestriction, h, mul_add, Finset.sum_add_distrib]
  map_smul' r c := by
    funext s t
    by_cases h : s ⊆ t <;>
      simp [cofaceRestriction, h, Finset.mul_sum, mul_comm, mul_assoc]

/-- The column sign `(-1) ^ #s`. -/
def signSwitch (V : Type) [Fintype V] [LinearOrder V] :
    (Finset V → Finset V → ℝ) →ₗ[ℝ] (Finset V → Finset V → ℝ) where
  toFun c := fun s => ((-1 : ℝ) ^ s.card) • c s
  map_add' c d := by funext s t; simp [mul_add]
  map_smul' r c := by funext s t; simp; ring

/-- The total differential of the coface double complex. -/
def dtotMap (V : Type) [Fintype V] [LinearOrder V] :
    (Finset V → Finset V → ℝ) →ₗ[ℝ] (Finset V → Finset V → ℝ) :=
  (signSwitch V).comp (dvMap V) + dhMap V

theorem dvMap_apply (c : Finset V → Finset V → ℝ) (s : Finset V) :
    dvMap V c s = cofaceBoundary s (c s) := rfl

theorem dhMap_apply (c : Finset V → Finset V → ℝ) (s t : Finset V) :
    dhMap V c s t =
      if s ⊆ t then ∑ v ∈ s, orientedSign ℝ (s.erase v) v * c (s.erase v) t else 0 := rfl

theorem dhMap_apply_of_subset {c : Finset V → Finset V → ℝ} {s t : Finset V} (h : s ⊆ t) :
    dhMap V c s t = ∑ v ∈ s, orientedSign ℝ (s.erase v) v * c (s.erase v) t := by
  simp only [dhMap_apply, h, ↓reduceIte]

theorem dhMap_apply_of_not_subset {c : Finset V → Finset V → ℝ} {s t : Finset V} (h : ¬ s ⊆ t) :
    dhMap V c s t = 0 := by
  simp only [dhMap_apply, h, ↓reduceIte]

theorem dtotMap_apply (c : Finset V → Finset V → ℝ) (s t : Finset V) :
    dtotMap V c s t = ((-1 : ℝ) ^ s.card) * cofaceBoundary s (c s) t + dhMap V c s t := rfl

/-! ### The differentials commute and square to zero -/

theorem dvMap_dvMap (c : Finset V → Finset V → ℝ) : dvMap V (dvMap V c) = 0 := by
  funext s
  exact cofaceBoundary_squared s (c s)

theorem dhMap_dhMap (c : Finset V → Finset V → ℝ) : dhMap V (dhMap V c) = 0 := by
  classical
  funext s t
  by_cases hst : s ⊆ t
  · rw [dhMap_apply_of_subset hst]
    have hexp : ∀ v ∈ s, orientedSign ℝ (s.erase v) v * dhMap V c (s.erase v) t
        = ∑ w ∈ s.erase v, orientedSign ℝ (s.erase v) v *
            (orientedSign ℝ ((s.erase v).erase w) w * c ((s.erase v).erase w) t) := by
      intro v _
      rw [dhMap_apply_of_subset ((Finset.erase_subset v s).trans hst), Finset.mul_sum]
    rw [Finset.sum_congr rfl hexp, Finset.sum_sigma']
    refine Finset.sum_involution (fun x _ => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_
    · rintro ⟨v, w⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_erase] at hx
      obtain ⟨hv, hwv, hw⟩ := hx
      have hvw : v ≠ w := fun h => hwv h.symm
      simp only [Finset.erase_right_comm (s := s) (a := w) (b := v)]
      have hvnot : v ∉ ((s.erase v).erase w) := fun h =>
        (Finset.notMem_erase v s) (Finset.mem_of_mem_erase h)
      have hwnot : w ∉ ((s.erase v).erase w) := Finset.notMem_erase w _
      have h1 : s.erase v = insert w ((s.erase v).erase w) := by
        rw [Finset.insert_erase (Finset.mem_erase.mpr ⟨hwv, hw⟩)]
      have h2 : s.erase w = insert v ((s.erase v).erase w) := by
        rw [Finset.erase_right_comm, Finset.insert_erase (Finset.mem_erase.mpr ⟨hvw, hv⟩)]
      have hsign := orientedSign_antisymm (𝕜 := ℝ) (f := (s.erase v).erase w) hvnot hwnot hvw
      set g := (s.erase v).erase w with hgdef
      rw [h1, h2]
      linear_combination (c g t) * hsign
    · rintro ⟨v, w⟩ hx _
      simp only [Finset.mem_sigma, Finset.mem_erase] at hx
      simp only [ne_eq, Sigma.mk.injEq, not_and]
      intro h
      exact absurd h hx.2.1
    · rintro ⟨v, w⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_erase] at hx ⊢
      exact ⟨hx.2.2, fun h => hx.2.1 h.symm, hx.1⟩
    · rintro ⟨v, w⟩ _
      rfl
  · exact dhMap_apply_of_not_subset hst

theorem dvMap_dhMap (c : Finset V → Finset V → ℝ) :
    dvMap V (dhMap V c) = dhMap V (dvMap V c) := by
  funext s t
  by_cases hst : s ⊆ t
  · have hlhs : dvMap V (dhMap V c) s t
        = ∑ v ∈ s, orientedSign ℝ (s.erase v) v * (boundary ℝ V (c (s.erase v))) t := by
      change cofaceBoundary s (dhMap V c s) t = _
      have h0 : cofaceBoundary s (dhMap V c s) t = (boundary ℝ V (dhMap V c s)) t := by
        simp [cofaceBoundary, cofaceRestriction, hst]
      rw [h0, boundary_apply]
      have hexp : ∀ w ∈ tᶜ, orientedSign ℝ t w * dhMap V c s (insert w t)
          = ∑ v ∈ s, orientedSign ℝ t w * (orientedSign ℝ (s.erase v) v
              * c (s.erase v) (insert w t)) := by
        intro w _
        rw [dhMap_apply_of_subset (hst.trans (Finset.subset_insert w t)), Finset.mul_sum]
      rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [boundary_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring
    have hrhs : dhMap V (dvMap V c) s t
        = ∑ v ∈ s, orientedSign ℝ (s.erase v) v * (boundary ℝ V (c (s.erase v))) t := by
      rw [dhMap_apply_of_subset hst]
      refine Finset.sum_congr rfl fun v _ => ?_
      have hval : dvMap V c (s.erase v) t = (boundary ℝ V (c (s.erase v))) t := by
        have hsub : s.erase v ⊆ t := (Finset.erase_subset v s).trans hst
        simp [dvMap_apply, cofaceBoundary, cofaceRestriction, hsub]
      rw [hval]
    rw [hlhs, hrhs]
  · have h1 : dvMap V (dhMap V c) s t = 0 := by
      change cofaceBoundary s (dhMap V c s) t = 0
      simp [cofaceBoundary, cofaceRestriction, hst]
    have h2 : dhMap V (dvMap V c) s t = 0 := dhMap_apply_of_not_subset hst
    rw [h1, h2]

theorem dvMap_signSwitch (c : Finset V → Finset V → ℝ) :
    dvMap V (signSwitch V c) = signSwitch V (dvMap V c) := by
  funext s t
  change cofaceBoundary s (((-1 : ℝ) ^ s.card) • c s) t
    = ((-1 : ℝ) ^ s.card) • cofaceBoundary s (c s) t
  rw [map_smul]
  rfl

theorem dhMap_signSwitch (c : Finset V → Finset V → ℝ) :
    dhMap V (signSwitch V c) = - signSwitch V (dhMap V c) := by
  funext s t
  have hrhs : (- signSwitch V (dhMap V c)) s t
      = -(((-1 : ℝ) ^ s.card) * dhMap V c s t) := rfl
  rw [hrhs]
  by_cases hst : s ⊆ t
  · rw [dhMap_apply_of_subset hst, dhMap_apply_of_subset hst, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hcard : (s.erase v).card + 1 = s.card := by
      rw [Finset.card_erase_of_mem hv]
      have hpos : 1 ≤ s.card := Finset.card_pos.mpr ⟨v, hv⟩
      omega
    have hpow : ((-1 : ℝ) ^ (s.erase v).card) = -((-1 : ℝ) ^ s.card) := by
      rw [← hcard, pow_succ]
      ring
    change orientedSign ℝ (s.erase v) v * (((-1 : ℝ) ^ (s.erase v).card) • c (s.erase v) t) = _
    rw [smul_eq_mul, hpow]
    ring
  · rw [dhMap_apply_of_not_subset hst, dhMap_apply_of_not_subset hst]
    simp

theorem dtotMap_dtotMap (c : Finset V → Finset V → ℝ) : dtotMap V (dtotMap V c) = 0 := by
  have hexp : ∀ x : Finset V → Finset V → ℝ,
      dtotMap V x = signSwitch V (dvMap V x) + dhMap V x := fun _ => rfl
  rw [hexp (dtotMap V c), hexp c]
  rw [map_add (dvMap V), map_add (dhMap V), dvMap_signSwitch, dvMap_dhMap,
    dhMap_signSwitch, dhMap_dhMap, dvMap_dvMap]
  simp only [map_zero, zero_add, add_zero]
  abel

/-! ### Support conditions -/

/-- Coefficient functions of two variables with a prescribed support condition. -/
def suppChains (P : Finset V → Finset V → Prop) :
    Submodule ℝ (Finset V → Finset V → ℝ) where
  carrier := {c | ∀ s t, c s t ≠ 0 → P s t}
  add_mem' := by
    intro c d hc hd s t hst
    by_cases h : c s t = 0
    · exact hd s t (by simpa [h] using hst)
    · exact hc s t h
  zero_mem' := by intro s t hst; simp at hst
  smul_mem' := by
    intro a c hc s t hst
    exact hc s t (fun h => hst (by simp [Pi.smul_apply, h]))

omit [Fintype V] [LinearOrder V] in
theorem mem_suppChains_iff {P : Finset V → Finset V → Prop}
    {c : Finset V → Finset V → ℝ} :
    c ∈ suppChains P ↔ ∀ s t, c s t ≠ 0 → P s t := Iff.rfl

/-- The bidegree condition of the coface double complex in total degree `k`. -/
def DblSupport (K : Finset (Finset V)) (G : Finset V) (k : ℕ) (s t : Finset V) : Prop :=
  s ∈ K ∧ ¬ s ⊆ G ∧ t ∈ K ∧ s ⊆ t ∧ t.card = s.card + k

/-- Total degree `k` part of the coface double complex. -/
def dblChains (K : Finset (Finset V)) (G : Finset V) (k : ℕ) :
    Submodule ℝ (Finset V → Finset V → ℝ) :=
  suppChains (DblSupport K G k)

omit [Fintype V] [LinearOrder V] in
theorem mem_dblChains_iff {K : Finset (Finset V)} {G : Finset V} {k : ℕ}
    {c : Finset V → Finset V → ℝ} :
    c ∈ dblChains K G k ↔ ∀ s t, c s t ≠ 0 → DblSupport K G k s t := Iff.rfl

theorem dvMap_mem_dblChains {K : Finset (Finset V)} (hK : FaceClosed K) {G : Finset V} {k : ℕ}
    {c : Finset V → Finset V → ℝ} (hc : c ∈ dblChains K G (k + 1)) :
    dvMap V c ∈ dblChains K G k := by
  classical
  intro s t hst
  have hsub : s ⊆ t := by
    by_contra h
    exact hst (by simp [dvMap_apply, cofaceBoundary, cofaceRestriction, h])
  have hval : dvMap V c s t = ∑ v ∈ tᶜ, orientedSign ℝ t v * c s (insert v t) := by
    simp [dvMap_apply, cofaceBoundary, cofaceRestriction, hsub]
  rw [hval] at hst
  obtain ⟨v, hv, hne⟩ : ∃ v ∈ tᶜ, orientedSign ℝ t v * c s (insert v t) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, ne_eq, not_not] at hcon
    exact hst (Finset.sum_eq_zero fun v hv => hcon v hv)
  have hcv : c s (insert v t) ≠ 0 := fun h => hne (by rw [h, mul_zero])
  obtain ⟨hsK, hsG, hins, hsins, hcard⟩ := hc s (insert v t) hcv
  have hvt : v ∉ t := by simpa using hv
  refine ⟨hsK, hsG, hK _ hins t (Finset.subset_insert v t), hsub, ?_⟩
  rw [Finset.card_insert_of_notMem hvt] at hcard
  omega

theorem dhMap_mem_dblChains {K : Finset (Finset V)} (hK : FaceClosed K) {G : Finset V} {k : ℕ}
    {c : Finset V → Finset V → ℝ} (hc : c ∈ dblChains K G (k + 1)) :
    dhMap V c ∈ dblChains K G k := by
  classical
  intro s t hst
  have hsub : s ⊆ t := by
    by_contra h
    exact hst (dhMap_apply_of_not_subset h)
  rw [dhMap_apply_of_subset hsub] at hst
  obtain ⟨v, hv, hne⟩ : ∃ v ∈ s, orientedSign ℝ (s.erase v) v * c (s.erase v) t ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, ne_eq, not_not] at hcon
    exact hst (Finset.sum_eq_zero fun v hv => hcon v hv)
  have hcv : c (s.erase v) t ≠ 0 := fun h => hne (by rw [h, mul_zero])
  obtain ⟨_, hsG, htK, _, hcard⟩ := hc (s.erase v) t hcv
  refine ⟨hK t htK s hsub, ?_, htK, hsub, ?_⟩
  · exact fun h => hsG ((Finset.erase_subset v s).trans h)
  · rw [Finset.card_erase_of_mem hv] at hcard
    have hpos : 1 ≤ s.card := Finset.card_pos.mpr ⟨v, hv⟩
    omega

theorem dtotMap_mem_dblChains {K : Finset (Finset V)} (hK : FaceClosed K) {G : Finset V} {k : ℕ}
    {c : Finset V → Finset V → ℝ} (hc : c ∈ dblChains K G (k + 1)) :
    dtotMap V c ∈ dblChains K G k := by
  have h1 := dvMap_mem_dblChains hK hc
  have h2 := dhMap_mem_dblChains hK hc
  have h3 : signSwitch V (dvMap V c) ∈ dblChains K G k := by
    intro s t hst
    refine h1 s t fun h => hst ?_
    simp only [signSwitch, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul, h,
      mul_zero]
  exact Submodule.add_mem _ h3 h2

/-! ### The row homotopy -/

/-- The apex used to contract a row: a good vertex of `t` if there is one, and
otherwise the least vertex of `t`.  It is returned as a subsingleton finset so
that no vertex has to exist. -/
def apexSet (G t : Finset V) : Finset V :=
  if h : (t ∩ G).Nonempty then {(t ∩ G).min' h}
  else if h2 : t.Nonempty then {t.min' h2} else ∅

omit [Fintype V] in
theorem apexSet_subset (G t : Finset V) : apexSet G t ⊆ t := by
  unfold apexSet
  split_ifs with h h2
  · intro v hv
    rw [Finset.mem_singleton] at hv
    subst hv
    exact Finset.mem_of_mem_inter_left ((t ∩ G).min'_mem h)
  · intro v hv
    rw [Finset.mem_singleton] at hv
    subst hv
    exact t.min'_mem h2
  · simp

omit [Fintype V] in
theorem apexSet_mem_good {G t : Finset V} (h : (t ∩ G).Nonempty) {v : V}
    (hv : v ∈ apexSet G t) : v ∈ G := by
  unfold apexSet at hv
  simp only [h, ↓reduceDIte, Finset.mem_singleton] at hv
  subst hv
  exact Finset.mem_of_mem_inter_right ((t ∩ G).min'_mem h)

omit [Fintype V] in
theorem apexSet_eq_empty_iff (G t : Finset V) : apexSet G t = ∅ ↔ t = ∅ := by
  unfold apexSet
  split_ifs with h h2
  · simp only [Finset.singleton_ne_empty, false_iff]
    intro ht
    rw [ht] at h
    simp at h
  · simp only [Finset.singleton_ne_empty, false_iff]
    intro ht
    exact absurd (ht ▸ h2) (by simp)
  · simp only [true_iff]
    exact Finset.not_nonempty_iff_eq_empty.mp h2

omit [Fintype V] in
theorem apexSet_cases (G t : Finset V) :
    apexSet G t = ∅ ∨ ∃ w ∈ t, apexSet G t = {w} := by
  unfold apexSet
  split_ifs with h h2
  · exact Or.inr ⟨_, Finset.mem_of_mem_inter_left ((t ∩ G).min'_mem h), rfl⟩
  · exact Or.inr ⟨_, t.min'_mem h2, rfl⟩
  · exact Or.inl rfl

omit [Fintype V] in
/-- The sign cancellation for the row contraction. -/
theorem orientedSign_swap {f : Finset V} {v w : V} (hv : v ∉ f) (hw : w ∉ f) (hvw : v ≠ w) :
    orientedSign ℝ f v * orientedSign ℝ f w
      + orientedSign ℝ (insert v f) w * orientedSign ℝ (insert w f) v = 0 := by
  have hac := orientedSign_antisymm (𝕜 := ℝ) hv hw hvw
  have ha := orientedSign_sq (𝕜 := ℝ) f v
  have hb := orientedSign_sq (𝕜 := ℝ) f w
  have hc := orientedSign_sq (𝕜 := ℝ) (insert v f) w
  have hd := orientedSign_sq (𝕜 := ℝ) (insert w f) v
  generalize orientedSign ℝ f v = a at *
  generalize orientedSign ℝ f w = b at *
  generalize orientedSign ℝ (insert v f) w = c at *
  generalize orientedSign ℝ (insert w f) v = d at *
  rcases mul_self_eq_one_iff.mp ha with rfl | rfl <;>
    rcases mul_self_eq_one_iff.mp hb with rfl | rfl <;>
      rcases mul_self_eq_one_iff.mp hc with rfl | rfl <;>
        rcases mul_self_eq_one_iff.mp hd with rfl | rfl <;>
          simp_all

/-- The contraction of a row of the double complex against the apex. -/
def rowHomotopy (G : Finset V) :
    (Finset V → Finset V → ℝ) →ₗ[ℝ] (Finset V → Finset V → ℝ) where
  toFun c := fun s t => ∑ v ∈ apexSet G t,
    if v ∈ s then 0 else orientedSign ℝ s v * c (insert v s) t
  map_add' c d := by
    funext s t
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h : v ∈ s <;> simp [h, mul_add]
  map_smul' r c := by
    funext s t
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h : v ∈ s
    · simp [h]
    · simp [h]
      ring

omit [Fintype V] in
theorem rowHomotopy_apply (G : Finset V) (c : Finset V → Finset V → ℝ) (s t : Finset V) :
    rowHomotopy G c s t = ∑ v ∈ apexSet G t,
      if v ∈ s then 0 else orientedSign ℝ s v * c (insert v s) t := rfl

omit [Fintype V] in
/-- The row homotopy lands in the double complex, one column lower. -/
theorem rowHomotopy_mem_dblChains {K : Finset (Finset V)} (hK : FaceClosed K) {G : Finset V}
    {k p : ℕ} (hp : 2 ≤ p) {c : Finset V → Finset V → ℝ} (hc : c ∈ dblChains K G k)
    (hlev : ∀ s t, c s t ≠ 0 → s.card = p) :
    rowHomotopy G c ∈ dblChains K G (k + 1) := by
  classical
  intro u t hu
  rw [rowHomotopy_apply] at hu
  obtain ⟨v, hv, hne⟩ : ∃ v ∈ apexSet G t,
      (if v ∈ u then (0:ℝ) else orientedSign ℝ u v * c (insert v u) t) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, ne_eq, not_not] at hcon
    exact hu (Finset.sum_eq_zero fun v hv => hcon v hv)
  have hvu : v ∉ u := by
    by_contra h
    simp only [h, ↓reduceIte] at hne
    exact hne rfl
  simp only [hvu, ↓reduceIte] at hne
  have hcv : c (insert v u) t ≠ 0 := fun h => hne (by rw [h, mul_zero])
  obtain ⟨hinsK, hinsG, htK, hinsub, hcard⟩ := hc (insert v u) t hcv
  have hcardp : (insert v u).card = p := hlev _ _ hcv
  have husub : u ⊆ t := (Finset.subset_insert v u).trans hinsub
  refine ⟨hK _ hinsK u (Finset.subset_insert v u), ?_, htK, husub, ?_⟩
  · intro huG
    have hvG : v ∉ G := fun hvG => hinsG (Finset.insert_subset hvG huG)
    by_cases hinter : (t ∩ G).Nonempty
    · exact hvG (apexSet_mem_good hinter hv)
    · have hempty : t ∩ G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hinter
      have huempty : u = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
        have hmem : x ∈ t ∩ G := Finset.mem_inter.mpr ⟨husub hx, huG hx⟩
        rw [hempty] at hmem
        exact absurd hmem (Finset.notMem_empty x)
      rw [huempty] at hcardp
      simp at hcardp
      omega
  · rw [Finset.card_insert_of_notMem hvu] at hcard
    omega

/-- **Row exactness.**  A horizontal cocycle is a horizontal coboundary, by the
explicit contraction against the apex. -/
theorem dhMap_rowHomotopy {K : Finset (Finset V)} {G : Finset V} {k : ℕ}
    {c : Finset V → Finset V → ℝ} (hc : c ∈ dblChains K G k) (hdh : dhMap V c = 0) :
    dhMap V (rowHomotopy G c) = c := by
  classical
  funext s t
  by_cases hst : s ⊆ t
  · rw [dhMap_apply_of_subset hst]
    rcases apexSet_cases G t with hA | ⟨w, hwt, hA⟩
    · have hzero : ∀ v ∈ s, orientedSign ℝ (s.erase v) v * rowHomotopy G c (s.erase v) t = 0 := by
        intro v _
        rw [rowHomotopy_apply, hA]
        simp
      rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
      have ht : t = ∅ := (apexSet_eq_empty_iff G t).mp hA
      have hs : s = ∅ := Finset.subset_empty.mp (ht ▸ hst)
      have hcz : c s t = 0 := by
        by_contra hne
        exact (hc s t hne).2.1 (hs ▸ (Finset.empty_subset G))
      rw [hcz]
    · have hterm : ∀ v ∈ s, orientedSign ℝ (s.erase v) v * rowHomotopy G c (s.erase v) t
          = orientedSign ℝ (s.erase v) v *
            (if w ∈ s.erase v then 0
              else orientedSign ℝ (s.erase v) w * c (insert w (s.erase v)) t) := by
        intro v _
        rw [rowHomotopy_apply, hA, Finset.sum_singleton]
      rw [Finset.sum_congr rfl hterm]
      by_cases hws : w ∈ s
      · rw [Finset.sum_eq_single w]
        · have hcond : ¬ (w ∈ s.erase w) := Finset.notMem_erase w s
          simp only [hcond, ↓reduceIte]
          rw [Finset.insert_erase hws, ← mul_assoc, orientedSign_sq, one_mul]
        · intro v hv hvw
          have hcond : w ∈ s.erase v := Finset.mem_erase.mpr ⟨fun h => hvw h.symm, hws⟩
          simp only [hcond, ↓reduceIte, mul_zero]
        · intro h
          exact absurd hws h
      · have hsimp : ∀ v ∈ s, orientedSign ℝ (s.erase v) v *
            (if w ∈ s.erase v then 0
              else orientedSign ℝ (s.erase v) w * c (insert w (s.erase v)) t)
            = -(orientedSign ℝ s w *
                (orientedSign ℝ (insert w (s.erase v)) v * c (insert w (s.erase v)) t)) := by
          intro v hv
          have hwerase : w ∉ s.erase v := fun h => hws (Finset.mem_of_mem_erase h)
          simp only [hwerase, ↓reduceIte]
          have hvnot : v ∉ s.erase v := Finset.notMem_erase v s
          have hvw : v ≠ w := fun h => hws (h ▸ hv)
          have hsw := orientedSign_swap (f := s.erase v) hvnot hwerase hvw
          rw [Finset.insert_erase hv] at hsw
          linear_combination (c (insert w (s.erase v)) t) * hsw
        rw [Finset.sum_congr rfl hsimp]
        have h0 : dhMap V c (insert w s) t = 0 := by rw [hdh]; rfl
        rw [dhMap_apply_of_subset (Finset.insert_subset hwt hst), Finset.sum_insert hws,
          Finset.erase_insert hws] at h0
        have hrew : ∀ v ∈ s, orientedSign ℝ ((insert w s).erase v) v * c ((insert w s).erase v) t
            = orientedSign ℝ (insert w (s.erase v)) v * c (insert w (s.erase v)) t := by
          intro v hv
          have hvw : v ≠ w := fun h => hws (h ▸ hv)
          rw [Finset.erase_insert_of_ne (Ne.symm hvw)]
        rw [Finset.sum_congr rfl hrew] at h0
        have hsq := orientedSign_sq (𝕜 := ℝ) s w
        have hpull : ∑ v ∈ s, -(orientedSign ℝ s w *
            (orientedSign ℝ (insert w (s.erase v)) v * c (insert w (s.erase v)) t))
            = -(orientedSign ℝ s w * ∑ v ∈ s,
              (orientedSign ℝ (insert w (s.erase v)) v * c (insert w (s.erase v)) t)) := by
          rw [Finset.mul_sum, Finset.sum_neg_distrib]
        rw [hpull]
        linear_combination (- orientedSign ℝ s w) * h0 + (c s t) * hsq
  · rw [dhMap_apply_of_not_subset hst]
    have hcz : c s t = 0 := by
      by_contra hne
      exact hst (hc s t hne).2.2.2.1
    rw [hcz]

/-! ### The two staircase theorems -/

/-- Chains concentrated in the first column, killed by the horizontal
differential: the image of the reduced chain complex of the induced subcomplex
on the bad vertices. -/
def rowChains (K : Finset (Finset V)) (G : Finset V) (k : ℕ) :
    Submodule ℝ (Finset V → Finset V → ℝ) :=
  suppChains (fun s t => DblSupport K G k s t ∧ s.card = 1) ⊓ LinearMap.ker (dhMap V)

/-- Chains concentrated in the top row, killed by the vertical differential:
the top cycles of the coface complexes. -/
def topChains (K : Finset (Finset V)) (G : Finset V) (Q k : ℕ) :
    Submodule ℝ (Finset V → Finset V → ℝ) :=
  suppChains (fun s t => DblSupport K G k s t ∧ t.card = Q) ⊓ LinearMap.ker (dvMap V)

theorem rowChains_le_dblChains (K : Finset (Finset V)) (G : Finset V) (k : ℕ) :
    rowChains K G k ≤ dblChains K G k := fun _ hc s t hst => (hc.1 s t hst).1

theorem topChains_le_dblChains (K : Finset (Finset V)) (G : Finset V) (Q k : ℕ) :
    topChains K G Q k ≤ dblChains K G k := fun _ hc s t hst => (hc.1 s t hst).1

/-- The part of a double chain in a fixed column. -/
def levelPart (j : ℕ) (c : Finset V → Finset V → ℝ) : Finset V → Finset V → ℝ :=
  fun s t => if s.card = j then c s t else 0

omit [Fintype V] [LinearOrder V] in
theorem levelPart_mem {K : Finset (Finset V)} {G : Finset V} {k j : ℕ}
    {c : Finset V → Finset V → ℝ} (hc : c ∈ dblChains K G k) :
    levelPart j c ∈ dblChains K G k := by
  intro s t hst
  refine hc s t ?_
  intro h
  rw [levelPart, h] at hst
  simp at hst

omit [Fintype V] [LinearOrder V] in
theorem levelPart_level {j : ℕ} (c : Finset V → Finset V → ℝ) :
    ∀ s t, levelPart j c s t ≠ 0 → s.card = j := by
  intro s t hst
  by_contra h
  simp only [levelPart, h, ↓reduceIte] at hst
  exact hst rfl

omit [Fintype V] in
theorem rowHomotopy_level {G : Finset V} {p : ℕ} {c : Finset V → Finset V → ℝ}
    (hlev : ∀ s t, c s t ≠ 0 → s.card = p + 1) :
    ∀ s t, rowHomotopy G c s t ≠ 0 → s.card = p := by
  classical
  intro u t hu
  rw [rowHomotopy_apply] at hu
  obtain ⟨v, hv, hne⟩ : ∃ v ∈ apexSet G t,
      (if v ∈ u then (0:ℝ) else orientedSign ℝ u v * c (insert v u) t) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, ne_eq, not_not] at hcon
    exact hu (Finset.sum_eq_zero fun v hv => hcon v hv)
  have hvu : v ∉ u := by
    by_contra h
    simp only [h, ↓reduceIte] at hne
    exact hne rfl
  simp only [hvu, ↓reduceIte] at hne
  have hcv : c (insert v u) t ≠ 0 := fun h => hne (by rw [h, mul_zero])
  have hcard := hlev _ _ hcv
  rw [Finset.card_insert_of_notMem hvu] at hcard
  omega

omit [Fintype V] [LinearOrder V] in
theorem zero_of_card_gt {q : ℕ} {c : Finset V → Finset V → ℝ}
    (hbound : ∀ s t, c s t ≠ 0 → s.card ≤ q) {s : Finset V} (hs : q < s.card) : c s = 0 := by
  funext t
  by_contra hne
  exact absurd (hbound s t hne) (by omega)

/-- The top layer of a total cycle is a horizontal cocycle. -/
theorem dhMap_levelPart_top {q : ℕ} {c : Finset V → Finset V → ℝ} (hcyc : dtotMap V c = 0)
    (hbound : ∀ s t, c s t ≠ 0 → s.card ≤ q) :
    dhMap V (levelPart q c) = 0 := by
  classical
  funext s t
  by_cases hst : s ⊆ t
  · rw [dhMap_apply_of_subset hst]
    by_cases hcard : s.card = q + 1
    · have hterm : ∀ v ∈ s, orientedSign ℝ (s.erase v) v * levelPart q c (s.erase v) t
          = orientedSign ℝ (s.erase v) v * c (s.erase v) t := by
        intro v hv
        have herase : (s.erase v).card = q := by
          rw [Finset.card_erase_of_mem hv, hcard]
          omega
        simp only [levelPart, herase, ↓reduceIte]
      rw [Finset.sum_congr rfl hterm]
      have hdh : dhMap V c s t = 0 := by
        have h0 : dtotMap V c s t = 0 := by rw [hcyc]; rfl
        rw [dtotMap_apply] at h0
        have hcs : c s = 0 := zero_of_card_gt hbound (by omega)
        rw [hcs] at h0
        simpa using h0
      rw [dhMap_apply_of_subset hst] at hdh
      exact hdh
    · refine Finset.sum_eq_zero fun v hv => ?_
      have hne : (s.erase v).card ≠ q := by
        rw [Finset.card_erase_of_mem hv]
        have hpos : 1 ≤ s.card := Finset.card_pos.mpr ⟨v, hv⟩
        omega
      simp only [levelPart, hne, ↓reduceIte, mul_zero]
  · exact dhMap_apply_of_not_subset hst

/-- The inductive form of the first staircase theorem: a total cycle supported
in the columns of at most `j + 1` vertices. -/
theorem exists_rowChains_of_cycle_aux {K : Finset (Finset V)} (hK : FaceClosed K) {G : Finset V}
    {k : ℕ} : ∀ (j : ℕ) (c : Finset V → Finset V → ℝ), c ∈ dblChains K G k → dtotMap V c = 0 →
      (∀ s t, c s t ≠ 0 → s.card ≤ j + 1) →
      ∃ w ∈ rowChains K G k, ∃ b ∈ dblChains K G (k + 1), c = w + dtotMap V b := by
  intro j
  induction j with
  | zero =>
    intro c hc hcyc hbound
    refine ⟨c, ⟨?_, ?_⟩, 0, (dblChains K G (k + 1)).zero_mem, by simp⟩
    · intro s t hst
      refine ⟨hc s t hst, ?_⟩
      have h1 : s.card ≤ 1 := hbound s t hst
      have h2 : s.card ≠ 0 := by
        intro h
        have hs : s = ∅ := Finset.card_eq_zero.mp h
        exact (hc s t hst).2.1 (hs ▸ Finset.empty_subset G)
      omega
    · have h := dhMap_levelPart_top (q := 1) hcyc hbound
      have heq : levelPart 1 c = c := by
        funext s t
        by_cases hcard : s.card = 1
        · simp only [levelPart, hcard, ↓reduceIte]
        · simp only [levelPart, hcard, ↓reduceIte]
          by_contra hne
          have h1 : s.card ≤ 1 := hbound s t (Ne.symm hne)
          have h2 : s.card ≠ 0 := by
            intro h0
            have hs : s = ∅ := Finset.card_eq_zero.mp h0
            exact (hc s t (Ne.symm hne)).2.1 (hs ▸ Finset.empty_subset G)
          omega
      rw [heq] at h
      exact h
  | succ j ih =>
    intro c hc hcyc hbound
    set c1 := levelPart (j + 2) c with hc1def
    have hc1mem : c1 ∈ dblChains K G k := levelPart_mem hc
    have hc1lev : ∀ s t, c1 s t ≠ 0 → s.card = j + 2 := levelPart_level c
    have hdhc1 : dhMap V c1 = 0 := dhMap_levelPart_top hcyc hbound
    set b := rowHomotopy G c1 with hbdef
    have hbmem : b ∈ dblChains K G (k + 1) :=
      rowHomotopy_mem_dblChains hK (p := j + 2) (by omega) hc1mem hc1lev
    have hblev : ∀ s t, b s t ≠ 0 → s.card = j + 1 :=
      rowHomotopy_level (p := j + 1) hc1lev
    have hdhb : dhMap V b = c1 := dhMap_rowHomotopy hc1mem hdhc1
    set c' := c - dtotMap V b with hc'def
    have hc'mem : c' ∈ dblChains K G k :=
      Submodule.sub_mem _ hc (dtotMap_mem_dblChains hK hbmem)
    have hc'cyc : dtotMap V c' = 0 := by
      rw [hc'def, map_sub, hcyc, dtotMap_dtotMap, sub_zero]
    have hc'bound : ∀ s t, c' s t ≠ 0 → s.card ≤ j + 1 := by
      intro s t hst
      by_contra hcard
      have hbs : b s = 0 := by
        funext t'
        by_contra hne
        exact absurd (hblev s t' hne) (by omega)
      have hdhbst : dhMap V b s t = c1 s t := by rw [hdhb]
      have hc1st : c1 s t = if s.card = j + 2 then c s t else 0 := rfl
      have hval : c' s t = c s t - dtotMap V b s t := rfl
      rw [dtotMap_apply] at hval
      have hcof : cofaceBoundary s (b s) t = 0 := by rw [hbs, map_zero]; rfl
      rw [hcof, mul_zero, zero_add, hdhbst, hc1st] at hval
      by_cases heq : s.card = j + 2
      · simp only [heq, ↓reduceIte, sub_self] at hval
        exact hst hval
      · simp only [heq, ↓reduceIte, sub_zero] at hval
        have hle := hbound s t (by rw [← hval]; exact hst)
        omega
    obtain ⟨w, hw, b', hb', heq⟩ := ih c' hc'mem hc'cyc hc'bound
    refine ⟨w, hw, b' + b, Submodule.add_mem _ hb' hbmem, ?_⟩
    have hcc : c = c' + dtotMap V b := by rw [hc'def]; abel
    rw [hcc, heq, map_add]
    abel

/-- **First staircase theorem.**  Every cycle of the total complex is
homologous to one concentrated in the first column. -/
theorem exists_rowChains_of_cycle {K : Finset (Finset V)} (hK : FaceClosed K) {G : Finset V}
    {k : ℕ} {c : Finset V → Finset V → ℝ} (hc : c ∈ dblChains K G k)
    (hcyc : dtotMap V c = 0) :
    ∃ w ∈ rowChains K G k, ∃ b ∈ dblChains K G (k + 1), c = w + dtotMap V b := by
  refine exists_rowChains_of_cycle_aux hK (Fintype.card V) c hc hcyc fun s t _ => ?_
  have : s.card ≤ Fintype.card V := Finset.card_le_univ s
  omega

/-- The inductive form of the second staircase theorem. -/
theorem dtotMap_topChains_of_mem_aux {K : Finset (Finset V)} (hK : FaceClosed K) {G : Finset V}
    {Q k : ℕ} (htop : ∀ t ∈ K, t.card ≤ Q)
    (hcol : ∀ s ∈ K, ∀ q, q ≠ Q → IsCofaceAcyclicAt K s q)
    {z : Finset V → Finset V → ℝ} (hz : z ∈ topChains K G Q k) :
    ∀ (n : ℕ) (b : Finset V → Finset V → ℝ), b ∈ dblChains K G (k + 1) → z = dtotMap V b →
      (∀ s t, b s t ≠ 0 → Q ≤ s.card + k + 1 + n) →
      ∃ y ∈ topChains K G Q (k + 1), z = dtotMap V y := by
  classical
  intro n
  induction n with
  | zero =>
    intro b hb hzb hlow
    have hexact : ∀ s, b s ≠ 0 → s.card + k + 1 = Q := by
      intro s hs
      obtain ⟨t, ht⟩ : ∃ t, b s t ≠ 0 := by
        by_contra hcon
        refine hs (funext fun t => ?_)
        by_contra hne
        exact hcon ⟨t, hne⟩
      obtain ⟨_, _, htK, _, hcard⟩ := hb s t ht
      have h1 := hlow s t ht
      have h2 := htop t htK
      omega
    refine ⟨b, ⟨fun s t hst => ⟨hb s t hst, ?_⟩, ?_⟩, hzb⟩
    · obtain ⟨_, _, htK, _, hcard⟩ := hb s t hst
      have h1 := hlow s t hst
      have h2 := htop t htK
      omega
    · refine LinearMap.mem_ker.mpr ?_
      funext s t
      by_cases hbs : b s = 0
      · change cofaceBoundary s (b s) t = 0
        rw [hbs, map_zero]
        rfl
      · have hcards := hexact s hbs
        have hdh : dhMap V b s t = 0 := by
          by_cases hst : s ⊆ t
          · rw [dhMap_apply_of_subset hst]
            refine Finset.sum_eq_zero fun v hv => ?_
            have hzero : b (s.erase v) t = 0 := by
              by_contra hne
              have h1 := hlow _ _ hne
              obtain ⟨_, _, htK, _, hcard'⟩ := hb _ _ hne
              have h2 := htop t htK
              have hpos : 1 ≤ s.card := Finset.card_pos.mpr ⟨v, hv⟩
              rw [Finset.card_erase_of_mem hv] at h1 hcard'
              omega
            rw [hzero, mul_zero]
          · exact dhMap_apply_of_not_subset hst
        have hzs : z s t = 0 := by
          by_contra hne
          obtain ⟨⟨_, _, _, _, hc⟩, hQ⟩ := hz.1 s t hne
          omega
        have h0 : dtotMap V b s t = 0 := by rw [← hzb]; exact hzs
        rw [dtotMap_apply, hdh, add_zero] at h0
        have hsign : ((-1 : ℝ) ^ s.card) ≠ 0 := by positivity
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd h hsign
        · exact h
  | succ n ih =>
    intro b hb hzb hlow
    by_cases hsmall : Q ≤ k + 1 + n
    · exact ih b hb hzb fun s t hst => by have := hlow s t hst; omega
    · -- peel off the lowest column `m`
      obtain ⟨m, hm⟩ : ∃ m, Q = m + k + 1 + n + 1 := ⟨Q - (k + 1 + n + 1), by omega⟩
      have hlowm : ∀ s t, b s t ≠ 0 → m ≤ s.card := by
        intro s t hst
        have := hlow s t hst
        omega
      -- the lowest layer is a vertical cycle
      have hdvlayer : ∀ s, s.card = m → cofaceBoundary s (b s) = 0 := by
        intro s hs
        funext t
        have hdh : dhMap V b s t = 0 := by
          by_cases hst : s ⊆ t
          · rw [dhMap_apply_of_subset hst]
            refine Finset.sum_eq_zero fun v hv => ?_
            have hzero : b (s.erase v) t = 0 := by
              by_contra hne
              have h1 := hlowm _ _ hne
              have hpos : 1 ≤ s.card := Finset.card_pos.mpr ⟨v, hv⟩
              rw [Finset.card_erase_of_mem hv] at h1
              omega
            rw [hzero, mul_zero]
          · exact dhMap_apply_of_not_subset hst
        have hzs : z s t = 0 := by
          by_contra hne
          obtain ⟨⟨_, _, _, _, hc⟩, hQ⟩ := hz.1 s t hne
          omega
        have h0 : dtotMap V b s t = 0 := by rw [← hzb]; exact hzs
        rw [dtotMap_apply, hdh, add_zero] at h0
        have hsign : ((-1 : ℝ) ^ s.card) ≠ 0 := by positivity
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd h hsign
        · exact h
      -- fill the lowest layer using exactness of the coface complexes
      have hy : ∀ s : Finset V, ∃ y : Finset V → ℝ,
          y ∈ cofaceChains K s (m + k + 2) ∧ cofaceBoundary s y = levelPart m b s ∧
            (¬ (s.card = m ∧ s ∈ K ∧ ¬ s ⊆ G) → y = 0) := by
        intro s
        by_cases hs : s.card = m ∧ s ∈ K ∧ ¬ s ⊆ G
        · have hxmem : levelPart m b s ∈ cofaceChains K s (m + k + 1) := by
            intro t ht
            have hbt : b s t ≠ 0 := by
              simpa only [levelPart, hs.1, ↓reduceIte] using ht
            obtain ⟨_, _, htK, hsub, hcard⟩ := hb s t hbt
            exact ⟨Finset.mem_filter.mpr ⟨htK, hsub⟩, by rw [hcard, hs.1]; ring⟩
          have hxbd : cofaceBoundary s (levelPart m b s) = 0 := by
            have hlp : levelPart m b s = b s := by
              funext t
              simp only [levelPart, hs.1, ↓reduceIte]
            rw [hlp]
            exact hdvlayer s hs.1
          obtain ⟨d, hd, hdb⟩ := hcol s hs.2.1 (m + k + 1) (by omega) _ hxmem hxbd
          exact ⟨d, hd, hdb, fun h => absurd hs h⟩
        · refine ⟨0, Submodule.zero_mem _, ?_, fun _ => rfl⟩
          rw [map_zero]
          funext t
          by_cases hcard : s.card = m
          · simp only [levelPart, hcard, ↓reduceIte, Pi.zero_apply]
            by_contra hne
            obtain ⟨hsK, hsG, _, _, _⟩ := hb s t (Ne.symm hne)
            exact hs ⟨hcard, hsK, hsG⟩
          · simp only [levelPart, hcard, ↓reduceIte, Pi.zero_apply]
      choose yf hy1 hy2 hy3 using hy
      obtain ⟨e, he_apply⟩ : ∃ e : Finset V → Finset V → ℝ, ∀ s, e s = ((-1 : ℝ) ^ m) • yf s :=
        ⟨_, fun _ => rfl⟩
      have hezero : ∀ s, ¬ (s.card = m ∧ s ∈ K ∧ ¬ s ⊆ G) → e s = 0 := by
        intro s hs
        rw [he_apply s, hy3 s hs, smul_zero]
      have hedv : ∀ s, cofaceBoundary s (e s) = ((-1 : ℝ) ^ m) • levelPart m b s := by
        intro s
        rw [he_apply s, map_smul, hy2 s]
      have hdhe : ∀ s t, s.card ≠ m + 1 → dhMap V e s t = 0 := by
        intro s t hs
        by_cases hst : s ⊆ t
        · rw [dhMap_apply_of_subset hst]
          refine Finset.sum_eq_zero fun v hv => ?_
          have hcard : (s.erase v).card ≠ m := by
            rw [Finset.card_erase_of_mem hv]
            have hpos : 1 ≤ s.card := Finset.card_pos.mpr ⟨v, hv⟩
            omega
          have h0 : e (s.erase v) t = 0 := by
            rw [hezero _ fun h => hcard h.1]
            rfl
          rw [h0, mul_zero]
        · exact dhMap_apply_of_not_subset hst
      have hemem : e ∈ dblChains K G (k + 2) := by
        intro s t hst
        by_cases hs : s.card = m ∧ s ∈ K ∧ ¬ s ⊆ G
        · have hchoose : yf s t ≠ 0 := by
            intro h
            refine hst ?_
            rw [he_apply s]
            simp only [Pi.smul_apply, h, smul_eq_mul, mul_zero]
          obtain ⟨htmem, htcard⟩ := hy1 s t hchoose
          obtain ⟨htK, hsub⟩ := Finset.mem_filter.mp htmem
          exact ⟨hs.2.1, hs.2.2, htK, hsub, by rw [htcard, hs.1]; ring⟩
        · refine absurd ?_ hst
          rw [hezero s hs]
          rfl
      have hsq : ((-1 : ℝ) ^ m) * ((-1 : ℝ) ^ m) = 1 := by
        rw [← mul_pow]
        norm_num
      have hb'low : ∀ s t, (b - dtotMap V e) s t ≠ 0 → m + 1 ≤ s.card := by
        intro s t hst
        by_contra hcon
        have hdh0 : dhMap V e s t = 0 := hdhe s t (by omega)
        have hval : (b - dtotMap V e) s t
            = b s t - (((-1 : ℝ) ^ s.card) * cofaceBoundary s (e s) t + dhMap V e s t) := rfl
        rw [hdh0, add_zero] at hval
        have hcof : cofaceBoundary s (e s) t = ((-1 : ℝ) ^ m) * levelPart m b s t := by
          rw [hedv s]
          rfl
        rw [hcof] at hval
        by_cases hcard : s.card = m
        · rw [hcard] at hval
          have hlp : levelPart m b s t = b s t := by
            simp only [levelPart, hcard, ↓reduceIte]
          rw [hlp, ← mul_assoc, hsq, one_mul, sub_self] at hval
          exact hst hval
        · have hlp : levelPart m b s t = 0 := by
            simp only [levelPart, hcard, ↓reduceIte]
          have hbz : b s t = 0 := by
            by_contra hne
            exact absurd (hlowm s t hne) (by omega)
          rw [hlp, mul_zero, mul_zero, sub_zero, hbz] at hval
          exact hst hval
      refine ih (b - dtotMap V e)
        (Submodule.sub_mem _ hb (dtotMap_mem_dblChains hK hemem)) ?_ ?_
      · rw [map_sub, dtotMap_dtotMap, sub_zero]
        exact hzb
      · intro s t hst
        have := hb'low s t hst
        omega

/-- **Second staircase theorem.**  A total boundary lying in the top row is the
horizontal boundary of an element of the top row. -/
theorem dtotMap_topChains_of_mem {K : Finset (Finset V)} (hK : FaceClosed K) {G : Finset V}
    {Q k : ℕ} (htop : ∀ t ∈ K, t.card ≤ Q)
    (hcol : ∀ s ∈ K, ∀ q, q ≠ Q → IsCofaceAcyclicAt K s q)
    {z : Finset V → Finset V → ℝ} (hz : z ∈ topChains K G Q k)
    {b : Finset V → Finset V → ℝ} (hb : b ∈ dblChains K G (k + 1)) (hzb : z = dtotMap V b) :
    ∃ y ∈ topChains K G Q (k + 1), z = dtotMap V y :=
  dtotMap_topChains_of_mem_aux hK htop hcol hz Q b hb hzb (fun s t _ => by omega)

end AffineTverberg.Simplicial
