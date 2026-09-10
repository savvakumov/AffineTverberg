import AffineTverberg.ConicalIncidence
import Mathlib.Analysis.Normed.Module.HahnBanach

set_option linter.style.header false

/-!
# Arbitrarily fine conical neighborhoods

The separation construction of `ConicalIncidence` produces, around a unit
center `a`, one open convex cone on which every active piece contains `a`.
For a local-to-global descent this is not enough: the neighborhoods have to
form a basis of the topology of the unit sphere.

This file supplies the missing refinement. For a continuous linear functional
`l` with `l a = 1` and `δ > 0` the set

  `{x | 0 < l x ∧ ‖x - l x • a‖ < δ * l x}`

is open, convex, invariant under positive scaling and avoids the origin,
and its unit-sphere cap is contained in the ball of radius `2 δ` around `a`.
Intersecting it with an active neighborhood keeps all the properties used by
the contraction arguments, so every center has arbitrarily small conical
neighborhoods with all the previous local conclusions.
-/

noncomputable section

open Set

namespace AffineTverberg

namespace ConicalIncidence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} {C : ι → Set E} {a : UnitSphere E}

namespace Neighborhood

/-- The intersection of two neighborhoods of the same center. -/
def inter (H H' : Neighborhood C a) : Neighborhood C a where
  carrier := H.carrier ∩ H'.carrier
  isOpen := H.isOpen.inter H'.isOpen
  center_mem := ⟨H.center_mem, H'.center_mem⟩
  convex := H.convex.inter H'.convex
  smul_mem t ht x hx := ⟨H.smul_mem t ht x hx.1, H'.smul_mem t ht x hx.2⟩
  zero_notMem h := H.zero_notMem h.1
  active x hx i hxi := H.active x hx.1 i hxi

theorem inter_carrier (H H' : Neighborhood C a) :
    (H.inter H').carrier = H.carrier ∩ H'.carrier := rfl

end Neighborhood

omit [NormedSpace ℝ E] in
theorem norm_ne_zero_unitSphere (a : UnitSphere E) : ‖a.val‖ ≠ 0 := by
  rw [a.property]
  norm_num

/-- The normalized cone of aperture `δ` around the unit center `a`, cut out by
a functional `l` with `l a = 1`. -/
def fineCone (l : E →L[ℝ] ℝ) (a : UnitSphere E) (δ : ℝ) : Set E :=
  {x | 0 < l x ∧ ‖x - l x • a.val‖ < δ * l x}

theorem isOpen_fineCone (l : E →L[ℝ] ℝ) (a : UnitSphere E) (δ : ℝ) :
    IsOpen (fineCone l a δ) := by
  have h1 : IsOpen {x : E | 0 < l x} := isOpen_lt continuous_const l.continuous
  have h2 : IsOpen {x : E | ‖x - l x • a.val‖ < δ * l x} := by
    apply isOpen_lt
    · fun_prop
    · fun_prop
  exact h1.inter h2

theorem center_mem_fineCone {l : E →L[ℝ] ℝ} {a : UnitSphere E} (hl : l a.val = 1)
    {δ : ℝ} (hδ : 0 < δ) : a.val ∈ fineCone l a δ := by
  refine ⟨by rw [hl]; norm_num, ?_⟩
  rw [hl, one_smul, sub_self, norm_zero, mul_one]
  exact hδ

theorem convex_fineCone (l : E →L[ℝ] ℝ) (a : UnitSphere E) (δ : ℝ) :
    Convex ℝ (fineCone l a δ) := by
  rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ u v hu hv huv
  have hlpos : 0 < l (u • x + v • y) := by
    simp only [map_add, map_smul, smul_eq_mul]
    rcases lt_or_eq_of_le hu with hu' | rfl
    · exact add_pos_of_pos_of_nonneg (mul_pos hu' hx1) (mul_nonneg hv hy1.le)
    · simp only [zero_add] at huv
      simpa [huv] using hy1
  refine ⟨hlpos, ?_⟩
  have hrw : (u • x + v • y) - l (u • x + v • y) • a.val =
      u • (x - l x • a.val) + v • (y - l y • a.val) := by
    simp only [map_add, map_smul, smul_eq_mul, smul_sub, add_smul, mul_smul]
    abel
  rw [hrw]
  have hbound : ‖u • (x - l x • a.val) + v • (y - l y • a.val)‖ ≤
      u * ‖x - l x • a.val‖ + v * ‖y - l y • a.val‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hu, abs_of_nonneg hv]
  refine lt_of_le_of_lt hbound ?_
  have hgoal : u * ‖x - l x • a.val‖ + v * ‖y - l y • a.val‖ <
      u * (δ * l x) + v * (δ * l y) := by
    rcases lt_or_eq_of_le hu with hu' | rfl
    · rcases lt_or_eq_of_le hv with hv' | rfl
      · exact add_lt_add (mul_lt_mul_of_pos_left hx2 hu') (mul_lt_mul_of_pos_left hy2 hv')
      · simp only [zero_mul, add_zero]
        exact mul_lt_mul_of_pos_left hx2 hu'
    · rcases lt_or_eq_of_le hv with hv' | rfl
      · simp only [zero_mul, zero_add]
        exact mul_lt_mul_of_pos_left hy2 hv'
      · exact absurd huv (by norm_num)
  refine hgoal.trans_le (le_of_eq ?_)
  simp only [map_add, map_smul, smul_eq_mul]
  ring

theorem smul_mem_fineCone (l : E →L[ℝ] ℝ) (a : UnitSphere E) (δ : ℝ)
    (t : ℝ) (ht : 0 < t) (x : E) (hx : x ∈ fineCone l a δ) :
    t • x ∈ fineCone l a δ := by
  obtain ⟨hx1, hx2⟩ := hx
  refine ⟨by simpa only [map_smul, smul_eq_mul] using mul_pos ht hx1, ?_⟩
  have hrw : t • x - l (t • x) • a.val = t • (x - l x • a.val) := by
    simp only [map_smul, smul_eq_mul, smul_sub, mul_smul]
  rw [hrw, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  simp only [map_smul, smul_eq_mul]
  calc t * ‖x - l x • a.val‖ < t * (δ * l x) := mul_lt_mul_of_pos_left hx2 ht
    _ = δ * (t * l x) := by ring

theorem zero_notMem_fineCone (l : E →L[ℝ] ℝ) (a : UnitSphere E) (δ : ℝ) :
    (0 : E) ∉ fineCone l a δ := by
  rintro ⟨h, -⟩
  simp at h

/-- Unit vectors in the fine cone are close to its center. -/
theorem norm_sub_lt_of_mem_fineCone {l : E →L[ℝ] ℝ} {a : UnitSphere E}
    (hnorm : ‖l‖ = 1) {δ : ℝ} (hδ : 0 < δ)
    {x : E} (hx : x ∈ fineCone l a δ) (hx1 : ‖x‖ = 1) :
    ‖x - a.val‖ < 2 * δ := by
  obtain ⟨hpos, hclose⟩ := hx
  have hna : ‖a.val‖ = 1 := a.property
  have hsm : ‖l x • a.val‖ = l x := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos, hna, mul_one]
  have hrev : |l x - 1| ≤ ‖x - l x • a.val‖ := by
    have h := abs_norm_sub_norm_le (l x • a.val) x
    rw [hsm, hx1] at h
    rw [abs_sub_comm] at h ⊢
    calc |1 - l x| = |(1 : ℝ) - l x| := rfl
      _ ≤ ‖l x • a.val - x‖ := h
      _ = ‖x - l x • a.val‖ := by rw [norm_sub_rev]
  have hsplit : ‖x - a.val‖ ≤ ‖x - l x • a.val‖ + |l x - 1| := by
    have h1 : x - a.val = (x - l x • a.val) + ((l x - 1) • a.val) := by
      rw [sub_smul, one_smul]
      abel
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, hna, mul_one]
  have hle1 : l x ≤ 1 := by
    have := l.le_opNorm x
    rw [hnorm, hx1, one_mul] at this
    exact (le_abs_self _).trans this
  calc ‖x - a.val‖ ≤ ‖x - l x • a.val‖ + |l x - 1| := hsplit
    _ ≤ ‖x - l x • a.val‖ + ‖x - l x • a.val‖ := by linarith
    _ < (δ * l x) + (δ * l x) := by linarith
    _ ≤ 2 * δ := by nlinarith

/-- **Fine neighborhoods exist.** Every unit center has active conical
neighborhoods of arbitrarily small diameter. -/
theorem exists_fine_neighborhood [Finite ι] (C : ι → Set E)
    (hcl : ∀ i, IsClosed (C i)) (hcv : ∀ i, Convex ℝ (C i))
    (h0 : ∀ i, (0 : E) ∈ C i)
    (hsmul : ∀ i (t : ℝ), 0 ≤ t → ∀ x ∈ C i, t • x ∈ C i)
    (a : UnitSphere E) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Neighborhood C a, ∀ x ∈ H.cap, ‖x.val - a.val‖ < ε := by
  obtain ⟨H0⟩ := exists_neighborhood C hcl hcv h0 hsmul a
  obtain ⟨l, hlnorm, hla⟩ := exists_dual_vector ℝ a.val (norm_ne_zero_unitSphere a)
  rw [a.property] at hla
  have hla' : l a.val = 1 := by exact_mod_cast hla
  set δ : ℝ := ε / 4 with hδdef
  have hδ : 0 < δ := by positivity
  let H : Neighborhood C a :=
    { carrier := H0.carrier ∩ fineCone l a δ
      isOpen := H0.isOpen.inter (isOpen_fineCone l a δ)
      center_mem := ⟨H0.center_mem, center_mem_fineCone hla' hδ⟩
      convex := H0.convex.inter (convex_fineCone l a δ)
      smul_mem := fun t ht x hx =>
        ⟨H0.smul_mem t ht x hx.1, smul_mem_fineCone l a δ t ht x hx.2⟩
      zero_notMem := fun h => H0.zero_notMem h.1
      active := fun x hx i hxi => H0.active x hx.1 i hxi }
  refine ⟨H, fun x hx => ?_⟩
  have hmem : x.val ∈ fineCone l a δ := (hx : x.val ∈ H.carrier).2
  have := norm_sub_lt_of_mem_fineCone hlnorm hδ hmem x.property
  calc ‖x.val - a.val‖ < 2 * δ := this
    _ < ε := by rw [hδdef]; linarith

section FineLocalHomology

open CategoryTheory HomologicalComplex AffChain

variable {X E ι : Type} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite ι]

/-- Every sphere parameter has arbitrarily small open neighborhoods whose
full incidence preimage retracts to the actual center fiber. -/
theorem exists_fine_open_fiberHomotopyEquiv
    (A : ι → Set X) (C : ι → Set E)
    (hcl : ∀ i, IsClosed (C i)) (hcv : ∀ i, Convex ℝ (C i))
    (h0 : ∀ i, (0 : E) ∈ C i)
    (hsmul : ∀ i (t : ℝ), 0 ≤ t → ∀ x ∈ C i, t • x ∈ C i)
    (a : UnitSphere E) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set (UnitSphere E), IsOpen U ∧ a ∈ U ∧
      (∀ x ∈ U, ‖x.val - a.val‖ < ε) ∧ ContractibleSpace U ∧
      Nonempty (ContinuousMap.HomotopyEquiv ↥((projection A C) ⁻¹' U)
        ↥((projection A C) ⁻¹' {a})) := by
  obtain ⟨H, hsmall⟩ := exists_fine_neighborhood C hcl hcv h0 hsmul a hε
  exact ⟨H.cap, H.isOpen_cap, H.center_mem_cap, hsmall, H.contractibleSpace_cap,
    ⟨localFiberHomotopyEquiv A C H hcv hsmul⟩⟩

/-- Fiber acyclicity yields the sharp homology range on arbitrarily small
actual open neighborhoods. -/
theorem exists_fine_open_homologyRange
    (A : ι → Set X) (C : ι → Set E)
    (hcl : ∀ i, IsClosed (C i)) (hcv : ∀ i, Convex ℝ (C i))
    (h0 : ∀ i, (0 : E) ∈ C i)
    (hsmul : ∀ i (t : ℝ), 0 ≤ t → ∀ x ∈ C i, t • x ∈ C i)
    {q : ℕ} (a : UnitSphere E) {ε : ℝ} (hε : 0 < ε)
    (hfib : SingularAcyclicBelow (TopCat.of ↥((projection A C) ⁻¹' {a})) q) :
    ∃ U : Set (UnitSphere E), IsOpen U ∧ a ∈ U ∧ (∀ x ∈ U, ‖x.val - a.val‖ < ε) ∧
      HomologyRange (singChainsMap (preimageRestriction
        (TopCat.ofHom (projection A C)) U)) q := by
  obtain ⟨U, ho, ha, hsmall, hU, ⟨e⟩⟩ :=
    exists_fine_open_fiberHomotopyEquiv A C hcl hcv h0 hsmul a hε
  exact ⟨U, ho, ha, hsmall, homologyRange_of_acyclic_contractible _ (hfib.of_homotopyEquiv e)⟩

end FineLocalHomology

end ConicalIncidence

end AffineTverberg
