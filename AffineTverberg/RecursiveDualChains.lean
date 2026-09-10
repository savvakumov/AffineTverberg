import AffineTverberg.AlexanderDuality
import AffineTverberg.ConeConnectingClasses

set_option linter.style.header false

/-!
# Explicit simplicial dual chains from a single global cycle

The dual chain at a face is constructed by coning the signed sum of the
dual chains at its immediate cofaces. The original simplicial identity
`boundary_boundary_apply` makes each such sum a cycle. Consequently its
literal boundary is exactly that signed sum. Summing against a cochain
gives a degree-reversing map intertwining simplicial coboundary and
simplicial boundary, without a singular-complement intermediate.

These are actual coefficient chains in the barycentric vertex universe.
Support in the dual blocks and the homology comparison are separate claims;
the chain identity here does not assume either of them.
-/

noncomputable section

open scoped BigOperators

namespace AffineTverberg.Simplicial

variable {V : Type} [Fintype V] [LinearOrder V] [inst : LinearOrder (Finset V)]

local instance recursiveDualChainsDecidableEq : DecidableEq (Finset V) := inst.toDecidableEq

/-- Signed incidence in the original complex, with flag-chain coefficients. -/
def dualIncidence (D : Finset V → Finset (Finset V) → ℝ)
    (s : Finset V) (C : Finset (Finset V)) : ℝ :=
  boundary ℝ V (fun t => D t C) s

omit inst in
theorem dualIncidence_eq_sum (D : Finset V → Finset (Finset V) → ℝ) (s : Finset V) :
    dualIncidence D s = ∑ v ∈ sᶜ, orientedSign ℝ s v • D (insert v s) := by
  funext C
  simp [dualIncidence, Pi.smul_apply, smul_eq_mul]

omit inst in
/-- Incidence squares to zero because it is the original oriented boundary,
evaluated at each flag coefficient. -/
theorem dualIncidence_dualIncidence (D : Finset V → Finset (Finset V) → ℝ) :
    dualIncidence (dualIncidence D) = 0 := by
  funext s C
  exact congrFun (boundary_boundary_apply (𝕜 := ℝ) (fun t => D t C)) s

theorem boundary_dualIncidence (D : Finset V → Finset (Finset V) → ℝ) (s : Finset V) :
    boundary ℝ (Finset V) (dualIncidence D s) =
      dualIncidence (fun t => boundary ℝ (Finset V) (D t)) s := by
  rw [dualIncidence_eq_sum, dualIncidence_eq_sum]
  simp only [map_sum, map_smul]

omit [LinearOrder V] in
private theorem boundary_vertex_chain (s : Finset V) :
    boundary ℝ (Finset V) (simplexChain ℝ {s}) = simplexChain ℝ ∅ := by
  funext C
  rw [boundary_simplexChain_apply]
  by_cases hC : C = ∅
  · subst C
    simp [boundaryCoeff, simplexChain]
  · have hfacet : ¬ IsSimplexFacet C {s} := by
      intro h
      have hcard := h.2
      simp only [Finset.card_singleton] at hcard
      exact hC (Finset.card_eq_zero.mp (by omega))
    rw [boundaryCoeff_eq_zero_of_not_isSimplexFacet hfacet]
    simp [simplexChain, hC]

/-- The oriented dual chain of depth q at s. At depth zero it is the
vertex s with its coefficient in the global cycle; each next depth cones
the signed coface sum to s. -/
def recursiveDualChain (c : Finset V → ℝ) : ℕ → Finset V → Finset (Finset V) → ℝ
  | 0, s => c s • simplexChain ℝ {s}
  | q + 1, s => coneHomotopy ℝ (Finset V) s (dualIncidence (recursiveDualChain c q) s)

theorem boundary_recursiveDualChain_zero (c : Finset V → ℝ) (s : Finset V) :
    boundary ℝ (Finset V) (recursiveDualChain c 0 s) = c s • simplexChain ℝ ∅ := by
  rw [recursiveDualChain, map_smul, boundary_vertex_chain]

private theorem boundary_dualIncidence_zero (c : Finset V → ℝ)
    (hc : boundary ℝ V c = 0) (s : Finset V) :
    boundary ℝ (Finset V) (dualIncidence (recursiveDualChain c 0) s) = 0 := by
  rw [boundary_dualIncidence]
  simp only [boundary_recursiveDualChain_zero]
  rw [dualIncidence_eq_sum]
  simp only [smul_smul, ← Finset.sum_smul]
  change boundary ℝ V c s • simplexChain ℝ ∅ = 0
  rw [hc, Pi.zero_apply, zero_smul]

/-- The actual simplicial incidence formula for the recursively constructed
dual chains. Every sign is fixed by the original orientation and the
existing cone operator. -/
theorem boundary_recursiveDualChain_succ (c : Finset V → ℝ)
    (hc : boundary ℝ V c = 0) (q : ℕ) (s : Finset V) :
    boundary ℝ (Finset V) (recursiveDualChain c (q + 1) s) =
      dualIncidence (recursiveDualChain c q) s := by
  induction q generalizing s with
  | zero =>
    exact boundary_coneHomotopy_of_cycle s (boundary_dualIncidence_zero c hc s)
  | succ q ih =>
    apply boundary_coneHomotopy_of_cycle
    rw [boundary_dualIncidence]
    simp only [ih]
    exact congrFun (dualIncidence_dualIncidence (recursiveDualChain c q)) s

theorem boundary_dualIncidence_recursiveDualChain (c : Finset V → ℝ)
    (hc : boundary ℝ V c = 0) (q : ℕ) (s : Finset V) :
    boundary ℝ (Finset V) (dualIncidence (recursiveDualChain c q) s) = 0 := by
  rw [← boundary_recursiveDualChain_succ c hc q s]
  exact boundary_boundary_apply _

/-- Cochain-to-chain dualization with the explicit dual chains. -/
def recursiveDualization (c : Finset V → ℝ) (q : ℕ) :
    (Finset V → ℝ) →ₗ[ℝ] (Finset (Finset V) → ℝ) where
  toFun f := ∑ s : Finset V, f s • recursiveDualChain c q s
  map_add' f g := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a f := by simp [mul_smul, Finset.smul_sum]

theorem recursiveDualization_apply (c f : Finset V → ℝ) (q : ℕ) :
    recursiveDualization c q f = ∑ s : Finset V, f s • recursiveDualChain c q s := rfl

/-- The degree-reversing simplicial chain identity. Its source is the
existing simplicial coboundary, not a differential defined to force the
identity. -/
theorem boundary_recursiveDualization (c : Finset V → ℝ)
    (hc : boundary ℝ V c = 0) (q : ℕ) (f : Finset V → ℝ) :
    boundary ℝ (Finset V) (recursiveDualization c (q + 1) f) =
      recursiveDualization c q (cochainDelta ℝ V f) := by
  rw [recursiveDualization_apply, recursiveDualization_apply]
  simp only [map_sum, map_smul, boundary_recursiveDualChain_succ c hc]
  funext C
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dualIncidence]
  exact sum_mul_boundary f (fun s => recursiveDualChain c q s C)

section Support

variable {K : Finset (Finset V)} {c : Finset V → ℝ} {n : ℕ}

/-- No dual chain is created at a nonface of the original complex. -/
theorem recursiveDualChain_eq_zero_of_not_mem (hK : FaceClosed K)
    (hc : c ∈ chains ℝ K n) (q : ℕ) {s : Finset V} (hs : s ∉ K) :
    recursiveDualChain c q s = 0 := by
  induction q generalizing s with
  | zero =>
    have hcs : c s = 0 := by
      by_contra h
      exact hs (hc s h).1
    simp [recursiveDualChain, hcs]
  | succ q ih =>
    have hsum : dualIncidence (recursiveDualChain c q) s = 0 := by
      rw [dualIncidence_eq_sum]
      apply Finset.sum_eq_zero
      intro v _
      rw [ih (fun h => hs (hK _ h _ (Finset.subset_insert _ _))), smul_zero]
    simp [recursiveDualChain, hsum]

/-- A dual chain can occur only in the dimension complementary to the
dimension of its original face. -/
theorem recursiveDualChain_eq_zero_of_card (hc : c ∈ chains ℝ K n)
    (q : ℕ) {s : Finset V} (hs : q + s.card ≠ n) :
    recursiveDualChain c q s = 0 := by
  induction q generalizing s with
  | zero =>
    have hcs : c s = 0 := by
      by_contra h
      exact hs (by simpa using (hc s h).2)
    simp [recursiveDualChain, hcs]
  | succ q ih =>
    have hsum : dualIncidence (recursiveDualChain c q) s = 0 := by
      rw [dualIncidence_eq_sum]
      apply Finset.sum_eq_zero
      intro v hv
      have hv' : v ∉ s := Finset.mem_compl.mp hv
      have hcard : q + (insert v s).card ≠ n := by
        rw [Finset.card_insert_of_notMem hv']
        omega
      rw [ih hcard, smul_zero]
    simp [recursiveDualChain, hsum]

/-- Every nonzero flag coefficient of the dual chain contains its apex. -/
theorem mem_of_recursiveDualChain_ne_zero (c : Finset V → ℝ) (q : ℕ)
    (s : Finset V) {C : Finset (Finset V)} (hC : recursiveDualChain c q s C ≠ 0) :
    s ∈ C := by
  cases q with
  | zero =>
    by_contra hs
    have hne : C ≠ {s} := by rintro rfl; exact hs (Finset.mem_singleton_self s)
    simp [recursiveDualChain, simplexChain, hne] at hC
  | succ q =>
    by_contra hs
    simp [recursiveDualChain, hs] at hC

/-- The recursive formula produces genuine simplicial chains of the
corresponding dual block, in the claimed flag degree. -/
theorem recursiveDualChain_mem_chains (hK : FaceClosed K)
    (hc : c ∈ chains ℝ K n) (q : ℕ) {s : Finset V} (hs : s.Nonempty) :
    recursiveDualChain c q s ∈ chains ℝ (dualBlockFaces K s) (q + 1) := by
  induction q generalizing s with
  | zero =>
    by_cases hsK : s ∈ K
    · apply (chains ℝ (dualBlockFaces K s) 1).smul_mem
      exact indicatorChain_mem_chains (singleton_mem_dualBlockFaces hsK hs) (by simp)
    · rw [recursiveDualChain_eq_zero_of_not_mem hK hc 0 hsK]
      exact Submodule.zero_mem _
  | succ q ih =>
    by_cases hsK : s ∈ K
    · have hcone : IsConeWithApex (dualBlockFaces K s) s := by
        intro C hC
        convert insert_mem_dualBlockFaces hsK hs hC using 1
        ext t
        simp
      apply coneHomotopy_mem_chains hcone
      rw [dualIncidence_eq_sum]
      apply Submodule.sum_mem
      intro v _
      apply Submodule.smul_mem
      exact chains_mono (dualBlockFaces_mono (Finset.subset_insert v s)) _
        (ih (Finset.insert_nonempty v s))
    · rw [recursiveDualChain_eq_zero_of_not_mem hK hc (q + 1) hsK]
      exact Submodule.zero_mem _

/-- The signed coface sum lies in the actual boundary of the dual block. -/
theorem dualIncidence_recursiveDualChain_mem_boundary (hK : FaceClosed K)
    (hc : c ∈ chains ℝ K n) (q : ℕ) (s : Finset V) :
    dualIncidence (recursiveDualChain c q) s ∈
      chains ℝ (dualBlockBoundaryFaces K s) (q + 1) := by
  rw [dualIncidence_eq_sum]
  apply Submodule.sum_mem
  intro v hv
  apply Submodule.smul_mem
  have hv' : v ∉ s := Finset.mem_compl.mp hv
  have hsub : dualBlockFaces K (insert v s) ⊆ dualBlockBoundaryFaces K s := by
    intro C hC
    obtain ⟨hCsd, hC⟩ := mem_dualBlockFaces.mp hC
    refine mem_dualBlockBoundaryFaces.mpr ⟨hCsd, fun t ht => ?_⟩
    exact (Finset.ssubset_insert hv').trans_le (hC t ht)
  exact chains_mono hsub _ (recursiveDualChain_mem_chains hK hc q (Finset.insert_nonempty v s))

/-- In particular these are relative cycles for the genuine dual-block
pair, expressed using only the simplicial boundary operator. -/
theorem boundary_recursiveDualChain_mem_boundary (hK : FaceClosed K)
    (hc : c ∈ cycles ℝ K n) (q : ℕ) (s : Finset V) :
    boundary ℝ (Finset V) (recursiveDualChain c (q + 1) s) ∈
      chains ℝ (dualBlockBoundaryFaces K s) (q + 1) := by
  rw [boundary_recursiveDualChain_succ c hc.2]
  exact dualIncidence_recursiveDualChain_mem_boundary hK hc.1 q s

/-- A nonzero global facet coefficient remains nonzero on the dual chain
at every nonempty subface, in the complementary dimension. This prevents
the chain comparison from degenerating to the zero map. -/
theorem recursiveDualChain_ne_zero_of_face (hK : FaceClosed K)
    (hc : c ∈ chains ℝ K n) (q : ℕ) {s F : Finset V} (hs : s.Nonempty)
    (hsF : s ⊆ F) (hF : c F ≠ 0) (hq : q + s.card = F.card) :
    recursiveDualChain c q s ≠ 0 := by
  induction q generalizing s with
  | zero =>
    have hs_eq : s = F := Finset.eq_of_subset_of_card_le hsF (by omega)
    subst F
    intro hz
    have h := congrFun hz {s}
    exact hF (by simpa [recursiveDualChain, simplexChain] using h)
  | succ q ih =>
    have hnot : ¬ F ⊆ s := by
      intro h
      have := Finset.card_le_card h
      omega
    obtain ⟨v, hvF, hvs⟩ := Finset.not_subset.mp hnot
    have hq' : q + (insert v s).card = F.card := by
      rw [Finset.card_insert_of_notMem hvs]
      omega
    have hne := ih (Finset.insert_nonempty v s) (Finset.insert_subset hvF hsF) hq'
    obtain ⟨C, hC⟩ := not_forall.mp
      (show ¬ ∀ C, recursiveDualChain c q (insert v s) C = 0 from fun h => hne (funext h))
    have hblock := (recursiveDualChain_mem_chains hK hc q
      (Finset.insert_nonempty v s) C hC).1
    have habove := (mem_dualBlockFaces.mp hblock).2
    have hsC : s ∉ C := by
      intro h
      exact hvs (habove s h (Finset.mem_insert_self v s))
    have hsum : dualIncidence (recursiveDualChain c q) s C =
        orientedSign ℝ s v * recursiveDualChain c q (insert v s) C := by
      change (∑ w ∈ sᶜ, orientedSign ℝ s w * recursiveDualChain c q (insert w s) C) = _
      apply Finset.sum_eq_single v
      · intro w _ hwv
        have hwzero : recursiveDualChain c q (insert w s) C = 0 := by
          by_contra h
          have hwC := mem_of_recursiveDualChain_ne_zero c q (insert w s) h
          have hvw : v ∈ insert w s := habove (insert w s) hwC (Finset.mem_insert_self v s)
          exact hwv ((Finset.mem_insert.mp hvw).resolve_right hvs).symm
        rw [hwzero, mul_zero]
      · intro hv
        exact (hv (Finset.mem_compl.mpr hvs)).elim
    have hcoeff : recursiveDualChain c (q + 1) s (insert s C) ≠ 0 := by
      rw [recursiveDualChain, coneHomotopy_apply,
        ite_eq_left (Finset.mem_insert_self s C), Finset.erase_insert hsC, hsum]
      exact mul_ne_zero (orientedSign_ne_zero C s)
        (mul_ne_zero (orientedSign_ne_zero s v) hC)
    intro hz
    exact hcoeff (congrFun hz (insert s C))

end Support

section RelativeClasses

open AffineTverberg.AffChain

variable {K : Finset (Finset V)} {c : Finset V → ℝ} {n : ℕ} {s : Finset V}

theorem recursiveDualChain_mem_cofaceChains (hK : FaceClosed K)
    (hc : c ∈ chains ℝ K n) (q : ℕ) (hs : s.Nonempty) :
    recursiveDualChain c q s ∈ cofaceChains (dualBlockFaces K s) {s} (q + 1) := by
  intro C hC
  obtain ⟨hmem, hcard⟩ := recursiveDualChain_mem_chains hK hc q hs C hC
  exact ⟨Finset.mem_filter.mpr ⟨hmem, Finset.singleton_subset_iff.mpr
    (mem_of_recursiveDualChain_ne_zero c q s hC)⟩, hcard⟩

theorem cofaceBoundary_recursiveDualChain (hK : FaceClosed K)
    (hc : c ∈ cycles ℝ K n) (q : ℕ) (s : Finset V) :
    cofaceBoundary {s} (recursiveDualChain c q s) = 0 := by
  change cofaceRestriction {s} (boundary ℝ (Finset V) (recursiveDualChain c q s)) = 0
  cases q with
  | zero =>
    rw [boundary_recursiveDualChain_zero]
    funext C
    by_cases hC : C = ∅
    · subst C
      simp [cofaceRestriction_apply]
    · simp [cofaceRestriction_apply, simplexChain, hC]
  | succ q =>
    have hb := boundary_recursiveDualChain_mem_boundary hK hc q s
    apply (cofaceRestriction_eq_zero_iff_costar
      (chains_mono (dualBlockBoundaryFaces_subset K s) _ hb)).mpr
    simpa only [costar_dualBlock_apex] using hb

theorem recursiveDualChain_isCycleAt (hK : FaceClosed K)
    (hc : c ∈ cycles ℝ K n) (q : ℕ) (hs : s.Nonempty) :
    IsCycleAt (cofaceComplex (faceClosed_dualBlockFaces K s) {s}) q
      (⟨recursiveDualChain c q s, recursiveDualChain_mem_cofaceChains hK hc.1 q hs⟩ :
        ↥(cofaceChains (dualBlockFaces K s) {s} (q + 1))) := by
  cases q with
  | zero => exact isCycleAt_zero _
  | succ q =>
    exact cofaceChain_isCycleAt (faceClosed_dualBlockFaces K s)
      (recursiveDualChain_mem_cofaceChains hK hc.1 (q + 1) hs)
      (cofaceBoundary_recursiveDualChain hK hc (q + 1) s)

/-- The literal recursively constructed cycle in the actual simplicial
relative homology of a dual block modulo its boundary, in all degrees. -/
def recursiveDualRelativeClass (hK : FaceClosed K)
    (hc : c ∈ cycles ℝ K n) (q : ℕ) (hs : s.Nonempty) :
    (cofaceComplex (faceClosed_dualBlockFaces K s) {s}).homology q :=
  homClass
    (⟨recursiveDualChain c q s, recursiveDualChain_mem_cofaceChains hK hc.1 q hs⟩ :
      ↥(cofaceChains (dualBlockFaces K s) {s} (q + 1)))
    (recursiveDualChain_isCycleAt hK hc q hs)

/-- In top complementary degree the explicit local relative class is
nonzero: a nonzero coefficient survives, and dimension excludes incoming
boundaries. This includes the degree-zero dual blocks. -/
theorem recursiveDualRelativeClass_ne_zero (hK : FaceClosed K)
    (hc : c ∈ cycles ℝ K n) (htop : ∀ t ∈ K, t.card ≤ n)
    (q : ℕ) (hs : s.Nonempty) {F : Finset V} (hsF : s ⊆ F) (hF : c F ≠ 0)
    (hq : q + s.card = n) :
    recursiveDualRelativeClass hK hc q hs ≠ 0 := by
  intro hz
  obtain ⟨w, hw⟩ := (homClass_eq_zero_iff _ _).mp hz
  have hwzero : w = 0 := by
    apply Subtype.ext
    funext C
    change w.val C = 0
    by_contra hC
    obtain ⟨hmem, hcard⟩ := w.property C hC
    have hblock := (Finset.mem_filter.mp hmem).1
    have hne : C.Nonempty := Finset.card_pos.mp (by omega)
    have hbound := card_add_card_le_of_mem_dualBlockFaces htop hblock hne
    omega
  rw [hwzero, map_zero] at hw
  have hchain : recursiveDualChain c q s = 0 :=
    (congrArg (fun x : (cofaceComplex (faceClosed_dualBlockFaces K s) {s}).X q => x.val) hw).symm
  exact recursiveDualChain_ne_zero_of_face hK hc.1 q hs hsF hF
    (hq.trans (hc.1 F hF).2.symm) hchain

end RelativeClasses

end AffineTverberg.Simplicial
