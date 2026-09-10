import AffineTverberg.CofaceRelativeChains
import AffineTverberg.LinkPseudomanifold

set_option linter.style.header false

/-!
# The coface chain complex is the shifted augmented chain complex of the link

The faces of `K` containing a fixed face `L` correspond bijectively to the
faces of the ordinary combinatorial link `link K L`, by `F ↦ F \ L`.  Carrying
the oriented coefficients across this bijection requires the shuffle sign
`linkSign L t = ∏ v ∈ t, orientedSign L v`, and with that sign the *actual*
coface differential `cofaceBoundary L` becomes the *actual* augmented oriented
boundary of the link, with a shift of `#L` in the cardinality degree.

Nothing here is a new homology definition: `linkShift` is an explicit linear
isomorphism between the concrete chain groups already used by
`CofaceRelativeChains`, and the boundary maps are the ones already defined in
`SimplicialHomology`.
-/

noncomputable section

open scoped BigOperators

namespace AffineTverberg.Simplicial

variable {V : Type} [LinearOrder V] {K : Finset (Finset V)}

/-! ### The shuffle sign -/

/-- The sign incurred by moving the face `L` past the face `t`. -/
def linkSign (L t : Finset V) : ℝ := ∏ v ∈ t, orientedSign ℝ L v

theorem linkSign_ne_zero (L t : Finset V) : linkSign L t ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => orientedSign_ne_zero _ _

theorem linkSign_mul_self (L t : Finset V) : linkSign L t * linkSign L t = 1 := by
  unfold linkSign
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun v _ => orientedSign_sq L v

theorem linkSign_insert {L t : Finset V} {v : V} (hv : v ∉ t) :
    linkSign L (insert v t) = orientedSign ℝ L v * linkSign L t :=
  Finset.prod_insert hv

/-- Incidence signs are multiplicative along a disjoint union. -/
theorem orientedSign_union {t L : Finset V} (h : Disjoint t L) (v : V) :
    orientedSign ℝ (t ∪ L) v = orientedSign ℝ t v * orientedSign ℝ L v := by
  unfold orientedSign
  rw [Finset.filter_union,
    Finset.card_union_of_disjoint
      (h.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)), pow_add]

/-! ### The shift isomorphism on coefficient functions -/

/-- Transport a chain supported on cofaces of `L` to a chain on the link. -/
def linkShift (L : Finset V) : (Finset V → ℝ) →ₗ[ℝ] (Finset V → ℝ) where
  toFun c t := if Disjoint t L then linkSign L t * c (t ∪ L) else 0
  map_add' c d := by
    funext t
    by_cases h : Disjoint t L <;> simp [h, mul_add]
  map_smul' a c := by
    funext t
    by_cases h : Disjoint t L <;> simp [h, mul_left_comm]

@[simp]
theorem linkShift_apply (L : Finset V) (c : Finset V → ℝ) (t : Finset V) :
    linkShift L c t = if Disjoint t L then linkSign L t * c (t ∪ L) else 0 := rfl

/-- Transport a chain on the link back to a chain supported on cofaces of `L`. -/
def cofaceUnshift (L : Finset V) : (Finset V → ℝ) →ₗ[ℝ] (Finset V → ℝ) where
  toFun b F := if L ⊆ F then linkSign L (F \ L) * b (F \ L) else 0
  map_add' b d := by
    funext F
    by_cases h : L ⊆ F <;> simp [h, mul_add]
  map_smul' a b := by
    funext F
    by_cases h : L ⊆ F <;> simp [h, mul_left_comm]

@[simp]
theorem cofaceUnshift_apply (L : Finset V) (b : Finset V → ℝ) (F : Finset V) :
    cofaceUnshift L b F = if L ⊆ F then linkSign L (F \ L) * b (F \ L) else 0 := rfl

theorem linkShift_cofaceUnshift {L : Finset V} {b : Finset V → ℝ}
    (hb : ∀ t, b t ≠ 0 → Disjoint t L) : linkShift L (cofaceUnshift L b) = b := by
  funext t
  by_cases ht : Disjoint t L
  · have hsub : L ⊆ t ∪ L := Finset.subset_union_right
    have hsdiff : (t ∪ L) \ L = t := by
      rw [Finset.union_sdiff_right, Finset.sdiff_eq_self_of_disjoint ht]
    simp only [linkShift_apply, ht, ite_true, cofaceUnshift_apply, hsub, hsdiff]
    rw [← mul_assoc, linkSign_mul_self, one_mul]
  · have hbt : b t = 0 := by
      by_contra h
      exact ht (hb t h)
    simp [ht, hbt]

theorem cofaceUnshift_linkShift {L : Finset V} {c : Finset V → ℝ}
    (hc : ∀ F, c F ≠ 0 → L ⊆ F) : cofaceUnshift L (linkShift L c) = c := by
  funext F
  by_cases hF : L ⊆ F
  · have hdis : Disjoint (F \ L) L := Finset.sdiff_disjoint
    have hunion : F \ L ∪ L = F := Finset.sdiff_union_of_subset hF
    simp only [cofaceUnshift_apply, hF, ite_true, linkShift_apply, hdis, ite_true, hunion]
    rw [← mul_assoc, linkSign_mul_self, one_mul]
  · have hcF : c F = 0 := by
      by_contra h
      exact hF (hc F h)
    simp [hF, hcF]

theorem linkShift_injOn {L : Finset V} {c d : Finset V → ℝ}
    (hc : ∀ F, c F ≠ 0 → L ⊆ F) (hd : ∀ F, d F ≠ 0 → L ⊆ F)
    (h : linkShift L c = linkShift L d) : c = d := by
  rw [← cofaceUnshift_linkShift hc, ← cofaceUnshift_linkShift hd, h]

theorem linkShift_eq_zero_iff {L : Finset V} {c : Finset V → ℝ}
    (hc : ∀ F, c F ≠ 0 → L ⊆ F) : linkShift L c = 0 ↔ c = 0 := by
  constructor
  · intro h
    refine linkShift_injOn hc (fun F hF => absurd rfl hF) ?_
    rw [h, map_zero]
  · rintro rfl
    exact map_zero _

theorem linkShift_cofaceRestriction (L : Finset V) (c : Finset V → ℝ) :
    linkShift L (cofaceRestriction L c) = linkShift L c := by
  funext t
  by_cases ht : Disjoint t L
  · simp only [linkShift_apply, ht, ite_true, cofaceRestriction_apply,
      Finset.subset_union_right, ite_true]
  · simp [ht]

/-! ### Compatibility with the chain groups -/

theorem mem_cofaceChains_subset {L : Finset V} {n : ℕ} {c : Finset V → ℝ}
    (hc : c ∈ cofaceChains K L n) : ∀ F, c F ≠ 0 → L ⊆ F :=
  fun F hF => (Finset.mem_filter.mp (hc F hF).1).2

theorem linkShift_mem_chains {L : Finset V} {n : ℕ} {c : Finset V → ℝ}
    (hc : c ∈ cofaceChains K L (n + L.card)) : linkShift L c ∈ chains ℝ (link K L) n := by
  intro t ht
  by_cases hdis : Disjoint t L
  · have hne : c (t ∪ L) ≠ 0 := by
      intro h
      apply ht
      simp [hdis, h]
    obtain ⟨hmem, hcard⟩ := hc _ hne
    have hcard' : (t ∪ L).card = t.card + L.card := Finset.card_union_of_disjoint hdis
    refine ⟨mem_link_iff.mpr ⟨(Finset.mem_filter.mp hmem).1, hdis⟩, ?_⟩
    omega
  · simp [hdis] at ht

theorem cofaceUnshift_mem_cofaceChains {L : Finset V} {n : ℕ} {b : Finset V → ℝ}
    (hb : b ∈ chains ℝ (link K L) n) :
    cofaceUnshift L b ∈ cofaceChains K L (n + L.card) := by
  intro F hF
  by_cases hLF : L ⊆ F
  · have hne : b (F \ L) ≠ 0 := by
      intro h
      apply hF
      simp [hLF, h]
    obtain ⟨hmem, hcard⟩ := hb _ hne
    obtain ⟨hunion, -⟩ := mem_link_iff.mp hmem
    have hFeq : F \ L ∪ L = F := Finset.sdiff_union_of_subset hLF
    have h1 : (F \ L).card = F.card - L.card := Finset.card_sdiff_of_subset hLF
    have h2 : L.card ≤ F.card := Finset.card_le_card hLF
    exact ⟨Finset.mem_filter.mpr ⟨hFeq ▸ hunion, hLF⟩, by omega⟩
  · simp [hLF] at hF

theorem chains_link_disjoint {L : Finset V} {n : ℕ} {b : Finset V → ℝ}
    (hb : b ∈ chains ℝ (link K L) n) : ∀ t, b t ≠ 0 → Disjoint t L :=
  fun t ht => (mem_link_iff.mp (hb t ht).1).2

/-- The explicit linear isomorphism between the coface chains of `L` in
cardinality degree `n + #L` and the chains of the ordinary link in
cardinality degree `n`. -/
def cofaceChainsEquivLink (K : Finset (Finset V)) (L : Finset V) (n : ℕ) :
    ↥(cofaceChains K L (n + L.card)) ≃ₗ[ℝ] ↥(chains ℝ (link K L) n) where
  toFun c := ⟨linkShift L c.val, linkShift_mem_chains c.property⟩
  map_add' c d := Subtype.ext (by simp)
  map_smul' a c := Subtype.ext (by simp)
  invFun b := ⟨cofaceUnshift L b.val, cofaceUnshift_mem_cofaceChains b.property⟩
  left_inv c := Subtype.ext (cofaceUnshift_linkShift (mem_cofaceChains_subset c.property))
  right_inv b := Subtype.ext (linkShift_cofaceUnshift (chains_link_disjoint b.property))

@[simp]
theorem cofaceChainsEquivLink_apply (L : Finset V) (n : ℕ)
    (c : ↥(cofaceChains K L (n + L.card))) :
    ((cofaceChainsEquivLink K L n c) : Finset V → ℝ) = linkShift L c.val := rfl

/-! ### Compatibility with the differentials -/

section Boundary

variable [Fintype V]

/-- The shift intertwines the actual oriented boundary maps. -/
theorem linkShift_boundary (L : Finset V) (c : Finset V → ℝ) :
    linkShift L (boundary ℝ V c) = boundary ℝ V (linkShift L c) := by
  funext t
  by_cases ht : Disjoint t L
  · have hsubset : ((t ∪ L)ᶜ : Finset V) ⊆ (tᶜ : Finset V) :=
      Finset.compl_subset_compl.mpr Finset.subset_union_left
    have hzero : ∀ v ∈ (tᶜ : Finset V), v ∉ ((t ∪ L)ᶜ : Finset V) →
        orientedSign ℝ t v * linkShift L c (insert v t) = 0 := by
      intro v hv hv'
      have hvL : v ∈ L := (by simpa using hv' : v ∉ t → v ∈ L) (by simpa using hv)
      have hnotdis : ¬ Disjoint (insert v t) L := fun hdis =>
        (Finset.disjoint_left.mp hdis (Finset.mem_insert_self v t)) hvL
      simp [hnotdis]
    have hRHS : boundary ℝ V (linkShift L c) t
        = ∑ v ∈ ((t ∪ L)ᶜ : Finset V), orientedSign ℝ t v * linkShift L c (insert v t) := by
      rw [boundary_apply]
      exact (Finset.sum_subset hsubset hzero).symm
    have hLHS : linkShift L (boundary ℝ V c) t = ∑ v ∈ ((t ∪ L)ᶜ : Finset V),
        linkSign L t * (orientedSign ℝ (t ∪ L) v * c (insert v (t ∪ L))) := by
      simp only [linkShift_apply, ht, ite_true, boundary_apply, Finset.mul_sum]
    rw [hLHS, hRHS]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hvt : v ∉ t := Finset.mem_compl.mp (hsubset hv)
    have hvL : v ∉ L := fun hcon =>
      (Finset.mem_compl.mp hv) (Finset.mem_union_right _ hcon)
    have hdis : Disjoint (insert v t) L := by
      rw [Finset.disjoint_insert_left]
      exact ⟨hvL, ht⟩
    have hunion : insert v t ∪ L = insert v (t ∪ L) := Finset.insert_union v t L
    have hterm : linkShift L c (insert v t) = linkSign L (insert v t) * c (insert v (t ∪ L)) := by
      simp only [linkShift_apply, hdis, ite_true, hunion]
    rw [hterm, linkSign_insert hvt, orientedSign_union ht v]
    ring
  · have hzero : ∀ v ∈ (tᶜ : Finset V),
        orientedSign ℝ t v * linkShift L c (insert v t) = 0 := by
      intro v _
      have hnotdis : ¬ Disjoint (insert v t) L := fun hdis =>
        ht (hdis.mono_left (Finset.subset_insert v t))
      simp [hnotdis]
    simp only [linkShift_apply, ht, ite_false, boundary_apply]
    exact (Finset.sum_eq_zero hzero).symm

/-- The concrete relative differential becomes the augmented link boundary. -/
theorem linkShift_cofaceBoundary (L : Finset V) (c : Finset V → ℝ) :
    linkShift L (cofaceBoundary L c) = boundary ℝ V (linkShift L c) := by
  change linkShift L (cofaceRestriction L (boundary ℝ V c)) = _
  rw [linkShift_cofaceRestriction, linkShift_boundary]

theorem cofaceBoundary_subset (L : Finset V) (c : Finset V → ℝ) :
    ∀ F, cofaceBoundary L c F ≠ 0 → L ⊆ F := by
  intro F hF
  by_contra hcon
  apply hF
  change cofaceRestriction L (boundary ℝ V c) F = 0
  simp [hcon]

/-! ### Exactness transfer -/

/-- Exactness of the concrete coface complex in cardinality degree `n`. -/
def IsCofaceAcyclicAt (K : Finset (Finset V)) (L : Finset V) (n : ℕ) : Prop :=
  ∀ c ∈ cofaceChains K L n, cofaceBoundary L c = 0 →
    ∃ d ∈ cofaceChains K L (n + 1), cofaceBoundary L d = c

/-- **The shifted comparison.**  The coface complex at `L` is exact in
cardinality degree `n + #L` exactly when the ordinary link is reduced acyclic
in cardinality degree `n`. -/
theorem isCofaceAcyclicAt_iff_link (L : Finset V) (n : ℕ) :
    IsCofaceAcyclicAt K L (n + L.card) ↔ IsReducedAcyclicAt ℝ (link K L) n := by
  have hshift : ∀ m : ℕ, (n + 1) + m = (n + m) + 1 := fun m => by omega
  constructor
  · intro h b hb
    obtain ⟨hbmem, hbbd⟩ := mem_cycles_iff.mp hb
    have hc : cofaceUnshift L b ∈ cofaceChains K L (n + L.card) :=
      cofaceUnshift_mem_cofaceChains hbmem
    have hshiftb : linkShift L (cofaceUnshift L b) = b :=
      linkShift_cofaceUnshift (chains_link_disjoint hbmem)
    have hbd : cofaceBoundary L (cofaceUnshift L b) = 0 := by
      refine (linkShift_eq_zero_iff (cofaceBoundary_subset L _)).mp ?_
      rw [linkShift_cofaceBoundary, hshiftb, hbbd]
    obtain ⟨d, hd, hdc⟩ := h _ hc hbd
    refine ⟨linkShift L d, ?_, ?_⟩
    · exact linkShift_mem_chains ((hshift L.card) ▸ hd)
    · rw [← linkShift_cofaceBoundary, hdc, hshiftb]
  · intro h c hc hcbd
    have hlink : linkShift L c ∈ cycles ℝ (link K L) n := by
      refine mem_cycles_iff.mpr ⟨linkShift_mem_chains hc, ?_⟩
      rw [← linkShift_cofaceBoundary, hcbd, map_zero]
    obtain ⟨b, hb, hbc⟩ := h hlink
    refine ⟨cofaceUnshift L b, ?_, ?_⟩
    · exact (hshift L.card) ▸ cofaceUnshift_mem_cofaceChains hb
    · refine linkShift_injOn (cofaceBoundary_subset L _) (mem_cofaceChains_subset hc) ?_
      rw [linkShift_cofaceBoundary, linkShift_cofaceUnshift (chains_link_disjoint hb), hbc]

end Boundary

end AffineTverberg.Simplicial
