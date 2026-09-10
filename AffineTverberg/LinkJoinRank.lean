import AffineTverberg.SimplexBoundaryRank

set_option linter.style.header false

/-!
# The top homology of the join of a simplex boundary with a finite point set

Let `L` be a nonempty simplex and let `V` be a finite set of vertices disjoint
from `L`.  The family

`boundaryJoinPoints L V = {t ⊆ L ∪ V | L ⊄ t and #(t ∩ V) ≤ 1}`

is the (abstract) join of the boundary of `L` with the discrete complex on the
vertex set `V`.  Geometrically this is exactly the local model around a
relative interior point of a codimension one face `L` of a pure complex, the
elements of `V` being the apexes of the facets containing `L`.

The main results are that all simplices of this family have at most `L.card`
vertices, so that the cycles in cardinality degree `L.card` are the top
homology, and that this top cycle space has dimension at least `V.card - 1`,
witnessed by the explicit differences of the normalised boundaries of the
cones `insert v L`.

Combined with `finrank_realSingularHomology_top` this bounds the rank of the
singular homology of the geometric realization from below by `V.card - 1`.
This is the combinatorial half of the local homology computation at a ridge:
a codimension one face contained in `k` facets contributes rank `k - 1`.
-/

noncomputable section

open scoped BigOperators

namespace AffineTverberg.Simplicial

section Combinatorial

variable {𝕜 W : Type*} [Field 𝕜] [Fintype W] [LinearOrder W]

/-- The join of the boundary of `L` with the discrete point set `V`: subsets of
`L ∪ V` which do not contain all of `L` and meet `V` in at most one point. -/
def boundaryJoinPoints (L V : Finset W) : Finset (Finset W) :=
  (L ∪ V).powerset.filter (fun t => ¬ L ⊆ t ∧ (t ∩ V).card ≤ 1)

variable {L V : Finset W}

omit [Fintype W] in
theorem mem_boundaryJoinPoints {t : Finset W} :
    t ∈ boundaryJoinPoints L V ↔ t ⊆ L ∪ V ∧ ¬ L ⊆ t ∧ (t ∩ V).card ≤ 1 := by
  simp only [boundaryJoinPoints, Finset.mem_filter, Finset.mem_powerset]

omit [Fintype W] in
theorem faceClosed_boundaryJoinPoints (L V : Finset W) :
    FaceClosed (boundaryJoinPoints L V) := by
  intro s hs t hts
  obtain ⟨hsub, hnot, hcard⟩ := mem_boundaryJoinPoints.mp hs
  refine mem_boundaryJoinPoints.mpr ⟨hts.trans hsub, ?_, ?_⟩
  · exact fun hL => hnot (hL.trans hts)
  · exact le_trans (Finset.card_le_card
      (Finset.inter_subset_inter_right hts)) hcard

omit [Fintype W] in
/-- Every simplex of the join has at most `L.card` vertices: it misses a vertex
of `L` and contains at most one vertex of `V`. -/
theorem card_le_of_mem_boundaryJoinPoints (hLV : Disjoint L V) {t : Finset W}
    (ht : t ∈ boundaryJoinPoints L V) : t.card ≤ L.card := by
  obtain ⟨hsub, hnot, hcard⟩ := mem_boundaryJoinPoints.mp ht
  have hsplit : t = (t ∩ L) ∪ (t ∩ V) := by
    rw [← Finset.inter_union_distrib_left]
    exact (Finset.inter_eq_left.mpr hsub).symm
  have hdisj : Disjoint (t ∩ L) (t ∩ V) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hLV)
  have hlt : (t ∩ L).card < L.card := by
    refine Finset.card_lt_card (lt_of_le_of_ne Finset.inter_subset_right ?_)
    intro heq
    exact hnot (heq ▸ Finset.inter_subset_left)
  calc t.card = (t ∩ L).card + (t ∩ V).card := by
        conv_lhs => rw [hsplit]
        exact Finset.card_union_of_disjoint hdisj
    _ ≤ L.card := by omega

/-- The normalised boundary of the cone `insert v L`: a chain with coefficient
one on `L`. -/
def apexCycle (𝕜 : Type*) [Field 𝕜] (L : Finset W) (v : W) : Finset W → 𝕜 :=
  (boundaryCoeff 𝕜 L (insert v L))⁻¹ • boundary 𝕜 W (simplexChain 𝕜 (insert v L))

theorem apexCycle_apply (L : Finset W) (v : W) (t : Finset W) :
    apexCycle 𝕜 L v t
      = (boundaryCoeff 𝕜 L (insert v L))⁻¹ * boundaryCoeff 𝕜 t (insert v L) := by
  rw [apexCycle, Pi.smul_apply, smul_eq_mul, boundary_simplexChain_apply]

theorem apexCycle_self {v : W} (hv : v ∉ L) : apexCycle 𝕜 L v L = 1 := by
  rw [apexCycle_apply]
  exact inv_mul_cancel₀ ((boundaryCoeff_ne_zero_iff (𝕜 := 𝕜) L _).mpr
    (isSimplexFacet_insert hv))

theorem apexCycle_eq_zero_of_not_isSimplexFacet {v : W} {t : Finset W}
    (h : ¬ IsSimplexFacet t (insert v L)) : apexCycle 𝕜 L v t = 0 := by
  rw [apexCycle_apply, boundaryCoeff_eq_zero_of_not_isSimplexFacet h, mul_zero]

theorem isSimplexFacet_of_apexCycle_ne_zero {v : W} {t : Finset W}
    (h : apexCycle 𝕜 L v t ≠ 0) : IsSimplexFacet t (insert v L) := by
  by_contra hf
  exact h (apexCycle_eq_zero_of_not_isSimplexFacet hf)

theorem boundary_apexCycle (L : Finset W) (v : W) :
    boundary 𝕜 W (apexCycle 𝕜 L v) = 0 := by
  rw [apexCycle, map_smul, boundary_boundary_apply, smul_zero]

/-- The `v`-th cone chain is nonzero on the facet obtained from `insert v L` by
deleting a vertex `u` of `L`. -/
theorem apexCycle_erase_ne_zero {v u : W} (hv : v ∉ L) (hu : u ∈ L) :
    apexCycle 𝕜 L v (insert v (L.erase u)) ≠ 0 := by
  have hvL : v ∉ L.erase u := fun h => hv (Finset.mem_of_mem_erase h)
  have hcard : (insert v (L.erase u)).card + 1 = (insert v L).card := by
    rw [Finset.card_insert_of_notMem hvL, Finset.card_insert_of_notMem hv,
      Finset.card_erase_of_mem hu]
    have : 1 ≤ L.card := Finset.card_pos.mpr ⟨u, hu⟩
    omega
  have hfacet : IsSimplexFacet (insert v (L.erase u)) (insert v L) :=
    ⟨Finset.insert_subset_insert _ (Finset.erase_subset _ _), hcard⟩
  rw [apexCycle_apply]
  exact mul_ne_zero (inv_ne_zero ((boundaryCoeff_ne_zero_iff (𝕜 := 𝕜) L _).mpr
    (isSimplexFacet_insert hv)))
    ((boundaryCoeff_ne_zero_iff (𝕜 := 𝕜) _ _).mpr hfacet)

/-- Distinct apexes see disjoint sets of facets. -/
theorem apexCycle_erase_eq_zero {v v' u : W} (hv : v ∉ L) (hne : v' ≠ v) :
    apexCycle 𝕜 L v' (insert v (L.erase u)) = 0 := by
  refine apexCycle_eq_zero_of_not_isSimplexFacet fun hfacet => ?_
  have hmem : v ∈ insert v' L := hfacet.1 (Finset.mem_insert_self _ _)
  rcases Finset.mem_insert.mp hmem with h | h
  · exact hne h.symm
  · exact hv h

/-- The difference of two cone chains is a top cycle of the join. -/
theorem sub_apexCycle_mem_cycles (hLV : Disjoint L V) {v v₀ : W}
    (hv : v ∈ V) (hv₀ : v₀ ∈ V) :
    apexCycle 𝕜 L v - apexCycle 𝕜 L v₀ ∈ cycles 𝕜 (boundaryJoinPoints L V) L.card := by
  have hvL : v ∉ L := fun h => (Finset.disjoint_left.mp hLV h) hv
  have hv₀L : v₀ ∉ L := fun h => (Finset.disjoint_left.mp hLV h) hv₀
  refine ⟨?_, ?_⟩
  · intro t ht
    have hL : (apexCycle 𝕜 L v - apexCycle 𝕜 L v₀) L = 0 := by
      simp [Pi.sub_apply, apexCycle_self (𝕜 := 𝕜) hvL, apexCycle_self (𝕜 := 𝕜) hv₀L]
    have htL : t ≠ L := fun h => ht (h ▸ hL)
    -- one of the two chains is nonzero at `t`
    have hex : ∃ w ∈ V, w ∉ L ∧ IsSimplexFacet t (insert w L) := by
      by_cases h : apexCycle 𝕜 L v t = 0
      · refine ⟨v₀, hv₀, hv₀L, isSimplexFacet_of_apexCycle_ne_zero (𝕜 := 𝕜) (t := t) ?_⟩
        intro h0
        exact ht (by simp [Pi.sub_apply, h, h0])
      · exact ⟨v, hv, hvL, isSimplexFacet_of_apexCycle_ne_zero h⟩
    obtain ⟨w, hwV, hwL, hfacet⟩ := hex
    have hcard : t.card = L.card := by
      have := hfacet.2
      rw [Finset.card_insert_of_notMem hwL] at this
      omega
    refine ⟨mem_boundaryJoinPoints.mpr ⟨?_, ?_, ?_⟩, hcard⟩
    · refine hfacet.1.trans ?_
      intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · exact Finset.mem_union_right _ (h ▸ hwV)
      · exact Finset.mem_union_left _ h
    · intro hsub
      exact htL (Finset.eq_of_subset_of_card_le hsub hcard.le).symm
    · have hsub : t ∩ V ⊆ {w} := by
        intro x hx
        rw [Finset.mem_inter] at hx
        have hxw : x ∈ insert w L := hfacet.1 hx.1
        rcases Finset.mem_insert.mp hxw with h | h
        · simp [h]
        · exact absurd hx.2 (Finset.disjoint_left.mp hLV h)
      calc (t ∩ V).card ≤ ({w} : Finset W).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton w
  · have hker : boundary 𝕜 W (apexCycle 𝕜 L v - apexCycle 𝕜 L v₀) = 0 := by
      rw [map_sub, boundary_apexCycle, boundary_apexCycle, sub_zero]
    exact hker

/-- **The lower bound on the top cycles of the join.**  If `L` is nonempty and
disjoint from `V`, then the top cycle space of `boundaryJoinPoints L V` has
dimension at least `V.card - 1`. -/
theorem card_sub_one_le_finrank_cycles_boundaryJoinPoints (hLV : Disjoint L V)
    (hL : L.Nonempty) :
    V.card - 1 ≤ Module.finrank 𝕜 ↥(cycles 𝕜 (boundaryJoinPoints L V) L.card) := by
  classical
  rcases V.eq_empty_or_nonempty with rfl | hV
  · simp
  obtain ⟨v₀, hv₀⟩ := hV
  obtain ⟨u, hu⟩ := hL
  set f : ↥(V.erase v₀) → (Finset W → 𝕜) :=
    fun v => apexCycle 𝕜 L (v : W) - apexCycle 𝕜 L v₀ with hf
  have hmemV : ∀ v : ↥(V.erase v₀), (v : W) ∈ V := fun v => Finset.mem_of_mem_erase v.2
  have hnotL : ∀ w ∈ V, w ∉ L := fun w hw hwL => (Finset.disjoint_left.mp hLV hwL) hw
  have hv₀L : v₀ ∉ L := hnotL v₀ hv₀
  -- linear independence
  have hli : LinearIndependent 𝕜 f := by
    rw [linearIndependent_iff']
    intro s g hg j hj
    have hjV : (j : W) ∈ V := hmemV j
    have hjL : (j : W) ∉ L := hnotL _ hjV
    have hjv₀ : (j : W) ≠ v₀ := Finset.ne_of_mem_erase j.2
    have heval := congrFun hg (insert (j : W) (L.erase u))
    have hzero : ∀ v ∈ s, v ≠ j →
        (g v • f v) (insert (j : W) (L.erase u)) = 0 := by
      intro v _ hvj
      have hvne : (v : W) ≠ (j : W) := fun h => hvj (Subtype.ext h)
      have h1 : apexCycle 𝕜 L (v : W) (insert (j : W) (L.erase u)) = 0 :=
        apexCycle_erase_eq_zero hjL hvne
      have h2 : apexCycle 𝕜 L v₀ (insert (j : W) (L.erase u)) = 0 :=
        apexCycle_erase_eq_zero hjL (Ne.symm hjv₀)
      simp [hf, Pi.smul_apply, Pi.sub_apply, h1, h2]
    have hjval : (g j • f j) (insert (j : W) (L.erase u))
        = g j * apexCycle 𝕜 L (j : W) (insert (j : W) (L.erase u)) := by
      have h2 : apexCycle 𝕜 L v₀ (insert (j : W) (L.erase u)) = 0 :=
        apexCycle_erase_eq_zero hjL (Ne.symm hjv₀)
      simp [hf, Pi.smul_apply, Pi.sub_apply, h2]
    have hsum : (∑ v ∈ s, g v • f v) (insert (j : W) (L.erase u))
        = g j * apexCycle 𝕜 L (j : W) (insert (j : W) (L.erase u)) := by
      rw [Finset.sum_apply, Finset.sum_eq_single_of_mem j hj hzero, hjval]
    rw [heval] at hsum
    have hne := apexCycle_erase_ne_zero (𝕜 := 𝕜) hjL hu
    have : g j * apexCycle 𝕜 L (j : W) (insert (j : W) (L.erase u)) = 0 := by
      simpa using hsum.symm
    exact (mul_eq_zero.mp this).resolve_right hne
  -- the span sits inside the cycles
  have hspan : Submodule.span 𝕜 (Set.range f) ≤ cycles 𝕜 (boundaryJoinPoints L V) L.card := by
    rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    exact sub_apexCycle_mem_cycles hLV (hmemV v) hv₀
  have hcard : Module.finrank 𝕜 ↥(Submodule.span 𝕜 (Set.range f))
      = Fintype.card ↥(V.erase v₀) := finrank_span_eq_card hli
  have hmono := Submodule.finrank_mono (R := 𝕜) hspan
  rw [hcard, Fintype.card_coe, Finset.card_erase_of_mem hv₀] at hmono
  exact hmono

end Combinatorial

section Singular

variable {W : Type} [Fintype W] [LinearOrder W] {L V : Finset W}

/-- **The singular version.**  The realization of the join of the boundary of a
`(j+2)`-element simplex `L` with a finite point set `V` disjoint from `L` has
singular homology of rank at least `V.card - 1` in degree `j + 1`. -/
theorem card_sub_one_le_finrank_realSingularHomology_boundaryJoinPoints
    (hLV : Disjoint L V) {j : ℕ} (hL : L.card = j + 2) :
    V.card - 1 ≤ Module.finrank ℝ
      ((realSingularHomology (j + 1)).obj (barySpace (boundaryJoinPoints L V))) := by
  have hne : L.Nonempty := Finset.card_pos.mp (by omega)
  rw [finrank_realSingularHomology_top (faceClosed_boundaryJoinPoints L V) j
    (fun t ht => hL ▸ card_le_of_mem_boundaryJoinPoints hLV ht)]
  have := card_sub_one_le_finrank_cycles_boundaryJoinPoints (𝕜 := ℝ) hLV hne
  rwa [hL] at this

end Singular

end AffineTverberg.Simplicial
