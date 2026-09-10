import AffineTverberg.LinkTopCycleRank

set_option linter.style.header false

/-!
# The incidence signs of iterated link orientations

The orientation of a link is the signed restriction of one global cycle.
Taking another link does not permit a new independent orientation choice:
the iterated signed restriction differs from restriction to the union by
exactly the shuffle sign. For adding a single vertex this is the ordinary
oriented simplex incidence sign. These are identities of the actual
coefficient maps, before taking homology.
-/

noncomputable section

open scoped BigOperators

namespace AffineTverberg.Simplicial

variable {V : Type} [LinearOrder V]

theorem linkSign_union_left {L M : Finset V} (hLM : Disjoint L M) (t : Finset V) :
    linkSign (L ∪ M) t = linkSign L t * linkSign M t := by
  simp only [linkSign, orientedSign_union hLM, Finset.prod_mul_distrib]

theorem linkSign_union_right (L : Finset V) {t M : Finset V} (htM : Disjoint t M) :
    linkSign L (t ∪ M) = linkSign L t * linkSign L M :=
  Finset.prod_union htM

/-- Iterating ordinary links gives the link of the union, as an exact
identity of finite face families. -/
theorem link_link_of_disjoint (K : Finset (Finset V)) {L M : Finset V}
    (hLM : Disjoint L M) : link (link K L) M = link K (L ∪ M) := by
  ext t
  simp only [mem_link_iff, Finset.disjoint_union_left, Finset.disjoint_union_right,
    hLM.symm, and_true]
  rw [show (t ∪ M) ∪ L = t ∪ (L ∪ M) by ac_rfl]
  exact and_assoc

/-- The shuffle sign records the complete discrepancy between an iterated
link restriction and the single restriction to the union. -/
theorem linkShift_linkShift {L M : Finset V} (hLM : Disjoint L M)
    (c : Finset V → ℝ) :
    linkShift M (linkShift L c) = linkSign L M • linkShift (L ∪ M) c := by
  funext t
  by_cases htM : Disjoint t M
  · by_cases htL : Disjoint t L
    · have htML : Disjoint (t ∪ M) L := Finset.disjoint_union_left.mpr ⟨htL, hLM.symm⟩
      have htLM : Disjoint t (L ∪ M) := Finset.disjoint_union_right.mpr ⟨htL, htM⟩
      simp only [linkShift_apply, htM, htML, htLM, ite_true, Pi.smul_apply,
        smul_eq_mul, linkSign_union_left hLM, linkSign_union_right L htM]
      rw [show (t ∪ M) ∪ L = t ∪ (L ∪ M) by ac_rfl]
      ring
    · have htML : ¬ Disjoint (t ∪ M) L := fun h => htL (h.mono_left Finset.subset_union_left)
      have htLM : ¬ Disjoint t (L ∪ M) := fun h => htL (h.mono_right Finset.subset_union_left)
      simp [htM, htML, htLM]
  · have htLM : ¬ Disjoint t (L ∪ M) := fun h => htM (h.mono_right Finset.subset_union_right)
    simp [htM, htLM]

/-- Adding one vertex gives exactly the original simplex incidence sign. -/
theorem linkShift_singleton_linkShift (L : Finset V) {v : V} (hv : v ∉ L)
    (c : Finset V → ℝ) :
    linkShift {v} (linkShift L c) = orientedSign ℝ L v • linkShift (insert v L) c := by
  have hdisj : Disjoint L {v} := by simp [hv]
  simpa [linkSign, Finset.union_singleton] using linkShift_linkShift hdisj c

variable [Fintype V] {K : Finset (Finset V)}

/-- The actual global-to-link top restriction has the signed coefficient
formula even when it is subsequently restricted to a further link. -/
theorem linkTopRestriction_iterated {L M : Finset V} (hLM : Disjoint L M)
    {n N : ℕ} (hn : n + L.card = N + 1)
    (z : ↥(cycles ℝ K (N + 1))) :
    linkShift M (linkTopRestriction hn z : Finset V → ℝ) =
      linkSign L M • linkShift (L ∪ M) z.val := by
  rw [linkTopRestriction_apply, linkShift_cofaceRestriction, linkShift_linkShift hLM]

/-- In particular, every codimension-one link orientation inherited from
the global cycle is related by the prescribed simplex incidence sign. -/
theorem linkTopRestriction_insert {L : Finset V} {v : V} (hv : v ∉ L)
    {n N : ℕ} (hn : n + L.card = N + 1)
    (z : ↥(cycles ℝ K (N + 1))) :
    linkShift {v} (linkTopRestriction hn z : Finset V → ℝ) =
      orientedSign ℝ L v • linkShift (insert v L) z.val := by
  rw [linkTopRestriction_apply, linkShift_cofaceRestriction, linkShift_singleton_linkShift L hv]

end AffineTverberg.Simplicial
