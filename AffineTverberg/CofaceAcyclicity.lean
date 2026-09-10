import AffineTverberg.LinkCofaceShift
import AffineTverberg.AlexanderDualityGeometric

set_option linter.style.header false

/-!
# Acyclicity of the coface complex from the costar and the ambient complex

The short exact sequence of the costar inclusion is here used at the level of
explicit coefficient functions: if the costar of a face is reduced acyclic in
degree `n - 1` and the ambient complex is reduced acyclic in degree `n`, then
the concrete relative (coface) complex is exact in cardinality degree `n`.
The chase is elementary — it uses only the actual oriented boundary and the
literal coface restriction — and therefore works in *every* degree, including
the two low endpoints that the global-to-relative homology comparison does not
reach.

Together with `LinkCofaceShift` this computes the reduced homology of the
*ordinary* combinatorial link in every degree.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.Simplicial

variable {V : Type} [Fintype V] [LinearOrder V] {K : Finset (Finset V)}

/-! ### Reduced acyclicity of a family with contractible polyhedron -/

/-- A face-closed family whose polyhedron is contractible is reduced acyclic in
every cardinality degree.  Degree `0` uses nonemptiness and degree `1` uses the
actual degree-zero augmentation. -/
theorem isReducedAcyclicAt_of_contractible_realization (hK : FaceClosed K)
    [ContractibleSpace ↥(barycentricCarrier K)] (n : ℕ) : IsReducedAcyclicAt ℝ K n := by
  match n with
  | 0 =>
    have hne : (barycentricCarrier K).Nonempty := by
      obtain ⟨x⟩ := (inferInstance : Nonempty ↥(barycentricCarrier K))
      exact ⟨x.val, x.property⟩
    exact isReducedAcyclicAt_zero_of_nonempty_realization hK hne
  | 1 =>
    have hpc : PathConnectedSpace ↥(barycentricCarrier K) := inferInstance
    have hpc' : PathConnectedSpace ↥(barySpace K) := hpc
    exact isReducedAcyclicAt_one_of_isIso_singularAugmentation hK inferInstance
  | (m + 2) =>
    refine (isZero_realSingularHomology_barySpace_iff hK m).mp ?_
    have hsub : Subsingleton ((realSingularHomology (m + 1)).obj (barySpace K)) :=
      realSingularHomology_subsingleton_of_contractible ↥(barycentricCarrier K) (m + 1)
        (Nat.succ_ne_zero m)
    exact ModuleCat.isZero_of_subsingleton _

/-! ### The chase -/

theorem boundary_mem_chains_costar {L : Finset V} {n : ℕ} {c : Finset V → ℝ}
    (hK : FaceClosed K) (hc : c ∈ cofaceChains K L (n + 1))
    (hcbd : cofaceBoundary L c = 0) :
    boundary ℝ V c ∈ chains ℝ (costarFamily K L) n := by
  have hmem : boundary ℝ V c ∈ chains ℝ K n :=
    boundary_mem_chains hK (cofaceChains_le L (n + 1) hc)
  intro t ht
  refine ⟨mem_costarFamily.mpr ⟨(hmem t ht).1, ?_⟩, (hmem t ht).2⟩
  intro hLt
  apply ht
  have h := congrFun hcbd t
  change (if L ⊆ t then boundary ℝ V c t else 0) = 0 at h
  simpa only [hLt, ite_true] using h

/-- **The elementary exactness chase.**  Acyclicity of the costar one degree
below and of the ambient family in the same degree gives exactness of the
concrete coface complex. -/
theorem isCofaceAcyclicAt_of_acyclic (hK : FaceClosed K) (L : Finset V) (n : ℕ)
    (hcostar : IsReducedAcyclicAt ℝ (costarFamily K L) n)
    (hambient : IsReducedAcyclicAt ℝ K (n + 1)) :
    IsCofaceAcyclicAt K L (n + 1) := by
  intro c hc hcbd
  have hcycle : boundary ℝ V c ∈ cycles ℝ (costarFamily K L) n :=
    mem_cycles_iff.mpr ⟨boundary_mem_chains_costar hK hc hcbd, boundary_boundary_apply c⟩
  obtain ⟨b, hb, hbc⟩ := hcostar hcycle
  have hbK : b ∈ chains ℝ K (n + 1) := chains_mono (costarFamily_subset K L) (n + 1) hb
  have hdiff : c - b ∈ cycles ℝ K (n + 1) := by
    refine mem_cycles_iff.mpr ⟨Submodule.sub_mem _ (cofaceChains_le L (n + 1) hc) hbK, ?_⟩
    rw [map_sub, hbc, sub_self]
  obtain ⟨d, hd, hdc⟩ := hambient hdiff
  refine ⟨cofaceRestriction L d, cofaceRestriction_mem_cofaceChains hd L, ?_⟩
  have hrestr : cofaceBoundary L (cofaceRestriction L d) = cofaceRestriction L (boundary ℝ V d) :=
    cofaceRestriction_boundary_cofaceRestriction L d
  rw [hrestr, hdc, map_sub, cofaceRestriction_eq_self hc,
    (cofaceRestriction_eq_zero_iff_costar hbK).mpr hb, sub_zero]

/-- **The reduced homology of the ordinary link, in every degree.**  If the
costar of `L` is acyclic one degree below and the ambient family is acyclic in
the shifted degree, the ordinary combinatorial link is reduced acyclic. -/
theorem isReducedAcyclicAt_link_of_acyclic (hK : FaceClosed K) (L : Finset V) (n j : ℕ)
    (hj : n + L.card = j + 1)
    (hcostar : IsReducedAcyclicAt ℝ (costarFamily K L) j)
    (hambient : IsReducedAcyclicAt ℝ K (j + 1)) :
    IsReducedAcyclicAt ℝ (link K L) n := by
  refine (isCofaceAcyclicAt_iff_link L n).mp ?_
  rw [hj]
  exact isCofaceAcyclicAt_of_acyclic hK L j hcostar hambient

end AffineTverberg.Simplicial
