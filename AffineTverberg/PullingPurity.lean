import AffineTverberg.PullingSubdivision

set_option linter.style.header false

/-!
# Purity of the pulling subdivision over a graded face family

Every simplex of `sdPoset orig F S` extends to an apex-flag simplex of `S`,
provided the face family is *graded relative to the apex*: any face `G ⊆ S` of
the family missing the apex of `S` is contained in a face `H ⊆ S` of the family
which still misses the apex of `S` and whose rank is one less than the rank of
`S`.  For a polytopal face family this hypothesis is exactly the facet lemma
`AffineTverberg.PolytopeFace.exists_facet_exposed_avoiding`.

Consequences proved here:

* `exists_isApexFlag` — full simplices exist;
* `sdPoset_purity` — every simplex extends to a full (flag) simplex;
* `sdPoset_exists_top_simplex_card` — the extension has exactly `rank S`
  vertices, i.e. the subdivision is pure of that dimension;
* `sdPoset_exists_extension_good_count` — the extension moreover carries at
  least `mm S + 1` good vertices, which is the form consumed by the local
  acyclicity theorem.
-/

open scoped BigOperators

namespace AffineTverberg
namespace BadEdge

variable {W V : Type*} [DecidableEq W] [LinearOrder W] [DecidableEq V]

/-- Gradedness of the face family relative to the apex of a face: this is the
combinatorial content of the polytope facet lemma. -/
def ApexGraded (orig : W → V) (F : Finset (Finset W)) (rank : Finset W → ℕ) : Prop :=
  ∀ S ∈ F, ∀ G ∈ F, G ⊆ S → ¬ apexSet orig S ⊆ G →
    ∃ H ∈ F, G ⊆ H ∧ H ⊆ S ∧ ¬ apexSet orig S ⊆ H ∧ rank H + 1 = rank S

/-- **Purity of the pulling subdivision.**  Over an apex-graded face family
every simplex of the subdivision of `S` is contained in an apex-flag simplex of
`S`. -/
theorem sdPoset_purity {orig : W → V} {F : Finset (Finset W)} {rank : Finset W → ℕ}
    (hgr : ApexGraded orig F rank) (hFe : ∅ ∈ F)
    (hrk : ∀ S ∈ F, rank S ≠ 0 → S.Nonempty)
    {S : Finset W} (hS : S ∈ F) {σ : Finset (Finset W)} (hσ : σ ∈ sdPoset orig F S) :
    ∃ τ, IsApexFlag orig F rank S τ ∧ σ ⊆ τ := by
  induction hk : S.card using Nat.strong_induction_on generalizing S σ with
  | _ k ih =>
    subst hk
    -- the recursive step, used in all three cases: enlarge a face missing the
    -- apex to one of codimension one and extend a simplex of its subdivision
    have key : ∀ G ∈ F, G ⊆ S → ¬ apexSet orig S ⊆ G → ∀ ρ ∈ sdPoset orig F G,
        ∃ τ, IsApexFlag orig F rank S (insert (apexSet orig S) τ) ∧ ρ ⊆ τ := by
      intro G hG hGS hna ρ hρ
      obtain ⟨H, hH, hGH, hHS, hnaH, hrank⟩ := hgr S hS G hG hGS hna
      have hlt : H.card < S.card := card_lt_of_apexSet_not_subset (orig := orig) hHS hnaH
      have hρH : ρ ∈ sdPoset orig F H := sdPoset_mono hG hGH hρ
      obtain ⟨τ, hτ, hρτ⟩ := ih H.card hlt hH hρH rfl
      exact ⟨τ, IsApexFlag.step hH hHS hnaH hrank hτ, hρτ⟩
    rcases mem_sdPoset_iff.mp hσ with rfl | ⟨G, hGF, hGS, hna, hcase⟩
    · -- the empty simplex: a full simplex exists
      by_cases h0 : rank S = 0
      · exact ⟨∅, IsApexFlag.base h0, Finset.Subset.refl _⟩
      · have hSne : S.Nonempty := hrk S hS h0
        have hane : (apexSet orig S).Nonempty := apexSet_nonempty hSne
        have hna : ¬ apexSet orig S ⊆ (∅ : Finset W) := by
          intro hsub
          rw [Finset.subset_empty] at hsub
          exact hane.ne_empty hsub
        obtain ⟨τ, hτ, -⟩ :=
          key ∅ hFe (Finset.empty_subset _) hna ∅ (empty_mem_sdPoset _ _ _)
        exact ⟨_, hτ, Finset.empty_subset _⟩
    · rcases hcase with h | ⟨ρ, hρ, rfl⟩
      · obtain ⟨τ, hτ, hστ⟩ := key G hGF hGS hna σ h
        exact ⟨_, hτ, hστ.trans (Finset.subset_insert _ _)⟩
      · obtain ⟨τ, hτ, hρτ⟩ := key G hGF hGS hna ρ hρ
        exact ⟨_, hτ, Finset.insert_subset_insert _ hρτ⟩

/-- Existence of full simplices. -/
theorem exists_isApexFlag {orig : W → V} {F : Finset (Finset W)} {rank : Finset W → ℕ}
    (hgr : ApexGraded orig F rank) (hFe : ∅ ∈ F)
    (hrk : ∀ S ∈ F, rank S ≠ 0 → S.Nonempty) {S : Finset W} (hS : S ∈ F) :
    ∃ τ, IsApexFlag orig F rank S τ := by
  obtain ⟨τ, hτ, -⟩ := sdPoset_purity hgr hFe hrk hS (empty_mem_sdPoset orig F S)
  exact ⟨τ, hτ⟩

/-- **The subdivision is pure**: every simplex extends to one with exactly
`rank S` vertices. -/
theorem sdPoset_exists_top_simplex_card {orig : W → V} {F : Finset (Finset W)}
    {rank : Finset W → ℕ} (hgr : ApexGraded orig F rank) (hFe : ∅ ∈ F)
    (hrk : ∀ S ∈ F, rank S ≠ 0 → S.Nonempty)
    {S : Finset W} (hS : S ∈ F) {σ : Finset (Finset W)} (hσ : σ ∈ sdPoset orig F S) :
    ∃ τ ∈ sdPoset orig F S, σ ⊆ τ ∧ τ.card = rank S := by
  obtain ⟨τ, hτ, hστ⟩ := sdPoset_purity hgr hFe hrk hS hσ
  exact ⟨τ, hτ.mem_sdPoset, hστ, hτ.card_eq_rank⟩

/-- **Purity together with the good-vertex count**, in the shape consumed by the
local acyclicity theorem: every simplex extends to a simplex with `rank S`
vertices, at least `mm S + 1` of which are good. -/
theorem sdPoset_exists_extension_good_count {orig : W → V} {F : Finset (Finset W)}
    {rank mm : Finset W → ℕ} (hgr : ApexGraded orig F rank) (hFe : ∅ ∈ F)
    (hrk : ∀ S ∈ F, rank S ≠ 0 → S.Nonempty)
    (hdrop : ∀ S ∈ F, ∀ G ∈ F, G ⊆ S → rank G + 1 = rank S → mm S ≤ mm G + 1)
    (hbad : ∀ S ∈ F, ∀ G ∈ F, G ⊆ S → rank G + 1 = rank S →
      ¬ apexSet orig S ⊆ G → (apexSet orig S).card = 2 → mm S ≤ mm G)
    (hrank1 : ∀ S ∈ F, rank S = 1 → mm S = 0 ∧ (apexSet orig S).card = 1)
    {S : Finset W} (hS : S ∈ F) (hS1 : 1 ≤ rank S)
    {σ : Finset (Finset W)} (hσ : σ ∈ sdPoset orig F S) :
    ∃ τ ∈ sdPoset orig F S, σ ⊆ τ ∧ τ.card = rank S ∧
      mm S + 1 ≤ (goodVertices τ).card := by
  obtain ⟨τ, hτ, hστ⟩ := sdPoset_purity hgr hFe hrk hS hσ
  exact ⟨τ, hτ.mem_sdPoset, hστ, hτ.card_eq_rank,
    card_goodVertices_ge hdrop hbad hrank1 hS hS1 hτ⟩

end BadEdge
end AffineTverberg
