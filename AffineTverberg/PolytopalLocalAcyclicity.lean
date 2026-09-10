import AffineTverberg.PolytopalIntersection
import AffineTverberg.LocalAcyclicity

set_option linter.style.header false

/-!
# Local acyclicity of the good subcomplex of a polytopal face

Purity (`sdQ_purity`), the sharp good-vertex count
(`card_goodVertices_ge_projDim_succ`) and the geometric realization
(`isGeometricRealization_sdQ`) are exactly the hypotheses of the verified local
acyclicity theorems.  Instantiating them gives, for every face `S` of the Cayley
join:

* `goodRealization_eq_deletedFaces` — the good carrier inside `S` is the union of
  the carriers of the deleted faces contained in `S` (the deleted join inside
  `S`, not merely at the top face);
* `local_simplicial_acyclicity_sdQ` — the good induced subcomplex of `sdQ P m S`
  is reduced acyclic up to the augmented degree `projDim S`, computed with the
  real oriented boundary;
* `local_singular_acyclicity_sdQ` — the corresponding statement in actual
  singular homology of the good carrier.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg
namespace Simplicial

/-! ### Instance-explicit forms of the local acyclicity theorems

The verified local acyclicity theorems phrase the induced subcomplex through the
decidable equality carried by the linear order on the vertices.  At a concrete
vertex type another (propositionally equal) decidable equality is inferred, so we
record the versions in which the decidable equality is an explicit argument. -/

section InstanceExplicit

variable {V E : Type} [Fintype V] [inst : LinearOrder V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem local_simplicial_acyclicity_of_good_count'
    {dec : DecidableEq V} {K : Finset (Finset V)} {p : V → E} (hK : FaceClosed K)
    (hgeom : @IsGeometricRealization V dec E _ _ K p) (G : Finset V) (m : ℕ)
    (hne : (geometricCarrier K p).Nonempty) (hconv : Convex ℝ (geometricCarrier K p))
    (hpure : ∀ s ∈ K, ∃ t ∈ K, s ⊆ t ∧
      t.card = Module.finrank ℝ (affineSpan ℝ (geometricCarrier K p)).direction + 1)
    (hgood : ∀ t ∈ K,
      t.card = Module.finrank ℝ (affineSpan ℝ (geometricCarrier K p)).direction + 1 →
      m + 1 ≤ (@Inter.inter _ (@Finset.instInter V dec) t G).card) :
    IsReducedAcyclicUpTo ℝ (@inducedFaces V dec K G) m := by
  have h : dec = inst.toDecidableEq := Subsingleton.elim _ _
  subst h
  exact local_simplicial_acyclicity_of_good_count hK hgeom G m hne hconv hpure hgood

omit [Fintype V] in
theorem local_singular_acyclicity_of_good_count' [Finite V]
    {dec : DecidableEq V} {K : Finset (Finset V)} {p : V → E} (hK : FaceClosed K)
    (hgeom : @IsGeometricRealization V dec E _ _ K p) (G : Finset V) (m : ℕ)
    (hne : (geometricCarrier K p).Nonempty) (hconv : Convex ℝ (geometricCarrier K p))
    (hpure : ∀ s ∈ K, ∃ t ∈ K, s ⊆ t ∧
      t.card = Module.finrank ℝ (affineSpan ℝ (geometricCarrier K p)).direction + 1)
    (hgood : ∀ t ∈ K,
      t.card = Module.finrank ℝ (affineSpan ℝ (geometricCarrier K p)).direction + 1 →
      m + 1 ≤ (@Inter.inter _ (@Finset.instInter V dec) t G).card) :
    (geometricCarrier (@inducedFaces V dec K G) p).Nonempty ∧
      (1 ≤ m → CategoryTheory.IsIso (realSingularAugmentation
        (TopCat.of ↥(geometricCarrier (@inducedFaces V dec K G) p)))) ∧
      ∀ n, n ≠ 0 → n + 1 ≤ m →
        CategoryTheory.Limits.IsZero ((realSingularHomology n).obj
          (TopCat.of ↥(geometricCarrier (@inducedFaces V dec K G) p))) := by
  have h : dec = inst.toDecidableEq := Subsingleton.elim _ _
  subst h
  exact local_singular_acyclicity_of_good_count hK hgeom G m hne hconv hpure hgood

end InstanceExplicit

end Simplicial

namespace BadVertex

open CayleyJoin PolytopeFace BadEdge _root_.AffineTverberg.Simplicial

variable {n : ℕ} {P : FullDimensionalPolytope n} {m : ℕ}

/-- An explicit linear order on the vertices of the subdivision; it shows that
the order hypothesis of the homology machinery is not vacuous. -/
@[instance_reducible] def joinVertexSetOrder (P : FullDimensionalPolytope n) (m : ℕ) :
    LinearOrder (Finset (JoinVertex P m)) :=
  LinearOrder.lift' (Fintype.equivFin (Finset (JoinVertex P m))) (Equiv.injective _)

/-- The good vertices of the subdivision: the original Cayley vertices. -/
def goodJoinVertices (P : FullDimensionalPolytope n) (m : ℕ) :
    Finset (Finset (JoinVertex P m)) :=
  Finset.univ.filter fun b ↦ b.card = 1

/-! ### The good carrier inside a face is the deleted join inside that face -/

/-- **The good subcomplex of a face is the deleted join inside that face.** -/
theorem goodRealization_eq_deletedFaces {S : Finset (JoinVertex P m)}
    (hS : S ∈ faceFamily P m) :
    goodRealization P m S =
      ⋃ T ∈ {T : Finset (JoinVertex P m) |
        T ∈ faceFamily P m ∧ T ⊆ S ∧ IsDeletedFace (origIndex P m) T},
        sdCarrier P m T := by
  apply Subset.antisymm
  · apply iUnion₂_subset
    intro σ hσ
    obtain ⟨hσQ, hgood⟩ := Finset.mem_filter.mp hσ
    obtain ⟨G, hGmem, hGsub, hGdel, hvert⟩ :=
      sdPoset_good_exists_deleted_face (empty_mem_faceFamily P m) hσQ hgood
    have hGfam : G ∈ faceFamily P m := by
      rcases hGmem with h | h
      · exact h
      · exact h ▸ hS
    refine subset_iUnion₂_of_subset G ⟨hGfam, hGsub, hGdel⟩ ?_
    apply convexHull_min _ (sdCarrier_convex P m G)
    rintro _ ⟨a, ha, rfl⟩
    exact sdPoint_mem_sdCarrier P m (hvert a ha) (sdPoset_vertex_nonempty hσQ ha)
  · apply iUnion₂_subset
    rintro T ⟨hTfam, hTS, hTdel⟩
    rw [← realization_eq_sdCarrier P m hTfam]
    apply iUnion₂_subset
    intro σ hσ
    refine subset_iUnion₂_of_subset σ (Finset.mem_filter.mpr ⟨sdQ_mono P m hTfam hTS hσ, ?_⟩)
      (subset_refl _)
    exact fun a ha ↦ sdPoset_card_eq_one_of_deleted hTdel hσ ha

/-! ### The hypotheses of the local acyclicity theorem -/

theorem faceClosed_sdQ (S : Finset (JoinVertex P m)) : FaceClosed (sdQ P m S) :=
  fun _ hσ _ hτ ↦ sdQ_faceClosed P m hσ hτ

theorem geometricCarrier_sdQ {S : Finset (JoinVertex P m)} (hS : S ∈ faceFamily P m) :
    geometricCarrier (sdQ P m S) (sdPoint P m) = sdCarrier P m S :=
  realization_eq_sdCarrier P m hS

theorem sdCarrier_nonempty {S : Finset (JoinVertex P m)} (hSne : S.Nonempty) :
    (sdCarrier P m S).Nonempty := by
  obtain ⟨w, hw⟩ := hSne
  exact ⟨pt P m w, subset_convexHull ℝ _ ⟨w, hw, rfl⟩⟩

/-- The affine dimension of a face of the Cayley join, in the form used by the
local acyclicity theorem. -/
theorem finrank_direction_sdCarrier {S : Finset (JoinVertex P m)}
    (hS : S ∈ faceFamily P m) (hSne : S.Nonempty) :
    Module.finrank ℝ (affineSpan ℝ (sdCarrier P m S)).direction + 1 = jrank P m S := by
  rw [jrank_eq_arank_sdCarrier hS, arank_of_nonempty (sdCarrier_nonempty hSne),
    direction_affineSpan]

/-- A simplex of full cardinality is an apex flag; this is where purity is
used. -/
theorem isApexFlag_of_card_eq {S : Finset (JoinVertex P m)} (hS : S ∈ faceFamily P m)
    {t : Finset (Finset (JoinVertex P m))} (ht : t ∈ sdQ P m S)
    (hcard : t.card = jrank P m S) :
    IsApexFlag (origIndex P m) (faceFamily P m) (jrank P m) S t := by
  obtain ⟨τ, hτ, htτ⟩ := sdQ_purity hS ht
  have hτcard : τ.card = jrank P m S := hτ.card_eq_rank
  have : t = τ := Finset.eq_of_subset_of_card_le htτ (by omega)
  exact this ▸ hτ

theorem inter_goodJoinVertices (t : Finset (Finset (JoinVertex P m))) :
    t ∩ goodJoinVertices P m = goodVertices t := by
  ext b
  simp [goodVertices, goodJoinVertices, Finset.mem_inter, Finset.mem_filter]

section Order

variable [inst : LinearOrder (Finset (JoinVertex P m))]

/-- **Local acyclicity of the good subcomplex of a polytopal face**, in the
oriented augmented simplicial complex used by the acyclic-gluing induction. -/
theorem local_simplicial_acyclicity_sdQ {S : Finset (JoinVertex P m)}
    (hS : S ∈ faceFamily P m) (hSne : S.Nonempty) :
    IsReducedAcyclicUpTo ℝ
      (inducedFaces (sdQ P m S) (goodJoinVertices P m)) (projDim P m S) := by
  have hjrank : 1 ≤ jrank P m S := by
    rcases Nat.eq_zero_or_pos (jrank P m S) with h | h
    · exact absurd (jrank_eq_zero_iff.mp h) hSne.ne_empty
    · exact h
  have hdim := finrank_direction_sdCarrier hS hSne
  have hcar := geometricCarrier_sdQ hS
  refine local_simplicial_acyclicity_of_good_count' (faceClosed_sdQ S)
    (isGeometricRealization_sdQ S) _ _ (by rw [hcar]; exact sdCarrier_nonempty hSne)
    (by rw [hcar]; exact sdCarrier_convex P m S) ?_ ?_
  · intro s hs
    obtain ⟨τ, hτ, hsτ⟩ := sdQ_purity hS hs
    refine ⟨τ, hτ.mem_sdPoset, hsτ, ?_⟩
    rw [hτ.card_eq_rank, hcar, hdim]
  · intro t ht hcard
    rw [hcar, hdim] at hcard
    rw [inter_goodJoinVertices]
    exact card_goodVertices_ge_projDim_succ hS hjrank (isApexFlag_of_card_eq hS ht hcard)

/-- **Local acyclicity in actual singular homology**: the good carrier inside a
face of the Cayley join is nonempty, has invertible degree-zero augmentation and
vanishing singular homology in the positive degrees below `projDim S`. -/
theorem local_singular_acyclicity_sdQ {S : Finset (JoinVertex P m)}
    (hS : S ∈ faceFamily P m) (hSne : S.Nonempty) :
    (geometricCarrier (inducedFaces (sdQ P m S) (goodJoinVertices P m))
        (sdPoint P m)).Nonempty ∧
      (1 ≤ projDim P m S → CategoryTheory.IsIso (realSingularAugmentation
        (TopCat.of ↥(geometricCarrier
          (inducedFaces (sdQ P m S) (goodJoinVertices P m)) (sdPoint P m))))) ∧
      ∀ k, k ≠ 0 → k + 1 ≤ projDim P m S →
        CategoryTheory.Limits.IsZero ((realSingularHomology k).obj
          (TopCat.of ↥(geometricCarrier
            (inducedFaces (sdQ P m S) (goodJoinVertices P m)) (sdPoint P m)))) := by
  have hjrank : 1 ≤ jrank P m S := by
    rcases Nat.eq_zero_or_pos (jrank P m S) with h | h
    · exact absurd (jrank_eq_zero_iff.mp h) hSne.ne_empty
    · exact h
  have hdim := finrank_direction_sdCarrier hS hSne
  have hcar := geometricCarrier_sdQ hS
  refine local_singular_acyclicity_of_good_count' (faceClosed_sdQ S)
    (isGeometricRealization_sdQ S) _ _ (by rw [hcar]; exact sdCarrier_nonempty hSne)
    (by rw [hcar]; exact sdCarrier_convex P m S) ?_ ?_
  · intro s hs
    obtain ⟨τ, hτ, hsτ⟩ := sdQ_purity hS hs
    refine ⟨τ, hτ.mem_sdPoset, hsτ, ?_⟩
    rw [hτ.card_eq_rank, hcar, hdim]
  · intro t ht hcard
    rw [hcar, hdim] at hcard
    rw [inter_goodJoinVertices]
    exact card_goodVertices_ge_projDim_succ hS hjrank (isApexFlag_of_card_eq hS ht hcard)

/-- The good subcomplex of the whole Cayley join is reduced acyclic up to the
dimension `n` of `P`. -/
theorem local_simplicial_acyclicity_topFace :
    IsReducedAcyclicUpTo ℝ
      (inducedFaces (sdQ P m (topFace P m)) (goodJoinVertices P m)) n := by
  have hne : (topFace P m).Nonempty := by
    obtain ⟨v, hv⟩ := P.actualVertices_nonempty
    obtain ⟨k, -⟩ := exists_vtx P hv
    exact ⟨((0, k) : JoinVertex P m), Finset.mem_univ _⟩
  have := local_simplicial_acyclicity_sdQ (topFace_mem_faceFamily P m) hne
  rwa [projDim_topFace] at this

end Order

/-- The same statement for the explicit linear order `joinVertexSetOrder`; it
shows that the order hypothesis of the previous results is satisfiable. -/
theorem local_simplicial_acyclicity_sdQ_explicitOrder {S : Finset (JoinVertex P m)}
    (hS : S ∈ faceFamily P m) (hSne : S.Nonempty) :
    @IsReducedAcyclicUpTo _ (joinVertexSetOrder P m) _ ℝ _
      (inducedFaces (sdQ P m S) (goodJoinVertices P m)) (projDim P m S) :=
  local_simplicial_acyclicity_sdQ (inst := joinVertexSetOrder P m) hS hSne

end BadVertex
end AffineTverberg
