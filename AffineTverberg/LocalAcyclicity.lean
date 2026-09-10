import AffineTverberg.AffineSpanRealization
import AffineTverberg.ReducedHomologyComparison

set_option linter.style.header false

/-!
# Local acyclicity from the geometric good-vertex count

The general comparison theorem completes the generic-cone argument. For a
finite triangulation of a nonempty convex face, purity and at least `m+1`
good vertices per full simplex imply actual reduced singular acyclicity
through geometric degree `m-1`. The affine dimension is that of the face,
not that of its containing coordinate space. The construction of the general
polytopal triangulation satisfying these geometric hypotheses is separate.
-/

noncomputable section

open Set CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.Simplicial

variable {V E : Type} [Fintype V] [LinearOrder V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isZero_goodSingularHomology_of_affineSpan
    {K : Finset (Finset V)} {p : V → E} (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (G : Finset V) (n : ℕ) (hn : n ≠ 0)
    (hne : (geometricCarrier K p).Nonempty) (hconv : Convex ℝ (geometricCarrier K p))
    (hbad : ∀ t ∈ inducedFaces K Gᶜ,
      t.card + (n + 1) ≤ Module.finrank ℝ (affineSpan ℝ (geometricCarrier K p)).direction) :
    IsZero ((realSingularHomology n).obj
      (TopCat.of ↥(geometricCarrier (inducedFaces K G) p))) := by
  have hiso := isIso_comparisonHomologyMap (faceClosed_inducedFaces hK G) n
  have hz := IsZero.of_epi_eq_zero (comparisonHomologyMap (faceClosed_inducedFaces hK G) n)
    (comparisonHomologyMap_good_eq_zero_of_affineSpan hK hgeom G n hn hne hconv hbad)
  exact IsZero.of_iso hz (realSingularHomologyIsoOfHomotopyEquiv
    (geometricRealizationHomeomorph (hgeom.induced G)).toHomotopyEquiv n).symm

omit [Fintype V] in
/-- The local acyclicity conclusion in actual singular homology, including
nonemptiness and the correct augmentation endpoint. -/
theorem local_singular_acyclicity_of_good_count [Finite V]
    {K : Finset (Finset V)} {p : V → E} (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (G : Finset V) (m : ℕ)
    (hne : (geometricCarrier K p).Nonempty) (hconv : Convex ℝ (geometricCarrier K p))
    (hpure : ∀ s ∈ K, ∃ t ∈ K, s ⊆ t ∧
      t.card = Module.finrank ℝ (affineSpan ℝ (geometricCarrier K p)).direction + 1)
    (hgood : ∀ t ∈ K,
      t.card = Module.finrank ℝ (affineSpan ℝ (geometricCarrier K p)).direction + 1 →
      m + 1 ≤ (t ∩ G).card) :
    (geometricCarrier (inducedFaces K G) p).Nonempty ∧
      (1 ≤ m → IsIso (realSingularAugmentation
        (TopCat.of ↥(geometricCarrier (inducedFaces K G) p)))) ∧
      ∀ n, n ≠ 0 → n + 1 ≤ m →
        IsZero ((realSingularHomology n).obj
          (TopCat.of ↥(geometricCarrier (inducedFaces K G) p))) := by
  let := Fintype.ofFinite V
  obtain ⟨hneG, haug, _⟩ :=
    local_filling_consequences_of_good_count hK hgeom G m hne hconv hpure hgood
  refine ⟨hneG, haug, fun n hn hnm ↦ ?_⟩
  apply isZero_goodSingularHomology_of_affineSpan hK hgeom G n hn hne hconv
  intro t ht
  have := card_bad_le_of_good_count hpure hgood ht
  omega

/-- The same local conclusion for the oriented augmented simplicial complex,
in precisely the grading consumed by the verified acyclic-gluing induction. -/
theorem local_simplicial_acyclicity_of_good_count
    {K : Finset (Finset V)} {p : V → E} (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (G : Finset V) (m : ℕ)
    (hne : (geometricCarrier K p).Nonempty) (hconv : Convex ℝ (geometricCarrier K p))
    (hpure : ∀ s ∈ K, ∃ t ∈ K, s ⊆ t ∧
      t.card = Module.finrank ℝ (affineSpan ℝ (geometricCarrier K p)).direction + 1)
    (hgood : ∀ t ∈ K,
      t.card = Module.finrank ℝ (affineSpan ℝ (geometricCarrier K p)).direction + 1 →
      m + 1 ≤ (t ∩ G).card) :
    IsReducedAcyclicUpTo ℝ (inducedFaces K G) m := by
  have hKg := faceClosed_inducedFaces hK G
  have hbound (t : Finset V) (ht : t ∈ inducedFaces K Gᶜ) :
      t.card + m ≤ Module.finrank ℝ (affineSpan ℝ (geometricCarrier K p)).direction :=
    card_bad_le_of_good_count hpure hgood ht
  intro k hk
  rcases k with _ | (_ | n)
  · have hneG := (local_filling_consequences_of_good_count
      hK hgeom G m hne hconv hpure hgood).1
    obtain ⟨x, hx⟩ := hneG
    let y := (geometricRealizationHomeomorph (hgeom.induced G)).symm ⟨x, hx⟩
    exact isReducedAcyclicAt_zero_of_nonempty_realization hKg ⟨y.1, y.2⟩
  · obtain ⟨q, hq, hqconv, hqfull⟩ := exists_realization_in_affineSpan hK hgeom hne hconv
    have hpc := pathConnectedSpace_geometricGood hK hq G hqconv hqfull (by
      intro t ht
      have := hbound t ht
      omega)
    have hpcb := (geometricRealizationHomeomorph (hq.induced G)).symm.pathConnectedSpace
    have hpcb' : PathConnectedSpace ↥(barySpace (inducedFaces K G)) := hpcb
    have haug : IsIso (realSingularAugmentation (barySpace (inducedFaces K G))) := by
      infer_instance
    exact isReducedAcyclicAt_one_of_isIso_singularAugmentation hKg haug
  · have hiso := isIso_comparisonHomologyMap hKg (n + 1)
    apply isReducedAcyclicAt_of_isZero_simplicialHomology hKg n
    apply IsZero.of_mono_eq_zero (comparisonHomologyMap hKg (n + 1))
    apply comparisonHomologyMap_good_eq_zero_of_affineSpan
      hK hgeom G (n + 1) (Nat.succ_ne_zero n) hne hconv
    intro t ht
    have := hbound t ht
    omega

end AffineTverberg.Simplicial
