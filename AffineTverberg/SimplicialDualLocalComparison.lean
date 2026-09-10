import AffineTverberg.RecursiveDualChains
import AffineTverberg.DualBlockRelativeRank

set_option linter.style.header false

/-!
# The explicit dual chains generate the local simplicial homology

The recursive chains, already proved to have the correct incidence formula,
generate the actual relative simplicial homology of every dual block. The
rank calculation reuses the established local homology of a triangulated
topological sphere; no PL or combinatorial-manifold hypothesis is added.

The remaining global step is the finite-filtration comparison. This file
does not assert that the global dualization already induces an isomorphism.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric

namespace AffineTverberg.Simplicial

open AffineTverberg.AffChain

variable {V : Type} [Fintype V] [LinearOrder V] [inst : LinearOrder (Finset V)]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {K : Finset (Finset V)} {p : V → E} {s : Finset V} {N : ℕ}

local instance simplicialDualLocalDecidableEq : DecidableEq (Finset V) := inst.toDecidableEq

/-- The local simplicial relative group is a line in its complementary
degree, including degree zero. -/
theorem finrank_dualBlockCofaceHomology_of_sphere
    (hgeom : IsGeometricRealization K p) (hK : FaceClosed K)
    (hsK : s ∈ K) (hs : s.Nonempty)
    (hdim : Module.finrank ℝ F = N + 1) (hN : 2 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : F) 1)
    (htop : ∀ t ∈ K, t.card ≤ N + 1) (q : ℕ) (hq : q + s.card = N + 1) :
    Module.finrank ℝ ((cofaceComplex (faceClosed_dualBlockFaces K s) {s}).homology q) = 1 := by
  have hBg : IsGeometricRealization (dualBlockFaces K s) (faceBarycenter p) := by
    have h := @IsGeometricRealization.mono (Finset V) (fun a b => a.decidableEq b)
      E _ _ _ _ _ (isGeometricRealization_subdivisionFaces hgeom) (dualBlockFaces_subset K s)
    convert h using 1
  have hiso := geometricCofaceHomologyIso (faceClosed_dualBlockFaces K s) hBg {s} q
  have hfin := hiso.toLinearEquiv.finrank_eq
  change Module.finrank ℝ ((cofaceComplex (faceClosed_dualBlockFaces K s) {s}).homology q) =
    Module.finrank ℝ (relativeHomology
      (X := TopCat.of ↥(geometricCarrier (dualBlockFaces K s) (faceBarycenter p)))
      (Subtype.val ⁻¹' geometricCarrier (costarFamily (dualBlockFaces K s) {s})
        (faceBarycenter p)) q) at hfin
  rw [costar_dualBlock_apex] at hfin
  exact hfin.trans
    (finrank_dualBlockRelativeHomology_of_sphere hgeom hK hsK hs hdim hN e htop q hq)

/-- The explicit recursively constructed class, not an independently chosen
orientation, generates the entire local simplicial relative group. -/
theorem span_recursiveDualRelativeClass_of_sphere
    (hgeom : IsGeometricRealization K p) (hK : FaceClosed K)
    (hsK : s ∈ K) (hs : s.Nonempty)
    (hdim : Module.finrank ℝ F = N + 1) (hN : 2 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : F) 1)
    (htop : ∀ t ∈ K, t.card ≤ N + 1)
    {c : Finset V → ℝ} (hc : c ∈ cycles ℝ K (N + 1))
    (hfull : ∀ t ∈ K, t.card = N + 1 → c t ≠ 0)
    (q : ℕ) (hq : q + s.card = N + 1) :
    Submodule.span ℝ {recursiveDualRelativeClass hK hc q hs} = ⊤ := by
  obtain ⟨t, htK, hst, htcard⟩ := exists_top_coface_of_sphere hK hsK hs hdim hN e hq
  have hne := recursiveDualRelativeClass_ne_zero hK hc htop q hs hst (hfull t htK htcard) hq
  exact (finrank_eq_one_iff_of_nonzero _ hne).mp
    (finrank_dualBlockCofaceHomology_of_sphere hgeom hK hsK hs hdim hN e htop q hq)

end AffineTverberg.Simplicial
