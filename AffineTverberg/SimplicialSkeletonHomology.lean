import AffineTverberg.LocalGeometricFilling
import AffineTverberg.SimplicialToSingular
import Mathlib.Algebra.Homology.ConcreteCategory

set_option linter.style.header false

/-!
# Homology classes are represented on the corresponding skeleton

The inclusion of the `j`-skeleton induces a surjection on ordinary simplicial
homology in every degree at most `j`. This is the algebraic counterpart of
the null-homotopy of the good skeleton in `LocalGeometricFilling`: it proves
that the geometric filling covers every relevant simplicial homology class,
not merely selected cycles. A homology comparison is still required to draw
the full topological local-acyclicity conclusion.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.Simplicial

variable {V : Type} [Fintype V] [LinearOrder V]

omit [Fintype V] [LinearOrder V] in
theorem chains_skeleton_eq {K : Finset (Finset V)} {j n : ℕ} (hn : n ≤ j + 1) :
    chains ℝ (skeleton K j) n = chains ℝ K n := by
  apply le_antisymm (chains_mono (skeleton_subset _ _) n)
  intro c hc s hcs
  obtain ⟨hs, hcard⟩ := hc s hcs
  exact ⟨Finset.mem_filter.mpr ⟨hs, hcard ▸ hn⟩, hcard⟩

/-- Every ordinary simplicial homology class in degree `n ≤ j` comes from
the `j`-skeleton. The proof lifts actual cycles, using equality of the chain
groups in the relevant degrees. -/
theorem epi_homologyMap_skeleton {K : Finset (Finset V)} (hK : FaceClosed K)
    {j n : ℕ} (hn : n ≤ j) :
    Epi (HomologicalComplex.homologyMap
      (simplicialChainsInclusion (faceClosed_skeleton hK j) hK (skeleton_subset K j)) n) := by
  let C := simplicialChains (faceClosed_skeleton hK j)
  let D := simplicialChains hK
  let f : C ⟶ D :=
    simplicialChainsInclusion (faceClosed_skeleton hK j) hK (skeleton_subset K j)
  change Epi (HomologicalComplex.homologyMap f n)
  rw [ModuleCat.epi_iff_surjective]
  intro a
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (D.homologyπ n)).mp inferInstance a
  let z : C.X n := ⟨((D.iCycles n).hom c).val, by
    rw [chains_skeleton_eq (K := K) (show n + 1 ≤ j + 1 by omega)]
    exact ((D.iCycles n).hom c).property⟩
  have hz : (f.f n).hom z = (D.iCycles n).hom c := rfl
  have hfmono (q : ℕ) : Function.Injective (f.f q).hom := by
    intro x y hxy
    change (Submodule.inclusion (chains_mono (skeleton_subset K j) (q + 1)) x) =
      (Submodule.inclusion (chains_mono (skeleton_subset K j) (q + 1)) y) at hxy
    apply Subtype.ext
    exact congrArg (fun w : chains ℝ K (q + 1) ↦ w.val) hxy
  have hzcyc : (C.d n ((ComplexShape.down ℕ).next n)).hom z = 0 := by
    apply hfmono ((ComplexShape.down ℕ).next n)
    have hcomm := congrArg (fun g : C.X n ⟶ D.X ((ComplexShape.down ℕ).next n) ↦ g.hom z)
      (f.comm n ((ComplexShape.down ℕ).next n))
    have hzero := congrArg
      (fun g : D.cycles n ⟶ D.X ((ComplexShape.down ℕ).next n) ↦ g.hom c)
      (D.iCycles_d n ((ComplexShape.down ℕ).next n))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at hcomm hzero
    rw [map_zero, ← hcomm, hz, hzero]
  let c' := HomologicalComplex.cyclesMk C z ((ComplexShape.down ℕ).next n) rfl hzcyc
  have hic : (C.iCycles n).hom c' = z :=
    HomologicalComplex.i_cyclesMk C z _ rfl hzcyc
  have hcyc : (HomologicalComplex.cyclesMap f n).hom c' = c := by
    apply (ModuleCat.mono_iff_injective (D.iCycles n)).mp inferInstance
    have hnat := congrArg (fun g : C.cycles n ⟶ D.X n ↦ g.hom c')
      (HomologicalComplex.cyclesMap_i f n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
    rw [hnat, hic, hz]
  refine ⟨(C.homologyπ n).hom c', ?_⟩
  have hnat := congrArg (fun g : C.cycles n ⟶ D.homology n ↦ g.hom c')
    (HomologicalComplex.homologyπ_naturality f n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  rw [hnat, hcyc]

section GeometricFilling

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

set_option backward.isDefEq.respectTransparency false in
/-- Passing through the geometric realization homeomorphism transfers the
zero homology map of the good-skeleton inclusion to barycentric coordinates. -/
theorem singularHomology_baryGoodSkeleton_map_zero
    {K : Finset (Finset V)} {p : V → E} (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (G : Finset V) (j : ℕ)
    (hconv : Convex ℝ (geometricCarrier K p))
    (hfull : affineSpan ℝ (geometricCarrier K p) = ⊤)
    (hbad : ∀ t ∈ inducedFaces K Gᶜ, t.card + (j + 1) ≤ Module.finrank ℝ E)
    (n : ℕ) (hn : n ≠ 0) :
    (realSingularHomology n).map (baryInclusion (skeleton_subset (inducedFaces K G) j)) = 0 := by
  let g := TopCat.ofHom (geometricRealizationMap (inducedFaces K G) p)
  let e := realSingularHomologyIsoOfHomotopyEquiv
    (geometricRealizationHomeomorph (hgeom.induced G)).toHomotopyEquiv n
  have hg : e.hom = (realSingularHomology n).map g := rfl
  have : IsIso ((realSingularHomology n).map g) := by rw [← hg]; infer_instance
  have hnat : baryInclusion (skeleton_subset (inducedFaces K G) j) ≫ g =
      TopCat.ofHom (geometricRealizationMap (skeleton (inducedFaces K G) j) p) ≫
        TopCat.ofHom (ContinuousMap.inclusion (geometricCarrier_mono (p := p)
          (skeleton_subset (inducedFaces K G) j))) := rfl
  apply (cancel_mono ((realSingularHomology n).map g)).mp
  rw [zero_comp, ← Functor.map_comp, hnat, Functor.map_comp,
    singularHomology_goodSkeleton_map_zero hK hgeom G j hconv hfull hbad n hn, comp_zero]

/-- Every positive-degree simplicial homology class of the good induced
subcomplex maps to zero in its actual singular homology under the local
dimension bound. No isomorphism property of the comparison map is assumed;
once the general comparison is proved, this gives full local acyclicity. -/
theorem comparisonHomologyMap_good_eq_zero
    {K : Finset (Finset V)} {p : V → E} (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (G : Finset V) (n : ℕ) (hn : n ≠ 0)
    (hconv : Convex ℝ (geometricCarrier K p))
    (hfull : affineSpan ℝ (geometricCarrier K p) = ⊤)
    (hbad : ∀ t ∈ inducedFaces K Gᶜ, t.card + (n + 1) ≤ Module.finrank ℝ E) :
    comparisonHomologyMap (faceClosed_inducedFaces hK G) n = 0 := by
  let hG := faceClosed_inducedFaces hK G
  let hS := faceClosed_skeleton hG n
  let hSG := skeleton_subset (inducedFaces K G) n
  have := epi_homologyMap_skeleton hG (Nat.le_refl n)
  apply (cancel_epi (HomologicalComplex.homologyMap (simplicialChainsInclusion hS hG hSG) n)).mp
  rw [comp_zero]
  change HomologicalComplex.homologyMap (simplicialChainsInclusion hS hG hSG) n ≫
    HomologicalComplex.homologyMap (comparisonChainMap hG) n = 0
  rw [← comparisonHomologyMap_naturality hS hG hSG n]
  change comparisonHomologyMap hS n ≫ (realSingularHomology n).map (baryInclusion hSG) = 0
  rw [singularHomology_baryGoodSkeleton_map_zero hK hgeom G n hconv hfull hbad n hn, comp_zero]

end GeometricFilling

end AffineTverberg.Simplicial
