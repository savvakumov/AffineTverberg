import AffineTverberg.SingularMayerVietoris
import AffineTverberg.SingularHomology

set_option linter.style.header false

/-!
# A rank bound from the Mayer-Vietoris sequence

If two opens `A`, `B` cover a space whose singular homology vanishes in degree
`n`, then the actual Mayer-Vietoris sequence forces the map
`Hₙ(A ∩ B) → Hₙ(A)` induced by the inclusion to be surjective.  In particular
the rank of `Hₙ(A)` is at most the rank of `Hₙ(A ∩ B)`.

This is the form of Mayer-Vietoris used to bound the local homology of a point
of a ball: `A` is the punctured space, `B` a small neighbourhood of the point,
and `A ∩ B` a punctured neighbourhood.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.AffChain

variable {X : TopCat.{0}}

/-- **Mayer-Vietoris surjectivity.**  If the ambient homology vanishes in
degree `n`, the inclusion `A ∩ B ⊆ A` is surjective on `Hₙ`. -/
theorem epi_homologyMap_subInclMap_inter_left (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcov : ∀ x, x ∈ A ∨ x ∈ B) (n : ℕ)
    (hX : IsZero ((realSingularHomology n).obj X)) :
    Epi ((realSingularHomology n).map
      (subInclMap (Set.inter_subset_left (s := A) (t := B)))) := by
  have hbeta : mvBeta A B n = 0 := hX.eq_zero_of_tgt _
  have hexact := mv_exact_pair A B hA hB hcov n
  have hepia : Epi (mvAlpha A B n) :=
    (ShortComplex.exact_iff_epi
      (ShortComplex.mk (mvAlpha A B n) (mvBeta A B n) (mvAlpha_comp_mvBeta A B n)) hbeta).mp hexact
  -- the first projection of the direct sum is a split epimorphism
  have hfst : HomologicalComplex.homologyMap
      (pairInl (singChains (subSpace A)) (singChains (subSpace B))) n ≫
      HomologicalComplex.homologyMap
        (pairFst (singChains (subSpace A)) (singChains (subSpace B))) n = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp]
    have h : pairInl (singChains (subSpace A)) (singChains (subSpace B)) ≫
        pairFst (singChains (subSpace A)) (singChains (subSpace B)) = 𝟙 _ :=
      (pairBicone (singChains (subSpace A)) (singChains (subSpace B))).inl_fst
    rw [h, HomologicalComplex.homologyMap_id]
  have hepifst : Epi (HomologicalComplex.homologyMap
      (pairFst (singChains (subSpace A)) (singChains (subSpace B))) n) :=
    @IsSplitEpi.epi _ _ _ _ _ ⟨⟨SplitEpi.mk _ hfst⟩⟩
  have hcomp : Epi (mvAlpha A B n ≫ HomologicalComplex.homologyMap
      (pairFst (singChains (subSpace A)) (singChains (subSpace B))) n) := epi_comp _ _
  have heq : mvAlpha A B n ≫ HomologicalComplex.homologyMap
      (pairFst (singChains (subSpace A)) (singChains (subSpace B))) n =
      (realSingularHomology n).map
        (subInclMap (Set.inter_subset_left (s := A) (t := B))) := by
    rw [mvAlpha_eq, ← HomologicalComplex.homologyMap_comp]
    rfl
  rwa [heq] at hcomp

/-- The same statement as surjectivity of the actual map of homology modules. -/
theorem surjective_homology_inter_left (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcov : ∀ x, x ∈ A ∨ x ∈ B) (n : ℕ)
    (hX : IsZero ((realSingularHomology n).obj X)) :
    Function.Surjective ((realSingularHomology n).map
      (subInclMap (Set.inter_subset_left (s := A) (t := B)))) :=
  (ModuleCat.epi_iff_surjective _).1 (epi_homologyMap_subInclMap_inter_left A B hA hB hcov n hX)

/-- If the homology of `A ∩ B` in degree `n` is finite dimensional, so is that
of `A`. -/
theorem finiteDimensional_homology_of_cover (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcov : ∀ x, x ∈ A ∨ x ∈ B) (n : ℕ)
    (hX : IsZero ((realSingularHomology n).obj X))
    [FiniteDimensional ℝ ((realSingularHomology n).obj (subSpace (A ∩ B)))] :
    FiniteDimensional ℝ ((realSingularHomology n).obj (subSpace A)) :=
  Module.Finite.of_surjective
    ((realSingularHomology n).map
      (subInclMap (Set.inter_subset_left (s := A) (t := B)))).hom
    (surjective_homology_inter_left A B hA hB hcov n hX)

/-- **Mayer-Vietoris injectivity.**  If the ambient homology vanishes one
degree higher, the inclusion `A ∩ B ⊆ A` is injective on `Hₙ` as soon as the
homology of `B` vanishes in degree `n`. -/
theorem injective_homology_inter_left (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcov : ∀ x, x ∈ A ∨ x ∈ B) (n : ℕ)
    (hX : IsZero ((realSingularHomology (n + 1)).obj X))
    (hBzero : IsZero ((realSingularHomology n).obj (subSpace B))) :
    Function.Injective ((realSingularHomology n).map
      (subInclMap (Set.inter_subset_left (s := A) (t := B)))) := by
  -- the connecting map vanishes, so `mvAlpha` is a monomorphism
  have hdelta : mvDelta A B hA hB hcov n = 0 := hX.eq_zero_of_src _
  have hexact := mv_exact_inter A B hA hB hcov n
  have hmono : Mono (mvAlpha A B n) :=
    (ShortComplex.exact_iff_mono
      (ShortComplex.mk (mvDelta A B hA hB hcov n) (mvAlpha A B n)
        (mvDelta_comp_mvAlpha A B hA hB hcov n)) hdelta).mp hexact
  -- the first projection of the direct sum is an isomorphism, since `Hₙ(B) = 0`
  set C := singChains (subSpace A) with hC
  set D := singChains (subSpace B) with hD
  have hsnd0 : HomologicalComplex.homologyMap (pairSnd C D) n = 0 :=
    hBzero.eq_zero_of_tgt _
  have hsnd : HomologicalComplex.homologyMap (pairSnd C D) n ≫
      HomologicalComplex.homologyMap (pairInr C D) n = 0 := by
    rw [hsnd0, zero_comp]
  have htotal : HomologicalComplex.homologyMap (pairFst C D) n ≫
      HomologicalComplex.homologyMap (pairInl C D) n = 𝟙 _ := by
    have h := congrArg
      (fun φ => (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℝ)
        (ComplexShape.down ℕ) n).map φ) (pairBicone_total C D)
    simp only [Functor.map_add, Functor.map_comp] at h
    rw [(HomologicalComplex.homologyFunctor (ModuleCat.{0} ℝ)
      (ComplexShape.down ℕ) n).map_id] at h
    change HomologicalComplex.homologyMap (pairFst C D) n ≫
      HomologicalComplex.homologyMap (pairInl C D) n +
      HomologicalComplex.homologyMap (pairSnd C D) n ≫
      HomologicalComplex.homologyMap (pairInr C D) n = 𝟙 _ at h
    rw [hsnd, add_zero] at h
    exact h
  have hfstmono : Mono (HomologicalComplex.homologyMap (pairFst C D) n) :=
    @IsSplitMono.mono _ _ _ _ _ ⟨⟨SplitMono.mk _ htotal⟩⟩
  have hcomp : Mono (mvAlpha A B n ≫ HomologicalComplex.homologyMap (pairFst C D) n) :=
    mono_comp _ _
  have heq : mvAlpha A B n ≫ HomologicalComplex.homologyMap (pairFst C D) n =
      (realSingularHomology n).map
        (subInclMap (Set.inter_subset_left (s := A) (t := B))) := by
    rw [mvAlpha_eq, ← HomologicalComplex.homologyMap_comp]
    rfl
  rw [heq] at hcomp
  exact (ModuleCat.mono_iff_injective _).1 hcomp

/-- The corresponding rank bound in the other direction. -/
theorem finrank_homology_inter_le_of_cover (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcov : ∀ x, x ∈ A ∨ x ∈ B) (n : ℕ)
    (hX : IsZero ((realSingularHomology (n + 1)).obj X))
    (hBzero : IsZero ((realSingularHomology n).obj (subSpace B)))
    [FiniteDimensional ℝ ((realSingularHomology n).obj (subSpace A))] :
    Module.finrank ℝ ((realSingularHomology n).obj (subSpace (A ∩ B))) ≤
      Module.finrank ℝ ((realSingularHomology n).obj (subSpace A)) :=
  LinearMap.finrank_le_finrank_of_injective
    (injective_homology_inter_left A B hA hB hcov n hX hBzero)

/-- **The Mayer-Vietoris rank bound.** -/
theorem finrank_homology_le_of_cover (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcov : ∀ x, x ∈ A ∨ x ∈ B) (n : ℕ)
    (hX : IsZero ((realSingularHomology n).obj X))
    [FiniteDimensional ℝ ((realSingularHomology n).obj (subSpace (A ∩ B)))] :
    Module.finrank ℝ ((realSingularHomology n).obj (subSpace A)) ≤
      Module.finrank ℝ ((realSingularHomology n).obj (subSpace (A ∩ B))) := by
  have hsurj := surjective_homology_inter_left A B hA hB hcov n hX
  have hle := LinearMap.finrank_range_le
    ((realSingularHomology n).map
      (subInclMap (Set.inter_subset_left (s := A) (t := B)))).hom
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hle
  exact hle

end AffineTverberg.AffChain
