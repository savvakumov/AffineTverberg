import AffineTverberg.SingularMayerVietoris
import AffineTverberg.SingularHomology

set_option linter.style.header false

/-!
# Relative singular homology of a pair and its long exact sequence

For a subset `A` of a space `X` the chain map `chainsInclusion A` induced by
the inclusion of subspaces is degreewise injective
(`AffChain.chainsInclusion_injective`), so

`0 ⟶ C(A) ⟶ C(X) ⟶ C(X, A) ⟶ 0`

is a short exact sequence of chain complexes, where the relative complex
`C(X, A)` is the actual cokernel in the abelian category of chain complexes of
real vector spaces. Mathlib's homology sequence of a short exact sequence of
homological complexes then supplies the connecting morphism and exactness at
all three spots. Nothing else is assumed: no excision, no duality and no
comparison statement.

The two consequences used downstream are the vanishing transfers

* `isZero_homology_sub_of_isZero_relative` : if `Hₖ₊₁(X, A) = 0` and
  `Hₖ(X) = 0` then `Hₖ(A) = 0`;
* `isZero_relativeHomology` : if `Hₖ₊₁(X) = 0` and `Hₖ(A) = 0` then
  `Hₖ₊₁(X, A) = 0`.
-/

noncomputable section

open CategoryTheory Limits

namespace AffineTverberg

namespace AffChain

variable {X : TopCat.{0}}

/-! ### The relative chain complex -/

/-- The relative singular chain complex of the pair `(X, A)`: the cokernel of
the degreewise injective chain map induced by the inclusion `A ↪ X`. -/
def relCx (A : Set X) : ChainComplex (ModuleCat.{0} ℝ) ℕ := cokernel (chainsInclusion A)

/-- The projection of absolute chains to relative chains. -/
def relProj (A : Set X) : singChains X ⟶ relCx A := cokernel.π (chainsInclusion A)

/-- The short complex `C(A) ⟶ C(X) ⟶ C(X, A)`. -/
def relShortComplex (A : Set X) : ShortComplex (ChainComplex (ModuleCat.{0} ℝ) ℕ) :=
  ShortComplex.mk (chainsInclusion A) (relProj A) (cokernel.condition _)

theorem mono_chainsInclusion (A : Set X) : Mono (chainsInclusion A) :=
  HomologicalComplex.mono_of_mono_f _ fun n ↦
    (ModuleCat.mono_iff_injective _).mpr (chainsInclusion_injective A n)

/-- **The short exact sequence of the pair.** -/
theorem relShortExact (A : Set X) : (relShortComplex A).ShortExact where
  exact := ShortComplex.exact_cokernel (chainsInclusion A)
  mono_f := mono_chainsInclusion A
  epi_g := coequalizer.π_epi

/-! ### Relative homology and the connecting morphism -/

/-- The relative singular homology of the pair `(X, A)` with real coefficients. -/
abbrev relativeHomology (A : Set X) (n : ℕ) : ModuleCat.{0} ℝ := (relCx A).homology n

/-- The connecting morphism `Hₙ₊₁(X, A) ⟶ Hₙ(A)` of the pair. -/
def relDelta (A : Set X) (n : ℕ) :
    relativeHomology A (n + 1) ⟶ (singChains (subSpace A)).homology n :=
  (relShortExact A).δ (n + 1) n (by simp)

/-- The map `Hₙ(A) ⟶ Hₙ(X)` induced by the inclusion. -/
def relIota (A : Set X) (n : ℕ) :
    (singChains (subSpace A)).homology n ⟶ (singChains X).homology n :=
  HomologicalComplex.homologyMap (chainsInclusion A) n

/-- The map `Hₙ(X) ⟶ Hₙ(X, A)` induced by the projection to relative chains. -/
def relPi (A : Set X) (n : ℕ) :
    (singChains X).homology n ⟶ relativeHomology A n :=
  HomologicalComplex.homologyMap (relProj A) n

theorem relDelta_comp_relIota (A : Set X) (n : ℕ) :
    relDelta A n ≫ relIota A n = 0 :=
  (relShortExact A).δ_comp (n + 1) n (by simp)

theorem relIota_comp_relPi (A : Set X) (n : ℕ) :
    relIota A n ≫ relPi A n = 0 := by
  rw [relIota, relPi, ← HomologicalComplex.homologyMap_comp]
  have h : chainsInclusion A ≫ relProj A = 0 := (relShortComplex A).zero
  rw [h, HomologicalComplex.homologyMap_zero]

theorem relPi_comp_relDelta (A : Set X) (n : ℕ) :
    relPi A (n + 1) ≫ relDelta A n = 0 :=
  (relShortExact A).comp_δ (n + 1) n (by simp)

/-- **Exactness at `Hₙ(A)`.** -/
theorem relExact_sub (A : Set X) (n : ℕ) :
    (ShortComplex.mk (relDelta A n) (relIota A n) (relDelta_comp_relIota A n)).Exact :=
  (relShortExact A).homology_exact₁ (n + 1) n (by simp)

/-- **Exactness at `Hₙ(X)`.** -/
theorem relExact_space (A : Set X) (n : ℕ) :
    (ShortComplex.mk (relIota A n) (relPi A n) (relIota_comp_relPi A n)).Exact :=
  (relShortExact A).homology_exact₂ n

/-- **Exactness at `Hₙ₊₁(X, A)`.** -/
theorem relExact_relative (A : Set X) (n : ℕ) :
    (ShortComplex.mk (relPi A (n + 1)) (relDelta A n) (relPi_comp_relDelta A n)).Exact :=
  (relShortExact A).homology_exact₃ (n + 1) n (by simp)

/-! ### The two vanishing transfers -/

/-- If the relative homology in degree `k + 1` and the homology of the ambient
space in degree `k` both vanish, then so does the homology of the subspace in
degree `k`. -/
theorem isZero_homology_sub_of_isZero_relative (A : Set X) (k : ℕ)
    (hrel : IsZero (relativeHomology A (k + 1)))
    (hX : IsZero ((singChains X).homology k)) :
    IsZero ((singChains (subSpace A)).homology k) := by
  have hex := relExact_sub A k
  have hf : (ShortComplex.mk (relDelta A k) (relIota A k) (relDelta_comp_relIota A k)).f = 0 :=
    hrel.eq_of_src _ _
  have hmono : Mono (relIota A k) := (ShortComplex.exact_iff_mono _ hf).mp hex
  exact IsZero.of_mono (relIota A k) hX

/-- If the ambient homology in degree `k + 1` and the homology of the subspace
in degree `k` both vanish, then the relative homology vanishes in degree
`k + 1`. -/
theorem isZero_relativeHomology (A : Set X) (k : ℕ)
    (hX : IsZero ((singChains X).homology (k + 1)))
    (hA : IsZero ((singChains (subSpace A)).homology k)) :
    IsZero (relativeHomology A (k + 1)) := by
  have hex := relExact_relative A k
  have hg : (ShortComplex.mk (relPi A (k + 1)) (relDelta A k) (relPi_comp_relDelta A k)).g = 0 :=
    hA.eq_of_tgt _ _
  have hepi : Epi (relPi A (k + 1)) := (ShortComplex.exact_iff_epi _ hg).mp hex
  exact IsZero.of_epi (relPi A (k + 1)) hX

/-! ### Compatibility with the singular homology functor -/

theorem realSingularHomology_subSpace (A : Set X) (n : ℕ) :
    (realSingularHomology n).obj (TopCat.of ↥A) = (singChains (subSpace A)).homology n := rfl

theorem realSingularHomology_space (n : ℕ) :
    (realSingularHomology n).obj X = (singChains X).homology n := rfl

end AffChain

end AffineTverberg
