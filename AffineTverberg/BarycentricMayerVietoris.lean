import AffineTverberg.BarycentricThickening
import AffineTverberg.SingularMayerVietoris

set_option linter.style.header false

/-!
# The Mayer-Vietoris cover of a realization along a maximal face

For a nonempty maximal face `s` of a finite family `K`, the punctured
realization (`punctured K s`, the realization minus the barycenter of `s`) and
the open star of `s` form an honest *open* cover of the barycentric
realization. This file feeds that verified cover into the singular
Mayer-Vietoris long exact sequence of `AffineTverberg.SingularMayerVietoris`.

All three pieces are understood: the punctured realization deformation retracts
onto the realization of `K.erase s` (`puncturedHomotopyEquiv`), the open star is
contractible (`contractibleSpace_openStar`), and the intersection deformation
retracts onto the realization of the boundary of `s` (`linkHomotopyEquiv`). The
resulting identifications of the homology terms, and their compatibility with
the inclusions, are in `AffineTverberg.BarycentricMayerVietorisTerms`.
-/

noncomputable section

open CategoryTheory AffineTverberg.AffChain

namespace AffineTverberg.Simplicial

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The barycentric realization of `K` as an object of `TopCat`. -/
abbrev realSpace (K : Finset (Finset V)) : TopCat.{0} := TopCat.of ↥(barycentricCarrier K)

theorem mem_punctured_or_openStar (K : Finset (Finset V)) (s : Finset V)
    (x : ↥(barycentricCarrier K)) : x ∈ punctured K s ∨ x ∈ openStar K s := by
  have hx : x ∈ punctured K s ∪ openStar K s := by
    rw [punctured_union_openStar K s]; trivial
  exact hx

variable (K : Finset (Finset V)) (s : Finset V)

/-- The Mayer-Vietoris connecting homomorphism of the cover of the realization
of `K` by the punctured realization and the open star of `s`. -/
def faceMvDelta (n : ℕ) :
    (singChains (realSpace K)).homology (n + 1) ⟶
      (singChains (subSpace (X := realSpace K) (punctured K s ∩ openStar K s))).homology n :=
  mvDelta (X := realSpace K) (punctured K s) (openStar K s) (isOpen_punctured K s)
    (isOpen_openStar K s) (mem_punctured_or_openStar K s) n

/-- **Exactness of the Mayer-Vietoris sequence of this cover at the homology of
the realization.** -/
theorem faceMv_exact_space (n : ℕ) :
    (ShortComplex.mk
      (mvBeta (X := realSpace K) (punctured K s) (openStar K s) (n + 1))
      (faceMvDelta K s n)
      (mvBeta_comp_mvDelta (X := realSpace K) (punctured K s) (openStar K s)
        (isOpen_punctured K s) (isOpen_openStar K s) (mem_punctured_or_openStar K s) n)).Exact :=
  mv_exact_space (X := realSpace K) (punctured K s) (openStar K s) (isOpen_punctured K s)
    (isOpen_openStar K s) (mem_punctured_or_openStar K s) n

/-- **Exactness of the Mayer-Vietoris sequence of this cover at the direct sum
of the homologies of the two pieces.** -/
theorem faceMv_exact_pair (n : ℕ) :
    (ShortComplex.mk
      (mvAlpha (X := realSpace K) (punctured K s) (openStar K s) n)
      (mvBeta (X := realSpace K) (punctured K s) (openStar K s) n)
      (mvAlpha_comp_mvBeta (X := realSpace K) (punctured K s) (openStar K s) n)).Exact :=
  mv_exact_pair (X := realSpace K) (punctured K s) (openStar K s) (isOpen_punctured K s)
    (isOpen_openStar K s) (mem_punctured_or_openStar K s) n

/-- **Exactness of the Mayer-Vietoris sequence of this cover at the homology of
the intersection.** -/
theorem faceMv_exact_inter (n : ℕ) :
    (ShortComplex.mk
      (faceMvDelta K s n)
      (mvAlpha (X := realSpace K) (punctured K s) (openStar K s) n)
      (mvDelta_comp_mvAlpha (X := realSpace K) (punctured K s) (openStar K s)
        (isOpen_punctured K s) (isOpen_openStar K s) (mem_punctured_or_openStar K s) n)).Exact :=
  mv_exact_inter (X := realSpace K) (punctured K s) (openStar K s) (isOpen_punctured K s)
    (isOpen_openStar K s) (mem_punctured_or_openStar K s) n

end AffineTverberg.Simplicial
