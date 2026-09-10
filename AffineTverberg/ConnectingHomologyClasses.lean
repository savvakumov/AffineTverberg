import AffineTverberg.HomologyClassCalculus
import AffineTverberg.RelativeHomologyMaps

set_option linter.style.header false

/-!
# Actual connecting maps on explicit cycle representatives

Mathlib's connecting homomorphism is computed by lifting a quotient cycle
and taking its boundary in the subcomplex. We expose that existing theorem
in the homClass API used throughout this development, including degree zero
on the receiving side. The relative specialization uses the genuine singular
pair sequence and its cokernel projection.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace AffineTverberg.AffChain

variable {S : ShortComplex (ChainComplex (ModuleCat.{0} ℝ) ℕ)}

/-- A lifted boundary in the first complex is automatically an actual cycle. -/
theorem isCycleAt_of_lifted_boundary (hS : S.ShortExact) (k : ℕ)
    (b : S.X₂.X (k + 1)) (a : S.X₁.X k)
    (ha : (S.f.f k).hom a = (S.X₂.d (k + 1) k).hom b) :
    IsCycleAt S.X₁ k a := by
  intro j
  exact hS.d_eq_zero_of_f_eq_d_apply (k + 1) k b a ha j

/-- The genuine connecting homomorphism takes a quotient cycle to the
class of the boundary of its chosen lift. No independent boundary map is
introduced here: this is Mathlib's connecting morphism itself. -/
theorem homologySequence_delta_homClass (hS : S.ShortExact) (k : ℕ)
    (z : S.X₃.X (k + 1)) (hz : IsCycleAt S.X₃ (k + 1) z)
    (b : S.X₂.X (k + 1)) (hb : (S.g.f (k + 1)).hom b = z)
    (a : S.X₁.X k) (ha : (S.f.f k).hom a = (S.X₂.d (k + 1) k).hom b)
    (hacycle : IsCycleAt S.X₁ k a) :
    (hS.δ (k + 1) k (by simp)).hom (homClass z hz) = homClass a hacycle := by
  exact hS.δ_apply (k + 1) k (by simp) z (hz k) b hb a ha
    ((ComplexShape.down ℕ).next k) rfl

/-- In a short complex, a chain whose boundary lies in the first
complex projects to a cycle in the quotient complex. -/
theorem isCycleAt_projection_of_lifted_boundary
    (S : ShortComplex (ChainComplex (ModuleCat.{0} ℝ) ℕ)) (k : ℕ)
    (b : S.X₂.X (k + 1)) (a : S.X₁.X k)
    (ha : (S.f.f k).hom a = (S.X₂.d (k + 1) k).hom b) :
    IsCycleAt S.X₃ (k + 1) ((S.g.f (k + 1)).hom b) := by
  apply isCycleAt_succ
  have hcomm := congrArg (fun f : S.X₂.X (k + 1) ⟶ S.X₃.X k => f.hom b) (S.g.comm (k + 1) k)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
  rw [hcomm, ← ha]
  have hzero := congrArg (fun f : S.X₁ ⟶ S.X₃ => f.f k) S.zero
  have hval := congrArg (fun f : S.X₁.X k ⟶ S.X₃.X k => f.hom a) hzero
  exact hval

variable {X : TopCat.{0}}

/-- An absolute singular chain whose boundary is in A defines a genuine
relative cycle in the cokernel complex C(X,A). -/
theorem relative_isCycleAt_of_lifted_boundary (A : Set X) (k : ℕ)
    (b : (singChains X).X (k + 1)) (a : (singChains (subSpace A)).X k)
    (ha : ((chainsInclusion A).f k).hom a = ((singChains X).d (k + 1) k).hom b) :
    IsCycleAt (relCx A) (k + 1) (((relProj A).f (k + 1)).hom b) :=
  isCycleAt_projection_of_lifted_boundary (relShortComplex A) k b a ha

/-- The actual singular connecting map is computed by that lifted boundary,
also when the receiving group is H0(A). -/
theorem relDelta_homClass_of_lifted_boundary (A : Set X) (k : ℕ)
    (b : (singChains X).X (k + 1)) (a : (singChains (subSpace A)).X k)
    (ha : ((chainsInclusion A).f k).hom a = ((singChains X).d (k + 1) k).hom b) :
    (relDelta A k).hom
      (homClass (((relProj A).f (k + 1)).hom b)
        (relative_isCycleAt_of_lifted_boundary A k b a ha)) =
      homClass a (isCycleAt_of_lifted_boundary (relShortExact A) k b a ha) :=
  homologySequence_delta_homClass (relShortExact A) k _
    (relative_isCycleAt_of_lifted_boundary A k b a ha) b rfl a ha _

end AffineTverberg.AffChain
