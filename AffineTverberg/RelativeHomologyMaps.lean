import AffineTverberg.RelativeSingularHomology
import AffineTverberg.ComparisonSubspace

set_option linter.style.header false

/-!
# Maps of relative singular chains

Continuous maps of pairs induce maps of the actual cokernel complexes. These
maps commute with projection and with the connecting homomorphism, and are
quasi-isomorphisms whenever the ambient and restricted maps are. In particular,
homeomorphisms of pairs induce isomorphisms of actual relative homology.
This extends the existing real-coefficient complex without replacing it.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.AffChain

variable {X Y Z : TopCat.{0}} {A : Set X} {B : Set Y} {C : Set Z}

/-- The map of genuine relative chain complexes induced by a map of pairs. -/
def relativeMap (f : X ⟶ Y) (h : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B) :
    relCx A ⟶ relCx B :=
  cokernel.map (chainsInclusion A) (chainsInclusion B)
    (singChainsMap (restrictMap f h)) (singChainsMap f)
    (chainsInclusion_naturality f h).symm

theorem relativeMap_proj (f : X ⟶ Y)
    (h : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B) :
    relProj A ≫ relativeMap f h = singChainsMap f ≫ relProj B :=
  cokernel.π_desc _ _ _

/-- The induced morphism of the short exact sequences of pairs. -/
def relativeShortComplexMap (f : X ⟶ Y)
    (h : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B) :
    relShortComplex A ⟶ relShortComplex B where
  τ₁ := singChainsMap (restrictMap f h)
  τ₂ := singChainsMap f
  τ₃ := relativeMap f h
  comm₁₂ := chainsInclusion_naturality f h
  comm₂₃ := (relativeMap_proj f h).symm

theorem relativeMap_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B)
    (hg : ∀ y ∈ B, (ConcreteCategory.hom g) y ∈ C) :
    relativeMap (f ≫ g) (fun x hx => hg _ (hf x hx)) =
      relativeMap f hf ≫ relativeMap g hg := by
  apply (cancel_epi (cokernel.π (chainsInclusion A))).mp
  change relProj A ≫ _ = relProj A ≫ _
  rw [relativeMap_proj, singChainsMap_comp]
  simp only [← Category.assoc, relativeMap_proj f hf]
  rw [Category.assoc, Category.assoc, relativeMap_proj g hg]

theorem relativeMap_id (A : Set X) :
    relativeMap (𝟙 X) (fun _ hx => hx : ∀ x ∈ A, (ConcreteCategory.hom (𝟙 X)) x ∈ A) =
      𝟙 (relCx A) := by
  apply (cancel_epi (cokernel.π (chainsInclusion A))).mp
  change relProj A ≫ _ = relProj A ≫ _
  have hid : singChainsMap (𝟙 X) = 𝟙 (singChains X) :=
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℝ)).obj
      (ModuleCat.of ℝ ℝ)).map_id X
  exact (relativeMap_proj (𝟙 X) (fun _ hx => hx)).trans (by
    rw [hid, Category.id_comp, Category.comp_id])

/-- Naturality of the actual connecting homomorphism. -/
theorem relativeMap_delta_naturality (f : X ⟶ Y)
    (h : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B) (k : ℕ) :
    relDelta A k ≫ HomologicalComplex.homologyMap (singChainsMap (restrictMap f h)) k =
      HomologicalComplex.homologyMap (relativeMap f h) (k + 1) ≫ relDelta B k :=
  HomologicalComplex.HomologySequence.δ_naturality (relativeShortComplexMap f h)
    (relShortExact A) (relShortExact B) (k + 1) k (by simp)

/-- The relative comparison follows from the two absolute comparisons. -/
theorem quasiIso_relativeMap (f : X ⟶ Y)
    (h : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B)
    (hsub : QuasiIso (singChainsMap (restrictMap f h)))
    (hspace : QuasiIso (singChainsMap f)) : QuasiIso (relativeMap f h) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (relativeShortComplexMap f h)
    (relShortExact A) (relShortExact B) hsub hspace

/-- A homeomorphism of pairs gives a quasi-isomorphism of the relative complexes. -/
theorem quasiIso_relativeMap_of_homeomorph (e : X ≃ₜ Y)
    (h : ∀ x, x ∈ A ↔ e x ∈ B) :
    QuasiIso (relativeMap (TopCat.ofHom (e : C(X, Y))) (fun x hx => (h x).mp hx)) := by
  apply quasiIso_relativeMap
  · exact Simplicial.quasiIso_singChainsMap_of_homotopyEquiv (e.subtype h).toHomotopyEquiv
  · exact Simplicial.quasiIso_singChainsMap_of_homotopyEquiv e.toHomotopyEquiv

/-- The isomorphism is induced by the homeomorphism, not chosen abstractly. -/
def relativeHomologyIsoOfHomeomorph (e : X ≃ₜ Y)
    (h : ∀ x, x ∈ A ↔ e x ∈ B) (k : ℕ) :
    relativeHomology A k ≅ relativeHomology B k := by
  have := quasiIso_relativeMap_of_homeomorph e h
  exact asIso (HomologicalComplex.homologyMap
    (relativeMap (TopCat.ofHom (e : C(X, Y))) (fun x hx => (h x).mp hx)) k)

end AffineTverberg.AffChain
