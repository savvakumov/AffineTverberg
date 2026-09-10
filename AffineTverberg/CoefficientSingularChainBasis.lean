import AffineTverberg.CoefficientSmallChainQuasiIso
import AffineTverberg.SingularChainBasis

set_option linter.style.header false

/-!
# Singular chain bases over arbitrary fields

The free-chain basis identifies chains carried by a subset with coefficients
supported on the corresponding singular simplices. This proves the intersection
and inclusion-range identities needed for actual Mayer–Vietoris over any field.
-/

noncomputable section

open CategoryTheory Limits Simplicial AffineTverberg.AffChain

namespace AffineTverberg.Coefficients.AffChain

variable (𝕜 : Type) [Field 𝕜]
variable {X : TopCat.{0}}

/-- The coordinate map of singular chains in the basis of singular simplices. -/
def toFinsuppHom (X : TopCat.{0}) (n : ℕ) :
    (singChains 𝕜 X).X n ⟶ ModuleCat.of 𝕜 (singIdx X n →₀ 𝕜) :=
  Limits.Sigma.desc (fun x => ModuleCat.ofHom (Finsupp.lsingle x))

/-- The inverse of `toFinsuppHom 𝕜`: a finitely supported family of coefficients
is the corresponding finite linear combination of singular simplices. -/
def ofFinsuppHom (X : TopCat.{0}) (n : ℕ) :
    ModuleCat.of 𝕜 (singIdx X n →₀ 𝕜) ⟶ (singChains 𝕜 X).X n :=
  ModuleCat.ofHom (Finsupp.lsum 𝕜 (fun x => (ιs 𝕜 x).hom))

lemma ιs_toFinsuppHom {n : ℕ} (x : singIdx X n) :
    ιs 𝕜 x ≫ toFinsuppHom 𝕜 X n = ModuleCat.ofHom (Finsupp.lsingle x) := by
  simp [toFinsuppHom, ιs, SSet.ιChainComplex]

lemma toFinsuppHom_ιs {n : ℕ} (x : singIdx X n) (r : 𝕜) :
    (toFinsuppHom 𝕜 X n).hom ((ιs 𝕜 x).hom r) = Finsupp.single x r := by
  have := congrArg (fun g : ModuleCat.of 𝕜 𝕜 ⟶ _ => g.hom r) (ιs_toFinsuppHom 𝕜 (X := X) x)
  simpa using this

lemma ofFinsuppHom_single {n : ℕ} (x : singIdx X n) (r : 𝕜) :
    (ofFinsuppHom 𝕜 X n).hom (Finsupp.single x r) = (ιs 𝕜 x).hom r := by
  simp [ofFinsuppHom]

lemma ofFinsuppHom_toFinsuppHom (X : TopCat.{0}) (n : ℕ) :
    ofFinsuppHom 𝕜 X n ≫ toFinsuppHom 𝕜 X n = 𝟙 _ := by
  refine ModuleCat.hom_ext (Finsupp.lhom_ext' fun x => LinearMap.ext fun r => ?_)
  change (toFinsuppHom 𝕜 X n).hom ((ofFinsuppHom 𝕜 X n).hom (Finsupp.single x r)) = _
  rw [ofFinsuppHom_single 𝕜, toFinsuppHom_ιs 𝕜]
  rfl

lemma toFinsuppHom_ofFinsuppHom (X : TopCat.{0}) (n : ℕ) :
    toFinsuppHom 𝕜 X n ≫ ofFinsuppHom 𝕜 X n = 𝟙 _ := by
  refine singChains_hom_ext 𝕜 fun x => ?_
  rw [← Category.assoc, ιs_toFinsuppHom 𝕜]
  refine ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
  change (ofFinsuppHom 𝕜 X n).hom (Finsupp.single x r) = _
  rw [ofFinsuppHom_single 𝕜]
  rfl

/-- **The singular `n`-chains are free on the singular `n`-simplices.** -/
def chainEquiv (X : TopCat.{0}) (n : ℕ) :
    (singChains 𝕜 X).X n ≃ₗ[𝕜] (singIdx X n →₀ 𝕜) where
  toFun := (toFinsuppHom 𝕜 X n).hom
  map_add' := map_add _
  map_smul' := map_smul _
  invFun := (ofFinsuppHom 𝕜 X n).hom
  left_inv x :=
    congrArg (fun g : (singChains 𝕜 X).X n ⟶ (singChains 𝕜 X).X n => g.hom x)
      (toFinsuppHom_ofFinsuppHom 𝕜 X n)
  right_inv y :=
    congrArg (fun g : ModuleCat.of 𝕜 (singIdx X n →₀ 𝕜) ⟶ _ => g.hom y)
      (ofFinsuppHom_toFinsuppHom 𝕜 X n)

@[simp] lemma chainEquiv_apply {n : ℕ} (x : (singChains 𝕜 X).X n) :
    chainEquiv 𝕜 X n x = (toFinsuppHom 𝕜 X n).hom x := rfl

lemma chainEquiv_ιs {n : ℕ} (x : singIdx X n) (r : 𝕜) :
    chainEquiv 𝕜 X n ((ιs 𝕜 x).hom r) = Finsupp.single x r := toFinsuppHom_ιs 𝕜 x r

lemma chainEquiv_sElt {n : ℕ} (σ : C(Δt n, X)) :
    chainEquiv 𝕜 X n (sElt 𝕜 σ) = Finsupp.single (singSimplex σ) 1 :=
  chainEquiv_ιs 𝕜 _ _

lemma chainEquiv_image_generators (S : Set X) (n : ℕ) :
    chainEquiv 𝕜 X n '' {x | ∃ σ : C(Δt n, X), (∀ t, σ t ∈ S) ∧ x = sElt 𝕜 σ} =
      (fun x => Finsupp.single x (1 : 𝕜)) '' simplicesIn S n := by
  ext y
  constructor
  · rintro ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
    exact ⟨singSimplex σ, by simpa [simplicesIn] using hσ, (chainEquiv_sElt 𝕜 σ).symm ▸ rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨sElt 𝕜 (simplexMap x), ⟨simplexMap x, hx, rfl⟩, ?_⟩
    rw [chainEquiv_sElt 𝕜, singSimplex_simplexMap]

/-- Under the basis identification, the chains carried by `S` are exactly the
coefficient families supported on the simplices with image in `S`. -/
theorem map_chainsIn (S : Set X) (n : ℕ) :
    Submodule.map (chainEquiv 𝕜 X n).toLinearMap (chainsIn 𝕜 S n) =
      Finsupp.supported 𝕜 𝕜 (simplicesIn S n) := by
  rw [chainsIn, Submodule.map_span, Finsupp.supported_eq_span_single]
  congr 1
  exact chainEquiv_image_generators 𝕜 S n

theorem chainsIn_eq_comap (S : Set X) (n : ℕ) :
    chainsIn 𝕜 S n =
      Submodule.comap (chainEquiv 𝕜 X n).toLinearMap (Finsupp.supported 𝕜 𝕜 (simplicesIn S n)) := by
  rw [← map_chainsIn 𝕜 S n, Submodule.comap_map_eq_of_injective (chainEquiv 𝕜 X n).injective]

lemma mem_chainsIn_iff {S : Set X} {n : ℕ} (c : (singChains 𝕜 X).X n) :
    c ∈ chainsIn 𝕜 S n ↔ ∀ x ∉ simplicesIn S n, chainEquiv 𝕜 X n c x = 0 := by
  rw [chainsIn_eq_comap 𝕜]
  exact Finsupp.mem_supported' (M := 𝕜) (R := 𝕜) _

lemma chainsIn_mono {S T : Set X} (h : S ⊆ T) (n : ℕ) : chainsIn 𝕜 S n ≤ chainsIn 𝕜 T n := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨σ, hσ, rfl⟩
  exact sElt_mem_chainsIn 𝕜 fun t => h (hσ t)

/-- **A chain carried by `S` and by `T` is carried by `S ∩ T`.** This is the
key freeness input to the Mayer-Vietoris short exact sequence. -/
theorem chainsIn_inf (S T : Set X) (n : ℕ) :
    chainsIn 𝕜 S n ⊓ chainsIn 𝕜 T n = chainsIn 𝕜 (S ∩ T) n := by
  refine le_antisymm (fun c hc => ?_) (le_inf (chainsIn_mono 𝕜 Set.inter_subset_left n)
    (chainsIn_mono 𝕜 Set.inter_subset_right n))
  rw [mem_chainsIn_iff 𝕜]
  intro x hx
  by_cases hS : x ∈ simplicesIn S n
  · have hT : x ∉ simplicesIn T n := fun hT => hx (fun t => ⟨hS t, hT t⟩)
    exact (mem_chainsIn_iff 𝕜 c).1 hc.2 x hT
  · exact (mem_chainsIn_iff 𝕜 c).1 hc.1 x hS

/-- For a two-element cover the small chains are the sum of the chains carried
by the two pieces. -/
theorem smallChains_bool (A B : Set X) (n : ℕ) :
    smallChains 𝕜 (fun b : Bool => bif b then A else B) n = chainsIn 𝕜 A n ⊔ chainsIn 𝕜 B n := by
  rw [smallChains_eq_iSup 𝕜, iSup_bool_eq]
  rfl

/-- The chain map induced by a subspace inclusion. -/
def chainsInclusion (S : Set X) : singChains 𝕜 (subSpace S) ⟶ singChains 𝕜 X :=
  SSet.chainComplexMap (TopCat.toSSet.map (subIncl S)) (ModuleCat.of 𝕜 𝕜)

lemma ιs_chainsInclusion {S : Set X} {n : ℕ} (x : singIdx (subSpace S) n) :
    ιs 𝕜 x ≫ (chainsInclusion 𝕜 S).f n = ιs 𝕜 (subSimplexMap S n x) :=
  by rw [chainsInclusion, SSet.ι_chainComplexMap_f]; rfl

lemma chainsInclusion_toFinsupp (S : Set X) (n : ℕ) :
    (chainsInclusion 𝕜 S).f n ≫ toFinsuppHom 𝕜 X n =
      toFinsuppHom 𝕜 (subSpace S) n ≫
        ModuleCat.ofHom (Finsupp.lmapDomain 𝕜 𝕜 (subSimplexMap S n)) := by
  refine singChains_hom_ext 𝕜 fun x => ?_
  rw [← Category.assoc, ιs_chainsInclusion 𝕜, ιs_toFinsuppHom 𝕜,
    ← Category.assoc, ιs_toFinsuppHom 𝕜]
  refine ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
  simp

lemma chainEquiv_chainsInclusion {S : Set X} {n : ℕ} (y : (singChains 𝕜 (subSpace S)).X n) :
    chainEquiv 𝕜 X n (((chainsInclusion 𝕜 S).f n).hom y) =
      Finsupp.mapDomain (subSimplexMap S n) (chainEquiv 𝕜 (subSpace S) n y) := by
  have := congrArg (fun g : (singChains 𝕜 (subSpace S)).X n ⟶ _ => g.hom y)
    (chainsInclusion_toFinsupp 𝕜 S n)
  simpa using this

/-- **The chain map induced by a subspace inclusion is injective.** -/
theorem chainsInclusion_injective (S : Set X) (n : ℕ) :
    Function.Injective ((chainsInclusion 𝕜 S).f n).hom := by
  intro a b hab
  apply (chainEquiv 𝕜 (subSpace S) n).injective
  apply Finsupp.mapDomain_injective (subSimplexMap_injective S n)
  rw [← chainEquiv_chainsInclusion 𝕜, ← chainEquiv_chainsInclusion 𝕜, hab]

/-- **The image of the chain map induced by a subspace inclusion consists
exactly of the chains carried by that subspace.** -/
theorem range_chainsInclusion (S : Set X) (n : ℕ) :
    LinearMap.range ((chainsInclusion 𝕜 S).f n).hom = chainsIn 𝕜 S n := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    rw [mem_chainsIn_iff 𝕜]
    intro x hx
    rw [chainEquiv_chainsInclusion 𝕜]
    by_contra hne
    have hmem : x ∈ Set.range (subSimplexMap S n) := by
      by_contra hnot
      exact hne (Finsupp.mapDomain_of_notMem_range _ _ hnot)
    exact hx ((range_subSimplexMap S n) ▸ hmem)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨σ, hσ, rfl⟩
    refine ⟨sElt 𝕜 ⟨fun t => ⟨σ t, hσ t⟩, by fun_prop⟩, ?_⟩
    have h := congrArg (fun g : ModuleCat.of 𝕜 𝕜 ⟶ (singChains 𝕜 X).X n => g.hom (1 : 𝕜))
      (ιs_chainsInclusion 𝕜 (S := S) (singSimplex (⟨fun t => ⟨σ t, hσ t⟩, by fun_prop⟩ :
        C(Δt n, subSpace S))))
    refine h.trans ?_
    congr 1

end AffineTverberg.Coefficients.AffChain
