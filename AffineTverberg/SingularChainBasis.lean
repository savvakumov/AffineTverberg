import AffineTverberg.SmallChainQuasiIso

set_option linter.style.header false

/-!
# The free basis of singular chains and chains carried by a subspace

Mathlib's singular chain complex of a space `X` is degreewise a coproduct of
copies of the coefficient object indexed by the singular simplices. This file
makes that description concrete over `ℝ`: `chainEquiv X n` is the linear
equivalence between the singular `n`-chains of `X` and the finitely supported
functions on the set of singular `n`-simplices.

Two consequences are proved, both needed for a genuine Mayer-Vietoris argument:

* `chainsIn_inf` : a chain carried by `S` and by `T` is carried by `S ∩ T`;
* `range_chainsInclusion` : the chain map induced by a subspace inclusion
  `S ↪ X` is injective in every degree with image exactly `chainsIn S n`.

Nothing here assumes any comparison or excision statement.
-/

noncomputable section

open CategoryTheory Limits Simplicial

namespace AffineTverberg

namespace AffChain

variable {X : TopCat.{0}}

/-! ### The free basis of singular chains -/

/-- The type of singular `n`-simplices of `X`. -/
abbrev singIdx (X : TopCat.{0}) (n : ℕ) := (TopCat.toSSet.obj X) _⦋n⦌

/-- The coordinate map of singular chains in the basis of singular simplices. -/
def toFinsuppHom (X : TopCat.{0}) (n : ℕ) :
    (singChains X).X n ⟶ ModuleCat.of ℝ (singIdx X n →₀ ℝ) :=
  Limits.Sigma.desc (fun x => ModuleCat.ofHom (Finsupp.lsingle x))

/-- The inverse of `toFinsuppHom`: a finitely supported family of coefficients
is the corresponding finite linear combination of singular simplices. -/
def ofFinsuppHom (X : TopCat.{0}) (n : ℕ) :
    ModuleCat.of ℝ (singIdx X n →₀ ℝ) ⟶ (singChains X).X n :=
  ModuleCat.ofHom (Finsupp.lsum ℝ (fun x => (ιs x).hom))

lemma ιs_toFinsuppHom {n : ℕ} (x : singIdx X n) :
    ιs x ≫ toFinsuppHom X n = ModuleCat.ofHom (Finsupp.lsingle x) := by
  simp [toFinsuppHom, ιs, SSet.ιChainComplex]

lemma toFinsuppHom_ιs {n : ℕ} (x : singIdx X n) (r : ℝ) :
    (toFinsuppHom X n).hom ((ιs x).hom r) = Finsupp.single x r := by
  have := congrArg (fun g : ModuleCat.of ℝ ℝ ⟶ _ => g.hom r) (ιs_toFinsuppHom (X := X) x)
  simpa using this

lemma ofFinsuppHom_single {n : ℕ} (x : singIdx X n) (r : ℝ) :
    (ofFinsuppHom X n).hom (Finsupp.single x r) = (ιs x).hom r := by
  simp [ofFinsuppHom]

lemma ofFinsuppHom_toFinsuppHom (X : TopCat.{0}) (n : ℕ) :
    ofFinsuppHom X n ≫ toFinsuppHom X n = 𝟙 _ := by
  refine ModuleCat.hom_ext (Finsupp.lhom_ext' fun x => LinearMap.ext fun r => ?_)
  change (toFinsuppHom X n).hom ((ofFinsuppHom X n).hom (Finsupp.single x r)) = _
  rw [ofFinsuppHom_single, toFinsuppHom_ιs]
  rfl

lemma toFinsuppHom_ofFinsuppHom (X : TopCat.{0}) (n : ℕ) :
    toFinsuppHom X n ≫ ofFinsuppHom X n = 𝟙 _ := by
  refine singChains_hom_ext fun x => ?_
  rw [← Category.assoc, ιs_toFinsuppHom]
  refine ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
  change (ofFinsuppHom X n).hom (Finsupp.single x r) = _
  rw [ofFinsuppHom_single]
  rfl

/-- **The singular `n`-chains are free on the singular `n`-simplices.** -/
def chainEquiv (X : TopCat.{0}) (n : ℕ) :
    (singChains X).X n ≃ₗ[ℝ] (singIdx X n →₀ ℝ) where
  toFun := (toFinsuppHom X n).hom
  map_add' := map_add _
  map_smul' := map_smul _
  invFun := (ofFinsuppHom X n).hom
  left_inv x :=
    congrArg (fun g : (singChains X).X n ⟶ (singChains X).X n => g.hom x)
      (toFinsuppHom_ofFinsuppHom X n)
  right_inv y :=
    congrArg (fun g : ModuleCat.of ℝ (singIdx X n →₀ ℝ) ⟶ _ => g.hom y)
      (ofFinsuppHom_toFinsuppHom X n)

@[simp] lemma chainEquiv_apply {n : ℕ} (x : (singChains X).X n) :
    chainEquiv X n x = (toFinsuppHom X n).hom x := rfl

lemma chainEquiv_ιs {n : ℕ} (x : singIdx X n) (r : ℝ) :
    chainEquiv X n ((ιs x).hom r) = Finsupp.single x r := toFinsuppHom_ιs x r

lemma chainEquiv_sElt {n : ℕ} (σ : C(Δt n, X)) :
    chainEquiv X n (sElt σ) = Finsupp.single (singSimplex σ) 1 :=
  chainEquiv_ιs _ _

/-! ### Chains carried by a subset -/

/-- The continuous map underlying a singular simplex. -/
def simplexMap {n : ℕ} (x : singIdx X n) : C(Δt n, X) :=
  X.toSSetObjEquiv (Opposite.op ⦋n⦌) x

@[simp] lemma simplexMap_singSimplex {n : ℕ} (σ : C(Δt n, X)) :
    simplexMap (singSimplex σ) = σ := toSSetObjEquiv_singSimplex σ

@[simp] lemma singSimplex_simplexMap {n : ℕ} (x : singIdx X n) :
    singSimplex (simplexMap x) = x := singSimplex_surjective x

/-- The singular simplices with image inside `S`. -/
def simplicesIn (S : Set X) (n : ℕ) : Set (singIdx X n) :=
  {x | ∀ t, simplexMap x t ∈ S}

lemma chainEquiv_image_generators (S : Set X) (n : ℕ) :
    chainEquiv X n '' {x | ∃ σ : C(Δt n, X), (∀ t, σ t ∈ S) ∧ x = sElt σ} =
      (fun x => Finsupp.single x (1 : ℝ)) '' simplicesIn S n := by
  ext y
  constructor
  · rintro ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
    exact ⟨singSimplex σ, by simpa [simplicesIn] using hσ, (chainEquiv_sElt σ).symm ▸ rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨sElt (simplexMap x), ⟨simplexMap x, hx, rfl⟩, ?_⟩
    rw [chainEquiv_sElt, singSimplex_simplexMap]

/-- Under the basis identification, the chains carried by `S` are exactly the
coefficient families supported on the simplices with image in `S`. -/
theorem map_chainsIn (S : Set X) (n : ℕ) :
    Submodule.map (chainEquiv X n).toLinearMap (chainsIn S n) =
      Finsupp.supported ℝ ℝ (simplicesIn S n) := by
  rw [chainsIn, Submodule.map_span, Finsupp.supported_eq_span_single]
  congr 1
  exact chainEquiv_image_generators S n

theorem chainsIn_eq_comap (S : Set X) (n : ℕ) :
    chainsIn S n =
      Submodule.comap (chainEquiv X n).toLinearMap (Finsupp.supported ℝ ℝ (simplicesIn S n)) := by
  rw [← map_chainsIn S n, Submodule.comap_map_eq_of_injective (chainEquiv X n).injective]

lemma mem_chainsIn_iff {S : Set X} {n : ℕ} (c : (singChains X).X n) :
    c ∈ chainsIn S n ↔ ∀ x ∉ simplicesIn S n, chainEquiv X n c x = 0 := by
  rw [chainsIn_eq_comap]
  exact Finsupp.mem_supported' (M := ℝ) (R := ℝ) _

lemma chainsIn_mono {S T : Set X} (h : S ⊆ T) (n : ℕ) : chainsIn S n ≤ chainsIn T n := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨σ, hσ, rfl⟩
  exact sElt_mem_chainsIn fun t => h (hσ t)

/-- **A chain carried by `S` and by `T` is carried by `S ∩ T`.** This is the
key freeness input to the Mayer-Vietoris short exact sequence. -/
theorem chainsIn_inf (S T : Set X) (n : ℕ) :
    chainsIn S n ⊓ chainsIn T n = chainsIn (S ∩ T) n := by
  refine le_antisymm (fun c hc => ?_) (le_inf (chainsIn_mono Set.inter_subset_left n)
    (chainsIn_mono Set.inter_subset_right n))
  rw [mem_chainsIn_iff]
  intro x hx
  by_cases hS : x ∈ simplicesIn S n
  · have hT : x ∉ simplicesIn T n := fun hT => hx (fun t => ⟨hS t, hT t⟩)
    exact (mem_chainsIn_iff c).1 hc.2 x hT
  · exact (mem_chainsIn_iff c).1 hc.1 x hS

/-- For a two-element cover the small chains are the sum of the chains carried
by the two pieces. -/
theorem smallChains_bool (A B : Set X) (n : ℕ) :
    smallChains (fun b : Bool => bif b then A else B) n = chainsIn A n ⊔ chainsIn B n := by
  rw [smallChains_eq_iSup, iSup_bool_eq]
  rfl

/-! ### The chain map induced by a subspace inclusion -/

/-- A subset of a space, as a space. -/
abbrev subSpace (S : Set X) : TopCat.{0} := TopCat.of ↥S

/-- The inclusion of a subspace. -/
def subIncl (S : Set X) : subSpace S ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The map on singular simplices induced by a subspace inclusion. -/
def subSimplexMap (S : Set X) (n : ℕ) : singIdx (subSpace S) n → singIdx X n :=
  fun x => (TopCat.toSSet.map (subIncl S)).app (Opposite.op ⦋n⦌) x

lemma simplexMap_subSimplexMap {S : Set X} {n : ℕ} (x : singIdx (subSpace S) n) (t : Δt n) :
    simplexMap (subSimplexMap S n x) t = (simplexMap x t : X) := rfl

lemma subSimplexMap_injective (S : Set X) (n : ℕ) :
    Function.Injective (subSimplexMap S n) := by
  intro x y h
  apply ((subSpace S).toSSetObjEquiv (Opposite.op ⦋n⦌)).injective
  ext t
  exact congrArg (fun z => simplexMap z t) h

lemma range_subSimplexMap (S : Set X) (n : ℕ) :
    Set.range (subSimplexMap S n) = simplicesIn S n := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact fun t => (simplexMap y t).2
  · intro hx
    refine ⟨singSimplex ⟨fun t => ⟨simplexMap x t, hx t⟩, by fun_prop⟩, ?_⟩
    apply (X.toSSetObjEquiv (Opposite.op ⦋n⦌)).injective
    ext t
    rfl

/-- The chain map induced by a subspace inclusion. -/
def chainsInclusion (S : Set X) : singChains (subSpace S) ⟶ singChains X :=
  SSet.chainComplexMap (TopCat.toSSet.map (subIncl S)) (ModuleCat.of ℝ ℝ)

lemma ιs_chainsInclusion {S : Set X} {n : ℕ} (x : singIdx (subSpace S) n) :
    ιs x ≫ (chainsInclusion S).f n = ιs (subSimplexMap S n x) :=
  by rw [chainsInclusion, SSet.ι_chainComplexMap_f]; rfl

lemma chainsInclusion_toFinsupp (S : Set X) (n : ℕ) :
    (chainsInclusion S).f n ≫ toFinsuppHom X n =
      toFinsuppHom (subSpace S) n ≫
        ModuleCat.ofHom (Finsupp.lmapDomain ℝ ℝ (subSimplexMap S n)) := by
  refine singChains_hom_ext fun x => ?_
  rw [← Category.assoc, ιs_chainsInclusion, ιs_toFinsuppHom, ← Category.assoc, ιs_toFinsuppHom]
  refine ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
  simp

lemma chainEquiv_chainsInclusion {S : Set X} {n : ℕ} (y : (singChains (subSpace S)).X n) :
    chainEquiv X n (((chainsInclusion S).f n).hom y) =
      Finsupp.mapDomain (subSimplexMap S n) (chainEquiv (subSpace S) n y) := by
  have := congrArg (fun g : (singChains (subSpace S)).X n ⟶ _ => g.hom y)
    (chainsInclusion_toFinsupp S n)
  simpa using this

/-- **The chain map induced by a subspace inclusion is injective.** -/
theorem chainsInclusion_injective (S : Set X) (n : ℕ) :
    Function.Injective ((chainsInclusion S).f n).hom := by
  intro a b hab
  apply (chainEquiv (subSpace S) n).injective
  apply Finsupp.mapDomain_injective (subSimplexMap_injective S n)
  rw [← chainEquiv_chainsInclusion, ← chainEquiv_chainsInclusion, hab]

/-- **The image of the chain map induced by a subspace inclusion consists
exactly of the chains carried by that subspace.** -/
theorem range_chainsInclusion (S : Set X) (n : ℕ) :
    LinearMap.range ((chainsInclusion S).f n).hom = chainsIn S n := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    rw [mem_chainsIn_iff]
    intro x hx
    rw [chainEquiv_chainsInclusion]
    by_contra hne
    have hmem : x ∈ Set.range (subSimplexMap S n) := by
      by_contra hnot
      exact hne (Finsupp.mapDomain_of_notMem_range _ _ hnot)
    exact hx ((range_subSimplexMap S n) ▸ hmem)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨σ, hσ, rfl⟩
    refine ⟨sElt ⟨fun t => ⟨σ t, hσ t⟩, by fun_prop⟩, ?_⟩
    have h := congrArg (fun g : ModuleCat.of ℝ ℝ ⟶ (singChains X).X n => g.hom (1 : ℝ))
      (ιs_chainsInclusion (S := S) (singSimplex (⟨fun t => ⟨σ t, hσ t⟩, by fun_prop⟩ :
        C(Δt n, subSpace S))))
    refine h.trans ?_
    congr 1

end AffChain

end AffineTverberg
