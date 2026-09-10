import AffineTverberg.CoefficientAffineChains
import AffineTverberg.SingularSubdivision

set_option linter.style.header false

/-!
# Singular subdivision over an arbitrary field

This constructs the actual subdivision chain map, its chain homotopy to the
identity, and naturality, over any field. It reuses the real standard-simplex
geometry; only the free-chain coefficients vary.
-/

noncomputable section

open CategoryTheory Limits Simplicial AffineTverberg.AffChain
open scoped BigOperators

namespace AffineTverberg.Coefficients.AffChain

variable (𝕜 : Type) [Field 𝕜]
variable {X Y : TopCat.{0}}

/-- The singular chain complex of `X` with arbitrary field coefficients. -/
abbrev singChains (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} 𝕜) ℕ :=
  (TopCat.toSSet.obj X).chainComplex (ModuleCat.of 𝕜 𝕜)


/-- The basis element of the singular chains attached to a singular simplex. -/
abbrev ιs {n : ℕ} (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    ModuleCat.of 𝕜 𝕜 ⟶ (singChains 𝕜 X).X n :=
  (TopCat.toSSet.obj X).ιChainComplex x

lemma singChains_hom_ext {n : ℕ} {T : ModuleCat.{0} 𝕜} {f g : (singChains 𝕜 X).X n ⟶ T}
    (h : ∀ x : (TopCat.toSSet.obj X) _⦋n⦌, ιs 𝕜 x ≫ f = ιs 𝕜 x ≫ g) : f = g :=
  SSet.chainComplex_hom_ext h

/-! ### Realization of affine chains along a singular simplex -/

lemma ιa_realChain_singSimplex {n j : ℕ} (σ : C(Δt n, X)) (v : Fin (j + 1) → Δt n) :
    ιa 𝕜 v ≫ (realChain 𝕜 σ).f j = ιs 𝕜 (singSimplex (σ.comp (affMap v))) :=
  ιa_realChain 𝕜 σ v

lemma ιa_idTuple_realChain {n : ℕ} (σ : C(Δt n, X)) :
    ιa 𝕜 (idTuple n) ≫ (realChain 𝕜 σ).f n = ιs 𝕜 (singSimplex σ) := by
  rw [ιa_realChain_singSimplex 𝕜, affMap_idTuple]
  rfl

/-- Realizing along a composite affine map is the pushforward followed by the
realization. -/
lemma realChain_comp_affMap {n k j : ℕ} (σ : C(Δt n, X)) (w : Fin (k + 1) → Δt n) :
    (realChain 𝕜 (σ.comp (affMap w))).f j = (pushChain 𝕜 w).f j ≫ (realChain 𝕜 σ).f j := by
  refine affChains_hom_ext 𝕜 fun v => ?_
  rw [ιa_realChain_singSimplex 𝕜, ← Category.assoc, ιa_pushChain 𝕜,
    ιa_realChain_singSimplex 𝕜]
  congr 2
  ext t
  change σ (affPoint w (affPoint v t)) = σ (affPoint (fun a => affPoint w (v a)) t)
  rw [affPoint_comp]

/-! ### The subdivision operator on singular chains -/

/-- The barycentric subdivision of singular chains. -/
def sdSing (X : TopCat.{0}) (n : ℕ) : (singChains 𝕜 X).X n ⟶ (singChains 𝕜 X).X n :=
  Sigma.desc (fun x : (TopCat.toSSet.obj X) _⦋n⦌ =>
    ιa 𝕜 (idTuple n) ≫ sdHom 𝕜 n n ≫ (realChain 𝕜 (X.toSSetObjEquiv (Opposite.op ⦋n⦌) x)).f n)

/-- The chain homotopy operator on singular chains. -/
def tdSing (X : TopCat.{0}) (n : ℕ) : (singChains 𝕜 X).X n ⟶ (singChains 𝕜 X).X (n + 1) :=
  Sigma.desc (fun x : (TopCat.toSSet.obj X) _⦋n⦌ =>
    ιa 𝕜 (idTuple n) ≫ tdHom 𝕜 n n ≫ (realChain 𝕜 (X.toSSetObjEquiv (Opposite.op ⦋n⦌) x)).f (n + 1))

lemma ιs_sdSing {n : ℕ} (σ : C(Δt n, X)) :
    ιs 𝕜 (singSimplex σ) ≫ sdSing 𝕜 X n =
      ιa 𝕜 (idTuple n) ≫ sdHom 𝕜 n n ≫ (realChain 𝕜 σ).f n := by
  refine (Sigma.ι_desc _ (singSimplex σ)).trans ?_
  rw [toSSetObjEquiv_singSimplex]

lemma ιs_tdSing {n : ℕ} (σ : C(Δt n, X)) :
    ιs 𝕜 (singSimplex σ) ≫ tdSing 𝕜 X n =
      ιa 𝕜 (idTuple n) ≫ tdHom 𝕜 n n ≫ (realChain 𝕜 σ).f (n + 1) := by
  refine (Sigma.ι_desc _ (singSimplex σ)).trans ?_
  rw [toSSetObjEquiv_singSimplex]

lemma singChains_hom_ext' {n : ℕ} {T : ModuleCat.{0} 𝕜} {f g : (singChains 𝕜 X).X n ⟶ T}
    (h : ∀ σ : C(Δt n, X), ιs 𝕜 (singSimplex σ) ≫ f = ιs 𝕜 (singSimplex σ) ≫ g) : f = g := by
  refine singChains_hom_ext 𝕜 fun x => ?_
  have := h (X.toSSetObjEquiv (Opposite.op ⦋n⦌) x)
  rwa [singSimplex_surjective] at this

/-- The subdivision is the identity on singular `0`-chains. -/
theorem sdSing_zero (X : TopCat.{0}) : sdSing 𝕜 X 0 = 𝟙 _ := by
  refine singChains_hom_ext' 𝕜 fun σ => ?_
  rw [ιs_sdSing 𝕜, sdHom_zero 𝕜, Category.id_comp, ιa_idTuple_realChain 𝕜, Category.comp_id]

/-- The key face computation: the subdivision of the `i`-th face of the
identity simplex. -/
lemma ιa_face_sdHom_real {n : ℕ} (σ : C(Δt (n + 1), X)) (i : Fin (n + 2)) :
    ιa 𝕜 (idTuple n) ≫ sdHom 𝕜 n n ≫ (realChain 𝕜 (σ.comp (faceMap i))).f n =
      ιa 𝕜 (idTuple (n + 1) ∘ i.succAbove) ≫ sdHom 𝕜 (n + 1) n ≫
        (realChain 𝕜 σ).f n := by
  rw [← affMap_idTuple_succAbove i, realChain_comp_affMap 𝕜,
    ← Category.assoc (sdHom 𝕜 n n), pushChain_sdHom 𝕜, Category.assoc,
    ← Category.assoc (ιa 𝕜 (idTuple n)), ιa_pushChain 𝕜]
  congr 2
  funext a
  exact affPoint_vertex _ a

/-- The analogous face computation for the homotopy operator. -/
lemma ιa_face_tdHom_real {n : ℕ} (σ : C(Δt (n + 1), X)) (i : Fin (n + 2)) :
    ιa 𝕜 (idTuple n) ≫ tdHom 𝕜 n n ≫ (realChain 𝕜 (σ.comp (faceMap i))).f (n + 1) =
      ιa 𝕜 (idTuple (n + 1) ∘ i.succAbove) ≫ tdHom 𝕜 (n + 1) n ≫
        (realChain 𝕜 σ).f (n + 1) := by
  rw [← affMap_idTuple_succAbove i, realChain_comp_affMap 𝕜,
    ← Category.assoc (tdHom 𝕜 n n), pushChain_tdHom 𝕜, Category.assoc,
    ← Category.assoc (ιa 𝕜 (idTuple n)), ιa_pushChain 𝕜]
  congr 2
  funext a
  exact affPoint_vertex _ a

/-- **The subdivision operator is a chain map.** -/
theorem sdSing_d (X : TopCat.{0}) (n : ℕ) :
    sdSing 𝕜 X (n + 1) ≫ (singChains 𝕜 X).d (n + 1) n =
      (singChains 𝕜 X).d (n + 1) n ≫ sdSing 𝕜 X n := by
  refine singChains_hom_ext' 𝕜 fun σ => ?_
  have hL : ιs 𝕜 (singSimplex σ) ≫ sdSing 𝕜 X (n + 1) ≫ (singChains 𝕜 X).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : 𝕜) ^ (i : ℕ) •
        (ιa 𝕜 (idTuple (n + 1) ∘ i.succAbove) ≫ sdHom 𝕜 (n + 1) n ≫
          (realChain 𝕜 σ).f n) := by
    rw [← Category.assoc, ιs_sdSing 𝕜, Category.assoc, Category.assoc,
      (realChain 𝕜 σ).comm (n + 1) n, ← Category.assoc (sdHom 𝕜 (n + 1) (n + 1)), sdHom_d 𝕜,
      Category.assoc, ← Category.assoc (ιa 𝕜 (idTuple (n + 1))), ιa_d 𝕜,
      Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Linear.smul_comp]
  have hR : ιs 𝕜 (singSimplex σ) ≫ (singChains 𝕜 X).d (n + 1) n ≫ sdSing 𝕜 X n =
      ∑ i : Fin (n + 2), (-1 : 𝕜) ^ (i : ℕ) •
        (ιa 𝕜 (idTuple (n + 1) ∘ i.succAbove) ≫ sdHom 𝕜 (n + 1) n ≫
          (realChain 𝕜 σ).f n) := by
    rw [← Category.assoc, (TopCat.toSSet.obj X).ιChainComplex_d (ModuleCat.of 𝕜 𝕜),
      Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul 𝕜 ((-1 : ℤ) ^ (i : ℕ))]
    push_cast
    rw [Linear.smul_comp]
    congr 1
    rw [show ((ConcreteCategory.hom ((TopCat.toSSet.obj X).δ i)) (singSimplex σ)) =
      (TopCat.toSSet.obj X).δ i (singSimplex σ) from rfl, delta_singSimplex, ιs_sdSing 𝕜,
      ιa_face_sdHom_real 𝕜]
  rw [hL, hR]

/-- **The homotopy identity in degree zero.** -/
theorem tdSing_d_zero (X : TopCat.{0}) :
    tdSing 𝕜 X 0 ≫ (singChains 𝕜 X).d 1 0 = 𝟙 _ - sdSing 𝕜 X 0 := by
  rw [sdSing_zero 𝕜, sub_self]
  refine singChains_hom_ext' 𝕜 fun σ => ?_
  rw [← Category.assoc, ιs_tdSing 𝕜, Category.assoc, Category.assoc,
    (realChain 𝕜 σ).comm 1 0, ← Category.assoc (tdHom 𝕜 0 0), tdHom_d_zero 𝕜,
    sdHom_zero 𝕜, sub_self, Limits.zero_comp, comp_zero, comp_zero]

/-- **The homotopy identity `∂T + T∂ = 1 - S` on singular chains.** -/
theorem tdSing_d (X : TopCat.{0}) (n : ℕ) :
    tdSing 𝕜 X (n + 1) ≫ (singChains 𝕜 X).d (n + 2) (n + 1) +
        (singChains 𝕜 X).d (n + 1) n ≫ tdSing 𝕜 X n =
      𝟙 _ - sdSing 𝕜 X (n + 1) := by
  refine singChains_hom_ext' 𝕜 fun σ => ?_
  have hsum : ιa 𝕜 (idTuple (n + 1)) ≫ ((affChains 𝕜 (n + 1)).d (n + 1) n ≫ tdHom 𝕜 (n + 1) n) ≫
        (realChain 𝕜 σ).f (n + 1) =
      ∑ i : Fin (n + 2), (-1 : 𝕜) ^ (i : ℕ) •
        (ιa 𝕜 (idTuple (n + 1) ∘ i.succAbove) ≫ tdHom 𝕜 (n + 1) n ≫ (realChain 𝕜 σ).f (n + 1)) := by
    simp only [Category.assoc]
    rw [← Category.assoc (ιa 𝕜 (idTuple (n + 1))) ((affChains 𝕜 (n + 1)).d (n + 1) n), ιa_d 𝕜,
      Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Linear.smul_comp]
  have hB : ιs 𝕜 (singSimplex σ) ≫ (singChains 𝕜 X).d (n + 1) n ≫ tdSing 𝕜 X n =
      ∑ i : Fin (n + 2), (-1 : 𝕜) ^ (i : ℕ) •
        (ιa 𝕜 (idTuple (n + 1) ∘ i.succAbove) ≫ tdHom 𝕜 (n + 1) n ≫ (realChain 𝕜 σ).f (n + 1)) := by
    rw [← Category.assoc, (TopCat.toSSet.obj X).ιChainComplex_d (ModuleCat.of 𝕜 𝕜),
      Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul 𝕜 ((-1 : ℤ) ^ (i : ℕ))]
    push_cast
    rw [Linear.smul_comp]
    congr 1
    rw [show ((ConcreteCategory.hom ((TopCat.toSSet.obj X).δ i)) (singSimplex σ)) =
      (TopCat.toSSet.obj X).δ i (singSimplex σ) from rfl, delta_singSimplex, ιs_tdSing 𝕜,
      ιa_face_tdHom_real 𝕜]
  have hA : ιs 𝕜 (singSimplex σ) ≫ tdSing 𝕜 X (n + 1) ≫ (singChains 𝕜 X).d (n + 2) (n + 1) =
      ιa 𝕜 (idTuple (n + 1)) ≫ (𝟙 _ - sdHom 𝕜 (n + 1) (n + 1)) ≫ (realChain 𝕜 σ).f (n + 1) -
        ιa 𝕜 (idTuple (n + 1)) ≫ ((affChains 𝕜 (n + 1)).d (n + 1) n ≫ tdHom 𝕜 (n + 1) n) ≫
          (realChain 𝕜 σ).f (n + 1) := by
    have h' : tdHom 𝕜 (n + 1) (n + 1) ≫ (affChains 𝕜 (n + 1)).d (n + 2) (n + 1) =
        𝟙 _ - sdHom 𝕜 (n + 1) (n + 1) - (affChains 𝕜 (n + 1)).d (n + 1) n ≫ tdHom 𝕜 (n + 1) n := by
      rw [← tdHom_d 𝕜 (n + 1) n]; abel
    rw [← Category.assoc, ιs_tdSing 𝕜, Category.assoc, Category.assoc,
      (realChain 𝕜 σ).comm (n + 2) (n + 1), ← Category.assoc (tdHom 𝕜 (n + 1) (n + 1)), h',
      Preadditive.sub_comp, Preadditive.comp_sub]
  have hC : ιs 𝕜 (singSimplex σ) ≫ (𝟙 _ - sdSing 𝕜 X (n + 1)) =
      ιa 𝕜 (idTuple (n + 1)) ≫ (𝟙 _ - sdHom 𝕜 (n + 1) (n + 1)) ≫ (realChain 𝕜 σ).f (n + 1) := by
    rw [Preadditive.comp_sub, Category.comp_id, ιs_sdSing 𝕜, Preadditive.sub_comp,
      Category.id_comp, Preadditive.comp_sub, ιa_idTuple_realChain 𝕜]
  rw [Preadditive.comp_add, hA, hB, hC, hsum]
  abel

/-! ### Packaging as a chain map and a homotopy -/

/-- The barycentric subdivision as an endomorphism of the singular chain
complex. -/
def sdChainMap (X : TopCat.{0}) : singChains 𝕜 X ⟶ singChains 𝕜 X where
  f n := sdSing 𝕜 X n
  comm' i j hij := by
    obtain ⟨rfl⟩ : j + 1 = i := hij
    exact sdSing_d 𝕜 X j

/-- **The barycentric subdivision is chain homotopic to the identity.** -/
def sdHomotopy (X : TopCat.{0}) : Homotopy (sdChainMap 𝕜 X) (𝟙 (singChains 𝕜 X)) where
  hom i j := if h : j = i + 1 then (-tdSing 𝕜 X i) ≫ eqToHom (by rw [h]) else 0
  zero i j hij := by
    rw [dite_eq_right]
    intro h
    exact hij (by simp [ComplexShape.down_Rel, h])
  comm i := by
    cases i with
    | zero =>
      rw [dNext_eq_zero _ _ (by simp [ChainComplex.next_nat_zero, ComplexShape.down_Rel]),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel (0 + 1) 0 from rfl), zero_add]
      change sdSing 𝕜 X 0 = ((if h : (0 : ℕ) + 1 = 0 + 1 then (-tdSing 𝕜 X 0) ≫ eqToHom (by rw [h])
        else 0) ≫ (singChains 𝕜 X).d (0 + 1) 0) + 𝟙 _
      rw [dite_eq_left rfl, eqToHom_refl, Category.comp_id, Preadditive.neg_comp,
        tdSing_d_zero 𝕜, sdSing_zero 𝕜, sub_self, neg_zero, zero_add]
    | succ m =>
      rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (m + 1) m from rfl),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel (m + 1 + 1) (m + 1) from rfl)]
      change sdSing 𝕜 X (m + 1) = ((singChains 𝕜 X).d (m + 1) m ≫
          (if h : m + 1 = m + 1 then (-tdSing 𝕜 X m) ≫ eqToHom (by rw [h]) else 0)) +
        ((if h : m + 1 + 1 = m + 1 + 1 then (-tdSing 𝕜 X (m + 1)) ≫ eqToHom (by rw [h])
          else 0) ≫ (singChains 𝕜 X).d (m + 1 + 1) (m + 1)) + 𝟙 _
      rw [dite_eq_left rfl, dite_eq_left rfl, eqToHom_refl, eqToHom_refl, Category.comp_id,
        Category.comp_id, Preadditive.comp_neg, Preadditive.neg_comp]
      have h : tdSing 𝕜 X (m + 1) ≫ (singChains 𝕜 X).d (m + 1 + 1) (m + 1) +
          (singChains 𝕜 X).d (m + 1) m ≫ tdSing 𝕜 X m = 𝟙 _ - sdSing 𝕜 X (m + 1) := tdSing_d 𝕜 X m
      have hsd : sdSing 𝕜 X (m + 1) = 𝟙 _ -
          (tdSing 𝕜 X (m + 1) ≫ (singChains 𝕜 X).d (m + 1 + 1) (m + 1) +
            (singChains 𝕜 X).d (m + 1) m ≫ tdSing 𝕜 X m) := by
        rw [h]; abel
      rw [hsd]
      abel

/-- The subdivision induces the identity on singular homology. -/
theorem homologyMap_sdChainMap (X : TopCat.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (sdChainMap 𝕜 X) n = 𝟙 _ := by
  rw [(sdHomotopy 𝕜 X).homologyMap_eq, HomologicalComplex.homologyMap_id]

/-! ### Naturality in the space -/

/-- The chain map of singular chains induced by a continuous map. -/
abbrev singChainsMap (f : X ⟶ Y) : singChains 𝕜 X ⟶ singChains 𝕜 Y :=
  SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of 𝕜 𝕜)


lemma ιs_singChainsMap {n : ℕ} (f : X ⟶ Y) (σ : C(Δt n, X)) :
    ιs 𝕜 (singSimplex σ) ≫ (singChainsMap 𝕜 f).f n =
      ιs 𝕜 (singSimplex ((ConcreteCategory.hom f).comp σ)) := by
  rw [SSet.ι_chainComplexMap_f, toSSet_map_singSimplex]

lemma realChain_singChainsMap {n j : ℕ} (f : X ⟶ Y) (σ : C(Δt n, X)) :
    (realChain 𝕜 σ).f j ≫ (singChainsMap 𝕜 f).f j =
      (realChain 𝕜 ((ConcreteCategory.hom f).comp σ)).f j := by
  refine affChains_hom_ext 𝕜 fun v => ?_
  rw [← Category.assoc, ιa_realChain_singSimplex 𝕜, ιs_singChainsMap 𝕜,
    ιa_realChain_singSimplex 𝕜]
  rfl

/-- **Naturality of the subdivision operator in the space.** -/
theorem sdSing_naturality (f : X ⟶ Y) (n : ℕ) :
    sdSing 𝕜 X n ≫ (singChainsMap 𝕜 f).f n = (singChainsMap 𝕜 f).f n ≫ sdSing 𝕜 Y n := by
  refine singChains_hom_ext' 𝕜 fun σ => ?_
  have hL : ιs 𝕜 (singSimplex σ) ≫ sdSing 𝕜 X n ≫ (singChainsMap 𝕜 f).f n =
      ιa 𝕜 (idTuple n) ≫ sdHom 𝕜 n n ≫
        (realChain 𝕜 ((ConcreteCategory.hom f).comp σ)).f n := by
    rw [← Category.assoc, ιs_sdSing 𝕜]
    simp only [Category.assoc]
    rw [realChain_singChainsMap 𝕜]
  have hR : ιs 𝕜 (singSimplex σ) ≫ (singChainsMap 𝕜 f).f n ≫ sdSing 𝕜 Y n =
      ιa 𝕜 (idTuple n) ≫ sdHom 𝕜 n n ≫
        (realChain 𝕜 ((ConcreteCategory.hom f).comp σ)).f n := by
    rw [← Category.assoc, ιs_singChainsMap 𝕜, ιs_sdSing 𝕜]
  rw [hL, hR]

/-- **Naturality of the homotopy operator in the space.** -/
theorem tdSing_naturality (f : X ⟶ Y) (n : ℕ) :
    tdSing 𝕜 X n ≫ (singChainsMap 𝕜 f).f (n + 1) = (singChainsMap 𝕜 f).f n ≫ tdSing 𝕜 Y n := by
  refine singChains_hom_ext' 𝕜 fun σ => ?_
  have hL : ιs 𝕜 (singSimplex σ) ≫ tdSing 𝕜 X n ≫ (singChainsMap 𝕜 f).f (n + 1) =
      ιa 𝕜 (idTuple n) ≫ tdHom 𝕜 n n ≫
        (realChain 𝕜 ((ConcreteCategory.hom f).comp σ)).f (n + 1) := by
    rw [← Category.assoc, ιs_tdSing 𝕜]
    simp only [Category.assoc]
    rw [realChain_singChainsMap 𝕜]
  have hR : ιs 𝕜 (singSimplex σ) ≫ (singChainsMap 𝕜 f).f n ≫ tdSing 𝕜 Y n =
      ιa 𝕜 (idTuple n) ≫ tdHom 𝕜 n n ≫
        (realChain 𝕜 ((ConcreteCategory.hom f).comp σ)).f (n + 1) := by
    rw [← Category.assoc, ιs_singChainsMap 𝕜, ιs_tdSing 𝕜]
  rw [hL, hR]

end AffineTverberg.Coefficients.AffChain

