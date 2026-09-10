import AffineTverberg.AffineChains
import Mathlib.Algebra.Homology.Homotopy

set_option linter.style.header false

/-!
# Barycentric subdivision of singular chains

Using the affine chain machinery of `AffineTverberg.AffineChains`, this file
constructs, for an arbitrary topological space `X`, the *barycentric
subdivision operator* on Mathlib's singular chain complex with real
coefficients

* `sdSing X n : Cₙ(X) ⟶ Cₙ(X)`,
* `tdSing X n : Cₙ(X) ⟶ Cₙ₊₁(X)`,

and proves the two classical identities

* `sdSing_d` : `S` is a chain map,
* `tdSing_d` : `∂T + T∂ = 1 - S`.

They are packaged as an actual chain map `sdChainMap X` together with an
actual `Homotopy` to the identity, so `sdChainMap` induces the identity on
singular homology (`homologyMap_sdChainMap`). Naturality in `X` is proved as
well (`sdSing_naturality`). Nothing is assumed: all of this is computed from
the genuine alternating face maps, the genuine barycentres, and the genuine
affine singular simplices.

This is the algebraic part of the classical small-chain argument. The metric
estimates and small-chain quasi-isomorphism are proved in the subsequent
`SmallChains`, `SmallSingular`, `SmallChainTheorem`, and `SmallChainQuasiIso` modules.
-/

noncomputable section

open CategoryTheory Limits Simplicial
open scoped BigOperators

namespace AffineTverberg

namespace AffChain

variable {X Y : TopCat.{0}}

/-- The singular chain complex of `X` with real coefficients. -/
abbrev singChains (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} ℝ) ℕ :=
  (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℝ ℝ)

/-- The singular simplex attached to a continuous map from the standard simplex. -/
def singSimplex {n : ℕ} (σ : C(Δt n, X)) : (TopCat.toSSet.obj X) _⦋n⦌ :=
  (X.toSSetObjEquiv (Opposite.op ⦋n⦌)).symm σ

@[simp] lemma toSSetObjEquiv_singSimplex {n : ℕ} (σ : C(Δt n, X)) :
    X.toSSetObjEquiv (Opposite.op ⦋n⦌) (singSimplex σ) = σ :=
  Equiv.apply_symm_apply _ _

lemma singSimplex_surjective {n : ℕ} (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    singSimplex (X.toSSetObjEquiv (Opposite.op ⦋n⦌) x) = x :=
  Equiv.symm_apply_apply _ _

/-- The basis element of the singular chains attached to a singular simplex. -/
abbrev ιs {n : ℕ} (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    ModuleCat.of ℝ ℝ ⟶ (singChains X).X n :=
  (TopCat.toSSet.obj X).ιChainComplex x

lemma singChains_hom_ext {n : ℕ} {T : ModuleCat.{0} ℝ} {f g : (singChains X).X n ⟶ T}
    (h : ∀ x : (TopCat.toSSet.obj X) _⦋n⦌, ιs x ≫ f = ιs x ≫ g) : f = g :=
  SSet.chainComplex_hom_ext h

/-- The `i`-th face inclusion of standard topological simplices. -/
def faceMap {n : ℕ} (i : Fin (n + 2)) : C(Δt n, Δt (n + 1)) :=
  ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map _⟩

lemma delta_singSimplex {n : ℕ} (σ : C(Δt (n + 1), X)) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj X).δ i (singSimplex σ) = singSimplex (σ.comp (faceMap i)) := by
  apply (X.toSSetObjEquiv (Opposite.op ⦋n⦌)).injective
  rw [toSSetObjEquiv_singSimplex]
  ext t
  rw [TopCat.toSSetObjEquiv_δ_apply, toSSetObjEquiv_singSimplex]
  rfl

/-- The vertex tuple of the identity affine simplex. -/
def idTuple (n : ℕ) : Fin (n + 1) → Δt n := fun i => stdSimplex.vertex i

lemma affMap_idTuple (n : ℕ) : affMap (idTuple n) = ContinuousMap.id (Δt n) :=
  ContinuousMap.ext fun t => affPoint_id t

lemma affMap_idTuple_succAbove {n : ℕ} (i : Fin (n + 2)) :
    affMap (idTuple (n + 1) ∘ i.succAbove) = faceMap i :=
  ContinuousMap.ext fun t =>
    (affPoint_map (idTuple (n + 1)) i.succAbove t).trans (affPoint_id _)

/-! ### Realization of affine chains along a singular simplex -/

lemma ιa_realChain_singSimplex {n j : ℕ} (σ : C(Δt n, X)) (v : Fin (j + 1) → Δt n) :
    ιa v ≫ (realChain σ).f j = ιs (singSimplex (σ.comp (affMap v))) :=
  ιa_realChain σ v

lemma ιa_idTuple_realChain {n : ℕ} (σ : C(Δt n, X)) :
    ιa (idTuple n) ≫ (realChain σ).f n = ιs (singSimplex σ) := by
  rw [ιa_realChain_singSimplex, affMap_idTuple]
  rfl

/-- Realizing along a composite affine map is the pushforward followed by the
realization. -/
lemma realChain_comp_affMap {n k j : ℕ} (σ : C(Δt n, X)) (w : Fin (k + 1) → Δt n) :
    (realChain (σ.comp (affMap w))).f j = (pushChain w).f j ≫ (realChain σ).f j := by
  refine affChains_hom_ext fun v => ?_
  rw [ιa_realChain_singSimplex, ← Category.assoc, ιa_pushChain,
    ιa_realChain_singSimplex]
  congr 2
  ext t
  change σ (affPoint w (affPoint v t)) = σ (affPoint (fun a => affPoint w (v a)) t)
  rw [affPoint_comp]

/-! ### The subdivision operator on singular chains -/

/-- The barycentric subdivision of singular chains. -/
def sdSing (X : TopCat.{0}) (n : ℕ) : (singChains X).X n ⟶ (singChains X).X n :=
  Sigma.desc (fun x : (TopCat.toSSet.obj X) _⦋n⦌ =>
    ιa (idTuple n) ≫ sdHom n n ≫ (realChain (X.toSSetObjEquiv (Opposite.op ⦋n⦌) x)).f n)

/-- The chain homotopy operator on singular chains. -/
def tdSing (X : TopCat.{0}) (n : ℕ) : (singChains X).X n ⟶ (singChains X).X (n + 1) :=
  Sigma.desc (fun x : (TopCat.toSSet.obj X) _⦋n⦌ =>
    ιa (idTuple n) ≫ tdHom n n ≫ (realChain (X.toSSetObjEquiv (Opposite.op ⦋n⦌) x)).f (n + 1))

lemma ιs_sdSing {n : ℕ} (σ : C(Δt n, X)) :
    ιs (singSimplex σ) ≫ sdSing X n =
      ιa (idTuple n) ≫ sdHom n n ≫ (realChain σ).f n := by
  refine (Sigma.ι_desc _ (singSimplex σ)).trans ?_
  rw [toSSetObjEquiv_singSimplex]

lemma ιs_tdSing {n : ℕ} (σ : C(Δt n, X)) :
    ιs (singSimplex σ) ≫ tdSing X n =
      ιa (idTuple n) ≫ tdHom n n ≫ (realChain σ).f (n + 1) := by
  refine (Sigma.ι_desc _ (singSimplex σ)).trans ?_
  rw [toSSetObjEquiv_singSimplex]

lemma singChains_hom_ext' {n : ℕ} {T : ModuleCat.{0} ℝ} {f g : (singChains X).X n ⟶ T}
    (h : ∀ σ : C(Δt n, X), ιs (singSimplex σ) ≫ f = ιs (singSimplex σ) ≫ g) : f = g := by
  refine singChains_hom_ext fun x => ?_
  have := h (X.toSSetObjEquiv (Opposite.op ⦋n⦌) x)
  rwa [singSimplex_surjective] at this

/-- The subdivision is the identity on singular `0`-chains. -/
theorem sdSing_zero (X : TopCat.{0}) : sdSing X 0 = 𝟙 _ := by
  refine singChains_hom_ext' fun σ => ?_
  rw [ιs_sdSing, sdHom_zero, Category.id_comp, ιa_idTuple_realChain, Category.comp_id]

/-- The key face computation: the subdivision of the `i`-th face of the
identity simplex. -/
lemma ιa_face_sdHom_real {n : ℕ} (σ : C(Δt (n + 1), X)) (i : Fin (n + 2)) :
    ιa (idTuple n) ≫ sdHom n n ≫ (realChain (σ.comp (faceMap i))).f n =
      ιa (idTuple (n + 1) ∘ i.succAbove) ≫ sdHom (n + 1) n ≫
        (realChain σ).f n := by
  rw [← affMap_idTuple_succAbove i, realChain_comp_affMap,
    ← Category.assoc (sdHom n n), pushChain_sdHom, Category.assoc,
    ← Category.assoc (ιa (idTuple n)), ιa_pushChain]
  congr 2
  funext a
  exact affPoint_vertex _ a

/-- The analogous face computation for the homotopy operator. -/
lemma ιa_face_tdHom_real {n : ℕ} (σ : C(Δt (n + 1), X)) (i : Fin (n + 2)) :
    ιa (idTuple n) ≫ tdHom n n ≫ (realChain (σ.comp (faceMap i))).f (n + 1) =
      ιa (idTuple (n + 1) ∘ i.succAbove) ≫ tdHom (n + 1) n ≫
        (realChain σ).f (n + 1) := by
  rw [← affMap_idTuple_succAbove i, realChain_comp_affMap,
    ← Category.assoc (tdHom n n), pushChain_tdHom, Category.assoc,
    ← Category.assoc (ιa (idTuple n)), ιa_pushChain]
  congr 2
  funext a
  exact affPoint_vertex _ a

/-- **The subdivision operator is a chain map.** -/
theorem sdSing_d (X : TopCat.{0}) (n : ℕ) :
    sdSing X (n + 1) ≫ (singChains X).d (n + 1) n =
      (singChains X).d (n + 1) n ≫ sdSing X n := by
  refine singChains_hom_ext' fun σ => ?_
  have hL : ιs (singSimplex σ) ≫ sdSing X (n + 1) ≫ (singChains X).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℝ) ^ (i : ℕ) •
        (ιa (idTuple (n + 1) ∘ i.succAbove) ≫ sdHom (n + 1) n ≫
          (realChain σ).f n) := by
    rw [← Category.assoc, ιs_sdSing, Category.assoc, Category.assoc,
      (realChain σ).comm (n + 1) n, ← Category.assoc (sdHom (n + 1) (n + 1)), sdHom_d,
      Category.assoc, ← Category.assoc (ιa (idTuple (n + 1))), ιa_d,
      Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Linear.smul_comp]
  have hR : ιs (singSimplex σ) ≫ (singChains X).d (n + 1) n ≫ sdSing X n =
      ∑ i : Fin (n + 2), (-1 : ℝ) ^ (i : ℕ) •
        (ιa (idTuple (n + 1) ∘ i.succAbove) ≫ sdHom (n + 1) n ≫
          (realChain σ).f n) := by
    rw [← Category.assoc, (TopCat.toSSet.obj X).ιChainComplex_d (ModuleCat.of ℝ ℝ),
      Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ ((-1 : ℤ) ^ (i : ℕ))]
    push_cast
    rw [Linear.smul_comp]
    congr 1
    rw [show ((ConcreteCategory.hom ((TopCat.toSSet.obj X).δ i)) (singSimplex σ)) =
      (TopCat.toSSet.obj X).δ i (singSimplex σ) from rfl, delta_singSimplex, ιs_sdSing,
      ιa_face_sdHom_real]
  rw [hL, hR]

/-- **The homotopy identity in degree zero.** -/
theorem tdSing_d_zero (X : TopCat.{0}) :
    tdSing X 0 ≫ (singChains X).d 1 0 = 𝟙 _ - sdSing X 0 := by
  rw [sdSing_zero, sub_self]
  refine singChains_hom_ext' fun σ => ?_
  rw [← Category.assoc, ιs_tdSing, Category.assoc, Category.assoc,
    (realChain σ).comm 1 0, ← Category.assoc (tdHom 0 0), tdHom_d_zero,
    sdHom_zero, sub_self, Limits.zero_comp, comp_zero, comp_zero]

/-- **The homotopy identity `∂T + T∂ = 1 - S` on singular chains.** -/
theorem tdSing_d (X : TopCat.{0}) (n : ℕ) :
    tdSing X (n + 1) ≫ (singChains X).d (n + 2) (n + 1) +
        (singChains X).d (n + 1) n ≫ tdSing X n =
      𝟙 _ - sdSing X (n + 1) := by
  refine singChains_hom_ext' fun σ => ?_
  have hsum : ιa (idTuple (n + 1)) ≫ ((affChains (n + 1)).d (n + 1) n ≫ tdHom (n + 1) n) ≫
        (realChain σ).f (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℝ) ^ (i : ℕ) •
        (ιa (idTuple (n + 1) ∘ i.succAbove) ≫ tdHom (n + 1) n ≫ (realChain σ).f (n + 1)) := by
    simp only [Category.assoc]
    rw [← Category.assoc (ιa (idTuple (n + 1))) ((affChains (n + 1)).d (n + 1) n), ιa_d,
      Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Linear.smul_comp]
  have hB : ιs (singSimplex σ) ≫ (singChains X).d (n + 1) n ≫ tdSing X n =
      ∑ i : Fin (n + 2), (-1 : ℝ) ^ (i : ℕ) •
        (ιa (idTuple (n + 1) ∘ i.succAbove) ≫ tdHom (n + 1) n ≫ (realChain σ).f (n + 1)) := by
    rw [← Category.assoc, (TopCat.toSSet.obj X).ιChainComplex_d (ModuleCat.of ℝ ℝ),
      Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ ((-1 : ℤ) ^ (i : ℕ))]
    push_cast
    rw [Linear.smul_comp]
    congr 1
    rw [show ((ConcreteCategory.hom ((TopCat.toSSet.obj X).δ i)) (singSimplex σ)) =
      (TopCat.toSSet.obj X).δ i (singSimplex σ) from rfl, delta_singSimplex, ιs_tdSing,
      ιa_face_tdHom_real]
  have hA : ιs (singSimplex σ) ≫ tdSing X (n + 1) ≫ (singChains X).d (n + 2) (n + 1) =
      ιa (idTuple (n + 1)) ≫ (𝟙 _ - sdHom (n + 1) (n + 1)) ≫ (realChain σ).f (n + 1) -
        ιa (idTuple (n + 1)) ≫ ((affChains (n + 1)).d (n + 1) n ≫ tdHom (n + 1) n) ≫
          (realChain σ).f (n + 1) := by
    have h' : tdHom (n + 1) (n + 1) ≫ (affChains (n + 1)).d (n + 2) (n + 1) =
        𝟙 _ - sdHom (n + 1) (n + 1) - (affChains (n + 1)).d (n + 1) n ≫ tdHom (n + 1) n := by
      rw [← tdHom_d (n + 1) n]; abel
    rw [← Category.assoc, ιs_tdSing, Category.assoc, Category.assoc,
      (realChain σ).comm (n + 2) (n + 1), ← Category.assoc (tdHom (n + 1) (n + 1)), h',
      Preadditive.sub_comp, Preadditive.comp_sub]
  have hC : ιs (singSimplex σ) ≫ (𝟙 _ - sdSing X (n + 1)) =
      ιa (idTuple (n + 1)) ≫ (𝟙 _ - sdHom (n + 1) (n + 1)) ≫ (realChain σ).f (n + 1) := by
    rw [Preadditive.comp_sub, Category.comp_id, ιs_sdSing, Preadditive.sub_comp,
      Category.id_comp, Preadditive.comp_sub, ιa_idTuple_realChain]
  rw [Preadditive.comp_add, hA, hB, hC, hsum]
  abel

/-! ### Packaging as a chain map and a homotopy -/

/-- The barycentric subdivision as an endomorphism of the singular chain
complex. -/
def sdChainMap (X : TopCat.{0}) : singChains X ⟶ singChains X where
  f n := sdSing X n
  comm' i j hij := by
    obtain ⟨rfl⟩ : j + 1 = i := hij
    exact sdSing_d X j

/-- **The barycentric subdivision is chain homotopic to the identity.** -/
def sdHomotopy (X : TopCat.{0}) : Homotopy (sdChainMap X) (𝟙 (singChains X)) where
  hom i j := if h : j = i + 1 then (-tdSing X i) ≫ eqToHom (by rw [h]) else 0
  zero i j hij := by
    rw [dite_eq_right]
    intro h
    exact hij (by simp [ComplexShape.down_Rel, h])
  comm i := by
    cases i with
    | zero =>
      rw [dNext_eq_zero _ _ (by simp [ChainComplex.next_nat_zero, ComplexShape.down_Rel]),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel (0 + 1) 0 from rfl), zero_add]
      change sdSing X 0 = ((if h : (0 : ℕ) + 1 = 0 + 1 then (-tdSing X 0) ≫ eqToHom (by rw [h])
        else 0) ≫ (singChains X).d (0 + 1) 0) + 𝟙 _
      rw [dite_eq_left rfl, eqToHom_refl, Category.comp_id, Preadditive.neg_comp,
        tdSing_d_zero, sdSing_zero, sub_self, neg_zero, zero_add]
    | succ m =>
      rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (m + 1) m from rfl),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel (m + 1 + 1) (m + 1) from rfl)]
      change sdSing X (m + 1) = ((singChains X).d (m + 1) m ≫
          (if h : m + 1 = m + 1 then (-tdSing X m) ≫ eqToHom (by rw [h]) else 0)) +
        ((if h : m + 1 + 1 = m + 1 + 1 then (-tdSing X (m + 1)) ≫ eqToHom (by rw [h])
          else 0) ≫ (singChains X).d (m + 1 + 1) (m + 1)) + 𝟙 _
      rw [dite_eq_left rfl, dite_eq_left rfl, eqToHom_refl, eqToHom_refl, Category.comp_id,
        Category.comp_id, Preadditive.comp_neg, Preadditive.neg_comp]
      have h : tdSing X (m + 1) ≫ (singChains X).d (m + 1 + 1) (m + 1) +
          (singChains X).d (m + 1) m ≫ tdSing X m = 𝟙 _ - sdSing X (m + 1) := tdSing_d X m
      have hsd : sdSing X (m + 1) = 𝟙 _ -
          (tdSing X (m + 1) ≫ (singChains X).d (m + 1 + 1) (m + 1) +
            (singChains X).d (m + 1) m ≫ tdSing X m) := by
        rw [h]; abel
      rw [hsd]
      abel

/-- The subdivision induces the identity on singular homology. -/
theorem homologyMap_sdChainMap (X : TopCat.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (sdChainMap X) n = 𝟙 _ := by
  rw [(sdHomotopy X).homologyMap_eq, HomologicalComplex.homologyMap_id]

/-! ### Naturality in the space -/

/-- The chain map of singular chains induced by a continuous map. -/
abbrev singChainsMap (f : X ⟶ Y) : singChains X ⟶ singChains Y :=
  SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℝ ℝ)

lemma toSSet_map_singSimplex {n : ℕ} (f : X ⟶ Y) (σ : C(Δt n, X)) :
    (ConcreteCategory.hom ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌))) (singSimplex σ) =
      singSimplex ((ConcreteCategory.hom f).comp σ) := rfl

lemma ιs_singChainsMap {n : ℕ} (f : X ⟶ Y) (σ : C(Δt n, X)) :
    ιs (singSimplex σ) ≫ (singChainsMap f).f n =
      ιs (singSimplex ((ConcreteCategory.hom f).comp σ)) := by
  rw [SSet.ι_chainComplexMap_f, toSSet_map_singSimplex]

lemma realChain_singChainsMap {n j : ℕ} (f : X ⟶ Y) (σ : C(Δt n, X)) :
    (realChain σ).f j ≫ (singChainsMap f).f j =
      (realChain ((ConcreteCategory.hom f).comp σ)).f j := by
  refine affChains_hom_ext fun v => ?_
  rw [← Category.assoc, ιa_realChain_singSimplex, ιs_singChainsMap,
    ιa_realChain_singSimplex]
  rfl

/-- **Naturality of the subdivision operator in the space.** -/
theorem sdSing_naturality (f : X ⟶ Y) (n : ℕ) :
    sdSing X n ≫ (singChainsMap f).f n = (singChainsMap f).f n ≫ sdSing Y n := by
  refine singChains_hom_ext' fun σ => ?_
  have hL : ιs (singSimplex σ) ≫ sdSing X n ≫ (singChainsMap f).f n =
      ιa (idTuple n) ≫ sdHom n n ≫
        (realChain ((ConcreteCategory.hom f).comp σ)).f n := by
    rw [← Category.assoc, ιs_sdSing]
    simp only [Category.assoc]
    rw [realChain_singChainsMap]
  have hR : ιs (singSimplex σ) ≫ (singChainsMap f).f n ≫ sdSing Y n =
      ιa (idTuple n) ≫ sdHom n n ≫
        (realChain ((ConcreteCategory.hom f).comp σ)).f n := by
    rw [← Category.assoc, ιs_singChainsMap, ιs_sdSing]
  rw [hL, hR]

/-- **Naturality of the homotopy operator in the space.** -/
theorem tdSing_naturality (f : X ⟶ Y) (n : ℕ) :
    tdSing X n ≫ (singChainsMap f).f (n + 1) = (singChainsMap f).f n ≫ tdSing Y n := by
  refine singChains_hom_ext' fun σ => ?_
  have hL : ιs (singSimplex σ) ≫ tdSing X n ≫ (singChainsMap f).f (n + 1) =
      ιa (idTuple n) ≫ tdHom n n ≫
        (realChain ((ConcreteCategory.hom f).comp σ)).f (n + 1) := by
    rw [← Category.assoc, ιs_tdSing]
    simp only [Category.assoc]
    rw [realChain_singChainsMap]
  have hR : ιs (singSimplex σ) ≫ (singChainsMap f).f n ≫ tdSing Y n =
      ιa (idTuple n) ≫ tdHom n n ≫
        (realChain ((ConcreteCategory.hom f).comp σ)).f (n + 1) := by
    rw [← Category.assoc, ιs_singChainsMap, ιs_tdSing]
  rw [hL, hR]

end AffChain

end AffineTverberg
