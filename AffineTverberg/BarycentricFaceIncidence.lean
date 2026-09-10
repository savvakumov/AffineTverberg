import AffineTverberg.BarycentricIncidenceHomology
import AffineTverberg.Incidence
import Mathlib.Analysis.Convex.Exposed

set_option linter.style.header false

/-!
# Barycentric coordinates for the actual exposed-face incidence space

Membership of a convex combination in an exposed face is precisely the
condition that all its positive-weight vertices lie in that face. This
identifies the geometric incidence space with the support-restricted model.
-/

noncomputable section

open Set

namespace AffineTverberg.Simplicial

variable {V E : Type*} [Fintype V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A convex combination lies in an exposed face exactly when every vertex
with nonzero weight lies in that face. Zero-weight vertices are irrelevant. -/
theorem barycentricEvaluation_mem_exposed_iff
    {Q F : Set E} (hQ : Convex ℝ Q) (hF : IsExposed ℝ Q F)
    (p : V → E) {x : V → ℝ} (hx0 : ∀ v, 0 ≤ x v) (hx1 : ∑ v, x v = 1)
    (hp : ∀ v, x v ≠ 0 → p v ∈ Q) :
    barycentricEvaluation p x ∈ F ↔ ∀ v, p v ∉ F → x v = 0 := by
  classical
  constructor
  · intro hz
    obtain ⟨l, hl⟩ := hF ⟨_, hz⟩
    have hz' : barycentricEvaluation p x ∈ Q ∧
        ∀ y ∈ Q, l y ≤ l (barycentricEvaluation p x) := by rwa [hl] at hz
    let M := l (barycentricEvaluation p x)
    have hnonneg : ∀ v, 0 ≤ x v * (M - l (p v)) := by
      intro v
      by_cases hv : x v = 0
      · simp [hv]
      · exact mul_nonneg (hx0 v) (sub_nonneg.mpr (hz'.2 _ (hp v hv)))
    have hsum : ∑ v, x v * (M - l (p v)) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hx1, one_mul]
      have he : l (barycentricEvaluation p x) = ∑ v, x v * l (p v) := by
        simp [barycentricEvaluation, map_sum, map_smul]
      exact sub_eq_zero.mpr he
    have hterm : ∀ v, x v * (M - l (p v)) = 0 := fun v ↦
      (Finset.sum_eq_zero_iff_of_nonneg (fun v _ ↦ hnonneg v)).mp hsum v (Finset.mem_univ v)
    intro v hv
    by_contra hxv
    have heq : l (p v) = M := by
      have := (mul_eq_zero.mp (hterm v)).resolve_left hxv
      linarith
    apply hv
    rw [hl]
    exact ⟨hp v hxv, fun y hy ↦ (hz'.2 y hy).trans_eq heq.symm⟩
  · intro h
    let s := Finset.univ.filter (fun v ↦ x v ≠ 0)
    have hsum : ∑ v ∈ s, x v = 1 := by
      rw [Finset.sum_subset (Finset.subset_univ s)]
      · exact hx1
      · intro v _ hv
        simpa [s] using hv
    have heval : barycentricEvaluation p x = ∑ v ∈ s, x v • p v := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro v _ hv
      have hxv : x v = 0 := by simpa [s] using hv
      simp [hxv]
    rw [heval]
    apply (hF.convex hQ).sum_mem (fun v _ ↦ hx0 v) hsum
    intro v hv
    by_contra hpv
    exact (Finset.mem_filter.mp hv).2 (h v hpv)

section Incidence

variable {T ι : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
  {K : Finset (Finset V)} {D : Set E}
  (G : ι → Set E) (Φ : E → T) (J : ι → Finset V)

/-- The sphere parameters nonnegative on the image of each geometric face. -/
def faceParameterFamily (i : ι) : Set (DualUnitSphere T) :=
  {y | ∀ z ∈ G i, 0 ≤ (y.val) (Φ z)}

variable (e : ↥(barycentricCarrier K) ≃ₜ D)
  (hface : ∀ i (x : ↥(barycentricCarrier K)),
    (e x).val ∈ G i ↔ ∀ v, v ∉ J i → x.val v = 0)

/-- The support model is homeomorphic to the geometric incidence space,
with the same base point and exactly the same unit functional. -/
def faceIncidenceHomeomorph :
    ↥(BarycentricIncidence.carrier K J (faceParameterFamily G Φ)) ≃ₜ
      FaceIncidenceSpace D G Φ where
  toFun z := ⟨(e ⟨z.val.1, z.property.1⟩, z.val.2.val), z.val.2.property, by
    obtain ⟨i, hi, hy⟩ := z.property.2
    exact ⟨i, (hface i _).mpr hi, hy⟩⟩
  invFun z := ⟨((e.symm z.val.1).val, ⟨z.val.2, z.property.1⟩),
    (e.symm z.val.1).property, by
      obtain ⟨i, hi, hy⟩ := z.property.2
      refine ⟨i, (hface i _).mp ?_, hy⟩
      simpa using hi⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val (e.symm_apply_apply ⟨z.val.1, z.property.1⟩)
    · rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact e.apply_symm_apply z.val.1
    · rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

omit [NormedSpace ℝ E] in
/-- The homeomorphism respects the actual first projections. -/
theorem faceIncidenceHomeomorph_projection
    (z : ↥(BarycentricIncidence.carrier K J (faceParameterFamily G Φ))) :
    faceIncidenceProjection (faceIncidenceHomeomorph G Φ J e hface z) =
      e (BarycentricIncidence.projection K J (faceParameterFamily G Φ) z) := rfl

/-- The same model identification on the genuine fiber of the projection. -/
def faceIncidenceModelFiberHomeomorph (x : ↥(barycentricCarrier K)) :
    ↥((BarycentricIncidence.projection K J (faceParameterFamily G Φ)) ⁻¹' {x}) ≃ₜ
      FaceIncidenceFiber D G Φ (e x) :=
  (faceIncidenceHomeomorph G Φ J e hface).subtype (fun z ↦ by
    change BarycentricIncidence.projection K J (faceParameterFamily G Φ) z = x ↔
      faceIncidenceProjection (faceIncidenceHomeomorph G Φ J e hface z) = e x
    rw [faceIncidenceHomeomorph_projection]
    exact e.injective.eq_iff.symm)

end Incidence

section Homology

open CategoryTheory HomologicalComplex AffChain

variable {V E T ι : Type} [Fintype V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  {K : Finset (Finset V)} {D : Set E}
  (G : ι → Set E) (Φ : E → T) (J : ι → Finset V)
  (e : ↥(barycentricCarrier K) ≃ₜ D)
  (hface : ∀ i (x : ↥(barycentricCarrier K)),
    (e x).val ∈ G i ↔ ∀ v, v ∉ J i → x.val v = 0)

include J e hface in
omit [NormedSpace ℝ E] in
/-- The actual geometric first projection induces singular homology
isomorphisms whenever its face-support model and contractible fibers are
supplied. The proof uses the direct open-star contractions and finite descent. -/
theorem quasiIso_faceIncidenceProjection_of_model (hK : FaceClosed K)
    (hfib : ∀ x : D, ContractibleSpace (FaceIncidenceFiber D G Φ x)) :
    QuasiIso (singChainsMap (TopCat.ofHom
      (⟨faceIncidenceProjection, continuous_faceIncidenceProjection⟩ :
        C(FaceIncidenceSpace D G Φ, D)))) := by
  have hmodel := BarycentricIncidence.quasiIso_projection (J := J)
    (C := faceParameterFamily G Φ) hK (fun x ↦ by
      have := hfib (e x)
      exact (faceIncidenceModelFiberHomeomorph G Φ J e hface x).contractibleSpace)
  let f := TopCat.ofHom (BarycentricIncidence.projection K J (faceParameterFamily G Φ))
  let g := TopCat.ofHom
    (⟨faceIncidenceProjection, continuous_faceIncidenceProjection⟩ :
      C(FaceIncidenceSpace D G Φ, D))
  exact (quasiIso_singChainsMap_iff_of_iso f g
    (TopCat.isoOfHomeo (faceIncidenceHomeomorph G Φ J e hface))
    (TopCat.isoOfHomeo e) (by
      ext z
      exact congrArg Subtype.val
        (faceIncidenceHomeomorph_projection G Φ J e hface z))).mp hmodel

end Homology

end AffineTverberg.Simplicial
