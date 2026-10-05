import QuaternionicSymmetry.QuaternionicStructure
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Pair symmetry and quaternion-linear curvature values force each real
coefficient two-form to come from a skew quaternion-linear endomorphism. -/
namespace QuaternionicSymmetry.QuaternionicCurvatureCoefficientForms
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance : NormedSpace ℝ E := inferInstance
variable (R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)

omit [FiniteDimensional ℝ E] in
theorem invariant_of_pair_symmetry (J : E ≃ₗᵢ[ℝ] E)
    (hpair : ∀ u v w z, inner ℝ (R u v w) z = inner ℝ (R w z u) v)
    (hJ : ∀ u v w, R u v (J w) = J (R u v w)) (u v : E) :
    R (J u) (J v) = R u v := by
  apply ContinuousLinearMap.ext
  intro w
  apply ext_inner_right ℝ
  intro z
  rw [hpair, hJ, J.inner_map_map, hpair w z]

def coefficientBilinear (L : (E →L[ℝ] E) →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) ℝ) L).comp R

def coefficientOperator (L : (E →L[ℝ] E) →L[ℝ] ℝ) : E →L[ℝ] E :=
  InnerProductSpace.continuousLinearMapOfBilin (coefficientBilinear R L)

theorem coefficientOperator_inner (L : (E →L[ℝ] E) →L[ℝ] ℝ) (u v : E) :
    inner ℝ (coefficientOperator R L u) v = L (R u v) :=
  InnerProductSpace.continuousLinearMapOfBilin_apply _ _ _

theorem coefficientOperator_skew (L : (E →L[ℝ] E) →L[ℝ] ℝ)
    (hanti : ∀ u v, R u v = -R v u) (u v : E) :
    inner ℝ (coefficientOperator R L u) v = -inner ℝ u (coefficientOperator R L v) := by
  rw [coefficientOperator_inner, real_inner_comm, coefficientOperator_inner,
    hanti, map_neg]

theorem coefficientOperator_commutes (L : (E →L[ℝ] E) →L[ℝ] ℝ)
    (J : E ≃ₗᵢ[ℝ] E) (hJ2 : ∀ u, J (J u) = -u)
    (hJskew : ∀ u v, inner ℝ (J u) v = -inner ℝ u (J v))
    (hinv : ∀ u v, R (J u) (J v) = R u v) (u : E) :
    coefficientOperator R L (J u) = J (coefficientOperator R L u) := by
  apply ext_inner_right ℝ
  intro v
  rw [coefficientOperator_inner, hJskew, coefficientOperator_inner]
  have h := hinv u (J v)
  rw [hJ2, map_neg] at h
  have h' : R (J u) v = -R u (J v) := by
    exact neg_eq_iff_eq_neg.mp h
  rw [h', map_neg]

theorem coefficientOperator_mem_skewCentralizer (S : QuaternionicStructure E)
    (L : (E →L[ℝ] E) →L[ℝ] ℝ)
    (hanti : ∀ u v, R u v = -R v u)
    (hpair : ∀ u v w z, inner ℝ (R u v w) z = inner ℝ (R w z u) v)
    (hI : ∀ u v w, R u v (S.I w) = S.I (R u v w))
    (hJ : ∀ u v w, R u v (S.J w) = S.J (R u v w)) :
    (coefficientOperator R L).toLinearMap ∈ S.skewCentralizer := by
  apply (S.mem_skewCentralizer_iff _).mpr
  exact ⟨coefficientOperator_skew R L hanti,
    coefficientOperator_commutes R L S.I S.I_sq S.I_skew
      (invariant_of_pair_symmetry R S.I hpair hI),
    coefficientOperator_commutes R L S.J S.J_sq S.J_skew
      (invariant_of_pair_symmetry R S.J hpair hJ)⟩

end
end QuaternionicSymmetry.QuaternionicCurvatureCoefficientForms
