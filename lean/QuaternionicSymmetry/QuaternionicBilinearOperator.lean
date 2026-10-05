import QuaternionicSymmetry.QuaternionicCurvatureCoefficientForms

/-! An invariant alternating bilinear form has a genuine skew
quaternion-linear Riesz operator. -/
namespace QuaternionicSymmetry.QuaternionicBilinearOperator
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (B : E →L[ℝ] E →L[ℝ] ℝ)

def operator : E →L[ℝ] E := InnerProductSpace.continuousLinearMapOfBilin B

theorem operator_inner (u v : E) : inner ℝ (operator B u) v = B u v :=
  InnerProductSpace.continuousLinearMapOfBilin_apply B u v

theorem operator_skew (hanti : ∀ u v, B u v = -B v u) (u v : E) :
    inner ℝ (operator B u) v = -inner ℝ u (operator B v) := by
  rw [operator_inner, real_inner_comm, operator_inner, hanti]

theorem operator_commutes (J : E ≃ₗᵢ[ℝ] E) (hJ2 : ∀ u, J (J u) = -u)
    (hJskew : ∀ u v, inner ℝ (J u) v = -inner ℝ u (J v))
    (hinv : ∀ u v, B (J u) (J v) = B u v) (u : E) :
    operator B (J u) = J (operator B u) := by
  apply ext_inner_right ℝ
  intro v
  rw [operator_inner, hJskew, operator_inner]
  have h := hinv u (J v)
  rw [hJ2, map_neg] at h
  exact neg_eq_iff_eq_neg.mp h

theorem operator_mem_skewCentralizer (S : QuaternionicStructure E)
    (hanti : ∀ u v, B u v = -B v u)
    (hI : ∀ u v, B (S.I u) (S.I v) = B u v)
    (hJ : ∀ u v, B (S.J u) (S.J v) = B u v) :
    (operator B).toLinearMap ∈ S.skewCentralizer := by
  apply (S.mem_skewCentralizer_iff _).mpr
  exact ⟨operator_skew B hanti, operator_commutes B S.I S.I_sq S.I_skew hI,
    operator_commutes B S.J S.J_sq S.J_skew hJ⟩

end
end QuaternionicSymmetry.QuaternionicBilinearOperator
