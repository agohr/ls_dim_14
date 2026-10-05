import QuaternionicSymmetry.ProjectionCubicSchurBridge
import QuaternionicSymmetry.QuaternionicGeneralCubicPositivity
import QuaternionicSymmetry.QuaternionicTraceConventionBridge

/-! Pointwise signs for the actual printed cubic projection polynomials in
the power-sum convention p_j = tr((-X²)^j)/2. -/
namespace QuaternionicSymmetry.PrintedProjectionCubicPositivity

open Module QuaternionicFundamental QuaternionicTracePositivity MatrixTracePolynomial
  QuaternionicTraceConventionBridge

noncomputable section
variable {ι κ β V : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  [Fintype β] [DecidableEq β] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [Fintype ι] [DecidableEq β] [FiniteDimensional ℝ V] in
def densityValues (Q : QuaternionicStructure V) {ι : Type*} [Fintype ι]
    (c : Basis ι ℝ V) (B : β → Matrix κ κ ℂ) (η : β → E V) : Fin 6 → CE V :=
  ![embed (V := V) (form Q c),
    embed (V := V) (signedTracePower (complexifiedMatrix B η) 1),
    embed (V := V) (signedTracePower (complexifiedMatrix B η) 2),
    embed (V := V) (signedTracePower (complexifiedMatrix B η) 3),
    embed (V := V) (signedTracePower (complexifiedMatrix B η) 4),
    embed (V := V) (signedTracePower (complexifiedMatrix B η) 5)]

theorem m3_mixed_in_positive_ray (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (ell : ℕ) (hell : ell ≤ Fintype.card κ) (hr : 3 ≤ Fintype.card κ)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 3 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (MvPolynomial.aeval (densityValues Q c B η)
        (ElevenTwelveProjectionCertificates.m3 (Fintype.card κ) ell) *
        embed (V := V) (form Q c) ^ (Q.quaternionicDimension - 3)) := by
  have hr' : (2 : ℚ) < Fintype.card κ := by exact_mod_cast (by omega : 2 < Fintype.card κ)
  rw [ProjectionCubicSchurBridge.m3_eval _ _ hr']
  have h := QuaternionicGeneralCubicPositivity.rank_cubic_mixed_in_positive_ray
    Q c ell hell hr B hB η hη hk
  simp only [tracePower_eq_twice_halfTrace B hB η] at h
  simpa [densityValues, Matrix.cons_val_two, Matrix.cons_val_three] using h

end
end QuaternionicSymmetry.PrintedProjectionCubicPositivity
