import QuaternionicSymmetry.QuarticOrbitalFiniteBridge
import QuaternionicSymmetry.OrbitalPointwisePolynomialSign

/-! Pointwise signs of the printed dimension-eleven and dimension-twelve
quartic orbital generators, with the literal scalar Haar source as the only
literature premise. The matrix and two-form coefficients are supplied local
data; their construction from PQK curvature is a separate obligation. -/

namespace QuaternionicSymmetry.PrintedQuarticOrbitalPositivity

open Module QuaternionicFundamental HyperholomorphicExterior MatrixTracePolynomial
  OrbitalInterleavedBridge QuarticOrbitalFiniteBridge

noncomputable section

variable {β ι V : Type*} [Fintype β] [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem orbital11_mem_positiveRay
    (hsource : LiteralInterleavedFormula) (a : List ℕ) (ha : a.length ≤ 11)
    (A : β → Matrix (Fin 11 ⊕ Fin 11) (Fin 11 ⊕ Fin 11) ℂ)
    (hA : ∀ b, QuaternionicMatrixModel.HermitianAntiSelfDual (A b))
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V) (η : β → E V)
    (hη : ∀ b, η b ∈ formSpace Q c) (hkQ : 4 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (topForm Q c)
      (MvPolynomial.aeval ![signedTracePower (complexifiedMatrix A η) 1,
        signedTracePower (complexifiedMatrix A η) 2,
        signedTracePower (complexifiedMatrix A η) 3,
        signedTracePower (complexifiedMatrix A η) 4]
        (QuarticOrbitalEleven.orbital a) *
        QuaternionicFundamental.form Q c ^ (Q.quaternionicDimension - 4)) := by
  have h := OrbitalPointwisePolynomialSign.orbital_mem_positiveRay
    hsource 11 4 (by decide) (by decide) a ha A hA Q c η hη hkQ
  rw [orbital11_eval] at h
  exact h

theorem orbital12_mem_positiveRay
    (hsource : LiteralInterleavedFormula) (a : List ℕ) (ha : a.length ≤ 12)
    (A : β → Matrix (Fin 12 ⊕ Fin 12) (Fin 12 ⊕ Fin 12) ℂ)
    (hA : ∀ b, QuaternionicMatrixModel.HermitianAntiSelfDual (A b))
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V) (η : β → E V)
    (hη : ∀ b, η b ∈ formSpace Q c) (hkQ : 4 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (topForm Q c)
      (MvPolynomial.aeval ![signedTracePower (complexifiedMatrix A η) 1,
        signedTracePower (complexifiedMatrix A η) 2,
        signedTracePower (complexifiedMatrix A η) 3,
        signedTracePower (complexifiedMatrix A η) 4]
        (QuarticOrbitalTwelve.orbital a) *
        QuaternionicFundamental.form Q c ^ (Q.quaternionicDimension - 4)) := by
  have h := OrbitalPointwisePolynomialSign.orbital_mem_positiveRay
    hsource 12 4 (by decide) (by decide) a ha A hA Q c η hη hkQ
  rw [orbital12_eval] at h
  exact h

end
end QuaternionicSymmetry.PrintedQuarticOrbitalPositivity
