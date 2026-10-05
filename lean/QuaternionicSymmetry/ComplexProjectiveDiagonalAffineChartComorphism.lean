import QuaternionicSymmetry.ComplexProjectiveDiagonalAlgebraicCharts

/-! A literal ℂ-algebra comorphism for each invariant standard affine
projective chart. Its target is the polynomial ring over the Laurent torus
coordinate ring, the algebraic coordinate ring of torus × affine space. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalAffineChartComorphism

open ComplexProjectiveDiagonalAlgebraicCharts
open TorusLaurentRepresentation
noncomputable section

variable {r d : ℕ}

def chartActionComorphism
    (μ : Fin (d + 1) → Fin r → ℤ) (i : Fin (d + 1)) :
    MvPolynomial (Fin d) ℂ →ₐ[ℂ]
      MvPolynomial (Fin d) (TorusCoordinateRing r) :=
  MvPolynomial.aeval (regularChartCoordinate μ i)

theorem chartActionComorphism_X
    (μ : Fin (d + 1) → Fin r → ℤ)
    (i : Fin (d + 1)) (k : Fin d) :
    chartActionComorphism μ i (MvPolynomial.X k) =
      regularChartCoordinate μ i k := by
  simp [chartActionComorphism]

theorem eval_chartActionComorphism
    (μ : Fin (d + 1) → Fin r → ℤ)
    (i : Fin (d + 1)) (z : ComplexTorus r)
    (w : Fin d → ℂ) (p : MvPolynomial (Fin d) ℂ) :
    MvPolynomial.eval₂ (evalTorus z) w (chartActionComorphism μ i p) =
      MvPolynomial.eval (ComplexProjectiveDiagonalHolomorphic.chartDiagonal μ z i w) p := by
  have h : (MvPolynomial.eval₂Hom (evalTorus z) w).comp
      (chartActionComorphism μ i).toRingHom =
      MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (ComplexProjectiveDiagonalHolomorphic.chartDiagonal μ z i w) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [chartActionComorphism, evalTorus, exponentCharacter,
        complexWeightCharacter]
    · intro k
      simp [chartActionComorphism_X, eval_regularChartCoordinate]
  exact congrArg (fun f : MvPolynomial (Fin d) ℂ →+* ℂ => f p) h

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalAffineChartComorphism
