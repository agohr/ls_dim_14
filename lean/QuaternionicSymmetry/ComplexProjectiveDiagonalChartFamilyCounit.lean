import QuaternionicSymmetry.ComplexProjectiveDiagonalChartFamilySpecialization

/-! The actual regular affine-chart quotient family specializes to the
identity at the complex-torus unit. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalChartFamilyCounit

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalAffineChartComorphism
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalChartQuotientFamily
open ComplexProjectiveDiagonalChartFamilySpecialization
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem chartFamily_counit
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    (specializeChartQuotient (r := r) A i 1).comp
        (chartQuotientFamilyHom μ A hA hCompact i) =
      RingHom.id (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i) := by
  apply RingHom.ext
  intro q
  induction q using Quotient.inductionOn' with
  | _ p =>
    let qmk := Ideal.Quotient.mk (chartVanishingIdeal A i)
    change specializeChartQuotient A i 1
      (chartQuotientFamilyHom μ A hA hCompact i (qmk p)) = qmk p
    have hpoly :
        ((specializeChartQuotient A i 1).comp
          (chartQuotientFamilyHom μ A hA hCompact i)).comp qmk = qmk := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [qmk, specializeChartQuotient, chartQuotientFamilyHom,
          chartActionComorphism, evalTorus]
      · intro k
        simp [qmk, specializeChartQuotient, chartQuotientFamilyHom,
          chartActionComorphism_X, regularChartCoordinate,
          evalTorus_laurentMonomial, complexWeightCharacter]
    exact congrArg (fun f : MvPolynomial (Fin d) ℂ →+* _ => f p) hpoly

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalChartFamilyCounit
