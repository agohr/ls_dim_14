import QuaternionicSymmetry.DimensionThirteenFourteenDensity

/-! Evaluation of the six-variable density inclusion over arbitrary
coefficient algebras. -/
namespace QuaternionicSymmetry.SixSevenPolynomialEvaluation
open MvPolynomial DimensionThirteenFourteenDensity
noncomputable section
variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem aeval_lift (v : Fin 7 → R) (P : DimensionElevenTwelveDensity.P) :
    aeval v (lift P) = aeval (fun i : Fin 6 => v i.castSucc) P := by
  unfold lift
  rw [MvPolynomial.comp_aeval_apply]
  have hv : (fun i : Fin 6 => aeval v (![u, p1, p2, p3, p4, p5] i)) =
      (fun i : Fin 6 => v i.castSucc) := by
    funext i
    fin_cases i <;> simp [u, p1, p2, p3, p4, p5]
  rw [hv]

end
end QuaternionicSymmetry.SixSevenPolynomialEvaluation
