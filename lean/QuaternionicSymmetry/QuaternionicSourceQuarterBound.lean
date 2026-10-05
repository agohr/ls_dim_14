import QuaternionicSymmetry.QuaternionicSourceIntegralBound
import QuaternionicSymmetry.ManifoldQuaternionicQuarterVolume

/-! Convert an actual scalar-density reserve into a bound by the canonical
top power of the analytic quarter-Pontryagin representative. -/
namespace QuaternionicSymmetry.QuaternionicSourceQuarterBound
open QuaternionicSourceIntegralBound QuaternionicClosedSourceNumbers
open ManifoldQuaternionicCanonicalIntegration
open ManifoldQuaternionicQuarterVolume ManifoldQuaternionicVolumeCoefficient
open ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicKSWScalarInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem sourcePolynomialNumber_quarter_lower_bound
    (t : ℝ) (k : ℕ) (hdim : 4*(k+1) = Module.finrank ℝ E)
    (P : DimensionThirteenFourteenDensity.P)
    (hP : MvPolynomial.IsWeightedHomogeneous
      ManifoldSevenVariableClosedEvaluation.slotGrade P (k+1))
    (reserve : ℝ) (hsp : KSWSp1CurvatureFormula S Q D)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (hbound : ∀ x : M,
      reserve * (t ^ 2 / Real.pi) ^ (2*(k+1)) ≤
        scalarDensity Q (sourceTopForm S Q D t k hdim P hP).val x) :
    reserve * integral Q (quarterTop Q D (k+1) hdim) ≤
      sourcePolynomialNumber S Q D t k hdim P := by
  rw [quarterTop_integral_normalized Q D S hsp t ht (k+1) hdim]
  convert sourcePolynomialNumber_lower_bound S Q D t k hdim P hP
    (reserve * (t ^ 2 / Real.pi) ^ (2*(k+1))) hbound using 1
  ring

end
end QuaternionicSymmetry.QuaternionicSourceQuarterBound
