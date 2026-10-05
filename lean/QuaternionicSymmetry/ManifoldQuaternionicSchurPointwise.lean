import QuaternionicSymmetry.ManifoldQuaternionicEinsteinDerivative

/-! Schur's finite contraction applied to the actual second Bianchi tensor
and the differentiated local Einstein equation. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicSchurPointwise
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicCoordinateMetricField
open ManifoldQuaternionicEinsteinFactor
open ManifoldQuaternionicEinsteinDerivative
open ManifoldQuaternionicSchurTensor
open ManifoldQuaternionicSchurRicciDerivative
open ManifoldQuaternionicKSWScalarInput
open ManifoldQuaternionicKSWEq38Input
open QuaternionicSymmetry.AlgebraicSchurContraction
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem schurTensor_einsteinDerivative
    (S : QuaternionicStructure E)
    (hdecomp : KSWEq38Decomposition S Q D)
    (p : M) (c : E) (hc : c ≠ 0) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    EinsteinDerivative (schurTensor Q D p y hy)
      (fun a => fderiv ℝ (einsteinFactor Q D p c) y
        (coordinateOrthonormalBasis Q p y hy a)) := by
  intro a v w
  rw [schurTensor_covariantRicci Q D p y hy a v w]
  rw [coordinateRicci_covariant_einsteinFactor Q D S hdecomp
    p c hc y hy (coordinateOrthonormalBasis Q p y hy a)
    (coordinateOrthonormalBasis Q p y hy v)
    (coordinateOrthonormalBasis Q p y hy w)]
  rw [← coordinateMetricField_apply Q p y hy,
    coordinateOrthonormalBasis_metric Q p y hy v w]

theorem einsteinFactor_fderiv_basis_zero
    (S : QuaternionicStructure E)
    (hdecomp : KSWEq38Decomposition S Q D)
    (p : M) (c : E) (hc : c ≠ 0) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (hcard : 3 ≤ Module.finrank ℝ E)
    (a : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (einsteinFactor Q D p c) y
      (coordinateOrthonormalBasis Q p y hy a) = 0 := by
  apply schur_derivative_zero (schurTensor Q D p y hy) _
    (by simpa using hcard)
    (schurTensor_pairSymmetric Q D p y hy)
    (schurTensor_secondBianchi Q D p y hy)
    (schurTensor_einsteinDerivative Q D S hdecomp p c hc y hy) a

end
end QuaternionicSymmetry.ManifoldQuaternionicSchurPointwise
