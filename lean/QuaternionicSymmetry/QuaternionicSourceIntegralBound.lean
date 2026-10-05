import QuaternionicSymmetry.QuaternionicClosedSourceNumbers
import QuaternionicSymmetry.ManifoldQuaternionicIntegralLowerBound

/-! A reusable canonical integration step for actual closed source
representatives. The hypothesis is an intrinsic pointwise scalar-density
estimate; the conclusion is a characteristic-number estimate using the
constructed de Rham class and canonical measure. -/

namespace QuaternionicSymmetry.QuaternionicSourceIntegralBound
open QuaternionicClosedSourceNumbers QuaternionicClosedSourceGenerators
open ManifoldClosedPolynomialRepresentative ManifoldQuaternionicCanonicalIntegration
open ManifoldQuaternionicIntegralLowerBound ManifoldQuaternionicVolumeCoefficient
open ManifoldQuaternionicVolume
open ManifoldQuaternionicDensityIntegration
open ManifoldEvenClosedAlgebra
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

def sourceTopForm (t : ℝ) (k : ℕ)
    (hdim : 4*(k+1) = Module.finrank ℝ E)
    (P : DimensionThirteenFourteenDensity.P)
    (hP : MvPolynomial.IsWeightedHomogeneous
      ManifoldSevenVariableClosedEvaluation.slotGrade P (k+1)) :
    SmoothTopForms (E := E) (M := M) :=
  ⟨ManifoldDeRhamWedge.castForm (by omega)
      (closedRepresentative (generators S Q D t) P hP).val.val,
    ManifoldDeRhamWedge.chartSmooth_castForm _ _
      (closedRepresentative (generators S Q D t) P hP).val.property⟩

theorem sourcePolynomialNumber_eq_sourceTopIntegral (t : ℝ) (k : ℕ)
    (hdim : 4*(k+1) = Module.finrank ℝ E)
    (P : DimensionThirteenFourteenDensity.P)
    (hP : MvPolynomial.IsWeightedHomogeneous
      ManifoldSevenVariableClosedEvaluation.slotGrade P (k+1)) :
    sourcePolynomialNumber S Q D t k hdim P =
      integral Q (sourceTopForm S Q D t k hdim P hP) :=
  sourcePolynomialNumber_representative S Q D t k hdim P hP

theorem sourcePolynomialNumber_lower_bound (t : ℝ) (k : ℕ)
    (hdim : 4*(k+1) = Module.finrank ℝ E)
    (P : DimensionThirteenFourteenDensity.P)
    (hP : MvPolynomial.IsWeightedHomogeneous
      ManifoldSevenVariableClosedEvaluation.slotGrade P (k+1))
    (c : ℝ)
    (hbound : ∀ x : M,
      c ≤ scalarDensity Q (sourceTopForm S Q D t k hdim P hP).val x) :
    c * integral Q (volumeForm Q) ≤
      sourcePolynomialNumber S Q D t k hdim P := by
  rw [sourcePolynomialNumber_eq_sourceTopIntegral S Q D t k hdim P hP]
  apply integral_lower_bound Q _ _
  intro x
  exact ⟨scalarDensity Q (sourceTopForm S Q D t k hdim P hP).val x,
    hbound x, eq_scalarDensity_smul Q _ x⟩

end
end QuaternionicSymmetry.QuaternionicSourceIntegralBound
