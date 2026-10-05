import QuaternionicSymmetry.ManifoldClosedGeneratorPower
import QuaternionicSymmetry.QuaternionicClosedSourceNumbers
import QuaternionicSymmetry.ManifoldQuaternionicQuarterVolume

/-! The polynomial quarter-class volume is the canonical integral of the
actual wedge power of the analytic quarter-Pontryagin form. -/
namespace QuaternionicSymmetry.QuaternionicQuarterPowerNumber
open QuaternionicClosedSourceNumbers QuaternionicClosedSourceGenerators
open ManifoldClosedGeneratorPower ManifoldQuaternionicQuarterVolume
open ManifoldClosedPolynomialRepresentative ManifoldSevenVariableClosedEvaluation
open ManifoldDeRhamWedge ManifoldQuaternionicCanonicalIntegration
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

theorem u_power_weighted (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous slotGrade
      (MvPolynomial.X (0 : Fin 7) ^ n : DimensionThirteenFourteenDensity.P) n := by
  simpa [slotGrade] using (MvPolynomial.isWeightedHomogeneous_X (R := ℚ) slotGrade 0).pow n

theorem sourcePolynomialNumber_u_power (t : ℝ) (k : ℕ)
    (hdim : 4*(k+1) = Module.finrank ℝ E) :
    sourcePolynomialNumber S Q D t k hdim (MvPolynomial.X (0 : Fin 7) ^ (k+1)) =
      integral Q (quarterTop Q D (k+1) hdim) := by
  rw [sourcePolynomialNumber_representative S Q D t k hdim _ (u_power_weighted (k+1))]
  congr 1
  apply Subtype.ext
  change castForm _ (closedRepresentative (generators S Q D t)
    (MvPolynomial.X (0 : Fin 7) ^ (k+1)) (u_power_weighted (k+1))).val.val =
      castForm hdim (ManifoldFormPowers.formPower
        (ManifoldQuaternionicAdjointChernWeil.quarterPontryaginCandidateForm Q D).val.val (k+1))
  rw [representative_u_power, castForm_comp]
  rfl

end
end QuaternionicSymmetry.QuaternionicQuarterPowerNumber
