import QuaternionicSymmetry.FiniteVirtualDensity
import QuaternionicSymmetry.ManifoldTangentLowerCharacterNumbers
import QuaternionicSymmetry.QuaternionicRecoveredSourceComparison

/-! Through dimension twelve the canonical tangent A-hat virtual-character
number is the actual corrected-source density number, at every correction
parameter. This identifies genuine characteristic integrals; the twistor
Euler characteristic comparison remains a separate theorem. -/
namespace QuaternionicSymmetry.ManifoldFiniteVirtualNumbers
open ManifoldEvenCharacteristicAlgebra ManifoldTangentTraceRootCandidates
open ManifoldTangentCharacterNumber ManifoldIntegratedRecoveredCertificates
open QuaternionicRecoveredSourceComparison QuaternionicClosedSourceNumbers
open FiniteVirtualDensity
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
local instance : Algebra ℚ (Total (E := E) (M := M)) :=
  ManifoldTangentTraceRootCandidates.rationalAlgebra

theorem virtual_eq_recovered (n : ℕ) (hn : 2 ≤ n) (hn' : n ≤ 12)
    (hdim : 4*(n-1+1) = Module.finrank ℝ E) :
    characteristicFunctional Q D n (n-1) hdim (Characters.virtual n) =
      sixCandidateNumber Q D n (n-1) hdim (density n) := by
  unfold characteristicFunctional
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  have hconv :
      TangentAhatCharacterDensity.characterDensity (n-1+1)
          (quarterUTotal Q D) (normalizedTangentHalfTrace Q D n) (Characters.virtual n) =
        MvPolynomial.aeval (RecoveredLogAhat.standardValues n (quarterUTotal Q D)
          (normalizedTangentHalfTrace Q D n)) (density n) := by
    rw [show n-1+1 = n by omega]
    exact characterDensity_eq n hn hn' _ _
  rw [hconv, standard_evaluation]
  rfl

theorem virtual_eq_source (n : ℕ) (hn : 2 ≤ n) (hn' : n ≤ 12)
    (hqdim : S.quaternionicDimension = n)
    (hdim : 4*(n-1+1) = Module.finrank ℝ E) (t : ℝ) :
    characteristicFunctional Q D n (n-1) hdim (Characters.virtual n) =
      sourcePolynomialNumber S Q D t (n-1) hdim
        (DimensionThirteenFourteenDensity.lift (density n)) := by
  rw [virtual_eq_recovered Q D n hn hn', sourceNumber_eq_sixCandidate, hqdim]

end
end QuaternionicSymmetry.ManifoldFiniteVirtualNumbers
