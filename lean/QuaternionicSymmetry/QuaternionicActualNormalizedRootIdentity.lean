import QuaternionicSymmetry.QuaternionicScaledBinomialNormalization
import QuaternionicSymmetry.QuaternionicActualTangentTraceBinomial

/-! The actual tangent curvature exterior coefficients satisfy the
normalized half-trace binomial and the six recovered standard power
identities, with precise half/quarter factors. -/
namespace QuaternionicSymmetry.QuaternionicActualNormalizedRootIdentity
open QuaternionicActualSpCurvatureCoordinates
  QuaternionicActualTangentExteriorMatrix
  QuaternionicActualTangentTraceBinomial
  QuaternionicTangentUniversalSpecialization
  QuaternionicScaledBinomialNormalization
  QuaternionicAbstractRootInversion
  QuaternionicTangentFormalMatrix
  QuaternionicUniversalEvenTrace QuaternionicExteriorEvenTrace
  EvenForms
open scoped Manifold ContDiff Topology
noncomputable section
set_option maxHeartbeats 1000000

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem scalarNorm_actualEta (p : M) (y : E) :
    scalarNorm (chartStructure Q p) (actualEta Q D p y) =
      normSquare (liftTwo (fun i =>
        QuaternionicCurvatureExteriorCoordinates.axialCurvaturePower Q D p y i)) := by
  simp [scalarNorm, scalarNormPolynomial, actualEta,
    normSquare, liftTwo, Fin.sum_univ_three]

theorem actual_scaled_binomial (p : M) (y : E) (c : EvenAlgebra E)
    (j : ℕ) (hj : j ≤ 6) :
    scaledTangentHalfTrace c
      (spMatrix (chartStructure Q p) (actualEta Q D p y))
      (scalarMatrix (chartStructure Q p) (actualEta Q D p y)) j =
    binomialTangentTrace (chartStructure Q p).quaternionicDimension
      (scaledU c (scalarNorm (chartStructure Q p) (actualEta Q D p y)))
      (scaledSpPower c
        (spMatrix (chartStructure Q p) (actualEta Q D p y))) j := by
  apply scaled_trace_eq_binomial _ _ _ _ _ ?_ j hj
  intro m
  exact tangent_even_trace_formal_binomial Q D p y m

theorem actual_sp_zero (p : M) (y : E) (c : EvenAlgebra E) :
    scaledSpPower c
      (spMatrix (chartStructure Q p) (actualEta Q D p y)) 0 =
      ((chartStructure Q p).quaternionicDimension : EvenAlgebra E) := by
  apply scaledSpPower_zero
  simpa [QuaternionicTangentFormalMatrix.MatrixIndex] using
    (chartStructure Q p).real_finrank

theorem actual_recovered_standard (p : M) (y : E) (c : EvenAlgebra E)
    (j : Fin 7) :
    QuaternionicTangentRootConversion.recoveredStandardPower
      (chartStructure Q p).quaternionicDimension
      (scaledU c (scalarNorm (chartStructure Q p) (actualEta Q D p y)))
      (fun m => scaledTangentHalfTrace c
        (spMatrix (chartStructure Q p) (actualEta Q D p y))
        (scalarMatrix (chartStructure Q p) (actualEta Q D p y)) m) j =
    (-1 : EvenAlgebra E) ^ j.val *
      (scaledSpPower c
        (spMatrix (chartStructure Q p) (actualEta Q D p y)) j.val +
        (scaledU c (scalarNorm (chartStructure Q p) (actualEta Q D p y))) ^ j.val) := by
  let n := (chartStructure Q p).quaternionicDimension
  let u := scaledU c (scalarNorm (chartStructure Q p) (actualEta Q D p y))
  let q := scaledSpPower c (spMatrix (chartStructure Q p) (actualEta Q D p y))
  have hq0 : q 0 = (n : EvenAlgebra E) := actual_sp_zero Q D p y c
  calc
    QuaternionicTangentRootConversion.recoveredStandardPower n u
        (fun m => scaledTangentHalfTrace c
          (spMatrix (chartStructure Q p) (actualEta Q D p y))
          (scalarMatrix (chartStructure Q p) (actualEta Q D p y)) m) j =
      QuaternionicTangentRootConversion.recoveredStandardPower n u
        (binomialTangentTrace n u q) j := by
          apply recoveredStandardPower_congr
          intro m hm
          exact actual_scaled_binomial Q D p y c m hm
    _ = _ := recoveredStandardPower_binomial n u q hq0 j

end
end QuaternionicSymmetry.QuaternionicActualNormalizedRootIdentity
