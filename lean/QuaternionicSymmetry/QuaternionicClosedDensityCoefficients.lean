import QuaternionicSymmetry.QuaternionicClosedDensityForms
import QuaternionicSymmetry.QuaternionicDensityCoefficient

/-! The actual closed C12 densities have scalar coefficients bounded below
by the printed reserve, relative to the fixed unscaled fundamental volume. -/
namespace QuaternionicSymmetry.QuaternionicClosedDensityCoefficients
open Module QuaternionicClosedDensityForms ManifoldEvenClosedEvaluation
open ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicKSWScalarInput
open QuaternionicFundamental
open scoped Manifold ContDiff
noncomputable section
variable {E M ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem density11_coefficient
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 11) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    ∃ r : ℝ, 288 * (t ^ 2 / Real.pi) ^ 22 ≤ r ∧
      gradeValue p y (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 11
        (density11Form S Q D t) = r • (form S b ^ 11) := by
  have h := QuaternionicDensityCoefficient.exists_coefficient_ge S b
    (gradeValue p y (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 11
      (density11Form S Q D t)) 288 (t ^ 2 / Real.pi) (fun F hF => by
        simpa only [hn] using
          density11Form_pointwise_bound S Q D hsource hsp hdecomp hn b t htpos ht p y hy F hF)
  simpa only [hn, Nat.reduceMul] using h

theorem density12_coefficient
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 12) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    ∃ r : ℝ, 336 * (t ^ 2 / Real.pi) ^ 24 ≤ r ∧
      gradeValue p y (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 12
        (density12Form S Q D t) = r • (form S b ^ 12) := by
  have h := QuaternionicDensityCoefficient.exists_coefficient_ge S b
    (gradeValue p y (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 12
      (density12Form S Q D t)) 336 (t ^ 2 / Real.pi) (fun F hF => by
        simpa only [hn] using
          density12Form_pointwise_bound S Q D hsource hsp hdecomp hn b t htpos ht p y hy F hF)
  simpa only [hn, Nat.reduceMul] using h

end
end QuaternionicSymmetry.QuaternionicClosedDensityCoefficients
