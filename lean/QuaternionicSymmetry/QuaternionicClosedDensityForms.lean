import QuaternionicSymmetry.QuaternionicClosedDensityEvaluation
import QuaternionicSymmetry.ManifoldClosedSixPolynomialEvaluation
import QuaternionicSymmetry.QuaternionicWeylNormalizedDensity
import QuaternionicSymmetry.ManifoldRecoveredElevenTwelveWeights

/-! Actual globally closed degree-44 and degree-48 densities satisfy the
printed pointwise lower bounds in their fixed orthonormal tangent frame. -/
namespace QuaternionicSymmetry.QuaternionicClosedDensityForms
open Module QuaternionicClosedSourceGenerators QuaternionicClosedDensityEvaluation
open ManifoldClosedPolynomialRepresentative ManifoldClosedSixPolynomialEvaluation
open ManifoldEvenClosedEvaluation QuaternionicWeylNormalizedDensity
open ManifoldRecoveredElevenTwelveWeights DimensionElevenTwelveDensity
open ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicKSWScalarInput
open QuaternionicFundamental QuaternionicTracePositivity
open scoped Manifold ContDiff
noncomputable section
variable {E M ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

def density11Form (t : ℝ) : ManifoldEvenClosedAlgebra.Grade E M 11 :=
  closedRepresentative (generators S Q D t) (DimensionThirteenFourteenDensity.lift density11)
    lifted_density11_weighted

def density12Form (t : ℝ) : ManifoldEvenClosedAlgebra.Grade E M 12 :=
  closedRepresentative (generators S Q D t) (DimensionThirteenFourteenDensity.lift density12)
    lifted_density12_weighted

theorem density11Form_pointwise_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 11) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (F : CE E →ₗ[ℝ] ℝ) (hF : 0 ≤ F (embed (V := E) (topForm S b))) :
    288 * F ((((t ^ 2 / Real.pi) ^ 2) • embed (V := E) (form S b)) ^ 11) ≤
      F (embed (V := E) (gradeValue p y
        (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 11 (density11Form S Q D t))) := by
  obtain ⟨W, hW, hv⟩ := six_generator_values S Q D hsp hdecomp b t ht p y hy
  rw [density11Form, pointwise_lift_representative, hv]
  exact density11_weyl_lower_bound S W hW b hsource hn (t^2 / Real.pi)
    (div_pos (sq_pos_of_pos htpos) Real.pi_pos) F hF

theorem density12Form_pointwise_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 12) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (F : CE E →ₗ[ℝ] ℝ) (hF : 0 ≤ F (embed (V := E) (topForm S b))) :
    336 * F ((((t ^ 2 / Real.pi) ^ 2) • embed (V := E) (form S b)) ^ 12) ≤
      F (embed (V := E) (gradeValue p y
        (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 12 (density12Form S Q D t))) := by
  obtain ⟨W, hW, hv⟩ := six_generator_values S Q D hsp hdecomp b t ht p y hy
  rw [density12Form, pointwise_lift_representative, hv]
  exact density12_weyl_lower_bound S W hW b hsource hn (t^2 / Real.pi)
    (div_pos (sq_pos_of_pos htpos) Real.pi_pos) F hF

end
end QuaternionicSymmetry.QuaternionicClosedDensityForms
