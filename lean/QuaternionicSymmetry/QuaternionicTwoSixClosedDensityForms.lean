import QuaternionicSymmetry.QuaternionicTwoSixWeylBounds
import QuaternionicSymmetry.QuaternionicClosedDensityEvaluation
import QuaternionicSymmetry.ManifoldClosedSixPolynomialEvaluation
import QuaternionicSymmetry.LowerCertificateWeights

/-! Actual globally closed printed characteristic densities through
quaternionic dimension six, with fixed-frame pointwise lower bounds. -/
namespace QuaternionicSymmetry.QuaternionicTwoSixClosedDensityForms
open Module QuaternionicClosedSourceGenerators QuaternionicClosedDensityEvaluation
open ManifoldClosedPolynomialRepresentative ManifoldClosedSixPolynomialEvaluation
open ManifoldEvenClosedEvaluation QuaternionicTwoSixWeylBounds
open ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicKSWScalarInput
open QuaternionicFundamental QuaternionicTracePositivity
open PrintedTwoSixLinearAssembly ReconstructionExamples LowerCertificateWeights
open scoped Manifold ContDiff
noncomputable section

variable {E M ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

def density2Form (t : ℝ) : ManifoldEvenClosedAlgebra.Grade E M 2 :=
  closedRepresentative (generators S Q D t)
    (DimensionThirteenFourteenDensity.lift density2) density2_weighted

theorem density2Form_pointwise_bound
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 2) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (F : CE E →ₗ[ℝ] ℝ) (hF : 0 ≤ F (embed (V := E) (topForm S b))) :
    16 * F ((((t ^ 2 / Real.pi) ^ 2) • embed (V := E) (form S b)) ^ 2) ≤
      F (embed (V := E) (gradeValue p y
        (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 2
        (density2Form S Q D t))) := by
  obtain ⟨W, hW, hv⟩ := six_generator_values S Q D hsp hdecomp b t ht p y hy
  rw [density2Form, pointwise_lift_representative, hv]
  exact density2_weyl_lower_bound S W hW b hn (t^2 / Real.pi)
    (div_pos (sq_pos_of_pos htpos) Real.pi_pos) F hF


def density3Form (t : ℝ) : ManifoldEvenClosedAlgebra.Grade E M 3 :=
  closedRepresentative (generators S Q D t)
    (DimensionThirteenFourteenDensity.lift density3) density3_weighted

theorem density3Form_pointwise_bound
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 3) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (F : CE E →ₗ[ℝ] ℝ) (hF : 0 ≤ F (embed (V := E) (topForm S b))) :
    32 * F ((((t ^ 2 / Real.pi) ^ 2) • embed (V := E) (form S b)) ^ 3) ≤
      F (embed (V := E) (gradeValue p y
        (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 3
        (density3Form S Q D t))) := by
  obtain ⟨W, hW, hv⟩ := six_generator_values S Q D hsp hdecomp b t ht p y hy
  rw [density3Form, pointwise_lift_representative, hv]
  exact density3_weyl_lower_bound S W hW b hn (t^2 / Real.pi)
    (div_pos (sq_pos_of_pos htpos) Real.pi_pos) F hF

def density4Form (t : ℝ) : ManifoldEvenClosedAlgebra.Grade E M 4 :=
  closedRepresentative (generators S Q D t)
    (DimensionThirteenFourteenDensity.lift density4) density4_weighted

theorem density4Form_pointwise_bound
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 4) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (F : CE E →ₗ[ℝ] ℝ) (hF : 0 ≤ F (embed (V := E) (topForm S b))) :
    48 * F ((((t ^ 2 / Real.pi) ^ 2) • embed (V := E) (form S b)) ^ 4) ≤
      F (embed (V := E) (gradeValue p y
        (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 4
        (density4Form S Q D t))) := by
  obtain ⟨W, hW, hv⟩ := six_generator_values S Q D hsp hdecomp b t ht p y hy
  rw [density4Form, pointwise_lift_representative, hv]
  exact density4_weyl_lower_bound S W hW b hn (t^2 / Real.pi)
    (div_pos (sq_pos_of_pos htpos) Real.pi_pos) F hF

def density5Form (t : ℝ) : ManifoldEvenClosedAlgebra.Grade E M 5 :=
  closedRepresentative (generators S Q D t)
    (DimensionThirteenFourteenDensity.lift k5) density5_weighted

theorem density5Form_pointwise_bound
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 5) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (F : CE E →ₗ[ℝ] ℝ) (hF : 0 ≤ F (embed (V := E) (topForm S b))) :
    72 * F ((((t ^ 2 / Real.pi) ^ 2) • embed (V := E) (form S b)) ^ 5) ≤
      F (embed (V := E) (gradeValue p y
        (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 5
        (density5Form S Q D t))) := by
  obtain ⟨W, hW, hv⟩ := six_generator_values S Q D hsp hdecomp b t ht p y hy
  rw [density5Form, pointwise_lift_representative, hv]
  exact density5_weyl_lower_bound S W hW b hn (t^2 / Real.pi)
    (div_pos (sq_pos_of_pos htpos) Real.pi_pos) F hF

def density6Form (t : ℝ) : ManifoldEvenClosedAlgebra.Grade E M 6 :=
  closedRepresentative (generators S Q D t)
    (DimensionThirteenFourteenDensity.lift k6) density6_weighted

theorem density6Form_pointwise_bound
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 6) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (F : CE E →ₗ[ℝ] ℝ) (hF : 0 ≤ F (embed (V := E) (topForm S b))) :
    96 * F ((((t ^ 2 / Real.pi) ^ 2) • embed (V := E) (form S b)) ^ 6) ≤
      F (embed (V := E) (gradeValue p y
        (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 6
        (density6Form S Q D t))) := by
  obtain ⟨W, hW, hv⟩ := six_generator_values S Q D hsp hdecomp b t ht p y hy
  rw [density6Form, pointwise_lift_representative, hv]
  exact density6_weyl_lower_bound S W hW b hn (t^2 / Real.pi)
    (div_pos (sq_pos_of_pos htpos) Real.pi_pos) F hF

end
end QuaternionicSymmetry.QuaternionicTwoSixClosedDensityForms
