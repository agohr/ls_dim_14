import QuaternionicSymmetry.QuaternionicSevenTenWeylBounds
import QuaternionicSymmetry.QuaternionicClosedDensityEvaluation
import QuaternionicSymmetry.ManifoldClosedSixPolynomialEvaluation
import QuaternionicSymmetry.LowerCertificateWeights

/-! Actual globally closed degree-28 through degree-40 representatives of
the printed n=7–10 characteristic densities and their fixed-frame bounds. -/
namespace QuaternionicSymmetry.QuaternionicSevenTenClosedDensityForms
open Module QuaternionicClosedSourceGenerators QuaternionicClosedDensityEvaluation
open ManifoldClosedPolynomialRepresentative ManifoldClosedSixPolynomialEvaluation
open ManifoldEvenClosedEvaluation QuaternionicSevenTenWeylBounds
open ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicKSWScalarInput
open QuaternionicFundamental QuaternionicTracePositivity
open PrintedCertificatesSevenTen LowerCertificateWeights
open scoped Manifold ContDiff
noncomputable section

variable {E M ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

def density7Form (t : ℝ) : ManifoldEvenClosedAlgebra.Grade E M 7 :=
  closedRepresentative (generators S Q D t) (DimensionThirteenFourteenDensity.lift rhs7)
    rhs7_weighted

theorem density7Form_pointwise_bound
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 7) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (F : CE E →ₗ[ℝ] ℝ) (hF : 0 ≤ F (embed (V := E) (topForm S b))) :
    128 * F ((((t ^ 2 / Real.pi) ^ 2) • embed (V := E) (form S b)) ^ 7) ≤
      F (embed (V := E) (gradeValue p y
        (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 7
        (density7Form S Q D t))) := by
  obtain ⟨W, hW, hv⟩ := six_generator_values S Q D hsp hdecomp b t ht p y hy
  rw [density7Form, pointwise_lift_representative, hv]
  exact density7_weyl_lower_bound S W hW b hn (t^2 / Real.pi)
    (div_pos (sq_pos_of_pos htpos) Real.pi_pos) F hF


def density8Form (t : ℝ) : ManifoldEvenClosedAlgebra.Grade E M 8 :=
  closedRepresentative (generators S Q D t) (DimensionThirteenFourteenDensity.lift rhs8)
    rhs8_weighted

theorem density8Form_pointwise_bound
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 8) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (F : CE E →ₗ[ℝ] ℝ) (hF : 0 ≤ F (embed (V := E) (topForm S b))) :
    160 * F ((((t ^ 2 / Real.pi) ^ 2) • embed (V := E) (form S b)) ^ 8) ≤
      F (embed (V := E) (gradeValue p y
        (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 8
        (density8Form S Q D t))) := by
  obtain ⟨W, hW, hv⟩ := six_generator_values S Q D hsp hdecomp b t ht p y hy
  rw [density8Form, pointwise_lift_representative, hv]
  exact density8_weyl_lower_bound S W hW b hn (t^2 / Real.pi)
    (div_pos (sq_pos_of_pos htpos) Real.pi_pos) F hF

def density9Form (t : ℝ) : ManifoldEvenClosedAlgebra.Grade E M 9 :=
  closedRepresentative (generators S Q D t) (DimensionThirteenFourteenDensity.lift rhs9)
    rhs9_weighted

theorem density9Form_pointwise_bound
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 9) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (F : CE E →ₗ[ℝ] ℝ) (hF : 0 ≤ F (embed (V := E) (topForm S b))) :
    200 * F ((((t ^ 2 / Real.pi) ^ 2) • embed (V := E) (form S b)) ^ 9) ≤
      F (embed (V := E) (gradeValue p y
        (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 9
        (density9Form S Q D t))) := by
  obtain ⟨W, hW, hv⟩ := six_generator_values S Q D hsp hdecomp b t ht p y hy
  rw [density9Form, pointwise_lift_representative, hv]
  exact density9_weyl_lower_bound S W hW b hn (t^2 / Real.pi)
    (div_pos (sq_pos_of_pos htpos) Real.pi_pos) F hF

def density10Form (t : ℝ) : ManifoldEvenClosedAlgebra.Grade E M 10 :=
  closedRepresentative (generators S Q D t) (DimensionThirteenFourteenDensity.lift rhs10)
    rhs10_weighted

theorem density10Form_pointwise_bound
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 10) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (F : CE E →ₗ[ℝ] ℝ) (hF : 0 ≤ F (embed (V := E) (topForm S b))) :
    240 * F ((((t ^ 2 / Real.pi) ^ 2) • embed (V := E) (form S b)) ^ 10) ≤
      F (embed (V := E) (gradeValue p y
        (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 10
        (density10Form S Q D t))) := by
  obtain ⟨W, hW, hv⟩ := six_generator_values S Q D hsp hdecomp b t ht p y hy
  rw [density10Form, pointwise_lift_representative, hv]
  exact density10_weyl_lower_bound S W hW b hn (t^2 / Real.pi)
    (div_pos (sq_pos_of_pos htpos) Real.pi_pos) F hF

end
end QuaternionicSymmetry.QuaternionicSevenTenClosedDensityForms
