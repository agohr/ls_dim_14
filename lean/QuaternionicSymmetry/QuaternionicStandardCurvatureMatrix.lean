import QuaternionicSymmetry.QuaternionicOperatorMatrix
import QuaternionicSymmetry.QuaternionicProjectiveCurvatureSourceTrace
import QuaternionicSymmetry.QuaternionicManifoldStandardQuaternionicCurvature

/-! Fixed-basis matrix coordinates for actual local standard curvature.
This precedes the corrected-connection and hyperholomorphic Weyl comparison. -/
namespace QuaternionicSymmetry.QuaternionicStandardCurvatureMatrix
open QuaternionicProjectiveStandardL2 QuaternionicProjectiveStandardHilbertStructure
  QuaternionicProjectiveStandardComplexTrace QuaternionicProjectiveCurvatureSourceTrace
  QuaternionicManifoldStandardQuaternionicCurvature QuaternionicOperatorMatrix
  QuaternionicCanonicalModel QuaternionicMatrixModel
open scoped ContDiff Manifold Matrix
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

omit [Nontrivial E] in
theorem standard_quaternionicDimension :
    (standardStructure S).quaternionicDimension = S.quaternionicDimension + 1 := by
  have h := (standardStructure S).real_finrank
  rw [standard_real_finrank, S.real_finrank] at h
  omega

def curvatureMatrix (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :=
  operatorMatrix (standardStructure S) (standardCurvature S Q D p y u v)
    (standardCurvature_commutes S Q D p y u v hy)

theorem curvatureMatrix_action (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (z : StandardSpace (E := E)) :
    realMatrixAction (curvatureMatrix S Q D p y u v hy)
        (canonicalModel (standardStructure S) z) =
      canonicalModel (standardStructure S) (standardCurvature S Q D p y u v z) :=
  operatorMatrix_action (standardStructure S) _ _ z

theorem curvatureMatrix_hermitianAntiSelfDual (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    HermitianAntiSelfDual (Complex.I • curvatureMatrix S Q D p y u v hy) :=
  operatorMatrix_hermitianAntiSelfDual (standardStructure S)
    (standardCurvature S Q D p y u v)
    (standardCurvature_commutes S Q D p y u v hy)
    (standardCurvature_commutes_J S Q D p y u v hy)
    (standardCurvature_isSkew S Q D p y u v hy)

def sourceCurvatureMatrix (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :=
  (1 / (2 * Real.pi) : ℝ) • (Complex.I • curvatureMatrix S Q D p y u v hy)

theorem sourceCurvatureMatrix_hermitianAntiSelfDual (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    HermitianAntiSelfDual (sourceCurvatureMatrix S Q D p y u v hy) :=
  (hermitianAntiSelfDualSubmodule _).smul_mem (1 / (2 * Real.pi) : ℝ)
    (curvatureMatrix_hermitianAntiSelfDual S Q D p y u v hy)

end
end QuaternionicSymmetry.QuaternionicStandardCurvatureMatrix
