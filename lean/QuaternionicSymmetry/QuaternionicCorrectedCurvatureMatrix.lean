import QuaternionicSymmetry.QuaternionicCorrectedCurvatureStructure
import QuaternionicSymmetry.QuaternionicStandardCurvatureMatrix

/-! Fixed quaternionic matrix coordinates of the actual corrected curvature,
including the source factor i/(2π). -/
namespace QuaternionicSymmetry.QuaternionicCorrectedCurvatureMatrix
open QuaternionicCorrectedCurvatureStructure QuaternionicManifoldCorrectedConnection
open QuaternionicProjectiveStandardL2 QuaternionicProjectiveStandardHilbertStructure
open QuaternionicOperatorMatrix QuaternionicCanonicalModel QuaternionicMatrixModel
open scoped Manifold ContDiff Matrix
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

def curvatureMatrix (t : ℝ) (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :=
  operatorMatrix (standardStructure S)
    (LocalConnection.curvature (correctedConnection S Q D t p) y u v).toLinearMap
    (curvature_I S Q D t p y u v hy)

theorem curvatureMatrix_action (t : ℝ) (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (z : StandardSpace (E := E)) :
    realMatrixAction (curvatureMatrix S Q D t p y u v hy)
        (canonicalModel (standardStructure S) z) =
      canonicalModel (standardStructure S)
        (LocalConnection.curvature (correctedConnection S Q D t p) y u v z) :=
  operatorMatrix_action (standardStructure S) _ _ z

theorem curvatureMatrix_hermitianAntiSelfDual (t : ℝ) (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    HermitianAntiSelfDual (Complex.I • curvatureMatrix S Q D t p y u v hy) :=
  operatorMatrix_hermitianAntiSelfDual (standardStructure S) _
    (curvature_I S Q D t p y u v hy) (curvature_J S Q D t p y u v hy)
    (curvature_skew S Q D t p y u v hy)

def sourceCurvatureMatrix (t : ℝ) (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :=
  (1 / (2 * Real.pi) : ℝ) • (Complex.I • curvatureMatrix S Q D t p y u v hy)

theorem sourceCurvatureMatrix_hermitianAntiSelfDual (t : ℝ) (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    HermitianAntiSelfDual (sourceCurvatureMatrix S Q D t p y u v hy) :=
  (hermitianAntiSelfDualSubmodule _).smul_mem (1 / (2 * Real.pi) : ℝ)
    (curvatureMatrix_hermitianAntiSelfDual S Q D t p y u v hy)

end
end QuaternionicSymmetry.QuaternionicCorrectedCurvatureMatrix
