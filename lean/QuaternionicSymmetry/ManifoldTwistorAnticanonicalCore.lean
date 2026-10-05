import QuaternionicSymmetry.HolomorphicDeterminantLine

/-! The anticanonical line of the source complex twistor atlas, as the
determinant of its genuine complex tangent bundle. The tangent transitions
come from derivatives of actual complex chart changes, and holomorphicity
of the determinant line follows from the polynomial determinant theorem. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

open QuaternionicSymmetry.HolomorphicDeterminantLine
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

/-- The true holomorphic tangent bundle core of the compatible source
complex atlas. -/
def CompatibleComplexAtlas.complexTangentCore {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) :
    letI := A.charts
    VectorBundleCore ℂ (SphereBundleTotal Q) (ComplexTwistorModel n)
      (atlas (ComplexTwistorModel n) (SphereBundleTotal Q)) := by
  letI := A.charts
  letI := A.complexManifold
  exact tangentBundleCore 𝓘(ℂ,ComplexTwistorModel n) (SphereBundleTotal Q)

theorem CompatibleComplexAtlas.complexTangentCore_holomorphic {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) :
    letI := A.charts
    (A.complexTangentCore Q D).IsContMDiff
      𝓘(ℂ,ComplexTwistorModel n) ∞ := by
  letI := A.charts
  letI := A.complexManifold
  letI : IsManifold 𝓘(ℂ,ComplexTwistorModel n) (∞ + 1)
      (SphereBundleTotal Q) := by simpa using A.complexManifold
  exact tangentBundleCore.isContMDiff
    (I := 𝓘(ℂ,ComplexTwistorModel n)) (M := SphereBundleTotal Q) (n := ∞)

/-- The anticanonical line `det(T^{1,0} Z)` as a genuine complex line
bundle core on the complex twistor manifold. -/
def CompatibleComplexAtlas.anticanonicalCore {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) :
    letI := A.charts
    VectorBundleCore ℂ (SphereBundleTotal Q) ℂ
      (atlas (ComplexTwistorModel n) (SphereBundleTotal Q)) := by
  letI := A.charts
  exact determinantCore (A.complexTangentCore Q D)

theorem CompatibleComplexAtlas.anticanonicalCore_holomorphic {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) :
    letI := A.charts
    (A.anticanonicalCore Q D).IsContMDiff
      𝓘(ℂ,ComplexTwistorModel n) ∞ := by
  letI := A.charts
  letI := A.complexTangentCore_holomorphic Q D
  exact determinantCore_isContMDiff (Z := A.complexTangentCore Q D)
    (IB := 𝓘(ℂ,ComplexTwistorModel n))

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
