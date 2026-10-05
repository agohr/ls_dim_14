import QuaternionicSymmetry.FourDimensionalTwistorAntipodalConnection

/-! The coefficient antipodal map anti-intertwines the actual local
connection-defined twistor almost-complex tensor, including its horizontal
base rotation and vertical cross-product rotation. This matches Hitchin's
stated antipodal convention but is not yet his Clifford/AHS identification. -/

namespace QuaternionicSymmetry.FourDimensionalTwistorAntipodalAlmostComplex

open scoped Manifold ContDiff Quaternion Matrix
open FourDimensionalTwistorAntipodalTensor
  FourDimensionalTwistorAntipodalConnection
  FourDimensionalHalfSpinAntipodalVerticalSign
  ManifoldTwistorHorizontalConnection
  ManifoldTwistorLocalAlmostComplex
  ManifoldTwistorVerticalComplex
  ManifoldTwistorSphereBundle
  ManifoldQuaternionicMetric
  ManifoldQuaternionicConnection
  VectorBundleFrameTransitions.QuaternionicFrameReduction

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem chartBaseComplex_antipodal (p : M) (y : E)
    (a : coefficientSphere) (u : E) :
    chartBaseComplex Q p y (antipodalCoefficient a) u =
      -(chartBaseComplex Q p y a u) := by
  let S := Q.reduction.Q (achart E p)
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  change Q.frames.fromFrame (achart E p) x
      (synth S (-a.1) (Q.frames.toFrame (achart E p) x u)) =
    -(Q.frames.fromFrame (achart E p) x
      (synth S a.1 (Q.frames.toFrame (achart E p) x u)))
  rw [map_neg]
  change Q.frames.fromFrame (achart E p) x
      (-(synth S a.1 (Q.frames.toFrame (achart E p) x u))) = _
  exact map_neg (Q.frames.fromFrame (achart E p) x) _

theorem rawAntipodal_chartSplitComplex (p : M) (y : E)
    (a : coefficientSphere) (uv : E × verticalSubmodule a) :
    rawAntipodal a (chartSplitComplex Q p y a uv) =
      -chartSplitComplex Q p y (antipodalCoefficient a)
        (rawAntipodal a uv) := by
  apply Prod.ext
  · change chartBaseComplex Q p y a uv.1 =
        -(chartBaseComplex Q p y (antipodalCoefficient a) uv.1)
    rw [chartBaseComplex_antipodal Q p y a uv.1, neg_neg]
  · apply Subtype.ext
    change -(a.1 ⨯₃ uv.2.1) =
      -((-a.1) ⨯₃ (-uv.2.1))
    simp only [map_neg, neg_neg]
    rfl

theorem rawAntipodal_localTwistorComplex (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : coefficientSphere) (uv : E × verticalSubmodule a) :
    rawAntipodal a (localTwistorComplex Q D p y hy a uv) =
      -localTwistorComplex Q D p y hy (antipodalCoefficient a)
        (rawAntipodal a uv) := by
  let b := antipodalCoefficient a
  let ca := connectionSplit Q D p y hy a
  let cb := connectionSplit Q D p y hy b
  apply cb.injective
  have hca := rawAntipodal_connectionSplit Q D p y hy a uv
  have hcs := rawAntipodal_chartSplitComplex Q p y a (ca uv)
  change cb (rawAntipodal a (ca.symm (chartSplitComplex Q p y a (ca uv)))) =
    cb (-cb.symm (chartSplitComplex Q p y b (cb (rawAntipodal a uv))))
  calc
    cb (rawAntipodal a (ca.symm (chartSplitComplex Q p y a (ca uv)))) =
        rawAntipodal a (ca (ca.symm (chartSplitComplex Q p y a (ca uv)))) :=
      (rawAntipodal_connectionSplit Q D p y hy a _).symm
    _ = rawAntipodal a (chartSplitComplex Q p y a (ca uv)) := by
      rw [ca.apply_symm_apply]
    _ = -chartSplitComplex Q p y b (rawAntipodal a (ca uv)) := hcs
    _ = -chartSplitComplex Q p y b (cb (rawAntipodal a uv)) := by
      rw [hca]
    _ = cb (-cb.symm (chartSplitComplex Q p y b (cb (rawAntipodal a uv)))) := by
      simp

end
end QuaternionicSymmetry.FourDimensionalTwistorAntipodalAlmostComplex
