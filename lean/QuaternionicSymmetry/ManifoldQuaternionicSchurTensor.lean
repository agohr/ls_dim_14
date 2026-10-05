import QuaternionicSymmetry.ManifoldQuaternionicCovariantRiemannSymmetry
import QuaternionicSymmetry.AlgebraicSchurContraction
import QuaternionicSymmetry.ManifoldQuaternionicScalarCurvature

/-! The actual covariant Riemann tensor in a pointwise orthonormal basis,
with all algebraic premises of the finite Schur contraction proved. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicSchurTensor
open ManifoldQuaternionicConnection
open ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicCoordinateMetricField
open ManifoldQuaternionicCovariantRiemannSymmetry
open ManifoldQuaternionicCoordinateSecondBianchi
open QuaternionicSymmetry.LocalConnectionRiemannSecondBianchi
open QuaternionicSymmetry.AlgebraicSchurContraction
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance : NormedAlgebra ℝ (E →L[ℝ] E) := inferInstance
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

def coordinateOrthonormalBasis (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (i : Fin (Module.finrank ℝ E)) : E :=
  (solderEquiv Q p y hy).symm (stdOrthonormalBasis ℝ E i)

omit [Nontrivial E] in
theorem coordinateOrthonormalBasis_metric (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (i j : Fin (Module.finrank ℝ E)) :
    coordinateMetricField Q p y (coordinateOrthonormalBasis Q p y hy i)
      (coordinateOrthonormalBasis Q p y hy j) = if i = j then 1 else 0 := by
  rw [coordinateMetricField_apply Q p y hy]
  change inner ℝ
    ((solderEquiv Q p y hy) ((solderEquiv Q p y hy).symm
      (stdOrthonormalBasis ℝ E i)))
    ((solderEquiv Q p y hy) ((solderEquiv Q p y hy).symm
      (stdOrthonormalBasis ℝ E j))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  simp only [OrthonormalBasis.inner_eq_ite]

/-- The actual five-index covariant derivative, with every index evaluated
on the pointwise orthonormal coordinate basis. -/
def schurTensor (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    CurvatureDerivative (Fin (Module.finrank ℝ E)) :=
  fun a b c d e => covariantRiemann Q D p y
    (coordinateOrthonormalBasis Q p y hy a)
    (coordinateOrthonormalBasis Q p y hy b)
    (coordinateOrthonormalBasis Q p y hy c)
    (coordinateOrthonormalBasis Q p y hy d)
    (coordinateOrthonormalBasis Q p y hy e)

omit [Nontrivial E] in
theorem schurTensor_pairSymmetric (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    PairSymmetric (schurTensor Q D p y hy) := by
  constructor
  · intro a b c d e
    exact covariantRiemann_skew_last Q D p y hy _ _ _ _ _
  · intro a b c d e
    exact covariantRiemann_pair_symmetry Q D p y hy _ _ _ _ _

omit [Nontrivial E] in
theorem schurTensor_secondBianchi (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    SecondBianchi (schurTensor Q D p y hy) := by
  intro a b c d e
  have h := congrArg
    (fun t : E => coordinateMetricField Q p y t
      (coordinateOrthonormalBasis Q p y hy e))
    (coordinate_second_bianchi Q D p y hy
      (coordinateOrthonormalBasis Q p y hy a)
      (coordinateOrthonormalBasis Q p y hy b)
      (coordinateOrthonormalBasis Q p y hy c)
      (coordinateOrthonormalBasis Q p y hy d))
  simpa only [SecondBianchi, schurTensor, covariantRiemann,
    map_add, map_zero] using h

end
end QuaternionicSymmetry.ManifoldQuaternionicSchurTensor
