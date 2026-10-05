import QuaternionicSymmetry.FiberBundleCompactHausdorff
import QuaternionicSymmetry.ManifoldTwistorSphereCore
import Mathlib.Analysis.Normed.Module.Connected

/-! Compactness, separation and countability of the actual associated twistor
sphere bundle. These follow from the bundle construction and its sphere fiber. -/

namespace QuaternionicSymmetry.ManifoldTwistorSphereCore

open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

instance [T2Space M] : T2Space (SphereBundleTotal Q) :=
  FiberBundleCompactHausdorff.totalSpace_t2 (sphereCore Q).Fiber

instance [CompactSpace M] : CompactSpace (SphereBundleTotal Q) :=
  FiberBundleCompactHausdorff.totalSpace_compact (sphereCore Q).Fiber

instance [CompactSpace M] : SecondCountableTopology (SphereBundleTotal Q) := by
  letI : SecondCountableTopology (ModelProd E (EuclideanSpace ℝ (Fin 2))) :=
    inferInstanceAs (SecondCountableTopology (E × EuclideanSpace ℝ (Fin 2)))
  exact ChartedSpace.secondCountable_of_sigmaCompact
    (ModelProd E (EuclideanSpace ℝ (Fin 2))) (SphereBundleTotal Q)

instance [PreconnectedSpace M] : PreconnectedSpace (SphereBundleTotal Q) := by
  letI : ConnectedSpace geometricSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num [EuclideanThree])
      (0 : EuclideanThree) (by norm_num : (0 : ℝ) ≤ 1))
  exact FiberBundleCompactHausdorff.totalSpace_preconnected (sphereCore Q).Fiber

instance [Nonempty M] : Nonempty (SphereBundleTotal Q) := by
  classical
  letI : Nonempty geometricSphere := (isConnected_sphere
    (by rw [← Module.finrank_eq_rank]; norm_num [EuclideanThree])
    (0 : EuclideanThree) (by norm_num : (0 : ℝ) ≤ 1)).nonempty.to_subtype
  exact (FiberBundle.surjective_proj geometricSphere (sphereCore Q).Fiber).nonempty

instance [ConnectedSpace M] : ConnectedSpace (SphereBundleTotal Q) where
  toPreconnectedSpace := inferInstance
  toNonempty := inferInstance

end QuaternionicSymmetry.ManifoldTwistorSphereCore
