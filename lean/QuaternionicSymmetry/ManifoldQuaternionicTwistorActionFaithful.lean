import QuaternionicSymmetry.ManifoldQuaternionicTwistorIsometryAction
import QuaternionicSymmetry.ManifoldQuaternionicTorusAction
import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff

/-! Faithfulness of the genuine isometry action survives passage to the
twistor sphere bundle, since its equivariant projection is surjective. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorActionFaithful

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction ManifoldTwistorSphereCore
open ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- The actual twistor bundle has a nonempty sphere over every base point. -/
theorem projection_surjective :
    Function.Surjective (fun z : SphereBundleTotal Q => z.1) := by
  letI : Nonempty geometricSphere := (isConnected_sphere
    (by rw [← Module.finrank_eq_rank]; norm_num [EuclideanThree])
    (0 : EuclideanThree) (by norm_num : (0 : ℝ) ≤ 1)).nonempty.to_subtype
  exact FiberBundle.surjective_proj geometricSphere (sphereCore Q).Fiber

/-- Two genuine quaternionic isometries with the same twistor lift coincide. -/
theorem sphereTotalMap_injective : Function.Injective (sphereTotalMap Q) := by
  intro f g h
  apply Subtype.ext
  apply Diffeomorph.ext
  intro x
  obtain ⟨z, rfl⟩ := projection_surjective Q x
  have hz := congrArg (fun a : SphereBundleTotal Q => a.1) (congrFun h z)
  simpa only [sphereTotalMap_base, smul_eq_apply] using hz

/-- A faithful torus action on the base remains faithful on the actual
twistor sphere bundle, not merely on an auxiliary representation. -/
theorem torus_lift_injective {r : ℕ} (A : ContinuousTorusAction Q r)
    (hA : A.Faithful) :
    Function.Injective (fun t => sphereTotalMap Q (A.representation t)) :=
  (sphereTotalMap_injective Q).comp hA

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorActionFaithful
