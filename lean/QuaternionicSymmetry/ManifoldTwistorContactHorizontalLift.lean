import QuaternionicSymmetry.ManifoldTwistorContactPullbackComplex

/-! The geometric horizontal lift from the genuine smooth pullback
bundle π*TM into the actual twistor tangent bundle. Fiberwise it is the
inverse of the differential of the projection and its image is exactly
the checked connection-horizontal contact plane. -/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

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

private abbrev I := (𝓘(ℝ,E)).prod (𝓡 2)

/-- The actual horizontal lift on the total spaces of two genuine smooth
vector bundles. Its smoothness as a total-space map is the next atlas
calculation; the fiberwise formula and inverse are established below. -/
def contactHorizontalLift :
    Bundle.TotalSpace E (contactPullbackFiber Q) →
      TangentBundle (I (E := E)) (SphereBundleTotal Q) :=
  fun t => ⟨t.1, (contactPullbackHorizontalEquiv Q D t.1 t.2).1⟩

theorem contactHorizontalLift_mem (t : Bundle.TotalSpace E (contactPullbackFiber Q)) :
    (contactHorizontalLift Q D t).2 ∈
      horizontalTangentSubmodule Q D (contactHorizontalLift Q D t).1 :=
  (contactPullbackHorizontalEquiv Q D t.1 t.2).2

theorem contactHorizontalLift_projection (t : Bundle.TotalSpace E (contactPullbackFiber Q)) :
    (contactHorizontalLift Q D t).1 = t.1 := rfl

/-- The differential of the genuine twistor projection is a left inverse
to horizontal lift on each fiber. -/
theorem sphereProjection_mfderiv_horizontalLift
    (z : SphereBundleTotal Q) (u : contactPullbackFiber Q z) :
    mfderiv (I (E := E)) 𝓘(ℝ,E)
      (fun w : SphereBundleTotal Q => w.1) z
      (contactHorizontalLift Q D ⟨z,u⟩).2 = u := by
  rw [sphereProjection_mfderiv Q z]
  change ((contactPullbackHorizontalEquiv Q D z u :
    horizontalTangentSubmodule Q D z) : TangentSpace (I (E := E)) z).1 = u
  rw [contactPullbackHorizontalEquiv_apply]
  simp [connectionTangentEquiv,
    ManifoldTwistorHorizontalConnection.connectionSplit, preferredTangentEquiv,
    LinearEquiv.prodCongr, AddEquiv.prodCongr, Equiv.prodCongr]

/-- Every horizontal tangent vector is the lift of its base projection. -/
theorem contactHorizontalLift_surjective_fiber (z : SphereBundleTotal Q)
    (v : TangentSpace (I (E := E)) z)
    (hv : v ∈ horizontalTangentSubmodule Q D z) :
    contactHorizontalLift Q D ⟨z,v.1⟩ =
      (⟨z,v⟩ : TangentBundle (I (E := E)) (SphereBundleTotal Q)) := by
  apply Bundle.TotalSpace.ext
  · rfl
  · apply heq_of_eq
    change ((contactPullbackHorizontalEquiv Q D z v.1 :
      horizontalTangentSubmodule Q D z) : TangentSpace (I (E := E)) z) = v
    rw [contactPullbackHorizontalEquiv_apply]
    have h := (mem_horizontalTangentSubmodule_iff Q D z v).mp hv
    apply (connectionTangentEquiv Q D z).injective
    rw [(connectionTangentEquiv Q D z).apply_symm_apply]
    exact Prod.ext rfl h.symm

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
