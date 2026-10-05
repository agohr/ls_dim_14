import QuaternionicSymmetry.ManifoldQuaternionicTwistorIsometryDiffeomorph
import QuaternionicSymmetry.ManifoldRiemannianFixedComponentGenericInput

/-! Identify the generic Riemannian fixed-set input with the actual lifted
quaternionic-isometry subgroup, and relate its points to base fixed points. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorLiftedFixedSet

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicTwistorIsometryDiffeomorph
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

def liftedSet (S : Subgroup (QuaternionicIsometries Q)) :
    Set (Diffeomorph (J (E := E)) (J (E := E))
      (SphereBundleTotal Q) (SphereBundleTotal Q) ∞) :=
  Set.range (fun f : S => realLift Q f.1)

def fixedSpherePoints (S : Subgroup (QuaternionicIsometries Q)) :
    Set (SphereBundleTotal Q) :=
  ManifoldRiemannianFixedComponentGenericInput.fixedPoints
    (F := E × EuclideanSpace ℝ (Fin 2))
    (H := ModelProd E (EuclideanSpace ℝ (Fin 2)))
    (N := SphereBundleTotal Q)
    (J (E := E)) (liftedSet Q S)

theorem mem_fixedSpherePoints_iff
    (S : Subgroup (QuaternionicIsometries Q)) (z : SphereBundleTotal Q) :
    z ∈ fixedSpherePoints Q S ↔
      ∀ f ∈ S, sphereTotalMap Q f z = z := by
  constructor
  · intro hz f hf
    change ∀ g ∈ liftedSet Q S, g z = z at hz
    have h := hz (realLift Q f) ⟨⟨f,hf⟩,rfl⟩
    simpa only [realLift_apply] using h
  · intro hz
    change ∀ g ∈ liftedSet Q S, g z = z
    intro g hg
    obtain ⟨f,rfl⟩ := hg
    exact (realLift_apply Q f z).trans (hz f.1 f.2)

theorem fixedSpherePoints_base_fixed
    (S : Subgroup (QuaternionicIsometries Q))
    (z : SphereBundleTotal Q) (hz : z ∈ fixedSpherePoints Q S) :
    z.1 ∈ fixedPoints Q S := by
  intro f hf
  have h := (mem_fixedSpherePoints_iff Q S z).mp hz f hf
  have hb := congrArg (fun w : SphereBundleTotal Q => w.1) h
  change (sphereTotalMap Q f z).1 = z.1 at hb
  rw [sphereTotalMap_base Q f z] at hb
  exact hb

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorLiftedFixedSet
