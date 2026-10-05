import QuaternionicSymmetry.ManifoldQuaternionicTwistorLiftedFixedSet
import QuaternionicSymmetry.ManifoldQuaternionicTwistorMetricBilinear
import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff

/-! Isolate the remaining smooth-metric packaging step for applying the
literal BG-R2 fixed-component theorem to the actual lifted isometries.
The parameter below must be CONSTRUCTED from `splitMetricCLM`; it is not a
registered source premise or a final hypothesis. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorFixedComponentBridge

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicTwistorIsometryDiffeomorph
open ManifoldQuaternionicTwistorLiftedFixedSet
open ManifoldQuaternionicTwistorSplitMetric
open ManifoldRiemannianFixedComponentGenericInput
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)
private abbrev F := E × EuclideanSpace ℝ (Fin 2)

theorem realLift_preserves_packaged_splitMetric
    (g : SmoothMetric (F := F (E := E))
      (N := SphereBundleTotal Q) (J (E := E)))
    (hg : ∀ z (u v : TangentSpace (J (E := E)) z),
      g.inner z u v = splitMetric Q D z u v)
    (f : QuaternionicIsometries Q) :
    PreservesMetric (J (E := E)) g (realLift Q f) := by
  intro z u v
  change g.inner (sphereTotalMap Q f z)
    (mfderiv (J (E := E)) (J (E := E)) (sphereTotalMap Q f) z u)
    (mfderiv (J (E := E)) (J (E := E)) (sphereTotalMap Q f) z v) =
    g.inner z u v
  rw [hg, hg]
  exact splitMetric_sphereTotalMap Q D f z u v

/-- The literal BG-R2 conclusion on the actual lifted subgroup, once the
explicit invariant split metric has been packaged as a smooth Riemannian
metric. No fixed atlas is supplied as an input. -/
theorem exists_liftedFixedComponentAtlas_of_packaged_metric
    [T2Space M] [CompactSpace M]
    (hBG : RiemannianFixedComponentOnModel
      (F := F (E := E)) (H := ModelProd E (EuclideanSpace ℝ (Fin 2)))
      (N := SphereBundleTotal Q) (J (E := E)))
    (g : SmoothMetric (F := F (E := E))
      (N := SphereBundleTotal Q) (J (E := E)))
    (hg : ∀ z (u v : TangentSpace (J (E := E)) z),
      g.inner z u v = splitMetric Q D z u v)
    (S : Subgroup (QuaternionicIsometries Q))
    (z : SphereBundleTotal Q) (hz : z ∈ fixedSpherePoints Q S) :
    ∃ k : ℕ, Nonempty (FixedComponentAtlas (J (E := E))
      (liftedSet Q S) z k) := by
  apply hBG g (liftedSet Q S) ?_ z hz
  intro h hh
  obtain ⟨f,rfl⟩ := hh
  exact realLift_preserves_packaged_splitMetric Q D g hg f.1

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorFixedComponentBridge
