import QuaternionicSymmetry.ManifoldQuaternionicInducedLocalSphereSmooth
import QuaternionicSymmetry.ManifoldQuaternionicInducedTwistorMap
import QuaternionicSymmetry.ManifoldQuaternionicTwistorLocalAction

/-! The fixed-chart sphere map is the chart expression of the actual
derivative-induced twistor map. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedSphereChartIdentity
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicInducedCoefficientMap
open ManifoldQuaternionicInducedLocalIntertwining
open ManifoldQuaternionicInducedLocalSphereSmooth
open ManifoldQuaternionicTwistorLocalAction
open ManifoldTwistorSphereBundle
open ManifoldTwistorSphereCore
open ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff
noncomputable section

variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (R : PositiveQuaternionicKahlerGeometry (E := F) (M := N))
  (ι : N → M)
  (hι : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
  (hR : IsInducedQuaternionicGeometry P R ι)

private theorem chartCoefficient_eq_transition
    {G X : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G] [Nontrivial G]
    [TopologicalSpace X] [ChartedSpace G X] [IsManifold 𝓘(ℝ,G) ∞ X]
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,G)) (M := X) (n := ∞))
    (i : atlas G X) (z : SphereBundleTotal Q)
    (hi : z.1 ∈ (sphereCore Q).baseSet i) :
    EuclideanSpace.equiv (Fin 3) ℝ (((sphereCore Q).localTriv i z).2 : EuclideanThree) =
      Q.reduction.rankThreeCoordChange (achart G z.1) i z.1
        (coefficientSphereHomeomorph.symm z.2).1 := by
  rw [(sphereCore Q).localTriv_apply]
  change (EuclideanSpace.equiv (Fin 3) ℝ)
    (euclideanSphereCoordChange Q (achart G z.1) i z.1 z.2).1 = _
  dsimp [euclideanSphereCoordChange]
  rw [dif_pos ⟨(sphereCore Q).mem_baseSet_at z.1, hi⟩]
  rfl

theorem sphereChartCoefficient_of_induced
    (c : N) (z : SphereBundleTotal R.tangent)
    (hx : z.1 ∈ (chartAt F c).source)
    (hy : ι z.1 ∈ (chartAt E (ι c)).source) :
    EuclideanSpace.equiv (Fin 3) ℝ
        ((((sphereCore P.tangent).localTriv (achart E (ι c))
          (sphereTotalMap P R ι hι hR z)).2) : EuclideanThree) =
      localCoefficientMap P R ι hι hR (achart F c) (achart E (ι c)) z.1
        (EuclideanSpace.equiv (Fin 3) ℝ
          ((((sphereCore R.tangent).localTriv (achart F c) z).2) : EuclideanThree)) := by
  have hs := chartCoefficient_eq_transition R.tangent (achart F c) z hx
  have ht := chartCoefficient_eq_transition P.tangent (achart E (ι c))
    (sphereTotalMap P R ι hι hR z) hy
  rw [ht, hs]
  change P.tangent.reduction.rankThreeCoordChange
      (achart E (ι z.1)) (achart E (ι c)) (ι z.1)
      (coefficientMap P R ι hι hR z.1
          (coefficientSphereHomeomorph.symm z.2).1) =
    P.tangent.reduction.rankThreeCoordChange
      (achart E (ι z.1)) (achart E (ι c)) (ι z.1)
      (coefficientMap P R ι hι hR z.1
        (R.tangent.reduction.rankThreeCoordChange
          (achart F c) (achart F z.1) z.1
          (R.tangent.reduction.rankThreeCoordChange
            (achart F z.1) (achart F c) z.1
            (coefficientSphereHomeomorph.symm z.2).1)))
  have hself := R.tangent.frames.adaptedCore.mem_baseSet_at z.1
  rw [R.tangent.reduction.rankThreeCoordChange_comp
      (achart F z.1) (achart F c) (achart F z.1) z.1 hself hx hself]
  rw [R.tangent.reduction.rankThreeCoordChange_self
      (achart F z.1) z.1 hself]

theorem localSphereMap_eq_lift_chart
    (c : N) (z : SphereBundleTotal R.tangent)
    (hx : z.1 ∈ (chartAt F c).source)
    (hy : ι z.1 ∈ (chartAt E (ι c)).source) :
    localSphereMap P R ι hι hR c
      ((sphereCore R.tangent).localTriv (achart F c) z) =
      ((sphereCore P.tangent).localTriv (achart E (ι c))
        (sphereTotalMap P R ι hι hR z)).2 := by
  apply Subtype.ext
  change localSphereAmbient P R ι hι hR c
      ((sphereCore R.tangent).localTriv (achart F c) z) = _
  have hbase : (((sphereCore R.tangent).localTriv (achart F c) z).1) = z.1 :=
    rfl
  rw [localSphereAmbient, if_pos (by simpa only [hbase] using And.intro hx hy)]
  have hc := sphereChartCoefficient_of_induced P R ι hι hR c z hx hy
  exact (congrArg (EuclideanSpace.equiv (Fin 3) ℝ).symm hc).symm

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedSphereChartIdentity
