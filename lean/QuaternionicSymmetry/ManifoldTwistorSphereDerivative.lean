import QuaternionicSymmetry.ManifoldTwistorHorizontalOverlap
import QuaternionicSymmetry.ManifoldTwistorSphereCore
/-! The affine transition used in the local horizontal connection is the
Fréchet derivative of the actual rotating sphere coordinate change after
embedding the sphere in its ambient three-space. -/

namespace QuaternionicSymmetry.ManifoldTwistorHorizontalOverlap
open QuaternionicSymmetry.ManifoldQuaternionicAdjointOverlap
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E]
 [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
private abbrev V := Fin 3 → ℝ

def ambientSphereTransition (p q : M) : E × V → E × V :=
 fun ya => (chartTransition (I := 𝓘(ℝ,E)) p q ya.1,
   rankThreeGauge Q p q ya.1 ya.2)

theorem ambientSphereTransition_fderiv (p q : M) (y : E) (a : V)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q) (uv : E × V) :
    fderiv ℝ (ambientSphereTransition Q p q) (y,a) uv =
      ambientTransition Q p q y a uv := by
  have hphi : DifferentiableAt ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y :=
    (chartTransition_contDiffAt p q y hy).differentiableAt (by norm_num)
  have hg : DifferentiableAt ℝ (rankThreeGauge Q p q) y :=
    (rankThreeGauge_contDiffAt Q p q y hy (by exact ENat.LEInfty.out)).differentiableAt
      (by norm_num)
  have hphi' := hphi.hasFDerivAt.comp (y,a) (hasFDerivAt_fst (𝕜 := ℝ))
  have hg' := hg.hasFDerivAt.comp (y,a) (hasFDerivAt_fst (𝕜 := ℝ))
  have happ := hg'.clm_apply (hasFDerivAt_snd (𝕜 := ℝ))
  have hprod := hphi'.prodMk happ
  have heq := congrArg (fun L : (E × V) →L[ℝ] (E × V) => L uv) hprod.fderiv
  simpa [ambientSphereTransition, ambientTransition, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, add_comm] using heq
theorem ambientSphereTransition_sphereCore (p q : M) (y : E)
    (s : geometricSphere)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q) :
    (ambientSphereTransition Q p q
      (y, (coefficientSphereHomeomorph.symm s).1)).2 =
      (coefficientSphereHomeomorph.symm
        ((sphereCore Q).coordChange (achart E p) (achart E q)
          ((extChartAt 𝓘(ℝ,E) p).symm y) s)).1 := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  have hp : x ∈ Q.frames.adaptedCore.baseSet (achart E p) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using
      (extChartAt 𝓘(ℝ,E) p).map_target hy.1
  have hq : x ∈ Q.frames.adaptedCore.baseSet (achart E q) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using hy.2
  change Q.reduction.rankThreeCoordChange (achart E p) (achart E q) x
      (coefficientSphereHomeomorph.symm s).1 =
    (coefficientSphereHomeomorph.symm
      (euclideanSphereCoordChange Q (achart E p) (achart E q) x s)).1
  dsimp [euclideanSphereCoordChange]
  rw [dif_pos ⟨hp,hq⟩]
  rfl
end
end QuaternionicSymmetry.ManifoldTwistorHorizontalOverlap
