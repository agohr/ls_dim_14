import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualMixedPoint
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreTransitionGerm
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMixedFullDerivative

/-! The literal independently constructed projective bundle-core
coordinate change from source chart 0 to target chart 1 agrees locally
with the jointly varying mixed Möbius map. This is the actual core germ,
including points outside the CP¹ chart intersection. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreMixedGerm

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinProjectiveActualMixedPoint
  FourDimensionalHalfSpinProjectiveMixedGaugeAlgebra
  FourDimensionalHalfSpinProjectiveMixedFullDerivative
  FourDimensionalHalfSpinProjectiveCoreTransitionGerm
  FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinProjectivePreferredSecondPoint
  FourDimensionalHalfSpinMatrix
  FourDimensionalHalfSpinMatrixConnection
  FourDimensionalHalfSpinActualTransition
  FourDimensionalHalfSpinActualTransitionSmooth
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldLocalStandardMaurer
  QuaternionicManifoldProductGaugeDifferential
  ManifoldQuaternionicConnection
  ComplexProjectiveTopology

noncomputable section

local instance : NormedRing Mat2 := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ Mat2 := Matrix.linftyOpNormedAlgebra
local instance : NormedSpace ℝ Mat2 := NormedAlgebra.toNormedSpace _

private def halfSpinMatrixLinear : ℍ →ₗ[ℝ] Mat2 where
  toFun := halfSpinMatrix
  map_add' p q := halfSpinMatrix_add p q
  map_smul' c p := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      simp [halfSpinMatrix, first, second] <;> ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

def coreMixedTransition (p q : M) (t : ℍ × ℂ) : ℍ × ℂ :=
  (chartTransition (I := 𝓘(ℝ, ℍ)) p q t.1,
    ((projectiveChart 1 1)
      (spinorCoordChange Q (achart ℍ p) (achart ℍ q)
        ((extChartAt 𝓘(ℝ, ℍ) p).symm t.1,
          affineSpinorPoint t.2))) 0)

theorem actual_core_mixed_transition (p q : M) (lift : unitary ℍ)
    (y : ℍ)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (z : ℂ)
    (hden : mixedDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z ≠ 0) :
    coreMixedTransition Q p q (y,z) =
      jointMixedTransition
        (chartTransition (I := 𝓘(ℝ, ℍ)) p q)
        (fun t => halfSpinMatrix
          (scalarChart Q p (achart ℍ p) (achart ℍ q) lift t)) (y,z) := by
  apply Prod.ext
  · rfl
  · have hcore : spinorCoordChange Q (achart ℍ p) (achart ℍ q)
        ((extChartAt 𝓘(ℝ, ℍ) p).symm y, affineSpinorPoint z) =
        spinorTransition Q (achart ℍ p) (achart ℍ q)
          ((extChartAt 𝓘(ℝ, ℍ) p).symm y) hx.1.1 hx.1.2
          (affineSpinorPoint z) := by
        dsimp [spinorCoordChange]
        rw [dif_pos ⟨hx.1.1, hx.1.2⟩]
    change ((projectiveChart 1 1)
      (spinorCoordChange Q (achart ℍ p) (achart ℍ q)
        ((extChartAt 𝓘(ℝ, ℍ) p).symm y, affineSpinorPoint z))) 0 = _
    rw [hcore, actualTransition_mixedPoint Q p q lift y hx z hden]
    rw [secondAffineSpinorPoint]
    rw [(projectiveChart 1 1).right_inv (by
      rw [projectiveChart_target]
      trivial)]
    rfl

theorem coreMixedTransition_eventuallyEq (p q : M) (lift : unitary ℍ)
    (y : ℍ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (z : ℂ)
    (hden : mixedDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z ≠ 0) :
    coreMixedTransition Q p q =ᶠ[𝓝 (y,z)]
      jointMixedTransition
        (chartTransition (I := 𝓘(ℝ, ℍ)) p q)
        (fun t => halfSpinMatrix
          (scalarChart Q p (achart ℍ p) (achart ℍ q) lift t)) := by
  let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
  let G : ℍ → Mat2 := fun t => halfSpinMatrix (r t)
  have hr : DifferentiableAt ℝ r y :=
    scalarLift_chart_differentiableAt Q p (achart ℍ p) (achart ℍ q)
      lift y hy.1 hx
  let L : ℍ →L[ℝ] Mat2 := halfSpinMatrixLinear.toContinuousLinearMap
  have hG : DifferentiableAt ℝ G y := L.differentiableAt.comp y hr
  have hGprod : DifferentiableAt ℝ
      (fun t : ℍ × ℂ => G t.1) (y,z) := by
    change DifferentiableAt ℝ (G ∘ Prod.fst) (y,z)
    exact (hG.hasFDerivAt.comp (y,z)
      (hasFDerivAt_fst (𝕜 := ℝ))).differentiableAt
  have hdenCont : ContinuousAt
      (fun t : ℍ × ℂ => mixedDen (G t.1) t.2) (y,z) := by
    have hd : DifferentiableAt ℝ
        (fun t : ℍ × ℂ => mixedDen (G t.1) t.2) (y,z) := by
      dsimp [mixedDen, chartNum]
      fun_prop
    exact hd.continuousAt
  have hdenEv : ∀ᶠ t : ℍ × ℂ in 𝓝 (y,z),
      mixedDen (G t.1) t.2 ≠ 0 :=
    hdenCont.eventually_ne (by exact hden)
  have hfst : Filter.Tendsto (Prod.fst : ℍ × ℂ → ℍ)
      (𝓝 (y,z)) (𝓝 y) := continuousAt_fst
  have hinv : Filter.Tendsto (extChartAt 𝓘(ℝ, ℍ) p).symm
      (𝓝 y) (𝓝 ((extChartAt 𝓘(ℝ, ℍ) p).symm y)) :=
    continuousAt_extChartAt_symm'' hy.1
  have hxEv : ∀ᶠ t : ℍ × ℂ in 𝓝 (y,z),
      (extChartAt 𝓘(ℝ, ℍ) p).symm t.1 ∈
        liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift :=
    (hinv.comp hfst).eventually
      ((isOpen_liftNeighborhood Q _ _ lift).mem_nhds hx)
  filter_upwards [hxEv, hdenEv] with t hxt hdt
  exact actual_core_mixed_transition Q p q lift t.1 hxt t.2 hdt

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreMixedGerm
