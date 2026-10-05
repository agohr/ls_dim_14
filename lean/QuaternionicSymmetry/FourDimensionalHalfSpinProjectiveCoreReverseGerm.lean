import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualReversePoint
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreMixedGerm
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthDerivative

/-! The literal projective bundle-core coordinate change from source
affine chart 1 to target affine chart 0 has the reverse mixed Möbius germ
on each genuine refined adapted-frame overlap. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreReverseGerm

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinProjectiveActualReversePoint
  FourDimensionalHalfSpinProjectiveReverseMixedGaugeAlgebra
  FourDimensionalHalfSpinProjectiveCoreMixedGerm
  FourDimensionalHalfSpinProjectiveCoreTransitionGerm
  FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinProjectivePreferredSecondPoint
  FourDimensionalHalfSpinProjectiveNorthDerivative
  FourDimensionalHalfSpinProjectiveSecondMobius
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

def coreReverseTransition (p q : M) (t : ℍ × ℂ) : ℍ × ℂ :=
  (chartTransition (I := 𝓘(ℝ, ℍ)) p q t.1,
    ((projectiveChart 1 0)
      (spinorCoordChange Q (achart ℍ p) (achart ℍ q)
        ((extChartAt 𝓘(ℝ, ℍ) p).symm t.1,
          secondAffineSpinorPoint t.2))) 0)

theorem actual_core_reverse_transition (p q : M) (lift : unitary ℍ)
    (y : ℍ)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (w : ℂ)
    (hden : reverseDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) w ≠ 0) :
    coreReverseTransition Q p q (y,w) =
      (chartTransition (I := 𝓘(ℝ, ℍ)) p q y,
        reverseMobius
          (halfSpinMatrix
            (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) w) := by
  apply Prod.ext
  · rfl
  · have hcore : spinorCoordChange Q (achart ℍ p) (achart ℍ q)
        ((extChartAt 𝓘(ℝ, ℍ) p).symm y, secondAffineSpinorPoint w) =
        spinorTransition Q (achart ℍ p) (achart ℍ q)
          ((extChartAt 𝓘(ℝ, ℍ) p).symm y) hx.1.1 hx.1.2
          (secondAffineSpinorPoint w) := by
        dsimp [spinorCoordChange]
        rw [dif_pos ⟨hx.1.1, hx.1.2⟩]
    change ((projectiveChart 1 0)
      (spinorCoordChange Q (achart ℍ p) (achart ℍ q)
        ((extChartAt 𝓘(ℝ, ℍ) p).symm y, secondAffineSpinorPoint w))) 0 = _
    rw [hcore, actualTransition_reversePoint Q p q lift y hx w hden]
    rw [affineSpinorPoint_eq_projectiveChart]
    rw [(projectiveChart 1 0).right_inv (by
      rw [projectiveChart_target]
      trivial)]
    rfl

theorem coreReverseTransition_eventuallyEq (p q : M) (lift : unitary ℍ)
    (y : ℍ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (w : ℂ)
    (hden : reverseDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) w ≠ 0) :
    coreReverseTransition Q p q =ᶠ[𝓝 (y,w)]
      (fun t =>
        (chartTransition (I := 𝓘(ℝ, ℍ)) p q t.1,
          reverseMobius
            (halfSpinMatrix
              (scalarChart Q p (achart ℍ p) (achart ℍ q) lift t.1)) t.2)) := by
  let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
  let G : ℍ → Mat2 := fun t => halfSpinMatrix (r t)
  have hr : DifferentiableAt ℝ r y :=
    scalarLift_chart_differentiableAt Q p (achart ℍ p) (achart ℍ q)
      lift y hy.1 hx
  let L : ℍ →L[ℝ] Mat2 := halfSpinMatrixLinear.toContinuousLinearMap
  have hG : DifferentiableAt ℝ G y := L.differentiableAt.comp y hr
  have hGprod : DifferentiableAt ℝ
      (fun t : ℍ × ℂ => G t.1) (y,w) := by
    change DifferentiableAt ℝ (G ∘ Prod.fst) (y,w)
    exact (hG.hasFDerivAt.comp (y,w)
      (hasFDerivAt_fst (𝕜 := ℝ))).differentiableAt
  have hdenCont : ContinuousAt
      (fun t : ℍ × ℂ => reverseDen (G t.1) t.2) (y,w) := by
    have hd : DifferentiableAt ℝ
        (fun t : ℍ × ℂ => reverseDen (G t.1) t.2) (y,w) := by
      dsimp [reverseDen, secondNum]
      fun_prop
    exact hd.continuousAt
  have hdenEv : ∀ᶠ t : ℍ × ℂ in 𝓝 (y,w),
      reverseDen (G t.1) t.2 ≠ 0 :=
    hdenCont.eventually_ne (by exact hden)
  have hfst : Filter.Tendsto (Prod.fst : ℍ × ℂ → ℍ)
      (𝓝 (y,w)) (𝓝 y) := continuousAt_fst
  have hinv : Filter.Tendsto (extChartAt 𝓘(ℝ, ℍ) p).symm
      (𝓝 y) (𝓝 ((extChartAt 𝓘(ℝ, ℍ) p).symm y)) :=
    continuousAt_extChartAt_symm'' hy.1
  have hxEv : ∀ᶠ t : ℍ × ℂ in 𝓝 (y,w),
      (extChartAt 𝓘(ℝ, ℍ) p).symm t.1 ∈
        liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift :=
    (hinv.comp hfst).eventually
      ((isOpen_liftNeighborhood Q _ _ lift).mem_nhds hx)
  filter_upwards [hxEv, hdenEv] with t hxt hdt
  exact actual_core_reverse_transition Q p q lift t.1 hxt t.2 hdt

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreReverseGerm
