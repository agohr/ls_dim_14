import QuaternionicSymmetry.ManifoldQuaternionicInducedConnectionDifferential
import QuaternionicSymmetry.ManifoldQuaternionicAdjointConnection
import QuaternionicSymmetry.ManifoldQuaternionicIntrinsicTwistorComparison
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-! Rank-three connection covariance for an actual totally geodesic
quaternionic immersion. No connection naturality is assumed by the source. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedConnectionCovariance
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTotalGeodesy
open ManifoldQuaternionicAdaptedRectangularSmooth
open ManifoldQuaternionicInducedConnectionDifferential
open ManifoldQuaternionicInducedConnectionAlgebra
open ManifoldQuaternionicAdjointConnection
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldTwistorSphereBundle
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open Filter
open scoped Manifold ContDiff Matrix Topology
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
  (hSmooth : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
  (hι : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
  (hR : IsInducedQuaternionicGeometry P R ι)
  (DP : ManifoldQuaternionicConnection.CompatibleTangentConnection P.tangent)
  (DR : ManifoldQuaternionicConnection.CompatibleTangentConnection R.tangent)

private abbrev R3 := Fin 3 → ℝ

private theorem synth_coeff_zero_of_nonzero
    (S : QuaternionicStructure E) (b : R3) (w : E)
    (hw : w ≠ 0) (h : synth S b w = 0) : b = 0 := by
  have hs := congrArg (fun T : E →L[ℝ] E => T w) (synth_square S b)
  simp only [pow_two, ContinuousLinearMap.mul_apply, h, map_zero,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] at hs
  have hb : squareNorm b = 0 := by
    have hz : -(squareNorm b) = 0 :=
      (smul_eq_zero.mp hs.symm).resolve_right hw
    exact neg_eq_zero.mp hz
  have hb' : b ⬝ᵥ b = 0 := by simpa [squareNorm, dotProduct] using hb
  exact dotProduct_self_eq_zero.mp hb'

private theorem inducedForm_commutator
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (p : M) (y u : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : R3) (v : E) :
    D.form p y u (synth (Q.reduction.Q (achart E p)) a v) -
      synth (Q.reduction.Q (achart E p)) a (D.form p y u v) =
      synth (Q.reduction.Q (achart E p))
        (inducedForm Q D p y u a) v := by
  have h := congrArg (fun T : E →L[ℝ] E => T v)
    (synth_inducedForm Q D p y u hy a)
  simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
    using h.symm

include hSmooth in
/-- The rank-three connection of the induced geometry is the pullback of
the ambient rank-three connection along the actual rectangular immersion
and its coefficient map, at every preferred chart center. -/
theorem induced_connection_covariance_at_center
    (hTot : IsTotallyGeodesic P R ι DP DR)
    (c : N) (u : F) (a : R3) :
    let y := extChartAt 𝓘(ℝ,F) c c
    let C := localCoefficientInChart P R ι hι hR c
    (fderiv ℝ C y u) a +
      inducedForm P.tangent DP (ι c)
        (localBaseMap ι c (ι c) y)
        (fderiv ℝ (localBaseMap ι c (ι c)) y u) (C y a) =
      C y (inducedForm R.tangent DR c y u a) := by
  let e := extChartAt 𝓘(ℝ,F) c
  let y : F := e c
  let A := adaptedRectangularDerivative P R ι c (ι c)
  let C := localCoefficientInChart P R ι hι hR c
  let ΓR := DR.form c y u
  let ΓP := DP.form (ι c) (localBaseMap ι c (ι c) y)
    (fderiv ℝ (localBaseMap ι c (ι c)) y u)
  let ΩR := inducedForm R.tangent DR c y u
  let ΩP := inducedForm P.tangent DP (ι c)
    (localBaseMap ι c (ι c) y)
    (fderiv ℝ (localBaseMap ι c (ι c)) y u)
  have hc : c ∈ e.source := mem_extChartAt_source c
  have he : e.symm y = c := e.left_inv hc
  have hy : y ∈ immersionChartOverlap (E := E) (F := F)
      (M := M) (N := N) ι c (ι c) := by
    change y ∈ e.target ∧ ι (e.symm y) ∈
      (extChartAt 𝓘(ℝ,E) (ι c)).source
    exact ⟨e.map_source hc, by simpa only [he] using mem_extChartAt_source (ι c)⟩
  have hGy : localBaseMap ι c (ι c) y =
      extChartAt 𝓘(ℝ,E) (ι c) (ι c) := by
    change (extChartAt 𝓘(ℝ,E) (ι c)) (ι (e.symm y)) = _
    rw [he]
  have hPtarget : localBaseMap ι c (ι c) y ∈
      (extChartAt 𝓘(ℝ,E) (ι c)).target := by
    rw [hGy]
    exact (extChartAt 𝓘(ℝ,E) (ι c)).map_source
      (mem_extChartAt_source (ι c))
  have hAt : DifferentiableAt ℝ A y :=
    adaptedRectangularDerivative_differentiableAt_center P R ι hSmooth c
  have hCt : DifferentiableAt ℝ C y :=
    localCoefficientInChart_differentiableAt_center
      P R ι hSmooth hι hR c
  have hInter : ∀ᶠ z in 𝓝 y, ∀ (b : R3) (v : F),
      A z (synth (R.tangent.reduction.Q (achart F c)) b v) =
        synth (P.tangent.reduction.Q (achart E (ι c)))
          (C z b) (A z v) :=
    eventually_adapted_intertwining P R ι hSmooth hι hR c
  have hHess (v : F) : (fderiv ℝ A y u) v =
      -ΓP (A y v) + A y (ΓR v) :=
    derivative_of_totallyGeodesic P R ι DP DR hTot c (ι c) y hy u v
  have hCommR (b : R3) (v : F) :
      ΓR (synth (R.tangent.reduction.Q (achart F c)) b v) -
        synth (R.tangent.reduction.Q (achart F c)) b (ΓR v) =
      synth (R.tangent.reduction.Q (achart F c)) (ΩR b) v :=
    inducedForm_commutator R.tangent DR c y u hy.1 b v
  have hCommP (b : R3) (v : E) :
      ΓP (synth (P.tangent.reduction.Q (achart E (ι c))) b v) -
        synth (P.tangent.reduction.Q (achart E (ι c))) b (ΓP v) =
      synth (P.tangent.reduction.Q (achart E (ι c))) (ΩP b) v :=
    inducedForm_commutator P.tangent DP (ι c)
      (localBaseMap ι c (ι c) y)
      (fderiv ℝ (localBaseMap ι c (ι c)) y u) hPtarget b v
  obtain ⟨v, hv⟩ := exists_ne (0 : F)
  have hAinj : Function.Injective (A y) :=
    adaptedRectangularDerivative_injective_on_overlap P R ι hι c (ι c) y hy
  have hAv : A y v ≠ 0 := by
    intro hz
    exact hv (hAinj (by simpa only [map_zero] using hz))
  have hDefect := connection_defect_annihilates_image
    (synth (R.tangent.reduction.Q (achart F c)))
    (synth (P.tangent.reduction.Q (achart E (ι c))))
    A C y hAt hCt hInter u ΓR ΓP ΩR ΩP hHess hCommR hCommP a v
  have hCoeff := synth_coeff_zero_of_nonzero
    (P.tangent.reduction.Q (achart E (ι c)))
    ((fderiv ℝ C y u) a + ΩP (C y a) - C y (ΩR a))
    (A y v) hAv hDefect
  exact sub_eq_zero.mp hCoeff

include hSmooth in
/-- In coefficient coordinates, the differential of the induced sphere map
sends the actual connection-horizontal graph to the ambient one. This
linear identity is a direct consequence of the proved connection
covariance, and does not assume horizontal naturality. -/
theorem horizontal_coefficient_covariance_at_center
    (hTot : IsTotallyGeodesic P R ι DP DR)
    (c : N) (u : F) (a b : R3)
    (hHorizontal : b +
      inducedForm R.tangent DR c (chartAt F c c) u a = 0) :
    let y := chartAt F c c
    let C := localCoefficientInChart P R ι hι hR c
    ((fderiv ℝ C y u) a + C y b) +
      inducedForm P.tangent DP (ι c)
        (localBaseMap ι c (ι c) y)
        (fderiv ℝ (localBaseMap ι c (ι c)) y u) (C y a) = 0 := by
  have hCov := induced_connection_covariance_at_center
    P R ι hSmooth hι hR DP DR hTot c u a
  dsimp at hCov ⊢
  have hMap := congrArg
    (fun d : R3 => (localCoefficientInChart P R ι hι hR c)
      (chartAt F c c) d) hHorizontal
  simp only [map_add, map_zero] at hMap
  calc
    _ = (fderiv ℝ (localCoefficientInChart P R ι hι hR c)
        (chartAt F c c) u) a +
        inducedForm P.tangent DP (ι c)
          (localBaseMap ι c (ι c) (chartAt F c c))
          (fderiv ℝ (localBaseMap ι c (ι c))
            (chartAt F c c) u)
          ((localCoefficientInChart P R ι hι hR c)
            (chartAt F c c) a) +
        (localCoefficientInChart P R ι hι hR c)
          (chartAt F c c) b := by abel
    _ = _ := by rw [hCov]; simpa only [add_comm] using hMap

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedConnectionCovariance
