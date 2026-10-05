import QuaternionicSymmetry.ManifoldQuaternionicAdaptedGaugeProducts
import QuaternionicSymmetry.GeneralConnectionGaugePullback
import QuaternionicSymmetry.GeneralConnectionGaugeLocalCongruence

/-! Affine overlap of the concrete adapted Levi-Civita form follows from
ordinary coordinate LC overlap and the actual tangent-gauge products. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaOverlap

open Filter Manifold Bundle GeneralLeviCivitaSource
open ManifoldQuaternionicConnection
  (solder adaptedGauge adaptedGaugeInv chartTransition_contDiffAt
    adaptedGauge_contDiffAt adaptedGauge_inverse)
open ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicFrameGaugeInfinity
open ManifoldQuaternionicAdaptedLeviCivitaForm
open ManifoldQuaternionicAdaptedGaugeProducts
open GeneralLeviCivitaChartDerivativeInverse
open GeneralConnectionGaugePullback
open GeneralConnectionGaugeLocalCongruence
open LocalConnectionGauge LocalConnectionCoordinatePullback
open scoped Manifold ContDiff Topology
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ConnectedSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
    (TangentSpace 𝓘(ℝ,E) : M → Type _))
  (D : CoordinateLeviCivitaConnection g)

theorem adaptedLeviCivitaForm_overlap (p q : M) (y : E)
    (hy : y ∈ chartOverlap p q) :
    adaptedLeviCivitaForm Q g D p y =
      LocalConnectionGauge.transform
        (LocalConnectionCoordinatePullback.pullback
          (adaptedLeviCivitaForm Q g D q) (chartTransition p q))
        (adaptedGauge Q p q) (adaptedGaugeInv Q p q) y := by
  let φ : E → E := chartTransition p q
  let C : E → E →L[ℝ] E := chartDerivative p q
  let Ci : E → E →L[ℝ] E := chartInverseDerivative p q
  let Ip := coordinateInverse Q p
  let Iq := coordinateInverse Q q
  let Sp := solder Q p
  let Sq := solder Q q
  let G := adaptedGauge Q p q
  let H := adaptedGaugeInv Q p q
  let z := φ y
  have hz : z ∈ (extChartAt 𝓘(ℝ,E) q).target :=
    (extChartAt 𝓘(ℝ,E) q).map_source hy.2
  have hφ2 : ContDiffAt ℝ 2 φ y :=
    chartTransition_contDiffAt (I := 𝓘(ℝ,E)) p q y hy
  have hφ : DifferentiableAt ℝ φ y := hφ2.differentiableAt (by norm_num)
  have hC : DifferentiableAt ℝ C y := by
    exact (hφ2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hIp : DifferentiableAt ℝ Ip y :=
    (coordinateInverse_contDiffAt_infinity Q p y hy.1).differentiableAt (by simp)
  have hIq : DifferentiableAt ℝ Iq z :=
    (coordinateInverse_contDiffAt_infinity Q q z hz).differentiableAt (by simp)
  have hG : DifferentiableAt ℝ G y :=
    (adaptedGauge_contDiffAt Q p q y hy
      (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)).differentiableAt
        (by norm_num)
  have hIqφ : DifferentiableAt ℝ (Iq ∘ φ) y := hIq.comp y hφ
  have hCiC : Ci y * C y = 1 :=
    chartInverseDerivative_mul_chartDerivative p q y hy
  have hSqIq : Sq z * Iq z = 1 := coordinateInverse_right Q q z hz
  have hDover := D.overlap p q y hy
  have hsource : adaptedLeviCivitaForm Q g D p y =
      LocalConnectionGauge.transform (pullback (D.form q) φ)
        (fun w => C w * Ip w) (fun w => Sp w * Ci w) y := by
    calc
      _ = transform (D.form p) Ip Sp y := rfl
      _ = transform (transform (pullback (D.form q) φ) C Ci) Ip Sp y :=
        transform_congr_at (D.form p)
          (transform (pullback (D.form q) φ) C Ci)
          Ip Ip Sp Sp y hDover Filter.EventuallyEq.rfl rfl
      _ = _ := transform_comp (pullback (D.form q) φ)
        C Ci Ip Sp y hC hIp hCiC
  have hqpull : pullback (adaptedLeviCivitaForm Q g D q) φ y =
      transform (pullback (D.form q) φ) (Iq ∘ φ) (Sq ∘ φ) y := by
    change pullback (transform (D.form q) Iq Sq) φ y = _
    exact pullback_transform (D.form q) Iq Sq φ y hφ hIq
  have htarget : transform
      (pullback (adaptedLeviCivitaForm Q g D q) φ) G H y =
      transform (pullback (D.form q) φ)
        (fun w => Iq (φ w) * G w)
        (fun w => H w * Sq (φ w)) y := by
    calc
      _ = transform
          (transform (pullback (D.form q) φ) (Iq ∘ φ) (Sq ∘ φ)) G H y :=
        transform_congr_at
          (pullback (adaptedLeviCivitaForm Q g D q) φ)
          (transform (pullback (D.form q) φ) (Iq ∘ φ) (Sq ∘ φ))
          G G H H y hqpull Filter.EventuallyEq.rfl rfl
      _ = _ := transform_comp (pullback (D.form q) φ)
        (Iq ∘ φ) (Sq ∘ φ) G H y hIqφ hG hSqIq
  have hprodG : (fun w => C w * Ip w) =ᶠ[𝓝 y]
      (fun w => Iq (φ w) * G w) := by
    filter_upwards [(ManifoldQuaternionicConnection.chartOverlap_isOpen
      (I := 𝓘(ℝ,E)) p q).mem_nhds hy] with w hw
    exact (coordinateInverse_mul_adaptedGauge Q p q w hw).symm
  have hprodH : H y * Sq (φ y) = Sp y * Ci y :=
    adaptedGaugeInv_mul_solder Q p q y hy
  calc
    adaptedLeviCivitaForm Q g D p y =
        transform (pullback (D.form q) φ)
          (fun w => C w * Ip w) (fun w => Sp w * Ci w) y := hsource
    _ = transform (pullback (D.form q) φ)
          (fun w => Iq (φ w) * G w)
          (fun w => H w * Sq (φ w)) y :=
        transform_congr_at (pullback (D.form q) φ)
          (pullback (D.form q) φ)
          (fun w => C w * Ip w) (fun w => Iq (φ w) * G w)
          (fun w => Sp w * Ci w) (fun w => H w * Sq (φ w))
          y rfl hprodG hprodH.symm
    _ = _ := htarget.symm

end
end QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaOverlap
