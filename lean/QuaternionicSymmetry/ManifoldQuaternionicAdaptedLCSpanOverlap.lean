import QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaOverlap
import QuaternionicSymmetry.ManifoldQuaternionicGaugePlaneDerivative
import QuaternionicSymmetry.ManifoldQuaternionicGaugePlaneBackward
import QuaternionicSymmetry.ManifoldQuaternionicCommutatorSpan
import QuaternionicSymmetry.GeneralAdaptedQuaternionicSpanDescent

/-! Preservation of the fixed adapted quaternionic span propagates from
one chart value to every overlapping chart coordinate by the actual
affine Levi-Civita overlap and differentiable rank-three gauge. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicAdaptedLCSpanOverlap

open Filter Manifold Bundle GeneralLeviCivitaSource
open ManifoldQuaternionicConnection
open ManifoldQuaternionicAdaptedLeviCivitaForm
open ManifoldQuaternionicAdaptedLeviCivitaOverlap
open ManifoldQuaternionicGaugePlaneDerivative
open ManifoldQuaternionicGaugePlaneBackward
open ManifoldQuaternionicCommutatorSpan
open GeneralAdaptedQuaternionicSpanDescent
open ManifoldQuaternionicAdjointOverlap
open VectorBundleFrameTransitions
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

theorem adaptedLeviCivitaForm_commutator_overlap
    (p q : M) (y : E) (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
    (hcommq : ∀ (t : Fin 3) (v : E),
      let Λ := adaptedLeviCivitaForm Q g D q
        (chartTransition (I := 𝓘(ℝ,E)) p q y) v
      let J := quaternionicGenerator (Q.reduction.Q (achart E q)) t
      Λ * J - J * Λ ∈ quaternionicSpan (Q.reduction.Q (achart E q)))
    (t : Fin 3) (u : E) :
    let Γ := adaptedLeviCivitaForm Q g D p y u
    let J := quaternionicGenerator (Q.reduction.Q (achart E p)) t
    Γ * J - J * Γ ∈ quaternionicSpan (Q.reduction.Q (achart E p)) := by
  let G := adaptedGauge Q p q
  let H := adaptedGaugeInv Q p q
  let T := quaternionicGenerator (Q.reduction.Q (achart E p)) t
  let Λ := adaptedLeviCivitaForm Q g D q
    (chartTransition (I := 𝓘(ℝ,E)) p q y)
    (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y u)
  let Γ := adaptedLeviCivitaForm Q g D p y u
  let U := transportedOperator Q p q T
  have hgh : G y * H y = 1 := (adaptedGauge_inverse Q p q y hy).2
  have hhg : H y * G y = 1 := (adaptedGauge_inverse Q p q y hy).1
  have hG : DifferentiableAt ℝ G y :=
    (adaptedGauge_contDiffAt Q p q y hy
      (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)).differentiableAt
        (by norm_num)
  have hH : DifferentiableAt ℝ H y :=
    (adaptedGaugeInv_contDiffAt Q p q y hy
      (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)).differentiableAt
        (by norm_num)
  have hdh : fderiv ℝ H y u = -(H y * fderiv ℝ G y u * H y) :=
    LocalConnectionGauge.fderiv_inverse_pair G H y hG hH
      (adaptedGauge_inverse_eventually Q p q y hy) hgh u
  have hΓ : Γ = H y * (Λ * G y + fderiv ℝ G y u) := by
    have hover := congrArg (fun F : E →L[ℝ] E →L[ℝ] E => F u)
      (adaptedLeviCivitaForm_overlap Q g D p q y hy)
    simpa only [LocalConnectionGauge.transform_apply,
      LocalConnectionCoordinatePullback.pullback,
      ContinuousLinearMap.comp_apply] using hover
  have hT : T ∈ quaternionicSpan (Q.reduction.Q (achart E p)) :=
    generator_mem_span _ t
  have hvalues := transportedOperator_value_and_derivative_mem Q p q y hy T hT u
  have hcomm : Λ * (G y * T * H y) - (G y * T * H y) * Λ ∈
      quaternionicSpan (Q.reduction.Q (achart E q)) := by
    apply commutator_mem_of_generators _ Λ
      (fun s => hcommq s _)
    exact hvalues.1
  have hderiv : fderiv ℝ U y u =
      fderiv ℝ G y u * T * H y + G y * T * fderiv ℝ H y u :=
    fderiv_conjugate_const G H T y u hG hH
  exact affine_quaternionic_span_descent
    (Q.reduction.Q (achart E p)) (Q.reduction.Q (achart E q))
    (G y) (H y) Λ (fderiv ℝ G y u) Γ T (fderiv ℝ H y u)
    (fderiv ℝ U y u) hgh hhg hΓ hdh hvalues.1 hcomm hderiv hvalues.2
    (fun V hV => inverseGauge_mem_quaternionicSpan Q p q y hy V hV)

end
end QuaternionicSymmetry.ManifoldQuaternionicAdaptedLCSpanOverlap
