import QuaternionicSymmetry.ManifoldQuaternionicInducedConnectionAlgebra
import QuaternionicSymmetry.ManifoldQuaternionicAdaptedRectangularSmooth

/-! Differentiating the genuine quaternionic intertwining identity at a
preferred immersion chart center. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedConnectionDifferential
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTotalGeodesy
open ManifoldQuaternionicAdaptedRectangularSmooth
open ManifoldQuaternionicInducedConnectionAlgebra
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open Filter
open scoped Manifold ContDiff Topology
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

private abbrev R3 := Fin 3 → ℝ

include hSmooth in
theorem eventually_adapted_intertwining (c : N) :
    let e := extChartAt 𝓘(ℝ,F) c
    ∀ᶠ y in 𝓝 (e c), ∀ (a : R3) (v : F),
      adaptedRectangularDerivative P R ι c (ι c) y
        (synth (R.tangent.reduction.Q (achart F c)) a v) =
      synth (P.tangent.reduction.Q (achart E (ι c)))
        (localCoefficientInChart P R ι hι hR c y a)
        (adaptedRectangularDerivative P R ι c (ι c) y v) := by
  let e := extChartAt 𝓘(ℝ,F) c
  let y₀ := e c
  have hc : c ∈ e.source := mem_extChartAt_source c
  have hy₀ : y₀ ∈ e.target := e.map_source hc
  have hsymm : ContinuousAt (e.symm : F → N) y₀ :=
    (contMDiffOn_extChartAt_symm (n := ∞) c y₀ hy₀).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) c).mem_nhds hy₀)
      |>.continuousAt
  have heq : e.symm y₀ = c := e.left_inv hc
  have hcomp : ContinuousAt (fun y : F => ι (e.symm y)) y₀ :=
    hSmooth.continuous.continuousAt.comp hsymm
  have hs : ∀ᶠ y in 𝓝 y₀, y ∈ e.target :=
    (isOpen_extChartAt_target (I := 𝓘(ℝ,F)) c).mem_nhds hy₀
  have ht : ∀ᶠ y in 𝓝 y₀,
      ι (e.symm y) ∈ (extChartAt 𝓘(ℝ,E) (ι c)).source := by
    apply hcomp.eventually
    change ∀ᶠ y in 𝓝 (ι (e.symm y₀)),
      y ∈ (extChartAt 𝓘(ℝ,E) (ι c)).source
    rw [heq]
    exact (isOpen_extChartAt_source (I := 𝓘(ℝ,E)) (ι c)).mem_nhds
      (mem_extChartAt_source (ι c))
  filter_upwards [hs, ht] with y hy₁ hy₂ a v
  have h := adaptedRectangularDerivative_intertwines_on_overlap
    P R ι hι hR c (ι c) y ⟨hy₁,hy₂⟩ a v
  simpa only [localCoefficientInChart,
    ManifoldQuaternionicInducedLocalCoefficientJointSmooth.localCoefficientCLM] using h

include hSmooth in
theorem fderiv_adapted_intertwining_at_center
    (c : N) (u : F) (a : R3) (v : F) :
    let y := extChartAt 𝓘(ℝ,F) c c
    let A := adaptedRectangularDerivative P R ι c (ι c)
    let C := localCoefficientInChart P R ι hι hR c
    (fderiv ℝ A y u)
        (synth (R.tangent.reduction.Q (achart F c)) a v) =
      synth (P.tangent.reduction.Q (achart E (ι c)))
        ((fderiv ℝ C y u) a) (A y v) +
      synth (P.tangent.reduction.Q (achart E (ι c)))
        (C y a) ((fderiv ℝ A y u) v) := by
  exact fderiv_of_rectangular_intertwining
    (synth (R.tangent.reduction.Q (achart F c)))
    (synth (P.tangent.reduction.Q (achart E (ι c))))
    (adaptedRectangularDerivative P R ι c (ι c))
    (localCoefficientInChart P R ι hι hR c)
    (extChartAt 𝓘(ℝ,F) c c)
    (adaptedRectangularDerivative_differentiableAt_center P R ι hSmooth c)
    (localCoefficientInChart_differentiableAt_center P R ι hSmooth hι hR c)
    (eventually_adapted_intertwining P R ι hSmooth hι hR c) u a v

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedConnectionDifferential
