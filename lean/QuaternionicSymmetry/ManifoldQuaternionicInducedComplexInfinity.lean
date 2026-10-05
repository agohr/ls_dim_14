import QuaternionicSymmetry.ManifoldQuaternionicInducedComplexAtlas
import QuaternionicSymmetry.ComplexSmoothRealInfinity

/-! Complex-C∞ regularity of the actual induced twistor immersion in
compatible source and target twistor atlases. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedComplexInfinity
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicInducedComplexAtlas
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open ComplexSmoothRealInfinity
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
  (hSmooth : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
  (hι : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
  (hR : IsInducedQuaternionicGeometry P R ι)
  (DP : ManifoldQuaternionicConnection.CompatibleTangentConnection P.tangent)
  (DR : ManifoldQuaternionicConnection.CompatibleTangentConnection R.tangent)
  (hTot : ManifoldQuaternionicInducedTotalGeodesy.IsTotallyGeodesic P R ι DP DR)

include hSmooth hTot in
theorem sphereTotalMap_contMDiff_complex_infty
    {m n : ℕ} (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n) :
    letI := A.charts
    letI := B.charts
    ContMDiff 𝓘(ℂ,ComplexTwistorModel m)
      𝓘(ℂ,ComplexTwistorModel n) ∞
      (sphereTotalMap P R ι hι hR) := by
  letI := A.charts
  letI := B.charts
  letI := A.realManifold
  letI := B.realManifold
  letI := A.complexManifold
  letI := B.complexManifold
  let G := ComplexTwistorModel m
  let H := ComplexTwistorModel n
  have hReal : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,H) ∞
      (sphereTotalMap P R ι hι hR) :=
    sphereTotalMap_realSmooth_in_compatibleAtlases
      P R ι hSmooth hι hR DP DR A B
  have hComplex : MDifferentiable 𝓘(ℂ,G) 𝓘(ℂ,H)
      (sphereTotalMap P R ι hι hR) :=
    sphereTotalMap_mdifferentiable_complex
      P R ι hSmooth hι hR DP DR hTot A B
  obtain ⟨hcont, hRealCharts⟩ := contMDiff_iff.mp hReal
  obtain ⟨_, hComplexCharts⟩ := mdifferentiable_iff.mp hComplex
  apply contMDiff_iff.mpr
  refine ⟨hcont, ?_⟩
  intro x y
  let s : Set G := (extChartAt 𝓘(ℂ,G) x).target ∩
    (extChartAt 𝓘(ℂ,G) x).symm ⁻¹'
      ((sphereTotalMap P R ι hι hR) ⁻¹'
        (extChartAt 𝓘(ℂ,H) y).source)
  have hs : IsOpen s := by
    apply (continuousOn_extChartAt_symm (I := 𝓘(ℂ,G)) x).isOpen_inter_preimage
      (isOpen_extChartAt_target (I := 𝓘(ℂ,G)) x)
    exact (isOpen_extChartAt_source (I := 𝓘(ℂ,H)) y).preimage hcont
  have hRealOn : ContDiffOn ℝ ∞
      (extChartAt 𝓘(ℂ,H) y ∘ sphereTotalMap P R ι hι hR ∘
        (extChartAt 𝓘(ℂ,G) x).symm) s := by
    simpa only [s] using hRealCharts x y
  have hC : DifferentiableOn ℂ
      (extChartAt 𝓘(ℂ,H) y ∘ sphereTotalMap P R ι hι hR ∘
        (extChartAt 𝓘(ℂ,G) x).symm) s := by
    simpa only [s] using hComplexCharts x y
  exact contDiffOn_infty_of_real_complex hs hRealOn hC

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedComplexInfinity
