import QuaternionicSymmetry.ManifoldQuaternionicInducedConnectionCovariance

/-! Ordinary joint derivative of the actual rectangular coefficient field,
the base/fiber block needed for the global twistor horizontal map. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedCoefficientChartDerivative
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicAdaptedRectangularSmooth
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

private abbrev R3 := Fin 3 → ℝ

include hSmooth in
theorem coefficientJoint_fderiv_center
    (c : N) (a b : R3) (u : F) :
    let y := extChartAt 𝓘(ℝ,F) c c
    let C := localCoefficientInChart P R ι hι hR c
    fderiv ℝ (fun q : F × R3 => C q.1 q.2) (y,a) (u,b) =
      (fderiv ℝ C y u) a + C y b := by
  let y := extChartAt 𝓘(ℝ,F) c c
  let C := localCoefficientInChart P R ι hι hR c
  have hC : DifferentiableAt ℝ C y :=
    localCoefficientInChart_differentiableAt_center
      P R ι hSmooth hι hR c
  have hCpair : DifferentiableAt ℝ (fun q : F × R3 => C q.1) (y,a) :=
    by fun_prop
  have ha : DifferentiableAt ℝ (fun q : F × R3 => q.2) (y,a) :=
    differentiableAt_snd
  have hderiv := fderiv_clm_apply hCpair ha
  have hval := congrArg (fun L : (F × R3) →L[ℝ] R3 => L (u,b)) hderiv
  change fderiv ℝ (fun q : F × R3 => C q.1 q.2) (y,a) (u,b) = _ at hval
  have hCf : fderiv ℝ (fun q : F × R3 => C q.1) (y,a) =
      (fderiv ℝ C y).comp (ContinuousLinearMap.fst ℝ F R3) := by
    change fderiv ℝ (C ∘ (Prod.fst : F × R3 → F)) (y,a) = _
    rw [fderiv_comp (y,a) hC
      (differentiableAt_fst : DifferentiableAt ℝ
        (Prod.fst : F × R3 → F) (y,a)), fderiv_fst]
  rw [hCf] at hval
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.flip_apply, fderiv_snd] at hval
  simpa [ContinuousLinearMap.fst, ContinuousLinearMap.snd, add_comm] using hval

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedCoefficientChartDerivative
