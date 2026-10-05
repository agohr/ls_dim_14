import QuaternionicSymmetry.ManifoldQuaternionicInducedCoefficientChartDerivative
import QuaternionicSymmetry.ManifoldQuaternionicIsometrySphereDerivative

/-! The genuine induced sphere differential in local coefficient charts. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedSphereDerivative
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedLocalIntertwining
open ManifoldQuaternionicAdaptedRectangularSmooth
open ManifoldQuaternionicInducedLocalSphereSmooth
open ManifoldQuaternionicInducedCoefficientChartDerivative
open ManifoldQuaternionicIsometrySphereDerivative
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorVerticalComplex
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

private abbrev JF := 𝓘(ℝ,F).prod (𝓡 2)
private abbrev R3 := Fin 3 → ℝ
local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

def localSphereCoefficients (c : N) (q : N × geometricSphere) : R3 :=
  sphereCoefficients (localSphereMap P R ι hι hR c q)

include hSmooth in
theorem localSphereCoefficients_eq_field_eventually
    (c : N) (s : geometricSphere) :
    localSphereCoefficients P R ι hι hR c =ᶠ[𝓝 (c,s)]
      fun q => localCoefficientInChart P R ι hι hR c
        (coefficientChart (E := F) c q).1
        (coefficientChart (E := F) c q).2 := by
  have hopen : IsOpen {q : N × geometricSphere |
      q.1 ∈ (chartAt F c).source ∧
        ι q.1 ∈ (chartAt E (ι c)).source} :=
    ((chartAt F c).open_source.inter
      ((chartAt E (ι c)).open_source.preimage hSmooth.continuous)).preimage
      continuous_fst
  filter_upwards [hopen.mem_nhds
      (⟨mem_chart_source F c, mem_chart_source E (ι c)⟩ :
        (c,s) ∈ {q : N × geometricSphere |
          q.1 ∈ (chartAt F c).source ∧
            ι q.1 ∈ (chartAt E (ι c)).source})] with q hq
  have he : (extChartAt 𝓘(ℝ,F) c).symm
      (extChartAt 𝓘(ℝ,F) c q.1) = q.1 :=
    (extChartAt 𝓘(ℝ,F) c).left_inv
      (by simpa only [extChartAt_source] using hq.1)
  change (EuclideanSpace.equiv (Fin 3) ℝ)
      (localSphereAmbient P R ι hι hR c q) = _
  rw [localSphereAmbient, if_pos hq]
  change (EuclideanSpace.equiv (Fin 3) ℝ)
      (toEuclidean (localCoefficientMap P R ι hι hR
        (achart F c) (achart E (ι c)) q.1
        (sphereCoefficients q.2))) =
      localCoefficientInChart P R ι hι hR c
        (extChartAt 𝓘(ℝ,F) c q.1) (sphereCoefficients q.2)
  rw [toEuclidean, (EuclideanSpace.equiv (Fin 3) ℝ).apply_symm_apply]
  simp only [localCoefficientInChart,
    ManifoldQuaternionicInducedLocalCoefficientJointSmooth.localCoefficientCLM,
    he]
  rfl

include hSmooth in
theorem localSphereCoefficients_mfderiv_center
    (c : N) (s : geometricSphere) (u : F)
    (w : TangentSpace (𝓡 2) s) :
    mfderiv (JF (F := F)) 𝓘(ℝ,R3)
      (localSphereCoefficients P R ι hι hR c) (c,s) (u,w) =
      (fderiv ℝ (localCoefficientInChart P R ι hι hR c)
        (extChartAt 𝓘(ℝ,F) c c) u) (sphereCoefficients s) +
      localCoefficientInChart P R ι hι hR c
        (extChartAt 𝓘(ℝ,F) c c)
        (EuclideanSpace.equiv (Fin 3) ℝ (sphereTangentMap s w)) := by
  let C := localCoefficientInChart P R ι hι hR c
  let Pfield : F × R3 → R3 := fun q => C q.1 q.2
  have hC : DifferentiableAt ℝ C (extChartAt 𝓘(ℝ,F) c c) :=
    localCoefficientInChart_differentiableAt_center
      P R ι hSmooth hι hR c
  have hP : DifferentiableAt ℝ Pfield
      (extChartAt 𝓘(ℝ,F) c c, sphereCoefficients s) := by
    dsimp only [Pfield]
    fun_prop
  have hPmd : MDifferentiableAt
      (𝓘(ℝ,F).prod 𝓘(ℝ,R3)) 𝓘(ℝ,R3)
      Pfield (extChartAt 𝓘(ℝ,F) c c, sphereCoefficients s) := by
    simpa only [modelWithCornersSelf_prod, chartedSpaceSelf_prod] using
      hP.mdifferentiableAt
  have hK := coefficientChart_mdifferentiableAt_center (E := F) c s
  have hcomp := mfderiv_comp (c,s) hPmd hK
  have hevent := localSphereCoefficients_eq_field_eventually
    P R ι hSmooth hι hR c s
  rw [hevent.mfderiv_eq (I := JF (F := F))
    (I' := 𝓘(ℝ,R3))]
  change mfderiv (JF (F := F)) 𝓘(ℝ,R3)
    (Pfield ∘ coefficientChart (E := F) c) (c,s) (u,w) = _
  rw [hcomp]
  change (mfderiv (𝓘(ℝ,F).prod 𝓘(ℝ,R3)) 𝓘(ℝ,R3) Pfield
      (extChartAt 𝓘(ℝ,F) c c, sphereCoefficients s))
    ((mfderiv (JF (F := F)) (𝓘(ℝ,F).prod 𝓘(ℝ,R3))
      (coefficientChart (E := F) c) (c,s)) (u,w)) = _
  rw [coefficientChart_mfderiv_center,
    mfderiv_prod_eq_add_apply hPmd]
  simp only [mfderiv_eq_fderiv]
  change fderiv ℝ (fun z : F => C z (sphereCoefficients s))
      (extChartAt 𝓘(ℝ,F) c c) u +
    fderiv ℝ (C (extChartAt 𝓘(ℝ,F) c c)) (sphereCoefficients s)
      (EuclideanSpace.equiv (Fin 3) ℝ (sphereTangentMap s w)) = _
  rw [fderiv_clm_apply hC (differentiableAt_const _),
    ContinuousLinearMap.fderiv]
  simp [C, ContinuousLinearMap.flip_apply]

include hSmooth in
/-- The actual sphere tangent differential, read through its Euclidean
coefficient embedding, has precisely the rectangular base/fiber block. -/
theorem localSphereMap_mfderiv_coefficients_center
    (c : N) (s : geometricSphere) (u : F)
    (w : TangentSpace (𝓡 2) s) :
    EuclideanSpace.equiv (Fin 3) ℝ
      (sphereTangentMap (localSphereMap P R ι hι hR c (c,s))
        (mfderiv (JF (F := F)) (𝓡 2)
          (localSphereMap P R ι hι hR c) (c,s) (u,w))) =
      (fderiv ℝ (localCoefficientInChart P R ι hι hR c)
        (extChartAt 𝓘(ℝ,F) c c) u) (sphereCoefficients s) +
      localCoefficientInChart P R ι hι hR c
        (extChartAt 𝓘(ℝ,F) c c)
        (EuclideanSpace.equiv (Fin 3) ℝ (sphereTangentMap s w)) := by
  have hS : MDifferentiableAt (JF (F := F)) (𝓡 2)
      (localSphereMap P R ι hι hR c) (c,s) :=
    (localSphereMap_smoothAt_center P R ι hSmooth hι hR c s)
      |>.mdifferentiableAt (by simp)
  have hC : MDifferentiableAt (𝓡 2) 𝓘(ℝ,R3)
      sphereCoefficients (localSphereMap P R ι hι hR c (c,s)) := by
    change MDifferentiableAt (𝓡 2) 𝓘(ℝ,R3)
      ManifoldTwistorGlobalAlmostComplex.coefficientEmbedding
        (localSphereMap P R ι hι hR c (c,s))
    exact ManifoldTwistorGlobalAlmostComplex.coefficientEmbedding_smooth.mdifferentiableAt
      (by simp)
  have hcomp := mfderiv_comp (c,s) hC hS
  have hvalue := congrArg (fun L : (F × TangentSpace (𝓡 2) s) →L[ℝ]
      R3 => L (u,w)) hcomp
  change mfderiv (JF (F := F)) 𝓘(ℝ,R3)
      (localSphereCoefficients P R ι hι hR c) (c,s) (u,w) = _ at hvalue
  change mfderiv (JF (F := F)) 𝓘(ℝ,R3)
      (localSphereCoefficients P R ι hι hR c) (c,s) (u,w) =
    (mfderiv (𝓡 2) 𝓘(ℝ,R3)
      sphereCoefficients (localSphereMap P R ι hι hR c (c,s)))
        ((mfderiv (JF (F := F)) (𝓡 2)
          (localSphereMap P R ι hι hR c) (c,s)) (u,w)) at hvalue
  rw [sphereCoefficients_mfderiv] at hvalue
  exact hvalue.symm.trans
    (localSphereCoefficients_mfderiv_center P R ι hSmooth hι hR c s u w)

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedSphereDerivative
