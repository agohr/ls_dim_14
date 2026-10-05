import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondTensorSmooth
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveScalarFiber

/-! The two local projective tensors are jointly C∞ in the genuine
`ℍ × (Fin 1 → ℂ)` model of the independently constructed bundle atlas,
not merely after forgetting the actual projective tangent model. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualModelTensorSmooth

open scoped ContDiff Manifold Quaternion
open FourDimensionalHalfSpinProjectiveFirstTensorSmooth
  FourDimensionalHalfSpinProjectiveSecondTensorSmooth
  FourDimensionalHalfSpinProjectiveScalarFiber
  FourDimensionalHalfSpinProjectiveLocalAHS
  FourDimensionalHalfSpinProjectiveSecondTensor
  ManifoldQuaternionicConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

private abbrev Model := ℍ × (Fin 1 → ℂ)
private def chartTangentSet (p : M) : Set (Model × Model) :=
  ((extChartAt 𝓘(ℝ, ℍ) p).target ×ˢ Set.univ) ×ˢ Set.univ

def firstModelTensor (p : M) (y : Model) (v : Model) : Model :=
  projectiveTangentModelEquiv.symm
    (localActualProjectiveAHS Q D p y.1 (y.2 0)
      (projectiveTangentModelEquiv v))

def secondModelTensor (p : M) (y : Model) (v : Model) : Model :=
  projectiveTangentModelEquiv.symm
    (secondLocalActualProjectiveAHS Q D p y.1 (y.2 0)
      (projectiveTangentModelEquiv v))

private theorem scalarChartProduct_smooth (p : M) :
    ContDiffOn ℝ ∞
      (fun z : Model × Model =>
        ((z.1.1, scalarFiberEquiv z.1.2),
          projectiveTangentModelEquiv z.2))
      (chartTangentSet p) := by
  have hbase : ContDiff ℝ ∞
      (fun z : Model × Model => z.1.1) := by fun_prop
  have hfiber : ContDiff ℝ ∞
      (fun z : Model × Model => scalarFiberEquiv z.1.2) :=
    scalarFiberEquiv.contDiff.comp (by fun_prop)
  have hdir : ContDiff ℝ ∞
      (fun z : Model × Model => projectiveTangentModelEquiv z.2) :=
    projectiveTangentModelEquiv.contDiff.comp contDiff_snd
  exact ((hbase.prodMk hfiber).prodMk hdir).contDiffOn

private theorem scalarChartProduct_mapsTo (p : M) :
    Set.MapsTo
      (fun z : Model × Model =>
        ((z.1.1, scalarFiberEquiv z.1.2),
          projectiveTangentModelEquiv z.2))
      (chartTangentSet p)
      (((extChartAt 𝓘(ℝ, ℍ) p).target ×ˢ Set.univ) ×ˢ Set.univ) := by
  intro z hz
  exact ⟨⟨hz.1.1, Set.mem_univ _⟩, Set.mem_univ _⟩

theorem first_model_tensor_smooth (p : M) :
    ContDiffOn ℝ ∞
      (fun z : Model × Model => firstModelTensor Q D p z.1 z.2)
      (chartTangentSet p) := by
  have h := (first_local_tensor_apply_smooth Q D p).comp
    (scalarChartProduct_smooth p) (scalarChartProduct_mapsTo p)
  exact projectiveTangentModelEquiv.symm.contDiff.contDiffOn.comp h (by
    intro z hz
    exact Set.mem_univ _)

theorem second_model_tensor_smooth (p : M) :
    ContDiffOn ℝ ∞
      (fun z : Model × Model => secondModelTensor Q D p z.1 z.2)
      (chartTangentSet p) := by
  have h := (second_local_tensor_apply_smooth Q D p).comp
    (scalarChartProduct_smooth p) (scalarChartProduct_mapsTo p)
  exact projectiveTangentModelEquiv.symm.contDiff.contDiffOn.comp h (by
    intro z hz
    exact Set.mem_univ _)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualModelTensorSmooth
