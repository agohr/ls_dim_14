import QuaternionicSymmetry.ManifoldQuaternionicInducedBaseComplex
import QuaternionicSymmetry.ManifoldQuaternionicInducedVerticalComplex

/-! Full complex linearity of the actual induced twistor-sphere immersion
under the separately sourced total-geodesy theorem. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedTwistorComplex
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedCoefficientMap
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicInducedTwistorDerivative
open ManifoldQuaternionicInducedSplitDerivative
open ManifoldQuaternionicInducedBaseComplex
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorSphereCore
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorLocalAlmostComplex
open ManifoldTwistorVerticalComplex
open ManifoldQuaternionicConnection
open scoped Manifold ContDiff Matrix
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
  (DP : CompatibleTangentConnection P.tangent)
  (DR : CompatibleTangentConnection R.tangent)
  (hTot : ManifoldQuaternionicInducedTotalGeodesy.IsTotallyGeodesic P R ι DP DR)

private abbrev JF := 𝓘(ℝ,F).prod (𝓡 2)
private abbrev JE := 𝓘(ℝ,E).prod (𝓡 2)
local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩
local instance (x : N) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore R.tangent).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2)) geometricSphere
  infer_instance

include hSmooth hTot in
theorem sphereTotalMap_mfderiv_intertwines_tangentComplex
    (z : SphereBundleTotal R.tangent)
    (t : TangentSpace (JF (F := F)) z) :
    mfderiv (JF (F := F)) (JE (E := E))
      (sphereTotalMap P R ι hι hR) z
      (tangentComplex R.tangent DR z t) =
      tangentComplex P.tangent DP (sphereTotalMap P R ι hι hR z)
        (mfderiv (JF (F := F)) (JE (E := E))
          (sphereTotalMap P R ι hι hR) z t) := by
  let w := sphereTotalMap P R ι hι hR z
  let L := mfderiv (JF (F := F)) (JE (E := E))
    (sphereTotalMap P R ι hι hR) z
  let e := connectionTangentEquiv R.tangent DR z
  let e' := connectionTangentEquiv P.tangent DP w
  apply e'.injective
  rw [tangentComplex_connectionTangentEquiv P.tangent DP w (L t)]
  apply Prod.ext
  · have h₁ := connectionTangentEquiv_mfderiv_fst
      P R ι hSmooth hι hR DP DR z
      (tangentComplex R.tangent DR z t)
    have h₂ := connectionTangentEquiv_mfderiv_fst
      P R ι hSmooth hι hR DP DR z t
    change (e' (L (tangentComplex R.tangent DR z t))).1 = _ at h₁
    change (e' (L t)).1 = _ at h₂
    rw [h₁, tangentComplex_connectionTangentEquiv R.tangent DR z t]
    change mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι z.1
        (chartBaseComplex R.tangent z.1 (extChartAt 𝓘(ℝ,F) z.1 z.1)
          (coefficientSphereHomeomorph.symm z.2) (e t).1) =
      chartBaseComplex P.tangent w.1 (extChartAt 𝓘(ℝ,E) w.1 w.1)
        (coefficientSphereHomeomorph.symm w.2) (e' (L t)).1
    rw [h₂]
    exact induced_mfderiv_intertwines_chartBaseComplex
      P R ι hι hR z (e t).1
  · apply Subtype.ext
    have h₁ := connectionTangentEquiv_mfderiv_snd_coefficients
      P R ι hSmooth hι hR DP DR hTot z
      (tangentComplex R.tangent DR z t)
    have h₂ := connectionTangentEquiv_mfderiv_snd_coefficients
      P R ι hSmooth hι hR DP DR hTot z t
    change ((e' (L (tangentComplex R.tangent DR z t))).2).1 = _ at h₁
    change ((e' (L t)).2).1 = _ at h₂
    rw [h₁, tangentComplex_connectionTangentEquiv R.tangent DR z t]
    change coefficientMap P R ι hι hR z.1
        ((verticalComplex (coefficientSphereHomeomorph.symm z.2)
          (e t).2).1) =
      (verticalComplex (coefficientSphereHomeomorph.symm w.2)
        (e' (L t)).2).1
    change coefficientMap P R ι hι hR z.1
        ((coefficientSphereHomeomorph.symm z.2).1 ⨯₃ (e t).2.1) =
      (coefficientSphereHomeomorph.symm w.2).1 ⨯₃ (e' (L t)).2.1
    have ha : (coefficientSphereHomeomorph.symm w.2).1 =
        coefficientMap P R ι hι hR z.1
          (coefficientSphereHomeomorph.symm z.2).1 := by
      exact sphereTotalMap_center_coefficients P R ι hι hR z
    calc
      _ = coefficientMap P R ι hι hR z.1
            (coefficientSphereHomeomorph.symm z.2).1 ⨯₃
          coefficientMap P R ι hι hR z.1 (e t).2.1 :=
        coefficientMap_cross P R ι hι hR z.1 _ _
      _ = (coefficientSphereHomeomorph.symm w.2).1 ⨯₃
          coefficientMap P R ι hι hR z.1 (e t).2.1 :=
        congrArg (fun a => a ⨯₃ coefficientMap P R ι hι hR z.1 (e t).2.1)
          ha.symm
      _ = _ :=
        congrArg (fun a => (coefficientSphereHomeomorph.symm w.2).1 ⨯₃ a)
          h₂.symm

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedTwistorComplex
