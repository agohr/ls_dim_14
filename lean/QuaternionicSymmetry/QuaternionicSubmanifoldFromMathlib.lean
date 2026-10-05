import QuaternionicSymmetry.ManifoldQuaternionicImmersionConnectionFrames
import QuaternionicSymmetry.ManifoldQuaternionicConstructedIdentification

/-! The original positive quaternionic-submanifold literature contract is
proved internally. Local quaternionic Gram-Schmidt supplies a compatible
atlas and induced metric. Orthogonal projection constructs its compatible
connection; quaternionic total geodesy and curvature comparison prove
positivity of its genuine scalar curvature. -/
namespace QuaternionicSymmetry.QuaternionicSubmanifoldFromMathlib
open ManifoldQuaternionicSubmanifoldInput ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicImmersionLocalGauge ManifoldQuaternionicImmersionGaugeAtlas
open ManifoldQuaternionicImmersionHermitianTangent ManifoldQuaternionicImmersionConnectionFrames
open ManifoldQuaternionicInducedConnectionConstruction
open ManifoldQuaternionicConstructedIdentification ManifoldQuaternionicConstructedScalarPositive
open scoped Manifold ContDiff
noncomputable section

theorem positiveQuaternionicSubmanifold : PositiveQuaternionicSubmanifoldSource := by
  intro E F M N hE hEi hF hFi hEf hEn hFf hFn hM hMc hMm hN hNc hNm hM3 hMs hN3 hNs
    P n m hn hm hdimE hdimF ι hι _hemb hinj hQ
  let G : ∀ c, LocalGauge (F := F) P ι c := fun c =>
    Classical.choice (exists_localGauge P ι hι hinj hQ c)
  let A := compatibleAtlas G hι hinj
  let Q : letI := charts G; letI := charts_manifold (old := hNc) G
      ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
        (I := 𝓘(ℝ,F)) (M := N) (n := ∞) := tangent (old := hNc) G
  let L : letI := charts G; letI := charts_manifold (old := hNc) G
      LocalFrames P Q ι := localFrames G hι hinj
  have hSmooth := A.inclusion_smooth
  refine ⟨A,?_⟩
  letI := A.charts
  letI := A.manifold
  let R : PositiveQuaternionicKahlerGeometry (E := F) (M := N) := {
    tangent := Q
    connection := connection L hSmooth
    scalar_pos := scalar_pos L hSmooth (by omega) (by omega) }
  refine ⟨R,?_,?_⟩
  · exact metric_induced L hSmooth
  · exact span_induced L hSmooth

end
end QuaternionicSymmetry.QuaternionicSubmanifoldFromMathlib
