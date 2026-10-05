import QuaternionicSymmetry.ManifoldFormPowerScaling
import QuaternionicSymmetry.ManifoldQuaternionicKSWFundamentalClass
import QuaternionicSymmetry.ManifoldQuaternionicIntegralLowerBound

/-! Exact canonical volume normalization of the analytic quarter-class's
actual top wedge power. Topological identification is not assumed here. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicQuarterVolume
open ManifoldDifferentialForms ManifoldDeRhamWedge ManifoldFormPowers
open ManifoldQuaternionicAdjointChernWeil ManifoldQuaternionicKSWFundamentalClass
open ManifoldQuaternionicKSWScalarInput ManifoldQuaternionicFourFormGluing
open ManifoldQuaternionicFundamentalClass ManifoldQuaternionicVolume
open ManifoldQuaternionicDensityIntegration ManifoldQuaternionicCanonicalIntegration
open ManifoldQuaternionicIntegralLowerBound
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

def quarterTop (n : ℕ) (hdim : 4*n = Module.finrank ℝ E) :
    SmoothTopForms (E := E) (M := M) :=
  ⟨castForm hdim (formPower (quarterPontryaginCandidateForm Q D).val.val n),
    chartSmooth_castForm _ _ (formPower_smooth _
      (quarterPontryaginCandidateForm Q D).val.property n)⟩

theorem quarterTop_eq_volume (n : ℕ) (hdim : 4*n = Module.finrank ℝ E)
    (c : ℝ) (hc : quarterPontryaginCandidateForm Q D = c • closedFundamental Q D) :
    quarterTop Q D n hdim = c^n • volumeForm Q := by
  have hraw := congrArg (fun α => α.val.val) hc
  change (quarterPontryaginCandidateForm Q D).val.val = c • fundamentalFourForm Q at hraw
  apply Subtype.ext
  change castForm hdim (formPower _ n) = c^n • fundamentalTopForm Q
  rw [hraw, formPower_smul, castForm_smul]
  have hn : n = Module.finrank ℝ E / 4 := by omega
  subst n
  rfl

variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]

theorem quarterTop_integral (n : ℕ) (hdim : 4*n = Module.finrank ℝ E)
    (c : ℝ) (hc : quarterPontryaginCandidateForm Q D = c • closedFundamental Q D) :
    integral Q (quarterTop Q D n hdim) = c^n * integral Q (volumeForm Q) := by
  rw [quarterTop_eq_volume Q D n hdim c hc, map_smul, smul_eq_mul]

theorem quarterTop_integral_normalized (S : QuaternionicStructure E)
    (hsp : KSWSp1CurvatureFormula S Q D) (t : ℝ)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t^2)
    (n : ℕ) (hdim : 4*n = Module.finrank ℝ E) :
    integral Q (quarterTop Q D n hdim) =
      (t^2 / Real.pi)^(2*n) * integral Q (volumeForm Q) := by
  have hc := quarterForm_eq_fundamental S Q D hsp (t^2) ht
  rw [quarterTop_integral Q D n hdim _ hc]
  rw [← div_pow, ← pow_mul]

end
end QuaternionicSymmetry.ManifoldQuaternionicQuarterVolume
