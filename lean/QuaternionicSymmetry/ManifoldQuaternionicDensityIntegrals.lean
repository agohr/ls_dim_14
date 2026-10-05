import QuaternionicSymmetry.ManifoldQuaternionicActualDensityBounds
import QuaternionicSymmetry.ManifoldQuaternionicIntegralLowerBound

/-! Canonical integral bounds for the actual closed C12 density representatives. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicDensityIntegrals
open Module ManifoldDeRhamWedge ManifoldQuaternionicActualDensityBounds
open ManifoldQuaternionicIntegralLowerBound ManifoldQuaternionicCanonicalIntegration
open ManifoldQuaternionicVolumeCoefficient ManifoldQuaternionicVolume
open ManifoldQuaternionicDensityIntegration
open ManifoldEvenClosedAlgebra QuaternionicClosedDensityForms
open ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicKSWScalarInput
open scoped Manifold ContDiff
noncomputable section
variable {E M ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

def density11Top (hn : S.quaternionicDimension = 11) (t : ℝ) :
    SmoothTopForms (E := E) (M := M) :=
  ⟨castForm (show 4 * 10 + 3 + 1 = Module.finrank ℝ E by
      have h := S.real_finrank; omega) (density11Form S Q D t).val.val,
    chartSmooth_castForm _ _ (density11Form S Q D t).val.property⟩

def density12Top (hn : S.quaternionicDimension = 12) (t : ℝ) :
    SmoothTopForms (E := E) (M := M) :=
  ⟨castForm (show 4 * 11 + 3 + 1 = Module.finrank ℝ E by
      have h := S.real_finrank; omega) (density12Form S Q D t).val.val,
    chartSmooth_castForm _ _ (density12Form S Q D t).val.property⟩

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [T2Space M] in
theorem density11_scalarDensity_bound_global
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 11) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2) (x : M) :
    288 * (t ^ 2 / Real.pi) ^ 22 ≤
      scalarDensity Q (density11Top (Q := Q) (D := D) S hn t).val x := by
  let y := extChartAt 𝓘(ℝ,E) x x
  have hy : y ∈ (extChartAt 𝓘(ℝ,E) x).target :=
    (extChartAt 𝓘(ℝ,E) x).map_source (by simp)
  have h := density11_scalarDensity_bound S Q D hsource hsp hdecomp hn b t htpos ht x y hy
  simpa only [density11Top, y, (extChartAt 𝓘(ℝ,E) x).left_inv (mem_extChartAt_source x)] using h

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [T2Space M] in
theorem density12_scalarDensity_bound_global
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 12) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2) (x : M) :
    336 * (t ^ 2 / Real.pi) ^ 24 ≤
      scalarDensity Q (density12Top (Q := Q) (D := D) S hn t).val x := by
  let y := extChartAt 𝓘(ℝ,E) x x
  have hy : y ∈ (extChartAt 𝓘(ℝ,E) x).target :=
    (extChartAt 𝓘(ℝ,E) x).map_source (by simp)
  have h := density12_scalarDensity_bound S Q D hsource hsp hdecomp hn b t htpos ht x y hy
  simpa only [density12Top, y, (extChartAt 𝓘(ℝ,E) x).left_inv (mem_extChartAt_source x)] using h

theorem density11_integral_lower_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 11) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2) :
    (288 * (t ^ 2 / Real.pi) ^ 22) * integral Q (volumeForm Q) ≤
      integral Q (density11Top (Q := Q) (D := D) S hn t) := by
  apply integral_lower_bound Q _ _
  intro x
  exact ⟨scalarDensity Q (density11Top (Q := Q) (D := D) S hn t).val x,
    density11_scalarDensity_bound_global S Q D hsource hsp hdecomp hn b t htpos ht x,
    eq_scalarDensity_smul Q _ x⟩

theorem density12_integral_lower_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 12) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2) :
    (336 * (t ^ 2 / Real.pi) ^ 24) * integral Q (volumeForm Q) ≤
      integral Q (density12Top (Q := Q) (D := D) S hn t) := by
  apply integral_lower_bound Q _ _
  intro x
  exact ⟨scalarDensity Q (density12Top (Q := Q) (D := D) S hn t).val x,
    density12_scalarDensity_bound_global S Q D hsource hsp hdecomp hn b t htpos ht x,
    eq_scalarDensity_smul Q _ x⟩

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [T2Space M] in
theorem density11_positive_ray
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 11) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2) (x : M) :
    PositiveRay.Contains (fundamentalTopForm Q x)
      ((density11Top (Q := Q) (D := D) S hn t).val x) := by
  rw [positive_ray_iff]
  have hc : 0 < 288 * (t ^ 2 / Real.pi) ^ 22 := by positivity
  exact le_trans (le_of_lt hc)
    (density11_scalarDensity_bound_global S Q D hsource hsp hdecomp hn b t htpos ht x)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [T2Space M] in
theorem density12_positive_ray
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 12) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2) (x : M) :
    PositiveRay.Contains (fundamentalTopForm Q x)
      ((density12Top (Q := Q) (D := D) S hn t).val x) := by
  rw [positive_ray_iff]
  have hc : 0 < 336 * (t ^ 2 / Real.pi) ^ 24 := by positivity
  exact le_trans (le_of_lt hc)
    (density12_scalarDensity_bound_global S Q D hsource hsp hdecomp hn b t htpos ht x)

theorem density11_integral_positive
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 11) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2) :
    0 < integral Q (density11Top (Q := Q) (D := D) S hn t) := by
  have hc : 0 < 288 * (t ^ 2 / Real.pi) ^ 22 := by positivity
  exact lt_of_lt_of_le (mul_pos hc (integral_topForm_pos Q))
    (density11_integral_lower_bound S Q D hsource hsp hdecomp hn b t htpos ht)

theorem density12_integral_positive
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 12) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2) :
    0 < integral Q (density12Top (Q := Q) (D := D) S hn t) := by
  have hc : 0 < 336 * (t ^ 2 / Real.pi) ^ 24 := by positivity
  exact lt_of_lt_of_le (mul_pos hc (integral_topForm_pos Q))
    (density12_integral_lower_bound S Q D hsource hsp hdecomp hn b t htpos ht)

end
end QuaternionicSymmetry.ManifoldQuaternionicDensityIntegrals
