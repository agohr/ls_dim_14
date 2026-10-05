import QuaternionicSymmetry.ManifoldQuaternionicFundamentalClass
import QuaternionicSymmetry.ManifoldQuaternionicCanonicalIntegration

/-! Nonvanishing of the genuine quaternionic fundamental de Rham classes. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFundamentalNonvanishing

open MeasureTheory ManifoldDifferentialForms ManifoldDeRhamWedge
  ManifoldDeRhamRing ManifoldDeRhamAllDegrees ManifoldDeRhamAllDegreeClasses
  ManifoldQuaternionicMetric ManifoldQuaternionicConnection
  ManifoldQuaternionicFourFormGluing ManifoldQuaternionicVolume
  ManifoldFormPowers
  ManifoldQuaternionicFundamentalClass ManifoldQuaternionicCanonicalIntegration
open scoped Manifold ContDiff Topology
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 2000000

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] [CompactSpace M] [T2Space M] in
theorem quaternionicRank_pos (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞)) :
    0 < Module.finrank ℝ E / 4 := by
  have hf : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hm := model_dimension Q
  omega

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] [CompactSpace M] [T2Space M] in
/-- The highest fundamental power represents the genuine top form. -/
theorem topPower_eq_topForm :
    castForm (model_dimension Q)
      (closedFundamentalPower Q D (Module.finrank ℝ E / 4)).val.val =
      fundamentalTopForm Q := rfl

/-- The top repeated wedge is a nonzero class in actual positive-degree
smooth de Rham cohomology. -/
theorem topPowerClosedClass_ne_zero :
    closedFormClass (4 * (Module.finrank ℝ E / 4) - 1)
      (castClosedDegree
        (by have hp := quaternionicRank_pos Q
            omega : 4 * (Module.finrank ℝ E / 4) =
              (4 * (Module.finrank ℝ E / 4) - 1) + 1)
        (closedFundamentalPower Q D (Module.finrank ℝ E / 4))) ≠ 0 := by
  let N := Module.finrank ℝ E / 4
  let m := 4 * N - 1
  have hN : 0 < N := quaternionicRank_pos Q
  have hpow : 4 * N = m + 1 := by omega
  have hdim : m + 1 = Module.finrank ℝ E := by
    have hm := model_dimension Q
    omega
  have he : castForm hdim
      (castClosedDegree hpow (closedFundamentalPower Q D N)).val.val =
        fundamentalTopForm Q := by
    rw [castClosedDegree_form]
    change castForm hdim (castForm hpow
      (closedFundamentalPower Q D N).val.val) =
        castForm (model_dimension Q)
          (closedFundamentalPower Q D N).val.val
    rw [castForm_comp]
  apply positive_class_ne_zero Q hdim
  · intro x
    rw [he]
    exact ⟨1, zero_le_one, (one_smul ℝ _).symm⟩
  · rw [he]
    exact fundamentalTopForm_ne_zero Q (Classical.arbitrary M)


end
end QuaternionicSymmetry.ManifoldQuaternionicFundamentalNonvanishing
