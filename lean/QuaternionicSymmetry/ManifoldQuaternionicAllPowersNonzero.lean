import QuaternionicSymmetry.ManifoldQuaternionicFundamentalPowerMul

/-! Every positive fundamental power survives in smooth de Rham cohomology. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFundamentalNonvanishing

open ManifoldDifferentialForms ManifoldDeRhamWedge ManifoldDeRhamAllDegrees
  ManifoldQuaternionicMetric ManifoldQuaternionicConnection
  ManifoldQuaternionicFundamentalClass ManifoldDeRhamDegreeZero
  ContinuousWedgeUnit
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

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
  [BorelSpace E] [Nonempty M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [T2Space M] in
private theorem positiveWedge_zero_left (k l : ℕ)
    (b : positiveDegreeCohomology (E := E) (M₀ := M) l) :
    cohomologyWedge k l 0 b = 0 := by
  have h := cohomologyWedge_add_left k l (0 :
    positiveDegreeCohomology (E := E) (M₀ := M) k) 0 b
  simp only [zero_add] at h
  have h' : cohomologyWedge k l 0 b + cohomologyWedge k l 0 b =
      cohomologyWedge k l 0 b := h.symm
  exact add_eq_left.mp h'

/-- The actual positive-degree de Rham class of every power below the
quaternionic dimension is nonzero. -/
theorem positivePowerClass_ne_zero (k : ℕ) (hk : 0 < k)
    (hle : k ≤ Module.finrank ℝ E / 4) :
    positivePowerClass Q D k hk ≠ 0 := by
  let N := Module.finrank ℝ E / 4
  have hN : 0 < N := quaternionicRank_pos Q
  intro hzero
  have hprop : ∀ j : ℕ, k ≤ j → ∀ hj : 0 < j,
      positivePowerClass Q D j hj = 0 := by
    intro j hkj
    induction j, hkj using Nat.le_induction with
    | base =>
        intro hj
        simpa using hzero
    | succ j hkj ih =>
        intro hj1
        have hj : 0 < j := lt_of_lt_of_le hk hkj
        rw [positivePowerClass_succ Q D j hj]
        rw [ih hj, positiveWedge_zero_left, castClass_zero]
  have htop : positivePowerClass Q D N hN = 0 := hprop N hle hN
  exact (topPowerClosedClass_ne_zero Q D) (by
    simpa only [positivePowerClass, positivePower] using htop)

theorem fundamentalPowerClass_positive_ne_zero (k : ℕ) (hk : 0 < k)
    (hle : k ≤ Module.finrank ℝ E / 4) :
    castDegree (by omega : 4 * k = (4 * k - 1) + 1)
      (fundamentalPowerClass Q D k) ≠
        (0 : positiveDegreeCohomology (E := E) (M₀ := M) (4 * k - 1)) := by
  rw [fundamentalPowerClass_eq_positivePowerClass Q D k hk]
  exact positivePowerClass_ne_zero Q D k hk hle

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] [CompactSpace M] [T2Space M] in
theorem fundamentalPowerClass_zero_ne_zero :
    fundamentalPowerClass Q D 0 ≠
      (0 : zeroDegreeCohomology (E := E) (M := M)) := by
  change oneClass (E := E) (M := M) ≠ 0
  intro hz
  have he := congrArg
    (fun α : closedForms (E := E) (M₀ := M) 0 =>
      α.val.val (Classical.arbitrary M)
        (Fin.elim0 : Fin 0 → TangentSpace 𝓘(ℝ, E) (Classical.arbitrary M))) hz
  norm_num [oneClass, oneForm, oneZero] at he

end
end QuaternionicSymmetry.ManifoldQuaternionicFundamentalNonvanishing
