import QuaternionicSymmetry.QuaternionicTwoSixNormalizedBounds
import QuaternionicSymmetry.QuaternionicWeylNormalizedDensity
import QuaternionicSymmetry.QuaternionicSixModelRankBound

/-! Apply the n=2–6 normalized finite polynomial bounds to the actual
algebraic quaternionic Weyl coefficient forms. -/
namespace QuaternionicSymmetry.QuaternionicTwoSixWeylBounds
open Module QuaternionicCurvatureFiniteExpansion QuaternionicCurvatureOrbitalSign
open QuaternionicWeylMatrixCoefficients ManifoldQuaternionicKSWEq38Input
open QuaternionicFundamental QuaternionicTracePositivity
open QuaternionicNormalizedDensityValues QuaternionicTwoSixNormalizedBounds
open DimensionElevenTwelveDensity PrintedTwoSixLinearAssembly ReconstructionExamples
open QuaternionicSixModelRankBound
noncomputable section
set_option maxHeartbeats 800000

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] (S : QuaternionicStructure E)
  (W : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E))
  (hW : HyperWeylFiber S W) (b : Basis ι ℝ E)

theorem density2_weyl_lower_bound
    (hn : S.quaternionicDimension = 2) (s : ℝ) (hs : 0 < s)
    (L : CE E →ₗ[ℝ] ℝ) (_hL : 0 ≤ L (embed (V := E) (topForm S b))) :
    16 * L ((s ^ 2 • embed (V := E) (form S b)) ^ 2) ≤
      L (MvPolynomial.aeval (normalizedValues S b s
        (fun a : Index S => (tangentSourceMatrixMap S (operatorBasis S a)).val)
        (coefficientExterior S W (HyperWeylFiber.mem_skewCentralizer S hW) b)) density2) := by
  have h := density2_lower_bound_normalized (β := Index S) S b s hs
  rw [← hn] at h
  simpa only [hn] using h _ _ L


theorem density3_weyl_lower_bound
    (hn : S.quaternionicDimension = 3) (s : ℝ) (hs : 0 < s)
    (L : CE E →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := E) (topForm S b))) :
    32 * L ((s ^ 2 • embed (V := E) (form S b)) ^ 3) ≤
      L (MvPolynomial.aeval (normalizedValues S b s
        (fun a : Index S => (tangentSourceMatrixMap S (operatorBasis S a)).val)
        (coefficientExterior S W (HyperWeylFiber.mem_skewCentralizer S hW) b)) density3) := by
  have h := density3_lower_bound_normalized (β := Index S) S b hn s hs
  rw [← hn] at h
  simpa only [hn] using h _
    (fun a => (tangentSourceMatrixMap S (operatorBasis S a)).property.1) _
    (coefficientExterior_mem S W (HyperWeylFiber.mem_skewCentralizer S hW)
      b hW.1 hW.2.2.2.2.1) L hL

theorem density4_weyl_lower_bound
    (hn : S.quaternionicDimension = 4) (s : ℝ) (hs : 0 < s)
    (L : CE E →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := E) (topForm S b))) :
    48 * L ((s ^ 2 • embed (V := E) (form S b)) ^ 4) ≤
      L (MvPolynomial.aeval (normalizedValues S b s
        (fun a : Index S => (tangentSourceMatrixMap S (operatorBasis S a)).val)
        (coefficientExterior S W (HyperWeylFiber.mem_skewCentralizer S hW) b)) density4) := by
  have h := density4_lower_bound_normalized (β := Index S) S b hn s hs
  rw [← hn] at h
  simpa only [hn] using h _
    (fun a => (tangentSourceMatrixMap S (operatorBasis S a)).property.1) _
    (coefficientExterior_mem S W (HyperWeylFiber.mem_skewCentralizer S hW)
      b hW.1 hW.2.2.2.2.1) L hL

theorem density5_weyl_lower_bound
    (hn : S.quaternionicDimension = 5) (s : ℝ) (hs : 0 < s)
    (L : CE E →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := E) (topForm S b))) :
    72 * L ((s ^ 2 • embed (V := E) (form S b)) ^ 5) ≤
      L (MvPolynomial.aeval (normalizedValues S b s
        (fun a : Index S => (tangentSourceMatrixMap S (operatorBasis S a)).val)
        (coefficientExterior S W (HyperWeylFiber.mem_skewCentralizer S hW) b)) k5) := by
  have h := density5_lower_bound_normalized (β := Index S) S b hn s hs
  rw [← hn] at h
  simpa only [hn] using h _
    (fun a => (tangentSourceMatrixMap S (operatorBasis S a)).property.1) _
    (coefficientExterior_mem S W (HyperWeylFiber.mem_skewCentralizer S hW)
      b hW.1 hW.2.2.2.2.1) L hL

theorem density6_weyl_lower_bound
    (hn : S.quaternionicDimension = 6) (s : ℝ) (hs : 0 < s)
    (L : CE E →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := E) (topForm S b))) :
    96 * L ((s ^ 2 • embed (V := E) (form S b)) ^ 6) ≤
      L (MvPolynomial.aeval (normalizedValues S b s
        (fun a : Index S => (tangentSourceMatrixMap S (operatorBasis S a)).val)
        (coefficientExterior S W (HyperWeylFiber.mem_skewCentralizer S hW) b)) k6) := by
  exact density6_lower_bound_normalized_model S.quaternionicDimension hn
    S b rfl s hs _
    (fun a => (tangentSourceMatrixMap S (operatorBasis S a)).property.1) _
    (coefficientExterior_mem S W (HyperWeylFiber.mem_skewCentralizer S hW)
      b hW.1 hW.2.2.2.2.1) L hL

end
end QuaternionicSymmetry.QuaternionicTwoSixWeylBounds
