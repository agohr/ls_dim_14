import QuaternionicSymmetry.QuaternionicWeylCertificateSigns
import QuaternionicSymmetry.QuaternionicNormalizedDensityBounds

/-! Normalized density lower bounds for the actual finite Weyl coefficients.
The functional is pointwise; manifold integration and index identification
are separate steps. -/
namespace QuaternionicSymmetry.QuaternionicWeylNormalizedDensity
open Module QuaternionicCurvatureFiniteExpansion QuaternionicCurvatureOrbitalSign
open QuaternionicWeylMatrixCoefficients ManifoldQuaternionicKSWEq38Input
open QuaternionicFundamental QuaternionicTracePositivity
open QuaternionicNormalizedDensityBounds QuaternionicNormalizedDensityValues
open DimensionElevenTwelveDensity
noncomputable section
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] (S : QuaternionicStructure E)
  (W : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E))
  (hW : HyperWeylFiber S W) (b : Basis ι ℝ E)

theorem density11_weyl_lower_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hn : S.quaternionicDimension = 11) (s : ℝ) (hs : 0 < s)
    (L : CE E →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := E) (topForm S b))) :
    288 * L ((s ^ 2 • embed (V := E) (form S b)) ^ 11) ≤
      L (MvPolynomial.aeval (normalizedValues S b s
        (fun a : Index S => (tangentSourceMatrixMap S (operatorBasis S a)).val)
        (coefficientExterior S W (HyperWeylFiber.mem_skewCentralizer S hW) b)) density11) := by
  have h := density11_lower_bound_normalized (β := Index S) hsource S b hn s hs
  rw [← hn] at h
  simpa only [hn] using h _ (fun a => (tangentSourceMatrixMap S (operatorBasis S a)).property) _
    (coefficientExterior_mem S W (HyperWeylFiber.mem_skewCentralizer S hW) b hW.1 hW.2.2.2.2.1) L hL

theorem density12_weyl_lower_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hn : S.quaternionicDimension = 12) (s : ℝ) (hs : 0 < s)
    (L : CE E →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := E) (topForm S b))) :
    336 * L ((s ^ 2 • embed (V := E) (form S b)) ^ 12) ≤
      L (MvPolynomial.aeval (normalizedValues S b s
        (fun a : Index S => (tangentSourceMatrixMap S (operatorBasis S a)).val)
        (coefficientExterior S W (HyperWeylFiber.mem_skewCentralizer S hW) b)) density12) := by
  have h := density12_lower_bound_normalized (β := Index S) hsource S b hn s hs
  rw [← hn] at h
  simpa only [hn] using h _
    (fun a => (tangentSourceMatrixMap S (operatorBasis S a)).property) _
    (coefficientExterior_mem S W (HyperWeylFiber.mem_skewCentralizer S hW) b hW.1 hW.2.2.2.2.1) L hL

end
end QuaternionicSymmetry.QuaternionicWeylNormalizedDensity
