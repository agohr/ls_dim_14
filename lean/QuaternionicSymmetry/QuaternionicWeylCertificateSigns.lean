import QuaternionicSymmetry.QuaternionicWeylRankReduction
import QuaternionicSymmetry.QuaternionicC12Pointwise
import QuaternionicSymmetry.ManifoldQuaternionicKSWEq38Input

/-! The twelve printed certificate generators apply to the finite coefficients
of a Weyl tensor in dimensions eleven and twelve. Here u is the unscaled
fundamental form; the actual scalar-curvature normalization is separate. -/
namespace QuaternionicSymmetry.QuaternionicWeylCertificateSigns
open Module QuaternionicCurvatureFiniteExpansion QuaternionicCurvatureOrbitalSign
open QuaternionicWeylMatrixCoefficients QuaternionicC12Pointwise
open QuaternionicFundamental PrintedQuarticDensityPositivity
open QuaternionicTracePositivity PrintedProjectionCubicPositivity
open ElevenTwelveLinearAssembly ManifoldQuaternionicKSWEq38Input
noncomputable section
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] (S : QuaternionicStructure E)
  (W : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E))
  (hW : HyperWeylFiber S W) (b : Basis ι ℝ E)

theorem generators11_positive
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hn : S.quaternionicDimension = 11) (i : Fin 12) :
    PositiveRay.Contains (embed (V := E) (topForm S b))
      (MvPolynomial.aeval (densityValues S b
        (fun a : Index S => (tangentSourceMatrixMap S (operatorBasis S a)).val)
        (coefficientExterior S W (HyperWeylFiber.mem_skewCentralizer S hW) b))
        (generators11 i)) := by
  have h := generators11_in_positive_ray (β := Index S) hsource S b hn
  rw [← hn] at h
  exact h _ (fun a => (tangentSourceMatrixMap S (operatorBasis S a)).property) _
    (coefficientExterior_mem S W (HyperWeylFiber.mem_skewCentralizer S hW) b hW.1 hW.2.2.2.2.1) i

theorem generators12_positive
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hn : S.quaternionicDimension = 12) (i : Fin 12) :
    PositiveRay.Contains (embed (V := E) (topForm S b))
      (MvPolynomial.aeval (densityValues S b
        (fun a : Index S => (tangentSourceMatrixMap S (operatorBasis S a)).val)
        (coefficientExterior S W (HyperWeylFiber.mem_skewCentralizer S hW) b))
        (generators12 i)) := by
  have h := fun (B : Index S → Matrix (Fin 12 ⊕ Fin 12) (Fin 12 ⊕ Fin 12) ℂ)
    (hB : ∀ a, QuaternionicMatrixModel.HermitianAntiSelfDual (B a))
    (η : Index S → QuaternionicFundamental.E E)
    (hη : ∀ a, η a ∈ HyperholomorphicExterior.formSpace S b) =>
      generators12_in_positive_ray hsource S b hn B hB η hη i
  rw [← hn] at h
  exact h _ (fun a => (tangentSourceMatrixMap S (operatorBasis S a)).property) _
    (coefficientExterior_mem S W (HyperWeylFiber.mem_skewCentralizer S hW) b hW.1 hW.2.2.2.2.1)

end
end QuaternionicSymmetry.QuaternionicWeylCertificateSigns
