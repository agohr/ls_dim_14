import QuaternionicSymmetry.ManifoldTwistorSWCohomology
import QuaternionicSymmetry.ManifoldQuaternionicKillingFields
import Mathlib.RingTheory.Finiteness.Descent

/-! The source-relative Salamon correspondence specialized to the actual
holomorphic contact line and actual complexified Killing fields. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

open QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open CategoryTheory TopologicalSpace
open scoped Manifold ContDiff
noncomputable section

universe u v w

variable {E : Type u} {M : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
  {n : ℕ} {A : CompatibleComplexAtlas P.tangent P.connection n}
  (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)

variable [HasSheafify (Opens.grothendieckTopology
    (TopCat.of (SphereBundleTotal P.tangent))) (ModuleCat.{v} ℂ)]
  [HasExt.{w} (TopCat.Sheaf (ModuleCat.{v} ℂ)
    (TopCat.of (SphereBundleTotal P.tangent)))]

/-- An explicit Salamon source isomorphism on genuine holomorphic
sections composes with the internally proved complex-linear `H⁰`
identification. -/
noncomputable def sw_h0_one_killingLinearEquiv
    (hSalamon : HolomorphicTwistSections
        P.tangent P.connection C.contact.line 1 ≃ₗ[ℂ]
          ManifoldQuaternionicKillingFields.ComplexKillingFields P.tangent) :
    sourceH (P := P) (C := C) 1 0 ≃ₗ[ℂ]
      ManifoldQuaternionicKillingFields.ComplexKillingFields P.tangent :=
  (holomorphicTwistComplexCohomologyZeroBundledLinearEquiv
    P.tangent P.connection C.contact.line 1).trans hSalamon

/-- Finiteness of actual `H⁰(L)` plus the source's Salamon isomorphism
implies finite dimensionality of the *real* Killing-field space by
faithfully-flat descent from ℝ to ℂ. -/
theorem sw_killingFields_finiteDimensional
    (hfinite : FiniteDimensional ℂ (sourceH (P := P) (C := C) 1 0))
    (hSalamon : HolomorphicTwistSections
        P.tangent P.connection C.contact.line 1 ≃ₗ[ℂ]
          ManifoldQuaternionicKillingFields.ComplexKillingFields P.tangent) :
    FiniteDimensional ℝ
      (ManifoldQuaternionicKillingFields.KillingFields P.tangent) := by
  letI := hfinite
  letI : FiniteDimensional ℂ
      (ManifoldQuaternionicKillingFields.ComplexKillingFields P.tangent) :=
    (sw_h0_one_killingLinearEquiv P C hSalamon).finiteDimensional
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat ℂ

/-- The first Hilbert value is the dimension of genuine Killing fields,
provided the exact Salamon correspondence and positive-twist Kodaira
vanishing from the source. It is not an input value. -/
theorem sw_hilbert_one_eq_killingDimension
    (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4 * n)
    (hCanonical : Nonempty (HolomorphicContactCanonicalIso
      P.tangent P.connection n A C.contact.line))
    (hfinite : ∀ s, FiniteDimensional ℂ (sourceH (P := P) (C := C) 1 s))
    (hKodaira : ∀ s, 0 < s → s ≤ 2 * n + 1 →
      Subsingleton (sourceH (P := P) (C := C) 1 s))
    (hSalamon : HolomorphicTwistSections
        P.tangent P.connection C.contact.line 1 ≃ₗ[ℂ]
          ManifoldQuaternionicKillingFields.ComplexKillingFields P.tangent) :
    sourceP (P := P) (C := C) 1 hfinite =
      (ManifoldQuaternionicKillingFields.killingDimension P.tangent : ℤ) := by
  rw [sw_hilbert_nonnegative_eq_sections P C hn hDim hCanonical 1 (by omega)
    hfinite hKodaira,
    hSalamon.finrank_eq,
    ManifoldQuaternionicKillingFields.complexKillingFields_finrank]

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
