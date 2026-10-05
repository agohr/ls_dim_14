import QuaternionicSymmetry.ManifoldTwistorSWKillingComparison
import QuaternionicSymmetry.ManifoldTwistorContactCanonicalApply

/-! A single exact source interface for Semmelmann--Weingart, §2,
arXiv:math/0208079v1. Only cohomological finiteness, Kodaira and Serre
statements, and Salamon's contact-section/Killing-field comparison occur
here. Hilbert values, negative roots, Euler/index equality, and
classification are consequences elsewhere, not source fields. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

open QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.GeneralComplexContactData
open CategoryTheory TopologicalSpace
open scoped Manifold ContDiff
noncomputable section

universe u v w

variable {E : Type u} {M : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
  {n : ℕ} {A : CompatibleComplexAtlas P.tangent P.connection n}
  (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)

variable [HasSheafify (Opens.grothendieckTopology
    (TopCat.of (SphereBundleTotal P.tangent))) (ModuleCat.{v} ℂ)]
  [HasExt.{w} (TopCat.Sheaf (ModuleCat.{v} ℂ)
    (TopCat.of (SphereBundleTotal P.tangent)))]

/-- The exact cohomological assertions applied to one genuine twistor
contact line. This proposition contains no prescribed Hilbert value or
symmetry dimension. -/
def SWCohomologyConclusions : Prop :=
  (∀ (r : ℤ) (s : ℕ),
    FiniteDimensional ℂ (sourceH (P := P) (C := C) r s)) ∧
  (∀ (r : ℤ), 0 ≤ r → ∀ s, 0 < s → s ≤ 2 * n + 1 →
    Subsingleton (sourceH (P := P) (C := C) r s)) ∧
  (∀ (r : ℤ), r < 0 → ∀ s, s ≤ 2 * n →
    Subsingleton (sourceH (P := P) (C := C) r s)) ∧
  (∀ (r : ℤ) (s : ℕ), s ≤ 2 * n + 1 →
    Module.finrank ℂ (sourceH (P := P) (C := C) r s) =
      Module.finrank ℂ
        (sourceH (P := P) (C := C) (-r - (n : ℤ) - 1)
          (2 * n + 1 - s))) ∧
  Nonempty (HolomorphicTwistSections
    P.tangent P.connection C.contact.line 1 ≃ₗ[ℂ]
      ManifoldQuaternionicKillingFields.ComplexKillingFields P.tangent)

/-- The registered SW source theorem, formulated universally on the
actual compact positive quaternionic-Kähler manifold and its actual
nondegenerate holomorphic contact line. The canonical-line isomorphism
is a geometric prerequisite, not a conclusion assumed in the record. -/
def SWCohomologicalSource : Prop :=
  ∀ {E : Type u} {M : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (_hn : 2 ≤ n) (_hDim : Module.finrank ℝ E = 4 * n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    [HasSheafify (Opens.grothendieckTopology
      (TopCat.of (SphereBundleTotal P.tangent))) (ModuleCat.{v} ℂ)]
    [HasExt.{w} (TopCat.Sheaf (ModuleCat.{v} ℂ)
      (TopCat.of (SphereBundleTotal P.tangent)))],
    Nonempty (HolomorphicContactCanonicalIso
      P.tangent P.connection n A C.contact.line) →
      SWCohomologyConclusions P C

/-- Apply the registered general contact/canonical-line theorem first,
so the SW cohomology source never receives an unproved contact-root
identification as an independent assumption. -/
theorem swCohomology_of_generalContact
    (hSW : SWCohomologicalSource.{u,v,w})
    (hGeneral : GeneralContactCanonicalTheorem.{u,u,v})
    (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4 * n) :
    SWCohomologyConclusions P C :=
  hSW P n hn hDim A C
    (contactCanonicalIso_of_generalContact P.tangent P.connection hGeneral C)

/-- The genuine holomorphic Euler value with finiteness supplied by the
universal source theorem, after the contact/canonical identification has
been proved by the registered general-contact theorem. -/
def swHilbertValue
    (hSW : SWCohomologicalSource.{u,v,w})
    (hGeneral : GeneralContactCanonicalTheorem.{u,u,v})
    (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4 * n)
    (r : ℤ) : ℤ :=
  sourceP (P := P) (C := C) r
    ((swCohomology_of_generalContact P C hSW hGeneral hn hDim).1 r)

/-- The constant Hilbert value is derived from the universal source
cohomology contract and genuine constant holomorphic sections. -/
theorem swHilbertValue_zero_eq_one
    (hSW : SWCohomologicalSource.{u,v,w})
    (hGeneral : GeneralContactCanonicalTheorem.{u,u,v})
    (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4 * n)
    (x : SphereBundleTotal P.tangent) :
    swHilbertValue P C hSW hGeneral hn hDim 0 = 1 := by
  let H := swCohomology_of_generalContact P C hSW hGeneral hn hDim
  exact sw_hilbert_zero_eq_one P C hn hDim
    (contactCanonicalIso_of_generalContact P.tangent P.connection hGeneral C)
    x (H.1 0) (H.2.1 0 (by omega))

/-- Every negative integer twist between `-n` and `-1` is an actual
root of the Euler function furnished by the universal source theorem. -/
theorem swHilbertValue_negative_root
    (hSW : SWCohomologicalSource.{u,v,w})
    (hGeneral : GeneralContactCanonicalTheorem.{u,u,v})
    (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4 * n)
    (r : ℤ) (hrlo : -(n : ℤ) ≤ r) (hrhi : r < 0) :
    swHilbertValue P C hSW hGeneral hn hDim r = 0 := by
  let H := swCohomology_of_generalContact P C hSW hGeneral hn hDim
  exact sw_hilbert_negative_root P C hn hDim
    (contactCanonicalIso_of_generalContact P.tangent P.connection hGeneral C)
    r hrlo hrhi H.1 H.2.2.1 H.2.2.2.1

/-- The first Hilbert value is the dimension of genuine Killing fields;
the Salamon identification is supplied by the precise source contract. -/
theorem swHilbertValue_one_eq_killingDimension
    (hSW : SWCohomologicalSource.{u,v,w})
    (hGeneral : GeneralContactCanonicalTheorem.{u,u,v})
    (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4 * n) :
    swHilbertValue P C hSW hGeneral hn hDim 1 =
      (ManifoldQuaternionicKillingFields.killingDimension P.tangent : ℤ) := by
  let H := swCohomology_of_generalContact P C hSW hGeneral hn hDim
  obtain ⟨hSalamon⟩ := H.2.2.2.2
  exact sw_hilbert_one_eq_killingDimension P C hn hDim
    (contactCanonicalIso_of_generalContact P.tangent P.connection hGeneral C)
    (H.1 1) (H.2.1 1 (by omega)) hSalamon

include C

/-- The registered cohomology source also makes the real space of
Killing fields finite dimensional, as a proved consequence of finite
holomorphic `H⁰` and faithful-flat descent. -/
theorem swKillingFields_finiteDimensional_of_source
    (hSW : SWCohomologicalSource.{u,v,w})
    (hGeneral : GeneralContactCanonicalTheorem.{u,u,v})
    (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4 * n) :
    FiniteDimensional ℝ
      (ManifoldQuaternionicKillingFields.KillingFields P.tangent) := by
  let H := swCohomology_of_generalContact P C hSW hGeneral hn hDim
  obtain ⟨hSalamon⟩ := H.2.2.2.2
  exact sw_killingFields_finiteDimensional P C (H.1 1 0) hSalamon

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
