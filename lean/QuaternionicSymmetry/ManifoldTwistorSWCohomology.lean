import QuaternionicSymmetry.ManifoldTwistorHolomorphicComplexCohomology
import QuaternionicSymmetry.ManifoldTwistorLeBrunExistenceInput

/-! Source-facing cohomological consequences of Semmelmann--Weingart,
"An upper bound for a Hilbert polynomial on quaternionic Kähler
manifolds", §2, pp. 2--3, arXiv:math/0208079v1. The source hypotheses
are applied to the actual positive quaternionic-Kähler twistor and
nondegenerate holomorphic contact line. Finiteness, Kodaira vanishing,
and Serre duality are explicit source inputs; no Hilbert value is input. -/

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

abbrev sourceH (r : ℤ) (s : ℕ) :=
  holomorphicTwistComplexCohomology P.tangent P.connection C.contact.line r s

abbrev sourceP (r : ℤ)
    (hfinite : ∀ s, FiniteDimensional ℂ (sourceH (P := P) (C := C) r s)) : ℤ :=
  holomorphicTwistComplexEulerCharacteristic
    P.tangent P.connection C.contact.line r (2 * n + 1) hfinite

/-- The constant Hilbert value follows from internally established
constant holomorphic sections and explicit source higher-cohomology
finiteness/vanishing. -/
theorem sw_hilbert_zero_eq_one
    (_hn : 2 ≤ n) (_hDim : Module.finrank ℝ E = 4 * n)
    (_hCanonical : Nonempty (HolomorphicContactCanonicalIso
      P.tangent P.connection n A C.contact.line))
    (x : SphereBundleTotal P.tangent)
    (hfinite : ∀ s, FiniteDimensional ℂ (sourceH (P := P) (C := C) 0 s))
    (hKodaira : ∀ s, 0 < s → s ≤ 2 * n + 1 →
      Subsingleton (sourceH (P := P) (C := C) 0 s)) :
    sourceP (P := P) (C := C) 0 hfinite = 1 := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  exact holomorphicTwistComplexEulerCharacteristic_zeroTwist
    P.tangent P.connection C.contact.line x hfinite hKodaira

/-- For nonnegative twists, the source's Kodaira vanishing leaves exactly
the dimension of the actual holomorphic contact-line sections. -/
theorem sw_hilbert_nonnegative_eq_sections
    (_hn : 2 ≤ n) (_hDim : Module.finrank ℝ E = 4 * n)
    (_hCanonical : Nonempty (HolomorphicContactCanonicalIso
      P.tangent P.connection n A C.contact.line))
    (r : ℤ) (hr : 0 ≤ r)
    (hfinite : ∀ s, FiniteDimensional ℂ (sourceH (P := P) (C := C) r s))
    (hKodaira : ∀ s, 0 < s → s ≤ 2 * n + 1 →
      Subsingleton (sourceH (P := P) (C := C) r s)) :
    sourceP (P := P) (C := C) r hfinite =
      (Module.finrank ℂ
        (HolomorphicTwistSections P.tangent P.connection C.contact.line r) : ℤ) := by
  exact holomorphicTwistComplexEulerCharacteristic_nonnegativeTwist
    P.tangent P.connection C.contact.line r hr hfinite hKodaira

/-- The source's negative-twist Kodaira range and top-degree Serre
duality force the consecutive integer roots `-n,…,-1`. This is derived
from cohomological statements, not supplied as a Hilbert-value premise. -/
theorem sw_hilbert_negative_root
    (_hn : 2 ≤ n) (_hDim : Module.finrank ℝ E = 4 * n)
    (_hCanonical : Nonempty (HolomorphicContactCanonicalIso
      P.tangent P.connection n A C.contact.line))
    (r : ℤ) (hrlo : -(n : ℤ) ≤ r) (hrhi : r < 0)
    (hfinite : ∀ (q : ℤ) (s : ℕ),
      FiniteDimensional ℂ (sourceH (P := P) (C := C) q s))
    (hKodaira : ∀ (q : ℤ), q < 0 → ∀ s, s ≤ 2 * n →
      Subsingleton (sourceH (P := P) (C := C) q s))
    (hSerre : ∀ (q : ℤ) (s : ℕ), s ≤ 2 * n + 1 →
      Module.finrank ℂ (sourceH (P := P) (C := C) q s) =
        Module.finrank ℂ
          (sourceH (P := P) (C := C) (-q - (n : ℤ) - 1)
            (2 * n + 1 - s))) :
    sourceP (P := P) (C := C) r (hfinite r) = 0 := by
  let q : ℤ := -r - (n : ℤ) - 1
  have hq : q < 0 := by dsimp [q]; omega
  have hq0 : Module.finrank ℂ (sourceH (P := P) (C := C) q 0) = 0 := by
    letI := hKodaira q hq 0 (by omega)
    simp [Module.finrank_zero_of_subsingleton]
  change holomorphicTwistComplexEulerCharacteristic
    P.tangent P.connection C.contact.line r (2 * n + 1) (hfinite r) = 0
  rw [holomorphicTwistComplexEulerCharacteristic_negativeTwist
    P.tangent P.connection C.contact.line r hrhi (hfinite r)
      (hKodaira r hrhi)]
  have hSerreTop := hSerre r (2 * n + 1) (le_refl _)
  rw [hSerreTop]
  have hzero : Module.finrank ℂ
      (sourceH (P := P) (C := C) (-r - (n : ℤ) - 1) 0) = 0 := by
    simpa only [q] using hq0
  have hSub : (2 * n + 1 : ℕ) - (2 * n + 1) = 0 := by omega
  rw [hSub, hzero]
  ring

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
