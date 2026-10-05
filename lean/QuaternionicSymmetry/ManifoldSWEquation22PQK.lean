import QuaternionicSymmetry.ManifoldTangentCharacterNumber
import QuaternionicSymmetry.ManifoldTwistorHolomorphicComplexCohomology
import QuaternionicSymmetry.ManifoldTwistorLeBrunContactNondegenerate
import QuaternionicSymmetry.ManifoldAnalyticPontryaginNormalization
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry

set_option maxHeartbeats 120000
set_option synthInstance.maxHeartbeats 40000

/-! Registered cohomological I1 source boundary: Semmelmann--Weingart
§2 Eq. (2.2) for the *actual* positive quaternionic-Kähler twistor space.
This premise mentions only individual nonnegative symmetric powers
`Sym^(n+2r)H`, never the virtual character or a symmetry bound.

The analytic Chern--Weil convention is explicit. The genuine rank-three
endomorphism bundle `Q` is the source's `Sym²H`; `u=p₁(H)=p₁(Q)/4` has
representative `−tr(F_Q²)/(32π²)`, checked algebraically in
`ManifoldAnalyticPontryaginNormalization`. `normalizedTangentHalfTrace`
is `(-1)^j tr(F_T^(2j))/(2(2π)^(2j))`, the half sum of powers of roots
`iF_T/(2π)`. The integration orientation is the canonical positive
quaternionic orientation used by `CompactConnectedPositiveQuaternionicKahlerGeometry`.
The cited RR/pushforward equality itself is an explicit source premise;
no integral Pontryagin class comparison or Dirac descent is claimed. -/
namespace QuaternionicSymmetry.ManifoldSWEquation22PQK
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldTangentCharacterNumber ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore CategoryTheory TopologicalSpace
open scoped Manifold ContDiff
noncomputable section

universe w
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (S : QuaternionicStructure E)
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))

variable [HasSheafify (Opens.grothendieckTopology
    (TopCat.of (SphereBundleTotal P.tangent))) (ModuleCat ℂ)]
  [twistorHasExt : HasExt.{w} (TopCat.Sheaf (ModuleCat ℂ)
    (TopCat.of (SphereBundleTotal P.tangent)))]

/-- Source SW Eq. (2.2), stated for the actual positive twistor and the
canonical tangent/rank-three Chern--Weil representatives. The dimension is
intrinsic: `n=S.quaternionicDimension` and `4n=finrank E` is proved from S. -/
def SWEquation22OnPQK
    (A : CompatibleComplexAtlas P.tangent P.connection S.quaternionicDimension)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection
      S.quaternionicDimension A) : Prop :=
  ∀ (hn : 2 ≤ S.quaternionicDimension) (r : ℤ)
    (hqr : 0 ≤ (S.quaternionicDimension : ℤ) + 2*r)
    (hfinite : ∀ s, FiniteDimensional ℂ
      (holomorphicTwistComplexCohomology P.tangent P.connection C.contact.line r s)),
    ((holomorphicTwistComplexEulerCharacteristic P.tangent P.connection C.contact.line r
      (2*S.quaternionicDimension+1) hfinite : ℤ) : ℝ) =
      characteristicFunctional P.tangent P.connection
        S.quaternionicDimension (S.quaternionicDimension-1)
        (show 4*((S.quaternionicDimension-1)+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (Characters.chi (((S.quaternionicDimension : ℤ) + 2*r).toNat))

/-- The integer twist corresponding to a symmetric-power exponent of the
same parity as the quaternionic dimension. -/
def twistForCharacter (n q : ℕ) : ℤ := ((q : ℤ) - (n : ℤ)) / 2

theorem twistForCharacter_correct (n q : ℕ) (hparity : q % 2 = n % 2) :
    (n : ℤ) + 2 * twistForCharacter n q = (q : ℤ) := by
  unfold twistForCharacter
  omega

set_option maxHeartbeats 400000
/-- The source formula at exactly the permitted χ(q) exponent; no
negative symmetric power is inferred from a negative Hilbert argument. -/
theorem sw_equation22_at_character
    (A : CompatibleComplexAtlas P.tangent P.connection S.quaternionicDimension)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection
      S.quaternionicDimension A)
    (hSW : SWEquation22OnPQK S P A C)
    (hn : 2 ≤ S.quaternionicDimension) (q : ℕ)
    (hparity : q % 2 = S.quaternionicDimension % 2)
    (hfinite : ∀ s, FiniteDimensional ℂ
      (holomorphicTwistComplexCohomology P.tangent P.connection C.contact.line
        (twistForCharacter S.quaternionicDimension q) s)) :
    ((holomorphicTwistComplexEulerCharacteristic P.tangent P.connection C.contact.line
      (twistForCharacter S.quaternionicDimension q)
      (2*S.quaternionicDimension+1) hfinite : ℤ) : ℝ) =
      characteristicFunctional P.tangent P.connection
        S.quaternionicDimension (S.quaternionicDimension-1)
        (show 4*((S.quaternionicDimension-1)+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega) (Characters.chi q) := by
  let r := twistForCharacter S.quaternionicDimension q
  have hr := twistForCharacter_correct S.quaternionicDimension q hparity
  have hqr : 0 ≤ (S.quaternionicDimension : ℤ) + 2*r := by omega
  have h := hSW hn r hqr hfinite
  simpa only [r, hr, Int.toNat_natCast] using h

theorem sw_equation22_at_twist
    (A : CompatibleComplexAtlas P.tangent P.connection S.quaternionicDimension)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection
      S.quaternionicDimension A)
    (hSW : SWEquation22OnPQK S P A C)
    (hn : 2 ≤ S.quaternionicDimension) (r : ℤ)
    (hqr : 0 ≤ (S.quaternionicDimension : ℤ) + 2*r)
    (hfinite : ∀ s, FiniteDimensional ℂ
      (holomorphicTwistComplexCohomology P.tangent P.connection C.contact.line r s)) :
    ((holomorphicTwistComplexEulerCharacteristic P.tangent P.connection C.contact.line r
      (2*S.quaternionicDimension+1) hfinite : ℤ) : ℝ) =
      characteristicFunctional P.tangent P.connection
        S.quaternionicDimension (S.quaternionicDimension-1)
        (show 4*((S.quaternionicDimension-1)+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (Characters.chi (((S.quaternionicDimension : ℤ) + 2*r).toNat)) :=
  hSW hn r hqr hfinite

end
end QuaternionicSymmetry.ManifoldSWEquation22PQK
