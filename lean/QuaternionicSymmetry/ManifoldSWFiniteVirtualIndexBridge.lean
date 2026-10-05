import QuaternionicSymmetry.ManifoldSWEquation22PQK
import QuaternionicSymmetry.FiniteVirtualCharacterSpan

/-! Internal linear extension of the actual per-twist SW formula to the
virtual character in dimensions 2--14. The source premise mentions only
ordinary nonnegative symmetric powers. The additive Euler-characteristic
map and all-degree cohomology finiteness remain explicit input here. -/
namespace QuaternionicSymmetry.ManifoldSWFiniteVirtualIndexBridge
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldSWEquation22PQK ManifoldTangentCharacterNumber
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open CategoryTheory TopologicalSpace
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

theorem index_virtual_eq_actual_characteristic
    (A : CompatibleComplexAtlas P.tangent P.connection S.quaternionicDimension)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection
      S.quaternionicDimension A)
    (hSW : SWEquation22OnPQK S P A C)
    (hn : 2 ≤ S.quaternionicDimension ∧ S.quaternionicDimension ≤ 14)
    (hfinite : ∀ (r : ℤ) (s : ℕ), FiniteDimensional ℂ
      (holomorphicTwistComplexCohomology P.tangent P.connection C.contact.line r s))
    (index : LaurentPolynomial ℚ →ₗ[ℚ] ℝ)
    (hindexEuler : ∀ q : ℕ,
      q ≤ S.quaternionicDimension + 2 →
      q % 2 = S.quaternionicDimension % 2 →
      index (Characters.chi q) =
        ((holomorphicTwistComplexEulerCharacteristic P.tangent P.connection
          C.contact.line (twistForCharacter S.quaternionicDimension q)
          (2*S.quaternionicDimension+1)
          (hfinite (twistForCharacter S.quaternionicDimension q)) : ℤ) : ℝ)) :
    index (Characters.virtual S.quaternionicDimension) =
      characteristicFunctional P.tangent P.connection
        S.quaternionicDimension (S.quaternionicDimension-1)
        (show 4*((S.quaternionicDimension-1)+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (Characters.virtual S.quaternionicDimension) := by
  apply FiniteVirtualCharacterSpan.maps_virtual_eq_of_chi
    S.quaternionicDimension hn index
    (characteristicFunctional P.tangent P.connection
      S.quaternionicDimension (S.quaternionicDimension-1)
      (show 4*((S.quaternionicDimension-1)+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega))
  intro q hq hparity
  rw [hindexEuler q hq hparity]
  exact sw_equation22_at_character S P A C hSW hn.1 q hparity
    (hfinite (twistForCharacter S.quaternionicDimension q))

end
end QuaternionicSymmetry.ManifoldSWFiniteVirtualIndexBridge
