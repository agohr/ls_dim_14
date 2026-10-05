import QuaternionicSymmetry.ComplexTorusHolomorphicStructure
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Genuine integral Laurent characters are holomorphic on the finite
complex-torus manifold. -/

namespace QuaternionicSymmetry.ComplexTorusCharacterHolomorphic

open TorusLaurentRepresentation ComplexTorusHolomorphicStructure
open scoped Manifold ContDiff BigOperators
noncomputable section

def allNonzero (r : ℕ) : Set (Fin r → ℂ) :=
  {x | ∀ i, x i ≠ 0}

theorem contDiffOn_coord_zpow {r : ℕ} (i : Fin r) (m : ℤ) :
    ContDiffOn ℂ ∞ (fun x : Fin r → ℂ => x i ^ m) (allNonzero r) := by
  have hcoord : ContDiffOn ℂ ∞ (fun x : Fin r → ℂ => x i) (allNonzero r) :=
    (contDiff_apply ℂ ℂ i).contDiffOn
  cases m with
  | ofNat n => simpa only [zpow_natCast] using hcoord.pow n
  | negSucc n =>
    have hpow := hcoord.pow (n + 1)
    have hinv := hpow.inv (fun x hx => pow_ne_zero _ (hx i))
    simpa only [zpow_negSucc] using hinv

def ambientCharacter {r : ℕ} (μ : Fin r → ℤ) (x : Fin r → ℂ) : ℂ :=
  ∏ i : Fin r, x i ^ μ i

theorem contDiffOn_ambientCharacter {r : ℕ} (μ : Fin r → ℤ) :
    ContDiffOn ℂ ∞ (ambientCharacter μ) (allNonzero r) := by
  simpa only [ambientCharacter] using
    (contDiffOn_prod (s := allNonzero r) (t := Finset.univ)
      (fun i hi => contDiffOn_coord_zpow i (μ i)))

theorem contMDiff_torusVal (r : ℕ) :
    ContMDiff 𝓘(ℂ, Fin r → ℂ) 𝓘(ℂ, Fin r → ℂ) ∞
      (torusVal r) :=
  contMDiff_isOpenEmbedding (torusVal_isOpenEmbedding r)

theorem complexWeightCharacter_holomorphic {r : ℕ} (μ : Fin r → ℤ) :
    ContMDiff 𝓘(ℂ, Fin r → ℂ) 𝓘(ℂ, ℂ) ∞
      (fun z : ComplexTorus r => (complexWeightCharacter μ z : ℂ)) := by
  have hA : ContMDiffOn 𝓘(ℂ, Fin r → ℂ) 𝓘(ℂ, ℂ) ∞
      (ambientCharacter μ) (allNonzero r) :=
    (contDiffOn_ambientCharacter μ).contMDiffOn
  have hmap : Set.MapsTo (torusVal r) Set.univ (allNonzero r) := by
    intro z hz i
    exact (z i).ne_zero
  have hcomp := hA.comp (contMDiff_torusVal r).contMDiffOn hmap
  apply contMDiffOn_univ.mp
  apply hcomp.congr
  intro z hz
  simp [ambientCharacter, torusVal, complexWeightCharacter]

end
end QuaternionicSymmetry.ComplexTorusCharacterHolomorphic
