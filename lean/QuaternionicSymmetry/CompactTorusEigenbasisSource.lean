import QuaternionicSymmetry.TorusCharacterInput
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! BG-T2: a finite-dimensional continuous complex representation of a
compact torus has a basis of character vectors. This is the abelian
corollary of Knapp, second edition, IV.2, Proposition 4.6, Corollaries
4.7 and 4.9, and the example on pp.240–241 (continuity convention p.238).
`CompactTorusEigenbasisFromMathlib` now proves this exact interface using
Fourier projections, without a literature premise. The interface contains
no manifold, line bundle, projective action,
faithfulness, integral weights, or algebraic complexification. -/
namespace QuaternionicSymmetry.CompactTorusEigenbasisSource

open ManifoldQuaternionicTorusAction TorusCharacterInput
noncomputable section

/-- Precisely the finite-dimensional compact-torus character decomposition.
In particular the normed space and joint continuity are supplied hypotheses,
not consequences silently attached to an abstract section representation. -/
def KnappTorusEigenbasis : Prop :=
  ∀ (r : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Torus r →* Module.End ℂ V),
    Continuous (fun p : Torus r × V => ρ p.1 p.2) →
      ∃ b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V,
        ∃ χ : Fin (Module.finrank ℂ V) → (Torus r →ₜ* Circle),
          ∀ (t : Torus r) (i : Fin (Module.finrank ℂ V)),
            ρ t (b i) = (χ i t : ℂ) • b i

/-- The integral weights are derived from BG-T1's circle statement and
the already proved coordinate-circle decomposition, not included in BG-T2. -/
theorem exists_integral_eigenbasis
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    {r : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Torus r →* Module.End ℂ V)
    (hρ : Continuous (fun p : Torus r × V => ρ p.1 p.2)) :
    ∃ b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V,
      ∃ μ : Fin (Module.finrank ℂ V) → (Fin r → ℤ),
        ∀ (t : Torus r) (i : Fin (Module.finrank ℂ V)),
          ρ t (b i) = (weightCharacter (μ i) t : ℂ) • b i := by
  obtain ⟨b,χ,hχ⟩ := hEigen r V ρ hρ
  choose μ hμ using fun i => exists_weightCharacter hCircle (χ i)
  exact ⟨b,μ,fun t i => by rw [hχ, hμ]⟩

end
end QuaternionicSymmetry.CompactTorusEigenbasisSource
