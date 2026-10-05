import QuaternionicSymmetry.ManifoldTwistorRawTransition

/-!
# Derivative of the coefficient-sphere embedding

The smooth embedding of the genuine sphere into the ambient rank-three
coefficient space has derivative equal to the previously checked
`sphereTangentAmbient` map. The result is also packaged for a product with
the raw base model, so derivatives of sphere transitions can be compared
with ambient Fréchet derivatives.
-/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff
noncomputable section
local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

def coefficientEmbedding (s : geometricSphere) : Fin 3 → ℝ :=
  (coefficientSphereHomeomorph.symm s).1

theorem coefficientEmbedding_mfderiv (s : geometricSphere)
    (v : TangentSpace (𝓡 2) s) :
    mfderiv (𝓡 2) 𝓘(ℝ,Fin 3 → ℝ) coefficientEmbedding s v =
      sphereTangentAmbient (⟨s,v⟩ : TangentBundle (𝓡 2) geometricSphere) := by
  let inc : geometricSphere → EuclideanThree := (↑)
  let lin := (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap
  have hinc : MDifferentiableAt (𝓡 2) 𝓘(ℝ,EuclideanThree) inc s :=
    (contMDiff_coe_sphere (m := ∞) (n := 2) (E := EuclideanThree)).mdifferentiableAt (by simp)
  have hlinSmooth : ContMDiff 𝓘(ℝ,EuclideanThree) 𝓘(ℝ,Fin 3 → ℝ) ∞ lin :=
    lin.contMDiff
  have hlin : MDifferentiableAt 𝓘(ℝ,EuclideanThree) 𝓘(ℝ,Fin 3 → ℝ) lin (inc s) :=
    hlinSmooth.mdifferentiableAt (by simp)
  change mfderiv (𝓡 2) 𝓘(ℝ,Fin 3 → ℝ) (lin ∘ inc) s v = _
  rw [mfderiv_comp s hlin hinc]
  rw [ContinuousLinearMap.mfderiv_eq]
  rfl

theorem coefficientEmbedding_smooth :
    ContMDiff (𝓡 2) 𝓘(ℝ,Fin 3 → ℝ) ∞ coefficientEmbedding := by
  convert ((EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.contMDiff).comp
    (contMDiff_coe_sphere (m := ∞) (n := 2) (E := EuclideanThree)) using 1

def productEmbedding {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ys : E × geometricSphere) : E × (Fin 3 → ℝ) :=
  (ys.1,coefficientEmbedding ys.2)

theorem productEmbedding_mfderiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (y : E) (s : geometricSphere)
    (u : E) (v : TangentSpace (𝓡 2) s) :
    mfderiv ((𝓘(ℝ,E)).prod (𝓡 2))
      ((𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ))
      (productEmbedding (E := E)) (y,s) (u,v) =
      (u,sphereTangentAmbient (⟨s,v⟩ : TangentBundle (𝓡 2) geometricSphere)) := by
  have hc : MDifferentiableAt (𝓡 2) 𝓘(ℝ,Fin 3 → ℝ)
      coefficientEmbedding s :=
    coefficientEmbedding_smooth.mdifferentiableAt (by simp)
  have hi : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) id y := mdifferentiableAt_id
  rw [show productEmbedding (E := E) = Prod.map id coefficientEmbedding from rfl]
  rw [mfderiv_prodMap hi hc, mfderiv_id]
  change (u, (mfderiv (𝓡 2) 𝓘(ℝ,Fin 3 → ℝ)
    coefficientEmbedding s) v) = _
  rw [coefficientEmbedding_mfderiv]
end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
