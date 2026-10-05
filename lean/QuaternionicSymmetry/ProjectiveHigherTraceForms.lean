import QuaternionicSymmetry.ProjectiveAdjointDescent
import QuaternionicSymmetry.LocalTracePowerGauge

/-!
# Higher trace forms on a supplied projective gauge atlas

The local normalized curvature trace powers agree on overlaps of a supplied
projective gauge atlas.  We therefore construct actual chart-independent
scalar differential forms on its covered normed vector space, and descend
their local Chern--Weil closure.  This does not construct an atlas from PQK
geometry or a characteristic cohomology class.
-/

namespace QuaternionicSymmetry.ProjectiveAdjointDescent.GaugeAtlas

open QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionGauge
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalChernWeilTracePowers
  QuaternionicSymmetry.LocalTracePowerGauge
open scoped Topology

noncomputable section

variable {ι E A B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance higherTraceFormsNormedSpace : NormedSpace ℝ A :=
  NormedAlgebra.toNormedSpace A

variable (P : GaugeAtlas ι E A) (D : P.Connection)
  (τ : CyclicTrace (A := A) (B := B))

/-- Every positive curvature trace power has the same actual alternating form
on overlapping charts of the supplied projective gauge atlas. -/
theorem tracePower_transition (k : ℕ) (i j : ι) (x : E)
    (hi : x ∈ P.U i) (hj : x ∈ P.U j) :
    tracePowerForm τ.T (D.Γ i) k x =
      tracePowerForm τ.T (D.Γ j) k x := by
  exact (tracePowerForm_transition τ.T τ.cyclic (D.Γ i) (D.Γ j)
    (P.g i j) (P.g j i) x (D.patch i j x hi hj)
    (D.regular i x hi) (P.regular i j x hi hj)
    ((P.regular j i x hj hi).differentiableAt (by norm_num))
    (P.inverse_germ i j x hi hj) (P.inverse i j x hi hj) k).symm

/-- The chart-independent scalar differential form `T(F^(k+1))` on the
covered normed vector space, constructed from the supplied local connection. -/
def tracePowerSection (k : ℕ) (x : E) :
    E [⋀^Fin (powerDegree k)]→L[ℝ] B :=
  let i := Classical.choose (P.cover.exists_mem x)
  tracePowerForm τ.T (D.Γ i) k x

theorem tracePowerSection_eq_local (k : ℕ) (x : E) (i : ι)
    (hi : x ∈ P.U i) :
    tracePowerSection P D τ k x =
      tracePowerForm τ.T (D.Γ i) k x := by
  unfold tracePowerSection
  exact tracePower_transition P D τ k _ i x
    (Classical.choose_spec (P.cover.exists_mem x)) hi

/-- The degree-four member of the all-degree construction is exactly the
previously descended quadratic trace section. -/
theorem tracePowerSection_one_eq_traceSquareSection :
    tracePowerSection P D τ 1 = traceSquareSection P D τ := by
  funext x
  obtain ⟨i, hi⟩ := P.cover.exists_mem x
  rw [tracePowerSection_eq_local P D τ 1 x i hi,
    traceSquareSection_eq_local P D τ x i hi]
  exact congrFun (tracePowerForm_one_eq_traceSquareForm τ.T (D.Γ i)) x

theorem tracePowerSection_germ (k : ℕ) (x : E) (i : ι)
    (hi : x ∈ P.U i) :
    tracePowerSection P D τ k =ᶠ[𝓝 x]
      tracePowerForm τ.T (D.Γ i) k := by
  filter_upwards [((P.U i).isOpen.mem_nhds hi)] with y hy
  exact tracePowerSection_eq_local P D τ k y i hy

/-- Every descended positive curvature trace power is closed when the local
connection forms are C².  The premise concerns regularity, not closure. -/
theorem tracePowerSection_closed (k : ℕ)
    (hC2 : ∀ i x, x ∈ P.U i → ContDiffAt ℝ 2 (D.Γ i) x)
    (x : E) :
    extDeriv (tracePowerSection P D τ k) x = 0 := by
  obtain ⟨i, hi⟩ := P.cover.exists_mem x
  rw [(tracePowerSection_germ P D τ k x i hi).extDeriv_eq]
  exact tracePowerForm_closed τ.T τ.cyclic (D.Γ i) x (hC2 i x hi) k

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

local instance : NormedAddCommGroup (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

/-- The actual endomorphism-trace curvature power on a supplied projective
gauge atlas is closed in every positive degree. -/
theorem endomorphismTracePowerSection_closed
    (Q : GaugeAtlas ι E (V →L[ℝ] V)) (C : Q.Connection)
    (hC2 : ∀ i x, x ∈ Q.U i → ContDiffAt ℝ 2 (C.Γ i) x)
    (k : ℕ) (x : E) :
    extDeriv (tracePowerSection Q C (endomorphismCyclicTrace (V := V)) k) x = 0 :=
  tracePowerSection_closed Q C (endomorphismCyclicTrace (V := V)) k hC2 x

end
end QuaternionicSymmetry.ProjectiveAdjointDescent.GaugeAtlas
