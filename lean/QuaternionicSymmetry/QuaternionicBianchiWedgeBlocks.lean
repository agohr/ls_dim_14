import QuaternionicSymmetry.QuaternionicBianchiWedgeEight

/-! The eight-dimensional Bianchi calculation applies to every pair of
quaternionic basis blocks, and therefore to every quaternionic dimension
at least two. -/
namespace QuaternionicSymmetry.QuaternionicBianchiWedgeBlocks
open QuaternionicBianchiWedgeEight
noncomputable section

def blockOmega {β : Type*} [DecidableEq β] (t : Fin 3)
    (p q : β × Fin 4) : ℝ :=
  if p.1 = q.1 then
    ![QuaternionicStructure.omegaICoeff,
      QuaternionicStructure.omegaJCoeff,
      QuaternionicStructure.omegaKCoeff] t p.2 q.2
  else 0

def blockMap {β : Type*} (i j : β) (k : Fin 8) : β × Fin 4 :=
  (if k.val < 4 then i else j, ⟨k.val % 4, Nat.mod_lt _ (by decide)⟩)

private theorem blockOmega_map {β : Type*} [DecidableEq β]
    (i j : β) (hij : i ≠ j) (t : Fin 3) (k l : Fin 8) :
    blockOmega t (blockMap i j k) (blockMap i j l) = omega t k l := by
  have hji : j ≠ i := Ne.symm hij
  fin_cases k <;> fin_cases l <;>
    simp [blockMap, blockOmega, omega, hij, hji]

theorem coefficients_on_pair {β : Type*} [DecidableEq β]
    (a : Fin 3 → (β × Fin 4) → (β × Fin 4) → ℝ)
    (hsk : ∀ t p q, a t p q = -a t q p)
    (h : ∀ s t p q r u, wedge (a s) (blockOmega t) p q r u =
      wedge (a t) (blockOmega s) p q r u)
    (i j : β) (hij : i ≠ j) :
    ∀ t k l,
      a t (blockMap i j k) (blockMap i j l) =
        a 0 (i,0) (i,1) * omega t k l := by
  let A : Fin 3 → Fin 8 → Fin 8 → ℝ :=
    fun t k l => a t (blockMap i j k) (blockMap i j l)
  have hA : ∀ s t k l m n, wedge (A s) (omega t) k l m n =
      wedge (A t) (omega s) k l m n := by
    intro s t k l m n
    have he := h s t (blockMap i j k) (blockMap i j l)
      (blockMap i j m) (blockMap i j n)
    simpa only [wedge, blockOmega_map i j hij, A] using he
  have hAsk : ∀ t k l, A t k l = -A t l k :=
    fun t k l => hsk t _ _
  simpa only [A, blockMap, show (0 : Fin 8).val = 0 from rfl,
    show (1 : Fin 8).val = 1 from rfl, Nat.zero_mod, if_pos (by decide : 0 < 4),
    if_pos (by decide : 1 < 4)] using coefficients A hA hAsk

private theorem first_map {β : Type*} (i j : β) (k : Fin 4) :
    blockMap i j ⟨k.val, by omega⟩ = (i,k) := by
  simp [blockMap, k.isLt, Nat.mod_eq_of_lt k.isLt]

private theorem second_map {β : Type*} (i j : β) (k : Fin 4) :
    blockMap i j ⟨k.val + 4, by omega⟩ = (j,k) := by
  simp [blockMap, show ¬k.val + 4 < 4 by omega, Nat.add_mod,
    Nat.mod_eq_of_lt k.isLt]

theorem coefficients {β : Type*} [DecidableEq β] [Nontrivial β]
    (a : Fin 3 → (β × Fin 4) → (β × Fin 4) → ℝ)
    (hsk : ∀ t p q, a t p q = -a t q p)
    (h : ∀ s t p q r u, wedge (a s) (blockOmega t) p q r u =
      wedge (a t) (blockOmega s) p q r u)
    (i₀ : β) :
    ∀ t p q, a t p q = a 0 (i₀,0) (i₀,1) * blockOmega t p q := by
  have hs (i j : β) (hij : i ≠ j) (t : Fin 3) (k l : Fin 4) :
      a t (i,k) (i,l) = a 0 (i,0) (i,1) * blockOmega t (i,k) (i,l) := by
    have he := coefficients_on_pair a hsk h i j hij t
      ⟨k.val, by omega⟩ ⟨l.val, by omega⟩
    rw [← blockOmega_map i j hij, first_map, first_map] at he
    exact he
  have hc (i j : β) (hij : i ≠ j) (t : Fin 3) (k l : Fin 4) :
      a t (i,k) (j,l) = a 0 (i,0) (i,1) * blockOmega t (i,k) (j,l) := by
    have he := coefficients_on_pair a hsk h i j hij t
      ⟨k.val, by omega⟩ ⟨l.val + 4, by omega⟩
    rw [← blockOmega_map i j hij, first_map, second_map] at he
    exact he
  have hv (i : β) : a 0 (i,0) (i,1) = a 0 (i₀,0) (i₀,1) := by
    by_cases hi : i₀ = i
    · subst i
      rfl
    have he := coefficients_on_pair a hsk h i₀ i hi 0 4 5
    simpa [blockMap, omega, QuaternionicStructure.omegaICoeff] using he
  intro t ⟨i,k⟩ ⟨j,l⟩
  by_cases hij : i = j
  · subst j
    obtain ⟨j,hji⟩ := exists_ne i
    rw [hs i j (Ne.symm hji), hv]
  · rw [hc i j hij, hv]

end
end QuaternionicSymmetry.QuaternionicBianchiWedgeBlocks
