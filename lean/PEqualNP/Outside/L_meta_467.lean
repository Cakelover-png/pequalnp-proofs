import Mathlib

theorem PEqualNP.Outside.L_meta_467 :
    ∀ (m k : ℕ) (H : SimpleGraph (Fin m))
      (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop)
      (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k →
      (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
        Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨
          (p = 2 * k + 1 ∧ x.val = v.val) ∨
          (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) →
      (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔
        ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
          ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) →
      ∀ (T : Finset (Fin m)) (T' : Finset (Fin (m + 2 * k * (m * m)))),
        (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) →
        (∀ x : Fin (m + 2 * k * (m * m)),
          x ∈ T' ↔ (∃ u ∈ T, x.val = u.val) ∨
            ∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧
              x.val = m + 2 * k * (u.val * m + v.val) + i ∧
              (i % 2 = 1 ↔ u ∈ T)) →
        ∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y → x ∈ T' ∨ y ∈ T' := by
  intro m k H Q S hk hQ hS T T' hT hT' x y hxy
  obtain ⟨u, v, huv, hEdge, p, hp, hOrientation⟩ := (hS x y).mp hxy
  let offset := m + 2 * k * (u.val * m + v.val)
  have liftVertex (z : Fin m) (a : Fin (m + 2 * k * (m * m)))
      (hz : z ∈ T) (ha : a.val = z.val) : a ∈ T' :=
    (hT' a).mpr (Or.inl ⟨z, hz, ha⟩)
  have liftInner (i : ℕ) (a : Fin (m + 2 * k * (m * m)))
      (hi : i < 2 * k) (ha : a.val = offset + i)
      (hParity : i % 2 = 1 ↔ u ∈ T) : a ∈ T' :=
    (hT' a).mpr (Or.inr ⟨u, v, i, hi, huv, hEdge, ha, hParity⟩)
  have coverStep (a b : Fin (m + 2 * k * (m * m)))
      (ha : Q u v p a) (hb : Q u v (p + 1) b) : a ∈ T' ∨ b ∈ T' := by
    have haPos := (hQ u v p a).mp ha
    have hbPos := (hQ u v (p + 1) b).mp hb
    by_cases hStart : p = 0
    · by_cases hu : u ∈ T
      · left
        refine liftVertex u a hu ?_
        rcases haPos with h | h | h <;> omega
      · right
        refine liftInner 0 b (by omega) ?_ (by simp [hu])
        dsimp only [offset]
        rcases hbPos with h | h | h <;> omega
    · by_cases hEnd : p = 2 * k
      · by_cases hv : v ∈ T
        · right
          refine liftVertex v b hv ?_
          rcases hbPos with h | h | h <;> omega
        · left
          have hu : u ∈ T := (hT u v hEdge).resolve_right hv
          refine liftInner (p - 1) a (by omega) ?_ ?_
          · dsimp only [offset]
            rcases haPos with h | h | h <;> omega
          · simp only [hu, iff_true]
            omega
      · have haVal : a.val = offset + (p - 1) := by
          dsimp only [offset]
          rcases haPos with h | h | h <;> omega
        have hbVal : b.val = offset + p := by
          dsimp only [offset]
          rcases hbPos with h | h | h <;> omega
        by_cases hParity : (p - 1) % 2 = 1 ↔ u ∈ T
        · exact Or.inl (liftInner (p - 1) a (by omega) haVal hParity)
        · have hFlip : p % 2 = 1 ↔ u ∈ T := by
            by_cases hu : u ∈ T
            · simp only [hu, iff_true] at hParity ⊢
              omega
            · simp only [hu, iff_false] at hParity ⊢
              omega
          exact Or.inr (liftInner p b (by omega) hbVal hFlip)
  rcases hOrientation with h | h
  · exact coverStep x y h.1 h.2
  · exact (coverStep y x h.1 h.2).symm
