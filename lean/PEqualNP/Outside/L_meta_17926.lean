import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_17926 : ∀ (x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ))) (x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool), (∀ (x3 x4 x5 x6 : Finset (Fin (13 : ℕ))), x3 ⊆ x4 → x5 ⊆ x6 → x2 x3 x5 = Bool.true → x2 x4 x6 = Bool.true) → (∀ (x4 x5 : Fin (13 : ℕ)), x4 ∈ x1 x5 → x2 {x4} {x5} = Bool.true) → x2 Finset.univ ∅ = Bool.false → (∀ (x6 : Fin (13 : ℕ)), x2 (x1 x6)ᶜ {x6} = Bool.false) → ∀ (x7 x8 : Finset (Fin (13 : ℕ))), x8.card ≤ (1 : ℕ) → (x2 x7 x8 = Bool.true ↔ ∃ x10 ∈ x7, ∃ x11 ∈ x8, x10 ∈ x1 x11) := by
  intro lines f mono flags empty avoid P L hL
  constructor
  · intro hf
    by_contra h
    by_cases h0 : L = ∅
    · subst L
      have bad := mono P Finset.univ ∅ ∅ (Finset.subset_univ _) (by rfl) hf
      simp_all
    · have hn : L.Nonempty := Finset.nonempty_iff_ne_empty.mpr h0
      have h1 : L.card = 1 := by have := Finset.card_pos.mpr hn; omega
      obtain ⟨l,rfl⟩ := Finset.card_eq_one.mp h1
      have sub : P ⊆ (lines l)ᶜ := by
        intro p hp
        apply Finset.mem_compl.mpr
        intro hit
        exact h ⟨p,hp,l,by simp,hit⟩
      have bad := mono P (lines l)ᶜ {l} {l} sub (by rfl) hf
      rw [avoid] at bad
      contradiction
  · rintro ⟨p,hp,l,hl,edge⟩
    exact mono {p} P {l} L (Finset.singleton_subset_iff.mpr hp)
      (Finset.singleton_subset_iff.mpr hl) (flags p l edge)
