import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19481 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3249245 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨⟨[⟨.or, [6, 1]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [12, 11]⟩, ⟨.or, [12, 0]⟩, ⟨.or, [10, 13]⟩, ⟨.and, [15, 14]⟩, ⟨.not, [16]⟩, ⟨.or, [6, 14]⟩, ⟨.and, [18, 17]⟩], 19⟩, ?_, by decide, ?_⟩
  · intro gate hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
