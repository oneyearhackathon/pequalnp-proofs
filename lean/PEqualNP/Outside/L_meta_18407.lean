import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18407
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Split (a b c : List Bool) : Prop :=
  ∀ i, c.getD i false = true → a.getD i false = true ∨ b.getD i false = true

theorem foldSplit (gs : List Gate) (hg : ∀ g ∈ gs, g.op = .or) :
    ∀ a b c : List Bool, a.length = c.length → b.length = c.length → Split a b c →
      Split (gs.foldl step a) (gs.foldl step b) (gs.foldl step c) := by
  induction gs with
  | nil => intro a b c _ _ h; exact h
  | cons g gs ih =>
    intro a b c ha hb hs
    simp only [List.foldl_cons]
    apply ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))
    · simp [step, ha]
    · simp [step, hb]
    · intro i hi
      unfold step at hi ⊢
      by_cases h : i < c.length
      · rw [List.getD_append _ _ _ _ h] at hi
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact hs i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), ha, hb]
        by_cases hz : i - c.length = 0
        · rw [hz] at hi ⊢
          simp only [List.getD_cons_zero, hg g List.mem_cons_self, GateOp.eval,
            List.any_map, Function.comp_apply, id_eq, List.any_eq_true] at hi ⊢
          obtain ⟨j, hj, hv⟩ := hi
          rcases hs j hv with h' | h'
          · exact Or.inl ⟨j, hj, h'⟩
          · exact Or.inr ⟨j, hj, h'⟩
        · obtain ⟨k, hk⟩ : ∃ k, i - c.length = k + 1 := ⟨i - c.length - 1, by omega⟩
          rw [hk] at hi
          simp at hi


private abbrev d (i j : Fin 13) : Prop :=
  i-j=0 ∨ i-j=1 ∨ i-j=3 ∨ i-j=9

private abbrev row (Q : Finset (Fin 13)) :=
  (List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++
  List.ofFn fun j : Fin 13 => decide (∀ i ∈ Q, ¬ d i j)

private abbrev a : Finset (Fin 13) := {0,1,2,5}
private abbrev b : Finset (Fin 13) := {2,4,5,6}
private abbrev pos := (List.ofFn fun i : Fin 13 => decide (i=0)) ++ (List.ofFn fun i : Fin 13 => decide (i=0))

private theorem covered : Split (row a) (row b) pos := by
  intro i hi
  by_cases h : i < 26
  · have c : ∀ t : Fin 26, pos.getD t.val false = true → (row a).getD t.val false = true ∨ (row b).getD t.val false = true := by decide +kernel
    exact c ⟨i,h⟩ hi
  · rw [List.getD_eq_default _ _ (by change 26 ≤ i; omega)] at hi
    contradiction

end PEqualNP.Outside.L_meta_18407
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_18407 in
theorem PEqualNP.Outside.L_meta_18407 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (¬∃ (x3 : Fin x1.gates.length), (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 → (∀ (x5 x6 : Fin (13 : ℕ)), x5 - x6 = (0 : Fin (13 : ℕ)) ∨ x5 - x6 = (1 : Fin (13 : ℕ)) ∨ x5 - x6 = (3 : Fin (13 : ℕ)) ∨ x5 - x6 = (9 : Fin (13 : ℕ)) → x1.eval ((List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x6)) = Bool.true) → (∀ (x6 : Finset (Fin (13 : ℕ))), x6.card = (4 : ℕ) → (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x6 | x9 - x8 = (0 : Fin (13 : ℕ)) ∨ x9 - x8 = (1 : Fin (13 : ℕ)) ∨ x9 - x8 = (3 : Fin (13 : ℕ)) ∨ x9 - x8 = (9 : Fin (13 : ℕ))}.card ≤ (2 : ℕ)) → x1.eval ((List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x6)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (∀ x10 ∈ x6, ¬(x10 - x9 = (0 : Fin (13 : ℕ)) ∨ x10 - x9 = (1 : Fin (13 : ℕ)) ∨ x10 - x9 = (3 : Fin (13 : ℕ)) ∨ x10 - x9 = (9 : Fin (13 : ℕ))))) = Bool.false) → (64 : ℕ) ≤ x1.size := by
  intro C mono noAnd _ hp hn
  have onlyOr : ∀ g ∈ C.gates, g.op = .or := by
    intro g hg
    obtain ⟨op, _⟩ := mono g hg
    rcases op with ha | ho
    · obtain ⟨i, hi⟩ := List.getElem_of_mem hg
      exact (noAnd ⟨⟨i, hi.1⟩, by simpa [hi.2] using ha⟩).elim
    · exact ho
  have hx : C.eval pos = true := hp 0 0 (by decide)
  have ha : C.eval (row a) = false := hn a (by decide +kernel) (by decide +kernel)
  have hb : C.eval (row b) = false := hn b (by decide +kernel) (by decide +kernel)
  rcases foldSplit C.gates onlyOr _ _ _ (by decide +kernel) (by decide +kernel) covered C.output hx with hit | hit
  · change C.eval (row a) = true at hit
    simp [ha] at hit
  · change C.eval (row b) = true at hit
    simp [hb] at hit
