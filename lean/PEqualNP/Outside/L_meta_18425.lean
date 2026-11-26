import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18425
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩


lemma split_or {n : ℕ} (C : Circuit)
    (ops : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or)
    (a b : Fin n → Bool) (j : ℕ) :
    val C (List.ofFn (fun t => a t || b t)) j = true →
    val C (List.ofFn a) j = true ∨ val C (List.ofFn b) j = true := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    by_cases hj : j < n
    · have raw (f : Fin n → Bool) : val C (List.ofFn f) j = f ⟨j,hj⟩ := by
        rw [val_input List.length_ofFn hj]
        simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj]
      simp only [raw, Bool.or_eq_true]
      exact id
    · by_cases hend : n + C.gates.length ≤ j
      · rw [val_ge List.length_ofFn hend]
        simp
      · let k := j - n
        have hkj : n+k = j := by dsimp [k]; omega
        have hk : k < C.gates.length := by dsimp [k]; omega
        rw [← hkj, val_or List.length_ofFn hk (ops k hk),
          val_or List.length_ofFn hk (ops k hk), val_or List.length_ofFn hk (ops k hk)]
        rintro ⟨i, hi, hlt, hv⟩
        rcases ih i (by omega) hv with ha | hb
        · exact Or.inl ⟨i, hi, hlt, ha⟩
        · exact Or.inr ⟨i, hi, hlt, hb⟩


private lemma opsOnly (C : Circuit) (mono : PEqualNP.MetaComplexity.Monotone2 C) (hno : ¬∃ j : Fin C.gates.length, (C.gates.get j).op = .and) : ∀ j < C.gates.length, (gateAt C j).op = .or := by
  intro j hj
  have h := (mono _ (gateAt_mem hj)).1
  change (gateAt C j).op = .and ∨ (gateAt C j).op = .or at h
  refine h.resolve_left fun he => hno ⟨⟨j,hj⟩, ?_⟩
  rw [gateAt_eq hj] at he
  exact he

open PEqualNP.MetaComplexity

theorem branch : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (¬(∃ (x2 : Fin x1.gates.length), (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and)) → x1.size ≤ (63 : ℕ) → (∀ (x4 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) → ∃ (x5 : Fin (26 : ℕ)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x6 ∧ x6.size + (5 : ℕ) ≤ x1.size ∧ ∀ (x7 : Fin (26 : ℕ) → Bool), x6.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), (x8 = x9 ∨ x8 = x9 + (1 : Fin (13 : ℕ)) ∨ x8 = x9 + (3 : Fin (13 : ℕ)) ∨ x8 = x9 + (9 : Fin (13 : ℕ))) ∧ Fin.castAdd (13 : ℕ) x8 ≠ x5 ∧ Fin.natAdd (13 : ℕ) x9 ≠ x5 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true := by
  intro C hao hn _ sem
  exfalso
  have mono : Monotone2 C := fun g hg => ⟨hao.1 g hg, (hao.2.2 g hg).le⟩
  let edge (x : Fin 26 → Bool) := ∃ i j : Fin 13,
    (i=j ∨ i=j+1 ∨ i=j+3 ∨ i=j+9) ∧ x (Fin.castAdd 13 i) = true ∧ x (Fin.natAdd 13 j) = true
  let a : Fin 26 → Bool := fun i => decide (i=0)
  let b : Fin 26 → Bool := fun i => decide (i=13)
  have ha : ¬ edge a := by decide +kernel
  have hb : ¬ edge b := by decide +kernel
  have hc : edge (fun i => a i || b i) := ⟨0,0,Or.inl rfl,rfl,rfl⟩
  rcases split_or C (opsOnly C mono hn) a b C.output ((sem _).mpr hc) with h | h
  · exact ha ((sem _).mp h)
  · exact hb ((sem _).mp h)
end PEqualNP.Outside.L_meta_18425

theorem PEqualNP.Outside.L_meta_18425 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (¬∃ (x3 : Fin x1.gates.length), (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and) → x1.size ≤ (63 : ℕ) → (∀ (x5 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) → ∃ (x6 : Fin (26 : ℕ)) (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x7 ∧ x7.size + (5 : ℕ) ≤ x1.size ∧ ∀ (x8 : Fin (26 : ℕ) → Bool), x7.eval (List.ofFn x8) = Bool.true ↔ ∃ (x9 : Fin (13 : ℕ)) (x10 : Fin (13 : ℕ)), (x9 = x10 ∨ x9 = x10 + (1 : Fin (13 : ℕ)) ∨ x9 = x10 + (3 : Fin (13 : ℕ)) ∨ x9 = x10 + (9 : Fin (13 : ℕ))) ∧ Fin.castAdd (13 : ℕ) x9 ≠ x6 ∧ Fin.natAdd (13 : ℕ) x10 ≠ x6 ∧ x8 (Fin.castAdd (13 : ℕ) x9) = Bool.true ∧ x8 (Fin.natAdd (13 : ℕ) x10) = Bool.true := PEqualNP.Outside.L_meta_18425.branch
