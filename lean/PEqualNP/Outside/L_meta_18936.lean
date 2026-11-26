import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18936

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

end PEqualNP.Outside.L_meta_18936

open PEqualNP.Outside.L_meta_18936 PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.L_meta_18936 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3) ∧ ∀ (x3 : Fin (26 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → ∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → ∃ x8 < x3.gates.length, PEqualNP.EdgeOwnership.Owns (26 : ℕ) x3 x8 (Fin.castAdd (13 : ℕ) x5) (Fin.natAdd (13 : ℕ) x6) := by
  classical
  intro inc good C h p l hp
  obtain ⟨ops,correct⟩ := h
  let u := Fin.castAdd 13 p
  let v := Fin.natAdd 13 l
  let x := pairInput u v
  let one (z : Fin 26) : Fin 26 → Bool := fun i => decide (i = z)
  have positive : W 26 C x C.output = true := (correct x).mpr ⟨p,l,hp,by simp [x,pairInput,u],by simp [x,pairInput,v]⟩
  have single (z : Fin 26) : W 26 C (one z) C.output ≠ true := by
    intro hz
    obtain ⟨a,b,_,ha,hb⟩ := (correct _).mp hz
    have ea : Fin.castAdd 13 a = z := of_decide_eq_true ha
    have eb : Fin.natAdd 13 b = z := of_decide_eq_true hb
    have e := congrArg Fin.val (ea.trans eb.symm)
    simp at e
    omega
  let active (k : ℕ) := k < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.and ∧ W 26 C x (26+k) = true
  have existsActive : ∃ k, active k := by
    by_contra! none
    have push (j : ℕ) (hj : W 26 C x j = true) : ∃ z, W 26 C (one z) j = true := by
      induction j using Nat.strong_induction_on with
      | _ j ih =>
        by_cases small : j < 26
        · exact ⟨⟨j,small⟩,by rw [W_input _ _ _ _ small]; simp [one]⟩
        let k := j-26
        have eqn : 26+k = j := by dsimp [k]; omega
        have hk : k < C.gates.length := by
          by_contra! too
          have hw := wires_length 26 C x
          have := getD_ge_length (C.wires (List.ofFn x)) j (by omega)
          exact Bool.noConfusion (this.symm.trans hj)
        obtain ⟨hop,a,b,inp,_,ha,hb⟩ := ops k C.gates[k] (by simp [hk])
        have atEq := gateAt_eq C k hk
        rw [← eqn] at hj ⊢
        rcases hop with op | op
        · exact False.elim (none k ⟨hk,by rw [atEq]; exact op,hj⟩)
        · have atOr (y : Fin 26 → Bool) : W 26 C y (26+k) = (W 26 C y a || W 26 C y b) := by
            rw [W_gate 26 C y k hk,atEq,op,inp]
            simp [GateOp.eval,ha,hb]
          rw [atOr, Bool.or_eq_true] at hj
          rcases hj with hv | hv
          · obtain ⟨z,hz⟩ := ih a (by omega) hv
            exact ⟨z,by rw [atOr,hz]; simp⟩
          · obtain ⟨z,hz⟩ := ih b (by omega) hv
            exact ⟨z,by rw [atOr,hz]; simp⟩
    obtain ⟨z,hz⟩ := push C.output positive
    exact single z hz
  let j := Nat.find existsActive
  obtain ⟨hj,hop,hv⟩ := Nat.find_spec existsActive
  refine ⟨j,hj,hj,hop,hv,?_⟩
  intro k hk _ hka
  by_contra! yes
  exact (Nat.find_min existsActive hk) ⟨by omega,hka,Bool.eq_true_of_not_eq_false yes⟩
