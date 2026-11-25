import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9140_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool



def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs {n : ℕ} : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  omega

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim_one (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s', s' + 1 ≤ s ∧ HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length + 1 ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨acc.2.length, hlen, ⟨acc.2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Sum.inl false) ≠ Sum.inl c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Sum.inl false) = Sum.inl b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Sum.inl false)
      = Sum.inl b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      statVal (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y))
        ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) with
  | inl c => exact absurd hst (hout b c)
  | inr j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

theorem snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]

theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨s', hs, h'⟩ := gate_elim_one n _ b s hdep' hnc' hg
  refine ⟨s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

theorem gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''



def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem split_at {α : Type} (gs : List α) (p : ℕ) (g : α) (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  have hlt : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hget : gs[p] = g := (List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p, gs.drop (p + 1), ?_, by simp; omega⟩
  have h1 : gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
  have h2 : gs.drop p = gs[p] :: gs.drop (p + 1) := List.drop_eq_getElem_cons hlt
  exact h1.trans (by rw [h2, hget])

theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def initId (n : ℕ) : List Stat := List.ofFn fun i : Fin n => Sum.inr (i : ℕ)

theorem inv_initId (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (initId n, []) := by
  refine ⟨by simp [initId], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [initId, hlt, statValid, statVal, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [initId]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem exists_clean (n : ℕ) (f : BFn n) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) :
    ∃ gs o, CleanL n gs ∧ gs.length ≤ s ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set acc := elim n C.gates (initId n, []) with hacc
  have hinv : ∀ y : Fin n → Bool, Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ ok (inv_initId n y)
  have hcl : CleanL n acc.2 := by
    apply elim_clean n C.gates (initId n, []) ok
    · intro i
      by_cases hlt : i < n
      · simp [initId, hlt, statValid]
      · rw [List.getD_eq_default _ _ (by simp [initId]; omega)]; trivial
    · intro p g hp; simp at hp
  have hlen : acc.2.length ≤ s := by
    have := elim_len n C.gates (initId n, [])
    rw [← hacc] at this
    simp only [List.length_nil, zero_add] at this
    omega
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have e1 := ((hinv y).2 C.output).2
    have e2 := ((hinv y').2 C.output).2
    rw [hst] at e1 e2
    have h1 : (wiresFrom C.gates (List.ofFn y)).getD C.output false = f y := hev y
    have h2 : (wiresFrom C.gates (List.ofFn y')).getD C.output false = f y' := hev y'
    rw [← h1, ← h2, ← e1, ← e2]; rfl
  | inr j =>
    have hj : j < n + acc.2.length := by
      obtain ⟨y, _, _⟩ := hnc
      have := ((hinv y).2 C.output).1
      rw [hst] at this
      exact this
    refine ⟨acc.2, j, hcl, hlen, hj, ?_⟩
    intro x
    have e1 := ((hinv x).2 C.output).2
    rw [hst] at e1
    exact e1.trans (hev x)

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (neg save : Bool), P s ((if neg then inv a else a) :: kept save a r) →
      P (s+1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s+1) (a :: b :: r)) → P t ws

theorem Run.done {α inv meet join y} : @Run α inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem Run.perm {α inv meet join y s xs zs} (p : List.Perm xs zs)
    (h : @Run α inv meet join y s xs) : Run inv meet join y s zs :=
  fun P d q u b => q p (h P d q u b)

theorem Run.one {α inv meet join y s a r} (neg save : Bool)
    (h : @Run α inv meet join y s ((if neg then inv a else a) :: kept save a r)) :
    Run inv meet join y (s+1) (a :: r) := fun P d q u b => u neg save (h P d q u b)

theorem Run.two {α inv meet join y s a b r} (c ka kb : Bool)
    (h : @Run α inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s+1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

theorem Run.fold {α inv meet join y} {P : ∀ t ws, @Run α inv meet join y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run inv meet join y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (neg save : Bool)
      (h : Run inv meet join y s ((if neg then inv a else a) :: kept save a r)),
      P _ _ h → P _ _ (Run.one neg save h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h))
    {t ws} (h : Run inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run inv meet join y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun n k ⟨h', ih⟩ => ⟨Run.one n k h', one n k h' ih⟩)
    (fun c a b ⟨h', ih⟩ => ⟨Run.two c a b h', two c a b h' ih⟩)
  exact hex.elim fun _ hp => hp

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

def Reach (n : ℕ) (gs : List Gate) (o a : ℕ) : Prop :=
  ∀ P : ℕ → Prop, P o →
    (∀ q g, gs[q]? = some g → P (n + q) → ∀ u ∈ g.inputs, P u) → P a

theorem reach_self (n : ℕ) (gs : List Gate) (o : ℕ) : Reach n gs o o :=
  fun _ ho _ => ho

theorem reach_step {n : ℕ} {gs : List Gate} {o q u : ℕ} {g : Gate}
    (hq : gs[q]? = some g) (hr : Reach n gs o (n + q)) (hu : u ∈ g.inputs) :
    Reach n gs o u :=
  fun P ho hs => hs q g hq (hr P ho hs) u hu

theorem reach_cases {n : ℕ} {gs : List Gate} {o a : ℕ} (h : Reach n gs o a) :
    a = o ∨ ∃ q g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q) := by
  apply h (fun x => x = o ∨ ∃ q g, gs[q]? = some g ∧ x ∈ g.inputs ∧ Reach n gs o (n + q))
  · exact Or.inl rfl
  · intro q g hq hP u hu
    refine Or.inr ⟨q, g, hq, hu, ?_⟩
    rcases hP with rfl | ⟨q', g', hq', hin', hr'⟩
    · exact reach_self n gs (n + q)
    · exact reach_step hq' hr' hin'

def Live (n : ℕ) (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q)

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live n gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live n gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ_reach (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (hr : Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live n gs o (p + 1) a)) := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases reach_cases hr with h | ⟨q, g', hg', hin, hrq⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin, hrq⟩
        have := cleanG_lt (hcl q g' hg') _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

theorem live_succ_dead (n : ℕ) (gs : List Gate) (o : ℕ)
    (p : ℕ) (hnr : ¬ Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔ a ∈ liveList gs n o p := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    have hne : a ≠ n + p := by
      rintro rfl
      rcases hl with rfl | ⟨q, _, g', hg', hin, hrq⟩
      · exact hnr (reach_self n gs _)
      · exact hnr (reach_step hg' hrq hin)
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro ⟨hlt, hl⟩
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · by_cases hqp : q = p
      · subst hqp; exact absurd hrq hnr
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length) :
    ∀ d p, p + d = gs.length →
      ∃ d', d' ≤ d ∧
        Run (invF (n := n)) meetF joinF (val gs n o) d' ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _, _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1; omega
    exact ⟨0, le_rfl, Run.perm (hperm.map (val gs n)) Run.done⟩
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    obtain ⟨d', hd', IH⟩ := ih (p + 1) (by omega)
    by_cases hr : Reach n gs o (n + p)
    · have hstep := live_succ_reach n gs o hcl p g hg hr
      have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
        (mem_liveList _ _ _ _ _).2 ⟨cleanG_lt (hcl p g hg) a ha, Or.inr ⟨p, le_rfl, g, hg, ha, hr⟩⟩
      have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
        Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
      have hvg := val_gate n gs p g hg (cleanG_lt (hcl p g hg))
      have hnd0 := nodup_liveList gs n o p
      have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
          val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
          Run (invF (n := n)) meetF joinF (val gs n o) (d' + 1)
            ((liveList gs n o p).map (val gs n)) := by
        intro j neg hmem hval
        have hj := hin j ((hmem j).2 rfl)
        have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
          List.perm_cons_erase hj
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
            rw [mem_kept]
            rintro (⟨_, h⟩ | h)
            · exact hnew j hj h.symm
            · exact hnew _ (List.mem_of_mem_erase h) rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
            simp only [decide_eq_true_eq]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
                · exact Or.inr (Or.inr ⟨haj, h1⟩)
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hj, fun _ => h1⟩
              · exact Or.inr ⟨h2, fun h => absurd h h1⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        rw [List.map_cons, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
      refine ⟨d' + 1, by omega, ?_⟩
      rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
      · apply single j true
        · intro a; simp [hinp]
        · funext x; rw [hvg x, hop, hinp]; simp [GateOp.eval]
      · by_cases hjk : j = k
        · subst hjk
          apply single j false
          · intro a; simp [hinp]
          · funext x; rw [hvg x, hinp]; rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        · have hjm := hin j (by simp [hinp])
          have hkm := hin k (by simp [hinp])
          have hke : k ∈ (liveList gs n o p).erase j :=
            (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
          have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
          have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
          have hp1 : (liveList gs n o p).Perm
              (j :: k :: ((liveList gs n o p).erase j).erase k) :=
            (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
          have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
              a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
            intro a; rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
          have hp2 : (liveList gs n o (p + 1)).Perm
              ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j
                (kept (decide (Live n gs o (p + 1) k)) k
                  (((liveList gs n o p).erase j).erase k))) := by
            refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
            · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
              · rw [mem_kept, mem_kept]
                rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
                · exact hnew j hjm h.symm
                · exact hnew k hkm h.symm
                · exact hnew _ ((hmr _).1 h).2.2 rfl
              · rw [hmr]; simp
              · rw [mem_kept, hmr]
                rintro (⟨_, h⟩ | h)
                · exact hjk h
                · exact h.2.1 rfl
            · intro a
              rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
              simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
              constructor
              · rintro (h | ⟨h1, h2⟩)
                · exact Or.inl h
                · by_cases haj : a = j
                  · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                  · by_cases hak : a = k
                    · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                    · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
              · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
                · exact Or.inl h
                · exact Or.inr ⟨hjm, fun _ => h1⟩
                · exact Or.inr ⟨hkm, fun _ => h1⟩
                · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
          have IH' := Run.perm (hp2.map (val gs n)) IH
          have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
              then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
            funext x; rw [hvg x, hinp]
            rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
          rw [List.map_cons, kept_map, kept_map, hval] at IH'
          exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')
    · have hp : (liveList gs n o (p + 1)).Perm (liveList gs n o p) :=
        (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) (nodup_liveList _ _ _ _)).2
          (live_succ_dead n gs o p hr)
      exact ⟨d', by omega, Run.perm (hp.map (val gs n)) IH⟩

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  obtain ⟨gs, o, hcl, hlen, ho, hev⟩ := exists_clean n f s hnc h
  obtain ⟨d', hd', hrun⟩ := run_live n gs o hcl ho gs.length 0 (by omega)
  refine ⟨d', by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact hrun

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha, hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha, hb] | exact hw _ (by simp only [List.mem_cons]; tauto)


theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

theorem next_one {m y a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun m y s ((if neg then a ^^^ m else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  apply List.any_eq_true.2 ⟨neg, by cases neg <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht, hsl2]

theorem next_two_sorted {m y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {m y a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {m y t ws} (h : NatRun m y t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) →
      next (m) (s+2-zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and] <;>
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])


theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih



theorem simplify_nonot (op : GateOp) (hop : op ≠ GateOp.not) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op ≠ GateOp.not := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp)
  · exact absurd rfl hop
  · simp at hg
  · simp at hg

theorem elim_nonot (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, g.op ≠ GateOp.not) → (∀ g ∈ acc.2, g.op ≠ GateOp.not) →
    ∀ g ∈ (elim n gs acc).2, g.op ≠ GateOp.not := by
  induction gs with
  | nil => intro acc _ h; exact h
  | cons g gs ih =>
    intro acc hg h
    apply ih (elimStep n acc g) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_nonot _ (hg g List.mem_cons_self) _ _ g' (by simpa using h1)

theorem exists_clean_m (n : ℕ) (f : BFn n) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (h : ∃ C : Circuit, FanInTwo C ∧ (∀ g ∈ C.gates, g.op ≠ GateOp.not) ∧ C.size ≤ s ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    ∃ gs o, CleanL n gs ∧ (∀ (p : ℕ) (g : Gate), gs[p]? = some g → g.op ≠ GateOp.not) ∧ gs.length ≤ s ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, ok, hC, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set acc := elim n C.gates (initId n, []) with hacc
  have hinv : ∀ y : Fin n → Bool, Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ ok (inv_initId n y)
  have hcl : CleanL n acc.2 := by
    apply elim_clean n C.gates (initId n, []) ok
    · intro i
      by_cases hlt : i < n
      · simp [initId, hlt, statValid]
      · rw [List.getD_eq_default _ _ (by simp [initId]; omega)]; trivial
    · intro p g hp; simp at hp
  have hlen : acc.2.length ≤ s := by
    have := elim_len n C.gates (initId n, [])
    rw [← hacc] at this
    simp only [List.length_nil, zero_add] at this
    omega
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have e1 := ((hinv y).2 C.output).2
    have e2 := ((hinv y').2 C.output).2
    rw [hst] at e1 e2
    have h1 : (wiresFrom C.gates (List.ofFn y)).getD C.output false = f y := hev y
    have h2 : (wiresFrom C.gates (List.ofFn y')).getD C.output false = f y' := hev y'
    rw [← h1, ← h2, ← e1, ← e2]; rfl
  | inr j =>
    have hj : j < n + acc.2.length := by
      obtain ⟨y, _, _⟩ := hnc
      have := ((hinv y).2 C.output).1
      rw [hst] at this
      exact this
    refine ⟨acc.2, j, hcl, fun p g hp => elim_nonot n C.gates (initId n, []) hC (fun _ h => by simp at h) g (List.mem_of_getElem? hp), hlen, hj, ?_⟩
    intro x
    have e1 := ((hinv x).2 C.output).2
    rw [hst] at e1
    exact e1.trans (hev x)

open Classical in
theorem run_live_m (n : ℕ) (inv : BFn n → BFn n) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (hm : ∀ (p : ℕ) (g : Gate), gs[p]? = some g → g.op ≠ GateOp.not) (ho : o < n + gs.length) :
    ∀ d p, p + d = gs.length →
      ∃ d', d' ≤ d ∧
        Run inv meetF joinF (val gs n o) d' ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _, _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1; omega
    exact ⟨0, le_rfl, Run.perm (hperm.map (val gs n)) Run.done⟩
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    obtain ⟨d', hd', IH⟩ := ih (p + 1) (by omega)
    by_cases hr : Reach n gs o (n + p)
    · have hstep := live_succ_reach n gs o hcl p g hg hr
      have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
        (mem_liveList _ _ _ _ _).2 ⟨cleanG_lt (hcl p g hg) a ha, Or.inr ⟨p, le_rfl, g, hg, ha, hr⟩⟩
      have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
        Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
      have hvg := val_gate n gs p g hg (cleanG_lt (hcl p g hg))
      have hnd0 := nodup_liveList gs n o p
      have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
          val gs n (n + p) = (if neg then inv (val gs n j) else val gs n j) →
          Run inv meetF joinF (val gs n o) (d' + 1)
            ((liveList gs n o p).map (val gs n)) := by
        intro j neg hmem hval
        have hj := hin j ((hmem j).2 rfl)
        have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
          List.perm_cons_erase hj
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
            rw [mem_kept]
            rintro (⟨_, h⟩ | h)
            · exact hnew j hj h.symm
            · exact hnew _ (List.mem_of_mem_erase h) rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
            simp only [decide_eq_true_eq]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
                · exact Or.inr (Or.inr ⟨haj, h1⟩)
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hj, fun _ => h1⟩
              · exact Or.inr ⟨h2, fun h => absurd h h1⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        rw [List.map_cons, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
      refine ⟨d' + 1, by omega, ?_⟩
      rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
      · exact absurd hop (hm p g hg)
      · by_cases hjk : j = k
        · subst hjk
          apply single j false
          · intro a; simp [hinp]
          · funext x; rw [hvg x, hinp]; rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        · have hjm := hin j (by simp [hinp])
          have hkm := hin k (by simp [hinp])
          have hke : k ∈ (liveList gs n o p).erase j :=
            (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
          have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
          have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
          have hp1 : (liveList gs n o p).Perm
              (j :: k :: ((liveList gs n o p).erase j).erase k) :=
            (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
          have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
              a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
            intro a; rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
          have hp2 : (liveList gs n o (p + 1)).Perm
              ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j
                (kept (decide (Live n gs o (p + 1) k)) k
                  (((liveList gs n o p).erase j).erase k))) := by
            refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
            · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
              · rw [mem_kept, mem_kept]
                rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
                · exact hnew j hjm h.symm
                · exact hnew k hkm h.symm
                · exact hnew _ ((hmr _).1 h).2.2 rfl
              · rw [hmr]; simp
              · rw [mem_kept, hmr]
                rintro (⟨_, h⟩ | h)
                · exact hjk h
                · exact h.2.1 rfl
            · intro a
              rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
              simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
              constructor
              · rintro (h | ⟨h1, h2⟩)
                · exact Or.inl h
                · by_cases haj : a = j
                  · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                  · by_cases hak : a = k
                    · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                    · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
              · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
                · exact Or.inl h
                · exact Or.inr ⟨hjm, fun _ => h1⟩
                · exact Or.inr ⟨hkm, fun _ => h1⟩
                · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
          have IH' := Run.perm (hp2.map (val gs n)) IH
          have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
              then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
            funext x; rw [hvg x, hinp]
            rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
          rw [List.map_cons, kept_map, kept_map, hval] at IH'
          exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')
    · have hp : (liveList gs n o (p + 1)).Perm (liveList gs n o p) :=
        (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) (nodup_liveList _ _ _ _)).2
          (live_succ_dead n gs o p hr)
      exact ⟨d', by omega, Run.perm (hp.map (val gs n)) IH⟩

theorem exists_run_m {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : ∃ C : Circuit, FanInTwo C ∧ (∀ g ∈ C.gates, g.op ≠ GateOp.not) ∧ C.size ≤ s ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (fun a => a) meetF joinF f s' ws := by
  obtain ⟨gs, o, hcl, hm, hlen, ho, hev⟩ := exists_clean_m n f s hnc h
  obtain ⟨d', hd', hrun⟩ := run_live_m n (fun a => a) gs o hcl hm ho gs.length 0 (by omega)
  refine ⟨d', by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact hrun




theorem run_nil {α inv meet join y t} (h : @Run α inv meet join y t []) : False := by
  have key : ∀ t ws, @Run α inv meet join y t ws → ws ≠ [] := by
    intro t ws h
    induction h using Run.fold with
    | done => simp
    | perm hp _ ih => exact fun he => ih (List.Perm.eq_nil (he ▸ hp))
    | one => simp
    | two => simp
  exact key t [] h rfl

def isort (l : List ℕ) : List ℕ := l.insertionSort (· ≤ ·)

inductive BT where
  | lf : BT
  | nd : BT → List ℕ → BT → BT

def leqL : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: s, b :: t => Nat.beq a b && leqL s t
  | _, _ => false

theorem leqL_eq : ∀ a b : List ℕ, leqL a b = true → a = b
  | [], [], _ => rfl
  | a :: s, b :: t, h => by
      simp only [leqL, Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1, leqL_eq s t h.2]
  | [], _ :: _, h => by simp [leqL] at h
  | _ :: _, [], h => by simp [leqL] at h

theorem leqL_self : ∀ a : List ℕ, leqL a a = true
  | [] => rfl
  | a :: s => by simp [leqL, leqL_self s]

def ltL : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: s, b :: t => Nat.blt a b || (Nat.beq a b && ltL s t)

def BT.mem : BT → List ℕ → Bool
  | .lf, _ => false
  | .nd l k r, x => leqL x k || (if ltL x k then l.mem x else r.mem x)

def BT.toList : BT → List (List ℕ)
  | .lf => []
  | .nd l k r => l.toList ++ k :: r.toList

theorem BT.mem_toList : ∀ (T : BT) (x : List ℕ), T.mem x = true → x ∈ T.toList
  | .lf, x, h => by simp [BT.mem] at h
  | .nd l k r, x, hm => by
      simp only [BT.mem, Bool.or_eq_true] at hm
      simp only [BT.toList, List.mem_append, List.mem_cons]
      rcases hm with he | hm
      · exact Or.inr (Or.inl (leqL_eq x k he))
      · split at hm
        · exact Or.inl (BT.mem_toList l x hm)
        · exact Or.inr (Or.inr (BT.mem_toList r x hm))

theorem all_app {α : Type} {p : α → Bool} {A B : List α} (ha : A.all p = true) (hb : B.all p = true) :
    (A ++ B).all p = true := by
  rw [List.all_append, ha, hb]; rfl

theorem cover {p : List ℕ → List (ℕ × ℕ) → Bool} (T : BT) (L : List (List ℕ × List (ℕ × ℕ)))
    (hK : T.toList = L.map Prod.fst) (hL : L.all (fun kh => p kh.1 kh.2) = true) :
    ∀ x, T.mem x = true → ∃ h, p x h = true := by
  intro x hx
  have h1 := BT.mem_toList T x hx
  rw [hK, List.mem_map] at h1
  obtain ⟨kh, hkh, rfl⟩ := h1
  exact ⟨kh.2, List.all_eq_true.1 hL kh hkh⟩


def accD (d : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t => Nat.lor (Nat.xor w (Nat.shiftRight w d)) (accD d t)


def accM (q : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t => bif Nat.testBit w q then accM q t else Nat.lor w (accM q t)

theorem accD_of (d i : ℕ) : ∀ (ws : List ℕ) (w : ℕ), w ∈ ws → w.testBit i ≠ w.testBit (d + i) →
    (accD d ws).testBit i = true
  | [], w, hw, _ => by simp at hw
  | u :: t, w, hw, hne => by
      have e : accD d (u :: t) = (u ^^^ (u >>> d)) ||| accD d t := rfl
      rw [e, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_shiftRight, Bool.or_eq_true]
      rcases List.mem_cons.1 hw with rfl | hw'
      · left; cases h1 : w.testBit i <;> cases h2 : w.testBit (d + i) <;> simp_all
      · right; exact accD_of d i t w hw' hne

theorem accM_of (q p : ℕ) : ∀ (ws : List ℕ) (w : ℕ), w ∈ ws → w.testBit p = true →
    w.testBit q = false → (accM q ws).testBit p = true
  | [], w, hw, _, _ => by simp at hw
  | u :: t, w, hw, hp, hq => by
      rcases List.mem_cons.1 hw with rfl | hw'
      · have e : accM q (w :: t) = w ||| accM q t := by simp [accM, hq]
        rw [e, Nat.testBit_or, hp, Bool.true_or]
      · have ih := accM_of q p t w hw' hp hq
        cases hu : Nat.testBit u q
        · have e : accM q (u :: t) = u ||| accM q t := by simp [accM, hu]
          rw [e, Nat.testBit_or, ih, Bool.or_true]
        · have e : accM q (u :: t) = accM q t := by simp [accM, hu]
          rw [e, ih]

theorem land_sub {R X i : ℕ} (h : Nat.beq (Nat.land R X) R = true) (hi : R.testBit i = true) :
    X.testBit i = true := by
  have he : (R &&& X) = R := Nat.eq_of_beq_eq_true h
  have h2 := congrArg (fun z => Nat.testBit z i) he
  simp only [Nat.testBit_and, hi, Bool.true_and] at h2
  exact h2

theorem land_of {R X : ℕ} (h : ∀ i, R.testBit i = true → X.testBit i = true) :
    Nat.beq (Nat.land R X) R = true := by
  have he : (R &&& X) = R := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hi : R.testBit i
    · rfl
    · rw [h i hi]; rfl
  exact Nat.beq_eq_true_eq _ _ ▸ he

def distOK (pD : List (ℕ × ℕ)) (ws : List ℕ) : Bool :=
  pD.all fun dr => Nat.beq (Nat.land dr.2 (accD dr.1 ws)) dr.2

def monoOK (pM : List (ℕ × ℕ)) (ws : List ℕ) : Bool :=
  pM.all fun qp => Nat.beq (Nat.land qp.2 (accM qp.1 ws)) qp.2

def via (y : ℕ) (pD pM : List (ℕ × ℕ)) (t : ℕ) (ws : List ℕ) : Bool :=
  Nat.ble ws.length (t + 1) && (t != 0 || leqL ws [y]) && distOK pD ws &&
    (ws.length != t + 1 || monoOK pM ws)


def prsOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) : Bool :=
  pD.all (fun dr => Nat.beq (Nat.land dr.2 (Nat.xor y (Nat.shiftRight y dr.1))) dr.2 &&
    Nat.beq (Nat.land dr.2 (Nat.xor m (Nat.shiftRight m dr.1))) 0) &&
  pM.all (fun qp => Nat.beq (Nat.land qp.2 y) qp.2 && !Nat.testBit y qp.1)

theorem land_zero {R X i : ℕ} (h : Nat.beq (Nat.land R X) 0 = true) (hi : R.testBit i = true) :
    X.testBit i = false := by
  have he : (R &&& X) = 0 := Nat.eq_of_beq_eq_true h
  have h2 := congrArg (fun z => Nat.testBit z i) he
  simp only [Nat.testBit_and, hi, Bool.true_and, Nat.zero_testBit] at h2
  exact h2

theorem via_sound {m y : ℕ} {pD pM : List (ℕ × ℕ)} (hp : prsOK m y pD pM = true) {t : ℕ}
    {ws : List ℕ} (h : NatRun m y t ws) : via y pD pM t ws = true := by
  simp only [prsOK, Bool.and_eq_true, List.all_eq_true] at hp
  have hl := run_len h
  simp only [via, Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨⟨⟨by rw [Nat.ble_eq]; exact hl, ?_⟩, ?_⟩, ?_⟩
  · rcases Nat.eq_zero_or_pos t with rfl | ht
    · right; rw [zero_done h rfl]; exact leqL_self _
    · left; simp only [bne_iff_ne, ne_eq]; omega
  · simp only [distOK, List.all_eq_true]
    intro dr hdr
    apply land_of
    intro i hi
    have h12 := hp.1 dr hdr
    have hy : (y ^^^ (y >>> dr.1)).testBit i = true := land_sub h12.1 hi
    have hmx : (m ^^^ (m >>> dr.1)).testBit i = false := land_zero h12.2 hi
    simp only [Nat.testBit_xor, Nat.testBit_shiftRight] at hy hmx
    have hmm : m.testBit i = m.testBit (dr.1 + i) := by
      cases h1 : m.testBit i <;> cases h2 : m.testBit (dr.1 + i) <;> simp_all
    by_contra hc
    have hall : ∀ w ∈ ws, w.testBit i = w.testBit (dr.1 + i) := by
      intro w hw
      by_contra hne
      exact hc (accD_of dr.1 i ws w hw hne)
    have := run_bits h i (dr.1 + i) hmm hall
    rw [this] at hy; simp at hy
  · by_cases hlen : ws.length = t + 1
    · right
      simp only [monoOK, List.all_eq_true]
      intro qp hqp
      have h1 := hp.2 qp hqp
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
      apply land_of
      intro p hpP
      have hyp : y.testBit p = true := land_sub h1.1 hpP
      by_contra hc
      have hle : ∀ w ∈ ws, w.testBit p ≤ w.testBit qp.1 := by
        intro w hw
        cases h2 : w.testBit p
        · exact Bool.false_le _
        · cases h3 : w.testBit qp.1
          · exact absurd (accM_of qp.1 p ws w hw h2 h3) hc
          · exact le_refl _
      have := bits_le h hlen p qp.1 hle
      rw [hyp, h1.2] at this
      exact absurd this (by decide)
    · left; simpa using hlen


def actL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, w => Nat.bit (w.testBit p) (actL ps w)

theorem actL_testBit : ∀ (pi : List ℕ) (w k : ℕ),
    (actL pi w).testBit k = (pi[k]?.map w.testBit).getD false
  | [], w, k => by simp [actL]
  | p :: ps, w, 0 => by simp [actL, Nat.testBit_bit_zero]
  | p :: ps, w, k + 1 => by simp [actL, Nat.testBit_bit_succ, actL_testBit ps w k]

theorem actL_and (pi : List ℕ) (a b : ℕ) : actL pi (a &&& b) = actL pi a &&& actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_and]

theorem actL_or (pi : List ℕ) (a b : ℕ) : actL pi (a ||| b) = actL pi a ||| actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_or]

theorem actL_xor (pi : List ℕ) (a b : ℕ) : actL pi (a ^^^ b) = actL pi a ^^^ actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_xor]

theorem run_act {m y : ℕ} (pi : List ℕ) (hm : actL pi m = m) (hy : actL pi y = y) {t : ℕ}
    {ws : List ℕ} (h : NatRun m y t ws) : NatRun m y t (ws.map (actL pi)) := by
  have h2 := Run.map (actL pi) (inv' := (· ^^^ m)) (meet' := (· &&& ·)) (join' := (· ||| ·))
    (fun a => by simp only [actL_xor, hm]) (fun a b => actL_and pi a b) (fun a b => actL_or pi a b) h
  rwa [hy] at h2

def symOK (m y : ℕ) (G : List (List ℕ)) : Bool :=
  G.all fun pi => Nat.beq (actL pi m) m && Nat.beq (actL pi y) y

theorem symOK_mem {m y : ℕ} {G : List (List ℕ)} (hG : symOK m y G = true) {pi : List ℕ}
    (hpi : pi ∈ G) : actL pi m = m ∧ actL pi y = y := by
  have := List.all_eq_true.1 hG pi hpi
  simp only [Bool.and_eq_true] at this
  exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩


def hfind (G : List (List ℕ)) (T : BT) (t : ℕ) (h : List (ℕ × ℕ)) (tag : ℕ) (ys : List ℕ) : Bool :=
  match h.lookup tag with
  | some j =>
    match G[j]? with
    | some pi => T.mem (t :: isort (ys.map (actL pi)))
    | none => false
  | none => false

theorem hfind_false {m y : ℕ} {G : List (List ℕ)} (hG : symOK m y G = true) (T : BT) (t : ℕ)
    (ih : ∀ ws, NatRun m y t ws → T.mem (t :: isort ws) = false)
    (h : List (ℕ × ℕ)) (tag : ℕ) {ys : List ℕ} (hys : NatRun m y t ys) : hfind G T t h tag ys = false := by
  unfold hfind
  split
  · split
    · rename_i pi hpi
      have hmem : pi ∈ G := List.mem_of_getElem? hpi
      obtain ⟨hm, hy⟩ := symOK_mem hG hmem
      exact ih _ (run_act pi hm hy hys)
    · rfl
  · rfl

def stepOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) :
    List ℕ → List (ℕ × ℕ) → Bool
  | [], _ => false
  | 0 :: _, _ => false
  | (t + 1) :: es, h => !(next m (t + 2 - es.length) es
      (fun tag ys => via y pD pM t ys && !T.mem (t :: isort ys) && !hfind G T t h tag ys))

theorem closure_sound {m y : ℕ} {pD pM : List (ℕ × ℕ)} {G : List (List ℕ)} (T : BT)
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true) :
    ∀ t ws, NatRun m y t ws → T.mem (t :: isort ws) = false := by
  intro t
  induction t with
  | zero =>
    intro ws _
    cases hm : T.mem (0 :: isort ws)
    · rfl
    · obtain ⟨h, hs⟩ := hT _ hm
      simp [stepOK] at hs
  | succ t ih =>
    intro ws hw
    cases hm : T.mem ((t + 1) :: isort ws)
    · rfl
    · obtain ⟨h, hs⟩ := hT _ hm
      simp only [stepOK, Bool.not_eq_true'] at hs
      have hperm : (isort ws).Perm ws := List.perm_insertionSort _ _
      have hr : NatRun m y (t + 1) (isort ws) := Run.perm hperm.symm hw
      have hn := next_complete hr t rfl (isort ws) (List.Perm.refl _)
        (fun tag ys => via y pD pM t ys && !T.mem (t :: isort ys) && !hfind G T t h tag ys)
        (fun tag ys hys => by simp [via_sound hp hys, ih ys hys, hfind_false hG T t ih h tag hys])
      rw [hn] at hs; cases hs

def rootOK (y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap : ℕ) (zs : List ℕ) : Bool :=
  !via y pD pM cap zs || T.mem (cap :: isort zs) || G.any (fun pi => T.mem (cap :: isort (zs.map (actL pi))))

theorem cert_core {m y : ℕ} {xs : List ℕ} {pD pM : List (ℕ × ℕ)} {G : List (List ℕ)} {T : BT} {cap : ℕ}
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true)
    (hi : xs.sublists.all (rootOK y pD pM G T cap) = true)
    {s' : ℕ} (hs' : s' ≤ cap) {ws : List ℕ} (hsub : ws.Sublist xs) (hr : NatRun m y s' ws) : False := by
  have hmem := List.all_eq_true.1 hi _ (List.mem_sublists.2 hsub)
  revert hr hmem
  cases ws with
  | nil => intro hr _; exact run_nil hr
  | cons a r =>
    intro hr hmem
    have hcap : NatRun m y cap (a :: r) := extend_run hr hs'
    have hd := via_sound hp hcap
    have hc := closure_sound T hp hG hT cap (a :: r) hcap
    have hg : (G.any fun pi => T.mem (cap :: isort ((a :: r).map (actL pi)))) = false := by
      rw [List.any_eq_false]
      intro pi hpi
      obtain ⟨hm, hy⟩ := symOK_mem hG hpi
      rw [closure_sound T hp hG hT cap _ (run_act pi hm hy hcap)]
      simp
    unfold rootOK at hmem
    rw [hd, hc, hg] at hmem
    simp at hmem

theorem lb_cert {n : ℕ} (f : BFn n) (l : List ℕ) (m y : ℕ) (xs : List ℕ)
    (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap lb : ℕ)
    (hlb : cap + 1 = lb)
    (hm : m = 2 ^ l.length - 1)
    (hy : encL f l = y)
    (hxs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map
      (fun a => encL a l) = xs)
    (hnc : ∃ a b : Fin n → Bool, f a ≠ f b)
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true)
    (hi : xs.sublists.all (rootOK y pD pM G T cap) = true) :
    ∀ s, HasCircuitSize n f s → lb ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run f hnc s h
  have hr : NatRun m (encL f l) s' (ws.map fun a => encL a l) :=
    Run.map (fun a : BFn n => encL a l) (fun a => by rw [hm]; exact encL_inv a l)
      (fun a b => encL_and a b l) (fun a b => encL_or a b l) hrun
  rw [hy] at hr
  have hsub' : (ws.map fun a => encL a l).Sublist xs := by rw [← hxs]; exact hsub.map _
  exact cert_core hp hG hT hi (by omega) hsub' hr

def w0 : Nat := 0
def w1 : Nat := 65535
def w2 : Nat := 16711935
def w3 : Nat := 252645135
def w4 : Nat := 858993459
def w5 : Nat := 1431655765
def w6 : Nat := 2863311530
def w7 : Nat := 3435973836
def w8 : Nat := 4042322160
def w9 : Nat := 4278255360
def w10 : Nat := 4294901760
def w11 : Nat := 4294967295
def w12 : Nat := 1095216660735
def w13 : Nat := 16557098926080
def w14 : Nat := 16557098929935
def w15 : Nat := 56294136348672
def w16 : Nat := 56294136361779
def w17 : Nat := 93823560602965
def w18 : Nat := 93823560646655
def w19 : Nat := 187647121162240
def w20 : Nat := 187647121205930
def w21 : Nat := 225176545447116
def w22 : Nat := 264913582878960
def w23 : Nat := 280375465148160
def w24 : Nat := 281470681743360
def w25 : Nat := 281470681795788
def w26 : Nat := 281470681805040
def w27 : Nat := 281470681808895
def w28 : Nat := 281474976710655
def w29 : Nat := 4222189076152335
def w30 : Nat := 14355442858917939
def w31 : Nat := 23925738098196565
def w32 : Nat := 47851476196393130
def w33 : Nat := 57421771435671756
def w34 : Nat := 67555025218437360
def w35 : Nat := 71776119077928960
def w36 : Nat := 71776123356119040
def w37 : Nat := 71777214277877760
def w38 : Nat := 71777214294589695
def w39 : Nat := 71777218572845055
def w40 : Nat := 72057589742960640
def w41 : Nat := 72057589759737855
def w42 : Nat := 217020518463700992
def w43 : Nat := 217020518514230019
def w44 : Nat := 361695345325834240
def w45 : Nat := 361700864190383365
def w46 : Nat := 361700864358813455
def w47 : Nat := 723401728212336640
def w48 : Nat := 723401728380766730
def w49 : Nat := 768438411859724970
def w50 : Nat := 868082074056920076
def w51 : Nat := 922126094231669964
def w52 : Nat := 1080880403494997760
def w53 : Nat := 1085086035472220160
def w54 : Nat := 1085086039514480640
def w55 : Nat := 1085097073538170880
def w56 : Nat := 1085102592318504960
def w57 : Nat := 1085102592520621068
def w58 : Nat := 1085102592571146240
def w59 : Nat := 1085102592571150095
def w60 : Nat := 1085102596613472255
def w61 : Nat := 1085367505901322240
def w62 : Nat := 1085367506154029055
def w63 : Nat := 1152640029898506240
def w64 : Nat := 1152657617521213440
def w65 : Nat := 1152657617789587455
def w66 : Nat := 1229782938247303441
def w67 : Nat := 1229782938819965747
def w68 : Nat := 2459565875921944576
def w69 : Nat := 2459565876494606882
def w70 : Nat := 2459715994191571626
def w71 : Nat := 2497847057451721386
def w72 : Nat := 3038287259199220266
def w73 : Nat := 3472328296227680304
def w74 : Nat := 3472540227093983472
def w75 : Nat := 3526372316402430192
def w76 : Nat := 3674993371882992384
def w77 : Nat := 3675217672255110912
def w78 : Nat := 3689292520605548544
def w79 : Nat := 3689348813882916864
def w80 : Nat := 3689348814691381296
def w81 : Nat := 3689348814741897216
def w82 : Nat := 3689348814741910323
def w83 : Nat := 3689348818177884159
def w84 : Nat := 3689573990428311552
def w85 : Nat := 3689573991287357439
def w86 : Nat := 3746713415867891712
def w87 : Nat := 3746770585305219072
def w88 : Nat := 3746770586177582079
def w89 : Nat := 4539697694678990592
def w90 : Nat := 4557361348983324672
def w91 : Nat := 4557430887737720832
def w92 : Nat := 4557430888798830399
def w93 : Nat := 4919131752989213764
def w94 : Nat := 4919131755279862988
def w95 : Nat := 4919281870686178508
def w96 : Nat := 5497853135693827148
def w97 : Nat := 5787213827046133840
def w98 : Nat := 5787213829741015280
def w99 : Nat := 5787390436101386480
def w100 : Nat := 6124988953138320640
def w101 : Nat := 6124988955990490880
def w102 : Nat := 6125175870115086080
def w103 : Nat := 6148820867675914240
def w104 : Nat := 6148820870539182080
def w105 : Nat := 6148914689804861440
def w106 : Nat := 6148914691236517205
def w107 : Nat := 6148914694099828735
def w108 : Nat := 6149102336926023680
def w109 : Nat := 6149102338357723135
def w110 : Nat := 6196766167432910335
def w111 : Nat := 6845575888801652480
def w112 : Nat := 6872211557990727680
def w113 : Nat := 6872316418017198080
def w114 : Nat := 6872316419617283935
def w115 : Nat := 8102099357864587376
def w116 : Nat := 8574984534393648896
def w117 : Nat := 8608349214746279936
def w118 : Nat := 8608480565726806016
def w119 : Nat := 8608480567731124087
def w120 : Nat := 9259542123273814144
def w121 : Nat := 9799982325021313024
def w122 : Nat := 9838113388281462784
def w123 : Nat := 9838263503687778304
def w124 : Nat := 9838263505978427528
def w125 : Nat := 11529390970613309440
def w126 : Nat := 11574251045037015040
def w127 : Nat := 11574427651397386240
def w128 : Nat := 11574427654092267680
def w129 : Nat := 12153149036796881064
def w130 : Nat := 12249790989299875840
def w131 : Nat := 12249977903424471040
def w132 : Nat := 12249977906276641280
def w133 : Nat := 12288259087233755784
def w134 : Nat := 12295014589755599520
def w135 : Nat := 12297641732488560640
def w136 : Nat := 12297641735351828480
def w137 : Nat := 12297791853048793224
def w138 : Nat := 12297818344407081120
def w139 : Nat := 12297828652328593920
def w140 : Nat := 12297829379609722880
def w141 : Nat := 12297829381765628032
def w142 : Nat := 12297829381891459072
def w143 : Nat := 12297829381900337152
def w144 : Nat := 12297829381900372104
def w145 : Nat := 12297829382294118400
def w146 : Nat := 12297829382304563200
def w147 : Nat := 12297829382304604320
def w148 : Nat := 12297829382439348392
def w149 : Nat := 12297829382461849600
def w150 : Nat := 12297829382461893120
def w151 : Nat := 12297829382472990720
def w152 : Nat := 12297829382473025672
def w153 : Nat := 12297829382473031840
def w154 : Nat := 12297829382473033896
def w155 : Nat := 12297829382473034410
def w156 : Nat := 12297829383904690175
def w157 : Nat := 12297923203170304000
def w158 : Nat := 12297923206033637375
def w159 : Nat := 12321567108377804800
def w160 : Nat := 12321755117702348800
def w161 : Nat := 12321755120571230975
def w162 : Nat := 12659337080509235200
def w163 : Nat := 12659524724935557120
def w164 : Nat := 12659530243715891200
def w165 : Nat := 12659530246663417775
def w166 : Nat := 13527612317570695168
def w167 : Nat := 13527612320720337851
def w168 : Nat := 13835269164735971328
def w169 : Nat := 13889101254044418048
def w170 : Nat := 13889313181676863488
def w171 : Nat := 13889313184910721216
def w172 : Nat := 14468034567480590528
def w173 : Nat := 14468034567615334600
def w174 : Nat := 14699749187159851008
def w175 : Nat := 14699973484109365248
def w176 : Nat := 14699973487531969536
def w177 : Nat := 14738254668489084040
def w178 : Nat := 14754017507706719424
def w179 : Nat := 14757170078986272768
def w180 : Nat := 14757170082422194176
def w181 : Nat := 14757170083281174528
def w182 : Nat := 14757320200119123968
def w183 : Nat := 14757320200119158920
def w184 : Nat := 14757382013288497344
def w185 : Nat := 14757394382794312704
def w186 : Nat := 14757395255531667456
def w187 : Nat := 14757395257822316680
def w188 : Nat := 14757395258765525184
def w189 : Nat := 14757395258954271744
def w190 : Nat := 14757395258967588864
def w191 : Nat := 14757395258967641292
def w192 : Nat := 14757395259826634751
def w193 : Nat := 14757432788391873740
def w194 : Nat := 14757451549668016128
def w195 : Nat := 14757451553103989964
def w196 : Nat := 14757451553104003071
def w197 : Nat := 14771750701826559231
def w198 : Nat := 14902075604610108620
def w199 : Nat := 14974187289516638208
def w200 : Nat := 14974415773995368448
def w201 : Nat := 14974415777431342284
def w202 : Nat := 14974415777481871311
def w203 : Nat := 15924971278159633664
def w204 : Nat := 15987178197214944733
def w205 : Nat := 16204198715190198464
def w206 : Nat := 16204198715729174752
def w207 : Nat := 16909585770718358186
def w208 : Nat := 16927529800487840426
def w209 : Nat := 16927600440168677376
def w210 : Nat := 16927600443031988906
def w211 : Nat := 16927600443402535104
def w212 : Nat := 16927600444109941482
def w213 : Nat := 17063273453090303180
def w214 : Nat := 17072245467975044300
def w215 : Nat := 17072280789247118540
def w216 : Nat := 17072280789786094828
def w217 : Nat := 17149969068216863744
def w218 : Nat := 17149969068787297792
def w219 : Nat := 17197745778192984746
def w220 : Nat := 17197820540979511296
def w221 : Nat := 17197820543842822826
def w222 : Nat := 17197820544402115584
def w223 : Nat := 17197820544983690922
def w224 : Nat := 17207353456827616460
def w225 : Nat := 17207390839652535500
def w226 : Nat := 17207390840222969548
def w227 : Nat := 17215835218375274218
def w228 : Nat := 17216698428919906304
def w229 : Nat := 17216698429492559872
def w230 : Nat := 17216886072605147136
def w231 : Nat := 17216886075468458666
def w232 : Nat := 17216886076041068544
def w233 : Nat := 17216886076613722112
def w234 : Nat := 17216886076613765802
def w235 : Nat := 17216923605465353420
def w236 : Nat := 17216923606038006988
def w237 : Nat := 17216945682169913568
def w238 : Nat := 17216956720235866858
def w239 : Nat := 17216958927849057516
def w240 : Nat := 17216960843404410880
def w241 : Nat := 17216960843404471978
def w242 : Nat := 17216961131453612032
def w243 : Nat := 17216961134316923562
def w244 : Nat := 17216961134889585868
def w245 : Nat := 17216961135226446048
def w246 : Nat := 17216961135426464972
def w247 : Nat := 17216961135428553932
def w248 : Nat := 17216961135428562156
def w249 : Nat := 17216961135460011212
def w250 : Nat := 17216961135462187008
def w251 : Nat := 17216961135462239436
def w252 : Nat := 17216961135462247660
def w253 : Nat := 17216961135462248174
def w254 : Nat := 17293822573129236480
def w255 : Nat := 17294086451893370880
def w256 : Nat := 17294086455919964160
def w257 : Nat := 17294087486712115440
def w258 : Nat := 17294102948594384640
def w259 : Nat := 17339123139398922400
def w260 : Nat := 17348130476094714048
def w261 : Nat := 17357137812790505696
def w262 : Nat := 17361376563513262080
def w263 : Nat := 17361376567555522560
def w264 : Nat := 17361553176610734080
def w265 : Nat := 17361553176610775200
def w266 : Nat := 17361588498421825728
def w267 : Nat := 17361640450346250240
def w268 : Nat := 17361641477096079360
def w269 : Nat := 17361641479790960800
def w270 : Nat := 17361641480329937088
def w271 : Nat := 17361641481122672640
def w272 : Nat := 17361641481138339840
def w273 : Nat := 17361641481138401520
def w274 : Nat := 17361641481391046655
def w275 : Nat := 17361652519204352240
def w276 : Nat := 17361658034195005440
def w277 : Nat := 17361658038237327600
def w278 : Nat := 17361658038237331455
def w279 : Nat := 17365863605790044400
def w280 : Nat := 17365863670214553855
def w281 : Nat := 17506321826780868848
def w282 : Nat := 17578661995559780352
def w283 : Nat := 17578661999602102512
def w284 : Nat := 17578661999652631539
def w285 : Nat := 17654379923751630080
def w286 : Nat := 17723342345328784885
def w287 : Nat := 17938111029669066992
def w288 : Nat := 17940354033390252272
def w289 : Nat := 17940362863708270832
def w290 : Nat := 17940362863843014904
def w291 : Nat := 18014673391415521280
def w292 : Nat := 18014673391583296000
def w293 : Nat := 18062436906849446570
def w294 : Nat := 18062524863574179840
def w295 : Nat := 18062524866437491370
def w296 : Nat := 18062524867600773120
def w297 : Nat := 18062524867779689130
def w298 : Nat := 18080539541171272426
def w299 : Nat := 18082217421685453040
def w300 : Nat := 18082228416633958640
def w301 : Nat := 18082228416801733360
def w302 : Nat := 18084767257701908480
def w303 : Nat := 18084767257870336000
def w304 : Nat := 18084954900780810240
def w305 : Nat := 18084954904823070720
def w306 : Nat := 18084954904991541930
def w307 : Nat := 18085032171284787440
def w308 : Nat := 18085032171453214960
def w309 : Nat := 18085041001905977592
def w310 : Nat := 18085043205308416000
def w311 : Nat := 18085043208171727530
def w312 : Nat := 18085043208677017800
def w313 : Nat := 18085043209350738160
def w314 : Nat := 18085043209484957936
def w315 : Nat := 18085043209485480176
def w316 : Nat := 18085043209485482232
def w317 : Nat := 18085043209518510320
def w318 : Nat := 18085043209519104000
def w319 : Nat := 18085043209519165680
def w320 : Nat := 18085043209519167736
def w321 : Nat := 18085043209519168250
def w322 : Nat := 18086439546337095920
def w323 : Nat := 18158790778715962368
def w324 : Nat := 18206079296368868520
def w325 : Nat := 18216159773593488588
def w326 : Nat := 18216212549346315468
def w327 : Nat := 18216212550151634124
def w328 : Nat := 18225219886847425772
def w329 : Nat := 18226332609794863344
def w330 : Nat := 18226345803733070064
def w331 : Nat := 18226345803934399728
def w332 : Nat := 18228597638108347640
def w333 : Nat := 18229445395933298688
def w334 : Nat := 18229670572478745804
def w335 : Nat := 18229710309314064624
def w336 : Nat := 18229710309516177648
def w337 : Nat := 18229719139968938224
def w338 : Nat := 18229719139968940280
def w339 : Nat := 18229723503655714032
def w340 : Nat := 18229723550950883328
def w341 : Nat := 18229723554386857164
def w342 : Nat := 18229723554993205488
def w343 : Nat := 18229723555195321596
def w344 : Nat := 18302908165815073792
def w345 : Nat := 18302908165848628736
def w346 : Nat := 18350759637772402688
def w347 : Nat := 18350759642000325632
def w348 : Nat := 18350759642045021866
def w349 : Nat := 18360329937250745548
def w350 : Nat := 18369900231682477260
def w351 : Nat := 18369900232487795916
def w352 : Nat := 18370463191033511152
def w353 : Nat := 18373277983548961008
def w354 : Nat := 18373277983750290672
def w355 : Nat := 18374123533996261376
def w356 : Nat := 18374388447545454832
def w357 : Nat := 18374388447579140336
def w358 : Nat := 18374399485409292528
def w359 : Nat := 18374399485611405552
def w360 : Nat := 18374399485645091056
def w361 : Nat := 18374403883691602160
def w362 : Nat := 18374403896593350656
def w363 : Nat := 18374403900029324492
def w364 : Nat := 18374403900635672816
def w365 : Nat := 18374403900837788924
def w366 : Nat := 18374403900871474942
def w367 : Nat := 18374686479671623680
def w368 : Nat := 18374686483949813760
def w369 : Nat := 18374779942438196480
def w370 : Nat := 18374873400926535680
def w371 : Nat := 18374873400926579200
def w372 : Nat := 18374910784321932288
def w373 : Nat := 18374950366740541440
def w374 : Nat := 18374963560880077824
def w375 : Nat := 18374966855136706560
def w376 : Nat := 18374966856562791680
def w377 : Nat := 18374966857988876800
def w378 : Nat := 18374966858559310848
def w379 : Nat := 18374966859163299840
def w380 : Nat := 18374966859364629504
def w381 : Nat := 18374966859414896640
def w382 : Nat := 18374966859414961920
def w383 : Nat := 18374966859426103210
def w384 : Nat := 18374966859431673855
def w385 : Nat := 18374967589559402410
def w386 : Nat := 18374967950353367040
def w387 : Nat := 18374967954631622655
def w388 : Nat := 18375811297230192387
def w389 : Nat := 18377781652132396810
def w390 : Nat := 18378908608601456640
def w391 : Nat := 18379188984066604800
def w392 : Nat := 18379189044211875840
def w393 : Nat := 18379189048491114255
def w394 : Nat := 18384537154654240546
def w395 : Nat := 18389322297992282112
def w396 : Nat := 18389322302273879859
def w397 : Nat := 18398892597513158485
def w398 : Nat := 18410996206198128512
def w399 : Nat := 18413247456256524032
def w400 : Nat := 18413248040363163392
def w401 : Nat := 18413248040372076424
def w402 : Nat := 18420002855699152640
def w403 : Nat := 18420003542883434240
def w404 : Nat := 18420003542893920160
def w405 : Nat := 18422255377067868072
def w406 : Nat := 18422537230001766400
def w407 : Nat := 18422724872833597440
def w408 : Nat := 18422724877111787520
def w409 : Nat := 18422724877122972330
def w410 : Nat := 18422817605455773440
def w411 : Nat := 18422817605466914560
def w412 : Nat := 18422818189582466952
def w413 : Nat := 18422818292661682080
def w414 : Nat := 18422818331321958400
def w415 : Nat := 18422818332748043520
def w416 : Nat := 18422818334185269930
def w417 : Nat := 18422818334753475720
def w418 : Nat := 18422818335359037600
def w419 : Nat := 18422818335560891560
def w420 : Nat := 18422818335600213760
def w421 : Nat := 18422818335609126792
def w422 : Nat := 18422818335610699680
def w423 : Nat := 18422818335611289600
def w424 : Nat := 18422818335611354880
def w425 : Nat := 18422818335611355050
def w426 : Nat := 18429010054955990784
def w427 : Nat := 18429010879577128704
def w428 : Nat := 18429010879589711808
def w429 : Nat := 18431262713763135424
def w430 : Nat := 18431262713763659720
def w431 : Nat := 18432107379212156928
def w432 : Nat := 18432332555757604044
def w433 : Nat := 18432387754663935744
def w434 : Nat := 18432387754677305088
def w435 : Nat := 18432388338792857344
def w436 : Nat := 18432388338792857480
def w437 : Nat := 18432388579311026112
def w438 : Nat := 18432388626559008768
def w439 : Nat := 18432388629994982604
def w440 : Nat := 18432388630837264128
def w441 : Nat := 18432388630850633676
def w442 : Nat := 18438018216283406272
def w443 : Nat := 18438018216285503456
def w444 : Nat := 18440833009002938346
def w445 : Nat := 18441677528422547456
def w446 : Nat := 18441957903885467392
def w447 : Nat := 18441957903887695616
def w448 : Nat := 18441958634032136106
def w449 : Nat := 18441958921796059136
def w450 : Nat := 18441958925232032972
def w451 : Nat := 18441958926087684044
def w452 : Nat := 18441958926089912302
def w453 : Nat := 18442240478376099840
def w454 : Nat := 18442505391958978800
def w455 : Nat := 18442520853841248000
def w456 : Nat := 18442521880339415040
def w457 : Nat := 18442521884381737200
def w458 : Nat := 18442521884617670400
def w459 : Nat := 18442521884633399280
def w460 : Nat := 18445336673056194560
def w461 : Nat := 18445336677098516720
def w462 : Nat := 18445336677350178800
def w463 : Nat := 18445336677350834170
def w464 : Nat := 18445899635894321148
def w465 : Nat := 18446462598732840960
def w466 : Nat := 18446462598985482240
def w467 : Nat := 18446462601596108800
def w468 : Nat := 18446462602168762368
def w469 : Nat := 18446462602741415936
def w470 : Nat := 18446462602775101440
def w471 : Nat := 18446462603011031040
def w472 : Nat := 18446462603027742720
def w473 : Nat := 18446462603027804400
def w474 : Nat := 18446462603027808255
def w475 : Nat := 18446463633819894000
def w476 : Nat := 18446463698244403455
def w477 : Nat := 18446465914447527936
def w478 : Nat := 18446473641093693440
def w479 : Nat := 18446479155831767040
def w480 : Nat := 18446479160126668800
def w481 : Nat := 18446479160126672655
def w482 : Nat := 18446481367739863313
def w483 : Nat := 18446500132451975168
def w484 : Nat := 18446515585744318512
def w485 : Nat := 18446518892869189632
def w486 : Nat := 18446518897164091392
def w487 : Nat := 18446518897164103728
def w488 : Nat := 18446518897164104499
def w489 : Nat := 18446550907555369040
def w490 : Nat := 18446556061516125440
def w491 : Nat := 18446556426588345685
def w492 : Nat := 18446603890271944832
def w493 : Nat := 18446612136609155072
def w494 : Nat := 18446612720724672512
def w495 : Nat := 18446612720724707464
def w496 : Nat := 18446638524888227840
def w497 : Nat := 18446639212082954240
def w498 : Nat := 18446639212082995360
def w499 : Nat := 18446648042535757992
def w500 : Nat := 18446649520004464640
def w501 : Nat := 18446649520004508160
def w502 : Nat := 18446650245854003200
def w503 : Nat := 18446650248717314730
def w504 : Nat := 18446650249289959560
def w505 : Nat := 18446650249896304800
def w506 : Nat := 18446650250148904960
def w507 : Nat := 18446650250148937856
def w508 : Nat := 18446650250148939776
def w509 : Nat := 18446650250148939912
def w510 : Nat := 18446650250148945920
def w511 : Nat := 18446650250148946080
def w512 : Nat := 18446650250148948136
def w513 : Nat := 18446650250148948650
def w514 : Nat := 18446669014861021184
def w515 : Nat := 18446673709260324864
def w516 : Nat := 18446674533893996544
def w517 : Nat := 18446674533894045888
def w518 : Nat := 18446683364346806464
def w519 : Nat := 18446683364346808520
def w520 : Nat := 18446686903399809024
def w521 : Nat := 18446686903399861248
def w522 : Nat := 18446687487515413640
def w523 : Nat := 18446687728033582272
def w524 : Nat := 18446687775278235648
def w525 : Nat := 18446687778714209484
def w526 : Nat := 18446687779573137408
def w527 : Nat := 18446687779573189836
def w528 : Nat := 18446709855705088192
def w529 : Nat := 18446709855705096416
def w530 : Nat := 18446720893770989568
def w531 : Nat := 18446720893771038912
def w532 : Nat := 18446724286795205632
def w533 : Nat := 18446725016939593728
def w534 : Nat := 18446725016939645952
def w535 : Nat := 18446725304702468096
def w536 : Nat := 18446725308138441932
def w537 : Nat := 18446725308997369856
def w538 : Nat := 18446725308997422284
def w539 : Nat := 18446725308997431022
def w540 : Nat := 18446726485818408960
def w541 : Nat := 18446726485818470400
def w542 : Nat := 18446727173013237920
def w543 : Nat := 18446727310452191424
def w544 : Nat := 18446727512315658240
def w545 : Nat := 18446727516357980400
def w546 : Nat := 18446727516610560000
def w547 : Nat := 18446727516610601120
def w548 : Nat := 18446727516610609344
def w549 : Nat := 18446727516610621440
def w550 : Nat := 18446727516610621680
def w551 : Nat := 18446730828030345216
def w552 : Nat := 18446730828030406896
def w553 : Nat := 18446736347063384312
def w554 : Nat := 18446737480934748160
def w555 : Nat := 18446738211079127040
def w556 : Nat := 18446738211079188480
def w557 : Nat := 18446738550381608960
def w558 : Nat := 18446738554423931120
def w559 : Nat := 18446738554676510720
def w560 : Nat := 18446738554676562120
def w561 : Nat := 18446738554676572400
def w562 : Nat := 18446738554676574456
def w563 : Nat := 18446738554676574970
def w564 : Nat := 18446739679958006784
def w565 : Nat := 18446740710750158064
def w566 : Nat := 18446740762289765628
def w567 : Nat := 18446742609125638144
def w568 : Nat := 18446742952723083504
def w569 : Nat := 18446742974197923840
def w570 : Nat := 18446742978476179200
def w571 : Nat := 18446742978492825600
def w572 : Nat := 18446742978492877824
def w573 : Nat := 18446742978492887040
def w574 : Nat := 18446742978492890880
def w575 : Nat := 18446743197536157696
def w576 : Nat := 18446743704342364160
def w577 : Nat := 18446743708637265920
def w578 : Nat := 18446743708637318280
def w579 : Nat := 18446743708637327520
def w580 : Nat := 18446743708637331200
def w581 : Nat := 18446743708637331370
def w582 : Nat := 18446743854666219468
def w583 : Nat := 18446744009284976640
def w584 : Nat := 18446744009285038320
def w585 : Nat := 18446744009285042160
def w586 : Nat := 18446744052234649600
def w587 : Nat := 18446744052234711280
def w588 : Nat := 18446744069414584320
def w589 : Nat := 18446744069414606165
def w590 : Nat := 18446744069414636748
def w591 : Nat := 18446744069414646000
def w592 : Nat := 18446744069414649855
def w593 : Nat := 18446744069420154965
def w594 : Nat := 18446744069427953868
def w595 : Nat := 18446744069430313200
def w596 : Nat := 18446744069431296000
def w597 : Nat := 18446744069431296255
def w598 : Nat := 18446744069498799365
def w599 : Nat := 18446744069616700428
def w600 : Nat := 18446744069667225600
def w601 : Nat := 18446744069667229455
def w602 : Nat := 18446744069700915473
def w603 : Nat := 18446744070223048752
def w604 : Nat := 18446744070273564672
def w605 : Nat := 18446744070273577779
def w606 : Nat := 18446744070559908932
def w607 : Nat := 18446744070762025040
def w608 : Nat := 18446744070840669440
def w609 : Nat := 18446744070846218240
def w610 : Nat := 18446744070846240085
def w611 : Nat := 18446744071570489472
def w612 : Nat := 18446744071696320512
def w613 : Nat := 18446744071705198592
def w614 : Nat := 18446744071705233544
def w615 : Nat := 18446744072098979840
def w616 : Nat := 18446744072109424640
def w617 : Nat := 18446744072109465760
def w618 : Nat := 18446744072244209832
def w619 : Nat := 18446744072266711040
def w620 : Nat := 18446744072266754560
def w621 : Nat := 18446744072277852160
def w622 : Nat := 18446744072277887112
def w623 : Nat := 18446744072277893280
def w624 : Nat := 18446744072277895850
def w625 : Nat := 18446744072635858944
def w626 : Nat := 18446744072648392704
def w627 : Nat := 18446744072648442048
def w628 : Nat := 18446744072783186120
def w629 : Nat := 18446744072837136384
def w630 : Nat := 18446744072837188608
def w631 : Nat := 18446744072846101640
def w632 : Nat := 18446744072849771712
def w633 : Nat := 18446744072850505728
def w634 : Nat := 18446744072850540680
def w635 : Nat := 18446744072850555072
def w636 : Nat := 18446744072850557952
def w637 : Nat := 18446744072850558156
def w638 : Nat := 18446744073136889309
def w639 : Nat := 18446744073187418336
def w640 : Nat := 18446744073389534444
def w641 : Nat := 18446744073423159296
def w642 : Nat := 18446744073423211724
def w643 : Nat := 18446744073423220462
def w644 : Nat := 18446744073441116160
def w645 : Nat := 18446744073441177600
def w646 : Nat := 18446744073451663520
def w647 : Nat := 18446744073453760704
def w648 : Nat := 18446744073456844800
def w649 : Nat := 18446744073456885920
def w650 : Nat := 18446744073456894144
def w651 : Nat := 18446744073456906240
def w652 : Nat := 18446744073456906480
def w653 : Nat := 18446744073541121525
def w654 : Nat := 18446744073591650552
def w655 : Nat := 18446744073625272320
def w656 : Nat := 18446744073625334000
def w657 : Nat := 18446744073625336570
def w658 : Nat := 18446744073642507264
def w659 : Nat := 18446744073655876812
def w660 : Nat := 18446744073658236144
def w661 : Nat := 18446744073658957824
def w662 : Nat := 18446744073659010252
def w663 : Nat := 18446744073659019504
def w664 : Nat := 18446744073659022588
def w665 : Nat := 18446744073692705008
def w666 : Nat := 18446744073692774400
def w667 : Nat := 18446744073692826624
def w668 : Nat := 18446744073692835840
def w669 : Nat := 18446744073692839680
def w670 : Nat := 18446744073703915520
def w671 : Nat := 18446744073703980970
def w672 : Nat := 18446744073706143744
def w673 : Nat := 18446744073706196172
def w674 : Nat := 18446744073706209228
def w675 : Nat := 18446744073708503040
def w676 : Nat := 18446744073708564720
def w677 : Nat := 18446744073708568560
def w678 : Nat := 18446744073709486080
def w679 : Nat := 18446744073709507925
def w680 : Nat := 18446744073709521032
def w681 : Nat := 18446744073709527200
def w682 : Nat := 18446744073709529770
def w683 : Nat := 18446744073709535424
def w684 : Nat := 18446744073709538304
def w685 : Nat := 18446744073709538508
def w686 : Nat := 18446744073709547520
def w687 : Nat := 18446744073709547760
def w688 : Nat := 18446744073709550844
def w689 : Nat := 18446744073709551360
def w690 : Nat := 18446744073709551615
def inputs : List ℕ := [w155,w191,w273,w382,w472,w588]
def allBits : ℕ := 18446744073709551615
def targetBits : ℕ := 18369900215343709416
def distPairs : List (ℕ × ℕ) := [(1,115265787548762780),(2,96054780007629778),(4,72076304274428710),(8,4521278049358356),(16,17180131846),(32,514),(3,86449340661572469),(5,79245228939774735),(6,78044509293070107),(7,77444201009324305),(9,4936349988785046),(10,4861307124795223),(11,4823785743130935),(12,299088910291463),(13,292045054348191),(14,287320515610451),(15,285009788993845),(17,1775995945887),(18,1448500020051),(19,1336291861301),(20,1116976730886),(21,1226365840159),(22,1173685098259),(23,1198884333845),(24,86168835606),(25,92502329751),(26,91357267543),(27,90784735671),(28,21743342151),(29,21635861439),(30,4384425795),(31,4348641597),(33,26837917),(34,22365010),(35,20128565),(36,16782086),(37,18451231),(38,18171667),(39,18030869),(40,1053206),(41,1149847),(42,1132375),(43,1122615),(44,70151),(45,68511),(46,67411),(47,65845),(48,518),(49,927),(50,851),(51,821),(52,774),(53,799),(54,787),(55,277),(56,22),(57,23),(58,23),(59,23),(60,7),(61,7),(62,3),(63,1)]
def monoPairs : List (ℕ × ℕ) := [(52,targetBits),(56,targetBits),(9,targetBits),(20,targetBits),(24,targetBits),(34,targetBits),(36,targetBits),(40,targetBits),(48,targetBits),(1,targetBits),(2,targetBits),(4,targetBits),(8,targetBits),(16,targetBits),(32,targetBits),(0,targetBits)]
noncomputable def node5 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [2,w191,w319,w448] BT.lf) [2,w191,w348,w561] BT.lf) [2,w191,w348,w568] (BT.nd (BT.nd BT.lf [2,w191,w360,w425] BT.lf) [2,w191,w360,w448] BT.lf)) [2,w191,w361,w425] (BT.nd (BT.nd (BT.nd BT.lf [2,w244,w348,w550] BT.lf) [2,w244,w357,w425] BT.lf) [2,w251,w273,w448] (BT.nd BT.lf [2,w251,w336,w425] BT.lf)))
noncomputable def node16 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [2,w348,w350,w550] BT.lf) [3,w140,w191,w348,w550] BT.lf) [3,w140,w191,w357,w425] (BT.nd (BT.nd BT.lf [3,w151,w191,w273,w448] BT.lf) [3,w151,w191,w336,w425] BT.lf)) [3,w155,w191,w319,w434] (BT.nd (BT.nd (BT.nd BT.lf [3,w155,w191,w323,w561] BT.lf) [3,w155,w191,w344,w561] BT.lf) [3,w155,w191,w347,w550] (BT.nd BT.lf [3,w155,w191,w360,w382] BT.lf)))
noncomputable def node10 : BT := (BT.nd node5 [2,w251,w357,w425] node16)
noncomputable def node27 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,w155,w244,w344,w550] BT.lf) [3,w155,w244,w357,w382] BT.lf) [3,w155,w251,w273,w434] (BT.nd (BT.nd BT.lf [3,w155,w251,w273,w447] BT.lf) [3,w155,w251,w336,w382] BT.lf)) [3,w155,w251,w357,w382] (BT.nd (BT.nd (BT.nd BT.lf [3,w155,w327,w382,w561] BT.lf) [3,w155,w327,w565,w588] BT.lf) [3,w155,w327,w585,w687] (BT.nd BT.lf [3,w155,w343,w437,w678] BT.lf)))
noncomputable def node37 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,w155,w349,w382,w561] BT.lf) [3,w155,w351,w382,w550] BT.lf) [3,w180,w191,w319,w425] (BT.nd BT.lf [3,w180,w251,w273,w425] BT.lf)) [3,w191,w229,w313,w425] (BT.nd (BT.nd (BT.nd BT.lf [3,w191,w233,w273,w425] BT.lf) [3,w191,w233,w273,w448] BT.lf) [3,w191,w234,w319,w382] (BT.nd BT.lf [3,w191,w234,w360,w382] BT.lf)))
noncomputable def node32 : BT := (BT.nd node27 [3,w155,w343,w437,w687] node37)
noncomputable def node21 : BT := (BT.nd node10 [3,w155,w244,w323,w550] node32)
noncomputable def node48 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,w191,w242,w357,w425] BT.lf) [3,w191,w273,w348,w506] BT.lf) [3,w191,w273,w348,w567] (BT.nd (BT.nd BT.lf [3,w191,w297,w382,w561] BT.lf) [3,w191,w297,w565,w588] BT.lf)) [3,w191,w297,w585,w687] (BT.nd (BT.nd (BT.nd BT.lf [3,w191,w313,w348,w472] BT.lf) [3,w191,w319,w425,w472] BT.lf) [3,w191,w319,w425,w506] (BT.nd BT.lf [3,w191,w319,w425,w513] BT.lf)))
noncomputable def node58 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,w191,w319,w425,w561] BT.lf) [3,w191,w319,w425,w574] BT.lf) [3,w191,w319,w425,w577] (BT.nd BT.lf [3,w191,w319,w425,w581] BT.lf)) [3,w191,w320,w425,w472] (BT.nd (BT.nd (BT.nd BT.lf [3,w191,w321,w425,w561] BT.lf) [3,w191,w321,w425,w579] BT.lf) [3,w191,w321,w425,w587] (BT.nd BT.lf [3,w191,w346,w348,w550] BT.lf)))
noncomputable def node53 : BT := (BT.nd node48 [3,w191,w319,w425,w550] node58)
noncomputable def node69 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,w191,w348,w550,w588] BT.lf) [3,w191,w348,w550,w637] BT.lf) [3,w191,w348,w550,w652] (BT.nd (BT.nd BT.lf [3,w191,w348,w550,w658] BT.lf) [3,w191,w348,w550,w664] BT.lf)) [3,w191,w348,w550,w678] (BT.nd (BT.nd (BT.nd BT.lf [3,w191,w348,w550,w687] BT.lf) [3,w191,w348,w565,w588] BT.lf) [3,w223,w327,w550,w588] (BT.nd BT.lf [3,w229,w244,w273,w425] BT.lf)))
noncomputable def node79 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,w234,w251,w273,w382] BT.lf) [3,w236,w313,w425,w472] BT.lf) [3,w238,w343,w382,w678] (BT.nd BT.lf [3,w238,w343,w382,w687] BT.lf)) [3,w244,w273,w348,w472] (BT.nd (BT.nd (BT.nd BT.lf [3,w244,w297,w382,w550] BT.lf) [3,w244,w308,w425,w472] BT.lf) [3,w244,w321,w425,w550] (BT.nd BT.lf [3,w251,w273,w425,w472] BT.lf)))
noncomputable def node74 : BT := (BT.nd node69 [3,w229,w251,w273,w425] node79)
noncomputable def node63 : BT := (BT.nd node53 [3,w191,w348,w353,w472] node74)
noncomputable def node42 : BT := (BT.nd node21 [3,w191,w240,w273,w425] node63)
noncomputable def node90 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,w251,w273,w425,w513] BT.lf) [3,w251,w273,w425,w550] BT.lf) [3,w251,w273,w425,w574] (BT.nd (BT.nd BT.lf [3,w251,w273,w425,w577] BT.lf) [3,w251,w273,w425,w581] BT.lf)) [3,w251,w319,w425,w472] (BT.nd (BT.nd (BT.nd BT.lf [3,w252,w273,w382,w513] BT.lf) [3,w252,w273,w382,w563] BT.lf) [3,w252,w273,w425,w472] (BT.nd BT.lf [3,w252,w273,w425,w550] BT.lf)))
noncomputable def node101 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,w253,w273,w382,w578] BT.lf) [3,w253,w273,w419,w472] BT.lf) [3,w253,w273,w425,w578] (BT.nd (BT.nd BT.lf [3,w253,w357,w425,w637] BT.lf) [3,w273,w348,w350,w472] BT.lf)) [3,w297,w350,w382,w550] (BT.nd (BT.nd (BT.nd BT.lf [3,w327,w348,w550,w588] BT.lf) [4,w44,w155,w191,w313,w382] BT.lf) [4,w53,w155,w191,w313,w382] (BT.nd BT.lf [4,w53,w155,w244,w273,w382] BT.lf)))
noncomputable def node95 : BT := (BT.nd node90 [3,w252,w321,w382,w550] node101)
noncomputable def node112 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w94,w155,w273,w382,w506] BT.lf) [4,w94,w155,w313,w382,w472] BT.lf) [4,w98,w155,w191,w382,w506] (BT.nd (BT.nd BT.lf [4,w98,w155,w244,w382,w472] BT.lf) [4,w100,w155,w191,w273,w506] BT.lf)) [4,w100,w155,w191,w313,w472] (BT.nd (BT.nd (BT.nd BT.lf [4,w100,w155,w244,w273,w472] BT.lf) [4,w101,w155,w191,w273,w506] BT.lf) [4,w101,w155,w191,w313,w472] (BT.nd BT.lf [4,w101,w155,w244,w273,w472] BT.lf)))
noncomputable def node122 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w104,w155,w244,w273,w382] BT.lf) [4,w136,w191,w313,w425,w472] BT.lf) [4,w136,w244,w273,w425,w472] (BT.nd BT.lf [4,w140,w155,w191,w323,w550] BT.lf)) [4,w140,w155,w191,w357,w382] (BT.nd (BT.nd (BT.nd BT.lf [4,w140,w155,w327,w382,w550] BT.lf) [4,w140,w191,w229,w273,w425] BT.lf) [4,w140,w191,w273,w348,w472] (BT.nd BT.lf [4,w140,w191,w297,w382,w550] BT.lf)))
noncomputable def node117 : BT := (BT.nd node112 [4,w104,w155,w191,w313,w382] node122)
noncomputable def node106 : BT := (BT.nd node95 [4,w55,w155,w191,w273,w382] node117)
noncomputable def node133 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w140,w191,w321,w425,w550] BT.lf) [4,w140,w236,w273,w425,w472] BT.lf) [4,w151,w155,w191,w273,w434] (BT.nd (BT.nd BT.lf [4,w151,w155,w191,w336,w382] BT.lf) [4,w151,w180,w191,w273,w425] BT.lf)) [4,w151,w191,w234,w273,w382] (BT.nd (BT.nd (BT.nd BT.lf [4,w151,w191,w273,w425,w472] BT.lf) [4,w151,w191,w273,w425,w506] BT.lf) [4,w151,w191,w273,w425,w513] (BT.nd BT.lf [4,w151,w191,w273,w425,w550] BT.lf)))
noncomputable def node143 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w151,w191,w273,w425,w577] BT.lf) [4,w151,w191,w273,w425,w581] BT.lf) [4,w151,w191,w319,w425,w472] (BT.nd BT.lf [4,w151,w251,w273,w425,w472] BT.lf)) [4,w152,w191,w273,w425,w472] (BT.nd (BT.nd (BT.nd BT.lf [4,w153,w191,w273,w382,w513] BT.lf) [4,w153,w191,w273,w382,w563] BT.lf) [4,w153,w191,w273,w425,w472] (BT.nd BT.lf [4,w153,w191,w273,w425,w550] BT.lf)))
noncomputable def node138 : BT := (BT.nd node133 [4,w151,w191,w273,w425,w574] node143)
noncomputable def node154 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w154,w191,w273,w382,w472] BT.lf) [4,w154,w191,w273,w382,w550] BT.lf) [4,w155,w163,w191,w273,w382] (BT.nd (BT.nd BT.lf [4,w155,w176,w327,w550,w588] BT.lf) [4,w155,w180,w191,w319,w382] BT.lf)) [4,w155,w180,w251,w273,w382] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w184,w343,w382,w678] BT.lf) [4,w155,w184,w343,w382,w687] BT.lf) [4,w155,w191,w229,w313,w382] (BT.nd BT.lf [4,w155,w191,w233,w273,w382] BT.lf)))
noncomputable def node164 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w256,w382,w561] BT.lf) [4,w155,w191,w256,w565,w588] BT.lf) [4,w155,w191,w256,w585,w687] (BT.nd BT.lf [4,w155,w191,w258,w550,w588] BT.lf)) [4,w155,w191,w273,w323,w506] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w273,w347,w472] BT.lf) [4,w155,w191,w273,w382,w477] BT.lf) [4,w155,w191,w273,w382,w478] (BT.nd BT.lf [4,w155,w191,w273,w382,w483] BT.lf)))
noncomputable def node159 : BT := (BT.nd node154 [4,w155,w191,w242,w357,w382] node164)
noncomputable def node148 : BT := (BT.nd node138 [4,w153,w191,w321,w382,w550] node159)
noncomputable def node127 : BT := (BT.nd node106 [4,w140,w191,w308,w425,w472] node148)
noncomputable def node84 : BT := (BT.nd node42 [3,w251,w273,w425,w506] node127)
noncomputable def node175 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w273,w382,w487] BT.lf) [4,w155,w191,w273,w382,w506] BT.lf) [4,w155,w191,w273,w382,w507] (BT.nd (BT.nd BT.lf [4,w155,w191,w273,w382,w508] BT.lf) [4,w155,w191,w273,w382,w509] BT.lf)) [4,w155,w191,w273,w382,w510] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w273,w382,w511] BT.lf) [4,w155,w191,w273,w382,w512] BT.lf) [4,w155,w191,w273,w382,w514] (BT.nd BT.lf [4,w155,w191,w273,w382,w530] BT.lf)))
noncomputable def node186 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w273,w382,w533] BT.lf) [4,w155,w191,w273,w382,w534] BT.lf) [4,w155,w191,w273,w382,w551] (BT.nd (BT.nd BT.lf [4,w155,w191,w273,w382,w552] BT.lf) [4,w155,w191,w273,w382,w555] BT.lf)) [4,w155,w191,w273,w382,w556] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w273,w382,w559] BT.lf) [4,w155,w191,w273,w382,w560] BT.lf) [4,w155,w191,w273,w382,w561] (BT.nd BT.lf [4,w155,w191,w273,w382,w562] BT.lf)))
noncomputable def node180 : BT := (BT.nd node175 [4,w155,w191,w273,w382,w531] node186)
noncomputable def node197 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w273,w382,w577] BT.lf) [4,w155,w191,w273,w382,w578] BT.lf) [4,w155,w191,w273,w382,w579] (BT.nd (BT.nd BT.lf [4,w155,w191,w273,w382,w586] BT.lf) [4,w155,w191,w273,w382,w587] BT.lf)) [4,w155,w191,w273,w391,w600] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w273,w391,w678] BT.lf) [4,w155,w191,w273,w400,w506] BT.lf) [4,w155,w191,w273,w401,w506] (BT.nd BT.lf [4,w155,w191,w273,w403,w506] BT.lf)))
noncomputable def node207 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w273,w410,w506] BT.lf) [4,w155,w191,w273,w411,w506] BT.lf) [4,w155,w191,w273,w415,w472] (BT.nd BT.lf [4,w155,w191,w273,w419,w472] BT.lf)) [4,w155,w191,w273,w420,w506] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w273,w420,w561] BT.lf) [4,w155,w191,w273,w420,w577] BT.lf) [4,w155,w191,w273,w421,w509] (BT.nd BT.lf [4,w155,w191,w273,w422,w511] BT.lf)))
noncomputable def node202 : BT := (BT.nd node197 [4,w155,w191,w273,w404,w506] node207)
noncomputable def node191 : BT := (BT.nd node180 [4,w155,w191,w273,w382,w575] node202)
noncomputable def node218 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w273,w425,w486] BT.lf) [4,w155,w191,w273,w425,w506] BT.lf) [4,w155,w191,w273,w425,w509] (BT.nd (BT.nd BT.lf [4,w155,w191,w273,w425,w511] BT.lf) [4,w155,w191,w273,w425,w559] BT.lf)) [4,w155,w191,w273,w425,w561] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w273,w425,w577] BT.lf) [4,w155,w191,w273,w425,w578] BT.lf) [4,w155,w191,w273,w425,w579] (BT.nd BT.lf [4,w155,w191,w273,w425,w586] BT.lf)))
noncomputable def node228 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w273,w428,w506] BT.lf) [4,w155,w191,w273,w434,w506] BT.lf) [4,w155,w191,w273,w434,w621] (BT.nd BT.lf [4,w155,w191,w273,w434,w678] BT.lf)) [4,w155,w191,w273,w434,w685] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w273,w434,w687] BT.lf) [4,w155,w191,w273,w435,w506] BT.lf) [4,w155,w191,w273,w436,w678] (BT.nd BT.lf [4,w155,w191,w273,w437,w678] BT.lf)))
noncomputable def node223 : BT := (BT.nd node218 [4,w155,w191,w273,w425,w587] node228)
noncomputable def node239 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w273,w447,w641] BT.lf) [4,w155,w191,w273,w447,w678] BT.lf) [4,w155,w191,w273,w448,w678] (BT.nd (BT.nd BT.lf [4,w155,w191,w275,w382,w472] BT.lf) [4,w155,w191,w277,w382,w550] BT.lf)) [4,w155,w191,w279,w382,w678] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w281,w382,w472] BT.lf) [4,w155,w191,w289,w382,w506] BT.lf) [4,w155,w191,w290,w382,w506] (BT.nd BT.lf [4,w155,w191,w291,w382,w561] BT.lf)))
noncomputable def node249 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w300,w382,w506] BT.lf) [4,w155,w191,w307,w382,w506] BT.lf) [4,w155,w191,w308,w382,w506] (BT.nd BT.lf [4,w155,w191,w308,w434,w588] BT.lf)) [4,w155,w191,w313,w323,w472] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w313,w344,w472] BT.lf) [4,w155,w191,w313,w382,w472] BT.lf) [4,w155,w191,w313,w382,w494] (BT.nd BT.lf [4,w155,w191,w313,w382,w495] BT.lf)))
noncomputable def node244 : BT := (BT.nd node239 [4,w155,w191,w296,w382,w550] node249)
noncomputable def node233 : BT := (BT.nd node223 [4,w155,w191,w273,w437,w687] node244)
noncomputable def node212 : BT := (BT.nd node191 [4,w155,w191,w273,w424,w506] node233)
noncomputable def node260 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w313,w382,w498] BT.lf) [4,w155,w191,w313,w382,w500] BT.lf) [4,w155,w191,w313,w382,w506] (BT.nd (BT.nd BT.lf [4,w155,w191,w313,w382,w511] BT.lf) [4,w155,w191,w313,w382,w517] BT.lf)) [4,w155,w191,w313,w382,w518] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w313,w382,w521] BT.lf) [4,w155,w191,w313,w382,w541] BT.lf) [4,w155,w191,w313,w382,w546] (BT.nd BT.lf [4,w155,w191,w313,w382,w550] BT.lf)))
noncomputable def node271 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w313,w382,w559] BT.lf) [4,w155,w191,w313,w382,w561] BT.lf) [4,w155,w191,w313,w382,w571] (BT.nd (BT.nd BT.lf [4,w155,w191,w313,w400,w472] BT.lf) [4,w155,w191,w313,w401,w472] BT.lf)) [4,w155,w191,w313,w403,w472] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w313,w404,w472] BT.lf) [4,w155,w191,w313,w410,w472] BT.lf) [4,w155,w191,w313,w411,w472] (BT.nd BT.lf [4,w155,w191,w313,w420,w472] BT.lf)))
noncomputable def node265 : BT := (BT.nd node260 [4,w155,w191,w313,w382,w554] node271)
noncomputable def node282 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w313,w420,w550] BT.lf) [4,w155,w191,w313,w420,w561] BT.lf) [4,w155,w191,w313,w422,w472] (BT.nd (BT.nd BT.lf [4,w155,w191,w313,w425,w472] BT.lf) [4,w155,w191,w313,w425,w506] BT.lf)) [4,w155,w191,w313,w425,w550] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w313,w425,w561] BT.lf) [4,w155,w191,w313,w428,w472] BT.lf) [4,w155,w191,w313,w429,w472] (BT.nd BT.lf [4,w155,w191,w313,w434,w472] BT.lf)))
noncomputable def node292 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w315,w382,w472] BT.lf) [4,w155,w191,w316,w382,w472] BT.lf) [4,w155,w191,w316,w382,w509] (BT.nd BT.lf [4,w155,w191,w316,w382,w550] BT.lf)) [4,w155,w191,w316,w382,w562] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w316,w421,w472] BT.lf) [4,w155,w191,w316,w425,w472] BT.lf) [4,w155,w191,w317,w382,w472] (BT.nd BT.lf [4,w155,w191,w319,w382,w472] BT.lf)))
noncomputable def node287 : BT := (BT.nd node282 [4,w155,w191,w314,w382,w472] node292)
noncomputable def node276 : BT := (BT.nd node265 [4,w155,w191,w313,w420,w506] node287)
noncomputable def node303 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w319,w382,w513] BT.lf) [4,w155,w191,w319,w382,w550] BT.lf) [4,w155,w191,w319,w382,w561] (BT.nd (BT.nd BT.lf [4,w155,w191,w319,w382,w574] BT.lf) [4,w155,w191,w319,w424,w472] BT.lf)) [4,w155,w191,w319,w425,w472] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w320,w382,w472] BT.lf) [4,w155,w191,w321,w382,w561] BT.lf) [4,w155,w191,w322,w382,w588] (BT.nd BT.lf [4,w155,w191,w323,w550,w588] BT.lf)))
noncomputable def node313 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w323,w550,w652] BT.lf) [4,w155,w191,w323,w550,w658] BT.lf) [4,w155,w191,w323,w550,w664] (BT.nd BT.lf [4,w155,w191,w323,w550,w678] BT.lf)) [4,w155,w191,w323,w550,w687] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w323,w565,w588] BT.lf) [4,w155,w191,w324,w550,w588] BT.lf) [4,w155,w191,w331,w382,w506] (BT.nd BT.lf [4,w155,w191,w336,w382,w506] BT.lf)))
noncomputable def node308 : BT := (BT.nd node303 [4,w155,w191,w323,w550,w637] node313)
noncomputable def node324 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w336,w382,w678] BT.lf) [4,w155,w191,w336,w382,w685] BT.lf) [4,w155,w191,w336,w382,w687] (BT.nd (BT.nd BT.lf [4,w155,w191,w336,w425,w678] BT.lf) [4,w155,w191,w336,w434,w678] BT.lf)) [4,w155,w191,w337,w382,w506] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w338,w382,w678] BT.lf) [4,w155,w191,w339,w382,w678] BT.lf) [4,w155,w191,w343,w382,w561] (BT.nd BT.lf [4,w155,w191,w345,w550,w588] BT.lf)))
noncomputable def node334 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w353,w382,w472] BT.lf) [4,w155,w191,w354,w382,w472] BT.lf) [4,w155,w191,w357,w382,w588] (BT.nd BT.lf [4,w155,w191,w357,w382,w637] BT.lf)) [4,w155,w191,w357,w382,w641] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w357,w382,w652] BT.lf) [4,w155,w191,w357,w382,w665] BT.lf) [4,w155,w191,w357,w382,w678] (BT.nd BT.lf [4,w155,w191,w357,w425,w588] BT.lf)))
noncomputable def node329 : BT := (BT.nd node324 [4,w155,w191,w348,w550,w588] node334)
noncomputable def node318 : BT := (BT.nd node308 [4,w155,w191,w336,w382,w621] node329)
noncomputable def node297 : BT := (BT.nd node276 [4,w155,w191,w319,w382,w506] node318)
noncomputable def node254 : BT := (BT.nd node212 [4,w155,w191,w313,w382,w497] node297)
noncomputable def node169 : BT := (BT.nd node84 [4,w155,w191,w273,w382,w486] node254)
noncomputable def node345 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w191,w358,w382,w472] BT.lf) [4,w155,w191,w359,w382,w472] BT.lf) [4,w155,w191,w364,w382,w550] (BT.nd (BT.nd BT.lf [4,w155,w191,w365,w382,w550] BT.lf) [4,w155,w191,w365,w382,w561] BT.lf)) [4,w155,w193,w273,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w198,w273,w382,w472] BT.lf) [4,w155,w215,w273,w382,w506] BT.lf) [4,w155,w215,w313,w382,w472] (BT.nd BT.lf [4,w155,w216,w273,w382,w506] BT.lf)))
noncomputable def node356 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w225,w273,w382,w506] BT.lf) [4,w155,w225,w313,w382,w472] BT.lf) [4,w155,w229,w244,w273,w382] (BT.nd (BT.nd BT.lf [4,w155,w229,w251,w273,w382] BT.lf) [4,w155,w235,w273,w382,w506] BT.lf)) [4,w155,w235,w313,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w236,w273,w382,w506] BT.lf) [4,w155,w236,w273,w434,w588] BT.lf) [4,w155,w236,w273,w447,w588] (BT.nd BT.lf [4,w155,w236,w313,w382,w472] BT.lf)))
noncomputable def node350 : BT := (BT.nd node345 [4,w155,w216,w313,w382,w472] node356)
noncomputable def node367 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w236,w357,w382,w588] BT.lf) [4,w155,w237,w343,w382,w588] BT.lf) [4,w155,w244,w256,w382,w550] (BT.nd (BT.nd BT.lf [4,w155,w244,w273,w323,w472] BT.lf) [4,w155,w244,w273,w344,w472] BT.lf)) [4,w155,w244,w273,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w244,w273,w382,w494] BT.lf) [4,w155,w244,w273,w382,w495] BT.lf) [4,w155,w244,w273,w382,w497] (BT.nd BT.lf [4,w155,w244,w273,w382,w498] BT.lf)))
noncomputable def node377 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w244,w273,w382,w506] BT.lf) [4,w155,w244,w273,w382,w509] BT.lf) [4,w155,w244,w273,w382,w517] (BT.nd BT.lf [4,w155,w244,w273,w382,w521] BT.lf)) [4,w155,w244,w273,w382,w528] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w244,w273,w382,w532] BT.lf) [4,w155,w244,w273,w382,w541] BT.lf) [4,w155,w244,w273,w382,w546] (BT.nd BT.lf [4,w155,w244,w273,w382,w550] BT.lf)))
noncomputable def node372 : BT := (BT.nd node367 [4,w155,w244,w273,w382,w500] node377)
noncomputable def node361 : BT := (BT.nd node350 [4,w155,w236,w336,w382,w588] node372)
noncomputable def node388 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w244,w273,w382,w571] BT.lf) [4,w155,w244,w273,w400,w472] BT.lf) [4,w155,w244,w273,w401,w472] (BT.nd (BT.nd BT.lf [4,w155,w244,w273,w403,w472] BT.lf) [4,w155,w244,w273,w404,w472] BT.lf)) [4,w155,w244,w273,w410,w472] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w244,w273,w411,w472] BT.lf) [4,w155,w244,w273,w420,w472] BT.lf) [4,w155,w244,w273,w420,w506] (BT.nd BT.lf [4,w155,w244,w273,w420,w550] BT.lf)))
noncomputable def node398 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w244,w273,w425,w472] BT.lf) [4,w155,w244,w273,w425,w506] BT.lf) [4,w155,w244,w273,w425,w550] (BT.nd BT.lf [4,w155,w244,w273,w428,w472] BT.lf)) [4,w155,w244,w273,w434,w472] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w244,w273,w442,w472] BT.lf) [4,w155,w244,w273,w446,w472] BT.lf) [4,w155,w244,w289,w382,w472] (BT.nd BT.lf [4,w155,w244,w290,w382,w472] BT.lf)))
noncomputable def node393 : BT := (BT.nd node388 [4,w155,w244,w273,w421,w472] node398)
noncomputable def node409 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w244,w307,w382,w472] BT.lf) [4,w155,w244,w308,w382,w472] BT.lf) [4,w155,w244,w313,w382,w472] (BT.nd (BT.nd BT.lf [4,w155,w244,w313,w382,w506] BT.lf) [4,w155,w244,w313,w382,w550] BT.lf)) [4,w155,w244,w313,w382,w561] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w244,w313,w420,w472] BT.lf) [4,w155,w244,w313,w425,w472] BT.lf) [4,w155,w244,w316,w382,w472] (BT.nd BT.lf [4,w155,w244,w321,w382,w550] BT.lf)))
noncomputable def node419 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w244,w336,w382,w472] BT.lf) [4,w155,w244,w343,w382,w550] BT.lf) [4,w155,w244,w352,w382,w472] (BT.nd BT.lf [4,w155,w244,w356,w382,w472] BT.lf)) [4,w155,w244,w365,w382,w550] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w246,w273,w382,w472] BT.lf) [4,w155,w247,w273,w382,w472] BT.lf) [4,w155,w248,w273,w382,w472] (BT.nd BT.lf [4,w155,w248,w273,w382,w511] BT.lf)))
noncomputable def node414 : BT := (BT.nd node409 [4,w155,w244,w331,w382,w472] node419)
noncomputable def node403 : BT := (BT.nd node393 [4,w155,w244,w300,w382,w472] node414)
noncomputable def node382 : BT := (BT.nd node361 [4,w155,w244,w273,w382,w561] node403)
noncomputable def node430 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w248,w273,w422,w472] BT.lf) [4,w155,w248,w273,w425,w472] BT.lf) [4,w155,w248,w313,w382,w472] (BT.nd (BT.nd BT.lf [4,w155,w249,w273,w382,w472] BT.lf) [4,w155,w251,w273,w382,w472] BT.lf)) [4,w155,w251,w273,w382,w506] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w251,w273,w382,w513] BT.lf) [4,w155,w251,w273,w382,w550] BT.lf) [4,w155,w251,w273,w382,w574] (BT.nd BT.lf [4,w155,w251,w273,w424,w472] BT.lf)))
noncomputable def node441 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w251,w319,w382,w472] BT.lf) [4,w155,w252,w273,w382,w472] BT.lf) [4,w155,w252,w273,w382,w550] (BT.nd (BT.nd BT.lf [4,w155,w253,w357,w382,w637] BT.lf) [4,w155,w273,w327,w382,w506] BT.lf)) [4,w155,w273,w327,w521,w588] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w273,w327,w564,w588] BT.lf) [4,w155,w273,w327,w574,w678] BT.lf) [4,w155,w273,w350,w382,w472] (BT.nd BT.lf [4,w155,w273,w351,w382,w472] BT.lf)))
noncomputable def node435 : BT := (BT.nd node430 [4,w155,w251,w273,w425,w472] node441)
noncomputable def node452 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w313,w349,w382,w472] BT.lf) [4,w155,w323,w327,w550,w588] BT.lf) [4,w155,w327,w331,w472,w588] (BT.nd (BT.nd BT.lf [4,w155,w327,w382,w550,w588] BT.lf) [4,w155,w327,w382,w550,w637] BT.lf)) [4,w155,w327,w382,w550,w645] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w327,w382,w550,w652] BT.lf) [4,w155,w327,w382,w550,w659] BT.lf) [4,w155,w327,w382,w550,w678] (BT.nd BT.lf [4,w155,w327,w382,w550,w687] BT.lf)))
noncomputable def node462 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w327,w459,w472,w652] BT.lf) [4,w155,w327,w459,w550,w588] BT.lf) [4,w155,w327,w550,w574,w588] (BT.nd BT.lf [4,w155,w327,w550,w585,w588] BT.lf)) [4,w155,w328,w382,w550,w588] (BT.nd (BT.nd (BT.nd BT.lf [4,w155,w328,w425,w550,w588] BT.lf) [4,w155,w328,w459,w472,w588] BT.lf) [4,w155,w328,w463,w472,w588] (BT.nd BT.lf [4,w155,w343,w437,w472,w588] BT.lf)))
noncomputable def node457 : BT := (BT.nd node452 [4,w155,w327,w425,w550,w588] node462)
noncomputable def node446 : BT := (BT.nd node435 [4,w155,w313,w327,w382,w472] node457)
noncomputable def node473 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w176,w191,w297,w550,w588] BT.lf) [4,w191,w212,w273,w382,w506] BT.lf) [4,w191,w212,w273,w382,w530] (BT.nd (BT.nd BT.lf [4,w191,w212,w313,w382,w472] BT.lf) [4,w191,w223,w256,w550,w588] BT.lf)) [4,w191,w223,w273,w382,w506] (BT.nd (BT.nd (BT.nd BT.lf [4,w191,w223,w273,w382,w533] BT.lf) [4,w191,w223,w313,w382,w472] BT.lf) [4,w191,w223,w353,w382,w472] (BT.nd BT.lf [4,w191,w229,w242,w273,w425] BT.lf)))
noncomputable def node483 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w191,w234,w273,w382,w506] BT.lf) [4,w191,w234,w273,w382,w621] BT.lf) [4,w191,w234,w273,w382,w641] (BT.nd BT.lf [4,w191,w234,w273,w382,w678] BT.lf)) [4,w191,w234,w273,w382,w685] (BT.nd (BT.nd (BT.nd BT.lf [4,w191,w234,w273,w382,w687] BT.lf) [4,w191,w234,w273,w425,w678] BT.lf) [4,w191,w234,w273,w434,w678] (BT.nd BT.lf [4,w191,w234,w273,w448,w678] BT.lf)))
noncomputable def node478 : BT := (BT.nd node473 [4,w191,w233,w234,w273,w382] node483)
noncomputable def node494 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w191,w234,w313,w382,w472] BT.lf) [4,w191,w234,w336,w382,w678] BT.lf) [4,w191,w234,w357,w382,w588] (BT.nd (BT.nd BT.lf [4,w191,w234,w358,w382,w472] BT.lf) [4,w191,w238,w273,w382,w678] BT.lf)) [4,w191,w238,w273,w382,w687] (BT.nd (BT.nd (BT.nd BT.lf [4,w191,w241,w273,w382,w678] BT.lf) [4,w191,w250,w273,w425,w472] BT.lf) [4,w191,w251,w273,w425,w472] (BT.nd BT.lf [4,w191,w253,w273,w382,w509] BT.lf)))
noncomputable def node504 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w191,w253,w273,w425,w577] BT.lf) [4,w191,w253,w313,w425,w472] BT.lf) [4,w191,w253,w316,w382,w472] (BT.nd BT.lf [4,w191,w253,w357,w425,w588] BT.lf)) [4,w191,w273,w297,w382,w506] (BT.nd (BT.nd (BT.nd BT.lf [4,w191,w273,w297,w382,w555] BT.lf) [4,w191,w273,w297,w521,w588] BT.lf) [4,w191,w273,w297,w574,w678] (BT.nd BT.lf [4,w191,w273,w318,w425,w472] BT.lf)))
noncomputable def node499 : BT := (BT.nd node494 [4,w191,w253,w273,w425,w506] node504)
noncomputable def node488 : BT := (BT.nd node478 [4,w191,w234,w308,w382,w588] node499)
noncomputable def node467 : BT := (BT.nd node446 [4,w155,w343,w437,w550,w588] node488)
noncomputable def node424 : BT := (BT.nd node382 [4,w155,w248,w273,w382,w550] node467)
noncomputable def node515 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w191,w273,w321,w425,w506] BT.lf) [4,w191,w273,w321,w425,w559] BT.lf) [4,w191,w273,w321,w425,w577] (BT.nd (BT.nd BT.lf [4,w191,w273,w346,w348,w472] BT.lf) [4,w191,w273,w348,w472,w588] BT.lf)) [4,w191,w273,w348,w472,w637] (BT.nd (BT.nd (BT.nd BT.lf [4,w191,w273,w348,w472,w652] BT.lf) [4,w191,w273,w348,w472,w658] BT.lf) [4,w191,w273,w348,w472,w664] (BT.nd BT.lf [4,w191,w273,w348,w472,w678] BT.lf)))
noncomputable def node526 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w191,w273,w348,w564,w588] BT.lf) [4,w191,w294,w297,w382,w550] BT.lf) [4,w191,w297,w313,w382,w472] (BT.nd (BT.nd BT.lf [4,w191,w297,w331,w472,w588] BT.lf) [4,w191,w297,w382,w550,w588] BT.lf)) [4,w191,w297,w382,w550,w637] (BT.nd (BT.nd (BT.nd BT.lf [4,w191,w297,w382,w550,w645] BT.lf) [4,w191,w297,w382,w550,w652] BT.lf) [4,w191,w297,w382,w550,w678] (BT.nd BT.lf [4,w191,w297,w382,w550,w687] BT.lf)))
noncomputable def node520 : BT := (BT.nd node515 [4,w191,w273,w348,w550,w588] node526)
noncomputable def node537 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w191,w297,w459,w472,w652] BT.lf) [4,w191,w297,w459,w550,w588] BT.lf) [4,w191,w297,w550,w574,w588] (BT.nd (BT.nd BT.lf [4,w191,w297,w550,w585,w588] BT.lf) [4,w191,w298,w382,w472,w652] BT.lf)) [4,w191,w298,w382,w550,w588] (BT.nd (BT.nd (BT.nd BT.lf [4,w191,w310,w321,w425,w550] BT.lf) [4,w191,w313,w321,w425,w472] BT.lf) [4,w191,w319,w382,w425,w472] (BT.nd BT.lf [4,w191,w319,w425,w472] BT.lf)))
noncomputable def node547 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w191,w319,w425,w472,w678] BT.lf) [4,w191,w321,w414,w425,w550] BT.lf) [4,w191,w321,w418,w425,w472] (BT.nd BT.lf [4,w191,w321,w425,w461,w472] BT.lf)) [4,w191,w321,w425,w472,w646] (BT.nd (BT.nd (BT.nd BT.lf [4,w191,w321,w425,w472,w652] BT.lf) [4,w191,w321,w425,w472,w664] BT.lf) [4,w191,w321,w425,w472,w687] (BT.nd BT.lf [4,w191,w321,w425,w542,w588] BT.lf)))
noncomputable def node542 : BT := (BT.nd node537 [4,w191,w319,w425,w472,w588] node547)
noncomputable def node531 : BT := (BT.nd node520 [4,w191,w297,w425,w550,w588] node542)
noncomputable def node558 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w191,w321,w425,w550,w637] BT.lf) [4,w191,w321,w425,w550,w652] BT.lf) [4,w191,w321,w425,w550,w678] (BT.nd (BT.nd BT.lf [4,w191,w321,w425,w550,w687] BT.lf) [4,w191,w323,w348,w550,w588] BT.lf)) [4,w191,w331,w348,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [4,w191,w343,w348,w550,w588] BT.lf) [4,w191,w348,w382,w550,w588] BT.lf) [4,w191,w348,w472,w550,w588] (BT.nd BT.lf [4,w191,w348,w550,w588] BT.lf)))
noncomputable def node568 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w212,w244,w273,w382,w472] BT.lf) [4,w223,w244,w273,w382,w472] BT.lf) [4,w223,w273,w327,w472,w588] (BT.nd BT.lf [4,w229,w253,w273,w425,w637] BT.lf)) [4,w234,w236,w273,w382,w588] (BT.nd (BT.nd (BT.nd BT.lf [4,w234,w244,w273,w382,w472] BT.lf) [4,w238,w343,w382,w472,w588] BT.lf) [4,w238,w343,w382,w550,w588] (BT.nd BT.lf [4,w244,w253,w273,w425,w472] BT.lf)))
noncomputable def node563 : BT := (BT.nd node558 [4,w191,w366,w425,w550,w588] node568)
noncomputable def node579 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w244,w273,w321,w425,w472] BT.lf) [4,w251,w273,w382,w425,w472] BT.lf) [4,w251,w273,w425,w472] (BT.nd (BT.nd BT.lf [4,w251,w273,w425,w472,w588] BT.lf) [4,w251,w273,w425,w472,w678] BT.lf)) [4,w253,w273,w382,w417,w472] (BT.nd (BT.nd (BT.nd BT.lf [4,w253,w273,w382,w509,w637] BT.lf) [4,w253,w273,w382,w513,w685] BT.lf) [4,w253,w273,w417,w425,w472] (BT.nd BT.lf [4,w253,w273,w421,w472,w637] BT.lf)))
noncomputable def node589 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w253,w273,w425,w472,w631] BT.lf) [4,w253,w273,w425,w472,w637] BT.lf) [4,w253,w273,w425,w472,w664] (BT.nd BT.lf [4,w253,w273,w425,w472,w685] BT.lf)) [4,w253,w273,w425,w522,w588] (BT.nd (BT.nd (BT.nd BT.lf [4,w253,w273,w425,w550,w637] BT.lf) [4,w253,w316,w382,w472,w637] BT.lf) [4,w253,w321,w382,w472,w664] (BT.nd BT.lf [4,w253,w321,w382,w550,w637] BT.lf)))
noncomputable def node584 : BT := (BT.nd node579 [4,w253,w273,w425,w450,w472] node589)
noncomputable def node573 : BT := (BT.nd node563 [4,w244,w273,w297,w382,w472] node584)
noncomputable def node552 : BT := (BT.nd node531 [4,w191,w321,w425,w550,w588] node573)
noncomputable def node600 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w253,w343,w425,w550,w588] BT.lf) [4,w273,w297,w350,w382,w472] BT.lf) [4,w273,w327,w348,w472,w588] (BT.nd (BT.nd BT.lf [4,w297,w327,w382,w550,w588] BT.lf) [4,w321,w328,w425,w472,w588] BT.lf)) [5,w6,w140,w191,w273,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w11,w155,w191,w273,w382,w506] BT.lf) [5,w11,w155,w191,w313,w382,w472] BT.lf) [5,w11,w155,w244,w273,w382,w472] (BT.nd BT.lf [5,w13,w155,w191,w273,w382,w472] BT.lf)))
noncomputable def node610 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w15,w155,w191,w273,w382,w472] BT.lf) [5,w18,w155,w191,w273,w382] BT.lf) [5,w18,w155,w191,w273,w382,w506] (BT.nd BT.lf [5,w19,w155,w191,w273,w382,w472] BT.lf)) [5,w24,w155,w191,w273,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w24,w155,w191,w273,w382,w550] BT.lf) [5,w24,w155,w191,w273,w425,w472] BT.lf) [5,w25,w155,w191,w273,w382,w472] (BT.nd BT.lf [5,w26,w155,w191,w273,w382,w472] BT.lf)))
noncomputable def node605 : BT := (BT.nd node600 [5,w13,w155,w191,w273,w382,w550] node610)
noncomputable def node621 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w27,w155,w191,w313,w382] BT.lf) [5,w27,w155,w191,w313,w382,w472] BT.lf) [5,w27,w155,w244,w273,w382] (BT.nd (BT.nd BT.lf [5,w27,w155,w244,w273,w382,w472] BT.lf) [5,w35,w155,w191,w273,w382,w678] BT.lf)) [5,w36,w155,w191,w273,w382,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w38,w155,w191,w273,w382,w506] BT.lf) [5,w38,w155,w191,w273,w506] BT.lf) [5,w38,w155,w191,w313,w382,w472] (BT.nd BT.lf [5,w38,w155,w191,w313,w472] BT.lf)))
noncomputable def node631 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w38,w155,w244,w273,w472] BT.lf) [5,w40,w155,w191,w273,w382,w472] BT.lf) [5,w42,w155,w191,w273,w382,w472] (BT.nd BT.lf [5,w46,w155,w191,w313,w382,w472] BT.lf)) [5,w46,w155,w191,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w47,w155,w191,w273,w382,w472] BT.lf) [5,w48,w191,w273,w425,w472,w588] BT.lf) [5,w49,w191,w273,w382,w472,w588] (BT.nd BT.lf [5,w51,w155,w273,w382,w472,w588] BT.lf)))
noncomputable def node626 : BT := (BT.nd node621 [5,w38,w155,w244,w273,w382,w472] node631)
noncomputable def node615 : BT := (BT.nd node605 [5,w27,w155,w191,w273,w382,w506] node626)
noncomputable def node642 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w53,w140,w155,w191,w273,w382] BT.lf) [5,w53,w155,w191,w273,w382,w588] BT.lf) [5,w53,w155,w191,w273,w382,w600] (BT.nd (BT.nd BT.lf [5,w53,w155,w191,w273,w382,w637] BT.lf) [5,w53,w155,w191,w273,w382,w652] BT.lf)) [5,w53,w155,w191,w273,w382,w678] (BT.nd (BT.nd (BT.nd BT.lf [5,w53,w155,w191,w273,w391,w588] BT.lf) [5,w53,w155,w191,w273,w425,w588] BT.lf) [5,w54,w155,w191,w273,w382,w588] (BT.nd BT.lf [5,w56,w155,w191,w273,w382,w472] BT.lf)))
noncomputable def node652 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w56,w155,w191,w273,w425,w472] BT.lf) [5,w57,w155,w191,w273,w382,w472] BT.lf) [5,w58,w155,w191,w273,w382,w472] (BT.nd BT.lf [5,w59,w155,w191,w273,w382,w506] BT.lf)) [5,w59,w155,w191,w313,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w59,w155,w191,w382,w506] BT.lf) [5,w59,w155,w244,w273,w382,w472] BT.lf) [5,w59,w155,w244,w382,w472] (BT.nd BT.lf [5,w61,w155,w191,w273,w382,w472] BT.lf)))
noncomputable def node647 : BT := (BT.nd node642 [5,w56,w155,w191,w273,w382,w550] node652)
noncomputable def node663 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w64,w155,w191,w273,w382,w472] BT.lf) [5,w67,w155,w244,w273,w382,w472] BT.lf) [5,w67,w155,w273,w382,w472] (BT.nd (BT.nd BT.lf [5,w68,w155,w191,w273,w382,w472] BT.lf) [5,w69,w191,w273,w425,w472,w588] BT.lf)) [5,w70,w191,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w71,w191,w273,w382,w472,w588] BT.lf) [5,w72,w191,w273,w382,w472,w588] BT.lf) [5,w73,w155,w191,w382,w550,w588] (BT.nd BT.lf [5,w74,w155,w191,w382,w472,w588] BT.lf)))
noncomputable def node673 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w77,w155,w191,w273,w472,w588] BT.lf) [5,w79,w155,w191,w273,w382,w472] BT.lf) [5,w79,w155,w191,w273,w382,w486] (BT.nd BT.lf [5,w79,w155,w191,w273,w382,w550] BT.lf)) [5,w79,w155,w191,w273,w425,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w80,w155,w191,w273,w382,w472] BT.lf) [5,w81,w155,w191,w273,w382,w472] BT.lf) [5,w82,w155,w191,w273,w382,w486] (BT.nd BT.lf [5,w82,w155,w191,w273,w382,w506] BT.lf)))
noncomputable def node668 : BT := (BT.nd node663 [5,w75,w155,w191,w382,w472,w588] node673)
noncomputable def node657 : BT := (BT.nd node647 [5,w63,w155,w191,w273,w382,w588] node668)
noncomputable def node636 : BT := (BT.nd node615 [5,w53,w56,w155,w191,w273,w382] node657)
noncomputable def node594 : BT := (BT.nd node552 [4,w253,w332,w425,w472,w588] node636)
noncomputable def node509 : BT := (BT.nd node424 [4,w191,w273,w319,w425,w472] node594)
noncomputable def node339 : BT := (BT.nd node169 [4,w155,w191,w357,w447,w588] node509)
noncomputable def node684 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w82,w155,w244,w273,w382,w472] BT.lf) [5,w82,w155,w273,w382,w486] BT.lf) [5,w82,w155,w273,w382,w506] (BT.nd (BT.nd BT.lf [5,w82,w155,w313,w382,w472] BT.lf) [5,w84,w155,w191,w273,w382,w472] BT.lf)) [5,w86,w155,w191,w273,w382,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w87,w155,w191,w273,w382,w472] BT.lf) [5,w89,w155,w191,w273,w472,w588] BT.lf) [5,w90,w155,w191,w273,w382,w588] (BT.nd BT.lf [5,w91,w155,w191,w273,w382,w472] BT.lf)))
noncomputable def node695 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w94,w140,w155,w273,w382,w472] BT.lf) [5,w94,w155,w273,w382,w472,w588] BT.lf) [5,w95,w155,w273,w382,w472,w588] (BT.nd (BT.nd BT.lf [5,w96,w155,w273,w382,w472,w588] BT.lf) [5,w97,w155,w191,w382,w472,w652] BT.lf)) [5,w97,w155,w191,w382,w550,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w98,w140,w155,w191,w382,w472] BT.lf) [5,w98,w155,w191,w382,w472,w588] BT.lf) [5,w99,w155,w191,w382,w472,w588] (BT.nd BT.lf [5,w100,w140,w155,w191,w273,w472] BT.lf)))
noncomputable def node689 : BT := (BT.nd node684 [5,w93,w155,w273,w382,w472,w637] node695)
noncomputable def node706 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w100,w155,w191,w273,w472,w608] BT.lf) [5,w100,w155,w191,w273,w472,w610] BT.lf) [5,w100,w155,w191,w273,w472,w637] (BT.nd (BT.nd BT.lf [5,w100,w155,w191,w273,w472,w652] BT.lf) [5,w100,w155,w191,w273,w472,w678] BT.lf)) [5,w100,w155,w191,w273,w490,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w100,w155,w191,w273,w550,w588] BT.lf) [5,w101,w140,w155,w191,w273,w472] BT.lf) [5,w101,w155,w191,w273,w472,w588] (BT.nd BT.lf [5,w102,w155,w191,w273,w472,w588] BT.lf)))
noncomputable def node716 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w104,w140,w155,w191,w273,w382] BT.lf) [5,w104,w155,w191,w273,w382,w588] BT.lf) [5,w106,w155,w191,w273,w382,w506] (BT.nd BT.lf [5,w106,w155,w191,w313,w382,w472] BT.lf)) [5,w106,w155,w244,w273,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w106,w191,w273,w382,w506] BT.lf) [5,w106,w191,w313,w382,w472] BT.lf) [5,w106,w244,w273,w382,w472] (BT.nd BT.lf [5,w107,w155,w191,w273,w382,w506] BT.lf)))
noncomputable def node711 : BT := (BT.nd node706 [5,w103,w155,w191,w273,w382,w678] node716)
noncomputable def node700 : BT := (BT.nd node689 [5,w100,w155,w191,w273,w472,w588] node711)
noncomputable def node727 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w107,w155,w244,w273,w382,w472] BT.lf) [5,w108,w155,w191,w273,w382,w472] BT.lf) [5,w111,w155,w191,w273,w472,w588] (BT.nd (BT.nd BT.lf [5,w112,w155,w191,w273,w382,w588] BT.lf) [5,w113,w155,w191,w273,w382,w472] BT.lf)) [5,w115,w155,w191,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w116,w155,w191,w273,w472,w588] BT.lf) [5,w117,w155,w191,w273,w382,w588] BT.lf) [5,w118,w155,w191,w273,w382,w472] (BT.nd BT.lf [5,w123,w155,w191,w273,w382,w506] BT.lf)))
noncomputable def node737 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w123,w155,w244,w273,w382,w472] BT.lf) [5,w124,w155,w191,w273,w382,w506] BT.lf) [5,w124,w155,w191,w313,w382,w472] (BT.nd BT.lf [5,w124,w155,w244,w273,w382,w472] BT.lf)) [5,w127,w155,w191,w273,w382,w506] (BT.nd (BT.nd (BT.nd BT.lf [5,w127,w155,w191,w313,w382,w472] BT.lf) [5,w127,w155,w244,w273,w382,w472] BT.lf) [5,w128,w155,w191,w273,w382,w506] (BT.nd BT.lf [5,w128,w155,w191,w313,w382,w472] BT.lf)))
noncomputable def node732 : BT := (BT.nd node727 [5,w123,w155,w191,w313,w382,w472] node737)
noncomputable def node748 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w131,w155,w191,w273,w382,w506] BT.lf) [5,w131,w155,w191,w313,w382,w472] BT.lf) [5,w131,w155,w244,w273,w382,w472] (BT.nd (BT.nd BT.lf [5,w132,w155,w191,w273,w382,w506] BT.lf) [5,w132,w155,w191,w313,w382,w472] BT.lf)) [5,w132,w155,w244,w273,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w135,w155,w191,w273,w382,w506] BT.lf) [5,w135,w155,w191,w313,w382,w472] BT.lf) [5,w135,w155,w244,w273,w382,w472] (BT.nd BT.lf [5,w136,w140,w191,w273,w425,w472] BT.lf)))
noncomputable def node758 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w136,w155,w191,w273,w434,w588] BT.lf) [5,w136,w155,w191,w313,w382,w472] BT.lf) [5,w136,w155,w191,w336,w382,w588] (BT.nd BT.lf [5,w136,w155,w244,w273,w382,w472] BT.lf)) [5,w136,w191,w234,w273,w382,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w140,w155,w191,w229,w273,w382] BT.lf) [5,w140,w155,w191,w256,w382,w550] BT.lf) [5,w140,w155,w191,w273,w323,w472] (BT.nd BT.lf [5,w140,w155,w191,w273,w382,w472] BT.lf)))
noncomputable def node753 : BT := (BT.nd node748 [5,w136,w155,w191,w273,w382,w506] node758)
noncomputable def node742 : BT := (BT.nd node732 [5,w128,w155,w244,w273,w382,w472] node753)
noncomputable def node721 : BT := (BT.nd node700 [5,w107,w155,w191,w313,w382,w472] node742)
noncomputable def node769 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w140,w155,w191,w273,w382,w495] BT.lf) [5,w140,w155,w191,w273,w382,w497] BT.lf) [5,w140,w155,w191,w273,w382,w498] (BT.nd (BT.nd BT.lf [5,w140,w155,w191,w273,w382,w500] BT.lf) [5,w140,w155,w191,w273,w382,w506] BT.lf)) [5,w140,w155,w191,w273,w382,w517] (BT.nd (BT.nd (BT.nd BT.lf [5,w140,w155,w191,w273,w382,w521] BT.lf) [5,w140,w155,w191,w273,w382,w541] BT.lf) [5,w140,w155,w191,w273,w382,w546] (BT.nd BT.lf [5,w140,w155,w191,w273,w382,w550] BT.lf)))
noncomputable def node780 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w140,w155,w191,w273,w382,w571] BT.lf) [5,w140,w155,w191,w273,w400,w472] BT.lf) [5,w140,w155,w191,w273,w401,w472] (BT.nd (BT.nd BT.lf [5,w140,w155,w191,w273,w403,w472] BT.lf) [5,w140,w155,w191,w273,w404,w472] BT.lf)) [5,w140,w155,w191,w273,w410,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w140,w155,w191,w273,w411,w472] BT.lf) [5,w140,w155,w191,w273,w420,w472] BT.lf) [5,w140,w155,w191,w273,w420,w506] (BT.nd BT.lf [5,w140,w155,w191,w273,w420,w550] BT.lf)))
noncomputable def node774 : BT := (BT.nd node769 [5,w140,w155,w191,w273,w382,w561] node780)
noncomputable def node791 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w140,w155,w191,w273,w425,w506] BT.lf) [5,w140,w155,w191,w273,w425,w550] BT.lf) [5,w140,w155,w191,w273,w428,w472] (BT.nd (BT.nd BT.lf [5,w140,w155,w191,w273,w434,w472] BT.lf) [5,w140,w155,w191,w289,w382,w472] BT.lf)) [5,w140,w155,w191,w290,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w140,w155,w191,w300,w382,w472] BT.lf) [5,w140,w155,w191,w307,w382,w472] BT.lf) [5,w140,w155,w191,w308,w382,w472] (BT.nd BT.lf [5,w140,w155,w191,w313,w382,w472] BT.lf)))
noncomputable def node801 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w140,w155,w191,w313,w382,w550] BT.lf) [5,w140,w155,w191,w313,w382,w561] BT.lf) [5,w140,w155,w191,w313,w420,w472] (BT.nd BT.lf [5,w140,w155,w191,w313,w425,w472] BT.lf)) [5,w140,w155,w191,w321,w382,w550] (BT.nd (BT.nd (BT.nd BT.lf [5,w140,w155,w191,w331,w382,w472] BT.lf) [5,w140,w155,w191,w336,w382,w472] BT.lf) [5,w140,w155,w191,w343,w382,w550] (BT.nd BT.lf [5,w140,w155,w215,w273,w382,w472] BT.lf)))
noncomputable def node796 : BT := (BT.nd node791 [5,w140,w155,w191,w313,w382,w506] node801)
noncomputable def node785 : BT := (BT.nd node774 [5,w140,w155,w191,w273,w425,w472] node796)
noncomputable def node812 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w140,w155,w225,w273,w382,w472] BT.lf) [5,w140,w155,w235,w273,w382,w472] BT.lf) [5,w140,w155,w236,w273,w382,w472] (BT.nd (BT.nd BT.lf [5,w140,w155,w244,w273,w382,w472] BT.lf) [5,w140,w155,w244,w273,w382,w506] BT.lf)) [5,w140,w155,w244,w273,w382,w550] (BT.nd (BT.nd (BT.nd BT.lf [5,w140,w155,w244,w273,w420,w472] BT.lf) [5,w140,w155,w244,w273,w425,w472] BT.lf) [5,w140,w155,w244,w313,w382,w472] (BT.nd BT.lf [5,w140,w155,w273,w327,w382,w472] BT.lf)))
noncomputable def node822 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w140,w191,w223,w273,w382,w472] BT.lf) [5,w140,w191,w234,w273,w382,w472] BT.lf) [5,w140,w191,w253,w273,w425,w472] (BT.nd BT.lf [5,w140,w191,w273,w297,w382,w472] BT.lf)) [5,w140,w191,w273,w321,w425,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w141,w155,w191,w273,w382,w472] BT.lf) [5,w142,w155,w191,w273,w382,w472] BT.lf) [5,w143,w155,w191,w273,w382,w472] (BT.nd BT.lf [5,w144,w155,w191,w273,w382,w472] BT.lf)))
noncomputable def node817 : BT := (BT.nd node812 [5,w140,w191,w212,w273,w382,w472] node822)
noncomputable def node833 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w144,w155,w191,w273,w382,w550] BT.lf) [5,w144,w155,w191,w273,w421,w472] BT.lf) [5,w144,w155,w191,w273,w425,w472] (BT.nd (BT.nd BT.lf [5,w144,w155,w191,w316,w382,w472] BT.lf) [5,w144,w155,w244,w273,w382,w472] BT.lf)) [5,w144,w191,w253,w273,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w144,w253,w273,w382,w472,w637] BT.lf) [5,w145,w155,w191,w273,w382,w472] BT.lf) [5,w146,w155,w191,w273,w382,w472] (BT.nd BT.lf [5,w147,w155,w191,w273,w382,w472] BT.lf)))
noncomputable def node843 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w147,w155,w191,w273,w382,w550] BT.lf) [5,w147,w155,w191,w273,w422,w472] BT.lf) [5,w147,w155,w191,w273,w425,w472] (BT.nd BT.lf [5,w147,w155,w191,w313,w382,w472] BT.lf)) [5,w147,w155,w248,w273,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w148,w155,w191,w273,w382,w472] BT.lf) [5,w149,w155,w191,w273,w382,w472] BT.lf) [5,w151,w155,w180,w191,w273,w382] (BT.nd BT.lf [5,w151,w155,w191,w273,w382,w472] BT.lf)))
noncomputable def node838 : BT := (BT.nd node833 [5,w147,w155,w191,w273,w382,w511] node843)
noncomputable def node827 : BT := (BT.nd node817 [5,w144,w155,w191,w273,w382,w509] node838)
noncomputable def node806 : BT := (BT.nd node785 [5,w140,w155,w216,w273,w382,w472] node827)
noncomputable def node763 : BT := (BT.nd node721 [5,w140,w155,w191,w273,w382,w494] node806)
noncomputable def node854 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w151,w155,w191,w273,w382,w513] BT.lf) [5,w151,w155,w191,w273,w382,w550] BT.lf) [5,w151,w155,w191,w273,w382,w574] (BT.nd (BT.nd BT.lf [5,w151,w155,w191,w273,w424,w472] BT.lf) [5,w151,w155,w191,w273,w425,w472] BT.lf)) [5,w151,w155,w191,w319,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w151,w155,w251,w273,w382,w472] BT.lf) [5,w151,w191,w273,w382,w425,w472] BT.lf) [5,w151,w191,w273,w425,w472] (BT.nd BT.lf [5,w151,w191,w273,w425,w472,w588] BT.lf)))
noncomputable def node865 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w152,w155,w191,w273,w382,w472] BT.lf) [5,w153,w155,w191,w273,w382,w472] BT.lf) [5,w153,w155,w191,w273,w382,w550] (BT.nd (BT.nd BT.lf [5,w155,w155,w191,w273,w382,w506] BT.lf) [5,w155,w155,w191,w313,w382,w472] BT.lf)) [5,w155,w155,w244,w273,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w157,w191,w273,w382,w472] BT.lf) [5,w155,w159,w191,w273,w382,w588] BT.lf) [5,w155,w160,w191,w273,w382,w472] (BT.nd BT.lf [5,w155,w162,w191,w273,w382,w588] BT.lf)))
noncomputable def node859 : BT := (BT.nd node854 [5,w151,w191,w273,w425,w472,w678] node865)
noncomputable def node876 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w166,w191,w273,w382,w472] BT.lf) [5,w155,w171,w191,w273,w382,w506] BT.lf) [5,w155,w171,w191,w313,w382,w472] (BT.nd (BT.nd BT.lf [5,w155,w171,w244,w273,w382,w472] BT.lf) [5,w155,w172,w191,w313,w382,w472] BT.lf)) [5,w155,w176,w191,w256,w550,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w176,w191,w273,w382,w506] BT.lf) [5,w155,w176,w191,w313,w382,w472] BT.lf) [5,w155,w176,w244,w273,w382,w472] (BT.nd BT.lf [5,w155,w176,w273,w327,w472,w588] BT.lf)))
noncomputable def node886 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w180,w191,w273,w382,w621] BT.lf) [5,w155,w180,w191,w273,w382,w678] BT.lf) [5,w155,w180,w191,w273,w382,w685] (BT.nd BT.lf [5,w155,w180,w191,w273,w382,w687] BT.lf)) [5,w155,w180,w191,w273,w425,w678] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w180,w191,w273,w434,w678] BT.lf) [5,w155,w180,w191,w308,w382,w588] BT.lf) [5,w155,w180,w191,w313,w382,w472] (BT.nd BT.lf [5,w155,w180,w191,w336,w382,w678] BT.lf)))
noncomputable def node881 : BT := (BT.nd node876 [5,w155,w180,w191,w273,w382,w506] node886)
noncomputable def node870 : BT := (BT.nd node859 [5,w155,w164,w191,w273,w382,w472] node881)
noncomputable def node897 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w180,w244,w273,w382,w472] BT.lf) [5,w155,w181,w191,w273,w382,w588] BT.lf) [5,w155,w182,w191,w273,w382,w506] (BT.nd (BT.nd BT.lf [5,w155,w183,w191,w273,w382,w678] BT.lf) [5,w155,w184,w191,w273,w382,w678] BT.lf)) [5,w155,w184,w191,w273,w382,w687] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w184,w343,w382,w472,w588] BT.lf) [5,w155,w184,w343,w382,w550,w588] BT.lf) [5,w155,w185,w191,w273,w382,w678] (BT.nd BT.lf [5,w155,w186,w191,w273,w382,w506] BT.lf)))
noncomputable def node907 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w186,w244,w273,w382,w472] BT.lf) [5,w155,w191,w191,w273,w382,w506] BT.lf) [5,w155,w191,w191,w313,w382,w472] (BT.nd BT.lf [5,w155,w191,w194,w273,w382,w472] BT.lf)) [5,w155,w191,w195,w273,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w199,w273,w382,w588] BT.lf) [5,w155,w191,w200,w273,w382,w472] BT.lf) [5,w155,w191,w201,w273,w382,w472] (BT.nd BT.lf [5,w155,w191,w203,w273,w472,w588] BT.lf)))
noncomputable def node902 : BT := (BT.nd node897 [5,w155,w186,w191,w313,w382,w472] node907)
noncomputable def node918 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w211,w273,w382,w472] BT.lf) [5,w155,w191,w220,w273,w382,w472] BT.lf) [5,w155,w191,w222,w273,w382,w472] (BT.nd (BT.nd BT.lf [5,w155,w191,w229,w242,w273,w382] BT.lf) [5,w155,w191,w229,w273,w382,w588] BT.lf)) [5,w155,w191,w229,w273,w382,w637] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w229,w273,w382,w641] BT.lf) [5,w155,w191,w229,w273,w382,w652] BT.lf) [5,w155,w191,w229,w273,w382,w678] (BT.nd BT.lf [5,w155,w191,w229,w273,w425,w588] BT.lf)))
noncomputable def node928 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w229,w357,w382,w588] BT.lf) [5,w155,w191,w230,w273,w382,w472] BT.lf) [5,w155,w191,w232,w273,w382,w472] (BT.nd BT.lf [5,w155,w191,w234,w273,w382,w678] BT.lf)) [5,w155,w191,w237,w273,w382,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w242,w273,w382,w472] BT.lf) [5,w155,w191,w242,w273,w382,w550] BT.lf) [5,w155,w191,w242,w273,w425,w472] (BT.nd BT.lf [5,w155,w191,w244,w273,w382,w472] BT.lf)))
noncomputable def node923 : BT := (BT.nd node918 [5,w155,w191,w229,w273,w447,w588] node928)
noncomputable def node912 : BT := (BT.nd node902 [5,w155,w191,w209,w273,w382,w472] node923)
noncomputable def node891 : BT := (BT.nd node870 [5,w155,w180,w236,w273,w382,w588] node912)
noncomputable def node939 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w244,w273,w382,w550] BT.lf) [5,w155,w191,w244,w273,w420,w472] BT.lf) [5,w155,w191,w244,w273,w425,w472] (BT.nd (BT.nd BT.lf [5,w155,w191,w244,w313,w382,w472] BT.lf) [5,w155,w191,w245,w273,w382,w472] BT.lf)) [5,w155,w191,w248,w273,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w250,w273,w382,w472] BT.lf) [5,w155,w191,w251,w273,w382,w472] BT.lf) [5,w155,w191,w253,w273,w382,w506] (BT.nd BT.lf [5,w155,w191,w253,w313,w382,w472] BT.lf)))
noncomputable def node949 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w256,w273,w382,w506] BT.lf) [5,w155,w191,w256,w273,w521,w588] BT.lf) [5,w155,w191,w256,w273,w574,w678] (BT.nd BT.lf [5,w155,w191,w256,w313,w382,w472] BT.lf)) [5,w155,w191,w256,w331,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w256,w382,w550,w588] BT.lf) [5,w155,w191,w256,w382,w550,w637] BT.lf) [5,w155,w191,w256,w382,w550,w645] (BT.nd BT.lf [5,w155,w191,w256,w382,w550,w652] BT.lf)))
noncomputable def node944 : BT := (BT.nd node939 [5,w155,w191,w253,w357,w382,w588] node949)
noncomputable def node960 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w256,w382,w550,w687] BT.lf) [5,w155,w191,w256,w425,w550,w588] BT.lf) [5,w155,w191,w256,w459,w472,w652] (BT.nd (BT.nd BT.lf [5,w155,w191,w256,w459,w550,w588] BT.lf) [5,w155,w191,w256,w550,w574,w588] BT.lf)) [5,w155,w191,w256,w550,w585,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w257,w382,w472,w588] BT.lf) [5,w155,w191,w258,w273,w472,w588] BT.lf) [5,w155,w191,w259,w382,w550,w588] (BT.nd BT.lf [5,w155,w191,w259,w425,w550,w588] BT.lf)))
noncomputable def node970 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w259,w463,w472,w588] BT.lf) [5,w155,w191,w260,w382,w472,w652] BT.lf) [5,w155,w191,w260,w382,w550,w588] (BT.nd BT.lf [5,w155,w191,w261,w382,w472,w588] BT.lf)) [5,w155,w191,w261,w425,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w263,w273,w382,w506] BT.lf) [5,w155,w191,w263,w313,w382,w472] BT.lf) [5,w155,w191,w264,w273,w382,w506] (BT.nd BT.lf [5,w155,w191,w267,w382,w550,w588] BT.lf)))
noncomputable def node965 : BT := (BT.nd node960 [5,w155,w191,w259,w459,w472,w588] node970)
noncomputable def node954 : BT := (BT.nd node944 [5,w155,w191,w256,w382,w550,w678] node965)
noncomputable def node981 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w268,w313,w382,w472] BT.lf) [5,w155,w191,w271,w382,w550,w588] BT.lf) [5,w155,w191,w273,w273,w382,w506] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w276,w382,w472] BT.lf) [5,w155,w191,w273,w277,w382,w472] BT.lf)) [5,w155,w191,w273,w282,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w283,w382,w472] BT.lf) [5,w155,w191,w273,w285,w472,w588] BT.lf) [5,w155,w191,w273,w294,w382,w472] (BT.nd BT.lf [5,w155,w191,w273,w296,w382,w472] BT.lf)))
noncomputable def node991 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w305,w382,w472] BT.lf) [5,w155,w191,w273,w310,w382,w472] BT.lf) [5,w155,w191,w273,w310,w382,w550] (BT.nd BT.lf [5,w155,w191,w273,w310,w382,w559] BT.lf)) [5,w155,w191,w273,w310,w425,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w312,w382,w472] BT.lf) [5,w155,w191,w273,w313,w382,w472] BT.lf) [5,w155,w191,w273,w313,w382,w506] (BT.nd BT.lf [5,w155,w191,w273,w313,w382,w550] BT.lf)))
noncomputable def node986 : BT := (BT.nd node981 [5,w155,w191,w273,w304,w382,w472] node991)
noncomputable def node1002 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w313,w420,w472] BT.lf) [5,w155,w191,w273,w313,w425,w472] BT.lf) [5,w155,w191,w273,w316,w382,w472] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w318,w382,w472] BT.lf) [5,w155,w191,w273,w319,w382,w472] BT.lf)) [5,w155,w191,w273,w321,w382,w506] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w321,w382,w559] BT.lf) [5,w155,w191,w273,w323,w472,w588] BT.lf) [5,w155,w191,w273,w323,w472,w637] (BT.nd BT.lf [5,w155,w191,w273,w323,w472,w652] BT.lf)))
noncomputable def node1012 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w323,w472,w664] BT.lf) [5,w155,w191,w273,w323,w472,w678] BT.lf) [5,w155,w191,w273,w323,w550,w588] (BT.nd BT.lf [5,w155,w191,w273,w323,w564,w588] BT.lf)) [5,w155,w191,w273,w324,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w333,w382,w678] BT.lf) [5,w155,w191,w273,w336,w382,w678] BT.lf) [5,w155,w191,w273,w343,w382,w506] (BT.nd BT.lf [5,w155,w191,w273,w345,w472,w588] BT.lf)))
noncomputable def node1007 : BT := (BT.nd node1002 [5,w155,w191,w273,w323,w472,w658] node1012)
noncomputable def node996 : BT := (BT.nd node986 [5,w155,w191,w273,w313,w382,w561] node1007)
noncomputable def node975 : BT := (BT.nd node954 [5,w155,w191,w268,w273,w382,w506] node996)
noncomputable def node933 : BT := (BT.nd node891 [5,w155,w191,w244,w273,w382,w506] node975)
noncomputable def node848 : BT := (BT.nd node763 [5,w151,w155,w191,w273,w382,w506] node933)
noncomputable def node1023 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w355,w382,w588] BT.lf) [5,w155,w191,w273,w357,w382,w588] BT.lf) [5,w155,w191,w273,w362,w382,w472] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w363,w382,w472] BT.lf) [5,w155,w191,w273,w364,w382,w472] BT.lf)) [5,w155,w191,w273,w365,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w368,w382,w506] BT.lf) [5,w155,w191,w273,w369,w472,w588] BT.lf) [5,w155,w191,w273,w370,w382,w506] (BT.nd BT.lf [5,w155,w191,w273,w374,w472,w588] BT.lf)))
noncomputable def node1034 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w375,w382,w506] BT.lf) [5,w155,w191,w273,w376,w472,w588] BT.lf) [5,w155,w191,w273,w376,w472,w610] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w380,w472,w588] BT.lf) [5,w155,w191,w273,w380,w472,w637] BT.lf)) [5,w155,w191,w273,w380,w472,w652] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w380,w472,w664] BT.lf) [5,w155,w191,w273,w382,w382,w506] BT.lf) [5,w155,w191,w273,w382,w386,w472] (BT.nd BT.lf [5,w155,w191,w273,w382,w390,w588] BT.lf)))
noncomputable def node1028 : BT := (BT.nd node1023 [5,w155,w191,w273,w374,w550,w588] node1034)
noncomputable def node1045 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w395,w472] BT.lf) [5,w155,w191,w273,w382,w407,w472] BT.lf) [5,w155,w191,w273,w382,w408,w472] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w414,w472] BT.lf) [5,w155,w191,w273,w382,w414,w550] BT.lf)) [5,w155,w191,w273,w382,w414,w577] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w417,w472] BT.lf) [5,w155,w191,w273,w382,w418,w472] BT.lf) [5,w155,w191,w273,w382,w420,w506] (BT.nd BT.lf [5,w155,w191,w273,w382,w423,w472] BT.lf)))
noncomputable def node1055 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w425,w577] BT.lf) [5,w155,w191,w273,w382,w431,w678] BT.lf) [5,w155,w191,w273,w382,w434,w678] (BT.nd BT.lf [5,w155,w191,w273,w382,w441,w506] BT.lf)) [5,w155,w191,w273,w382,w445,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w449,w472] BT.lf) [5,w155,w191,w273,w382,w450,w472] BT.lf) [5,w155,w191,w273,w382,w459,w506] (BT.nd BT.lf [5,w155,w191,w273,w382,w460,w472] BT.lf)))
noncomputable def node1050 : BT := (BT.nd node1045 [5,w155,w191,w273,w382,w425,w506] node1055)
noncomputable def node1039 : BT := (BT.nd node1028 [5,w155,w191,w273,w382,w392,w472] node1050)
noncomputable def node1066 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w465,w506] BT.lf) [5,w155,w191,w273,w382,w466,w588] BT.lf) [5,w155,w191,w273,w382,w468,w678] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w468,w685] BT.lf) [5,w155,w191,w273,w382,w469,w588] BT.lf)) [5,w155,w191,w273,w382,w469,w637] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w479] BT.lf) [5,w155,w191,w273,w382,w472,w480] BT.lf) [5,w155,w191,w273,w382,w472,w485] (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w486] BT.lf)))
noncomputable def node1076 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w504] BT.lf) [5,w155,w191,w273,w382,w472,w505] BT.lf) [5,w155,w191,w273,w382,w472,w506] (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w509] BT.lf)) [5,w155,w191,w273,w382,w472,w511] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w535] BT.lf) [5,w155,w191,w273,w382,w472,w536] BT.lf) [5,w155,w191,w273,w382,w472,w537] (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w538] BT.lf)))
noncomputable def node1071 : BT := (BT.nd node1066 [5,w155,w191,w273,w382,w472,w502] node1076)
noncomputable def node1087 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w558] BT.lf) [5,w155,w191,w273,w382,w472,w559] BT.lf) [5,w155,w191,w273,w382,w472,w561] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w576] BT.lf) [5,w155,w191,w273,w382,w472,w577] BT.lf)) [5,w155,w191,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w589] BT.lf) [5,w155,w191,w273,w382,w472,w590] BT.lf) [5,w155,w191,w273,w382,w472,w591] (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w593] BT.lf)))
noncomputable def node1097 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w595] BT.lf) [5,w155,w191,w273,w382,w472,w596] BT.lf) [5,w155,w191,w273,w382,w472,w598] (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w599] BT.lf)) [5,w155,w191,w273,w382,w472,w600] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w602] BT.lf) [5,w155,w191,w273,w382,w472,w603] BT.lf) [5,w155,w191,w273,w382,w472,w604] (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w606] BT.lf)))
noncomputable def node1092 : BT := (BT.nd node1087 [5,w155,w191,w273,w382,w472,w594] node1097)
noncomputable def node1081 : BT := (BT.nd node1071 [5,w155,w191,w273,w382,w472,w557] node1092)
noncomputable def node1060 : BT := (BT.nd node1039 [5,w155,w191,w273,w382,w461,w472] node1081)
noncomputable def node1108 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w608] BT.lf) [5,w155,w191,w273,w382,w472,w609] BT.lf) [5,w155,w191,w273,w382,w472,w610] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w611] BT.lf) [5,w155,w191,w273,w382,w472,w612] BT.lf)) [5,w155,w191,w273,w382,w472,w613] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w614] BT.lf) [5,w155,w191,w273,w382,w472,w615] BT.lf) [5,w155,w191,w273,w382,w472,w616] (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w617] BT.lf)))
noncomputable def node1119 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w619] BT.lf) [5,w155,w191,w273,w382,w472,w621] BT.lf) [5,w155,w191,w273,w382,w472,w622] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w623] BT.lf) [5,w155,w191,w273,w382,w472,w625] BT.lf)) [5,w155,w191,w273,w382,w472,w626] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w627] BT.lf) [5,w155,w191,w273,w382,w472,w628] BT.lf) [5,w155,w191,w273,w382,w472,w629] (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w630] BT.lf)))
noncomputable def node1113 : BT := (BT.nd node1108 [5,w155,w191,w273,w382,w472,w618] node1119)
noncomputable def node1130 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w632] BT.lf) [5,w155,w191,w273,w382,w472,w633] BT.lf) [5,w155,w191,w273,w382,w472,w634] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w635] BT.lf) [5,w155,w191,w273,w382,w472,w636] BT.lf)) [5,w155,w191,w273,w382,w472,w637] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w638] BT.lf) [5,w155,w191,w273,w382,w472,w639] BT.lf) [5,w155,w191,w273,w382,w472,w640] (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w641] BT.lf)))
noncomputable def node1140 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w644] BT.lf) [5,w155,w191,w273,w382,w472,w645] BT.lf) [5,w155,w191,w273,w382,w472,w646] (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w647] BT.lf)) [5,w155,w191,w273,w382,w472,w648] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w649] BT.lf) [5,w155,w191,w273,w382,w472,w650] BT.lf) [5,w155,w191,w273,w382,w472,w651] (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w652] BT.lf)))
noncomputable def node1135 : BT := (BT.nd node1130 [5,w155,w191,w273,w382,w472,w642] node1140)
noncomputable def node1124 : BT := (BT.nd node1113 [5,w155,w191,w273,w382,w472,w631] node1135)
noncomputable def node1151 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w654] BT.lf) [5,w155,w191,w273,w382,w472,w655] BT.lf) [5,w155,w191,w273,w382,w472,w656] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w658] BT.lf) [5,w155,w191,w273,w382,w472,w659] BT.lf)) [5,w155,w191,w273,w382,w472,w660] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w661] BT.lf) [5,w155,w191,w273,w382,w472,w662] BT.lf) [5,w155,w191,w273,w382,w472,w663] (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w664] BT.lf)))
noncomputable def node1161 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w667] BT.lf) [5,w155,w191,w273,w382,w472,w668] BT.lf) [5,w155,w191,w273,w382,w472,w670] (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w672] BT.lf)) [5,w155,w191,w273,w382,w472,w673] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w675] BT.lf) [5,w155,w191,w273,w382,w472,w676] BT.lf) [5,w155,w191,w273,w382,w472,w678] (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w679] BT.lf)))
noncomputable def node1156 : BT := (BT.nd node1151 [5,w155,w191,w273,w382,w472,w666] node1161)
noncomputable def node1172 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w681] BT.lf) [5,w155,w191,w273,w382,w472,w683] BT.lf) [5,w155,w191,w273,w382,w472,w684] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w685] BT.lf) [5,w155,w191,w273,w382,w472,w686] BT.lf)) [5,w155,w191,w273,w382,w472,w687] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w472,w688] BT.lf) [5,w155,w191,w273,w382,w473,w588] BT.lf) [5,w155,w191,w273,w382,w474,w678] (BT.nd BT.lf [5,w155,w191,w273,w382,w475,w588] BT.lf)))
noncomputable def node1182 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w484,w588] BT.lf) [5,w155,w191,w273,w382,w486] BT.lf) [5,w155,w191,w273,w382,w486,w588] (BT.nd BT.lf [5,w155,w191,w273,w382,w488,w678] BT.lf)) [5,w155,w191,w273,w382,w489,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w490,w588] BT.lf) [5,w155,w191,w273,w382,w492,w588] BT.lf) [5,w155,w191,w273,w382,w493,w588] (BT.nd BT.lf [5,w155,w191,w273,w382,w494,w588] BT.lf)))
noncomputable def node1177 : BT := (BT.nd node1172 [5,w155,w191,w273,w382,w482,w588] node1182)
noncomputable def node1166 : BT := (BT.nd node1156 [5,w155,w191,w273,w382,w472,w680] node1177)
noncomputable def node1145 : BT := (BT.nd node1124 [5,w155,w191,w273,w382,w472,w653] node1166)
noncomputable def node1102 : BT := (BT.nd node1060 [5,w155,w191,w273,w382,w472,w607] node1145)
noncomputable def node1193 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w495,w614] BT.lf) [5,w155,w191,w273,w382,w495,w637] BT.lf) [5,w155,w191,w273,w382,w495,w652] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w495,w678] BT.lf) [5,w155,w191,w273,w382,w495,w680] BT.lf)) [5,w155,w191,w273,w382,w496,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w497,w588] BT.lf) [5,w155,w191,w273,w382,w498,w588] BT.lf) [5,w155,w191,w273,w382,w498,w617] (BT.nd BT.lf [5,w155,w191,w273,w382,w498,w637] BT.lf)))
noncomputable def node1204 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w498,w678] BT.lf) [5,w155,w191,w273,w382,w498,w681] BT.lf) [5,w155,w191,w273,w382,w499,w588] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w500,w588] BT.lf) [5,w155,w191,w273,w382,w501,w678] BT.lf)) [5,w155,w191,w273,w382,w502,w506] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w502,w550] BT.lf) [5,w155,w191,w273,w382,w506] BT.lf) [5,w155,w191,w273,w382,w506,w506] (BT.nd BT.lf [5,w155,w191,w273,w382,w506,w513] BT.lf)))
noncomputable def node1198 : BT := (BT.nd node1193 [5,w155,w191,w273,w382,w498,w652] node1204)
noncomputable def node1215 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w506,w538] BT.lf) [5,w155,w191,w273,w382,w506,w550] BT.lf) [5,w155,w191,w273,w382,w506,w561] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w506,w574] BT.lf) [5,w155,w191,w273,w382,w506,w580] BT.lf)) [5,w155,w191,w273,w382,w506,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w506,w624] BT.lf) [5,w155,w191,w273,w382,w506,w637] BT.lf) [5,w155,w191,w273,w382,w506,w652] (BT.nd BT.lf [5,w155,w191,w273,w382,w506,w669] BT.lf)))
noncomputable def node1225 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w509] BT.lf) [5,w155,w191,w273,w382,w509,w588] BT.lf) [5,w155,w191,w273,w382,w509,w637] (BT.nd BT.lf [5,w155,w191,w273,w382,w511] BT.lf)) [5,w155,w191,w273,w382,w511,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w511,w652] BT.lf) [5,w155,w191,w273,w382,w513,w621] BT.lf) [5,w155,w191,w273,w382,w513,w678] (BT.nd BT.lf [5,w155,w191,w273,w382,w513,w685] BT.lf)))
noncomputable def node1220 : BT := (BT.nd node1215 [5,w155,w191,w273,w382,w506,w678] node1225)
noncomputable def node1209 : BT := (BT.nd node1198 [5,w155,w191,w273,w382,w506,w527] node1220)
noncomputable def node1236 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w515,w588] BT.lf) [5,w155,w191,w273,w382,w516,w588] BT.lf) [5,w155,w191,w273,w382,w517,w588] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w517,w627] BT.lf) [5,w155,w191,w273,w382,w517,w637] BT.lf)) [5,w155,w191,w273,w382,w517,w652] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w517,w678] BT.lf) [5,w155,w191,w273,w382,w517,w683] BT.lf) [5,w155,w191,w273,w382,w519,w588] (BT.nd BT.lf [5,w155,w191,w273,w382,w520,w588] BT.lf)))
noncomputable def node1246 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w521,w630] BT.lf) [5,w155,w191,w273,w382,w521,w637] BT.lf) [5,w155,w191,w273,w382,w521,w652] (BT.nd BT.lf [5,w155,w191,w273,w382,w521,w678] BT.lf)) [5,w155,w191,w273,w382,w521,w684] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w522,w588] BT.lf) [5,w155,w191,w273,w382,w523,w588] BT.lf) [5,w155,w191,w273,w382,w529,w588] (BT.nd BT.lf [5,w155,w191,w273,w382,w540,w588] BT.lf)))
noncomputable def node1241 : BT := (BT.nd node1236 [5,w155,w191,w273,w382,w521,w588] node1246)
noncomputable def node1257 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w541,w637] BT.lf) [5,w155,w191,w273,w382,w541,w645] BT.lf) [5,w155,w191,w273,w382,w541,w652] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w541,w678] BT.lf) [5,w155,w191,w273,w382,w541,w686] BT.lf)) [5,w155,w191,w273,w382,w542,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w543,w588] BT.lf) [5,w155,w191,w273,w382,w546,w588] BT.lf) [5,w155,w191,w273,w382,w546,w637] (BT.nd BT.lf [5,w155,w191,w273,w382,w546,w652] BT.lf)))
noncomputable def node1267 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w547,w588] BT.lf) [5,w155,w191,w273,w382,w548,w588] BT.lf) [5,w155,w191,w273,w382,w548,w637] (BT.nd BT.lf [5,w155,w191,w273,w382,w549,w588] BT.lf)) [5,w155,w191,w273,w382,w550,w557] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w550,w561] BT.lf) [5,w155,w191,w273,w382,w550,w588] BT.lf) [5,w155,w191,w273,w382,w550,w610] (BT.nd BT.lf [5,w155,w191,w273,w382,w550,w614] BT.lf)))
noncomputable def node1262 : BT := (BT.nd node1257 [5,w155,w191,w273,w382,w546,w678] node1267)
noncomputable def node1251 : BT := (BT.nd node1241 [5,w155,w191,w273,w382,w541,w588] node1262)
noncomputable def node1230 : BT := (BT.nd node1209 [5,w155,w191,w273,w382,w513,w687] node1251)
noncomputable def node1278 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w550,w621] BT.lf) [5,w155,w191,w273,w382,w550,w623] BT.lf) [5,w155,w191,w273,w382,w550,w627] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w550,w630] BT.lf) [5,w155,w191,w273,w382,w550,w633] BT.lf)) [5,w155,w191,w273,w382,w550,w635] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w550,w637] BT.lf) [5,w155,w191,w273,w382,w550,w645] BT.lf) [5,w155,w191,w273,w382,w550,w648] (BT.nd BT.lf [5,w155,w191,w273,w382,w550,w652] BT.lf)))
noncomputable def node1288 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w550,w666] BT.lf) [5,w155,w191,w273,w382,w550,w668] BT.lf) [5,w155,w191,w273,w382,w550,w678] (BT.nd BT.lf [5,w155,w191,w273,w382,w550,w685] BT.lf)) [5,w155,w191,w273,w382,w550,w687] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w550,w688] BT.lf) [5,w155,w191,w273,w382,w553,w588] BT.lf) [5,w155,w191,w273,w382,w559] (BT.nd BT.lf [5,w155,w191,w273,w382,w559,w588] BT.lf)))
noncomputable def node1283 : BT := (BT.nd node1278 [5,w155,w191,w273,w382,w550,w664] node1288)
noncomputable def node1299 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w561,w588] BT.lf) [5,w155,w191,w273,w382,w563,w678] BT.lf) [5,w155,w191,w273,w382,w563,w687] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w564,w588] BT.lf) [5,w155,w191,w273,w382,w565,w588] BT.lf)) [5,w155,w191,w273,w382,w571,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w571,w637] BT.lf) [5,w155,w191,w273,w382,w571,w652] BT.lf) [5,w155,w191,w273,w382,w571,w678] (BT.nd BT.lf [5,w155,w191,w273,w382,w572,w588] BT.lf)))
noncomputable def node1309 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w573,w588] BT.lf) [5,w155,w191,w273,w382,w573,w652] BT.lf) [5,w155,w191,w273,w382,w574,w621] (BT.nd BT.lf [5,w155,w191,w273,w382,w574,w678] BT.lf)) [5,w155,w191,w273,w382,w574,w685] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w574,w687] BT.lf) [5,w155,w191,w273,w382,w577] BT.lf) [5,w155,w191,w273,w382,w577,w588] (BT.nd BT.lf [5,w155,w191,w273,w382,w581,w678] BT.lf)))
noncomputable def node1304 : BT := (BT.nd node1299 [5,w155,w191,w273,w382,w572,w637] node1309)
noncomputable def node1293 : BT := (BT.nd node1283 [5,w155,w191,w273,w382,w561] node1304)
noncomputable def node1320 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w382,w584,w588] BT.lf) [5,w155,w191,w273,w382,w585,w678] BT.lf) [5,w155,w191,w273,w382,w585,w687] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w383,w472,w588] BT.lf) [5,w155,w191,w273,w385,w472,w588] BT.lf)) [5,w155,w191,w273,w388,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w389,w472,w588] BT.lf) [5,w155,w191,w273,w391,w472,w588] BT.lf) [5,w155,w191,w273,w394,w472,w588] (BT.nd BT.lf [5,w155,w191,w273,w398,w472,w588] BT.lf)))
noncomputable def node1330 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w400,w472,w588] BT.lf) [5,w155,w191,w273,w401,w472,w588] BT.lf) [5,w155,w191,w273,w401,w472,w614] (BT.nd BT.lf [5,w155,w191,w273,w401,w472,w637] BT.lf)) [5,w155,w191,w273,w401,w472,w652] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w401,w472,w678] BT.lf) [5,w155,w191,w273,w401,w495,w588] BT.lf) [5,w155,w191,w273,w401,w550,w588] (BT.nd BT.lf [5,w155,w191,w273,w402,w472,w588] BT.lf)))
noncomputable def node1325 : BT := (BT.nd node1320 [5,w155,w191,w273,w399,w472,w588] node1330)
noncomputable def node1341 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w404,w472,w588] BT.lf) [5,w155,w191,w273,w404,w472,w617] BT.lf) [5,w155,w191,w273,w404,w472,w637] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w404,w472,w652] BT.lf) [5,w155,w191,w273,w404,w472,w678] BT.lf)) [5,w155,w191,w273,w404,w498,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w404,w550,w588] BT.lf) [5,w155,w191,w273,w405,w472,w588] BT.lf) [5,w155,w191,w273,w410,w472,w588] (BT.nd BT.lf [5,w155,w191,w273,w411,w472,w588] BT.lf)))
noncomputable def node1351 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w411,w472,w637] BT.lf) [5,w155,w191,w273,w411,w472,w652] BT.lf) [5,w155,w191,w273,w411,w472,w678] (BT.nd BT.lf [5,w155,w191,w273,w411,w550,w588] BT.lf)) [5,w155,w191,w273,w412,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w413,w472,w588] BT.lf) [5,w155,w191,w273,w413,w550,w588] BT.lf) [5,w155,w191,w273,w414,w420,w472] (BT.nd BT.lf [5,w155,w191,w273,w414,w425,w472] BT.lf)))
noncomputable def node1346 : BT := (BT.nd node1341 [5,w155,w191,w273,w411,w472,w621] node1351)
noncomputable def node1335 : BT := (BT.nd node1325 [5,w155,w191,w273,w403,w472,w588] node1346)
noncomputable def node1314 : BT := (BT.nd node1293 [5,w155,w191,w273,w382,w583,w588] node1335)
noncomputable def node1272 : BT := (BT.nd node1230 [5,w155,w191,w273,w382,w550,w617] node1314)
noncomputable def node1187 : BT := (BT.nd node1102 [5,w155,w191,w273,w382,w495,w588] node1272)
noncomputable def node1017 : BT := (BT.nd node848 [5,w155,w191,w273,w348,w472,w588] node1187)
noncomputable def node678 : BT := (BT.nd node339 [5,w82,w155,w191,w313,w382,w472] node1017)
noncomputable def node1362 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w414,w425,w577] BT.lf) [5,w155,w191,w273,w417,w425,w472] BT.lf) [5,w155,w191,w273,w418,w425,w472] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w420,w472,w506] BT.lf) [5,w155,w191,w273,w420,w472,w588] BT.lf)) [5,w155,w191,w273,w420,w472,w637] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w420,w472,w652] BT.lf) [5,w155,w191,w273,w420,w472,w678] BT.lf) [5,w155,w191,w273,w420,w506] (BT.nd BT.lf [5,w155,w191,w273,w420,w506,w588] BT.lf)))
noncomputable def node1373 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w421,w472,w588] BT.lf) [5,w155,w191,w273,w421,w472,w637] BT.lf) [5,w155,w191,w273,w422,w472,w588] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w422,w472,w652] BT.lf) [5,w155,w191,w273,w423,w425,w472] BT.lf)) [5,w155,w191,w273,w424,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w424,w472,w678] BT.lf) [5,w155,w191,w273,w425,w445,w588] BT.lf) [5,w155,w191,w273,w425,w449,w472] (BT.nd BT.lf [5,w155,w191,w273,w425,w450,w472] BT.lf)))
noncomputable def node1367 : BT := (BT.nd node1362 [5,w155,w191,w273,w420,w550,w588] node1373)
noncomputable def node1384 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w425,w461,w472] BT.lf) [5,w155,w191,w273,w425,w472,w502] BT.lf) [5,w155,w191,w273,w425,w472,w506] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w425,w472,w576] BT.lf) [5,w155,w191,w273,w425,w472,w577] BT.lf)) [5,w155,w191,w273,w425,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w425,w472,w593] BT.lf) [5,w155,w191,w273,w425,w472,w610] BT.lf) [5,w155,w191,w273,w425,w472,w614] (BT.nd BT.lf [5,w155,w191,w273,w425,w472,w617] BT.lf)))
noncomputable def node1394 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w425,w472,w627] BT.lf) [5,w155,w191,w273,w425,w472,w630] BT.lf) [5,w155,w191,w273,w425,w472,w631] (BT.nd BT.lf [5,w155,w191,w273,w425,w472,w633] BT.lf)) [5,w155,w191,w273,w425,w472,w637] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w425,w472,w645] BT.lf) [5,w155,w191,w273,w425,w472,w646] BT.lf) [5,w155,w191,w273,w425,w472,w648] (BT.nd BT.lf [5,w155,w191,w273,w425,w472,w652] BT.lf)))
noncomputable def node1389 : BT := (BT.nd node1384 [5,w155,w191,w273,w425,w472,w621] node1394)
noncomputable def node1378 : BT := (BT.nd node1367 [5,w155,w191,w273,w425,w460,w472] node1389)
noncomputable def node1405 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w425,w472,w666] BT.lf) [5,w155,w191,w273,w425,w472,w670] BT.lf) [5,w155,w191,w273,w425,w472,w678] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w425,w472,w685] BT.lf) [5,w155,w191,w273,w425,w472,w687] BT.lf)) [5,w155,w191,w273,w425,w495,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w425,w498,w588] BT.lf) [5,w155,w191,w273,w425,w506] BT.lf) [5,w155,w191,w273,w425,w506,w588] (BT.nd BT.lf [5,w155,w191,w273,w425,w513,w678] BT.lf)))
noncomputable def node1415 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w425,w521,w588] BT.lf) [5,w155,w191,w273,w425,w522,w588] BT.lf) [5,w155,w191,w273,w425,w541,w588] (BT.nd BT.lf [5,w155,w191,w273,w425,w542,w588] BT.lf)) [5,w155,w191,w273,w425,w546,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w425,w550,w588] BT.lf) [5,w155,w191,w273,w425,w550,w637] BT.lf) [5,w155,w191,w273,w425,w550,w652] (BT.nd BT.lf [5,w155,w191,w273,w425,w550,w678] BT.lf)))
noncomputable def node1410 : BT := (BT.nd node1405 [5,w155,w191,w273,w425,w517,w588] node1415)
noncomputable def node1426 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w425,w571,w588] BT.lf) [5,w155,w191,w273,w425,w574,w678] BT.lf) [5,w155,w191,w273,w425,w577] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w425,w577,w588] BT.lf) [5,w155,w191,w273,w425,w581,w678] BT.lf)) [5,w155,w191,w273,w426,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w427,w472,w588] BT.lf) [5,w155,w191,w273,w428,w472,w588] BT.lf) [5,w155,w191,w273,w428,w472,w627] (BT.nd BT.lf [5,w155,w191,w273,w428,w472,w637] BT.lf)))
noncomputable def node1436 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w428,w472,w678] BT.lf) [5,w155,w191,w273,w428,w517,w588] BT.lf) [5,w155,w191,w273,w428,w550,w588] (BT.nd BT.lf [5,w155,w191,w273,w430,w472,w588] BT.lf)) [5,w155,w191,w273,w433,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w434,w472,w588] BT.lf) [5,w155,w191,w273,w434,w472,w633] BT.lf) [5,w155,w191,w273,w434,w472,w637] (BT.nd BT.lf [5,w155,w191,w273,w434,w472,w652] BT.lf)))
noncomputable def node1431 : BT := (BT.nd node1426 [5,w155,w191,w273,w428,w472,w652] node1436)
noncomputable def node1420 : BT := (BT.nd node1410 [5,w155,w191,w273,w425,w550,w687] node1431)
noncomputable def node1399 : BT := (BT.nd node1378 [5,w155,w191,w273,w425,w472,w664] node1420)
noncomputable def node1447 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w434,w527,w588] BT.lf) [5,w155,w191,w273,w434,w550,w588] BT.lf) [5,w155,w191,w273,w434,w588,w678] (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w434,w678] BT.lf) [5,w155,w191,w273,w436,w472,w588] BT.lf)) [5,w155,w191,w273,w437,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w437,w550,w588] BT.lf) [5,w155,w191,w273,w441,w521,w588] BT.lf) [5,w155,w191,w273,w441,w574,w678] (BT.nd BT.lf [5,w155,w191,w273,w443,w472,w588] BT.lf)))
noncomputable def node1458 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w273,w447,w472,w588] BT.lf) [5,w155,w191,w273,w448,w472,w588] BT.lf) [5,w155,w191,w274,w382,w472,w652] (BT.nd (BT.nd BT.lf [5,w155,w191,w278,w382,w550,w588] BT.lf) [5,w155,w191,w279,w382,w472,w588] BT.lf)) [5,w155,w191,w280,w382,w550,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w287,w382,w472,w588] BT.lf) [5,w155,w191,w288,w382,w472,w588] BT.lf) [5,w155,w191,w289,w382,w472,w588] (BT.nd BT.lf [5,w155,w191,w290,w382,w472,w588] BT.lf)))
noncomputable def node1452 : BT := (BT.nd node1447 [5,w155,w191,w273,w444,w472,w588] node1458)
noncomputable def node1469 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w290,w382,w472,w637] BT.lf) [5,w155,w191,w290,w382,w472,w652] BT.lf) [5,w155,w191,w290,w382,w472,w654] (BT.nd (BT.nd BT.lf [5,w155,w191,w290,w382,w472,w678] BT.lf) [5,w155,w191,w290,w382,w495,w588] BT.lf)) [5,w155,w191,w290,w382,w550,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w290,w382,w553,w588] BT.lf) [5,w155,w191,w290,w401,w472,w588] BT.lf) [5,w155,w191,w290,w425,w472,w588] (BT.nd BT.lf [5,w155,w191,w291,w313,w382,w472] BT.lf)))
noncomputable def node1479 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w297,w382,w550,w588] BT.lf) [5,w155,w191,w299,w382,w472,w588] BT.lf) [5,w155,w191,w300,w382,w472,w588] (BT.nd BT.lf [5,w155,w191,w301,w382,w472,w652] BT.lf)) [5,w155,w191,w301,w382,w550,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w302,w313,w382,w472] BT.lf) [5,w155,w191,w307,w382,w472,w588] BT.lf) [5,w155,w191,w308,w382,w472,w588] (BT.nd BT.lf [5,w155,w191,w308,w382,w472,w621] BT.lf)))
noncomputable def node1474 : BT := (BT.nd node1469 [5,w155,w191,w292,w382,w550,w588] node1479)
noncomputable def node1463 : BT := (BT.nd node1452 [5,w155,w191,w290,w382,w472,w614] node1474)
noncomputable def node1490 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w308,w382,w472,w652] BT.lf) [5,w155,w191,w308,w382,w472,w656] BT.lf) [5,w155,w191,w308,w382,w472,w678] (BT.nd (BT.nd BT.lf [5,w155,w191,w308,w382,w513,w588] BT.lf) [5,w155,w191,w308,w382,w550,w588] BT.lf)) [5,w155,w191,w308,w382,w574,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w308,w411,w472,w588] BT.lf) [5,w155,w191,w308,w425,w472,w588] BT.lf) [5,w155,w191,w309,w382,w472,w588] (BT.nd BT.lf [5,w155,w191,w310,w313,w382,w472] BT.lf)))
noncomputable def node1500 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w313,w313,w382,w472] BT.lf) [5,w155,w191,w313,w321,w382,w472] BT.lf) [5,w155,w191,w313,w343,w382,w472] (BT.nd BT.lf [5,w155,w191,w313,w365,w382,w472] BT.lf)) [5,w155,w191,w313,w368,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w313,w375,w382,w472] BT.lf) [5,w155,w191,w313,w382,w382,w472] BT.lf) [5,w155,w191,w313,w382,w420,w472] (BT.nd BT.lf [5,w155,w191,w313,w382,w425,w472] BT.lf)))
noncomputable def node1495 : BT := (BT.nd node1490 [5,w155,w191,w310,w321,w382,w550] node1500)
noncomputable def node1511 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w313,w382,w459,w472] BT.lf) [5,w155,w191,w313,w382,w462,w472] BT.lf) [5,w155,w191,w313,w382,w465,w472] (BT.nd (BT.nd BT.lf [5,w155,w191,w313,w382,w472] BT.lf) [5,w155,w191,w313,w382,w472,w472] BT.lf)) [5,w155,w191,w313,w382,w472,w506] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w313,w382,w472,w513] BT.lf) [5,w155,w191,w313,w382,w472,w527] BT.lf) [5,w155,w191,w313,w382,w472,w550] (BT.nd BT.lf [5,w155,w191,w313,w382,w472,w561] BT.lf)))
noncomputable def node1521 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w313,w382,w472,w588] BT.lf) [5,w155,w191,w313,w382,w472,w624] BT.lf) [5,w155,w191,w313,w382,w472,w637] (BT.nd BT.lf [5,w155,w191,w313,w382,w472,w652] BT.lf)) [5,w155,w191,w313,w382,w472,w669] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w313,w382,w472,w678] BT.lf) [5,w155,w191,w313,w382,w506] BT.lf) [5,w155,w191,w313,w382,w506,w588] (BT.nd BT.lf [5,w155,w191,w313,w382,w550] BT.lf)))
noncomputable def node1516 : BT := (BT.nd node1511 [5,w155,w191,w313,w382,w472,w574] node1521)
noncomputable def node1505 : BT := (BT.nd node1495 [5,w155,w191,w313,w382,w441,w472] node1516)
noncomputable def node1484 : BT := (BT.nd node1463 [5,w155,w191,w308,w382,w472,w637] node1505)
noncomputable def node1441 : BT := (BT.nd node1399 [5,w155,w191,w273,w434,w472,w678] node1484)
noncomputable def node1532 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w313,w382,w561] BT.lf) [5,w155,w191,w313,w382,w561,w588] BT.lf) [5,w155,w191,w313,w420,w472] (BT.nd (BT.nd BT.lf [5,w155,w191,w313,w420,w472,w588] BT.lf) [5,w155,w191,w313,w425,w472] BT.lf)) [5,w155,w191,w313,w425,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w316,w382,w472] BT.lf) [5,w155,w191,w316,w382,w472,w588] BT.lf) [5,w155,w191,w316,w382,w472,w637] (BT.nd BT.lf [5,w155,w191,w319,w382,w472] BT.lf)))
noncomputable def node1543 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w319,w382,w472,w678] BT.lf) [5,w155,w191,w321,w382,w472,w652] BT.lf) [5,w155,w191,w321,w382,w472,w664] (BT.nd (BT.nd BT.lf [5,w155,w191,w321,w382,w472,w687] BT.lf) [5,w155,w191,w321,w382,w550,w588] BT.lf)) [5,w155,w191,w321,w382,w550,w637] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w321,w382,w550,w652] BT.lf) [5,w155,w191,w321,w382,w550,w678] BT.lf) [5,w155,w191,w321,w382,w550,w687] (BT.nd BT.lf [5,w155,w191,w321,w425,w472,w652] BT.lf)))
noncomputable def node1537 : BT := (BT.nd node1532 [5,w155,w191,w319,w382,w472,w588] node1543)
noncomputable def node1554 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w323,w331,w472,w588] BT.lf) [5,w155,w191,w323,w343,w550,w588] BT.lf) [5,w155,w191,w323,w382,w550,w588] (BT.nd (BT.nd BT.lf [5,w155,w191,w323,w472,w550,w588] BT.lf) [5,w155,w191,w323,w550,w588] BT.lf)) [5,w155,w191,w327,w382,w550,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w329,w382,w472,w588] BT.lf) [5,w155,w191,w330,w382,w472,w588] BT.lf) [5,w155,w191,w331,w382,w472,w588] (BT.nd BT.lf [5,w155,w191,w331,w382,w472,w630] BT.lf)))
noncomputable def node1564 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w331,w382,w472,w652] BT.lf) [5,w155,w191,w331,w382,w472,w660] BT.lf) [5,w155,w191,w331,w382,w472,w678] (BT.nd BT.lf [5,w155,w191,w331,w382,w521,w588] BT.lf)) [5,w155,w191,w331,w382,w550,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w331,w382,w565,w588] BT.lf) [5,w155,w191,w331,w425,w472,w588] BT.lf) [5,w155,w191,w331,w441,w472,w588] (BT.nd BT.lf [5,w155,w191,w332,w382,w472,w588] BT.lf)))
noncomputable def node1559 : BT := (BT.nd node1554 [5,w155,w191,w331,w382,w472,w637] node1564)
noncomputable def node1548 : BT := (BT.nd node1537 [5,w155,w191,w321,w425,w550,w588] node1559)
noncomputable def node1575 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w335,w382,w472,w588] BT.lf) [5,w155,w191,w336,w382,w472,w588] BT.lf) [5,w155,w191,w336,w382,w472,w633] (BT.nd (BT.nd BT.lf [5,w155,w191,w336,w382,w472,w637] BT.lf) [5,w155,w191,w336,w382,w472,w652] BT.lf)) [5,w155,w191,w336,w382,w472,w663] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w336,w382,w472,w678] BT.lf) [5,w155,w191,w336,w382,w527,w588] BT.lf) [5,w155,w191,w336,w382,w550,w588] (BT.nd BT.lf [5,w155,w191,w336,w382,w588,w678] BT.lf)))
noncomputable def node1585 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w336,w425,w472,w588] BT.lf) [5,w155,w191,w336,w434,w472,w588] BT.lf) [5,w155,w191,w338,w382,w472,w588] (BT.nd BT.lf [5,w155,w191,w339,w382,w472,w588] BT.lf)) [5,w155,w191,w342,w382,w550,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w343,w382,w517,w588] BT.lf) [5,w155,w191,w343,w382,w550,w588] BT.lf) [5,w155,w191,w343,w382,w550,w637] (BT.nd BT.lf [5,w155,w191,w343,w382,w550,w652] BT.lf)))
noncomputable def node1580 : BT := (BT.nd node1575 [5,w155,w191,w336,w382,w678] node1585)
noncomputable def node1596 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w343,w382,w550,w678] BT.lf) [5,w155,w191,w343,w382,w550,w687] BT.lf) [5,w155,w191,w343,w425,w550,w588] (BT.nd (BT.nd BT.lf [5,w155,w191,w343,w428,w472,w588] BT.lf) [5,w155,w191,w357,w382,w472,w588] BT.lf)) [5,w155,w191,w357,w382,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w191,w366,w382,w550,w588] BT.lf) [5,w155,w192,w273,w382,w472,w637] BT.lf) [5,w155,w205,w244,w273,w382,w472] (BT.nd BT.lf [5,w155,w213,w273,w382,w472,w588] BT.lf)))
noncomputable def node1606 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w215,w273,w382,w472,w588] BT.lf) [5,w155,w216,w273,w382,w472,w588] BT.lf) [5,w155,w216,w273,w382,w472,w617] (BT.nd BT.lf [5,w155,w216,w273,w382,w472,w637] BT.lf)) [5,w155,w216,w273,w382,w472,w640] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w216,w273,w382,w472,w652] BT.lf) [5,w155,w216,w273,w382,w472,w678] BT.lf) [5,w155,w216,w273,w382,w498,w588] (BT.nd BT.lf [5,w155,w216,w273,w382,w550,w588] BT.lf)))
noncomputable def node1601 : BT := (BT.nd node1596 [5,w155,w214,w273,w382,w472,w588] node1606)
noncomputable def node1590 : BT := (BT.nd node1580 [5,w155,w191,w343,w382,w550,w664] node1601)
noncomputable def node1569 : BT := (BT.nd node1548 [5,w155,w191,w332,w425,w472,w588] node1590)
noncomputable def node1617 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w216,w273,w425,w472,w588] BT.lf) [5,w155,w217,w244,w273,w382,w472] BT.lf) [5,w155,w224,w273,w382,w472,w588] (BT.nd (BT.nd BT.lf [5,w155,w225,w273,w382,w472,w588] BT.lf) [5,w155,w226,w273,w382,w472,w637] BT.lf)) [5,w155,w228,w244,w273,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w229,w236,w273,w382,w588] BT.lf) [5,w155,w229,w253,w273,w382,w637] BT.lf) [5,w155,w235,w273,w382,w472,w588] (BT.nd BT.lf [5,w155,w236,w273,w382,w472,w588] BT.lf)))
noncomputable def node1627 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w236,w273,w382,w472,w637] BT.lf) [5,w155,w236,w273,w382,w472,w642] BT.lf) [5,w155,w236,w273,w382,w472,w652] (BT.nd BT.lf [5,w155,w236,w273,w382,w472,w678] BT.lf)) [5,w155,w236,w273,w382,w513,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w236,w273,w382,w550,w588] BT.lf) [5,w155,w236,w273,w382,w574,w588] BT.lf) [5,w155,w236,w273,w411,w472,w588] (BT.nd BT.lf [5,w155,w236,w273,w425,w472,w588] BT.lf)))
noncomputable def node1622 : BT := (BT.nd node1617 [5,w155,w236,w273,w382,w472,w621] node1627)
noncomputable def node1638 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w239,w273,w382,w472,w588] BT.lf) [5,w155,w239,w273,w382,w550,w588] BT.lf) [5,w155,w242,w244,w273,w382,w472] (BT.nd (BT.nd BT.lf [5,w155,w244,w244,w273,w382,w472] BT.lf) [5,w155,w244,w253,w273,w382,w472] BT.lf)) [5,w155,w244,w256,w273,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w244,w263,w273,w382,w472] BT.lf) [5,w155,w244,w268,w273,w382,w472] BT.lf) [5,w155,w244,w273,w273,w382,w472] (BT.nd BT.lf [5,w155,w244,w273,w313,w382,w472] BT.lf)))
noncomputable def node1648 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w244,w273,w343,w382,w472] BT.lf) [5,w155,w244,w273,w365,w382,w472] BT.lf) [5,w155,w244,w273,w368,w382,w472] (BT.nd BT.lf [5,w155,w244,w273,w375,w382,w472] BT.lf)) [5,w155,w244,w273,w382,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w244,w273,w382,w420,w472] BT.lf) [5,w155,w244,w273,w382,w425,w472] BT.lf) [5,w155,w244,w273,w382,w441,w472] (BT.nd BT.lf [5,w155,w244,w273,w382,w451,w472] BT.lf)))
noncomputable def node1643 : BT := (BT.nd node1638 [5,w155,w244,w273,w321,w382,w472] node1648)
noncomputable def node1632 : BT := (BT.nd node1622 [5,w155,w236,w308,w382,w472,w588] node1643)
noncomputable def node1659 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w244,w273,w382,w465,w472] BT.lf) [5,w155,w244,w273,w382,w472] BT.lf) [5,w155,w244,w273,w382,w472,w472] (BT.nd (BT.nd BT.lf [5,w155,w244,w273,w382,w472,w506] BT.lf) [5,w155,w244,w273,w382,w472,w513] BT.lf)) [5,w155,w244,w273,w382,w472,w527] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w244,w273,w382,w472,w538] BT.lf) [5,w155,w244,w273,w382,w472,w550] BT.lf) [5,w155,w244,w273,w382,w472,w574] (BT.nd BT.lf [5,w155,w244,w273,w382,w472,w588] BT.lf)))
noncomputable def node1669 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w244,w273,w382,w472,w637] BT.lf) [5,w155,w244,w273,w382,w472,w652] BT.lf) [5,w155,w244,w273,w382,w472,w669] (BT.nd BT.lf [5,w155,w244,w273,w382,w472,w678] BT.lf)) [5,w155,w244,w273,w382,w506] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w244,w273,w382,w506,w588] BT.lf) [5,w155,w244,w273,w382,w550] BT.lf) [5,w155,w244,w273,w382,w550,w588] (BT.nd BT.lf [5,w155,w244,w273,w420,w472] BT.lf)))
noncomputable def node1664 : BT := (BT.nd node1659 [5,w155,w244,w273,w382,w472,w624] node1669)
noncomputable def node1680 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w244,w273,w425,w472] BT.lf) [5,w155,w244,w273,w425,w472,w588] BT.lf) [5,w155,w244,w313,w382,w472] (BT.nd (BT.nd BT.lf [5,w155,w244,w313,w382,w472,w588] BT.lf) [5,w155,w248,w273,w382,w472] BT.lf)) [5,w155,w248,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w248,w273,w382,w472,w652] BT.lf) [5,w155,w251,w273,w382,w472] BT.lf) [5,w155,w251,w273,w382,w472,w588] (BT.nd BT.lf [5,w155,w251,w273,w382,w472,w678] BT.lf)))
noncomputable def node1690 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w253,w273,w382,w472,w664] BT.lf) [5,w155,w253,w273,w382,w472,w685] BT.lf) [5,w155,w253,w273,w382,w550,w637] (BT.nd BT.lf [5,w155,w253,w273,w425,w472,w637] BT.lf)) [5,w155,w253,w343,w382,w550,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w256,w327,w382,w550,w588] BT.lf) [5,w155,w273,w323,w327,w472,w588] BT.lf) [5,w155,w273,w325,w382,w472,w588] (BT.nd BT.lf [5,w155,w273,w326,w382,w472,w588] BT.lf)))
noncomputable def node1685 : BT := (BT.nd node1680 [5,w155,w253,w273,w382,w472,w637] node1690)
noncomputable def node1674 : BT := (BT.nd node1664 [5,w155,w244,w273,w420,w472,w588] node1685)
noncomputable def node1653 : BT := (BT.nd node1632 [5,w155,w244,w273,w382,w459,w472] node1674)
noncomputable def node1611 : BT := (BT.nd node1569 [5,w155,w216,w273,w404,w472,w588] node1653)
noncomputable def node1526 : BT := (BT.nd node1441 [5,w155,w191,w313,w382,w550,w588] node1611)
noncomputable def node1701 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w273,w327,w382,w472,w637] BT.lf) [5,w155,w273,w327,w382,w472,w645] BT.lf) [5,w155,w273,w327,w382,w472,w652] (BT.nd (BT.nd BT.lf [5,w155,w273,w327,w382,w472,w659] BT.lf) [5,w155,w273,w327,w382,w472,w678] BT.lf)) [5,w155,w273,w327,w382,w541,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w273,w327,w382,w550,w588] BT.lf) [5,w155,w273,w327,w425,w472,w588] BT.lf) [5,w155,w273,w327,w459,w472,w588] (BT.nd BT.lf [5,w155,w273,w327,w472,w574,w588] BT.lf)))
noncomputable def node1712 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w155,w273,w328,w425,w472,w588] BT.lf) [5,w155,w327,w382,w472,w550,w588] BT.lf) [5,w155,w327,w382,w550,w588] (BT.nd (BT.nd BT.lf [5,w155,w343,w382,w441,w550,w588] BT.lf) [5,w155,w343,w441,w459,w472,w588] BT.lf)) [5,w161,w191,w273,w425,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w176,w191,w273,w297,w472,w588] BT.lf) [5,w177,w253,w273,w425,w472,w588] BT.lf) [5,w180,w191,w234,w273,w382,w678] (BT.nd BT.lf [5,w191,w207,w273,w382,w472,w588] BT.lf)))
noncomputable def node1706 : BT := (BT.nd node1701 [5,w155,w273,w328,w382,w472,w588] node1712)
noncomputable def node1723 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w191,w209,w212,w273,w382,w472] BT.lf) [5,w191,w210,w273,w382,w472,w588] BT.lf) [5,w191,w212,w273,w382,w472,w588] (BT.nd (BT.nd BT.lf [5,w191,w212,w273,w382,w472,w627] BT.lf) [5,w191,w212,w273,w382,w472,w637] BT.lf)) [5,w191,w212,w273,w382,w472,w652] (BT.nd (BT.nd (BT.nd BT.lf [5,w191,w212,w273,w382,w472,w678] BT.lf) [5,w191,w212,w273,w382,w517,w588] BT.lf) [5,w191,w212,w273,w382,w550,w588] (BT.nd BT.lf [5,w191,w212,w273,w425,w472,w588] BT.lf)))
noncomputable def node1733 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w191,w212,w273,w444,w472,w588] BT.lf) [5,w191,w212,w343,w382,w472,w588] BT.lf) [5,w191,w219,w273,w382,w472,w588] (BT.nd BT.lf [5,w191,w220,w223,w273,w382,w472] BT.lf)) [5,w191,w221,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w191,w223,w256,w273,w472,w588] BT.lf) [5,w191,w223,w273,w382,w472,w588] BT.lf) [5,w191,w223,w273,w382,w472,w630] (BT.nd BT.lf [5,w191,w223,w273,w382,w472,w637] BT.lf)))
noncomputable def node1728 : BT := (BT.nd node1723 [5,w191,w212,w273,w428,w472,w588] node1733)
noncomputable def node1717 : BT := (BT.nd node1706 [5,w191,w208,w273,w382,w472,w588] node1728)
noncomputable def node1744 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w191,w223,w273,w382,w472,w678] BT.lf) [5,w191,w223,w273,w382,w521,w588] BT.lf) [5,w191,w223,w273,w382,w550,w588] (BT.nd (BT.nd BT.lf [5,w191,w223,w273,w425,w472,w588] BT.lf) [5,w191,w223,w273,w441,w472,w588] BT.lf)) [5,w191,w223,w331,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w191,w227,w273,w382,w472,w588] BT.lf) [5,w191,w229,w234,w273,w382,w588] BT.lf) [5,w191,w229,w253,w273,w425,w588] (BT.nd BT.lf [5,w191,w230,w234,w273,w382,w472] BT.lf)))
noncomputable def node1754 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w191,w234,w273,w382,w472,w588] BT.lf) [5,w191,w234,w273,w382,w472,w633] BT.lf) [5,w191,w234,w273,w382,w472,w637] (BT.nd BT.lf [5,w191,w234,w273,w382,w472,w652] BT.lf)) [5,w191,w234,w273,w382,w472,w678] (BT.nd (BT.nd (BT.nd BT.lf [5,w191,w234,w273,w382,w527,w588] BT.lf) [5,w191,w234,w273,w382,w550,w588] BT.lf) [5,w191,w234,w273,w382,w588,w678] (BT.nd BT.lf [5,w191,w234,w273,w382,w678] BT.lf)))
noncomputable def node1749 : BT := (BT.nd node1744 [5,w191,w231,w273,w382,w472,w588] node1754)
noncomputable def node1765 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w191,w234,w273,w434,w472,w588] BT.lf) [5,w191,w234,w273,w448,w472,w588] BT.lf) [5,w191,w234,w336,w382,w472,w588] (BT.nd (BT.nd BT.lf [5,w191,w238,w273,w382,w472,w588] BT.lf) [5,w191,w238,w273,w382,w550,w588] BT.lf)) [5,w191,w241,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w191,w242,w253,w273,w425,w472] BT.lf) [5,w191,w243,w273,w425,w472,w588] BT.lf) [5,w191,w253,w273,w382,w513,w678] (BT.nd BT.lf [5,w191,w253,w273,w414,w425,w472] BT.lf)))
noncomputable def node1775 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w191,w253,w273,w425,w472,w637] BT.lf) [5,w191,w253,w273,w425,w472,w652] BT.lf) [5,w191,w253,w273,w425,w472,w678] (BT.nd BT.lf [5,w191,w253,w273,w425,w550,w588] BT.lf)) [5,w191,w253,w321,w382,w472,w652] (BT.nd (BT.nd (BT.nd BT.lf [5,w191,w253,w321,w382,w550,w588] BT.lf) [5,w191,w256,w297,w382,w550,w588] BT.lf) [5,w191,w259,w321,w425,w472,w588] (BT.nd BT.lf [5,w191,w273,w293,w382,w472,w588] BT.lf)))
noncomputable def node1770 : BT := (BT.nd node1765 [5,w191,w253,w273,w425,w472,w588] node1775)
noncomputable def node1759 : BT := (BT.nd node1749 [5,w191,w234,w273,w425,w472,w588] node1770)
noncomputable def node1738 : BT := (BT.nd node1717 [5,w191,w223,w273,w382,w472,w652] node1759)
noncomputable def node1786 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w191,w273,w295,w382,w472,w588] BT.lf) [5,w191,w273,w297,w382,w472,w588] BT.lf) [5,w191,w273,w297,w382,w472,w637] (BT.nd (BT.nd BT.lf [5,w191,w273,w297,w382,w472,w645] BT.lf) [5,w191,w273,w297,w382,w472,w652] BT.lf)) [5,w191,w273,w297,w382,w472,w678] (BT.nd (BT.nd (BT.nd BT.lf [5,w191,w273,w297,w382,w541,w588] BT.lf) [5,w191,w273,w297,w382,w550,w588] BT.lf) [5,w191,w273,w297,w425,w472,w588] (BT.nd BT.lf [5,w191,w273,w297,w459,w472,w588] BT.lf)))
noncomputable def node1797 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w191,w273,w298,w382,w472,w588] BT.lf) [5,w191,w273,w306,w425,w472,w588] BT.lf) [5,w191,w273,w310,w321,w425,w472] (BT.nd (BT.nd BT.lf [5,w191,w273,w311,w425,w472,w588] BT.lf) [5,w191,w273,w321,w414,w425,w472] BT.lf)) [5,w191,w273,w321,w425,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w191,w273,w321,w425,w472,w637] BT.lf) [5,w191,w273,w321,w425,w472,w652] BT.lf) [5,w191,w273,w321,w425,w472,w678] (BT.nd BT.lf [5,w191,w273,w321,w425,w550,w588] BT.lf)))
noncomputable def node1791 : BT := (BT.nd node1786 [5,w191,w273,w297,w472,w574,w588] node1797)
noncomputable def node1808 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w191,w273,w343,w348,w472,w588] BT.lf) [5,w191,w273,w348,w382,w472,w588] BT.lf) [5,w191,w273,w348,w472,w588] (BT.nd (BT.nd BT.lf [5,w191,w273,w366,w425,w472,w588] BT.lf) [5,w191,w297,w382,w472,w550,w588] BT.lf)) [5,w191,w297,w382,w550,w588] (BT.nd (BT.nd (BT.nd BT.lf [5,w191,w321,w343,w425,w472,w588] BT.lf) [5,w191,w321,w382,w425,w472,w652] BT.lf) [5,w191,w321,w382,w425,w550,w588] (BT.nd BT.lf [5,w191,w321,w425,w472,w550,w588] BT.lf)))
noncomputable def node1818 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w191,w321,w425,w472,w652] BT.lf) [5,w191,w321,w425,w550,w588] BT.lf) [5,w253,w273,w321,w382,w472,w637] (BT.nd BT.lf [5,w253,w273,w343,w425,w472,w588] BT.lf)) [5,w253,w273,w382,w425,w472,w637] (BT.nd (BT.nd (BT.nd BT.lf [5,w253,w273,w382,w472,w513,w637] BT.lf) [5,w253,w273,w382,w513,w527,w588] BT.lf) [5,w253,w273,w425,w472,w527,w588] (BT.nd BT.lf [5,w253,w273,w425,w472,w588,w637] BT.lf)))
noncomputable def node1813 : BT := (BT.nd node1808 [5,w191,w321,w425,w472,w588,w652] node1818)
noncomputable def node1802 : BT := (BT.nd node1791 [5,w191,w273,w323,w348,w472,w588] node1813)
noncomputable def node1829 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w253,w321,w343,w382,w472,w588] BT.lf) [5,w273,w297,w327,w382,w472,w588] BT.lf) [6,w0,w155,w191,w273,w382,w472,w588] (BT.nd (BT.nd BT.lf [6,w1,w155,w191,w273,w382,w472] BT.lf) [6,w1,w155,w191,w273,w382,w472,w588] BT.lf)) [6,w1,w155,w191,w273,w382,w472,w678] (BT.nd (BT.nd (BT.nd BT.lf [6,w2,w155,w191,w273,w382,w472,w588] BT.lf) [6,w3,w155,w191,w273,w382,w472] BT.lf) [6,w3,w155,w191,w273,w382,w472,w588] (BT.nd BT.lf [6,w3,w155,w191,w273,w382,w472,w652] BT.lf)))
noncomputable def node1839 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w4,w155,w191,w273,w382,w472,w588] BT.lf) [6,w4,w155,w191,w273,w382,w472,w637] BT.lf) [6,w5,w155,w191,w273,w382,w472,w588] (BT.nd BT.lf [6,w6,w155,w191,w273,w382,w472] BT.lf)) [6,w6,w155,w191,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w7,w155,w191,w273,w382,w472,w588] BT.lf) [6,w8,w155,w191,w273,w382,w472,w588] BT.lf) [6,w9,w155,w191,w273,w382,w472,w588] (BT.nd BT.lf [6,w10,w155,w191,w273,w382,w472,w588] BT.lf)))
noncomputable def node1834 : BT := (BT.nd node1829 [6,w4,w155,w191,w273,w382,w472] node1839)
noncomputable def node1850 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w11,w38,w155,w191,w273,w472] BT.lf) [6,w11,w59,w155,w191,w382,w472] BT.lf) [6,w11,w82,w155,w273,w382,w472] (BT.nd (BT.nd BT.lf [6,w11,w106,w191,w273,w382,w472] BT.lf) [6,w11,w140,w155,w191,w273,w382,w472] BT.lf)) [6,w11,w155,w191,w273,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [6,w11,w155,w191,w273,w382,w472,w588] BT.lf) [6,w11,w155,w191,w273,w382,w472,w637] BT.lf) [6,w11,w155,w191,w273,w382,w472,w652] (BT.nd BT.lf [6,w11,w155,w191,w273,w382,w472,w678] BT.lf)))
noncomputable def node1860 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w11,w155,w191,w273,w382,w550,w588] BT.lf) [6,w11,w155,w191,w273,w425,w472] BT.lf) [6,w11,w155,w191,w273,w425,w472,w588] (BT.nd BT.lf [6,w12,w155,w191,w273,w382,w472,w588] BT.lf)) [6,w14,w155,w191,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w14,w155,w191,w273,w382,w550,w588] BT.lf) [6,w14,w155,w191,w273,w382,w588] BT.lf) [6,w16,w155,w191,w273,w382,w472,w588] (BT.nd BT.lf [6,w17,w155,w191,w273,w382,w472,w588] BT.lf)))
noncomputable def node1855 : BT := (BT.nd node1850 [6,w11,w155,w191,w273,w382,w550] node1860)
noncomputable def node1844 : BT := (BT.nd node1834 [6,w11,w27,w155,w191,w273,w382] node1855)
noncomputable def node1823 : BT := (BT.nd node1802 [5,w253,w273,w425,w472,w637] node1844)
noncomputable def node1780 : BT := (BT.nd node1738 [5,w191,w273,w294,w297,w382,w472] node1823)
noncomputable def node1871 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w21,w155,w191,w273,w382,w472,w588] BT.lf) [6,w22,w155,w191,w273,w382,w472,w588] BT.lf) [6,w23,w155,w191,w273,w382,w472,w588] (BT.nd (BT.nd BT.lf [6,w24,w27,w155,w191,w273,w382] BT.lf) [6,w24,w27,w155,w191,w273,w382,w472] BT.lf)) [6,w24,w155,w191,w273,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [6,w24,w155,w191,w273,w382,w472,w588] BT.lf) [6,w27,w38,w155,w191,w273,w588] BT.lf) [6,w27,w59,w155,w191,w382,w588] (BT.nd BT.lf [6,w27,w82,w155,w273,w382,w588] BT.lf)))
noncomputable def node1882 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w27,w140,w155,w191,w273,w382] BT.lf) [6,w27,w140,w155,w191,w273,w382,w472] BT.lf) [6,w27,w155,w191,w273,w382,w472,w588] (BT.nd (BT.nd BT.lf [6,w27,w155,w191,w273,w382,w472,w637] BT.lf) [6,w27,w155,w191,w273,w382,w472,w652] BT.lf)) [6,w27,w155,w191,w273,w382,w472,w678] (BT.nd (BT.nd (BT.nd BT.lf [6,w27,w155,w191,w273,w382,w550,w588] BT.lf) [6,w27,w155,w191,w273,w382,w588] BT.lf) [6,w27,w155,w191,w273,w382,w637] (BT.nd BT.lf [6,w27,w155,w191,w273,w382,w652] BT.lf)))
noncomputable def node1876 : BT := (BT.nd node1871 [6,w27,w106,w191,w273,w382,w588] node1882)
noncomputable def node1893 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w27,w155,w191,w273,w425,w472,w588] BT.lf) [6,w27,w155,w191,w273,w425,w588] BT.lf) [6,w28,w155,w191,w273,w382,w472,w588] (BT.nd (BT.nd BT.lf [6,w29,w155,w191,w273,w382,w472,w588] BT.lf) [6,w30,w155,w191,w273,w382,w472,w588] BT.lf)) [6,w31,w155,w191,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w31,w155,w191,w273,w425,w472,w588] BT.lf) [6,w31,w155,w191,w273,w472,w588] BT.lf) [6,w32,w155,w191,w273,w382,w472,w588] (BT.nd BT.lf [6,w33,w155,w191,w273,w382,w472,w588] BT.lf)))
noncomputable def node1903 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w35,w155,w191,w273,w382,w472,w588] BT.lf) [6,w37,w155,w191,w273,w382,w472,w588] BT.lf) [6,w38,w59,w155,w191,w472,w588] (BT.nd BT.lf [6,w38,w82,w155,w273,w472,w588] BT.lf)) [6,w38,w106,w191,w273,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w38,w140,w155,w191,w273,w382,w472] BT.lf) [6,w38,w140,w155,w191,w273,w472] BT.lf) [6,w38,w155,w191,w273,w382,w472,w588] (BT.nd BT.lf [6,w38,w155,w191,w273,w382,w472,w637] BT.lf)))
noncomputable def node1898 : BT := (BT.nd node1893 [6,w34,w155,w191,w273,w382,w472,w588] node1903)
noncomputable def node1887 : BT := (BT.nd node1876 [6,w27,w155,w191,w273,w382,w678] node1898)
noncomputable def node1914 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w38,w155,w191,w273,w382,w472,w678] BT.lf) [6,w38,w155,w191,w273,w382,w550,w588] BT.lf) [6,w38,w155,w191,w273,w425,w472,w588] (BT.nd (BT.nd BT.lf [6,w38,w155,w191,w273,w472,w588] BT.lf) [6,w38,w155,w191,w273,w472,w637] BT.lf)) [6,w38,w155,w191,w273,w472,w652] (BT.nd (BT.nd (BT.nd BT.lf [6,w38,w155,w191,w273,w472,w678] BT.lf) [6,w38,w155,w191,w273,w550,w588] BT.lf) [6,w39,w155,w191,w273,w382,w472,w588] (BT.nd BT.lf [6,w41,w155,w191,w273,w382,w472,w588] BT.lf)))
noncomputable def node1924 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w45,w155,w191,w273,w382,w472,w588] BT.lf) [6,w48,w155,w191,w273,w382,w472,w588] BT.lf) [6,w50,w155,w191,w273,w382,w472,w588] (BT.nd BT.lf [6,w52,w155,w191,w273,w382,w472,w588] BT.lf)) [6,w53,w59,w155,w191,w273,w382,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w53,w59,w155,w191,w382,w588] BT.lf) [6,w53,w155,w191,w273,w382,w472,w588] BT.lf) [6,w53,w155,w191,w273,w382,w588] (BT.nd BT.lf [6,w56,w59,w155,w191,w273,w382,w472] BT.lf)))
noncomputable def node1919 : BT := (BT.nd node1914 [6,w43,w155,w191,w273,w382,w472,w588] node1924)
noncomputable def node1935 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w56,w155,w191,w273,w382,w472] BT.lf) [6,w56,w155,w191,w273,w382,w472,w588] BT.lf) [6,w59,w82,w155,w382,w472,w588] (BT.nd (BT.nd BT.lf [6,w59,w106,w191,w382,w472,w588] BT.lf) [6,w59,w140,w155,w191,w273,w382,w472] BT.lf)) [6,w59,w140,w155,w191,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [6,w59,w155,w191,w273,w382,w472,w588] BT.lf) [6,w59,w155,w191,w273,w382,w472,w637] BT.lf) [6,w59,w155,w191,w273,w382,w472,w652] (BT.nd BT.lf [6,w59,w155,w191,w273,w382,w472,w678] BT.lf)))
noncomputable def node1945 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w59,w155,w191,w273,w425,w472,w588] BT.lf) [6,w59,w155,w191,w382,w472,w588] BT.lf) [6,w59,w155,w191,w382,w472,w637] (BT.nd BT.lf [6,w59,w155,w191,w382,w472,w652] BT.lf)) [6,w59,w155,w191,w382,w472,w678] (BT.nd (BT.nd (BT.nd BT.lf [6,w59,w155,w191,w382,w550,w588] BT.lf) [6,w59,w155,w191,w425,w472,w588] BT.lf) [6,w60,w155,w191,w273,w382,w472,w588] (BT.nd BT.lf [6,w62,w155,w191,w273,w382,w472,w588] BT.lf)))
noncomputable def node1940 : BT := (BT.nd node1935 [6,w59,w155,w191,w273,w382,w550,w588] node1945)
noncomputable def node1929 : BT := (BT.nd node1919 [6,w56,w59,w155,w191,w382,w472] node1940)
noncomputable def node1908 : BT := (BT.nd node1887 [6,w38,w155,w191,w273,w382,w472,w652] node1929)
noncomputable def node1956 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w66,w155,w191,w273,w382,w472,w588] BT.lf) [6,w69,w155,w191,w273,w382,w472,w588] BT.lf) [6,w73,w155,w191,w273,w382,w472,w588] (BT.nd (BT.nd BT.lf [6,w76,w155,w191,w273,w382,w472,w588] BT.lf) [6,w78,w155,w191,w273,w382,w472,w588] BT.lf)) [6,w79,w82,w155,w191,w273,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [6,w79,w82,w155,w273,w382,w472] BT.lf) [6,w79,w155,w191,w273,w382,w472] BT.lf) [6,w79,w155,w191,w273,w382,w472,w588] (BT.nd BT.lf [6,w82,w106,w273,w382,w472,w588] BT.lf)))
noncomputable def node1966 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w82,w140,w155,w273,w382,w472] BT.lf) [6,w82,w155,w191,w273,w382,w472,w588] BT.lf) [6,w82,w155,w191,w273,w382,w472,w637] (BT.nd BT.lf [6,w82,w155,w191,w273,w382,w472,w652] BT.lf)) [6,w82,w155,w191,w273,w382,w472,w678] (BT.nd (BT.nd (BT.nd BT.lf [6,w82,w155,w191,w273,w382,w550,w588] BT.lf) [6,w82,w155,w191,w273,w425,w472,w588] BT.lf) [6,w82,w155,w273,w382,w472,w588] (BT.nd BT.lf [6,w82,w155,w273,w382,w472,w637] BT.lf)))
noncomputable def node1961 : BT := (BT.nd node1956 [6,w82,w140,w155,w191,w273,w382,w472] node1966)
noncomputable def node1977 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w82,w155,w273,w382,w472,w678] BT.lf) [6,w82,w155,w273,w382,w550,w588] BT.lf) [6,w82,w155,w273,w425,w472,w588] (BT.nd (BT.nd BT.lf [6,w83,w155,w191,w273,w382,w472,w588] BT.lf) [6,w85,w155,w191,w273,w382,w472,w588] BT.lf)) [6,w88,w155,w191,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w92,w155,w191,w273,w382,w472,w588] BT.lf) [6,w93,w155,w191,w273,w382,w472,w588] BT.lf) [6,w97,w155,w191,w273,w382,w472,w588] (BT.nd BT.lf [6,w100,w106,w155,w191,w273,w472,w588] BT.lf)))
noncomputable def node1987 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w100,w155,w191,w273,w382,w472,w588] BT.lf) [6,w100,w155,w191,w273,w472,w588] BT.lf) [6,w103,w155,w191,w273,w382,w472,w588] (BT.nd BT.lf [6,w105,w155,w191,w273,w382,w472,w588] BT.lf)) [6,w106,w140,w155,w191,w273,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [6,w106,w140,w191,w273,w382,w472] BT.lf) [6,w106,w155,w191,w273,w382,w472,w588] BT.lf) [6,w106,w155,w191,w273,w382,w472,w610] (BT.nd BT.lf [6,w106,w155,w191,w273,w382,w472,w637] BT.lf)))
noncomputable def node1982 : BT := (BT.nd node1977 [6,w100,w106,w191,w273,w472,w588] node1987)
noncomputable def node1971 : BT := (BT.nd node1961 [6,w82,w155,w273,w382,w472,w652] node1982)
noncomputable def node1998 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w106,w155,w191,w273,w382,w472,w678] BT.lf) [6,w106,w155,w191,w273,w382,w550,w588] BT.lf) [6,w106,w155,w191,w273,w425,w472,w588] (BT.nd (BT.nd BT.lf [6,w106,w191,w273,w382,w472,w588] BT.lf) [6,w106,w191,w273,w382,w472,w610] BT.lf)) [6,w106,w191,w273,w382,w472,w637] (BT.nd (BT.nd (BT.nd BT.lf [6,w106,w191,w273,w382,w472,w652] BT.lf) [6,w106,w191,w273,w382,w472,w678] BT.lf) [6,w106,w191,w273,w382,w550,w588] (BT.nd BT.lf [6,w106,w191,w273,w425,w472,w588] BT.lf)))
noncomputable def node2008 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w107,w155,w191,w273,w382,w472] BT.lf) [6,w107,w155,w191,w273,w382,w472,w588] BT.lf) [6,w109,w155,w191,w273,w382,w472,w588] (BT.nd BT.lf [6,w110,w155,w191,w273,w382,w472,w588] BT.lf)) [6,w114,w155,w191,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w119,w155,w191,w273,w382,w472,w588] BT.lf) [6,w120,w155,w191,w273,w382,w472,w588] BT.lf) [6,w121,w155,w191,w273,w382,w472,w588] (BT.nd BT.lf [6,w122,w155,w191,w273,w382,w472,w588] BT.lf)))
noncomputable def node2003 : BT := (BT.nd node1998 [6,w107,w140,w155,w191,w273,w382,w472] node2008)
noncomputable def node2019 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w123,w155,w191,w273,w382,w472,w588] BT.lf) [6,w124,w140,w155,w191,w273,w382,w472] BT.lf) [6,w124,w155,w191,w273,w382,w472,w588] (BT.nd (BT.nd BT.lf [6,w124,w155,w191,w273,w382,w472,w614] BT.lf) [6,w124,w155,w191,w273,w382,w472,w637] BT.lf)) [6,w124,w155,w191,w273,w382,w472,w652] (BT.nd (BT.nd (BT.nd BT.lf [6,w124,w155,w191,w273,w382,w472,w678] BT.lf) [6,w124,w155,w191,w273,w382,w495,w588] BT.lf) [6,w124,w155,w191,w273,w382,w550,w588] (BT.nd BT.lf [6,w124,w155,w191,w273,w401,w472,w588] BT.lf)))
noncomputable def node2029 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w124,w155,w191,w290,w382,w472,w588] BT.lf) [6,w125,w155,w191,w273,w382,w472,w588] BT.lf) [6,w126,w155,w191,w273,w382,w472,w588] (BT.nd BT.lf [6,w127,w140,w155,w191,w273,w382,w472] BT.lf)) [6,w127,w155,w191,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w128,w140,w155,w191,w273,w382,w472] BT.lf) [6,w128,w155,w191,w273,w382,w472,w588] BT.lf) [6,w128,w155,w191,w273,w382,w472,w617] (BT.nd BT.lf [6,w128,w155,w191,w273,w382,w472,w637] BT.lf)))
noncomputable def node2024 : BT := (BT.nd node2019 [6,w124,w155,w191,w273,w425,w472,w588] node2029)
noncomputable def node2013 : BT := (BT.nd node2003 [6,w123,w140,w155,w191,w273,w382,w472] node2024)
noncomputable def node1992 : BT := (BT.nd node1971 [6,w106,w155,w191,w273,w382,w472,w652] node2013)
noncomputable def node1950 : BT := (BT.nd node1908 [6,w65,w155,w191,w273,w382,w472,w588] node1992)
noncomputable def node1865 : BT := (BT.nd node1780 [6,w20,w155,w191,w273,w382,w472,w588] node1950)
noncomputable def node1695 : BT := (BT.nd node1526 [5,w155,w273,w327,w382,w472,w588] node1865)
noncomputable def node2040 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w128,w155,w191,w273,w382,w472,w678] BT.lf) [6,w128,w155,w191,w273,w382,w498,w588] BT.lf) [6,w128,w155,w191,w273,w382,w550,w588] (BT.nd (BT.nd BT.lf [6,w128,w155,w191,w273,w404,w472,w588] BT.lf) [6,w128,w155,w191,w273,w425,w472,w588] BT.lf)) [6,w128,w155,w216,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w129,w155,w191,w273,w382,w472,w588] BT.lf) [6,w130,w155,w191,w273,w382,w472,w588] BT.lf) [6,w131,w140,w155,w191,w273,w382,w472] (BT.nd BT.lf [6,w131,w155,w191,w273,w382,w472,w588] BT.lf)))
noncomputable def node2051 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w132,w155,w191,w273,w382,w472,w588] BT.lf) [6,w132,w155,w191,w273,w382,w472,w637] BT.lf) [6,w132,w155,w191,w273,w382,w472,w652] (BT.nd (BT.nd BT.lf [6,w132,w155,w191,w273,w382,w472,w678] BT.lf) [6,w132,w155,w191,w273,w382,w550,w588] BT.lf)) [6,w132,w155,w191,w273,w425,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w133,w155,w191,w273,w382,w472,w588] BT.lf) [6,w134,w155,w191,w273,w382,w472,w588] BT.lf) [6,w135,w140,w155,w191,w273,w382,w472] (BT.nd BT.lf [6,w135,w155,w191,w273,w382,w472,w588] BT.lf)))
noncomputable def node2045 : BT := (BT.nd node2040 [6,w132,w140,w155,w191,w273,w382,w472] node2051)
noncomputable def node2062 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w136,w155,w180,w191,w273,w382,w588] BT.lf) [6,w136,w155,w191,w273,w382,w472,w588] BT.lf) [6,w136,w155,w191,w273,w382,w472,w621] (BT.nd (BT.nd BT.lf [6,w136,w155,w191,w273,w382,w472,w637] BT.lf) [6,w136,w155,w191,w273,w382,w472,w652] BT.lf)) [6,w136,w155,w191,w273,w382,w472,w678] (BT.nd (BT.nd (BT.nd BT.lf [6,w136,w155,w191,w273,w382,w513,w588] BT.lf) [6,w136,w155,w191,w273,w382,w550,w588] BT.lf) [6,w136,w155,w191,w273,w382,w574,w588] (BT.nd BT.lf [6,w136,w155,w191,w273,w411,w472,w588] BT.lf)))
noncomputable def node2072 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w136,w155,w191,w308,w382,w472,w588] BT.lf) [6,w136,w155,w236,w273,w382,w472,w588] BT.lf) [6,w137,w155,w191,w273,w382,w472,w588] (BT.nd BT.lf [6,w138,w155,w191,w273,w382,w472,w588] BT.lf)) [6,w138,w155,w191,w273,w382,w550,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w139,w155,w191,w273,w382,w472,w588] BT.lf) [6,w140,w140,w155,w191,w273,w382,w472] BT.lf) [6,w140,w155,w155,w191,w273,w382,w472] (BT.nd BT.lf [6,w140,w155,w171,w191,w273,w382,w472] BT.lf)))
noncomputable def node2067 : BT := (BT.nd node2062 [6,w136,w155,w191,w273,w425,w472,w588] node2072)
noncomputable def node2056 : BT := (BT.nd node2045 [6,w136,w140,w155,w191,w273,w382,w472] node2067)
noncomputable def node2083 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w140,w155,w180,w191,w273,w382,w472] BT.lf) [6,w140,w155,w186,w191,w273,w382,w472] BT.lf) [6,w140,w155,w191,w191,w273,w382,w472] (BT.nd (BT.nd BT.lf [6,w140,w155,w191,w244,w273,w382,w472] BT.lf) [6,w140,w155,w191,w253,w273,w382,w472] BT.lf)) [6,w140,w155,w191,w256,w273,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [6,w140,w155,w191,w263,w273,w382,w472] BT.lf) [6,w140,w155,w191,w268,w273,w382,w472] BT.lf) [6,w140,w155,w191,w273,w273,w382,w472] (BT.nd BT.lf [6,w140,w155,w191,w273,w313,w382,w472] BT.lf)))
noncomputable def node2093 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w140,w155,w191,w273,w343,w382,w472] BT.lf) [6,w140,w155,w191,w273,w368,w382,w472] BT.lf) [6,w140,w155,w191,w273,w375,w382,w472] (BT.nd BT.lf [6,w140,w155,w191,w273,w382,w382,w472] BT.lf)) [6,w140,w155,w191,w273,w382,w420,w472] (BT.nd (BT.nd (BT.nd BT.lf [6,w140,w155,w191,w273,w382,w425,w472] BT.lf) [6,w140,w155,w191,w273,w382,w441,w472] BT.lf) [6,w140,w155,w191,w273,w382,w459,w472] (BT.nd BT.lf [6,w140,w155,w191,w273,w382,w465,w472] BT.lf)))
noncomputable def node2088 : BT := (BT.nd node2083 [6,w140,w155,w191,w273,w321,w382,w472] node2093)
noncomputable def node2104 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w140,w155,w191,w273,w382,w472,w472] BT.lf) [6,w140,w155,w191,w273,w382,w472,w506] BT.lf) [6,w140,w155,w191,w273,w382,w472,w513] (BT.nd (BT.nd BT.lf [6,w140,w155,w191,w273,w382,w472,w527] BT.lf) [6,w140,w155,w191,w273,w382,w472,w550] BT.lf)) [6,w140,w155,w191,w273,w382,w472,w574] (BT.nd (BT.nd (BT.nd BT.lf [6,w140,w155,w191,w273,w382,w472,w588] BT.lf) [6,w140,w155,w191,w273,w382,w472,w624] BT.lf) [6,w140,w155,w191,w273,w382,w472,w637] (BT.nd BT.lf [6,w140,w155,w191,w273,w382,w472,w652] BT.lf)))
noncomputable def node2114 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w140,w155,w191,w273,w382,w472,w678] BT.lf) [6,w140,w155,w191,w273,w382,w506] BT.lf) [6,w140,w155,w191,w273,w382,w506,w588] (BT.nd BT.lf [6,w140,w155,w191,w273,w382,w550] BT.lf)) [6,w140,w155,w191,w273,w382,w550,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w140,w155,w191,w273,w420,w472] BT.lf) [6,w140,w155,w191,w273,w420,w472,w588] BT.lf) [6,w140,w155,w191,w273,w425,w472] (BT.nd BT.lf [6,w140,w155,w191,w273,w425,w472,w588] BT.lf)))
noncomputable def node2109 : BT := (BT.nd node2104 [6,w140,w155,w191,w273,w382,w472,w669] node2114)
noncomputable def node2098 : BT := (BT.nd node2088 [6,w140,w155,w191,w273,w382,w472] node2109)
noncomputable def node2077 : BT := (BT.nd node2056 [6,w140,w155,w176,w191,w273,w382,w472] node2098)
noncomputable def node2125 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w140,w155,w191,w313,w382,w472,w588] BT.lf) [6,w140,w155,w244,w273,w382,w472] BT.lf) [6,w140,w155,w244,w273,w382,w472,w588] (BT.nd (BT.nd BT.lf [6,w144,w155,w191,w273,w382,w472] BT.lf) [6,w144,w155,w191,w273,w382,w472,w588] BT.lf)) [6,w144,w155,w191,w273,w382,w472,w637] (BT.nd (BT.nd (BT.nd BT.lf [6,w147,w155,w191,w273,w382,w472] BT.lf) [6,w147,w155,w191,w273,w382,w472,w588] BT.lf) [6,w147,w155,w191,w273,w382,w472,w652] (BT.nd BT.lf [6,w150,w155,w191,w273,w382,w472,w588] BT.lf)))
noncomputable def node2136 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w151,w155,w191,w273,w382,w472,w588] BT.lf) [6,w151,w155,w191,w273,w382,w472,w678] BT.lf) [6,w155,w155,w191,w273,w382,w472,w588] (BT.nd (BT.nd BT.lf [6,w155,w155,w191,w273,w382,w472,w637] BT.lf) [6,w155,w155,w191,w273,w382,w472,w652] BT.lf)) [6,w155,w155,w191,w273,w382,w472,w678] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w155,w191,w273,w382,w550,w588] BT.lf) [6,w155,w155,w191,w273,w425,w472,w588] BT.lf) [6,w155,w156,w191,w273,w382,w472,w588] (BT.nd BT.lf [6,w155,w158,w191,w273,w382,w472,w588] BT.lf)))
noncomputable def node2130 : BT := (BT.nd node2125 [6,w151,w155,w191,w273,w382,w472] node2136)
noncomputable def node2147 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w161,w191,w273,w472,w588] BT.lf) [6,w155,w165,w191,w273,w382,w472,w588] BT.lf) [6,w155,w167,w191,w273,w382,w472,w588] (BT.nd (BT.nd BT.lf [6,w155,w168,w191,w273,w382,w472,w588] BT.lf) [6,w155,w169,w191,w273,w382,w472,w588] BT.lf)) [6,w155,w170,w191,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w171,w191,w273,w382,w472,w588] BT.lf) [6,w155,w171,w191,w273,w382,w472,w627] BT.lf) [6,w155,w171,w191,w273,w382,w472,w637] (BT.nd BT.lf [6,w155,w171,w191,w273,w382,w472,w652] BT.lf)))
noncomputable def node2157 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w171,w191,w273,w382,w517,w588] BT.lf) [6,w155,w171,w191,w273,w382,w550,w588] BT.lf) [6,w155,w171,w191,w273,w425,w472,w588] (BT.nd BT.lf [6,w155,w171,w191,w273,w428,w472,w588] BT.lf)) [6,w155,w171,w191,w343,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w173,w191,w273,w382,w472,w588] BT.lf) [6,w155,w174,w191,w273,w382,w472,w588] BT.lf) [6,w155,w175,w191,w273,w382,w472,w588] (BT.nd BT.lf [6,w155,w176,w191,w256,w273,w472,w588] BT.lf)))
noncomputable def node2152 : BT := (BT.nd node2147 [6,w155,w171,w191,w273,w382,w472,w678] node2157)
noncomputable def node2141 : BT := (BT.nd node2130 [6,w155,w161,w191,w273,w382,w472,w588] node2152)
noncomputable def node2168 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w176,w191,w273,w382,w472,w630] BT.lf) [6,w155,w176,w191,w273,w382,w472,w637] BT.lf) [6,w155,w176,w191,w273,w382,w472,w652] (BT.nd (BT.nd BT.lf [6,w155,w176,w191,w273,w382,w472,w678] BT.lf) [6,w155,w176,w191,w273,w382,w521,w588] BT.lf)) [6,w155,w176,w191,w273,w382,w550,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w176,w191,w273,w425,w472,w588] BT.lf) [6,w155,w176,w191,w273,w441,w472,w588] BT.lf) [6,w155,w176,w191,w331,w382,w472,w588] (BT.nd BT.lf [6,w155,w177,w191,w273,w382,w472,w588] BT.lf)))
noncomputable def node2178 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w178,w191,w273,w382,w472,w588] BT.lf) [6,w155,w179,w191,w273,w382,w472,w588] BT.lf) [6,w155,w180,w191,w273,w382,w472,w588] (BT.nd BT.lf [6,w155,w180,w191,w273,w382,w472,w633] BT.lf)) [6,w155,w180,w191,w273,w382,w472,w637] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w180,w191,w273,w382,w472,w652] BT.lf) [6,w155,w180,w191,w273,w382,w472,w678] BT.lf) [6,w155,w180,w191,w273,w382,w527,w588] (BT.nd BT.lf [6,w155,w180,w191,w273,w382,w550,w588] BT.lf)))
noncomputable def node2173 : BT := (BT.nd node2168 [6,w155,w177,w191,w273,w425,w472,w588] node2178)
noncomputable def node2189 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w180,w191,w273,w382,w678] BT.lf) [6,w155,w180,w191,w273,w425,w472,w588] BT.lf) [6,w155,w180,w191,w273,w434,w472,w588] (BT.nd (BT.nd BT.lf [6,w155,w180,w191,w336,w382,w472,w588] BT.lf) [6,w155,w183,w191,w273,w382,w472,w588] BT.lf)) [6,w155,w184,w191,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w184,w191,w273,w382,w550,w588] BT.lf) [6,w155,w185,w191,w273,w382,w472,w588] BT.lf) [6,w155,w186,w191,w273,w382,w472,w588] (BT.nd BT.lf [6,w155,w186,w191,w273,w382,w472,w637] BT.lf)))
noncomputable def node2199 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w186,w191,w273,w382,w472,w678] BT.lf) [6,w155,w186,w191,w273,w382,w550,w588] BT.lf) [6,w155,w186,w191,w273,w425,w472,w588] (BT.nd BT.lf [6,w155,w187,w191,w273,w382,w472,w588] BT.lf)) [6,w155,w188,w191,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w188,w191,w273,w382,w472,w652] BT.lf) [6,w155,w189,w191,w273,w382,w472,w588] BT.lf) [6,w155,w190,w191,w273,w382,w472,w588] (BT.nd BT.lf [6,w155,w190,w191,w273,w382,w472,w678] BT.lf)))
noncomputable def node2194 : BT := (BT.nd node2189 [6,w155,w186,w191,w273,w382,w472,w652] node2199)
noncomputable def node2183 : BT := (BT.nd node2173 [6,w155,w180,w191,w273,w382,w588,w678] node2194)
noncomputable def node2162 : BT := (BT.nd node2141 [6,w155,w176,w191,w273,w382,w472,w588] node2183)
noncomputable def node2119 : BT := (BT.nd node2077 [6,w140,w155,w191,w313,w382,w472] node2162)
noncomputable def node2210 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w191,w273,w382,w472,w637] BT.lf) [6,w155,w191,w191,w273,w382,w472,w652] BT.lf) [6,w155,w191,w191,w273,w382,w472,w678] (BT.nd (BT.nd BT.lf [6,w155,w191,w191,w273,w382,w550,w588] BT.lf) [6,w155,w191,w191,w273,w425,w472,w588] BT.lf)) [6,w155,w191,w192,w273,w382,w472] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w192,w273,w382,w472,w588] BT.lf) [6,w155,w191,w196,w273,w382,w472,w588] BT.lf) [6,w155,w191,w197,w273,w382,w472,w588] (BT.nd BT.lf [6,w155,w191,w202,w273,w382,w472,w588] BT.lf)))
noncomputable def node2221 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w206,w273,w382,w472,w588] BT.lf) [6,w155,w191,w212,w273,w382,w472,w588] BT.lf) [6,w155,w191,w216,w273,w382,w472,w588] (BT.nd (BT.nd BT.lf [6,w155,w191,w218,w273,w382,w472,w588] BT.lf) [6,w155,w191,w223,w273,w382,w472,w588] BT.lf)) [6,w155,w191,w226,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w229,w253,w273,w382,w588] BT.lf) [6,w155,w191,w229,w273,w382,w472,w588] BT.lf) [6,w155,w191,w229,w273,w382,w588] (BT.nd BT.lf [6,w155,w191,w234,w273,w382,w472,w588] BT.lf)))
noncomputable def node2215 : BT := (BT.nd node2210 [6,w155,w191,w204,w273,w382,w472,w588] node2221)
noncomputable def node2232 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w242,w253,w273,w382,w472] BT.lf) [6,w155,w191,w242,w273,w382,w472] BT.lf) [6,w155,w191,w242,w273,w382,w472,w588] (BT.nd (BT.nd BT.lf [6,w155,w191,w243,w273,w382,w472,w588] BT.lf) [6,w155,w191,w244,w273,w382,w472] BT.lf)) [6,w155,w191,w244,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w253,w273,w382,w472,w588] BT.lf) [6,w155,w191,w253,w273,w382,w472,w637] BT.lf) [6,w155,w191,w253,w273,w382,w472,w652] (BT.nd BT.lf [6,w155,w191,w253,w273,w382,w472,w678] BT.lf)))
noncomputable def node2242 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w253,w273,w425,w472,w588] BT.lf) [6,w155,w191,w254,w273,w382,w472,w588] BT.lf) [6,w155,w191,w255,w273,w382,w472,w588] (BT.nd BT.lf [6,w155,w191,w256,w273,w382,w472,w588] BT.lf)) [6,w155,w191,w256,w273,w382,w472,w637] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w256,w273,w382,w472,w645] BT.lf) [6,w155,w191,w256,w273,w382,w472,w652] BT.lf) [6,w155,w191,w256,w273,w382,w472,w678] (BT.nd BT.lf [6,w155,w191,w256,w273,w382,w541,w588] BT.lf)))
noncomputable def node2237 : BT := (BT.nd node2232 [6,w155,w191,w253,w273,w382,w550,w588] node2242)
noncomputable def node2226 : BT := (BT.nd node2215 [6,w155,w191,w236,w273,w382,w472,w588] node2237)
noncomputable def node2253 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w256,w273,w425,w472,w588] BT.lf) [6,w155,w191,w256,w273,w459,w472,w588] BT.lf) [6,w155,w191,w256,w273,w472,w574,w588] (BT.nd (BT.nd BT.lf [6,w155,w191,w256,w382,w472,w550,w588] BT.lf) [6,w155,w191,w256,w382,w550,w588] BT.lf)) [6,w155,w191,w259,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w259,w273,w425,w472,w588] BT.lf) [6,w155,w191,w260,w273,w382,w472,w588] BT.lf) [6,w155,w191,w262,w273,w382,w472,w588] (BT.nd BT.lf [6,w155,w191,w263,w273,w382,w472,w588] BT.lf)))
noncomputable def node2263 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w263,w273,w382,w472,w648] BT.lf) [6,w155,w191,w263,w273,w382,w472,w652] BT.lf) [6,w155,w191,w263,w273,w382,w472,w678] (BT.nd BT.lf [6,w155,w191,w263,w273,w382,w550,w588] BT.lf)) [6,w155,w191,w263,w273,w425,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w265,w273,w382,w472,w588] BT.lf) [6,w155,w191,w266,w273,w382,w472,w588] BT.lf) [6,w155,w191,w267,w273,w382,w472,w588] (BT.nd BT.lf [6,w155,w191,w268,w273,w382,w472,w588] BT.lf)))
noncomputable def node2258 : BT := (BT.nd node2253 [6,w155,w191,w263,w273,w382,w472,w637] node2263)
noncomputable def node2274 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w268,w273,w382,w472,w652] BT.lf) [6,w155,w191,w268,w273,w382,w472,w678] BT.lf) [6,w155,w191,w268,w273,w382,w546,w588] (BT.nd (BT.nd BT.lf [6,w155,w191,w268,w273,w382,w550,w588] BT.lf) [6,w155,w191,w268,w273,w425,w472,w588] BT.lf)) [6,w155,w191,w269,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w270,w273,w382,w472,w588] BT.lf) [6,w155,w191,w270,w273,w382,w472,w637] BT.lf) [6,w155,w191,w271,w273,w382,w472,w588] (BT.nd BT.lf [6,w155,w191,w272,w273,w382,w472,w588] BT.lf)))
noncomputable def node2284 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w273,w382,w472,w588] BT.lf) [6,w155,w191,w273,w273,w382,w472,w637] BT.lf) [6,w155,w191,w273,w273,w382,w472,w652] (BT.nd BT.lf [6,w155,w191,w273,w273,w382,w472,w678] BT.lf)) [6,w155,w191,w273,w273,w382,w550,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w273,w425,w472,w588] BT.lf) [6,w155,w191,w273,w274,w382,w472] BT.lf) [6,w155,w191,w273,w274,w382,w472,w588] (BT.nd BT.lf [6,w155,w191,w273,w278,w382,w472,w588] BT.lf)))
noncomputable def node2279 : BT := (BT.nd node2274 [6,w155,w191,w272,w273,w382,w472,w678] node2284)
noncomputable def node2268 : BT := (BT.nd node2258 [6,w155,w191,w268,w273,w382,w472,w637] node2279)
noncomputable def node2247 : BT := (BT.nd node2226 [6,w155,w191,w256,w273,w382,w550,w588] node2268)
noncomputable def node2295 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w280,w382,w472,w588] BT.lf) [6,w155,w191,w273,w284,w382,w472,w588] BT.lf) [6,w155,w191,w273,w286,w382,w472,w588] (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w290,w382,w472,w588] BT.lf) [6,w155,w191,w273,w292,w382,w472,w588] BT.lf)) [6,w155,w191,w273,w297,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w301,w382,w472,w588] BT.lf) [6,w155,w191,w273,w303,w382,w472,w588] BT.lf) [6,w155,w191,w273,w306,w382,w472,w588] (BT.nd BT.lf [6,w155,w191,w273,w308,w382,w472,w588] BT.lf)))
noncomputable def node2305 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w310,w382,w472] BT.lf) [6,w155,w191,w273,w310,w382,w472,w588] BT.lf) [6,w155,w191,w273,w311,w382,w472,w588] (BT.nd BT.lf [6,w155,w191,w273,w313,w382,w472] BT.lf)) [6,w155,w191,w273,w313,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w321,w382,w472,w588] BT.lf) [6,w155,w191,w273,w321,w382,w472,w637] BT.lf) [6,w155,w191,w273,w321,w382,w472,w652] (BT.nd BT.lf [6,w155,w191,w273,w321,w382,w472,w678] BT.lf)))
noncomputable def node2300 : BT := (BT.nd node2295 [6,w155,w191,w273,w310,w321,w382,w472] node2305)
noncomputable def node2316 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w321,w425,w472,w588] BT.lf) [6,w155,w191,w273,w323,w343,w472,w588] BT.lf) [6,w155,w191,w273,w323,w382,w472,w588] (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w323,w472,w588] BT.lf) [6,w155,w191,w273,w327,w382,w472,w588] BT.lf)) [6,w155,w191,w273,w331,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w333,w382,w472,w588] BT.lf) [6,w155,w191,w273,w334,w382,w472,w588] BT.lf) [6,w155,w191,w273,w336,w382,w472,w588] (BT.nd BT.lf [6,w155,w191,w273,w340,w382,w472,w588] BT.lf)))
noncomputable def node2326 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w342,w382,w472,w588] BT.lf) [6,w155,w191,w273,w343,w382,w472,w588] BT.lf) [6,w155,w191,w273,w343,w382,w472,w637] (BT.nd BT.lf [6,w155,w191,w273,w343,w382,w472,w652] BT.lf)) [6,w155,w191,w273,w343,w382,w472,w664] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w343,w382,w472,w678] BT.lf) [6,w155,w191,w273,w343,w382,w550,w588] BT.lf) [6,w155,w191,w273,w343,w425,w472,w588] (BT.nd BT.lf [6,w155,w191,w273,w366,w382,w472,w588] BT.lf)))
noncomputable def node2321 : BT := (BT.nd node2316 [6,w155,w191,w273,w341,w382,w472,w588] node2326)
noncomputable def node2310 : BT := (BT.nd node2300 [6,w155,w191,w273,w321,w382,w550,w588] node2321)
noncomputable def node2337 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w368,w382,w472,w588] BT.lf) [6,w155,w191,w273,w368,w382,w472,w637] BT.lf) [6,w155,w191,w273,w368,w382,w472,w652] (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w368,w382,w472,w666] BT.lf) [6,w155,w191,w273,w368,w382,w472,w678] BT.lf)) [6,w155,w191,w273,w368,w382,w550,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w368,w425,w472,w588] BT.lf) [6,w155,w191,w273,w371,w382,w472,w588] BT.lf) [6,w155,w191,w273,w372,w382,w472,w588] (BT.nd BT.lf [6,w155,w191,w273,w373,w382,w472,w588] BT.lf)))
noncomputable def node2347 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w375,w382,w472,w588] BT.lf) [6,w155,w191,w273,w375,w382,w472,w637] BT.lf) [6,w155,w191,w273,w375,w382,w472,w652] (BT.nd BT.lf [6,w155,w191,w273,w375,w382,w472,w678] BT.lf)) [6,w155,w191,w273,w375,w382,w550,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w375,w382,w571,w588] BT.lf) [6,w155,w191,w273,w375,w425,w472,w588] BT.lf) [6,w155,w191,w273,w377,w382,w472,w588] (BT.nd BT.lf [6,w155,w191,w273,w378,w382,w472,w588] BT.lf)))
noncomputable def node2342 : BT := (BT.nd node2337 [6,w155,w191,w273,w373,w382,w550,w588] node2347)
noncomputable def node2358 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w379,w382,w472,w588] BT.lf) [6,w155,w191,w273,w379,w382,w472,w652] BT.lf) [6,w155,w191,w273,w381,w382,w472,w588] (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w381,w382,w472,w678] BT.lf) [6,w155,w191,w273,w382,w382,w472,w588] BT.lf)) [6,w155,w191,w273,w382,w382,w472,w637] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w382,w472,w652] BT.lf) [6,w155,w191,w273,w382,w382,w472,w678] BT.lf) [6,w155,w191,w273,w382,w382,w550,w588] (BT.nd BT.lf [6,w155,w191,w273,w382,w384,w472,w588] BT.lf)))
noncomputable def node2368 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w393,w472,w588] BT.lf) [6,w155,w191,w273,w382,w396,w472,w588] BT.lf) [6,w155,w191,w273,w382,w397,w472,w588] (BT.nd BT.lf [6,w155,w191,w273,w382,w401,w472,w588] BT.lf)) [6,w155,w191,w273,w382,w404,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w406,w472,w588] BT.lf) [6,w155,w191,w273,w382,w409,w472,w588] BT.lf) [6,w155,w191,w273,w382,w411,w472,w588] (BT.nd BT.lf [6,w155,w191,w273,w382,w414,w425,w472] BT.lf)))
noncomputable def node2363 : BT := (BT.nd node2358 [6,w155,w191,w273,w382,w387,w472,w588] node2368)
noncomputable def node2352 : BT := (BT.nd node2342 [6,w155,w191,w273,w378,w382,w472,w637] node2363)
noncomputable def node2331 : BT := (BT.nd node2310 [6,w155,w191,w273,w367,w382,w472,w588] node2352)
noncomputable def node2289 : BT := (BT.nd node2247 [6,w155,w191,w273,w278,w382,w588] node2331)
noncomputable def node2204 : BT := (BT.nd node2119 [6,w155,w191,w191,w273,w382,w472,w588] node2289)
noncomputable def node2379 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w414,w472,w588] BT.lf) [6,w155,w191,w273,w382,w416,w472,w588] BT.lf) [6,w155,w191,w273,w382,w420,w472,w588] (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w425,w472,w588] BT.lf) [6,w155,w191,w273,w382,w425,w472,w637] BT.lf)) [6,w155,w191,w273,w382,w425,w472,w652] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w425,w472,w678] BT.lf) [6,w155,w191,w273,w382,w425,w550,w588] BT.lf) [6,w155,w191,w273,w382,w428,w472,w588] (BT.nd BT.lf [6,w155,w191,w273,w382,w431,w472,w588] BT.lf)))
noncomputable def node2390 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w434,w472,w588] BT.lf) [6,w155,w191,w273,w382,w438,w472,w588] BT.lf) [6,w155,w191,w273,w382,w439,w472,w588] (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w440,w472,w588] BT.lf) [6,w155,w191,w273,w382,w441,w472,w588] BT.lf)) [6,w155,w191,w273,w382,w441,w472,w637] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w441,w472,w652] BT.lf) [6,w155,w191,w273,w382,w441,w472,w678] BT.lf) [6,w155,w191,w273,w382,w441,w550,w588] (BT.nd BT.lf [6,w155,w191,w273,w382,w452,w472,w588] BT.lf)))
noncomputable def node2384 : BT := (BT.nd node2379 [6,w155,w191,w273,w382,w432,w472,w588] node2390)
noncomputable def node2401 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w454,w472,w588] BT.lf) [6,w155,w191,w273,w382,w455,w472,w588] BT.lf) [6,w155,w191,w273,w382,w456,w472,w588] (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w457,w472,w588] BT.lf) [6,w155,w191,w273,w382,w458,w472,w588] BT.lf)) [6,w155,w191,w273,w382,w459,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w459,w472,w637] BT.lf) [6,w155,w191,w273,w382,w459,w472,w652] BT.lf) [6,w155,w191,w273,w382,w459,w472,w678] (BT.nd BT.lf [6,w155,w191,w273,w382,w459,w550,w588] BT.lf)))
noncomputable def node2411 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w464,w472,w588] BT.lf) [6,w155,w191,w273,w382,w465,w472,w588] BT.lf) [6,w155,w191,w273,w382,w465,w472,w637] (BT.nd BT.lf [6,w155,w191,w273,w382,w465,w472,w652] BT.lf)) [6,w155,w191,w273,w382,w465,w472,w678] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w465,w550,w588] BT.lf) [6,w155,w191,w273,w382,w467,w472,w588] BT.lf) [6,w155,w191,w273,w382,w468,w472,w588] (BT.nd BT.lf [6,w155,w191,w273,w382,w468,w472,w637] BT.lf)))
noncomputable def node2406 : BT := (BT.nd node2401 [6,w155,w191,w273,w382,w463,w472,w588] node2411)
noncomputable def node2395 : BT := (BT.nd node2384 [6,w155,w191,w273,w382,w453,w472,w588] node2406)
noncomputable def node2422 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w470,w472,w652] BT.lf) [6,w155,w191,w273,w382,w471,w472,w588] BT.lf) [6,w155,w191,w273,w382,w472,w472,w588] (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w472,w637] BT.lf) [6,w155,w191,w273,w382,w472,w472,w652] BT.lf)) [6,w155,w191,w273,w382,w472,w472,w678] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w474] BT.lf) [6,w155,w191,w273,w382,w472,w474,w588] BT.lf) [6,w155,w191,w273,w382,w472,w476,w588] (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w481,w588] BT.lf)))
noncomputable def node2432 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w491,w588] BT.lf) [6,w155,w191,w273,w382,w472,w495,w588] BT.lf) [6,w155,w191,w273,w382,w472,w498,w588] (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w501,w588] BT.lf)) [6,w155,w191,w273,w382,w472,w502] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w502,w513] BT.lf) [6,w155,w191,w273,w382,w472,w502,w588] BT.lf) [6,w155,w191,w273,w382,w472,w503,w588] (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w506] BT.lf)))
noncomputable def node2427 : BT := (BT.nd node2422 [6,w155,w191,w273,w382,w472,w488,w588] node2432)
noncomputable def node2443 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w513,w588] BT.lf) [6,w155,w191,w273,w382,w472,w513,w637] BT.lf) [6,w155,w191,w273,w382,w472,w513,w652] (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w513,w678] BT.lf) [6,w155,w191,w273,w382,w472,w517,w588] BT.lf)) [6,w155,w191,w273,w382,w472,w521,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w524,w588] BT.lf) [6,w155,w191,w273,w382,w472,w525,w588] BT.lf) [6,w155,w191,w273,w382,w472,w526,w588] (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w527,w588] BT.lf)))
noncomputable def node2453 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w527,w652] BT.lf) [6,w155,w191,w273,w382,w472,w527,w678] BT.lf) [6,w155,w191,w273,w382,w472,w527,w685] (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w539,w588] BT.lf)) [6,w155,w191,w273,w382,w472,w541,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w544,w588] BT.lf) [6,w155,w191,w273,w382,w472,w545,w588] BT.lf) [6,w155,w191,w273,w382,w472,w546,w588] (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w550,w588] BT.lf)))
noncomputable def node2448 : BT := (BT.nd node2443 [6,w155,w191,w273,w382,w472,w527,w637] node2453)
noncomputable def node2437 : BT := (BT.nd node2427 [6,w155,w191,w273,w382,w472,w506,w588] node2448)
noncomputable def node2416 : BT := (BT.nd node2395 [6,w155,w191,w273,w382,w470,w472,w588] node2437)
noncomputable def node2464 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w550,w652] BT.lf) [6,w155,w191,w273,w382,w472,w550,w678] BT.lf) [6,w155,w191,w273,w382,w472,w550,w687] (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w563,w588] BT.lf) [6,w155,w191,w273,w382,w472,w566,w588] BT.lf)) [6,w155,w191,w273,w382,w472,w569,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w570,w588] BT.lf) [6,w155,w191,w273,w382,w472,w571,w588] BT.lf) [6,w155,w191,w273,w382,w472,w574,w588] (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w574,w637] BT.lf)))
noncomputable def node2475 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w574,w678] BT.lf) [6,w155,w191,w273,w382,w472,w581,w588] BT.lf) [6,w155,w191,w273,w382,w472,w582,w588] (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w585,w588] BT.lf) [6,w155,w191,w273,w382,w472,w588] BT.lf)) [6,w155,w191,w273,w382,w472,w588,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w588,w592] BT.lf) [6,w155,w191,w273,w382,w472,w588,w597] BT.lf) [6,w155,w191,w273,w382,w472,w588,w601] (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w588,w605] BT.lf)))
noncomputable def node2469 : BT := (BT.nd node2464 [6,w155,w191,w273,w382,w472,w574,w652] node2475)
noncomputable def node2486 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w588,w614] BT.lf) [6,w155,w191,w273,w382,w472,w588,w617] BT.lf) [6,w155,w191,w273,w382,w472,w588,w620] (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w588,w621] BT.lf) [6,w155,w191,w273,w382,w472,w588,w624] BT.lf)) [6,w155,w191,w273,w382,w472,w588,w627] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w588,w630] BT.lf) [6,w155,w191,w273,w382,w472,w588,w633] BT.lf) [6,w155,w191,w273,w382,w472,w588,w637] (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w588,w643] BT.lf)))
noncomputable def node2496 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w588,w648] BT.lf) [6,w155,w191,w273,w382,w472,w588,w652] BT.lf) [6,w155,w191,w273,w382,w472,w588,w657] (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w588,w664] BT.lf)) [6,w155,w191,w273,w382,w472,w588,w666] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w588,w669] BT.lf) [6,w155,w191,w273,w382,w472,w588,w671] BT.lf) [6,w155,w191,w273,w382,w472,w588,w674] (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w588,w677] BT.lf)))
noncomputable def node2491 : BT := (BT.nd node2486 [6,w155,w191,w273,w382,w472,w588,w645] node2496)
noncomputable def node2480 : BT := (BT.nd node2469 [6,w155,w191,w273,w382,w472,w588,w610] node2491)
noncomputable def node2507 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w588,w682] BT.lf) [6,w155,w191,w273,w382,w472,w588,w685] BT.lf) [6,w155,w191,w273,w382,w472,w588,w687] (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w588,w689] BT.lf) [6,w155,w191,w273,w382,w472,w588,w690] BT.lf)) [6,w155,w191,w273,w382,w472,w610] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w614] BT.lf) [6,w155,w191,w273,w382,w472,w617] BT.lf) [6,w155,w191,w273,w382,w472,w621] (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w624,w637] BT.lf)))
noncomputable def node2517 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w624,w678] BT.lf) [6,w155,w191,w273,w382,w472,w627] BT.lf) [6,w155,w191,w273,w382,w472,w630] (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w633] BT.lf)) [6,w155,w191,w273,w382,w472,w637] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w637,w637] BT.lf) [6,w155,w191,w273,w382,w472,w637,w643] BT.lf) [6,w155,w191,w273,w382,w472,w637,w652] (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w637,w664] BT.lf)))
noncomputable def node2512 : BT := (BT.nd node2507 [6,w155,w191,w273,w382,w472,w624,w652] node2517)
noncomputable def node2528 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w637,w674] BT.lf) [6,w155,w191,w273,w382,w472,w637,w678] BT.lf) [6,w155,w191,w273,w382,w472,w637,w685] (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w645] BT.lf) [6,w155,w191,w273,w382,w472,w648] BT.lf)) [6,w155,w191,w273,w382,w472,w652] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w652,w652] BT.lf) [6,w155,w191,w273,w382,w472,w652,w657] BT.lf) [6,w155,w191,w273,w382,w472,w652,w664] (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w652,w669] BT.lf)))
noncomputable def node2538 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w652,w678] BT.lf) [6,w155,w191,w273,w382,w472,w652,w687] BT.lf) [6,w155,w191,w273,w382,w472,w664] (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w666] BT.lf)) [6,w155,w191,w273,w382,w472,w669,w678] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w678] BT.lf) [6,w155,w191,w273,w382,w472,w678,w678] BT.lf) [6,w155,w191,w273,w382,w472,w678,w682] (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w678,w685] BT.lf)))
noncomputable def node2533 : BT := (BT.nd node2528 [6,w155,w191,w273,w382,w472,w652,w677] node2538)
noncomputable def node2522 : BT := (BT.nd node2512 [6,w155,w191,w273,w382,w472,w637,w669] node2533)
noncomputable def node2501 : BT := (BT.nd node2480 [6,w155,w191,w273,w382,w472,w588,w678] node2522)
noncomputable def node2458 : BT := (BT.nd node2416 [6,w155,w191,w273,w382,w472,w550,w637] node2501)
noncomputable def node2549 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w472,w678,w689] BT.lf) [6,w155,w191,w273,w382,w472,w685] BT.lf) [6,w155,w191,w273,w382,w472,w687] (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w495,w588] BT.lf) [6,w155,w191,w273,w382,w498,w588] BT.lf)) [6,w155,w191,w273,w382,w506] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w506,w588] BT.lf) [6,w155,w191,w273,w382,w513,w527,w588] BT.lf) [6,w155,w191,w273,w382,w513,w550,w588] (BT.nd BT.lf [6,w155,w191,w273,w382,w513,w588,w678] BT.lf)))
noncomputable def node2560 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w517,w588] BT.lf) [6,w155,w191,w273,w382,w521,w588] BT.lf) [6,w155,w191,w273,w382,w527,w550,w588] (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w527,w574,w588] BT.lf) [6,w155,w191,w273,w382,w541,w588] BT.lf)) [6,w155,w191,w273,w382,w544,w550,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w546,w588] BT.lf) [6,w155,w191,w273,w382,w550,w550,w588] BT.lf) [6,w155,w191,w273,w382,w550,w563,w588] (BT.nd BT.lf [6,w155,w191,w273,w382,w550,w566,w588] BT.lf)))
noncomputable def node2554 : BT := (BT.nd node2549 [6,w155,w191,w273,w382,w513,w678] node2560)
noncomputable def node2571 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w550,w585,w588] BT.lf) [6,w155,w191,w273,w382,w550,w588] BT.lf) [6,w155,w191,w273,w382,w550,w588,w588] (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w550,w588,w624] BT.lf) [6,w155,w191,w273,w382,w550,w588,w637] BT.lf)) [6,w155,w191,w273,w382,w550,w588,w652] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w550,w588,w669] BT.lf) [6,w155,w191,w273,w382,w550,w588,w678] BT.lf) [6,w155,w191,w273,w382,w550,w588,w687] (BT.nd BT.lf [6,w155,w191,w273,w382,w550,w637] BT.lf)))
noncomputable def node2581 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w382,w550,w678] BT.lf) [6,w155,w191,w273,w382,w550,w687] BT.lf) [6,w155,w191,w273,w382,w571,w588] (BT.nd BT.lf [6,w155,w191,w273,w382,w574,w588,w678] BT.lf)) [6,w155,w191,w273,w382,w574,w678] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w401,w472,w588] BT.lf) [6,w155,w191,w273,w404,w472,w588] BT.lf) [6,w155,w191,w273,w406,w425,w472,w588] (BT.nd BT.lf [6,w155,w191,w273,w411,w472,w588] BT.lf)))
noncomputable def node2576 : BT := (BT.nd node2571 [6,w155,w191,w273,w382,w550,w652] node2581)
noncomputable def node2565 : BT := (BT.nd node2554 [6,w155,w191,w273,w382,w550,w574,w588] node2576)
noncomputable def node2592 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w414,w425,w472,w588] BT.lf) [6,w155,w191,w273,w420,w472,w588] BT.lf) [6,w155,w191,w273,w425,w425,w472,w588] (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w425,w441,w472,w588] BT.lf) [6,w155,w191,w273,w425,w452,w472,w588] BT.lf)) [6,w155,w191,w273,w425,w459,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w425,w463,w472,w588] BT.lf) [6,w155,w191,w273,w425,w465,w472,w588] BT.lf) [6,w155,w191,w273,w425,w472,w472,w588] (BT.nd BT.lf [6,w155,w191,w273,w425,w472,w513,w588] BT.lf)))
noncomputable def node2602 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w425,w472,w550,w588] BT.lf) [6,w155,w191,w273,w425,w472,w574,w588] BT.lf) [6,w155,w191,w273,w425,w472,w581,w588] (BT.nd BT.lf [6,w155,w191,w273,w425,w472,w588] BT.lf)) [6,w155,w191,w273,w425,w472,w588,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w425,w472,w588,w624] BT.lf) [6,w155,w191,w273,w425,w472,w588,w637] BT.lf) [6,w155,w191,w273,w425,w472,w588,w652] (BT.nd BT.lf [6,w155,w191,w273,w425,w472,w588,w669] BT.lf)))
noncomputable def node2597 : BT := (BT.nd node2592 [6,w155,w191,w273,w425,w472,w527,w588] node2602)
noncomputable def node2613 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w425,w472,w588,w678] BT.lf) [6,w155,w191,w273,w425,w472,w637] BT.lf) [6,w155,w191,w273,w425,w472,w652] (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w425,w472,w678] BT.lf) [6,w155,w191,w273,w425,w550,w588] BT.lf)) [6,w155,w191,w273,w428,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w273,w434,w472,w588] BT.lf) [6,w155,w191,w273,w441,w459,w472,w588] BT.lf) [6,w155,w191,w273,w441,w472,w574,w588] (BT.nd BT.lf [6,w155,w191,w290,w382,w472,w588] BT.lf)))
noncomputable def node2623 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w313,w382,w472] BT.lf) [6,w155,w191,w313,w382,w472,w588] BT.lf) [6,w155,w191,w321,w343,w382,w472,w588] (BT.nd BT.lf [6,w155,w191,w321,w382,w472,w550,w588] BT.lf)) [6,w155,w191,w321,w382,w472,w588,w652] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w321,w382,w472,w652] BT.lf) [6,w155,w191,w321,w382,w550,w588] BT.lf) [6,w155,w191,w331,w382,w472,w588] (BT.nd BT.lf [6,w155,w191,w336,w382,w472,w588] BT.lf)))
noncomputable def node2618 : BT := (BT.nd node2613 [6,w155,w191,w308,w382,w472,w588] node2623)
noncomputable def node2607 : BT := (BT.nd node2597 [6,w155,w191,w273,w425,w472,w588,w671] node2618)
noncomputable def node2586 : BT := (BT.nd node2565 [6,w155,w191,w273,w414,w425,w472] node2607)
noncomputable def node2634 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w191,w343,w382,w472,w550,w588] BT.lf) [6,w155,w191,w343,w382,w550,w588] BT.lf) [6,w155,w216,w273,w382,w472,w588] (BT.nd (BT.nd BT.lf [6,w155,w236,w273,w382,w472,w588] BT.lf) [6,w155,w244,w273,w382,w472] BT.lf)) [6,w155,w244,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w253,w273,w343,w382,w472,w588] BT.lf) [6,w155,w253,w273,w382,w472,w527,w588] BT.lf) [6,w155,w253,w273,w382,w472,w588,w637] (BT.nd BT.lf [6,w155,w253,w273,w382,w472,w637] BT.lf)))
noncomputable def node2644 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w155,w273,w327,w382,w472,w588] BT.lf) [6,w155,w273,w343,w382,w441,w472,w588] BT.lf) [6,w171,w191,w212,w273,w382,w472,w588] (BT.nd BT.lf [6,w176,w191,w223,w273,w382,w472,w588] BT.lf)) [6,w180,w191,w234,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [6,w191,w212,w273,w382,w472,w588] BT.lf) [6,w191,w223,w273,w382,w472,w588] BT.lf) [6,w191,w234,w273,w382,w472,w588] (BT.nd BT.lf [6,w191,w253,w273,w321,w382,w472,w588] BT.lf)))
noncomputable def node2639 : BT := (BT.nd node2634 [6,w155,w256,w273,w327,w382,w472,w588] node2644)
noncomputable def node2655 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w191,w253,w273,w382,w472,w513,w588] BT.lf) [6,w191,w253,w273,w425,w472,w588] BT.lf) [6,w191,w256,w273,w297,w382,w472,w588] (BT.nd (BT.nd BT.lf [6,w191,w273,w297,w382,w472,w588] BT.lf) [6,w191,w273,w321,w382,w425,w472,w588] BT.lf)) [6,w191,w273,w321,w425,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [7,w11,w155,w191,w273,w382,w472] BT.lf) [7,w11,w155,w191,w273,w382,w472,w588] BT.lf) [7,w27,w155,w191,w273,w382,w472,w588] (BT.nd BT.lf [7,w27,w155,w191,w273,w382,w588] BT.lf)))
noncomputable def node2665 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,w38,w155,w191,w273,w472,w588] BT.lf) [7,w59,w155,w191,w273,w382,w472,w588] BT.lf) [7,w59,w155,w191,w382,w472,w588] (BT.nd BT.lf [7,w82,w155,w191,w273,w382,w472,w588] BT.lf)) [7,w82,w155,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [7,w106,w155,w191,w273,w382,w472,w588] BT.lf) [7,w106,w191,w273,w382,w472,w588] BT.lf) [7,w124,w155,w191,w273,w382,w472,w588] (BT.nd BT.lf [7,w128,w155,w191,w273,w382,w472,w588] BT.lf)))
noncomputable def node2660 : BT := (BT.nd node2655 [7,w38,w155,w191,w273,w382,w472,w588] node2665)
noncomputable def node2649 : BT := (BT.nd node2639 [6,w191,w253,w273,w382,w425,w472,w588] node2660)
noncomputable def node2676 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,w136,w155,w191,w273,w382,w472,w588] BT.lf) [7,w140,w155,w191,w273,w382,w472] BT.lf) [7,w140,w155,w191,w273,w382,w472,w588] (BT.nd (BT.nd BT.lf [7,w155,w155,w191,w273,w382,w472,w588] BT.lf) [7,w155,w171,w191,w273,w382,w472,w588] BT.lf)) [7,w155,w176,w191,w273,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [7,w155,w180,w191,w273,w382,w472,w588] BT.lf) [7,w155,w186,w191,w273,w382,w472,w588] BT.lf) [7,w155,w191,w191,w273,w382,w472,w588] (BT.nd BT.lf [7,w155,w191,w253,w273,w382,w472,w588] BT.lf)))
noncomputable def node2686 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,w155,w191,w263,w273,w382,w472,w588] BT.lf) [7,w155,w191,w268,w273,w382,w472,w588] BT.lf) [7,w155,w191,w273,w273,w382,w472,w588] (BT.nd BT.lf [7,w155,w191,w273,w321,w382,w472,w588] BT.lf)) [7,w155,w191,w273,w343,w382,w472,w588] (BT.nd (BT.nd (BT.nd BT.lf [7,w155,w191,w273,w368,w382,w472,w588] BT.lf) [7,w155,w191,w273,w375,w382,w472,w588] BT.lf) [7,w155,w191,w273,w382,w382,w472,w588] (BT.nd BT.lf [7,w155,w191,w273,w382,w425,w472,w588] BT.lf)))
noncomputable def node2681 : BT := (BT.nd node2676 [7,w155,w191,w256,w273,w382,w472,w588] node2686)
noncomputable def node2697 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,w155,w191,w273,w382,w459,w472,w588] BT.lf) [7,w155,w191,w273,w382,w465,w472,w588] BT.lf) [7,w155,w191,w273,w382,w472,w472,w588] (BT.nd (BT.nd BT.lf [7,w155,w191,w273,w382,w472,w513,w588] BT.lf) [7,w155,w191,w273,w382,w472,w527,w588] BT.lf)) [7,w155,w191,w273,w382,w472,w550,w588] (BT.nd (BT.nd (BT.nd BT.lf [7,w155,w191,w273,w382,w472,w574,w588] BT.lf) [7,w155,w191,w273,w382,w472,w588] BT.lf) [7,w155,w191,w273,w382,w472,w588,w588] (BT.nd BT.lf [7,w155,w191,w273,w382,w472,w588,w624] BT.lf)))
noncomputable def node2707 : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,w155,w191,w273,w382,w472,w588,w652] BT.lf) [7,w155,w191,w273,w382,w472,w588,w669] BT.lf) [7,w155,w191,w273,w382,w472,w588,w678] (BT.nd BT.lf [7,w155,w191,w273,w382,w472,w637] BT.lf)) [7,w155,w191,w273,w382,w472,w652] (BT.nd (BT.nd (BT.nd BT.lf [7,w155,w191,w273,w382,w472,w678] BT.lf) [7,w155,w191,w273,w382,w550,w588] BT.lf) [7,w155,w191,w273,w425,w472,w588] (BT.nd BT.lf [8,w155,w191,w273,w382,w472,w588] BT.lf)))
noncomputable def node2702 : BT := (BT.nd node2697 [7,w155,w191,w273,w382,w472,w588,w637] node2707)
noncomputable def node2691 : BT := (BT.nd node2681 [7,w155,w191,w273,w382,w441,w472,w588] node2702)
noncomputable def node2670 : BT := (BT.nd node2649 [7,w132,w155,w191,w273,w382,w472,w588] node2691)
noncomputable def node2628 : BT := (BT.nd node2586 [6,w155,w191,w343,w382,w459,w472,w588] node2670)
noncomputable def node2543 : BT := (BT.nd node2458 [6,w155,w191,w273,w382,w472,w678,w687] node2628)
noncomputable def node2373 : BT := (BT.nd node2204 [6,w155,w191,w273,w382,w414,w472] node2543)
noncomputable def node2034 : BT := (BT.nd node1695 [6,w128,w155,w191,w273,w382,w472,w652] node2373)
noncomputable def node1356 : BT := (BT.nd node678 [5,w155,w191,w273,w414,w425,w550] node2034)

noncomputable def certTree : BT := node1356
noncomputable def validKey (k : List ℕ) := stepOK allBits targetBits distPairs monoPairs [] certTree k []
theorem joinValid (l r : BT) (k : List ℕ) (hl : l.toList.all validKey = true)
    (hk : validKey k = true) (hr : r.toList.all validKey = true) :
    (BT.nd l k r).toList.all validKey = true := by
  simp [BT.toList, List.all_append, hl, hk, hr]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node5 : node5.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node16 : node16.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node27 : node27.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node37 : node37.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node48 : node48.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node58 : node58.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node69 : node69.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node79 : node79.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node90 : node90.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node101 : node101.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node112 : node112.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node122 : node122.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node133 : node133.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node143 : node143.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node154 : node154.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node164 : node164.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node175 : node175.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node186 : node186.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node197 : node197.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node207 : node207.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node218 : node218.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node228 : node228.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node239 : node239.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node249 : node249.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node260 : node260.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node271 : node271.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node282 : node282.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node292 : node292.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node303 : node303.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node313 : node313.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node324 : node324.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node334 : node334.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node345 : node345.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node356 : node356.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node367 : node367.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node377 : node377.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node388 : node388.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node398 : node398.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node409 : node409.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node419 : node419.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node430 : node430.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node441 : node441.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node452 : node452.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node462 : node462.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node473 : node473.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node483 : node483.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node494 : node494.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node504 : node504.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node515 : node515.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node526 : node526.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node537 : node537.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node547 : node547.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node558 : node558.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node568 : node568.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node579 : node579.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node589 : node589.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node600 : node600.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node610 : node610.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node621 : node621.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node631 : node631.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node642 : node642.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node652 : node652.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node663 : node663.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node673 : node673.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node684 : node684.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node695 : node695.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node706 : node706.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node716 : node716.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node727 : node727.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node737 : node737.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node748 : node748.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node758 : node758.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node769 : node769.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node780 : node780.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node791 : node791.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node801 : node801.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node812 : node812.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node822 : node822.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node833 : node833.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node843 : node843.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node854 : node854.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node865 : node865.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node876 : node876.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node886 : node886.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node897 : node897.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node907 : node907.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node918 : node918.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node928 : node928.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node939 : node939.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node949 : node949.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node960 : node960.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node970 : node970.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node981 : node981.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node991 : node991.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1002 : node1002.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1012 : node1012.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1023 : node1023.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1034 : node1034.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1045 : node1045.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1055 : node1055.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1066 : node1066.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1076 : node1076.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1087 : node1087.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1097 : node1097.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1108 : node1108.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1119 : node1119.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1130 : node1130.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1140 : node1140.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1151 : node1151.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1161 : node1161.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1172 : node1172.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1182 : node1182.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1193 : node1193.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1204 : node1204.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1215 : node1215.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1225 : node1225.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1236 : node1236.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1246 : node1246.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1257 : node1257.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1267 : node1267.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1278 : node1278.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1288 : node1288.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1299 : node1299.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1309 : node1309.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1320 : node1320.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1330 : node1330.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1341 : node1341.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1351 : node1351.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1362 : node1362.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1373 : node1373.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1384 : node1384.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1394 : node1394.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1405 : node1405.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1415 : node1415.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1426 : node1426.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1436 : node1436.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1447 : node1447.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1458 : node1458.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1469 : node1469.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1479 : node1479.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1490 : node1490.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1500 : node1500.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1511 : node1511.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1521 : node1521.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1532 : node1532.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1543 : node1543.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1554 : node1554.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1564 : node1564.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1575 : node1575.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1585 : node1585.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1596 : node1596.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1606 : node1606.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1617 : node1617.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1627 : node1627.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1638 : node1638.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1648 : node1648.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1659 : node1659.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1669 : node1669.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1680 : node1680.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1690 : node1690.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1701 : node1701.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1712 : node1712.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1723 : node1723.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1733 : node1733.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1744 : node1744.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1754 : node1754.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1765 : node1765.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1775 : node1775.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1786 : node1786.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1797 : node1797.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1808 : node1808.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1818 : node1818.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1829 : node1829.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1839 : node1839.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1850 : node1850.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1860 : node1860.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1871 : node1871.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1882 : node1882.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1893 : node1893.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1903 : node1903.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1914 : node1914.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1924 : node1924.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1935 : node1935.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1945 : node1945.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1956 : node1956.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1966 : node1966.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1977 : node1977.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1987 : node1987.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1998 : node1998.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2008 : node2008.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2019 : node2019.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2029 : node2029.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2040 : node2040.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2051 : node2051.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2062 : node2062.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2072 : node2072.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2083 : node2083.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2093 : node2093.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2104 : node2104.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2114 : node2114.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2125 : node2125.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2136 : node2136.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2147 : node2147.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2157 : node2157.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2168 : node2168.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2178 : node2178.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2189 : node2189.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2199 : node2199.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2210 : node2210.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2221 : node2221.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2232 : node2232.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2242 : node2242.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2253 : node2253.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2263 : node2263.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2274 : node2274.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2284 : node2284.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2295 : node2295.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2305 : node2305.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2316 : node2316.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2326 : node2326.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2337 : node2337.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2347 : node2347.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2358 : node2358.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2368 : node2368.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2379 : node2379.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2390 : node2390.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2401 : node2401.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2411 : node2411.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2422 : node2422.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2432 : node2432.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2443 : node2443.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2453 : node2453.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2464 : node2464.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2475 : node2475.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2486 : node2486.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2496 : node2496.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2507 : node2507.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2517 : node2517.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2528 : node2528.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2538 : node2538.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2549 : node2549.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2560 : node2560.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2571 : node2571.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2581 : node2581.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2592 : node2592.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2602 : node2602.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2613 : node2613.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2623 : node2623.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2634 : node2634.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2644 : node2644.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2655 : node2655.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2665 : node2665.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2676 : node2676.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2686 : node2686.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2697 : node2697.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2707 : node2707.toList.all validKey = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node10 : node10.toList.all validKey = true :=
  joinValid _ _ _ valid_node5 (by decide +kernel) valid_node16
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node32 : node32.toList.all validKey = true :=
  joinValid _ _ _ valid_node27 (by decide +kernel) valid_node37
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node21 : node21.toList.all validKey = true :=
  joinValid _ _ _ valid_node10 (by decide +kernel) valid_node32
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node53 : node53.toList.all validKey = true :=
  joinValid _ _ _ valid_node48 (by decide +kernel) valid_node58
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node74 : node74.toList.all validKey = true :=
  joinValid _ _ _ valid_node69 (by decide +kernel) valid_node79
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node63 : node63.toList.all validKey = true :=
  joinValid _ _ _ valid_node53 (by decide +kernel) valid_node74
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node42 : node42.toList.all validKey = true :=
  joinValid _ _ _ valid_node21 (by decide +kernel) valid_node63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node95 : node95.toList.all validKey = true :=
  joinValid _ _ _ valid_node90 (by decide +kernel) valid_node101
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node117 : node117.toList.all validKey = true :=
  joinValid _ _ _ valid_node112 (by decide +kernel) valid_node122
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node106 : node106.toList.all validKey = true :=
  joinValid _ _ _ valid_node95 (by decide +kernel) valid_node117
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node138 : node138.toList.all validKey = true :=
  joinValid _ _ _ valid_node133 (by decide +kernel) valid_node143
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node159 : node159.toList.all validKey = true :=
  joinValid _ _ _ valid_node154 (by decide +kernel) valid_node164
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node148 : node148.toList.all validKey = true :=
  joinValid _ _ _ valid_node138 (by decide +kernel) valid_node159
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node127 : node127.toList.all validKey = true :=
  joinValid _ _ _ valid_node106 (by decide +kernel) valid_node148
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node84 : node84.toList.all validKey = true :=
  joinValid _ _ _ valid_node42 (by decide +kernel) valid_node127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node180 : node180.toList.all validKey = true :=
  joinValid _ _ _ valid_node175 (by decide +kernel) valid_node186
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node202 : node202.toList.all validKey = true :=
  joinValid _ _ _ valid_node197 (by decide +kernel) valid_node207
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node191 : node191.toList.all validKey = true :=
  joinValid _ _ _ valid_node180 (by decide +kernel) valid_node202
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node223 : node223.toList.all validKey = true :=
  joinValid _ _ _ valid_node218 (by decide +kernel) valid_node228
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node244 : node244.toList.all validKey = true :=
  joinValid _ _ _ valid_node239 (by decide +kernel) valid_node249
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node233 : node233.toList.all validKey = true :=
  joinValid _ _ _ valid_node223 (by decide +kernel) valid_node244
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node212 : node212.toList.all validKey = true :=
  joinValid _ _ _ valid_node191 (by decide +kernel) valid_node233
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node265 : node265.toList.all validKey = true :=
  joinValid _ _ _ valid_node260 (by decide +kernel) valid_node271
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node287 : node287.toList.all validKey = true :=
  joinValid _ _ _ valid_node282 (by decide +kernel) valid_node292
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node276 : node276.toList.all validKey = true :=
  joinValid _ _ _ valid_node265 (by decide +kernel) valid_node287
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node308 : node308.toList.all validKey = true :=
  joinValid _ _ _ valid_node303 (by decide +kernel) valid_node313
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node329 : node329.toList.all validKey = true :=
  joinValid _ _ _ valid_node324 (by decide +kernel) valid_node334
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node318 : node318.toList.all validKey = true :=
  joinValid _ _ _ valid_node308 (by decide +kernel) valid_node329
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node297 : node297.toList.all validKey = true :=
  joinValid _ _ _ valid_node276 (by decide +kernel) valid_node318
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node254 : node254.toList.all validKey = true :=
  joinValid _ _ _ valid_node212 (by decide +kernel) valid_node297
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node169 : node169.toList.all validKey = true :=
  joinValid _ _ _ valid_node84 (by decide +kernel) valid_node254
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node350 : node350.toList.all validKey = true :=
  joinValid _ _ _ valid_node345 (by decide +kernel) valid_node356
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node372 : node372.toList.all validKey = true :=
  joinValid _ _ _ valid_node367 (by decide +kernel) valid_node377
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node361 : node361.toList.all validKey = true :=
  joinValid _ _ _ valid_node350 (by decide +kernel) valid_node372
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node393 : node393.toList.all validKey = true :=
  joinValid _ _ _ valid_node388 (by decide +kernel) valid_node398
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node414 : node414.toList.all validKey = true :=
  joinValid _ _ _ valid_node409 (by decide +kernel) valid_node419
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node403 : node403.toList.all validKey = true :=
  joinValid _ _ _ valid_node393 (by decide +kernel) valid_node414
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node382 : node382.toList.all validKey = true :=
  joinValid _ _ _ valid_node361 (by decide +kernel) valid_node403
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node435 : node435.toList.all validKey = true :=
  joinValid _ _ _ valid_node430 (by decide +kernel) valid_node441
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node457 : node457.toList.all validKey = true :=
  joinValid _ _ _ valid_node452 (by decide +kernel) valid_node462
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node446 : node446.toList.all validKey = true :=
  joinValid _ _ _ valid_node435 (by decide +kernel) valid_node457
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node478 : node478.toList.all validKey = true :=
  joinValid _ _ _ valid_node473 (by decide +kernel) valid_node483
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node499 : node499.toList.all validKey = true :=
  joinValid _ _ _ valid_node494 (by decide +kernel) valid_node504
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node488 : node488.toList.all validKey = true :=
  joinValid _ _ _ valid_node478 (by decide +kernel) valid_node499
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node467 : node467.toList.all validKey = true :=
  joinValid _ _ _ valid_node446 (by decide +kernel) valid_node488
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node424 : node424.toList.all validKey = true :=
  joinValid _ _ _ valid_node382 (by decide +kernel) valid_node467
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node520 : node520.toList.all validKey = true :=
  joinValid _ _ _ valid_node515 (by decide +kernel) valid_node526
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node542 : node542.toList.all validKey = true :=
  joinValid _ _ _ valid_node537 (by decide +kernel) valid_node547
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node531 : node531.toList.all validKey = true :=
  joinValid _ _ _ valid_node520 (by decide +kernel) valid_node542
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node563 : node563.toList.all validKey = true :=
  joinValid _ _ _ valid_node558 (by decide +kernel) valid_node568
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node584 : node584.toList.all validKey = true :=
  joinValid _ _ _ valid_node579 (by decide +kernel) valid_node589
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node573 : node573.toList.all validKey = true :=
  joinValid _ _ _ valid_node563 (by decide +kernel) valid_node584
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node552 : node552.toList.all validKey = true :=
  joinValid _ _ _ valid_node531 (by decide +kernel) valid_node573
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node605 : node605.toList.all validKey = true :=
  joinValid _ _ _ valid_node600 (by decide +kernel) valid_node610
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node626 : node626.toList.all validKey = true :=
  joinValid _ _ _ valid_node621 (by decide +kernel) valid_node631
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node615 : node615.toList.all validKey = true :=
  joinValid _ _ _ valid_node605 (by decide +kernel) valid_node626
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node647 : node647.toList.all validKey = true :=
  joinValid _ _ _ valid_node642 (by decide +kernel) valid_node652
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node668 : node668.toList.all validKey = true :=
  joinValid _ _ _ valid_node663 (by decide +kernel) valid_node673
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node657 : node657.toList.all validKey = true :=
  joinValid _ _ _ valid_node647 (by decide +kernel) valid_node668
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node636 : node636.toList.all validKey = true :=
  joinValid _ _ _ valid_node615 (by decide +kernel) valid_node657
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node594 : node594.toList.all validKey = true :=
  joinValid _ _ _ valid_node552 (by decide +kernel) valid_node636
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node509 : node509.toList.all validKey = true :=
  joinValid _ _ _ valid_node424 (by decide +kernel) valid_node594
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node339 : node339.toList.all validKey = true :=
  joinValid _ _ _ valid_node169 (by decide +kernel) valid_node509
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node689 : node689.toList.all validKey = true :=
  joinValid _ _ _ valid_node684 (by decide +kernel) valid_node695
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node711 : node711.toList.all validKey = true :=
  joinValid _ _ _ valid_node706 (by decide +kernel) valid_node716
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node700 : node700.toList.all validKey = true :=
  joinValid _ _ _ valid_node689 (by decide +kernel) valid_node711
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node732 : node732.toList.all validKey = true :=
  joinValid _ _ _ valid_node727 (by decide +kernel) valid_node737
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node753 : node753.toList.all validKey = true :=
  joinValid _ _ _ valid_node748 (by decide +kernel) valid_node758
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node742 : node742.toList.all validKey = true :=
  joinValid _ _ _ valid_node732 (by decide +kernel) valid_node753
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node721 : node721.toList.all validKey = true :=
  joinValid _ _ _ valid_node700 (by decide +kernel) valid_node742
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node774 : node774.toList.all validKey = true :=
  joinValid _ _ _ valid_node769 (by decide +kernel) valid_node780
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node796 : node796.toList.all validKey = true :=
  joinValid _ _ _ valid_node791 (by decide +kernel) valid_node801
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node785 : node785.toList.all validKey = true :=
  joinValid _ _ _ valid_node774 (by decide +kernel) valid_node796
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node817 : node817.toList.all validKey = true :=
  joinValid _ _ _ valid_node812 (by decide +kernel) valid_node822
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node838 : node838.toList.all validKey = true :=
  joinValid _ _ _ valid_node833 (by decide +kernel) valid_node843
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node827 : node827.toList.all validKey = true :=
  joinValid _ _ _ valid_node817 (by decide +kernel) valid_node838
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node806 : node806.toList.all validKey = true :=
  joinValid _ _ _ valid_node785 (by decide +kernel) valid_node827
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node763 : node763.toList.all validKey = true :=
  joinValid _ _ _ valid_node721 (by decide +kernel) valid_node806
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node859 : node859.toList.all validKey = true :=
  joinValid _ _ _ valid_node854 (by decide +kernel) valid_node865
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node881 : node881.toList.all validKey = true :=
  joinValid _ _ _ valid_node876 (by decide +kernel) valid_node886
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node870 : node870.toList.all validKey = true :=
  joinValid _ _ _ valid_node859 (by decide +kernel) valid_node881
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node902 : node902.toList.all validKey = true :=
  joinValid _ _ _ valid_node897 (by decide +kernel) valid_node907
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node923 : node923.toList.all validKey = true :=
  joinValid _ _ _ valid_node918 (by decide +kernel) valid_node928
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node912 : node912.toList.all validKey = true :=
  joinValid _ _ _ valid_node902 (by decide +kernel) valid_node923
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node891 : node891.toList.all validKey = true :=
  joinValid _ _ _ valid_node870 (by decide +kernel) valid_node912
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node944 : node944.toList.all validKey = true :=
  joinValid _ _ _ valid_node939 (by decide +kernel) valid_node949
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node965 : node965.toList.all validKey = true :=
  joinValid _ _ _ valid_node960 (by decide +kernel) valid_node970
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node954 : node954.toList.all validKey = true :=
  joinValid _ _ _ valid_node944 (by decide +kernel) valid_node965
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node986 : node986.toList.all validKey = true :=
  joinValid _ _ _ valid_node981 (by decide +kernel) valid_node991
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1007 : node1007.toList.all validKey = true :=
  joinValid _ _ _ valid_node1002 (by decide +kernel) valid_node1012
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node996 : node996.toList.all validKey = true :=
  joinValid _ _ _ valid_node986 (by decide +kernel) valid_node1007
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node975 : node975.toList.all validKey = true :=
  joinValid _ _ _ valid_node954 (by decide +kernel) valid_node996
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node933 : node933.toList.all validKey = true :=
  joinValid _ _ _ valid_node891 (by decide +kernel) valid_node975
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node848 : node848.toList.all validKey = true :=
  joinValid _ _ _ valid_node763 (by decide +kernel) valid_node933
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1028 : node1028.toList.all validKey = true :=
  joinValid _ _ _ valid_node1023 (by decide +kernel) valid_node1034
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1050 : node1050.toList.all validKey = true :=
  joinValid _ _ _ valid_node1045 (by decide +kernel) valid_node1055
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1039 : node1039.toList.all validKey = true :=
  joinValid _ _ _ valid_node1028 (by decide +kernel) valid_node1050
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1071 : node1071.toList.all validKey = true :=
  joinValid _ _ _ valid_node1066 (by decide +kernel) valid_node1076
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1092 : node1092.toList.all validKey = true :=
  joinValid _ _ _ valid_node1087 (by decide +kernel) valid_node1097
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1081 : node1081.toList.all validKey = true :=
  joinValid _ _ _ valid_node1071 (by decide +kernel) valid_node1092
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1060 : node1060.toList.all validKey = true :=
  joinValid _ _ _ valid_node1039 (by decide +kernel) valid_node1081
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1113 : node1113.toList.all validKey = true :=
  joinValid _ _ _ valid_node1108 (by decide +kernel) valid_node1119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1135 : node1135.toList.all validKey = true :=
  joinValid _ _ _ valid_node1130 (by decide +kernel) valid_node1140
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1124 : node1124.toList.all validKey = true :=
  joinValid _ _ _ valid_node1113 (by decide +kernel) valid_node1135
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1156 : node1156.toList.all validKey = true :=
  joinValid _ _ _ valid_node1151 (by decide +kernel) valid_node1161
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1177 : node1177.toList.all validKey = true :=
  joinValid _ _ _ valid_node1172 (by decide +kernel) valid_node1182
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1166 : node1166.toList.all validKey = true :=
  joinValid _ _ _ valid_node1156 (by decide +kernel) valid_node1177
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1145 : node1145.toList.all validKey = true :=
  joinValid _ _ _ valid_node1124 (by decide +kernel) valid_node1166
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1102 : node1102.toList.all validKey = true :=
  joinValid _ _ _ valid_node1060 (by decide +kernel) valid_node1145
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1198 : node1198.toList.all validKey = true :=
  joinValid _ _ _ valid_node1193 (by decide +kernel) valid_node1204
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1220 : node1220.toList.all validKey = true :=
  joinValid _ _ _ valid_node1215 (by decide +kernel) valid_node1225
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1209 : node1209.toList.all validKey = true :=
  joinValid _ _ _ valid_node1198 (by decide +kernel) valid_node1220
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1241 : node1241.toList.all validKey = true :=
  joinValid _ _ _ valid_node1236 (by decide +kernel) valid_node1246
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1262 : node1262.toList.all validKey = true :=
  joinValid _ _ _ valid_node1257 (by decide +kernel) valid_node1267
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1251 : node1251.toList.all validKey = true :=
  joinValid _ _ _ valid_node1241 (by decide +kernel) valid_node1262
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1230 : node1230.toList.all validKey = true :=
  joinValid _ _ _ valid_node1209 (by decide +kernel) valid_node1251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1283 : node1283.toList.all validKey = true :=
  joinValid _ _ _ valid_node1278 (by decide +kernel) valid_node1288
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1304 : node1304.toList.all validKey = true :=
  joinValid _ _ _ valid_node1299 (by decide +kernel) valid_node1309
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1293 : node1293.toList.all validKey = true :=
  joinValid _ _ _ valid_node1283 (by decide +kernel) valid_node1304
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1325 : node1325.toList.all validKey = true :=
  joinValid _ _ _ valid_node1320 (by decide +kernel) valid_node1330
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1346 : node1346.toList.all validKey = true :=
  joinValid _ _ _ valid_node1341 (by decide +kernel) valid_node1351
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1335 : node1335.toList.all validKey = true :=
  joinValid _ _ _ valid_node1325 (by decide +kernel) valid_node1346
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1314 : node1314.toList.all validKey = true :=
  joinValid _ _ _ valid_node1293 (by decide +kernel) valid_node1335
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1272 : node1272.toList.all validKey = true :=
  joinValid _ _ _ valid_node1230 (by decide +kernel) valid_node1314
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1187 : node1187.toList.all validKey = true :=
  joinValid _ _ _ valid_node1102 (by decide +kernel) valid_node1272
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1017 : node1017.toList.all validKey = true :=
  joinValid _ _ _ valid_node848 (by decide +kernel) valid_node1187
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node678 : node678.toList.all validKey = true :=
  joinValid _ _ _ valid_node339 (by decide +kernel) valid_node1017
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1367 : node1367.toList.all validKey = true :=
  joinValid _ _ _ valid_node1362 (by decide +kernel) valid_node1373
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1389 : node1389.toList.all validKey = true :=
  joinValid _ _ _ valid_node1384 (by decide +kernel) valid_node1394
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1378 : node1378.toList.all validKey = true :=
  joinValid _ _ _ valid_node1367 (by decide +kernel) valid_node1389
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1410 : node1410.toList.all validKey = true :=
  joinValid _ _ _ valid_node1405 (by decide +kernel) valid_node1415
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1431 : node1431.toList.all validKey = true :=
  joinValid _ _ _ valid_node1426 (by decide +kernel) valid_node1436
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1420 : node1420.toList.all validKey = true :=
  joinValid _ _ _ valid_node1410 (by decide +kernel) valid_node1431
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1399 : node1399.toList.all validKey = true :=
  joinValid _ _ _ valid_node1378 (by decide +kernel) valid_node1420
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1452 : node1452.toList.all validKey = true :=
  joinValid _ _ _ valid_node1447 (by decide +kernel) valid_node1458
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1474 : node1474.toList.all validKey = true :=
  joinValid _ _ _ valid_node1469 (by decide +kernel) valid_node1479
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1463 : node1463.toList.all validKey = true :=
  joinValid _ _ _ valid_node1452 (by decide +kernel) valid_node1474
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1495 : node1495.toList.all validKey = true :=
  joinValid _ _ _ valid_node1490 (by decide +kernel) valid_node1500
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1516 : node1516.toList.all validKey = true :=
  joinValid _ _ _ valid_node1511 (by decide +kernel) valid_node1521
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1505 : node1505.toList.all validKey = true :=
  joinValid _ _ _ valid_node1495 (by decide +kernel) valid_node1516
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1484 : node1484.toList.all validKey = true :=
  joinValid _ _ _ valid_node1463 (by decide +kernel) valid_node1505
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1441 : node1441.toList.all validKey = true :=
  joinValid _ _ _ valid_node1399 (by decide +kernel) valid_node1484
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1537 : node1537.toList.all validKey = true :=
  joinValid _ _ _ valid_node1532 (by decide +kernel) valid_node1543
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1559 : node1559.toList.all validKey = true :=
  joinValid _ _ _ valid_node1554 (by decide +kernel) valid_node1564
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1548 : node1548.toList.all validKey = true :=
  joinValid _ _ _ valid_node1537 (by decide +kernel) valid_node1559
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1580 : node1580.toList.all validKey = true :=
  joinValid _ _ _ valid_node1575 (by decide +kernel) valid_node1585
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1601 : node1601.toList.all validKey = true :=
  joinValid _ _ _ valid_node1596 (by decide +kernel) valid_node1606
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1590 : node1590.toList.all validKey = true :=
  joinValid _ _ _ valid_node1580 (by decide +kernel) valid_node1601
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1569 : node1569.toList.all validKey = true :=
  joinValid _ _ _ valid_node1548 (by decide +kernel) valid_node1590
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1622 : node1622.toList.all validKey = true :=
  joinValid _ _ _ valid_node1617 (by decide +kernel) valid_node1627
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1643 : node1643.toList.all validKey = true :=
  joinValid _ _ _ valid_node1638 (by decide +kernel) valid_node1648
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1632 : node1632.toList.all validKey = true :=
  joinValid _ _ _ valid_node1622 (by decide +kernel) valid_node1643
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1664 : node1664.toList.all validKey = true :=
  joinValid _ _ _ valid_node1659 (by decide +kernel) valid_node1669
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1685 : node1685.toList.all validKey = true :=
  joinValid _ _ _ valid_node1680 (by decide +kernel) valid_node1690
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1674 : node1674.toList.all validKey = true :=
  joinValid _ _ _ valid_node1664 (by decide +kernel) valid_node1685
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1653 : node1653.toList.all validKey = true :=
  joinValid _ _ _ valid_node1632 (by decide +kernel) valid_node1674
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1611 : node1611.toList.all validKey = true :=
  joinValid _ _ _ valid_node1569 (by decide +kernel) valid_node1653
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1526 : node1526.toList.all validKey = true :=
  joinValid _ _ _ valid_node1441 (by decide +kernel) valid_node1611
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1706 : node1706.toList.all validKey = true :=
  joinValid _ _ _ valid_node1701 (by decide +kernel) valid_node1712
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1728 : node1728.toList.all validKey = true :=
  joinValid _ _ _ valid_node1723 (by decide +kernel) valid_node1733
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1717 : node1717.toList.all validKey = true :=
  joinValid _ _ _ valid_node1706 (by decide +kernel) valid_node1728
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1749 : node1749.toList.all validKey = true :=
  joinValid _ _ _ valid_node1744 (by decide +kernel) valid_node1754
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1770 : node1770.toList.all validKey = true :=
  joinValid _ _ _ valid_node1765 (by decide +kernel) valid_node1775
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1759 : node1759.toList.all validKey = true :=
  joinValid _ _ _ valid_node1749 (by decide +kernel) valid_node1770
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1738 : node1738.toList.all validKey = true :=
  joinValid _ _ _ valid_node1717 (by decide +kernel) valid_node1759
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1791 : node1791.toList.all validKey = true :=
  joinValid _ _ _ valid_node1786 (by decide +kernel) valid_node1797
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1813 : node1813.toList.all validKey = true :=
  joinValid _ _ _ valid_node1808 (by decide +kernel) valid_node1818
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1802 : node1802.toList.all validKey = true :=
  joinValid _ _ _ valid_node1791 (by decide +kernel) valid_node1813
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1834 : node1834.toList.all validKey = true :=
  joinValid _ _ _ valid_node1829 (by decide +kernel) valid_node1839
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1855 : node1855.toList.all validKey = true :=
  joinValid _ _ _ valid_node1850 (by decide +kernel) valid_node1860
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1844 : node1844.toList.all validKey = true :=
  joinValid _ _ _ valid_node1834 (by decide +kernel) valid_node1855
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1823 : node1823.toList.all validKey = true :=
  joinValid _ _ _ valid_node1802 (by decide +kernel) valid_node1844
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1780 : node1780.toList.all validKey = true :=
  joinValid _ _ _ valid_node1738 (by decide +kernel) valid_node1823
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1876 : node1876.toList.all validKey = true :=
  joinValid _ _ _ valid_node1871 (by decide +kernel) valid_node1882
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1898 : node1898.toList.all validKey = true :=
  joinValid _ _ _ valid_node1893 (by decide +kernel) valid_node1903
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1887 : node1887.toList.all validKey = true :=
  joinValid _ _ _ valid_node1876 (by decide +kernel) valid_node1898
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1919 : node1919.toList.all validKey = true :=
  joinValid _ _ _ valid_node1914 (by decide +kernel) valid_node1924
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1940 : node1940.toList.all validKey = true :=
  joinValid _ _ _ valid_node1935 (by decide +kernel) valid_node1945
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1929 : node1929.toList.all validKey = true :=
  joinValid _ _ _ valid_node1919 (by decide +kernel) valid_node1940
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1908 : node1908.toList.all validKey = true :=
  joinValid _ _ _ valid_node1887 (by decide +kernel) valid_node1929
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1961 : node1961.toList.all validKey = true :=
  joinValid _ _ _ valid_node1956 (by decide +kernel) valid_node1966
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1982 : node1982.toList.all validKey = true :=
  joinValid _ _ _ valid_node1977 (by decide +kernel) valid_node1987
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1971 : node1971.toList.all validKey = true :=
  joinValid _ _ _ valid_node1961 (by decide +kernel) valid_node1982
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2003 : node2003.toList.all validKey = true :=
  joinValid _ _ _ valid_node1998 (by decide +kernel) valid_node2008
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2024 : node2024.toList.all validKey = true :=
  joinValid _ _ _ valid_node2019 (by decide +kernel) valid_node2029
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2013 : node2013.toList.all validKey = true :=
  joinValid _ _ _ valid_node2003 (by decide +kernel) valid_node2024
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1992 : node1992.toList.all validKey = true :=
  joinValid _ _ _ valid_node1971 (by decide +kernel) valid_node2013
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1950 : node1950.toList.all validKey = true :=
  joinValid _ _ _ valid_node1908 (by decide +kernel) valid_node1992
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1865 : node1865.toList.all validKey = true :=
  joinValid _ _ _ valid_node1780 (by decide +kernel) valid_node1950
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1695 : node1695.toList.all validKey = true :=
  joinValid _ _ _ valid_node1526 (by decide +kernel) valid_node1865
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2045 : node2045.toList.all validKey = true :=
  joinValid _ _ _ valid_node2040 (by decide +kernel) valid_node2051
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2067 : node2067.toList.all validKey = true :=
  joinValid _ _ _ valid_node2062 (by decide +kernel) valid_node2072
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2056 : node2056.toList.all validKey = true :=
  joinValid _ _ _ valid_node2045 (by decide +kernel) valid_node2067
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2088 : node2088.toList.all validKey = true :=
  joinValid _ _ _ valid_node2083 (by decide +kernel) valid_node2093
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2109 : node2109.toList.all validKey = true :=
  joinValid _ _ _ valid_node2104 (by decide +kernel) valid_node2114
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2098 : node2098.toList.all validKey = true :=
  joinValid _ _ _ valid_node2088 (by decide +kernel) valid_node2109
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2077 : node2077.toList.all validKey = true :=
  joinValid _ _ _ valid_node2056 (by decide +kernel) valid_node2098
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2130 : node2130.toList.all validKey = true :=
  joinValid _ _ _ valid_node2125 (by decide +kernel) valid_node2136
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2152 : node2152.toList.all validKey = true :=
  joinValid _ _ _ valid_node2147 (by decide +kernel) valid_node2157
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2141 : node2141.toList.all validKey = true :=
  joinValid _ _ _ valid_node2130 (by decide +kernel) valid_node2152
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2173 : node2173.toList.all validKey = true :=
  joinValid _ _ _ valid_node2168 (by decide +kernel) valid_node2178
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2194 : node2194.toList.all validKey = true :=
  joinValid _ _ _ valid_node2189 (by decide +kernel) valid_node2199
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2183 : node2183.toList.all validKey = true :=
  joinValid _ _ _ valid_node2173 (by decide +kernel) valid_node2194
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2162 : node2162.toList.all validKey = true :=
  joinValid _ _ _ valid_node2141 (by decide +kernel) valid_node2183
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2119 : node2119.toList.all validKey = true :=
  joinValid _ _ _ valid_node2077 (by decide +kernel) valid_node2162
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2215 : node2215.toList.all validKey = true :=
  joinValid _ _ _ valid_node2210 (by decide +kernel) valid_node2221
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2237 : node2237.toList.all validKey = true :=
  joinValid _ _ _ valid_node2232 (by decide +kernel) valid_node2242
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2226 : node2226.toList.all validKey = true :=
  joinValid _ _ _ valid_node2215 (by decide +kernel) valid_node2237
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2258 : node2258.toList.all validKey = true :=
  joinValid _ _ _ valid_node2253 (by decide +kernel) valid_node2263
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2279 : node2279.toList.all validKey = true :=
  joinValid _ _ _ valid_node2274 (by decide +kernel) valid_node2284
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2268 : node2268.toList.all validKey = true :=
  joinValid _ _ _ valid_node2258 (by decide +kernel) valid_node2279
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2247 : node2247.toList.all validKey = true :=
  joinValid _ _ _ valid_node2226 (by decide +kernel) valid_node2268
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2300 : node2300.toList.all validKey = true :=
  joinValid _ _ _ valid_node2295 (by decide +kernel) valid_node2305
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2321 : node2321.toList.all validKey = true :=
  joinValid _ _ _ valid_node2316 (by decide +kernel) valid_node2326
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2310 : node2310.toList.all validKey = true :=
  joinValid _ _ _ valid_node2300 (by decide +kernel) valid_node2321
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2342 : node2342.toList.all validKey = true :=
  joinValid _ _ _ valid_node2337 (by decide +kernel) valid_node2347
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2363 : node2363.toList.all validKey = true :=
  joinValid _ _ _ valid_node2358 (by decide +kernel) valid_node2368
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2352 : node2352.toList.all validKey = true :=
  joinValid _ _ _ valid_node2342 (by decide +kernel) valid_node2363
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2331 : node2331.toList.all validKey = true :=
  joinValid _ _ _ valid_node2310 (by decide +kernel) valid_node2352
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2289 : node2289.toList.all validKey = true :=
  joinValid _ _ _ valid_node2247 (by decide +kernel) valid_node2331
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2204 : node2204.toList.all validKey = true :=
  joinValid _ _ _ valid_node2119 (by decide +kernel) valid_node2289
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2384 : node2384.toList.all validKey = true :=
  joinValid _ _ _ valid_node2379 (by decide +kernel) valid_node2390
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2406 : node2406.toList.all validKey = true :=
  joinValid _ _ _ valid_node2401 (by decide +kernel) valid_node2411
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2395 : node2395.toList.all validKey = true :=
  joinValid _ _ _ valid_node2384 (by decide +kernel) valid_node2406
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2427 : node2427.toList.all validKey = true :=
  joinValid _ _ _ valid_node2422 (by decide +kernel) valid_node2432
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2448 : node2448.toList.all validKey = true :=
  joinValid _ _ _ valid_node2443 (by decide +kernel) valid_node2453
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2437 : node2437.toList.all validKey = true :=
  joinValid _ _ _ valid_node2427 (by decide +kernel) valid_node2448
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2416 : node2416.toList.all validKey = true :=
  joinValid _ _ _ valid_node2395 (by decide +kernel) valid_node2437
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2469 : node2469.toList.all validKey = true :=
  joinValid _ _ _ valid_node2464 (by decide +kernel) valid_node2475
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2491 : node2491.toList.all validKey = true :=
  joinValid _ _ _ valid_node2486 (by decide +kernel) valid_node2496
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2480 : node2480.toList.all validKey = true :=
  joinValid _ _ _ valid_node2469 (by decide +kernel) valid_node2491
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2512 : node2512.toList.all validKey = true :=
  joinValid _ _ _ valid_node2507 (by decide +kernel) valid_node2517
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2533 : node2533.toList.all validKey = true :=
  joinValid _ _ _ valid_node2528 (by decide +kernel) valid_node2538
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2522 : node2522.toList.all validKey = true :=
  joinValid _ _ _ valid_node2512 (by decide +kernel) valid_node2533
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2501 : node2501.toList.all validKey = true :=
  joinValid _ _ _ valid_node2480 (by decide +kernel) valid_node2522
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2458 : node2458.toList.all validKey = true :=
  joinValid _ _ _ valid_node2416 (by decide +kernel) valid_node2501
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2554 : node2554.toList.all validKey = true :=
  joinValid _ _ _ valid_node2549 (by decide +kernel) valid_node2560
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2576 : node2576.toList.all validKey = true :=
  joinValid _ _ _ valid_node2571 (by decide +kernel) valid_node2581
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2565 : node2565.toList.all validKey = true :=
  joinValid _ _ _ valid_node2554 (by decide +kernel) valid_node2576
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2597 : node2597.toList.all validKey = true :=
  joinValid _ _ _ valid_node2592 (by decide +kernel) valid_node2602
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2618 : node2618.toList.all validKey = true :=
  joinValid _ _ _ valid_node2613 (by decide +kernel) valid_node2623
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2607 : node2607.toList.all validKey = true :=
  joinValid _ _ _ valid_node2597 (by decide +kernel) valid_node2618
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2586 : node2586.toList.all validKey = true :=
  joinValid _ _ _ valid_node2565 (by decide +kernel) valid_node2607
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2639 : node2639.toList.all validKey = true :=
  joinValid _ _ _ valid_node2634 (by decide +kernel) valid_node2644
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2660 : node2660.toList.all validKey = true :=
  joinValid _ _ _ valid_node2655 (by decide +kernel) valid_node2665
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2649 : node2649.toList.all validKey = true :=
  joinValid _ _ _ valid_node2639 (by decide +kernel) valid_node2660
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2681 : node2681.toList.all validKey = true :=
  joinValid _ _ _ valid_node2676 (by decide +kernel) valid_node2686
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2702 : node2702.toList.all validKey = true :=
  joinValid _ _ _ valid_node2697 (by decide +kernel) valid_node2707
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2691 : node2691.toList.all validKey = true :=
  joinValid _ _ _ valid_node2681 (by decide +kernel) valid_node2702
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2670 : node2670.toList.all validKey = true :=
  joinValid _ _ _ valid_node2649 (by decide +kernel) valid_node2691
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2628 : node2628.toList.all validKey = true :=
  joinValid _ _ _ valid_node2586 (by decide +kernel) valid_node2670
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2543 : node2543.toList.all validKey = true :=
  joinValid _ _ _ valid_node2458 (by decide +kernel) valid_node2628
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2373 : node2373.toList.all validKey = true :=
  joinValid _ _ _ valid_node2204 (by decide +kernel) valid_node2543
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node2034 : node2034.toList.all validKey = true :=
  joinValid _ _ _ valid_node1695 (by decide +kernel) valid_node2373
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem valid_node1356 : node1356.toList.all validKey = true :=
  joinValid _ _ _ valid_node678 (by decide +kernel) valid_node2034

theorem closed (x : List ℕ) (hx : certTree.mem x = true) :
    ∃ h, stepOK allBits targetBits distPairs monoPairs [] certTree x h = true :=
  ⟨[], List.all_eq_true.mp valid_node1356 x (certTree.mem_toList x hx)⟩
def rowTarget (x : Fin 6 → Bool) : Bool := decide (∃ i < ([0, 1, 0, 2, 0, 4, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3] : List ℕ).length / 2, (List.ofFn x).getD (([0, 1, 0, 2, 0, 4, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 1, 0, 2, 0, 4, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3] : List ℕ).getD (2 * i + 1) 0) false = true)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem lower : ∀ s, HasCircuitSize 6 rowTarget s → 9 ≤ s :=
  lb_cert rowTarget (List.range 64) allBits targetBits inputs distPairs monoPairs [] certTree 8 9
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) closed (by decide +kernel)

def upper : List Gate := [⟨.or,[0,1]⟩, ⟨.or,[2,4]⟩, ⟨.and,[6,7]⟩,
  ⟨.or,[1,2]⟩, ⟨.or,[5,9]⟩, ⟨.and,[3,9]⟩, ⟨.or,[0,11]⟩,
  ⟨.and,[10,12]⟩, ⟨.or,[8,13]⟩]

set_option maxRecDepth 8192 in
theorem upper_ok :
    (∀ g ∈ upper, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
    ∀ x : Fin 6 → Bool, (Circuit.mk upper 14).eval (List.ofFn x) = rowTarget x := by
  let _ := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  decide

end PEqualNP.Outside.L_meta_9140_aux

open PEqualNP.Outside.L_meta_9140_aux in
theorem PEqualNP.Outside.L_meta_9140 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 6 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 1, 0, 2, 0, 4, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3] : List ℕ).length / 2, (List.ofFn x).getD (([0, 1, 0, 2, 0, 4, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 1, 0, 2, 0, 4, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 6 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 1, 0, 2, 0, 4, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3] : List ℕ).length / 2, (List.ofFn x).getD (([0, 1, 0, 2, 0, 4, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 1, 0, 2, 0, 4, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o shape _ ev
  have hs : PEqualNP.MetaComplexity.HasCircuitSize 6 rowTarget gs.length := by
    refine ⟨⟨gs,o⟩, ?_, le_rfl, ev⟩
    intro g hg
    obtain ⟨hop, hfan⟩ := shape g hg
    exact ⟨by simpa using hop, hfan⟩
  exact ⟨upper,14,upper_ok.1, lower _ hs,upper_ok.2⟩
