import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18617
open PEqualNP.CircuitLowerBounds
private def C : Circuit := ⟨[⟨.or, [13, 18]⟩, ⟨.or, [27, 24]⟩, ⟨.and, [1, 28]⟩, ⟨.or, [15, 19]⟩, ⟨.or, [30, 25]⟩, ⟨.and, [2, 31]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [33, 21]⟩, ⟨.and, [4, 34]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [36, 23]⟩, ⟨.and, [10, 37]⟩, ⟨.or, [29, 32]⟩, ⟨.or, [39, 35]⟩, ⟨.or, [40, 38]⟩],41⟩
private def links : List (Fin 13 × Fin 13) := [(1, 0), (1, 5), (1, 11), (2, 2), (2, 6), (2, 12), (4, 3), (4, 4), (4, 8), (10, 7), (10, 9), (10, 10)]
private theorem link (p l : Fin 13) : (p,l) ∈ links ↔ p ∈ ([1,2,4,10] : List (Fin 13)) ∧ l ≠ 1 ∧ (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) := by
  revert p l
  decide +kernel
end PEqualNP.Outside.L_meta_18617
open PEqualNP.Outside.L_meta_18617 in
set_option maxHeartbeats 4800000 in
theorem PEqualNP.Outside.L_meta_18617 : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (15 : ℕ) ∧ (27 : ℕ) ≤ x1.output ∧ x1.output < (27 : ℕ) + x1.size ∧ PEqualNP.TopForm.IsAO2 (27 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ ∀ (x2 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [x2 (1 : Fin (26 : ℕ)) || x2 (2 : Fin (26 : ℕ))]) = Bool.true ↔ ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 ∈ [(1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (4 : Fin (13 : ℕ)), (10 : Fin (13 : ℕ))] ∧ x4 ≠ (1 : Fin (13 : ℕ)) ∧ (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true := by
  refine ⟨C,by decide,by decide,by decide,by decide,by decide,?_⟩
  intro x
  let active (z : Fin 13 × Fin 13) := x (Fin.castAdd 13 z.1) && x (Fin.natAdd 13 z.2)
  have eval : C.eval (List.ofFn x ++ [x 1 || x 2]) = links.any active := by
    let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have calcor (w : List Bool) (a b : ℕ) : step w ⟨.or,[a,b]⟩ = w ++ [w.getD a false || w.getD b false] := by simp [step,PEqualNP.CircuitLowerBounds.GateOp.eval]
    have calcand (w : List Bool) (a b : ℕ) : step w ⟨.and,[a,b]⟩ = w ++ [w.getD a false && w.getD b false] := by simp [step,PEqualNP.CircuitLowerBounds.GateOp.eval]
    change (C.gates.foldl step (List.ofFn x ++ [x 1 || x 2])).getD C.output false = _
    rw [show List.ofFn x ++ [x 1 || x 2] = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2)] from rfl]
    unfold C
    let z0 := x 13 || x 18
    rw [List.foldl_cons,show step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2)] ⟨.or,[13,18]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0] from by rw [calcor]; rfl]
    let z1 := z0 || x 24
    rw [List.foldl_cons,show step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0] ⟨.or,[27,24]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1] from by rw [calcor]; rfl]
    let z2 := x 1 && z1
    rw [List.foldl_cons,show step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1] ⟨.and,[1,28]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2] from by rw [calcand]; rfl]
    let z3 := x 15 || x 19
    rw [List.foldl_cons,show step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2] ⟨.or,[15,19]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3] from by rw [calcor]; rfl]
    let z4 := z3 || x 25
    rw [List.foldl_cons,show step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3] ⟨.or,[30,25]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3, z4] from by rw [calcor]; rfl]
    let z5 := x 2 && z4
    rw [List.foldl_cons,show step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3, z4] ⟨.and,[2,31]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3, z4, z5] from by rw [calcand]; rfl]
    let z6 := x 16 || x 17
    rw [List.foldl_cons,show step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3, z4, z5] ⟨.or,[16,17]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3, z4, z5, z6] from by rw [calcor]; rfl]
    let z7 := z6 || x 21
    rw [List.foldl_cons,show step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3, z4, z5, z6] ⟨.or,[33,21]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3, z4, z5, z6, z7] from by rw [calcor]; rfl]
    let z8 := x 4 && z7
    rw [List.foldl_cons,show step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3, z4, z5, z6, z7] ⟨.and,[4,34]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3, z4, z5, z6, z7, z8] from by rw [calcand]; rfl]
    let z9 := x 20 || x 22
    rw [List.foldl_cons,show step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3, z4, z5, z6, z7, z8] ⟨.or,[20,22]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3, z4, z5, z6, z7, z8, z9] from by rw [calcor]; rfl]
    let z10 := z9 || x 23
    rw [List.foldl_cons,show step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3, z4, z5, z6, z7, z8, z9] ⟨.or,[36,23]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10] from by rw [calcor]; rfl]
    let z11 := x 10 && z10
    rw [List.foldl_cons,show step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10] ⟨.and,[10,37]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11] from by rw [calcand]; rfl]
    let z12 := z2 || z5
    rw [List.foldl_cons,show step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11] ⟨.or,[29,32]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12] from by rw [calcor]; rfl]
    let z13 := z12 || z8
    rw [List.foldl_cons,show step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12] ⟨.or,[39,35]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13] from by rw [calcor]; rfl]
    let z14 := z13 || z11
    rw [List.foldl_cons,show step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13] ⟨.or,[40,38]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14] from by rw [calcor]; rfl]
    change ((x 1 && (x 13 || x 18 || x 24)) || (x 2 && (x 15 || x 19 || x 25)) || (x 4 && (x 16 || x 17 || x 21)) || (x 10 && (x 20 || x 22 || x 23))) = ((x 1 && x 13) || ((x 1 && x 18) || ((x 1 && x 24) || ((x 2 && x 15) || ((x 2 && x 19) || ((x 2 && x 25) || ((x 4 && x 16) || ((x 4 && x 17) || ((x 4 && x 21) || ((x 10 && x 20) || ((x 10 && x 22) || ((x 10 && x 23) || false))))))))))))
    simp only [Bool.and_or_distrib_left, Bool.or_false]
    ac_rfl
  rw [eval,List.any_eq_true]
  constructor
  · rintro ⟨⟨p,l⟩,hm,h⟩
    obtain ⟨hp,hl,he⟩ := (link p l).mp hm
    obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
    exact ⟨p,l,hp,hl,he,a,b⟩
  · rintro ⟨p,l,hp,hl,he,a,b⟩
    exact ⟨(p,l),(link p l).mpr ⟨hp,hl,he⟩,Bool.and_eq_true_iff.mpr ⟨a,b⟩⟩
