import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18966
private def col (i : Fin 26) : ℕ := (let u := (if i.val < 13 then [9820805366576,3697915243686326406,3772072151941599339,8659025085589474860,762494670591627578,9998186360218198862,7813898889586405971,2492579563743896212,8260024526693886294,9773907680645894422,2402781631192498177] else [1231427982286,4772337669408815584,1455263899191340963,9832454934276868335,925941497934626908,2690850975655642988,2184208476895364767,3353807136187280627,2669759675931372401,6826416250394358953,6258748122593763329] : List ℕ).foldl (fun x y => 10^19*x+y) 0; let n := i.val % 13; let p := (2^676-1)/8191; ((u >>> (13-n)) &&& ((2^n-1)*p)) ||| ((u <<< n) &&& ((8192-2^n)*p)))
private def bank : List ℕ := ([col 0, col 1, col 2, col 3, col 4, col 5, col 6, col 7, col 8, col 9, col 10, col 11, col 12, col 13, col 14, col 15, col 16, col 17, col 18, col 19, col 20, col 21, col 22, col 23, col 24, col 25] : List ℕ)
private def step (l : List ℕ) (g : Bool × ℕ × ℕ) := l ++ [if g.1 then l.getD g.2.1 0 ||| l.getD g.2.2 0 else l.getD g.2.1 0 &&& l.getD g.2.2 0]
private def data : List (Bool × ℕ × ℕ) := [(true,0,1), (true,1,2), (true,2,3), (true,3,4), (true,4,5), (true,5,6), (true,3,9), (true,4,10), (true,5,11), (true,6,12), (true,7,0), (true,8,1), (true,26,32), (true,27,33), (true,28,34), (true,29,35), (true,30,36), (true,31,37), (false,38,13), (false,39,14), (false,40,15), (false,41,16), (false,42,17), (false,43,18), (true,44,45), (true,50,46), (true,51,47), (true,52,48), (true,53,49)]
private def w (i : ℕ) := (data.foldl step bank).getD i 0
private def pick (j : ℕ) := data.getD j (false,0,0)
private theorem parents : ∀ j : Fin 29, (pick j.val).2.1 < 26+j.val ∧ (pick j.val).2.2 < 26+j.val := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert : ∀ j : Fin 29, let p := pick j.val; w (26+j.val) = (if p.1 then w p.2.1 ||| w p.2.2 else w p.2.1 &&& w p.2.2) := by decide +kernel
end PEqualNP.Outside.L_meta_18966
open PEqualNP.Outside.L_meta_18966 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.L_meta_18966 : ∃ (x1 : ℕ → ℕ),   (∀ (x2 : Fin (26 : ℕ)),       x1 ↑x2 =         have x3 : ℕ := List.foldl (fun (x3 x4 : ℕ) => (10 : ℕ) ^ (19 : ℕ) * x3 + x4) (0 : ℕ) (if ↑x2 < (13 : ℕ) then [(9820805366576 : ℕ), (3697915243686326406 : ℕ), (3772072151941599339 : ℕ), (8659025085589474860 : ℕ), (762494670591627578 : ℕ), (9998186360218198862 : ℕ), (7813898889586405971 : ℕ), (2492579563743896212 : ℕ), (8260024526693886294 : ℕ), (9773907680645894422 : ℕ), (2402781631192498177 : ℕ)] else [(1231427982286 : ℕ), (4772337669408815584 : ℕ), (1455263899191340963 : ℕ), (9832454934276868335 : ℕ), (925941497934626908 : ℕ), (2690850975655642988 : ℕ), (2184208476895364767 : ℕ), (3353807136187280627 : ℕ), (2669759675931372401 : ℕ), (6826416250394358953 : ℕ), (6258748122593763329 : ℕ)]);         have x4 : ℕ := ↑x2 % (13 : ℕ);         have x5 : ℕ := ((2 : ℕ) ^ (676 : ℕ) - (1 : ℕ)) / (8191 : ℕ);         x3 >>> ((13 : ℕ) - x4) &&& ((2 : ℕ) ^ x4 - (1 : ℕ)) * x5 ||| x3 <<< x4 &&& ((8192 : ℕ) - (2 : ℕ) ^ x4) * x5) ∧     (∀ (x2 : Fin (6 : ℕ)), x1 ((26 : ℕ) + ↑x2) = x1 ↑x2 ||| x1 (↑x2 + (1 : ℕ)) ∧ x1 ((32 : ℕ) + ↑x2) = x1 (↑x2 + (3 : ℕ)) ||| x1 ((↑x2 + (9 : ℕ)) % (13 : ℕ)) ∧ x1 ((38 : ℕ) + ↑x2) = x1 ((26 : ℕ) + ↑x2) ||| x1 ((32 : ℕ) + ↑x2)) ∧ x1 (54 : ℕ) = (34638844649535 : ℕ) ∧ ∀ (x2 : Fin (29 : ℕ)), ∃ (x3 : Fin ((26 : ℕ) + ↑x2)) (x4 : Fin ((26 : ℕ) + ↑x2)), x1 ((26 : ℕ) + ↑x2) = x1 ↑x3 &&& x1 ↑x4 ∨ x1 ((26 : ℕ) + ↑x2) = x1 ↑x3 ||| x1 ↑x4 := by
  refine ⟨w, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro j
  refine ⟨⟨_,(parents j).1⟩,⟨_,(parents j).2⟩,?_⟩
  have h := cert j
  cases eq : (pick j.val).1 <;> simp [eq] at h
  · exact Or.inl h
  · exact Or.inr h
