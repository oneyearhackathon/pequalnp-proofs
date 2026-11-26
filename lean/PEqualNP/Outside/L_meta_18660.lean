import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_18660 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)),   have x3 : Finset (Fin x1) → Prop := fun (x3 : Finset (Fin x1)) => ∀ (x4 x5 : Fin x1), x2.Adj x4 x5 → x4 ∈ x3 ∨ x5 ∈ x3;   ¬x2.Colorable (2 : ℕ) → (∀ (x5 : Fin x1), (∃ (x6 : Fin x1), x2.Adj x5 x6) → (x2.neighborSet x5).ncard = (3 : ℕ)) → ∃ (x6 : Finset (Fin x1)), x3 x6 ∧ (∀ (x7 : Finset (Fin x1)), x3 x7 → x6.card ≤ x7.card) ∧ (∀ x7 ∈ x6, ∃ x9 ∉ x6, x2.Adj x7 x9) ∧ (∃ x7 ∈ x6, ∃ x8 ∈ x6, x2.Adj x7 x8) ∧ ∀ x7 ∈ x6, ∀ x9 ∈ x6, x2.Adj x7 x9 → (x2.edgeSet \ (x2.incidenceSet x7 ∪ x2.incidenceSet x9)).ncard + ((x6.erase x7).erase x9).card + (7 : ℕ) = x2.edgeSet.ncard + x6.card := by
  classical
  intro n G covers nonbip cubic
  let good (k : ℕ) := ∃ T : Finset (Fin n), covers T ∧ T.card = k
  have ex : ∃ k, good k := ⟨_,Finset.univ,fun _ _ _ => Or.inl (Finset.mem_univ _),rfl⟩
  obtain ⟨T,hT,ht⟩ := Nat.find_spec ex
  have least (S) (hS : covers S) : T.card ≤ S.card := by
    rw [ht]
    exact Nat.find_min' ex ⟨S,hS,rfl⟩
  refine ⟨T,hT,least,?_,?_,?_⟩
  · intro u hu
    by_contra nop
    have keep (w) (adj : G.Adj u w) : w ∈ T := by
      by_contra h
      exact nop ⟨w,h,adj⟩
    have hcov : covers (T.erase u) := by
      intro a b ab
      by_cases ha : a = u
      · subst a; exact Or.inr (Finset.mem_erase.mpr ⟨ab.ne.symm,keep b ab⟩)
      by_cases hb : b = u
      · subst b; exact Or.inl (Finset.mem_erase.mpr ⟨ha,keep a ab.symm⟩)
      exact (hT a b ab).imp (fun h => Finset.mem_erase.mpr ⟨ha,h⟩) (fun h => Finset.mem_erase.mpr ⟨hb,h⟩)
    have hle := least _ hcov
    have hlt := Finset.card_erase_lt_of_mem hu
    omega
  · by_contra none
    apply nonbip
    refine ⟨SimpleGraph.Coloring.mk (fun u => if u ∈ T then (1 : Fin 2) else 0) ?_⟩
    intro u v adj
    by_cases hu : u ∈ T
    · have hv : v ∉ T := fun hv => none ⟨u,hu,v,hv,adj⟩
      simp [hu,hv]
    · have hv := (hT u v adj).resolve_left hu
      simp [hu,hv]
  · intro u hu v hv adj
    have sub := Set.union_subset (G.incidenceSet_subset u) (G.incidenceSet_subset v)
    have hc := Set.ncard_sdiff_add_ncard_of_subset sub
    have ha := Set.ncard_union_add_ncard_inter (G.incidenceSet u) (G.incidenceSet v)
    rw [G.incidenceSet_inter_incidenceSet_of_adj adj,Set.ncard_singleton,
      G.ncard_incidenceSet,G.ncard_incidenceSet,← G.ncard_neighborSet,← G.ncard_neighborSet,
      cubic u ⟨v,adj⟩,cubic v ⟨u,adj.symm⟩] at ha
    have hev : v ∈ T.erase u := Finset.mem_erase.mpr ⟨adj.ne.symm,hv⟩
    have h1 := Finset.card_erase_add_one hu
    have h2 := Finset.card_erase_add_one hev
    omega
