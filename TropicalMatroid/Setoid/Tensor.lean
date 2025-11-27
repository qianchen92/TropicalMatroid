import TropicalMatroid.Setoid.Basic

namespace TropicalMatroid

variable (α β : Type*) [Fintype α] [Fintype β]
variable [PowersetSetoid α] [PowersetSetoid β]

instance : PowersetSetoid (α × β) where
  r := fun (p1 p2 : α × β) ↦ (p1.1 ≈ p2.1) ∧ (p1.2 ≈ p2.2)
  iseqv :={
    refl := fun p ↦ ⟨Setoid.refl p.1, Setoid.refl p.2⟩
    symm := fun h ↦ ⟨Setoid.symm h.1, Setoid.symm h.2⟩
    trans := fun h1 h2 ↦ ⟨Setoid.trans h1.1 h2.1, Setoid.trans h1.2 h2.2⟩
  }
  setEquiv := fun (S1 S2 : Set (α × β)) ↦
  (PowersetSetoid.setEquiv (Prod.fst '' S1) (Prod.fst '' S2)) ∧
    (PowersetSetoid.setEquiv (Prod.snd '' S1) (Prod.snd '' S2))
  setEquiv_Equiv := {
    refl := by
      intro S
      constructor
      · exact PowersetSetoid.setEquiv_Equiv.refl (Prod.fst '' S)
      · exact PowersetSetoid.setEquiv_Equiv.refl (Prod.snd '' S)
    symm := by
      intro S1 S2 h
      constructor
      · exact PowersetSetoid.setEquiv_Equiv.symm h.1
      · exact PowersetSetoid.setEquiv_Equiv.symm h.2
    trans := by
      intro S1 S2 S3 h1 h2
      constructor
      · exact PowersetSetoid.setEquiv_Equiv.trans h1.1 h2.1
      · exact PowersetSetoid.setEquiv_Equiv.trans h1.2 h2.2
  }
  singleton_consistency := by
    intro x y
    constructor
    · intro h
      rcases h with ⟨h1, h2⟩
      rw [Set.image_singleton, Set.image_singleton] at h1
      rw [Set.image_singleton, Set.image_singleton] at h2
      rw [PowersetSetoid.singleton_consistency] at h1
      rw [PowersetSetoid.singleton_consistency] at h2
      exact ⟨h1, h2⟩
    · intro h
      rcases h with ⟨h1, h2⟩
      constructor
      · rw [Set.image_singleton, Set.image_singleton]
        rw [PowersetSetoid.singleton_consistency]
        exact h1
      · rw [Set.image_singleton, Set.image_singleton]
        rw [PowersetSetoid.singleton_consistency]
        exact h2
  insert_congruence := by
    intro S1 S2 x y hS hxy
    constructor
    · rcases hS with ⟨hS1,hS2⟩
      rcases hxy with ⟨hx, hy⟩
      have h1 : PowersetSetoid.setEquiv (Prod.fst '' S1 ∪ {x.1}) (Prod.fst '' S2 ∪ {y.1}) := by
        apply PowersetSetoid.insert_congruence
        · exact hS1
        · exact hx
      rw [Set.image_union, Set.image_singleton, Set.image_union, Set.image_singleton]
      exact h1
    · rcases hS with ⟨hS1,hS2⟩
      rcases hxy with ⟨hx, hy⟩
      have h2 : PowersetSetoid.setEquiv (Prod.snd '' S1 ∪ {x.2}) (Prod.snd '' S2 ∪ {y.2}) := by
        apply PowersetSetoid.insert_congruence
        · exact hS2
        · exact hy
      rw [Set.image_union, Set.image_singleton, Set.image_union, Set.image_singleton]
      exact h2
  substitutivity := by
    intro S x y hx hxy
    constructor
    · let S1 := Prod.fst '' S
      let x1 := x.1
      let y1 := y.1
      have hx1 : x1 ∈ S1 := ⟨x, hx, rfl⟩
      have h_sub : Prod.fst '' (S \ {x}) ⊆ S1 := by
        intro z hz
        rcases hz with ⟨w, hw, rfl⟩
        use w
        exact ⟨hw.1, rfl⟩
      have h_sup : S1 \ {x1} ⊆ Prod.fst '' (S \ {x}) := by
        intro z hz
        rcases hz with ⟨⟨w, hw, rfl⟩, hneq⟩
        use w
        constructor
        · constructor
          · exact hw
          · intro h_eq
            rw [h_eq] at hneq
            contradiction
        · rfl

      by_cases h_unique : ∃ w ∈ S, w.1 = x1 ∧ w ≠ x
      · rcases h_unique with ⟨w, hw, hw1, hwn⟩
        have h_eq : Prod.fst '' (S \ {x}) = S1 := by
          apply Set.Subset.antisymm
          · exact h_sub
          · intro z hz
            if hzx : z = x1 then
              rw [hzx, ←hw1]
              refine ⟨w, ?_, rfl⟩
              exact ⟨hw, hwn⟩
            else
              rcases hz with ⟨u, hu, rfl⟩
              refine ⟨u, ?_, rfl⟩
              exact ⟨hu, by intro h; rw [h] at hzx; contradiction⟩
        rw [Set.image_union, Set.image_singleton, h_eq]
        apply PowersetSetoid.setEquiv_Equiv.symm
        have h_ins := PowersetSetoid.insert_congruence S1 S1 x1 y1
          (PowersetSetoid.setEquiv_Equiv.refl S1) hxy.1
        simp only [Set.union_singleton, Set.insert_eq_of_mem hx1] at h_ins
        simp only [Set.union_singleton]
        exact h_ins
      · push_neg at h_unique
        have h_eq : Prod.fst '' (S \ {x}) = S1 \ {x1} := by
          apply Set.Subset.antisymm
          · intro z hz
            rcases hz with ⟨w, ⟨hwS, hwn⟩, rfl⟩
            constructor
            · refine ⟨w, hwS, rfl⟩
            · intro h_eq
              apply hwn
              apply h_unique w hwS
              exact h_eq
          · exact h_sup
        rw [Set.image_union, Set.image_singleton, h_eq]
        apply PowersetSetoid.substitutivity
        · exact hx1
        · exact hxy.1
    · let S2 := Prod.snd '' S
      let x2 := x.2
      let y2 := y.2
      have hx2 : x2 ∈ S2 := ⟨x, hx, rfl⟩
      have h_sub : Prod.snd '' (S \ {x}) ⊆ S2 := by
        intro z hz; rcases hz with ⟨w, hw, rfl⟩; use w; exact ⟨hw.1, rfl⟩
      have h_sup : S2 \ {x2} ⊆ Prod.snd '' (S \ {x}) := by
        intro z hz
        rcases hz with ⟨⟨w, hw, rfl⟩, hneq⟩
        use w
        constructor
        · constructor
          · exact hw
          · intro h_eq
            rw [h_eq] at hneq
            contradiction
        · rfl
      by_cases h_unique : ∃ w ∈ S, w.2 = x2 ∧ w ≠ x
      · rcases h_unique with ⟨w, hw, hw2, hwn⟩
        have h_eq : Prod.snd '' (S \ {x}) = S2 := by
          apply Set.Subset.antisymm
          · exact h_sub
          · intro z hz
            if hzx : z = x2 then
              rw [hzx, ←hw2]
              refine ⟨w, ?_, rfl⟩
              exact ⟨hw, hwn⟩
            else
              rcases hz with ⟨u, hu, rfl⟩
              refine ⟨u, ?_, rfl⟩
              exact ⟨hu, by intro h; rw [h] at hzx; contradiction⟩
        rw [Set.image_union, Set.image_singleton, h_eq]
        apply PowersetSetoid.setEquiv_Equiv.symm
        have h_ins := PowersetSetoid.insert_congruence S2 S2 x2 y2
          (PowersetSetoid.setEquiv_Equiv.refl S2) hxy.2
        simp only [Set.union_singleton, Set.insert_eq_of_mem hx2] at h_ins
        simp only [Set.union_singleton]
        exact h_ins
      · push_neg at h_unique
        have h_eq : Prod.snd '' (S \ {x}) = S2 \ {x2} := by
          apply Set.Subset.antisymm
          · intro z hz
            rcases hz with ⟨w, ⟨hwS, hwn⟩, rfl⟩
            constructor
            · refine ⟨w, hwS, rfl⟩
            · intro h_eq
              apply hwn
              apply h_unique w hwS
              exact h_eq
          · exact h_sup
        rw [Set.image_union, Set.image_singleton, h_eq]
        apply PowersetSetoid.substitutivity
        · exact hx2
        · exact hxy.2
end TropicalMatroid
