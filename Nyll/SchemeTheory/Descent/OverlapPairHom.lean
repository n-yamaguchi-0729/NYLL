/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.RadicialDescentCocycle

/-!
# Reindexing the original overlap morphism

The existing `pairHom` is natural for the actual cartesian maps. Therefore
its equation on the actual threefold pullback implies the equation on any
compatible triple. These lemmas use no geometric hypothesis on the base
morphism, and preserve the original overlap map throughout.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteEtale

variable {S Y T T' : Scheme.{u}} (q : Y ⟶ S) (V : Over Y)
  (η : (Over.pullback (Limits.pullback.fst q q)).obj V ⟶
    (Over.pullback (Limits.pullback.snd q q)).obj V)

/-- Naturality of the actual pair lift for morphisms with the two
specified cartesian projections. -/
lemma pairLift_comp_of_projections
    (a b : T ⟶ Y) (hab : a ≫ q = b ≫ q)
    (a' b' : T' ⟶ Y) (hab' : a' ≫ q = b' ≫ q)
    (k : T' ⟶ T) (ha : k ≫ a = a') (hb : k ≫ b = b')
    (K : Limits.pullback V.hom a' ⟶ Limits.pullback V.hom a)
    (hK₁ : K ≫ Limits.pullback.fst V.hom a = Limits.pullback.fst V.hom a')
    (hK₂ : K ≫ Limits.pullback.snd V.hom a = Limits.pullback.snd V.hom a' ≫ k) :
    K ≫ pairLift q V a b hab = pairLift q V a' b' hab' := by
  have hk : k ≫ Limits.pullback.lift a b hab = Limits.pullback.lift a' b' hab' := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, ha, Limits.pullback.lift_fst]
    · rw [Category.assoc, Limits.pullback.lift_snd, hb, Limits.pullback.lift_snd]
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, pairLift_fst, hK₁, pairLift_fst]
  · rw [Category.assoc, pairLift_snd, ← Category.assoc, hK₂,
      Category.assoc, hk, pairLift_snd]

/-- Reindexing the original overlap morphism commutes with the actual
cartesian maps, including its projection into the original cover. -/
lemma pairHom_naturality_of_projections
    (a b : T ⟶ Y) (hab : a ≫ q = b ≫ q)
    (a' b' : T' ⟶ Y) (hab' : a' ≫ q = b' ≫ q)
    (k : T' ⟶ T) (ha : k ≫ a = a') (hb : k ≫ b = b')
    (K₁ : Limits.pullback V.hom a' ⟶ Limits.pullback V.hom a)
    (K₂ : Limits.pullback V.hom b' ⟶ Limits.pullback V.hom b)
    (hK₁₁ : K₁ ≫ Limits.pullback.fst V.hom a = Limits.pullback.fst V.hom a')
    (hK₁₂ : K₁ ≫ Limits.pullback.snd V.hom a = Limits.pullback.snd V.hom a' ≫ k)
    (hK₂₁ : K₂ ≫ Limits.pullback.fst V.hom b = Limits.pullback.fst V.hom b')
    (hK₂₂ : K₂ ≫ Limits.pullback.snd V.hom b = Limits.pullback.snd V.hom b' ≫ k) :
    K₁ ≫ (pairHom q V η a b hab).left =
      (pairHom q V η a' b' hab').left ≫ K₂ := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, pairHom_fst, ← Category.assoc,
      pairLift_comp_of_projections q V a b hab a' b' hab' k ha hb K₁ hK₁₁ hK₁₂,
      Category.assoc, hK₂₁, pairHom_fst]
  · rw [Category.assoc, pairHom_snd, hK₁₂, Category.assoc, hK₂₂,
      pairHom_snd_assoc]

/-- The cocycle of the original overlap map on the chosen genuine triple
fiber product gives its cocycle on every compatible triple of maps. -/
theorem pairHom_cocycle_of_triple
    (hθ :
      pairHom q V η (radicialTripleFirst q) (radicialTripleSecond q)
          (radicialTriple_first_second q) ≫
        pairHom q V η (radicialTripleSecond q) (radicialTripleThird q)
          (radicialTriple_second_third q) =
        pairHom q V η (radicialTripleFirst q) (radicialTripleThird q)
          (radicialTriple_first_third q))
    (a b c : T ⟶ Y) (hab : a ≫ q = b ≫ q) (hbc : b ≫ q = c ≫ q) :
    pairHom q V η a b hab ≫ pairHom q V η b c hbc =
      pairHom q V η a c (hab.trans hbc) := by
  let k : T ⟶ radicialTriple q :=
    Limits.pullback.lift (Limits.pullback.lift a b hab) (Limits.pullback.lift a c (hab.trans hbc))
      (by rw [Limits.pullback.lift_fst, Limits.pullback.lift_fst])
  have hk₁ : k ≫ radicialTripleFirst q = a := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun r => r ≫ Limits.pullback.fst q q)
        (Limits.pullback.lift_fst (Limits.pullback.lift a b hab)
          (Limits.pullback.lift a c (hab.trans hbc)) _)).trans
            (Limits.pullback.lift_fst a b hab))
  have hk₂ : k ≫ radicialTripleSecond q = b := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun r => r ≫ Limits.pullback.snd q q)
        (Limits.pullback.lift_fst (Limits.pullback.lift a b hab)
          (Limits.pullback.lift a c (hab.trans hbc)) _)).trans
            (Limits.pullback.lift_snd a b hab))
  have hk₃ : k ≫ radicialTripleThird q = c := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun r => r ≫ Limits.pullback.snd q q)
        (Limits.pullback.lift_snd (Limits.pullback.lift a b hab)
          (Limits.pullback.lift a c (hab.trans hbc)) _)).trans
            (Limits.pullback.lift_snd a c (hab.trans hbc)))
  let K₁ : Limits.pullback V.hom a ⟶ Limits.pullback V.hom (radicialTripleFirst q) :=
    Limits.pullback.lift (Limits.pullback.fst V.hom a) (Limits.pullback.snd V.hom a ≫ k) (by
      rw [Category.assoc, hk₁]
      exact Limits.pullback.condition)
  let K₂ : Limits.pullback V.hom b ⟶ Limits.pullback V.hom (radicialTripleSecond q) :=
    Limits.pullback.lift (Limits.pullback.fst V.hom b) (Limits.pullback.snd V.hom b ≫ k) (by
      rw [Category.assoc, hk₂]
      exact Limits.pullback.condition)
  let K₃ : Limits.pullback V.hom c ⟶ Limits.pullback V.hom (radicialTripleThird q) :=
    Limits.pullback.lift (Limits.pullback.fst V.hom c) (Limits.pullback.snd V.hom c ≫ k) (by
      rw [Category.assoc, hk₃]
      exact Limits.pullback.condition)
  have h₁ := pairHom_naturality_of_projections q V η
    (radicialTripleFirst q) (radicialTripleSecond q) (radicialTriple_first_second q)
    a b hab k hk₁ hk₂ K₁ K₂ (Limits.pullback.lift_fst _ _ _) (Limits.pullback.lift_snd _ _ _)
      (Limits.pullback.lift_fst _ _ _) (Limits.pullback.lift_snd _ _ _)
  have h₂ := pairHom_naturality_of_projections q V η
    (radicialTripleSecond q) (radicialTripleThird q) (radicialTriple_second_third q)
    b c hbc k hk₂ hk₃ K₂ K₃ (Limits.pullback.lift_fst _ _ _) (Limits.pullback.lift_snd _ _ _)
      (Limits.pullback.lift_fst _ _ _) (Limits.pullback.lift_snd _ _ _)
  have h₃ := pairHom_naturality_of_projections q V η
    (radicialTripleFirst q) (radicialTripleThird q) (radicialTriple_first_third q)
    a c (hab.trans hbc) k hk₁ hk₃ K₁ K₃
      (Limits.pullback.lift_fst _ _ _) (Limits.pullback.lift_snd _ _ _)
      (Limits.pullback.lift_fst _ _ _) (Limits.pullback.lift_snd _ _ _)
  have hK₃ : K₃ ≫ Limits.pullback.fst V.hom (radicialTripleThird q) =
      Limits.pullback.fst V.hom c := Limits.pullback.lift_fst _ _ _
  let f₁₂ : Limits.pullback V.hom a ⟶ Limits.pullback V.hom b :=
    (pairHom q V η a b hab).left
  let f₂₃ : Limits.pullback V.hom b ⟶ Limits.pullback V.hom c :=
    (pairHom q V η b c hbc).left
  let f₁₃ : Limits.pullback V.hom a ⟶ Limits.pullback V.hom c :=
    (pairHom q V η a c (hab.trans hbc)).left
  let g₁₂ : Limits.pullback V.hom (radicialTripleFirst q) ⟶
      Limits.pullback V.hom (radicialTripleSecond q) :=
    (pairHom q V η (radicialTripleFirst q) (radicialTripleSecond q)
      (radicialTriple_first_second q)).left
  let g₂₃ : Limits.pullback V.hom (radicialTripleSecond q) ⟶
      Limits.pullback V.hom (radicialTripleThird q) :=
    (pairHom q V η (radicialTripleSecond q) (radicialTripleThird q)
      (radicialTriple_second_third q)).left
  let g₁₃ : Limits.pullback V.hom (radicialTripleFirst q) ⟶
      Limits.pullback V.hom (radicialTripleThird q) :=
    (pairHom q V η (radicialTripleFirst q) (radicialTripleThird q)
      (radicialTriple_first_third q)).left
  have hg : g₁₂ ≫ g₂₃ = g₁₃ := congrArg
    (fun r : (Over.pullback (radicialTripleFirst q)).obj V ⟶
        (Over.pullback (radicialTripleThird q)).obj V => r.left) hθ
  change K₁ ≫ g₁₂ = f₁₂ ≫ K₂ at h₁
  change K₂ ≫ g₂₃ = f₂₃ ≫ K₃ at h₂
  change K₁ ≫ g₁₃ = f₁₃ ≫ K₃ at h₃
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · change (f₁₂ ≫ f₂₃) ≫ Limits.pullback.fst V.hom c =
      f₁₃ ≫ Limits.pullback.fst V.hom c
    calc
      _ = (f₁₂ ≫ K₂ ≫ g₂₃) ≫
          Limits.pullback.fst V.hom (radicialTripleThird q) := by
        rw [Category.assoc, h₂]
        simp only [Category.assoc, hK₃]
      _ = (K₁ ≫ g₁₂ ≫ g₂₃) ≫
          Limits.pullback.fst V.hom (radicialTripleThird q) := by
        simpa only [Category.assoc] using congrArg
          (fun r => r ≫ g₂₃ ≫ Limits.pullback.fst V.hom (radicialTripleThird q)) h₁.symm
      _ = (K₁ ≫ g₁₃) ≫ Limits.pullback.fst V.hom (radicialTripleThird q) := by rw [hg]
      _ = _ := by rw [h₃, Category.assoc, hK₃]
  · change ((pairHom q V η a b hab).left ≫ (pairHom q V η b c hbc).left) ≫
        Limits.pullback.snd V.hom c = _
    rw [Category.assoc, pairHom_snd, pairHom_snd, pairHom_snd]

/-- Identity on the genuine diagonal gives identity at every test map. -/
theorem pairHom_refl_of_diagonal
    (hθ : pairHom q V η (𝟙 Y) (𝟙 Y) rfl = 𝟙 _) (a : T ⟶ Y) :
    pairHom q V η a a rfl = 𝟙 _ := by
  let K : Limits.pullback V.hom a ⟶ Limits.pullback V.hom (𝟙 Y) :=
    Limits.pullback.lift (Limits.pullback.fst V.hom a) (Limits.pullback.snd V.hom a ≫ a) (by
      rw [Category.comp_id]
      exact Limits.pullback.condition)
  have h := pairHom_naturality_of_projections q V η (𝟙 Y) (𝟙 Y) rfl
    a a rfl a (Category.comp_id a) (Category.comp_id a) K K
      (Limits.pullback.lift_fst _ _ _) (Limits.pullback.lift_snd _ _ _)
      (Limits.pullback.lift_fst _ _ _) (Limits.pullback.lift_snd _ _ _)
  rw [hθ] at h
  change K ≫ 𝟙 _ = (pairHom q V η a a rfl).left ≫ K at h
  rw [Category.comp_id] at h
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · change (pairHom q V η a a rfl).left ≫ Limits.pullback.fst V.hom a =
      (𝟙 (Limits.pullback V.hom a)) ≫ Limits.pullback.fst V.hom a
    have h' := congrArg (fun r => r ≫ Limits.pullback.fst V.hom (𝟙 Y)) h.symm
    simpa only [Category.assoc, K, Limits.pullback.lift_fst, Category.id_comp] using h'
  · exact (pairHom_snd q V η a a rfl).trans (Category.id_comp _).symm

end AlgebraicGeometry.FiniteEtale
