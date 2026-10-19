/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.OpenKummerArithmeticRootFiber

/-!
# Full coefficient-root torsor on the original arithmetic Kummer fiber

The coefficient embedding is explicit, so the fixed ambient embedding from
rational configurations can be used without choosing another field or point.
Only the coefficient action is constructed. The arithmetic monodromy action
remains the original action on the original named cover fiber.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open JacobianVarieties.Kummer Opposite TopologicalSpace
open scoped FintypeCatDiscrete

namespace AlgebraicCurve.CurveModel.OpenKummer

private theorem exists_rootCoordinate_torsor
    {κ Ω T : Type} [Field κ] [IsSepClosed κ] [Field Ω] [Nonempty T]
    (ι : κ →+* Ω) (n : ℕ+) (hn : IsUnit ((n : ℕ) : κ))
    (a : Ωˣ) (e : T ≃ {β : Ω // β ^ (n : ℕ) = (a : Ω)}) :
    ∃ t : Torsor (rootsOfUnity (n : ℕ) κ) T,
      ∀ (ζ : rootsOfUnity (n : ℕ) κ) x,
        (e (t.toMulAction.toSMul.smul ζ x)).val = ι (ζ.val : κ) * (e x).val := by
  let act (ζ : rootsOfUnity (n : ℕ) κ) (x : T) : T :=
    e.symm ⟨ι (ζ.val : κ) * (e x).val, by
      have hz : (ζ.val : κ) ^ (n : ℕ) = 1 :=
        congrArg (fun u : κˣ => (u : κ)) ((mem_rootsOfUnity _ _).mp ζ.property)
      rw [mul_pow, ← map_pow, hz, map_one, one_mul]
      exact (e x).property⟩
  have he (ζ : rootsOfUnity (n : ℕ) κ) (x : T) :
      (e (act ζ x)).val = ι (ζ.val : κ) * (e x).val :=
    congrArg Subtype.val (e.apply_symm_apply _)
  let ma : MulAction (rootsOfUnity (n : ℕ) κ) T := {
    smul := act
    one_smul := fun x => e.injective (Subtype.ext (by
      change (e (act 1 x)).val = (e x).val
      rw [he]
      change ι 1 * (e x).val = (e x).val
      rw [map_one, one_mul]))
    mul_smul := fun ζ η x => e.injective (Subtype.ext (by
      change (e (act (ζ * η) x)).val = (e (act ζ (act η x))).val
      rw [he, he, he]
      change ι ((ζ.val : κ) * (η.val : κ)) * (e x).val = _
      rw [map_mul, mul_assoc])) }
  let := ma
  have hzero (x : T) : (e x).val ≠ 0 := by
    intro hx
    have hp := (e x).property
    rw [hx, zero_pow n.ne_zero] at hp
    exact a.ne_zero hp.symm
  have hu (x y : T) : ∃! ζ : rootsOfUnity (n : ℕ) κ, ζ • x = y := by
    obtain ⟨ζ, hζ, huniq⟩ := EtaleFundamentalGroups.Kummer.existsUnique_rootScale
      ι n hn (e x).val (e y).val (hzero x) ((e x).property.trans (e y).property.symm)
    refine ⟨ζ, e.injective (Subtype.ext ((he ζ x).trans hζ)), ?_⟩
    intro η hη
    apply huniq η
    exact (he η x).symm.trans (congrArg (fun z : T => (e z).val) hη)
  let d (x y : T) : rootsOfUnity (n : ℕ) κ := (hu y x).exists.choose
  have hd (x y : T) : d x y • y = x := (hu y x).exists.choose_spec
  let t : Torsor (rootsOfUnity (n : ℕ) κ) T := {
    toMulAction := ma
    sdiv := d
    nonempty := inferInstance
    sdiv_smul' := hd
    smul_sdiv' := fun ζ x => (hu x (ζ • x)).unique (hd (ζ • x) x) rfl }
  exact ⟨t, he⟩

/-- The full root group of the specified separably closed coefficient field
acts simply transitively on the original arithmetic named-cover fiber.
The displayed semilinearity is proved for the original generic Galois action,
without replacing it by an action transported through the coordinate map. -/
theorem exists_arithmeticKummerFiber_fullRootTorsor
    {K F : Type} [Field K] [Field F] [Algebra K F]
    (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
    (w : Pic0.openKummerUnits K F S n)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hi : ∀ (y : X) (x : closedPoints M.C), x.val = j y → M.placeOfPoint x ∉ S)
    (hn : IsUnit ((n : ℕ) : K))
    {Ω : Type} [Field Ω] [IsSepClosed Ω] [Algebra X.functionField Ω]
    [IsSepClosure X.functionField Ω]
    {κ : Type} [Field κ] [IsSepClosed κ] (ι : κ →+* Ω)
    (hnκ : IsUnit ((n : ℕ) : κ)) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    let W := M.openKummerCover S n hn w j hj hi
    ∃ a : Ωˣ, ∃ e : (FiniteEtale.fiber ξ).obj W ≃ {β : Ω // β ^ (n : ℕ) = (a : Ω)},
      ∃ t : Torsor (rootsOfUnity (n : ℕ) κ) ((FiniteEtale.fiber ξ).obj W),
        (∀ (ζ : rootsOfUnity (n : ℕ) κ) x,
          (e (t.toMulAction.toSMul.smul ζ x)).val = ι (ζ.val : κ) * (e x).val) ∧
        ∀ (σ : Ω ≃ₐ[X.functionField] Ω) (ζ : rootsOfUnity (n : ℕ) κ) x,
          let g := FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η
            (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω) σ)
          (e (g • (t.toMulAction.toSMul.smul ζ x))).val =
            σ (ι (ζ.val : κ)) * (e (g • x)).val := by
  intro η ξ W
  obtain ⟨a, e, _hscale, hg⟩ := exists_arithmeticKummerFiber_rootEquiv
    M S n w j hj hi hn (Ω := Ω)
  let : Nonempty ((FiniteEtale.fiber ξ).obj W) :=
    kummerGeometricFiber_nonempty M S n w j hj hi hn ξ
  obtain ⟨t, ht⟩ := exists_rootCoordinate_torsor ι n hnκ a e
  refine ⟨a, e, t, ht, ?_⟩
  intro σ ζ x g
  exact (hg σ _).trans ((congrArg σ (ht ζ x)).trans
    ((map_mul σ _ _).trans (congrArg (σ (ι (ζ.val : κ)) * ·) (hg σ x).symm)))

end AlgebraicCurve.CurveModel.OpenKummer
