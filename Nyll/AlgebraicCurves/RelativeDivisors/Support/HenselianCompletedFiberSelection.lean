/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.NormTrace.CompletionTraceSumSeparable
import Nyll.AlgebraicCurves.Places.ValuationRings.UniqueCentrePlaceProper
import Nyll.AlgebraicCurves.RelativeDivisors.Support.ClopenDivisorDecomposition
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Stalk

/-! # Completed components selected by the actual Henselian regular block

A component over a completed field extends to its integral valuation ring by
properness of the finite Cartier family. The image of its closed point is
proved to be a centre of the original place, using the original-field map
and equality of the original and completed valuations. Membership in an
open-and-closed block is unchanged under this specialization. Consequently,
the closed-fibre selection in `exists_henselian_regularBlock` selects exactly
those completed components whose valuation centres lie in the source open.

The generic component maps and their two projection formulas are precisely
the data constructed by `exists_finiteCurveTrace_completed_fibre`; no
regular/boundary matching or integral extension is assumed here. The base
ring is kept general so the statement applies directly to the actual
`K[[s]]` family after the completed-base identification.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicCurve.Place WithZero

namespace AlgebraicGeometry.Scheme.Hom

/-- An integral extension of the original completed generic point has its
closed point at a centre of the original place. The local stalk map and the
completed valuation give both inequalities in the centre condition. -/
theorem centre_of_adicCompletion_extension
    {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]
    [Algebra K C.functionField] (w : AlgebraicCurve.Place K C.functionField)
    (q : Spec (.of w.adicCompletionIntegers) ⟶ C)
    (hq : Spec.map (CommRingCat.ofHom
        (algebraMap w.adicCompletionIntegers w.adicCompletion)) ≫ q =
      Spec.map (CommRingCat.ofHom (algebraMap C.functionField w.adicCompletion)) ≫
        C.fromSpecStalk (genericPoint C)) :
    ∀ s : C.presheaf.stalk (q (IsLocalRing.closedPoint w.adicCompletionIntegers)),
      w.adicValuation (algebraMap _ C.functionField s) ≤ 1 ∧
        (s ∈ IsLocalRing.maximalIdeal _ →
          w.adicValuation (algebraMap _ C.functionField s) < 1) := by
  let z := q (IsLocalRing.closedPoint w.adicCompletionIntegers)
  let ψ : C.presheaf.stalk z ⟶ CommRingCat.of w.adicCompletionIntegers :=
    Scheme.stalkClosedPointTo q
  have hψ : ψ ≫ CommRingCat.ofHom
        (algebraMap w.adicCompletionIntegers w.adicCompletion) =
      C.presheaf.stalkSpecializes ((genericPoint_spec C).specializes (Set.mem_univ z)) ≫
        CommRingCat.ofHom (algebraMap C.functionField w.adicCompletion) := by
    apply Spec.map_injective
    apply (cancel_mono (C.fromSpecStalk z)).mp
    calc
      _ = Spec.map (CommRingCat.ofHom
          (algebraMap w.adicCompletionIntegers w.adicCompletion)) ≫ q := by
        rw [Spec.map_comp, Category.assoc]
        exact congrArg (fun f => Spec.map (CommRingCat.ofHom
          (algebraMap w.adicCompletionIntegers w.adicCompletion)) ≫ f)
            (Scheme.Spec_stalkClosedPointTo_fromSpecStalk q)
      _ = _ := hq
      _ = _ := by
        symm
        calc
          _ = Spec.map (CommRingCat.ofHom
              (algebraMap C.functionField w.adicCompletion)) ≫
              (Spec.map (C.presheaf.stalkSpecializes
                ((genericPoint_spec C).specializes (Set.mem_univ z))) ≫ C.fromSpecStalk z) :=
            (congrArg (fun f => f ≫ C.fromSpecStalk z) (Spec.map_comp
              (C.presheaf.stalkSpecializes
                ((genericPoint_spec C).specializes (Set.mem_univ z)))
              (CommRingCat.ofHom (algebraMap C.functionField w.adicCompletion)))).trans
                (Category.assoc _ _ _)
          _ = _ := congrArg (fun f => Spec.map (CommRingCat.ofHom
              (algebraMap C.functionField w.adicCompletion)) ≫ f)
            (Scheme.SpecMap_stalkSpecializes_fromSpecStalk
              ((genericPoint_spec C).specializes (Set.mem_univ z)))
  intro s
  have hs : algebraMap C.functionField w.adicCompletion
      (algebraMap (C.presheaf.stalk z) C.functionField s) =
        algebraMap w.adicCompletionIntegers w.adicCompletion (ψ.hom s) := by
    exact (congrArg (fun f => f.hom s) hψ).symm
  have hv : w.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) =
      (Valued.v : Valuation w.adicCompletion ℤᵐ⁰)
        (algebraMap w.adicCompletionIntegers w.adicCompletion (ψ.hom s)) := by
    have h := AlgebraicCurve.valued_algebraMap_adicCompletion w
      (algebraMap (C.presheaf.stalk z) C.functionField s)
    change Valued.v (algebraMap C.functionField w.adicCompletion
      (algebraMap (C.presheaf.stalk z) C.functionField s)) =
        w.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) at h
    exact h.symm.trans (congrArg Valued.v hs)
  constructor
  · rw [hv]
    exact (ψ.hom s).property
  · intro hsm
    have hψm : ψ.hom s ∈ IsLocalRing.maximalIdeal w.adicCompletionIntegers := by
      rw [IsLocalRing.mem_maximalIdeal] at hsm ⊢
      exact fun hu => hsm ((isUnit_map_iff ψ.hom s).mp hu)
    rw [hv]
    exact (Valuation.mem_maximalIdeal_iff
      (v := (Valued.v : Valuation w.adicCompletion ℤᵐ⁰))).mp hψm

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.RelEffCartierDiv

/-- Extend a completed component of a genuine Cartier family to its
valuation ring and compute its membership in a selected Henselian block.
Only the already computed generic projection formulas are inputs. -/
theorem exists_completed_component_specialization
    {R K : Type u} [CommRing R] [IsLocalRing R] [Field K]
    {C S : Scheme.{u}} [IsIntegral C] [Algebra K C.functionField]
    {c : C ⟶ S} {n : ℕ} {t : Spec (.of R) ⟶ S}
    (D : RelEffCartierDiv c n t) (U : C.Opens)
    (V : D.I.subscheme.Opens) (hV : IsClosed (V : Set D.I.subscheme))
    (hsel : pullback.fst (D.I.subschemeι ≫ pullback.snd c t)
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ⁻¹'
          (V : Set D.I.subscheme) =
      (pullback.fst (D.I.subschemeι ≫ pullback.snd c t)
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫
        D.I.subschemeι ≫ pullback.fst c t) ⁻¹' (U : Set C))
    (w : AlgebraicCurve.Place K C.functionField)
    (a : R →+* w.adicCompletionIntegers) [IsLocalHom a]
    (ξ : Spec (.of w.adicCompletion) ⟶ D.I.subscheme)
    (hbase : ξ ≫ D.I.subschemeι ≫ pullback.snd c t =
      Spec.map (CommRingCat.ofHom
        (algebraMap w.adicCompletionIntegers w.adicCompletion)) ≫
        Spec.map (CommRingCat.ofHom a))
    (hsource : ξ ≫ D.I.subschemeι ≫ pullback.fst c t =
      Spec.map (CommRingCat.ofHom (algebraMap C.functionField w.adicCompletion)) ≫
        C.fromSpecStalk (genericPoint C)) :
    ∃ ℓ : Spec (.of w.adicCompletionIntegers) ⟶ D.I.subscheme,
      Spec.map (CommRingCat.ofHom
        (algebraMap w.adicCompletionIntegers w.adicCompletion)) ≫ ℓ = ξ ∧
      ℓ ≫ D.I.subschemeι ≫ pullback.snd c t = Spec.map (CommRingCat.ofHom a) ∧
      let z := (ℓ ≫ D.I.subschemeι ≫ pullback.fst c t)
        (IsLocalRing.closedPoint w.adicCompletionIntegers)
      (∀ s : C.presheaf.stalk z,
        w.adicValuation (algebraMap _ C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal _ →
            w.adicValuation (algebraMap _ C.functionField s) < 1)) ∧
      (ξ (IsLocalRing.closedPoint w.adicCompletion) ∈ V ↔ z ∈ U) := by
  let p := D.I.subschemeι ≫ pullback.snd c t
  let q := D.I.subschemeι ≫ pullback.fst c t
  let j := Spec.map (CommRingCat.ofHom
    (algebraMap w.adicCompletionIntegers w.adicCompletion))
  have : IsFinite p := D.isFinite
  have hVC : ValuativeCriterion p := by
    have hp : IsProper p := inferInstance
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  let sq : ValuativeCommSq p :=
    { R := w.adicCompletionIntegers
      K := w.adicCompletion
      i₁ := ξ
      i₂ := Spec.map (CommRingCat.ofHom a)
      commSq := ⟨hbase⟩ }
  obtain ⟨hUnique⟩ := hVC sq
  let ℓ := hUnique.default.l
  have hℓ : j ≫ ℓ = ξ := hUnique.default.fac_left
  have hℓp : ℓ ≫ p = Spec.map (CommRingCat.ofHom a) := hUnique.default.fac_right
  let z := (ℓ ≫ q) (IsLocalRing.closedPoint w.adicCompletionIntegers)
  have hq : j ≫ (ℓ ≫ q) =
      Spec.map (CommRingCat.ofHom (algebraMap C.functionField w.adicCompletion)) ≫
        C.fromSpecStalk (genericPoint C) := by
    rw [← Category.assoc, hℓ]
    exact hsource
  refine ⟨ℓ, hℓ, hℓp, Scheme.Hom.centre_of_adicCompletion_extension w (ℓ ≫ q) hq, ?_⟩
  let y := ℓ (IsLocalRing.closedPoint w.adicCompletionIntegers)
  have hy : p y = IsLocalRing.closedPoint R := by
    change (ℓ ≫ p) (IsLocalRing.closedPoint w.adicCompletionIntegers) = _
    rw [hℓp]
    exact Spec_closedPoint (f := CommRingCat.ofHom a)
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let r₀ := IsLocalRing.closedPoint (IsLocalRing.ResidueField R)
  have hr : r r₀ = IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
  obtain ⟨z₀, hz₀, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := p) (g := r) y r₀ (hy.trans hr.symm)
  have hyV : y ∈ V ↔ z ∈ U := by
    have h := Set.ext_iff.mp hsel z₀
    change (pullback.fst p r z₀ ∈ V ↔ q (pullback.fst p r z₀) ∈ U) at h
    rw [hz₀] at h
    exact h
  have hs := (IsLocalRing.specializes_closedPoint
    (j (IsLocalRing.closedPoint w.adicCompletion))).map ℓ.continuous
  have hξ : ℓ (j (IsLocalRing.closedPoint w.adicCompletion)) =
      ξ (IsLocalRing.closedPoint w.adicCompletion) :=
    congrArg (fun f => f (IsLocalRing.closedPoint w.adicCompletion)) hℓ
  constructor
  · intro hx
    exact hyV.mp (hs.mem_closed hV (hξ.symm ▸ hx))
  · intro hz
    exact hξ ▸ hs.mem_open V.isOpen (hyV.mpr hz)

/-- For the block constructed by the Henselian selection theorem, every
completed generic component has an integral specialization and is selected
exactly when its actual valuation centre belongs to the prescribed open. -/
theorem exists_henselian_regularBlock_completed_components
    {R K : Type u} [CommRing R] [HenselianLocalRing R] [Field K]
    {C S : Scheme.{u}} [IsIntegral C] [Algebra K C.functionField]
    {c : C ⟶ S} {n : ℕ} {t : Spec (.of R) ⟶ S}
    (D : RelEffCartierDiv c n t) (U : C.Opens) :
    ∃ V : D.I.subscheme.Opens, IsClosed (V : Set D.I.subscheme) ∧
      ∃ (m : ℕ) (D₀ : RelEffCartierDiv c m t),
        D₀.I = (V.ι ≫ D.I.subschemeι).ker ∧ D₀.SupportedIn U ∧
        ∀ (w : AlgebraicCurve.Place K C.functionField)
          (a : R →+* w.adicCompletionIntegers) [IsLocalHom a]
          (ξ : Spec (.of w.adicCompletion) ⟶ D.I.subscheme),
          (ξ ≫ D.I.subschemeι ≫ pullback.snd c t =
            Spec.map (CommRingCat.ofHom
              (algebraMap w.adicCompletionIntegers w.adicCompletion)) ≫
              Spec.map (CommRingCat.ofHom a)) →
          (ξ ≫ D.I.subschemeι ≫ pullback.fst c t =
            Spec.map (CommRingCat.ofHom (algebraMap C.functionField w.adicCompletion)) ≫
              C.fromSpecStalk (genericPoint C)) →
          ∃ z : C,
            (∀ s : C.presheaf.stalk z,
              w.adicValuation (algebraMap _ C.functionField s) ≤ 1 ∧
                (s ∈ IsLocalRing.maximalIdeal _ →
                  w.adicValuation (algebraMap _ C.functionField s) < 1)) ∧
            (ξ (IsLocalRing.closedPoint w.adicCompletion) ∈ V ↔ z ∈ U) := by
  obtain ⟨V, hV, hsel, m, D₀, hD₀, hU⟩ := D.exists_henselian_regularBlock U
  refine ⟨V, hV, m, D₀, hD₀, hU, ?_⟩
  intro w a ha ξ hbase hsource
  obtain ⟨ℓ, _, _, hcentre, hmem⟩ := D.exists_completed_component_specialization
    U V hV hsel w a ξ hbase hsource
  exact ⟨_, hcentre, hmem⟩

end AlgebraicGeometry.RelEffCartierDiv
