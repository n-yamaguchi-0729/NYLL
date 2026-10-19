/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.Unrigidified
import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleTensorInverse
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.Data.Quot

/-! # Actual base twists and local triviality of the zero relative class -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory NeronModelInfra

namespace AlgebraicGeometry.RelPicard.Unrigidified

variable {R : Type u} [CommRing R] {C T : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))

/-- Tensoring by actual base line bundles is already an equivalence relation. -/
theorem baseTwist_equivalence : Equivalence (BaseTwist c t) := by
  refine ⟨fun M => baseTwist_of_iso (Iso.refl M.val), ?_, ?_⟩
  · intro M N h
    obtain ⟨Q, hQ, ⟨e⟩⟩ := h
    obtain ⟨Q', hQ', ⟨a⟩⟩ := hQ.exists_tensor_inverse
    refine ⟨Q', hQ', ⟨?_⟩⟩
    exact ((Iso.refl _ ⊗ᵢ e) ≪≫ (α_ _ _ _).symm ≪≫
      ((Scheme.Modules.pullbackTensorObjIso (pullback.snd c t) Q' Q).symm ⊗ᵢ
        Iso.refl _) ≪≫
      ((Scheme.Modules.pullback (pullback.snd c t)).mapIso ((β_ Q' Q) ≪≫ a) ⊗ᵢ
        Iso.refl _) ≪≫
      (Scheme.Modules.pullbackUnitIso (pullback.snd c t) ⊗ᵢ Iso.refl _) ≪≫ λ_ _).symm
  · intro M N P hMN hNP
    obtain ⟨Q, hQ, ⟨e⟩⟩ := hMN
    obtain ⟨Q', hQ', ⟨e'⟩⟩ := hNP
    refine ⟨Q' ⊗ Q, hQ'.tensor hQ, ⟨?_⟩⟩
    exact e' ≪≫ (Iso.refl _ ⊗ᵢ e) ≪≫ (α_ _ _ _).symm ≪≫
      ((Scheme.Modules.pullbackTensorObjIso (pullback.snd c t) Q' Q).symm ⊗ᵢ Iso.refl _)

/-- Equality in the actual relative quotient is witnessed by one actual base line bundle. -/
theorem classes_eq_iff_baseTwist (M N : LineBundle c t) :
    (Quot.mk _ M : Classes c t) = Quot.mk _ N ↔ BaseTwist c t M N :=
  Quot.eq.trans (baseTwist_equivalence c t).eqvGen_iff

/-- A zero relative class is actually trivial on a cover obtained by trivializing its base twist.
This construction uses no curve section or Picard representation. -/
def zeroClassTrivializationCover (M : LineBundle c t)
    (hM : (Quot.mk _ M : Classes c t) =
      Quot.mk _ ⟨𝟙_ (pullback c t).Modules, Scheme.Modules.isInvertible_unit _⟩) :
    {V : T.OpenCover // ∀ j : V.I₀, Nonempty
      ((Scheme.Modules.pullback
        (baseChangeSnd c (⟨V.f j, rfl⟩ : SchemeHomOver (V.f j ≫ t) t))).obj M.val ≅
          𝟙_ (pullback c (V.f j ≫ t)).Modules)} := by
  classical
  have ht := (classes_eq_iff_baseTwist c t
    ⟨𝟙_ (pullback c t).Modules, Scheme.Modules.isInvertible_unit _⟩ M).mp hM.symm
  let Q : T.Modules := ht.choose
  have hQ : Scheme.Modules.IsInvertible Q := ht.choose_spec.1
  let e := ht.choose_spec.2.some
  let eM : M.val ≅ (Scheme.Modules.pullback (pullback.snd c t)).obj Q := e ≪≫ ρ_ _
  choose U hx he using hQ.exists_trivialization
  let V : T.OpenCover := Scheme.Cover.mkOfCovers
    (P := (@IsOpenImmersion : MorphismProperty Scheme.{u})) T
    (fun x => (U x).toScheme) (fun x => (U x).ι)
    (fun x => ⟨x, ⟨x, hx x⟩, rfl⟩)
  refine ⟨V, fun x => ⟨?_⟩⟩
  let f : SchemeHomOver ((U x).ι ≫ t) t := ⟨(U x).ι, rfl⟩
  exact (Scheme.Modules.pullback (baseChangeSnd c f)).mapIso eM ≪≫
    (Scheme.Modules.pullbackComp (baseChangeSnd c f) (pullback.snd c t)).app Q ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_snd f)).app Q ≪≫
    ((Scheme.Modules.pullbackComp (pullback.snd c ((U x).ι ≫ t)) (U x).ι).app Q).symm ≪≫
    (Scheme.Modules.pullback (pullback.snd c ((U x).ι ≫ t))).mapIso (he x).some ≪≫
    Scheme.Modules.pullbackUnitIso _

end AlgebraicGeometry.RelPicard.Unrigidified
