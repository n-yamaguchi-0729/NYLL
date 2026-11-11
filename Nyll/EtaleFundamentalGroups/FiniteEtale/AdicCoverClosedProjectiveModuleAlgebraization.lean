/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverClosedProjectiveCokernelAlgebraization
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverClosedProjectivePresentations
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeLocality
public import Nyll.SchemeTheory.Modules.Tensor.InvertibleCoherence
public import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Projective.InvertibleTensorPow
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleDual
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleIsoEvAppTensorUnit
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Untwisted coherent algebraization of the original cover modules

Choose actual first and second compatible presentations and algebraize
their relation map over the complete local coefficient ring. The existing
invertible tensor equivalences remove both twists from its finite
quasicoherent cokernel. The transported original maps recover all closed
levels and commute with the original cover transitions.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules ProjSpace
open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_IsInvertible_isIso_ev_app_tensorUnit.AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Over a complete Noetherian local ring, the actual compatible cover
modules on a closed projective family come from a finite quasicoherent
module. The original maps recover each level after pullback and retain
all the original transition maps. -/
theorem exists_closedProjective_module_algebraization
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (n : ℕ)
    {Y : Scheme.{u}}
    (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    [IsClosedImmersion j]
    (V : MorphismProperty.Over
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤
        (level (j ≫ π R n) (IsLocalRing.maximalIdeal R) 0)) :
    let f := j ≫ π R n
    let I := IsLocalRing.maximalIdeal R
    ∃ F : Y.Modules, F.IsQuasicoherent ∧ F.IsFiniteType ∧
      ∃ s : ∀ a : ℕ, F ⟶ moduleSheaf f I V a,
        (∀ a : ℕ, IsIso
          ((Scheme.Modules.pullback (Limits.pullback.fst f (baseInclusion I a))).map (s a))) ∧
        (∀ a : ℕ, s (a + 1) ≫ moduleTransition f I V a = s a) := by
  intro f I
  let L : Y.Modules := (Scheme.Modules.pullback j).obj (twistingSheaf R n)
  obtain ⟨d, hd⟩ := exists_closedProjective_twisting_bound_compatible_presentations R I n j V
  obtain ⟨K, hK, α, hgen, hα⟩ := hd d le_rfl
  have : Finite K := hK
  obtain ⟨e, he⟩ := exists_closedProjective_twisting_bound_cokernel_algebraization
    R n j V d K α hα hgen
  obtain ⟨J, _hJ, φ, hCqc, hCft, r, hrIso, hr⟩ := he e le_rfl
  let C : Y.Modules := cokernel φ
  have : C.IsQuasicoherent := hCqc
  have : C.IsFiniteType := hCft
  have hL : IsInvertible L := IsInvertible.pullback j (isInvertible_twistingSheaf R n)
  let D : Y.Modules := L.tensorPow d
  let N : Y.Modules := L.tensorPow e
  have hD : IsInvertible D := hL.tensorPow d
  have hN : IsInvertible N := hL.tensorPow e
  obtain ⟨hDdual, hDev⟩ := hD.dual
  obtain ⟨hNdual, hNev⟩ := hN.dual
  let ED : Y.Modules ≌ Y.Modules :=
    CoevAux.tensorRightEquivalence (β_ (dual D) D ≪≫ hDev.some) hDev.some
  let EN : Y.Modules ≌ Y.Modules :=
    CoevAux.tensorRightEquivalence (β_ (dual N) N ≪≫ hNev.some) hNev.some
  let E : Y.Modules ≌ Y.Modules := ED.trans EN
  let F : Y.Modules := E.inverse.obj C
  let G₁ : Y.Modules := C ⊗ (dual N).tensorPow 1
  let G : Y.Modules := G₁ ⊗ (dual D).tensorPow 1
  have : G₁.IsQuasicoherent := IsInvertible.isQuasicoherent_tensorPow C hNdual 1
  have : G₁.IsFiniteType := IsInvertible.isFiniteType_tensorPow C hNdual 1
  have hGqc : G.IsQuasicoherent := IsInvertible.isQuasicoherent_tensorPow G₁ hDdual 1
  have hGft : G.IsFiniteType := IsInvertible.isFiniteType_tensorPow G₁ hDdual 1
  let eF : G ≅ F :=
    tensorIso (tensorIso (Iso.refl C) (tensorPowOneIso (dual N)))
      (tensorPowOneIso (dual D))
  let S : Y.Modules ≌ SheafOfModules.{u} Y.ringCatSheaf := sheafOfModulesEquivalence Y
  have hFqc : F.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (C := Y.Opens) Y.ringCatSheaf).prop_of_iso
      (S.functor.mapIso eF) hGqc
  have hFft : F.IsFiniteType :=
    SheafOfModules.IsFiniteType.of_iso (C := Y.Opens) (R := Y.ringCatSheaf)
      (S.functor.mapIso eF) hGft
  let B (a : ℕ) : Y.Modules := moduleSheaf f I V a
  let t (a : ℕ) : C ⟶ E.functor.obj (B a) := r a
  let s (a : ℕ) : F ⟶ B a := E.inverse.map (t a) ≫ E.unitIso.inv.app (B a)
  refine ⟨F, hFqc, hFft, s, ?_, ?_⟩
  · intro a
    let i : level f I a ⟶ Y := Limits.pullback.fst f (baseInclusion I a)
    let H : Y.Modules ⥤ (level f I a).Modules := Scheme.Modules.pullback i
    let _ : H.Monoidal := Scheme.Modules.pullback_monoidal i
    have : IsIso (H.map (t a)) := hrIso a
    have h₁ : IsIso (H.map (t a ▷ dual N)) := by
      rw [Functor.Monoidal.map_whiskerRight]
      infer_instance
    have h₂ : IsIso (H.map ((t a ▷ dual N) ▷ dual D)) := by
      rw [Functor.Monoidal.map_whiskerRight]
      infer_instance
    have : IsIso (H.map (E.inverse.map (t a))) := h₂
    change IsIso (H.map (E.inverse.map (t a) ≫ E.unitIso.inv.app (B a)))
    rw [Functor.map_comp]
    infer_instance
  · intro a
    let q : B (a + 1) ⟶ B a := moduleTransition f I V a
    have ht : t (a + 1) ≫ E.functor.map q = t a := hr.1 a
    calc
      s (a + 1) ≫ q =
          E.inverse.map (t (a + 1)) ≫ (E.unitIso.inv.app (B (a + 1)) ≫ q) :=
        Category.assoc _ _ _
      _ = E.inverse.map (t (a + 1)) ≫
          (E.inverse.map (E.functor.map q) ≫ E.unitIso.inv.app (B a)) :=
        congrArg (fun b => E.inverse.map (t (a + 1)) ≫ b)
          (E.unitIso.inv.naturality q).symm
      _ = (E.inverse.map (t (a + 1)) ≫ E.inverse.map (E.functor.map q)) ≫
          E.unitIso.inv.app (B a) := (Category.assoc _ _ _).symm
      _ = E.inverse.map (t (a + 1) ≫ E.functor.map q) ≫ E.unitIso.inv.app (B a) :=
        congrArg (fun b => b ≫ E.unitIso.inv.app (B a)) (E.inverse.map_comp _ _).symm
      _ = E.inverse.map (t a) ≫ E.unitIso.inv.app (B a) :=
        congrArg (fun b => E.inverse.map b ≫ E.unitIso.inv.app (B a)) ht

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
