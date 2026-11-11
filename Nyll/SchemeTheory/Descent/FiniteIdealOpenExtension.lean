/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.FiniteClosedThickeningRecovery
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Extending finite ideal equations from an open subscheme

A finitely presented closed subscheme on a quasicompact open can be
extended by finitely many global ideal equations while staying inside a
prescribed ambient ideal. The intersection with its schematic closure
first gives an arbitrary global ideal with the correct restriction.
Exact finite-stage recovery then supplies finitely many global equations
without changing that restriction.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

private theorem comap_inf_of_isOpenImmersion (I₁ I₂ : X.IdealSheafData)
    (j : Y ⟶ X) [IsOpenImmersion j] :
    (I₁ ⊓ I₂).comap j = I₁.comap j ⊓ I₂.comap j := by
  ext U : 2
  simp only [ideal_inf, Pi.inf_apply, ideal_comap_of_isOpenImmersion, Ideal.comap_inf]

private theorem comap_map_of_isOpenImmersion (K : Y.IdealSheafData)
    (j : Y ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    (K.map j).comap j = K := by
  have hrange : Set.range (K.subschemeι ≫ j) ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    exact ⟨K.subschemeι x, rfl⟩
  have hlift : IsOpenImmersion.lift j (K.subschemeι ≫ j) hrange = K.subschemeι := by
    apply (cancel_mono j).mp
    exact IsOpenImmersion.lift_fac j (K.subschemeι ≫ j) hrange
  have sq := IsOpenImmersion.isPullback_lift_id (K.subschemeι ≫ j) j hrange
  rw [hlift] at sq
  ext U : 2
  rw [ideal_comap_of_isOpenImmersion]
  change ((K.subschemeι ≫ j).ker.ideal
    ⟨j ''ᵁ U, U.2.image_of_isOpenImmersion j⟩).comap (j.appIso U).inv.hom = K.ideal U
  simpa only [K.ker_subschemeι] using
    (ker_ideal_of_isPullback_of_isOpenImmersion
      (K.subschemeι ≫ j) K.subschemeι (𝟙 K.subscheme) j sq U).symm

private theorem ker_pullback_subscheme_snd (I : X.IdealSheafData) (j : Y ⟶ X) :
    (pullback.snd I.subschemeι j).ker = I.comap j := by
  rw [← pullbackSymmetry_hom_comp_fst I.subschemeι j, Scheme.Hom.ker_comp_of_isIso]
  rfl

/-- Finite equations on a quasicompact open extend to finite global
equations inside the original ideal, with literal equality of the
restricted ideal sheaf. -/
theorem exists_finiteSubideal_comap_eq
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (I : X.IdealSheafData) (j : Y ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (K : Y.IdealSheafData) [LocallyOfFinitePresentation K.subschemeι]
    (hK : K ≤ I.comap j) :
    ∃ J : FiniteSubideal I, J.1.comap j = K := by
  let H : X.IdealSheafData := I ⊓ K.map j
  have hHK : H.comap j = K := by
    rw [comap_inf_of_isOpenImmersion, comap_map_of_isOpenImmersion, inf_eq_right.mpr hK]
  have : LocallyOfFinitePresentation (H.comap j).subschemeι := hHK.symm ▸ inferInstance
  have : LocallyOfFinitePresentation (pullback.fst j H.subschemeι) := by
    rw [← H.comapIso_inv_subschemeι j]
    infer_instance
  have : LocallyOfFinitePresentation (pullback.snd H.subschemeι j) := by
    rw [← pullbackSymmetry_hom_comp_fst H.subschemeι j]
    infer_instance
  obtain ⟨J, hJ⟩ := exists_isIso_baseChangeProjection H j
  have : IsIso ((finiteSubschemeBaseChangeCone H j).π.app J) := hJ
  refine ⟨⟨J.unop.1, J.unop.2.1.trans inf_le_left, J.unop.2.2⟩, ?_⟩
  change J.unop.1.comap j = K
  rw [← hHK, ← ker_pullback_subscheme_snd J.unop.1 j, ← ker_pullback_subscheme_snd H j]
  exact (Scheme.Hom.ker_comp_of_isIso
    ((finiteSubschemeBaseChangeCone H j).π.app J)
    (pullback.snd J.unop.1.subschemeι j)).symm.trans
      (congrArg Scheme.Hom.ker (finiteSubschemeBaseChangeCone_projection_snd H j J))

end AlgebraicGeometry.Scheme.IdealSheafData
