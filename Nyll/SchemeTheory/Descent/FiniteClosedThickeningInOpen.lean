/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.ClosedImmersionFinitePresentationLimit
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Finite-presentation closed thickenings inside an open neighbourhood

For a closed subscheme of a qcqs ambient scheme, every open neighbourhood
contains one of its actual finite-presentation closed thickenings. Compact
inverse-limit convergence supplies the finite stage from the exhaustive
finite-subideal diagram.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

/-- An open containing the original closed subscheme contains a finite stage
of the actual finite-subideal approximation. -/
theorem exists_finiteSubideal_preimage_eq_top (I : X.IdealSheafData)
    (U : X.Opens) (hU : I.subschemeι ⁻¹ᵁ U = ⊤) :
    ∃ J : FiniteSubideal I, J.1.subschemeι ⁻¹ᵁ U = ⊤ := by
  have (J : (FiniteSubideal I)ᵒᵖ) : CompactSpace ((finiteSubschemeDiagram I).obj J) := by
    change CompactSpace J.unop.1.subscheme
    exact QuasiCompact.compactSpace_of_compactSpace J.unop.1.subschemeι
  let J₀ : FiniteSubideal I := ⟨⊥, bot_le, fun _ => Submodule.fg_bot⟩
  have h₀ : (finiteSubschemeCone I).π.app (op J₀) ⁻¹ᵁ
      (J₀.1.subschemeι ⁻¹ᵁ U) = ⊤ := by
    change inclusion J₀.2.1 ⁻¹ᵁ (J₀.1.subschemeι ⁻¹ᵁ U) = ⊤
    rw [← Scheme.Hom.comp_preimage, inclusion_subschemeι, hU]
  obtain ⟨J, h, hJ⟩ := exists_map_eq_top (finiteSubschemeDiagram I)
    (finiteSubschemeCone I) (finiteSubschemeConeIsLimit I) _ h₀
  refine ⟨J.unop, ?_⟩
  change inclusion (show J₀.1 ≤ J.unop.1 from h.unop.le) ⁻¹ᵁ
    (J₀.1.subschemeι ⁻¹ᵁ U) = ⊤ at hJ
  rwa [← Scheme.Hom.comp_preimage, inclusion_subschemeι] at hJ

/-- The finite closed thickening has an actual closed immersion of finite
presentation into the prescribed open, with its original ambient map. -/
theorem exists_finiteSubideal_closedImmersion_into_open (I : X.IdealSheafData)
    (U : X.Opens) (hU : I.subschemeι ⁻¹ᵁ U = ⊤) :
    ∃ (J : FiniteSubideal I) (j : J.1.subscheme ⟶ U.toScheme),
      IsClosedImmersion j ∧ LocallyOfFinitePresentation j ∧ j ≫ U.ι = J.1.subschemeι := by
  obtain ⟨J, hJ⟩ := exists_finiteSubideal_preimage_eq_top I U hU
  have hrange : Set.range J.1.subschemeι ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hJ.ge (Set.mem_univ x)
  let j : J.1.subscheme ⟶ U.toScheme := IsOpenImmersion.lift U.ι J.1.subschemeι hrange
  have hj : j ≫ U.ι = J.1.subschemeι := IsOpenImmersion.lift_fac _ _ hrange
  have : IsClosedImmersion (j ≫ U.ι) := hj.symm ▸ inferInstance
  have : LocallyOfFinitePresentation J.1.subschemeι :=
    locallyOfFinitePresentation_subschemeι_of_fg J.1 J.2.2
  exact ⟨J, j, IsClosedImmersion.of_comp j U.ι,
    MorphismProperty.of_isPullback
      (IsOpenImmersion.isPullback_lift_id J.1.subschemeι U.ι hrange).flip
      (inferInstanceAs (LocallyOfFinitePresentation J.1.subschemeι)), hj⟩

end AlgebraicGeometry.Scheme.IdealSheafData
