/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.FiniteClosedThickeningClosedImmersion
public import Nyll.SchemeTheory.Descent.FiniteClosedThickeningInOpen

/-!
# Closed finite thickenings with two prescribed open projections

The thickening is first chosen inside the two prescribed open inverse
images, while remaining closed in the original ambient scheme. Eventual
closedness for each projection and a common finite upper bound then make
both projections closed immersions. This retains the ambient closedness
needed for separated binary gluing.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ClosedImmersionApproximation

open Scheme.IdealSheafData

/-- Finite equations simultaneously preserve the ambient closed immersion
and the closed immersions into two prescribed quasicompact opens. -/
theorem exists_finite_thickening_with_open_projections
    {P X Y : Scheme.{u}} [CompactSpace P] [QuasiSeparatedSpace P]
    [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y]
    (I : P.IdealSheafData) (f : P ⟶ X) (g : P ⟶ Y)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g]
    (U : X.Opens) (V : Y.Opens)
    (hUc : IsCompact (U : Set X)) (hVc : IsCompact (V : Set Y))
    (s : I.subscheme ⟶ U.toScheme) (t : I.subscheme ⟶ V.toScheme)
    [IsClosedImmersion s] [IsClosedImmersion t]
    (hs : I.subschemeι ≫ f = s ≫ U.ι)
    (ht : I.subschemeι ≫ g = t ≫ V.ι) :
    ∃ (C : Scheme.{u}) (c : C ⟶ P) (a : I.subscheme ⟶ C)
      (u : C ⟶ U.toScheme) (v : C ⟶ V.toScheme),
      IsClosedImmersion c ∧ LocallyOfFinitePresentation c ∧
      IsClosedImmersion u ∧ LocallyOfFinitePresentation u ∧
      IsClosedImmersion v ∧ LocallyOfFinitePresentation v ∧
      c ≫ f = u ≫ U.ι ∧ c ≫ g = v ≫ V.ι ∧ a ≫ c = I.subschemeι := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hUc
  have : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hVc
  have : QuasiSeparatedSpace U.toScheme := quasiSeparatedSpace_of_quasiSeparated U.ι
  have : QuasiSeparatedSpace V.toScheme := quasiSeparatedSpace_of_quasiSeparated V.ι
  let O : P.Opens := f ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V
  have hU : I.subschemeι ⁻¹ᵁ (f ⁻¹ᵁ U) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, hs, Scheme.Hom.comp_preimage,
      Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]
  have hV : I.subschemeι ⁻¹ᵁ (g ⁻¹ᵁ V) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, ht, Scheme.Hom.comp_preimage,
      Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]
  have hO : I.subschemeι ⁻¹ᵁ O = ⊤ := by
    change I.subschemeι ⁻¹ᵁ (f ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V) = ⊤
    rw [Scheme.Hom.preimage_inf, hU, hV, inf_top_eq]
  obtain ⟨K, hK⟩ := exists_finiteSubideal_preimage_eq_top I O hO
  have : CompactSpace K.1.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace K.1.subschemeι
  have : QuasiSeparatedSpace K.1.subscheme :=
    quasiSeparatedSpace_of_quasiSeparated K.1.subschemeι
  have : LocallyOfFinitePresentation K.1.subschemeι :=
    locallyOfFinitePresentation_subschemeι_of_fg K.1 K.2.2
  have hrU : Set.range (K.1.subschemeι ≫ f) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact (hK.ge (Set.mem_univ x)).1
  have hrV : Set.range (K.1.subschemeι ≫ g) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact (hK.ge (Set.mem_univ x)).2
  let u₀ := IsOpenImmersion.lift U.ι (K.1.subschemeι ≫ f) hrU
  let v₀ := IsOpenImmersion.lift V.ι (K.1.subschemeι ≫ g) hrV
  have hu₀ : u₀ ≫ U.ι = K.1.subschemeι ≫ f := IsOpenImmersion.lift_fac _ _ hrU
  have hv₀ : v₀ ≫ V.ι = K.1.subschemeι ≫ g := IsOpenImmersion.lift_fac _ _ hrV
  have : LocallyOfFinitePresentation u₀ :=
    MorphismProperty.of_isPullback
      (IsOpenImmersion.isPullback_lift_id (K.1.subschemeι ≫ f) U.ι hrU).flip
      (inferInstanceAs (LocallyOfFinitePresentation (K.1.subschemeι ≫ f)))
  have : LocallyOfFinitePresentation v₀ :=
    MorphismProperty.of_isPullback
      (IsOpenImmersion.isPullback_lift_id (K.1.subschemeι ≫ g) V.ι hrV).flip
      (inferInstanceAs (LocallyOfFinitePresentation (K.1.subschemeι ≫ g)))
  let a₀ : I.subscheme ⟶ K.1.subscheme := inclusion K.2.1
  have ha₀u : a₀ ≫ u₀ = s := by
    apply (cancel_mono U.ι).mp
    change (inclusion K.2.1 ≫ u₀) ≫ U.ι = s ≫ U.ι
    rw [Category.assoc, hu₀, ← Category.assoc, inclusion_subschemeι, hs]
  have ha₀v : a₀ ≫ v₀ = t := by
    apply (cancel_mono V.ι).mp
    change (inclusion K.2.1 ≫ v₀) ≫ V.ι = t ≫ V.ι
    rw [Category.assoc, hv₀, ← Category.assoc, inclusion_subschemeι, ht]
  let H := a₀.ker
  have huH : a₀.toImage ≫ (H.subschemeι ≫ u₀) = s := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, ha₀u]
  have hvH : a₀.toImage ≫ (H.subschemeι ≫ v₀) = t := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, ha₀v]
  have : IsClosedImmersion (H.subschemeι ≫ u₀) :=
    (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion a₀.toImage _).mp
      (huH.symm ▸ inferInstanceAs (IsClosedImmersion s))
  have : IsClosedImmersion (H.subschemeι ≫ v₀) :=
    (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion a₀.toImage _).mp
      (hvH.symm ▸ inferInstanceAs (IsClosedImmersion t))
  obtain ⟨J, hJ⟩ := exists_finiteSubideal_isClosedImmersion H u₀
  obtain ⟨J', hJ'⟩ := exists_finiteSubideal_isClosedImmersion H v₀
  obtain ⟨L, hJL, hJ'L⟩ := exists_ge_ge J J'
  have hLu : inclusion (show J.1 ≤ L.1 from hJL) ≫ (J.1.subschemeι ≫ u₀) =
      L.1.subschemeι ≫ u₀ := by
    rw [← Category.assoc, inclusion_subschemeι]
  have hLv : inclusion (show J'.1 ≤ L.1 from hJ'L) ≫ (J'.1.subschemeι ≫ v₀) =
      L.1.subschemeι ≫ v₀ := by
    rw [← Category.assoc, inclusion_subschemeι]
  have : IsClosedImmersion (L.1.subschemeι ≫ u₀) := hLu ▸ inferInstance
  have : IsClosedImmersion (L.1.subschemeι ≫ v₀) := hLv ▸ inferInstance
  have : LocallyOfFinitePresentation L.1.subschemeι :=
    locallyOfFinitePresentation_subschemeι_of_fg L.1 L.2.2
  let c : L.1.subscheme ⟶ P := L.1.subschemeι ≫ K.1.subschemeι
  let a : I.subscheme ⟶ L.1.subscheme := a₀.toImage ≫ inclusion L.2.1
  refine ⟨L.1.subscheme, c, a, L.1.subschemeι ≫ u₀, L.1.subschemeι ≫ v₀,
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, ?_, ?_⟩
  · exact (Category.assoc L.1.subschemeι K.1.subschemeι f).trans
      ((congrArg (fun z : K.1.subscheme ⟶ X => L.1.subschemeι ≫ z) hu₀.symm).trans
        (Category.assoc L.1.subschemeι u₀ U.ι).symm)
  · exact (Category.assoc L.1.subschemeι K.1.subschemeι g).trans
      ((congrArg (fun z : K.1.subscheme ⟶ Y => L.1.subschemeι ≫ z) hv₀.symm).trans
        (Category.assoc L.1.subschemeι v₀ V.ι).symm)
  · change (a₀.toImage ≫ inclusion L.2.1) ≫ (L.1.subschemeι ≫ K.1.subschemeι) =
      I.subschemeι
    rw [Category.assoc, ← Category.assoc (inclusion L.2.1),
      inclusion_subschemeι, ← Category.assoc, Scheme.Hom.toImage_imageι]
    exact inclusion_subschemeι K.2.1

end AlgebraicGeometry.ClosedImmersionApproximation
