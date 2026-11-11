/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.FiniteIdealOpenExtension

/-!
# Realizing a prescribed finite closed patch as an open in an ambient thickening

A finite closed thickening on a quasicompact ambient open extends to
finite equations in the whole ambient scheme. The resulting ambient
closed thickening contains the original closed subscheme, and the
prescribed patch is its literal open pullback. Both comparison squares
are retained for binary gluing.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ClosedImmersionApproximation

open Scheme.IdealSheafData

/-- A prescribed finitely presented closed patch extends to an ambient
finite closed thickening, with an open immersion of that same patch and
the actual original-source pullback square. -/
theorem exists_finitePresentation_ambient_with_open_patch
    {X Z W C : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Opens)
    (hUc : IsCompact (U : Set X))
    (j : W ⟶ Z) (p : W ⟶ U.toScheme) (sq : IsPullback j p i U.ι)
    (k : C ⟶ U.toScheme) [IsClosedImmersion k] [LocallyOfFinitePresentation k]
    (a : W ⟶ C) (ha : a ≫ k = p) :
    ∃ (Y : Scheme.{u}) (m : Y ⟶ X) (i' : Z ⟶ Y) (v : C ⟶ Y),
      IsClosedImmersion m ∧ LocallyOfFinitePresentation m ∧
      IsClosedImmersion i' ∧ IsOpenImmersion v ∧
      i' ≫ m = i ∧ IsPullback k v U.ι m ∧ IsPullback j a i' v := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hUc
  have : QuasiSeparatedSpace U.toScheme := quasiSeparatedSpace_of_quasiSeparated U.ι
  have hker : p.ker = i.ker.comap U.ι := by
    rw [← sq.isoPullback_hom_snd, Scheme.Hom.ker_comp_of_isIso,
      ← pullbackSymmetry_hom_comp_fst i U.ι, Scheme.Hom.ker_comp_of_isIso]
    exact ker_fst_of_isClosedImmersion i U.ι
  have hk : k.ker ≤ i.ker.comap U.ι :=
    (Scheme.Hom.le_ker_comp a k).trans_eq ((congrArg Scheme.Hom.ker ha).trans hker)
  have hkimage : inv k.toImage ≫ k = k.ker.subschemeι :=
    (congrArg (fun z : C ⟶ U.toScheme => inv k.toImage ≫ z)
      k.toImage_imageι.symm).trans (IsIso.inv_hom_id_assoc k.toImage k.ker.subschemeι)
  have : LocallyOfFinitePresentation k.ker.subschemeι :=
    hkimage ▸ inferInstanceAs (LocallyOfFinitePresentation (inv k.toImage ≫ k))
  obtain ⟨J, hJ⟩ := exists_finiteSubideal_comap_eq i.ker U.ι k.ker hk
  have : LocallyOfFinitePresentation J.1.subschemeι :=
    locallyOfFinitePresentation_subschemeι_of_fg J.1 J.2.2
  have hlift : J.1.subschemeι.ker ≤ (k ≫ U.ι).ker := by
    rw [ker_subschemeι, ← map_ker]
    exact le_map_iff_comap_le.mpr hJ.le
  let v : C ⟶ J.1.subscheme := IsClosedImmersion.lift J.1.subschemeι (k ≫ U.ι) hlift
  have hv : v ≫ J.1.subschemeι = k ≫ U.ι := IsClosedImmersion.lift_fac _ _ hlift
  have sqC : IsPullback k v U.ι J.1.subschemeι :=
    isPullback_of_isClosedImmersion k J.1.subschemeι v U.ι hv.symm
      (by rw [ker_subschemeι]; exact hJ)
  have : IsOpenImmersion v :=
    MorphismProperty.of_isPullback sqC (inferInstanceAs (IsOpenImmersion U.ι))
  let i' : Z ⟶ J.1.subscheme := i.toImage ≫ inclusion J.2.1
  have hi' : i' ≫ J.1.subschemeι = i := by
    change (i.toImage ≫ inclusion J.2.1) ≫ J.1.subschemeι = i
    rw [Category.assoc, inclusion_subschemeι, Scheme.Hom.toImage_imageι]
  have hcomm : j ≫ i' = a ≫ v := by
    apply (cancel_mono J.1.subschemeι).mp
    rw [Category.assoc, hi', Category.assoc, hv, ← Category.assoc, ha]
    exact sq.w
  have sq' : IsPullback j (a ≫ k) (i' ≫ J.1.subschemeι) U.ι := by
    rw [ha, hi']
    exact sq
  exact ⟨J.1.subscheme, J.1.subschemeι, i', v,
    inferInstance, inferInstance, inferInstance, inferInstance,
    hi', sqC, IsPullback.of_bot sq' hcomm sqC.flip⟩

end AlgebraicGeometry.ClosedImmersionApproximation
