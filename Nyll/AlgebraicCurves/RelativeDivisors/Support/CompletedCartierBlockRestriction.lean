/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.Support.ClopenDivisorDecomposition
import Mathlib.AlgebraicGeometry.Limits

/-! # Restriction of the actual completed Cartier coproduct to a clopen block

The selected component spectra are restricted along the actual open-and-closed
immersion. The resulting isomorphism is then transported through the full
Cartier kernel ideal and its pullback, so both ambient projections are retained.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

private theorem exists_sigma_field_open_iso
    {I : Type u} (F : I → Type u) [∀ i, Field (F i)]
    {X : Scheme.{u}} (e : (∐ fun i => Spec (.of (F i))) ≅ X)
    (V : X.Opens) (P : I → Prop)
    (hP : ∀ i, (Sigma.ι (fun i => Spec (.of (F i))) i ≫ e.hom)
      (IsLocalRing.closedPoint (F i)) ∈ V ↔ P i) :
    ∃ d : (∐ fun i : {i // P i} => Spec (.of (F i.1))) ≅ V,
      ∀ i : {i // P i},
        Sigma.ι (fun i : {i // P i} => Spec (.of (F i.1))) i ≫ d.hom ≫ V.ι =
          Sigma.ι (fun i => Spec (.of (F i))) i.1 ≫ e.hom := by
  classical
  let Z : I → Scheme.{u} := fun i => Spec (.of (F i))
  let f (i : {i // P i}) : Z i.1 ⟶ X := Sigma.ι Z i.1 ≫ e.hom
  have hf (i : {i // P i}) : IsOpenImmersion (f i) := inferInstance
  let d := Sigma.desc f
  have hd : IsOpenImmersion d := by
    apply isOpenImmersion_sigmaDesc
    intro i j hij
    apply Set.disjoint_iff_forall_ne.mpr
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    have hxy' : Sigma.ι Z i.1 x = Sigma.ι Z j.1 y :=
      e.hom.homeomorph.injective hxy
    have hval : i.1 = j.1 := congrArg Sigma.fst ((sigmaι_eq_iff Z _ _ _ _).mp hxy')
    exact hij (Subtype.ext hval)
  have hrange : Set.range d = Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      have hy : ∃ (i : {i // P i}) (z : Z i.1),
          Sigma.ι (fun i : {i // P i} => Z i.1) i z = y :=
        (sigmaOpenCover (fun i : {i // P i} => Z i.1)).exists_eq y
      obtain ⟨i, z, rfl⟩ := hy
      have hdpoint : d (Sigma.ι (fun i : {i // P i} => Z i.1) i z) = f i z :=
        congrArg (fun a => a z) (Sigma.ι_comp_desc f i)
      rw [hdpoint]
      have hz : z = IsLocalRing.closedPoint (F i.1) := Subsingleton.elim _ _
      rw [hz]
      exact (hP i.1).mpr i.2
    · intro hx
      have hy : ∃ (i : I) (z : Z i), Sigma.ι Z i z = e.inv x :=
        (sigmaOpenCover Z).exists_eq (e.inv x)
      obtain ⟨i, z, hz⟩ := hy
      have hz' : (Sigma.ι Z i ≫ e.hom) z = x := by
        change e.hom (Sigma.ι Z i z) = x
        rw [hz]
        exact congrArg (fun f : X ⟶ X => f x) e.inv_hom_id
      have hp : P i := (hP i).mp (by
        have hzc : IsLocalRing.closedPoint (F i) = z := Subsingleton.elim _ _
        rw [hzc, hz']
        exact hx)
      refine ⟨Sigma.ι (fun i : {i // P i} => Z i.1) ⟨i, hp⟩ z, ?_⟩
      exact (congrArg (fun a => a z) (Sigma.ι_comp_desc f ⟨i, hp⟩)).trans hz'
  let E := IsOpenImmersion.isoOfRangeEq d V.ι hrange
  refine ⟨E, ?_⟩
  intro i
  rw [IsOpenImmersion.isoOfRangeEq_hom_fac, Sigma.ι_comp_desc]

private def idealSubschemeIso {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    I.subscheme ≅ J.subscheme := eqToIso (congrArg Scheme.IdealSheafData.subscheme h)

private theorem idealSubschemeIso_hom_ι {X : Scheme.{u}} {I J : X.IdealSheafData}
    (h : I = J) : (idealSubschemeIso h).hom ≫ J.subschemeι = I.subschemeι := by
  cases h
  exact Category.id_comp _

namespace RelEffCartierDiv

/-- Restrict a labelled completed fibre to the actual Cartier block cut
out by a clopen subset. The full ideal equality, rather than support alone,
identifies its base change; its ambient immersion is computed explicitly. -/
theorem exists_completed_clopen_block_iso
    {C S R T : Scheme.{u}} {c : C ⟶ S} {r : R ⟶ S} {t : T ⟶ S}
    {n k : ℕ} (D : RelEffCartierDiv c n r)
    (W : D.I.subscheme.Opens) (hW : IsClosed (W : Set D.I.subscheme))
    (D₁ : RelEffCartierDiv c k r) (hI : D₁.I = (W.ι ≫ D.I.subschemeι).ker)
    (a : T ⟶ R) (ha : a ≫ r = t)
    {I : Type u} (F : I → Type u) [∀ i, Field (F i)]
    (e : (∐ fun i => Spec (.of (F i))) ≅ (D.pullbackAlong a ha).I.subscheme)
    (P : I → Prop)
    (hP : ∀ i,
      (Sigma.ι (fun i => Spec (.of (F i))) i ≫ e.hom ≫
        comapSubschemeMapOver D.I a ha) (IsLocalRing.closedPoint (F i)) ∈ W ↔ P i) :
    ∃ d : (∐ fun i : {i // P i} => Spec (.of (F i.1))) ≅
        (D₁.pullbackAlong a ha).I.subscheme,
      ∀ i : {i // P i},
        Sigma.ι (fun i : {i // P i} => Spec (.of (F i.1))) i ≫ d.hom ≫
          (D₁.pullbackAlong a ha).I.subschemeι =
        Sigma.ι (fun i => Spec (.of (F i))) i.1 ≫ e.hom ≫
          (D.pullbackAlong a ha).I.subschemeι := by
  let f : pullback c t ⟶ pullback c r := mapOnProdOver c a ha
  let m : (D.pullbackAlong a ha).I.subscheme ⟶ D.I.subscheme :=
    comapSubschemeMapOver D.I a ha
  let W' : (D.pullbackAlong a ha).I.subscheme.Opens := m ⁻¹ᵁ W
  have hWι : IsClosedImmersion W.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hW)
  let j := W.ι ≫ D.I.subschemeι
  have hj : IsClosedImmersion j := inferInstance
  let eW : W.toScheme ≅ D₁.I.subscheme :=
    asIso j.toImage ≪≫ idealSubschemeIso hI.symm
  have heW : eW.hom ≫ D₁.I.subschemeι = j := by
    rw [Iso.trans_hom, Category.assoc, idealSubschemeIso_hom_ι]
    exact j.toImage_imageι
  have hSquare := (isPullback_morphismRestrict m W).paste_vert
    (isPullback_comapSubschemeMapOver D.I a ha)
  have hSquare' : IsPullback ((m ∣_ W) ≫ eW.hom)
      (W'.ι ≫ (D.pullbackAlong a ha).I.subschemeι) D₁.I.subschemeι f := by
    apply hSquare.of_iso (Iso.refl _) eW (Iso.refl _) (Iso.refl _)
    · simp only [Iso.refl_hom, Category.id_comp]
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl
    · simp only [Iso.refl_hom, Category.comp_id]
      exact heW.symm
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl
  let eBlock : W'.toScheme ≅ (D₁.pullbackAlong a ha).I.subscheme :=
    hSquare'.isoPullback ≪≫ pullbackSymmetry _ _ ≪≫ (D₁.I.comapIso f).symm
  have hBlock : eBlock.hom ≫ (D₁.pullbackAlong a ha).I.subschemeι =
      W'.ι ≫ (D.pullbackAlong a ha).I.subschemeι := by
    change hSquare'.isoPullback.hom ≫
      (pullbackSymmetry D₁.I.subschemeι f).hom ≫
      (D₁.I.comapIso f).inv ≫ (D₁.I.comap f).subschemeι = _
    rw [Scheme.IdealSheafData.comapIso_inv_subschemeι,
      pullbackSymmetry_hom_comp_fst, hSquare'.isoPullback_hom_snd]
  obtain ⟨d, hd⟩ := exists_sigma_field_open_iso F e W' P hP
  refine ⟨d ≪≫ eBlock, ?_⟩
  intro i
  rw [Iso.trans_hom, Category.assoc, hBlock]
  simpa only [Category.assoc] using
    congrArg (fun f => f ≫ (D.pullbackAlong a ha).I.subschemeι) (hd i)

end RelEffCartierDiv
end AlgebraicGeometry
