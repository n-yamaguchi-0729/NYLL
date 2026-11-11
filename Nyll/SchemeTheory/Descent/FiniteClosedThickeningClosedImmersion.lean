/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.FiniteClosedThickeningAffineTarget
public import Nyll.SchemeTheory.Descent.FiniteIdealOpenExtension
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.Data.Finset.Order

/-!
# Finite closed thickenings preserving a closed immersion

The affine-target construction is applied on a finite affine open cover.
Its finite ideal equations extend to the original ambient ideal. A common
upper bound of these finite subideals gives the required global thickening.
The comparisons use the actual pullbacks and the native comap ideal sheaves.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

private theorem isPullback_comap_composition
    {X Y V : Scheme.{u}} (I : X.IdealSheafData) (f : X ⟶ Y) (g : V ⟶ Y) :
    IsPullback
      (subschemeMap (I.comap (pullback.fst f g)) I
        (pullback.fst f g) (I.le_map_comap (pullback.fst f g)))
      ((I.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g)
      (I.subschemeι ≫ f) g := by
  have h := isPullback_of_isClosedImmersion
    (I.comap (pullback.fst f g)).subschemeι I.subschemeι
    (subschemeMap (I.comap (pullback.fst f g)) I
      (pullback.fst f g) (I.le_map_comap (pullback.fst f g)))
    (pullback.fst f g)
    (subschemeMap_subschemeι _ _ _ _).symm
    (by rw [ker_subschemeι, ker_subschemeι])
  exact h.flip.paste_vert (IsPullback.of_hasPullback f g)

/-- A finite-type morphism between qcqs schemes that is a closed immersion
on a closed subscheme remains a closed immersion on an actual finite
closed thickening of that subscheme. -/
theorem exists_finiteSubideal_isClosedImmersion
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (I : X.IdealSheafData) (f : X ⟶ Y) [LocallyOfFiniteType f]
    [IsClosedImmersion (I.subschemeι ≫ f)] :
    ∃ J : FiniteSubideal I, IsClosedImmersion (J.1.subschemeι ≫ f) := by
  classical
  let 𝒰 := Y.affineCover.finiteSubcover
  have hlocal (v : 𝒰.I₀) : ∃ J : FiniteSubideal I,
      IsClosedImmersion
        ((J.1.comap (pullback.fst f (𝒰.f v))).subschemeι ≫
          pullback.snd f (𝒰.f v)) := by
    let g := 𝒰.f v
    let p : pullback f g ⟶ X := pullback.fst f g
    let q : pullback f g ⟶ 𝒰.X v := pullback.snd f g
    have : CompactSpace (pullback f g : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace q
    have : QuasiSeparatedSpace (pullback f g : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated p
    have : IsClosedImmersion ((I.comap p).subschemeι ≫ q) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @IsClosedImmersion.{u})
        (self := IsClosedImmersion.isStableUnderBaseChange)
        (isPullback_comap_composition I f g) inferInstance
    obtain ⟨K, hK⟩ :=
      exists_finiteSubideal_isClosedImmersion_of_isAffine (I.comap p) q
    have : LocallyOfFinitePresentation K.1.subschemeι :=
      locallyOfFinitePresentation_subschemeι_of_fg K.1 K.2.2
    obtain ⟨J, hJ⟩ := exists_finiteSubideal_comap_eq I p K.1 K.2.1
    exact ⟨J, hJ.symm ▸ hK⟩
  choose J hJ using hlocal
  obtain ⟨K, hK⟩ := Finset.exists_le (Finset.univ.image J)
  refine ⟨K, IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) 𝒰 ?_⟩
  intro v
  let g := 𝒰.f v
  let p : pullback f g ⟶ X := pullback.fst f g
  let q : pullback f g ⟶ 𝒰.X v := pullback.snd f g
  have hJK : (J v).1 ≤ K.1 :=
    hK (J v) (Finset.mem_image_of_mem J (Finset.mem_univ v))
  have hJK' : (J v).1.comap p ≤ K.1.comap p := comap_mono p hJK
  let a : (K.1.comap p).subscheme ⟶ ((J v).1.comap p).subscheme := inclusion hJK'
  have ha : a ≫ (((J v).1.comap p).subschemeι ≫ q) =
      (K.1.comap p).subschemeι ≫ q :=
    (Category.assoc a ((J v).1.comap p).subschemeι q).symm.trans
      (congrArg (fun z : (K.1.comap p).subscheme ⟶ pullback f g => z ≫ q)
        (inclusion_subschemeι hJK'))
  have : IsClosedImmersion (((J v).1.comap p).subschemeι ≫ q) := hJ v
  have : IsClosedImmersion ((K.1.comap p).subschemeι ≫ q) :=
    ha ▸ inferInstanceAs
      (IsClosedImmersion (a ≫ (((J v).1.comap p).subschemeι ≫ q)))
  let sq := isPullback_comap_composition K.1 f g
  change IsClosedImmersion (pullback.snd (K.1.subschemeι ≫ f) g)
  exact sq.isoPullback_inv_snd ▸ inferInstanceAs
    (IsClosedImmersion (sq.isoPullback.inv ≫ ((K.1.comap p).subschemeι ≫ q)))

end AlgebraicGeometry.Scheme.IdealSheafData
