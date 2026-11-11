/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sheaves.Stalks
public import Nyll.AbelianVarieties.NeronModels.Basic
public import Nyll.AbelianVarieties.NeronModels.AbelianExtensions
public import Nyll.SchemeTheory.BaseChange.SchemeHomOver
public import Nyll.AbelianVarieties.NeronModels.Differentials.ComponentData
public import Nyll.AbelianVarieties.NeronModels.Differentials.Components
public import Nyll.AbelianVarieties.NeronModels.Differentials.Order
public import Nyll.SchemeTheory.RingTheory.Differentials.TopForms
public import Nyll.AbelianVarieties.NeronModels.LocalExtensionCharts
public import Nyll.AbelianVarieties.NeronModels.ModelCovers
public import Nyll.AbelianVarieties.NeronModels.ModelFamilies
public import Nyll.AbelianVarieties.NeronModels.StalkExtensions
public import Nyll.AbelianVarieties.NeronModels.WeakModel
public import Nyll.SchemeTheory.RingTheory.Differentials.Basic
public import Nyll.SchemeTheory.Modules.Differentials.Sections
public import Nyll.SchemeTheory.LocalGeometry.StalkPullbacks
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.BaseChange
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Basic
public import Nyll.SchemeTheory.Modules.ExteriorPower.Det
public import Nyll.SchemeTheory.Modules.ExteriorPower.PresheafExteriorPower
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Nyll.SchemeTheory.Modules.KaehlerDifferentials
public import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra
public import Nyll.SchemeTheory.Modules.Tensor.TensorSections
public import Nyll.SchemeTheory.RingTheory.Smooth.AlgebraFormallyEtaleFormallySmooth
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Minimal components measured by top differential forms

Construct a finite family of components with least differential order, identify locally
isomorphic members, and compare stalks of compatible multiplication charts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian TopologicalSpace Topology
open scoped TensorProduct
open GoodReductionJacobian.AbelianSchemePropertyBundle.NGlue
  (specGenericFibreInclusion_base_ne_closedPoint)

attribute [local instance] AlgebraicGeometry.Scheme.Hom.kaehlerPresheafModule

universe u

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.MinimalComponentSmoothness

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
    GoodReductionJacobian
open scoped TensorProduct

namespace GenericPoints

theorem pointGenericFibre_comp_genericFibreRestrict
    {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
    {X U : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (u : U ⟶ Spec (CommRingCat.of R))
    (q : U ⟶ X) (hq : q ≫ f = u) (η : U) (x : X)
    [Algebra R (U.presheaf.stalk η)]
    (halgU : U.fromSpecStalk η ≫ u = Spec.map (CommRingCat.ofHom (algebraMap R (U.presheaf.stalk
      η))))
    [Algebra R (X.presheaf.stalk x)]
    (halgX : X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk
      x))))
    (F : Type u) [CommRing F] [Algebra (U.presheaf.stalk η) F] [Algebra (X.presheaf.stalk x) F]
    [Algebra R F] [Algebra K F] [IsScalarTower R (U.presheaf.stalk η) F]
    [IsScalarTower R (X.presheaf.stalk x) F] [IsScalarTower R K F]
    (hF : Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) F)) ≫ X.fromSpecStalk x =
      Spec.map (CommRingCat.ofHom (algebraMap (U.presheaf.stalk η) F)) ≫ U.fromSpecStalk η ≫ q) :
    (pointGenericFibre (K := K) (K' := F)
        (⟨U.fromSpecStalk η, halgU⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (U.presheaf.stalk η)))) u)).1 ≫
      (genericFibreRestrict R K f u ⟨q, hq⟩).1 =
    (pointGenericFibre (K := K) (K' := F)
        (⟨X.fromSpecStalk x, halgX⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk x)))) f)).1
            := by
  apply pullback.hom_ext
  · rw [Category.assoc, pointGenericFibre_coe_comp_fst, hF]
    simp only [genericFibreRestrict, pullback.lift_fst]
    rw [← Category.assoc, pointGenericFibre_coe_comp_fst, Category.assoc]
  · rw [Category.assoc, pointGenericFibre_coe_comp_snd]
    simp only [genericFibreRestrict, pullback.lift_snd]
    rw [pointGenericFibre_coe_comp_snd]

end GenericPoints

namespace StalkCharts

theorem exists_affine_chart_of_point
    {K : Type u} [Field K] {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (ω : Γ(gK.topDifferentials d, ⊤))
    (F : Type u) [Field F] [Algebra K F] (φ : Spec (CommRingCat.of F) ⟶ XK)
    (hφ : φ ≫ gK = Spec.map (CommRingCat.ofHom (algebraMap K F))) :
    ∃ (U'' : XK.Opens) (hU'' : IsAffineOpen U'') (_ : Algebra Γ(XK, U'') F)
      (_ : let : Algebra K Γ(XK, U'') := gK.sectionsAlgebra U''; IsScalarTower K Γ(XK, U'') F)
      (_ : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U'') F)) ≫ hU''.fromSpec = φ)
      (ωU'' : ⋀[Γ(XK, U'')]^d (gK.kaehlerPresheaf.obj (op U''))),
      gK.topToSections d U'' ωU'' = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω := by
  classical
  let pt : ↥(Spec (CommRingCat.of F)) := (default : PrimeSpectrum F)
  have hpt : ∀ q : ↥(Spec (CommRingCat.of F)), q = pt := fun q => Subsingleton.elim (α :=
    PrimeSpectrum F) q pt
  obtain ⟨_, ⟨(U'' : XK.Opens), (hU'' : IsAffineOpen U''), rfl⟩, hxU, -⟩ :=
    XK.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (φ.base pt)) isOpen_univ
  have hrange : Set.range φ.base ⊆ Set.range U''.ι.base := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι, hpt q]
    exact hxU
  have hl : IsOpenImmersion.lift U''.ι φ hrange ≫ U''.ι = φ := IsOpenImmersion.lift_fac _ _ _
  let ρ : Γ(XK, U'') ⟶ CommRingCat.of F := Spec.preimage (IsOpenImmersion.lift U''.ι φ hrange ≫
    hU''.isoSpec.hom)
  have hρ : Spec.map ρ ≫ hU''.fromSpec = φ := by
    rw [Spec.map_preimage, Category.assoc, ← IsAffineOpen.isoSpec_inv_ι, Iso.hom_inv_id_assoc, hl]
  let algU'' : Algebra Γ(XK, U'') F := ρ.hom.toAlgebra
  let : Algebra K Γ(XK, U'') := gK.sectionsAlgebra U''
  have hK : CommRingCat.ofHom (algebraMap K F) =
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ gK.appLE ⊤ U'' le_top) ≫ ρ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
      IsAffineOpen.SpecMap_appLE_fromSpec gK (isAffineOpen_top _) hU'' le_top, reassoc_of% hρ, hφ]
  have htower : IsScalarTower K Γ(XK, U'') F :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hK)
  obtain ⟨ωU'', hω⟩ := (AlgebraicGeometry.Scheme.Hom.topToSections_bijective_of_isAffineOpen gK d
    hU'').2
    ((gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω)
  exact ⟨U'', hU'', algU'', htower, hρ, ωU'', hω⟩

end StalkCharts

namespace StalkCharts

theorem bijective_map_comp_mapBaseChange_stalk_of_isOpenImmersion
    {R : Type u} [CommRing R] {X Z U : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : Z ⟶ Spec (CommRingCat.of R))
    (ι : U ⟶ pullback z f) [IsOpenImmersion ι] (u : ↥U)
    (g : U ⟶ Z) (hg : g = ι ≫ pullback.fst z f) (ζ : ↥Z) (hζ : g.base u = ζ)
    [algRZ : Algebra R (Z.presheaf.stalk ζ)]
    (halgZ : Z.fromSpecStalk ζ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk
      ζ))))
    [Algebra R (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))]
    (halgX : X.fromSpecStalk ((pullback.snd z f).base (ι.base u)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base (ι.base
        u))))))
    (O₀ : Type u) [CommRing O₀] [Algebra R O₀] (φ : O₀ →+* (X.presheaf.stalk ((pullback.snd z
      f).base (ι.base u))))
    (hφ : Function.Bijective φ) (hφR : φ.comp (algebraMap R O₀) = algebraMap R (X.presheaf.stalk
      ((pullback.snd z f).base (ι.base u))))
    [Algebra R (U.presheaf.stalk u)]
    [algZU : Algebra (Z.presheaf.stalk ζ) (U.presheaf.stalk u)] [Algebra O₀ (U.presheaf.stalk u)]
    (hA : ∀ a, algebraMap (Z.presheaf.stalk ζ) (U.presheaf.stalk u) a =
      (g.stalkMap u).hom ((Z.presheaf.stalkCongr (.of_eq hζ.symm)).hom a))
    (hB : ∀ b, algebraMap O₀ (U.presheaf.stalk u) b = ((ι ≫ pullback.snd z f).stalkMap u).hom (φ b))
    [towerRZU : IsScalarTower R (Z.presheaf.stalk ζ) (U.presheaf.stalk u)] [IsScalarTower R O₀
      (U.presheaf.stalk u)] :
    Function.Bijective
      ((KaehlerDifferential.map R (Z.presheaf.stalk ζ) (U.presheaf.stalk u) (U.presheaf.stalk
        u)).restrictScalars (U.presheaf.stalk u) ∘ₗ
        KaehlerDifferential.mapBaseChange R O₀ (U.presheaf.stalk u)) := by
  subst hζ
  subst hg
  let : Algebra R (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) := algRZ
  let : Algebra (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u)))
      (U.presheaf.stalk u) := algZU
  have : IsScalarTower R (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u)))
      (U.presheaf.stalk u) := towerRZU
  have hA' : ∀ a, algebraMap (Z.presheaf.stalk ((ι ≫ pullback.fst z f).base u)) (U.presheaf.stalk
    u) a =
      (ι.stalkMap u).hom (((pullback.fst z f).stalkMap (ι.base u)).hom a) := by
    intro a
    rw [hA, Scheme.Hom.stalkMap_comp]
    simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
      CommRingCat.hom_id, RingHom.id_apply]
    rfl
  have hB' : ∀ b, algebraMap O₀ (U.presheaf.stalk u) b =
      (ι.stalkMap u).hom (((pullback.snd z f).stalkMap (ι.base u)).hom (φ b)) := by
    intro b
    rw [hB, Scheme.Hom.stalkMap_comp]
    rfl
  obtain ⟨𝔔, h𝔔, e, he₁, he₂⟩ :=
    AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk f z
    (ι.base u) halgZ halgX
  have : 𝔔.IsPrime := h𝔔
  let ιu : ((pullback z f).presheaf.stalk (ι.base u)) ≃+* (U.presheaf.stalk u) := (asIso
    (ι.stalkMap u)).commRingCatIsoToRingEquiv
  have hιu : ∀ s, ιu s = (ι.stalkMap u).hom s := fun _ => rfl
  let eO : (U.presheaf.stalk u) ≃+* Localization.AtPrime 𝔔 := ιu.symm.trans e
  let algT : Algebra ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R]
    (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) (U.presheaf.stalk u) :=
    (eO.symm.toRingHom.comp (algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u)))
      ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) (Localization.AtPrime
      𝔔))).toAlgebra
  have halgT : ∀ t, algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R]
    (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) (U.presheaf.stalk u) t = ιu (e.symm
    (algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk
    ((pullback.snd z f).base (ι.base u)))) (Localization.AtPrime 𝔔) t)) :=
    fun _ => rfl
  let eT : Localization.AtPrime 𝔔 ≃ₐ[((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R]
    (X.presheaf.stalk ((pullback.snd z f).base (ι.base u))))] (U.presheaf.stalk u) :=
    AlgEquiv.ofRingEquiv (f := eO.symm) (fun _ => rfl)
  have hlocT : IsLocalization 𝔔.primeCompl (U.presheaf.stalk u) :=
    IsLocalization.isLocalization_of_algEquiv 𝔔.primeCompl eT
  let φₐ : O₀ ≃ₐ[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u))) :=
    AlgEquiv.ofBijective { toRingHom := φ, commutes' := fun r => RingHom.congr_fun hφR r } hφ
  have hφₐ : ∀ b, φₐ b = φ b := fun _ => rfl
  let Ψ : ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀) ≃ₐ[R]
    ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd
    z f).base (ι.base u)))) := Algebra.TensorProduct.congr AlgEquiv.refl φₐ
  have hΨ : ∀ (a : (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u)))) (b : O₀), Ψ (a ⊗ₜ[R]
    b) = a ⊗ₜ[R] φ b := fun a b => by
    change Algebra.TensorProduct.map (AlgEquiv.refl : (Z.presheaf.stalk ((pullback.fst z f).base
      (ι.base u))) ≃ₐ[R] (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u)))).toAlgHom
      φₐ.toAlgHom (a ⊗ₜ[R] b) = _
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  let algT₀ : Algebra ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀)
    (U.presheaf.stalk u) :=
    ((algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk
      ((pullback.snd z f).base (ι.base u)))) (U.presheaf.stalk u)).comp
      (Ψ.symm.toRingEquiv).symm.toRingHom).toAlgebra
  have hloc₀ : IsLocalization (𝔔.primeCompl.map (Ψ.symm.toRingEquiv : ((Z.presheaf.stalk
    ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base
    u)))) ≃* ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀))) (U.presheaf.stalk
    u) :=
    IsLocalization.isLocalization_of_base_ringEquiv 𝔔.primeCompl (U.presheaf.stalk u)
      Ψ.symm.toRingEquiv
  have halgT₀ : ∀ t, algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀)
    (U.presheaf.stalk u) t = algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u)))
    ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) (U.presheaf.stalk u) (Ψ t) := by
    intro t
    change algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R]
      (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) (U.presheaf.stalk u)
      ((Ψ.symm.toRingEquiv).symm t) = _
    rfl
  have : IsScalarTower (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ((Z.presheaf.stalk
    ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀) (U.presheaf.stalk u) :=
    IsScalarTower.of_algebraMap_eq (R := (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))))
      (S := ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀)) (A :=
      (U.presheaf.stalk u)) fun a => by
      rw [halgT₀, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, hΨ, map_one,
        halgT, ← he₁, RingEquiv.symm_apply_apply, hιu]
      exact hA' a
  have hBT : (algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀)
    (U.presheaf.stalk u)).comp
      (Algebra.TensorProduct.includeRight (R := R) (A := (Z.presheaf.stalk ((pullback.fst z
        f).base (ι.base u)))) (B := O₀)).toRingHom =
      algebraMap O₀ (U.presheaf.stalk u) := by
    refine RingHom.ext fun b => ?_
    rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Algebra.TensorProduct.includeRight_apply,
      halgT₀, hΨ, halgT, ← he₂, RingEquiv.symm_apply_apply, hιu, hB']
  have : IsLocalization (⊥ : Submonoid (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))))
    (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) := IsLocalization.self bot_le
  exact KaehlerDifferential.bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct R
    (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) (Z.presheaf.stalk ((pullback.fst z
    f).base (ι.base u))) O₀ (U.presheaf.stalk u)
    (⊥ : Submonoid (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u)))) hBT (𝔔.primeCompl.map
      (Ψ.symm.toRingEquiv : ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R]
      (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) ≃* ((Z.presheaf.stalk
      ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀)))

end StalkCharts

theorem tfm_KK (K K' B F : Type u) [Field K] [Field K'] [Algebra K K'] [CommRing B] [Algebra K B]
    [Field F]
    [Algebra B F] [Algebra K F] [Algebra K' F] [IsScalarTower K B F] [IsScalarTower K K' F]
    (d : ℕ) (ω : ⋀[B]^d (Ω[B⁄K])) :
    TopFormOrder.topFormMap K K' F F d (TopFormOrder.topFormMap K K B F d ω) =
      TopFormOrder.topFormMap K K' B F d ω := by
  rw [NeronModelInfra.TopFormOrder.topFormMap_topFormMap K K K' B F F d ω]

theorem tfm_KE (K K' B E F : Type u) [Field K] [Field K'] [Algebra K K'] [CommRing B] [Algebra K
    B] [Field E] [Field F]
    [Algebra B E] [Algebra E F] [Algebra B F] [IsScalarTower B E F]
    [Algebra K E] [IsScalarTower K B E] [Algebra K F] [Algebra K' F] [IsScalarTower K E F]
      [IsScalarTower K K' F]
    [IsScalarTower K B F]
    (d : ℕ) (ω : ⋀[B]^d (Ω[B⁄K])) :
    TopFormOrder.topFormMap K K' E F d (TopFormOrder.topFormMap K K B E d ω) =
      TopFormOrder.topFormMap K K' B F d ω := by
  rw [NeronModelInfra.TopFormOrder.topFormMap_topFormMap K K K' B E F d ω]

/-- Transfer an equality of top forms through an intermediate field. -/
private theorem topFormMap_comp_of_eq
    (K K' B C E F : Type u) [Field K] [Field K'] [Algebra K K']
    [CommRing B] [CommRing C] [Field E] [Field F]
    [Algebra K B] [algKC : Algebra K C] [algCE : Algebra C E]
    [Algebra E F] [Algebra C F] [IsScalarTower C E F]
    [algKE : Algebra K E] [towerKCE : IsScalarTower K C E]
    [Algebra K F] [Algebra K' F] [IsScalarTower K E F] [IsScalarTower K K' F]
    [Algebra B F] [IsScalarTower K B F] [IsScalarTower K C F]
    (d : ℕ) (ωB : ⋀[B]^d (Ω[B⁄K])) (ωC : ⋀[C]^d (Ω[C⁄K]))
    (θ : ⋀[E]^d (Ω[E⁄K]))
    (hBC : TopFormOrder.topFormMap K K' B F d ωB =
      TopFormOrder.topFormMap K K' C F d ωC)
    (hC : TopFormOrder.topFormMap K K C E d ωC = θ) :
    TopFormOrder.topFormMap K K' F F d (TopFormOrder.topFormMap K K B F d ωB) =
      TopFormOrder.topFormMap K K' E F d θ := by
  calc
    _ = TopFormOrder.topFormMap K K' B F d ωB := tfm_KK K K' B F d ωB
    _ = TopFormOrder.topFormMap K K' C F d ωC := hBC
    _ = TopFormOrder.topFormMap K K' E F d
        (TopFormOrder.topFormMap K K C E d ωC) := (tfm_KE K K' C E F d ωC).symm
    _ = TopFormOrder.topFormMap K K' E F d θ :=
      congrArg (TopFormOrder.topFormMap K K' E F d) hC

theorem stalkAlgebraMap_comp' {R : Type u} [CommRing R] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (f : Y ⟶ Spec (CommRingCat.of R)) (x : X) :
    (g.stalkMap x).hom.comp (stalkAlgebraMap f (g.base x)) = stalkAlgebraMap (g ≫ f) x := by
  ext r
  simp only [RingHom.comp_apply, stalkAlgebraMap_apply, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp]
  erw [Scheme.Hom.germ_stalkMap_apply]
  rfl

namespace ValuationMaps

theorem injective_of_map_irreducible_ne_zero {A B : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] (f : A →+* B) (ϖ : A) (hϖ : Irreducible ϖ) (h : f ϖ ≠ 0) :
    Function.Injective f := by
  refine (injective_iff_map_eq_zero f).mpr (fun a ha => ?_)
  by_contra ha0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  rw [map_mul, map_pow] at ha
  exact pow_ne_zero n h ((IsUnit.map f u.isUnit).mul_right_eq_zero.mp ha)

theorem map_uniformizer_ne_zero {A B : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] (f : A →+* B) (ϖ : A)
    (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (h : Ideal.map f (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B) : f ϖ ≠ 0 := by
  intro h0
  rw [hϖ, Ideal.map_span, Set.image_singleton, h0, Ideal.span_singleton_eq_bot.mpr rfl] at h
  exact IsDiscreteValuationRing.not_a_field B h.symm

theorem maximalIdeal_eq_span_map {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B]
    (f : A →+* B) (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (h : Ideal.map f (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B) :
    IsLocalRing.maximalIdeal B = Ideal.span {f ϖ} := by
  rw [← h, hϖ, Ideal.map_span, Set.image_singleton]

end ValuationMaps

end AbelianVarieties.NOSProofs.MinimalComponentSmoothness

namespace NeronModelInfra

open AbelianVarieties.NOSProofs.MinimalComponentSmoothness
open NeronModelInfra.MinimalComponentData
  (exists_ringHom_stalk_chart_comp_eq_pointGenericFibre_of_forall_specializes)

theorem
    exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK)
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤)) (hωframe : Scheme.Modules.IsFrameOn ω ⊤)
    (hleft : (∀ (L F : Type u) [Field L] [Field F] [Algebra K L] [Algebra L F] [Algebra K F]
      [IsScalarTower K L F]
        (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) gK)
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) gK)
        (U' U'' : XK.Opens) (hU' : IsAffineOpen U') (hU'' : IsAffineOpen U'')
        [Algebra Γ(XK, U') F] [Algebra Γ(XK, U'') F],
        let : Algebra K Γ(XK, U') := gK.sectionsAlgebra U'
        let : Algebra K Γ(XK, U'') := gK.sectionsAlgebra U''
        ∀ [IsScalarTower K Γ(XK, U') F] [IsScalarTower K Γ(XK, U'') F],
        Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U') F)) ≫ hU'.fromSpec = x.1 →
        Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U'') F)) ≫ hU''.fromSpec =
          (LXK.mul (Spec.map (CommRingCat.ofHom (algebraMap K F)))
            ⟨Spec.map (CommRingCat.ofHom (algebraMap L F)) ≫ a.1, by
              rw [Category.assoc, a.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                ← IsScalarTower.algebraMap_eq]⟩ x).1 →
        ∀ (ω' : ⋀[Γ(XK, U')]^d (gK.kaehlerPresheaf.obj (op U')))
          (ω'' : ⋀[Γ(XK, U'')]^d (gK.kaehlerPresheaf.obj (op U''))),
          gK.topToSections d U' ω' = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω →
          gK.topToSections d U'' ω'' = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω →
          TopFormOrder.topFormMap K L Γ(XK, U'') F d ω'' = TopFormOrder.topFormMap K L Γ(XK, U') F
            d ω'))
    (D : MinimalComponentData R K gK d ω) (hD : D.IsOmegaMinimal)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    (V : ∀ c : D.ι, ((D.C c).Y).Opens) (j : ∀ c : D.ι, SchemeHomOver ((V c).ι ≫ (D.C c).f) f)
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [IsIso e.1]
    (hyV : ∀ c, (D.C c).y ∈ V c)
    (hVK : ∀ c (y' : ↥(D.C c).Y), (D.C c).f.base y' ≠ IsLocalRing.closedPoint R → y' ∈ V c)
    (hjopen : ∀ c, IsOpenImmersion (j c).1)
    (hjchart : ∀ c, (genericFibreRestrict R K f ((V c).ι ≫ (D.C c).f) (j c)).1 ≫ e.1 =
      (genericFibreRestrict R K (D.C c).f ((V c).ι ≫ (D.C c).f) ⟨(V c).ι, rfl⟩).1 ≫ (D.C c).e.1)
    (hcover : ∀ x : ↥X, ∃ c, x ∈ Set.range (j c).1.base)
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (η : ↑(pullback z f)) (hη : (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R)
    (hmax : ∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint
      R → y = η)
    (T : ComponentReading R K gK d ω)
    (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀) (τ₀ : SchemeHomOver (U₀.ι ≫ pullback.fst z f ≫ z)
      T.f)
    (hτ₀ : (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K T.f (U₀.ι ≫ pullback.fst z f ≫ z) τ₀) T.e).1 =
            pullback.map (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U₀.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f) (hv₁ : v ≫ pullback.fst z T.f = U₀.ι ≫ pullback.fst z
      f)
    (hv₂ : v ≫ pullback.snd z T.f = τ₀.1)
    (hgen : T.y ⤳ τ₀.1.base ⟨η, hηU⟩) :
    (∃ c : D.ι, T.n = (D.C c).n) ∧
      let : Algebra ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ :
        Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := (v.stalkMap ⟨η, hηU⟩).hom.toAlgebra
      Algebra.FormallySmooth ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ :
        Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := by
  classical
  have : Smooth (pullback.fst z f) := inferInstance
  let ηU : (U₀ : Scheme.{u}) := ⟨η, hηU⟩
  let η' : ↥(pullback z T.f) := v.base ηU
  let ζ₀ : ↥Z := (pullback.fst z T.f).base η'
  have hζ₀ : (U₀.ι ≫ pullback.fst z f).base ηU = ζ₀ := by
    change (U₀.ι ≫ pullback.fst z f).base ηU = (v ≫ pullback.fst z T.f).base ηU
    rw [hv₁]
  let algR'O' : Algebra (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η') :=
    ((pullback.fst z T.f).stalkMap η').hom.toAlgebra
  let algO'O : Algebra ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU) :=
    (v.stalkMap ηU).hom.toAlgebra
  let algR'O : Algebra (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) :=
    ((v.stalkMap ηU).hom.comp ((pullback.fst z T.f).stalkMap η').hom).toAlgebra
  have : IsScalarTower (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η')
      ((U₀ : Scheme.{u}).presheaf.stalk ηU) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hFS : Algebra.FormallySmooth (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk
    ηU) := by
    have : Smooth (v ≫ pullback.fst z T.f) := by rw [hv₁]; infer_instance
    have hmem : ηU ∈ (v ≫ pullback.fst z T.f).smoothLocus := by
      rw [Scheme.Hom.smoothLocus_eq_top]; trivial
    have hfs : ((v ≫ pullback.fst z T.f).stalkMap ηU).hom.FormallySmooth :=
      (Scheme.Hom.mem_smoothLocus).mp hmem
    rw [Scheme.Hom.stalkMap_comp] at hfs
    exact hfs
  have hmain : (∃ c : D.ι, T.n = (D.C c).n) ∧
      Function.Bijective (KaehlerDifferential.mapBaseChange (Z.presheaf.stalk ζ₀)
        ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := by
    let y₁ : ↥T.Y := (pullback.snd z T.f).base η'
    have hy₁ : τ₀.1.base ηU = y₁ := by
      change τ₀.1.base ηU = (v ≫ pullback.snd z T.f).base ηU
      rw [hv₂]
    have hgen₁ : T.y ⤳ y₁ := hy₁ ▸ hgen
    have hmaxU : ∀ y : (U₀ : Scheme.{u}), y ⤳ ηU → (U₀.ι ≫ pullback.fst z f ≫ z).base y =
      IsLocalRing.closedPoint R → y = ηU := by
      intro y hy hsp
      apply Subtype.ext
      exact hmax (U₀.ι.base y) (hy.map U₀.ι.base.hom.continuous) hsp
    have e₁ : v ≫ pullback.snd z T.f ≫ T.f = U₀.ι ≫ pullback.fst z f ≫ z := by
      rw [← pullback.condition, ← Category.assoc, hv₁, Category.assoc]
    have e₂ : (U₀.ι ≫ pullback.snd z f) ≫ f = U₀.ι ≫ pullback.fst z f ≫ z := by
      rw [Category.assoc, ← pullback.condition]
    have e₃ : (v ≫ pullback.fst z T.f) ≫ z = U₀.ι ≫ pullback.fst z f ≫ z := by
      rw [hv₁, Category.assoc]
    have hηsp : (U₀.ι ≫ pullback.fst z f ≫ z).base ηU = IsLocalRing.closedPoint R := hη
    have hy₁sp : T.f.base y₁ = IsLocalRing.closedPoint R := by
      have h := congrArg (fun φ => φ.base ηU) e₁
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
      rw [← hηsp]; exact h
    have hξsp : f.base ((pullback.snd z f).base (U₀.ι.base ηU)) = IsLocalRing.closedPoint R := by
      have h := congrArg (fun φ => φ.base ηU) e₂
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
      rw [← hηsp]; exact h
    have hζ₀sp : z.base ζ₀ = IsLocalRing.closedPoint R := by
      have h := congrArg (fun φ => φ.base ηU) e₃
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
      rw [← hηsp]; exact h
    have hξmax : ∀ y : ↥X, y ⤳ ((pullback.snd z f).base (U₀.ι.base ηU)) → f.base y =
      IsLocalRing.closedPoint R → y = ((pullback.snd z f).base (U₀.ι.base ηU)) := by
      intro y hy hysp
      have hy2 : y ⤳ (U₀.ι ≫ pullback.snd z f).base ηU := hy
      obtain ⟨y', hy', rfl⟩ := Flat.generalizingMap (U₀.ι ≫ pullback.snd z f) hy2
      have hsp' : (U₀.ι ≫ pullback.fst z f ≫ z).base y' = IsLocalRing.closedPoint R := by
        rw [← e₂, Scheme.Hom.comp_apply]; exact hysp
      rw [hmaxU y' hy' hsp']
      rfl
    have hζ₀max : ∀ y : ↥Z, y ⤳ ζ₀ → z.base y = IsLocalRing.closedPoint R → y = ζ₀ := by
      intro y hy hysp
      have hy2 : y ⤳ (U₀.ι ≫ pullback.fst z f).base ηU := by rw [hζ₀]; exact hy
      obtain ⟨y', hy', rfl⟩ := Flat.generalizingMap (U₀.ι ≫ pullback.fst z f) hy2
      have hsp' : (U₀.ι ≫ pullback.fst z f ≫ z).base y' = IsLocalRing.closedPoint R := by
        rw [← Category.assoc, Scheme.Hom.comp_apply]; exact hysp
      rw [hmaxU y' hy' hsp']
      exact hζ₀
    let algRR' : Algebra R (Z.presheaf.stalk ζ₀) := stalkAlgebra z ζ₀
    have halgZ : Z.fromSpecStalk ζ₀ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R
      (Z.presheaf.stalk ζ₀))) :=
      fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra z ζ₀
    let algRO' : Algebra R ((pullback z T.f).presheaf.stalk η') := ((algebraMap (Z.presheaf.stalk
      ζ₀) ((pullback z T.f).presheaf.stalk η')).comp (algebraMap R (Z.presheaf.stalk ζ₀))).toAlgebra
    let algRO : Algebra R ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((algebraMap (Z.presheaf.stalk
      ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU)).comp (algebraMap R (Z.presheaf.stalk
      ζ₀))).toAlgebra
    have : IsScalarTower R (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η') :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have : IsScalarTower R (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have : IsScalarTower R ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk
      ηU) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hmap : algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ηU) = stalkAlgebraMap (U₀.ι ≫
      pullback.fst z f ≫ z) ηU := by
      change ((v.stalkMap ηU).hom.comp ((pullback.fst z T.f).stalkMap η').hom).comp
        (stalkAlgebraMap z ζ₀) = _
      rw [RingHom.comp_assoc, stalkAlgebraMap_comp', stalkAlgebraMap_comp', ← Category.assoc, hv₁,
        Category.assoc]
    have halgO : (U₀ : Scheme.{u}).fromSpecStalk ηU ≫ (U₀.ι ≫ pullback.fst z f ≫ z) =
        Spec.map (CommRingCat.ofHom (algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ηU))) := by
      rw [hmap]
      exact fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra (U₀.ι ≫ pullback.fst z f ≫ z) ηU
    let algRO₁ : Algebra R (T.Y.presheaf.stalk y₁) := stalkAlgebra T.f y₁
    have halg₁ : T.Y.fromSpecStalk y₁ ≫ T.f = Spec.map (CommRingCat.ofHom (algebraMap R
      (T.Y.presheaf.stalk y₁))) :=
      fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra T.f y₁
    let algO₁O' : Algebra (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk η') :=
      ((pullback.snd z T.f).stalkMap η').hom.toAlgebra
    have : IsScalarTower R (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk η') :=
      IsScalarTower.of_algebraMap_eq (fun r => by
      change ((pullback.fst z T.f).stalkMap η').hom (stalkAlgebraMap z ζ₀ r) =
        ((pullback.snd z T.f).stalkMap η').hom (stalkAlgebraMap T.f y₁ r)
      rw [← RingHom.comp_apply, ← RingHom.comp_apply, stalkAlgebraMap_comp',
        stalkAlgebraMap_comp', pullback.condition])
    let algO₁O : Algebra (T.Y.presheaf.stalk y₁) ((U₀ : Scheme.{u}).presheaf.stalk ηU) :=
      ((algebraMap ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk
      ηU)).comp (algebraMap (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk η'))).toAlgebra
    have : IsScalarTower (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk η') ((U₀ :
      Scheme.{u}).presheaf.stalk ηU) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have : IsScalarTower R (T.Y.presheaf.stalk y₁) ((U₀ : Scheme.{u}).presheaf.stalk ηU) :=
      IsScalarTower.of_algebraMap_eq (fun x => by
      change _ = algebraMap ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk
        ηU) (algebraMap (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk η') (algebraMap R
        (T.Y.presheaf.stalk y₁) x))
      rw [← IsScalarTower.algebraMap_apply R (T.Y.presheaf.stalk y₁) ((pullback z
        T.f).presheaf.stalk η'), ← IsScalarTower.algebraMap_apply R ((pullback z
        T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU)])
    let algRX : Algebra R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) :=
      stalkAlgebra f ((pullback.snd z f).base (U₀.ι.base ηU))
    have halgX : X.fromSpecStalk ((pullback.snd z f).base (U₀.ι.base ηU)) ≫ f = Spec.map
      (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base
      ηU))))) :=
      fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra f ((pullback.snd z f).base (U₀.ι.base
        ηU))
    let algXO : Algebra (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ :
      Scheme.{u}).presheaf.stalk ηU) := ((U₀.ι ≫ pullback.snd z f).stalkMap ηU).hom.toAlgebra
    have hpin2 : ((U₀.ι ≫ pullback.snd z f).stalkMap ηU).hom.comp (stalkAlgebraMap f
      ((pullback.snd z f).base (U₀.ι.base ηU))) =
        stalkAlgebraMap (U₀.ι ≫ pullback.fst z f ≫ z) ηU := by
      have h := stalkAlgebraMap_comp' (U₀.ι ≫ pullback.snd z f) f ηU
      rw [Category.assoc, ← pullback.condition] at h
      exact h
    have : IsScalarTower R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ :
      Scheme.{u}).presheaf.stalk ηU) := IsScalarTower.of_algebraMap_eq (fun r =>
      (RingHom.congr_fun hmap r).trans (RingHom.congr_fun hpin2 r).symm)
    obtain ⟨hdomO, hdomO', hfrac⟩ :=
      NeronModelInfra.isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift
        K LXK d ω X f e Z z uK η T U₀ hηU τ₀ hτ₀ v hv₁ hv₂
    obtain ⟨_hdomO, hdvrO, hlocO, hidxO⟩ :=
      NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes (U₀.ι ≫
        pullback.fst z f ≫ z) ηU
        hη hmaxU halgO
    have : IsDiscreteValuationRing ((U₀ : Scheme.{u}).presheaf.stalk ηU) := hdvrO
    obtain ⟨hdomR', hdvrR', hlocR', hidxR'⟩ :=
      NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes z ζ₀ hζ₀sp hζ₀max
        halgZ
    have : IsLocalHom (algebraMap (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU)) :=
      RingHom.isLocalHom_comp (v.stalkMap ηU).hom ((pullback.fst z T.f).stalkMap η').hom
    have hO : Ideal.map (algebraMap (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU))
      (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ := by
      rw [← hidxR'.map_maximalIdeal, Ideal.map_map]
      exact hidxO.map_maximalIdeal
    obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖirr
    have hϖO : algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ηU) ϖ ≠ 0 :=
      ValuationMaps.map_uniformizer_ne_zero _ ϖ hϖ hidxO.map_maximalIdeal
    have hϖR' : algebraMap R (Z.presheaf.stalk ζ₀) ϖ ≠ 0 := ValuationMaps.map_uniformizer_ne_zero
      _ ϖ hϖ hidxR'.map_maximalIdeal
    have hinjRO : Function.Injective (algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ηU)) :=
      ValuationMaps.injective_of_map_irreducible_ne_zero _ ϖ hϖirr hϖO
    have hinjRR' : Function.Injective (algebraMap R (Z.presheaf.stalk ζ₀)) :=
      ValuationMaps.injective_of_map_irreducible_ne_zero _ ϖ hϖirr hϖR'
    have hinjR'O : Function.Injective (algebraMap (Z.presheaf.stalk ζ₀) ((U₀ :
      Scheme.{u}).presheaf.stalk ηU)) :=
      ValuationMaps.injective_of_map_irreducible_ne_zero _ (algebraMap R (Z.presheaf.stalk ζ₀) ϖ)
        ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
          (ValuationMaps.maximalIdeal_eq_span_map _ ϖ hϖ hidxR'.map_maximalIdeal))
        (by rw [← IsScalarTower.algebraMap_apply R (Z.presheaf.stalk ζ₀) ((U₀ :
          Scheme.{u}).presheaf.stalk ηU)]; exact hϖO)
    have hinjXO : Function.Injective (algebraMap (X.presheaf.stalk ((pullback.snd z f).base
      (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := by
      obtain ⟨hdomX, hdvrX, hlocX, hidxX⟩ :=
        NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes f ((pullback.snd
          z f).base (U₀.ι.base ηU)) hξsp hξmax halgX
      exact ValuationMaps.injective_of_map_irreducible_ne_zero _ (algebraMap R (X.presheaf.stalk
        ((pullback.snd z f).base (U₀.ι.base ηU))) ϖ)
        ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
          (ValuationMaps.maximalIdeal_eq_span_map _ ϖ hϖ hidxX.map_maximalIdeal))
        (by rw [← IsScalarTower.algebraMap_apply R (X.presheaf.stalk ((pullback.snd z f).base
          (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU)]; exact hϖO)
    let F := FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)
    have : IsScalarTower (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η') F :=
      IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply ((pullback z T.f).presheaf.stalk η') ((U₀ :
        Scheme.{u}).presheaf.stalk ηU) F, IsScalarTower.algebraMap_apply (Z.presheaf.stalk ζ₀)
        ((U₀ : Scheme.{u}).presheaf.stalk ηU) F,
        ← IsScalarTower.algebraMap_apply (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk
          η') ((U₀ : Scheme.{u}).presheaf.stalk ηU)])
    have : IsScalarTower R (Z.presheaf.stalk ζ₀) F := IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk
        ηU) F, IsScalarTower.algebraMap_apply R ((U₀ : Scheme.{u}).presheaf.stalk ηU) F,
        ← IsScalarTower.algebraMap_apply R (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk
          ηU)])
    have : IsScalarTower R (T.Y.presheaf.stalk y₁) F := IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply (T.Y.presheaf.stalk y₁) ((U₀ : Scheme.{u}).presheaf.stalk
        ηU) F, IsScalarTower.algebraMap_apply R ((U₀ : Scheme.{u}).presheaf.stalk ηU) F,
        ← IsScalarTower.algebraMap_apply R (T.Y.presheaf.stalk y₁) ((U₀ :
          Scheme.{u}).presheaf.stalk ηU)])
    have : IsScalarTower R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) F :=
      IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base
        ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) F, IsScalarTower.algebraMap_apply R ((U₀ :
        Scheme.{u}).presheaf.stalk ηU) F,
        ← IsScalarTower.algebraMap_apply R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base
          ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU)])
    have : FaithfulSMul R F := (faithfulSMul_iff_algebraMap_injective R F).mpr (by
      rw [IsScalarTower.algebraMap_eq R ((U₀ : Scheme.{u}).presheaf.stalk ηU) F]; exact
        (IsFractionRing.injective ((U₀ : Scheme.{u}).presheaf.stalk ηU) F).comp hinjRO)
    let algKF : Algebra K F := (IsFractionRing.lift (g := algebraMap R F)
      (FaithfulSMul.algebraMap_injective R F)).toAlgebra
    have : IsScalarTower R K F := IsScalarTower.of_algebraMap_eq (fun x =>
      (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective R F) x).symm)
    let K' := FractionRing (Z.presheaf.stalk ζ₀)
    have : FaithfulSMul R K' := (faithfulSMul_iff_algebraMap_injective R K').mpr (by
      rw [IsScalarTower.algebraMap_eq R (Z.presheaf.stalk ζ₀) K']; exact (IsFractionRing.injective
        (Z.presheaf.stalk ζ₀) K').comp hinjRR')
    let algKK' : Algebra K K' := (IsFractionRing.lift (g := algebraMap R K')
      (FaithfulSMul.algebraMap_injective R K')).toAlgebra
    have : IsScalarTower R K K' := IsScalarTower.of_algebraMap_eq (fun x =>
      (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective R K') x).symm)
    have : FaithfulSMul (Z.presheaf.stalk ζ₀) F := (faithfulSMul_iff_algebraMap_injective
      (Z.presheaf.stalk ζ₀) F).mpr (by
      rw [IsScalarTower.algebraMap_eq (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU)
        F]; exact (IsFractionRing.injective ((U₀ : Scheme.{u}).presheaf.stalk ηU) F).comp hinjR'O)
    let algK'F : Algebra K' F := FractionRing.liftAlgebra (Z.presheaf.stalk ζ₀) F
    have : IsScalarTower (Z.presheaf.stalk ζ₀) K' F := FractionRing.isScalarTower_liftAlgebra
      (Z.presheaf.stalk ζ₀) F
    have : IsScalarTower R K' F := IsScalarTower.of_algebraMap_eq (fun r => by
      rw [IsScalarTower.algebraMap_apply R (Z.presheaf.stalk ζ₀) K' r, ←
        IsScalarTower.algebraMap_apply (Z.presheaf.stalk ζ₀) K' F,
        ← IsScalarTower.algebraMap_apply R (Z.presheaf.stalk ζ₀) F])
    have towKK'F : IsScalarTower K K' F := IsScalarTower.of_algebraMap_eq (fun x => by
      have h : (algebraMap K' F).comp (algebraMap K K') = algebraMap K F :=
        IsLocalization.ringHom_ext (nonZeroDivisors R) (by
          ext r
          simp only [RingHom.comp_apply]
          rw [← IsScalarTower.algebraMap_apply R K K', ← IsScalarTower.algebraMap_apply R K' F,
            ← IsScalarTower.algebraMap_apply R K F])
      exact (RingHom.congr_fun h x).symm)
    have hbc' :=
      AlgebraicGeometry.bijective_kaehlerDifferential_map_comp_mapBaseChange_stalk_pullback T.f z
      η' halgZ halg₁
    have hRO : algebraMap (Z.presheaf.stalk ζ₀) F = (algebraMap ((U₀ : Scheme.{u}).presheaf.stalk
      ηU) F).comp ((v.stalkMap ηU).hom.comp ((pullback.fst z T.f).stalkMap η').hom) := by
      rw [IsScalarTower.algebraMap_eq (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU)
        F]; rfl
    have hτF : algebraMap (T.Y.presheaf.stalk y₁) F = (algebraMap ((U₀ :
      Scheme.{u}).presheaf.stalk ηU) F).comp ((v.stalkMap ηU).hom.comp ((pullback.snd z
      T.f).stalkMap η').hom) := by
      rw [IsScalarTower.algebraMap_eq (T.Y.presheaf.stalk y₁) ((U₀ : Scheme.{u}).presheaf.stalk
        ηU) F]; rfl
    have htrans :=
      mul_pointGenericFibre_eq_pointGenericFibre_comp_chart_of_genericFibreRestrict_comp_eq_mul
        K LXK d ω X f e Z z uK η T U₀ hηU τ₀ hτ₀ v hv₁ hv₂ halgZ halgO halg₁ K' F hRO hτF
    obtain ⟨U'', hU'', algU'', hKU'', hx'', ωU'', hωU''⟩ : ∃ (U'' : XK.Opens) (hU'' : IsAffineOpen
      U'')
        (algU'' : Algebra Γ(XK, U'') F) (_ : let : Algebra K Γ(XK, U'') := gK.sectionsAlgebra U'';
          IsScalarTower K Γ(XK, U'') F)
        (_ : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U'') F)) ≫ hU''.fromSpec =
          (NeronModelInfra.schemeHomOverComp
            (pointGenericFibre (K := K) (K' := F)
              (⟨T.Y.fromSpecStalk y₁, halg₁⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom
                (algebraMap R (T.Y.presheaf.stalk y₁)))) T.f))
            T.e).1)
        (ωU'' : ⋀[Γ(XK, U'')]^d (gK.kaehlerPresheaf.obj (op U''))),
        gK.topToSections d U'' ωU'' = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω
          := by
      exact StalkCharts.exists_affine_chart_of_point gK d ω F _
        (NeronModelInfra.schemeHomOverComp
          (pointGenericFibre (K := K) (K' := F)
            (⟨T.Y.fromSpecStalk y₁, halg₁⟩ :
              SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁))))
                T.f))
          T.e).2
    obtain ⟨b₁, w₁, hread⟩ :=
      NeronModelInfra.ComponentReading.exists_basis_units_topFormMap_eq_mul_zpow_smul_of_specializes
        ϖ hϖ K hωframe T y₁ hy₁sp hgen₁ halg₁ F U'' hU'' hKU'' hx'' ωU'' hωU''
    obtain ⟨c, φ, hc, hφbij, hφloc, hφR, algF₀F, hTowO₀, hTowK, hxX⟩ :=
      exists_ringHom_stalk_chart_comp_eq_pointGenericFibre_of_forall_specializes
        K d ω D X f e V j hyV hVK hjopen hjchart hcover
        ((pullback.snd z f).base (U₀.ι.base ηU)) hξsp hξmax halgX F
        (by rw [IsScalarTower.algebraMap_eq (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base
          ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) F]; exact (IsFractionRing.injective ((U₀ :
          Scheme.{u}).presheaf.stalk ηU) F).comp hinjXO)
    let : Algebra R ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).algebra
    let : Algebra K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).algebraK
    have : IsScalarTower R K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C
      c).isScalarTower
    let algO₀O : Algebra ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk
      ηU) := ((algebraMap (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ :
      Scheme.{u}).presheaf.stalk ηU)).comp φ).toAlgebra
    have : IsScalarTower ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C
      c).Y.presheaf.stalk (D.C c).y)) F := IsScalarTower.of_algebraMap_eq (fun x => by
      have h := @IsScalarTower.algebraMap_apply ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing
        ((D.C c).Y.presheaf.stalk (D.C c).y)) F _ _ _ _ _ (((algebraMap (X.presheaf.stalk
        ((pullback.snd z f).base (U₀.ι.base ηU))) F).comp φ).toAlgebra) hTowO₀ x
      rw [← h, IsScalarTower.algebraMap_apply ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ :
        Scheme.{u}).presheaf.stalk ηU) F x]
      change _ = (algebraMap (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) F) (φ x)
      rw [IsScalarTower.algebraMap_apply (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base
        ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) F (φ x)]
      rfl)
    have : IsScalarTower R ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk
      ηU) := IsScalarTower.of_algebraMap_eq (fun r => by
      change algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ηU) r = algebraMap (X.presheaf.stalk
        ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) (φ
        (algebraMap R ((D.C c).Y.presheaf.stalk (D.C c).y) r))
      rw [← RingHom.comp_apply φ, hφR, ← IsScalarTower.algebraMap_apply R (X.presheaf.stalk
        ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU)])
    have : IsScalarTower R ((D.C c).Y.presheaf.stalk (D.C c).y) F :=
      IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ :
        Scheme.{u}).presheaf.stalk ηU) F, IsScalarTower.algebraMap_apply R ((U₀ :
        Scheme.{u}).presheaf.stalk ηU) F,
        ← IsScalarTower.algebraMap_apply R ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ :
          Scheme.{u}).presheaf.stalk ηU)])
    have : IsLocalHom (algebraMap ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ :
      Scheme.{u}).presheaf.stalk ηU)) :=
      @RingHom.isLocalHom_comp _ _ _ _ _ _ ((U₀.ι ≫ pullback.snd z f).stalkMap ηU).hom φ
        inferInstance hφloc
    have : IsScalarTower K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F := hTowK
    have : Smooth (D.C c).f := (D.C c).smooth
    obtain ⟨-, -, hlocO₀, hidxO₀⟩ :=
      NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes (D.C c).f (D.C
        c).y (D.C c).hy
        (D.C c).hmax (D.C c).halg
    have hbc : Function.Bijective
        ((KaehlerDifferential.map R (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU)
          ((U₀ : Scheme.{u}).presheaf.stalk ηU)).restrictScalars ((U₀ : Scheme.{u}).presheaf.stalk
          ηU) ∘ₗ
          KaehlerDifferential.mapBaseChange R ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ :
            Scheme.{u}).presheaf.stalk ηU)) := by
      exact StalkCharts.bijective_map_comp_mapBaseChange_stalk_of_isOpenImmersion f z U₀.ι ηU
        (v ≫ pullback.fst z T.f) hv₁ ζ₀ rfl halgZ halgX ((D.C c).Y.presheaf.stalk (D.C c).y) φ
          hφbij hφR
        (fun a => by
          have hc : (Z.presheaf.stalkCongr
              (.of_eq (rfl : ζ₀ = (v ≫ pullback.fst z T.f) ηU))).hom =
              𝟙 (Z.presheaf.stalk ζ₀) := Z.presheaf.stalkSpecializes_refl ζ₀
          have hcₐ : (Z.presheaf.stalkCongr
                (.of_eq (rfl : ζ₀ = (v ≫ pullback.fst z T.f) ηU))).hom a = a :=
            congrArg (fun h : Z.presheaf.stalk ζ₀ ⟶ Z.presheaf.stalk ζ₀ => h.hom a) hc
          have hm : algebraMap (Z.presheaf.stalk ζ₀)
              ((U₀ : Scheme.{u}).presheaf.stalk ηU) a =
              ((v ≫ pullback.fst z T.f).stalkMap ηU).hom a :=
            (congrArg (fun h : Z.presheaf.stalk ζ₀ ⟶
                (U₀ : Scheme.{u}).presheaf.stalk ηU => h.hom a)
              (Scheme.Hom.stalkMap_comp v (pullback.fst z T.f) ηU)).symm
          exact hm.trans
            (congrArg ((v ≫ pullback.fst z T.f).stalkMap ηU).hom hcₐ.symm))
        (fun b => rfl)
    let : Algebra K Γ(XK, (D.C c).U) := gK.sectionsAlgebra (D.C c).U
    let : Algebra Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C
      c).algebraU
    let algUcF : Algebra Γ(XK, (D.C c).U) F := ((algebraMap (FractionRing ((D.C
      c).Y.presheaf.stalk (D.C c).y)) F).comp (algebraMap Γ(XK, (D.C c).U) (FractionRing ((D.C
      c).Y.presheaf.stalk (D.C c).y)))).toAlgebra
    let : Algebra K Γ(XK, U'') := gK.sectionsAlgebra U''
    have : IsScalarTower K Γ(XK, U'') F := hKU''
    have hKUc : IsScalarTower K Γ(XK, (D.C c).U) F := IsScalarTower.of_algebraMap_eq (fun x => by
      change algebraMap K F x = algebraMap (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F
        (algebraMap Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y))
        (algebraMap K Γ(XK, (D.C c).U) x))
      rw [← @IsScalarTower.algebraMap_apply K Γ(XK, (D.C c).U) (FractionRing ((D.C
        c).Y.presheaf.stalk (D.C c).y)) _ _ _ (gK.sectionsAlgebra (D.C c).U)
        (D.C c).algebraU _ (D.C c).isScalarTowerU x, ← IsScalarTower.algebraMap_apply K
          (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F])
    have : IsFractionRing ((pullback z T.f).presheaf.stalk η') F := by
      have e : (((algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ηU) F).comp (v.stalkMap
        ηU).hom).toAlgebra : Algebra ((pullback z T.f).presheaf.stalk η') F) =
          (inferInstance : Algebra ((pullback z T.f).presheaf.stalk η') F) :=
        Algebra.algebra_ext _ _ (fun r => (IsScalarTower.algebraMap_apply ((pullback z
          T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU) F r).symm)
      exact (congrArg (fun i : Algebra ((pullback z T.f).presheaf.stalk η') F => @IsLocalization _
        _ (nonZeroDivisors _) F _ i) e).mp hfrac
    have hxpt : (NeronModelInfra.schemeHomOverComp
          (pointGenericFibre (K := K) (K' := F)
            (⟨(U₀ : Scheme.{u}).fromSpecStalk ηU, halgO⟩ :
              SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R ((U₀ :
                Scheme.{u}).presheaf.stalk ηU)))) (U₀.ι ≫ pullback.fst z f ≫ z)))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U₀.ι ≫ pullback.fst z f ≫ z)
              ⟨U₀.ι ≫ pullback.snd z f, by rw [Category.assoc, ← pullback.condition]⟩) e)).1 =
        (NeronModelInfra.schemeHomOverComp
          (pointGenericFibre (K := K) (K' := F)
            (⟨X.fromSpecStalk ((pullback.snd z f).base (U₀.ι.base ηU)), halgX⟩ : SchemeHomOver
              (Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z
              f).base (U₀.ι.base ηU)))))) f))
          e).1 := by
      have hFpt : Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk ((pullback.snd z
        f).base (U₀.ι.base ηU))) F)) ≫
            X.fromSpecStalk ((pullback.snd z f).base (U₀.ι.base ηU)) =
          Spec.map (CommRingCat.ofHom (algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ηU) F)) ≫
            (U₀ : Scheme.{u}).fromSpecStalk ηU ≫ (U₀.ι ≫ pullback.snd z f) := by
        rw [IsScalarTower.algebraMap_eq (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)))
          ((U₀ : Scheme.{u}).presheaf.stalk ηU) F, CommRingCat.ofHom_comp, Spec.map_comp,
            Category.assoc]
        erw [← Scheme.SpecMap_stalkMap_fromSpecStalk (U₀.ι ≫ pullback.snd z f) (x := ηU)]
        rfl
      simp only [NeronModelInfra.schemeHomOverComp_coe]
      rw [← Category.assoc, GenericPoints.pointGenericFibre_comp_genericFibreRestrict K f (U₀.ι ≫
        pullback.fst z f ≫ z)
        (U₀.ι ≫ pullback.snd z f) (by rw [Category.assoc, ← pullback.condition]) ηU
        ((pullback.snd z f).base (U₀.ι.base ηU)) halgO halgX F hFpt]
    have hleftη : TopFormOrder.topFormMap K K' Γ(XK, U'') F d ωU'' = TopFormOrder.topFormMap K K'
      Γ(XK, (D.C c).U) F d (D.C c).ωU :=
      hleft K' F _ _ (D.C c).U U'' (D.C c).hU hU'' (hxX.trans hxpt.symm) (hx''.trans htrans.symm)
        (D.C c).ωU ωU'' (D.C c).hωU hωU''
    have towUcF₀F : IsScalarTower Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C
      c).y)) F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have towKUcF₀ : IsScalarTower K Γ(XK, (D.C c).U)
        (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).isScalarTowerU
    have hX : TopFormOrder.topFormMap K K' F F d (TopFormOrder.topFormMap K K Γ(XK, U'') F d ωU'') =
        TopFormOrder.topFormMap K K' (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F d
          ((D.C c).a • TopFormOrder.topFormMap R K ((D.C c).Y.presheaf.stalk (D.C c).y)
            (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) d (exteriorPower.ιMulti ((D.C
            c).Y.presheaf.stalk (D.C c).y) d (D.C c).b)) := by
      exact @topFormMap_comp_of_eq K K' Γ(XK, U'') Γ(XK, (D.C c).U)
        (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F
        (inferInstance : Field K) (inferInstance : Field K') algKK'
        (CommRingCat.commRing Γ(XK, U'')) (CommRingCat.commRing Γ(XK, (D.C c).U))
        (inferInstance : Field (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)))
        (inferInstance : Field F)
        (gK.sectionsAlgebra U'') (gK.sectionsAlgebra (D.C c).U)
        (D.C c).algebraU algF₀F algUcF towUcF₀F (D.C c).algebraK towKUcF₀
        algKF algK'F hTowK towKK'F algU'' hKU'' hKUc d ωU'' (D.C c).ωU
        ((D.C c).a • TopFormOrder.topFormMap R K ((D.C c).Y.presheaf.stalk (D.C c).y)
          (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) d
          (exteriorPower.ιMulti ((D.C c).Y.presheaf.stalk (D.C c).y) d (D.C c).b))
        hleftη (D.C c).ha
    have hmin : TopFormOrder.addOrd ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C
      c).Y.presheaf.stalk (D.C c).y)) (D.C c).a ≤ T.n := hD.1 c T
    have hsq :=
      TopFormOrder.eq_addOrd_and_bijective_mapBaseChange_of_topFormMap_eq_of_addOrd_le
        R K (Z.presheaf.stalk ζ₀) K' ϖ hϖ hidxR'.map_maximalIdeal
        ((D.C c).Y.presheaf.stalk (D.C c).y)
        (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) hidxO₀.map_maximalIdeal
      d (D.C c).b (D.C c).a (D.C c).ha0 (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk
        η') b₁ w₁ T.n hbc' ((U₀ : Scheme.{u}).presheaf.stalk ηU) F hO hbc
      (TopFormOrder.topFormMap K K Γ(XK, U'') F d ωU'') hread hX hmin
    exact ⟨⟨c, hsq.1⟩, hsq.2⟩
  refine ⟨hmain.1, ?_⟩
  have : Algebra.FormallyEtale ((pullback z T.f).presheaf.stalk η')
      ((U₀ : Scheme.{u}).presheaf.stalk ηU) :=
    Algebra.FormallyEtale.of_formallySmooth_of_bijective_mapBaseChange hmain.2
  exact inferInstance

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_minimalComponentData_isOmegaMinimal_of_catchesIndexOnePoints.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.MinimalComponentSelection

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
    GoodReductionJacobian TopologicalSpace Topology

noncomputable section

namespace Selection

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
  [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Smooth gK] [IsSeparated gK]
  [LocallyOfFiniteType gK] [QuasiCompact gK] in
theorem genericFibreRestrict_incl_val {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) (W :
    Y.Opens) :
    (genericFibreRestrict R K f (W.ι ≫ f) ⟨W.ι, rfl⟩).1 =
      pullback.map (W.ι ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K) W.ι
        (𝟙 _)
        (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) := by
  exact NeronModelInfra.genericFibreRestrict_coe_eq_pullbackMap f (W.ι ≫ f)
    ⟨W.ι, rfl⟩ (Category.comp_id _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- An open completion of one smooth model chart, with unchanged generic fibre. -/
structure Completion (M : ModelFamily R K gK) (i : M.ι) where
  /-- The completed scheme. -/
  Y' : Scheme.{u}
  /-- The completed structure morphism. -/
  f' : Y' ⟶ Spec (CommRingCat.of R)
  /-- The original chart inclusion. -/
  j : M.X i ⟶ Y'
  /-- The inclusion is over the base. -/
  hj : j ≫ f' = M.str i
  /-- The generic-fibre chart. -/
  e' : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K)) gK
  /-- The inclusion is open. -/
  hjo : IsOpenImmersion j
  /-- The model is separated. -/
  sep : IsSeparated f'
  /-- The model is locally of finite type. -/
  lft : LocallyOfFiniteType f'
  /-- The model is quasi-compact. -/
  qc : QuasiCompact f'
  /-- The generic-fibre chart is an isomorphism. -/
  iso : IsIso e'.1
  /-- The original chart covers the special fibre. -/
  hsurj : ∀ y' : Y', f'.base y' = IsLocalRing.closedPoint R → y' ∈ Set.range j.base
  /-- The generic-fibre chart extends the original chart. -/
  hchart : schemeHomOverComp (genericFibreRestrict R K f' (M.str i) ⟨j, hj⟩) e' = M.chart i
  /-- The model is smooth. -/
  smooth : Smooth f'

theorem nonempty_completion (M : ModelFamily R K gK)
    (hM : ∀ i, Smooth (M.str i) ∧ IsSeparated (M.str i) ∧ LocallyOfFiniteType (M.str i) ∧
      QuasiCompact (M.str i)) (i : M.ι) : Nonempty (Completion K M i) := by
  have : Smooth (M.str i) := (hM i).1
  have : IsSeparated (M.str i) := (hM i).2.1
  have : LocallyOfFiniteType (M.str i) := (hM i).2.2.1
  have : QuasiCompact (M.str i) := (hM i).2.2.2
  obtain ⟨Y', f', j, hj, e', hjo, hsep, hlft, hqc, hiso, hsurj, hchart, hsm⟩ :=
    NeronModelInfra.exists_isOpenImmersion_model_isIso_genericFibre_of_isOpenImmersion_chart K gK
      (M.str i)
      (M.chart i)
  exact ⟨⟨Y', f', j, hj, e', hjo, hsep, hlft, hqc, hiso, hsurj, hchart, hsm ‹_› ‹_›⟩⟩

section Main

variable (M : ModelFamily R K gK) (hfin : Finite M.ι)
  (hM : ∀ i, Smooth (M.str i) ∧ IsSeparated (M.str i) ∧ LocallyOfFiniteType (M.str i) ∧
    QuasiCompact (M.str i))

/-- Choose a completion of the indicated chart. -/
def Cpl (i : M.ι) : Completion K M i := (nonempty_completion K M hM i).some

scoped instance (i : M.ι) : Smooth (Cpl K M hM i).f' := (Cpl K M hM i).smooth
scoped instance (i : M.ι) : IsSeparated (Cpl K M hM i).f' := (Cpl K M hM i).sep
scoped instance (i : M.ι) : LocallyOfFiniteType (Cpl K M hM i).f' := (Cpl K M hM i).lft
scoped instance (i : M.ι) : QuasiCompact (Cpl K M hM i).f' := (Cpl K M hM i).qc
scoped instance (i : M.ι) : IsOpenImmersion (Cpl K M hM i).j := (Cpl K M hM i).hjo
scoped instance (i : M.ι) : IsIso (Cpl K M hM i).e'.1 := (Cpl K M hM i).iso

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Smooth gK] [IsSeparated gK]
  [LocallyOfFiniteType gK] [QuasiCompact gK] in
theorem noetherianSpace_of {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R]
    [LocallyOfFiniteType f] [QuasiCompact f] : NoetherianSpace Y := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian Y := {}
  infer_instance

/-- A generic point of an irreducible component of the special fibre. -/
def IsMaxSpecial {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) (ξ : Y) : Prop :=
  f.base ξ = IsLocalRing.closedPoint R ∧
    ∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ

/-- The finitely many maximal special-fibre points of the completed charts. -/
def Idx : Type u := Σ i : M.ι, {ξ : ↥(Cpl K M hM i).Y' // IsMaxSpecial (Cpl K M hM i).f' ξ}

include hfin in
theorem finite_idx : Finite (Idx K M hM) := by
  change Finite (Σ i : M.ι, {ξ : (Cpl K M hM i).Y' //
    IsMaxSpecial (Cpl K M hM i).f' ξ})
  have : ∀ i : M.ι, Finite {ξ : ↥(Cpl K M hM i).Y' // IsMaxSpecial (Cpl K M hM i).f' ξ} := fun i =>
    (NeronModelInfra.finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens
      (Cpl K M hM i).f').1.to_subtype
  infer_instance

variable {d : ℕ} [SmoothOfRelativeDimension d gK] {ω : Γ(gK.topDifferentials d, ⊤)}
  (hω : Scheme.Modules.IsFrameOn ω ⊤)

/-- Differential data at a fixed maximal special-fibre point. -/
structure RTail {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) (y : Y) where
  /-- The stalk is a domain. -/
  isDomain : IsDomain (Y.presheaf.stalk y)
  /-- The stalk is a discrete valuation ring. -/
  isDiscreteValuationRing : IsDiscreteValuationRing (Y.presheaf.stalk y)
  /-- The base algebra on the stalk. -/
  algebra : Algebra R (Y.presheaf.stalk y)
  /-- The algebra agrees with the structural morphism. -/
  halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))
  /-- The fraction-field algebra on the generic stalk. -/
  algebraK : Algebra K (FractionRing (Y.presheaf.stalk y))
  /-- The base-field tower commutes. -/
  isScalarTower : IsScalarTower R K (FractionRing (Y.presheaf.stalk y))
  /-- A basis of stalk differentials. -/
  b : Module.Basis (Fin d) (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄R])
  /-- An affine chart around the generic-fibre point. -/
  U : XK.Opens
  /-- The chosen chart is affine. -/
  hU : IsAffineOpen U
  /-- The generic stalk as an algebra over chart sections. -/
  algebraU : Algebra Γ(XK, U) (FractionRing (Y.presheaf.stalk y))
  /-- The chart-section algebra is compatible with the base field. -/
  isScalarTowerU : let : Algebra K Γ(XK, U) := gK.sectionsAlgebra U
    IsScalarTower K Γ(XK, U) (FractionRing (Y.presheaf.stalk y))
  /-- The chart point is the actual generic-fibre point. -/
  hx : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))) ≫
    hU.fromSpec =
    (schemeHomOverComp
      (pointGenericFibre (K := K) (K' := FractionRing (Y.presheaf.stalk y))
        (⟨Y.fromSpecStalk y, halg⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) f))
      e).1
  /-- The local top differential form. -/
  ωU : ⋀[Γ(XK, U)]^d (gK.kaehlerPresheaf.obj (op U))
  /-- The local form represents the global form. -/
  hωU : gK.topToSections d U ωU = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω
  /-- The coefficient of the form in the chosen basis. -/
  a : FractionRing (Y.presheaf.stalk y)
  /-- The local form has this basis coefficient. -/
  ha : let : Algebra K Γ(XK, U) := gK.sectionsAlgebra U
    TopFormOrder.topFormMap K K Γ(XK, U) (FractionRing (Y.presheaf.stalk y)) d ωU =
      a • TopFormOrder.topFormMap R K (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y)) d
        (exteriorPower.ιMulti (Y.presheaf.stalk y) d b)
  /-- The coefficient is nonzero. -/
  ha0 : a ≠ 0

include hω in
omit [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK] [Smooth gK] in
theorem nonempty_rtail {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f]
    [LocallyOfFiniteType f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion e.1]
    (y : Y) (hy : f.base y = IsLocalRing.closedPoint R)
    (hmax : ∀ y' : Y, y' ⤳ y → f.base y' = IsLocalRing.closedPoint R → y' = y) :
    Nonempty (RTail K (gK := gK) (d := d) (ω := ω) f e y) := by
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, h16, h17⟩ :=
    NeronModelInfra.exists_componentReading_data_of_smooth_of_forall_specializes K gK d ω hω f e y
      hy hmax
  exact ⟨⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, h16, h17⟩⟩

/-- Choose the differential data supplied by the component construction. -/
def tail {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] [LocallyOfFiniteType f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion e.1]
    (y : Y) (hy : f.base y = IsLocalRing.closedPoint R)
    (hmax : ∀ y' : Y, y' ⤳ y → f.base y' = IsLocalRing.closedPoint R → y' = y) :
    RTail K (gK := gK) (d := d) (ω := ω) f e y :=
  Classical.choice (nonempty_rtail K hω f e y hy hmax)

/-- Assemble the chosen differential data with the fixed model and point. -/
@[reducible] def mkReading {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [hs : Smooth f]
    [hl : LocallyOfFiniteType f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [ho : IsOpenImmersion
      e.1]
    (y : Y) (hy : f.base y = IsLocalRing.closedPoint R)
    (hmax : ∀ y' : Y, y' ⤳ y → f.base y' = IsLocalRing.closedPoint R → y' = y) :
    ComponentReading R K gK d ω :=
  let t := tail K hω f e y hy hmax
  { Y := Y, f := f, smooth := hs, locallyOfFiniteType := hl, e := e, isOpenImmersion := ho, y := y,
    hy := hy, hmax := hmax,
    isDomain := t.isDomain, isDiscreteValuationRing := t.isDiscreteValuationRing, algebra :=
      t.algebra,
    halg := t.halg, algebraK := t.algebraK, isScalarTower := t.isScalarTower, b := t.b, U := t.U,
      hU := t.hU,
    algebraU := t.algebraU, isScalarTowerU := t.isScalarTowerU, hx := t.hx, ωU := t.ωU, hωU :=
      t.hωU,
    a := t.a, ha := t.ha, ha0 := t.ha0 }

omit [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK] [Smooth gK] in
@[scoped simp] theorem mkReading_Y {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f]
    [LocallyOfFiniteType f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion e.1]
    (y : Y) (hy : f.base y = IsLocalRing.closedPoint R)
    (hmax : ∀ y' : Y, y' ⤳ y → f.base y' = IsLocalRing.closedPoint R → y' = y) :
    (mkReading K hω f e y hy hmax).Y = Y := rfl

section Members

variable (c : Idx K M hM)

/-- The completed chart containing the selected component. -/
abbrev Yp : Scheme.{u} := (Cpl K M hM c.1).Y'

/-- The structure morphism of the completed chart. -/
abbrev fp : Yp K M hM c ⟶ Spec (CommRingCat.of R) := (Cpl K M hM c.1).f'

scoped instance : NoetherianSpace ↥(Yp K M hM c) := noetherianSpace_of (fp K M hM c)

theorem exists_V : ∃ V : (Yp K M hM c).Opens, c.2.1 ∈ V ∧
    (∀ y', (fp K M hM c).base y' ≠ IsLocalRing.closedPoint R → y' ∈ V) ∧
    (∀ y', y' ∈ V → (fp K M hM c).base y' = IsLocalRing.closedPoint R → c.2.1 ⤳ y') ∧
    (∀ y', (fp K M hM c).base y' = IsLocalRing.closedPoint R → c.2.1 ⤳ y' → y' ∈ V) :=
  (NeronModelInfra.finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens
    (fp K M hM c)).2.2 c.2.1 c.2.2.1 c.2.2.2

/-- The open neighbourhood containing exactly the chosen special-fibre component. -/
def V : (Yp K M hM c).Opens := (exists_V K M hM c).choose

theorem mem_V : c.2.1 ∈ V K M hM c := (exists_V K M hM c).choose_spec.1
theorem mem_V_of_ne (y' : ↥(Yp K M hM c)) (h : (fp K M hM c).base y' ≠ IsLocalRing.closedPoint R) :
    y' ∈ V K M hM c := (exists_V K M hM c).choose_spec.2.1 y' h
theorem gen_V (y' : ↥(Yp K M hM c)) (h : y' ∈ V K M hM c)
    (h' : (fp K M hM c).base y' = IsLocalRing.closedPoint R) : c.2.1 ⤳ y' :=
  (exists_V K M hM c).choose_spec.2.2.1 y' h h'
theorem mem_V_of_specializes (y' : ↥(Yp K M hM c)) (h' : (fp K M hM c).base y' =
    IsLocalRing.closedPoint R)
    (h : c.2.1 ⤳ y') : y' ∈ V K M hM c :=
  (exists_V K M hM c).choose_spec.2.2.2 y' h' h

/-- The selected component neighbourhood as an open subscheme. -/
abbrev Yc : Scheme.{u} := ↑(V K M hM c)

/-- The structure morphism of the component neighbourhood. -/
abbrev fc : Yc K M hM c ⟶ Spec (CommRingCat.of R) := (V K M hM c).ι ≫ fp K M hM c

/-- The generic-fibre chart of the component neighbourhood. -/
def ec : SchemeHomOver (pullback.snd (fc K M hM c) (specGenericFibreInclusion R K)) gK :=
  schemeHomOverComp (genericFibreRestrict R K (fp K M hM c) (fc K M hM c) ⟨(V K M hM c).ι, rfl⟩)
    (Cpl K M hM c.1).e'

/-- The generic special-fibre point in its component neighbourhood. -/
def yc : ↥(Yc K M hM c) := ⟨c.2.1, mem_V K M hM c⟩

theorem yc_val : ((V K M hM c).ι).base (yc K M hM c) = c.2.1 := rfl

theorem fc_base (y' : ↥(Yc K M hM c)) : (fc K M hM c).base y' = (fp K M hM c).base y'.1 := rfl

theorem hy_c : (fc K M hM c).base (yc K M hM c) = IsLocalRing.closedPoint R := c.2.2.1

theorem hmax_c (y' : ↥(Yc K M hM c)) (h : y' ⤳ yc K M hM c)
    (h' : (fc K M hM c).base y' = IsLocalRing.closedPoint R) : y' = yc K M hM c := by
  apply Subtype.ext
  have h1 : y'.1 ⤳ c.2.1 := h.map (V K M hM c).ι.continuous
  exact c.2.2.2 y'.1 h1 h'

theorem hgen_c (y' : ↥(Yc K M hM c)) (h' : (fc K M hM c).base y' = IsLocalRing.closedPoint R) :
    yc K M hM c ⤳ y' := by
  have h1 : (V K M hM c).ι.base (yc K M hM c) ⤳ (V K M hM c).ι.base y' := gen_V K M hM c y'.1 y'.2
    h'
  exact ((V K M hM c).ι.isOpenEmbedding.isInducing.specializes_iff).mp h1

scoped instance : IsOpenImmersion (ec K M hM c).1 := by
  change IsOpenImmersion ((genericFibreRestrict R K (fp K M hM c) (fc K M hM c) ⟨(V K M hM c).ι,
    rfl⟩).1 ≫
    (Cpl K M hM c.1).e'.1)
  rw [genericFibreRestrict_incl_val]
  infer_instance

end Members

section Members2

variable (c : Idx K M hM)

scoped instance : IsIso (ec K M hM c).1 := by
  change IsIso ((genericFibreRestrict R K (fp K M hM c) (fc K M hM c) ⟨(V K M hM c).ι, rfl⟩).1 ≫
    (Cpl K M hM c.1).e'.1)
  rw [genericFibreRestrict_incl_val]
  have : IsIso (pullback.map ((V K M hM c).ι ≫ fp K M hM c) (specGenericFibreInclusion R K) (fp K
    M hM c)
      (specGenericFibreInclusion R K) (V K M hM c).ι (𝟙 _) (𝟙 _) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)) := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨?_⟩⟩
    rw [← Set.range_eq_univ, Scheme.Pullback.range_map]
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_univ, iff_true]
    refine ⟨?_, ?_⟩
    · rw [Scheme.Opens.range_ι]
      apply mem_V_of_ne
      intro hp
      refine specGenericFibreInclusion_base_ne_closedPoint R K
        ((pullback.snd (fp K M hM c) (specGenericFibreInclusion R K)).base p) ?_
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
      exact hp
    · exact ⟨(pullback.snd (fp K M hM c) (specGenericFibreInclusion R K)).base p, rfl⟩
  infer_instance

/-- The component reading of a chosen completed-chart neighbourhood. -/
@[reducible] def Tc : ComponentReading R K gK d ω :=
  mkReading K hω (fc K M hM c) (ec K M hM c) (yc K M hM c) (hy_c K M hM c) (hmax_c K M hM c)

theorem Tc_Y : (Tc K M hM hω c).Y = Yc K M hM c := rfl
theorem Tc_f : (Tc K M hM hω c).f = fc K M hM c := rfl
theorem Tc_e : (Tc K M hM hω c).e = ec K M hM c := rfl
theorem Tc_y : (Tc K M hM hω c).y = yc K M hM c := rfl

end Members2

section Reach

variable (hpts : M.CatchesIndexOnePoints)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Smooth gK] [IsSeparated gK]
  [LocallyOfFiniteType gK] [QuasiCompact gK] in
theorem gFR_incl_comp {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) (U : Y.Opens) {W' :
    Scheme.{u}}
    (k : W' ⟶ ↑U) :
    (genericFibreRestrict R K (U.ι ≫ f) ((k ≫ U.ι) ≫ f) ⟨k, (Category.assoc _ _ _).symm⟩).1 ≫
      pullback.map (U.ι ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K) U.ι
        (𝟙 _) (𝟙 _)
        (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) =
    pullback.map ((k ≫ U.ι) ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K)
      (k ≫ U.ι)
        (𝟙 _) (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp
          _).symm) := by
  apply pullback.hom_ext
  · simp only [genericFibreRestrict, Category.assoc, pullback.map, pullback.lift_fst,
    pullback.lift_fst_assoc,
      Category.comp_id]
  · simp only [genericFibreRestrict, Category.assoc, pullback.map, pullback.lift_snd,
      Category.comp_id]

omit [SmoothOfRelativeDimension d gK] in
include hpts in
theorem reach (T : ComponentReading R K gK d ω) :
    ∃ (c : Idx K M hM) (W : T.Y.Opens) (hyW : T.y ∈ W) (u : SchemeHomOver (W.ι ≫ T.f) (fc K M hM
      c)),
      (genericFibreRestrict R K (fc K M hM c) (W.ι ≫ T.f) u).1 ≫ (ec K M hM c).1 =
        (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1 ∧
      yc K M hM c ⤳ u.1.base ⟨T.y, hyW⟩ := by
  have : Smooth T.f := T.smooth
  obtain ⟨i, U, hU, u₀, hc₀⟩ :=
    NeronModelInfra.exists_nhds_extension_chart_of_catchesIndexOnePoints K M
    (fun i => (hM i).2.2.1) hpts T.f T.e T.y T.hy T.hmax
  set Cp := Cpl K M hM i
  set u₁ : (U : Scheme.{u}) ⟶ Cp.Y' := u₀.1 ≫ Cp.j with hu₁
  have hu₁f : u₁ ≫ Cp.f' = U.ι ≫ T.f := by rw [hu₁, Category.assoc, Cp.hj, u₀.2]
  let wU : (U : Scheme.{u}) := ⟨T.y, hU⟩
  let p : Cp.Y' := u₁ wU
  have hps : Cp.f' p = IsLocalRing.closedPoint R :=
    (congrArg (fun q : (U : Scheme.{u}) ⟶ Spec (CommRingCat.of R) => q wU) hu₁f).trans T.hy
  obtain ⟨ξ, ⟨⟨hξs, hξmax⟩, hξp⟩, -⟩ :=
    (NeronModelInfra.finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens
      Cp.f').2.1 p hps
  let c : Idx K M hM := ⟨i, ⟨ξ, hξs, hξmax⟩⟩
  have hpV : p ∈ V K M hM c := mem_V_of_specializes K M hM c p hps hξp
  let W₀ : (U : Scheme.{u}).Opens := u₁ ⁻¹ᵁ (V K M hM c)
  let W : T.Y.Opens := U.ι ''ᵁ W₀
  have hyW : T.y ∈ W := by
    refine ⟨⟨T.y, hU⟩, hpV, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k : (W : Scheme.{u}) ⟶ ↑U, k = (U.ι.isoImage W₀).inv ≫ W₀.ι := ⟨_, rfl⟩
  have hk : k ≫ U.ι = W.ι := by rw [hkdef, Category.assoc]; exact Scheme.Hom.isoImage_inv_ι _ _
  obtain ⟨uu, huudef⟩ : ∃ uu : (W : Scheme.{u}) ⟶ Yc K M hM c, uu = (U.ι.isoImage W₀).inv ≫ (u₁ ∣_
    V K M hM c) :=
    ⟨_, rfl⟩
  have huuV : uu ≫ (V K M hM c).ι = k ≫ u₁ := by
    rw [huudef, hkdef, Category.assoc, Category.assoc, morphismRestrict_ι]
  have huu : uu ≫ fc K M hM c = W.ι ≫ T.f := by
    change uu ≫ (V K M hM c).ι ≫ Cp.f' = W.ι ≫ T.f
    rw [← Category.assoc, huuV, Category.assoc, hu₁f, ← hk, Category.assoc]
  refine ⟨c, W, hyW, ⟨uu, huu⟩, ?_, ?_⟩
  · let w : SchemeHomOver (W.ι ≫ T.f) (U.ι ≫ T.f) := ⟨k, by rw [← hk, Category.assoc]⟩
    have hcomp : schemeHomOverComp (⟨uu, huu⟩ : SchemeHomOver (W.ι ≫ T.f) (fc K M hM c))
        (⟨(V K M hM c).ι, rfl⟩ : SchemeHomOver (fc K M hM c) Cp.f') =
        schemeHomOverComp (schemeHomOverComp w u₀) ⟨Cp.j, Cp.hj⟩ := by
      apply Subtype.ext
      change uu ≫ (V K M hM c).ι = (k ≫ u₀.1) ≫ Cp.j
      rw [huuV, hu₁, Category.assoc]
    change (genericFibreRestrict R K (fc K M hM c) (W.ι ≫ T.f) ⟨uu, huu⟩).1 ≫
      ((genericFibreRestrict R K Cp.f' (fc K M hM c) ⟨(V K M hM c).ι, rfl⟩).1 ≫ Cp.e'.1) = _
    rw [← Category.assoc, ← NeronModelInfra.schemeHomOverComp_coe (genericFibreRestrict R K (fc K
      M hM c) _ _),
      ← genericFibreRestrict_schemeHomOverComp, hcomp, genericFibreRestrict_schemeHomOverComp,
      genericFibreRestrict_schemeHomOverComp]
    simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc]
    have h2 : (genericFibreRestrict R K Cp.f' (M.str i) ⟨Cp.j, Cp.hj⟩).1 ≫ Cp.e'.1 = (M.chart i).1
      := by
      rw [← NeronModelInfra.schemeHomOverComp_coe, Cp.hchart]
    rw [h2]
    have h3 : (genericFibreRestrict R K (M.str i) (U.ι ≫ T.f) u₀).1 ≫ (M.chart i).1 =
        pullback.map (U.ι ≫ T.f) (specGenericFibreInclusion R K) T.f (specGenericFibreInclusion R
          K) U.ι (𝟙 _)
          (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            T.e.1 := by
      rw [← NeronModelInfra.schemeHomOverComp_coe]; exact hc₀
    rw [h3, genericFibreRestrict_incl_val, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp only [genericFibreRestrict, pullback.map, Category.assoc, pullback.lift_fst,
      pullback.lift_fst_assoc,
        Category.comp_id]
      change pullback.fst (W.ι ≫ T.f) (specGenericFibreInclusion R K) ≫ k ≫ U.ι = _
      rw [hk]
    · simp only [genericFibreRestrict, pullback.map, Category.assoc, pullback.lift_snd,
      Category.comp_id]
  · apply hgen_c
    let w : (W : Scheme.{u}) := ⟨T.y, hyW⟩
    exact (congrArg (fun q : (W : Scheme.{u}) ⟶ Spec (CommRingCat.of R) => q w) huu).trans T.hy

end Reach

section Rel

/-- A component reading locally identifies with a chosen chart at its special point. -/
def Rel' (T : ComponentReading R K gK d ω) (c : Idx K M hM) : Prop :=
  ∃ (W : T.Y.Opens) (hyW : T.y ∈ W) (ε : SchemeHomOver (W.ι ≫ T.f) (fc K M hM c)),
    IsOpenImmersion ε.1 ∧ ε.1.base ⟨T.y, hyW⟩ = yc K M hM c ∧
    (genericFibreRestrict R K (fc K M hM c) (W.ι ≫ T.f) ε).1 ≫ (ec K M hM c).1 =
      (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1

/-- The equivalence relation given by local isomorphisms of component charts. -/
def Rel (c c' : Idx K M hM) : Prop := Rel' K M hM (Tc K M hM hω c) c'

theorem rel_refl (c : Idx K M hM) : Rel K M hM hω c c := by
  refine ⟨⊤, trivial, ⟨(⊤ : (Yc K M hM c).Opens).ι, rfl⟩, ?_, rfl, rfl⟩
  exact (inferInstance : IsOpenImmersion (⊤ : (Yc K M hM c).Opens).ι)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Smooth gK] [IsSeparated gK]
  [LocallyOfFiniteType gK] [QuasiCompact gK] in
theorem gFR_val_congr {Y X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) {g : Y ⟶ Spec
    (CommRingCat.of R)}
    (φ ψ : SchemeHomOver g f) (h : φ.1 = ψ.1) :
    (genericFibreRestrict R K f g φ).1 = (genericFibreRestrict R K f g ψ).1 := by
  have : φ = ψ := Subtype.ext h
  rw [this]

theorem rel'_comp (T : ComponentReading R K gK d ω) (c c' : Idx K M hM)
    (h1 : Rel' K M hM T c) (h2 : Rel K M hM hω c c') : Rel' K M hM T c' := by
  obtain ⟨W, hyW, ε, hεo, hεy, hεc⟩ := h1
  obtain ⟨W₂, hy₂, ε₂, hε₂o, hε₂y, hε₂c⟩ := h2
  change (Yc K M hM c).Opens at W₂
  change yc K M hM c ∈ W₂ at hy₂
  change SchemeHomOver (W₂.ι ≫ fc K M hM c) (fc K M hM c') at ε₂
  change ε₂.1.base ⟨yc K M hM c, hy₂⟩ = yc K M hM c' at hε₂y
  change (genericFibreRestrict R K (fc K M hM c') (W₂.ι ≫ fc K M hM c) ε₂).1 ≫ (ec K M hM c').1 =
      (genericFibreRestrict R K (fc K M hM c) (W₂.ι ≫ fc K M hM c) ⟨W₂.ι, rfl⟩).1 ≫ (ec K M hM
        c).1 at hε₂c
  have : IsOpenImmersion ε.1 := hεo
  have : IsOpenImmersion ε₂.1 := hε₂o
  let W₀ : (W : Scheme.{u}).Opens := ε.1 ⁻¹ᵁ W₂
  let W₃ : T.Y.Opens := W.ι ''ᵁ W₀
  have hy₀ : (⟨T.y, hyW⟩ : (W : Scheme.{u})) ∈ W₀ := by
    change ε.1.base ⟨T.y, hyW⟩ ∈ W₂
    rw [hεy]; exact hy₂
  have hy₃ : T.y ∈ W₃ := ⟨⟨T.y, hyW⟩, hy₀, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k : (W₃ : Scheme.{u}) ⟶ ↑W, k = (W.ι.isoImage W₀).inv ≫ W₀.ι := ⟨_, rfl⟩
  have hk : k ≫ W.ι = W₃.ι := by rw [hkdef, Category.assoc]; exact Scheme.Hom.isoImage_inv_ι _ _
  obtain ⟨m, hmdef⟩ : ∃ m : (W₃ : Scheme.{u}) ⟶ ↑W₂, m = (W.ι.isoImage W₀).inv ≫ (ε.1 ∣_ W₂) :=
    ⟨_, rfl⟩
  have hmW₂ : m ≫ W₂.ι = k ≫ ε.1 := by
    rw [hmdef, hkdef, Category.assoc, Category.assoc, morphismRestrict_ι]
  have : IsOpenImmersion m := by rw [hmdef]; infer_instance
  have hm_over : m ≫ W₂.ι ≫ fc K M hM c = W₃.ι ≫ T.f := by
    rw [← Category.assoc, hmW₂, Category.assoc, ε.2, ← hk, Category.assoc]
  let ε₃ : SchemeHomOver (W₃.ι ≫ T.f) (fc K M hM c') := ⟨m ≫ ε₂.1, by rw [Category.assoc, ε₂.2,
    hm_over]⟩
  refine ⟨W₃, hy₃, ε₃, ?_, ?_, ?_⟩
  · change IsOpenImmersion (m ≫ ε₂.1); infer_instance
  · let w₃ : (W₃ : Scheme.{u}) := ⟨T.y, hy₃⟩
    let w : (W : Scheme.{u}) := ⟨T.y, hyW⟩
    let w₂ : (W₂ : Scheme.{u}) := ⟨yc K M hM c, hy₂⟩
    have hk₀ : k w₃ = w := by
      apply W.ι.isOpenEmbedding.injective
      exact congrArg (fun q : (W₃ : Scheme.{u}) ⟶ T.Y => q w₃) hk
    have hm₀ : m w₃ = w₂ := by
      apply W₂.ι.isOpenEmbedding.injective
      calc
        W₂.ι (m w₃) = ε.1 (k w₃) :=
          congrArg (fun q : (W₃ : Scheme.{u}) ⟶ Yc K M hM c => q w₃) hmW₂
        _ = ε.1 w := congrArg ε.1 hk₀
        _ = W₂.ι w₂ := hεy
    change ε₂.1 (m w₃) = yc K M hM c'
    rw [hm₀]
    exact hε₂y
  · have e1 : ε₃ = schemeHomOverComp (⟨m, hm_over⟩ : SchemeHomOver (W₃.ι ≫ T.f) (W₂.ι ≫ fc K M hM
    c)) ε₂ :=
      Subtype.ext rfl
    rw [e1, genericFibreRestrict_schemeHomOverComp, NeronModelInfra.schemeHomOverComp_coe,
      Category.assoc, hε₂c,
      ← Category.assoc, ← NeronModelInfra.schemeHomOverComp_coe (genericFibreRestrict R K _ _ _),
      ← genericFibreRestrict_schemeHomOverComp]
    have e2 : (genericFibreRestrict R K (fc K M hM c) (W₃.ι ≫ T.f)
        (schemeHomOverComp (⟨m, hm_over⟩ : SchemeHomOver (W₃.ι ≫ T.f) (W₂.ι ≫ fc K M hM c)) ⟨W₂.ι,
          rfl⟩)).1 =
        (genericFibreRestrict R K (fc K M hM c) (W₃.ι ≫ T.f)
          (schemeHomOverComp (⟨k, by rw [← hk, Category.assoc]⟩ : SchemeHomOver (W₃.ι ≫ T.f) (W.ι
            ≫ T.f)) ε)).1 := by
      apply gFR_val_congr
      simp only [NeronModelInfra.schemeHomOverComp_coe]
      exact hmW₂
    rw [e2, genericFibreRestrict_schemeHomOverComp, NeronModelInfra.schemeHomOverComp_coe,
      Category.assoc, hεc,
      ← Category.assoc, ← NeronModelInfra.schemeHomOverComp_coe (genericFibreRestrict R K _ _ _),
      ← genericFibreRestrict_schemeHomOverComp]
    congr 1
    apply gFR_val_congr
    simp only [NeronModelInfra.schemeHomOverComp_coe]
    exact hk

end Rel

section Rel2

theorem rel'_of_n_eq (T : ComponentReading R K gK d ω) (c : Idx K M hM)
    (W : T.Y.Opens) (hyW : T.y ∈ W) (u : SchemeHomOver (W.ι ≫ T.f) (fc K M hM c))
    (hu : (genericFibreRestrict R K (fc K M hM c) (W.ι ≫ T.f) u).1 ≫ (ec K M hM c).1 =
      (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1)
    (hgen : yc K M hM c ⤳ u.1.base ⟨T.y, hyW⟩) (heq : T.n = (Tc K M hM hω c).n) :
    Rel' K M hM T c := by
  obtain ⟨-, h2⟩ :=
    NeronModelInfra.ComponentReading.n_le_n_and_isOpenImmersion_of_n_eq_of_specializes K hω T
    (Tc K M hM hω c) W hyW u hu hgen
  obtain ⟨hpt, W', hW', hyW', hoi⟩ := h2 heq
  refine ⟨W', hyW', ⟨T.Y.homOfLE hW' ≫ u.1, by rw [Category.assoc, u.2, ← Category.assoc,
    Scheme.homOfLE_ι]⟩,
    hoi, ?_, ?_⟩
  · let w' : (W' : Scheme.{u}) := ⟨T.y, hyW'⟩
    have hw : T.Y.homOfLE hW' w' = (⟨T.y, hyW⟩ : (W : Scheme.{u})) :=
      Scheme.homOfLE_apply' hW' T.y hyW'
    change u.1 (T.Y.homOfLE hW' w') = yc K M hM c
    exact (congrArg u.1 hw).trans hpt
  · have e1 : (⟨T.Y.homOfLE hW' ≫ u.1, by rw [Category.assoc, u.2, ← Category.assoc,
    Scheme.homOfLE_ι]⟩ :
        SchemeHomOver (W'.ι ≫ T.f) (fc K M hM c)) =
        schemeHomOverComp (⟨T.Y.homOfLE hW', by rw [← Category.assoc, Scheme.homOfLE_ι]⟩ :
          SchemeHomOver (W'.ι ≫ T.f) (W.ι ≫ T.f)) u := Subtype.ext rfl
    rw [e1, genericFibreRestrict_schemeHomOverComp, NeronModelInfra.schemeHomOverComp_coe,
      Category.assoc, hu,
      ← Category.assoc, ← NeronModelInfra.schemeHomOverComp_coe (genericFibreRestrict R K _ _ _),
      ← genericFibreRestrict_schemeHomOverComp]
    congr 1
    apply gFR_val_congr
    simp only [NeronModelInfra.schemeHomOverComp_coe]
    exact Scheme.homOfLE_ι _ _

theorem rel_symm (c c' : Idx K M hM) (h : Rel K M hM hω c c') : Rel K M hM hω c' c := by
  obtain ⟨W, hyW, ε, hεo, hεy, hεc⟩ := h
  change (Yc K M hM c).Opens at W
  change yc K M hM c ∈ W at hyW
  change SchemeHomOver (W.ι ≫ fc K M hM c) (fc K M hM c') at ε
  change ε.1.base ⟨yc K M hM c, hyW⟩ = yc K M hM c' at hεy
  change (genericFibreRestrict R K (fc K M hM c') (W.ι ≫ fc K M hM c) ε).1 ≫ (ec K M hM c').1 =
      (genericFibreRestrict R K (fc K M hM c) (W.ι ≫ fc K M hM c) ⟨W.ι, rfl⟩).1 ≫ (ec K M hM c).1
        at hεc
  have : IsOpenImmersion ε.1 := hεo
  let W' : (Yc K M hM c').Opens := ε.1.opensRange
  have hy' : yc K M hM c' ∈ W' := by rw [← hεy]; exact ⟨_, rfl⟩
  let ι' := ε.1.isoOpensRange
  have h2 : W.ι ≫ fc K M hM c = ε.1 ≫ fc K M hM c' := ε.2.symm
  have h3 : ι'.inv ≫ ε.1 = W'.ι := Scheme.Hom.isoOpensRange_inv_comp _
  have hε'over : (ι'.inv ≫ W.ι) ≫ fc K M hM c = W'.ι ≫ fc K M hM c' :=
    calc (ι'.inv ≫ W.ι) ≫ fc K M hM c = ι'.inv ≫ (W.ι ≫ fc K M hM c) := Category.assoc _ _ _
      _ = ι'.inv ≫ (ε.1 ≫ fc K M hM c') := congrArg (ι'.inv ≫ ·) h2
      _ = (ι'.inv ≫ ε.1) ≫ fc K M hM c' := (Category.assoc _ _ _).symm
      _ = W'.ι ≫ fc K M hM c' := congrArg (· ≫ fc K M hM c') h3
  let ε' : SchemeHomOver (W'.ι ≫ fc K M hM c') (fc K M hM c) := ⟨ι'.inv ≫ W.ι, hε'over⟩
  refine ⟨W', hy', ε', ?_, ?_, ?_⟩
  · change IsOpenImmersion (ι'.inv ≫ W.ι); infer_instance
  · let w : (W : Scheme.{u}) := ⟨yc K M hM c, hyW⟩
    let w' : (W' : Scheme.{u}) := ⟨yc K M hM c', hy'⟩
    have hw : ι'.hom w = w' := by
      apply W'.ι.isOpenEmbedding.injective
      exact (congrArg (fun q : (W : Scheme.{u}) ⟶ Yc K M hM c' => q w)
        (Scheme.Hom.isoOpensRange_hom_ι ε.1)).trans hεy
    change (ι'.inv ≫ W.ι) w' = yc K M hM c
    rw [← hw]
    exact congrArg (fun q : (W : Scheme.{u}) ⟶ Yc K M hM c => q w)
      (Iso.hom_inv_id_assoc ι' W.ι)
  · change (genericFibreRestrict R K (fc K M hM c) (W'.ι ≫ fc K M hM c') ε').1 ≫ (ec K M hM c).1 =
      (genericFibreRestrict R K (fc K M hM c') (W'.ι ≫ fc K M hM c') ⟨W'.ι, rfl⟩).1 ≫ (ec K M hM
        c').1
    let h : SchemeHomOver (W.ι ≫ fc K M hM c) (W'.ι ≫ fc K M hM c') :=
      ⟨ι'.hom, by rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, ε.2]⟩
    have : IsIso (genericFibreRestrict R K (W'.ι ≫ fc K M hM c') (W.ι ≫ fc K M hM c) h).1 := by
      change IsIso (pullback.lift (pullback.fst (W.ι ≫ fc K M hM c) (specGenericFibreInclusion R
        K) ≫ ι'.hom)
        (pullback.snd _ _) _)
      have : pullback.lift (pullback.fst (W.ι ≫ fc K M hM c) (specGenericFibreInclusion R K) ≫
        ι'.hom)
          (pullback.snd (W.ι ≫ fc K M hM c) (specGenericFibreInclusion R K)) (by rw
            [Category.assoc, h.2, pullback.condition]) =
          pullback.map (W.ι ≫ fc K M hM c) (specGenericFibreInclusion R K) (W'.ι ≫ fc K M hM c')
            (specGenericFibreInclusion R K) ι'.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, h.2])
            ((Category.comp_id _).trans (Category.id_comp _).symm) := by
        apply pullback.hom_ext <;>
          simp only [pullback.map, pullback.lift_fst, pullback.lift_snd, Category.comp_id]
      rw [this]; infer_instance
    have eA : (genericFibreRestrict R K (W'.ι ≫ fc K M hM c') (W.ι ≫ fc K M hM c) h).1 ≫
        (genericFibreRestrict R K (fc K M hM c) (W'.ι ≫ fc K M hM c') ε').1 =
        (genericFibreRestrict R K (fc K M hM c) (W.ι ≫ fc K M hM c) (schemeHomOverComp h
          ε')).1 := by
      rw [genericFibreRestrict_schemeHomOverComp]; rfl
    have eB : (genericFibreRestrict R K (W'.ι ≫ fc K M hM c') (W.ι ≫ fc K M hM c) h).1 ≫
        (genericFibreRestrict R K (fc K M hM c') (W'.ι ≫ fc K M hM c') ⟨W'.ι, rfl⟩).1 =
        (genericFibreRestrict R K (fc K M hM c') (W.ι ≫ fc K M hM c) (schemeHomOverComp h ⟨W'.ι,
          rfl⟩)).1 := by
      rw [genericFibreRestrict_schemeHomOverComp]; rfl
    have e1 : (genericFibreRestrict R K (fc K M hM c) (W.ι ≫ fc K M hM c) (schemeHomOverComp h
      ε')).1 =
        (genericFibreRestrict R K (fc K M hM c) (W.ι ≫ fc K M hM c) ⟨W.ι, rfl⟩).1 := by
      apply gFR_val_congr
      simp only [NeronModelInfra.schemeHomOverComp_coe]
      change ι'.hom ≫ ι'.inv ≫ W.ι = W.ι
      rw [Iso.hom_inv_id_assoc]
    have e2 : (genericFibreRestrict R K (fc K M hM c') (W.ι ≫ fc K M hM c) (schemeHomOverComp h
      ⟨W'.ι, rfl⟩)).1 =
        (genericFibreRestrict R K (fc K M hM c') (W.ι ≫ fc K M hM c) ε).1 := by
      apply gFR_val_congr
      simp only [NeronModelInfra.schemeHomOverComp_coe]
      exact Scheme.Hom.isoOpensRange_hom_ι _
    refine (cancel_epi (genericFibreRestrict R K (W'.ι ≫ fc K M hM c') (W.ι ≫ fc K M hM c)
      h).1).mp ?_
    set X := (genericFibreRestrict R K (W'.ι ≫ fc K M hM c') (W.ι ≫ fc K M hM c) h).1 with hX
    calc X ≫ (genericFibreRestrict R K (fc K M hM c) (W'.ι ≫ fc K M hM c') ε').1 ≫ (ec K M hM c).1
        = (X ≫ (genericFibreRestrict R K (fc K M hM c) (W'.ι ≫ fc K M hM c') ε').1) ≫ (ec K M hM
          c).1 :=
          (Category.assoc _ _ _).symm
      _ = (genericFibreRestrict R K (fc K M hM c) (W.ι ≫ fc K M hM c) ⟨W.ι, rfl⟩).1 ≫ (ec K M hM
        c).1 := by
          rw [eA, e1]
      _ = (genericFibreRestrict R K (fc K M hM c') (W.ι ≫ fc K M hM c) ε).1 ≫ (ec K M hM c').1 :=
        hεc.symm
      _ = (X ≫ (genericFibreRestrict R K (fc K M hM c') (W'.ι ≫ fc K M hM c') ⟨W'.ι, rfl⟩).1) ≫
            (ec K M hM c').1 := by rw [eB, e2]
      _ = X ≫ (genericFibreRestrict R K (fc K M hM c') (W'.ι ≫ fc K M hM c') ⟨W'.ι, rfl⟩).1 ≫ (ec
        K M hM c').1 :=
          Category.assoc _ _ _

end Rel2

section Final

variable (LXK : RelativeGroupLaw K gK) (hpts : M.CatchesIndexOnePoints)

include LXK hpts in
theorem nonempty_idx : Nonempty (Idx K M hM) := by
  obtain ⟨i, U, hU, u₀, -⟩ := NeronModelInfra.exists_nhds_extension_chart_of_catchesIndexOnePoints
    K M
    (fun i => (hM i).2.2.1) hpts (𝟙 (Spec (CommRingCat.of R)))
    (LXK.one (pullback.snd (𝟙 _) (specGenericFibreInclusion R K))) (IsLocalRing.closedPoint R) rfl
    (fun y _ h => h)
  set Cp := Cpl K M hM i
  let u : (U : Scheme.{u}) := ⟨(IsLocalRing.closedPoint R : Spec (CommRingCat.of R)), hU⟩
  let p : Cp.Y' := (u₀.1 ≫ Cp.j) u
  have hps : Cp.f' p = IsLocalRing.closedPoint R := by
    have hcomp : (u₀.1 ≫ Cp.j) ≫ Cp.f' = U.ι := by
      rw [Category.assoc, Cp.hj, u₀.2, Category.comp_id]
    exact congrArg (fun q : (U : Scheme.{u}) ⟶ Spec (CommRingCat.of R) => q u) hcomp
  obtain ⟨ξ, ⟨⟨hξs, hξmax⟩, -⟩, -⟩ :=
    (NeronModelInfra.finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens
      Cp.f').2.1 p hps
  exact ⟨⟨i, ⟨ξ, hξs, hξmax⟩⟩⟩

include hfin hM hω LXK hpts in
theorem exists_D : ∃ D : MinimalComponentData R K gK d ω, D.IsOmegaMinimal := by
  classical
  have : Finite (Idx K M hM) := finite_idx K M hfin hM
  have : Nonempty (Idx K M hM) := nonempty_idx K M hM LXK hpts
  obtain ⟨c₀, hc₀⟩ := Finite.exists_min (fun c : Idx K M hM => (Tc K M hM hω c).n)
  set n₀ := (Tc K M hM hω c₀).n with hn₀
  let I₁ := {c : Idx K M hM // (Tc K M hM hω c).n = n₀}
  have : Nonempty I₁ := ⟨⟨c₀, rfl⟩⟩
  let s : Setoid I₁ :=
    { r := fun a b => Rel K M hM hω a.1 b.1
      iseqv :=
        { refl := fun a => rel_refl K M hM hω a.1
          symm := fun h => rel_symm K M hM hω _ _ h
          trans := fun h h' => rel'_comp K M hM hω _ _ _ h h' } }
  let Q := Quotient s
  have : Finite Q := Quotient.finite s
  have : Nonempty Q := ⟨Quotient.mk s (Classical.arbitrary I₁)⟩
  let rep : Q → I₁ := fun q => q.out
  have hrep : ∀ q : Q, Quotient.mk s (rep q) = q := fun q => Quotient.out_eq q
  have hrel_of_mk_eq : ∀ a b : I₁, Quotient.mk s a = Quotient.mk s b → Rel K M hM hω a.1 b.1 :=
    fun a b h => Quotient.exact h
  have : ∀ c : Idx K M hM, QuasiCompact (fc K M hM c) := fun c => by
    have : NoetherianSpace ↥(Yc K M hM c) := NoetherianSpace.set _
    infer_instance
  refine ⟨{
    ι := Q
    finite := inferInstance
    nonempty := inferInstance
    C := fun q => Tc K M hM hω (rep q).1
    isSeparated := fun q => inferInstance
    quasiCompact := fun q => inferInstance
    isIso := fun q => inferInstance
    hgen := fun q => hgen_c K M hM (rep q).1
    inequiv := ?_ }, ?_, ?_⟩
  · intro q q' hne U hyU u heq
    apply hne
    let w : (U : Scheme.{u}) := ⟨yc K M hM (rep q).1, hyU⟩
    have hsp : (fc K M hM (rep q').1) (u.1 w) = IsLocalRing.closedPoint R :=
      (congrArg (fun g : (U : Scheme.{u}) ⟶ Spec (CommRingCat.of R) => g w) u.2).trans
        (hy_c K M hM (rep q).1)
    have hg : yc K M hM (rep q').1 ⤳ u.1.base ⟨yc K M hM (rep q).1, hyU⟩ := hgen_c K M hM (rep
      q').1 _ hsp
    have hn : (Tc K M hM hω (rep q).1).n = (Tc K M hM hω (rep q').1).n := (rep q).2.trans (rep
      q').2.symm
    have r : Rel K M hM hω (rep q).1 (rep q').1 :=
      rel'_of_n_eq K M hM hω (Tc K M hM hω (rep q).1) (rep q').1 U hyU u heq hg hn
    rw [← hrep q, ← hrep q']
    exact Quotient.sound r
  · intro q T
    obtain ⟨c, W, hyW, u, hu, hg⟩ := reach K M hM hpts T
    have h1 := (NeronModelInfra.ComponentReading.n_le_n_and_isOpenImmersion_of_n_eq_of_specializes
      K hω T
      (Tc K M hM hω c) W hyW u hu hg).1
    have h0 : (Tc K M hM hω (rep q).1).n ≤ (Tc K M hM hω c).n := by rw [(rep q).2]; exact hc₀ c
    exact h0.trans h1
  · rintro T ⟨q₀, hT⟩
    obtain ⟨c, W, hyW, u, hu, hg⟩ := reach K M hM hpts T
    have h1 := (NeronModelInfra.ComponentReading.n_le_n_and_isOpenImmersion_of_n_eq_of_specializes
      K hω T
      (Tc K M hM hω c) W hyW u hu hg).1
    have hTn : T.n = n₀ := hT.trans (rep q₀).2
    have hc : (Tc K M hM hω c).n = n₀ := le_antisymm (h1.trans hTn.le) (hc₀ c)
    have heq : T.n = (Tc K M hM hω c).n := hTn.trans hc.symm
    have r1 : Rel' K M hM T c := rel'_of_n_eq K M hM hω T c W hyW u hu hg heq
    let c1 : I₁ := ⟨c, hc⟩
    let q := Quotient.mk s c1
    have r2 : Rel K M hM hω c (rep q).1 := by
      apply rel_symm
      exact hrel_of_mk_eq (rep q) c1 (hrep q)
    exact ⟨q, rel'_comp K M hM hω T c (rep q).1 r1 r2⟩

end Final

end Main

end Selection

end

end AbelianVarieties.NOSProofs.MinimalComponentSelection

namespace NeronModelInfra

open AbelianVarieties.NOSProofs.MinimalComponentSelection

theorem
    exists_minimalComponentData_isOmegaMinimal_of_catchesIndexOnePoints
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK)
    (M : ModelFamily R K gK) (hfin : Finite M.ι)
    (hM : ∀ i, Smooth (M.str i) ∧ IsSeparated (M.str i) ∧ LocallyOfFiniteType (M.str i) ∧
      QuasiCompact (M.str i))
    (hpts : M.CatchesIndexOnePoints)
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤)) (hω : Scheme.Modules.IsFrameOn ω ⊤) :
    ∃ D : MinimalComponentData R K gK d ω, D.IsOmegaMinimal :=
  Selection.exists_D K M hfin hM hω LXK hpts

end NeronModelInfra
end
