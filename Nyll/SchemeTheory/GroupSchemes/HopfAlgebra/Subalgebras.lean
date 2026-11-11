/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Set
public import Nyll.SchemeTheory.RingTheory.Coalgebras
public import Nyll.SchemeTheory.RingTheory.Flat.Descent
public import Nyll.SchemeTheory.GroupSchemes.HopfAlgebra.Basic
public import Nyll.SchemeTheory.GroupSchemes.HopfAlgebra.Flatness
public import Nyll.SchemeTheory.GroupSchemes.HopfAlgebra.Kernels
public import Nyll.SchemeTheory.GroupSchemes.HopfAlgebra.Quotients
public import Nyll.SchemeTheory.GroupSchemes.HopfAlgebra.Reducedness
public import Nyll.SchemeTheory.LocalGeometry.Points
public import Nyll.SchemeTheory.RingTheory.Flat.OpenLocus

/-!
# Faithful flatness over stable Hopf subalgebras

Subalgebras stable under comultiplication and the antipode inherit a Hopf algebra structure.
Finite-dimensional subcoalgebras give finitely generated stable subalgebras, and descent
reduces faithful flatness to the reduced case over an algebraically closed field.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.HopfSubalgebras.ReducedCase

open scoped TensorProduct

universe u v w

namespace InducedStructure

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]

variable (K : Subalgebra k H)

/-- The inclusion of the stable subalgebra as a linear map. -/
abbrev ι : ↥K →ₗ[k] H := K.val.toLinearMap

/-- The tensor square of the subalgebra inclusion. -/
abbrev ι₂ : ↥K ⊗[k] ↥K →ₗ[k] H ⊗[k] H := TensorProduct.map (ι K) (ι K)

theorem ι_injective : Function.Injective (ι K) := Subtype.val_injective

theorem ι₂_injective : Function.Injective (ι₂ K) :=
  TensorProduct.map_injective_of_flat_flat _ _ (ι_injective K) (ι_injective K)

theorem ι₂_tmul (a b : ↥K) : ι₂ K (a ⊗ₜ[k] b) = (a : H) ⊗ₜ[k] (b : H) := rfl

theorem span_le_range_ι₂ :
    Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b} ≤ LinearMap.range (ι₂ K) := by
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact ⟨⟨a, ha⟩ ⊗ₜ[k] ⟨b, hb⟩, rfl⟩

section comul

variable (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
  Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
include hΔ

theorem comul_mem_range (x : ↥K) : Coalgebra.comul (R := k) (x : H) ∈ LinearMap.range (ι₂ K) :=
  span_le_range_ι₂ K (hΔ x x.2)

/-- The comultiplication obtained by restricting to the stable subalgebra. -/
noncomputable def comulLin : ↥K →ₗ[k] ↥K ⊗[k] ↥K :=
  (LinearEquiv.ofInjective (ι₂ K) (ι₂_injective K)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range (ι₂ K)) (Coalgebra.comul ∘ₗ ι K) (comul_mem_range K hΔ)

@[scoped simp] theorem ι₂_comulLin (x : ↥K) : ι₂ K (comulLin K hΔ x) = Coalgebra.comul (R := k) (x
    : H) := by
  simp only [comulLin, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [← LinearEquiv.ofInjective_apply (ι₂ K) (h := ι₂_injective K), LinearEquiv.apply_symm_apply]
  rfl

end comul

/-- The counit restricted to the stable subalgebra. -/
def counitLin : ↥K →ₗ[k] k := Coalgebra.counit ∘ₗ ι K

@[scoped simp] theorem counitLin_apply (x : ↥K) : counitLin K x = Coalgebra.counit (R := k) (x :
    H) := rfl

theorem map_ι₂_ι_rTensor {f : ↥K →ₗ[k] ↥K ⊗[k] ↥K} {F : H →ₗ[k] H ⊗[k] H}
    (hfF : ∀ x, ι₂ K (f x) = F (x : H)) (z : ↥K ⊗[k] ↥K) :
    TensorProduct.map (ι₂ K) (ι K) (LinearMap.rTensor (↥K) f z) = LinearMap.rTensor H F (ι₂ K z)
      := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, hfF]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem map_ι_ι₂_lTensor {f : ↥K →ₗ[k] ↥K ⊗[k] ↥K} {F : H →ₗ[k] H ⊗[k] H}
    (hfF : ∀ x, ι₂ K (f x) = F (x : H)) (z : ↥K ⊗[k] ↥K) :
    TensorProduct.map (ι K) (ι₂ K) (LinearMap.lTensor (↥K) f z) = LinearMap.lTensor H F (ι₂ K z)
      := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [LinearMap.lTensor_tmul, TensorProduct.map_tmul, hfF]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem map_ι_ι₂_assoc (w : (↥K ⊗[k] ↥K) ⊗[k] ↥K) :
    TensorProduct.map (ι K) (ι₂ K) (TensorProduct.assoc k _ _ _ w) =
      TensorProduct.assoc k H H H (TensorProduct.map (ι₂ K) (ι K) w) := by
  induction w using TensorProduct.inductionOn with
  | tmul z c =>
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp only [TensorProduct.assoc_tmul, TensorProduct.map_tmul]
    | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem ι₃_injective : Function.Injective (TensorProduct.map (ι K) (ι₂ K)) :=
  TensorProduct.map_injective_of_flat_flat _ _ (ι_injective K) (ι₂_injective K)

theorem lTensor_ι_rTensor_counit (z : ↥K ⊗[k] ↥K) :
    LinearMap.lTensor k (ι K) (LinearMap.rTensor (↥K) (counitLin K) z) =
      LinearMap.rTensor H Coalgebra.counit (ι₂ K z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      TensorProduct.map_tmul, counitLin_apply]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem rTensor_ι_lTensor_counit (z : ↥K ⊗[k] ↥K) :
    LinearMap.rTensor k (ι K) (LinearMap.lTensor (↥K) (counitLin K) z) =
      LinearMap.lTensor H Coalgebra.counit (ι₂ K z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      TensorProduct.map_tmul, counitLin_apply]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

section structures

variable (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
  Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})

/-- The comultiplication and counit on the stable subalgebra. -/
@[reducible] noncomputable def coalgebraStruct : CoalgebraStruct k ↥K where
  comul := comulLin K hΔ
  counit := counitLin K

/-- The coalgebra induced on the stable subalgebra. -/
@[reducible] noncomputable def coalgebra : Coalgebra k ↥K :=
  { coalgebraStruct K hΔ with
    coassoc := by
      apply LinearMap.ext
      intro x
      apply ι₃_injective K
      change TensorProduct.map (ι K) (ι₂ K) (TensorProduct.assoc k _ _ _
          (LinearMap.rTensor (↥K) (comulLin K hΔ) (comulLin K hΔ x))) =
        TensorProduct.map (ι K) (ι₂ K) (LinearMap.lTensor (↥K) (comulLin K hΔ) (comulLin K hΔ x))
      rw [map_ι_ι₂_assoc, map_ι₂_ι_rTensor K (ι₂_comulLin K hΔ), map_ι_ι₂_lTensor K (ι₂_comulLin K
        hΔ),
        ι₂_comulLin, Coalgebra.coassoc_apply]
    rTensor_counit_comp_comul := by
      apply LinearMap.ext
      intro x
      apply Module.Flat.lTensor_preserves_injective_linearMap (M := k) (ι K) (ι_injective K)
      change LinearMap.lTensor k (ι K) (LinearMap.rTensor (↥K) (counitLin K) (comulLin K hΔ x)) =
        LinearMap.lTensor k (ι K) ((1 : k) ⊗ₜ[k] x)
      rw [lTensor_ι_rTensor_counit, ι₂_comulLin, Coalgebra.rTensor_counit_comul]
      rfl
    lTensor_counit_comp_comul := by
      apply LinearMap.ext
      intro x
      apply Module.Flat.rTensor_preserves_injective_linearMap (M := k) (ι K) (ι_injective K)
      change LinearMap.rTensor k (ι K) (LinearMap.lTensor (↥K) (counitLin K) (comulLin K hΔ x)) =
        LinearMap.rTensor k (ι K) (x ⊗ₜ[k] (1 : k))
      rw [rTensor_ι_lTensor_counit, ι₂_comulLin, Coalgebra.lTensor_counit_comul]
      rfl }

end structures

theorem ι₂_eq_toLinearMap :
    ι₂ K = (Algebra.TensorProduct.map K.val K.val).toLinearMap := by
  apply TensorProduct.ext'
  intro a b
  rfl

theorem ι₂_mul (z w : ↥K ⊗[k] ↥K) : ι₂ K (z * w) = ι₂ K z * ι₂ K w := by
  rw [ι₂_eq_toLinearMap]
  exact map_mul (Algebra.TensorProduct.map K.val K.val) z w

theorem ι₂_one : ι₂ K 1 = 1 := by
  rw [ι₂_eq_toLinearMap]
  exact map_one (Algebra.TensorProduct.map K.val K.val)

section structures2

variable (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
  Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})

theorem comulLin_mul (a b : ↥K) : comulLin K hΔ (a * b) = comulLin K hΔ a * comulLin K hΔ b := by
  apply ι₂_injective K
  rw [ι₂_mul, ι₂_comulLin, ι₂_comulLin, ι₂_comulLin, Subalgebra.coe_mul, Bialgebra.comul_mul]

theorem comulLin_one : comulLin K hΔ 1 = 1 := by
  apply ι₂_injective K
  rw [ι₂_comulLin, ι₂_one, Subalgebra.coe_one, Bialgebra.comul_one]

/-- The bialgebra induced on the stable subalgebra. -/
@[reducible] noncomputable def bialgebra : Bialgebra k ↥K :=
  { coalgebra K hΔ with
    counit_one := by
      change counitLin K 1 = 1
      rw [counitLin_apply, Subalgebra.coe_one, Bialgebra.counit_one]
    mul_compr₂_counit := by
      apply LinearMap.ext; intro a; apply LinearMap.ext; intro b
      change counitLin K (a * b) = counitLin K a * counitLin K b
      rw [counitLin_apply, counitLin_apply, counitLin_apply, Subalgebra.coe_mul,
        Bialgebra.counit_mul]
    comul_one := comulLin_one K hΔ
    mul_compr₂_comul := by
      apply LinearMap.ext; intro a; apply LinearMap.ext; intro b
      exact comulLin_mul K hΔ a b }

variable (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)

/-- The antipode restricted to the stable subalgebra. -/
def antipodeLin : ↥K →ₗ[k] ↥K :=
  LinearMap.codRestrict K.toSubmodule ((HopfAlgebra.antipode k).comp (ι K)) (fun x => hS x x.2)

@[scoped simp] theorem coe_antipodeLin (x : ↥K) : (antipodeLin K hS x : H) = HopfAlgebra.antipode
    k (x : H) := rfl

theorem ι_mul'_rTensor (z : ↥K ⊗[k] ↥K) :
    ι K (LinearMap.mul' k ↥K (LinearMap.rTensor (↥K) (antipodeLin K hS) z)) =
      LinearMap.mul' k H (LinearMap.rTensor H (HopfAlgebra.antipode k) (ι₂ K z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem ι_mul'_lTensor (z : ↥K ⊗[k] ↥K) :
    ι K (LinearMap.mul' k ↥K (LinearMap.lTensor (↥K) (antipodeLin K hS) z)) =
      LinearMap.mul' k H (LinearMap.lTensor H (HopfAlgebra.antipode k) (ι₂ K z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [LinearMap.lTensor_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The Hopf algebra induced on the stable subalgebra. -/
@[reducible] noncomputable def hopfAlgebra : HopfAlgebra k ↥K :=
  { bialgebra K hΔ with
    antipode := antipodeLin K hS
    mul_antipode_rTensor_comul := by
      apply LinearMap.ext; intro x
      apply ι_injective K
      change ι K (LinearMap.mul' k ↥K (LinearMap.rTensor (↥K) (antipodeLin K hS) (comulLin K hΔ
        x))) =
        ι K (algebraMap k ↥K (counitLin K x))
      rw [ι_mul'_rTensor, ι₂_comulLin, HopfAlgebra.mul_antipode_rTensor_comul_apply,
        counitLin_apply]
      rfl
    mul_antipode_lTensor_comul := by
      apply LinearMap.ext; intro x
      apply ι_injective K
      change ι K (LinearMap.mul' k ↥K (LinearMap.lTensor (↥K) (antipodeLin K hS) (comulLin K hΔ
        x))) =
        ι K (algebraMap k ↥K (counitLin K x))
      rw [ι_mul'_lTensor, ι₂_comulLin, HopfAlgebra.mul_antipode_lTensor_comul_apply,
        counitLin_apply]
      rfl }

theorem val_comul (x : ↥K) :
    let : HopfAlgebra k ↥K := hopfAlgebra K hΔ hS
    Coalgebra.comul (R := k) (x : H) =
      TensorProduct.map (IsScalarTower.toAlgHom k ↥K H).toLinearMap (IsScalarTower.toAlgHom k ↥K
        H).toLinearMap
        (Coalgebra.comul (R := k) x) := by
  intro sharedOwner1
  change Coalgebra.comul (R := k) (x : H) = TensorProduct.map _ _ (comulLin K hΔ x)
  rw [← ι₂_comulLin K hΔ x]
  rfl

theorem val_counit (x : ↥K) :
    letI : HopfAlgebra k ↥K := hopfAlgebra K hΔ hS
    Coalgebra.counit (R := k) (x : H) = Coalgebra.counit (R := k) x := rfl

theorem val_antipode (x : ↥K) :
    letI : HopfAlgebra k ↥K := hopfAlgebra K hΔ hS
    ((HopfAlgebra.antipode k x : ↥K) : H) = HopfAlgebra.antipode k (x : H) := rfl

theorem algebraMap_injective : Function.Injective (algebraMap ↥K H) := Subtype.val_injective

end structures2

end InducedStructure

namespace Translations

/-- The canonical localization module, selected before specializing to a subalgebra. -/
private abbrev localizationModule {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal B) [P.IsPrime] : Module A (Localization.AtPrime P) :=
  inferInstance

theorem flat_transport {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (σ : A ≃+* A) (e : B ≃+* B) (hcompat : ∀ a, e (algebraMap A B a) = algebraMap A B (σ a))
    (P Q : Ideal B) [P.IsPrime] [Q.IsPrime] (hQP : ∀ x, x ∈ Q ↔ e x ∈ P)
    (hP : Module.Flat A (Localization.AtPrime P)) : Module.Flat A (Localization.AtPrime Q) := by
  have hmapS : Submonoid.map e.toMonoidHom Q.primeCompl = P.primeCompl := by
    ext y
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact fun h => hx ((hQP x).mpr h)
    · intro hy
      refine ⟨e.symm y, fun h => hy ?_, ?_⟩
      · have := (hQP (e.symm y)).mp h
        simpa only [RingEquiv.apply_symm_apply] using this
      · exact e.apply_symm_apply y
  let eLoc : Localization.AtPrime Q ≃+* Localization.AtPrime P :=
    IsLocalization.ringEquivOfRingEquiv (M := Q.primeCompl) (T := P.primeCompl)
      (Localization.AtPrime Q) (Localization.AtPrime P) e hmapS
  have hsq : ∀ x : A, eLoc (algebraMap A (Localization.AtPrime Q) x) =
      algebraMap A (Localization.AtPrime P) (σ x) := by
    intro x
    rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime Q),
      IsScalarTower.algebraMap_apply A B (Localization.AtPrime P),
      IsLocalization.ringEquivOfRingEquiv_eq, hcompat]
  have hflatP : (algebraMap A (Localization.AtPrime P)).Flat := RingHom.flat_algebraMap_iff.mpr hP
  have hcomp : algebraMap A (Localization.AtPrime Q) =
      (eLoc.symm.toRingHom.comp (algebraMap A (Localization.AtPrime P))).comp (σ : A →+* A) := by
    apply RingHom.ext
    intro x
    change algebraMap A (Localization.AtPrime Q) x = eLoc.symm (algebraMap A (Localization.AtPrime
      P) (σ x))
    rw [← hsq, RingEquiv.symm_apply_apply]
  rw [← RingHom.flat_algebraMap_iff, hcomp]
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective σ.bijective)
    (RingHom.Flat.comp hflatP (RingHom.Flat.of_bijective eLoc.symm.bijective))

theorem exists_flat_localization_atPrime_of_isReduced_of_injective
    (K : Type v) [CommRing K] [IsReduced K]
    (H : Type w) [CommRing H] [Nontrivial H] [Algebra K H] (hinj : Function.Injective (algebraMap
      K H)) :
    ∃ Q : PrimeSpectrum H, Module.Flat K (Localization.AtPrime Q.asIdeal) := by
  classical
  have : Nontrivial K := (algebraMap K H).domain_nontrivial
  obtain ⟨⟨p, hp⟩⟩ := Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal K)) bot_ne_top
  have hp' : p ∈ minimalPrimes K := hp
  obtain ⟨Q, hQ, hQp⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective hinj p hp'
  have : p.IsPrime := hp.1.1
  have : Q.IsPrime := hQ
  refine ⟨⟨Q, hQ⟩, ?_⟩
  let Kp := Localization.AtPrime p
  have : Ring.KrullDimLE 0 Kp := Ring.KrullDimLE.of_isLocalization p hp' Kp
  have : IsReduced Kp := inferInstance
  have hfield : IsField Kp := Ring.KrullDimLE.isField_of_isReduced
  let : Field Kp := hfield.toField
  let φ : Kp →+* Localization.AtPrime Q := Localization.localRingHom p Q (algebraMap K H) hQp.symm
  let : Algebra Kp (Localization.AtPrime Q) := φ.toAlgebra
  have : IsScalarTower K Kp (Localization.AtPrime Q) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap K (Localization.AtPrime Q) x = φ (algebraMap K Kp x)
    rw [Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply K H (Localization.AtPrime
      Q)]
  have : Module.Flat K Kp := IsLocalization.flat Kp p.primeCompl
  have : Module.Flat Kp (Localization.AtPrime Q) := inferInstance
  exact Module.Flat.trans K Kp (Localization.AtPrime Q)

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]

theorem exists_algHom_ker_eq [IsAlgClosed k] [Algebra.FiniteType k H]
    (M : Ideal H) [hM : M.IsMaximal] :
    ∃ x : H →ₐ[k] k, RingHom.ker x = M := by
  let : Field (H ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite k (H ⧸ M) := finite_of_finite_type_of_isJacobsonRing k (H ⧸ M)
  have : Algebra.IsIntegral k (H ⧸ M) := inferInstance
  let e : k ≃ₐ[k] (H ⧸ M) :=
    AlgEquiv.ofBijective (Algebra.ofId k (H ⧸ M)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k M), ?_⟩
  ext h
  simp only [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [show (e.symm.toAlgHom (Ideal.Quotient.mk M h) = 0) ↔ (Ideal.Quotient.mk M h = 0) from
    ⟨fun h0 => by
      exact e.symm.injective (h0.trans (map_zero e.symm).symm),
      fun h0 => by rw [h0, map_zero]⟩]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Left translation by a rational point of the affine group scheme. -/
noncomputable def τ (g : H →ₐ[k] k) : H →ₐ[k] H :=
  (Algebra.TensorProduct.lid k H).toAlgHom.comp
    ((Algebra.TensorProduct.map g (AlgHom.id k H)).comp (Bialgebra.comulAlgHom k H))

theorem τ_spec (g : H →ₐ[k] k) (h : H) :
    τ g h = Algebra.TensorProduct.lid k H (Algebra.TensorProduct.map g (AlgHom.id k H)
      (Coalgebra.comul h)) := rfl

end Translations

open Translations in
theorem _root_.HopfAlgebra.faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k] {H : Type v} [CommRing H] [HopfAlgebra k H]
      [Algebra.FiniteType k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)
    (hfg : K.FG) [IsReduced ↥K] :
    Module.FaithfullyFlat ↥K H := by
  classical
  let hK : HopfAlgebra k ↥K := InducedStructure.hopfAlgebra K hΔ hS
  have : Algebra.FiniteType k ↥K := (Subalgebra.fg_iff_finiteType K).mp hfg
  have : IsNoetherianRing ↥K := Algebra.FiniteType.isNoetherianRing k ↥K
  have : Algebra.FiniteType ↥K H := Algebra.FiniteType.of_restrictScalars_finiteType k ↥K H
  have : IsJacobsonRing H := isJacobsonRing_of_finiteType (A := k) (B := H)
  have hinj : Function.Injective (algebraMap ↥K H) := Subtype.val_injective
  have hH : Nontrivial H := Bialgebra.nontrivial k
  let localizationModules (P : Ideal H) [P.IsPrime] : Module ↥K (Localization.AtPrime P) :=
    localizationModule (A := ↥K) P
  obtain ⟨hτbij, hτmem, hτtrans⟩ :=
    HopfAlgebra.bijective_translate_and_map_mem_and_exists_comp_translate_eq (k := k) (H := H) τ
      τ_spec
  let τK : (↥K →ₐ[k] k) → (↥K →ₐ[k] ↥K) := fun g =>
    (Algebra.TensorProduct.lid k ↥K).toAlgHom.comp
      ((Algebra.TensorProduct.map g (AlgHom.id k ↥K)).comp (Bialgebra.comulAlgHom k ↥K))
  obtain ⟨hτKbij, -, -⟩ :=
    HopfAlgebra.bijective_translate_and_map_mem_and_exists_comp_translate_eq (k := k) (H := ↥K) τK
      (fun g h => rfl)
  have hτK : ∀ (g : H →ₐ[k] k) (x : ↥K), ((τK (g.comp K.val) x : ↥K) : H) = τ g x := by
    intro g x
    change ((Algebra.TensorProduct.lid k ↥K (Algebra.TensorProduct.map (g.comp K.val) (AlgHom.id k
      ↥K)
      (Coalgebra.comul (R := k) x)) : ↥K) : H) =
      Algebra.TensorProduct.lid k H (Algebra.TensorProduct.map g (AlgHom.id k H) (Coalgebra.comul
        (R := k) (x : H)))
    rw [InducedStructure.val_comul K hΔ hS x]
    induction (Coalgebra.comul (R := k) x) using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul,
        TensorProduct.map_tmul,
        AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgHom.coe_id, id_eq,
          IsScalarTower.coe_toAlgHom',
        Subalgebra.coe_smul]
      rfl
    | add a b ha hb =>
      simp only [map_add, Subalgebra.coe_add, ha, hb]
  have hUopen : IsOpen {Q : PrimeSpectrum H | Module.Flat ↥K (Localization.AtPrime Q.asIdeal)} :=
    Module.Flat.isOpen_setOf_flat_localization_atPrime (A := ↥K) (B := H)
  have hUne : ({Q : PrimeSpectrum H | Module.Flat ↥K (Localization.AtPrime Q.asIdeal)}).Nonempty
    := by
    obtain ⟨Q, hQ⟩ := exists_flat_localization_atPrime_of_isReduced_of_injective ↥K H hinj
    exact ⟨Q, hQ⟩
  have hUtrans : ∀ P Q : PrimeSpectrum H, P.asIdeal.IsMaximal → Q.asIdeal.IsMaximal →
      P ∈ {Q : PrimeSpectrum H | Module.Flat ↥K (Localization.AtPrime Q.asIdeal)} → Q ∈ {Q :
        PrimeSpectrum H | Module.Flat ↥K (Localization.AtPrime Q.asIdeal)} := by
    intro P Q hP hQ hPU
    have : P.asIdeal.IsMaximal := hP
    have : Q.asIdeal.IsMaximal := hQ
    obtain ⟨xP, hxP⟩ := exists_algHom_ker_eq (k := k) P.asIdeal
    obtain ⟨xQ, hxQ⟩ := exists_algHom_ker_eq (k := k) Q.asIdeal
    obtain ⟨g, hg⟩ := hτtrans xP xQ
    let e : H ≃ₐ[k] H := AlgEquiv.ofBijective (τ g) (hτbij g)
    have he : ∀ h, e h = τ g h := fun _ => rfl
    have hQP : ∀ x : H, x ∈ Q.asIdeal ↔ e x ∈ P.asIdeal := by
      intro x
      rw [← hxQ, ← hxP, hg, RingHom.mem_ker, RingHom.mem_ker, he]
      rfl
    let σ : ↥K ≃ₐ[k] ↥K := AlgEquiv.ofBijective (τK (g.comp K.val)) (hτKbij _)
    have hσ : ∀ x : ↥K, ((σ x : ↥K) : H) = e x := fun x => hτK g x
    have hPU' : Module.Flat ↥K (Localization.AtPrime P.asIdeal) := hPU
    have : P.asIdeal.IsPrime := hP.isPrime
    have : Q.asIdeal.IsPrime := hQ.isPrime
    exact flat_transport (A := ↥K) (B := H) σ.toRingEquiv e.toRingEquiv (fun a => (hσ a).symm)
      P.asIdeal Q.asIdeal hQP hPU'
  have hU : {Q : PrimeSpectrum H | Module.Flat ↥K (Localization.AtPrime Q.asIdeal)} = Set.univ :=
    PrimeSpectrum.eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal _ hUopen hUne hUtrans
  have hflat : Module.Flat ↥K H := by
    apply Module.flat_of_isLocalized_maximal H H (fun P _ => Localization.AtPrime P)
      (fun P _ => Algebra.linearMap H (Localization.AtPrime P))
    intro P hP
    have hmem : (⟨P, hP.isPrime⟩ : PrimeSpectrum H) ∈ {Q : PrimeSpectrum H | Module.Flat ↥K
      (Localization.AtPrime Q.asIdeal)} := by
      rw [hU]; trivial
    exact hmem
  exact HopfAlgebra.faithfullyFlat_of_flat_of_injective_of_isAlgClosed ↥K H hinj
    (fun x => InducedStructure.val_comul K hΔ hS x) (fun x => InducedStructure.val_counit K hΔ hS x)

end SchemeTheory.HopfSubalgebras.ReducedCase
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.HopfSubalgebras.FiniteGeneration

open scoped TensorProduct

universe u v

namespace TensorSpans

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]

/-- The span of pure tensors with factors in the indicated submodules. -/
def spanTmul (A B : Submodule k H) : Submodule k (H ⊗[k] H) :=
  Submodule.span k {t : H ⊗[k] H | ∃ a ∈ A, ∃ b ∈ B, t = a ⊗ₜ[k] b}

theorem spanTmul_def (A B : Submodule k H) :
    spanTmul A B = Submodule.span k {t : H ⊗[k] H | ∃ a ∈ A, ∃ b ∈ B, t = a ⊗ₜ[k] b} := rfl

theorem spanTmul_mono {A A' B B' : Submodule k H} (hA : A ≤ A') (hB : B ≤ B') : spanTmul A B ≤
    spanTmul A' B' :=
  Submodule.span_mono fun _ ⟨a, ha, b, hb, hs⟩ => ⟨a, hA ha, b, hB hb, hs⟩

theorem tmul_mem_spanTmul {A B : Submodule k H} {a b : H} (ha : a ∈ A) (hb : b ∈ B) : a ⊗ₜ[k] b ∈
    spanTmul A B :=
  Submodule.subset_span ⟨a, ha, b, hb, rfl⟩

theorem map_comm_mem_spanTmul (A B : Submodule k H) (t : H ⊗[k] H) (ht : t ∈ spanTmul A B) :
    TensorProduct.comm k H H (TensorProduct.map (HopfAlgebra.antipode k) (HopfAlgebra.antipode k) t)
      ∈ spanTmul (B.map (HopfAlgebra.antipode k (A := H))) (A.map (HopfAlgebra.antipode k (A :=
        H))) := by
  induction ht using Submodule.span_induction with
  | mem s hs =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hs
      rw [TensorProduct.map_tmul, TensorProduct.comm_tmul]
      exact tmul_mem_spanTmul (Submodule.mem_map_of_mem hb) (Submodule.mem_map_of_mem ha)
  | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
  | add s t _ _ hs ht => rw [map_add, map_add]; exact Submodule.add_mem _ hs ht
  | smul r s _ hs => rw [map_smul, map_smul]; exact Submodule.smul_mem _ _ hs

theorem mul_mem_spanTmul (A : Subalgebra k H) {x y : H ⊗[k] H}
    (hx : x ∈ spanTmul A.toSubmodule A.toSubmodule) (hy : y ∈ spanTmul A.toSubmodule
      A.toSubmodule) :
    x * y ∈ spanTmul A.toSubmodule A.toSubmodule := by
  induction hx using Submodule.span_induction generalizing y with
  | mem s hs =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hs
      induction hy using Submodule.span_induction with
      | mem t ht =>
          obtain ⟨a', ha', b', hb', rfl⟩ := ht
          rw [Algebra.TensorProduct.tmul_mul_tmul]
          exact tmul_mem_spanTmul (A.mul_mem ha ha') (A.mul_mem hb hb')
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add t t' _ _ ht ht' => rw [mul_add]; exact Submodule.add_mem _ ht ht'
      | smul r t _ ht => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ht
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add s s' _ _ hs hs' => rw [add_mul]; exact Submodule.add_mem _ (hs hy) (hs' hy)
  | smul r s _ hs => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ (hs hy)

end TensorSpans

open TensorSpans in
theorem _root_.HopfAlgebra.exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)
    (s : Finset H) (hs : (↑s : Set H) ⊆ K) :
    ∃ K₀ : Subalgebra k H, K₀ ≤ K ∧ K₀.FG ∧ (↑s : Set H) ⊆ K₀ ∧
      (∀ x ∈ K₀, Coalgebra.comul (R := k) x ∈
        Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K₀, ∃ b ∈ K₀, t = a ⊗ₜ[k] b}) ∧
      (∀ x ∈ K₀, HopfAlgebra.antipode k x ∈ K₀) := by
  classical
  have hK' : ∀ x ∈ K.toSubmodule, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K.toSubmodule, ∃ b ∈ K.toSubmodule, t = a ⊗ₜ[k] b} :=
        hΔ
  have hloc : ∀ x : ↥s, ∃ D : Submodule k H, D ≤ K.toSubmodule ∧ FiniteDimensional k ↥D ∧ (x : H)
    ∈ D ∧
      ∀ y ∈ D, Coalgebra.comul (R := k) y ∈ spanTmul D D :=
    fun x => Coalgebra.exists_finiteDimensional_le_comul_mem_span K.toSubmodule hK' x (hs x.2)
  choose Dx hDxK hDxfin hxDx hΔDx using hloc
  let D : Submodule k H := ⨆ x : ↥s, Dx x
  have hDK : D ≤ K.toSubmodule := iSup_le hDxK
  have : FiniteDimensional k ↥D := Submodule.finiteDimensional_iSup _
  have hsD : ∀ x ∈ s, x ∈ D := fun x hx => (le_iSup Dx ⟨x, hx⟩) (hxDx ⟨x, hx⟩)
  have hΔD : ∀ y ∈ D, Coalgebra.comul (R := k) y ∈ spanTmul D D := by
    intro y hy
    induction hy using Submodule.iSup_induction' with
    | mem x y hy => exact spanTmul_mono (le_iSup Dx x) (le_iSup Dx x) (hΔDx x y hy)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  let SD : Submodule k H := D.map (HopfAlgebra.antipode k (A := H))
  let D' : Submodule k H := D ⊔ SD
  have hD'K : D' ≤ K.toSubmodule := by
    refine sup_le hDK ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hS z (hDK hz)
  have : FiniteDimensional k ↥D' := Submodule.finiteDimensional_sup D SD
  have hΔSD : ∀ y ∈ SD, Coalgebra.comul (R := k) y ∈ spanTmul SD SD := by
    rintro _ ⟨z, hz, rfl⟩
    rw [HopfAlgebra.comul_antipode]
    exact map_comm_mem_spanTmul D D _ (hΔD z hz)
  have hΔD' : ∀ y ∈ D', Coalgebra.comul (R := k) y ∈ spanTmul D' D' := by
    intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
    rw [map_add]
    exact Submodule.add_mem _ (spanTmul_mono le_sup_left le_sup_left (hΔD y₁ hy₁))
      (spanTmul_mono le_sup_right le_sup_right (hΔSD y₂ hy₂))
  have hSD' : ∀ y ∈ D', HopfAlgebra.antipode k y ∈ D' := by
    intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
    rw [map_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mem_map_of_mem hy₁)) ?_
    obtain ⟨z, hz, rfl⟩ := hy₂
    rw [HopfAlgebra.antipode_antipode]
    exact Submodule.mem_sup_left hz
  obtain ⟨tfin, htfin⟩ := (Submodule.fg_iff_finiteDimensional D').mpr inferInstance
  let K₀ : Subalgebra k H := Algebra.adjoin k (D' : Set H)
  have hK₀t : K₀ = Algebra.adjoin k (↑tfin : Set H) := by
    change Algebra.adjoin k (D' : Set H) = _
    rw [← htfin, Algebra.adjoin_span]
  have hD'K₀ : (D' : Set H) ⊆ K₀ := Algebra.subset_adjoin
  have hΔK₀ : ∀ x ∈ K₀, Coalgebra.comul (R := k) x ∈ spanTmul K₀.toSubmodule K₀.toSubmodule := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
        exact spanTmul_mono (fun z hz => hD'K₀ hz) (fun z hz => hD'K₀ hz) (hΔD' y hy)
    | algebraMap r =>
        rw [Algebra.algebraMap_eq_smul_one, map_smul, Bialgebra.comul_one]
        exact Submodule.smul_mem _ _ (tmul_mem_spanTmul K₀.one_mem K₀.one_mem)
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | mul y z _ _ hy hz => rw [Bialgebra.comul_mul]; exact mul_mem_spanTmul K₀ hy hz
  have hSK₀ : ∀ x ∈ K₀, HopfAlgebra.antipode k x ∈ K₀ := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem y hy => exact hD'K₀ (hSD' y hy)
    | algebraMap r =>
        rw [Algebra.algebraMap_eq_smul_one, map_smul, HopfAlgebra.antipode_one]
        exact K₀.smul_mem K₀.one_mem r
    | add y z _ _ hy hz => rw [map_add]; exact K₀.add_mem hy hz
    | mul y z _ _ hy hz => rw [HopfAlgebra.antipode_mul_antidistrib]; exact K₀.mul_mem hz hy
  refine ⟨K₀, ?_, ⟨tfin, hK₀t.symm⟩, fun x hx => hD'K₀ (Submodule.mem_sup_left (hsD x hx)), hΔK₀,
    hSK₀⟩
  exact Algebra.adjoin_le fun y hy => hD'K hy

end SchemeTheory.HopfSubalgebras.FiniteGeneration
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_faithfullyFlat_subalgebra_of_forall_isReduced_of_perfectField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.HopfSubalgebras.PerfectFieldCase

open scoped TensorProduct

universe u v

namespace ScalarDescent

theorem codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong (fun {R S} [CommRing R] [CommRing S] => RingHom.FaithfullyFlat (R :=
      R) (S := S))
      (fun {R S} [CommRing R] [CommRing S] => RingHom.FaithfullyFlat (R := R) (S := S)) := by
  refine RingHom.CodescendsAlong.mk _ RingHom.FaithfullyFlat.respectsIso ?_
  intro R S T _ _ _ _ _ hRS hST
  rw [RingHom.faithfullyFlat_algebraMap_iff] at hRS hST ⊢
  exact
AbelianVarieties.NOSProofs.BaseChangeFlatDescent.S17Ta.faithfullyFlat_of_faithfullyFlat_baseChange
      R S T

end ScalarDescent

open ScalarDescent in
theorem _root_.HopfAlgebra.faithfullyFlat_subalgebra_of_forall_isReduced_of_perfectField
    {k : Type u} [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {H : Type v} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    (hred : ∀ K' : Subalgebra k H,
      (∀ x ∈ K', Coalgebra.comul (R := k) x ∈
        Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K', ∃ b ∈ K', t = a ⊗ₜ[k] b}) →
      (∀ x ∈ K', HopfAlgebra.antipode k x ∈ K') → K'.FG → IsReduced ↥K' →
      Module.FaithfullyFlat ↥K' H)
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K) (hfg : K.FG) :
    Module.FaithfullyFlat ↥K H := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨r, K', hK'K, hK'fg, hK'red, hK'set, hΔ', hS'⟩ :=
    HopfAlgebra.exists_subalgebra_pow_char_pow_isReduced p K hΔ hS hfg
  have : IsReduced ↥K' := hK'red
  have hffK' : Module.FaithfullyFlat ↥K' H := hred K' hΔ' hS' hK'fg hK'red
  have hpowK' : ∀ x ∈ K, x ^ p ^ r ∈ K' := fun x hx => by
    change x ^ p ^ r ∈ (K' : Set H)
    rw [hK'set]; exact ⟨x, hx, rfl⟩
  let : Algebra ↥K' ↥K := (Subalgebra.inclusion hK'K).toAlgebra
  have : IsScalarTower ↥K' ↥K H := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  obtain ⟨Hb, _, _, πc, hπsurj, hker, hcounit, hanti, hsub⟩ :=
    HopfAlgebra.exists_hopfAlgebra_surjective_ker_eq_span_of_comul_mem_span_of_antipode_mem K' hΔ'
      hS'
  obtain ⟨hΔb, hSb⟩ := hsub K hΔ hS
  let π : H →ₐ[k] Hb := (πc : H →ₐ[k] Hb)
  have hπsurj' : Function.Surjective π := hπsurj
  have hkerπ : RingHom.ker π = Ideal.span {x : H | x ∈ K' ∧ Coalgebra.counit (R := k) x = 0} := hker
  have hnil : IsNilpotent (RingHom.ker ((Bialgebra.counitAlgHom k Hb).comp (K.map π).val)) := by
    have hKfg : (K.map π).FG := hfg.map π
    have hKft : Algebra.FiniteType k ↥(K.map π) := (Subalgebra.fg_iff_finiteType _).mp hKfg
    have : IsNoetherianRing ↥(K.map π) := Algebra.FiniteType.isNoetherianRing k ↥(K.map π)
    refine (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)).mpr ?_
    intro y hy
    rw [RingHom.mem_ker] at hy
    have hy' : Coalgebra.counit (R := k) (y : Hb) = 0 := hy
    obtain ⟨x, hxK, hxy⟩ := Subalgebra.mem_map.mp y.2
    have hcx : Coalgebra.counit (R := k) x = 0 := by
      rw [← hcounit x]
      change Coalgebra.counit (R := k) (π x) = 0
      rw [hxy]
      exact hy'
    have hmem : x ^ p ^ r ∈ RingHom.ker π := by
      rw [hkerπ]
      refine Ideal.subset_span ⟨hpowK' x hxK, ?_⟩
      change Bialgebra.counitAlgHom k H (x ^ p ^ r) = 0
      rw [map_pow, show Bialgebra.counitAlgHom k H x = Coalgebra.counit x from rfl, hcx,
        zero_pow (pow_ne_zero _ hp.ne_zero)]
    rw [mem_nilradical]
    refine ⟨p ^ r, Subtype.ext ?_⟩
    rw [Subalgebra.coe_pow, Subalgebra.coe_zero, ← hxy, ← map_pow]
    exact RingHom.mem_ker.mp hmem
  have hfree : Module.Free ↥(K.map π) Hb := HopfAlgebra.free_subalgebra_of_isNilpotent_ker_counit
    (K.map π) hΔb hSb hnil
  have hsq := HopfAlgebra.faithfullyFlat_map_toAlgHom_tensor_of_free_map_of_ker_eq_span K' K hΔ'
    hΔ Hb π hπsurj' hkerπ
  have : Module.FaithfullyFlat ↥K (↥K ⊗[↥K'] H) := inferInstance
  have hQS : (algebraMap ↥K (↥K ⊗[↥K'] H)).FaithfullyFlat :=
    (RingHom.faithfullyFlat_algebraMap_iff).mpr inferInstance
  let e : (↥K ⊗[↥K'] H) ⊗[↥K] H ≃ₐ[↥K] H ⊗[↥K'] H :=
    (Algebra.TensorProduct.comm ↥K (↥K ⊗[↥K'] H) H).trans (Algebra.TensorProduct.cancelBaseChange
      ↥K' ↥K ↥K H H)
  have he : ∀ s : ↥K ⊗[↥K'] H, e (s ⊗ₜ[↥K] (1 : H))
      = Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥K' ↥K H) (AlgHom.id ↥K' H) s := by
    intro s
    induction s using TensorProduct.inductionOn with
    | tmul a h =>
        change Algebra.TensorProduct.cancelBaseChange ↥K' ↥K ↥K H H
          (Algebra.TensorProduct.comm ↥K (↥K ⊗[↥K'] H) H ((a ⊗ₜ[↥K'] h) ⊗ₜ[↥K] (1 : H))) = _
        rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.cancelBaseChange_tmul,
          Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.toAlgHom_apply,
            Algebra.smul_def, mul_one]
    | add x y hx hy => rw [TensorProduct.add_tmul, map_add, map_add, hx, hy]
  refine (RingHom.faithfullyFlat_algebraMap_iff).mp
    (RingHom.CodescendsAlong.algebraMap_tensorProduct _ ↥K (↥K ⊗[↥K'] H) H
      codescendsAlong_faithfullyFlat hQS ?_)
  have h1 := @(RingHom.FaithfullyFlat.respectsIso).1 (↥K ⊗[↥K'] H) (H ⊗[↥K'] H) ((↥K ⊗[↥K'] H)
    ⊗[↥K] H)
    _ _ _ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥K' ↥K H) (AlgHom.id ↥K' H)).toRingHom
    e.symm.toRingEquiv hsq
  have hEq : e.symm.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥K' ↥K H) (AlgHom.id ↥K' H)).toRingHom
      = algebraMap (↥K ⊗[↥K'] H) ((↥K ⊗[↥K'] H) ⊗[↥K] H) := by
    apply RingHom.ext
    intro s
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    change e.symm (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥K' ↥K H) (AlgHom.id ↥K' H)
      s) = s ⊗ₜ[↥K] 1
    rw [← he, AlgEquiv.symm_apply_apply]
  rw [hEq] at h1
  exact h1

end SchemeTheory.HopfSubalgebras.PerfectFieldCase
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.HopfSubalgebras.FaithfulFlatness

open scoped TensorProduct

universe u v w

namespace Descent

/-- Stability under comultiplication, expressed in the ambient tensor square. -/
abbrev ΔStable {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H) : Prop :=
  ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
    Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}

/-- Stability under the antipode. -/
abbrev SStable {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H) : Prop :=
  ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K

theorem algClosed_case {k : Type u} [Field k] [IsAlgClosed k] {H : Type v} [CommRing H]
    [HopfAlgebra k H]
    [Algebra.FiniteType k H] (K : Subalgebra k H) (hΔ : ΔStable K) (hS : SStable K) :
    Module.FaithfullyFlat ↥K H := by
  classical
  have key : ∀ K₀ : Subalgebra k H,
      ΔStable K₀ → SStable K₀ → K₀.FG → Module.FaithfullyFlat ↥K₀ H := by
    intro K₀ hΔ₀ hS₀ hfg
    obtain ⟨p, hp⟩ := CharP.exists k
    rcases CharP.char_is_prime_or_zero k p with hpr | rfl
    · have : Fact p.Prime := ⟨hpr⟩
      exact HopfAlgebra.faithfullyFlat_subalgebra_of_forall_isReduced_of_perfectField p
        (fun K' hΔ' hS' hfg' _ =>
          HopfAlgebra.faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed K' hΔ' hS' hfg')
        K₀ hΔ₀ hS₀ hfg
    · have : CharZero k := CharP.charP_to_charZero k
      have : IsReduced H := HopfAlgebra.isReduced_of_finiteType_of_charZero k H
      have : IsReduced ↥K₀ := isReduced_of_injective K₀.val Subtype.val_injective
      exact HopfAlgebra.faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed K₀ hΔ₀ hS₀ hfg
  let ι := {K₀ : Subalgebra k H // K₀ ≤ K ∧ K₀.FG ∧ ΔStable K₀ ∧ SStable K₀}
  have hex : ∀ s : Finset H, (↑s : Set H) ⊆ K → ∃ i : ι, (↑s : Set H) ⊆ i.1 := by
    intro s hs
    obtain ⟨K₀, hle, hfg, hsub, hΔ₀, hS₀⟩ :=
      HopfAlgebra.exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset K hΔ hS s hs
    exact ⟨⟨K₀, hle, hfg, hΔ₀, hS₀⟩, hsub⟩
  have : Nonempty ι := by
    obtain ⟨i, -⟩ := hex ∅ (by rw [Finset.coe_empty]; exact Set.empty_subset _)
    exact ⟨i⟩
  refine Subalgebra.faithfullyFlat_of_directed_of_forall_faithfullyFlat K (fun i : ι => i.1) ?_
    (fun i => i.2.1)
    ?_ (fun i => key i.1 i.2.2.2.1 i.2.2.2.2 i.2.2.1)
  · intro i j
    obtain ⟨sᵢ, hsᵢ⟩ := i.2.2.1
    obtain ⟨sⱼ, hsⱼ⟩ := j.2.2.1
    have hsub : (↑(sᵢ ∪ sⱼ) : Set H) ⊆ K := by
      rw [Finset.coe_union]
      refine Set.union_subset ?_ ?_
      · exact (Algebra.subset_adjoin.trans (le_of_eq hsᵢ : Algebra.adjoin k ↑sᵢ ≤ i.1)).trans i.2.1
      · exact (Algebra.subset_adjoin.trans (le_of_eq hsⱼ : Algebra.adjoin k ↑sⱼ ≤ j.1)).trans j.2.1
    obtain ⟨m, hm⟩ := hex (sᵢ ∪ sⱼ) hsub
    refine ⟨m, ?_, ?_⟩
    · change i.1 ≤ m.1
      rw [← hsᵢ]
      exact Algebra.adjoin_le ((Finset.coe_subset.mpr Finset.subset_union_left).trans hm)
    · change j.1 ≤ m.1
      rw [← hsⱼ]
      exact Algebra.adjoin_le ((Finset.coe_subset.mpr Finset.subset_union_right).trans hm)
  · intro x hx
    obtain ⟨i, hi⟩ := hex {x} (by
      intro y hy
      have hyx : y = x := Finset.mem_singleton.mp hy
      subst y
      exact hx)
    exact ⟨i, hi (Finset.mem_singleton_self x)⟩

theorem stable_range {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H) (hΔ : ΔStable K) (hS : SStable K) (k' : Type w) [Field k'] [Algebra k k'] :
    ΔStable ((Algebra.TensorProduct.map (AlgHom.id k' k') K.val).range) ∧
      SStable ((Algebra.TensorProduct.map (AlgHom.id k' k') K.val).range) := by
  classical
  set φ := Algebra.TensorProduct.map (AlgHom.id k' k') K.val with hφ
  have hφ_tmul : ∀ (c : k') (y : ↥K), φ (c ⊗ₜ[k] y) = c ⊗ₜ[k] (y : H) := fun c y => by
    rw [hφ, Algebra.TensorProduct.map_tmul]; rfl
  have hmem : ∀ (c : k') (y : H), y ∈ K → c ⊗ₜ[k] y ∈ φ.range := fun c y hy =>
    ⟨c ⊗ₜ[k] ⟨y, hy⟩, hφ_tmul c ⟨y, hy⟩⟩
  set P : Submodule k' ((k' ⊗[k] H) ⊗[k'] (k' ⊗[k] H)) :=
    Submodule.span k' {t | ∃ a ∈ φ.range, ∃ b ∈ φ.range, t = a ⊗ₜ[k'] b} with hP
  constructor
  · rintro _ ⟨t, rfl⟩
    change Coalgebra.comul (R := k') (φ t) ∈ P
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add]; exact P.add_mem hx hy
    | tmul c y =>
        rw [hφ_tmul, TensorProduct.comul_tmul, CommSemiring.comul_apply]
        refine Submodule.span_induction ?_ ?_ ?_ ?_ (hΔ (y : H) y.2)
        · rintro _ ⟨a, ha, b, hb, rfl⟩
          rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
          exact Submodule.subset_span ⟨_, hmem 1 a ha, _, hmem c b hb, rfl⟩
        · rw [TensorProduct.tmul_zero, map_zero]; exact P.zero_mem
        · intro z₁ z₂ _ _ h₁ h₂
          rw [TensorProduct.tmul_add, map_add]; exact P.add_mem h₁ h₂
        · intro r z _ hz
          rw [TensorProduct.tmul_smul, ← algebraMap_smul k' r, LinearEquiv.map_smul]
          exact P.smul_mem _ hz
  · rintro _ ⟨t, rfl⟩
    change HopfAlgebra.antipode k' (φ t) ∈ φ.range
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add]; exact Subalgebra.add_mem _ hx hy
    | tmul c y =>
        rw [hφ_tmul, TensorProduct.antipode_def, TensorProduct.AlgebraTensorModule.map_tmul,
          CommSemiring.antipode_eq_id, LinearMap.id_apply]
        exact hmem c _ (hS (y : H) y.2)

end Descent

open Descent in
theorem _root_.HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K) :
    Module.FaithfullyFlat ↥K H := by
  obtain ⟨hΔ', hS'⟩ := stable_range K hΔ hS (AlgebraicClosure k)
  exact Subalgebra.faithfullyFlat_of_faithfullyFlat_range_baseChange K (AlgebraicClosure k)
    (algClosed_case _ hΔ' hS')

end SchemeTheory.HopfSubalgebras.FaithfulFlatness
end
